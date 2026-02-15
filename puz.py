#!/usr/bin/env python3

import asyncio
import aiohttp
import time
import hashlib
import binascii
import multiprocessing
from multiprocessing import Process, Queue
import base58
import ecdsa
import random
import secrets
import json
import os
import ssl
import socket
from datetime import datetime
from typing import List, Tuple, Dict, Optional
import sys
import threading
from queue import Empty
import signal

# Import untuk Electrum client yang lebih baik
from aiorpcx import connect_rs, RPCError, TaskTimeout
import nest_asyncio

# ============================================================
# CONFIG - OPTIMIZED
# ============================================================

# Puzzle 160 range 
LOW = 0x3da316fc3dfc61f38f7e832cb02759b2bb0be4359ad4c02ceac5e2de41c7a337
HIGH = 0x6b60169b1d6f8f7f21207d4ff2d3575f8d3e73e6dd0b87cf86269c23ee6803f7

# Performance tuning
WORKERS_PER_CORE = 4  # Increased from 2
QUEUE_SIZE = 50000  # Increased from 10000
BATCH_SIZE = 500  # Increased from 100 untuk throughput lebih tinggi
MAX_CONCURRENT_BATCHES = 200  # Increased from 50
BATCH_TIMEOUT = 15  # Timeout per batch in seconds
SERVER_TEST_TIMEOUT = 10  # Reduced from 20
REQUEST_TIMEOUT = 15  # Reduced from 30

# Test addresses untuk verifikasi server
TEST_ADDRESSES = [
    "1111111111111111111114oLvT2",  # Legacy address
    "1A1zP1eP5QGefi2DMPTfTL5SLmv7DivfNa",  # Genesis address
    "111111811zDiVJNrGoufFmZUdetqXMqV"  # Another test address
]

# Daftar server Electrum yang stabil (ditambah lebih banyak)
ELECTRUM_SERVERS = [
    {"host": "electrum.blockstream.info", "port": 50002, "protocol": "ssl"},
    {"host": "23.155.96.131", "port": 50002, "protocol": "ssl"},
    {"host": "blockstream.info", "port": 700, "protocol": "ssl"},
]

# ============================================================
# [SEMUA FUNGSI UTILITY TETAP SAMA - BECH32, ADDRESS, DLL]
# ============================================================

CHARSET = "qpzry9x8gf2tvdw0s3jn54khce6mua7l"

def bech32_polymod(values):
    GENERATORS = [0x3b6a57b2, 0x26508e6d, 0x1ea119fa, 0x3d4233dd, 0x2a1462b3]
    chk = 1
    for v in values:
        b = (chk >> 25)
        chk = ((chk & 0x1ffffff) << 5) ^ v
        for i in range(5):
            if ((b >> i) & 1):
                chk ^= GENERATORS[i]
    return chk

def bech32_hrp_expand(hrp):
    return [ord(x) >> 5 for x in hrp] + [0] + [ord(x) & 31 for x in hrp]

def bech32_decode_custom(bech):
    if ((any(ord(x) < 33 or ord(x) > 126 for x in bech)) or
        (bech.lower() != bech and bech.upper() != bech)):
        return (None, None)
    bech = bech.lower()
    pos = bech.rfind('1')
    if pos < 1 or pos + 7 > len(bech):
        return (None, None)
    hrp = bech[:pos]
    data = []
    for c in bech[pos+1:]:
        if c not in CHARSET:
            return (None, None)
        data.append(CHARSET.find(c))

    pm = bech32_polymod(bech32_hrp_expand(hrp) + data)
    if pm == 1 or pm == 0x2bc830a3:
        return (hrp, data)
    return (None, None)

def convertbits(data, frombits, tobits, pad=True):
    acc = 0
    bits = 0
    ret = []
    maxv = (1 << tobits) - 1
    for value in data:
        if value < 0 or (value >> frombits):
            return None
        acc = (acc << frombits) | value
        bits += frombits
        while bits >= tobits:
            bits -= tobits
            ret.append((acc >> bits) & maxv)
    if pad:
        if bits:
            ret.append((acc << (tobits - bits)) & maxv)
    elif bits >= frombits or ((acc << (tobits - bits)) & maxv):
        return None
    return ret

def taproot_scriptpubkey_from_witness(witness_version: int, witness_program: bytes) -> bytes:
    if witness_version == 0:
        ver_byte = 0x00
    else:
        ver_byte = 0x50 + witness_version

    push_len = len(witness_program)
    if push_len < 0x4c:
        return bytes([ver_byte, push_len]) + witness_program
    if push_len <= 0xff:
        return bytes([ver_byte, 0x4c, push_len]) + push_len.to_bytes(1, 'little') + witness_program
    if push_len <= 0xffff:
        return bytes([ver_byte, 0x4d]) + push_len.to_bytes(2, 'little') + witness_program
    return bytes([ver_byte, 0x4e]) + push_len.to_bytes(4, 'little') + witness_program

def generate_private_key():
    range_size = HIGH - LOW + 1
    candidate = LOW + secrets.randbelow(range_size)
    return hex(candidate)[2:].zfill(64)


def private_key_to_WIF(private_key: str) -> str:
    var80 = "80" + private_key
    first_sha = hashlib.sha256(binascii.unhexlify(var80)).digest()
    second_sha = hashlib.sha256(first_sha).digest()
    checksum = second_sha[:4]
    return base58.b58encode(
        binascii.unhexlify(var80) + checksum
    ).decode()

def private_key_to_public_key(private_key: str) -> str:
    sk = ecdsa.SigningKey.from_string(
        binascii.unhexlify(private_key),
        curve=ecdsa.SECP256k1
    )
    vk = sk.verifying_key
    key_bytes = vk.to_string()
    x = key_bytes[:32]
    y = key_bytes[32:]
    prefix = b'\x02' if (y[-1] % 2 == 0) else b'\x03'
    return binascii.hexlify(prefix + x).decode()

def public_key_to_address(public_key: str) -> str:
    public_key_bytes = binascii.unhexlify(public_key)
    sha256_hash = hashlib.sha256(public_key_bytes).digest()
    ripemd160 = hashlib.new('ripemd160')
    ripemd160.update(sha256_hash)
    hashed_public_key = ripemd160.digest()
    versioned_payload = b'\x00' + hashed_public_key
    checksum = hashlib.sha256(
        hashlib.sha256(versioned_payload).digest()
    ).digest()[:4]
    return base58.b58encode(versioned_payload + checksum).decode()

def address_to_scripthash(address: str) -> str:
    try:
        if address.startswith("bc1") or address.startswith("tb1"):
            try:
                hrp, data = bech32_decode_custom(address)
                if hrp is None or data is None:
                    raise ValueError("Invalid bech32 / bech32m address or checksum")
                witver = data[0]
                witprog = convertbits(data[1:-6], 5, 8, False)
                if witprog is None:
                    raise ValueError("Invalid witness program conversion")
                witprog_bytes = bytes(witprog)
                if len(witprog_bytes) < 2 or len(witprog_bytes) > 40:
                    raise ValueError("Invalid witness program length")
                script = taproot_scriptpubkey_from_witness(witver, witprog_bytes)
            except Exception:
                try:
                    import bech32
                    if address.startswith("bc1"): 
                        hrp = "bc"
                    else: 
                        hrp = "tb"
                    
                    witver, witprog = bech32.decode(hrp, address)
                    if witver is None or witprog is None:
                        raise ValueError("Invalid bech32/bech32m address")
                    
                    witprog_bytes = bytes(convertbits(witprog, 5, 8, False))
                    
                    if witver == 0:
                        if len(witprog_bytes) == 20:
                            script = bytes([0x00, 0x14]) + witprog_bytes
                        elif len(witprog_bytes) == 32:
                            script = bytes([0x00, 0x20]) + witprog_bytes
                        else:
                            raise ValueError(f"Invalid witness program length for segwit v0: {len(witprog_bytes)}")
                    elif witver == 1:
                        if len(witprog_bytes) == 32:
                            script = bytes([0x51, 0x20]) + witprog_bytes
                        else:
                            raise ValueError(f"Invalid witness program length for Taproot: {len(witprog_bytes)}")
                    else:
                        if 2 <= len(witprog_bytes) <= 40:
                            script = bytes([0x50 + witver, len(witprog_bytes)]) + witprog_bytes
                        else:
                            raise ValueError(f"Unsupported witness version: {witver}")
                except ImportError:
                    raise ValueError("bech32 library not available and custom decoder failed")

        else:
            decoded = base58.b58decode_check(address)
            ver, payload = decoded[0], decoded[1:]
            if ver == 0x00:
                script = b"\x76\xa9\x14" + payload + b"\x88\xac"
            elif ver == 0x05:
                script = b"\xa9\x14" + payload + b"\x87"
            else:
                raise ValueError("unknown address version")

        scripthash = hashlib.sha256(script).digest()[::-1].hex()
        return scripthash

    except Exception as e:
        raise ValueError(f"address_to_scripthash error for {address}: {e}")

# ============================================================
# OPTIMIZED ELECTRUM SERVER MANAGER
# ============================================================

class ElectrumServerManager:
    def __init__(self):
        self.servers = ELECTRUM_SERVERS
        self._healthy_servers = []
        self._ssl_context = self._create_ssl_context()
        self._server_stats = {}
        self._last_test_time = 0
        self._test_interval = 300  # Test servers every 5 minutes
        self._lock = asyncio.Lock()
        self._verified_servers = []  # Servers that passed the test addresses verification

    def _create_ssl_context(self):
        context = ssl.create_default_context()
        context.check_hostname = False
        context.verify_mode = ssl.CERT_NONE
        return context

    async def _test_server_speed(self, server):
        host, port = server["host"], server["port"]
        
        try:
            ssl_ctx = self._ssl_context
            
            async with asyncio.timeout(SERVER_TEST_TIMEOUT):
                async with connect_rs(host, port, ssl=ssl_ctx) as session:
                    start_time = time.time()
                    await session.send_request("server.version", ["electrum-client", "1.4"])
                    
                    test_address = "1A1zP1eP5QGefi2DMPTfTL5SLmv7DivfNa"
                    test_scripthash = address_to_scripthash(test_address)
                    
                    balance_response = await session.send_request(
                        "blockchain.scripthash.get_balance", 
                        [test_scripthash]
                    )
                    
                    response_time = (time.time() - start_time) * 1000
                    
                    if isinstance(balance_response, dict):
                        server_key = f"{host}:{port}"
                        self._server_stats[server_key] = {
                            'response_time': response_time,
                            'last_success': time.time(),
                            'success_count': self._server_stats.get(server_key, {}).get('success_count', 0) + 1
                        }
                        return True, response_time
                    else:
                        return False, float('inf')
                        
        except asyncio.TimeoutError:
            return False, float('inf')
        except Exception:
            return False, float('inf')

    async def _verify_server_with_test_addresses(self, server):
        """Verify server by checking known test addresses"""
        host, port = server["host"], server["port"]
        
        try:
            ssl_ctx = self._ssl_context
            
            async with asyncio.timeout(SERVER_TEST_TIMEOUT * 2):  # Double timeout for verification
                async with connect_rs(host, port, ssl=ssl_ctx) as session:
                    # Test all test addresses
                    all_successful = True
                    results = {}
                    
                    for address in TEST_ADDRESSES:
                        try:
                            scripthash = address_to_scripthash(address)
                            response = await session.send_request(
                                "blockchain.scripthash.get_balance", 
                                [scripthash]
                            )
                            
                            if isinstance(response, dict):
                                confirmed = response.get("confirmed", 0)
                                unconfirmed = response.get("unconfirmed", 0)
                                total = confirmed + unconfirmed
                                results[address] = total / 100000000  # Convert to BTC
                            else:
                                all_successful = False
                                break
                        except Exception as e:
                            print(f"   ❌ Failed to check {address}: {str(e)[:50]}")
                            all_successful = False
                            break
                    
                    if all_successful:
                        print(f"   ✅ Verification successful - All test addresses responded")
                        print(f"      Balances: {', '.join([f'{addr[:10]}...: {results[addr]:.8f} BTC' for addr in TEST_ADDRESSES])}")
                        return True, results
                    else:
                        print(f"   ❌ Verification failed - Some addresses didn't respond properly")
                        return False, None
                        
        except Exception as e:
            print(f"   ❌ Verification error: {str(e)[:50]}")
            return False, None

    async def get_fastest_servers(self, limit=3, verify=True):
        """Get multiple fastest servers untuk load balancing, with optional verification"""
        async with self._lock:
            current_time = time.time()
            
            # Test servers if needed
            if not self._healthy_servers or (current_time - self._last_test_time) > self._test_interval:
                print("\n" + "=" * 80)
                print("⚡ TESTING ELECTRUM SERVERS WITH VERIFICATION")
                print("=" * 80)
                
                # First test speed
                print("\n📊 Testing server speed...")
                speed_tasks = [self._test_server_speed(server) for server in self.servers]
                speed_results = await asyncio.gather(*speed_tasks, return_exceptions=True)
                
                healthy = []
                for i, (server, result) in enumerate(zip(self.servers, speed_results)):
                    if isinstance(result, tuple) and result[0]:
                        healthy.append((server, result[1]))
                        print(f"   ✅ {server['host']}:{server['port']} - {result[1]:.1f}ms")
                    else:
                        print(f"   ❌ {server['host']}:{server['port']} - Failed speed test")
                
                # Sort by response time
                healthy.sort(key=lambda x: x[1])
                
                if verify:
                    print("\n🔍 Verifying top servers with test addresses...")
                    # Verify top 5 fastest servers
                    verified_servers = []
                    for server, response_time in healthy[:5]:
                        print(f"\n   Testing {server['host']}:{server['port']}...")
                        verified, results = await self._verify_server_with_test_addresses(server)
                        if verified:
                            verified_servers.append((server, response_time))
                            print(f"   ✅ Server verified and added to pool")
                        else:
                            print(f"   ❌ Server rejected - verification failed")
                    
                    if verified_servers:
                        self._healthy_servers = [s for s, _ in verified_servers[:limit]]
                        self._verified_servers = verified_servers
                        print(f"\n✅ Found {len(self._healthy_servers)} verified fast servers")
                        
                        # Print summary
                        print("\n📋 VERIFIED SERVERS SUMMARY:")
                        for i, (server, resp_time) in enumerate(verified_servers[:limit]):
                            print(f"   {i+1}. {server['host']}:{server['port']} - {resp_time:.1f}ms")
                    else:
                        print("\n⚠️  No servers passed verification! Falling back to speed-tested only...")
                        self._healthy_servers = [s for s, _ in healthy[:limit]]
                else:
                    self._healthy_servers = [s for s, _ in healthy[:limit]]
                
                self._last_test_time = current_time
            
            return self._healthy_servers

    async def get_verification_results(self):
        """Get the results from the last verification test"""
        if self._verified_servers:
            return self._verified_servers
        return []

# ============================================================
# OPTIMIZED ELECTRUM CLIENT WITH CONNECTION POOLING
# ============================================================

class ConnectionPool:
    def __init__(self, max_connections=10):
        self.max_connections = max_connections
        self._connections = {}  # {server_key: [connections]}
        self._locks = {}  # {server_key: asyncio.Lock}
        self._ssl_context = ssl.create_default_context()
        self._ssl_context.check_hostname = False
        self._ssl_context.verify_mode = ssl.CERT_NONE

    async def get_connection(self, host, port):
        server_key = f"{host}:{port}"
        
        if server_key not in self._locks:
            self._locks[server_key] = asyncio.Lock()
        
        async with self._locks[server_key]:
            if server_key not in self._connections:
                self._connections[server_key] = []
            
            # Try to get an existing connection
            if self._connections[server_key]:
                conn = self._connections[server_key].pop()
                try:
                    # Test if connection is still alive
                    await conn.send_request("server.version", ["test", "1.4"])
                    return conn
                except:
                    pass  # Connection dead, create new
            
            # Create new connection
            try:
                conn = await connect_rs(host, port, ssl=self._ssl_context)
                return conn
            except Exception as e:
                raise e

    async def return_connection(self, host, port, conn):
        server_key = f"{host}:{port}"
        async with self._locks.get(server_key, asyncio.Lock()):
            if server_key not in self._connections:
                self._connections[server_key] = []
            
            if len(self._connections[server_key]) < self.max_connections:
                self._connections[server_key].append(conn)
            else:
                await conn.close()

class EnhancedElectrumClient:
    def __init__(self):
        self.server_manager = ElectrumServerManager()
        self.connection_pool = ConnectionPool(max_connections=20)
        self.request_count = 0
        self.failed_requests = 0
        self.MAX_CONCURRENT_REQUESTS = 200  # Increased
        self._request_semaphore = asyncio.Semaphore(self.MAX_CONCURRENT_REQUESTS)
        self.found_addresses = []
        self._batch_semaphore = asyncio.Semaphore(MAX_CONCURRENT_BATCHES)
        self.verified_servers = []

    async def initialize(self):
        await self.server_manager.get_fastest_servers(limit=5, verify=True)
        self.verified_servers = await self.server_manager.get_verification_results()
        return self

    async def batch_get_balance(self, addresses_with_keys: List[Tuple[str, str]]) -> Dict[str, float]:
        if not addresses_with_keys:
            return {}
        
        # Gunakan semaphore untuk membatasi concurrent batches
        async with self._batch_semaphore:
            return await self._do_batch_get_balance(addresses_with_keys)

    async def _do_batch_get_balance(self, addresses_with_keys: List[Tuple[str, str]]) -> Dict[str, float]:
        # Convert to scripthashes dengan caching sederhana
        request_map = {}
        for pk, addr in addresses_with_keys:
            try:
                scripthash = address_to_scripthash(addr)
                request_map[scripthash] = (pk, addr)
            except ValueError:
                continue
        
        if not request_map:
            return {}
        
        # Dapatkan multiple servers untuk load balancing
        servers = await self.server_manager.get_fastest_servers(limit=3, verify=False)  # Use cached results
        if not servers:
            return {addr: 0 for _, addr in addresses_with_keys}
        
        # Split scripthashes ke multiple servers untuk parallel processing
        scripthash_items = list(request_map.items())
        chunk_size = max(1, len(scripthash_items) // len(servers))
        chunks = [scripthash_items[i:i + chunk_size] for i in range(0, len(scripthash_items), chunk_size)]
        
        # Process chunks secara parallel
        tasks = []
        for i, chunk in enumerate(chunks):
            if chunk:
                server = servers[i % len(servers)]
                task = asyncio.create_task(
                    self._process_chunk(server, chunk)
                )
                tasks.append(task)
        
        # Gabungkan results
        results = {}
        chunk_results = await asyncio.gather(*tasks, return_exceptions=True)
        
        for chunk_result in chunk_results:
            if isinstance(chunk_result, dict):
                results.update(chunk_result)
        
        # Fill missing addresses with 0
        for pk, addr in addresses_with_keys:
            if addr not in results:
                results[addr] = 0
        
        return results

    async def _process_chunk(self, server: dict, chunk: List[Tuple[str, Tuple[str, str]]]) -> Dict[str, float]:
        """Process a chunk of scripthashes on a specific server"""
        host, port = server["host"], server["port"]
        results = {}
        
        try:
            # Get connection from pool
            session = await self.connection_pool.get_connection(host, port)
            
            try:
                # Create tasks for each scripthash in chunk
                tasks = []
                scripthash_list = []
                
                for scripthash, (pk, addr) in chunk:
                    self.request_count += 1
                    scripthash_list.append((scripthash, addr))
                    task = asyncio.create_task(
                        self._safe_get_balance(session, scripthash)
                    )
                    tasks.append(task)
                
                # Wait for all tasks with overall timeout
                batch_results = await asyncio.wait_for(
                    asyncio.gather(*tasks, return_exceptions=True),
                    timeout=BATCH_TIMEOUT
                )
                
                # Process results
                for i, (scripthash, addr) in enumerate(scripthash_list):
                    result = batch_results[i] if i < len(batch_results) else 0

                    if isinstance(result, (int, float)):
                        balance = float(result)
                        results[addr] = balance
                        if balance > 0:
                            pk = chunk[i][1][0]
                            self.found_addresses.append((pk, addr, balance))

                    elif isinstance(result, Exception):
                        self.failed_requests += 1
                        results[addr] = None  # ← beda dengan 0

                    else:
                        self.failed_requests += 1
                        results[addr] = None
   
                        
            finally:
                # Return connection to pool
                await self.connection_pool.return_connection(host, port, session)
                
        except asyncio.TimeoutError:
            print("⚠ Batch timeout - partial results lost")
            for task in tasks:
                task.cancel()

        except Exception:
            for scripthash, (pk, addr) in chunk:
                results[addr] = 0
                self.failed_requests += 1
        
        return results

    async def _safe_get_balance(self, session, scripthash, retries=3):
        delay = 0.5

        for attempt in range(retries):
            try:
                return await self._get_single_balance(session, scripthash)

            except Exception as e:
                if attempt == retries - 1:
                    raise e  # gagal total

                await asyncio.sleep(delay)
                delay *= 2  # exponential backoff

        return 0


    async def _get_single_balance(self, session, scripthash: str) -> float:
        async with self._request_semaphore:
            try:
                result = await asyncio.wait_for(
                    session.send_request(
                        "blockchain.scripthash.get_balance",
                        [scripthash]
                    ),
                    timeout=REQUEST_TIMEOUT
                )

                if isinstance(result, dict):
                    confirmed = result.get("confirmed", 0)
                    unconfirmed = result.get("unconfirmed", 0)
                    total = confirmed + unconfirmed
                    return total / 100000000

                raise ValueError("Invalid RPC response format")

            except (asyncio.TimeoutError, TaskTimeout) as e:
                raise e  # ← JANGAN return 0
            except Exception as e:
                raise e  # ← Propagate error


# ============================================================
# OPTIMIZED ASYNC WORKER
# ============================================================

# ============================================================
# OPTIMIZED ASYNC WORKER - DENGAN FORMAT TABEL
# ============================================================

async def batch_worker(worker_id: int, queue: Queue, stats_queue: Queue):
    """Async worker dengan format tabel untuk semua address"""
    print(f"🚀 Async Worker {worker_id} started")
    
    # Initialize enhanced client
    client = EnhancedElectrumClient()
    await client.initialize()
    
    # Statistics
    checked_count = 0
    found_count = 0
    start_time = time.time()
    last_stats_time = time.time()
    
    # Buffer untuk batch
    batch_buffer = []
    
    # Tampilkan header tabel sekali di awal
    print("\n" + "=" * 110)
    print(f"{'TIME':<10} | {'WORKER':<6} | {'STATUS':<8} | {'BITCOIN ADDRESS':<42} | {'BALANCE':<14} | {'PRIVATE KEY (first 16)':<16}")
    print("=" * 110)
    
    while True:
        # Collect batch dengan non-blocking get
        try:
            while len(batch_buffer) < BATCH_SIZE:
                item = queue.get_nowait()
                batch_buffer.append(item)
        except Empty:
            pass
        
        if not batch_buffer:
            await asyncio.sleep(0.01)
            continue
        
        # Process batch
        current_batch = batch_buffer[:BATCH_SIZE]
        batch_buffer = batch_buffer[BATCH_SIZE:]
        
        # Check batch
        results = await client.batch_get_balance(current_batch)
        
        # Process results dan tampilkan SEMUA address
        for pk, addr in current_batch:
            checked_count += 1
            balance = results.get(addr)
            if balance is None:
                print("⚠ RPC ERROR")
                continue

            timestamp = datetime.now().strftime("%H:%M:%S")
            
            # Tampilkan SEMUA address dengan format tabel
            if balance > 0:
                found_count += 1
                wif = private_key_to_WIF(pk)
                
                # Save to file
                with open("found.txt", "a") as f:
                    f.write(
                        f"=== FOUND {timestamp} ===\n"
                        f"Address: {addr}\n"
                        f"Private Key: {pk}\n"
                        f"WIF: {wif}\n"
                        f"Balance: {balance:.8f} BTC\n"
                        f"==================\n\n"
                    )
                
                # Tampilkan FOUND dengan highlight hijau
                print(f"\033[92m{timestamp:<10} | {worker_id:6d} | 💰 FOUND  | {addr:<42} | {balance:14.8f} | {pk[:16]:<16}\033[0m")
            else:
                # Tampilkan EMPTY dengan warna normal
                print(f"{timestamp:<10} | {worker_id:6d} | ❌ EMPTY  | {addr:<42} | {0:14.8f} | {pk[:16]:<16}")
        
        # Periodic statistics (dengan pemisah yang jelas)
        current_time = time.time()
        if current_time - last_stats_time >= 10:  # Stats every 10 seconds
            elapsed = current_time - start_time
            rate = checked_count / elapsed if elapsed > 0 else 0
            queue_size = queue.qsize()
            
            print("-" * 110)
            print(f"📊 WORKER {worker_id} STATS: Checked: {checked_count:,} | Found: {found_count} | Rate: {rate:.1f} addr/sec | Queue: {queue_size}")
            print("-" * 110)
            
            last_stats_time = current_time

# ============================================================
# PRODUCER OPTIMIZED
# ============================================================

def producer(queue):
    """Producer dengan multiple threads untuk generate address lebih cepat"""
    print("🟡 Producer started with multiple threads", flush=True)
    
    def generate_worker(worker_id, local_queue):
        """Worker thread untuk generate address"""
        local_counter = 0
        while True:
            pk = generate_private_key()
            pub = private_key_to_public_key(pk)
            addr = public_key_to_address(pub)
            
            # Try to put dengan timeout
            try:
                local_queue.put((pk, addr), timeout=1)
                local_counter += 1
                
                if local_counter % 10000 == 0:
                    print(f"📈 Thread-{worker_id} Generated {local_counter:,} addresses", flush=True)
            except:
                # Queue full, sleep sebentar
                time.sleep(0.1)
    
    # Start multiple generator threads
    num_generators = max(4, multiprocessing.cpu_count())
    threads = []
    
    for i in range(num_generators):
        thread = threading.Thread(target=generate_worker, args=(i, queue), daemon=True)
        thread.start()
        threads.append(thread)
    
    # Keep main thread alive
    try:
        while True:
            time.sleep(1)
    except KeyboardInterrupt:
        pass

# ============================================================
# SERVER TEST FUNCTION
# ============================================================

async def test_servers_only():
    """Function to test servers with the specified addresses"""
    print("\n" + "=" * 80)
    print("🧪 TESTING ELECTRUM SERVERS WITH SPECIFIED ADDRESSES")
    print("=" * 80)
    
    # Test addresses
    print(f"\n📋 Test Addresses:")
    for i, addr in enumerate(TEST_ADDRESSES):
        print(f"   {i+1}. {addr}")
    
    # Create server manager
    server_manager = ElectrumServerManager()
    
    # Get verified servers
    print("\n🔍 Starting server verification...")
    verified_servers = await server_manager.get_fastest_servers(limit=5, verify=True)
    
    if verified_servers:
        print("\n" + "=" * 80)
        print("✅ SERVER VERIFICATION COMPLETE")
        print("=" * 80)
        print(f"\n📊 Found {len(verified_servers)} verified servers:")
        
        # Get detailed verification results
        verification_results = await server_manager.get_verification_results()
        
        for i, (server, resp_time) in enumerate(verification_results[:5]):
            print(f"\n   Server {i+1}: {server['host']}:{server['port']}")
            print(f"   Response Time: {resp_time:.1f}ms")
            
            # Test each address individually on this server
            print(f"   Test Address Balances:")
            
            ssl_ctx = server_manager._ssl_context
            try:
                async with connect_rs(server['host'], server['port'], ssl=ssl_ctx) as session:
                    for addr in TEST_ADDRESSES:
                        try:
                            scripthash = address_to_scripthash(addr)
                            response = await session.send_request(
                                "blockchain.scripthash.get_balance", 
                                [scripthash]
                            )
                            if isinstance(response, dict):
                                confirmed = response.get("confirmed", 0)
                                unconfirmed = response.get("unconfirmed", 0)
                                total = (confirmed + unconfirmed) / 100000000
                                print(f"      {addr[:15]}...: {total:.8f} BTC")
                            else:
                                print(f"      {addr[:15]}...: Failed to get balance")
                        except Exception as e:
                            print(f"      {addr[:15]}...: Error - {str(e)[:30]}")
            except Exception as e:
                print(f"   ❌ Failed to connect: {str(e)[:50]}")
    else:
        print("\n❌ No servers could be verified!")
    
    print("\n" + "=" * 80)
    return verified_servers

# ============================================================
# MAIN EXECUTION
# ============================================================

def run_async_workers(num_workers: int, queue: Queue, stats_queue: Queue):
    """Run async workers in a separate process"""
    try:
        # Set signal handlers
        signal.signal(signal.SIGINT, signal.SIG_IGN)
        
        # Create new event loop
        loop = asyncio.new_event_loop()
        asyncio.set_event_loop(loop)
        
        # Apply nest_asyncio
        try:
            nest_asyncio.apply(loop)
        except:
            pass
        
        # Run main async function
        loop.run_until_complete(main_async(num_workers, queue, stats_queue))
        loop.close()
    except Exception as e:
        print(f"❌ Error in worker process: {e}")

async def main_async(num_workers: int, queue: Queue, stats_queue: Queue):
    """Main async function"""
    # Create tasks dengan pengaturan yang lebih baik
    tasks = []
    for i in range(num_workers):
        task = asyncio.create_task(batch_worker(i, queue, stats_queue))
        tasks.append(task)
    
    # Wait for all tasks with proper cleanup
    try:
        await asyncio.gather(*tasks)
    except asyncio.CancelledError:
        # Cancel all tasks on shutdown
        for task in tasks:
            task.cancel()
        await asyncio.gather(*tasks, return_exceptions=True)
        raise

def main():
    """Main entry point"""
    # Apply nest_asyncio di main thread
    try:
        nest_asyncio.apply()
    except:
        pass
    
    # Run server test first
    print("\n" + "=" * 80)
    print("🔧 INITIALIZING BITCOIN PUZZLE 160 SOLVER")
    print("=" * 80)
    
    # Run server test
    loop = asyncio.new_event_loop()
    asyncio.set_event_loop(loop)
    verified_servers = loop.run_until_complete(test_servers_only())
    loop.close()
    
    if not verified_servers:
        print("\n⚠️  WARNING: No verified servers found! Proceeding with speed-tested servers only...")
        response = input("Continue? (y/n): ")
        if response.lower() != 'y':
            print("Exiting...")
            return
    
    # Get CPU info
    cpu_count = multiprocessing.cpu_count()
    num_workers = cpu_count * WORKERS_PER_CORE
    
    print("\n" + "=" * 80)
    print("🚀 BITCOIN PUZZLE 160 SOLVER - ULTRA HIGH PERFORMANCE")
    print("=" * 80)
    print("🔥 OPTIMIZED VERSION with Connection Pooling & Load Balancing")
    print("=" * 80)
    print(f"🔥 CPU Cores: {cpu_count}")
    print(f"🔥 Async Workers: {num_workers}")
    print(f"🔥 Producer Threads: {max(4, cpu_count)}")
    print(f"🔥 Batch Size: {BATCH_SIZE} addresses/request")
    print(f"🔥 Max Concurrent Batches: {MAX_CONCURRENT_BATCHES}")
    print(f"🔥 Connection Pool Size: 20 per server")
    print(f"🔥 Key Range: {hex(LOW)} - {hex(HIGH)}")
    print("=" * 80)
    
    # Create queue dengan size lebih besar
    queue = Queue(maxsize=QUEUE_SIZE)
    stats_queue = Queue()
    
    # Start producer
    producer_process = Process(target=producer, args=(queue,))
    producer_process.daemon = True
    producer_process.start()
    
    # Start async workers
    num_processes = max(1, cpu_count)  # Use all cores
    workers_per_process = max(1, num_workers // num_processes)
    
    print(f"📦 Creating {num_processes} processes with {workers_per_process} async workers each")
    
    processes = []
    for i in range(num_processes):
        p = Process(
            target=run_async_workers,
            args=(workers_per_process, queue, stats_queue)
        )
        p.daemon = True
        p.start()
        processes.append(p)
    
    # Monitor dengan update lebih sering
    try:
        last_queue_size = 0
        stuck_count = 0
        
        while True:
            time.sleep(2)  # Check every 2 seconds
            queue_size = queue.qsize()
            
            # Deteksi jika queue stuck
            if queue_size == last_queue_size:
                stuck_count += 1
                if stuck_count >= 5:  # Stuck for 10 seconds
                    print(f"\n⚠️  WARNING: Queue stuck at {queue_size}. Workers might be too slow!")
                    print(f"   Try reducing BATCH_SIZE or increasing workers.")
                    stuck_count = 0
            else:
                stuck_count = 0
            
            last_queue_size = queue_size
            
            # Tampilkan status
            print(f"\n📊 System Status - Queue: {queue_size}/{QUEUE_SIZE} | "
                  f"Processes: {len(processes)} | "
                  f"Usage: {queue_size/QUEUE_SIZE*100:.1f}%")
            
            # Jika queue hampir penuh, beri warning
            if queue_size > QUEUE_SIZE * 0.9:
                print(f"⚠️  Queue nearly full! Workers can't keep up!")
                
    except KeyboardInterrupt:
        print("\n\n🛑 Shutting down...")
        for p in processes:
            p.terminate()
        producer_process.terminate()

if __name__ == "__main__":
    multiprocessing.freeze_support()
    main()
