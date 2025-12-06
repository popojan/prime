// Prime DNA - JavaScript implementation
// Compact prime storage for web embedding

class PrimeDNA {
  constructor() {
    this.firstPrime = 2;
    this.halfGaps = null; // Uint8Array
  }

  // Encode primes to DNA
  encode(primes) {
    if (primes.length < 2) {
      this.firstPrime = primes[0] || 2;
      this.halfGaps = new Uint8Array(0);
      return;
    }

    this.firstPrime = primes[0];
    this.halfGaps = new Uint8Array(primes.length - 1);

    // First gap raw (handles 2→3 = 1)
    this.halfGaps[0] = primes[1] - primes[0];

    // Rest as gap/2
    for (let i = 2; i < primes.length; i++) {
      this.halfGaps[i - 1] = (primes[i] - primes[i - 1]) / 2;
    }
  }

  // Decode DNA to primes
  decode() {
    const primes = new Array(this.halfGaps.length + 1);
    let p = this.firstPrime;
    primes[0] = p;

    if (this.halfGaps.length > 0) {
      p += this.halfGaps[0]; // First gap raw
      primes[1] = p;

      for (let i = 1; i < this.halfGaps.length; i++) {
        p += 2 * this.halfGaps[i];
        primes[i + 1] = p;
      }
    }

    return primes;
  }

  // Export to base64
  toBase64() {
    // Header: firstPrime (4 bytes) + data
    const header = new Uint8Array(4);
    const view = new DataView(header.buffer);
    view.setUint32(0, this.firstPrime, true);

    const combined = new Uint8Array(4 + this.halfGaps.length);
    combined.set(header);
    combined.set(this.halfGaps, 4);

    return btoa(String.fromCharCode(...combined));
  }

  // Import from base64
  fromBase64(b64) {
    const binary = atob(b64);
    const bytes = new Uint8Array(binary.length);
    for (let i = 0; i < binary.length; i++) {
      bytes[i] = binary.charCodeAt(i);
    }

    const view = new DataView(bytes.buffer);
    this.firstPrime = view.getUint32(0, true);
    this.halfGaps = bytes.slice(4);

    return this;
  }

  // Number of primes
  get count() {
    return this.halfGaps.length + 1;
  }

  // Get nth prime (0-indexed)
  getNth(n) {
    if (n === 0) return this.firstPrime;
    if (n > this.halfGaps.length) return null;

    let p = this.firstPrime;
    p += this.halfGaps[0]; // First gap
    if (n === 1) return p;

    for (let i = 1; i < n; i++) {
      p += 2 * this.halfGaps[i];
    }
    return p;
  }

  // Check if number is prime (binary search)
  isPrime(n) {
    if (n < 2) return false;
    if (n === 2) return true;
    if (n % 2 === 0) return false;

    const primes = this.decode();
    let lo = 0, hi = primes.length - 1;

    while (lo <= hi) {
      const mid = (lo + hi) >> 1;
      if (primes[mid] === n) return true;
      if (primes[mid] < n) lo = mid + 1;
      else hi = mid - 1;
    }

    return false;
  }
}

// Simple sieve for generating test data
function sievePrimes(limit) {
  const sieve = new Uint8Array(limit + 1);
  sieve.fill(1);
  sieve[0] = sieve[1] = 0;

  for (let i = 2; i * i <= limit; i++) {
    if (sieve[i]) {
      for (let j = i * i; j <= limit; j += i) {
        sieve[j] = 0;
      }
    }
  }

  const primes = [];
  for (let i = 2; i <= limit; i++) {
    if (sieve[i]) primes.push(i);
  }
  return primes;
}

// Demo / Test
if (typeof window === 'undefined') {
  // Node.js test
  const limit = 100000;
  console.log(`Generating primes up to ${limit}...`);

  const primes = sievePrimes(limit);
  console.log(`Found ${primes.length} primes`);

  const dna = new PrimeDNA();
  dna.encode(primes);

  const b64 = dna.toBase64();
  console.log(`Base64 length: ${b64.length} chars`);
  console.log(`First 100 chars: ${b64.slice(0, 100)}...`);

  // Decode and verify
  const dna2 = new PrimeDNA().fromBase64(b64);
  const decoded = dna2.decode();

  const correct = decoded.length === primes.length &&
    decoded.every((p, i) => p === primes[i]);
  console.log(`Correct: ${correct}`);

  // isPrime test
  console.log(`isPrime(97): ${dna2.isPrime(97)}`);
  console.log(`isPrime(98): ${dna2.isPrime(98)}`);
  console.log(`isPrime(99991): ${dna2.isPrime(99991)}`);
}

// Export for browser/Node
if (typeof module !== 'undefined') {
  module.exports = { PrimeDNA, sievePrimes };
}
