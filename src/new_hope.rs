use tiny_keccak::Keccak;
use std::rc::Rc;
use crate::finite_field::{FiniteField, FiniteFieldElement, FiniteFieldPolynomial};
//use std::convert::TryInto;

// argument sizes:
// NewHope-512 & NewHope-1024 specific: 64,32 128,34 64,32 32,32 32,32 32,64 96,64 32,64
// NewHope-512 specific: 32,928 96,960 32,1120 32,1120
// NewHope-1024 specific: 32,1824 96,1856 32,2208 32,2208
// set of possible argument sizes numbers: 32, 34, 64, 96, 128, 928, 960, 1120, 1824, 1856, 2208
fn shake256_64(d: [u8; 32], out: &mut [u8; 64]) {
    let mut hash = Keccak::new_shake256();
    hash.update(&d[..]);

    let mut res: [u8; 64] = [0; 64];
    hash.finalize(&mut res);
}

fn uniform_distribution_sample() -> [u8; 32] {
    return rand::random::<[u8; 32]>();
}

// Evaluate Number Theoretic Transform for given x ∈ ℤ_q^n w.r.t. to n-th primitive root of unity ∈ ℤ_q
pub fn ntt(x: FiniteFieldPolynomial, omega_n: FiniteFieldElement, n: u32) -> FiniteFieldPolynomial {
    let field = omega_n.field();
    let mut x_tilde = x.bit_rev(n);
    dbg!(&x_tilde);
    let mut m = 2;
    while m <= n {
        let omega_m = omega_n.pow(n/m);
        let mut omega = field.element(1);
        for j in 0..m/2 {
            let mut k = 0;
            while k < n {
                let t = omega * x_tilde.get((k + j + m/2) as usize);
                let u = x_tilde.get((k + j) as usize);
                x_tilde.set((k + j) as usize, u + t);
                x_tilde.set((k + j + m/2) as usize, u - t);
                k += m;
            }
            omega = omega * omega_m;
        }
        m *= 2;
    }
    x_tilde
}

#[derive(Clone,Copy,Debug)]
pub struct Parameters {
    pub n: u32,      // number of dimensions of the lattice
    pub q: u32,      // number of elements in the field
    pub gamma: u32,  // n-th primitive root of unity
}

impl Parameters {
    pub fn finite_field(&self) -> FiniteField {
        FiniteField { size: self.q }
    }
}

#[derive(Debug)]
pub struct NewHope<'a> {
    parameters: &'a Parameters,
}

impl<'a> NewHope<'a> {
    pub fn new(params: &'a Parameters) -> NewHope {
        NewHope{parameters: params}
    }

    // Algorithm 4: Deterministic sampling of polynomials in R_q from ψ_8^n
    /*fn sample(&mut self, seed: [u8; 32], nonce: u8) -> FiniteFieldPolynomial {
        let mut r = self.parameters.finite_field().element(0);

        let mut extseed = [u8; 34];
        extseed[0..32].copy_from_slice(&seed[..]);
        extseed[32] = nonce;
        for i in 0..n/64 {
            extseed[33] = i;
            let buf = self.shake256(128, extseed);
            for j in 0..64 {
                let a = buf[2 * j];
                let b = buf[2 * j + 1];
                r[64 * i + j] = (a.count_ones() + q - b.count_ones()) % q;
            }
        }

        r
    }

    fn nnt(&self) -> FiniteFieldPolynomial {
        // TODO
        self.parameters.finite_field().element(3)
    }

    // Algorithm 6: Encoding of a polynomial in R_q to a byte array
    fn encode_polynomial(&self, s_hat: &FiniteFieldPolynomial) -> Vec<u8> {
        let mut r = [0u8; (7 * n) / 4];
        for i in 0..self.parameters.n/4 {
            let t0 = s_hat[4*i + 0] % self.parameters.q;
            let t1 = s_hat[4*i + 1] % self.parameters.q;
            let t2 = s_hat[4*i + 2] % self.parameters.q;
            let t3 = s_hat[4*i + 3] % self.parameters.q;
            r[7*i + 0] = t0 & 0xFF;
            r[7*i + 1] = (t0 >> 8) | (t1 << 6) & 0xFF;
            r[7*i + 2] = (t1 >> 2) & 0xFF;
            r[7*i + 3] = (t1 >> 10) | (t2 << 4) & 0xFF;
            r[7*i + 4] = (t2 >> 4) & 0xFF;
            r[7*i + 5] = (t2 >> 12) | (t3 << 2) & 0xFF;
            r[7*i + 6] = (t3 >> 6) & 0xFF;
        }
        r
    }

    // Algorithm 8: Encoding of the public key
    fn encode_pk_512(&self, b_hat: &FiniteFieldPolynomial, public_seed: [u8; 32]) -> [u8; 928] {
        let mut r = [0u8; 928];
        r[0..896] = self.encode_polynomial(b_hat);
        r[896..928] = public_seed[0..32];
        r
    }

    fn encode_pk_1024(&self, b_hat: &FiniteFieldPolynomial, public_seed: [u8; 32]) -> [u8; 1824] {
        let mut r = [0u8; 1824];
        r[0..1792] = self.encode_polynomial(b_hat);
        r[1792..1824] = public_seed[0..32];
        r
    }

    // Algorithm 5: Deterministic generation of â by expansion of a seed
    fn gen_a(&self, seed: &[u8; 32]) -> FiniteFieldPolynomial {
        let mut a_hat = self.parameters.finite_field().element(0);
        extseed = rand::random::<[u8; 33]>();
        extseed[0:32] = seed[0:32];
        for i in 0..n/64 {
            let mut ctr = 0;
            extseed[32] = i;
            state = shake128_absorb(extseed);
            while ctr < 64 {
                let buf, state = shake128_squeeze(1, state);
                j = 0;
                while j < 168 && ctr < 64 {
                    let val = buf[j] | (buf[j+1] << 8);
                    if val < 5 * q {
                        a_hat.set(i * 64 + ctr, val);
                        ctr = ctr + 1;
                    }
                    j = j + 2;
                }
            }
        }
        a_hat
    }

    // Algorithm 1: NewHope-CPA-PKE Key Generation
    fn cpa_pke_gen(&mut self,) -> (FiniteFieldPolynomial, Vec<u8>) {
        let seed = uniform_distribution_sample();
        println!("seed: {:?}", seed);

        let z: [u8; 64] = [0; 64];

        shake256_64(seed, &mut z);
        let public_seed_slice: &[u8] = &(z[0..31]);
        let public_seed: &[u8; 32] = public_seed_slice.try_into().expect("slice with incorrect length");
        let noise_seed_slice: &[u8] = &(z[32..63]);
        let noise_seed: &[u8; 32] = noise_seed_slice.try_into().expect("slice with incorrect length");
        let a_hat = self.gen_a(public_seed);
        let s = self.sample(noise_seed, 0).bit_rev();
        let s_hat = self.ntt(s);
        let e = self.sample(noise_seed, 1).bit_rev();
        let e_hat = self.ntt(e);
        let b_hat = a_hat.coeff_mul(s_hat) + e_hat;

        return (self.encode_pk(b_hat, public_seed), self.encode_polynomial(s_hat));
    }

    // Algorithm 2: NewHope-CPA-PKE Encryption
    fn cpa_pke_encrypt_512(&mut self, pk: [u8; 928], mu: [u8; 32], coin: [u8; 32]) {
        let (b_hat, publicseed) = self.decode_pk(pk);
        let a_hat = self.gen_a(publicseed);
        let s_prime = self.poly_bit_rev(self.sample(coin, 0));
        let e_prime = self.poly_bit_rev(self.sample(coin, 0));
        let e_primeprime = self.sample(coin, 2);
        let t_hat = self.ntt(s_prime);
        let u_hat = a_hat.coeff_mul(t_hat) + self.ntt(e_prime);
        let v = self.encode(mu);
        let v_prime = self.intt(b_hat.coeff_mul(t_hat)) + e_primeprime + v;
        let h = self.compress(v_prime);
        self.encodeC(u_hat, h)
    }

    fn cpa_pke_encrypt_1024(&mut self, pk: [u8; 1824], mu: [u8; 32], coin: [u8; 32]) {
        let (b_hat, publicseed) = self.decode_pk(pk);
        let a_hat = self.gen_a(publicseed);
        let s_prime = self.poly_bit_rev(self.sample(coin, 0));
        let e_prime = self.poly_bit_rev(self.sample(coin, 0));
        let e_primeprime = self.sample(coin, 2);
        let t_hat = self.ntt(s_prime);
        let u_hat = a_hat.coeff_mul(t_hat) + self.ntt(e_prime);
        let v = self.encode(mu);
        let v_prime = self.intt(b_hat.coeff_mul(t_hat)) + e_primeprime + v;
        let h = self.compress(v_prime);
        self.encodeC(u_hat, h)
    }

    // Algorithm 3: NewHope-CPA-PKE Decryption
    fn cpa_pke_decrypt_512(&mut self, c: [u8; 1088], sk: [u8; 896]) {
        let (u_hat, h) = self.decode_c(c);
        let s_hat = self.decode_polynomial(sk);
        let v_prime = self.decompress(h);
        let mu = self.decode(v_prime - self.intt(u_hat.coeff_mul(s_hat)));
        mu
    }

    fn cpa_pke_decrypt_1024(&mut self, c: [u8; 2176], sk: [u8; 1792]) {
        let (u_hat, h) = self.decode_c(c);
        let s_hat = self.decode_polynomial(sk);
        let v_prime = self.decompress(h);
        let mu = self.decode(v_prime - self.intt(u_hat.coeff_mul(s_hat)));
        mu
    }

    // Algorithm 14: Ciphertext decoding
    fn decode_c(&self, c: &FiniteFieldElement) -> (FiniteFieldPolynomial, FiniteFieldElement) {
        // NOTE c has size 1088 or 2176
        let u = self.decode_polynomial(&c[0:896]); // NOTE either 896 or 1792
        let h = c[896:1088];  // NOTE either 896:1088 or 1792:2176
        (u, h)
    }

    // Algorithm 12: Ciphertext compression
    fn compress_512(&self, v_prime: &FiniteFieldElement) -> [u8; 192] {
        let mut k = 0;
        let mut t = [0u8; 8];
        let mut h = [0u8; 192];
        let q = self.parameters.q;
        for l in 0..64 {
            let i = 8 * l;
            for j in 0..7 {
                t[j] = v_prime[i + j] % q;
                t[j] = (((t[j] << 3) + q/2) / q) & 7;
            }
            h[k + 0] = t[0] | (t[1] << 3) | (t[2] << 6);
            h[k + 1] = (t[2] >> 2) | (t[3] << 1) | (t[4] << 4) | (t[5] << 7);
            h[k + 2] = (t[5] >> 1) | (t[6] << 2) | (t[7] << 5);
            k += 3;
        }
        h
    }

    fn compress_1024(&self, v_prime: &FiniteFieldElement) -> [u8; 384] {
        let mut k = 0;
        let mut t = [0u8; 8];
        let mut h = [0u8; 384];
        let q = self.parameters.q;
        for l in 0..128 {
            let i = 8 * l;
            for j in 0..7 {
                t[j] = v_prime[i + j] % q;
                t[j] = (((t[j] << 3) + q/2) / q) & 7;
            }
            h[k + 0] = t[0] | (t[1] << 3) | (t[2] << 6);
            h[k + 1] = (t[2] >> 2) | (t[3] << 1) | (t[4] << 4) | (t[5] << 7);
            h[k + 2] = (t[5] >> 1) | (t[6] << 2) | (t[7] << 5);
            k += 3;
        }
        h
    }

    // Algorithm 15: Ciphertext decompression
    fn decompress_512(&self, h: &FiniteFieldElement) -> FiniteFieldElement {
        let mut k = 0;
        let mut r = FiniteFieldPolynomial::new<192>();
        for l in 0..64 {
            let i = 8 * l;
            r.set(i + 0, h[k+0] & 7);
            r.set(i + 1, (h[k+0] >> 3) & 7);
            r.set(i + 2, (h[k+0] >> 6) | ((h[k+1] << 2) & 4));
            r.set(i + 3, (h[k+1] >> 1) & 7);
            r.set(i + 4, (h[k+1] >> 4) & 7);
            r.set(i + 5, (h[k+1] >> 7) | ((h[k+2] << 1) & 6));
            r.set(i + 6, (h[k+2] >> 2) & 7);
            r.set(i + 7, h[k+2] >> 5);
            k += 3;
            for j in 0..8 {
                r.set(i + j, (r.get(i + j) * q + 4) >> 3);
            }
        }
        r
    }

    fn decompress_1024(&self, h: &FiniteFieldElement) -> FiniteFieldElement {
        let mut k = 0;
        let mut r = FiniteFieldPolynomial::new<384>();
        for l in 0..64 {
            let i = 8 * l;
            r.set(i + 0, h[k+0] & 7);
            r.set(i + 1, (h[k+0] >> 3) & 7);
            r.set(i + 2, (h[k+0] >> 6) | ((h[k+1] << 2) & 4));
            r.set(i + 3, (h[k+1] >> 1) & 7);
            r.set(i + 4, (h[k+1] >> 4) & 7);
            r.set(i + 5, (h[k+1] >> 7) | ((h[k+2] << 1) & 6));
            r.set(i + 6, (h[k+2] >> 2) & 7);
            r.set(i + 7, h[k+2] >> 5);
            k += 3;
            for j in 0..8 {
                r.set(i + j, (r.get(i + j) * q + 4) >> 3);
            }
        }
        r
    }

    // Algorithm 7: Decoding of a polynomial represented as a byte array into an element in R_q
    fn decode_polynomial_512(&self, v: &FiniteFieldElement) -> FiniteFieldPolynomial {
        for i in 0..128 {
            let mut r = FiniteFieldPolynomial::new<128>();
            r.set(4*i + 0, append(b2i(v[7*i + 0]), ((b2i(v[7*i + 1]) & 0x3F) << 8)));
            r.set(4*i + 1, append(b2i(v[7*i + 1]) >> 6, b2i(v[7*i + 2]) << 2, (b2i(v[7*i + 3]) & 0x0F) << 10));
            r.set(4*i + 2, append(b2i(v[7*i + 3]) >> 4, b2i(v[7*i + 4]) << 4, (b2i(v[7*i + 5]) & 0x03) << 12));
            r.set(4*i + 3, append(b2i(v[7*i + 5]) >> 2, b2i(v[7*i + 6]) << 6));
        }
        r
    }

    fn decode_polynomial_1024(&self, v: &FiniteFieldElement) -> FiniteFieldPolynomial {
        for i in 0..256 {
            let mut r = FiniteFieldPolynomial::new<128>();
            r.set(4*i + 0, append(b2i(v[7*i + 0]), ((b2i(v[7*i + 1]) & 0x3F) << 8)));
            r.set(4*i + 1, append(b2i(v[7*i + 1]) >> 6, b2i(v[7*i + 2]) << 2, (b2i(v[7*i + 3]) & 0x0F) << 10));
            r.set(4*i + 2, append(b2i(v[7*i + 3]) >> 4, b2i(v[7*i + 4]) << 4, (b2i(v[7*i + 5]) & 0x03) << 12));
            r.set(4*i + 3, append(b2i(v[7*i + 5]) >> 2, b2i(v[7*i + 6]) << 6));
        }
        r
    }

    fn decryption_512(&self, c: &FiniteFieldElement<544>, sk: &FiniteFieldElement<896>) -> FiniteFieldPolynomial {
        let (u, h) = self.decode_c(c);
        let s = self.decode_polynomial_512(&sk);
        let v = self.decompress_512(&h);
        let mu = self.decode(v - INTT(u.coeff_mul(s)));
        mu
    }

    fn decryption_1024(&self, c: &FiniteFieldElement<1088>, sk: &FiniteFieldElement<3584>) -> FiniteFieldPolynomial {
        let (u, h) = self.decode_c(c);
        let s = self.decode_polynomial_512(&sk);
        let v = self.decompress_512(&h);
        let mu = self.decode(v - INTT(u.coeff_mul(s)));
        mu
    }

    // Algorithm 13: Ciphertext encoding
    fn encode_c_512(&self, u_hat: FiniteFieldPolynomial, h: [u8; 192]) -> [u8; 1088] {
        let mut c = [0u8; 1088];
        c[0..896] = self.encode_polynomial(u_hat);
        c[896..1087] = h;
        c
    }

    fn encode_c_1024(&self, u_hat: FiniteFieldPolynomial, h: [u8; 384]) -> [u8; 2176] {
        let mut c = [0u8; 2176];
        c[0..1792] = self.encode_polynomial(u_hat);
        c[1792..2176] = h;
        c
    }

    // Algorithm 9: Decoding of the public key
    fn decode_pk(&self, pk: [u8; 7*n/4+32]) -> (FiniteFieldPolynomial, [u8; 32]) {
        let b_hat = self.decode_polynomial(pk[0:7*n/4]);
        let seed = pk[7*n/4:7*n/4+32];
        (b_hat, seed)
    }

    // Algorithm 10: Message encoding
    fn encode(&self, mu: [u8; 32]) -> FiniteFieldPolynomial {
        let mut v = self.parameters.finite_field().element(0);
        for i in 0..32 {
            for j in 0..8 {
                let mask = -((msg[i] >> j) & 1);
                v[8*i + j + 0] = mask & (q/2);
                v[8*i + j + 256] = mask & (q/2);
                if self.parameters.n == 1024 {
                    v[8*i + j + 512] = mask & (q/2);
                    v[8*i + j + 768] = mask & (q/2);
                }
            }
        }
        v
    }

    // Algorithm 11: Message decoding
    fn decode(&self, v: FiniteFieldPolynomial) -> [u8; 32] {
        let mut mu = [0u8; 32];
        let q = self.parameters.q;
        let qh = (q - 1) / 2;
        for i in 0..256 {
            let mut t = ((v[i+0] % q) - qh) % q + ((v[i + 256] % q) - qh);
            if self.parameters.n == 1024 {
                t += ((v[i + 512] & q) - qh) % q + ((v[i + 768] & q) - qh) % q;
                t = t - q;
            } else {
                t = t - q/2;
            }
            t = t >> 15;
            mu[i >> 3] = mu[i >> 3] | (t << (i & 7));
        }
        mu
    }

    // Algorithm 16: NewHope-CPA-KEM Key Generation
    fn cpa_kem_gen_512(&self) -> (FiniteFieldPolynomial, Vec<u8>) {
        self.cpa_pke_gen_512()
    }

    fn cpa_kem_gen_1024(&self) -> (FiniteFieldPolynomial, Vec<u8>) {
        self.cpa_pke_gen_1024()
    }

    // Algorithm 20: NewHope-CCA-KEM Encapsulation
    fn cpa_kem_encaps_512(&self, pk: [u8; 928]) {
        let coin = rand::random::<[u8; 32]>();
        let mu = shake256(32, coin);
        let (k || coin' || d) = shake256(96, mu || shake256(32, pk));
        let c = cpa_pke_encrypt_512(pk, mu, coin');
        let ss = shake256(32, k || shake256(32, c || d));
        (c || d, ss)
    }

    fn cpa_kem_encaps_1024(&self, pk: [u8; 1824]) {
        let coin = rand::random::<[u8; 32]>();
        let mu = shake256(32, coin);
        let (k || coin' || d) = shake256(96, mu || shake256(32, pk));
        let c = cpa_pke_encrypt_512(pk, mu, coin');
        let ss = shake256(32, k || shake256(32, c || d));
        (c || d, ss)
    }

    // Algorithm 21: NewHope-CCA-KEM Decapsulation
    fn cpa_kem_decaps_512(&self, c: [u8; 1020], sk: [u8; 896]) {
        let c||d = c;
        sk||pk||h||s = sk;
        let mu_prime = cpa_pke_decrypt_512(c, sk);
        let K_prime||coin_primeprime||d_prime = shake256(96, mu_prime||h);
        let K = [0u8; 32*2];
        K[0..32] = K_prime;
        K[32..64] = s;
        let fail = if c == cpa_pke_encrypt_512(pk, mu_prime, coin_primeprime) && d == d_prime {
            0
        } else {
            1
        };
        shake256(32, K[32 * fail .. 32 * (fail + 1)] || shake256(32, c || d))
    }

    fn cpa_kem_decaps_1024(&self, c: [u8; 2208], sk: [u8; 1792]) {
    }*/
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ntt_1() {
        let q = 12289;
        let n = 512;
        let result = ntt(FiniteFieldPolynomial::new(q, vec![FiniteFieldElement::new(q, 1)]), FiniteFieldElement::new(q, 3), n);
        let expected = FiniteFieldPolynomial::new(q, vec![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1].iter().map(|v: &u32| FiniteFieldElement::new(q, *v)).collect());
        assert_eq!(result, expected);
    }

    #[test]
    fn test_ntt_2() {
        let q = 12289;
        let n = 512;
        let one = FiniteFieldElement::new(q, 1);
        let result = ntt(FiniteFieldPolynomial::new(q, vec![one, one, FiniteFieldElement::new(q, 42)]), FiniteFieldElement::new(q, 3), n);
        let expected = FiniteFieldPolynomial::new(q, vec![44,382,3412,6068,5286,10213,4428,10892,11164,11946,1697,5063,2664,5884,10985,9835,5776,407,8705,7464,2017,7027,5303,9102,2926,10576,11059,6929,5773,5099,3645,4395,3497,9338,5364,8882,10928,1939,10875,4429,5319,5706,10898,1308,4113,1767,8481,4923,2151,3508,8613,8656,6516,4253,10299,8773,11554,105,8832,4853,4123,4484,3948,58,4717,5898,4878,9907,11772,8970,11014,595,4714,3652,2585,6166,4213,6980,6892,4861,7443,7241,8837,8865,2976,5286,7674,10827,8765,9491,143,3544,1816,12143,10677,9192,6376,390,4590,7699,5341,3703,10846,5609,7973,5694,541,238,554,238,203,8315,8292,10194,9061,5556,6376,250,2910,3608,1609,7931,2589,1282,6942,11839,3806,8682,1438,4060,9910,9316,3995,5337,5351,6152,3097,6255,3746,11262,9440,5846,11912,9696,3657,3310,2442,1395,12267,11243,347,7844,11041,6743,4027,1458,7095,8923,1550,11186,6375,7985,9734,11830,2048,118,7581,1779,1012,994,9198,9820,4689,57,9276,11477,10178,8897,4020,4661,8853,4983,5116,601,4275,10511,10723,4652,12099,7311,6855,7769,6471,3084,9775,9470,9488,5650,8264,8079,9015,664,10359,8084,1666,10653,9136,6352,1614,7637,11215,2131,5430,7639,6519,7170,8355,4998,6453,3951,8376,6140,7301,7871,7942,5693,1366,10165,11380,9589,4448,3402,6767,1655,9213,4442,1193,4999,3215,1935,10165,8306,9568,1171,1512,11121,6621,403,10420,3574,7344,3935,8705,10520,1822,8198,42,376,3394,6014,5124,9727,2970,6518,10331,9447,6489,7150,8925,89,5889,6836,9068,10283,1466,10325,10600,8198,8816,7352,9965,7115,676,358,10638,7405,10563,571,4314,11789,428,6363,3371,3846,4307,9303,7652,416,7317,2854,8751,3392,1067,7259,9159,12243,10240,1248,8870,11315,6907,10886,5604,6833,4438,3960,1444,8736,4415,1459,8920,6218,5838,498,8123,10312,2751,384,4081,1753,9177,1364,2096,629,128,9147,8012,8948,1669,11939,12198,8374,4649,1752,6118,1550,898,5809,8611,7950,10387,8322,3766,4849,5678,10963,2844,8501,662,11924,2340,1084,11289,7904,11263,7787,10561,2522,3202,7213,118,3305,11912,4569,3578,5612,7621,1389,7541,3849,2354,10364,11670,7696,10769,7475,7866,3184,10177,11594,11833,1020,12279,9223,361,1107,3553,474,8085,10504,6081,10582,11969,5398,11987,10403,10116,284,650,148,8820,3548,1076,3155,8824,8430,10396,7759,9056,9796,8235,6390,1819,9071,10599,5177,9458,10600,7029,7077,5758,923,3094,12223,1709,10017,343,4031,2260,4322,3149,7133,589,11117,6916,4051,9364,3007,4474,9382,4091,4707,7488,11939,2553,3235,6772,6224,2461,8968,4318,6320,8426,4222,7513,756,2861,1647,3978,3283,5740,4833,1344,8543,4799,11278,5779,10638,8506,11486,6498,1361,659,8044,5017,2789,8626,3647,7502,3860,3539,11998,11572,11558,10603,11810,2923,11158,5835,2261,4782,8642,11473,2670,4932,11688,7108,3227,6581,4148,7284,6].iter().map(|v: &u32| FiniteFieldElement::new(q, *v)).collect());
        assert_eq!(result, expected);
    }

    #[test]
    fn test_ntt_3() {
        let q = 12289;
        let n = 512;
        let to_ffe = |v: Vec<u32>| v.iter().map(|v: &u32| FiniteFieldElement::new(q, *v)).collect();
        let poly = FiniteFieldPolynomial::new(q, to_ffe(vec![123, 804, 22, 91]));
        let result = ntt(poly, FiniteFieldElement::new(q, 3), n);
        let expected = FiniteFieldPolynomial::new(q, to_ffe(vec![1040,5190,1746,10250,4592,2735,4946,10064,9225,818,11756,250,4647,10139,1416,4976,7903,9719,1680,4782,7030,2731,4746,11354,3929,6758,7339,2185,574,7484,9951,8700,2280,10915,5528,10775,7773,8306,4547,1650,11352,5767,9600,8,9480,2189,6007,9140,1529,11971,4334,4616,10237,7128,10990,4861,2553,485,10045,3804,9497,2559,4440,2596,766,6227,8820,5050,4164,326,6279,5726,65,11976,8116,4778,7641,832,8244,6266,7509,9112,12146,6984,7631,1142,9870,2736,4374,899,759,482,211,9387,2370,9361,8618,5009,10954,9379,10719,9531,3699,2644,11891,5955,11653,1481,11803,3257,11167,5143,5091,6628,6766,47,11256,7174,11014,7451,5783,9068,5441,1937,6180,10956,12257,5087,10063,7104,8950,3503,9107,7507,4272,2671,7629,2197,4368,6267,3621,5463,6352,9370,2685,6628,275,8320,6976,8007,6774,5687,4799,5852,8588,7723,2491,7472,6632,2908,10938,11174,4813,10007,12060,9855,3456,9091,7230,1689,12075,9942,8528,2962,5301,11684,2682,1110,10641,26,10272,11441,3653,12275,1842,9619,11317,3470,2740,9351,1194,1002,7704,6094,7046,1859,12184,4722,1220,7483,10491,9485,2383,10167,8619,1977,658,9190,5970,4055,4330,11144,941,4764,1908,7900,219,929,2065,10407,12195,9714,8681,4391,874,1994,8370,3601,5973,5646,9448,10873,5110,11862,6509,10091,7615,11124,3074,7358,3417,10741,9994,5753,10009,1722,8584,7884,10209,3267,3724,11721,5790,4267,3793,5771,11539,7741,2064,9783,1691,2688,5026,3982,4620,11218,8577,8733,498,9620,2401,2831,11236,807,5063,4781,3335,2563,4065,4532,1898,6850,2564,11240,7682,3407,77,5850,3812,5078,1262,11500,6399,6673,5406,12225,954,4707,8964,5343,12133,6025,4506,9775,6981,1206,1690,10765,3334,2442,11727,1000,11361,12172,3588,6324,5953,11633,10719,8977,3111,2120,2890,60,2991,656,591,4980,8298,12167,10579,1752,5,4569,1530,5998,2587,6050,11743,9425,2903,5673,341,1172,4252,1033,2372,1151,229,4894,1301,9421,10984,9684,8714,5908,2006,4714,11937,933,6045,6033,8248,3614,7506,8799,9346,5460,2345,9172,10576,6595,9687,7299,6674,2305,6319,11859,8888,2166,4201,6771,10139,10174,2428,5035,21,1534,9680,12140,10826,8353,3596,10837,369,9820,4015,12137,2612,7893,3246,7916,5763,7187,7729,11769,9485,3497,2155,5610,6579,3922,2034,6707,8410,7612,8040,10192,1178,5077,11127,236,11661,2104,5534,618,6720,9777,7218,1605,9256,6760,1589,10783,8405,9663,1227,4059,10989,6934,9314,2794,120,11472,6880,1527,8717,206,1200,10629,6314,5812,5731,7077,4691,6881,6216,3731,3992,8373,8805,5403,2349,3616,9004,5853,9140,9806,1306,1202,662,973,3936,9920,7585,741,146,1075,429,1897,4594,8383,9321,6182,6372,5179,12275,10620,2024,1220,10949,9884,10435,1890,1483,7109,1928,10818,10023,386,6407,8875,11087,7430,2759,876,7017,9246,8899,3076,11170,4038]));
        assert_eq!(result, expected);
    }
}