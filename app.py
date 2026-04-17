from flask import Flask, render_template, request, url_for
from math import gcd
import numpy as np
import random
import struct
import math


app = Flask(__name__)

alphabet = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
char_to_index = {alphabet[i]: i for i in range(26)}
index_to_char = {i: alphabet[i] for i in range(26)}


# ============================================================
#                    VIGENERE CIPHER
# ============================================================
def vigenere_encrypt_full(plain, key):
    steps = []
    j = 0
    for ch in plain.upper():
        if ch in char_to_index:
            p = char_to_index[ch]
            k = char_to_index[key[j % len(key)].upper()]
            c = (p + k) % 26
            steps.append({
                "p": ch, "pval": p,
                "k": key[j % len(key)].upper(), "kval": k,
                "c": index_to_char[c], "cval": c
            })
            j += 1
    return "".join(s["c"] for s in steps), steps


def vigenere_decrypt_full(cipher, key):
    steps = []
    j = 0
    for ch in cipher.upper():
        if ch in char_to_index:
            c = char_to_index[ch]
            k = char_to_index[key[j % len(key)].upper()]
            p = (c - k) % 26
            steps.append({
                "c": ch, "cval": c,
                "k": key[j % len(key)].upper(), "kval": k,
                "p": index_to_char[p], "pval": p
            })
            j += 1
    return "".join(s["p"] for s in steps), steps


# ============================================================
#                    PLAYFAIR CIPHER
# ============================================================
def generate_key_matrix(key):
    key = key.upper().replace("J", "I")
    seen = set()
    matrix = []
    for ch in key:
        if ch.isalpha() and ch not in seen:
            matrix.append(ch)
            seen.add(ch)
    for ch in "ABCDEFGHIKLMNOPQRSTUVWXYZ":
        if ch not in seen:
            matrix.append(ch)
    return [matrix[i*5:(i+1)*5] for i in range(5)]


def find_pos(m, ch):
    for i in range(5):
        for j in range(5):
            if m[i][j] == ch:
                return i, j
    return None, None


def preprocess_playfair(text):
    text = text.upper().replace("J", "I")
    text = ''.join(c for c in text if c.isalpha())
    res = ""
    i = 0
    while i < len(text):
        a = text[i]
        b = text[i+1] if i+1 < len(text) else 'X'
        if a == b:
            res += a + 'X'
            i += 1
        else:
            res += a + b
            i += 2
    if len(res) % 2 == 1:
        res += 'X'
    return res


def playfair_encrypt_full(text, matrix):
    text = preprocess_playfair(text)
    steps = []
    res = ""
    for i in range(0, len(text), 2):
        a, b = text[i], text[i+1]
        ra, ca = find_pos(matrix, a)
        rb, cb = find_pos(matrix, b)
        if ra == rb:
            rule = "Same Row"
            c1 = matrix[ra][(ca+1) % 5]
            c2 = matrix[rb][(cb+1) % 5]
        elif ca == cb:
            rule = "Same Column"
            c1 = matrix[(ra+1) % 5][ca]
            c2 = matrix[(rb+1) % 5][cb]
        else:
            rule = "Rectangle"
            c1 = matrix[ra][cb]
            c2 = matrix[rb][ca]
        res += c1 + c2
        steps.append({
            "pair": a + b,
            "pos": f"({ra},{ca}) ({rb},{cb})",
            "rule": rule,
            "out": c1 + c2
        })
    return res, steps


def playfair_decrypt_full(text, matrix):
    text = text.upper().replace("J", "I")
    text = ''.join(c for c in text if c.isalpha())
    steps = []
    res = ""
    for i in range(0, len(text), 2):
        a, b = text[i], text[i+1]
        ra, ca = find_pos(matrix, a)
        rb, cb = find_pos(matrix, b)
        if ra == rb:
            rule = "Same Row"
            p1 = matrix[ra][(ca-1) % 5]
            p2 = matrix[rb][(cb-1) % 5]
        elif ca == cb:
            rule = "Same Column"
            p1 = matrix[(ra-1) % 5][ca]
            p2 = matrix[(rb-1) % 5][cb]
        else:
            rule = "Rectangle"
            p1 = matrix[ra][cb]
            p2 = matrix[rb][ca]
        res += p1 + p2
        steps.append({
            "pair": a + b,
            "pos": f"({ra},{ca}) ({rb},{cb})",
            "rule": rule,
            "out": p1 + p2
        })
    return res, steps


# ============================================================
#                    AFFINE CIPHER
# ============================================================
def egcd(a, b):
    if b == 0:
        return a, 1, 0
    g, x1, y1 = egcd(b, a % b)
    return g, y1, x1 - (a // b) * y1


def modinv(a, m):
    g, x, y = egcd(a, m)
    return None if g != 1 else x % m


def is_valid_affine_a(a):
    return gcd(a, 26) == 1


def get_valid_a_values():
    return [i for i in range(1, 26) if gcd(i, 26) == 1]


def affine_encrypt_full(text, a, b):
    steps = []
    for ch in text.upper():
        if ch in char_to_index:
            p = char_to_index[ch]
            ap = a * p
            apb = ap + b
            c = apb % 26
            steps.append({
                "p": ch, "pval": p,
                "ap": ap, "apb": apb,
                "c": index_to_char[c], "cval": c
            })
    return "".join(s["c"] for s in steps), steps


def affine_decrypt_full(text, a, b):
    inv = modinv(a, 26)
    if inv is None:
        return None, [], None
    steps = []
    res = ""
    for ch in text.upper():
        if ch in char_to_index:
            c = char_to_index[ch]
            cmb = c - b
            mul = inv * cmb
            p = mul % 26
            res += index_to_char[p]
            steps.append({
                "c": ch, "cval": c,
                "cmb": cmb, "inv": inv,
                "mul": mul, "mod": p,
                "p": index_to_char[p]
            })
    return res, steps, inv


# ============================================================
#                    HILL CIPHER
# ============================================================
def hill_encrypt(text, key_matrix):
    text = text.upper().replace(" ", "")
    text = ''.join(c for c in text if c.isalpha())
    n = len(key_matrix)
    
    while len(text) % n != 0:
        text += 'X'
    
    steps = []
    result = ""
    
    for i in range(0, len(text), n):
        block = text[i:i+n]
        block_nums = [char_to_index[c] for c in block]
        
        encrypted_nums = []
        calc_details = []
        for row_idx, row in enumerate(key_matrix):
            val = sum(row[j] * block_nums[j] for j in range(n))
            calc_str = " + ".join([f"{row[j]}×{block_nums[j]}" for j in range(n)])
            calc_details.append(f"Row{row_idx}: {calc_str} = {val} mod 26 = {val % 26}")
            encrypted_nums.append(val % 26)
        
        encrypted_block = ''.join(index_to_char[num] for num in encrypted_nums)
        result += encrypted_block
        
        steps.append({
            "block": block,
            "block_nums": block_nums,
            "calculations": calc_details,
            "encrypted_nums": encrypted_nums,
            "encrypted_block": encrypted_block
        })
    
    return result, steps


def matrix_mod_inverse(matrix, mod=26):
    det = int(round(np.linalg.det(matrix)))
    det_mod = det % mod
    
    if gcd(det_mod, mod) != 1:
        return None, det_mod
    
    det_inv = modinv(det_mod, mod)
    if det_inv is None:
        return None, det_mod
    
    if len(matrix) == 2:
        adj = np.array([[matrix[1][1], -matrix[0][1]],
                        [-matrix[1][0], matrix[0][0]]])
        inv_matrix = (det_inv * adj) % mod
        return inv_matrix.astype(int).tolist(), det_mod
    
    return None, det_mod


def hill_decrypt(text, key_matrix):
    inv_matrix, det = matrix_mod_inverse(np.array(key_matrix))
    if inv_matrix is None:
        return None, [], None, det
    
    text = text.upper().replace(" ", "")
    text = ''.join(c for c in text if c.isalpha())
    n = len(key_matrix)
    
    steps = []
    result = ""
    
    for i in range(0, len(text), n):
        block = text[i:i+n]
        block_nums = [char_to_index[c] for c in block]
        
        decrypted_nums = []
        calc_details = []
        for row_idx, row in enumerate(inv_matrix):
            val = sum(row[j] * block_nums[j] for j in range(n))
            calc_str = " + ".join([f"{row[j]}×{block_nums[j]}" for j in range(n)])
            calc_details.append(f"Row{row_idx}: {calc_str} = {val} mod 26 = {int(val) % 26}")
            decrypted_nums.append(int(val) % 26)
        
        decrypted_block = ''.join(index_to_char[num] for num in decrypted_nums)
        result += decrypted_block
        
        steps.append({
            "block": block,
            "block_nums": block_nums,
            "calculations": calc_details,
            "decrypted_nums": decrypted_nums,
            "decrypted_block": decrypted_block
        })
    
    return result, steps, inv_matrix, det


# ============================================================
#                    EUCLIDEAN ALGORITHM
# ============================================================
def euclidean_gcd(a, b):
    """Calculate GCD with steps"""
    steps = []
    original_a, original_b = a, b
    if a < b:
        a, b = b, a
    
    steps.append({
        'step': 0,
        'description': f'Start: a={a}, b={b}',
        'a': a,
        'b': b,
        'quotient': '-',
        'remainder': '-'
    })
    
    step_num = 1
    while b != 0:
        q, r = a // b, a % b
        steps.append({
            'step': step_num,
            'description': f'{a} = {q} × {b} + {r}',
            'a': a,
            'b': b,
            'quotient': q,
            'remainder': r
        })
        a, b = b, r
        step_num += 1
    
    steps.append({
        'step': step_num,
        'description': f'GCD = {a}',
        'a': a,
        'b': 0,
        'quotient': '-',
        'remainder': 'GCD'
    })
    return a, steps


def extended_euclidean(a, b):
    """Extended Euclidean Algorithm"""
    steps = []
    original_a, original_b = a, b
    divisions = []
    
    steps.append({
        'phase': 'Forward Pass',
        'step': 0,
        'equation': f'Start: a={a}, b={b}',
        'details': 'Finding GCD'
    })
    
    temp_a, temp_b = abs(a), abs(b)
    step_num = 1
    
    while temp_b != 0:
        q, r = temp_a // temp_b, temp_a % temp_b
        divisions.append({'a': temp_a, 'b': temp_b, 'q': q, 'r': r})
        steps.append({
            'phase': 'Forward Pass',
            'step': step_num,
            'equation': f'{temp_a} = {q} × {temp_b} + {r}',
            'details': f'q={q}, r={r}'
        })
        temp_a, temp_b = temp_b, r
        step_num += 1
    
    gcd_result = temp_a
    steps.append({
        'phase': 'Forward Pass',
        'step': step_num,
        'equation': f'GCD = {gcd_result}',
        'details': 'Remainder is 0'
    })
    
    if len(divisions) == 0:
        x, y = 1, 0
    else:
        x, y = 1, 0
        for i in range(len(divisions) - 1, -1, -1):
            div = divisions[i]
            new_x, new_y = y, x - div['q'] * y
            steps.append({
                'phase': 'Back Substitution',
                'step': len(divisions) - i,
                'equation': f"{div['r']} = {div['a']} - {div['q']}×{div['b']}",
                'details': f'x={new_x}, y={new_y}'
            })
            x, y = new_x, new_y
    
    steps.append({
        'phase': 'Result',
        'step': 0,
        'equation': f'{original_a}×({x}) + {original_b}×({y}) = {gcd_result}',
        'details': f'x={x}, y={y}'
    })
    return gcd_result, x, y, steps


def modular_inverse_euclidean(a, m):
    """Find modular inverse using Extended Euclidean"""
    steps = [{
        'phase': 'Setup',
        'step': 0,
        'equation': f'Find {a}⁻¹ mod {m}',
        'details': f'{a}x ≡ 1 (mod {m})'
    }]
    
    gcd_val, x, y, ext_steps = extended_euclidean(a, m)
    steps.extend(ext_steps)
    
    if gcd_val != 1:
        steps.append({
            'phase': 'Result',
            'step': 0,
            'equation': f'GCD ≠ 1',
            'details': 'No inverse exists'
        })
        return None, steps
    
    inverse = x % m
    steps.append({
        'phase': 'Final',
        'step': 0,
        'equation': f'{a}⁻¹ mod {m} = {inverse}',
        'details': f'Verify: {a}×{inverse} mod {m} = {(a*inverse)%m}'
    })
    return inverse, steps


# ============================================================
#                    FERMAT'S THEOREM
# ============================================================
def is_prime_simple(n):
    """Simple primality check"""
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    for i in range(3, int(n**0.5) + 1, 2):
        if n % i == 0:
            return False
    return True


def mod_exp(base, exp, mod):
    """Fast modular exponentiation using square-and-multiply with steps"""
    steps = []
    result = 1
    base = base % mod
    original_base = base
    original_exp = exp
    
    steps.append({
        'step': 0,
        'operation': 'Initialize',
        'value': f'base={base}, exp={exp}, mod={mod}',
        'details': 'Starting square-and-multiply algorithm'
    })
    
    step_num = 1
    binary_exp = bin(original_exp)[2:]
    
    steps.append({
        'step': step_num,
        'operation': f'Binary of {original_exp}',
        'value': binary_exp,
        'details': f'Process from right to left'
    })
    step_num += 1
    
    temp_base = base
    temp_exp = exp
    
    while temp_exp > 0:
        if temp_exp % 2 == 1:
            old_result = result
            result = (result * temp_base) % mod
            steps.append({
                'step': step_num,
                'operation': f'Multiply (bit=1)',
                'value': f'{old_result} × {temp_base} mod {mod} = {result}',
                'details': f'exp bit is 1, multiply result by base'
            })
            step_num += 1
        
        temp_exp = temp_exp // 2
        if temp_exp > 0:
            old_base = temp_base
            temp_base = (temp_base * temp_base) % mod
            steps.append({
                'step': step_num,
                'operation': f'Square',
                'value': f'{old_base}² mod {mod} = {temp_base}',
                'details': f'Square the base for next iteration'
            })
            step_num += 1
    
    steps.append({
        'step': step_num,
        'operation': 'Final Result',
        'value': result,
        'details': f'{original_base}^{original_exp} mod {mod} = {result}',
        'highlight': True
    })
    
    return result, steps


def mod_exp_simple(base, exp, mod):
    """Fast modular exponentiation without steps"""
    result = 1
    base = base % mod
    while exp > 0:
        if exp % 2 == 1:
            result = (result * base) % mod
        exp = exp // 2
        base = (base * base) % mod
    return result


def verify_fermat(a, p):
    """Verify Fermat's Little Theorem: a^(p-1) ≡ 1 (mod p)"""
    steps = []
    
    steps.append({
        'step': 1,
        'operation': 'Check if p is prime',
        'value': f'p = {p}',
        'details': f'{"Yes, p is prime" if is_prime_simple(p) else "No, p is NOT prime"}'
    })
    
    steps.append({
        'step': 2,
        'operation': 'Check gcd(a, p)',
        'value': f'gcd({a}, {p}) = {gcd(a, p)}',
        'details': f'{"Coprime ✓" if gcd(a, p) == 1 else "Not coprime - theorem may not apply"}'
    })
    
    steps.append({
        'step': 3,
        'operation': f'Calculate {a}^{p-1} mod {p}',
        'value': f'{a}^{p-1} mod {p}',
        'details': 'Using fast modular exponentiation'
    })
    
    result, exp_steps = mod_exp(a, p - 1, p)
    
    for i, exp_step in enumerate(exp_steps):
        exp_step['step'] = 4 + i
        steps.append(exp_step)
    
    return result, steps


def fermat_mod_inverse(a, p):
    """Calculate modular inverse using Fermat: a^(-1) ≡ a^(p-2) (mod p)"""
    steps = []
    
    steps.append({
        'step': 1,
        'operation': 'Verify p is prime',
        'value': f'p = {p}',
        'details': f'{"Yes ✓" if is_prime_simple(p) else "No - Fermat method requires prime modulus"}'
    })
    
    if not is_prime_simple(p):
        return None, steps
    
    steps.append({
        'step': 2,
        'operation': 'Apply Fermat formula',
        'value': f'a⁻¹ ≡ a^(p-2) mod p',
        'details': f'{a}⁻¹ ≡ {a}^{p-2} mod {p}'
    })
    
    steps.append({
        'step': 3,
        'operation': f'Calculate {a}^{p-2} mod {p}',
        'value': f'Exponent = {p-2}',
        'details': 'Using fast modular exponentiation'
    })
    
    result, exp_steps = mod_exp(a, p - 2, p)
    
    for i, exp_step in enumerate(exp_steps):
        exp_step['step'] = 4 + i
        steps.append(exp_step)
    
    steps.append({
        'step': len(steps) + 1,
        'operation': 'Verification',
        'value': f'{a} × {result} mod {p} = {(a * result) % p}',
        'details': 'Should equal 1',
        'highlight': True
    })
    
    return result, steps


def fermat_primality_test(n, k=5):
    """Fermat primality test with k iterations"""
    steps = []
    
    if n < 2:
        steps.append({'step': 1, 'operation': 'Check', 'value': f'{n} < 2', 'details': 'Not prime'})
        return False, steps
    
    if n == 2:
        steps.append({'step': 1, 'operation': 'Check', 'value': 'n = 2', 'details': 'Prime'})
        return True, steps
    
    if n % 2 == 0:
        steps.append({'step': 1, 'operation': 'Check', 'value': f'{n} is even', 'details': 'Not prime'})
        return False, steps
    
    steps.append({
        'step': 1,
        'operation': 'Initialize',
        'value': f'n = {n}, k = {k}',
        'details': f'Testing with {k} random bases'
    })
    
    for i in range(k):
        a = random.randrange(2, n)
        result = mod_exp_simple(a, n - 1, n)
        
        steps.append({
            'step': i + 2,
            'operation': f'Test base a = {a}',
            'value': f'{a}^{n-1} mod {n} = {result}',
            'details': '✓ Passed' if result == 1 else '✗ Failed - Composite!'
        })
        
        if result != 1:
            steps.append({
                'step': i + 3,
                'operation': 'Conclusion',
                'value': 'COMPOSITE',
                'details': f'{n} is definitely NOT prime',
                'highlight': True
            })
            return False, steps
    
    steps.append({
        'step': k + 2,
        'operation': 'Conclusion',
        'value': 'PROBABLY PRIME',
        'details': f'Passed all {k} tests (probabilistic)',
        'highlight': True
    })
    
    return True, steps


def euler_totient(n):
    """Calculate Euler's totient function φ(n)"""
    result = n
    p = 2
    temp_n = n
    factors = []
    
    while p * p <= temp_n:
        if temp_n % p == 0:
            factors.append(p)
            while temp_n % p == 0:
                temp_n //= p
            result -= result // p
        p += 1
    
    if temp_n > 1:
        factors.append(temp_n)
        result -= result // temp_n
    
    return result, factors


def verify_euler(a, n):
    """Verify Euler's theorem: a^φ(n) ≡ 1 (mod n) when gcd(a,n) = 1"""
    steps = []
    
    phi, factors = euler_totient(n)
    
    steps.append({
        'step': 1,
        'operation': f'Calculate φ({n})',
        'value': f'φ({n}) = {phi}',
        'details': f'Prime factors of {n}: {factors}' if factors else 'Using totient formula'
    })
    
    g = gcd(a, n)
    steps.append({
        'step': 2,
        'operation': f'Check gcd({a}, {n})',
        'value': f'gcd = {g}',
        'details': 'Must be 1 for theorem to apply'
    })
    
    if g != 1:
        steps.append({
            'step': 3,
            'operation': 'Error',
            'value': f'gcd({a}, {n}) ≠ 1',
            'details': "Euler's theorem does not apply"
        })
        return None, phi, steps
    
    steps.append({
        'step': 3,
        'operation': f'Calculate {a}^{phi} mod {n}',
        'value': f'{a}^φ({n}) mod {n}',
        'details': 'Using fast exponentiation'
    })
    
    result, exp_steps = mod_exp(a, phi, n)
    
    for i, exp_step in enumerate(exp_steps):
        exp_step['step'] = 4 + i
        steps.append(exp_step)
    
    return result, phi, steps


# ============================================================
#                    RSA ALGORITHM
# ============================================================
def generate_prime(bits=8):
    """Generate a random prime number with specified bits"""
    while True:
        n = random.getrandbits(bits) | (1 << bits - 1) | 1
        if is_prime_simple(n):
            return n


def generate_rsa_keys(p, q, e=None):
    """Generate RSA keys with detailed steps"""
    steps = []
    
    steps.append({
        'phase': 'Prime Selection',
        'step': 1,
        'operation': 'Input primes p and q',
        'value': f'p = {p}, q = {q}',
        'details': f'p is {"prime ✓" if is_prime_simple(p) else "NOT prime ✗"}, q is {"prime ✓" if is_prime_simple(q) else "NOT prime ✗"}'
    })
    
    if not is_prime_simple(p) or not is_prime_simple(q):
        return None, None, None, None, None, steps, "Both p and q must be prime numbers"
    
    if p == q:
        return None, None, None, None, None, steps, "p and q must be different primes"
    
    n = p * q
    steps.append({
        'phase': 'Calculate n',
        'step': 2,
        'operation': 'n = p × q',
        'value': f'n = {p} × {q} = {n}',
        'details': f'n is the modulus for both public and private keys'
    })
    
    phi_n = (p - 1) * (q - 1)
    steps.append({
        'phase': 'Calculate φ(n)',
        'step': 3,
        'operation': 'φ(n) = (p-1) × (q-1)',
        'value': f'φ({n}) = ({p}-1) × ({q}-1) = {p-1} × {q-1} = {phi_n}',
        'details': "Euler's totient function"
    })
    
    if e is None:
        e = 65537
        if gcd(e, phi_n) != 1:
            e = 3
            while gcd(e, phi_n) != 1:
                e += 2
    
    if gcd(e, phi_n) != 1:
        return None, None, None, None, None, steps, f"e={e} is not coprime with φ(n)={phi_n}"
    
    steps.append({
        'phase': 'Choose e',
        'step': 4,
        'operation': f'Choose e such that 1 < e < φ(n) and gcd(e, φ(n)) = 1',
        'value': f'e = {e}',
        'details': f'gcd({e}, {phi_n}) = {gcd(e, phi_n)} ✓'
    })
    
    d = modinv(e, phi_n)
    if d is None:
        return None, None, None, None, None, steps, "Could not calculate modular inverse"
    
    steps.append({
        'phase': 'Calculate d',
        'step': 5,
        'operation': f'd = e⁻¹ mod φ(n)',
        'value': f'd = {e}⁻¹ mod {phi_n} = {d}',
        'details': f'Using Extended Euclidean Algorithm'
    })
    
    verification = (d * e) % phi_n
    steps.append({
        'phase': 'Verification',
        'step': 6,
        'operation': 'd × e mod φ(n)',
        'value': f'{d} × {e} mod {phi_n} = {verification}',
        'details': '✓ Verified!' if verification == 1 else '✗ Error!',
        'highlight': True
    })
    
    steps.append({
        'phase': 'Key Summary',
        'step': 7,
        'operation': 'Public Key (e, n)',
        'value': f'({e}, {n})',
        'details': 'Share this publicly'
    })
    
    steps.append({
        'phase': 'Key Summary',
        'step': 8,
        'operation': 'Private Key (d, n)',
        'value': f'({d}, {n})',
        'details': 'Keep this secret!'
    })
    
    return n, phi_n, e, d, (e, n, d), steps, None


def rsa_encrypt(message, e, n):
    """RSA encryption with detailed steps"""
    steps = []
    encrypted_values = []
    
    steps.append({
        'phase': 'Setup',
        'step': 0,
        'char': '-',
        'ascii': '-',
        'operation': f'Using public key (e={e}, n={n})',
        'calculation': '-',
        'result': '-'
    })
    
    step_num = 1
    for char in message:
        m = ord(char)
        
        if m >= n:
            steps.append({
                'phase': 'Error',
                'step': step_num,
                'char': char,
                'ascii': m,
                'operation': 'Check m < n',
                'calculation': f'{m} >= {n}',
                'result': 'ERROR: Message value must be less than n'
            })
            return None, steps, f"Character '{char}' (ASCII {m}) is >= n ({n}). Use larger primes."
        
        c = mod_exp_simple(m, e, n)
        encrypted_values.append(c)
        
        steps.append({
            'phase': 'Encryption',
            'step': step_num,
            'char': char,
            'ascii': m,
            'operation': f'C = M^e mod n',
            'calculation': f'C = {m}^{e} mod {n}',
            'result': c
        })
        step_num += 1
    
    steps.append({
        'phase': 'Result',
        'step': step_num,
        'char': '-',
        'ascii': '-',
        'operation': 'Encrypted values',
        'calculation': str(encrypted_values),
        'result': ' '.join(map(str, encrypted_values)),
        'highlight': True
    })
    
    return encrypted_values, steps, None


def rsa_decrypt(encrypted_values, d, n):
    """RSA decryption with detailed steps"""
    steps = []
    decrypted_chars = []
    
    steps.append({
        'phase': 'Setup',
        'step': 0,
        'cipher': '-',
        'operation': f'Using private key (d={d}, n={n})',
        'calculation': '-',
        'ascii': '-',
        'char': '-'
    })
    
    step_num = 1
    for c in encrypted_values:
        m = mod_exp_simple(c, d, n)
        
        try:
            char = chr(m)
            decrypted_chars.append(char)
        except:
            char = '?'
            decrypted_chars.append(char)
        
        steps.append({
            'phase': 'Decryption',
            'step': step_num,
            'cipher': c,
            'operation': f'M = C^d mod n',
            'calculation': f'M = {c}^{d} mod {n}',
            'ascii': m,
            'char': char
        })
        step_num += 1
    
    decrypted_message = ''.join(decrypted_chars)
    
    steps.append({
        'phase': 'Result',
        'step': step_num,
        'cipher': '-',
        'operation': 'Decrypted message',
        'calculation': '-',
        'ascii': '-',
        'char': decrypted_message,
        'highlight': True
    })
    
    return decrypted_message, steps


def rsa_encrypt_text(plaintext, e, n):
    """Encrypt entire text and return as space-separated cipher values"""
    encrypted, steps, error = rsa_encrypt(plaintext, e, n)
    if error:
        return None, steps, error
    cipher_text = ' '.join(map(str, encrypted))
    return cipher_text, steps, None


def rsa_decrypt_text(cipher_text, d, n):
    """Decrypt space-separated cipher values back to text"""
    try:
        encrypted_values = [int(x) for x in cipher_text.strip().split()]
    except ValueError:
        return None, [], "Invalid ciphertext format. Use space-separated numbers."
    
    return rsa_decrypt(encrypted_values, d, n)


# ============================================================
#                    AES CONSTANTS & FUNCTIONS
# ============================================================
AES_SBOX = [
    0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
    0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
    0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
    0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
    0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
    0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
    0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
    0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
    0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
    0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
    0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
    0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
    0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
    0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
    0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
    0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16
]

AES_INV_SBOX = [
    0x52, 0x09, 0x6a, 0xd5, 0x30, 0x36, 0xa5, 0x38, 0xbf, 0x40, 0xa3, 0x9e, 0x81, 0xf3, 0xd7, 0xfb,
    0x7c, 0xe3, 0x39, 0x82, 0x9b, 0x2f, 0xff, 0x87, 0x34, 0x8e, 0x43, 0x44, 0xc4, 0xde, 0xe9, 0xcb,
    0x54, 0x7b, 0x94, 0x32, 0xa6, 0xc2, 0x23, 0x3d, 0xee, 0x4c, 0x95, 0x0b, 0x42, 0xfa, 0xc3, 0x4e,
    0x08, 0x2e, 0xa1, 0x66, 0x28, 0xd9, 0x24, 0xb2, 0x76, 0x5b, 0xa2, 0x49, 0x6d, 0x8b, 0xd1, 0x25,
    0x72, 0xf8, 0xf6, 0x64, 0x86, 0x68, 0x98, 0x16, 0xd4, 0xa4, 0x5c, 0xcc, 0x5d, 0x65, 0xb6, 0x92,
    0x6c, 0x70, 0x48, 0x50, 0xfd, 0xed, 0xb9, 0xda, 0x5e, 0x15, 0x46, 0x57, 0xa7, 0x8d, 0x9d, 0x84,
    0x90, 0xd8, 0xab, 0x00, 0x8c, 0xbc, 0xd3, 0x0a, 0xf7, 0xe4, 0x58, 0x05, 0xb8, 0xb3, 0x45, 0x06,
    0xd0, 0x2c, 0x1e, 0x8f, 0xca, 0x3f, 0x0f, 0x02, 0xc1, 0xaf, 0xbd, 0x03, 0x01, 0x13, 0x8a, 0x6b,
    0x3a, 0x91, 0x11, 0x41, 0x4f, 0x67, 0xdc, 0xea, 0x97, 0xf2, 0xcf, 0xce, 0xf0, 0xb4, 0xe6, 0x73,
    0x96, 0xac, 0x74, 0x22, 0xe7, 0xad, 0x35, 0x85, 0xe2, 0xf9, 0x37, 0xe8, 0x1c, 0x75, 0xdf, 0x6e,
    0x47, 0xf1, 0x1a, 0x71, 0x1d, 0x29, 0xc5, 0x89, 0x6f, 0xb7, 0x62, 0x0e, 0xaa, 0x18, 0xbe, 0x1b,
    0xfc, 0x56, 0x3e, 0x4b, 0xc6, 0xd2, 0x79, 0x20, 0x9a, 0xdb, 0xc0, 0xfe, 0x78, 0xcd, 0x5a, 0xf4,
    0x1f, 0xdd, 0xa8, 0x33, 0x88, 0x07, 0xc7, 0x31, 0xb1, 0x12, 0x10, 0x59, 0x27, 0x80, 0xec, 0x5f,
    0x60, 0x51, 0x7f, 0xa9, 0x19, 0xb5, 0x4a, 0x0d, 0x2d, 0xe5, 0x7a, 0x9f, 0x93, 0xc9, 0x9c, 0xef,
    0xa0, 0xe0, 0x3b, 0x4d, 0xae, 0x2a, 0xf5, 0xb0, 0xc8, 0xeb, 0xbb, 0x3c, 0x83, 0x53, 0x99, 0x61,
    0x17, 0x2b, 0x04, 0x7e, 0xba, 0x77, 0xd6, 0x26, 0xe1, 0x69, 0x14, 0x63, 0x55, 0x21, 0x0c, 0x7d
]

AES_RCON = [
    [0x01, 0x00, 0x00, 0x00], [0x02, 0x00, 0x00, 0x00], [0x04, 0x00, 0x00, 0x00],
    [0x08, 0x00, 0x00, 0x00], [0x10, 0x00, 0x00, 0x00], [0x20, 0x00, 0x00, 0x00],
    [0x40, 0x00, 0x00, 0x00], [0x80, 0x00, 0x00, 0x00], [0x1b, 0x00, 0x00, 0x00],
    [0x36, 0x00, 0x00, 0x00]
]

AES_IV = bytes([0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
                0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F])


def bytes_to_state(b):
    state = [[0] * 4 for _ in range(4)]
    for i in range(16):
        state[i % 4][i // 4] = b[i]
    return state


def state_to_bytes(state):
    result = []
    for col in range(4):
        for row in range(4):
            result.append(state[row][col])
    return bytes(result)


def state_to_hex_str(state):
    return ' '.join([format(state[row][col], '02x') for col in range(4) for row in range(4)])


def sub_bytes_aes(state, inverse=False):
    sbox = AES_INV_SBOX if inverse else AES_SBOX
    for i in range(4):
        for j in range(4):
            state[i][j] = sbox[state[i][j]]
    return state


def shift_rows_aes(state, inverse=False):
    for i in range(1, 4):
        if inverse:
            state[i] = state[i][-i:] + state[i][:-i]
        else:
            state[i] = state[i][i:] + state[i][:i]
    return state


def xtime(a):
    return ((a << 1) ^ 0x1b) & 0xff if a & 0x80 else (a << 1) & 0xff


def mix_single_column(col):
    t = col[0] ^ col[1] ^ col[2] ^ col[3]
    u = col[0]
    col[0] ^= t ^ xtime(col[0] ^ col[1])
    col[1] ^= t ^ xtime(col[1] ^ col[2])
    col[2] ^= t ^ xtime(col[2] ^ col[3])
    col[3] ^= t ^ xtime(col[3] ^ u)
    return col


def mix_columns_aes(state, inverse=False):
    if inverse:
        for _ in range(3):
            for i in range(4):
                col = [state[j][i] for j in range(4)]
                col = mix_single_column(col)
                for j in range(4):
                    state[j][i] = col[j]
    else:
        for i in range(4):
            col = [state[j][i] for j in range(4)]
            col = mix_single_column(col)
            for j in range(4):
                state[j][i] = col[j]
    return state


def add_round_key(state, round_key):
    for i in range(4):
        for j in range(4):
            state[i][j] ^= round_key[i][j]
    return state


def key_expansion_aes(key):
    key_schedule = [[0] * 4 for _ in range(44)]
    for i in range(4):
        key_schedule[i] = [key[4*i], key[4*i+1], key[4*i+2], key[4*i+3]]
    for i in range(4, 44):
        temp = key_schedule[i-1].copy()
        if i % 4 == 0:
            temp = temp[1:] + temp[:1]
            temp = [AES_SBOX[b] for b in temp]
            temp = [temp[j] ^ AES_RCON[i//4 - 1][j] for j in range(4)]
        key_schedule[i] = [key_schedule[i-4][j] ^ temp[j] for j in range(4)]
    round_keys = []
    for r in range(11):
        rk = [[0] * 4 for _ in range(4)]
        for col in range(4):
            for row in range(4):
                rk[row][col] = key_schedule[r*4 + col][row]
        round_keys.append(rk)
    return round_keys


def aes_encrypt_block(plaintext, key):
    steps = []
    state = bytes_to_state(plaintext)
    round_keys = key_expansion_aes(key)
    
    steps.append({'round': 'Initial', 'operation': 'Input', 'state': state_to_hex_str(state)})
    state = add_round_key(state, round_keys[0])
    steps.append({'round': 0, 'operation': 'AddRoundKey', 'state': state_to_hex_str(state)})
    
    for r in range(1, 10):
        state = sub_bytes_aes(state)
        steps.append({'round': r, 'operation': 'SubBytes', 'state': state_to_hex_str(state)})
        state = shift_rows_aes(state)
        steps.append({'round': r, 'operation': 'ShiftRows', 'state': state_to_hex_str(state)})
        state = mix_columns_aes(state)
        steps.append({'round': r, 'operation': 'MixColumns', 'state': state_to_hex_str(state)})
        state = add_round_key(state, round_keys[r])
        steps.append({'round': r, 'operation': 'AddRoundKey', 'state': state_to_hex_str(state)})
    
    state = sub_bytes_aes(state)
    steps.append({'round': 10, 'operation': 'SubBytes', 'state': state_to_hex_str(state)})
    state = shift_rows_aes(state)
    steps.append({'round': 10, 'operation': 'ShiftRows', 'state': state_to_hex_str(state)})
    state = add_round_key(state, round_keys[10])
    steps.append({'round': 10, 'operation': 'AddRoundKey (Final)', 'state': state_to_hex_str(state)})
    
    return state_to_bytes(state), steps


def aes_decrypt_block(ciphertext, key):
    steps = []
    state = bytes_to_state(ciphertext)
    round_keys = key_expansion_aes(key)
    
    steps.append({'round': 'Initial', 'operation': 'Input', 'state': state_to_hex_str(state)})
    state = add_round_key(state, round_keys[10])
    steps.append({'round': 10, 'operation': 'AddRoundKey', 'state': state_to_hex_str(state)})
    
    for r in range(9, 0, -1):
        state = shift_rows_aes(state, inverse=True)
        steps.append({'round': r, 'operation': 'InvShiftRows', 'state': state_to_hex_str(state)})
        state = sub_bytes_aes(state, inverse=True)
        steps.append({'round': r, 'operation': 'InvSubBytes', 'state': state_to_hex_str(state)})
        state = add_round_key(state, round_keys[r])
        steps.append({'round': r, 'operation': 'AddRoundKey', 'state': state_to_hex_str(state)})
        state = mix_columns_aes(state, inverse=True)
        steps.append({'round': r, 'operation': 'InvMixColumns', 'state': state_to_hex_str(state)})
    
    state = shift_rows_aes(state, inverse=True)
    steps.append({'round': 0, 'operation': 'InvShiftRows', 'state': state_to_hex_str(state)})
    state = sub_bytes_aes(state, inverse=True)
    steps.append({'round': 0, 'operation': 'InvSubBytes', 'state': state_to_hex_str(state)})
    state = add_round_key(state, round_keys[0])
    steps.append({'round': 0, 'operation': 'AddRoundKey (Final)', 'state': state_to_hex_str(state)})
    
    return state_to_bytes(state), steps


def xor_bytes_aes(a, b):
    return bytes([x ^ y for x, y in zip(a, b)])


def pad_text(text, block_size):
    pad_len = block_size - (len(text) % block_size)
    return text + bytes([pad_len] * pad_len)


def unpad_text(text):
    pad_len = text[-1]
    return text[:-pad_len]


def aes_encrypt(plaintext, key, mode='ecb'):
    all_steps = []
    padded = pad_text(plaintext.encode() if isinstance(plaintext, str) else plaintext, 16)
    blocks = [padded[i:i+16] for i in range(0, len(padded), 16)]
    result = b''
    prev_block = AES_IV if mode == 'cbc' else None
    
    for i, block in enumerate(blocks):
        block_info = {'block_num': i + 1, 'input': block.hex()}
        if mode == 'cbc':
            block = xor_bytes_aes(block, prev_block)
            block_info['after_xor_iv'] = block.hex()
        encrypted, steps = aes_encrypt_block(block, key)
        block_info['output'] = encrypted.hex()
        block_info['steps'] = steps
        all_steps.append(block_info)
        result += encrypted
        if mode == 'cbc':
            prev_block = encrypted
    
    return result, all_steps


def aes_decrypt(ciphertext, key, mode='ecb'):
    all_steps = []
    blocks = [ciphertext[i:i+16] for i in range(0, len(ciphertext), 16)]
    result = b''
    prev_block = AES_IV if mode == 'cbc' else None
    
    for i, block in enumerate(blocks):
        block_info = {'block_num': i + 1, 'input': block.hex()}
        decrypted, steps = aes_decrypt_block(block, key)
        block_info['steps'] = steps
        if mode == 'cbc':
            decrypted = xor_bytes_aes(decrypted, prev_block)
            block_info['after_xor_iv'] = decrypted.hex()
            prev_block = block
        block_info['output'] = decrypted.hex()
        all_steps.append(block_info)
        result += decrypted
    
    try:
        result = unpad_text(result)
    except:
        pass
    
    return result, all_steps


# ============================================================
#                    DES CONSTANTS & FUNCTIONS
# ============================================================
DES_IP = [58,50,42,34,26,18,10,2,60,52,44,36,28,20,12,4,62,54,46,38,30,22,14,6,64,56,48,40,32,24,16,8,57,49,41,33,25,17,9,1,59,51,43,35,27,19,11,3,61,53,45,37,29,21,13,5,63,55,47,39,31,23,15,7]
DES_IP_INV = [40,8,48,16,56,24,64,32,39,7,47,15,55,23,63,31,38,6,46,14,54,22,62,30,37,5,45,13,53,21,61,29,36,4,44,12,52,20,60,28,35,3,43,11,51,19,59,27,34,2,42,10,50,18,58,26,33,1,41,9,49,17,57,25]
DES_E = [32,1,2,3,4,5,4,5,6,7,8,9,8,9,10,11,12,13,12,13,14,15,16,17,16,17,18,19,20,21,20,21,22,23,24,25,24,25,26,27,28,29,28,29,30,31,32,1]
DES_P = [16,7,20,21,29,12,28,17,1,15,23,26,5,18,31,10,2,8,24,14,32,27,3,9,19,13,30,6,22,11,4,25]
DES_PC1 = [57,49,41,33,25,17,9,1,58,50,42,34,26,18,10,2,59,51,43,35,27,19,11,3,60,52,44,36,63,55,47,39,31,23,15,7,62,54,46,38,30,22,14,6,61,53,45,37,29,21,13,5,28,20,12,4]
DES_PC2 = [14,17,11,24,1,5,3,28,15,6,21,10,23,19,12,4,26,8,16,7,27,20,13,2,41,52,31,37,47,55,30,40,51,45,33,48,44,49,39,56,34,53,46,42,50,36,29,32]
DES_SHIFTS = [1,1,2,2,2,2,2,2,1,2,2,2,2,2,2,1]

DES_SBOXES = [
    [[14,4,13,1,2,15,11,8,3,10,6,12,5,9,0,7],[0,15,7,4,14,2,13,1,10,6,12,11,9,5,3,8],[4,1,14,8,13,6,2,11,15,12,9,7,3,10,5,0],[15,12,8,2,4,9,1,7,5,11,3,14,10,0,6,13]],
    [[15,1,8,14,6,11,3,4,9,7,2,13,12,0,5,10],[3,13,4,7,15,2,8,14,12,0,1,10,6,9,11,5],[0,14,7,11,10,4,13,1,5,8,12,6,9,3,2,15],[13,8,10,1,3,15,4,2,11,6,7,12,0,5,14,9]],
    [[10,0,9,14,6,3,15,5,1,13,12,7,11,4,2,8],[13,7,0,9,3,4,6,10,2,8,5,14,12,11,15,1],[13,6,4,9,8,15,3,0,11,1,2,12,5,10,14,7],[1,10,13,0,6,9,8,7,4,15,14,3,11,5,2,12]],
    [[7,13,14,3,0,6,9,10,1,2,8,5,11,12,4,15],[13,8,11,5,6,15,0,3,4,7,2,12,1,10,14,9],[10,6,9,0,12,11,7,13,15,1,3,14,5,2,8,4],[3,15,0,6,10,1,13,8,9,4,5,11,12,7,2,14]],
    [[2,12,4,1,7,10,11,6,8,5,3,15,13,0,14,9],[14,11,2,12,4,7,13,1,5,0,15,10,3,9,8,6],[4,2,1,11,10,13,7,8,15,9,12,5,6,3,0,14],[11,8,12,7,1,14,2,13,6,15,0,9,10,4,5,3]],
    [[12,1,10,15,9,2,6,8,0,13,3,4,14,7,5,11],[10,15,4,2,7,12,9,5,6,1,13,14,0,11,3,8],[9,14,15,5,2,8,12,3,7,0,4,10,1,13,11,6],[4,3,2,12,9,5,15,10,11,14,1,7,6,0,8,13]],
    [[4,11,2,14,15,0,8,13,3,12,9,7,5,10,6,1],[13,0,11,7,4,9,1,10,14,3,5,12,2,15,8,6],[1,4,11,13,12,3,7,14,10,15,6,8,0,5,9,2],[6,11,13,8,1,4,10,7,9,5,0,15,14,2,3,12]],
    [[13,2,8,4,6,15,11,1,10,9,3,14,5,0,12,7],[1,15,13,8,10,3,7,4,12,5,6,11,0,14,9,2],[7,11,4,1,9,12,14,2,0,6,10,13,15,3,5,8],[2,1,14,7,4,10,8,13,15,12,9,0,3,5,6,11]]
]

DES_IV = bytes([0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xF0])


def permute_des(block, table):
    return [block[i - 1] for i in table]


def left_shift_des(bits, n):
    return bits[n:] + bits[:n]


def bytes_to_bits_des(b):
    result = []
    for byte in b:
        result.extend([int(x) for x in format(byte, '08b')])
    return result


def bits_to_bytes_des(bits):
    result = []
    for i in range(0, len(bits), 8):
        byte = int(''.join(map(str, bits[i:i+8])), 2)
        result.append(byte)
    return bytes(result)


def bits_to_hex_des(bits):
    hex_str = ''
    for i in range(0, len(bits), 4):
        nibble = bits[i:i+4]
        if len(nibble) == 4:
            hex_str += format(int(''.join(map(str, nibble)), 2), 'x')
    return hex_str


def generate_des_keys(key_bits):
    steps = []
    key_56 = permute_des(key_bits, DES_PC1)
    C = key_56[:28]
    D = key_56[28:]
    round_keys = []
    
    for i in range(16):
        C = left_shift_des(C, DES_SHIFTS[i])
        D = left_shift_des(D, DES_SHIFTS[i])
        CD = C + D
        round_key = permute_des(CD, DES_PC2)
        round_keys.append(round_key)
        steps.append({'round': i + 1, 'shifts': DES_SHIFTS[i], 'round_key': bits_to_hex_des(round_key)})
    
    return round_keys, steps


def des_f_function(R, K, round_num):
    step_info = {'round': round_num}
    expanded = permute_des(R, DES_E)
    step_info['after_expansion'] = bits_to_hex_des(expanded)
    
    xored = [expanded[i] ^ K[i] for i in range(48)]
    step_info['after_key_xor'] = bits_to_hex_des(xored)
    
    sbox_output = []
    for i in range(8):
        block = xored[i*6:(i+1)*6]
        row = block[0] * 2 + block[5]
        col = block[1] * 8 + block[2] * 4 + block[3] * 2 + block[4]
        val = DES_SBOXES[i][row][col]
        sbox_output.extend([int(b) for b in format(val, '04b')])
    
    step_info['after_sbox'] = bits_to_hex_des(sbox_output)
    result = permute_des(sbox_output, DES_P)
    step_info['after_pbox'] = bits_to_hex_des(result)
    
    return result, step_info


def des_encrypt_block(plaintext_bits, key_bits):
    all_steps = []
    round_keys, key_steps = generate_des_keys(key_bits)
    all_steps.append({'type': 'key_generation', 'steps': key_steps})
    
    permuted = permute_des(plaintext_bits, DES_IP)
    all_steps.append({'type': 'initial_permutation', 'input': bits_to_hex_des(plaintext_bits), 'output': bits_to_hex_des(permuted)})
    
    L, R = permuted[:32], permuted[32:]
    round_steps = []
    
    for i in range(16):
        old_L, old_R = L.copy(), R.copy()
        f_result, f_step = des_f_function(R, round_keys[i], i + 1)
        new_R = [L[j] ^ f_result[j] for j in range(32)]
        L, R = R, new_R
        round_steps.append({'round': i + 1, 'L_in': bits_to_hex_des(old_L), 'R_in': bits_to_hex_des(old_R), 'f_details': f_step, 'L_out': bits_to_hex_des(L), 'R_out': bits_to_hex_des(R)})
    
    all_steps.append({'type': 'rounds', 'steps': round_steps})
    
    combined = R + L
    ciphertext = permute_des(combined, DES_IP_INV)
    all_steps.append({'type': 'final_permutation', 'input': bits_to_hex_des(combined), 'output': bits_to_hex_des(ciphertext)})
    
    return ciphertext, all_steps


def des_decrypt_block(ciphertext_bits, key_bits):
    all_steps = []
    round_keys, key_steps = generate_des_keys(key_bits)
    all_steps.append({'type': 'key_generation', 'steps': key_steps})
    round_keys = round_keys[::-1]
    
    permuted = permute_des(ciphertext_bits, DES_IP)
    all_steps.append({'type': 'initial_permutation', 'input': bits_to_hex_des(ciphertext_bits), 'output': bits_to_hex_des(permuted)})
    
    L, R = permuted[:32], permuted[32:]
    round_steps = []
    
    for i in range(16):
        old_L, old_R = L.copy(), R.copy()
        f_result, f_step = des_f_function(R, round_keys[i], i + 1)
        new_R = [L[j] ^ f_result[j] for j in range(32)]
        L, R = R, new_R
        round_steps.append({'round': i + 1, 'L_in': bits_to_hex_des(old_L), 'R_in': bits_to_hex_des(old_R), 'f_details': f_step, 'L_out': bits_to_hex_des(L), 'R_out': bits_to_hex_des(R)})
    
    all_steps.append({'type': 'rounds', 'steps': round_steps})
    
    combined = R + L
    plaintext = permute_des(combined, DES_IP_INV)
    all_steps.append({'type': 'final_permutation', 'input': bits_to_hex_des(combined), 'output': bits_to_hex_des(plaintext)})
    
    return plaintext, all_steps


def xor_bits_des(a, b):
    return [x ^ y for x, y in zip(a, b)]


def des_encrypt(plaintext, key, mode='ecb'):
    all_steps = []
    if isinstance(plaintext, str):
        plaintext = plaintext.encode()
    padded = pad_text(plaintext, 8)
    key_bits = bytes_to_bits_des(key)
    result_bits = []
    prev_block = bytes_to_bits_des(DES_IV) if mode == 'cbc' else None
    
    for i in range(0, len(padded), 8):
        block = padded[i:i+8]
        block_bits = bytes_to_bits_des(block)
        block_info = {'block_num': i // 8 + 1, 'input': bits_to_hex_des(block_bits)}
        
        if mode == 'cbc':
            block_bits = xor_bits_des(block_bits, prev_block)
            block_info['after_xor_iv'] = bits_to_hex_des(block_bits)
        
        encrypted, steps = des_encrypt_block(block_bits, key_bits)
        block_info['output'] = bits_to_hex_des(encrypted)
        block_info['steps'] = steps
        all_steps.append(block_info)
        result_bits.extend(encrypted)
        
        if mode == 'cbc':
            prev_block = encrypted
    
    return bits_to_bytes_des(result_bits), all_steps


def des_decrypt(ciphertext, key, mode='ecb'):
    all_steps = []
    key_bits = bytes_to_bits_des(key)
    result_bits = []
    prev_block = bytes_to_bits_des(DES_IV) if mode == 'cbc' else None
    
    for i in range(0, len(ciphertext), 8):
        block = ciphertext[i:i+8]
        block_bits = bytes_to_bits_des(block)
        block_info = {'block_num': i // 8 + 1, 'input': bits_to_hex_des(block_bits)}
        
        decrypted, steps = des_decrypt_block(block_bits, key_bits)
        block_info['steps'] = steps
        
        if mode == 'cbc':
            decrypted = xor_bits_des(decrypted, prev_block)
            block_info['after_xor_iv'] = bits_to_hex_des(decrypted)
            prev_block = block_bits
        
        block_info['output'] = bits_to_hex_des(decrypted)
        all_steps.append(block_info)
        result_bits.extend(decrypted)
    
    result = bits_to_bytes_des(result_bits)
    try:
        result = unpad_text(result)
    except:
        pass
    
    return result, all_steps


def parse_key(key_str, key_format, required_bits):
    try:
        if key_format == 'hex':
            key_str = key_str.replace(' ', '').replace('0x', '').replace('0X', '')
            if len(key_str) * 4 != required_bits:
                return None, f"Key must be {required_bits} bits ({required_bits // 4} hex characters)"
            return bytes.fromhex(key_str), None
        else:
            key_str = key_str.replace(' ', '')
            if len(key_str) != required_bits:
                return None, f"Key must be {required_bits} bits"
            if not all(c in '01' for c in key_str):
                return None, "Binary key must contain only 0s and 1s"
            key_bytes = []
            for i in range(0, len(key_str), 8):
                key_bytes.append(int(key_str[i:i+8], 2))
            return bytes(key_bytes), None
    except Exception as e:
        return None, str(e)


# ============================================================
#                    MD5 HASH ALGORITHM
# ============================================================
MD5_INIT = [0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476]
MD5_K = [int(abs(math.sin(i + 1)) * (2 ** 32)) & 0xFFFFFFFF for i in range(64)]
MD5_S = [
    7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22,
    5,  9, 14, 20, 5,  9, 14, 20, 5,  9, 14, 20, 5,  9, 14, 20,
    4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23,
    6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21
]


def md5_f(x, y, z):
    return (x & y) | (~x & z)

def md5_g(x, y, z):
    return (x & z) | (y & ~z)

def md5_h(x, y, z):
    return x ^ y ^ z

def md5_i(x, y, z):
    return y ^ (x | ~z)


def left_rotate_md5(value, shift):
    return ((value << shift) | (value >> (32 - shift))) & 0xFFFFFFFF


def md5_pad_message(message):
    if isinstance(message, str):
        message = message.encode()
    
    msg_len = len(message)
    msg_bit_len = msg_len * 8
    
    padded = bytearray(message)
    padded.append(0x80)
    
    while (len(padded) % 64) != 56:
        padded.append(0x00)
    
    padded.extend(struct.pack('<Q', msg_bit_len))
    
    return bytes(padded), msg_len, msg_bit_len


def md5_process_block(block, state, block_num):
    steps = []
    M = list(struct.unpack('<16I', block))
    
    A, B, C, D = state
    
    steps.append({
        'round': 'Init',
        'A': f'{A:08x}',
        'B': f'{B:08x}',
        'C': f'{C:08x}',
        'D': f'{D:08x}'
    })
    
    for i in range(64):
        if i < 16:
            func = md5_f(B, C, D)
            g = i
            round_name = 'F'
        elif i < 32:
            func = md5_g(B, C, D)
            g = (5 * i + 1) % 16
            round_name = 'G'
        elif i < 48:
            func = md5_h(B, C, D)
            g = (3 * i + 5) % 16
            round_name = 'H'
        else:
            func = md5_i(B, C, D)
            g = (7 * i) % 16
            round_name = 'I'
        
        F = (func + A + MD5_K[i] + M[g]) & 0xFFFFFFFF
        A = D
        D = C
        C = B
        B = (B + left_rotate_md5(F, MD5_S[i])) & 0xFFFFFFFF
        
        if i % 4 == 3 or i == 63:
            steps.append({
                'round': f'{i+1} ({round_name})',
                'A': f'{A:08x}',
                'B': f'{B:08x}',
                'C': f'{C:08x}',
                'D': f'{D:08x}',
                'func': round_name,
                'M_index': g
            })
    
    state[0] = (state[0] + A) & 0xFFFFFFFF
    state[1] = (state[1] + B) & 0xFFFFFFFF
    state[2] = (state[2] + C) & 0xFFFFFFFF
    state[3] = (state[3] + D) & 0xFFFFFFFF
    
    return state, steps


def compute_md5_hash(message):
    """Compute MD5 hash"""
    all_steps = []
    
    padded, original_len, bit_len = md5_pad_message(message)
    
    all_steps.append({
        'phase': 'Padding',
        'original_message': message if isinstance(message, str) else message.decode('utf-8', errors='replace'),
        'original_length': original_len,
        'bit_length': bit_len,
        'padded_hex': padded.hex(),
        'padded_length': len(padded)
    })
    
    state = MD5_INIT.copy()
    
    all_steps.append({
        'phase': 'Initialization',
        'A': f'{state[0]:08x}',
        'B': f'{state[1]:08x}',
        'C': f'{state[2]:08x}',
        'D': f'{state[3]:08x}'
    })
    
    block_steps = []
    for i in range(0, len(padded), 64):
        block = padded[i:i+64]
        state, steps = md5_process_block(block, state, i // 64 + 1)
        
        block_steps.append({
            'block_num': i // 64 + 1,
            'block_hex': block.hex(),
            'steps': steps,
            'state_after': {
                'A': f'{state[0]:08x}',
                'B': f'{state[1]:08x}',
                'C': f'{state[2]:08x}',
                'D': f'{state[3]:08x}'
            }
        })
    
    all_steps.append({
        'phase': 'Block Processing',
        'blocks': block_steps
    })
    
    hash_bytes = struct.pack('<4I', *state)
    hash_hex = hash_bytes.hex()
    
    all_steps.append({
        'phase': 'Final Hash',
        'hash': hash_hex,
        'hash_length': len(hash_bytes) * 8
    })
    
    return hash_hex, all_steps


# ============================================================
# CMAC with MD5 → DES Flow (Complete Implementation)
# ============================================================

def des_cmac_generate_subkeys(key):
    """Generate K1 and K2 subkeys for DES-CMAC (64-bit)"""
    steps = []
    Rb = 0x1B  # Polynomial for 64-bit blocks
    
    # Encrypt zero block with key
    zero_block = bytes([0] * 8)
    zero_bits = bytes_to_bits_des(zero_block)
    key_bits = bytes_to_bits_des(key)
    
    L_bits, _ = des_encrypt_block(zero_bits, key_bits)
    L_bytes = bits_to_bytes_des(L_bits)
    L_int = int.from_bytes(L_bytes, 'big')
    
    steps.append({
        'step': 1,
        'operation': 'Encrypt Zero Block',
        'input': zero_block.hex(),
        'output': L_bytes.hex(),
        'details': 'L = DES(K, 0^64)'
    })
    
    # Generate K1
    K1_int = (L_int << 1) & ((1 << 64) - 1)
    if L_int & (1 << 63):  # MSB is 1
        K1_int ^= Rb
        xor_applied = True
    else:
        xor_applied = False
    
    K1 = K1_int.to_bytes(8, 'big')
    
    steps.append({
        'step': 2,
        'operation': 'Generate K1',
        'input': L_bytes.hex(),
        'output': K1.hex(),
        'details': f'K1 = (L << 1) {"⊕ Rb" if xor_applied else ""}',
        'msb_check': f'MSB(L) = {1 if xor_applied else 0}'
    })
    
    # Generate K2
    K2_int = (K1_int << 1) & ((1 << 64) - 1)
    if K1_int & (1 << 63):  # MSB is 1
        K2_int ^= Rb
        xor_applied2 = True
    else:
        xor_applied2 = False
    
    K2 = K2_int.to_bytes(8, 'big')
    
    steps.append({
        'step': 3,
        'operation': 'Generate K2',
        'input': K1.hex(),
        'output': K2.hex(),
        'details': f'K2 = (K1 << 1) {"⊕ Rb" if xor_applied2 else ""}',
        'msb_check': f'MSB(K1) = {1 if xor_applied2 else 0}'
    })
    
    steps.append({
        'step': 4,
        'operation': 'Rb Constant',
        'value': f'0x{Rb:02x}',
        'details': 'Polynomial constant for 64-bit blocks'
    })
    
    return K1, K2, steps


def md5_to_64bit_key(message):
    """
    Step 1: Hash message with MD5
    Step 2: Extract 64-bit from MD5 hash
    """
    steps = []
    
    # Compute MD5 hash (128-bit)
    md5_result, md5_steps = compute_md5_hash(message)
    
    steps.append({
        'phase': 'MD5 Hash Generation',
        'input_message': message if isinstance(message, str) else message.decode('utf-8', errors='replace'),
        'md5_full': md5_result,
        'md5_bits': 128,
        'md5_bytes': 16
    })
    
    # Extract first 64 bits (8 bytes / 16 hex chars)
    des_key_hex = md5_result[:16]
    des_key = bytes.fromhex(des_key_hex)
    
    steps.append({
        'phase': '64-bit Extraction',
        'method': 'First 64 bits of MD5',
        'extracted_hex': des_key_hex,
        'extracted_bits': 64,
        'extracted_bytes': 8
    })
    
    return des_key, md5_result, steps, md5_steps


def cmac_message_only(message, output_bits=64):
    """
    Complete CMAC Flow (Message Only):
    1. Input Message
    2. MD5 Hash → 128-bit
    3. Extract 64-bit
    4. Use as DES key
    5. Encrypt message with DES
    6. Output n-bit CMAC
    """
    all_steps = []
    
    # Step 1 & 2: Message → MD5 → 64-bit key
    des_key, md5_hash, key_steps, md5_detail_steps = md5_to_64bit_key(message)
    
    all_steps.append({
        'phase': 'Step 1-2: MD5 Hash & Key Derivation',
        'key_derivation_steps': key_steps,
        'md5_details': md5_detail_steps,
        'derived_key_hex': des_key.hex(),
        'derived_key_bits': 64
    })
    
    # Step 3: Generate CMAC subkeys (K1, K2)
    K1, K2, subkey_steps = des_cmac_generate_subkeys(des_key)
    
    all_steps.append({
        'phase': 'Step 3: CMAC Subkey Generation',
        'K1': K1.hex(),
        'K2': K2.hex(),
        'steps': subkey_steps
    })
    
    # Step 4: Prepare message (padding if needed)
    if isinstance(message, str):
        message = message.encode()
    
    block_size = 8  # DES block size
    msg_len = len(message)
    
    padding_info = []
    
    # Check if padding needed
    if msg_len == 0 or msg_len % block_size != 0:
        # Need padding
        pad_len = block_size - (msg_len % block_size)
        padding = b'\x80' + b'\x00' * (pad_len - 1)
        padded_message = message + padding
        last_key = K2
        
        padding_info.append({
            'padding_needed': True,
            'original_length': msg_len,
            'original_hex': message.hex(),
            'padding_length': pad_len,
            'padding_hex': padding.hex(),
            'padding_pattern': '0x80 followed by 0x00',
            'padded_message_hex': padded_message.hex(),
            'padded_length': len(padded_message),
            'subkey_used': 'K2',
            'reason': 'Message not multiple of block size'
        })
    else:
        # No padding needed
        padded_message = message
        last_key = K1
        
        padding_info.append({
            'padding_needed': False,
            'original_length': msg_len,
            'original_hex': message.hex(),
            'padding_length': 0,
            'padded_message_hex': padded_message.hex(),
            'padded_length': len(padded_message),
            'subkey_used': 'K1',
            'reason': 'Message is exact multiple of block size'
        })
    
    all_steps.append({
        'phase': 'Step 4: Message Padding',
        'block_size': block_size,
        'block_size_bits': block_size * 8,
        'padding_info': padding_info
    })
    
    # Step 5: Split into blocks
    blocks = [padded_message[i:i+block_size] for i in range(0, len(padded_message), block_size)]
    num_blocks = len(blocks)
    
    all_steps.append({
        'phase': 'Step 5: Block Splitting',
        'num_blocks': num_blocks,
        'blocks': [{'block_num': i+1, 'hex': blocks[i].hex()} for i in range(num_blocks)]
    })
    
    # Step 6: Process blocks with DES
    mac = bytes([0] * 8)
    mac_int = 0
    block_steps = []
    key_bits = bytes_to_bits_des(des_key)
    
    for i, block in enumerate(blocks):
        is_last = (i == len(blocks) - 1)
        block_int = int.from_bytes(block, 'big')
        
        step_info = {
            'block_num': i + 1,
            'is_last': is_last,
            'block_hex': block.hex()
        }
        
        # XOR with previous MAC
        xor_result = mac_int ^ block_int
        step_info['previous_mac_hex'] = f'{mac_int:016x}'
        step_info['after_xor_hex'] = f'{xor_result:016x}'
        
        # If last block, XOR with subkey
        if is_last:
            subkey_int = int.from_bytes(last_key, 'big')
            xor_result ^= subkey_int
            step_info['subkey_hex'] = last_key.hex()
            step_info['subkey_name'] = 'K2' if last_key == K2 else 'K1'
            step_info['after_subkey_xor_hex'] = f'{xor_result:016x}'
        else:
            step_info['subkey_hex'] = 'N/A'
            step_info['subkey_name'] = 'N/A'
            step_info['after_subkey_xor_hex'] = 'N/A'
        
        # DES encrypt
        input_bytes = xor_result.to_bytes(8, 'big')
        input_bits = bytes_to_bits_des(input_bytes)
        
        encrypted_bits, des_steps = des_encrypt_block(input_bits, key_bits)
        encrypted_bytes = bits_to_bytes_des(encrypted_bits)
        
        mac_int = int.from_bytes(encrypted_bytes, 'big')
        mac = encrypted_bytes
        
        step_info['des_input_hex'] = input_bytes.hex()
        step_info['des_output_hex'] = mac.hex()
        step_info['current_mac_hex'] = mac.hex()
        
        block_steps.append(step_info)
    
    all_steps.append({
        'phase': 'Step 6: DES Encryption (Block Processing)',
        'cipher': 'DES',
        'key_used_hex': des_key.hex(),
        'steps': block_steps
    })
    
    # Step 7: Output (truncate if needed)
    full_mac = mac
    full_mac_bits = len(mac) * 8
    
    if output_bits < full_mac_bits:
        truncate_bytes = (output_bits + 7) // 8
        mac = mac[:truncate_bytes]
        
        # If not byte-aligned, mask extra bits
        if output_bits % 8 != 0:
            remaining_bits = output_bits % 8
            mask = (0xFF << (8 - remaining_bits)) & 0xFF
            mac = bytes([mac[0] & mask]) + mac[1:]
        
        truncated = True
    else:
        truncated = False
    
    all_steps.append({
        'phase': 'Step 7: Final CMAC Output',
        'full_mac_hex': full_mac.hex(),
        'full_mac_bits': full_mac_bits,
        'requested_bits': output_bits,
        'truncated': truncated,
        'final_mac_hex': mac.hex(),
        'final_mac_bits': len(mac) * 8
    })
    
    return mac, all_steps, des_key, md5_hash


def cmac_verify_message_only(message, received_mac, output_bits=64):
    """Verify CMAC (message-only mode)"""
    
    computed_mac, steps, des_key, md5_hash = cmac_message_only(message, output_bits)
    
    is_valid = (computed_mac == received_mac)
    
    steps.append({
        'phase': 'Verification',
        'computed_mac_hex': computed_mac.hex(),
        'received_mac_hex': received_mac.hex(),
        'match': is_valid,
        'result': 'VALID ✓' if is_valid else 'INVALID ✗'
    })
    
    return is_valid, computed_mac, steps, des_key, md5_hash


# ============================================================
#                    ROUTES
# ============================================================
@app.route("/")
def home():
    return render_template("index.html", page="home")


@app.route("/ex1")
def ex1():
    return render_template("index.html", page="ex1")


@app.route("/ex2")
def ex2():
    return render_template("index.html", page="ex2")


@app.route("/ex3")
def ex3():
    return render_template("index.html", page="ex3")


@app.route("/ex4")
def ex4():
    return render_template("index.html", page="ex4")


@app.route("/vigenere", methods=["GET", "POST"])
def vigenere():
    result, steps, mode, error = None, None, None, None
    if request.method == "POST":
        text = request.form.get("text", "")
        key = request.form.get("key", "")
        mode = request.form.get("mode", "enc")
        if not text or not key:
            error = "Please provide both text and key"
        elif not key.isalpha():
            error = "Key must contain only letters"
        else:
            if mode == "enc":
                result, steps = vigenere_encrypt_full(text, key)
            else:
                result, steps = vigenere_decrypt_full(text, key)
    return render_template("index.html", page="vigenere", result=result, steps=steps, mode=mode, error=error)


@app.route("/playfair", methods=["GET", "POST"])
def playfair():
    result, steps, matrix, mode, error = None, None, None, None, None
    if request.method == "POST":
        text = request.form.get("text", "")
        key = request.form.get("key", "")
        mode = request.form.get("mode", "enc")
        if not text or not key:
            error = "Please provide both text and key"
        else:
            matrix = generate_key_matrix(key)
            if mode == "enc":
                result, steps = playfair_encrypt_full(text, matrix)
            else:
                result, steps = playfair_decrypt_full(text, matrix)
    return render_template("index.html", page="playfair", result=result, steps=steps, matrix=matrix, mode=mode, error=error)


@app.route("/affine", methods=["GET", "POST"])
def affine():
    result, steps, inv, mode, error = None, None, None, None, None
    valid_a_values = get_valid_a_values()
    if request.method == "POST":
        text = request.form.get("text", "")
        mode = request.form.get("mode", "enc")
        try:
            a = int(request.form.get("a", 0))
            b = int(request.form.get("b", 0))
        except ValueError:
            error = "Values 'a' and 'b' must be integers"
            return render_template("index.html", page="affine", error=error, valid_a_values=valid_a_values)
        if not text:
            error = "Please provide text"
        elif not is_valid_affine_a(a):
            error = f"Invalid 'a' = {a}. Must be coprime with 26. Valid: {valid_a_values}"
        else:
            if mode == "enc":
                result, steps = affine_encrypt_full(text, a, b)
            else:
                result, steps, inv = affine_decrypt_full(text, a, b)
                if result is None:
                    error = f"Cannot decrypt: modular inverse of {a} does not exist"
    return render_template("index.html", page="affine", result=result, steps=steps, inv=inv, mode=mode, error=error, valid_a_values=valid_a_values)


@app.route("/hill", methods=["GET", "POST"])
def hill():
    result, steps, mode, error, inv_matrix, det = None, None, None, None, None, None
    if request.method == "POST":
        text = request.form.get("text", "")
        mode = request.form.get("mode", "enc")
        try:
            k00 = int(request.form.get("k00", 0))
            k01 = int(request.form.get("k01", 0))
            k10 = int(request.form.get("k10", 0))
            k11 = int(request.form.get("k11", 0))
            key_matrix = [[k00, k01], [k10, k11]]
        except ValueError:
            error = "Key matrix values must be integers"
            return render_template("index.html", page="hill", error=error)
        if not text:
            error = "Please provide text"
        else:
            det_val = (k00 * k11 - k01 * k10) % 26
            if not is_valid_affine_a(det_val):
                error = f"Invalid matrix. Det = {det_val} must be coprime with 26."
            else:
                if mode == "enc":
                    result, steps = hill_encrypt(text, key_matrix)
                else:
                    result, steps, inv_matrix, det = hill_decrypt(text, key_matrix)
                    if result is None:
                        error = f"Matrix not invertible mod 26"
    return render_template("index.html", page="hill", result=result, steps=steps, mode=mode, error=error, inv_matrix=inv_matrix)


@app.route("/euclidean", methods=["GET", "POST"])
def euclidean():
    result, steps, error, calc_type = None, None, None, "gcd"
    a_val, b_val, m_val, x_val, y_val, inverse = None, None, None, None, None, None
    
    if request.method == "POST":
        calc_type = request.form.get("calc_type", "gcd")
        try:
            if calc_type == "gcd":
                a_val = int(request.form.get("a", 0))
                b_val = int(request.form.get("b", 0))
                if a_val <= 0 or b_val <= 0:
                    error = "Please provide positive integers"
                else:
                    result, steps = euclidean_gcd(a_val, b_val)
            elif calc_type == "extended":
                a_val = int(request.form.get("a", 0))
                b_val = int(request.form.get("b", 0))
                result, x_val, y_val, steps = extended_euclidean(a_val, b_val)
            elif calc_type == "modinv":
                a_val = int(request.form.get("a", 0))
                m_val = int(request.form.get("m", 0))
                if a_val <= 0 or m_val <= 0:
                    error = "Please provide positive integers"
                else:
                    inverse, steps = modular_inverse_euclidean(a_val, m_val)
                    if inverse is None:
                        error = "Modular inverse does not exist (GCD ≠ 1)"
                    else:
                        result = inverse
        except ValueError:
            error = "Please enter valid integers"
    
    return render_template("index.html", page="euclidean", result=result, steps=steps, error=error,
                          calc_type=calc_type, a_val=a_val, b_val=b_val, m_val=m_val,
                          x_val=x_val, y_val=y_val, inverse=inverse)


@app.route("/fermat", methods=["GET", "POST"])
def fermat():
    result, steps, error, calc_type = None, None, None, None
    a_val, p_val, base_val, exp_val, mod_val = None, None, None, None, None
    n_val, k_val, is_prime, phi_val = None, None, None, None
    
    if request.method == "POST":
        calc_type = request.form.get("calc_type", "verify")
        try:
            if calc_type == "verify":
                a_val = int(request.form.get("a", 0))
                p_val = int(request.form.get("p", 0))
                if a_val <= 0 or p_val <= 1:
                    error = "Please provide valid positive integers (p > 1)"
                elif a_val % p_val == 0:
                    error = f"{a_val} is divisible by {p_val}. Theorem requires gcd(a,p) = 1"
                else:
                    result, steps = verify_fermat(a_val, p_val)
            elif calc_type == "modexp":
                base_val = int(request.form.get("base", 0))
                exp_val = int(request.form.get("exp", 0))
                mod_val = int(request.form.get("mod", 0))
                if mod_val <= 0:
                    error = "Modulus must be positive"
                elif exp_val < 0:
                    error = "Exponent must be non-negative"
                else:
                    result, steps = mod_exp(base_val, exp_val, mod_val)
            elif calc_type == "modinv":
                a_val = int(request.form.get("a", 0))
                p_val = int(request.form.get("p", 0))
                if a_val <= 0 or p_val <= 1:
                    error = "Please provide valid positive integers"
                elif not is_prime_simple(p_val):
                    error = f"{p_val} is not prime. Fermat's method requires prime modulus."
                elif gcd(a_val, p_val) != 1:
                    error = f"gcd({a_val}, {p_val}) ≠ 1. No inverse exists."
                else:
                    result, steps = fermat_mod_inverse(a_val, p_val)
            elif calc_type == "primality":
                n_val = int(request.form.get("n", 0))
                k_val = int(request.form.get("k", 5))
                if n_val <= 0:
                    error = "Please provide a positive integer"
                else:
                    k_val = min(max(k_val, 1), 20)
                    is_prime, steps = fermat_primality_test(n_val, k_val)
                    result = is_prime
            elif calc_type == "euler":
                a_val = int(request.form.get("a", 0))
                n_val = int(request.form.get("n", 0))
                if a_val <= 0 or n_val <= 1:
                    error = "Please provide valid positive integers (n > 1)"
                else:
                    result, phi_val, steps = verify_euler(a_val, n_val)
                    if result is None:
                        error = f"gcd({a_val}, {n_val}) ≠ 1. Euler's theorem doesn't apply."
        except ValueError:
            error = "Please enter valid integers"
        except Exception as e:
            error = f"Error: {str(e)}"
    
    return render_template("index.html", page="fermat", result=result, steps=steps, error=error,
                          calc_type=calc_type, a_val=a_val, p_val=p_val, base_val=base_val,
                          exp_val=exp_val, mod_val=mod_val, n_val=n_val, k_val=k_val,
                          is_prime=is_prime, phi_val=phi_val)


@app.route("/rsa", methods=["GET", "POST"])
def rsa():
    key_result = None
    key_steps = None
    key_error = None
    p_val, q_val, e_val, n_val, phi_val, d_val = None, None, None, None, None, None
    public_key, private_key = None, None
    
    enc_result = None
    enc_steps = None
    enc_error = None
    
    dec_result = None
    dec_steps = None
    dec_error = None
    
    operation = None
    
    if request.method == "POST":
        operation = request.form.get("operation", "keygen")
        
        try:
            if operation == "keygen":
                p_val = int(request.form.get("p", 0))
                q_val = int(request.form.get("q", 0))
                e_input = request.form.get("e", "").strip()
                e_val = int(e_input) if e_input else None
                
                n_val, phi_val, e_val, d_val, keys, key_steps, key_error = generate_rsa_keys(p_val, q_val, e_val)
                
                if not key_error:
                    public_key = (e_val, n_val)
                    private_key = (d_val, n_val)
                    key_result = {
                        'n': n_val,
                        'phi_n': phi_val,
                        'e': e_val,
                        'd': d_val,
                        'public_key': public_key,
                        'private_key': private_key
                    }
            
            elif operation == "encrypt":
                plaintext = request.form.get("plaintext", "")
                e_val = int(request.form.get("enc_e", 0))
                n_val = int(request.form.get("enc_n", 0))
                
                if not plaintext:
                    enc_error = "Please provide plaintext"
                elif e_val <= 0 or n_val <= 0:
                    enc_error = "Please provide valid e and n values"
                else:
                    enc_result, enc_steps, enc_error = rsa_encrypt_text(plaintext, e_val, n_val)
            
            elif operation == "decrypt":
                ciphertext = request.form.get("ciphertext", "")
                d_val = int(request.form.get("dec_d", 0))
                n_val = int(request.form.get("dec_n", 0))
                
                if not ciphertext:
                    dec_error = "Please provide ciphertext"
                elif d_val <= 0 or n_val <= 0:
                    dec_error = "Please provide valid d and n values"
                else:
                    dec_result, dec_steps = rsa_decrypt_text(ciphertext, d_val, n_val)
        
        except ValueError as e:
            if operation == "keygen":
                key_error = "Please enter valid integers for p, q, and e"
            elif operation == "encrypt":
                enc_error = "Please enter valid integers"
            else:
                dec_error = "Please enter valid integers"
        except Exception as e:
            if operation == "keygen":
                key_error = f"Error: {str(e)}"
            elif operation == "encrypt":
                enc_error = f"Error: {str(e)}"
            else:
                dec_error = f"Error: {str(e)}"
    
    return render_template("index.html", page="rsa",
                          operation=operation,
                          key_result=key_result, key_steps=key_steps, key_error=key_error,
                          p_val=p_val, q_val=q_val, e_val=e_val, n_val=n_val,
                          phi_val=phi_val, d_val=d_val,
                          public_key=public_key, private_key=private_key,
                          enc_result=enc_result, enc_steps=enc_steps, enc_error=enc_error,
                          dec_result=dec_result, dec_steps=dec_steps, dec_error=dec_error)


@app.route("/aes", methods=["GET", "POST"])
def aes():
    result, steps, error, mode, op_mode = None, None, None, None, None
    if request.method == "POST":
        text = request.form.get("text", "")
        key_str = request.form.get("key", "")
        key_format = request.form.get("key_format", "hex")
        mode = request.form.get("mode", "enc")
        op_mode = request.form.get("op_mode", "ecb")
        
        if not text:
            error = "Please provide text"
        elif mode == "enc" and not text.replace(' ', '').isalpha():
            error = "Plaintext must contain only alphabetic characters"
        else:
            key, key_error = parse_key(key_str, key_format, 128)
            if key_error:
                error = key_error
            else:
                try:
                    if mode == "enc":
                        result_bytes, steps = aes_encrypt(text, key, op_mode)
                        result = result_bytes.hex()
                    else:
                        cipher_bytes = bytes.fromhex(text.replace(' ', ''))
                        result_bytes, steps = aes_decrypt(cipher_bytes, key, op_mode)
                        result = result_bytes.decode('utf-8', errors='replace')
                except Exception as e:
                    error = f"Error: {str(e)}"
    
    return render_template("index.html", page="aes", result=result, steps=steps, error=error, mode=mode, op_mode=op_mode, aes_iv=AES_IV.hex())


@app.route("/des", methods=["GET", "POST"])
def des_route():
    result, steps, error, mode, op_mode = None, None, None, None, None
    if request.method == "POST":
        text = request.form.get("text", "")
        key_str = request.form.get("key", "")
        key_format = request.form.get("key_format", "hex")
        mode = request.form.get("mode", "enc")
        op_mode = request.form.get("op_mode", "ecb")
        
        if not text:
            error = "Please provide text"
        elif mode == "enc" and not text.replace(' ', '').isalpha():
            error = "Plaintext must contain only alphabetic characters"
        else:
            key, key_error = parse_key(key_str, key_format, 64)
            if key_error:
                error = key_error
            else:
                try:
                    if mode == "enc":
                        result_bytes, steps = des_encrypt(text, key, op_mode)
                        result = result_bytes.hex()
                    else:
                        cipher_bytes = bytes.fromhex(text.replace(' ', ''))
                        result_bytes, steps = des_decrypt(cipher_bytes, key, op_mode)
                        result = result_bytes.decode('utf-8', errors='replace')
                except Exception as e:
                    error = f"Error: {str(e)}"
    
    return render_template("index.html", page="des", result=result, steps=steps, error=error, mode=mode, op_mode=op_mode, des_iv=DES_IV.hex())

@app.route("/cmac", methods=["GET", "POST"])
def cmac():
    result, steps, error, mode = None, None, None, None
    verification_result = None
    md5_hash_value = None
    des_key_value = None
    
    if request.method == "POST":
        message = request.form.get("message", "")
        mode = request.form.get("mode", "generate")
        
        try:
            output_bits = int(request.form.get("output_bits", 64))
            if output_bits <= 0 or output_bits > 64:
                error = "Output bits must be between 1 and 64"
                return render_template("index.html", page="cmac", error=error, mode=mode)
        except ValueError:
            error = "Invalid output bits value"
            return render_template("index.html", page="cmac", error=error, mode=mode)
        
        if not message:
            error = "Please provide a message"
        else:
            try:
                if mode == "generate":
                    # Generate CMAC
                    mac, steps, des_key, md5_hash_value = cmac_message_only(message, output_bits)
                    result = mac.hex()
                    des_key_value = des_key.hex()
                    
                else:  # verify mode
                    received_mac_str = request.form.get("mac", "")
                    if not received_mac_str:
                        error = "Please provide MAC to verify"
                    else:
                        received_mac = bytes.fromhex(received_mac_str.replace(' ', ''))
                        
                        is_valid, computed_mac, steps, des_key, md5_hash_value = cmac_verify_message_only(
                            message, received_mac, output_bits
                        )
                        
                        verification_result = is_valid
                        result = computed_mac.hex()
                        des_key_value = des_key.hex()
                        
            except Exception as e:
                error = f"Error: {str(e)}"
                import traceback
                print(traceback.format_exc())
    
    return render_template("index.html", page="cmac", result=result, steps=steps, 
                          error=error, mode=mode, verification_result=verification_result,
                          md5_hash=md5_hash_value, des_key=des_key_value)

@app.route("/md5", methods=["GET", "POST"])
def md5_route():
    result, steps, error = None, None, None
    
    if request.method == "POST":
        message = request.form.get("message", "")
        
        if not message:
            error = "Please provide a message"
        else:
            try:
                result, steps = compute_md5_hash(message)
            except Exception as e:
                error = f"Error: {str(e)}"
    
    return render_template("index.html", page="md5", result=result, steps=steps, error=error)


if __name__ == "__main__":
    app.run(debug=True)