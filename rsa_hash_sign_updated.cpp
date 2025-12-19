#include <iostream>
#include <fstream>
#include <vector>
#include <random>
#include <string>
#include <bitset>
#include <iterator>
#include <sstream>
#include <cstdint>

using namespace std;

const int HASH_LENGTH = 16;

long long mul_mod(long long a, long long b, long long mod) {
    if (mod <= 1) return 0;
    long long res = 0;
    a %= mod;
    if (a < 0) a += mod;
    while (b > 0) {
        if (b & 1) res = (res + a) % mod;
        a = (a << 1) % mod;
        b >>= 1;
    }
    return res;
}

long long mod_pow(long long base, long long exp, long long mod) {
    if (mod == 1) return 0;
    long long result = 1;
    base %= mod;
    if (base < 0) base += mod;
    while (exp > 0) {
        if (exp & 1) result = mul_mod(result, base, mod);
        base = mul_mod(base, base, mod);
        exp >>= 1;
    }
    return result;
}

bool is_prime(long long n) {
    if (n <= 1) return false;
    if (n <= 3) return true;
    if (n % 2 == 0 || n % 3 == 0) return false;
    for (long long i = 5; i * i <= n; i += 6)
        if (n % i == 0 || n % (i + 2) == 0)
            return false;
    return true;
}

long long gcd(long long a, long long b) {
    while (b != 0) {
        long long t = b;
        b = a % b;
        a = t;
    }
    return a;
}

long long generate_prime(long long min_val, long long max_val) {
    random_device rd;
    mt19937_64 gen(rd());
    uniform_int_distribution<long long> dist(min_val, max_val);

    long long p;
    int attempts = 0;
    const int max_attempts = 100000;
    do {
        if (++attempts > max_attempts) return -1;
        p = dist(gen);
        if (p < 2) p = 2;
    } while (!is_prime(p));
    return p;
}

long long mod_inverse(long long e, long long phi) {
    long long t = 0, newt = 1;
    long long r = phi, newr = e;
    while (newr != 0) {
        long long q = r / newr;
        swap(t, newt); newt -= q * t;
        swap(r, newr); newr -= q * r;
    }
    if (r > 1) return -1;
    if (t < 0) t += phi;
    return t;
}

//хеш меркля-домгара
string to_binary_string(const string& data) {
    string bin;
    for (unsigned char c : data) {
        bitset<8> b(c);
        bin += b.to_string();
    }
    return bin;
}

string merkle_damgard_hash(const string& bits) {
    string padded = bits + "1";
    while ((padded.size() + HASH_LENGTH) % HASH_LENGTH != 0) padded += "0";
    string len_bits = bitset<HASH_LENGTH>(bits.size()).to_string();
    padded += len_bits;

    string y(HASH_LENGTH, '0');
    for (size_t i = 0; i < padded.size(); i += HASH_LENGTH) {
        string block = padded.substr(i, HASH_LENGTH);
        string next;
        for (int j = 0; j < HASH_LENGTH; ++j) {
            next += ((block[j] ^ y[j]) & 1) ? '1' : '0';
        }
        y = next;
    }
    return y;
}

struct PrivateKey {
    long long p, q, d, N;
};

struct PublicKey {
    long long e, N;
};

void save_private_key(const PrivateKey& key, const string& filename) {
    ofstream out(filename);
    out << "p=" << key.p << "\n";
    out << "q=" << key.q << "\n";
    out << "d=" << key.d << "\n";
    out << "N=" << key.N << "\n";
    out.close();
}

void save_public_key(const PublicKey& key, const string& filename) {
    ofstream out(filename);
    out << "e=" << key.e << "\n";
    out << "N=" << key.N << "\n";
    out.close();
}

PrivateKey load_private_key(const string& filename) {
    ifstream in(filename);
    PrivateKey key{};
    string line;
    while (getline(in, line)) {
        if (line.substr(0, 2) == "p=") key.p = stoll(line.substr(2));
        else if (line.substr(0, 2) == "q=") key.q = stoll(line.substr(2));
        else if (line.substr(0, 2) == "d=") key.d = stoll(line.substr(2));
        else if (line.substr(0, 2) == "N=") key.N = stoll(line.substr(2));
    }
    in.close();
    return key;
}

PublicKey load_public_key(const string& filename) {
    ifstream in(filename);
    PublicKey key{};
    string line;
    while (getline(in, line)) {
        if (line.substr(0, 2) == "e=") key.e = stoll(line.substr(2));
        else if (line.substr(0, 2) == "N=") key.N = stoll(line.substr(2));
    }
    in.close();
    return key;
}
//подпитс
long long sign_message(const string& message, const PrivateKey& priv) {
    string bits = to_binary_string(message);
    string hash = merkle_damgard_hash(bits);
    unsigned long long h = 0;
    for (char c : hash) h = (h << 1) | (c - '0');
    return mod_pow(static_cast<long long>(h), priv.d, priv.N);
}
//проверка
bool verify_message(const string& message, long long signature, const PublicKey& pub) {
    string bits = to_binary_string(message);
    string hash = merkle_damgard_hash(bits);
    unsigned long long expected = 0;
    for (char c : hash) expected = (expected << 1) | (c - '0');

    long long recovered = mod_pow(signature, pub.e, pub.N);
    return (recovered == static_cast<long long>(expected));
}

//cохраняем подпись в бинарь
void save_signature(const string& sig_file, long long S) {
    ofstream out(sig_file, ios::binary);
    for (int i = 7; i >= 0; --i) {
        out.put((S >> (i * 8)) & 0xFF);
    }
    out.close();
}

//загрузка подписи из бинаря
long long load_signature(const string& sig_file) {
    ifstream in(sig_file, ios::binary);
    long long S = 0;
    for (int i = 0; i < 8; ++i) {
        unsigned char byte;
        in.get(reinterpret_cast<char&>(byte));
        S = (S << 8) | byte;
    }
    in.close();
    return S;
}

int main() {
    system("chcp 1251");
    
    while (true) {
        cout << "Выберите режим:\n1 — Генерация ключей\n2 — Подпись файла\n3 — Проверка подписи\n4 — Выход\nВаш выбор: ";

        int mode;
        cin >> mode;

        switch (mode) {
        case 1: {
            cout << "Генерация 2048-подобных ключей...\n";
            const long long min_val = 1000000000LL; //1 млрд
            const long long max_val = 2147483647LL; //2^31 - 1

            long long p = generate_prime(min_val, max_val);
            if (p == -1) { cerr << "Ошибка генерации p\n"; return 1; }
            long long q;
            do {
                q = generate_prime(min_val, max_val);
                if (q == -1) { cerr << "Ошибка генерации q\n"; return 1; }
            } while (q == p);

            long long N = p * q;
            long long phi = (p - 1) * (q - 1);
            long long e = 65537;
            while (gcd(e, phi) != 1) {
                e += 2;
                if (e >= phi) { cerr << "Не удалось подобрать e\n"; return 1; }
            }
            long long d = mod_inverse(e, phi);
            if (d == -1) { cerr << "Ошибка вычисления d\n"; return 1; }

            PrivateKey priv = { p, q, d, N };
            PublicKey pub = { e, N };

            save_private_key(priv, "private.key");
            save_public_key(pub, "public.key");
            cout << "Ключи сохранены: private.key, public.key\n";
            break;
        }

        case 2: {
            string file, priv_file;
            cout << "Имя файла для подписи: ";
            cin >> file;
            cout << "Имя файла закрытого ключа: ";
            cin >> priv_file;

            ifstream fin(file, ios::binary);
            if (!fin) { cerr << "Не удалось открыть файл\n"; return 1; }
            string data((istreambuf_iterator<char>(fin)), {});
            fin.close();

            PrivateKey priv = load_private_key(priv_file);
            long long S = sign_message(data, priv);
            string sig_file = file + ".sig";
            save_signature(sig_file, S);
            cout << "Подпись сохранена в " << sig_file << "\n";
            break;
        }

        case 3: {
            string file, pub_file, sig_file;
            cout << "Имя проверяемого файла: ";
            cin >> file;
            cout << "Имя файла подписи (.sig): ";
            cin >> sig_file;
            cout << "Имя файла открытого ключа: ";
            cin >> pub_file;

            ifstream fin(file, ios::binary);
            if (!fin) { cerr << "Не удалось открыть файл\n"; return 1; }
            string data((istreambuf_iterator<char>(fin)), {});
            fin.close();

            long long S = load_signature(sig_file);
            PublicKey pub = load_public_key(pub_file);

            bool valid = verify_message(data, S, pub);
            cout << "Результат проверки: " << (valid ? "ЦЕЛОСТНОСТЬ СОХРАНЕНА" : "ФАЙЛ ИЗМЕНЁН!") << "\n";
            break;
        }

        case 4:
            cout << "Выход из программы...\n";
            return 0;

        default:
            cerr << "Неверный режим. Выберите 1, 2, 3 или 4.\n";
            return 1;
        }

    }

    return 0;
}