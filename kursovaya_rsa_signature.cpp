#include <iostream>
#include <fstream>
#include <string>
#include <random>
#include <iomanip>
#include <sstream>
#include <cstdint>
#include <chrono>
#include <limits>
#include <vector>
#include <algorithm>
#include <openssl/evp.h>
#include <openssl/err.h>
using namespace std;

random_device rd;
mt19937_64 rng(rd());

vector<uint8_t> sha256_hash(const string& data) {
    vector<uint8_t> hash(EVP_MAX_MD_SIZE);
    unsigned int hash_len = 0;

    EVP_MD_CTX* ctx = EVP_MD_CTX_new();
    if (!ctx) {
        throw runtime_error("Не удалось создать контекст для хеширования");
    }

    //инициализация контекста для SHA-256
    if (EVP_DigestInit_ex(ctx, EVP_sha256(), NULL) != 1) {
        EVP_MD_CTX_free(ctx);
        throw runtime_error("Не удалось инициализировать SHA-256");
    }

    //заполнение хеша данными
    if (EVP_DigestUpdate(ctx, data.c_str(), data.size()) != 1) {
        EVP_MD_CTX_free(ctx);
        throw runtime_error("Не удалось обновить хеш данными");
    }

    //получение финального хеша
    if (EVP_DigestFinal_ex(ctx, hash.data(), &hash_len) != 1) {
        EVP_MD_CTX_free(ctx);
        throw runtime_error("Не удалось получить финальный хеш");
    }

    EVP_MD_CTX_free(ctx);

    //изменяем размер вектора до фактической длины хеша
    hash.resize(hash_len);
    return hash;
}

//преобразование хеша в число (первые 8 байт для 64-битного RSA)
uint64_t hash_to_uint64(const vector<uint8_t>& hash) {
    uint64_t result = 0;
    for (int i = 0; i < 8 && i < hash.size(); i++) {
        result = (result << 8) | hash[i];
    }
    return result;
}

class RSASignatureSystem {
private:
    uint64_t n = 0, e = 65537, d = 0;

    static uint64_t mulmod(uint64_t a, uint64_t b, uint64_t mod) {
        uint64_t res = 0;
        a %= mod;
        while (b > 0) {
            if (b & 1)
                res = (res + a) % mod;
            a = (a * 2) % mod;
            b >>= 1;
        }
        return res % mod;
    }

    static uint64_t mod_pow(uint64_t base, uint64_t exp, uint64_t mod) {
        if (mod == 1) return 0;
        uint64_t result = 1;
        base %= mod;
        while (exp > 0) {
            if (exp & 1)
                result = mulmod(result, base, mod);
            base = mulmod(base, base, mod);
            exp >>= 1;
        }
        return result;
    }

    static uint64_t gcd(uint64_t a, uint64_t b) {
        while (b != 0) {
            uint64_t t = b;
            b = a % b;
            a = t;
        }
        return a;
    }

    static uint64_t mod_inverse(uint64_t a, uint64_t m) {
        int64_t m0 = m, y = 0, x = 1;
        if (m == 1) return 0;

        while (a > 1) {
            uint64_t q = a / m;
            uint64_t t = m;
            m = a % m;
            a = t;
            t = y;
            y = x - q * y;
            x = t;
        }

        if (x < 0) x += m0;
        return x;
    }

    static bool miller_rabin_test(uint64_t n, uint64_t a) {
        if (n < 2) return false;
        if (n == 2 || n == 3) return true;
        if (n % 2 == 0) return false;

        uint64_t d = n - 1;
        uint64_t s = 0;
        while (d % 2 == 0) {
            d /= 2;
            s++;
        }

        uint64_t x = mod_pow(a, d, n);
        if (x == 1 || x == n - 1) return true;

        for (uint64_t i = 0; i < s - 1; i++) {
            x = mulmod(x, x, n);
            if (x == n - 1) return true;
            if (x == 1) return false;
        }

        return false;
    }

    static bool is_prime(uint64_t n) {
        if (n < 2) return false;
        if (n == 2 || n == 3) return true;
        if (n % 2 == 0) return false;

        uint64_t witnesses[] = { 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37 };
        for (uint64_t a : witnesses) {
            if (a < n && !miller_rabin_test(n, a)) {
                return false;
            }
        }
        return true;
    }

    uint64_t generate_prime(int bits) {
        if (bits > 31) bits = 31;

        uint64_t min_val = (1ULL << (bits - 1));
        uint64_t max_val = ((1ULL << bits) - 1);

        if (min_val < 2) min_val = 2;

        uniform_int_distribution<uint64_t> dist(min_val, max_val);
        uint64_t p;
        int attempts = 0;

        do {
            p = dist(rng) | 1ULL;
            if (++attempts > 100000) throw runtime_error("Не удалось сгенерировать простое число");
        } while (!is_prime(p));

        return p;
    }

public:
    RSASignatureSystem() = default;

    RSASignatureSystem(uint64_t n_val, uint64_t e_val, uint64_t d_val = 0) : n(n_val), e(e_val), d(d_val) {}

    void generate_keys(int bits = 512) {
        cout << "Генерация ключей RSA..." << endl;

        int prime_bits = bits / 2;
        if (prime_bits > 31) prime_bits = 31;

        uint64_t p = generate_prime(prime_bits);
        cout << "  Сгенерировано простое число p = " << p << endl;

        uint64_t q;
        do {
            q = generate_prime(prime_bits);
        } while (p == q);
        cout << "  Сгенерировано простое число q = " << q << endl;

        n = p * q;
        cout << "  Вычислен модуль n = p * q = " << n << endl;

        uint64_t phi = (p - 1) * (q - 1);
        cout << "  Вычислена функция Эйлера phi(n) = " << phi << endl;

        if (gcd(e, phi) != 1) {
            cout << "  e = 65537 не взаимно просто с phi(n), ищем другое e..." << endl;
            e = 3;
            while (e < phi && gcd(e, phi) != 1) {
                e += 2;
            }
        }
        cout << "  Открытая экспонента e = " << e << endl;

        d = mod_inverse(e, phi);
        if (d == 0) throw runtime_error("Не удалось вычислить секретную экспоненту d");
        cout << "  Секретная экспонента d = " << d << endl;

        uint64_t check = mulmod(e, d, phi);
        if (check != 1) {
            cout << "  Предыдущая d не подошла, пересчитываем..." << endl;

            int64_t t = 0, newt = 1;
            int64_t r = phi, newr = e;

            while (newr != 0) {
                int64_t quotient = r / newr;

                int64_t temp_t = t;
                t = newt;
                newt = temp_t - quotient * newt;

                int64_t temp_r = r;
                r = newr;
                newr = temp_r - quotient * newr;
            }

            if (r > 1) throw runtime_error("e не обратимо по модулю phi(n)");
            if (t < 0) t += phi;

            d = t;
            check = mulmod(e, d, phi);
        }

        cout << "  Проверка: e*d mod phi(n) = " << check << " OK" << endl;
        cout << "  Размер модуля n: " << (int)(log2(n) + 1) << " бит" << endl;
        cout << "Генерация ключей завершена успешно!" << endl;
    }

    uint64_t sign(const string& message) {
        if (n == 0 || d == 0) throw runtime_error("Ключи не сгенерированы или отсутствует секретный ключ!");

        vector<uint8_t> hash_bytes = sha256_hash(message);
        uint64_t hash_num = hash_to_uint64(hash_bytes);

        uint64_t m = hash_num % n;
        if (m < 2) m = 2; // Избегаем 0 и 1

        return mod_pow(m, d, n);
    }

    bool verify(const string& message, uint64_t signature) {
        if (n == 0 || e == 0) throw runtime_error("Ключи не сгенерированы или отсутствует открытый ключ!");

        vector<uint8_t> hash_bytes = sha256_hash(message);
        uint64_t hash_num = hash_to_uint64(hash_bytes);

        uint64_t expected_m = hash_num % n;
        if (expected_m < 2) expected_m = 2;

        uint64_t recovered_m = mod_pow(signature, e, n);

        return recovered_m == expected_m;
    }

    void save_public_key(const string& filename) {
        ofstream file(filename);
        if (!file) throw runtime_error("Не удалось создать файл: " + filename);

        file << "PUBLIC_KEY" << endl;
        file << "n=" << n << endl;
        file << "e=" << e << endl;

        file.close();
        cout << "Открытый ключ сохранен в файл: " << filename << endl;
    }

    void save_private_key(const string& filename) {
        ofstream file(filename);
        if (!file) throw runtime_error("Не удалось создать файл: " + filename);

        file << "PRIVATE_KEY" << endl;
        file << "n=" << n << endl;
        file << "e=" << e << endl;
        file << "d=" << d << endl;

        file.close();
        cout << "Закрытый ключ сохранен в файл: " << filename << endl;
    }

    static RSASignatureSystem load_public_key(const string& filename) {
        ifstream file(filename);
        if (!file) throw runtime_error("Не удалось открыть файл: " + filename);

        string line;
        uint64_t n_val = 0, e_val = 0;

        getline(file, line); //пропускаем заголовок

        while (getline(file, line)) {
            if (line.find("n=") == 0) {
                n_val = stoull(line.substr(2));
            }
            else if (line.find("e=") == 0) {
                e_val = stoull(line.substr(2));
            }
        }

        file.close();

        if (n_val == 0 || e_val == 0) {
            throw runtime_error("Неверный формат файла открытого ключа");
        }

        return RSASignatureSystem(n_val, e_val);
    }

    static RSASignatureSystem load_private_key(const string& filename) {
        ifstream file(filename);
        if (!file) throw runtime_error("Не удалось открыть файл: " + filename);

        string line;
        uint64_t n_val = 0, e_val = 0, d_val = 0;

        getline(file, line); //пропускаем заголовок

        while (getline(file, line)) {
            if (line.find("n=") == 0) {
                n_val = stoull(line.substr(2));
            }
            else if (line.find("e=") == 0) {
                e_val = stoull(line.substr(2));
            }
            else if (line.find("d=") == 0) {
                d_val = stoull(line.substr(2));
            }
        }

        file.close();

        if (n_val == 0 || e_val == 0 || d_val == 0) {
            throw runtime_error("Неверный формат файла закрытого ключа");
        }

        return RSASignatureSystem(n_val, e_val, d_val);
    }

    static void create_signed_file(const string& input_file, const string& private_key_file,
        const string& signed_file, const string& signature_file = "") {

        RSASignatureSystem rsa = load_private_key(private_key_file);

        ifstream in_file(input_file, ios::binary);
        if (!in_file) throw runtime_error("Не удалось открыть файл: " + input_file);

        string message((istreambuf_iterator<char>(in_file)), istreambuf_iterator<char>());
        in_file.close();

        cout << "Файл загружен: " << input_file << " (" << message.size() << " байт)" << endl;

        // Выводим SHA-256 хеш для наглядности
        vector<uint8_t> hash = sha256_hash(message);
        cout << "SHA-256 хеш файла: ";
        for (uint8_t byte : hash) {
            printf("%02x", byte);
        }
        cout << endl;

        cout << "Создание подписи..." << endl;
        uint64_t signature = rsa.sign(message);
        cout << "Подпись создана: " << signature << endl;

        ofstream out_file(signed_file, ios::binary);
        if (!out_file) throw runtime_error("Не удалось создать файл: " + signed_file);

        out_file.write(message.c_str(), message.size());

        string sig_str = "\n---RSA_SIGNATURE---\n" + to_string(signature);
        out_file.write(sig_str.c_str(), sig_str.size());

        out_file.close();
        cout << "Подписанный файл создан: " << signed_file << endl;

        if (!signature_file.empty()) {
            ofstream sig_file(signature_file);
            if (!sig_file) throw runtime_error("Не удалось создать файл: " + signature_file);

            sig_file << "SIGNATURE" << endl;
            sig_file << "original_file=" << input_file << endl;
            sig_file << "hash=SHA-256" << endl;
            sig_file << "signature=" << signature << endl;

            sig_file.close();
            cout << "Файл с подписью создан: " << signature_file << endl;
        }
    }

    static bool verify_signed_file(const string& signed_file, const string& public_key_file,
        string& original_content) {
        RSASignatureSystem rsa = load_public_key(public_key_file);

        ifstream in_file(signed_file, ios::binary);
        if (!in_file) throw runtime_error("Не удалось открыть файл: " + signed_file);

        string content((istreambuf_iterator<char>(in_file)), istreambuf_iterator<char>());
        in_file.close();

        size_t sig_pos = content.find("\n---RSA_SIGNATURE---\n");
        if (sig_pos == string::npos) {
            throw runtime_error("Файл не содержит подписи");
        }

        //разделяем содержимое и подпись
        original_content = content.substr(0, sig_pos);
        string signature_str = content.substr(sig_pos + 21); //21 = длина разделителя

        uint64_t signature;
        try {
            signature = stoull(signature_str);
        }
        catch (...) {
            throw runtime_error("Неверный формат подписи в файле");
        }

        cout << "Исходное содержимое извлечено (" << original_content.size() << " байт)" << endl;

        // Выводим SHA-256 хеш для наглядности
        vector<uint8_t> hash = sha256_hash(original_content);
        cout << "SHA-256 хеш файла: ";
        for (uint8_t byte : hash) {
            printf("%02x", byte);
        }
        cout << endl;

        cout << "Подпись из файла: " << signature << endl;

        cout << "Проверка подписи..." << endl;
        bool result = rsa.verify(original_content, signature);

        return result;
    }

    static bool verify_signature_file(const string& original_file, const string& signature_file,
        const string& public_key_file) {
        RSASignatureSystem rsa = load_public_key(public_key_file);

        ifstream orig_file(original_file, ios::binary);
        if (!orig_file) throw runtime_error("Не удалось открыть файл: " + original_file);

        string message((istreambuf_iterator<char>(orig_file)), istreambuf_iterator<char>());
        orig_file.close();

        ifstream sig_file(signature_file);
        if (!sig_file) throw runtime_error("Не удалось открыть файл: " + signature_file);

        string line;
        uint64_t signature = 0;

        while (getline(sig_file, line)) {
            if (line.find("signature=") == 0) {
                signature = stoull(line.substr(10));
                break;
            }
        }

        sig_file.close();

        if (signature == 0) {
            throw runtime_error("Не удалось извлечь подпись из файла");
        }

        cout << "Исходный файл: " << original_file << " (" << message.size() << " байт)" << endl;

        // Выводим SHA-256 хеш для наглядности
        vector<uint8_t> hash = sha256_hash(message);
        cout << "SHA-256 хеш файла: ";
        for (uint8_t byte : hash) {
            printf("%02x", byte);
        }
        cout << endl;

        cout << "Подпись из файла: " << signature << endl;

        //проверка подписи
        cout << "Проверка подписи..." << endl;
        return rsa.verify(message, signature);
    }

    //геттеры
    uint64_t get_n() const { return n; }
    uint64_t get_e() const { return e; }
    uint64_t get_d() const { return d; }
};

void print_menu() {
    cout << "========================================" << endl;
    cout << "  СИСТЕМА ЭЛЕКТРОННОЙ ПОДПИСИ RSA" << endl;
    cout << "========================================" << endl;
    cout << "1. Генерация ключей" << endl;
    cout << "2. Подпись файла" << endl;
    cout << "3. Проверка подписанного файла" << endl;
    cout << "4. Проверка файла с отдельной подписью" << endl;
    cout << "5. Выход" << endl;
    cout << "========================================" << endl;
    cout << "Выберите действие (1-5): ";
}

int main() {
    // Инициализация OpenSSL
    OpenSSL_add_all_digests();

    system("chcp 1251");

    while (true) {
        print_menu();

        int choice;
        cin >> choice;
        cin.ignore(); //очистка буфера

        cout << endl;

        switch (choice) {
        case 1: {
            //генерация ключей
            int key_size;
            cout << "Введите размер ключа (в битах, например 512): ";
            cin >> key_size;
            cin.ignore();

            RSASignatureSystem rsa;
            rsa.generate_keys(key_size);

            cout << endl;
            cout << "Сохранить ключи в файлы:" << endl;
            string pub_file, priv_file;

            cout << "Имя файла для открытого ключа (например: public.key): ";
            getline(cin, pub_file);
            cout << "Имя файла для закрытого ключа (например: private.key): ";
            getline(cin, priv_file);

            rsa.save_public_key(pub_file);
            rsa.save_private_key(priv_file);

            cout << endl << "Ключи успешно сохранены!" << endl;
            break;
        }

        case 2: {
            //сама подпись файла
            string input_file, private_key_file, signed_file, signature_file;

            cout << "Имя файла для подписи: ";
            getline(cin, input_file);
            cout << "Имя файла с закрытым ключом: ";
            getline(cin, private_key_file);
            cout << "Имя подписанного файла (результат): ";
            getline(cin, signed_file);

            cout << "Сохранить подпись в отдельный файл? (y/n): ";
            char save_separate;
            cin >> save_separate;
            cin.ignore();

            if (tolower(save_separate) == 'y') {
                cout << "Имя файла для подписи: ";
                getline(cin, signature_file);
                RSASignatureSystem::create_signed_file(input_file, private_key_file, signed_file, signature_file);
            }
            else {
                RSASignatureSystem::create_signed_file(input_file, private_key_file, signed_file);
            }

            cout << endl << "Файл успешно подписан!" << endl;
            break;
        }

        case 3: {
            //проверка подписанного файла
            string signed_file, public_key_file, output_file;

            cout << "Имя подписанного файла: ";
            getline(cin, signed_file);
            cout << "Имя файла с открытым ключом: ";
            getline(cin, public_key_file);

            string original_content;
            bool result = RSASignatureSystem::verify_signed_file(signed_file, public_key_file, original_content);

            cout << endl << "РЕЗУЛЬТАТ ПРОВЕРКИ: ";
            if (result) {
                cout << "ПОДПИСЬ ВЕРНА - файл не был изменен" << endl;

                cout << "Сохранить извлеченный исходный файл? (y/n): ";
                char save_original;
                cin >> save_original;
                cin.ignore();

                if (tolower(save_original) == 'y') {
                    cout << "Имя файла для сохранения исходного содержимого: ";
                    getline(cin, output_file);

                    ofstream out_file(output_file, ios::binary);
                    if (!out_file) throw runtime_error("Не удалось создать файл: " + output_file);

                    out_file.write(original_content.c_str(), original_content.size());
                    out_file.close();

                    cout << "Исходное содержимое сохранено в файл: " << output_file << endl;
                }
            }
            else {
                cout << "ПОДПИСЬ НЕВЕРНА - файл был изменен или поврежден!" << endl;
            }
            break;
        }

        case 4: {
            //проверка файла с отдельной подписью
            string original_file, signature_file, public_key_file;

            cout << "Имя исходного файла: ";
            getline(cin, original_file);
            cout << "Имя файла с подписью: ";
            getline(cin, signature_file);
            cout << "Имя файла с открытым ключом: ";
            getline(cin, public_key_file);

            bool result = RSASignatureSystem::verify_signature_file(original_file, signature_file, public_key_file);

            cout << endl << "РЕЗУЛЬТАТ ПРОВЕРКИ: ";
            if (result) {
                cout << "ПОДПИСЬ ВЕРНА - файл не был изменен" << endl;
            }
            else {
                cout << "ПОДПИСЬ НЕВЕРНА - файл был изменен или подпись недействительна!" << endl;
            }
            break;
        }

        case 5: {
            cout << "Выход из программы..." << endl;
            // Очистка OpenSSL
            EVP_cleanup();
            return 0;
        }

        default: {
            cout << "Неверный выбор. Попробуйте снова." << endl;
            break;
        }
        }

        cout << endl;
        cout << "Нажмите Enter для продолжения...";
        cin.get();
        cout << endl;
    }

    return 0;
}
