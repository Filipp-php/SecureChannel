using System.Numerics;
using System.Security.Cryptography;
using System.Text;

namespace SecureChannel
{
    
    class SecureChannelClient
    {

        BigInteger P;
        BigInteger Q;
        BigInteger N;
        BigInteger K;
        BigInteger H;
        Random Random;

        private void CheckParams()
        {
            /* Выполняет проверку параметров */
            BigInteger x, y;
            if (Extended_gcd(P, Q, out x, out y) != 1)
            {
                throw new Exception("Параметры p и q не взаимно простые");
            }
            x = 0; y = 0;
            if (Extended_gcd(N, K, out x, out y) != 1)
            {
                throw new Exception("Параметры n и k не взаимно простые");
            }
            if (!MillerRabinTest(P, 10)) throw new Exception("Число P не простое!");
            if (!MillerRabinTest(Q, 10)) throw new Exception("Число Q не простое!");
        }

        private void CountParams()
        {
            N = P * Q;
            BigInteger k_2, y;
            Extended_gcd(K * K, N, out k_2, out y);
            H = -ModN(k_2);
            CheckParams();
        }

        public BigInteger GetH () {
            return H;
        }

        public SecureChannelClient (BigInteger p, BigInteger q, BigInteger k)
        {
            P = p;
            Q = q;
            K = k;
            CountParams();
            Random = new Random();
        }

        public Tuple<BigInteger, BigInteger> Sign (BigInteger x, BigInteger y) {
            BigInteger a, b;
            if (Extended_gcd(x, N, out a, out b) != 1)
            {
                throw new Exception("Параметры x и N не взаимно простые");
            }
            a = 0; b = 0;
            if (Extended_gcd(y, N, out a, out b) != 1)
            {
                throw new Exception("Параметры y и N не взаимно простые");
            }
            BigInteger y_1, two_1;
            b = 0;
            Extended_gcd(y, N, out y_1, out b);
            b = 0;
            Extended_gcd(new BigInteger(2), N, out two_1, out b);
            two_1 = ModN(two_1);
            Tuple<BigInteger, BigInteger> sign = new Tuple<BigInteger, BigInteger>(
                ModN(two_1 * (x * y_1 + y)), ModN(two_1 * K * (x * y_1 - y))
            );
            return sign;
        }

        public bool CheckSign (BigInteger x, Tuple<BigInteger, BigInteger> sign, BigInteger h) {
            BigInteger check;
            check = ModN(sign.Item1 * sign.Item1 + h * sign.Item2 * sign.Item2);
            return x == check;
        }

        public BigInteger GetSecureMessage (BigInteger x, Tuple<BigInteger, BigInteger> sign, BigInteger k) {
            BigInteger k_1, k_2, b;
            b = 0;
            Extended_gcd(k, N, out k_1, out b);
            k_1 = ModN(k_1);
            b = 0;
            Extended_gcd(k * k, N, out k_2, out b);
            k_2 = ModN(k_2);
            BigInteger check = ModN(sign.Item1 * sign.Item1 - sign.Item2 * sign.Item2 * k_2);

            if (check == x) {
                BigInteger tmp, tmp_1;
                tmp = sign.Item1 + sign.Item2 * k_1;
                b = 0;
                Extended_gcd(tmp, N, out tmp_1, out b);
                tmp_1 = ModN(tmp_1);
                return x * tmp_1 % N;
            }
            return new BigInteger();
        }

        private BigInteger ModN(BigInteger item) {
            BigInteger result = item % N;
            if (result < 0) result = N + result;
            return result;
        } 

        private BigInteger RandomBigInt(BigInteger N)
        {
            byte[] bytes = N.ToByteArray();
            BigInteger R;
            do
            {
                Random.NextBytes(bytes);
                bytes[bytes.Length - 1] &= (byte)0x7F; //force sign bit to positive
                R = new BigInteger(bytes);
            } while (R >= N || R == 0);
            return R;
        }

        public bool MillerRabinTest(BigInteger n, int k)
        {
            /* тест Миллера — Рабина на простоту числа
             * производится k раундов проверки числа n на простоту
             */
            // если n == 2 или n == 3 - эти числа простые, возвращаем true
            if (n == 2 || n == 3)
                return true;

            // если n < 2 или n четное - возвращаем false
            if (n < 2 || n % 2 == 0)
                return false;

            // представим n − 1 в виде (2^s)·t, где t нечётно, это можно сделать последовательным делением n - 1 на 2
            BigInteger t = n - 1;

            int s = 0;

            while (t % 2 == 0)
            {
                t /= 2;
                s += 1;
            }

            // повторить k раз
            for (int i = 0; i < k; i++)
            {
                // выберем случайное целое число a в отрезке [2, n − 2]
                RNGCryptoServiceProvider rng = new RNGCryptoServiceProvider();

                byte[] _a = new byte[n.ToByteArray().LongLength];

                BigInteger a;

                do
                {
                    rng.GetBytes(_a);
                    a = new BigInteger(_a);
                }
                while (a < 2 || a >= n - 2);

                // x ← a^t mod n, вычислим с помощью возведения в степень по модулю
                BigInteger x = BigInteger.ModPow(a, t, n);

                // если x == 1 или x == n − 1, то перейти на следующую итерацию цикла
                if (x == 1 || x == n - 1)
                    continue;

                // повторить s − 1 раз
                for (int r = 1; r < s; r++)
                {
                    // x ← x^2 mod n
                    x = BigInteger.ModPow(x, 2, n);

                    // если x == 1, то вернуть "составное"
                    if (x == 1)
                        return false;

                    // если x == n − 1, то перейти на следующую итерацию внешнего цикла
                    if (x == n - 1)
                        break;
                }

                if (x != n - 1)
                    return false;
            }
            // вернуть "вероятно простое"
            return true;
        }

        public static BigInteger Extended_gcd(BigInteger a, BigInteger b, out BigInteger x, out BigInteger y)
        {   /* Расширенный алгоритм Евклида */

            if (a == 0)
            {
                x = 0;
                y = 1;
                return b;
            }

            BigInteger result = Extended_gcd(b % a, a, out x, out y);

            BigInteger newY = x;
            BigInteger newX = y - (b / a) * x;

            x = newX;
            y = newY;
            return result;

        }
    }

    internal class Program
    {
        static void Main(string[] args)
        {
            if (args.Length == 2)
            {
                string input = args[0];
                string output = args[1];
                if (!File.Exists(input))
                {
                    Console.WriteLine("Файл для ввода данных не существует");
                    return;
                }
                byte[] buffer = File.ReadAllBytes(input);
                string[] keys = Encoding.UTF8.GetString(buffer).Split(",");
                if (keys.Length == 7)
                {
                    BigInteger p = BigInteger.Parse(keys[0]);
                    BigInteger q = BigInteger.Parse(keys[1]);
                    BigInteger kAlice = BigInteger.Parse(keys[2]);
                    BigInteger kChecker = BigInteger.Parse(keys[3]);
                    BigInteger kBob = BigInteger.Parse(keys[4]);
                    BigInteger x = BigInteger.Parse(keys[5]);
                    BigInteger y = BigInteger.Parse(keys[6]);
                    SecureChannelClient Alice = new SecureChannelClient(p, q, kAlice);
                    SecureChannelClient Checker = new SecureChannelClient(p, q, kChecker);
                    SecureChannelClient Bob = new SecureChannelClient(p, q, kBob);

                    string outputBuffer = "";

                    Tuple<BigInteger, BigInteger> sign =
                        Alice.Sign(x, y);

                    outputBuffer += "Подпись: (" + sign.Item1 + ", " + sign.Item2 + ")";
                    outputBuffer += "\nПроверка подлинности: " + Checker.CheckSign(x, sign, Alice.GetH());
                    outputBuffer += "\nСекретное сообщение: " + Bob.GetSecureMessage(x, sign, kAlice);
                    File.WriteAllBytes(output, Encoding.UTF8.GetBytes(outputBuffer));
                }
                else
                {
                    Console.WriteLine("Файл для ввода данных не содержит нужных параметров");
                }
            }
            else
            {
                BigInteger p = new BigInteger(683);
                BigInteger q = new BigInteger(811);
                BigInteger kAlice = new BigInteger(3);
                BigInteger kChecker = new BigInteger(13);
                BigInteger kBob = new BigInteger(5);
                BigInteger x = new BigInteger(7);
                BigInteger y = new BigInteger(11);
                SecureChannelClient Alice = new SecureChannelClient(p, q, kAlice);
                SecureChannelClient Checker = new SecureChannelClient(p, q, kChecker);
                SecureChannelClient Bob = new SecureChannelClient(p, q, kBob);

                Tuple<BigInteger, BigInteger> sign = 
                    Alice.Sign(x, y);

                Console.WriteLine(sign.Item1 + ", " + sign.Item2);

                Console.WriteLine("Проверка подлинности: " + Checker.CheckSign(x, sign, Alice.GetH()));

                Console.WriteLine("Секретное сообщение: " + Bob.GetSecureMessage(x, sign, kAlice));
                
            }
        }
    }
}