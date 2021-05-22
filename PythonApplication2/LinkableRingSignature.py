### HASH FÜGGVÉNYEK

### Bemenetként egy stringet kap meg -> hash -> int


def H2( input ):
    return int( hashlib.sha512( ('Monero%s'%(input)).encode()).hexdigest(), 16 )



### Bemenetként egy stringet és egy elliptikus görbe Pontot kap meg
### Ezekből készit egy stringet amelyet hashel -> int
def H3(message, P1):
    
    str = "%s,%d,%d" % (message, P1.x, P1.y)
   
    return int( hashlib.sha512( ("Monero%s"%(str)).encode()).hexdigest(), 16 )


  
# keys - publikus kulcsokból készitett lenyomat ( mapelve)
# Y_Tilde = key_image - linkability
# message
# két elliptikus görbe pont ( P1, P2)
#Ezekből készit egy stringet és hasheli
def H1(keys, Y_tilde, message, P1, P2):
   
    str = "%s,%X,%X,%s,%X,%X,%X,%X" % ( keys, Y_tilde.x, Y_tilde.y, message,
                                     P1.x, P1.y, P2.x, P2.y)
    return int(hashlib.sha512(str.encode()).hexdigest(), 16) 

from ecpy.curves import Curve, Point
from ecpy.keys import ECPrivateKey
from ecpy.eddsa import EDDSA
import secrets, hashlib, binascii
import math
import itertools as it
import random
from pprint import pprint


### Az secp25kk1-t curvet használom a program során
### A görbének az egyenletét, jellemzőit kiprinteltem
### A G -generátorpont a későbbiekben is felhasználódik

curve = Curve.get_curve('secp256k1')
G     = curve.generator
print(f"Name: {curve.name},  Type: {curve.type}")
print(f"Size: {curve.size}, a={curve.a}")
print(f"G={curve.generator}, field={curve.field}, order={curve.order}\n")


   

### A ring_sign metódusba történik meg a signature elkészítése
### Inputként megkapjuk a görbét, az üzenetet, a ringben levő public-keyeket,
### a private_keyek egy arrayét- de ebből csak a signerét fogjuk használni
### key_index - ki a signer
###

def ring_sign(curve, message, public_keyek, private_keyek, key_index):
    
    ### key_count - hány személy van a ringben
    ### előkészitjük az adott tömböket
    key_count = len(public_keyek)
    e = [0] * key_count
    ss = [0] * key_count
    z_s = [0] * key_count
    z__s = [0] * key_count


    ####elkészitjük a public keys tömb hashét
    public_keys_coords = list(map( lambda point: (point.W.x, point.W.y),  public_keyek))
    public_keys_hash =H2(public_keys_coords )

    #A find_ecc_point segitségével rendelünk hozzá egy inthez egy EC pontot, kimenetként egy, a görbén levő pontot kapunk
    H = find_ecc_point(public_keys_hash, curve.field)
    
    ##key_image
    Y_tilde = curve.mul_point(private_keyek[key_index].d, H)
    

    
    ##Első lépés
    ### Alfát random választjuk meg, max a görbe rendjéig
    ### Kiszámoljuk Q-t (ami egy public keyként müködik), amely alfa*G (curve.mul_point - multiplication(scalar, Point))
    ### Meghatározzuk a pi_plus_1 indexet majd erre külön kiszámoljuk az e értékét
    alfa = random.randint(0,curve.order)
    Q = curve.mul_point(alfa, G)
    LL = curve.mul_point(alfa, H)
    pi_plus_1 = (key_index+1) % key_count
    e[pi_plus_1] = H1(public_keys_hash, Y_tilde, message,Q,LL)

   
   #Második lépés
   ### Végigmegyünk a tömbön, úgy, hogy i != key_index, tehát a ring többi tagjára számolunk
    for i in it.chain(range(key_index+1, key_count), range(key_index)):
        if i!=key_index:
         # print(i)
         ###Meghatározunk egy random értéket
          ss[i] = random.randint( 0,curve.order )
         
         # print(ss[i])
         ### És az indexet
          next_i = (i+1) % key_count
          
         ### Két új EC pontot hozunk létre, ss_i és G illetve e_i és as publikus kulcsok(pontok) szorzatából
         # print(curve.is_on_curve(curve.mul_point(e[i],publicKeys[i].W)))
          z_s[i] = curve.add_point(curve.mul_point(ss[i],G), curve.mul_point(e[i],public_keyek[i].W))
          z__s[i] = curve.add_point(curve.mul_point(ss[i],H), curve.mul_point(e[i], Y_tilde))
          e[next_i] = H1(public_keys_hash, Y_tilde, message, z_s[i], z__s[i])

         
       



    ### Maga a signer részét, külön számoljuk ki. Itt kerül be a privát kulcsa
    #print(e)
    #ss[key_indexx] = (privateKeys[key_indexx].d  - signer.private_key * cs[signer_index] ) % curve.order
    ss[key_index] = ( alfa - private_keyek[key_index].d * e[key_index] ) % curve.order
    
  

    ###Visszaadjuk a publikus kulcsokat tartalmazó tömböket,
    # az üzenetet,
    # az első elemet az e-ből,
    # és a random s-ket 
    # + a signer s-ét
    # és a KEY_IMAGE-t
    #
    #
    return (public_keyek, message, e[0], ss, Y_tilde)


### A signature ellenőrzése: meghatározza, hogy az 's' értékek mindenképpen az 'e' értékek után lettek kiszámolva,
### tehát közrejátszik egy private key felhasználása
### Megkapja a curvet, a public keyeket, az üzenetet, és az előzőleg kiszámolt e_0-t és s-k tömbjét

def verify(curve,public_keys, message, e_0, ss, Y_tilde): 


    ### Tömböket előkészítem
    
    
    n = len(public_keys)
    e = [e_0] + [0] * ( n - 1 )
    z_s = [0] * n
    z__s = [0] * n

    public_keys_coords = list(map( lambda point: (point.W.x, point.W.y), public_keys))
    public_keys_hash =H2(public_keys_coords )
  

    H = find_ecc_point(public_keys_hash, curve.field)

    ###Végig iterálok a tömbön, és a signaturehez hasonlóan kiszámolom a z_s_i értékeket, amikkel az e-ket határozom meg
    for i in range( n ):
        z_s[i] = curve.add_point(curve.mul_point(ss[i],G),curve.mul_point( e[i],public_keys[i].W))
        z__s[i] = curve.add_point(curve.mul_point(ss[i],H), curve.mul_point(e[i], Y_tilde))
        if i < n - 1:
            e[i+1] = H1(public_keys_hash, Y_tilde, message, z_s[i], z__s[i])
            #print(e)

   
    to_check = H1(public_keys_hash, Y_tilde, message, z_s[n-1], z__s[n-1])
   
    print()
    
    ##Egy tömböt adok vissza returnként
    ## array[0]  - hogy valid e a signature
    ## array[1] - a signaturehoz tartozo key_image
    if (e[0]==to_check):
      return ["The signature is valid", Y_tilde]
    else:
      return ["Invalid signature", Y_tilde]

    
  #### Az EC pont megtalálásához használt algoritmus
### Eredetileg beépitett libraryk moduljával gondoltam el, de nem sikerült
### A következő algoritmust találam végül: Tonelli-Shanks

#  Find a quadratic residue (mod p) of 'a'. p
#       must be an odd prime.
#       Solve the congruence of the form:
#           x^2 = a (mod p)
#       And returns x.

#url:   http://eli.thegreenplace.net/2009/03/07/computing-modular-square-roots-in-python/


def modular_sqrt(a, p):
    """ Find a quadratic residue (mod p) of 'a'. p
        must be an odd prime.
        Solve the congruence of the form:
            x^2 = a (mod p)
        And returns x. Note that p - x is also a root.
        0 is returned is no square root exists for
        these a and p.
        The Tonelli-Shanks algorithm is used (except
        for some simple cases in which the solution
        is known from an identity). This algorithm
        runs in polynomial time (unless the
        generalized Riemann hypothesis is false).
        Originally taken from
        http://eli.thegreenplace.net/2009/03/07/computing-modular-square-roots-in-python/
    """
    # Simple cases
    #
    if legendre_symbol(a, p) != 1:
        return 0
    elif a == 0:
        return 0
    elif p == 2:
        return p
    elif p % 4 == 3:
        return pow(a, (p + 1) // 4, p)

    # Partition p-1 to s * 2^e for an odd s (i.e.
    # reduce all the powers of 2 from p-1)
    #
    s = p - 1
    e = 0
    while s % 2 == 0:
        s //= 2
        e += 1

    # Find some 'n' with a legendre symbol n|p = -1.
    # Shouldn't take long.
    #
    n = 2
    while legendre_symbol(n, p) != -1:
        n += 1

    # Here be dragons!
    # Read the paper "Square roots from 1; 24, 51,
    # 10 to Dan Shanks" by Ezra Brown for more
    # information
    #

    # x is a guess of the square root that gets better
    # with each iteration.
    # b is the "fudge factor" - by how much we're off
    # with the guess. The invariant x^2 = ab (mod p)
    # is maintained throughout the loop.
    # g is used for successive powers of n to update
    # both a and b
    # r is the exponent - decreases with each update
    #
    x = pow(a, (s + 1) // 2, p)
    b = pow(a, s, p)
    g = pow(n, s, p)
    r = e

    while True:
        t = b
        m = 0
        for m in xrange(r):
            if t == 1:
                break
            t = pow(t, 2, p)

        if m == 0:
            return x

        gs = pow(g, 2 ** (r - m - 1), p)
        g = (gs * gs) % p
        x = (x * gs) % p
        b = (b * g) % p
        r = m


def legendre_symbol(a:int,p:int):
    """ Compute the Legendre symbol a|p using
        Euler's criterion. p is a prime, a is
        relatively prime to p (if p divides
        a, then a|p = 0)
        Returns 1 if a has a square root modulo
        p, -1 otherwise.
        Originally taken from
        http://eli.thegreenplace.net/2009/03/07/computing-modular-square-roots-in-python/
    """
    
    ls = pow(a, (p - 1) // 2, p)
    return -1 if ls == p - 1 else ls

#### 1-sével növelve, megkeresem az adott x-y pontpárt, amely rajta van a görbén
#### Ennek teljesitenie kell a görbét leiró képletét, innen kifejezve lesz az 
#### y=x^3 + 7
#### Ha találok egy x-y párt, egy Pontot hozok létre és térek vissza vele
def find_ecc_point(x, p):
    found = False
    x -= 1
    while not found:
        x += 1
        y_sq = pow(x,3) + 7
        y = modular_sqrt( y_sq, p )
        if y != 0:
           return Point(x,y,curve)

publicKeys=[]
privateKeys=[]

#Létrehozom a publickey-privatekey párokat
seckey0  = ECPrivateKey(0xf026a4e75eec75544c0f44e937dcf5ee6355c7176600b9688c667e5c283b43c5, curve)
seckey1  = ECPrivateKey(0xf126a4e75eec75544c0f44e937dcf5ee6355c7176600b9688c667e5c283b43c5, curve)
seckey2  = ECPrivateKey(0xf226a4e75eec75544c0f44e937dcf5ee6355c7176600b9688c667e5c283b43c5, curve)
seckey3  = ECPrivateKey(0xf326a4e75eec75544c0f44e937dcf5ee6355c7176600b9688c667e5c283b43c5, curve)
seckey4  = ECPrivateKey(0xf426a4e75eec75544c0f44e937dcf5ee6355c7176600b9688c667e5c283b43c5, curve)
seckey5 =  ECPrivateKey(0xfb26a4e75eec75544c0f44e937dcf5ee6355c7176600b9688c667e5c283b43c5, curve)
seckey6  = ECPrivateKey(0xf626a4e75eec75544c0f44e937dcf5ee6355c7176600b9688c667e5c283b43c5, curve)
seckey7  = ECPrivateKey(0xf726a4e75eec75544c0f44e937dcf5ee6355c7176600b9688c667e5c283b43c5, curve)
seckey8  = ECPrivateKey(0xf826a4e75eec75544c0f44e937dcf5ee6355c7176600b9688c667e5c283b43c5, curve)
        


pubkey0 = seckey0.get_public_key()
pubkey1 = seckey1.get_public_key()
pubkey2 = seckey2.get_public_key()
pubkey3 = seckey3.get_public_key()
pubkey4 = seckey4.get_public_key()
pubkey5 = seckey5.get_public_key()
pubkey6 = seckey6.get_public_key()
pubkey7 = seckey7.get_public_key()
pubkey8 = seckey8.get_public_key()

############################################

#Feltöltök 2 tömböt velük

publicKeys = [pubkey0, pubkey1, pubkey2, pubkey3, pubkey4]
publicKeys2 = [pubkey4, pubkey1, pubkey6, pubkey7, pubkey8]
privateKeys = [seckey0, seckey1, seckey2, seckey3, seckey4]
privateKeys2 = [seckey4, seckey1, seckey6, seckey7, seckey8]


####LINKABILITY TEST: ABBAN AZ ESETBEN HA KÜLÖNBÖZIK A KÉT RING"
### Ellenőrizhető, hogy a signature ugyanazon ringbeli memberekkel lett létrehozva
###Kiválasztom a 2-es indexen levő embert a signernek(de lehetne véletlenszerü is)
#key_index = random.randint(0,3)
#### Az az eset, amikor a ring memberek különböznek: publickeys és publicKeys2

key_index=1

#két különböző messaget irok alá
message = "This is a ring signature"
message2 = "This is another ring"

#létrehozom a két ringet és meghatározom a hozzájuk tartozó key imaget ( itt két különböző publikus kulcsos vektort használok)
keyimage1 =verify(curve, *ring_sign(curve, message, publicKeys, privateKeys, key_index))
keyimage2= verify(curve, *ring_sign(curve, message2, publicKeys2, privateKeys2, key_index))

#kiiratások
print("\033[0;32;47m  Ring 1 has the members: \033[0m")
for i in publicKeys:
  print(i)
print()
print(" Ring signature number 1: \033[92m", keyimage1[0] +"\033[0m")

print()
print("\033[0;36;47m  Ring 2 has the members: \033[0m")
for i in publicKeys2:
  print(i)
print()
print(" Ring signature number 2: \033[92m", keyimage2[0] +"\033[0m")
print()

##ha megegyezik a kettő -> linkable, ellenkező esetben nem
is_Key_Image_Same = keyimage1[1]==keyimage2[1]
print("\033[1;34;47m LINKABILITY TEST \033[0m")

if(is_Key_Image_Same):
   
   print("\033[92m The two signatures were made by the same ring, therefore they are linkable \033[0m")
else:

  print("\033[1;31;47m The two signatures were made containing different ring members \033[0m")

    


