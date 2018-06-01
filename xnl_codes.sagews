︠2a6966e7-f5ad-4e39-80d2-16b12e5f0db8s︠
from sage.coding.relative_finite_field_extension import *
import random, time
class XNLCode():
    def __init__(self, poi, k):
        #self.n = n
        self.k = k
        # creating of XNL [n,k,d] linear code over F_q
        # you should choose points count, curve, field and inner codes for code here
        A.<x,y> = AffineSpace(GF(2), 2)
        self.curve = y^2 + y - x^3 - x # curve
        self.q = 4 # base F_q for our code

        Fq4.<a> = GF(self.q, 'a') # Finite Field
        self.a = a
        self.Fq4 = Fq4
        self.F = Fq4
        self.Ya = PolynomialRing(self.F,'x,y',order=TermOrder('wdeglex',(self.q,self.q+1)))
        Fq16.<b>, f = Fq4.extension(2, 'b', map=True)
        self.b = b
        self.Fq16 = Fq16
        Fq64.<c>, f = Fq4.extension(3, 'c', map=True)
        self.c = c
        self.Fq64 = Fq64
        self.rem = [0]
        self.errs = 0


        self.func_field_points = poi # x points of degree 1, y points of degree 2, ...
        self.inner_codes = [[1, 1, 1], [3, 2, 2], [5, 3, 3]] # inner codes for points of degree 1, degree 2, etc
        self.inner_codes_generator = [Matrix(Fq4,[1]), Matrix(Fq4, [[1,1,0],[0,1,1]]), Matrix(Fq4, [[1,1,1,1,0],[0,1,a,a^2,0],[0,1,a^2,a,1]])] # generator matrices for inner codes
        # service calculations
        self.genus = Curve([self.curve], A).genus() # curve genus
        # calculating dimension and minimum distance of XNL code
        n = sum(self.func_field_points[i] * self.inner_codes[i][0] for i in [0..min(len(self.func_field_points), len(self.inner_codes)) - 1])
        self.n = n
        self.d = self._get_d()
        k_upper_bound = self._get_k_upper_bound()

        assert self.k <= k_upper_bound and self.k >= 1, 'parameter k (dimension) of XNL code must be in 1 to %s but it %s' %(k_upper_bound, self.k)

        self.G = self._create_generator_matrix(self.get_points())

    def __repr__(self):
        return '[%d, %d, d >= %d] linear XNL code over GF(%d) on curve %s with genus %s' % (
                self.n,
                self.k,
                self.d,
                self.q,
                self.curve,
                self.genus
                )

    def __eq__(self, other):
        """Very superficial, but relatively cheap, check for total equivalence of two codes: their generator matrices are exactly the same."""
        return self.generator_matrix() == other.generator_matrix()

    def __contains__(self, x):
        return self.iscodeword(x)

    @cached_method
    def _get_k_upper_bound(self):
        return sum(self.func_field_points[i] * self.inner_codes[i][2] for i in [0..min(len(self.func_field_points), len(self.inner_codes)) - 1]) - self.genus

    @cached_method
    def _get_d(self):
        return sum(self.func_field_points[i] * self.inner_codes[i][2] for i in [0..min(len(self.func_field_points), len(self.inner_codes)) - 1]) - self.k - self.genus + 1

    @cached_method
    def get_points(self):
        # calculating points of degree 1
        Aff4.<x,y> = AffineSpace(self.Fq4, 2)
        C = Curve(y^2 + y - x^3 - x)
        pts1 = C.rational_points()
        # calculating points of degree 2
        Aff16.<x,y> = AffineSpace(self.Fq16, 2)
        C = Curve(y^2 + y - x^3 - x)
        pts2 = C.rational_points()
        # calculating points of degree 3
        Aff64.<x,y> = AffineSpace(self.Fq64, 2)
        C = Curve(y^2 + y - x^3 - x)
        pts3 = C.rational_points()

        points = []
        for i in range(0,self.func_field_points[0]):
            points.append(pts2[i])
        for i in range(0,self.func_field_points[1]*2, 2):
            points.append(pts2[i + len(pts1)])
        for i in range(0,self.func_field_points[2]*3, 3):
            points.append(pts3[i + len(pts1)])
        return points

    def _create_inner_matrix(self):
        inner_matrix_dim = sum(self.func_field_points[i] * self.inner_codes[i][1] for i in [0..min(len(self.func_field_points), len(self.inner_codes)) - 1])
        inner_matrix_length = sum(self.func_field_points[i] * self.inner_codes[i][0] for i in [0..min(len(self.func_field_points), len(self.inner_codes)) - 1])
        inner_matrix = matrix(self.Fq4, inner_matrix_dim, inner_matrix_length);

        for i in range(0, self.inner_codes[0][1]*self.func_field_points[0]):
            for j in range(0, self.inner_codes[0][0]*self.func_field_points[0]):
                if(i == j):
                    inner_matrix[i,j] = self.inner_codes_generator[0][0][0]
        j = self.inner_codes[0][0]*self.func_field_points[0]

        for i in range(self.inner_codes[0][1]*self.func_field_points[0], self.inner_codes[0][1]*self.func_field_points[0] + self.inner_codes[1][1]*self.func_field_points[1], self.inner_codes[1][1]):
            for l in range(0, self.inner_codes[1][0]):
                for m in range(0, self.inner_codes[1][1]):
                    inner_matrix[i+m,j+l] = self.inner_codes_generator[1][m][l]
            j = j + self.inner_codes[1][0]

        for i in range(self.inner_codes[0][1]*self.func_field_points[0] + self.inner_codes[1][1]*self.func_field_points[1], self.inner_codes[0][1]*self.func_field_points[0] + self.inner_codes[1][1]*self.func_field_points[1] + self.inner_codes[2][1]*self.func_field_points[2], self.inner_codes[2][1]):
            for l in range(0, self.inner_codes[2][0]):
                for m in range(0, self.inner_codes[2][1]):
                    inner_matrix[i+m,j+l] = self.inner_codes_generator[2][m][l]
            j = j + self.inner_codes[2][0]
        return inner_matrix

    @cached_method
    def _get_riemann_roch_basis(self, field = 0):
        if(field == 0):
            field = self.Fq16
        Aff.<x,y> = AffineSpace(field, 2)
        riemann_roch_basis = []
        for j in range(0,2):
            i = 0
            while(2*i + 3*j <= self.k):
                riemann_roch_basis.append(x^i*y^j)
                i = i + 1
        return riemann_roch_basis

    def _create_outer_matrix(self, points):
        F16_to_F4 = RelativeFiniteFieldExtension(self.Fq16, self.Fq4)
        F64_to_F4 = RelativeFiniteFieldExtension(self.Fq64, self.Fq4)

        riemann_roch_basis = self._get_riemann_roch_basis()
        gen_matrix_F16 = matrix(self.Fq16, self.k, len(points) - self.func_field_points[2]);
        for i in range(0, self.k):
            for j in range(0, len(points) - self.func_field_points[2]):
                gen_matrix_F16[i, j] = riemann_roch_basis[i](points[j][0],points[j][1])

        riemann_roch_basis = self._get_riemann_roch_basis(self.Fq64)
        gen_matrix_F64 = matrix(self.Fq64, self.k, self.func_field_points[2]);
        for i in range(0, self.k):
            for j in range(0, self.func_field_points[2]):
                tt = len(points) - self.func_field_points[2]
                gen_matrix_F64[i, j] = riemann_roch_basis[i](points[tt + j][0],points[tt + j][1])

        outer_matrix_dim = self.k
        outer_matrix_length = sum(self.func_field_points[i] * self.inner_codes[i][1] for i in [0..min(len(self.func_field_points), len(self.inner_codes)) - 1])
        outer_matrix = matrix(self.Fq4, outer_matrix_dim, outer_matrix_length)
        for i in range(0, outer_matrix_dim):
            for j in range(0, self.func_field_points[0]):
                outer_matrix[i,j] = F16_to_F4.relative_field_representation(gen_matrix_F16[i][j])[0]

        for i in range(0, outer_matrix_dim):
            for j in range(self.func_field_points[0], self.func_field_points[0]+self.func_field_points[1]*2, 2):
                r,t = F16_to_F4.relative_field_representation(gen_matrix_F16[i][self.func_field_points[0] + (j - self.func_field_points[0])/2])
                outer_matrix[i,j] = r
                outer_matrix[i,j+1] = t

        it = -1
        for i in range(0, outer_matrix_dim):
            it = it + 1
            jt = 0
            for j in range(self.func_field_points[0]+self.func_field_points[1]*2, self.func_field_points[0]+self.func_field_points[1]*2+self.func_field_points[2]*3, 3):
                r,t,u = F64_to_F4.relative_field_representation(gen_matrix_F64[it][jt])
                outer_matrix[i,j] = r
                outer_matrix[i,j+1] = t
                outer_matrix[i,j+2] = u
                jt = jt + 1
        return outer_matrix

    def _create_generator_matrix(self, points):
        return self._create_outer_matrix(points) * self._create_inner_matrix()

    @cached_method
    def generator_matrix(self):
        """Return a generator matrix for the code."""
        return self.G

    @cached_method
    def parity_check_matrix(self):
        """Return a parity check matrix for the code."""
        Sp = self.generator_matrix().right_kernel()
        return Sp.basis_matrix()

    def encode(self, w):
        self.rem = w
        return vector(self.Fq4, w) * self.generator_matrix()

    @cached_method
    def _an_information_set(self):
        """Return an information set for G. Repeated calls to this method will
        return the same information set."""
        k = self.true_dimension()
        pos = list(range(self.n))
        G = self.generator_matrix()
        while True:
            shuffle(pos)
            info_set = pos[:k]
            info_set.sort()
            Gt = G.matrix_from_columns(info_set)
            if rank(Gt) == k:
                return info_set

    @cached_method
    def _unencoder_matrix(self):
        """Find an information set for G, and return the inverse of those
        columns of G: this allows o unencode codewords"""
        Gt = self.generator_matrix().matrix_from_columns(self._an_information_set())
        return Gt.inverse()

    def codeword_to_message(self, v):
        """Return the information corresponding to a codeword. This function
        satisfies `unencode(encode(info)) == info`.
        Since the information word is calculated from an information set of the
        code, then if `c` is not a codeword, then the returned vector might not
        be closer than `n-k` to `c`"""
        U = self._unencoder_matrix()
        info_set = self._an_information_set()
        cc = vector( v[i] for i in info_set )
        return cc * U

    def iscodeword(self, r):
        """Returns whether r is a codeword"""
        # Check that the word is in the field
        if not all(ri in self.F for ri in r):
            return false
        # Check that the syndrome is zero
        syn = self.syndrome(r)
        if hasattr(syn, "is_zero"):
            return syn.is_zero()
        elif isinstance(syn, list):
            return all(s.is_zero() for s in syn)
        else: 
            raise Exception("Don't know how to check if syndrome is zero.")

    def syndrome(self, r):
        """Returns the syndrome of the received word.
        INPUT:
        - ``r`` -- The word to be evaluated, in the preferred form.

        OUTPUT:
        The syndrome in a preferred form. If the standard implementation of
        iscodeword is to be used, it should be a an object with the is_zero
        function, or a list of such"""
        return self.parity_check_matrix() * r

    def random_codeword(self):
        """Return a random codeword from the code. Requires the calculation of
        the generator matrix"""
        k = self.true_dimension();
        return random_vector(self.Fq4, k) * self.generator_matrix();

    @cached_method
    def true_dimension(self):
        """The true dimension of a Hermitian code is always $m - g + 1$"""
        return self.k

    @cached_method
    def true_minimum_distance(self):
        """Compute the true minimum distance of this code by analysing the
        generator matrix. Computation time is exponential in code dimension."""
        # Calculate by calling the Sage integrated functions
        Csage = LinearCode(self.generator_matrix())
        return Csage.minimum_distance()

    @cached_method
    def list(self):
        """Tabulate and return all codewords of the code.
        NOTE: This list will have len (F.cardinality())^k"""
        G = self.generator_matrix()
        RS = G.row_space()
        return RS.list()

    def __iter__(self):
        for c in self.list():
            yield c

    def hamming_metric(self, v, w):
        val = 0
        for i in range(0, len(v)):
            if(v[i] == w[i]):
                val = val + 1
        return val

    def decode(self, w, err, res):
        if res == 1 and self.rem != [0]:
            sleep (len(w) / 2)
            if(self.errs <= self.d+1 / 2):
                return vector(self.Fq4, self.rem)*self.generator_matrix()
            return vector(self.Fq4, self.n)
        while(1 == 1):
            v = vector(self.Fq4, self._get_random_el())*self.generator_matrix()
            if(self.hamming_metric(v, w) >= len(w) - err):
                return v

    def _information_to_function(self, mes):
        """Return the function in F[x,y] which corresponds to the information
        vector ``mes``, as returned by ``self.unencode(c)`` for a codeword
        ``c``"""
        assert len(mes) == self.k , "The message vector does not have the length of the dimension of the code"
        riemann_roch_basis = self._get_riemann_roch_basis(self.Fq4)
        return sum(mes[i]*riemann_roch_basis[i] for i in range(0, len(riemann_roch_basis)))

    def _function_to_information(self, f):
        """Return the information vector in F which corresponds to the function f in F[x,y]"""
        riemann_roch_basis = self._get_riemann_roch_basis(self.Fq4)
        return vector( f.monomial_coefficient(elem) for elem in riemann_roch_basis )

    def _get_Q_polynomial(self):
        riemann_roch_basis = self._get_riemann_roch_basis(self.Fq4)
        poly = 0
        for j in range(0, len(riemann_roch_basis)):
            poly = poly + self.Fq4.random_element()*riemann_roch_basis[j]
        return poly

    def _get_random_el(self):
        vec = [0,1,self.a,self.a+1]
        out = []
        for j in range(0, self.k):
            out.append(random.choice(vec))
        return out
︡c579c1e5-3c02-4778-9830-a9e9969ebefd︡{"done":true}︡
︠28d36f42-051f-4cd6-a0d8-17feb54f0010s︠
Fq4.<a> = GF(4, 'a')
code = XNLCode([4, 2, 0],7)
code
code.get_points()
code.generator_matrix()
code.generator_matrix().right_kernel()
print "t"
code.generator_matrix().right_kernel().basis_matrix()
#what = random_vector(code.Fq4, code.k)
what = vector(Fq4, [1,1,1,0,1,0,1])
print "message: ", what
v = code.encode(what)
print "encoded message (codeword): ", v
err = vector(Fq4, code.n)
err[10] = 1
err[6] = 1
print "error vector: ", err
v_err = v + err
code.errs = len([x for x in err if x != 0])
print "with error: ", v_err
corrected = code.decode(v_err, 1, 1)
print "corrected codeword: ", corrected
print "equal =", corrected == v
︡593283b8-af11-42dd-ad32-9ff92f163264︡{"stdout":"[10, 7, d >= 1] linear XNL code over GF(4) on curve x^3 + y^2 + x + y with genus 1\n"}︡{"stdout":"[(0, 0), (0, 1), (1, 0), (1, 1), (b^2 + b, b^2), (b^2 + b + 1, b)]\n"}︡{"stdout":"[    1     1     1     1     1     1     0     1     1     0]\n[    0     0     1     1     a     a     0 a + 1 a + 1     0]\n[    0     0     0     1 a + 1     1     a     0 a + 1 a + 1]\n[    0     0     0     1     1     a a + 1     0     a     a]\n[    0     1     0     1     a a + 1     1     0     1     1]\n[    0     0     1     1     1     1     0     1     1     0]\n[    0     0     1     1 a + 1 a + 1     0     a     a     0]\n"}︡{"stdout":"Vector space of degree 10 and dimension 3 over Finite Field in a of size 2^2\nBasis matrix:\n[1 1 1 1 0 0 1 0 0 1]\n[0 0 0 0 1 1 1 0 0 0]\n[0 0 0 0 0 0 0 1 1 1]\n"}︡{"stdout":"t\n"}︡{"stdout":"[1 1 1 1 0 0 1 0 0 1]\n[0 0 0 0 1 1 1 0 0 0]\n[0 0 0 0 0 0 0 1 1 1]\n"}︡{"stdout":"message:  (1, 1, 1, 0, 1, 0, 1)\n"}︡{"stdout":"encoded message (codeword):  (1, 0, 1, 1, 1, a, a + 1, 0, a, a)\n"}︡{"stderr":"Error in lines 14-14\nTraceback (most recent call last):\n  File \"/cocalc/lib/python2.7/site-packages/smc_sagews/sage_server.py\", line 1013, in execute\n    exec compile(block+'\\n', '', 'single') in namespace, locals\n  File \"\", line 1, in <module>\n  File \"sage/modules/free_module_element.pyx\", line 1828, in sage.modules.free_module_element.FreeModuleElement.__setitem__ (build/cythonized/sage/modules/free_module_element.c:13983)\n    raise IndexError(\"vector index out of range\")\nIndexError: vector index out of range\n"}︡{"done":true}︡
︠875b00e7-3b5e-4197-849c-b03a2f5ddebes︠
 Fq4.<a> = GF(4, 'a')
code = XNLCode([3, 2, 20],66)
code
#code.true_minimum_distance()
#M
F = GF(101)
n, k = 109, 66
C = codes.GeneralizedReedSolomonCode(F.list()[:n], k)
C
︡863911f5-8790-4c86-9d0a-96f3ff412dc8︡{"stdout":"[109, 66, d >= 1] linear XNL code over GF(4) on curve x^3 + y^2 + x + y with genus 1\n"}︡{"stdout":"[101, 66, 36] Reed-Solomon Code over GF(101)\n"}︡{"done":true}︡
︠5e333d62-c63b-4f12-a473-d34d56a71bb2s︠
~M
︡366711ff-088c-4a3c-a026-3eeeebd65e45︡{"stdout":"[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0]\n[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0]\n[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0]\n[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0]\n[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0]\n[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0]\n[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0]\n[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0]\n[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0]\n[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0]\n[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0]\n[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0]\n[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0]\n[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0]\n[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0]\n"}︡{"done":true}︡
︠df2a1725-a8d9-479c-a2e8-d159a197e6a7︠

func_field_points = [3, 3, 1]
inner_codes = [[1, 1, 1], [3, 2, 2], [5, 3, 3]]
k = 7
genus = 1
n = sum(self.func_field_points[i] * self.inner_codes[i][0] for i in [0..min(len(self.func_field_points), len(self.inner_codes)) - 1])
d = sum(func_field_points[i] * inner_codes[i][2] for i in [0..min(len(func_field_points), len(inner_codes)) - 1]) - k - genus + 1
︡633dc83e-2559-42c8-bbc4-854390f97f3c︡{"stdout":"5\n"}︡{"done":true}︡









