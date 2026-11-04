module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# The short complex of cycles of a complex, and acyclicity of its image under a functor

For a homological complex `K` and indices `i`, `j` this file introduces the short complex

`Z^i(K) ⟶ K^i ⟶ Z^j(K)`

whose first map is the inclusion of the cycles and whose second is the map induced by the
differential.  When `j` follows `i` and `K` is exact in degree `j`, that short complex is
*short exact*: this is the sequence an acyclic complex splices out of, and it is the only
thing about an acyclic complex that an additive functor has to be told in order to conclude
that the image complex is again acyclic.

The last result is exactly that statement: a functor which carries each of those short exact
sequences to a short exact sequence carries the complex to an acyclic complex.  The functor is
*not* assumed exact — in the intended application (pullback along a morphism of ringed topoi)
it is not, and the short exactness of the images is supplied by a flatness hypothesis on the
cycles.

## Main definitions

* `HomologicalComplex.cyclesShortComplex`: the short complex `Z^i(K) ⟶ K^i ⟶ Z^j(K)`.

## Main results

* `HomologicalComplex.cyclesShortComplex_shortExact`: it is short exact when `c.Rel i j` and
  `K` is exact in degree `j`.
* `CochainComplex.acyclic_mapHomologicalComplex_of_cyclesShortExact`: if `F` carries every one
  of those short complexes of a cochain complex `K` to a short exact sequence, then the
  degreewise image `F(K)` is acyclic.
* `ChainComplex.acyclic_mapHomologicalComplex_of_cyclesShortExact`: the same statement for an
  `ℕ`-indexed chain complex, where only the sequences at the index pairs `(n + 1, n)` are
  available and degree `0` has to be treated apart.
* `ChainComplex.prop_cycles_of_acyclic` and
  `ChainComplex.acyclic_mapHomologicalComplex_of_prop`: the form in which the hypothesis is met
  in practice.  A class of objects closed under passing to the first term of a short exact
  sequence whose other two terms belong to it is inherited by all the cycles of an acyclic
  complex whose terms belong to it, by induction on the degree; a functor which keeps short
  exact sequences with third term in the class short exact therefore carries the complex to an
  acyclic complex.
* `CategoryTheory.ShortComplex.exact_of_epi_of_isKernel`: the exactness criterion the last
  proof runs on — a short complex is exact as soon as its first map factors as an epimorphism
  followed by a kernel of its second map.

## Implementation notes

*Why the cycles sequence is not read off Mathlib's `sc'`.*  Mathlib states exactness of a
complex at `j` as exactness of the short complex `K^i ⟶ K^j ⟶ K^k` of differentials, and
relates `(K.sc' i j k).cycles` to `K.cycles j` by an isomorphism
(`HomologicalComplex.cyclesIsoSc'`).  Going through that isomorphism to get
`Epi (K.toCycles i j)` is possible but costs an instance mismatch: the `HasLeftHomology`
argument of `ShortComplex.Exact.epi_toCycles` and the `HasHomology` argument of
`HomologicalComplex.toCycles_cyclesIsoSc'_hom` are found by different paths, so the resulting
hypothesis does not fire as a local instance even though it prints as the goal.
`epi_toCycles_of_exactAt` instead reads the same fact off the cokernel presentation
`HomologicalComplex.homologyIsCokernel`, which mentions `K.toCycles i j` directly: the homology
in degree `j` *is* the cokernel of that map, and a map with zero cokernel is an epimorphism.

*Why the two kernel transfers are the pre-existing ones.*  The step from "a kernel of `g`" to
"a kernel of `g ≫ m`" for `m` a monomorphism, and its converse, are
`CategoryTheory.Limits.isKernelCompMono` and `CategoryTheory.Limits.isKernelOfComp`.  Both
directions are needed — the converse for the `exact` field of the cycles sequence, where the
cycles are known to be the kernel of the *differential* and must be exhibited as the kernel of
`toCycles`, and the forward one for the image complex, where the kernel of `F(toCycles)` must
be exhibited as the kernel of the differential `F(d)`.  Neither was written here.

*The index pair is explicit.*  `cyclesShortComplex` takes both indices rather than deriving
the second from `c.next`, and the acyclicity theorem below instantiates it at the literal pairs
`(n - 1, n)` and `(n, n + 1)`.  Deriving the second index would force an index transport
between `(n - 1) + 1` and `n` at every use.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **A short complex is exact as soon as its first map factors as an epimorphism followed by a
kernel of its second map.**  This is the form in which a spliced complex is exact: at each
degree the incoming differential factors through the cycles, surjectively, and the cycles are
the kernel of the outgoing differential. -/
lemma exact_of_epi_of_isKernel {S : ShortComplex C} {A : C}
    (e : S.X₁ ⟶ A) (k : A ⟶ S.X₂) (he : Epi e) (hek : e ≫ k = S.f)
    (w : k ≫ S.g = 0) (hk : IsLimit (KernelFork.ofι k w)) : S.Exact := by
  have := he
  have hkmono : Mono k := mono_of_isLimit_fork hk
  have hti : S.liftCycles k w ≫ S.iCycles = k := S.liftCycles_i k w
  have hsk : hk.lift (KernelFork.ofι S.iCycles S.iCycles_g) ≫ k = S.iCycles :=
    Fork.IsLimit.lift_ι hk
  have hiso : IsIso (S.liftCycles k w) :=
    ⟨hk.lift (KernelFork.ofι S.iCycles S.iCycles_g),
      by rw [← cancel_mono k, Category.assoc, hsk, hti, Category.id_comp],
      by rw [← cancel_mono S.iCycles, Category.assoc, hti, hsk, Category.id_comp]⟩
  rw [S.exact_iff_epi_toCycles]
  have h : S.toCycles = e ≫ S.liftCycles k w := by
    rw [← cancel_mono S.iCycles, Category.assoc, hti, S.toCycles_i, hek]
  rw [h]
  exact epi_comp _ _

end CategoryTheory.ShortComplex

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C] {ι : Type*} {c : ComplexShape ι}

/-- **The short complex of cycles** `Z^i(K) ⟶ K^i ⟶ Z^j(K)` of a homological complex: the
inclusion of the cycles in degree `i`, followed by the map to the cycles in degree `j` induced
by the differential `K^i ⟶ K^j`. -/
@[simps]
def cyclesShortComplex (K : HomologicalComplex C c) (i j : ι) : ShortComplex C :=
  ShortComplex.mk (K.iCycles i) (K.toCycles i j) (by
    rw [← cancel_mono (K.iCycles j), Category.assoc, HomologicalComplex.toCycles_i,
      HomologicalComplex.iCycles_d, zero_comp])

/-- **The map to the cycles induced by a differential is an epimorphism exactly where the
complex is exact.**  The homology in degree `j` is the cokernel of `K.toCycles i j`, so it
vanishes if and only if that map is an epimorphism; this is the direction that is used. -/
lemma epi_toCycles_of_exactAt (K : HomologicalComplex C c) {i j : ι} (hij : c.Rel i j)
    (h : K.ExactAt j) : Epi (K.toCycles i j) :=
  Preadditive.epi_of_isZero_cokernel' _ (K.homologyIsCokernel i j (c.prev_eq' hij))
    h.isZero_homology

/-- **The cycles sequence of a complex that is exact in degree `j` is short exact.**  Its first
map is a monomorphism because the cycles are a kernel, its second is an epimorphism by
exactness in degree `j`, and it is exact in the middle because the cycles in degree `i` are the
kernel of the differential `K^i ⟶ K^j`, hence of the map to the cycles in degree `j`. -/
lemma cyclesShortComplex_shortExact (K : HomologicalComplex C c) {i j : ι} (hij : c.Rel i j)
    (h : K.ExactAt j) : (cyclesShortComplex K i j).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _
    (isKernelOfComp (f := K.toCycles i j) (K.iCycles j) (K.d i j)
      (K.cyclesIsKernel i j (c.next_eq' hij)) (cyclesShortComplex K i j).zero
      (K.toCycles_i i j))
  mono_f := inferInstanceAs (Mono (K.iCycles i))
  epi_g := epi_toCycles_of_exactAt K hij h

/-- The differential of the image complex factors through the images of the cycles maps. -/
private theorem map_d_eq_map_toCycles_comp_map_iCycles {D : Type*} [Category* D] [Abelian D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : HomologicalComplex C c) (p q : ι) :
    ((F.mapHomologicalComplex c).obj K).d p q = F.map (K.toCycles p q) ≫ F.map (K.iCycles q) := by
  rw [Functor.mapHomologicalComplex_obj_d, ← F.map_comp, toCycles_i]

/-- If `F` keeps the cycles sequences at `(i, j)` and `(j, k)` short exact, and `F(Z^k(K)) ⟶ F(K^k)`
is a monomorphism, then `F(K^i) ⟶ F(K^j) ⟶ F(K^k)` is exact. -/
private theorem exact_sc'_map_of_cyclesShortExact {D : Type*} [Category* D] [Abelian D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : HomologicalComplex C c) {i j k : ι}
    (hk : Mono (F.map (K.iCycles k)))
    (h₁ : ((cyclesShortComplex K i j).map F).ShortExact)
    (h₂ : ((cyclesShortComplex K j k).map F).ShortExact) :
    (((F.mapHomologicalComplex c).obj K).sc' i j k).Exact :=
  ShortComplex.exact_of_epi_of_isKernel (F.map (K.toCycles i j)) (F.map (K.iCycles j))
    h₁.epi_g (map_d_eq_map_toCycles_comp_map_iCycles F K i j).symm
    (by
      change F.map (K.iCycles j) ≫ ((F.mapHomologicalComplex c).obj K).d j k = 0
      rw [Functor.mapHomologicalComplex_obj_d, ← F.map_comp, iCycles_d, F.map_zero])
    (isKernelCompMono (hg := hk) h₂.fIsKernel (F.map (K.iCycles k))
      (map_d_eq_map_toCycles_comp_map_iCycles F K j k))

end HomologicalComplex

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type*} [Category* D] [Abelian D]

/-- **A functor which keeps the cycles sequences of a cochain complex short exact carries it to
an acyclic complex.**

The functor is not assumed exact, and the complex is not assumed acyclic: both are consequences
of the hypothesis, which at the index pair `(i, j)` says that

`0 ⟶ F(Z^i(K)) ⟶ F(K^i) ⟶ F(Z^j(K)) ⟶ 0`

is short exact.  At degree `n` the differential of `F(K)` is then `F(Z^n(K)) ↪ F(K^{n+1})`
precomposed with the epimorphism `F(K^n) ↠ F(Z^{n+1}(K))`, so `F(Z^n(K))` is a kernel of it,
and the incoming differential factors through that kernel by an epimorphism. -/
theorem acyclic_mapHomologicalComplex_of_cyclesShortExact
    (F : C ⥤ D) [F.PreservesZeroMorphisms] (K : CochainComplex C ℤ)
    (h : ∀ i j : ℤ, (ComplexShape.up ℤ).Rel i j →
      ((HomologicalComplex.cyclesShortComplex K i j).map F).ShortExact) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic := by
  intro n
  rw [HomologicalComplex.exactAt_iff' _ (n - 1) n (n + 1)
    ((ComplexShape.up ℤ).prev_eq' (by simp)) ((ComplexShape.up ℤ).next_eq' rfl)]
  exact HomologicalComplex.exact_sc'_map_of_cyclesShortExact F K
    (h (n + 1) (n + 2) (by change n + 1 + 1 = n + 2; omega)).mono_f (h (n - 1) n (by simp))
    (h n (n + 1) rfl)

end CochainComplex

namespace ChainComplex

open ZeroObject

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type*} [Category* D] [Abelian D]

/-- **The cycles of an acyclic chain complex inherit a property closed under the kernel of a
short exact sequence.**

If `P` holds for every term of the `ℕ`-indexed chain complex `K`, and the first term of a short
exact sequence satisfies `P` whenever the other two do, then `P` holds for the cycles of `K` in
every degree.  In degree `n + 1` this is the short exact cycles sequence
`Z_{n+1}(K) ⟶ K_{n+1} ⟶ Z_n(K)`; in degree `0` the cycles are the whole of `K_0`, because the
outgoing differential there is zero. -/
theorem prop_cycles_of_acyclic (P : C → Prop)
    (hP : ∀ S : ShortComplex C, S.ShortExact → P S.X₂ → P S.X₃ → P S.X₁)
    (K : ChainComplex C ℕ) (hK : K.Acyclic) (hX : ∀ i, P (K.X i)) (n : ℕ) :
    P (K.cycles n) := by
  induction n with
  | zero =>
    have hzero : P (0 : C) := by
      refine hP (ShortComplex.mk (0 : (0 : C) ⟶ K.X 0) (𝟙 (K.X 0)) (by simp)) ?_ (hX 0) (hX 0)
      exact { exact := (ShortComplex.exact_iff_mono _ rfl).2 inferInstance
              mono_f := ⟨fun _ _ _ ↦ (isZero_zero C).eq_of_tgt _ _⟩
              epi_g := inferInstance }
    refine hP (ShortComplex.mk (K.iCycles 0) (0 : K.X 0 ⟶ (0 : C)) (by simp)) ?_ (hX 0) hzero
    exact { exact := (ShortComplex.exact_iff_epi _ rfl).2 inferInstance
            mono_f := inferInstanceAs (Mono (K.iCycles 0))
            epi_g := ⟨fun _ _ _ ↦ (isZero_zero C).eq_of_src _ _⟩ }
  | succ m ih =>
    exact hP _ (K.cyclesShortComplex_shortExact (i := m + 1) (j := m) rfl (hK m))
      (hX (m + 1)) ih

/-- **A functor which keeps the cycles sequences of an `ℕ`-indexed chain complex short exact
carries it to an acyclic complex.**

The functor is not assumed exact and the complex is not assumed acyclic; both are consequences
of the hypothesis, which at the index `n` says that

`0 ⟶ F(Z_{n+1}(K)) ⟶ F(K_{n+1}) ⟶ F(Z_n(K)) ⟶ 0`

is short exact.  In a positive degree the argument is the one of
`CochainComplex.acyclic_mapHomologicalComplex_of_cyclesShortExact`: the differential of `F(K)`
is the inclusion `F(Z_n(K)) ↪ F(K_n)` precomposed with the epimorphism
`F(K_{n+1}) ↠ F(Z_n(K))`, so the former is a kernel of it and the incoming differential factors
through that kernel by an epimorphism.  In degree `0` the outgoing differential vanishes and
exactness is epimorphy of `F(K_1) ⟶ F(K_0)`, which holds because `Z_0(K) ⟶ K_0` is an
isomorphism. -/
theorem acyclic_mapHomologicalComplex_of_cyclesShortExact
    (F : C ⥤ D) [F.PreservesZeroMorphisms] (K : ChainComplex C ℕ)
    (h : ∀ n : ℕ, ((HomologicalComplex.cyclesShortComplex K (n + 1) n).map F).ShortExact) :
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K).Acyclic := by
  have hmono : ∀ q : ℕ, Mono (F.map (K.iCycles q))
    | 0 => inferInstance
    | m + 1 => (h m).mono_f
  intro n
  match n with
  | 0 =>
    have hepi : Epi (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K).d 1 0) := by
      have : Epi (F.map (K.toCycles 1 0)) := (h 0).epi_g
      rw [HomologicalComplex.map_d_eq_map_toCycles_comp_map_iCycles]
      exact epi_comp _ _
    have hg0 : ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K).d 0 0 = 0 :=
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K).shape 0 0 (by simp)
    rw [HomologicalComplex.exactAt_iff' _ 1 0 0 (by simp) (by simp)]
    exact (ShortComplex.exact_iff_epi _ hg0).2 hepi
  | m + 1 =>
    rw [HomologicalComplex.exactAt_iff' _ (m + 2) (m + 1) m (by simp) (by simp)]
    exact HomologicalComplex.exact_sc'_map_of_cyclesShortExact F K (hmono m) (h (m + 1)) (h m)

/-- **Tensoring an acyclic complex of objects of an adapted class.**

Let `P` be a class of objects of an abelian category which contains the first term of any short
exact sequence whose other two terms belong to it, and let `F` be a functor which carries a
short exact sequence whose third term belongs to `P` to a short exact sequence.  Then `F`
carries every acyclic `ℕ`-indexed chain complex whose terms belong to `P` to an acyclic
complex: the cycles belong to `P` by `ChainComplex.prop_cycles_of_acyclic`, so the cycles
sequences stay short exact and
`ChainComplex.acyclic_mapHomologicalComplex_of_cyclesShortExact` applies. -/
theorem acyclic_mapHomologicalComplex_of_prop (P : C → Prop)
    (hP : ∀ S : ShortComplex C, S.ShortExact → P S.X₂ → P S.X₃ → P S.X₁)
    (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (hF : ∀ S : ShortComplex C, S.ShortExact → P S.X₃ → (S.map F).ShortExact)
    (K : ChainComplex C ℕ) (hK : K.Acyclic) (hX : ∀ i, P (K.X i)) :
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K).Acyclic :=
  acyclic_mapHomologicalComplex_of_cyclesShortExact F K fun n ↦
    hF _ (K.cyclesShortComplex_shortExact (i := n + 1) (j := n) rfl (hK n))
      (prop_cycles_of_acyclic P hP K hK hX n)

end ChainComplex

end

end
