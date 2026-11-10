module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.MonomialKoszulStrand
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.TrivialMonomial

/-!
# The degree-`n` row of Tag 01XW over an arbitrary base

Let `S` be a scheme, let `n = m + 1 ≥ 1`, let `d` be an integer and let `f : ℙⁿ_S ⟶ S` be the
structure morphism of projective `n`-space over `S`. The degree-`n` row of the display of
[Stacks, Tag 01XW] reads

`Rⁿ f_* 𝒪(d) ≅ Hom_{𝒪_S}((𝒪_S[T₀, …, Tₙ])_{-n-1-d}, 𝒪_S)`,

and this file proves it for every twist `d` and every base `S`. The morphism being inverted is
the duality pairing `pairing`: its component at a multidegree `b` of total degree `t = -n-1-d` is
multiplication by the monomial `T^b`, a map `Rⁿ f_* 𝒪(d) ⟶ Rⁿ f_* 𝒪(-n-1)`, followed by the trace
isomorphism `Rⁿ f_* 𝒪(-n-1) ≅ 𝒪_S`.

The proof is an induction on the complementary degree `t`. For `t < 0` both sides vanish, and for
`t = 0` the only multidegree is the zero one, where multiplication by `T^b` is the identity and
the pairing is the trace. For `t ≥ 1` the Koszul complex of the coordinates at the twist `d`,

`0 ⟶ 𝒪(d) ⟶ 𝒪(d+1)^{⊕ binom(n+1,1)} ⟶ ⋯ ⟶ 𝒪(d+n+1) ⟶ 0`,

has all of its terms silent for `f_*` outside the degree `n`, so its degree-`n` higher direct
images form an exact sequence; in particular `Rⁿ f_* 𝒪(d)` is a **kernel** of the map from the
first to the second term. On the other side the degree-`t` part of the polynomial algebra is,
dually, a kernel of the corresponding dual Koszul map, by `isLimit_dualDiff`. The pairings at
the twists `d + 1` and `d + 2` are isomorphisms by induction, they intertwine the two Koszul maps
entry by entry, and two kernels of isomorphic maps are isomorphic.

The names in the lists below are relative to the
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage` namespace.

## Main definitions

* `pushKoszul`: the complex of degree-`n` higher direct images of the Koszul complex of `ℙⁿ_S`.
* `pushKoszulIso`: its degree-`j` term as a direct sum of copies of `Rⁿ f_* 𝒪(d+j)`.
* `pushKoszulCompare`: the comparison of that term with the direct sum of copies of the dual of
  the degree-`(-n-1-d-j)` part of the polynomial algebra.
* `rightDerivedPlusTopIsoDualBaseDegreeSheaf`: **the degree-`n` row of [Stacks, Tag 01XW] over an
  arbitrary base, for every twist.**

## Main results

* `koszulCoeff_comp_pairing`: **the comparison morphisms intertwine the Koszul differential with
  its dual, entry by entry.**
* `pushKoszul_square`: the same, as a commuting square of direct sums.
* `isLimit_pushKoszul`: the pushed Koszul complex presents its degree-zero term as a kernel.
* `isIso_pairing`: **the duality pairing is an isomorphism**, for every twist and every base.

## Implementation notes

The degree-`j` term of the Koszul complex of `ℙⁿ_S` is a direct sum of copies of the twist
`𝒪(a+j)`, with the source degree spelled `a + j` and not normalised; the comparison morphisms
below are therefore indexed by `a + j` as well, and `pairing_eqToHom_comp` is what converts the
degree-zero instance `a + 0` into the twist `a` the statement of the row is about. The two
transports it rests on, `twistOverMulMonomial_eqToHom_comp` and
`twistOverMulMonomial_comp_eqToHom`, are substitutions of an integer and nothing more.

The Koszul complex lives on the integral model in the spelling
`CategoryTheory.SheafOfModules` of the category of modules, and the functors applied to it in
the spelling `AlgebraicGeometry.Scheme.Modules`; the two are definitionally equal but not
syntactically so, and a `rw` whose motive mentions an object in the first spelling where the
second is expected is rejected at `implicit` transparency. Every step that distributes a functor
over the additive structure of the Koszul differential is therefore taken as a term with the
functor supplied — `CategoryTheory.Functor.map_zsmul (pullPush m S (m + 1))` rather than
`rw [Functor.map_zsmul]` — and the comparison isomorphisms are introduced with their targets
ascribed, so that the direct sums downstream are formed on one family.

No `stacks` attribute is attached: what is proved here is one row of [Stacks, Tag 01XW]. The
range `-n - 1 < d`, where the statement is the vanishing of both sides, is also
`rightDerivedPlusTopIsoDualBaseDegreeSheaf_of_lt`. The three rows of the display in one
statement, at `n ≥ 1`, are
`StacksFrontier/AlgebraicGeometry/ProjectiveSpaceHigherDirectImage/Display.lean`.

## References

* [Stacks Project, Tag 01XW](https://stacks.math.columbia.edu/tag/01XW)
* [Stacks Project, Tag 0BQS](https://stacks.math.columbia.edu/tag/0BQS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)
open Stacks.AlgebraicGeometry.ReflexiveModules (dualSheaf)

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

open Stacks.AlgebraicGeometry.ProjKoszulComplex (koszulIndex koszulSign koszulCoeff koszulDiff
  koszulCoeff_eq koszulCoeff_eq_zero twistMulX)
open Stacks.AlgebraicGeometry.ProjKoszulOverBase (koszulOver koszulOver_d isZero_koszulOver_X)
open Stacks.AlgebraicGeometry.ProjPolyChart (X_mem_one)

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 2000] HasDerivedCategory.standard

/-! ### A diagonal morphism of biproducts -/

/-- **A diagonal morphism of finite biproducts is invertible componentwise**: an inverse of the
diagonal morphism given by a family `p` has `ι ≫ inv ≫ π` as its diagonal entries, and those are
inverses of the `p j`. -/
theorem isIso_of_isIso_biproduct_map {C : Type*} [Category C] [Preadditive C]
    [HasFiniteBiproducts C] {J : Type} [Finite J] {f g : J → C} (p : ∀ j, f j ⟶ g j)
    [IsIso (biproduct.map p)] (j : J) : IsIso (p j) := by
  refine ⟨biproduct.ι g j ≫ inv (biproduct.map p) ≫ biproduct.π f j, ?_, ?_⟩
  · rw [← Category.assoc, ← biproduct.ι_map, Category.assoc, IsIso.hom_inv_id_assoc,
      biproduct.ι_π_self]
  · rw [Category.assoc, Category.assoc, ← biproduct.map_π, IsIso.inv_hom_id_assoc,
      biproduct.ι_π_self]

/-! ### Transport of the comparison morphism along an equality of twists -/

/-- **Multiplication by a monomial out of a twist named by an equal integer** is the same
morphism, read through the transport of its source. -/
theorem twistOverMulMonomial_eqToHom_comp (n : ℕ) (S : Scheme.{u}) {e₁ : ℤ}
    (b : MonomialIndex.{u} n e₁) {d d' : ℤ} (hd : d' = d) (g : ℤ) (h : e₁ + d = g)
    (h' : e₁ + d' = g) :
    eqToHom (congrArg (twistOver n S) hd) ≫ twistOverMulMonomial n S b d g h =
      twistOverMulMonomial n S b d' g h' := by
  subst hd
  rw [eqToHom_refl, Category.id_comp]

/-- **Multiplication by a monomial into a twist named by an equal integer** is the same morphism,
read through the transport of its target. -/
theorem twistOverMulMonomial_comp_eqToHom (n : ℕ) (S : Scheme.{u}) {e₁ : ℤ}
    (b : MonomialIndex.{u} n e₁) (d : ℤ) {g g' : ℤ} (hg : g = g') (h : e₁ + d = g)
    (h' : e₁ + d = g') :
    twistOverMulMonomial n S b d g h ≫ eqToHom (congrArg (twistOver n S) hg) =
      twistOverMulMonomial n S b d g' h' := by
  subst hg
  rw [eqToHom_refl, Category.comp_id]

/-- **The comparison morphism of the degree-`n` row at a twist named by an equal integer** is the
same morphism, read through the transport of its source. -/
theorem pairing_eqToHom_comp (m : ℕ) (S : Scheme.{u}) {d d' t : ℤ} (hd : d' = d)
    (h : t + d = -((m + 1 : ℕ) : ℤ) - 1) (h' : t + d' = -((m + 1 : ℕ) : ℤ) - 1) :
    pairing m S d' t h' =
      (push m S (m + 1)).map (eqToHom (congrArg (twistOver (m + 1) S) hd)) ≫
        pairing m S d t h := by
  refine biproduct.hom_ext _ _ fun b => ?_
  simp only [pairing, Category.assoc, biproduct.lift_π]
  rw [← Category.assoc, ← Functor.map_comp,
    twistOverMulMonomial_eqToHom_comp (m + 1) S b hd (-((m + 1 : ℕ) : ℤ) - 1) h h']

/-! ### The entrywise intertwining identity -/

/-- **Multiplication by a coordinate on the twists of the integral model pulls back to
multiplication by the monomial of that coordinate on `ℙⁿ_S`.** -/
theorem pullback_twistMulX (n : ℕ) (S : Scheme.{u}) (i : Fin (n + 1)) (d e : ℤ)
    (he : (1 : ℤ) + d = e) :
    (Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse n S)).map
        (twistMulX (ULift.{u} ℤ) n i d e he) =
      twistOverMulMonomial n S (coordIndex.{u} i) d e he := by
  rw [twistOverMulMonomial]
  exact twistOverMulLeft_congr n S
    (⟨MvPolynomial.X i, X_mem_one (ULift.{u} ℤ) n i⟩ : integralHomogeneous.{u} n 1)
    ⟨coordMonomial (coordIndex.{u} i), coordMonomial_mem _⟩
    (coordMonomial_coordIndex i).symm d e _ _

/-- **The matrix entry of the Koszul differential of `ℙⁿ_S`, read through the degree-`n` higher
direct image**: a morphism `Rⁿ f_* 𝒪(a+j) ⟶ Rⁿ f_* 𝒪(a+j+1)`. -/
def pushKoszulCoeff (m : ℕ) (S : Scheme.{u}) (a j : ℤ) (s : koszulIndex (m + 1 + 1) j)
    (u : koszulIndex (m + 1 + 1) (j + 1)) :
    (push m S (m + 1)).obj (twistOver (m + 1) S (a + j)) ⟶
      (push m S (m + 1)).obj (twistOver (m + 1) S (a + (j + 1))) :=
  (pullPush m S (m + 1)).map (koszulCoeff (ULift.{u} ℤ) (m + 1) a j s u)

/-- **The matrix entry of the pushed Koszul differential at a pair of index sets differing by one
coordinate** is the Koszul sign of that coordinate times multiplication by it. -/
theorem pushKoszulCoeff_eq (m : ℕ) (S : Scheme.{u}) (a j : ℤ) (s : koszulIndex (m + 1 + 1) j)
    (u : koszulIndex (m + 1 + 1) (j + 1)) {i : Fin (m + 1 + 1)} (hi : i ∉ s.1)
    (hu : u.1 = insert i s.1) (hr : (1 : ℤ) + (a + j) = a + (j + 1)) :
    pushKoszulCoeff m S a j s u =
      koszulSign i s.1 • (push m S (m + 1)).map
        (twistOverMulMonomial (m + 1) S (coordIndex.{u} i) (a + j) (a + (j + 1)) hr) := by
  change (pullPush m S (m + 1)).map (koszulCoeff (ULift.{u} ℤ) (m + 1) a j s u) = _
  rw [koszulCoeff_eq (ULift.{u} ℤ) (m + 1) a j s u hi hu]
  exact (Functor.map_zsmul (pullPush m S (m + 1))).trans
    (congrArg (fun z => koszulSign i s.1 • (push m S (m + 1)).map z)
      (pullback_twistMulX (m + 1) S i (a + j) (a + (j + 1)) hr))

/-- **The matrix entry of the pushed Koszul differential vanishes** at a pair of index sets not
differing by a single new coordinate. -/
theorem pushKoszulCoeff_eq_zero (m : ℕ) (S : Scheme.{u}) (a j : ℤ)
    (s : koszulIndex (m + 1 + 1) j) (u : koszulIndex (m + 1 + 1) (j + 1))
    (h : ∀ i : Fin (m + 1 + 1), i ∉ s.1 → u.1 ≠ insert i s.1) :
    pushKoszulCoeff m S a j s u = 0 := by
  change (pullPush m S (m + 1)).map (koszulCoeff (ULift.{u} ℤ) (m + 1) a j s u) = _
  rw [koszulCoeff_eq_zero (ULift.{u} ℤ) (m + 1) a j s u h]
  exact Functor.map_zero (pullPush m S (m + 1)) _ _

/-- **The comparison morphisms intertwine the Koszul differential with its dual, entry by
entry**: the matrix entry of the Koszul differential of `ℙⁿ_S`, read through the degree-`n` higher
direct image, is carried by the comparison morphisms of the degree-`n` row to the matrix entry of
the dual Koszul differential of the monomial sums.

Both entries are a signed multiplication by a single coordinate when the two index sets differ by
that coordinate and zero otherwise, and in the first case the identity is
`pairing_comp_monomialSumMul`. -/
theorem koszulCoeff_comp_pairing (m : ℕ) (S : Scheme.{u}) (a j tj tj' : ℤ)
    (htj : tj + (a + j) = -((m + 1 : ℕ) : ℤ) - 1)
    (htj' : tj' + (a + (j + 1)) = -((m + 1 : ℕ) : ℤ) - 1) (hjj : 1 + tj' = tj)
    (s : koszulIndex (m + 1 + 1) j) (u : koszulIndex (m + 1 + 1) (j + 1)) :
    pushKoszulCoeff m S a j s u ≫ pairing m S (a + (j + 1)) tj' htj' =
      pairing m S (a + j) tj htj ≫ dualCoeff m S j (j + 1) hjj s u := by
  have hr : (1 : ℤ) + (a + j) = a + (j + 1) := by ring
  by_cases hex : ∃ i : Fin (m + 1 + 1), i ∉ s.1 ∧ u.1 = insert i s.1
  · obtain ⟨i, hi, hu⟩ := hex
    rw [pushKoszulCoeff_eq m S a j s u hi hu hr, dualCoeff_eq m S j (j + 1) hjj s u hi hu,
      Preadditive.zsmul_comp, Preadditive.comp_zsmul]
    exact congrArg (fun z => koszulSign i s.1 • z)
      (pairing_comp_monomialSumMul m S i (a + j) (a + (j + 1)) tj tj' hr hjj htj htj')
  · rw [pushKoszulCoeff_eq_zero m S a j s u fun i hi hu => hex ⟨i, hi, hu⟩,
      dualCoeff_eq_zero m S j (j + 1) hjj s u fun i hi hu => hex ⟨i, hi, hu⟩,
      zero_comp, comp_zero]

/-! ### The pushed Koszul complex and the commuting square -/

/-- **The complex of degree-`n` higher direct images of the Koszul complex of `ℙⁿ_S`** at the
twist `a`. -/
abbrev pushKoszul (m : ℕ) (S : Scheme.{u}) (a : ℤ) : CochainComplex S.Modules ℤ :=
  ((push m S (m + 1)).mapHomologicalComplex (ComplexShape.up ℤ)).obj (koszulOver (m + 1) S a)

/-- The family of summands of the degree-`j` term of the pushed Koszul complex: one copy of
`Rⁿ f_* 𝒪(a+j)` for each `j`-element set of coordinates. -/
abbrev pushKoszulFamily (m : ℕ) (S : Scheme.{u}) (a j : ℤ) :
    koszulIndex (m + 1 + 1) j → S.Modules :=
  fun _ => (push m S (m + 1)).obj (twistOver (m + 1) S (a + j))

/-- **The degree-`j` term of the pushed Koszul complex is a direct sum of copies of
`Rⁿ f_* 𝒪(a+j)`**, indexed by the `j`-element sets of coordinates. -/
def pushKoszulIso (m : ℕ) (S : Scheme.{u}) (a j : ℤ) :
    (pushKoszul m S a).X j ≅ ⨁ pushKoszulFamily.{u} m S a j :=
  Functor.mapBiproduct (pullPush m S (m + 1)) (koszulFamilyOver.{u} m a j)

/-- **The comparison morphism of the degree-`n` row at the degree-`j` term of the Koszul
complex**: the duality pairing at the twist `a + j` on each summand. -/
def pushKoszulCompare (m : ℕ) (S : Scheme.{u}) (a j tj : ℤ)
    (htj : tj + (a + j) = -((m + 1 : ℕ) : ℤ) - 1) :
    (pushKoszul m S a).X j ⟶ ⨁ fun _ : koszulIndex (m + 1 + 1) j => monomialSum (m + 1) S tj :=
  (pushKoszulIso m S a j).hom ≫
    biproduct.map (f := pushKoszulFamily.{u} m S a j) fun _ => pairing m S (a + j) tj htj

/-- **The comparison morphism at the degree-`j` term, as an isomorphism**, once the duality
pairing at the twist `a + j` is known to be one. -/
def pushKoszulCompareIso (m : ℕ) (S : Scheme.{u}) (a j tj : ℤ)
    (htj : tj + (a + j) = -((m + 1 : ℕ) : ℤ) - 1) [IsIso (pairing m S (a + j) tj htj)] :
    (pushKoszul m S a).X j ≅ ⨁ fun _ : koszulIndex (m + 1 + 1) j => monomialSum (m + 1) S tj :=
  pushKoszulIso m S a j ≪≫ biproduct.mapIso (f := pushKoszulFamily.{u} m S a j)
    fun _ => asIso (pairing m S (a + j) tj htj)

/-- The matrix of the differential of the pushed Koszul complex is the matrix of the values of
the Koszul coefficients. -/
theorem pushKoszulIso_inv_d_hom (m : ℕ) (S : Scheme.{u}) (a j : ℤ) :
    (pushKoszulIso m S a j).inv ≫ (pushKoszul m S a).d j (j + 1) ≫
        (pushKoszulIso m S a (j + 1)).hom =
      biproduct.matrix (pushKoszulCoeff m S a j) := by
  change (Functor.mapBiproduct (pullPush m S (m + 1)) (koszulFamilyOver.{u} m a j)).inv ≫
    (push m S (m + 1)).map ((koszulOver (m + 1) S a).d j (j + 1)) ≫
      (Functor.mapBiproduct (pullPush m S (m + 1)) (koszulFamilyOver.{u} m a (j + 1))).hom = _
  rw [koszulOver_d]
  exact Functor.mapBiproduct_inv_map_matrix (pullPush m S (m + 1))
    (koszulCoeff (ULift.{u} ℤ) (m + 1) a j)

/-- **The comparison morphisms of the degree-`n` row intertwine the Koszul differential with its
dual**: the square

```
(pushKoszul a).X j  --d-->  (pushKoszul a).X j'
       |                            |
    compare                      compare
       v                            v
  ⨁ monomialSum tj  --δ-->   ⨁ monomialSum tj'
```

commutes. Both composites are matrices, and `koszulCoeff_comp_pairing` is the identity of their
entries. -/
theorem pushKoszul_square (m : ℕ) (S : Scheme.{u}) (a j j' tj tj' : ℤ) (hj : j + 1 = j')
    (htj : tj + (a + j) = -((m + 1 : ℕ) : ℤ) - 1)
    (htj' : tj' + (a + j') = -((m + 1 : ℕ) : ℤ) - 1) (hjj : 1 + tj' = tj) :
    (pushKoszul m S a).d j j' ≫ pushKoszulCompare m S a j' tj' htj' =
      pushKoszulCompare m S a j tj htj ≫ dualDiff m S j j' hj hjj := by
  subst hj
  have hinv : (pushKoszulIso m S a j).inv ≫ (pushKoszul m S a).d j (j + 1) ≫
        (pushKoszulIso m S a (j + 1)).hom ≫
          biproduct.map (f := pushKoszulFamily.{u} m S a (j + 1))
            (fun _ => pairing m S (a + (j + 1)) tj' htj') =
      biproduct.map (f := pushKoszulFamily.{u} m S a j) (fun _ => pairing m S (a + j) tj htj) ≫
        dualDiff m S j (j + 1) rfl hjj :=
    calc _ = ((pushKoszulIso m S a j).inv ≫ (pushKoszul m S a).d j (j + 1) ≫
            (pushKoszulIso m S a (j + 1)).hom) ≫
              biproduct.map (f := pushKoszulFamily.{u} m S a (j + 1))
                (fun _ => pairing m S (a + (j + 1)) tj' htj') := by
          simp only [Category.assoc]
      _ = biproduct.matrix fun s u =>
            pushKoszulCoeff m S a j s u ≫ pairing m S (a + (j + 1)) tj' htj' := by
          rw [pushKoszulIso_inv_d_hom, biproduct.matrix_comp_map]
      _ = biproduct.matrix fun s u =>
            pairing m S (a + j) tj htj ≫ dualCoeff m S j (j + 1) hjj s u :=
          congrArg biproduct.matrix (funext fun s => funext fun u =>
            koszulCoeff_comp_pairing m S a j tj tj' htj htj' hjj s u)
      _ = biproduct.map (f := pushKoszulFamily.{u} m S a j)
              (fun _ => pairing m S (a + j) tj htj) ≫ dualDiff m S j (j + 1) rfl hjj := by
          rw [dualDiff, biproduct.map_comp_matrix]
  simp only [pushKoszulCompare, Category.assoc]
  exact (Iso.inv_comp_eq (pushKoszulIso m S a j)).1 hinv

/-! ### The degree-zero term of the pushed Koszul complex is a kernel -/

/-- **The pushed Koszul complex of a very negative twist presents its degree-zero term as a
kernel of its first differential**: the complex is exact and vanishes in the degree `-1`. -/
def isLimit_pushKoszul (m : ℕ) (S : Scheme.{u}) (a : ℤ)
    (ha : a + ((m + 1 : ℕ) : ℤ) + 1 < 0) :
    IsLimit (KernelFork.ofι ((pushKoszul m S a).d 0 1) ((pushKoszul m S a).d_comp_d 0 1 2)) := by
  have hmono : Mono ((pushKoszul m S a).d 0 1) := by
    have hz : IsZero ((pushKoszul m S a).X (-1)) :=
      Functor.map_isZero (push m S (m + 1))
        (isZero_koszulOver_X (m + 1) S a (-1) (Or.inl (by norm_num)))
    have hex : ((pushKoszul m S a).sc' (-1) 0 1).Exact := by
      rw [← HomologicalComplex.exactAt_iff' _ (-1) 0 1
        ((ComplexShape.up ℤ).prev_eq' (show (-1 : ℤ) + 1 = 0 by ring))
        ((ComplexShape.up ℤ).next_eq' (show (0 : ℤ) + 1 = 1 by ring))]
      exact acyclic_push_koszulOver m S a ha 0
    exact hex.mono_g (hz.eq_of_src _ _)
  have : Mono ((pushKoszul m S a).sc' 0 1 2).f := hmono
  have hex1 : ((pushKoszul m S a).sc' 0 1 2).Exact := by
    rw [← HomologicalComplex.exactAt_iff' _ 0 1 2
      ((ComplexShape.up ℤ).prev_eq' (show (0 : ℤ) + 1 = 1 by ring))
      ((ComplexShape.up ℤ).next_eq' (show (1 : ℤ) + 1 = 2 by ring))]
    exact acyclic_push_koszulOver m S a ha 1
  exact hex1.fIsKernel

/-! ### The induction on the complementary degree -/

/-- **There is only one multidegree of total degree zero**, the zero one. -/
instance uniqueMonomialIndexZero (n : ℕ) : Unique (MonomialIndex.{u} n 0) where
  default := ⟨0, by rw [map_zero]; rfl⟩
  uniq b := Subtype.ext ((Finsupp.degree_eq_zero_iff b.1).1 (by exact_mod_cast b.2))

/-- **The duality pairing is an isomorphism in a negative complementary degree**, both of its
sides being the zero sheaf there. -/
theorem isIso_pairing_of_neg (m : ℕ) (S : Scheme.{u}) (d t : ℤ)
    (ht : t + d = -((m + 1 : ℕ) : ℤ) - 1) (htneg : t < 0) : IsIso (pairing m S d t ht) := by
  have hX : IsZero ((push m S (m + 1)).obj (twistOver (m + 1) S d)) :=
    IsZero.of_iso (isZero_rightDerivedPlus_pushforward_twistOver_top_of_lt m S (by omega))
      ((Stacks.DerivedIndexing.rightDerivedIso
        (Scheme.Modules.pushforward (projectiveSpaceOver (m + 1) S ↘ S)) (m + 1)).app _)
  exact ⟨0, hX.eq_of_src _ _, (isZero_monomialSum_of_neg (m + 1) S htneg).eq_of_src _ _⟩

/-- **The duality pairing is an isomorphism in the complementary degree zero**, where the only
multidegree is the zero one and the pairing is the trace isomorphism. -/
theorem isIso_pairing_of_zero (m : ℕ) (S : Scheme.{u}) (d t : ℤ)
    (ht : t + d = -((m + 1 : ℕ) : ℤ) - 1) (ht0 : t = 0) : IsIso (pairing m S d t ht) := by
  subst ht0
  have hd : d = -((m + 1 : ℕ) : ℤ) - 1 := by omega
  have hπι : biproduct.π (fun _ : MonomialIndex.{u} (m + 1) 0 => Scheme.unitModule S) default ≫
      biproduct.ι (fun _ : MonomialIndex.{u} (m + 1) 0 => Scheme.unitModule S) default = 𝟙 _ := by
    refine biproduct.hom_ext _ _ fun b => ?_
    obtain rfl : b = default := Subsingleton.elim _ _
    rw [Category.assoc, biproduct.ι_π_self, Category.comp_id, Category.id_comp]
  have : IsIso (biproduct.π
      (fun _ : MonomialIndex.{u} (m + 1) 0 => Scheme.unitModule S) default) :=
    ⟨biproduct.ι (fun _ : MonomialIndex.{u} (m + 1) 0 => Scheme.unitModule S) default, hπι,
      biproduct.ι_π_self _ _⟩
  have hpair : pairing m S d 0 ht ≫
        biproduct.π (fun _ : MonomialIndex.{u} (m + 1) 0 => Scheme.unitModule S) default =
      (push m S (m + 1)).map (eqToHom (congrArg (twistOver (m + 1) S) hd)) ≫ (trace m S).hom := by
    rw [pairing, biproduct.lift_π]
    refine congrArg (fun z => (push m S (m + 1)).map z ≫ (trace m S).hom) ?_
    rw [← twistOverMulMonomial_comp_eqToHom (m + 1) S
        (default : MonomialIndex.{u} (m + 1) 0) d hd (by omega) ht,
      twistOverMulMonomial_zero (m + 1) S d default (by omega), Category.id_comp]
  have : IsIso (pairing m S d 0 ht ≫
      biproduct.π (fun _ : MonomialIndex.{u} (m + 1) 0 => Scheme.unitModule S) default) := by
    rw [hpair]
    infer_instance
  exact IsIso.of_isIso_comp_right (pairing m S d 0 ht) (biproduct.π _ default)

/-- **The inductive step of the degree-`n` row**: if the duality pairing is an isomorphism at the
twists `d + 1` and `d + 2` then it is one at `d`, provided the complementary degree of `d` is
positive.

The degree-`n` higher direct images of the Koszul complex at the twist `d` are exact, so
`Rⁿ f_* 𝒪(d)` is a kernel of the map from the first to the second term; the dual Koszul strand of
the monomial sums is split, so its degree-zero term is a kernel of the corresponding map; the
comparison morphisms of the two middle and two last terms are isomorphisms by hypothesis and
`pushKoszul_square` is the compatibility. -/
theorem isIso_pairing_step (m : ℕ) (S : Scheme.{u}) (d t : ℤ)
    (ht : t + d = -((m + 1 : ℕ) : ℤ) - 1) (ht1 : 1 ≤ t)
    (hi1 : IsIso (pairing m S (d + 1) (t - 1) (by omega)))
    (hi2 : IsIso (pairing m S (d + 2) (t - 2) (by omega))) :
    IsIso (pairing m S d t ht) := by
  have h0 : t + (d + 0) = -((m + 1 : ℕ) : ℤ) - 1 := by omega
  have h1 : t - 1 + (d + 1) = -((m + 1 : ℕ) : ℤ) - 1 := by omega
  have h2 : t - 2 + (d + 2) = -((m + 1 : ℕ) : ℤ) - 1 := by omega
  have hA1 : 1 + (t - 1) = t := by omega
  have hA2 : 1 + (t - 2) = t - 1 := by omega
  have hj0 : (0 : ℤ) + 1 = 1 := by ring
  have hj1 : (1 : ℤ) + 1 = 2 := by ring
  have : IsIso (pairing m S (d + 1) (t - 1) h1) := hi1
  have : IsIso (pairing m S (d + 2) (t - 2) h2) := hi2
  have hφ : IsIso (pushKoszulCompare m S d 0 t h0) :=
    isIso_of_isKernel_of_isKernel (isLimit_pushKoszul m S d (by omega))
      (isLimit_dualDiff m S ht1 hA1 hA2 hj0 hj1
        (dualDiff_comp_dualDiff m S hA1 hA2 hj0 hj1))
      (pushKoszulCompareIso m S d 1 (t - 1) h1) (pushKoszulCompareIso m S d 2 (t - 2) h2)
      (pushKoszul_square m S d 1 2 (t - 1) (t - 2) hj1 h1 h2 hA2)
      (pushKoszulCompare m S d 0 t h0)
      (pushKoszul_square m S d 0 1 t (t - 1) hj0 h0 h1 hA1).symm
  have : IsIso ((pushKoszulIso m S d 0).hom ≫
      biproduct.map (f := pushKoszulFamily.{u} m S d 0) fun _ => pairing m S (d + 0) t h0) := hφ
  have : IsIso (biproduct.map (f := pushKoszulFamily.{u} m S d 0)
      fun _ => pairing m S (d + 0) t h0) :=
    IsIso.of_isIso_comp_left (pushKoszulIso m S d 0).hom _
  have : IsIso (pairing m S (d + 0) t h0) :=
    isIso_of_isIso_biproduct_map (f := pushKoszulFamily.{u} m S d 0)
      (fun _ => pairing m S (d + 0) t h0) ⟨∅, by simp⟩
  have hd0 : d + 0 = d := by ring
  have : IsIso ((push m S (m + 1)).map
      (eqToHom (congrArg (twistOver (m + 1) S) hd0)) ≫ pairing m S d t ht) := by
    rw [← pairing_eqToHom_comp m S hd0 ht h0]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((push m S (m + 1)).map (eqToHom (congrArg (twistOver (m + 1) S) hd0)))
    (pairing m S d t ht)

/-- **The duality pairing is an isomorphism** in every complementary degree below a bound, by
strong induction on that degree. -/
theorem isIso_pairing_aux (m : ℕ) (S : Scheme.{u}) :
    ∀ (k : ℕ) (d t : ℤ) (ht : t + d = -((m + 1 : ℕ) : ℤ) - 1), t < (k : ℤ) →
      IsIso (pairing m S d t ht) := by
  intro k
  induction k with
  | zero =>
    intro d t ht htk
    exact isIso_pairing_of_neg m S d t ht (by exact_mod_cast htk)
  | succ k ih =>
    intro d t ht htk
    rcases lt_or_ge t (k : ℤ) with hlt | hge
    · exact ih d t ht hlt
    rcases lt_or_ge t 0 with hneg | hpos
    · exact isIso_pairing_of_neg m S d t ht hneg
    rcases eq_or_lt_of_le hpos with h0 | h1
    · exact isIso_pairing_of_zero m S d t ht h0.symm
    · push_cast at htk
      exact isIso_pairing_step m S d t ht h1
        (ih (d + 1) (t - 1) (by omega) (by omega)) (ih (d + 2) (t - 2) (by omega) (by omega))

/-- **The duality pairing of the degree-`n` row of [Stacks, Tag 01XW] is an isomorphism**, for
every scheme `S`, every `n = m + 1 ≥ 1` and every twist `d`. -/
theorem isIso_pairing (m : ℕ) (S : Scheme.{u}) (d t : ℤ)
    (ht : t + d = -((m + 1 : ℕ) : ℤ) - 1) : IsIso (pairing m S d t ht) :=
  isIso_pairing_aux m S (t + 1).toNat d t ht (by omega)

/-! ### The degree-`n` row -/

/-- **The degree-`n` row of [Stacks, Tag 01XW] over an arbitrary base**: for the structure
morphism `f : ℙⁿ_S ⟶ S` over an arbitrary scheme `S`, for `n = m + 1 ≥ 1` and for every integer
`d`,

`Rⁿ f_* 𝒪(d) ≅ Hom_{𝒪_S}((𝒪_S[T₀, …, Tₙ])_{-n-1-d}, 𝒪_S)`.

The isomorphism is the duality pairing `pairing`, whose component at a multidegree `b` of total
degree `-n-1-d` is multiplication by `T^b` followed by the trace isomorphism, composed with the
identification `monomialSumIsoDual` of the direct sum of copies of `𝒪_S` indexed by those
multidegrees with the `𝒪_S`-dual of `(𝒪_S[T₀, …, Tₙ])_{-n-1-d}`. -/
def rightDerivedPlusTopIsoDualBaseDegreeSheaf (m : ℕ) (S : Scheme.{u}) (d : ℤ) :
    (((Scheme.Modules.pushforward (projectiveSpaceOver (m + 1) S ↘ S)).rightDerivedPlus
        ((m + 1 : ℕ) : ℤ)).obj (twistOver (m + 1) S d)) ≅
      dualSheaf (baseDegreeSheaf (m + 1) S (-((m + 1 : ℕ) : ℤ) - 1 - d)) :=
  haveI := isIso_pairing m S d (-((m + 1 : ℕ) : ℤ) - 1 - d) (by ring)
  ((Stacks.DerivedIndexing.rightDerivedIso
        (Scheme.Modules.pushforward (projectiveSpaceOver (m + 1) S ↘ S)) (m + 1)).app
      (twistOver (m + 1) S d)).symm ≪≫
    asIso (pairing m S d (-((m + 1 : ℕ) : ℤ) - 1 - d) (by ring)) ≪≫
    monomialSumIsoDual (m + 1) S (-((m + 1 : ℕ) : ℤ) - 1 - d)

end Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

end
