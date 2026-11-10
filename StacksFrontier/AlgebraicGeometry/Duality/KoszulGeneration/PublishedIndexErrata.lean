module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksFrontier.RingTheory.Koszul.DerivedQuotientModel
public import StacksFrontier.RingTheory.MvPolynomial.VariablesRegular

/-!
# Counterexamples to the published indices of [Stacks, Tag 0GEJ] and [Stacks, Tag 0GEK]

In Situation [Stacks, Tag 08CZ] — a ring `A`, elements `f₁, …, f_r ∈ A`, `X = Spec A`,
`U = X ∖ V(f₁, …, f_r)` with open immersion `j : U ⟶ X`, and `K` the perfect object of
`D(𝒪_X)` given by the Koszul complex on `f₁, …, f_r` — the two tags compare, for `E ∈ D_QCoh(𝒪_X)`
and `a ∈ ℤ`, the conditions

* 0GEJ: (1) `τ_{≥a}E ⟶ τ_{≥a}Rj_*(E|_U)` is an isomorphism, and
  (2) `Hom_{D(𝒪_X)}(K[-n], E) = 0` for all `n ≥ a`;
* 0GEK: (1) `τ_{≤a}E ⟶ τ_{≤a}Rj_*(E|_U)` is an isomorphism, and
  (2) `Hom_{D(𝒪_X)}(K[-n], E) = 0` for all `n ≤ a`.

0GEJ summarises itself as "(2) implies (1) and (1) implies (2) with `a` replaced by `a + 1`", and
0GEK as "(2) implies (1) and (1) implies (2) with `a` replaced by `a - 1`". This file proves that
**one conjunct of each summary is false**, by the two data recorded below. No statement of either
source is weakened or repaired here; the two implications this repository proves are the sharp
ones of `StacksFrontier/AlgebraicGeometry/Duality/KoszulHighDegreeOrthogonality.lean` and
`StacksFrontier/AlgebraicGeometry/Duality/KoszulTruncatedOrthogonality.lean`.

## The two counterexamples

**0GEJ, at `A = k[x, y]`, `f = (x, y)`, `E = k = A/(x, y)`, `a = 1`.** Here `r = 2`,
`U = Spec A ∖ {origin}` and `K ≃ A/(x, y)` in `D(A)` because `x, y` is a Koszul-regular sequence.
Condition (1) holds at `a = 1`: `E` restricts to zero on `U`, so `Rj_*(E|_U) = 0`, and
`τ_{≥1}E = 0`, so the canonical map is an isomorphism of zero objects. Condition (2) fails at
`a + 1 = 2`: `Hom(K[-2], E) = Ext²_A(k, k) ≠ 0`. **So "(1) implies (2) with `a` replaced by
`a + 1`" is false.** The index that holds is `a + r = 3`, which is the index of
`Stacks.Koszul.Truncation.hom_koszul_eq_zero_of_truncGE_restriction`.

**0GEK, at `A = k[x]`, `f = (x)`, `E = 𝒪_X`, `a = 0`.** Here `r = 1`, `U = D(x)` and
`K ≃ A/(x)` in `D(A)`. Condition (2) holds at `a = 0`: `Hom(K[-n], E) = Ext^n_A(A/x, A) = 0` for
every `n ≤ 0`, the group at `n = 0` being `Hom_A(A/x, A) = 0` because `A` is a domain and the
negative ones vanishing by t-structure orthogonality. Condition (1) fails at `a = 0`:
`Rj_*(E|_U) = A[1/x]` in degree `0`, both sides are `≤ 0`, and the unit `A ⟶ A[1/x]` is not an
isomorphism because `x` is not a unit of `A`. **So "(2) implies (1)" is false.** What holds is
"(2) at `a + 1` implies (1) at `a`", the index of
`Stacks.Koszul.Truncation.truncLE_restriction_of_hom_koszul_eq_zero`.

## How the published situation is rendered

Everything below lives in `D(ModuleCat A)`, the affine side of the comparison
`D(A) ≌ D_QCoh(𝒪_{Spec A})` of [Stacks, Tag 06Z0]
(`AlgebraicGeometry.derivedGlobalSectionsQuasicoherent_isEquivalence`), under which:

* `K` — the sheafified Koszul object `Stacks.Koszul.Truncation.koszulObject f` is
  `DerivedCategory.Q.obj` of the termwise sheafification of `Koszul.seqCochainComplex f`, so it
  corresponds to `DerivedCategory.Q.obj (Koszul.seqCochainComplex f)`, which is what is used here;
* `E|_U = 0` — `U` is covered by the principal opens `D(f_i)`, so a quasi-coherent `E` restricts to
  zero on `U` exactly when each localisation `E_{f_i}` vanishes, which is the form
  `Errata.restrictsToZero_modXY` takes;
* `Rj_*(𝒪_U)` for `U = D(x)` — `j` is an affine open immersion, so `Rj_*` is restriction of
  scalars along `A ⟶ A[1/x]` and the unit of the adjunction is the localisation map; that map,
  placed in degree `0`, is `Errata.unitHomGEK`.

The conditions are invariant under isomorphism in `D(A)`, and the identification
`DerivedCategory.Q.obj (Koszul.seqCochainComplex f) ≅ A/(f)` for a Koszul-regular sequence is
`Koszul.nonempty_Q_obj_seqCochainComplex_iso_single`; `MvPolynomial.isKoszulRegular_X` supplies
the regularity.

## Main results

* `Stacks.Koszul.Errata.erratum_0GEJ` — at the 0GEJ datum, condition (1) holds at `a = 1` while
  condition (2) fails at `a + 1 = 2`.
* `Stacks.Koszul.Errata.erratum_0GEK` — at the 0GEK datum, condition (2) holds at `a = 0` while
  condition (1) fails at `a = 0`.
* `Stacks.Koszul.Errata.not_subsingleton_ext_two` — `Ext²_{k[x,y]}(k, k) ≠ 0`, the arithmetic
  heart of the first counterexample, obtained from the two short exact sequences
  `0 ⟶ A --x--> A ⟶ A/(x) ⟶ 0` and `0 ⟶ A/(x) --y--> A/(x) ⟶ A/(x,y) ⟶ 0` and the fact that
  `x` and `y` act as zero on `A/(x, y)`.
* `Stacks.Koszul.Errata.not_isZero_objE` and `Stacks.Koszul.Errata.not_isZero_objEGEK` — the two
  objects `E` are nonzero, so neither counterexample is degenerate.

## Implementation notes

**No Stacks tag attribute is attached to anything in this file**, and none should be: a
counterexample to a published summary is not a clause of the tag it refutes. The errata are for the
operator to record.

**`k[x]` is `MvPolynomial (Fin 1) k` and `k[x, y]` is `MvPolynomial (Fin 2) k`.** Writing both
polynomial rings on `Fin r` makes `MvPolynomial.isKoszulRegular_X`,
`MvPolynomial.one_notMem_span_X_image` and `MvPolynomial.mem_span_X_image_of_X_mul_mem` apply
verbatim, the last of these being exactly the regularity of `y` modulo `(x)` that the second short
exact sequence needs. `MvPolynomial (Fin 1) k` is the polynomial ring in one variable.

**The derived category is pinned to `CategoryTheory.HasDerivedCategory.standard`**, by a
`local instance`, because `Koszul.nonempty_Q_obj_seqCochainComplex_iso_single` is stated there.
That costs nothing: all models of `D(A)` are equivalent, and a counterexample at one model is a
counterexample.

**The `Ext²` nonvanishing is a triangulated-category argument, not a resolution computation.** The
two short exact sequences give distinguished triangles whose first morphism is `c • 𝟙` for `c` one
of the two variables; since `c` annihilates `A/(x, y)`, precomposition with the connecting morphism
of each triangle is injective on morphisms into any shift of `E`
(`Stacks.Koszul.Errata.eq_zero_of_mor₃_comp_eq_zero`), and chaining the two injections carries the
nonzero quotient map `A ⟶ A/(x, y)` to a nonzero element of `Ext²`. The `Linear A`-structure on
`D(ModuleCat A)` and the `A`-linearity of the shift and single functors are
`Mathlib/Algebra/Homology/DerivedCategory/Linear.lean`.

## References

* [Stacks Project, Tag 0GEJ](https://stacks.math.columbia.edu/tag/0GEJ)
* [Stacks Project, Tag 0GEK](https://stacks.math.columbia.edu/tag/0GEK)
* [Stacks Project, Tag 08CZ](https://stacks.math.columbia.edu/tag/08CZ)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 062F](https://stacks.math.columbia.edu/tag/062F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks.Koszul.Errata

attribute [local instance] HasDerivedCategory.standard

universe w v u

/-! ### Transport of Hom-vanishing along isomorphisms and shifts -/

section Transport

variable {𝒞 : Type u} [Category.{v} 𝒞]

/-- Hom-vanishing transports along an isomorphism of the source. -/
theorem subsingleton_hom_of_iso_left {X X' Y : 𝒞} (e : X ≅ X')
    (h : Subsingleton (X' ⟶ Y)) : Subsingleton (X ⟶ Y) :=
  ⟨fun u v => (cancel_epi e.inv).mp (h.allEq (e.inv ≫ u) (e.inv ≫ v))⟩

/-- Hom-vanishing transports along an isomorphism of the target. -/
theorem subsingleton_hom_of_iso_right {X Y Y' : 𝒞} (e : Y ≅ Y')
    (h : Subsingleton (X ⟶ Y')) : Subsingleton (X ⟶ Y) :=
  ⟨fun u v => (cancel_mono e.hom).mp (h.allEq (u ≫ e.hom) (v ≫ e.hom))⟩

end Transport

section TransportShift

variable {𝒞 : Type u} [Category.{v} 𝒞] [HasShift 𝒞 ℤ]

/-- Moving a shift from the source to the target: if nothing nonzero goes from `X⟦-m⟧` to `Y`
then nothing nonzero goes from `X` to `Y⟦m⟧`. -/
theorem subsingleton_hom_shift_target {X Y : 𝒞} (m : ℤ)
    (h : Subsingleton (X⟦-m⟧ ⟶ Y)) : Subsingleton (X ⟶ Y⟦m⟧) := by
  refine ⟨fun u v => (shiftFunctor 𝒞 (-m)).map_injective ?_⟩
  exact (cancel_mono ((shiftFunctorCompIsoId 𝒞 m (-m) (by omega)).app Y).hom).mp (h.allEq _ _)

end TransportShift

/-! ### Detecting a morphism through the connecting map of a distinguished triangle -/

section Triangles

variable {𝒟 : Type u} [Category.{v} 𝒟] [Preadditive 𝒟] [HasZeroObject 𝒟] [HasShift 𝒟 ℤ]
  [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟]

/-- **Precomposition with the connecting morphism of a distinguished triangle is injective once
the first morphism kills everything into the target.** If every morphism `T.obj₂⟦1⟧ ⟶ X` is
annihilated by `T.mor₁⟦1⟧`, then a morphism `T.obj₁⟦1⟧ ⟶ X` whose composite with `T.mor₃`
vanishes is itself zero.

This is exactness of `Hom(−, X)` at `Hom(T.obj₁⟦1⟧, X)`, read off the doubly rotated
triangle. -/
theorem eq_zero_of_mor₃_comp_eq_zero {T : Triangle 𝒟} (hT : T ∈ distTriang 𝒟) {X : 𝒟}
    (hkill : ∀ g : (T.obj₂)⟦(1 : ℤ)⟧ ⟶ X, (shiftFunctor 𝒟 (1 : ℤ)).map T.mor₁ ≫ g = 0)
    (h : (T.obj₁)⟦(1 : ℤ)⟧ ⟶ X) (hh : T.mor₃ ≫ h = 0) : h = 0 := by
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ T.rotate.rotate
    (rot_of_distTriang _ (rot_of_distTriang _ hT)) h hh
  have key : ∀ u : (T.obj₂)⟦(1 : ℤ)⟧ ⟶ X,
      (-((shiftFunctor 𝒟 (1 : ℤ)).map T.mor₁)) ≫ u = 0 := by
    intro u
    rw [Preadditive.neg_comp, hkill u, neg_zero]
  exact hg.trans (key g)

end Triangles

/-! ### Scalars that annihilate an object -/

section LinearShift

variable {R : Type*} [Ring R] {𝒟 : Type u} [Category.{v} 𝒟] [Preadditive 𝒟] [Linear R 𝒟]
  [HasShift 𝒟 ℤ] [∀ n : ℤ, (shiftFunctor 𝒟 n).Linear R]

/-- A scalar annihilating an object annihilates all its shifts. -/
theorem smul_id_shift_eq_zero (c : R) {X : 𝒟} (h : c • 𝟙 X = 0) (n : ℤ) :
    c • 𝟙 (X⟦n⟧) = 0 := by
  rw [← (shiftFunctor 𝒟 n).map_id X, ← (shiftFunctor 𝒟 n).map_smul, h,
    (shiftFunctor 𝒟 n).map_zero]

omit [HasShift 𝒟 ℤ] [∀ n : ℤ, (shiftFunctor 𝒟 n).Linear R] in
/-- A scalar annihilating an object annihilates every morphism into it. -/
theorem smul_eq_zero_of_smul_id_target (c : R) {Y X : 𝒟} (hX : c • 𝟙 X = 0) (u : Y ⟶ X) :
    c • u = 0 := by
  rw [← Category.comp_id u, ← Linear.comp_smul, hX, comp_zero]

/-- Applying a shift to a scalar multiple of an identity and composing with a morphism into an
object killed by the scalar gives zero. -/
private theorem shift_map_smul_id_comp_eq_zero (c : R) {Y Z : 𝒟} (hY : c • 𝟙 Y = 0)
    (g : Z⟦(1 : ℤ)⟧ ⟶ Y) : (shiftFunctor 𝒟 (1 : ℤ)).map (c • 𝟙 Z) ≫ g = 0 := by
  rw [Functor.map_smul, Linear.smul_comp, smul_eq_zero_of_smul_id_target c hY]

end LinearShift

/-! ### The single-object embedding and the canonical t-structure -/

section Single

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- Hom-vanishing in an abelian category gives Hom-vanishing between the single objects of its
derived category: the single functor is full. -/
theorem subsingleton_hom_single (M N : C) (h : Subsingleton (M ⟶ N)) :
    Subsingleton ((DerivedCategory.singleFunctor C 0).obj M ⟶
      (DerivedCategory.singleFunctor C 0).obj N) := by
  refine ⟨fun u v => ?_⟩
  obtain ⟨u', rfl⟩ := (DerivedCategory.singleFunctor C 0).map_surjective u
  obtain ⟨v', rfl⟩ := (DerivedCategory.singleFunctor C 0).map_surjective v
  rw [h.allEq u' v']

/-- **A morphism between objects concentrated in degrees `≤ n` is invertible as soon as its
`τ_{≤n}` is.** The comparison `τ_{≤n}X ⟶ X` is invertible at both ends, so the naturality square
factors the morphism through `τ_{≤n}` of it. -/
theorem isIso_of_isIso_truncLE_map {X Y : DerivedCategory C} (f : X ⟶ Y) (n : ℤ)
    [X.IsLE n] [Y.IsLE n]
    (h : IsIso ((DerivedCategory.TStructure.t.truncLE n).map f)) : IsIso f := by
  have hf : f = inv ((DerivedCategory.TStructure.t.truncLEι n).app X) ≫
      ((DerivedCategory.TStructure.t.truncLE n).map f ≫
        (DerivedCategory.TStructure.t.truncLEι n).app Y) := by
    rw [(DerivedCategory.TStructure.t.truncLEι n).naturality f]
    simp
  rw [hf]
  infer_instance

end Single

/-! ### Scalars acting on a quotient ring -/

section Quotient

variable {A : Type u} [CommRing A]

/-- An element of an ideal annihilates the quotient by it. -/
theorem smul_eq_zero_of_mem {I : Ideal A} {c : A} (hc : c ∈ I) (q : A ⧸ I) : c • q = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective I q
  rw [← Submodule.Quotient.mk_smul]
  exact (Submodule.Quotient.mk_eq_zero I).2 (by
    simpa [smul_eq_mul] using Ideal.mul_mem_right a I hc)

/-- An element of an ideal annihilates the identity of the quotient module. -/
theorem smul_id_quotient_eq_zero {I : Ideal A} {c : A} (hc : c ∈ I) :
    c • 𝟙 (ModuleCat.of A (A ⧸ I)) = 0 :=
  ModuleCat.hom_ext (LinearMap.ext fun q => smul_eq_zero_of_mem hc q)

/-- **There is no nonzero map from a cyclic torsion module to a domain.** If some nonzero `c` of a
domain `A` lies in `I`, then `Hom_A(A/I, A) = 0`. -/
theorem subsingleton_hom_quotient_self [IsDomain A] (I : Ideal A) {c : A} (hc : c ≠ 0)
    (hcI : c ∈ I) : Subsingleton (ModuleCat.of A (A ⧸ I) ⟶ ModuleCat.of A A) := by
  have key : ∀ f : (A ⧸ I) →ₗ[A] A, f = 0 := by
    intro f
    have h1 : f (Submodule.Quotient.mk (1 : A)) = 0 := by
      have hcf : c * f (Submodule.Quotient.mk (1 : A)) = 0 := by
        rw [← smul_eq_mul, ← map_smul, smul_eq_zero_of_mem hcI, map_zero]
      exact (mul_eq_zero.mp hcf).resolve_left hc
    refine LinearMap.ext fun q => ?_
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective I q
    rw [show (Submodule.Quotient.mk a : A ⧸ I) = a • Submodule.Quotient.mk (1 : A) by
      rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one], map_smul, h1, smul_zero,
      LinearMap.zero_apply]
  refine ⟨fun u v => ?_⟩
  rw [← ModuleCat.ofHom_hom u, ← ModuleCat.ofHom_hom v, key u.hom, key v.hom]

end Quotient

/-! ### [Stacks, Tag 0GEK]: `A = k[x]`, `f = (x)`, `E = 𝒪_X`, `a = 0` -/

section GEK

variable (k : Type u) [Field k]

/-- `A = k[x]`, the polynomial ring in one variable. -/
abbrev ringGEK : Type u := MvPolynomial (Fin 1) k

/-- the sequence `f = (x)`. -/
abbrev seqGEK : Fin 1 → ringGEK k := MvPolynomial.X

/-- `K`, the Koszul object on `x` in `D(A)`. -/
abbrev koszulGEK : DerivedCategory (ModuleCat.{u} (ringGEK k)) :=
  DerivedCategory.Q.obj (Koszul.seqCochainComplex (seqGEK k))

/-- `A/(x)`, which `K` is quasi-isomorphic to. -/
abbrev quotGEK : ModuleCat.{u} (ringGEK k) :=
  ModuleCat.of _ (ringGEK k ⧸ Ideal.span (Set.range (seqGEK k)))

/-- `E = 𝒪_X`, that is `A` in degree `0`. -/
abbrev objEGEK : DerivedCategory (ModuleCat.{u} (ringGEK k)) :=
  (DerivedCategory.singleFunctor (ModuleCat.{u} (ringGEK k)) 0).obj
    (ModuleCat.of (ringGEK k) (ringGEK k))

/-- The Koszul object `K` on `x` is isomorphic in `D(A)` to `A/(x)` placed in degree `0`. -/
theorem koszulGEK_iso : Nonempty (koszulGEK k ≅
    (DerivedCategory.singleFunctor (ModuleCat.{u} (ringGEK k)) 0).obj (quotGEK k)) :=
  Koszul.nonempty_Q_obj_seqCochainComplex_iso_single _ (MvPolynomial.isKoszulRegular_X 0)

/-- The variable `x` lies in the ideal `(x)` of `k[x]`. -/
theorem X_mem_spanGEK :
    (MvPolynomial.X 0 : ringGEK k) ∈ Ideal.span (Set.range (seqGEK k)) :=
  Ideal.subset_span ⟨0, rfl⟩

/-- Every `A`-linear map `A/(x) ⟶ A` is zero, for `A = k[x]`. -/
theorem subsingleton_quotGEK_hom :
    Subsingleton (quotGEK k ⟶ ModuleCat.of (ringGEK k) (ringGEK k)) :=
  subsingleton_hom_quotient_self _ (MvPolynomial.X_ne_zero 0) (X_mem_spanGEK k)

/-- **Condition (2) of [Stacks, Tag 0GEK] holds at `a = 0`** for `E = 𝒪_X`: every morphism
`K⟦-n⟧ ⟶ 𝒪_X` vanishes for `n ≤ 0`.

At `n = 0` this is `Hom_A(A/x, A) = 0`, which holds because `A` is a domain; for `n < 0` the source
is concentrated in degree `n < 0` and the target in degree `0`, so the t-structure admits no
nonzero morphism. -/
theorem hom_koszulGEK_subsingleton (n : ℤ) (hn : n ≤ 0) :
    Subsingleton ((koszulGEK k)⟦-n⟧ ⟶ objEGEK k) := by
  obtain ⟨e⟩ := koszulGEK_iso k
  refine subsingleton_hom_of_iso_left ((shiftFunctor _ (-n)).mapIso e) ?_
  rcases eq_or_lt_of_le hn with heq | hlt
  · exact subsingleton_hom_of_iso_left
      ((shiftFunctorZero' (DerivedCategory (ModuleCat.{u} (ringGEK k))) (-n) (by omega)).app _)
      (subsingleton_hom_single _ _ (subsingleton_quotGEK_hom k))
  · have hLE : DerivedCategory.TStructure.t.IsLE
        (((DerivedCategory.singleFunctor (ModuleCat.{u} (ringGEK k)) 0).obj
          (quotGEK k))⟦-n⟧) n :=
      DerivedCategory.TStructure.t.isLE_shift _ 0 (-n) n (by omega)
    exact ⟨fun u v => by
      rw [DerivedCategory.TStructure.t.zero_of_isLE_of_isGE u n 0 (by omega) hLE inferInstance,
        DerivedCategory.TStructure.t.zero_of_isLE_of_isGE v n 0 (by omega) hLE inferInstance]⟩

/-- `A[1/x]`, which is `Γ(U, 𝒪_U)` for `U = D(x)`, so that `Rj_*(𝒪_U)` is this module in
degree `0`. -/
abbrev awayGEK : Type u := Localization.Away (MvPolynomial.X 0 : ringGEK k)

/-- the unit `𝒪_X ⟶ Rj_*(𝒪_U)` as a map of `A`-modules: the localisation map `A ⟶ A[1/x]`. -/
abbrev unitHomGEK : ModuleCat.of (ringGEK k) (ringGEK k) ⟶ ModuleCat.of _ (awayGEK k) :=
  ModuleCat.ofHom (Algebra.linearMap (ringGEK k) (awayGEK k))

/-- The variable `x` is not a unit of `k[x]`. -/
theorem not_isUnit_X_GEK : ¬ IsUnit (MvPolynomial.X 0 : ringGEK k) := fun h => by
  simpa using h.map (MvPolynomial.eval (fun _ => (0 : k)))

/-- The localisation map `A ⟶ A[1/x]` is not surjective: it would make `x` a unit of `A`. -/
theorem not_surjective_algebraMapGEK :
    ¬ Function.Surjective (algebraMap (ringGEK k) (awayGEK k)) := by
  intro hsurj
  obtain ⟨a, ha⟩ := hsurj (IsLocalization.mk' (awayGEK k) (1 : ringGEK k)
    (⟨MvPolynomial.X 0, Submonoid.mem_powers _⟩ :
      Submonoid.powers (MvPolynomial.X 0 : ringGEK k)))
  have h1 : algebraMap (ringGEK k) (awayGEK k) (a * MvPolynomial.X 0)
      = algebraMap (ringGEK k) (awayGEK k) 1 := by
    rw [map_mul, ha]
    exact IsLocalization.mk'_spec _ _ _
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists
    (Submonoid.powers (MvPolynomial.X 0 : ringGEK k)) (awayGEK k)).mp h1
  obtain ⟨m, hm⟩ := c.2
  have hcne : (c : ringGEK k) ≠ 0 := hm ▸ pow_ne_zero _ (MvPolynomial.X_ne_zero 0)
  have hax : a * MvPolynomial.X 0 = 1 := mul_left_cancel₀ hcne (by simpa using hc)
  exact not_isUnit_X_GEK k ⟨⟨MvPolynomial.X 0, a, (mul_comm _ _).trans hax, hax⟩, rfl⟩

/-- **Condition (1) of [Stacks, Tag 0GEK] fails at `a = 0`** for `E = 𝒪_X`: the canonical map
`τ_{≤0}𝒪_X ⟶ τ_{≤0}Rj_*(𝒪_U)` is not an isomorphism.

Both objects are concentrated in degree `0`, so invertibility of `τ_{≤0}` of the unit would make
the unit itself invertible, hence — the single functor being fully faithful — would make the
localisation map `A ⟶ A[1/x]` bijective. -/
theorem not_isIso_truncLE_unitGEK :
    ¬ IsIso ((DerivedCategory.TStructure.t.truncLE (0 : ℤ)).map
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (ringGEK k)) 0).map (unitHomGEK k))) := by
  intro h
  have h1 : IsIso ((DerivedCategory.singleFunctor (ModuleCat.{u} (ringGEK k)) 0).map
      (unitHomGEK k)) := isIso_of_isIso_truncLE_map _ 0 h
  have h2 : IsIso (unitHomGEK k) :=
    isIso_of_fully_faithful (DerivedCategory.singleFunctor (ModuleCat.{u} (ringGEK k)) 0) _
  exact not_surjective_algebraMapGEK k (ConcreteCategory.bijective_of_isIso (unitHomGEK k)).2

/-- `E = 𝒪_X` is not the zero object, so the counterexample is not degenerate. -/
theorem not_isZero_objEGEK : ¬ IsZero (objEGEK k) := by
  intro h
  have h0 : (𝟙 (ModuleCat.of (ringGEK k) (ringGEK k))) = 0 := by
    refine (DerivedCategory.singleFunctor (ModuleCat.{u} (ringGEK k)) 0).map_injective ?_
    rw [(DerivedCategory.singleFunctor (ModuleCat.{u} (ringGEK k)) 0).map_zero,
      (DerivedCategory.singleFunctor (ModuleCat.{u} (ringGEK k)) 0).map_id]
    exact h.eq_of_src _ _
  exact one_ne_zero (congrArg (fun u : ModuleCat.of (ringGEK k) (ringGEK k) ⟶
    ModuleCat.of (ringGEK k) (ringGEK k) => u.hom (1 : ringGEK k)) h0)

/-- **[Stacks, Tag 0GEK]'s published "(2) implies (1)" fails at `A = k[x]`, `f = (x)`,
`E = 𝒪_X`, `a = 0`.** Condition (2) holds at `a = 0` and condition (1) fails at `a = 0`.

Deliberately untagged: this refutes the published summary and is not a clause of the tag. -/
theorem erratum_0GEK :
    (∀ n : ℤ, n ≤ 0 → Subsingleton ((koszulGEK k)⟦-n⟧ ⟶ objEGEK k)) ∧
      ¬ IsIso ((DerivedCategory.TStructure.t.truncLE (0 : ℤ)).map
        ((DerivedCategory.singleFunctor (ModuleCat.{u} (ringGEK k)) 0).map (unitHomGEK k))) :=
  ⟨hom_koszulGEK_subsingleton k, not_isIso_truncLE_unitGEK k⟩

end GEK

/-! ### [Stacks, Tag 0GEJ]: `A = k[x,y]`, `f = (x,y)`, `E = k`, `a = 1` -/

section GEJ

variable (k : Type u) [Field k]

/-- `A = k[x, y]`, the polynomial ring in two variables. -/
abbrev ringGEJ : Type u := MvPolynomial (Fin 2) k

/-- the ideal `(x)`. -/
abbrev idealX : Ideal (ringGEJ k) := Ideal.span (MvPolynomial.X '' ({0} : Set (Fin 2)))

/-- the ideal `(x, y)` generated by the sequence `f`. -/
abbrev idealXY : Ideal (ringGEJ k) :=
  Ideal.span (Set.range (MvPolynomial.X : Fin 2 → ringGEJ k))

/-- The ideal `(x)` of `k[x, y]` is the span of the singleton `{x}`. -/
theorem idealX_eq_span_singleton :
    idealX k = Ideal.span {(MvPolynomial.X 0 : ringGEJ k)} :=
  congrArg Ideal.span Set.image_singleton

/-- The ideal `(x)` is contained in the ideal `(x, y)`. -/
theorem idealX_le_idealXY : idealX k ≤ idealXY k :=
  Ideal.span_mono (by rintro _ ⟨i, -, rfl⟩; exact ⟨i, rfl⟩)

/-- The ideal `(x)` is contained in the preimage of `(x, y)` under the identity map. -/
theorem idealX_le_comap : idealX k ≤ Submodule.comap LinearMap.id (idealXY k) := by
  simpa using idealX_le_idealXY k

/-- The variable `x` lies in the ideal `(x)`. -/
theorem X0_mem_idealX : (MvPolynomial.X 0 : ringGEJ k) ∈ idealX k :=
  Ideal.subset_span ⟨0, rfl, rfl⟩

/-- Each variable of `k[x, y]` lies in the ideal `(x, y)`. -/
theorem X_mem_idealXY (i : Fin 2) : (MvPolynomial.X i : ringGEJ k) ∈ idealXY k :=
  Ideal.subset_span ⟨i, rfl⟩

/-- The ideal `(x, y)` of `k[x, y]` is proper: it does not contain `1`. -/
theorem one_notMem_idealXY : (1 : ringGEJ k) ∉ idealXY k := by
  intro hmem
  exact MvPolynomial.one_notMem_span_X_image (R := k) (s := (Set.univ : Set (Fin 2)))
    (by rwa [Set.image_univ])

/-- `A/(x)`. -/
abbrev modX : ModuleCat.{u} (ringGEJ k) := ModuleCat.of _ (ringGEJ k ⧸ idealX k)

/-- `A/(x, y)`, which is `k`: the object `E` of the counterexample. -/
abbrev modXY : ModuleCat.{u} (ringGEJ k) := ModuleCat.of _ (ringGEJ k ⧸ idealXY k)

/-- `A`, which is `𝒪_X`. -/
abbrev modA : ModuleCat.{u} (ringGEJ k) := ModuleCat.of (ringGEJ k) (ringGEJ k)

/-- the quotient map `A/(x) ⟶ A/(x, y)`. -/
abbrev mapXY : modX k ⟶ modXY k :=
  ModuleCat.ofHom (Submodule.mapQ (idealX k) (idealXY k) LinearMap.id (idealX_le_comap k))

/-- the short exact sequence `0 ⟶ A --x--> A ⟶ A/(x) ⟶ 0`. -/
abbrev sesX : ShortComplex (ModuleCat.{u} (ringGEJ k)) :=
  ShortComplex.mk ((MvPolynomial.X 0 : ringGEJ k) • 𝟙 (modA k))
    (ModuleCat.ofHom (idealX k).mkQ) (by
      rw [Linear.smul_comp, Category.id_comp]
      apply ModuleCat.hom_ext
      refine LinearMap.ext fun a => ?_
      change (MvPolynomial.X 0 : ringGEJ k) • ((idealX k).mkQ a) = 0
      exact smul_eq_zero_of_mem (X0_mem_idealX k) _)

/-- The sequence `0 ⟶ A --x--> A ⟶ A/(x) ⟶ 0` is short exact. -/
theorem sesX_shortExact : (sesX k).ShortExact where
  exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro a ha
    have ha' : a ∈ idealX k := (Submodule.Quotient.mk_eq_zero _).1 ha
    rw [idealX_eq_span_singleton, Ideal.mem_span_singleton] at ha'
    obtain ⟨b, rfl⟩ := ha'
    exact ⟨b, rfl⟩
  mono_f := by
    rw [ModuleCat.mono_iff_injective]
    intro a b hab
    exact mul_left_cancel₀ (MvPolynomial.X_ne_zero 0) hab
  epi_g := by
    rw [ModuleCat.epi_iff_surjective]
    intro q
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective (idealX k) q
    exact ⟨a, rfl⟩

/-- the short exact sequence `0 ⟶ A/(x) --y--> A/(x) ⟶ A/(x, y) ⟶ 0`. Injectivity of `y` is the
regularity of the variables, `MvPolynomial.mem_span_X_image_of_X_mul_mem`. -/
abbrev sesY : ShortComplex (ModuleCat.{u} (ringGEJ k)) :=
  ShortComplex.mk ((MvPolynomial.X 1 : ringGEJ k) • 𝟙 (modX k)) (mapXY k) (by
      rw [Linear.smul_comp, Category.id_comp]
      apply ModuleCat.hom_ext
      refine LinearMap.ext fun q => ?_
      change (MvPolynomial.X 1 : ringGEJ k) •
        (Submodule.mapQ (idealX k) (idealXY k) LinearMap.id (idealX_le_comap k) q) = 0
      exact smul_eq_zero_of_mem (X_mem_idealXY k 1) _)

/-- The sequence `0 ⟶ A/(x) --y--> A/(x) ⟶ A/(x, y) ⟶ 0` is short exact. -/
theorem sesY_shortExact : (sesY k).ShortExact where
  exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro q hq
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective (idealX k) q
    have ha : a ∈ idealXY k := (Submodule.Quotient.mk_eq_zero _).1 hq
    obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun (R := ringGEJ k)).mp ha
    have hsum : c 0 * MvPolynomial.X 0 + c 1 * MvPolynomial.X 1 = a := by
      simpa [Fin.sum_univ_two, smul_eq_mul] using hc
    refine ⟨Submodule.Quotient.mk (c 1), ?_⟩
    change (MvPolynomial.X 1 : ringGEJ k) • (Submodule.Quotient.mk (c 1) : ringGEJ k ⧸ idealX k)
      = Submodule.Quotient.mk a
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, idealX_eq_span_singleton]
    refine Ideal.mem_span_singleton.2 ⟨-c 0, ?_⟩
    rw [← hsum, smul_eq_mul]
    ring
  mono_f := by
    rw [ModuleCat.mono_iff_injective]
    intro q₁ q₂ h
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective (idealX k) q₁
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective (idealX k) q₂
    have hsm : (MvPolynomial.X 1 : ringGEJ k) •
        (Submodule.Quotient.mk a : ringGEJ k ⧸ idealX k)
        = (MvPolynomial.X 1 : ringGEJ k) • (Submodule.Quotient.mk b : ringGEJ k ⧸ idealX k) := h
    have h' : (MvPolynomial.X 1 : ringGEJ k) * (a - b) ∈ idealX k := by
      rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
        Submodule.Quotient.eq] at hsm
      have hd : (MvPolynomial.X 1 : ringGEJ k) • a - (MvPolynomial.X 1 : ringGEJ k) • b
          ∈ idealX k := hsm
      rw [mul_sub]
      simpa [smul_eq_mul] using hd
    rw [Submodule.Quotient.eq]
    exact MvPolynomial.mem_span_X_image_of_X_mul_mem (R := k)
      (s := ({0} : Set (Fin 2))) (i := 1) (by simp) h'
  epi_g := by
    rw [ModuleCat.epi_iff_surjective]
    intro q
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective (idealXY k) q
    exact ⟨Submodule.Quotient.mk a, rfl⟩

/-- the single-object embedding `ModuleCat A ⥤ D(A)` for `A = k[x, y]`. -/
abbrev SgJ : ModuleCat.{u} (ringGEJ k) ⥤ DerivedCategory (ModuleCat.{u} (ringGEJ k)) :=
  DerivedCategory.singleFunctor (ModuleCat.{u} (ringGEJ k)) 0

/-- `E = A/(x, y) = k`, placed in degree `0`. -/
abbrev objE : DerivedCategory (ModuleCat.{u} (ringGEJ k)) := (SgJ k).obj (modXY k)

/-- Every element of `(x, y)` acts as zero on `E = A/(x, y)`. -/
theorem smul_id_objE {c : ringGEJ k} (hc : c ∈ idealXY k) : c • 𝟙 (objE k) = 0 := by
  rw [← (SgJ k).map_id (modXY k), ← (SgJ k).map_smul, smul_id_quotient_eq_zero hc,
    (SgJ k).map_zero]

/-- The quotient map `A ⟶ A/(x, y)` is nonzero. -/
theorem mkQ_ne_zero : (ModuleCat.ofHom (idealXY k).mkQ : modA k ⟶ modXY k) ≠ 0 := by
  intro h
  refine one_notMem_idealXY k ((Submodule.Quotient.mk_eq_zero (idealXY k)).1 ?_)
  exact congrArg (fun u : modA k ⟶ modXY k => u.hom (1 : ringGEJ k)) h

/-- the distinguished triangle of `0 ⟶ A --x--> A ⟶ A/(x) ⟶ 0`. -/
abbrev triX : Triangle (DerivedCategory (ModuleCat.{u} (ringGEJ k))) :=
  (sesX_shortExact k).singleTriangle

/-- the distinguished triangle of `0 ⟶ A/(x) --y--> A/(x) ⟶ A/(x, y) ⟶ 0`. -/
abbrev triY : Triangle (DerivedCategory (ModuleCat.{u} (ringGEJ k))) :=
  (sesY_shortExact k).singleTriangle

/-- The first morphism of the triangle `triX` is multiplication by `x` on `A`. -/
theorem triX_mor₁ : (triX k).mor₁
    = (MvPolynomial.X 0 : ringGEJ k) • 𝟙 ((SgJ k).obj (modA k)) := by
  change (SgJ k).map ((MvPolynomial.X 0 : ringGEJ k) • 𝟙 (modA k)) = _
  rw [(SgJ k).map_smul, (SgJ k).map_id]

/-- The first morphism of the triangle `triY` is multiplication by `y` on `A/(x)`. -/
theorem triY_mor₁ : (triY k).mor₁
    = (MvPolynomial.X 1 : ringGEJ k) • 𝟙 ((SgJ k).obj (modX k)) := by
  change (SgJ k).map ((MvPolynomial.X 1 : ringGEJ k) • 𝟙 (modX k)) = _
  rw [(SgJ k).map_smul, (SgJ k).map_id]

/-- **`Ext²_{k[x,y]}(k, k) ≠ 0`.** The quotient map `A ⟶ A/(x, y)` is nonzero; both variables
annihilate `A/(x, y)`, so precomposition with the connecting morphism of each of the two
triangles is injective, and the two connecting morphisms carry the quotient map to a nonzero
morphism `E ⟶ E⟦1⟧⟦1⟧`. -/
theorem not_subsingleton_ext_two :
    ¬ Subsingleton (objE k ⟶ ((objE k)⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧) := by
  intro hsub
  have hφ : (SgJ k).map (ModuleCat.ofHom (idealXY k).mkQ) ≠ 0 :=
    (Functor.map_eq_zero_iff _).not.2 (mkQ_ne_zero k)
  have hψ₁ : (triX k).mor₃ ≫
      (shiftFunctor (DerivedCategory (ModuleCat.{u} (ringGEJ k))) (1 : ℤ)).map
        ((SgJ k).map (ModuleCat.ofHom (idealXY k).mkQ)) ≠ 0 := fun h =>
    (Functor.map_eq_zero_iff _).not.2 hφ (eq_zero_of_mor₃_comp_eq_zero
      (sesX_shortExact k).singleTriangle_distinguished
      (fun g => by
        rw [triX_mor₁]
        exact shift_map_smul_id_comp_eq_zero _ (smul_id_shift_eq_zero _
          (smul_id_objE k (X_mem_idealXY k 0)) 1) g) _ h)
  refine (Functor.map_eq_zero_iff _).not.2 hψ₁ (eq_zero_of_mor₃_comp_eq_zero
    (sesY_shortExact k).singleTriangle_distinguished (fun g => ?_) _ (hsub.allEq _ 0))
  rw [triY_mor₁]
  exact shift_map_smul_id_comp_eq_zero _
    (smul_id_shift_eq_zero _ (smul_id_shift_eq_zero _ (smul_id_objE k (X_mem_idealXY k 1)) 1) 1) g

/-- `K`, the Koszul object on `x, y` in `D(A)`. -/
abbrev koszulGEJ : DerivedCategory (ModuleCat.{u} (ringGEJ k)) :=
  DerivedCategory.Q.obj (Koszul.seqCochainComplex (MvPolynomial.X : Fin 2 → ringGEJ k))

/-- The Koszul object `K` on `x, y` is isomorphic in `D(A)` to `E = A/(x, y)` in degree `0`. -/
theorem koszulGEJ_iso : Nonempty (koszulGEJ k ≅ objE k) :=
  Koszul.nonempty_Q_obj_seqCochainComplex_iso_single _ (MvPolynomial.isKoszulRegular_X 1)

/-- **Condition (2) of [Stacks, Tag 0GEJ] fails at `a + 1 = 2`** for `E = k`: there is a nonzero
morphism `K⟦-2⟧ ⟶ E`.

`K` is quasi-isomorphic to `E` because `x, y` is Koszul-regular, so the group in question is
`Ext²_A(k, k)`, which `Stacks.Koszul.Errata.not_subsingleton_ext_two` shows is nonzero. -/
theorem not_subsingleton_hom_koszulGEJ :
    ¬ Subsingleton ((koszulGEJ k)⟦(-2 : ℤ)⟧ ⟶ objE k) := by
  obtain ⟨e⟩ := koszulGEJ_iso k
  intro hsub
  refine not_subsingleton_ext_two k (subsingleton_hom_of_iso_right
    ((shiftFunctorAdd' (DerivedCategory (ModuleCat.{u} (ringGEJ k))) 1 1 2
      (by omega)).app (objE k)).symm (subsingleton_hom_shift_target 2 ?_))
  exact subsingleton_hom_of_iso_left
    ((shiftFunctor (DerivedCategory (ModuleCat.{u} (ringGEJ k))) (-2 : ℤ)).mapIso e.symm) hsub

/-- **Condition (1) of [Stacks, Tag 0GEJ] holds at `a = 1`** for `E = k`: `τ_{≥1}E = 0`, and
`Rj_*(E|_U) = 0` because `E` restricts to zero on `U`, so the canonical map
`τ_{≥1}E ⟶ τ_{≥1}Rj_*(E|_U)` is an isomorphism of zero objects. -/
theorem isZero_truncGE_objE :
    IsZero ((DerivedCategory.TStructure.t.truncGE (1 : ℤ)).obj (objE k)) :=
  DerivedCategory.TStructure.t.isZero_truncGE_obj_of_isLE 0 1 rfl (objE k)

/-- **`E` restricts to zero on `U`.** `U` is the union of the principal opens `D(f_i)`, and the
localisation of `E = A/(x, y)` at each `f_i = X i` vanishes because `X i` annihilates `E`. Hence
`E|_U = 0` and `Rj_*(E|_U) = 0`. -/
theorem restrictsToZero_modXY (i : Fin 2) :
    Subsingleton (LocalizedModule (Submonoid.powers (MvPolynomial.X i : ringGEJ k))
      (ringGEJ k ⧸ idealXY k)) := by
  rw [LocalizedModule.subsingleton_iff]
  exact fun m => ⟨MvPolynomial.X i, Submonoid.mem_powers _,
    smul_eq_zero_of_mem (X_mem_idealXY k i) m⟩

/-- `E = k` is not the zero object, so the counterexample is not degenerate. -/
theorem not_isZero_objE : ¬ IsZero (objE k) := by
  intro h
  refine mkQ_ne_zero k ((SgJ k).map_injective ?_)
  rw [(SgJ k).map_zero]
  exact h.eq_of_tgt _ _

/-- **[Stacks, Tag 0GEJ]'s published "(1) implies (2) with `a` replaced by `a + 1`" fails at
`A = k[x,y]`, `f = (x,y)`, `E = k`, `a = 1`.** The three conjuncts are: `E` restricts to zero on
`U`, so `Rj_*(E|_U) = 0`; `τ_{≥1}E = 0`, so condition (1) holds at `a = 1`; and there is a nonzero
morphism `K⟦-2⟧ ⟶ E`, so condition (2) fails at `a + 1 = 2`.

Deliberately untagged: this refutes the published summary and is not a clause of the tag. -/
theorem erratum_0GEJ :
    (∀ i : Fin 2, Subsingleton (LocalizedModule
        (Submonoid.powers (MvPolynomial.X i : ringGEJ k)) (ringGEJ k ⧸ idealXY k))) ∧
      IsZero ((DerivedCategory.TStructure.t.truncGE (1 : ℤ)).obj (objE k)) ∧
      ¬ Subsingleton ((koszulGEJ k)⟦(-2 : ℤ)⟧ ⟶ objE k) :=
  ⟨restrictsToZero_modXY k, isZero_truncGE_objE k, not_subsingleton_hom_koszulGEJ k⟩

end GEJ

end Stacks.Koszul.Errata

end
