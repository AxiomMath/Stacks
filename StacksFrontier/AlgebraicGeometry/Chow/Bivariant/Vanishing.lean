module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.EnvelopeDescent
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.Coproduct
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.GenericFibre
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardRationalEquivalence.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# When a bivariant class is zero

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `f : X ⟶ Y` be a
morphism of schemes locally of finite type over `S` and let `c ∈ A^p(X ⟶ Y)`. **Stacks 02UC**
says that the following are equivalent: `c` is zero; `c ∩ [Y'] = 0` for every integral scheme
`Y'` locally of finite type over `Y`; and for every such `Y'` there is a proper birational
`Y'' ⟶ Y'` with `c ∩ [Y''] = 0`.

## Main definitions

* `Stacks.Chow.fundamentalCycle`, `Stacks.Chow.fundamentalChowClass` — the fundamental cycle
  `[T]_k` of a scheme locally of finite type over the base, and its class in `A_k(T)`.
* `Stacks.Chow.BivariantClass.CapsIntegralFundamentalClassesToZero` — clause (2).
* `Stacks.Chow.BivariantClass.HasBirationalModificationCappingToZero` — clause (3).

## Main results

* `Stacks.Chow.BivariantClass.cap_cycleAssociatedToClosedSubscheme_eq_zero` — the content of
  (2) `⇒` (1): a class satisfying (2) kills the cycle of every integral closed subscheme of
  every test scheme.
* `Stacks.Chow.BivariantClass.cap_mk_eq_zero_of_finite_support` — such a class kills the class of
  every *finitely supported* cycle.
* `Stacks.Chow.BivariantClass.cap_eq_zero_of_clopen_cover` — a cap product vanishes as soon as it
  vanishes on every piece of a decomposition of the test scheme into open and closed subschemes.
* `Stacks.Chow.BivariantClass.cap_mk_eq_zero_of_integralPresentation` — (2) `⇒` (1) for the class
  of an arbitrary, locally finite cycle, by passing to the coproduct of the integral closed
  subschemes carrying it.
* `Stacks.Chow.BivariantClass.eq_zero_iff_capsIntegralFundamentalClassesToZero` — (1) `⇔` (2).
* `Stacks.Chow.BivariantClass.eq_zero_tfae` — all three clauses.

## Implementation notes

A cycle on a test scheme is a *locally finite* formal sum of integral closed subschemes, so
(2) `⇒` (1) cannot be reduced to the finitely supported case: a Chow class on a test scheme which
is not quasi-compact need not be the class of a finitely supported cycle. The proof follows the
source and passes to the coproduct `W = ∐ Y'ᵢ` of the integral closed subschemes carrying the
cycle, which is proper over the test scheme and decomposed by its summands into open and closed
subschemes; the substrate for this is
`StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.Coproduct`.

Everything here is read against an arbitrary `Stacks.Chow.GysinSystem`, the parameter
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Basic` states Stacks 0B76 against. The
instantiation at the Gysin system that is *constructed*, which is the group `A^p(X ⟶ Y)` of the
source with no datum handed in, is
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.VanishingUnconditional`; the descent hypotheses
that the proper and flat axioms of `Stacks.Chow.BivariantClass` quantify over are discharged
there too. Nothing in the proofs below assumes either: Stacks 02S2 is supplied by
`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isProper` and Stacks 02S1,
along the open immersions of a clopen decomposition, by
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_of_isOpenImmersion`.

## References

* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The fundamental class of a test scheme -/

/-- The fundamental cycle `[T]_k` of a scheme locally of finite type over the base: the cycle of
Stacks 02QU associated to `T` as a closed subscheme of itself. It is zero unless `k` is the
delta-dimension of a component of `T`. -/
def fundamentalCycle (C : ChowSituation.{u}) {T : Scheme.{u}} (sT : T ⟶ C.S)
    [LocallyOfFiniteType sT] (k : ℤ) : CycleGroup C sT k :=
  cycleAssociatedToClosedSubscheme C sT (𝟙 T) k

/-- The fundamental class `[T]` of a scheme locally of finite type over the base, in `A_k(T)`. -/
def fundamentalChowClass (C : ChowSituation.{u}) {T : Scheme.{u}} (sT : T ⟶ C.S)
    [LocallyOfFiniteType sT] (k : ℤ) : chowGroup C sT k :=
  QuotientAddGroup.mk' (rationalEquivalences C sT k) (fundamentalCycle C sT k)

/-- The class of an integer multiple of a fundamental cycle is that multiple of the fundamental
class. -/
theorem mk_zsmul_fundamentalCycle (C : ChowSituation.{u}) {T : Scheme.{u}} (sT : T ⟶ C.S)
    [LocallyOfFiniteType sT] (k : ℤ) (n : ℤ) :
    QuotientAddGroup.mk' (rationalEquivalences C sT k) (n • fundamentalCycle C sT k) =
      n • fundamentalChowClass C sT k :=
  map_zsmul _ _ _

/-- A Chow class heterogeneously equal to the zero class of another degree is zero. The two
degrees of the flat-pullback law of Stacks 0B76, `(k + r) - p` and `(k - p) + r`, are the same
integer written two ways, which is why that law is a heterogeneous equality. -/
public theorem chowGroup_eq_zero_of_heq_zero (C : ChowSituation.{u}) {T : Scheme.{u}}
    {q : T ⟶ C.S} [LocallyOfFiniteType q] {i j : ℤ} (hij : i = j) {x : chowGroup C q i}
    (h : x ≍ (0 : chowGroup C q j)) : x = 0 := by
  subst hij
  exact eq_of_heq h

/-- Proper pushforward along a closed immersion carries the fundamental cycle of the subscheme to
the cycle of the subscheme. This is the case `i = 𝟙` of
`Stacks.Chow.properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp`. -/
theorem properPushforward_fundamentalCycle_of_isClosedImmersion (C : ChowSituation.{u})
    {T Z : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (sT : T ⟶ C.S)
    [LocallyOfFiniteType sT] (ι : Z ⟶ T) [IsClosedImmersion ι] (hι : ι ≫ sT = sZ) (k : ℤ) :
    properPushforward C sZ sT ι hι k (fundamentalCycle C sZ k) =
      cycleAssociatedToClosedSubscheme C sT ι k := by
  rw [fundamentalCycle,
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp C sZ sT ι hι
      (𝟙 Z) k]
  exact cycleAssociatedToClosedSubscheme_congr C sT (𝟙 Z ≫ ι) ι (Category.id_comp ι) k

/-- The identity morphism is birational: it is the identity on generic points and on every
local ring. -/
theorem isBirational_id (T : Scheme.{u}) : AlgebraicGeometry.IsBirational (𝟙 T) := by
  refine ⟨?_, fun x _ ↦ ?_⟩
  · simpa using Set.bijOn_id (genericPoints T)
  · simp only [Scheme.Hom.stalkMap]
    infer_instance

/-! ### Pushing forward a fundamental cycle along a proper birational morphism -/

/-- A morphism whose stalk map at a point is surjective induces an isomorphism of residue fields
there: the induced map is surjective, and injective because its source is a field. -/
theorem bijective_residueFieldMap_of_surjective_stalkMap {X Y : Scheme.{u}} (h : X ⟶ Y) (x : X)
    (hsurj : Function.Surjective (h.stalkMap x).hom) :
    Function.Bijective (h.residueFieldMap x).hom := by
  refine ⟨(h.residueFieldMap x).hom.injective, ?_⟩
  have hc : Function.Surjective ((h.residueFieldMap x).hom ∘ (Y.residue (h.base x)).hom) := by
    rw [← RingHom.coe_comp, ← CommRingCat.hom_comp, Scheme.residue_residueFieldMap,
      CommRingCat.hom_comp, RingHom.coe_comp]
    exact (X.residue_surjective x).comp hsurj
  exact Function.Surjective.of_comp hc

/-- A morphism inducing an isomorphism of residue fields at a point has residue degree one
there. -/
theorem residueDegree_eq_one_of_bijective_residueFieldMap {X Y : Scheme.{u}} (h : X ⟶ Y) (x : X)
    (hx : Function.Bijective (h.residueFieldMap x).hom) : h.residueDegree x = 1 := by
  let _ := (h.residueFieldMap x).hom.toAlgebra
  show Module.finrank (Y.residueField (h.base x)) (X.residueField x) = 1
  exact Module.finrank_of_bijective_algebraMap hx

/-- A closed subscheme has multiplicity one at a component whose local ring is a field: the local
ring is then a simple module over itself, so it has length one. -/
theorem componentMultiplicity_eq_one_of_isField {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (ξ : genericPoints Z) (hfield : IsField (Z.presheaf.stalk ξ.1)) :
    componentMultiplicity i ξ = 1 := by
  rw [componentMultiplicity_eq_length_stalk i ξ]
  let _ : Field (Z.presheaf.stalk ξ.1) := hfield.toField
  rw [Module.length_eq_one_iff.2 (inferInstance : IsSimpleModule _ _)]
  rfl

/-- On a scheme with a single generic point `η`, of relative dimension `k` over the base and with
field local ring, the fundamental cycle in degree `k` is the prime cycle at `η`. -/
theorem fundamentalCycle_eq_single (C : ChowSituation.{u}) {T : Scheme.{u}} (sT : T ⟶ C.S)
    [LocallyOfFiniteType sT] {k : ℤ} {η : T} (hsingle : genericPoints T = {η})
    (hdim : relativeDimension C.dimensionFunction sT η = k)
    (hfield : IsField (T.presheaf.stalk η)) :
    (fundamentalCycle C sT k).1 =
      @Function.locallyFinsuppWithin.single T _ ℤ (Classical.decEq T) _ η (1 : ℤ) := by
  classical
  have hmem : η ∈ genericPoints T := by rw [hsingle]; rfl
  have hgen : ∀ ξ : genericPoints T, (ξ : T) = η := fun ξ ↦
    (Set.eq_singleton_iff_unique_mem.mp hsingle).2 _ ξ.2
  refine Function.locallyFinsuppWithin.ext fun y ↦ ?_
  rw [Function.locallyFinsuppWithin.single_apply, fundamentalCycle]
  by_cases hy : y = η
  · subst hy
    have h1 : (cycleAssociatedToClosedSubscheme C sT (𝟙 T) k).1 y = 1 := by
      have h2 := cycleAssociatedToClosedSubscheme_apply C sT (𝟙 T) k ⟨y, hmem⟩ hdim
      rwa [componentMultiplicity_eq_one_of_isField (𝟙 T) ⟨y, hmem⟩ hfield] at h2
    simp [h1]
  · have h0 : (cycleAssociatedToClosedSubscheme C sT (𝟙 T) k).1 y = 0 := by
      refine cycleAssociatedToClosedSubscheme_apply_eq_zero C sT (𝟙 T) k y ?_
      rintro ⟨ξ, hξ, -⟩
      exact hy (hξ.symm.trans (hgen ξ))
    simp [h0, hy]

/-- On a scheme with a single generic point `η`, the fundamental cycle vanishes in every degree
other than the relative dimension of `η`. -/
theorem fundamentalCycle_eq_zero_of_ne (C : ChowSituation.{u}) {T : Scheme.{u}} (sT : T ⟶ C.S)
    [LocallyOfFiniteType sT] {k : ℤ} {η : T} (hsingle : genericPoints T = {η})
    (hdim : relativeDimension C.dimensionFunction sT η ≠ k) : fundamentalCycle C sT k = 0 := by
  have hgen : ∀ ξ : genericPoints T, (ξ : T) = η := fun ξ ↦
    (Set.eq_singleton_iff_unique_mem.mp hsingle).2 _ ξ.2
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
  show (cycleAssociatedToClosedSubscheme C sT (𝟙 T) k).1 y = 0
  refine cycleAssociatedToClosedSubscheme_apply_eq_zero C sT (𝟙 T) k y ?_
  rintro ⟨ξ, hξ, hd⟩
  exact hdim ((hξ.symm.trans (hgen ξ) : y = η) ▸ hd)

/-- Proper pushforward along a proper birational morphism onto an integral scheme carries the
fundamental cycle to the fundamental cycle. The source has a single generic point, lying over the
generic point of the target and with the same local ring, so both the multiplicity of that
component and the residue degree of the morphism there are one. -/
@[sga "7 XVII 5.2" "special case"]
theorem properPushforward_fundamentalCycle_of_isBirational (C : ChowSituation.{u})
    {T T' : Scheme.{u}} (sT' : T' ⟶ C.S) [LocallyOfFiniteType sT'] (sT : T ⟶ C.S)
    [LocallyOfFiniteType sT] [IsIntegral T] (h : T' ⟶ T) [IsProper h] (hcomp : h ≫ sT = sT')
    (hbir : AlgebraicGeometry.IsBirational h) (k : ℤ) :
    properPushforward C sT' sT h hcomp k (fundamentalCycle C sT' k) =
      fundamentalCycle C sT k := by
  classical
  have hsingleT : genericPoints T = {genericPoint T} := genericPoints_eq_singleton
  obtain ⟨η', hη'mem, hη'⟩ : ∃ η' : T', η' ∈ genericPoints T' ∧ h.base η' = genericPoint T :=
    hbir.bijOn.surjOn (genericPoint_mem_genericPoints T)
  have hsingle : genericPoints T' = {η'} := by
    refine Set.eq_singleton_iff_unique_mem.2 ⟨hη'mem, fun ξ hξ ↦ ?_⟩
    refine hbir.bijOn.injOn hξ hη'mem ?_
    have h1 : h.base ξ ∈ genericPoints T := hbir.bijOn.mapsTo hξ
    rw [hsingleT, Set.mem_singleton_iff] at h1
    rw [h1, hη']
  have hiso : IsIso (h.stalkMap η') := hbir.isIso_stalkMap η' hη'mem
  have _ := hiso
  have hbij : Function.Bijective (h.residueFieldMap η').hom :=
    bijective_residueFieldMap_of_surjective_stalkMap h η'
      (ConcreteCategory.bijective_of_isIso _).surjective
  have hfieldT : IsField (T.presheaf.stalk (h.base η')) := by
    rw [hη']
    exact Field.toIsField _
  have hfieldT' : IsField (T'.presheaf.stalk η') :=
    (asIso (h.stalkMap η')).commRingCatIsoToRingEquiv.symm.toMulEquiv.isField hfieldT
  have hdeg : h.residueDegree η' = 1 :=
    residueDegree_eq_one_of_bijective_residueFieldMap h η' hbij
  have hdim : relativeDimension C.dimensionFunction sT' η' =
      relativeDimension C.dimensionFunction sT (genericPoint T) := by
    rw [← hcomp,
      relativeDimension_comp_of_bijective_residueFieldMap C.dimensionFunction h sT η' hbij, hη']
  by_cases hk : relativeDimension C.dimensionFunction sT (genericPoint T) = k
  · apply Subtype.ext
    rw [properPushforward_single C sT' sT h hcomp k η' (fundamentalCycle C sT' k)
        (fundamentalCycle_eq_single C sT' hsingle (hdim.trans hk) hfieldT'),
      fundamentalCycle_eq_single C sT hsingleT hk (Field.toIsField _), hη', hdeg]
    simp [hk]
  · rw [fundamentalCycle_eq_zero_of_ne C sT' hsingle (fun hc ↦ hk (hdim.symm.trans hc)),
      fundamentalCycle_eq_zero_of_ne C sT hsingleT hk, properPushforward_zero]

/-! ### Pushing a cycle forward along a morphism with bijective residue field maps -/

/-- A cycle pushes forward to a given cycle along a proper morphism all of whose residue field
maps are bijective, as soon as the points of the support of the target cycle are the images of
points of the source carrying the same coefficients, and the source cycle is supported on those
points.

Bijectivity of the residue field maps makes every residue degree one and leaves the
delta-dimension of a point unchanged, so each locally finite sum defining a coefficient of the
pushforward collapses to a single term. -/
theorem properPushforward_eq_of_support_section (C : ChowSituation.{u}) {T W : Scheme.{u}}
    (sT : T ⟶ C.S) [LocallyOfFiniteType sT] (sW : W ⟶ C.S) [LocallyOfFiniteType sW]
    (π : W ⟶ T) [IsProper π] (hπ : π ≫ sT = sW) (k : ℤ)
    (hres : ∀ x : W, Function.Bijective ((π.residueFieldMap x).hom))
    (α : CycleGroup C sT k) (γ : CycleGroup C sW k)
    (e : ↥(Function.support (α.1 : T → ℤ)) → W) (he : ∀ i, π.base (e i) = (i : T))
    (hγ : ∀ i, γ.1 (e i) = α.1 (i : T))
    (hγsupport : ∀ x : W, γ.1 x ≠ 0 → ∃ i, x = e i) :
    properPushforward C sW sT π hπ k γ = α := by
  classical
  subst hπ
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
  have hterm : ∀ x : W, γ.1 x *
      (if relativeDimension C.dimensionFunction (π ≫ sT) x =
          relativeDimension C.dimensionFunction sT (π.base x) then (π.residueDegree x : ℤ)
        else 0) = γ.1 x := fun x ↦ by
    rw [relativeDimension_comp_of_bijective_residueFieldMap C.dimensionFunction π sT x (hres x),
      residueDegree_eq_one_of_bijective_residueFieldMap π x (hres x)]
    simp
  rw [properPushforward_apply, finsum_mem_congr rfl (fun x _ ↦ hterm x),
    ← finsum_set_coe_eq_finsum_mem]
  by_cases hy : α.1 y = 0
  · rw [hy]
    refine finsum_eq_zero_of_forall_eq_zero fun z ↦ ?_
    by_contra hz
    obtain ⟨i, hi⟩ := hγsupport z.1 hz
    exact i.2 (((he i).symm.trans (hi ▸ z.2) : (i : T) = y) ▸ hy)
  · refine Eq.trans (finsum_eq_single _ ⟨e ⟨y, hy⟩, he ⟨y, hy⟩⟩ fun z hz ↦ ?_) (hγ ⟨y, hy⟩)
    by_contra hzero
    obtain ⟨i, hi⟩ := hγsupport z.1 hzero
    have hiy : i = ⟨y, hy⟩ := Subtype.ext ((he i).symm.trans (hi ▸ z.2))
    exact hz (Subtype.ext (hi.trans (congrArg e hiy)))

/-! ### Finitely supported cycles are finite sums of fundamental cycles -/

/-- The fundamental cycle of the integral closed subscheme attached to a point `x` of relative
dimension `k` has coefficient one at `x`. -/
theorem cycleAssociatedToIntegralComponentAt_apply_self (C : ChowSituation.{u}) {T : Scheme.{u}}
    (sT : T ⟶ C.S) [LocallyOfFiniteType sT] {k : ℤ} {x : T}
    (hx : relativeDimension C.dimensionFunction sT x = k) :
    (cycleAssociatedToClosedSubscheme C sT (integralComponentAt x).subschemeι k).1 x = 1 := by
  have hW : IsIntegral (integralComponentAt x).subscheme := isIntegral_integralComponentAt x
  let _ := hW
  have hgp : genericPointOf (integralComponentAt x) hW = x :=
    genericPointOf_integralComponentAt x
  have hgp' : (integralComponentAt x).subschemeι.base
      (genericPoint (integralComponentAt x).subscheme) = x := hgp
  have hdim : schemeDeltaDimension C ((integralComponentAt x).subschemeι ≫ sT) = (k : EInt) := by
    rw [schemeDeltaDimension_eq_genericPoint C ((integralComponentAt x).subschemeι ≫ sT),
      relativeDimension_comp_closedImmersion C.dimensionFunction
        (integralComponentAt x).subschemeι sT, hgp', hx]
  have h := cycleAssociatedToClosedSubscheme_integral_apply C sT (integralComponentAt x) hW hdim
  rwa [hgp] at h

/-- The fundamental cycle of the integral closed subscheme attached to a point `x` vanishes away
from `x`. -/
theorem cycleAssociatedToIntegralComponentAt_apply_of_ne (C : ChowSituation.{u})
    {T : Scheme.{u}} (sT : T ⟶ C.S) [LocallyOfFiniteType sT] (k : ℤ) (x : T) {y : T}
    (hy : y ≠ x) :
    (cycleAssociatedToClosedSubscheme C sT (integralComponentAt x).subschemeι k).1 y = 0 := by
  refine cycleAssociatedToClosedSubscheme_integral_apply_of_ne C sT (integralComponentAt x)
    (isIntegral_integralComponentAt x) k ?_
  rwa [genericPointOf_integralComponentAt x]

/-- A `k`-cycle with finite support is the finite sum, over the points of its support, of its
coefficient there times the fundamental cycle of the integral closed subscheme with that point as
generic point. This is the presentation `α = ∑ nᵢ [Zᵢ]` of Stacks 02QR for a finite sum. -/
theorem eq_finsetSum_cycleAssociatedToIntegralComponentAt (C : ChowSituation.{u})
    {T : Scheme.{u}} (sT : T ⟶ C.S) [LocallyOfFiniteType sT] (k : ℤ) (α : CycleGroup C sT k)
    (hfin : (Function.support (α.1 : T → ℤ)).Finite) :
    α = ∑ x ∈ hfin.toFinset,
      α.1 x • cycleAssociatedToClosedSubscheme C sT (integralComponentAt x).subschemeι k := by
  classical
  have hdim : ∀ x ∈ hfin.toFinset, relativeDimension C.dimensionFunction sT x = k := fun x hx ↦
    (mem_cyclesOfDimension_iff_forall_point C sT k α.1).mp α.2 x (hfin.mem_toFinset.mp hx)
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
  let ev : CycleGroup C sT k →+ ℤ :=
    { toFun := fun a ↦ a.1 y
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have hev : ∀ a : CycleGroup C sT k, ev a = a.1 y := fun _ ↦ rfl
  show ev α = ev _
  rw [map_sum]
  have hterm : ∀ x ∈ hfin.toFinset,
      ev (α.1 x • cycleAssociatedToClosedSubscheme C sT (integralComponentAt x).subschemeι k) =
        if y = x then α.1 y else 0 := by
    intro x hx
    rw [map_zsmul, hev]
    by_cases hyx : y = x
    · subst hyx
      rw [cycleAssociatedToIntegralComponentAt_apply_self C sT (hdim y hx)]
      simp
    · rw [cycleAssociatedToIntegralComponentAt_apply_of_ne C sT k x hyx]
      simp [hyx]
  rw [Finset.sum_congr rfl hterm, hev α]
  by_cases hy : y ∈ hfin.toFinset
  · rw [Finset.sum_eq_single_of_mem y hy (fun x _ hxy ↦ by simp [Ne.symm hxy])]
    simp
  · have hzero : α.1 y = 0 := of_not_not fun h ↦ hy (hfin.mem_toFinset.mpr h)
    have hsum : ∑ x ∈ hfin.toFinset, (if y = x then α.1 y else 0) = 0 := by
      refine Finset.sum_eq_zero fun x hx ↦ ?_
      have hne : y ≠ x := fun he ↦ hy (by rw [he]; exact hx)
      simp [hne]
    rw [hsum, hzero]

/-- On a quasi-compact scheme every cycle has finite support: the support is locally finite and
the whole space is compact. -/
theorem finite_support_of_compactSpace (C : ChowSituation.{u}) {T : Scheme.{u}}
    (sT : T ⟶ C.S) [LocallyOfFiniteType sT] [CompactSpace T] (k : ℤ) (α : CycleGroup C sT k) :
    (Function.support (α.1 : T → ℤ)).Finite := by
  simpa using α.1.locallyFiniteSupport.finite_inter_support_of_isCompact
    (CompactSpace.isCompact_univ (X := T))

/-- The integral closed subschemes attached to the points of the support of a cycle form a
locally finite family: the supports are the closures of those points, and the support of a cycle
is locally finite. -/
theorem locallyFinite_range_subschemeι_support (C : ChowSituation.{u}) {T : Scheme.{u}}
    (sT : T ⟶ C.S) [LocallyOfFiniteType sT] (k : ℤ) (α : CycleGroup C sT k) :
    LocallyFinite fun i : ↥(Function.support (α.1 : T → ℤ)) ↦
      Set.range (integralComponentAt (i : T)).subschemeι := by
  have hsingle : LocallyFinite fun i : ↥(Function.support (α.1 : T → ℤ)) ↦
      ({(i : T)} : Set T) :=
    LocallyFiniteSupport.locallyFinite_support _ α.1.locallyFiniteSupport
  refine (locallyFinite_closure_singleton
    (fun i : ↥(Function.support (α.1 : T → ℤ)) ↦ (i : T)) hsingle).subset fun i ↦ ?_
  rw [(integralComponentAt (i : T)).range_subschemeι, coe_support_integralComponentAt]

/-! ### The two vanishing criteria -/

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
  [LocallyOfFiniteType f] (hf : f ≫ sY = sX) (p : ℤ)

/-- **Clause (2) of Stacks 02UC.** The cap product of `c` with the fundamental class of every
integral scheme locally of finite type over `Y` vanishes.

Quantifying over all degrees `k` expresses the vanishing of `c ∩ [T]` in the graded group
`CH_*(T ×_Y X)`; only the delta-dimension of `T` contributes a nonzero fundamental class. -/
def BivariantClass.CapsIntegralFundamentalClassesToZero
    (c : BivariantClass C G sX sY f hf p) : Prop :=
  ∀ {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] [IsIntegral T] (k : ℤ),
    c.cap g k (fundamentalChowClass C (g ≫ sY) k) = 0

/-- **Clause (3) of Stacks 02UC.** Every integral scheme `T` locally of finite type over `Y`
admits a proper birational `T' ⟶ T` whose fundamental class is killed by `c`. -/
def BivariantClass.HasBirationalModificationCappingToZero
    (c : BivariantClass C G sX sY f hf p) : Prop :=
  ∀ {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] [IsIntegral T],
    ∃ (T' : Scheme.{u}) (h : T' ⟶ T) (hproper : IsProper h),
      letI := hproper
      AlgebraicGeometry.IsBirational h ∧
        ∀ k : ℤ, c.cap (h ≫ g) k (fundamentalChowClass C ((h ≫ g) ≫ sY) k) = 0

/-- The vanishing of a cap product with a fundamental class depends on the test morphism only
through its value. -/
theorem BivariantClass.cap_fundamentalChowClass_eq_zero_congr
    (c : BivariantClass C G sX sY f hf p) {T : Scheme.{u}} {g₁ g₂ : T ⟶ Y}
    [LocallyOfFiniteType g₁] [LocallyOfFiniteType g₂] (hg : g₁ = g₂) (k : ℤ)
    (h : c.cap g₂ k (fundamentalChowClass C (g₂ ≫ sY) k) = 0) :
    c.cap g₁ k (fundamentalChowClass C (g₁ ≫ sY) k) = 0 := by
  subst hg
  exact h

/-- **Stacks 02UC, (1) `⇒` (2).** The zero bivariant class kills every fundamental class. -/
theorem BivariantClass.zero_capsIntegralFundamentalClassesToZero :
    (0 : BivariantClass C G sX sY f hf p).CapsIntegralFundamentalClassesToZero
      C G sX sY f hf p := by
  intro T g _ _ k
  rfl

/-- **Stacks 02UC, (2) `⇒` (3).** A class killing the fundamental class of every integral test
scheme admits the identity as the required proper birational modification. -/
theorem BivariantClass.hasBirationalModificationCappingToZero_of_capsIntegral
    {c : BivariantClass C G sX sY f hf p}
    (hc : c.CapsIntegralFundamentalClassesToZero C G sX sY f hf p) :
    c.HasBirationalModificationCappingToZero C G sX sY f hf p := by
  intro T g _ _
  exact ⟨T, 𝟙 T, inferInstance, isBirational_id T, fun k ↦
    c.cap_fundamentalChowClass_eq_zero_congr C G sX sY f hf p (Category.id_comp g) k (hc g k)⟩

/-! ### From integral test schemes to arbitrary finitely supported cycles -/

/-- Capping with a bivariant class commutes with proper pushforward: if a cycle `β` is the proper
pushforward of a cycle `γ` whose class is capped to zero, then `β` is capped to zero. -/
private theorem BivariantClass.cap_eq_zero_of_properPushforward_aux
    (c : BivariantClass C G sX sY f hf p) {T W : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g]
    (π : W ⟶ T) [IsProper π] (k : ℤ) (β : CycleGroup C (g ≫ sY) k)
    (γ : CycleGroup C ((π ≫ g) ≫ sY) k)
    (hpush : properPushforward C ((π ≫ g) ≫ sY) (g ≫ sY) π (Category.assoc _ _ _).symm k γ = β)
    (hzero : c.cap (π ≫ g) k
      (QuotientAddGroup.mk' (rationalEquivalences C ((π ≫ g) ≫ sY) k) γ) = 0) :
    c.cap g k (QuotientAddGroup.mk' (rationalEquivalences C (g ≫ sY) k) β) = 0 := by
  have hfstcomp : bivariantBaseChangeMap f g π ≫ (pullback.fst f g ≫ sX) =
      pullback.fst f (π ≫ g) ≫ sX := by
    rw [← Category.assoc, bivariantBaseChangeMap_fst]
  have hnat := c.proper_naturality g π (bivariantBaseChangeMap f g π)
    (isPullback_bivariantBaseChangeMap f g π) (bivariantBaseChangeMap_fst f g π) k
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper C
      ((π ≫ g) ≫ sY) (g ≫ sY) π (Category.assoc _ _ _).symm k)
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper C
      (pullback.fst f (π ≫ g) ≫ sX) (pullback.fst f g ≫ sX) (bivariantBaseChangeMap f g π)
      hfstcomp (k - p))
    (QuotientAddGroup.mk' (rationalEquivalences C ((π ≫ g) ≫ sY) k) γ)
  rwa [properChowPushforward_mk, hpush, hzero, map_zero] at hnat

/-- **The step of (2) `⇒` (1) in Stacks 02UC.** A class killing the fundamental class of every
integral test scheme kills the class of the cycle of every integral closed subscheme of every
test scheme: that cycle is the proper pushforward along the closed immersion of the subscheme's
own fundamental class, and capping commutes with proper pushforward. -/
theorem BivariantClass.cap_cycleAssociatedToClosedSubscheme_eq_zero
    {c : BivariantClass C G sX sY f hf p}
    (hc : c.CapsIntegralFundamentalClassesToZero C G sX sY f hf p)
    {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (W : T.IdealSheafData)
    (hW : IsIntegral W.subscheme) (k : ℤ) :
    c.cap g k (QuotientAddGroup.mk' (rationalEquivalences C (g ≫ sY) k)
        (cycleAssociatedToClosedSubscheme C (g ≫ sY) W.subschemeι k)) = 0 := by
  let _ := hW
  set ι : W.subscheme ⟶ T := W.subschemeι with hιdef
  exact c.cap_eq_zero_of_properPushforward_aux C G sX sY f hf p g ι k _ _
    (properPushforward_fundamentalCycle_of_isClosedImmersion C ((ι ≫ g) ≫ sY) (g ≫ sY) ι
      (Category.assoc _ _ _).symm k) (hc (ι ≫ g) k)

/-- **The unconditional half of (2) `⇒` (1) in Stacks 02UC.** A class killing the fundamental
class of every integral test scheme kills the class of every *finitely supported* cycle on every
test scheme: such a cycle is a finite sum of fundamental cycles of integral closed
subschemes. -/
theorem BivariantClass.cap_mk_eq_zero_of_finite_support
    {c : BivariantClass C G sX sY f hf p}
    (hc : c.CapsIntegralFundamentalClassesToZero C G sX sY f hf p)
    {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ)
    (α : CycleGroup C (g ≫ sY) k) (hfin : (Function.support (α.1 : T → ℤ)).Finite) :
    c.cap g k (QuotientAddGroup.mk' (rationalEquivalences C (g ≫ sY) k) α) = 0 := by
  set F := (c.cap g k).comp (QuotientAddGroup.mk' (rationalEquivalences C (g ≫ sY) k)) with hF
  show F α = 0
  rw [eq_finsetSum_cycleAssociatedToIntegralComponentAt C (g ≫ sY) k α hfin, map_sum]
  refine Finset.sum_eq_zero fun x _ ↦ ?_
  rw [map_zsmul, show F (cycleAssociatedToClosedSubscheme C (g ≫ sY)
      (integralComponentAt x).subschemeι k) = 0 from
    c.cap_cycleAssociatedToClosedSubscheme_eq_zero C G sX sY f hf p hc g (integralComponentAt x)
      (isIntegral_integralComponentAt x) k, smul_zero]

/-! ### Capping with a class that vanishes on the pieces of a decomposition -/

/-- The vanishing of a cap product does not depend on the way its degree is written. -/
theorem BivariantClass.cap_eq_zero_congr_degree (c : BivariantClass C G sX sY f hf p)
    {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] {k k' : ℤ} (hk : k = k')
    (α : chowGroup C (g ≫ sY) k) :
    c.cap g k α = 0 ↔ c.cap g k' (hk ▸ α : chowGroup C (g ≫ sY) k') = 0 := by
  cases hk
  exact Iff.rfl

/-- The range of the base change of a morphism of test schemes is the inverse image of its
range: the base change square is a pullback square, so the base change is, up to the isomorphism
with the pullback, the second projection. -/
theorem range_bivariantBaseChangeMap {X' Y' T T' : Scheme.{u}} (f' : X' ⟶ Y') (g : T ⟶ Y')
    (h : T' ⟶ T) :
    Set.range (bivariantBaseChangeMap f' g h) =
      pullback.snd f' g ⁻¹' Set.range h := by
  have hsq := isPullback_bivariantBaseChangeMap f' g h
  have hsnd : hsq.isoPullback.hom ≫ pullback.snd h (pullback.snd f' g) =
      bivariantBaseChangeMap f' g h := hsq.isoPullback_hom_snd
  have hsurj : Function.Surjective hsq.isoPullback.hom := Surjective.surj
  rw [← hsnd, show Set.range ((hsq.isoPullback.hom ≫ pullback.snd h (pullback.snd f' g))) =
      Set.range ((pullback.snd h (pullback.snd f' g)) ∘ hsq.isoPullback.hom) from rfl,
    Set.range_comp, hsurj.range_eq, Set.image_univ, Scheme.Pullback.range_snd]

/-- **A cap product vanishes as soon as it vanishes on every piece of a decomposition of the
test scheme into open and closed subschemes.**

The decomposition of the test scheme base changes to a decomposition of the base change of `X`,
and capping with a bivariant class commutes with the flat pullbacks onto the pieces, which are
the projections of the product decomposition of the Chow groups. This is the step of the proof of
Stacks 02UC reading `CH_{k-p}(X'') = ∏ CH_{k-p}(X'ᵢ)`. -/
theorem BivariantClass.cap_eq_zero_of_clopen_cover {c : BivariantClass C G sX sY f hf p}
    {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] {I : Type u} {Z : I → Scheme.{u}}
    (m : ∀ i, Z i ⟶ T) [∀ i, IsOpenImmersion (m i)]
    (hcover : ∀ x : T, ∃ i, x ∈ Set.range (m i))
    (hdisjoint : Pairwise fun i l ↦ Disjoint (Set.range (m i)) (Set.range (m l))) (k : ℤ)
    (α : chowGroup C (g ≫ sY) k)
    (hα : ∀ i, c.cap (m i ≫ g) k (chowGroupRestrict C (g ≫ sY) ((m i ≫ g) ≫ sY) (m i)
      (Category.assoc _ _ _).symm k α) = 0) :
    c.cap g k α = 0 := by
  have hk : k + ((0 : ℕ) : ℤ) = k := by simp
  have hopen : ∀ i, IsOpenImmersion (bivariantBaseChangeMap f g (m i)) := fun i ↦
    MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap f g (m i))
      (P := @IsOpenImmersion) inferInstance
  have hbase : ∀ i, bivariantBaseChangeMap f g (m i) ≫ (pullback.fst f g ≫ sX) =
      pullback.fst f (m i ≫ g) ≫ sX := fun i ↦ by
    rw [← Category.assoc, bivariantBaseChangeMap_fst]
  have hrange : ∀ i, Set.range (bivariantBaseChangeMap f g (m i)) =
      pullback.snd f g ⁻¹' Set.range (m i) := fun i ↦ range_bivariantBaseChangeMap f g (m i)
  have hcover' : ∀ x : (pullback f g : Scheme.{u}),
      ∃ i, x ∈ Set.range (bivariantBaseChangeMap f g (m i)) := fun x ↦ by
    obtain ⟨i, hi⟩ := hcover (pullback.snd f g x)
    exact ⟨i, (hrange i).symm ▸ hi⟩
  have hdisjoint' : Pairwise fun i l ↦ Disjoint
      (Set.range (bivariantBaseChangeMap f g (m i)))
      (Set.range (bivariantBaseChangeMap f g (m l))) := fun i l hil ↦ by
    simp only [hrange]
    exact (hdisjoint hil).preimage _
  refine eq_zero_of_chowGroupRestrict_eq_zero C (pullback.fst f g ≫ sX)
    (fun i ↦ pullback.fst f (m i ≫ g) ≫ sX) (fun i ↦ bivariantBaseChangeMap f g (m i)) hbase
    (isClopenDecomposition_of_isOpenImmersion_cover _ hcover' hdisjoint') (k - p) _ fun i ↦ ?_
  have hfacm : FlatPullbackFactorsThroughRationalEquivalence C ((m i ≫ g) ≫ sY) (g ≫ sY) (m i)
      (Category.assoc _ _ _).symm 0 (relativeDimension_of_isOpenImmersion (m i)) k :=
    flatPullbackFactorsThroughRationalEquivalence_of_isOpenImmersion C (g ≫ sY)
      ((m i ≫ g) ≫ sY) (m i) (Category.assoc _ _ _).symm k
  have hfac' : FlatPullbackFactorsThroughRationalEquivalence C
      (pullback.fst f (m i ≫ g) ≫ sX) (pullback.fst f g ≫ sX)
      (bivariantBaseChangeMap f g (m i)) (hbase i) 0
      (relativeDimension_of_isOpenImmersion _) (k - p) :=
    flatPullbackFactorsThroughRationalEquivalence_of_isOpenImmersion C (pullback.fst f g ≫ sX)
      (pullback.fst f (m i ≫ g) ≫ sX) (bivariantBaseChangeMap f g (m i)) (hbase i) (k - p)
  rw [← flatPullbackChow_eq_zero_iff_chowGroupRestrict_eq_zero C (pullback.fst f g ≫ sX)
    (pullback.fst f (m i ≫ g) ≫ sX) (bivariantBaseChangeMap f g (m i)) (hbase i) (k - p) hfac']
  have hpiece : c.cap (m i ≫ g) (k + ((0 : ℕ) : ℤ))
      (flatPullbackChow C ((m i ≫ g) ≫ sY) (g ≫ sY) (m i) (Category.assoc _ _ _).symm 0
        (relativeDimension_of_isOpenImmersion (m i)) k hfacm α) = 0 := by
    rw [c.cap_eq_zero_congr_degree C G sX sY f hf p (m i ≫ g) hk,
      cast_flatPullbackChow_eq_chowGroupRestrict C (g ≫ sY) ((m i ≫ g) ≫ sY) (m i)
        (Category.assoc _ _ _).symm k hk hfacm α]
    exact hα i
  refine eq_of_heq (HEq.trans (c.flat_naturality g (m i) 0
    (relativeDimension_of_isOpenImmersion (m i)) (bivariantBaseChangeMap f g (m i))
    (isPullback_bivariantBaseChangeMap f g (m i)) (bivariantBaseChangeMap_fst f g (m i)) k
    (relativeDimension_of_isOpenImmersion _) hfacm hfac' α).symm ?_)
  rw [hpiece]
  exact chowGroup_zero_heq C (pullback.fst f (m i ≫ g) ≫ sX) (by omega)

/-- **The cap product with the class of a cycle which restricts to a multiple of a fundamental
class on an open piece vanishes on that piece**, for a class satisfying (2): the piece is an
integral scheme locally of finite type over `Y`, so its fundamental class is killed by (2). -/
theorem BivariantClass.cap_chowGroupRestrict_mk_eq_zero {c : BivariantClass C G sX sY f hf p}
    (hc : c.CapsIntegralFundamentalClassesToZero C G sX sY f hf p) {W Z : Scheme.{u}}
    (g : W ⟶ Y) [LocallyOfFiniteType g] [IsIntegral Z] (m : Z ⟶ W) [IsOpenImmersion m] (k : ℤ)
    (γ : CycleGroup C (g ≫ sY) k) (n : ℤ)
    (hrestrict : cycleGroupRestrict C (g ≫ sY) ((m ≫ g) ≫ sY) m (Category.assoc _ _ _).symm k γ =
      n • fundamentalCycle C ((m ≫ g) ≫ sY) k) :
    c.cap (m ≫ g) k (chowGroupRestrict C (g ≫ sY) ((m ≫ g) ≫ sY) m (Category.assoc _ _ _).symm k
      (QuotientAddGroup.mk' (rationalEquivalences C (g ≫ sY) k) γ)) = 0 := by
  rw [chowGroupRestrict_mk, hrestrict, mk_zsmul_fundamentalCycle, map_zsmul, hc (m ≫ g) k,
    smul_zero]

/-! ### Descending the vanishing along a proper cover -/

/-- **The vanishing of a cap product descends along a proper pushforward.** If the cycle `β` on a
test scheme is the proper pushforward of a cycle `γ` on a scheme proper over it, and the cap
product with the class of `γ` vanishes, then so does the cap product with the class of `β`:
capping with a bivariant class commutes with proper pushforward. -/
theorem BivariantClass.cap_mk_eq_zero_of_properPushforward
    (c : BivariantClass C G sX sY f hf p) {T W : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g]
    (π : W ⟶ T) [IsProper π] (k : ℤ) (β : CycleGroup C (g ≫ sY) k)
    (γ : CycleGroup C ((π ≫ g) ≫ sY) k)
    (hpush : properPushforward C ((π ≫ g) ≫ sY) (g ≫ sY) π (Category.assoc _ _ _).symm k γ = β)
    (hzero : c.cap (π ≫ g) k
      (QuotientAddGroup.mk' (rationalEquivalences C ((π ≫ g) ≫ sY) k) γ) = 0) :
    c.cap g k (QuotientAddGroup.mk' (rationalEquivalences C (g ≫ sY) k) β) = 0 := by
  exact c.cap_eq_zero_of_properPushforward_aux C G sX sY f hf p g π k β γ hpush hzero

/-! ### From a locally finite family of integral components to the whole Chow group -/

/-- **The step of (2) `⇒` (1) in Stacks 02UC for a locally finite family.** Let `β` be a
`k`-cycle on a test scheme `T`, and present the points of its support as the generic points of a
locally finite family of integral closed subschemes `Zᵢ ⊆ T`. A class satisfying (2) kills the
class of `β`.

This is the argument of the source: the coproduct `W = ∐ Zᵢ` is proper over `T` by
`Stacks.Chow.isProper_sigmaDesc_of_locallyFinite`, the cycle `∑ nᵢ [Zᵢ]` on `W` pushes forward to
`β`, and `W` is decomposed into open and closed subschemes by its summands, so the cap product
with the class of that cycle vanishes piecewise — on the summand `Zᵢ` it is `nᵢ` times the cap
product with the fundamental class of the integral scheme `Zᵢ`, which is zero by (2). -/
theorem BivariantClass.cap_mk_eq_zero_of_integralPresentation
    {c : BivariantClass C G sX sY f hf p}
    (hc : c.CapsIntegralFundamentalClassesToZero C G sX sY f hf p)
    {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ)
    (β : CycleGroup C (g ≫ sY) k)
    (Z : ↥(Function.support (β.1 : T → ℤ)) → Scheme.{u}) [∀ i, IsIntegral (Z i)]
    (v : ∀ i, Z i ⟶ T) [∀ i, IsClosedImmersion (v i)]
    (hv : ∀ i, (v i).base (genericPoint (Z i)) = (i : T))
    (hlf : LocallyFinite fun i ↦ Set.range (v i)) :
    c.cap g k (QuotientAddGroup.mk' (rationalEquivalences C (g ≫ sY) k) β) = 0 := by
  classical
  have hproper : IsProper (Sigma.desc v) := isProper_sigmaDesc_of_locallyFinite Z v hlf
  -- the summand inclusions, and the base morphisms of the summands
  have hti : ∀ i, (Sigma.ι Z i ≫ (Sigma.desc v ≫ g)) ≫ sY = v i ≫ (g ≫ sY) := fun i ↦ by
    rw [← Category.assoc, Sigma.ι_desc, Category.assoc]
  have hassoc : ∀ i, Sigma.ι Z i ≫ ((Sigma.desc v ≫ g) ≫ sY) =
      (Sigma.ι Z i ≫ (Sigma.desc v ≫ g)) ≫ sY := fun i ↦ (Category.assoc _ _ _).symm
  -- the fundamental cycle of a summand sits in degree `k`
  have hdim : ∀ i, relativeDimension C.dimensionFunction
      ((Sigma.ι Z i ≫ (Sigma.desc v ≫ g)) ≫ sY) (genericPoint (Z i)) = k := fun i ↦ by
    rw [hti i, relativeDimension_comp_closedImmersion, hv i]
    exact (mem_cyclesOfDimension_iff_forall_point C (g ≫ sY) k β.1).1 β.2 _ i.2
  have hcoeff : ∀ i, ∀ z : Z i,
      (β.1 (i : T) • fundamentalCycle C ((Sigma.ι Z i ≫ (Sigma.desc v ≫ g)) ≫ sY) k).1 z =
        if z = genericPoint (Z i) then β.1 (i : T) else 0 := fun i z ↦ by
    show β.1 (i : T) •
      (fundamentalCycle C ((Sigma.ι Z i ≫ (Sigma.desc v ≫ g)) ≫ sY) k).1 z = _
    rw [fundamentalCycle_eq_single C ((Sigma.ι Z i ≫ (Sigma.desc v ≫ g)) ≫ sY)
      genericPoints_eq_singleton (hdim i) (Field.toIsField _)]
    simp [Function.locallyFinsuppWithin.single_apply]
  -- the cycle on the coproduct
  obtain ⟨γ, hγ⟩ := exists_cycleGroup_of_sigma C Z ((Sigma.desc v ≫ g) ≫ sY)
    (fun i ↦ (Sigma.ι Z i ≫ (Sigma.desc v ≫ g)) ≫ sY) hassoc k
    (fun i ↦ β.1 (i : T) • fundamentalCycle C ((Sigma.ι Z i ≫ (Sigma.desc v ≫ g)) ≫ sY) k)
  -- it pushes forward to `β`
  have hres : ∀ x : (∐ Z : Scheme.{u}),
      Function.Bijective (((Sigma.desc v).residueFieldMap x).hom) := by
    have : SurjectiveOnStalks (Sigma.desc v) := surjectiveOnStalks_sigmaDesc Z v
    exact fun x ↦ bijective_residueFieldMap_of_surjective_stalkMap (Sigma.desc v) x
      ((Sigma.desc v).stalkMap_surjective x)
  have hepoint : ∀ i, (Sigma.desc v).base (Sigma.ι Z i (genericPoint (Z i))) = (i : T) :=
    fun i ↦ by
      rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]
      exact hv i
  have hpush : properPushforward C ((Sigma.desc v ≫ g) ≫ sY) (g ≫ sY) (Sigma.desc v)
      (Category.assoc _ _ _).symm k γ = β := by
    refine properPushforward_eq_of_support_section C (g ≫ sY) ((Sigma.desc v ≫ g) ≫ sY)
      (Sigma.desc v) (Category.assoc _ _ _).symm k hres β γ
      (fun i ↦ Sigma.ι Z i (genericPoint (Z i))) hepoint (fun i ↦ ?_) (fun x hx ↦ ?_)
    · rw [hγ i, hcoeff i]
      simp
    · obtain ⟨⟨i, z⟩, rfl⟩ := (sigmaMk Z).surjective x
      rw [sigmaMk_mk, hγ i, hcoeff i] at hx
      refine ⟨i, ?_⟩
      by_cases hz : z = genericPoint (Z i)
      · rw [sigmaMk_mk, hz]
      · simp [hz] at hx
  -- the cap product with its class vanishes summandwise
  have hzero : c.cap (Sigma.desc v ≫ g) k
      (QuotientAddGroup.mk' (rationalEquivalences C ((Sigma.desc v ≫ g) ≫ sY) k) γ) = 0 := by
    refine c.cap_eq_zero_of_clopen_cover C G sX sY f hf p (Sigma.desc v ≫ g) (Sigma.ι Z)
      (exists_mem_range_sigmaι Z) (pairwise_disjoint_range_sigmaι Z) k _ fun i ↦ ?_
    refine c.cap_chowGroupRestrict_mk_eq_zero C G sX sY f hf p hc (Sigma.desc v ≫ g)
      (Sigma.ι Z i) k γ (β.1 (i : T)) (Subtype.ext (Function.locallyFinsuppWithin.ext fun z ↦ ?_))
    rw [cycleGroupRestrict_apply]
    exact hγ i z
  exact c.cap_mk_eq_zero_of_properPushforward C G sX sY f hf p g (Sigma.desc v) k β γ hpush hzero

/-- **Stacks 02UC, (2) `⇒` (1).** A bivariant class killing the fundamental class of every
integral scheme locally of finite type over `Y` is zero.

Every Chow class on a test scheme is the class of a cycle, and the points of the support of that
cycle are the generic points of a locally finite family of integral closed subschemes — the
reduced closures of those points — so
`Stacks.Chow.BivariantClass.cap_mk_eq_zero_of_integralPresentation` applies. -/
theorem BivariantClass.eq_zero_of_capsIntegralFundamentalClassesToZero
    {c : BivariantClass C G sX sY f hf p}
    (hc : c.CapsIntegralFundamentalClassesToZero C G sX sY f hf p) : c = 0 := by
  apply BivariantClass.ext
  intro T g _ k α
  rw [BivariantClass.zero_cap]
  induction α using QuotientAddGroup.induction_on with
  | H β =>
    have : ∀ i : ↥(Function.support (β.1 : T → ℤ)),
        IsIntegral (integralComponentAt (i : T)).subscheme := fun i ↦
      isIntegral_integralComponentAt (i : T)
    exact c.cap_mk_eq_zero_of_integralPresentation C G sX sY f hf p hc g k β
      (fun i ↦ (integralComponentAt (i : T)).subscheme)
      (fun i ↦ (integralComponentAt (i : T)).subschemeι)
      (fun i ↦ genericPointOf_integralComponentAt (i : T))
      (locallyFinite_range_subschemeι_support C (g ≫ sY) k β)

/-- **Stacks 02UC, (1) `⇔` (2).** A bivariant class is zero exactly when its cap product with
the fundamental class of every integral scheme locally of finite type over `Y` vanishes. -/
@[stacks 02UC "(1) ⇔ (2)"]
theorem BivariantClass.eq_zero_iff_capsIntegralFundamentalClassesToZero
    (c : BivariantClass C G sX sY f hf p) :
    c = 0 ↔ c.CapsIntegralFundamentalClassesToZero C G sX sY f hf p := by
  refine ⟨fun h ↦ ?_, fun hc ↦
    BivariantClass.eq_zero_of_capsIntegralFundamentalClassesToZero C G sX sY f hf p hc⟩
  subst h
  exact BivariantClass.zero_capsIntegralFundamentalClassesToZero C G sX sY f hf p

/-- **Stacks 02UC, (3) `⇒` (2).** If some proper birational modification of each integral test
scheme has its fundamental class killed by `c`, then so has the test scheme itself: the
modification pushes its fundamental class forward to the fundamental class, and capping with a
bivariant class commutes with proper pushforward. -/
@[stacks 02UC "(3) ⇒ (2)"]
theorem BivariantClass.capsIntegralFundamentalClassesToZero_of_hasBirationalModification
    {c : BivariantClass C G sX sY f hf p}
    (hc : c.HasBirationalModificationCappingToZero C G sX sY f hf p) :
    c.CapsIntegralFundamentalClassesToZero C G sX sY f hf p := by
  intro T g _ _ k
  obtain ⟨T', h, hproper, hbir, hzero⟩ := hc g
  let _ := hproper
  exact c.cap_eq_zero_of_properPushforward_aux C G sX sY f hf p g h k _ _
    (properPushforward_fundamentalCycle_of_isBirational C ((h ≫ g) ≫ sY) (g ≫ sY) h
      (Category.assoc _ _ _).symm hbir k) (hzero k)

/-- **Stacks 02UC, (2) `⇔` (3).** A bivariant class kills the fundamental class of every integral
scheme locally of finite type over `Y` exactly when each such scheme admits a proper birational
modification whose fundamental class it kills. -/
@[stacks 02UC "(2) ⇔ (3)"]
theorem BivariantClass.capsIntegralFundamentalClassesToZero_iff_hasBirationalModification
    (c : BivariantClass C G sX sY f hf p) :
    c.CapsIntegralFundamentalClassesToZero C G sX sY f hf p ↔
      c.HasBirationalModificationCappingToZero C G sX sY f hf p :=
  ⟨BivariantClass.hasBirationalModificationCappingToZero_of_capsIntegral C G sX sY f hf p,
    BivariantClass.capsIntegralFundamentalClassesToZero_of_hasBirationalModification
      C G sX sY f hf p⟩

/-- **Stacks 02UC.** For a bivariant class `c ∈ A^p(X ⟶ Y)` the following are equivalent: `c` is
zero; `c ∩ [Y'] = 0` for every integral scheme `Y'` locally of finite type over `Y`; and every
such `Y'` admits a proper birational `Y'' ⟶ Y'` with `c ∩ [Y''] = 0`. -/
@[stacks 02UC "all three clauses"]
theorem BivariantClass.eq_zero_tfae (c : BivariantClass C G sX sY f hf p) :
    [c = 0, c.CapsIntegralFundamentalClassesToZero C G sX sY f hf p,
      c.HasBirationalModificationCappingToZero C G sX sY f hf p].TFAE := by
  have h12 := BivariantClass.eq_zero_iff_capsIntegralFundamentalClassesToZero
    C G sX sY f hf p c
  have h23 := BivariantClass.capsIntegralFundamentalClassesToZero_iff_hasBirationalModification
    C G sX sY f hf p c
  refine List.tfae_of_forall (b := (c = 0)) fun a ha ↦ ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact Iff.rfl
  · exact h12.symm
  · exact (h12.trans h23).symm

/-- The fundamental class of a scheme is carried to the fundamental class by the transport
between the Chow groups of two equal structure morphisms. The fundamental class is the class of
the cycle of `T` as a closed subscheme of itself, so it does not see the structure morphism
except through the group it lives in. -/
public theorem chowGroupCongr_fundamentalChowClass (C : ChowSituation.{u}) {T : Scheme.{u}}
    {q q' : T ⟶ C.S} [LocallyOfFiniteType q] [LocallyOfFiniteType q'] (hq : q = q') (k : ℤ) :
    chowGroupCongr C hq k (fundamentalChowClass C q k) = fundamentalChowClass C q' k := by
  subst hq
  rfl

end Stacks.Chow

end
