module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.RingTheory.Kaehler.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Factor
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.Retrofit

/-!
# Formal unramifiedness on étale charts

A formally unramified morphism of presheaves on the big fppf site of `S` is formally
unramified on every commuting square of étale scheme charts, and conversely such a square
can always be found with both chart morphisms surjective. These are the implications
(1) ⟹ (2) ⟹ (3) of [Stacks Project, Tag 04G8].

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.formallyUnramified_of_etale`: an étale morphism of presheaves is
  formally unramified.
* `AlgebraicGeometry.Space.formallyUnramified_of_etaleSquare`: in a commuting square of
  étale charts over a formally unramified morphism, the chart morphism is formally
  unramified as a morphism of presheaves.
* `AlgebraicGeometry.Space.formallyUnramified_map_of_formallyUnramified`: a morphism of the
  site whose Yoneda image is formally unramified has formally unramified underlying
  morphism of schemes. This is the step from the site-level lifting condition of
  [Stacks Project, Tag 049S] to Mathlib's `AlgebraicGeometry.FormallyUnramified`, which is
  the formal unramifiedness of morphisms of schemes of [Stacks Project, Tag 02H8].
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_of_formallyUnramified` is the implication
  (1) ⟹ (2) of [Stacks Project, Tag 04G8], and
  `AlgebraicGeometry.Space.exists_surjectiveEtaleChart_of_holdsOnEveryEtaleChart` is its
  implication (2) ⟹ (3).

## Implementation notes

The content is the passage from the site-level uniqueness of infinitesimal lifts, which
tests only square-zero thickenings *inside the chosen big fppf site*, to formal
unramifiedness of a morphism of schemes, which tests all of them. It is carried out in
three stages.

First, `formallyUnramified_hom_ext_of_contains` turns the site-level condition into a
cancellation statement about morphisms of schemes: any two sections of a square-zero
thickening whose source and target both satisfy the site's size cutoff and are affine
agree. The thickening is transported into the slice by `CategoryTheory.Functor.preimage`
along the full and faithful inclusion of the site, and the structure morphisms to `S` are
obtained by composing with those of the two given objects.

Second, over an affine pair the universal square-zero thickening
`Γ(X, ⊤) ⊗ Γ(X, ⊤) ⧸ J ^ 2` of the first-order jets is used. It has exactly two features
that matter: its cardinality is bounded by that of the two section rings, so
`AlgebraicGeometry.Scheme.size_Spec` places its spectrum inside the site; and its sections
are the endomorphisms of the module of Kähler differentials, by
`KaehlerDifferential.endEquiv`, so uniqueness of sections says `Ω` is trivial, which is
`Algebra.FormallyUnramified`.

Third, the general case is reduced to the affine one by restricting to a pair of affine
opens. An open immersion is a monomorphism and locally of finite presentation, so
`AlgebraicGeometry.Scheme.size_le_of_mono_locallyOfFinitePresentation` places the affine
opens inside the site as well, and the restriction of the morphism to them is a chart
square to which `formallyUnramified_of_etaleSquare` applies.

The remaining implication (3) ⟹ (1) of Tag 04G8 is the descent of formal unramifiedness
along a surjective étale chart, which is [Stacks Project, Tag 04CY] in its descent form.
Only the composition form of that tag is available here
(`AlgebraicGeometry.Space.formallyUnramified_comp_of_etale`), so nothing in this file
closes the equivalence and the two implications proved carry part strings rather than the
bare tag.

## References

* [Stacks Project, Tag 02H8](https://stacks.math.columbia.edu/tag/02H8)
* [Stacks Project, Tag 02X1](https://stacks.math.columbia.edu/tag/02X1)
* [Stacks Project, Tag 049S](https://stacks.math.columbia.edu/tag/049S)
* [Stacks Project, Tag 049T](https://stacks.math.columbia.edu/tag/049T)
* [Stacks Project, Tag 04AL](https://stacks.math.columbia.edu/tag/04AL)
* [Stacks Project, Tag 04CY](https://stacks.math.columbia.edu/tag/04CY)
* [Stacks Project, Tag 04G5](https://stacks.math.columbia.edu/tag/04G5)
* [Stacks Project, Tag 04G8](https://stacks.math.columbia.edu/tag/04G8)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Space

/-! ### The site-level half -/

/-- An étale morphism of presheaves on the big fppf site of `S` is formally unramified: it
is unramified by [Stacks Project, Tag 02G8], hence formally unramified by
[Stacks Project, Tag 04AL]. -/
theorem formallyUnramified_of_etale (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G)
    (ha : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    FormallyUnramified a :=
  formallyUnramified_of_unramified B S hS a
    ((MorphismProperty.relative_monotone (F := CategoryTheory.yoneda)
      (MorphismProperty.monotone_inverseImage _
        (fun _ _ _ hf => @unramified_of_etale _ _ _ hf)) a) ha)

/-- **Stacks 04G8, the site-level square.** If `f` is formally unramified and `a`, `b` are
étale charts of its source and target fitting in a commuting square over a morphism `ψ` of
the site, then `ψ` is formally unramified as a morphism of presheaves.

The chart `a` is formally unramified by `AlgebraicGeometry.Space.formallyUnramified_of_etale`,
so `a ≫ f` is by [Stacks Project, Tag 049T], and `yoneda.map ψ ≫ b` is the same morphism;
since `b` is formally unramified, [Stacks Project, Tag 04G5] leaves `yoneda.map ψ`
formally unramified. No algebraicity hypothesis on the source or target is used. -/
theorem formallyUnramified_of_etaleSquare (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hf : FormallyUnramified f) {U V : BigFppfOver B S hS}
    (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (ψ : U ⟶ V)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hdiag : yoneda.map ψ ≫ b = a ≫ f) :
    FormallyUnramified (yoneda.map ψ) :=
  formallyUnramified_left_of_comp (yoneda.map ψ) b
    (formallyUnramified_of_etale B S hS b hb)
    (hdiag ▸ formallyUnramified_comp a f (formallyUnramified_of_etale B S hS a ha) hf)

/-! ### From the site-level condition to a cancellation law for schemes -/

/-- A morphism of the big fppf category over `S`, read as a morphism of schemes, commutes with
the structure morphisms to `S`. -/
private theorem map_comp_inclusion_hom_eq (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {P Q : BigFppfOver B S hS} (ψ : P ⟶ Q) :
    (BigFppfOver.toScheme B S hS).map ψ ≫ B.inclusion.map Q.hom = B.inclusion.map P.hom := by
  change B.inclusion.map (Over.Hom.left ψ) ≫ B.inclusion.map Q.hom = _
  rw [← Functor.map_comp, Over.w ψ]

/-- Two morphisms of the big fppf category over `S` are equal when their underlying morphisms
of schemes are. -/
private theorem over_hom_ext_of_inclusion_map (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {P Q : BigFppfOver B S hS} {f g : P ⟶ Q}
    (h : B.inclusion.map f.left = B.inclusion.map g.left) : f = g :=
  Over.OverMorphism.ext (B.inclusion.map_injective h)

/-- **The transfer step.** Let `ψ` be a morphism of the big fppf site over `S` whose Yoneda
image is formally unramified. Let `i : Z ⟶ Z'` be a closed immersion of affine schemes
defined by a square-zero ideal, both of which satisfy the site's size cutoff. Then two
morphisms `Z' ⟶ P` which agree after restriction along `i` and after composition with `ψ`
are equal.

This is the site-level lifting condition read as a cancellation law for morphisms of
schemes: the thickening is transported into the slice over `S` along the full and faithful
inclusion of the site, with structure morphisms obtained from those of `P` and `Q`. -/
private theorem formallyUnramified_hom_ext_of_contains
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {P Q : BigFppfOver B S hS} (ψ : P ⟶ Q)
    (hψ : FormallyUnramified (yoneda.map ψ))
    {Z Z' : Scheme.{u}} (hZ : B.Contains Z) (hZ' : B.Contains Z')
    (hZaff : IsAffine Z) (hZ'aff : IsAffine Z')
    (i : Z ⟶ Z') (hi : _root_.AlgebraicGeometry.IsClosedImmersion i) (hker : i.ker ^ 2 = ⊥)
    (z₁ z₂ : Z' ⟶ (BigFppfOver.toScheme B S hS).obj P)
    (hiz : i ≫ z₁ = i ≫ z₂)
    (hcomm : z₁ ≫ (BigFppfOver.toScheme B S hS).map ψ
        = z₂ ≫ (BigFppfOver.toScheme B S hS).map ψ) :
    z₁ = z₂ := by
  let G := BigFppfOver.toScheme B S hS
  let iL : B.obj hZ ⟶ B.obj hZ' := B.inclusion.preimage i
  let zL : (Z' ⟶ G.obj P) → (B.obj hZ' ⟶ P.left) := fun z => B.inclusion.preimage z
  have hMapI : B.inclusion.map iL = i := B.inclusion.map_preimage _
  have hMapZ : ∀ z, B.inclusion.map (zL z) = z := fun z => B.inclusion.map_preimage _
  have htop := map_comp_inclusion_hom_eq B S hS ψ
  let yBase : B.obj hZ' ⟶ B.obj hS := zL z₁ ≫ P.hom
  let T : BigFppfOver B S hS := Over.mk (iL ≫ yBase)
  let T' : BigFppfOver B S hS := Over.mk yBase
  let iB : T ⟶ T' := Over.homMk iL rfl
  let zB₁ : T' ⟶ P := Over.homMk (zL z₁) rfl
  have hz₂ : zL z₂ ≫ P.hom = yBase := by
    apply B.inclusion.map_injective
    change B.inclusion.map (zL z₂) ≫ B.inclusion.map P.hom =
      B.inclusion.map (zL z₁) ≫ B.inclusion.map P.hom
    rw [hMapZ, hMapZ, ← htop, ← Category.assoc, ← Category.assoc, hcomm]
  let zB₂ : T' ⟶ P := Over.homMk (zL z₂) hz₂
  have hmapiB : G.map iB = i := hMapI
  have hAffT : IsAffine (G.obj T) := hZaff
  have hAffT' : IsAffine (G.obj T') := hZ'aff
  have hSq : IsSquareZeroClosedImmersion B S hS iB := by
    change _root_.AlgebraicGeometry.IsClosedImmersion (G.map iB) ∧ (G.map iB).ker ^ 2 = ⊥
    rw [hmapiB]
    exact ⟨hi, hker⟩
  have hL₁ : IsLift (yoneda.map ψ) iB (iB ≫ zB₁) (zB₁ ≫ ψ) zB₁ := ⟨rfl, rfl⟩
  have hiB₂ : iB ≫ zB₂ = iB ≫ zB₁ := by
    refine over_hom_ext_of_inclusion_map B S hS ?_
    rw [Over.comp_left, Over.comp_left, Functor.map_comp, Functor.map_comp]
    change B.inclusion.map iL ≫ B.inclusion.map (zL z₂) =
      B.inclusion.map iL ≫ B.inclusion.map (zL z₁)
    rw [hMapI, hMapZ, hMapZ, hiz]
  have hψ₂ : zB₂ ≫ ψ = zB₁ ≫ ψ := by
    refine over_hom_ext_of_inclusion_map B S hS ?_
    rw [Over.comp_left, Over.comp_left, Functor.map_comp, Functor.map_comp]
    change B.inclusion.map (zL z₂) ≫ G.map ψ = B.inclusion.map (zL z₁) ≫ G.map ψ
    rw [hMapZ, hMapZ, hcomm]
  have hu := hψ T T' hAffT hAffT' iB hSq (iB ≫ zB₁) (zB₁ ≫ ψ) rfl zB₁ zB₂ hL₁ ⟨hiB₂, hψ₂⟩
  calc z₁ = B.inclusion.map (zL z₁) := (hMapZ z₁).symm
    _ = B.inclusion.map (zL z₂) := congrArg B.inclusion.map (congrArg Over.Hom.left hu)
    _ = z₂ := hMapZ z₂

/-! ### The universal square-zero thickening of an algebra -/

/-- The multiplication map out of the universal first-order quotient `A ⊗[R] A ⧸ J ^ 2` is
surjective: the class of `a ⊗ₜ 1` is a preimage of `a`. -/
private theorem surjective_kerSquareLift (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] :
    Function.Surjective
      (Algebra.TensorProduct.lmul' R (S := A)).kerSquareLift.toRingHom := fun a =>
  ⟨Ideal.Quotient.mk _ (a ⊗ₜ[R] (1 : A)), by
    change (Algebra.TensorProduct.lmul' R (S := A)).kerSquareLift
      (Ideal.Quotient.mk _ (a ⊗ₜ[R] (1 : A))) = a
    rw [AlgHom.kerSquareLift_mk]
    simp⟩

/-- The kernel of the multiplication map out of `A ⊗[R] A ⧸ J ^ 2` is square zero: it is
the cotangent ideal of `J`. -/
private theorem ker_sq_kerSquareLift (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] :
    RingHom.ker (Algebra.TensorProduct.lmul' R (S := A)).kerSquareLift.toRingHom ^ 2 = ⊥ := by
  rw [AlgHom.ker_kerSquareLift]
  exact Ideal.cotangentIdeal_square _

/-- The spectrum of the universal first-order quotient `A ⊗[R] A ⧸ J ^ 2` maps to the
spectrum of `A` by a closed immersion, since the multiplication map is surjective. -/
private theorem isClosedImmersion_specMap_kerSquareLift (R A : Type u) [CommRing R]
    [CommRing A] [Algebra R A] :
    _root_.AlgebraicGeometry.IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.lmul' R (S := A)).kerSquareLift.toRingHom)) :=
  IsClosedImmersion.spec_of_surjective _ (surjective_kerSquareLift R A)

/-- The kernel ideal sheaf of the closed immersion `Spec A ⟶ Spec C` attached to a
surjective ring map `φ : C →+* A` with square-zero kernel is itself square zero. -/
private theorem ker_sq_specMap_of_ker_sq {C A : Type u} [CommRing C] [CommRing A]
    (φ : C →+* A) (hsurj : Function.Surjective φ) (hker : RingHom.ker φ ^ 2 = ⊥) :
    (Spec.map (CommRingCat.ofHom φ)).ker ^ 2 = ⊥ := by
  have hiA : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.injective
  have hiC : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of C)).commRingCatIsoToRingEquiv.injective
  have hNat : (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp
      (Spec.map (CommRingCat.ofHom φ)).appTop.hom =
      φ.comp (Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom := by
    simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] using
      congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
  have hci : _root_.AlgebraicGeometry.IsClosedImmersion (Spec.map (CommRingCat.ofHom φ)) :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom φ) hsurj
  have hkerApp : RingHom.ker (Spec.map (CommRingCat.ofHom φ)).appTop.hom ^ 2 = ⊥ := by
    rw [← RingHom.ker_comp_of_injective _ hiA, hNat]
    have hcomp : RingHom.ker (φ.comp (Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom) =
        Ideal.comap (Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom (RingHom.ker φ) := by
      ext x
      simp only [RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply, Ideal.mem_comap]
    rw [hcomp]
    refine le_antisymm ((Ideal.le_comap_pow _ _).trans ?_) bot_le
    rw [hker, ← RingHom.ker_eq_comap_bot]
    exact le_of_eq ((RingHom.injective_iff_ker_eq_bot _).mp hiC)
  apply Scheme.IdealSheafData.ext_of_isAffine
  change _ ^ 2 = (⊥ : Scheme.IdealSheafData (Spec (CommRingCat.of C))).ideal
    ⟨⊤, isAffineOpen_top _⟩
  rwa [Scheme.Hom.ker_apply]

/-- Any quotient of `A ⊗[R] A` has cardinality at most the maximum of `ℵ₀`, `#A` and `#R`:
the tensor product is spanned over `R` by the elementary tensors, which are indexed by
`A × A`. -/
private theorem mk_tensorQuotient_le (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (I : Ideal (A ⊗[R] A)) :
    Cardinal.mk ((A ⊗[R] A) ⧸ I) ≤
      max Cardinal.aleph0 (max (Cardinal.mk A) (Cardinal.mk R)) := by
  classical
  have hspan : Submodule.span R (Set.range (fun p : A × A => p.1 ⊗ₜ[R] p.2)) = ⊤ := by
    rw [show Set.range (fun p : A × A => p.1 ⊗ₜ[R] p.2) = {t | ∃ a b, a ⊗ₜ[R] b = t} by
      ext t; simp only [Set.mem_range, Set.mem_ofPred_eq, Prod.exists]]
    exact TensorProduct.span_tmul_eq_top R A A
  have hsurj : Function.Surjective
      (Finsupp.linearCombination R (fun p : A × A => p.1 ⊗ₜ[R] p.2)) := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination, hspan]
  have hprod : Cardinal.mk (A × A) ≤ max Cardinal.aleph0 (Cardinal.mk A) := by
    rw [Cardinal.mk_prod]
    simpa only [Cardinal.lift_id] using
      (Cardinal.mul_le_max (Cardinal.mk A) (Cardinal.mk A)).trans
        (max_le (max_le (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _))
  have hfs : Cardinal.mk ((A × A) →₀ R) ≤
      max Cardinal.aleph0 (max (Cardinal.mk A) (Cardinal.mk R)) := by
    refine (Cardinal.mk_le_of_injective (Finsupp.graph_injective (A × A) R)).trans ?_
    by_cases hInf : Infinite ((A × A) × R)
    · rw [Cardinal.mk_finset_of_infinite, Cardinal.mk_prod]
      simpa only [Cardinal.lift_id] using
        (Cardinal.mul_le_max (Cardinal.mk (A × A)) (Cardinal.mk R)).trans
          (max_le (max_le (hprod.trans (max_le_max_left _ (le_max_left _ _)))
            ((le_max_right _ _).trans (le_max_right _ _))) (le_max_left _ _))
    · have : Finite ((A × A) × R) := Finite.of_not_infinite hInf
      exact Cardinal.mk_le_aleph0.trans (le_max_left _ _)
  exact Cardinal.mk_quotient_le.trans ((Cardinal.mk_le_of_surjective hsurj).trans hfs)

/-- A ring whose cardinality is bounded by the sections of two affine schemes of the big
fppf site has spectrum again in the site, by `AlgebraicGeometry.Scheme.size_Spec`. -/
private theorem contains_Spec_of_mk_le (B : BigFppfSite.{u}) {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] (hX : B.Contains X) (hY : B.Contains Y) (C : Type u)
    [CommRing C]
    (h : Cardinal.mk C ≤ max Cardinal.aleph0 (max (Cardinal.mk Γ(X, ⊤)) (Cardinal.mk Γ(Y, ⊤)))) :
    B.Contains (Spec (CommRingCat.of C)) := by
  have hXc : Cardinal.mk Γ(X, ⊤) ≤ X.size := X.mk_sections_le_size ⟨⊤, isAffineOpen_top _⟩
  have hYc : Cardinal.mk Γ(Y, ⊤) ≤ Y.size := Y.mk_sections_le_size ⟨⊤, isAffineOpen_top _⟩
  change (Spec (CommRingCat.of C)).size < B.cutoff
  rw [Scheme.size_Spec (CommRingCat.of C)]
  exact max_lt B.aleph0_lt_cutoff (h.trans_lt (max_lt B.aleph0_lt_cutoff
    (max_lt (hXc.trans_lt hX) (hYc.trans_lt hY))))

/-- If the sections of the universal square-zero thickening of `A` over `R` are unique then
`Ω[A⁄R]` is trivial, that is, `A` is a formally unramified `R`-algebra. The sections are the
endomorphisms of `Ω[A⁄R]` by `KaehlerDifferential.endEquiv`, so uniqueness makes the
identity of `Ω[A⁄R]` equal to zero. -/
private theorem formallyUnramified_of_subsingleton_sections (R A : Type u) [CommRing R]
    [CommRing A] [Algebra R A]
    (H : Subsingleton { g // (Algebra.TensorProduct.lmul' R (S := A)).kerSquareLift.comp g
      = AlgHom.id R A }) :
    Algebra.FormallyUnramified R A := by
  have hsub : Subsingleton (Module.End A Ω[A⁄R]) :=
    (KaehlerDifferential.endEquiv R A).subsingleton
  have hid : (LinearMap.id : Ω[A⁄R] →ₗ[A] Ω[A⁄R]) = 0 := Subsingleton.elim _ _
  have hzero : ∀ x : Ω[A⁄R], x = 0 := fun x => by
    simpa using congrArg (fun k : Ω[A⁄R] →ₗ[A] Ω[A⁄R] => k x) hid
  exact ⟨⟨fun x y => (hzero x).trans (hzero y).symm⟩⟩

/-- **Stacks 04G8, the affine case, in algebra form.** Let `ψ` be a morphism of the big
fppf site over `S` whose Yoneda image is formally unramified, let `R` and `A` present the
global sections of the targets and sources of its underlying morphism of schemes, and let
`#A` be bounded by the sections of those two schemes. Then `A` is a formally unramified
`R`-algebra.

The universal square-zero thickening of `A` over `R` is `A ⊗[R] A ⧸ J ^ 2`; it lies in the
site by `AlgebraicGeometry.Space.mk_cotangentQuotient_le`, so
`AlgebraicGeometry.Space.formallyUnramified_hom_ext_of_contains` cancels the two morphisms
of schemes attached to a pair of sections, and
`AlgebraicGeometry.Space.formallyUnramified_of_subsingleton_sections` turns uniqueness of
sections into triviality of `Ω[A⁄R]`. -/
private theorem algebra_formallyUnramified_of_formallyUnramified
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {P Q : BigFppfOver B S hS} (ψ : P ⟶ Q)
    (hP : IsAffine ((BigFppfOver.toScheme B S hS).obj P))
    (hQ : IsAffine ((BigFppfOver.toScheme B S hS).obj Q))
    (hψ : FormallyUnramified (yoneda.map ψ))
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (eX : Spec (CommRingCat.of A) ≅ (BigFppfOver.toScheme B S hS).obj P)
    (eY : (BigFppfOver.toScheme B S hS).obj Q ≅ Spec (CommRingCat.of R))
    (hA : Cardinal.mk A ≤ max Cardinal.aleph0
      (max (Cardinal.mk Γ((BigFppfOver.toScheme B S hS).obj P, ⊤))
        (Cardinal.mk Γ((BigFppfOver.toScheme B S hS).obj Q, ⊤))))
    (hR : Cardinal.mk R ≤ max Cardinal.aleph0
      (max (Cardinal.mk Γ((BigFppfOver.toScheme B S hS).obj P, ⊤))
        (Cardinal.mk Γ((BigFppfOver.toScheme B S hS).obj Q, ⊤))))
    (hf : eX.hom ≫ (BigFppfOver.toScheme B S hS).map ψ ≫ eY.hom =
      Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    Algebra.FormallyUnramified R A := by
  have hPi : IsAffine ((BigFppfOver.toScheme B S hS).obj P) := hP
  have hQi : IsAffine ((BigFppfOver.toScheme B S hS).obj Q) := hQ
  have hPsize : B.Contains ((BigFppfOver.toScheme B S hS).obj P) := P.left.property
  have hQsize : B.Contains ((BigFppfOver.toScheme B S hS).obj Q) := Q.left.property
  -- the two morphisms of schemes attached to a section can be cancelled
  have H : ∀ z₁ z₂ : Spec (CommRingCat.of ((A ⊗[R] A) ⧸
        (KaehlerDifferential.ideal R A) ^ 2)) ⟶ (BigFppfOver.toScheme B S hS).obj P,
      Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.lmul' R (S := A)).kerSquareLift.toRingHom) ≫ z₁ =
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.lmul' R (S := A)).kerSquareLift.toRingHom) ≫ z₂ →
      z₁ ≫ (BigFppfOver.toScheme B S hS).map ψ =
        z₂ ≫ (BigFppfOver.toScheme B S hS).map ψ → z₁ = z₂ := by
    intro z₁ z₂ hiz hcomm
    exact formallyUnramified_hom_ext_of_contains B S hS ψ hψ
      (contains_Spec_of_mk_le B hPsize hQsize A hA)
      (contains_Spec_of_mk_le B hPsize hQsize _
        ((mk_tensorQuotient_le R A _).trans (max_le (le_max_left _ _) (max_le hA hR))))
      inferInstance inferInstance _
      (isClosedImmersion_specMap_kerSquareLift R A)
      (ker_sq_specMap_of_ker_sq _ (surjective_kerSquareLift R A)
        (ker_sq_kerSquareLift R A))
      z₁ z₂ hiz hcomm
  refine formallyUnramified_of_subsingleton_sections R A ⟨fun s c => Subtype.ext ?_⟩
  have key : ∀ (g : A →ₐ[R] ((A ⊗[R] A) ⧸ (KaehlerDifferential.ideal R A) ^ 2)),
      (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ eX.hom) ≫
          (BigFppfOver.toScheme B S hS).map ψ ≫ eY.hom =
        Spec.map (CommRingCat.ofHom (algebraMap R
          ((A ⊗[R] A) ⧸ (KaehlerDifferential.ideal R A) ^ 2))) := by
    intro g
    calc (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ eX.hom) ≫
            (BigFppfOver.toScheme B S hS).map ψ ≫ eY.hom
        = Spec.map (CommRingCat.ofHom g.toRingHom) ≫ eX.hom ≫
            (BigFppfOver.toScheme B S hS).map ψ ≫ eY.hom := by rw [Category.assoc]
      _ = Spec.map (CommRingCat.ofHom g.toRingHom) ≫
            Spec.map (CommRingCat.ofHom (algebraMap R A)) := by rw [hf]
      _ = Spec.map (CommRingCat.ofHom (algebraMap R A) ≫
            CommRingCat.ofHom g.toRingHom) := (Spec.map_comp _ _).symm
      _ = _ := congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext g.commutes))
  have hsec : ∀ (t : { g // (Algebra.TensorProduct.lmul' R (S := A)).kerSquareLift.comp g
        = AlgHom.id R A }),
      Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.lmul' R (S := A)).kerSquareLift.toRingHom) ≫
        (Spec.map (CommRingCat.ofHom t.val.toRingHom) ≫ eX.hom) = eX.hom := by
    intro t
    have hid : CommRingCat.ofHom t.val.toRingHom ≫ CommRingCat.ofHom
        (Algebra.TensorProduct.lmul' R (S := A)).kerSquareLift.toRingHom =
        𝟙 (CommRingCat.of A) :=
      CommRingCat.hom_ext (by
        simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_id]
        calc (Algebra.TensorProduct.lmul' R (S := A)).kerSquareLift.toRingHom.comp
              t.val.toRingHom
            = ((Algebra.TensorProduct.lmul' R (S := A)).kerSquareLift.comp
                t.val).toRingHom := rfl
          _ = (AlgHom.id R A).toRingHom := congrArg AlgHom.toRingHom t.property
          _ = RingHom.id A := rfl)
    calc Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.lmul' R (S := A)).kerSquareLift.toRingHom) ≫
          (Spec.map (CommRingCat.ofHom t.val.toRingHom) ≫ eX.hom)
        = Spec.map (CommRingCat.ofHom t.val.toRingHom ≫ CommRingCat.ofHom
            (Algebra.TensorProduct.lmul' R (S := A)).kerSquareLift.toRingHom) ≫ eX.hom := by
          rw [Spec.map_comp, Category.assoc]
      _ = eX.hom := by rw [hid, Spec.map_id, Category.id_comp]
  have hz := H (Spec.map (CommRingCat.ofHom s.val.toRingHom) ≫ eX.hom)
    (Spec.map (CommRingCat.ofHom c.val.toRingHom) ≫ eX.hom)
    ((hsec s).trans (hsec c).symm)
    (by
      have h1 := key s.val
      have h2 := key c.val
      refine (cancel_mono eY.hom).1 ?_
      simp only [Category.assoc] at h1 h2 ⊢
      rw [h1, h2])
  have hSpec : Spec.map (CommRingCat.ofHom s.val.toRingHom) =
      Spec.map (CommRingCat.ofHom c.val.toRingHom) := (cancel_mono eX.hom).1 hz
  have hRing : CommRingCat.ofHom s.val.toRingHom = CommRingCat.ofHom c.val.toRingHom :=
    congrArg Opposite.unop (Scheme.Spec.map_injective hSpec)
  exact AlgHom.ext fun a =>
    congrArg (fun k : A →+* _ => k a) (congrArg CommRingCat.Hom.hom hRing)

/-- **Stacks 04G8, the affine case.** For a morphism `ψ` of the big fppf site over `S`
between objects with affine underlying schemes, whose Yoneda image is formally unramified,
the induced ring map on global sections is formally unramified. -/
private theorem formallyUnramified_appTop_of_isAffine
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {P Q : BigFppfOver B S hS} (ψ : P ⟶ Q)
    (hP : IsAffine ((BigFppfOver.toScheme B S hS).obj P))
    (hQ : IsAffine ((BigFppfOver.toScheme B S hS).obj Q))
    (hψ : FormallyUnramified (yoneda.map ψ)) :
    ((BigFppfOver.toScheme B S hS).map ψ).appTop.hom.FormallyUnramified := by
  have hPi : IsAffine ((BigFppfOver.toScheme B S hS).obj P) := hP
  have hQi : IsAffine ((BigFppfOver.toScheme B S hS).obj Q) := hQ
  exact @algebra_formallyUnramified_of_formallyUnramified B S hS P Q ψ hP hQ hψ
    ↑Γ((BigFppfOver.toScheme B S hS).obj Q, ⊤)
    ↑Γ((BigFppfOver.toScheme B S hS).obj P, ⊤) _ _
    (((BigFppfOver.toScheme B S hS).map ψ).appTop.hom.toAlgebra)
    ((BigFppfOver.toScheme B S hS).obj P).isoSpec.symm
    ((BigFppfOver.toScheme B S hS).obj Q).isoSpec
    (le_max_of_le_right (le_max_left _ _))
    (le_max_of_le_right (le_max_right _ _))
    (by
      have hn := Scheme.isoSpec_hom_naturality ((BigFppfOver.toScheme B S hS).map ψ)
      rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Iso.symm_hom, ← hn,
        Iso.inv_hom_id_assoc])

/-! ### The general case -/

/-- **Stacks 04G8, from the site to schemes.** A morphism `ψ` of the big fppf site over `S`
whose Yoneda image is formally unramified in the sense of [Stacks Project, Tag 049S] has
formally unramified underlying morphism of schemes.

The pair of affine opens to be tested is placed inside the site by
`AlgebraicGeometry.Scheme.size_le_of_mono_locallyOfFinitePresentation`, since the inclusion
of an open subscheme is a monomorphism and locally of finite presentation. The resulting
objects of the site form a square of étale charts over `ψ`, so
`AlgebraicGeometry.Space.formallyUnramified_of_etaleSquare` carries the hypothesis to the
restricted morphism, and the affine case applies to it. -/
theorem formallyUnramified_map_of_formallyUnramified
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {P Q : BigFppfOver B S hS} (ψ : P ⟶ Q)
    (hψ : FormallyUnramified (yoneda.map ψ)) :
    _root_.AlgebraicGeometry.FormallyUnramified
      ((BigFppfOver.toScheme B S hS).map ψ) := by
  have hrespects : (RingHom.toMorphismProperty RingHom.FormallyUnramified).RespectsIso := by
    rw [← RingHom.toMorphismProperty_respectsIso_iff]
    exact RingHom.FormallyUnramified.respectsIso
  refine ⟨fun {U} hU {V} hV hVU => ?_⟩
  have hmV : Mono V.ι := inferInstance
  have hfV : LocallyOfFinitePresentation V.ι := inferInstance
  have hmU : Mono U.ι := inferInstance
  have hfU : LocallyOfFinitePresentation U.ι := inferInstance
  let Vobj : B.Schemes := B.obj (lt_of_le_of_lt
    (Scheme.size_le_of_mono_locallyOfFinitePresentation V.ι) P.left.property)
  let Uobj : B.Schemes := B.obj (lt_of_le_of_lt
    (Scheme.size_le_of_mono_locallyOfFinitePresentation U.ι) Q.left.property)
  let vBase : Vobj ⟶ P.left := B.inclusion.preimage V.ι
  let uBase : Uobj ⟶ Q.left := B.inclusion.preimage U.ι
  have hMapV : B.inclusion.map vBase = V.ι := B.inclusion.map_preimage _
  have hMapU : B.inclusion.map uBase = U.ι := B.inclusion.map_preimage _
  let P' : BigFppfOver B S hS := Over.mk (vBase ≫ P.hom)
  let Q' : BigFppfOver B S hS := Over.mk (uBase ≫ Q.hom)
  let a : P' ⟶ P := Over.homMk vBase rfl
  let b : Q' ⟶ Q := Over.homMk uBase rfl
  have hres : ((BigFppfOver.toScheme B S hS).map ψ).resLE U V hVU ≫ U.ι =
      V.ι ≫ (BigFppfOver.toScheme B S hS).map ψ :=
    Scheme.Hom.resLE_comp_ι _ hVU
  have htop := map_comp_inclusion_hom_eq B S hS ψ
  let fBase : P'.left ⟶ Q'.left :=
    B.inclusion.preimage (((BigFppfOver.toScheme B S hS).map ψ).resLE U V hVU)
  have hMapF : B.inclusion.map fBase =
      ((BigFppfOver.toScheme B S hS).map ψ).resLE U V hVU := B.inclusion.map_preimage _
  let ψOpen : P' ⟶ Q' := Over.homMk fBase (by
    apply B.inclusion.map_injective
    change B.inclusion.map fBase ≫ B.inclusion.map uBase ≫ B.inclusion.map Q.hom =
      B.inclusion.map vBase ≫ B.inclusion.map P.hom
    rw [hMapF, hMapU, hMapV, ← Category.assoc, hres, Category.assoc, htop])
  have hMapψOpen : (BigFppfOver.toScheme B S hS).map ψOpen =
      ((BigFppfOver.toScheme B S hS).map ψ).resLE U V hVU := hMapF
  have hchart : ∀ {X Y : BigFppfOver B S hS} (c : X ⟶ Y), Etale (B.inclusion.map c.left) →
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map c) := fun c hc =>
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@Etale.{u} : MorphismProperty Scheme.{u}) c).mpr hc
  have ha := hchart a (by change Etale (B.inclusion.map vBase); rw [hMapV]; infer_instance)
  have hb := hchart b (by change Etale (B.inclusion.map uBase); rw [hMapU]; infer_instance)
  have hdiag : yoneda.map ψOpen ≫ yoneda.map b = yoneda.map a ≫ yoneda.map ψ := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    refine congrArg yoneda.map (over_hom_ext_of_inclusion_map B S hS ?_)
    rw [Over.comp_left, Over.comp_left, Functor.map_comp, Functor.map_comp]
    change B.inclusion.map fBase ≫ B.inclusion.map uBase =
      B.inclusion.map vBase ≫ (BigFppfOver.toScheme B S hS).map ψ
    rw [hMapF, hMapU, hMapV, hres]
  have hψOpen : FormallyUnramified (yoneda.map ψOpen) :=
    formallyUnramified_of_etaleSquare B S hS (yoneda.map ψ) hψ (yoneda.map a) (yoneda.map b)
      ψOpen ha hb hdiag
  have hPaff : IsAffine ((BigFppfOver.toScheme B S hS).obj P') := hV
  have hQaff : IsAffine ((BigFppfOver.toScheme B S hS).obj Q') := hU
  have hOpen : ((BigFppfOver.toScheme B S hS).map ψOpen).appTop.hom.FormallyUnramified :=
    formallyUnramified_appTop_of_isAffine B S hS ψOpen hPaff hQaff hψOpen
  rw [hMapψOpen] at hOpen
  exact (MorphismProperty.arrow_mk_iso_iff
    (RingHom.toMorphismProperty RingHom.FormallyUnramified)
    (arrowResLEAppIso ((BigFppfOver.toScheme B S hS).map ψ) U V hVU)).mp hOpen

/-! ### The two implications of Tag 04G8 -/

/-- **Stacks 04G8, condition (1) implies condition (2).** A formally unramified morphism of
presheaves on the big fppf site of `S` is formally unramified on every commuting square of
étale scheme charts.

No algebraicity hypothesis on the source or target is needed, and none is imposed. -/
@[stacks 04G8 "condition (1) implies condition (2)"]
theorem holdsOnEveryEtaleChart_of_formallyUnramified (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hf : FormallyUnramified f) :
    HoldsOnEveryEtaleChart B S hS
      (@_root_.AlgebraicGeometry.FormallyUnramified.{u} : MorphismProperty Scheme.{u}) f :=
  fun _U _V a b h ha hb hdiag =>
    formallyUnramified_map_of_formallyUnramified B S hS h
      (formallyUnramified_of_etaleSquare B S hS f hf a b h ha hb hdiag)

/-- **Stacks 04G8, condition (2) implies condition (3).** If a morphism of algebraic spaces
over `S` is formally unramified on every commuting square of étale scheme charts, then
there is one such square whose two chart morphisms are in addition surjective.

The square is produced from a surjective étale chart of the target, which exists by
`AlgebraicGeometry.IsAlgebraicSpace.exists_atlas`, and its lift to the source, which is
[Stacks Project, Tag 02X1]. -/
@[stacks 04G8 "condition (2) implies condition (3)"]
theorem exists_surjectiveEtaleChart_of_holdsOnEveryEtaleChart (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hall : HoldsOnEveryEtaleChart B S hS
      (@_root_.AlgebraicGeometry.FormallyUnramified.{u} : MorphismProperty Scheme.{u}) f) :
    ∃ (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (h : U ⟶ V),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf b ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf b ∧
      yoneda.map h ≫ b = a ≫ f ∧
      _root_.AlgebraicGeometry.FormallyUnramified
        ((BigFppfOver.toScheme B S hS).map h) := by
  obtain ⟨V, b, hbSurj, hbEtale⟩ := hY.exists_atlas
  obtain ⟨U, a, α, hdiag, haSurj, haEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hY f V b hbSurj hbEtale
  exact ⟨U, V, a, b, α, haEtale, hbEtale, haSurj, hbSurj, hdiag.symm,
    hall U V a b α haEtale hbEtale hdiag.symm⟩

end AlgebraicGeometry.Space

end
