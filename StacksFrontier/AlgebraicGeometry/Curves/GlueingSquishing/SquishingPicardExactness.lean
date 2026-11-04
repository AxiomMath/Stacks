module

public import StacksFrontier.AlgebraicGeometry.Picard.FirstCohomologyNaturality

/-!
# Exactness at the Picard group of the sequence of a squishing

Let `k` be an algebraically closed field and let `f : X' ⟶ X` squish the tangent vector `θ` of
an algebraic `k`-scheme `X'`, in the sense of `AlgebraicGeometry.IsSquishingTangentVector`.
[Stacks, Tag 0C1N] records the exact sequence

`(k, +) ⟶ Pic(X) ⟶ Pic(X') ⟶ 0`,

whose first map is the tangent homomorphism
`Stacks.SquishSheafSequence.picardTangentHom` and whose second is pullback of Picard classes.
Surjectivity on the right is `Stacks.SquishPicard.surjective_schemePullbackClassHom`
and injectivity on the left for a proper reduced `X'` is
`Stacks.SquishSheafSequence.injective_picardTangentHom_of_isProper_of_isReduced`.  **This file
proves exactness in the middle**: a Picard class of `X` pulls back to zero on `X'` exactly when
it comes from a scalar.

The argument is the one of the source.  Taking cohomology over the whole space of the short
exact sequence of sheaves of units

`1 ⟶ 𝒪_X^* ⟶ f_*𝒪_{X'}^* ⟶ (k, +)_x ⟶ 1`

gives `H⁰(X, f_*𝒪_{X'}^*) ⟶ k ⟶ H¹(X, 𝒪_X^*) ⟶ H¹(X, f_*𝒪_{X'}^*)`, so the kernel of the
third map is the image of the connecting map.  The first Leray edge map
`H¹(X, f_*𝒪_{X'}^*) ⟶ H¹(X', 𝒪_{X'}^*)` is injective, so that kernel is also the kernel of the
composite, and the composite is pullback of Picard classes by the naturality of
[Stacks, Tag 09NU] in a morphism of schemes.

## Main results

* `Stacks.SquishSheafSequence.h1NativeUnitsPullback_eq_zero_iff` — the composite of
  `𝒪_X^* ⟶ f_*𝒪_{X'}^*` with the first Leray edge map has the same kernel as the first map
  alone, the edge map being injective.
* `Stacks.SquishSheafSequence.h1map_unitsPushforwardMap_eq_zero_iff` — exactness of the long
  exact cohomology sequence of the units sequence at `H¹(X, 𝒪_X^*)`.
* `Stacks.SquishSheafSequence.exists_apply_eq_iff_of_eq_inv_comp` — precomposing a morphism of
  abelian groups with two isomorphisms does not change its image.  This is the step that reads
  the image of the connecting map of the long exact sequence as the image of
  `Stacks.SquishSheafSequence.connectingHom`; it mentions nothing of the squishing, and the
  glueing sequence of [Stacks, Tag 0C1J] uses it as it stands.
* `Stacks.SquishSheafSequence.schemePullbackClassHom_eq_zero_iff_exists_picardTangentHom` —
  **exactness at `Pic(X)`**, the kernel of pullback being the range of the tangent
  homomorphism.
* `Stacks.SquishSheafSequence.exact_picardTangentHom_schemePullbackClassHom` — the same, in the
  `Function.Exact` spelling.

## References

* [Stacks Project, Tag 0C1N](https://stacks.math.columbia.edu/tag/0C1N)
* [Stacks Project, Tag 0C1K](https://stacks.math.columbia.edu/tag/0C1K)
* [Stacks Project, Tag 09NU](https://stacks.math.columbia.edu/tag/09NU)
* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.SquishSheafSequence

open Stacks.GlueSquishUnits (ringPushforwardMap unitsPushforwardMap unitsPushforwardMap_app)
open Stacks.Cohomology.Generators (unitsSheaf)
open Stacks.Cohomology.AbelianColimit (abSections H'functor H'δ shortComplex_H'_exact₁)
open Stacks.Cohomology.LerayLowDegree (abelianCohomology abelianPushforward abelianEdgeMap
  abelianEdgeMap_injective abelianSheafHasSheafify)
open Stacks.GluePicard (h0Iso h1Iso h1UnitsAddEquivOfScheme)
open Stacks.Picard.FirstCohomology (h1NativeUnitsPullback h1UnitsAddEquivOfScheme_naturality)

attribute [local instance] abelianSheafHasSheafify

/-! ### Vanishing under injective maps of abelian groups -/

/-- An injective morphism of abelian groups vanishes only at zero. -/
private theorem apply_eq_zero_iff_of_injective {A B : AddCommGrpCat.{u}} (g : A ⟶ B)
    (hg : Function.Injective g) (x : A) : g x = 0 ↔ x = 0 :=
  map_eq_zero_iff (ConcreteCategory.hom g) hg

/-- The forward map of an isomorphism of abelian groups vanishes only at zero. -/
private theorem iso_hom_apply_eq_zero_iff {A B : AddCommGrpCat.{u}} (e : A ≅ B) (x : A) :
    e.hom x = 0 ↔ x = 0 :=
  apply_eq_zero_iff_of_injective e.hom (ConcreteCategory.bijective_of_isIso e.hom).1 x

/-- The backward map of an isomorphism of abelian groups vanishes only at zero. -/
private theorem iso_inv_apply_eq_zero_iff {A B : AddCommGrpCat.{u}} (e : A ≅ B) (x : B) :
    e.inv x = 0 ↔ x = 0 :=
  iso_hom_apply_eq_zero_iff e.symm x

/-! ### Images under two isomorphisms -/

/-- **A morphism of abelian groups obtained from another one by composing with the inverses of
two isomorphisms is carried back to it by those two isomorphisms.**  The derived morphism is
taken as a parameter together with its factorization, so that the statement is about the name it
is given rather than about its unfolding. -/
theorem comp_eq_of_eq_inv_comp {A B D E : AddCommGrpCat.{u}} (e₁ : A ≅ B) (e₂ : B ≅ D)
    (g : A ⟶ E) (conn : D ⟶ E) (hconn : conn = e₂.inv ≫ e₁.inv ≫ g) :
    (e₁.hom ≫ e₂.hom) ≫ conn = g := by
  rw [hconn, Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc]

/-- **Precomposing a morphism of abelian groups with two isomorphisms does not change its
image.**  This is the bookkeeping that reads the image of the connecting map of a long exact
cohomology sequence, whose source is degree-zero cohomology of the quotient sheaf, as the image
of a connecting map whose source is the group that two isomorphisms identify that cohomology
with. -/
theorem exists_apply_eq_iff_of_eq_inv_comp {A B D E : AddCommGrpCat.{u}} (e₁ : A ≅ B)
    (e₂ : B ≅ D) (g : A ⟶ E) (conn : D ⟶ E) (hconn : conn = e₂.inv ≫ e₁.inv ≫ g) (c : E) :
    (∃ t : A, g t = c) ↔ ∃ d : D, conn d = c := by
  have hinv : (e₂.inv ≫ e₁.inv) ≫ g = conn := by
    rw [hconn, Category.assoc]
  refine ⟨fun ht => ?_, fun hd => ?_⟩
  · obtain ⟨t, ht⟩ := ht
    exact ⟨(e₁.hom ≫ e₂.hom) t,
      (ConcreteCategory.congr_hom (comp_eq_of_eq_inv_comp e₁ e₂ g conn hconn) t).trans ht⟩
  · obtain ⟨d, hd⟩ := hd
    exact ⟨e₁.inv (e₂.inv d), (ConcreteCategory.congr_hom hinv d).trans hd⟩

/-! ### The kernel of pullback on first cohomology of the units sheaf -/

section Leray

variable {X' X : Scheme.{u}}

/-- **Pullback on native first cohomology of the sheaf of units has the same kernel as the map
induced by `𝒪_X^* ⟶ f_*𝒪_{X'}^*`.**  The two differ by the first Leray edge map, which is
injective, and by the comparison of native cohomology with right-derived sections, which is an
isomorphism. -/
theorem h1NativeUnitsPullback_eq_zero_iff (f : X' ⟶ X)
    (c : (H'functor (X := (X : Type u)) ⊤ 1).obj (unitsSheaf X.toRingedSpace)) :
    h1NativeUnitsPullback f c = 0 ↔
      (H'functor (X := (X : Type u)) ⊤ 1).map (unitsPushforwardMap f) c = 0 := by
  have hnat := ConcreteCategory.congr_hom
    ((h1Iso (X : Type u)).hom.naturality (unitsPushforwardMap f)) c
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hnat
  have hstep : h1NativeUnitsPullback f c =
      ((h1Iso (X' : Type u)).app (unitsSheaf X'.toRingedSpace)).inv
        ((abelianEdgeMap.{u, u} f.base 1).app (unitsSheaf X'.toRingedSpace)
          (((h1Iso (X : Type u)).app
              ((abelianPushforward.{u, u} f.base).obj (unitsSheaf X'.toRingedSpace))).hom
            ((H'functor (X := (X : Type u)) ⊤ 1).map (unitsPushforwardMap f) c))) :=
    congrArg
      (fun y => ((h1Iso (X' : Type u)).app (unitsSheaf X'.toRingedSpace)).inv
        ((abelianEdgeMap.{u, u} f.base 1).app (unitsSheaf X'.toRingedSpace) y))
      hnat.symm
  rw [hstep]
  refine Iff.trans (iso_inv_apply_eq_zero_iff
    ((h1Iso (X' : Type u)).app (unitsSheaf X'.toRingedSpace)) _) ?_
  refine Iff.trans (apply_eq_zero_iff_of_injective
    ((abelianEdgeMap.{u, u} f.base 1).app (unitsSheaf X'.toRingedSpace))
    (abelianEdgeMap_injective.{u, u} f.base (unitsSheaf X'.toRingedSpace)) _) ?_
  exact iso_hom_apply_eq_zero_iff
    ((h1Iso (X : Type u)).app
      ((abelianPushforward.{u, u} f.base).obj (unitsSheaf X'.toRingedSpace)))
    ((H'functor (X := (X : Type u)) ⊤ 1).map (unitsPushforwardMap f) c)

end Leray

/-! ### Exactness of the cohomology sequence -/

section Exactness

variable {k : Type u} [Field k] [IsAlgClosed k] {X' X : Scheme.{u}}
  [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]

/-- The connecting map of the long exact sequence followed by the map induced by
`𝒪_X^* ⟶ f_*𝒪_{X'}^*` on first cohomology is zero. -/
private theorem H'δ_comp_h1map_eq_zero (f : X' ⟶ X)
    (θ : Spec (.of (DualNumber k)) ⟶ X')
    (h : AlgebraicGeometry.IsSquishingTangentVector f θ) :
    H'δ (unitsComplex_shortExact f θ h) (⊤ : Opens (X : Type u)) (zero_add 1) ≫
        (H'functor (X := (X : Type u)) ⊤ 1).map (unitsComplex f θ h).f = 0 := by
  rw [Stacks.Cohomology.AbelianColimit.H'δ_eq_postcomp_extClass,
    Stacks.Cohomology.AbelianColimit.H'map_eq_postcomp_mk₀]
  exact Stacks.Cohomology.AbelianColimit.postcomp_extClass_comp_postcomp_mk₀_f
    (unitsComplex_shortExact f θ h) (⊤ : Opens (X : Type u)) (zero_add 1)

/-- **Exactness at `H¹(X, 𝒪_X^*)` of the long exact cohomology sequence of the units sequence
of a squishing**: a class killed by the map induced by `𝒪_X^* ⟶ f_*𝒪_{X'}^*` is the image of a
degree-zero class of the skyscraper under the connecting map. -/
theorem h1map_unitsPushforwardMap_eq_zero_iff (f : X' ⟶ X)
    (θ : Spec (.of (DualNumber k)) ⟶ X')
    (h : AlgebraicGeometry.IsSquishingTangentVector f θ)
    (c : (H'functor (X := (X : Type u)) ⊤ 1).obj (unitsSheaf X.toRingedSpace)) :
    (H'functor (X := (X : Type u)) ⊤ 1).map (unitsPushforwardMap f) c = 0 ↔
      ∃ t : (H'functor (X := (X : Type u)) ⊤ 0).obj (unitsComplex f θ h).X₃,
        H'δ (unitsComplex_shortExact f θ h) (⊤ : Opens (X : Type u)) (zero_add 1) t = c := by
  refine ⟨fun hc => ?_, fun ht => ?_⟩
  · exact (ShortComplex.ab_exact_iff _).1
      (shortComplex_H'_exact₁ (unitsComplex_shortExact f θ h)
        (⊤ : Opens (X : Type u)) (zero_add 1)) c hc
  · obtain ⟨t, rfl⟩ := ht
    exact (ConcreteCategory.comp_apply
      (H'δ (unitsComplex_shortExact f θ h) (⊤ : Opens (X : Type u)) (zero_add 1))
      ((H'functor (X := (X : Type u)) ⊤ 1).map (unitsComplex f θ h).f) t).symm.trans
      (ConcreteCategory.congr_hom (H'δ_comp_h1map_eq_zero f θ h) t)

/-- **The kernel of pullback on native first cohomology of the sheaf of units is the image of
the connecting map** of the units sequence of a squishing. -/
theorem h1NativeUnitsPullback_eq_zero_iff_exists_connectingHom (f : X' ⟶ X)
    (θ : Spec (.of (DualNumber k)) ⟶ X')
    (h : AlgebraicGeometry.IsSquishingTangentVector f θ)
    (c : (H'functor (X := (X : Type u)) ⊤ 1).obj (unitsSheaf X.toRingedSpace)) :
    h1NativeUnitsPullback f c = 0 ↔ ∃ a : k, connectingHom f θ h a = c :=
  (h1NativeUnitsPullback_eq_zero_iff f c).trans
    ((h1map_unitsPushforwardMap_eq_zero_iff f θ h c).trans
      (exists_apply_eq_iff_of_eq_inv_comp ((h0Iso (X : Type u)).app (unitsComplex f θ h).X₃)
        (sequenceTopIso f θ h)
        (H'δ (unitsComplex_shortExact f θ h) (⊤ : Opens (X : Type u)) (zero_add 1))
        (connectingHom f θ h) rfl c))

/-! ### Exactness at the Picard group -/

/-- **Exactness at `Pic(X)` of the sequence of [Stacks, Tag 0C1N].**  For `k` algebraically
closed and `f : X' ⟶ X` the squishing of the tangent vector `θ` of `X'`, a Picard class of `X`
pulls back to zero on `X'` exactly when it is the value of the tangent homomorphism
`Stacks.SquishSheafSequence.picardTangentHom` at a scalar; that is, the kernel of
`Pic(X) ⟶ Pic(X')` is the image of `(k, +) ⟶ Pic(X)`. -/
@[stacks 0C1N "exactness"]
theorem schemePullbackClassHom_eq_zero_iff_exists_picardTangentHom (f : X' ⟶ X)
    (θ : Spec (.of (DualNumber k)) ⟶ X')
    (h : AlgebraicGeometry.IsSquishingTangentVector f θ) (L : Stacks.Picard.ofScheme X) :
    Stacks.Picard.schemePullbackClassHom f L = 0 ↔
      ∃ a : k, picardTangentHom f θ h a = L := by
  have hc : h1UnitsAddEquivOfScheme X ((h1UnitsAddEquivOfScheme X).symm L) = L :=
    (h1UnitsAddEquivOfScheme X).apply_symm_apply L
  have hpull : Stacks.Picard.schemePullbackClassHom f L =
      h1UnitsAddEquivOfScheme X'
        (h1NativeUnitsPullback f ((h1UnitsAddEquivOfScheme X).symm L)) :=
    ((h1UnitsAddEquivOfScheme_naturality f ((h1UnitsAddEquivOfScheme X).symm L)).trans
      (congrArg (fun y => Stacks.Picard.schemePullbackClassHom f y) hc)).symm
  have hrange : (∃ a : k, picardTangentHom f θ h a = L) ↔
      ∃ a : k, connectingHom f θ h a = (h1UnitsAddEquivOfScheme X).symm L := by
    refine exists_congr fun a => ?_
    refine Iff.trans ?_ ((h1UnitsAddEquivOfScheme X).apply_eq_iff_eq (x := _) (y := _))
    rw [picardTangentHom_apply, hc]
    exact Iff.rfl
  rw [hpull, AddEquiv.map_eq_zero_iff, hrange]
  exact h1NativeUnitsPullback_eq_zero_iff_exists_connectingHom f θ h _

/-- **Exactness at `Pic(X)` of the sequence of [Stacks, Tag 0C1N]**, in the `Function.Exact`
spelling: the kernel of pullback of Picard classes is the range of the tangent homomorphism. -/
@[stacks 0C1N "exactness"]
theorem exact_picardTangentHom_schemePullbackClassHom (f : X' ⟶ X)
    (θ : Spec (.of (DualNumber k)) ⟶ X')
    (h : AlgebraicGeometry.IsSquishingTangentVector f θ) :
    Function.Exact (picardTangentHom f θ h) (Stacks.Picard.schemePullbackClassHom f) :=
  fun L => (schemePullbackClassHom_eq_zero_iff_exists_picardTangentHom f θ h L).trans
    Set.mem_range.symm

end Exactness

end Stacks.SquishSheafSequence

end
