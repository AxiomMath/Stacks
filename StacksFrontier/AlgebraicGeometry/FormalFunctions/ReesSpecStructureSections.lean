module

public import StacksFrontier.AlgebraicGeometry.FormalFunctions.SpecReesRelativeSpec
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.ReesComapLocallySurjective
public import StacksFrontier.AlgebraicGeometry.RelativeSpecBaseChange.AffineBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.RelativeSpecCriterion
public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.Basic

/-!
# The closed immersion `X' ⟶ Spec(B) ×_{Spec A} X`, with its algebra map computed

[Stacks, Tag 0897]'s base change needs the structure morphism `f' : X' ⟶ Spec B`, and
`cmp` needs the ring map `specAlgebraRingHom B f' : B →+* Γ(X', ⊤)` it induces on global
sections. `Stacks.Cohomology.FormalFunctions.reesRelativeSpecToPullback` produces such an `f'`,
but its algebra map cannot be computed: it is built from
`Stacks.AffineAlgebraEquivalence.relativeSpecBaseChangeIso`, hence from `overRelativeSpecIso`
and `relativeSpecOverIso`, and none of those has any characterisation on sections.

This file builds the closed immersion again, the other way round: out of
`Stacks.AffineAlgebraEquivalence.overHomOfAlgebraHom`, whose defining property
`pushforwardAlgebraMap_overHomOfAlgebraHom` says exactly what algebra map it induces. The
comparison of the base change with the relative spectrum of `f^* B̃` is
`AlgebraicGeometry.relativeSpecOverIsoOfAlgebraIso`, which is built the same way, so its
algebra map is computed too.

## Main definitions

* `Stacks.Cohomology.FormalFunctions.reesPullbackAlgebra`: `f^* B̃`.
* `Stacks.Cohomology.FormalFunctions.reesPullbackAlgebraIso`:
  **`f^* B̃ ≅ pr₂_* 𝒪_{Spec(B) ×_{Spec A} X}`**, the base-change comparison of [Stacks, Tag 01SA]
  at the Rees algebra.
* `Stacks.Cohomology.FormalFunctions.reesClosedImmersion`: **`X' ⟶ Spec(B) ×_{Spec A} X`**.

## Main results

* `Stacks.Cohomology.FormalFunctions.isClosedImmersion_reesClosedImmersion`: it is a closed
  immersion, because `Stacks.Cohomology.FormalFunctions.baseReesComapPullbackHom` is locally
  surjective.
* `Stacks.Cohomology.FormalFunctions.pushforwardAlgebraMap_reesClosedImmersionOver`: **its
  algebra map is `ψ`**, between the two identifications.
* `Stacks.Cohomology.FormalFunctions.appTop_reesClosedImmersion`: its ring map on global
  sections is the `⊤`-component of that algebra map.
* `Stacks.Cohomology.FormalFunctions.appTop_pullbackFst`: the ring map of the projection
  `Spec(B) ×_{Spec A} X ⟶ Spec B` on global sections is the algebra-pullback unit followed by
  the base-change comparison of [Stacks, Tag 01SA].
* `Stacks.Cohomology.FormalFunctions.appTop_reesSpecStructure`: **the ring map of
  `f' : X' ⟶ Spec B` on global sections is the algebra-pullback unit followed by `ψ`**, which is
  the form `Stacks.Blowup.reesComapPullbackHom_app_unit` computes.

## Implementation notes

`Stacks.Cohomology.FormalFunctions.reesPullbackAlgebraIso` and
`Stacks.Cohomology.FormalFunctions.reesPullbackRelativeSpecIso` are made locally irreducible
after the one `rfl` that needs to see through them: a `rw` whose motive mentions either of them
unfolded makes the kernel time out.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 01S8](https://stacks.math.columbia.edu/tag/01S8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Blowup Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence
open Stacks.AlgebraicGeometry.GradedProperCohomology
open scoped DirectSum

universe u

namespace Stacks.Cohomology.FormalFunctions

variable {A : Type u} [CommRing A] (I : Ideal A) (X : Over (Spec (.of A)))

/-- `Spec B ⟶ Spec A` is affine. -/
instance isAffineHom_reesSpecToBase : AlgebraicGeometry.IsAffineHom (reesSpecToBase I) :=
  inferInstance

/-- Hence so is the projection of the base change `Spec(B) ×_{Spec A} X ⟶ X`. -/
instance isAffineHom_pullbackSnd_reesSpecToBase :
    AlgebraicGeometry.IsAffineHom
      (pullback.snd (Over.mk (reesSpecToBase I)).hom X.hom) :=
  isAffineHom_pullback_hom X.hom (reesSpecToBase I)

/-- `f^* B̃`, the algebra pullback of the Rees algebra sheaf of `Spec A` along `f : X ⟶ Spec A`.
This is the sheaf of `𝒪_X`-algebras whose relative spectrum is the honest base change
`Spec(B) ×_{Spec A} X`. -/
abbrev reesPullbackAlgebra : AlgebraSheaf X.left :=
  (algebraPullback X.hom).obj (specReesAlgebraSheaf I)

/-- **`f^* B̃ ≅ pr₂_* 𝒪_{Spec(B) ×_{Spec A} X}`**: the base-change comparison of
[Stacks, Tag 01SA], composed with the identification of `B̃` with the pushed-forward structure
sheaf of `Spec B ⟶ Spec A`. -/
def reesPullbackAlgebraIso :
    reesPullbackAlgebra I X ≅
      pushforwardAlgebra ((Over.pullback X.hom).obj (Over.mk (reesSpecToBase I))).hom :=
  haveI := isIso_baseChangeAlgebraHom X.hom (Over.mk (reesSpecToBase I))
  (algebraPullback X.hom).mapIso (specReesAlgebraSheafIso I) ≪≫
    asIso (baseChangeAlgebraHom X.hom (Over.mk (reesSpecToBase I)))

/-- The base-change comparison cancels the first factor of `reesPullbackAlgebraIso`. -/
theorem baseChangeAlgebraHom_comp_reesPullbackAlgebraIso_inv :
    baseChangeAlgebraHom X.hom (Over.mk (reesSpecToBase I)) ≫ (reesPullbackAlgebraIso I X).inv =
      (algebraPullback X.hom).map (specReesAlgebraSheafIso I).inv :=
  have := isIso_baseChangeAlgebraHom X.hom (Over.mk (reesSpecToBase I))
  Iso.hom_inv_id_assoc (asIso (baseChangeAlgebraHom X.hom (Over.mk (reesSpecToBase I))))
    ((algebraPullback X.hom).mapIso (specReesAlgebraSheafIso I)).inv

/-- **The honest base change `Spec(B) ×_{Spec A} X` is the relative spectrum of `f^* B̃`**, as an
isomorphism over `X` whose algebra map is `reesPullbackAlgebraIso` — which is what makes the ring
map of the closed immersion below computable. -/
def reesPullbackRelativeSpecIso :
    ((Over.pullback X.hom).obj (Over.mk (reesSpecToBase I)) : Over X.left) ≅
      Over.mk (relativeSpecToBase (reesPullbackAlgebra I X)) :=
  relativeSpecOverIsoOfAlgebraIso _ (reesPullbackAlgebra I X)
    (reesPullbackAlgebraIso I X).symm

/-- **`X' = Spec_X(⨁ₙ ℐⁿ) ⟶ Spec(B) ×_{Spec A} X`**, as a morphism over `X`. -/
def reesClosedImmersionOver :
    (Over.mk (relativeSpecToBase (reesAlgebraSheaf (baseIdealSheaf A I X.hom))) : Over X.left) ⟶
      (Over.pullback X.hom).obj (Over.mk (reesSpecToBase I)) :=
  relativeSpecMapOfAlgebraHom (reesPullbackAlgebra I X)
      (reesAlgebraSheaf (baseIdealSheaf A I X.hom)) (baseReesComapPullbackHom I X) ≫
    (reesPullbackRelativeSpecIso I X).inv

/-- **`X' ⟶ Spec(B) ×_{Spec A} X`.** -/
def reesClosedImmersion : (reesRelativeSpec I X).left ⟶ pullback (reesSpecToBase I) X.hom :=
  (reesClosedImmersionOver I X).left

/-- **It is a closed immersion**: the first factor is one because
`Stacks.Cohomology.FormalFunctions.baseReesComapPullbackHom` is locally surjective, and the
second is an isomorphism. -/
theorem isClosedImmersion_reesClosedImmersion :
    AlgebraicGeometry.IsClosedImmersion (reesClosedImmersion I X) :=
  have hci := Stacks.RelativeSpecClosedImmersion.isClosedImmersion_relativeSpecMapOfAlgebraHom
    (reesPullbackAlgebra I X) (reesAlgebraSheaf (baseIdealSheaf A I X.hom))
    (baseReesComapPullbackHom I X) (isLocallySurjective_baseReesComapPullbackHom I X)
  have : IsIso (reesPullbackRelativeSpecIso I X).inv.left :=
    show IsIso ((Over.forget X.left).map (reesPullbackRelativeSpecIso I X).inv) from
      inferInstance
  @AlgebraicGeometry.IsClosedImmersion.comp _ _ _ _ _ hci inferInstance

/-- The inverse of the comparison is the morphism `fromRelativeSpecOfAlgebraIso` of
[Stacks, Tag 01S8], whose algebra map is computed. -/
theorem reesPullbackRelativeSpecIso_inv :
    (reesPullbackRelativeSpecIso I X).inv =
      fromRelativeSpecOfAlgebraIso _ (reesPullbackAlgebra I X)
        (reesPullbackAlgebraIso I X).symm :=
  rfl

attribute [local irreducible] reesPullbackAlgebraIso reesPullbackRelativeSpecIso

/-- The algebra map of the closed immersion, split at its two factors. -/
theorem pushforwardAlgebraMap_reesClosedImmersionOver_comp :
    pushforwardAlgebraMap (reesClosedImmersionOver I X) =
      pushforwardAlgebraMap ((reesPullbackRelativeSpecIso I X).inv) ≫
        pushforwardAlgebraMap (relativeSpecMapOfAlgebraHom (reesPullbackAlgebra I X)
          (reesAlgebraSheaf (baseIdealSheaf A I X.hom)) (baseReesComapPullbackHom I X)) :=
  pushforwardAlgebraMap_comp _ _

/-- The algebra map of the comparison with the relative spectrum of `f^* B̃`. -/
theorem pushforwardAlgebraMap_reesPullbackRelativeSpecIso_inv :
    pushforwardAlgebraMap ((reesPullbackRelativeSpecIso I X).inv) =
      (reesPullbackAlgebraIso I X).symm.hom ≫
        (pushforwardAlgebraIso (reesPullbackAlgebra I X)).inv :=
  (congrArg (fun u => pushforwardAlgebraMap u) (reesPullbackRelativeSpecIso_inv I X)).trans
    (pushforwardAlgebraMap_fromRelativeSpecOfAlgebraIso _ (reesPullbackAlgebra I X)
      (reesPullbackAlgebraIso I X).symm)

/-- The algebra map of the relative spectrum of `ψ` is `ψ`. -/
theorem pushforwardAlgebraMap_relativeSpecMap_baseReesComapPullbackHom :
    pushforwardAlgebraMap (relativeSpecMapOfAlgebraHom (reesPullbackAlgebra I X)
        (reesAlgebraSheaf (baseIdealSheaf A I X.hom)) (baseReesComapPullbackHom I X)) =
      (pushforwardAlgebraIso (reesPullbackAlgebra I X)).hom ≫
        baseReesComapPullbackHom I X ≫
        (pushforwardAlgebraIso (reesAlgebraSheaf (baseIdealSheaf A I X.hom))).inv :=
  pushforwardAlgebraMap_relativeSpecMapOfAlgebraHom _ _ _

/-- **The algebra map of the closed immersion is `ψ`**, between the two identifications. This is
the point of building the closed immersion out of `overHomOfAlgebraHom`: its ring map on global
sections is then computable, and nothing about
`Stacks.AffineAlgebraEquivalence.pushforwardAlgebraIso` at the open `⊤` is needed. -/
theorem pushforwardAlgebraMap_reesClosedImmersionOver :
    pushforwardAlgebraMap (reesClosedImmersionOver I X) =
      (reesPullbackAlgebraIso I X).inv ≫ baseReesComapPullbackHom I X ≫
        (pushforwardAlgebraIso (reesAlgebraSheaf (baseIdealSheaf A I X.hom))).inv := by
  rw [pushforwardAlgebraMap_reesClosedImmersionOver_comp,
    pushforwardAlgebraMap_reesPullbackRelativeSpecIso_inv,
    pushforwardAlgebraMap_relativeSpecMap_baseReesComapPullbackHom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc]

/-- The ring map of the closed immersion on global sections is the `⊤`-component of its algebra
map. -/
theorem appTop_reesClosedImmersion :
    (pushforwardAlgebraMap (reesClosedImmersionOver I X)).right.hom.app (op ⊤) =
      (reesClosedImmersion I X).appTop := by
  rw [pushforwardAlgebraMap_app (reesClosedImmersionOver I X) ⊤
    (preimage_le_preimage_preimage _ _)]
  exact (reesClosedImmersion I X).appLE_eq_app

/-- The canonical map attached to the fibre-product projection is the adjunct of the base-change
comparison; this is how that comparison was defined. -/
theorem homEquiv_baseChangeAlgebraHom :
    pushforwardAlgebraMap (baseChangeProjection X.hom (Over.mk (reesSpecToBase I))) =
      (algebraPullbackPushforwardAdjunction X.hom).homEquiv _ _
        (baseChangeAlgebraHom X.hom (Over.mk (reesSpecToBase I))) :=
  (((algebraPullbackPushforwardAdjunction X.hom).homEquiv
      (pushforwardAlgebra (Over.mk (reesSpecToBase I)).hom)
      (pushforwardAlgebra
        ((Over.pullback X.hom).obj (Over.mk (reesSpecToBase I))).hom)).apply_symm_apply
    (pushforwardAlgebraMap (baseChangeProjection X.hom (Over.mk (reesSpecToBase I))))).symm

/-- **The ring map of the projection `Spec(B) ×_{Spec A} X ⟶ Spec B` on global sections**: the
unit of the algebra-pullback adjunction, followed by the base-change comparison. -/
theorem appTop_pullbackFst :
    (pullback.fst (Over.mk (reesSpecToBase I)).hom X.hom).appTop =
      ((algebraPullbackPushforwardAdjunction X.hom).unit.app
          (pushforwardAlgebra (Over.mk (reesSpecToBase I)).hom)).right.hom.app (op ⊤) ≫
        (baseChangeAlgebraHom X.hom (Over.mk (reesSpecToBase I))).right.hom.app (op ⊤) := by
  rw [← pushforwardAlgebraMap_baseChangeProjection_app_top X.hom (Over.mk (reesSpecToBase I)),
    homEquiv_baseChangeAlgebraHom, Adjunction.homEquiv_unit]
  rfl

/-- **The ring map of the closed immersion on global sections** is `ψ`, between the two
identifications. -/
theorem appTop_reesClosedImmersion_eq :
    (reesClosedImmersion I X).appTop =
      (reesPullbackAlgebraIso I X).inv.right.hom.app (op ⊤) ≫
        (baseReesComapPullbackHom I X).right.hom.app (op ⊤) ≫
        (pushforwardAlgebraIso
          (reesAlgebraSheaf (baseIdealSheaf A I X.hom))).inv.right.hom.app (op ⊤) := by
  rw [← appTop_reesClosedImmersion, pushforwardAlgebraMap_reesClosedImmersionOver]
  rfl

/-- The unit of the algebra-pullback adjunction is natural in the algebra sheaf, read at `⊤`. -/
theorem unit_app_top_naturality :
    ((algebraPullbackPushforwardAdjunction X.hom).unit.app
          (pushforwardAlgebra (Over.mk (reesSpecToBase I)).hom)).right.hom.app (op ⊤) ≫
        ((algebraPullback X.hom).map (specReesAlgebraSheafIso I).inv).right.hom.app (op ⊤) =
      (specReesAlgebraSheafIso I).inv.right.hom.app (op ⊤) ≫
        ((algebraPullbackPushforwardAdjunction X.hom).unit.app
          (specReesAlgebraSheaf I)).right.hom.app (op ⊤) :=
  congrArg (fun φ => φ.right.hom.app (op ⊤))
    ((algebraPullbackPushforwardAdjunction X.hom).unit.naturality
      (specReesAlgebraSheafIso I).inv).symm

/-- A rearrangement of five composable morphisms, proved in an abstract category: at the
concrete types below `simp` and `rw` cannot associate the composites, because the underlying
space of a scheme has two spellings. -/
private theorem comp_rearrange {C : Type*} [Category C] {w x y z t v : C}
    (u : w ⟶ x) (bc : x ⟶ y) (pinv : y ⟶ z) (au : x ⟶ z) (sinv : w ⟶ v) (uf : v ⟶ z)
    (rest : z ⟶ t) (h1 : bc ≫ pinv = au) (h2 : u ≫ au = sinv ≫ uf) :
    (u ≫ bc) ≫ (pinv ≫ rest) = sinv ≫ uf ≫ rest := by
  rw [← Category.assoc sinv uf rest, ← h2, ← h1]
  simp only [Category.assoc]

/-- **The ring map of `f' : X' ⟶ Spec B` on global sections**, reduced to the algebra-pullback
unit followed by `ψ`. This is the form `Stacks.Blowup.reesComapPullbackHom_app_unit` computes. -/
theorem appTop_reesSpecStructure :
    (reesClosedImmersion I X ≫
        pullback.fst (Over.mk (reesSpecToBase I)).hom X.hom).appTop =
      (specReesAlgebraSheafIso I).inv.right.hom.app (op ⊤) ≫
        ((algebraPullbackPushforwardAdjunction X.hom).unit.app
          (specReesAlgebraSheaf I)).right.hom.app (op ⊤) ≫
        (baseReesComapPullbackHom I X).right.hom.app (op ⊤) ≫
        (pushforwardAlgebraIso
          (reesAlgebraSheaf (baseIdealSheaf A I X.hom))).inv.right.hom.app (op ⊤) := by
  have h1 : (baseChangeAlgebraHom X.hom (Over.mk (reesSpecToBase I))).right.hom.app (op ⊤) ≫
      (reesPullbackAlgebraIso I X).inv.right.hom.app (op ⊤) =
      ((algebraPullback X.hom).map (specReesAlgebraSheafIso I).inv).right.hom.app (op ⊤) :=
    congrArg (fun φ => φ.right.hom.app (op (⊤ : X.left.Opens)))
      (baseChangeAlgebraHom_comp_reesPullbackAlgebraIso_inv I X)
  rw [Scheme.Hom.comp_appTop, appTop_pullbackFst, appTop_reesClosedImmersion_eq]
  exact comp_rearrange _ _ _ _ _ _ _ h1 (unit_app_top_naturality I X)

end Stacks.Cohomology.FormalFunctions

end
