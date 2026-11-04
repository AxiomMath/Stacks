module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDivisorPresheafSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDivisorSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# The second map of Stacks 03RI as a map of presheaves: the commuting square

Let `X` be an integral normal scheme with generic point `η`, function field `K` and inclusion
`j : Spec K ⟶ X`. The second map of the fundamental exact sequence of Stacks 03RI,
`0 → 𝐆_{m,X} → j_* 𝐆_{m,η} → ⨁_{x ∈ X_0} (i_x)_* 𝐙 → 0`,
is read on sections over an étale `X`-scheme `U` by
`Stacks.EtaleCohomology.closedPointDivisorSections`. This file proves that this family of
homomorphisms is compatible with restriction along every morphism of the small étale site, at
every level at which the second map is written down: the order of vanishing at a point, the
`x`-component in the sections of `(i_x)_* 𝐙`, the family in the direct sum, and the section of
the coproduct of the underlying presheaves of the skyscrapers. It also shows that an affine
scheme étale over a locally Noetherian scheme has a Noetherian space.

## Main definitions

* `Stacks.EtaleCohomology.closedPointDivisorPresheafSection`: the second map on sections over an
  étale `X`-scheme with Noetherian space, valued in the coproduct of the underlying presheaves of
  the skyscrapers.

## Main results

* `Stacks.EtaleCohomology.smallEtaleBaseChange_map_left_eq_etaleGenericFibreMap`: the morphism of
  generic fibres induced by a morphism of the small étale site is its base change along the
  inclusion of the generic point.
* `Stacks.EtaleCohomology.residueFibreOrdOfPoint_comap`: the family of orders of vanishing on the
  fibre over a point of `X` is compatible with restriction, read in the locally constant
  `𝐙`-valued maps on the fibre.
* `Stacks.EtaleCohomology.integerSkyscraperDivisorOfPoint_map` and
  `Stacks.EtaleCohomology.integerSkyscraperDivisorOfPoint_map_baseChange`: the `x`-component of
  the second map is compatible with restriction along a morphism of the small étale site, read in
  the sections of `(i_x)_* 𝐙`.
* `Stacks.EtaleCohomology.closedPointDivisorSections_map` and
  `Stacks.EtaleCohomology.closedPointDivisorPresheafSection_map`: the same for the whole family,
  in the direct sum of the groups of sections and in the coproduct of the underlying presheaves.
* `Stacks.EtaleCohomology.closedPointDivisorPresheafSection_restrict_eq_zero`: the sequence is a
  complex on sections, read in the presheaf coproduct.
* `Stacks.EtaleCohomology.isLocallyNoetherian_etale_left` and
  `Stacks.EtaleCohomology.noetherianSpace_affineEtale_left`: an étale scheme over a locally
  Noetherian scheme is locally Noetherian, and an affine one has a Noetherian space.
* `Stacks.EtaleCohomology.isLocallyNoetherian_of_isCurve` and
  `Stacks.EtaleCohomology.isNormal_of_isCurve_of_smooth`: a curve is locally Noetherian, and a
  smooth curve over a field is normal.

## References

* [Stacks Project, Tag 03RI](https://stacks.math.columbia.edu/tag/03RI): the fundamental exact
  sequence.
* [Stacks Project, Tag 03P5](https://stacks.math.columbia.edu/tag/03P5): the sections of a
  constant sheaf are the locally constant maps.
* [Stacks Project, Tag 03RM](https://stacks.math.columbia.edu/tag/03RM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

attribute [local instance 10000] hasCoproduct_closedPointSkyscraper
  hasCoproduct_closedPointSkyscraper_obj

/-! ### The morphism of generic fibres is the base change of a morphism of the site -/

/-- **The morphism of generic fibres induced by a morphism of the small étale site of `X` is the
base change of that morphism along the inclusion of the generic point.** -/
theorem smallEtaleBaseChange_map_left_eq_etaleGenericFibreMap {X : Scheme.{u}}
    [IrreducibleSpace X] {U V : X.Etale} (φ : U ⟶ V) :
    ((smallEtaleBaseChange (genericPointInclusion X)).map φ).left = etaleGenericFibreMap φ := by
  rw [smallEtaleBaseChange_map_left, etaleGenericFibreMap]
  refine pullback.hom_ext ?_ ?_
  · exact (pullback.lift_fst _ _ _).trans (pullback.map_fst ..).symm
  · exact (pullback.lift_snd _ _ _).trans (by simp)

/-! ### Compatibility of the components with restriction -/

/-- **The family of orders of vanishing on the fibre over a point of `X` is compatible with
restriction**, read in the locally constant `𝐙`-valued maps on that fibre: restricting the family
attached to a unit on the generic fibre of `V` along a morphism `φ : U ⟶ V` of the small étale site
gives the family attached to the restricted unit. -/
theorem residueFibreOrdOfPoint_comap {X : Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
    [IsNormal X] {U V : X.Etale} [IsLocallyNoetherian U.left] [IsLocallyNoetherian V.left]
    (x : X) (φ : U ⟶ V) (a : (Γ(pullback V.hom (genericPointInclusion X), ⊤))ˣ) :
    ((smallEtaleLocallyConstantMapsAb.{u, max (u + 1) v} (Spec (X.residueField x))
          (ULift.{max (u + 1) v} ℤ)).map
        ((smallEtaleBaseChange (X.fromSpecResidueField x)).map φ).op).hom
        (residueFibreOrdOfPoint.{u, v} V x (Additive.ofMul a)) =
      residueFibreOrdOfPoint.{u, v} U x
        (Additive.ofMul (Units.map (etaleGenericFibreMap φ).appTop.hom.toMonoidHom a)) := by
  refine LocallyConstant.ext fun y => ?_
  show ULift.up (etaleGenericFibreOrdOfPoint V
      ((pullback.fst V.hom (X.fromSpecResidueField x))
        (((smallEtaleBaseChange (X.fromSpecResidueField x)).map φ).left y))
      (Additive.ofMul a)) =
    ULift.up (etaleGenericFibreOrdOfPoint U
      ((pullback.fst U.hom (X.fromSpecResidueField x)) y)
      (Additive.ofMul (Units.map (etaleGenericFibreMap φ).appTop.hom.toMonoidHom a)))
  rw [etaleGenericFibreOrdOfPoint_appTop φ ((pullback.fst U.hom (X.fromSpecResidueField x)) y) a,
    smallEtaleBaseChange_map_left_apply (X.fromSpecResidueField x) φ y]

/-- **The `x`-component of the second map of the fundamental exact sequence is compatible with
restriction along a morphism of the small étale site**, read in the sections of `(i_x)_* 𝐙` over an
étale `X`-scheme. Neither object is assumed irreducible. -/
@[stacks 03RI "the x-component of the second map is compatible with restriction along a morphism
of étale X-schemes, read in the sections of i_{x,*} Z, for X integral and normal"]
theorem integerSkyscraperDivisorOfPoint_map {X : Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
    [IsNormal X] {U V : X.Etale} [IsLocallyNoetherian U.left] [IsLocallyNoetherian V.left]
    (x : X) (φ : U ⟶ V) (a : (Γ(pullback V.hom (genericPointInclusion X), ⊤))ˣ) :
    ((integerSkyscraper.{u, v} X x).obj.map φ.op).hom
        (integerSkyscraperDivisorOfPoint.{u, v} V x (Additive.ofMul a)) =
      integerSkyscraperDivisorOfPoint.{u, v} U x
        (Additive.ofMul (Units.map (etaleGenericFibreMap φ).appTop.hom.toMonoidHom a)) := by
  have h := NatTrans.naturality_apply
    (smallEtaleConstantSheafIsoLocallyConstantMapsAb.{u, v} (Spec (X.residueField x))
      (ULift.{max (u + 1) v} ℤ)).inv
    ((smallEtaleBaseChange (X.fromSpecResidueField x)).map φ).op
    (residueFibreOrdOfPoint.{u, v} V x (Additive.ofMul a))
  rw [integerSkyscraperDivisorOfPoint, AddMonoidHom.comp_apply,
    integerSkyscraperDivisorOfPoint, AddMonoidHom.comp_apply,
    ← residueFibreOrdOfPoint_comap.{u, v} x φ a]
  exact h.symm

/-- **`Stacks.EtaleCohomology.integerSkyscraperDivisorOfPoint_map` with the restriction on the
generic fibre spelled as the base change of the morphism of the site.** -/
theorem integerSkyscraperDivisorOfPoint_map_baseChange {X : Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [IsNormal X] {U V : X.Etale} [IsLocallyNoetherian U.left]
    [IsLocallyNoetherian V.left] (x : X) (φ : U ⟶ V)
    (a : (Γ(pullback V.hom (genericPointInclusion X), ⊤))ˣ) :
    ((integerSkyscraper.{u, v} X x).obj.map φ.op).hom
        (integerSkyscraperDivisorOfPoint.{u, v} V x (Additive.ofMul a)) =
      integerSkyscraperDivisorOfPoint.{u, v} U x (Additive.ofMul (Units.map
        ((smallEtaleBaseChange (genericPointInclusion X)).map
          φ).left.appTop.hom.toMonoidHom a)) :=
  (integerSkyscraperDivisorOfPoint_map.{u, v} x φ a).trans
    (congrArg (fun m : pullback U.hom (genericPointInclusion X) ⟶
          pullback V.hom (genericPointInclusion X) =>
        integerSkyscraperDivisorOfPoint.{u, v} U x
          (Additive.ofMul (Units.map m.appTop.hom.toMonoidHom a)))
      (smallEtaleBaseChange_map_left_eq_etaleGenericFibreMap φ).symm)

/-! ### The second map on sections, valued in the presheaf coproduct -/

section Section

variable {X : Scheme.{u}} [AlgebraicGeometry.IsIntegral X] [IsNormal X]

/-- **The second map of the fundamental exact sequence on sections over an étale `X`-scheme `U`
with Noetherian space, valued in the coproduct of the underlying presheaves of the skyscrapers.**
It is `Stacks.EtaleCohomology.closedPointDivisorSections` followed by
`Stacks.EtaleCohomology.closedPointDivisorSheaf.presheafCoproductSectionOfDirectSum`; no
irreducibility hypothesis is carried on `U`. -/
def closedPointDivisorPresheafSection (U : X.Etale) [IsLocallyNoetherian U.left]
    [NoetherianSpace U.left] :
    Additive ((Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ) →+
      (∐ fun x : closedPoints X ↦ (closedPointSkyscraper.{u, v} X x).obj).obj (op U) :=
  (closedPointDivisorSheaf.presheafCoproductSectionOfDirectSum.{u, v} X U).comp
    (closedPointDivisorSections.{u, v} U)

/-- **The family of orders of vanishing is compatible with restriction along a morphism of the
small étale site**, read in the direct sum of the groups of sections of the skyscrapers. -/
theorem closedPointDivisorSections_map {U V : X.Etale} [IsLocallyNoetherian U.left]
    [NoetherianSpace U.left] [IsLocallyNoetherian V.left] [NoetherianSpace V.left]
    (φ : U ⟶ V) (a : (Γ(pullback V.hom (genericPointInclusion X), ⊤))ˣ) :
    DirectSum.map
        (fun x : closedPoints X ↦ ((closedPointSkyscraper.{u, v} X x).obj.map φ.op).hom)
        (closedPointDivisorSections.{u, v} V (Additive.ofMul a)) =
      closedPointDivisorSections.{u, v} U (Additive.ofMul (Units.map
        ((smallEtaleBaseChange (genericPointInclusion X)).map
          φ).left.appTop.hom.toMonoidHom a)) :=
  DFinsupp.ext fun x =>
    (DirectSum.map_apply _ x _).trans
      ((congrArg (fun z => ((closedPointSkyscraper.{u, v} X x).obj.map φ.op).hom z)
            (closedPointDivisorSections_apply.{u, v} V (Additive.ofMul a) x)).trans
        ((integerSkyscraperDivisorOfPoint_map_baseChange.{u, v} x.1 φ a).trans
          (closedPointDivisorSections_apply.{u, v} U _ x).symm))

/-- **The second map on sections is compatible with restriction**, read in the coproduct of the
underlying presheaves of the skyscrapers: restricting the section attached to a unit on the generic
fibre of `V` along a morphism `φ : U ⟶ V` of the small étale site gives the section attached to the
restricted unit. Neither object is assumed irreducible. -/
@[stacks 03RI "the second map of the sequence is compatible with restriction along a morphism of
étale X-schemes, read in the coproduct of the underlying presheaves of the skyscrapers, for X
integral and normal"]
theorem closedPointDivisorPresheafSection_map {U V : X.Etale} [IsLocallyNoetherian U.left]
    [NoetherianSpace U.left] [IsLocallyNoetherian V.left] [NoetherianSpace V.left]
    (φ : U ⟶ V) (a : (Γ(pullback V.hom (genericPointInclusion X), ⊤))ˣ) :
    ((∐ fun x : closedPoints X ↦ (closedPointSkyscraper.{u, v} X x).obj).map φ.op).hom
        (closedPointDivisorPresheafSection.{u, v} V (Additive.ofMul a)) =
      closedPointDivisorPresheafSection.{u, v} U (Additive.ofMul (Units.map
        ((smallEtaleBaseChange (genericPointInclusion X)).map
          φ).left.appTop.hom.toMonoidHom a)) :=
  (congrArg (fun ψ : _ →+ _ => ψ (closedPointDivisorSections.{u, v} V (Additive.ofMul a)))
      (closedPointDivisorSheaf.map_comp_presheafCoproductSectionOfDirectSum.{u, v} X φ)).trans
    (congrArg (closedPointDivisorSheaf.presheafCoproductSectionOfDirectSum.{u, v} X U)
      (closedPointDivisorSections_map.{u, v} φ a))

/-- **An invertible global function on `U` has trivial image under the second map**, read in the
presheaf coproduct: the sequence is a complex on sections over an étale `X`-scheme with Noetherian
space, with no irreducibility hypothesis. -/
@[stacks 03RI "the sequence is a complex on sections over an arbitrary étale X-scheme, read in the
coproduct of the underlying presheaves of the skyscrapers, for X integral and normal"]
theorem closedPointDivisorPresheafSection_restrict_eq_zero (U : X.Etale)
    [IsLocallyNoetherian U.left] [NoetherianSpace U.left] (a : (Γ(U.left, ⊤))ˣ) :
    closedPointDivisorPresheafSection.{u, v} U (Additive.ofMul (Units.map
      (pullback.fst U.hom (genericPointInclusion X)).appTop.hom.toMonoidHom a)) = 0 :=
  (AddMonoidHom.comp_apply
      (closedPointDivisorSheaf.presheafCoproductSectionOfDirectSum.{u, v} X U)
      (closedPointDivisorSections.{u, v} U) _).trans
    ((congrArg (closedPointDivisorSheaf.presheafCoproductSectionOfDirectSum.{u, v} X U)
      (closedPointDivisorSections_restrict_eq_zero.{u, v} U a)).trans (map_zero _))

end Section

/-! ### Noetherianity of the affine étale objects -/

section Noetherian

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/-- **An étale scheme over a locally Noetherian scheme is locally Noetherian.** -/
theorem isLocallyNoetherian_etale_left (U : X.Etale) : IsLocallyNoetherian U.left :=
  have : Etale U.hom := U.prop
  have : IsLocallyNoetherian ((Functor.fromPUnit X).obj U.right) :=
    inferInstanceAs (IsLocallyNoetherian X)
  LocallyOfFiniteType.isLocallyNoetherian U.hom

/-- **An affine scheme étale over a locally Noetherian scheme has a Noetherian space.** -/
theorem noetherianSpace_affineEtale_left (W : X.AffineEtale) :
    NoetherianSpace ((Scheme.AffineEtale.Spec X).obj W).left :=
  have : IsLocallyNoetherian ((Scheme.AffineEtale.Spec X).obj W).left :=
    isLocallyNoetherian_etale_left X _
  have : CompactSpace ((Scheme.AffineEtale.Spec X).obj W).left :=
    inferInstanceAs (CompactSpace (Scheme.Spec.obj W.left))
  have : AlgebraicGeometry.IsNoetherian ((Scheme.AffineEtale.Spec X).obj W).left :=
    AlgebraicGeometry.IsNoetherian.mk
  inferInstance

end Noetherian

/-! ### The hypotheses on `X` in the setting of Stacks 03RM -/

/-- **A curve is locally Noetherian.** -/
theorem isLocallyNoetherian_of_isCurve {k : Type u} [Field k] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of k)) [IsCurve k g] : IsLocallyNoetherian X :=
  LocallyOfFiniteType.isLocallyNoetherian g

/-- **A smooth curve over a field is normal.** -/
theorem isNormal_of_isCurve_of_smooth {k : Type u} [Field k] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of k)) [IsCurve k g] [Smooth g] : IsNormal X :=
  have : IsNormal (Spec (CommRingCat.of k)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed k)
  isNormal_of_smooth g

end Stacks.EtaleCohomology

end
