module

public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.StepThreeCone

/-!
# Step (iii): the cone over the glued stages is limiting

The cone `AlgebraicGeometry.gluePairFunctorCone` is a limit as soon as the three cones it is
built from are: the one from the first open over the first diagram, the one from the second open
over the second, and the one from their intersection over the common diagram.

This is step (iii) of the one-affine-open step of Tag 07RN.  In the application the three
known limits are the system of models of the part already approximated, the spectra of the
finite-type subalgebras — through `AlgebraicGeometry.isLimitSpecMapCone` applied to the colimit
of `Stacks.StageSubalgebra.ringCocone` — and the models of the overlap.

## Main results

* `AlgebraicGeometry.isLimitCompatibleOpensConeOfIso`: a cone over the *source* of a natural
  transformation with open-immersion components and compatible images becomes, after
  postcomposition with the identification of `AlgebraicGeometry.compatibleOpensDiagramIso`, a
  limiting cone over the subdiagram that transformation cuts out.
* `AlgebraicGeometry.isLimitGluePairFunctorCone`: step (iii).

## Implementation notes

In `AlgebraicGeometry.isLimitCompatibleOpensConeOfIso` the two cones have the *same vertex*, so
the comparison is `CategoryTheory.Limits.Cone.ext` at the identity isomorphism, and its one
hypothesis is the leg equation.  Cancelling the monomorphism `(V j).ι` turns that equation into
the hypothesis `hp`, by `AlgebraicGeometry.Scheme.Hom.resLE_comp_ι` and
`AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_hom_fac`.  The components of the identification
are `CategoryTheory.NatIso.ofComponents` applications, so the component of its forward direction
is reached by `CategoryTheory.NatIso.ofComponents_hom_app` before the defining equation of
`AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq` can fire.

In `AlgebraicGeometry.isLimitGluePairFunctorCone` the three restricted cones are three
applications of that transport; the covering condition at one stage is
`AlgebraicGeometry.Scheme.gluePair_opensRange_sup`, and the assembly is
`AlgebraicGeometry.isLimitOfCompatibleOpensPair`.  The third application is at the composite `α`
followed by the first leg, whose image is the intersection of the two families by
`AlgebraicGeometry.Scheme.gluePair_opensRange_inf`; its leg equation is the first one restricted
along the inclusion of the intersection into the first open, which is where the compatibility
`hXW` is used a second time.

`AlgebraicGeometry.compatibleOpensCone` takes its two compatibility proofs as arguments and uses
them only through `.ge`, so two cones built from different proofs of the same two propositions
are equal by proof irrelevance; the third restricted cone can therefore be handed to the assembly
lemma, which names its own proofs, with no transport.

The index category is free in its object and morphism universes, with the schemes in `u`.
`CategoryTheory.IsCofiltered` is assumed, as `AlgebraicGeometry.isLimitOfCompatibleOpensPair`
requires; it also supplies the stage at which the covering condition is checked.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
* [Stacks Project, Tag 01YT](https://stacks.math.columbia.edu/tag/01YT)
* [Stacks Project, Tag 01JA](https://stacks.math.columbia.edu/tag/01JA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe v w u

namespace AlgebraicGeometry

/-- **The restricted cone over a cut-out subdiagram is limiting as soon as the corresponding
cone over the source diagram is.**  The two cones have the same vertex, so the comparison is at
the identity isomorphism and its one hypothesis is the leg equation. -/
noncomputable def isLimitCompatibleOpensConeOfIso {J : Type w} [Category.{v} J]
    {D E : J ⥤ Scheme.{u}} (ν : E ⟶ D) [∀ j, IsOpenImmersion (ν.app j)]
    (V : ∀ j, (D.obj j).Opens) (hV : ∀ ⦃j k : J⦄ (u : j ⟶ k), D.map u ⁻¹ᵁ V k = V j)
    (hνV : ∀ j, (ν.app j).opensRange = V j) {c : Cone D} (U : c.pt.Opens)
    (hU : ∀ j, c.π.app j ⁻¹ᵁ V j = U)
    (p : (Functor.const J).obj (U : Scheme.{u}) ⟶ E)
    (hp : ∀ j, U.ι ≫ c.π.app j = p.app j ≫ ν.app j)
    (hlim : IsLimit (Cone.mk (U : Scheme.{u}) p)) :
    IsLimit (compatibleOpensCone D c V hV U hU) :=
  IsLimit.ofIsoLimit
    ((IsLimit.postcomposeHomEquiv (compatibleOpensDiagramIso ν V hV hνV)
      (Cone.mk (U : Scheme.{u}) p)).symm hlim)
    (Cone.ext (Iso.refl _) fun j ↦ by
      change p.app j ≫ (compatibleOpensDiagramIso ν V hV hνV).hom.app j =
        𝟙 _ ≫ (c.π.app j).resLE (V j) U (hU j).ge
      rw [Category.id_comp]
      refine (cancel_mono (Scheme.Opens.ι (V j))).mp ?_
      rw [Category.assoc, Scheme.Hom.resLE_comp_ι, hp j]
      exact congrArg (fun m ↦ p.app j ≫ m)
        (compatibleOpensDiagramIso_hom_app_ι ν V hV hνV j))

section Limit

variable {J : Type w} [Category.{v} J] {Dw Dx Dy : J ⥤ Scheme.{u}} (α : Dw ⟶ Dx) (β : Dw ⟶ Dy)
  [∀ j, IsOpenImmersion (α.app j)] [∀ j, IsOpenImmersion (β.app j)]
  {S : Scheme.{u}} (U₁ U₂ : S.Opens)
  (pX : (Functor.const J).obj (U₁ : Scheme.{u}) ⟶ Dx)
  (pY : (Functor.const J).obj (U₂ : Scheme.{u}) ⟶ Dy)
  (pW : (Functor.const J).obj ((U₁ ⊓ U₂ : S.Opens) : Scheme.{u}) ⟶ Dw)
  (hXW : ∀ j, S.homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁) ≫ pX.app j = pW.app j ≫ α.app j)
  (hYW : ∀ j, S.homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂) ≫ pY.app j = pW.app j ≫ β.app j)
  (hS : U₁ ⊔ U₂ = ⊤)
  (hα : ∀ ⦃j k : J⦄ (u : j ⟶ k), Dx.map u ⁻¹ᵁ (α.app k).opensRange = (α.app j).opensRange)
  (hβ : ∀ ⦃j k : J⦄ (u : j ⟶ k), Dy.map u ⁻¹ᵁ (β.app k).opensRange = (β.app j).opensRange)

include hXW hYW hS in
/-- The leg equation of the third restricted cone: the first one, restricted along the inclusion
of the intersection into the first open. -/
lemma ι_gluePairFunctorCone_app_inter (j : J) :
    (U₁ ⊓ U₂ : S.Opens).ι ≫ (gluePairFunctorCone α β U₁ U₂ pX pY pW hXW hYW hS).app j =
      pW.app j ≫ α.app j ≫ Scheme.gluePairInl (α.app j) (β.app j) := by
  rw [← Scheme.homOfLE_ι_assoc S (inf_le_left : U₁ ⊓ U₂ ≤ U₁), ι_gluePairFunctorCone_app_left]
  exact (reassoc_of% (hXW j)) _

include hXW hYW hS hα hβ in
/-- **Step (iii): the cone over the glued stages is limiting.**  The three restricted cones of
`AlgebraicGeometry.isLimitOfCompatibleOpensPair` are the three transports of the given limits
along the identifications of `AlgebraicGeometry.compatibleOpensDiagramIso`. -/
noncomputable def isLimitGluePairFunctorCone [IsCofiltered J]
    (hXr : ∀ j, pX.app j ⁻¹ᵁ (α.app j).opensRange = U₁.ι ⁻¹ᵁ U₂)
    (hYr : ∀ j, pY.app j ⁻¹ᵁ (β.app j).opensRange = U₂.ι ⁻¹ᵁ U₁)
    (hX : IsLimit (Cone.mk (U₁ : Scheme.{u}) pX))
    (hY : IsLimit (Cone.mk (U₂ : Scheme.{u}) pY))
    (hW : IsLimit (Cone.mk ((U₁ ⊓ U₂ : S.Opens) : Scheme.{u}) pW)) :
    IsLimit (Cone.mk S (gluePairFunctorCone α β U₁ U₂ pX pY pW hXW hYW hS)) := by
  have j₀ : J := (IsCofiltered.nonempty (C := J)).some
  refine isLimitOfCompatibleOpensPair (compatibleOpens_gluePairFunctorInl α β hβ)
    (compatibleOpens_gluePairFunctorInr α β hα)
    (preimage_opensRange_gluePairFunctorCone_left α β U₁ U₂ pX pY pW hXW hYW hS hYr)
    (preimage_opensRange_gluePairFunctorCone_right α β U₁ U₂ pX pY pW hXW hYW hS hXr)
    j₀ (Scheme.gluePair_opensRange_sup (α.app j₀) (β.app j₀)) ?_ ?_ ?_
  · exact isLimitCompatibleOpensConeOfIso (gluePairFunctorInl α β) _
      (compatibleOpens_gluePairFunctorInl α β hβ) (fun _ ↦ rfl)
      (c := Cone.mk S (gluePairFunctorCone α β U₁ U₂ pX pY pW hXW hYW hS)) U₁
      (preimage_opensRange_gluePairFunctorCone_left α β U₁ U₂ pX pY pW hXW hYW hS hYr) pX
      (ι_gluePairFunctorCone_app_left α β U₁ U₂ pX pY pW hXW hYW hS) hX
  · exact isLimitCompatibleOpensConeOfIso (gluePairFunctorInr α β) _
      (compatibleOpens_gluePairFunctorInr α β hα) (fun _ ↦ rfl)
      (c := Cone.mk S (gluePairFunctorCone α β U₁ U₂ pX pY pW hXW hYW hS)) U₂
      (preimage_opensRange_gluePairFunctorCone_right α β U₁ U₂ pX pY pW hXW hYW hS hXr) pY
      (ι_gluePairFunctorCone_app_right α β U₁ U₂ pX pY pW hXW hYW hS) hY
  · exact isLimitCompatibleOpensConeOfIso (α ≫ gluePairFunctorInl α β) _
      (compatibleOpens_gluePairFunctorInter α β hα hβ)
      (fun j ↦ (Scheme.gluePair_opensRange_inf (α.app j) (β.app j)).symm)
      (c := Cone.mk S (gluePairFunctorCone α β U₁ U₂ pX pY pW hXW hYW hS)) (U₁ ⊓ U₂)
      (CompatibleOpensPair.preimage_inf_eq_of_preimage_eq
        (preimage_opensRange_gluePairFunctorCone_left α β U₁ U₂ pX pY pW hXW hYW hS hYr)
        (preimage_opensRange_gluePairFunctorCone_right α β U₁ U₂ pX pY pW hXW hYW hS hXr)) pW
      (ι_gluePairFunctorCone_app_inter α β U₁ U₂ pX pY pW hXW hYW hS) hW

end Limit

end AlgebraicGeometry
