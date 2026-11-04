module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesGraphBaseChange

/-!
# The slice step of Stacks 0AF6 at one space over `X`

In a formal glueing situation `D = (f : Y ⟶ X, Z, U = X \ Z, V = Y \ f⁻¹(Z))`, write `F` for the
restriction functor of Stacks 0AF3.
`AlgebraicGeometry.Space.FormalGlueingSituation.closedSliceRealization_of_essSurj` derives the
closed-immersion construction in the slice over *every* space over `X` from clause (2) of
Stacks 0AF4 for *every* formal glueing situation. Its proof uses that clause at one situation
only, the base change of `D` along the given space `Qq ⟶ X`. This module states the construction
at one space and proves it from that single instance, and does the same for the graph argument
of Stacks 0AF6, which uses the construction at one space only: the fibre product
`X'₁ ×_X X'₂`.

These pointwise forms are what globalizing clause (1) of Stacks 0AF4 needs. When `X'₁` and `X'₂`
are affine schemes over an affine `X`, their fibre product is again an affine scheme, so fullness
of `F` on such a pair needs clause (1) only for situations over an affine base.

## Main definitions

* `AlgebraicGeometry.Space.FormalGlueingSituation.ClosedSliceRealizationAt`: the
  closed-immersion construction in the slice over one space `Qq` over `X`.

## Main results

* `AlgebraicGeometry.Space.FormalGlueingSituation.closedSliceRealizationAt_of_essSurj` and
  `…closedSliceRealizationAt_of_essSurj_affine`: the construction over `Qq` from clause (2),
  resp. clause (1), of Stacks 0AF4 for the base change of the situation along `Qq ⟶ X`.
* `AlgebraicGeometry.Space.FormalGlueingSituation.exists_map_eq_of_closedSliceRealizationAt`:
  the graph argument of Stacks 0AF6, granted the construction over the fibre products of the
  source and the target only.

## References

* [Stacks Project, Tag 0AF4](https://stacks.math.columbia.edu/tag/0AF4)
* [Stacks Project, Tag 0AF6](https://stacks.math.columbia.edu/tag/0AF6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.FormalGlueingSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The closed-immersion construction in the slice over one space `Qq` over `X`: a morphism of
glueing data `ψ : G ⟶ F Qq` whose two legs are closed immersions is the restriction of a morphism
`k : T ⟶ Qq` of spaces over `X`, up to an isomorphism `F T ≅ G`.
`AlgebraicGeometry.Space.FormalGlueingSituation.ClosedSliceRealization D` is this statement at
every `Qq`. -/
def ClosedSliceRealizationAt (D : FormalGlueingSituation B S hS) (Qq : spacesOverX D) : Prop :=
  ∀ (G : glueingData D) (ψ : G ⟶ (formalGlueingFunctor D).1.obj Qq),
    IsClosedImmersion B S hS ψ.hom.left.left →
    IsClosedImmersion B S hS ψ.hom.right.left →
    ∃ (T : spacesOverX D) (k : T ⟶ Qq) (θ : (formalGlueingFunctor D).1.obj T ≅ G),
      θ.hom ≫ ψ = (formalGlueingFunctor D).1.map k

/-- The construction at every space is `ClosedSliceRealization`. -/
theorem closedSliceRealization_iff_forall_at (D : FormalGlueingSituation B S hS) :
    ClosedSliceRealization D ↔ ∀ Qq, ClosedSliceRealizationAt D Qq :=
  Iff.rfl

/-- **The closed-immersion construction over `Qq` from clause (2) of Stacks 0AF4 for the base
change of the situation along `Qq ⟶ X`.** The proof of
`AlgebraicGeometry.Space.FormalGlueingSituation.closedSliceRealization_of_essSurj`, which uses
clause (2) at that base change only. -/
theorem closedSliceRealizationAt_of_essSurj (D : FormalGlueingSituation B S hS)
    (Qq : spacesOverX D)
    (hess : (closedGlueingFunctor (D.baseChangeAlong Qq.property Qq.obj.hom)).EssSurj) :
    ClosedSliceRealizationAt D Qq := by
  intro G ψ hl hr
  have hU := baseChangeAlong_U_eq D Qq.property Qq.obj.hom
  have hV := baseChangeAlong_V_eq D Qq.property Qq.obj.hom
  have hYsq := IsPullback.of_hasPullback D.f Qq.obj.hom
  obtain ⟨T', hT', θU, θY, hθU, hθY⟩ :=
    exists_iso_restrictionDiagram_of_closedLegs D (D.baseChangeAlong Qq.property Qq.obj.hom)
      hYsq (Subfunctor.isPullback_mapOfEqPreimage D.U Qq.obj.hom hU)
      (Subfunctor.isPullback_mapOfEqPreimage D.V (pullback.fst D.f Qq.obj.hom) hV)
      (Subfunctor.mapOfEqPreimage_comm D.U hYsq hU hV)
      hess G ψ.hom.left ψ.hom.right ψ.hom.w hl hr
  have : Mono ψ.hom.right.left := mono_of_isClosedImmersion B S hS _ hr
  exact exists_iso_formalGlueingFunctor_of_legs D ψ T' hT' θU θY hθU hθY

/-- **The closed-immersion construction over `Qq` from clause (1) of Stacks 0AF4 for the base
change of the situation along `Qq ⟶ X`**, through clause (2) for that base change
(`AlgebraicGeometry.Space.FormalGlueingSituation.essSurj_closedGlueingFunctor`). -/
theorem closedSliceRealizationAt_of_essSurj_affine (D : FormalGlueingSituation B S hS)
    (Qq : spacesOverX D)
    (hes : (affineGlueingFunctor (D.baseChangeAlong Qq.property Qq.obj.hom)).EssSurj) :
    ClosedSliceRealizationAt D Qq :=
  closedSliceRealizationAt_of_essSurj D Qq (essSurj_closedGlueingFunctor _ hes)

/-- **The graph argument of Stacks 0AF6, granted the construction over the fibre products of the
source and the target.** This is
`AlgebraicGeometry.Space.FormalGlueingSituation.exists_map_eq_of_essSurj_closedImmersion` with
its hypothesis asked only at the spaces `Q` over `X` which are fibre products `X'₁ ×_X X'₂` —
the only spaces at which that proof uses it. -/
theorem exists_map_eq_of_closedSliceRealizationAt (D : FormalGlueingSituation B S hS)
    {X₁ X₂ : spacesOverX D} (hsep : IsSeparated B S hS X₂.obj.hom)
    (hreal : ∀ (Q : spacesOverX D) (p₁ : Q ⟶ X₁) (p₂ : Q ⟶ X₂),
      IsLimit (BinaryFan.mk p₁.hom p₂.hom) → ClosedSliceRealizationAt D Q)
    (φ : (formalGlueingFunctor D).1.obj X₁ ⟶ (formalGlueingFunctor D).1.obj X₂) :
    ∃ a : X₁ ⟶ X₂, (formalGlueingFunctor D).1.map a = φ := by
  obtain ⟨Q, p₁, p₂, ⟨hQlim⟩, hsep₁⟩ : ∃ (Q : spacesOverX D) (p₁ : Q ⟶ X₁) (p₂ : Q ⟶ X₂),
      Nonempty (IsLimit (BinaryFan.mk p₁.hom p₂.hom)) ∧ IsSeparated B S hS p₁.hom.left :=
    ⟨⟨Over.mk (pullback.fst X₁.obj.hom X₂.obj.hom ≫ X₁.obj.hom),
        isAlgebraicSpace_pullback B S hS X₁.obj.hom X₂.obj.hom X₁.property X₂.property
          D.algebraicSpace_X⟩,
      ⟨Over.homMk (pullback.fst X₁.obj.hom X₂.obj.hom) rfl⟩,
      ⟨Over.homMk (pullback.snd X₁.obj.hom X₂.obj.hom) pullback.condition.symm⟩,
      ⟨overProdIsLimit X₁.obj X₂.obj⟩,
      isSeparated_of_isPullback B S hS
        (IsPullback.of_hasPullback X₁.obj.hom X₂.obj.hom).flip hsep⟩
  obtain ⟨Γ, hΓ₁, hΓ₂⟩ := exists_lift_formalGlueingFunctor D p₁ p₂ hQlim
    ((formalGlueingFunctor D).1.obj X₁) (𝟙 _) φ
  have hciU : IsClosedImmersion B S hS Γ.hom.left.left :=
    isClosedImmersion_of_isSeparated_of_section B S hS _
      (isSeparated_of_isPullback B S hS
        (isPullback_overPullback_map_left D.U.ι p₁.hom).flip hsep₁) _
      (congrArg (fun m : (formalGlueingFunctor D).1.obj X₁ ⟶
        (formalGlueingFunctor D).1.obj X₁ ↦ m.hom.left.left) hΓ₁)
  have hciY : IsClosedImmersion B S hS Γ.hom.right.left :=
    isClosedImmersion_of_isSeparated_of_section B S hS _
      (isSeparated_of_isPullback B S hS
        (isPullback_overPullback_map_left D.f p₁.hom).flip hsep₁) _
      (congrArg (fun m : (formalGlueingFunctor D).1.obj X₁ ⟶
        (formalGlueingFunctor D).1.obj X₁ ↦ m.hom.right.left) hΓ₁)
  obtain ⟨T, k, θ, hθ⟩ := hreal Q p₁ p₂ hQlim _ Γ hciU hciY
  refine exists_map_eq_of_graph_formalGlueingFunctor D p₁ p₂ k θ ?_ ?_
  · rw [Functor.map_comp, ← hθ, Category.assoc, hΓ₁, Category.comp_id]
  · rw [Functor.map_comp, ← hθ, Category.assoc, hΓ₂]

end AlgebraicGeometry.Space.FormalGlueingSituation

end
