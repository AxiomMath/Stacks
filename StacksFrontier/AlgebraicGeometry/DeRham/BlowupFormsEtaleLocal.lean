module

public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupSmoothCentreFormsDirectImage
public import StacksFrontier.AlgebraicGeometry.DeRham.FormsDirectImageEtaleBaseChange

/-!
# Clauses (1) and (2) of Stacks 0FUU are étale local

Let `f : X ⟶ S` be a morphism, let `i : Z ⟶ X` be a closed immersion, let `b : X' ⟶ X` be the
blowing up of `X` along `Z` and `p : E ⟶ Z` the projection of its exceptional divisor onto the
centre. The two comparison maps of [Stacks, Tag 0FUU]

* `Ω^a_{X/S} ⟶ b_*Ω^a_{X'/S}` (`Stacks.DeRham.blowupFormsDirectImage`) and
* `Ω^a_{Z/S} ⟶ p_*Ω^a_{E/S}` (`Stacks.DeRham.exceptionalFormsDirectImage`)

are compatible with étale base change. Let `ε : X₁ ⟶ X` be étale, lying over an étale morphism
of bases `S₁ ⟶ S`, and let `i₁ : Z₁ ⟶ X₁` be the base change of `i` along `ε`, with
`δ : Z₁ ⟶ Z` the induced étale morphism. Blowing up commutes
with flat base change ([Stacks, Tag 0805]), and so does the exceptional divisor, so the two
comparison maps for `i₁` are, up to the canonical isomorphisms, the inverse images along `ε` and
`δ` of those for `i`. This is the step "the pullback by `ε` of the maps in (1), (2) are the maps
for `X₁`" of the source's proof, which uses [Stacks, Tag 0FLV] for the forms and flat base change
for the direct images; the latter needs `b` quasi-compact (it is always separated).

## Main results

* `Stacks.DeRham.isIso_blowupFormsDirectImage_of_isPullback` and
  `Stacks.DeRham.isIso_exceptionalFormsDirectImage_of_isPullback`: invertibility of the
  comparison maps passes to an étale base change.
* `Stacks.DeRham.isIso_pullback_map_blowupFormsDirectImage_of_isPullback` and
  `Stacks.DeRham.isIso_pullback_map_exceptionalFormsDirectImage_of_isPullback`: the inverse
  image along `ε`, respectively `δ`, of a comparison map is invertible as soon as the comparison
  map of the base change is.

## References

* [Stacks Project, Tag 0FUU](https://stacks.math.columbia.edu/tag/0FUU)
* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
* [Stacks Project, Tag 0FLV](https://stacks.math.columbia.edu/tag/0FLV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] CategoryTheory.catToReflQuiver

namespace Stacks.DeRham

/-- **The comparison map of clause (1) is the comparison map on direct images of forms** along
the blowing-up morphism. -/
theorem blowupFormsDirectImage_eq {S X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ S) (a : ℤ) :
    blowupFormsDirectImage i f a =
      Scheme.Hom.formsDirectImageComparison (Stacks.Blowup.blowUpToBase i.ker) f a := by
  rw [blowupFormsDirectImage, Adjunction.homEquiv_unit]
  rfl

/-- **The comparison map of clause (2) is the comparison map on direct images of forms** along
the projection of the exceptional divisor onto the centre. -/
theorem exceptionalFormsDirectImage_eq {S X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ S) (a : ℤ) :
    exceptionalFormsDirectImage i f a =
      Scheme.Hom.formsDirectImageComparison (Stacks.Blowup.exceptionalToCentre i) (i ≫ f) a := by
  rw [exceptionalFormsDirectImage, Adjunction.homEquiv_unit]
  rfl

/-- Invertibility of the comparison map on direct images of forms does not see how the structure
morphism to the base is written. -/
theorem isIso_formsDirectImageComparison_congr {S X Y : Scheme.{u}} (g : Y ⟶ X) {π π' : X ⟶ S}
    (h : π = π') (d : ℤ) :
    IsIso (Scheme.Hom.formsDirectImageComparison g π d) ↔
      IsIso (Scheme.Hom.formsDirectImageComparison g π' d) := by
  subst h
  rfl

/-- The projection of the exceptional divisor onto the centre is quasi-compact as soon as the
blowing-up morphism is: it is a base change of it. -/
theorem quasiCompact_exceptionalToCentre {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [QuasiCompact (Stacks.Blowup.blowUpToBase i.ker)] :
    QuasiCompact (Stacks.Blowup.exceptionalToCentre i) :=
  MorphismProperty.of_isPullback (Stacks.Blowup.isPullback_exceptionalToCentre i) inferInstance

/-- The projection of the exceptional divisor onto the centre is separated: it is a base change
of the blowing-up morphism. -/
instance isSeparated_exceptionalToCentre {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    IsSeparated (Stacks.Blowup.exceptionalToCentre i) :=
  MorphismProperty.of_isPullback (Stacks.Blowup.isPullback_exceptionalToCentre i) inferInstance

section EtaleBaseChange

variable {S X Z S₁ X₁ Z₁ : Scheme.{u}} (f : X ⟶ S) (f₁ : X₁ ⟶ S₁) {i : Z ⟶ X}
  [IsClosedImmersion i] {ε : X₁ ⟶ X} [Etale ε] {δ : Z₁ ⟶ Z} {i₁ : Z₁ ⟶ X₁}
  [IsClosedImmersion i₁] (H : IsPullback δ i₁ i ε) (e : S₁ ⟶ S) [Etale e]
  (he : ε ≫ f = f₁ ≫ e) [QuasiCompact (Stacks.Blowup.blowUpToBase i.ker)] (a : ℕ)

include H he in
/-- **Clause (1) of [Stacks, Tag 0FUU] passes to an étale base change**: if
`Ω^a_{X/S} ⟶ b_*Ω^a_{X'/S}` is an isomorphism, then so is the comparison map for the base change
`i₁` of the centre along the étale `ε`, over an étale morphism of bases `S₁ ⟶ S`. -/
theorem isIso_blowupFormsDirectImage_of_isPullback
    (h : IsIso (blowupFormsDirectImage i f (a : ℤ))) :
    IsIso (blowupFormsDirectImage i₁ f₁ (a : ℤ)) := by
  obtain ⟨ε', hb⟩ := Stacks.Blowup.exists_isPullback_blowUpToBase_of_isPullback H
  rw [blowupFormsDirectImage_eq] at h ⊢
  exact Scheme.Hom.isIso_formsDirectImageComparison_of_isPullback hb f f₁ e he a

include H he in
/-- **Clause (1) of [Stacks, Tag 0FUU] is detected after an étale base change**: if the comparison
map for the base change `i₁` of the centre along the étale `ε`, over an étale morphism of bases
`S₁ ⟶ S`, is an isomorphism, then so is the inverse image along `ε` of
`Ω^a_{X/S} ⟶ b_*Ω^a_{X'/S}`. -/
theorem isIso_pullback_map_blowupFormsDirectImage_of_isPullback
    (h : IsIso (blowupFormsDirectImage i₁ f₁ (a : ℤ))) :
    IsIso ((Scheme.Modules.pullback ε).map (blowupFormsDirectImage i f (a : ℤ))) := by
  obtain ⟨ε', hb⟩ := Stacks.Blowup.exists_isPullback_blowUpToBase_of_isPullback H
  rw [blowupFormsDirectImage_eq] at h ⊢
  exact Scheme.Hom.isIso_pullback_map_formsDirectImageComparison_of_isPullback hb f f₁ e he a

/-- An étale base change of the centre induces a base change of the projection of the exceptional
divisor onto the centre, along the étale morphism `δ`; this projection is quasi-compact. -/
private theorem exists_isPullback_exceptionalToCentre_of_isPullback
    (H : IsPullback δ i₁ i ε) :
    ∃ ε'' : Stacks.Blowup.exceptionalDivisor i₁.ker ⟶ Stacks.Blowup.exceptionalDivisor i.ker,
      IsPullback ε'' (Stacks.Blowup.exceptionalToCentre i₁) (Stacks.Blowup.exceptionalToCentre i)
        δ ∧ Etale δ ∧ QuasiCompact (Stacks.Blowup.exceptionalToCentre i) := by
  obtain ⟨ε', hb⟩ := Stacks.Blowup.exists_isPullback_blowUpToBase_of_isPullback H
  obtain ⟨ε'', -, hE⟩ := Stacks.Blowup.exists_isPullback_exceptionalDivisor hb H
  exact ⟨ε'', hE, MorphismProperty.of_isPullback H.flip inferInstance,
    quasiCompact_exceptionalToCentre i⟩

include H he in
/-- **Clause (2) of [Stacks, Tag 0FUU] passes to an étale base change**: if
`Ω^a_{Z/S} ⟶ p_*Ω^a_{E/S}` is an isomorphism, then so is the comparison map for the base change
`i₁` of the centre along the étale `ε`, over an étale morphism of bases `S₁ ⟶ S`. -/
theorem isIso_exceptionalFormsDirectImage_of_isPullback
    (h : IsIso (exceptionalFormsDirectImage i f (a : ℤ))) :
    IsIso (exceptionalFormsDirectImage i₁ f₁ (a : ℤ)) := by
  obtain ⟨_, hE, _, _⟩ := exists_isPullback_exceptionalToCentre_of_isPullback H
  rw [exceptionalFormsDirectImage_eq] at h ⊢
  exact Scheme.Hom.isIso_formsDirectImageComparison_of_isPullback hE (i ≫ f) (i₁ ≫ f₁) e
    (by rw [reassoc_of% H.w, he, Category.assoc]) a

include H he in
/-- **Clause (2) of [Stacks, Tag 0FUU] is detected after an étale base change**: if the comparison
map for the base change `i₁` of the centre along the étale `ε`, over an étale morphism of bases
`S₁ ⟶ S`, is an isomorphism, then so is the inverse image along `δ : Z₁ ⟶ Z` of
`Ω^a_{Z/S} ⟶ p_*Ω^a_{E/S}`. -/
theorem isIso_pullback_map_exceptionalFormsDirectImage_of_isPullback
    (h : IsIso (exceptionalFormsDirectImage i₁ f₁ (a : ℤ))) :
    IsIso ((Scheme.Modules.pullback δ).map (exceptionalFormsDirectImage i f (a : ℤ))) := by
  obtain ⟨_, hE, _, _⟩ := exists_isPullback_exceptionalToCentre_of_isPullback H
  rw [exceptionalFormsDirectImage_eq] at h ⊢
  exact Scheme.Hom.isIso_pullback_map_formsDirectImageComparison_of_isPullback hE (i ≫ f)
    (i₁ ≫ f₁) e (by rw [reassoc_of% H.w, he, Category.assoc]) a

end EtaleBaseChange

end Stacks.DeRham

end
