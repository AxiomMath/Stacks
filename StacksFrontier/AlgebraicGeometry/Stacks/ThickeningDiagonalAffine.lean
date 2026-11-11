module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AffineOfAffineThickening
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningDiagonalAffineIntegral

/-!
# Affineness and integrality of the relative diagonal across a morphism of thickenings

For a morphism of thickenings `(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` of algebraic stacks, the relative
diagonal of `f` is affine (resp. integral) if and only if that of `f'` is: properties (b) and (f)
of the seventeen listed in Stacks 0BPV.

Both are `AlgebraicGeometry.Stack.hasRelativeProperty_relativeDiagonal_iff`, whose only input
beyond the permanence of the property is its cancellation against a surjective closed immersion:
if `a ≫ b` is affine and `a` is a surjective closed immersion of algebraic spaces, then `b` is
affine (`AlgebraicGeometry.Space.isAffineHom_of_comp_of_isClosedImmersion_of_isSurjective`). Over
an affine scheme `Z → D`, the base change `C ×_D Z` receives the surjective closed immersion
`A ×_D Z → C ×_D Z` from an affine scheme, so it is affine by
`AlgebraicGeometry.Space.isAffineSpace_of_isClosedImmersion_of_isSurjective_of_isAffineSpace`.
Integrality is affineness together with universal closedness (Stacks 0415), and universal
closedness cancels against any surjection.

## References

* [Stacks Project, Tag 0BPV](https://stacks.math.columbia.edu/tag/0BPV)
* [Stacks Project, Tag 0415](https://stacks.math.columbia.edu/tag/0415)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `HasPullbacks` on presheaves over the big fppf site is slow
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_ThickeningDiagonalAffine :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_ThickeningDiagonalAffine
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **Affineness cancels against a surjective closed immersion.** Let `a : A → C` be a closed
immersion of algebraic spaces over `S` which is surjective, and `b : C → D` a morphism of
algebraic spaces. If `a ≫ b` is affine, so is `b`. -/
theorem isAffineHom_of_comp_of_isClosedImmersion_of_isSurjective
    {A C D : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hC : IsAlgebraicSpace B S hS C)
    (hD : IsAlgebraicSpace B S hS D) (a : A ⟶ C) (b : C ⟶ D)
    (ha : IsClosedImmersion B S hS a) (has : IsSurjective B S hS a)
    (hab : IsAffineHom B S hS (a ≫ b)) : IsAffineHom B S hS b := by
  intro Z g
  obtain ⟨W₁, p₁, q₁, h₁⟩ := hab Z g
  have hb : IsPullback (pullback.fst b g) (pullback.snd b g) b g := IsPullback.of_hasPullback _ _
  let φ := hb.lift (p₁ ≫ a) (yoneda.map q₁) (by rw [Category.assoc, h₁.w])
  have hφ₁ : φ ≫ pullback.fst b g = p₁ ≫ a := hb.lift_fst _ _ _
  have hφ₂ : φ ≫ pullback.snd b g = yoneda.map q₁ := hb.lift_snd _ _ _
  have htop : IsPullback p₁ φ a (pullback.fst b g) :=
    IsPullback.of_bot (by rw [hφ₂]; exact h₁) hφ₁.symm hb
  have hφ : IsClosedImmersion B S hS φ :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback htop ha
  have hφs : IsSurjective B S hS φ :=
    isSurjective_of_presheafSurjective B S hS φ
      ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback htop
        (presheafSurjective_of_isSurjective B S hS a ha.1 has))
  have hW₁ : IsAffineSpace B S hS (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj W₁)) :=
    isAffineSpace_yoneda B S hS _ (BigAffineFppf.isAffine_toScheme_obj B S hS W₁)
  have hCZ : IsAlgebraicSpace B S hS (pullback b g) :=
    isAlgebraicSpace_pullback B S hS b g hC (isAlgebraicSpace_yoneda B S hS _) hD
  obtain ⟨T, hT, ⟨e⟩⟩ :=
    isAffineSpace_of_isClosedImmersion_of_isSurjective_of_isAffineSpace B S hS φ
      hW₁.isAlgebraicSpace hCZ hφ hφs hW₁
  refine ⟨⟨T, hT⟩, e.inv ≫ pullback.fst b g, yoneda.preimage (e.inv ≫ pullback.snd b g), ?_⟩
  refine hb.of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp only [Iso.refl_hom, Category.comp_id, Functor.map_preimage, Iso.hom_inv_id_assoc]
  · simp
  · simp

/-- **Integrality cancels against a surjective closed immersion.** Let `a : A → C` be a closed
immersion of algebraic spaces over `S` which is surjective, and `b : C → D` a morphism of
algebraic spaces. If `a ≫ b` is integral, so is `b`. -/
theorem isIntegralHom_of_comp_of_isClosedImmersion_of_isSurjective
    {A C D : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hA : IsAlgebraicSpace B S hS A)
    (hC : IsAlgebraicSpace B S hS C) (hD : IsAlgebraicSpace B S hS D) (a : A ⟶ C) (b : C ⟶ D)
    (ha : IsClosedImmersion B S hS a) (has : IsSurjective B S hS a)
    (hab : IsIntegralHom B S hS (a ≫ b)) : IsIntegralHom B S hS b := by
  obtain ⟨haff, huc⟩ :=
    (isIntegralHom_iff_isAffineHom_and_universallyClosed B S hS hA hD (a ≫ b)).1 hab
  exact (isIntegralHom_iff_isAffineHom_and_universallyClosed B S hS hC hD b).2
    ⟨isAffineHom_of_comp_of_isClosedImmersion_of_isSurjective B S hS hC hD a b ha has haff,
      universallyClosed_of_isSurjective_comp B S hS hA hC hD a b huc has⟩

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {𝒳 𝒳' 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}
  {i : 𝒳 ⟶ 𝒳'} {j : 𝒴 ⟶ 𝒴'} {hi : IsThickening i} {hj : IsThickening j}
  (m : ThickeningMorphism i j hi hj)

/-- **Stacks 0BPV, property (b).** For a morphism of thickenings
`(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` of algebraic stacks over `S`, the relative diagonal
`Δ : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` is affine in the sense of Stacks 04XB (**Stacks 03WF**) if and only if
`Δ' : 𝒳' ⟶ 𝒳' ×_{𝒴'} 𝒳'` is. -/
theorem isAffineHom_relativeDiagonal_inner_iff_outer :
    Stack.IsAffineHom B S hS (AlgebraicStacks.relativeDiagonal B S hS m.inner).hom ↔
      Stack.IsAffineHom B S hS (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom := by
  have _haffBC : (Space.affineMorphismProperty B S hS).IsStableUnderBaseChange :=
    { of_isPullback := fun sq hg => Space.isAffineHom_hom_of_isPullback sq hg }
  have _haffLoc : (Space.affineMorphismProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    have _hfpqc : (Space.affineMorphismProperty B S hS).IsLocalAtTarget
        (Space.Topology.fpqc.precoverage.{u, u} B S hS) :=
      Space.isLocalAtTarget_isAffineHom_fpqc.{u, u} B S hS
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  exact hasRelativeProperty_relativeDiagonal_iff B S hS m (Space.affineMorphismProperty B S hS)
    (fun {A C D} a b hab hci hsurj =>
      Space.isAffineHom_of_comp_of_isClosedImmersion_of_isSurjective B S hS C.2 D.2
        a.hom b.hom hci hsurj hab)
    (isAffineHom_of_isThickening B S hS (isThickening_selfProductDiagonalMap B S hS m))

/-- **Stacks 0BPV, property (f).** For a morphism of thickenings
`(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` of algebraic stacks over `S`, the relative diagonal
`Δ : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` is integral in the sense of Stacks 04XB (**Stacks 03ZP**) if and only if
`Δ' : 𝒳' ⟶ 𝒳' ×_{𝒴'} 𝒳'` is. -/
theorem isIntegralHom_relativeDiagonal_inner_iff_outer :
    HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.integralMorphismProperty B S hS)
        (AlgebraicStacks.relativeDiagonal B S hS m.inner).hom
        (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS m.inner) ↔
      HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.integralMorphismProperty B S hS)
        (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom
        (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS m.outer) :=
  hasRelativeProperty_relativeDiagonal_iff B S hS m (Space.integralMorphismProperty B S hS)
    (fun {A C D} a b hab hci hsurj =>
      Space.isIntegralHom_of_comp_of_isClosedImmersion_of_isSurjective B S hS A.2 C.2 D.2
        a.hom b.hom hci hsurj hab)
    (hasRelativeProperty_integral_of_isThickening B S hS
      (isThickening_selfProductDiagonalMap B S hS m))

end AlgebraicGeometry.Stack
