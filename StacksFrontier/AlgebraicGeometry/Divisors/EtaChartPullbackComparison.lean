module

public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness

/-!
# Preservation of a fibre product under pullback along a morphism of affine schemes

Let `φ : R ⟶ S` be a homomorphism of commutative rings and let `M ⟶ P ⟵ N` be a cospan of
`R`-modules. If extension of scalars `S ⊗_R -` preserves its fibre product, then pullback along
`Spec S ⟶ Spec R` preserves the fibre product of the associated cospan of quasi-coherent
sheaves `M̃ ⟶ P̃ ⟵ Ñ`. Both `~` functors are exact, and pullback of an associated sheaf is the
associated sheaf of the extension of scalars, naturally in the module (Stacks 01I9).

The statements are about the comparison map
`CategoryTheory.Limits.pullbackComparison G a b : G(A ×_C B) ⟶ G A ×_{G C} G B`, which is an
isomorphism exactly when `G` preserves the fibre product. Two general facts about it are recorded
first: it is invariant under a natural isomorphism of functors and under an isomorphism of
cospans.

## Main results

* `CategoryTheory.Limits.isIso_pullbackComparison_iff_of_natIso`: invariance under a natural
  isomorphism of functors.
* `CategoryTheory.Limits.isIso_pullbackComparison_iff_of_isIso`: invariance under an isomorphism
  of cospans.
* `AlgebraicGeometry.isIso_pullbackComparison_pullback_spec_map_tilde`: the affine statement.

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Limits

variable {C D : Type*} [Category C] [Category D]

/-- The comparison map of a fibre product is invertible for one functor exactly when it is
invertible for a naturally isomorphic one. -/
theorem isIso_pullbackComparison_iff_of_natIso {F G : C ⥤ D} (α : F ≅ G) {X Y Z : C}
    (a : X ⟶ Z) (b : Y ⟶ Z) [HasPullback a b] [HasPullback (F.map a) (F.map b)]
    [HasPullback (G.map a) (G.map b)] :
    IsIso (pullbackComparison F a b) ↔ IsIso (pullbackComparison G a b) := by
  have e : pullbackComparison G a b = α.inv.app (pullback a b) ≫ pullbackComparison F a b ≫
      pullback.map (F.map a) (F.map b) (G.map a) (G.map b) (α.hom.app X) (α.hom.app Y)
        (α.hom.app Z) (α.hom.naturality a) (α.hom.naturality b) := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullbackComparison_comp_fst, Category.assoc, Category.assoc, pullback.lift_fst,
        ← Category.assoc (pullbackComparison F a b), pullbackComparison_comp_fst,
        α.hom.naturality, Iso.inv_hom_id_app_assoc]
    · rw [pullbackComparison_comp_snd, Category.assoc, Category.assoc, pullback.lift_snd,
        ← Category.assoc (pullbackComparison F a b), pullbackComparison_comp_snd,
        α.hom.naturality, Iso.inv_hom_id_app_assoc]
  rw [e, isIso_comp_left_iff, isIso_comp_right_iff]

/-- The comparison map of a fibre product is invertible at one cospan exactly when it is
invertible at an isomorphic one. -/
theorem isIso_pullbackComparison_iff_of_isIso (G : C ⥤ D) {X Y Z X' Y' Z' : C}
    (a : X ⟶ Z) (b : Y ⟶ Z) (a' : X' ⟶ Z') (b' : Y' ⟶ Z') [HasPullback a b]
    [HasPullback a' b'] [HasPullback (G.map a) (G.map b)] [HasPullback (G.map a') (G.map b')]
    (eX : X ⟶ X') (eY : Y ⟶ Y') (eZ : Z ⟶ Z') [IsIso eX] [IsIso eY] [IsIso eZ]
    (h₁ : a ≫ eZ = eX ≫ a') (h₂ : b ≫ eZ = eY ≫ b') :
    IsIso (pullbackComparison G a b) ↔ IsIso (pullbackComparison G a' b') := by
  have e : G.map (pullback.map a b a' b' eX eY eZ h₁ h₂) ≫ pullbackComparison G a' b' =
      pullbackComparison G a b ≫ pullback.map (G.map a) (G.map b) (G.map a') (G.map b')
        (G.map eX) (G.map eY) (G.map eZ) (by rw [← G.map_comp, h₁, G.map_comp])
        (by rw [← G.map_comp, h₂, G.map_comp]) := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullbackComparison_comp_fst, ← G.map_comp, pullback.lift_fst,
        Category.assoc, pullback.lift_fst, ← Category.assoc, pullbackComparison_comp_fst,
        G.map_comp]
    · rw [Category.assoc, pullbackComparison_comp_snd, ← G.map_comp, pullback.lift_snd,
        Category.assoc, pullback.lift_snd, ← Category.assoc, pullbackComparison_comp_snd,
        G.map_comp]
  rw [← isIso_comp_left_iff (G.map (pullback.map a b a' b' eX eY eZ h₁ h₂))
    (pullbackComparison G a' b'), e, isIso_comp_right_iff]

end CategoryTheory.Limits

namespace AlgebraicGeometry

/-- **Pullback along a morphism of affine schemes preserves the fibre product of an associated
cospan of quasi-coherent sheaves** when extension of scalars preserves the fibre product of the
cospan of modules. The functors `~` are exact, and `Spec(φ)^* ∘ ~ ≅ ~ ∘ (S ⊗_R -)` by
`AlgebraicGeometry.pullbackTildeIso` (Stacks 01I9). -/
theorem isIso_pullbackComparison_pullback_spec_map_tilde {R S : CommRingCat.{u}} (φ : R ⟶ S)
    {M N P : ModuleCat.{u} R} (a : M ⟶ P) (b : N ⟶ P)
    (h : IsIso (pullbackComparison (ModuleCat.extendScalars φ.hom) a b)) :
    IsIso (pullbackComparison (Scheme.Modules.pullback (Spec.map φ))
      ((tilde.functor R).map a) ((tilde.functor R).map b)) := by
  have : PreservesFiniteLimits (tilde.functor R) := AlgebraicGeometry.tilde.preservesFiniteLimits R
  have : PreservesFiniteLimits (tilde.functor S) := AlgebraicGeometry.tilde.preservesFiniteLimits S
  have : PreservesLimitsOfShape WalkingCospan (tilde.functor R) :=
    PreservesFiniteLimits.preservesFiniteLimits (F := tilde.functor R) WalkingCospan
  have : PreservesLimitsOfShape WalkingCospan (tilde.functor S) :=
    PreservesFiniteLimits.preservesFiniteLimits (F := tilde.functor S) WalkingCospan
  have hT : IsIso (pullbackComparison (tilde.functor R) a b) := by
    rw [← PreservesPullback.iso_hom]
    infer_instance
  have hT' : IsIso (pullbackComparison (tilde.functor S)
      ((ModuleCat.extendScalars φ.hom).map a) ((ModuleCat.extendScalars φ.hom).map b)) := by
    rw [← PreservesPullback.iso_hom]
    infer_instance
  have h1 : IsIso (pullbackComparison (ModuleCat.extendScalars φ.hom ⋙ tilde.functor S) a b) := by
    rw [pullbackComparison_comp]
    infer_instance
  have h2 : IsIso (pullbackComparison
      (tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map φ)) a b) :=
    (isIso_pullbackComparison_iff_of_natIso (pullbackTildeIso R S φ) a b).2 h1
  rw [pullbackComparison_comp] at h2
  exact IsIso.of_isIso_comp_left
    ((Scheme.Modules.pullback (Spec.map φ)).map (pullbackComparison (tilde.functor R) a b)) _

/-- **The same for a cospan of quasi-coherent modules on `Spec R`**: pullback along
`Spec S ⟶ Spec R` preserves its fibre product as soon as `S ⊗_R -` preserves the fibre product of
the cospan of modules of global sections. A quasi-coherent module is the associated sheaf of its
global sections, naturally (the counit `AlgebraicGeometry.Scheme.Modules.fromTildeΓ`), so the
cospan is isomorphic to the associated cospan of its global sections. -/
theorem isIso_pullbackComparison_pullback_spec_map_of_isQuasicoherent {R S : CommRingCat.{u}}
    (φ : R ⟶ S) {M N P : (Spec R).Modules} (a : M ⟶ P) (b : N ⟶ P)
    [M.IsQuasicoherent] [N.IsQuasicoherent] [P.IsQuasicoherent]
    (h : IsIso (pullbackComparison (ModuleCat.extendScalars φ.hom)
      (moduleSpecΓFunctor.map a) (moduleSpecΓFunctor.map b))) :
    IsIso (pullbackComparison (Scheme.Modules.pullback (Spec.map φ)) a b) := by
  have hM := (isQuasicoherent_iff_isIso_fromTildeΓ M).mp inferInstance
  have hN := (isQuasicoherent_iff_isIso_fromTildeΓ N).mp inferInstance
  have hP := (isQuasicoherent_iff_isIso_fromTildeΓ P).mp inferInstance
  exact (isIso_pullbackComparison_iff_of_isIso (Scheme.Modules.pullback (Spec.map φ)) _ _ a b
    (Scheme.Modules.fromTildeΓ M) (Scheme.Modules.fromTildeΓ N) (Scheme.Modules.fromTildeΓ P)
    ((Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality a)
    ((Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality b)).1
    (isIso_pullbackComparison_pullback_spec_map_tilde φ _ _ h)

end AlgebraicGeometry

end
