module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsTensorComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.TensorBaseChangeProjection
public import StacksFrontier.AlgebraicGeometry.ProjectionFormulaInvertible.Abstract
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardTensorMap
public import StacksFrontier.CategoryTheory.Adjunction.ProjectionFormulaPushforwardSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BraidingNatIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RightUnitorNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedUnitorCoherenceUnitPullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormulaOfToposHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsDirectSums

/-!
# The projection map of `h` at a direct image, and at the structure sheaf

On `D(-_étale, Λ)` the projection map of a morphism of schemes `h : Y ⟶ X'` is
`A ⊗^L Rh_*B ⟶ Rh_*(h⁻¹A ⊗^L B)`
(`Stacks.EtaleCohomology.EtaleCoefficients.projectionMap`). The last paragraph of the proof of
[Stacks, Tag 0F1J] computes it at `A = Rπ'_*Λ̲` for a finite `π' : X'' ⟶ X'`. This file proves
the two facts that computation rests on, for an arbitrary commutative square

```
X'  <-h--  Y
^          ^
π'         ρ
X'' <-hᵢ-- Y''
```

* **At a direct image** (`isIso_projectionMap_pushforward`): the projection map of `h` at
  `(Rπ'_*E, G)` is invertible as soon as the projection formula maps of `π'` and `ρ`, the base
  change maps `π'⁻¹Rh_* ⟶ Rhᵢ_*ρ⁻¹` at `G` and `h⁻¹Rπ'_* ⟶ Rρ_*hᵢ⁻¹` at `E`, and the projection
  map of `hᵢ` at `(E, ρ⁻¹G)` are. Pushed forward to `X'` the two ways around the square agree:
  this is `Stacks.AffineProjectionFormula.adjunctionTensorMap_pushforward_square`, whose one
  input, the compatibility of the four comparisons of [Stacks, Tag 07A4] around the square, is
  `tensorComparisonCompatible_pullbackTensorIso`.
* **At the structure sheaf** (`isIso_projectionMap_of_iso_unit`): the projection map at an
  object isomorphic to `Λ̲[0]` is invertible, tensoring by `Λ̲[0]` on the left being the identity
  (`tensorUnitIso`: the commutativity constraint followed by the right unit constraint).

## Main results

All in the namespace `Stacks.EtaleCohomology.EtaleCoefficients`.

* `isIso_projectionMap_pushforward`, `isIso_projectionMap_of_iso_unit`.
* `isIso_projectionMap_iff_of_iso` — the projection map is invertible at isomorphic first
  variables together.

In `Stacks.ProjectionFormula`, over abstract adjunctions:

* `isIso_adjunctionTensorMapSnd_of_isEquivalence_tensorRightOf` — the projection-formula map with
  the counit in the second factor is invertible when tensoring on the left by `H` and by `L H` are
  equivalences; it is the one with the counit in the first factor for the bifunctors with
  interchanged variables (`adjunctionTensorMapSnd_eq_adjunctionTensorMap_swap`).

## Implementation notes

The projection formula map of [Stacks, Tag 0F0G] enters as
`Stacks.Cohomology.ProjectionFormulaOnRingedTopoi.projectionFormulaMap` along the morphism of
ringed topoi `ringedToposHom Λ f`, which is
`Stacks.EtaleCohomology.EtaleCoefficients.projectionFormulaMap` by definition; the module of the
latter declares a `pushforwardCompIso` that collides with the one of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsAbelianBaseChange`,
imported here, so it is not imported.

The base change maps of the square appear with an equation of the square each
(`w'`, `w''`): matching two base change maps whose equations are different proofs of the same
equation unfolds the base change map in the kernel.

The derived categories are the standard model, as at line 394 of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/AdjunctionForRingedTopoi.lean`.

## References

* [Stacks Project, Tag 0F1J](https://stacks.math.columbia.edu/tag/0F1J)
* [Stacks Project, Tag 0F0G](https://stacks.math.columbia.edu/tag/0F0G)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Prod

universe u

namespace Stacks.ProjectionFormula

variable {C : Type*} [Category C] {D : Type*} [Category D] {L : C ⥤ D} {R : D ⥤ C}
  (adj : L ⊣ R) (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)

/-- The comparison `α` read on the bifunctors with their two variables interchanged. -/
def swapComparison :
    (CategoryTheory.Prod.swap C C ⋙ A) ⋙ L ⟶ L.prod L ⋙ (CategoryTheory.Prod.swap D D ⋙ B) :=
  Functor.whiskerLeft (CategoryTheory.Prod.swap C C) α

/-- The projection-formula map with the counit in the second factor is the one with the counit
in the first factor, for the bifunctors with their variables interchanged. -/
theorem adjunctionTensorMapSnd_eq_adjunctionTensorMap_swap (H : C) (G : D) :
    adjunctionTensorMapSnd adj A B α H G =
      adjunctionTensorMap adj (CategoryTheory.Prod.swap C C ⋙ A)
        (CategoryTheory.Prod.swap D D ⋙ B) (swapComparison A B α) G H :=
  rfl

/-- **The projection-formula map with the counit in the second factor is an isomorphism** when
tensoring on the left by `H`, and by `L H`, are equivalences and the comparison is invertible
with `H` in the first variable. -/
theorem isIso_adjunctionTensorMapSnd_of_isEquivalence_tensorRightOf (H : C) (G : D)
    [(tensorRightOf (CategoryTheory.Prod.swap C C ⋙ A) H).IsEquivalence]
    [(tensorRightOf (CategoryTheory.Prod.swap D D ⋙ B) (L.obj H)).IsEquivalence]
    (hα : ∀ M : C, IsIso (α.app (H, M))) :
    IsIso (adjunctionTensorMapSnd adj A B α H G) := by
  rw [adjunctionTensorMapSnd_eq_adjunctionTensorMap_swap]
  exact isIso_adjunctionTensorMap adj _ _ _ G H hα

end Stacks.ProjectionFormula

namespace Stacks.EtaleCohomology.EtaleCoefficients

-- `derivedPullback` (`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/
-- AdjunctionForRingedTopoi.lean:394`) is stated for the standard model of the derived category.
attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type (u + 1)) [CommRing Λ]

/-! ### The projection map at the structure sheaf -/

section Unit

/-- The structure sheaf `Λ̲[0]` of `D(X_étale, Λ)`. -/
abbrev unit (X : Scheme.{u}) : DerivedModules Λ X :=
  Stacks.DerivedTensor.RingedSite.unitObject
    ⟨(ringedTopos Λ X).C, (ringedTopos Λ X).J, (ringedTopos Λ X).O⟩

/-- Tensoring on the left by `H`, read through the bifunctor with interchanged variables, is
`H ⊗^L -`. -/
def tensorRightOfSwapIso {X : Scheme.{u}} (H : DerivedModules Λ X) :
    Stacks.ProjectionFormula.tensorRightOf
        (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj (tensor Λ X)) H ≅
      (tensor Λ X).obj H :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro M M' g
    dsimp
    rw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, Category.comp_id])

/-- **`Λ̲[0] ⊗^L -` is the identity**: the commutativity constraint followed by the right unit
constraint of the derived tensor product. -/
def tensorUnitIso (X : Scheme.{u}) : (tensor Λ X).obj (unit Λ X) ≅ 𝟭 (DerivedModules Λ X) :=
  Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.tensorFlipSlotIso
      ⟨(ringedTopos Λ X).C, (ringedTopos Λ X).J, (ringedTopos Λ X).O⟩
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct (ringedTopos Λ X).O)
      (unit Λ X) ≪≫
    Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitorNatIso
      ⟨(ringedTopos Λ X).C, (ringedTopos Λ X).J, (ringedTopos Λ X).O⟩
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct (ringedTopos Λ X).O)

/-- Tensoring on the left by an object isomorphic to `Λ̲[0]` is an equivalence. -/
theorem isEquivalence_tensorRightOf_swap_of_iso {X : Scheme.{u}} {H : DerivedModules Λ X}
    (i : H ≅ unit Λ X) :
    (Stacks.ProjectionFormula.tensorRightOf
      (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj (tensor Λ X)) H).IsEquivalence :=
  Functor.isEquivalence_of_iso
    (tensorRightOfSwapIso Λ H ≪≫ (tensor Λ X).mapIso i ≪≫ tensorUnitIso Λ X).symm

/-- `f⁻¹Λ̲[0] ≅ Λ̲[0]`. -/
def pullbackUnitIso {X Y : Scheme.{u}} (f : X ⟶ Y) : (pullback Λ f).obj (unit Λ Y) ≅ unit Λ X :=
  Stacks.Sheaves.DerivedPullback.derivedPullbackUnitIso (ringedToposHom Λ f)
    (isMorphismOfSites_ringedToposHom Λ f)

/-- The projection map at `H` is invertible when tensoring on the left by `H` and by `h⁻¹H` are
equivalences. -/
private theorem isIso_projectionMap_of_isEquivalence {X' Y : Scheme.{u}} (h : Y ⟶ X')
    (H : DerivedModules Λ X') (B : DerivedModules Λ Y)
    [(Stacks.ProjectionFormula.tensorRightOf
      (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj (tensor Λ X')) H).IsEquivalence]
    [(Stacks.ProjectionFormula.tensorRightOf
      (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj (tensor Λ Y))
        ((pullback Λ h).obj H)).IsEquivalence] :
    IsIso (projectionMap Λ h H B) :=
  Stacks.ProjectionFormula.isIso_adjunctionTensorMapSnd_of_isEquivalence_tensorRightOf
    (adjunction Λ h)
    (Functor.uncurry.obj (tensor Λ X')) (Functor.uncurry.obj (tensor Λ Y))
    (pullbackTensorIso Λ h).hom H B (fun _ => inferInstance)

/-- **The projection map at an object isomorphic to the structure sheaf is invertible**: for
`h : Y ⟶ X'`, `H ≅ Λ̲[0]` and every `B`, the map `H ⊗^L Rh_*B ⟶ Rh_*(h⁻¹H ⊗^L B)` is an
isomorphism. Tensoring by `H` and by `h⁻¹H ≅ Λ̲[0]` on the left is an equivalence. -/
theorem isIso_projectionMap_of_iso_unit {X' Y : Scheme.{u}} (h : Y ⟶ X')
    {H : DerivedModules Λ X'} (i : H ≅ unit Λ X') (B : DerivedModules Λ Y) :
    IsIso (projectionMap Λ h H B) := by
  have := isEquivalence_tensorRightOf_swap_of_iso Λ i
  have := isEquivalence_tensorRightOf_swap_of_iso Λ
    ((pullback Λ h).mapIso i ≪≫ pullbackUnitIso Λ h)
  exact isIso_projectionMap_of_isEquivalence Λ h H B

/-- **`Λ̲[0]⟦s⟧ ⊗^L -` is the shift by `s`.** -/
def tensorUnitShiftIso (X : Scheme.{u}) (s : ℤ) :
    (tensor Λ X).obj ((unit Λ X)⟦s⟧) ≅ shiftFunctor (DerivedModules Λ X) s :=
  Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.tensorFlipSlotIso
      ⟨(ringedTopos Λ X).C, (ringedTopos Λ X).J, (ringedTopos Λ X).O⟩
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct (ringedTopos Λ X).O)
      ((unit Λ X)⟦s⟧) ≪≫
    Functor.flipObjShiftIsoOfUnitor (tensor Λ X) (unit Λ X)
      (Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitorNatIso
        ⟨(ringedTopos Λ X).C, (ringedTopos Λ X).J, (ringedTopos Λ X).O⟩
        (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct (ringedTopos Λ X).O)) s

/-- Tensoring on the left by an object isomorphic to a shift of `Λ̲[0]` is an equivalence. -/
theorem isEquivalence_tensorRightOf_swap_of_iso_shift {X : Scheme.{u}} {H : DerivedModules Λ X}
    {s : ℤ} (i : H ≅ (unit Λ X)⟦s⟧) :
    (Stacks.ProjectionFormula.tensorRightOf
      (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj (tensor Λ X)) H).IsEquivalence :=
  Functor.isEquivalence_of_iso
    (tensorRightOfSwapIso Λ H ≪≫ (tensor Λ X).mapIso i ≪≫ tensorUnitShiftIso Λ X s).symm

/-- `f⁻¹(Λ̲[0]⟦s⟧) ≅ Λ̲[0]⟦s⟧`. -/
def pullbackUnitShiftIso' {X Y : Scheme.{u}} (f : X ⟶ Y) (s : ℤ) :
    (pullback Λ f).obj ((unit Λ Y)⟦s⟧) ≅ (unit Λ X)⟦s⟧ :=
  ((pullback Λ f).commShiftIso s).app _ ≪≫ (shiftFunctor _ s).mapIso (pullbackUnitIso Λ f)

/-- **The projection map at an object isomorphic to a shift of the structure sheaf is
invertible.** -/
theorem isIso_projectionMap_of_iso_unitShift {X' Y : Scheme.{u}} (h : Y ⟶ X')
    {H : DerivedModules Λ X'} {s : ℤ} (i : H ≅ (unit Λ X')⟦s⟧) (B : DerivedModules Λ Y) :
    IsIso (projectionMap Λ h H B) := by
  have := isEquivalence_tensorRightOf_swap_of_iso_shift Λ i
  have := isEquivalence_tensorRightOf_swap_of_iso_shift Λ
    ((pullback Λ h).mapIso i ≪≫ pullbackUnitShiftIso' Λ h s)
  exact isIso_projectionMap_of_isEquivalence Λ h H B

end Unit

/-! ### The projection map at a direct image, around a square -/

section Unfold

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- `projectionMap` is the projection-formula map with the counit in the second factor. -/
theorem projectionMap_eq_adjunctionTensorMapSnd (A : DerivedModules Λ Y)
    (B : DerivedModules Λ X) :
    projectionMap Λ f A B =
      Stacks.ProjectionFormula.adjunctionTensorMapSnd (adjunction Λ f)
        (Functor.uncurry.obj (tensor Λ Y)) (Functor.uncurry.obj (tensor Λ X))
        (pullbackTensorIso Λ f).hom A B :=
  rfl

/-- The projection formula map of Stacks 0B56 along `f` is the projection-formula map with the
counit in the first factor. -/
theorem projectionFormulaMap_eq_adjunctionTensorMap (E : DerivedModules Λ X)
    (K : DerivedModules Λ Y) :
    Stacks.Cohomology.ProjectionFormulaOnRingedTopoi.projectionFormulaMap (ringedToposHom Λ f)
        (isMorphismOfSites_ringedToposHom Λ f) E K =
      adjunctionTensorMap (adjunction Λ f) (Functor.uncurry.obj (tensor Λ Y))
        (Functor.uncurry.obj (tensor Λ X)) (pullbackTensorIso Λ f).hom E K :=
  rfl

/-- The projection map is natural in its first variable. -/
theorem projectionMap_naturality_left {A A' : DerivedModules Λ Y} (a : A ⟶ A')
    (B : DerivedModules Λ X) :
    (Functor.uncurry.obj (tensor Λ Y)).map (a ×ₘ 𝟙 ((pushforward Λ f).obj B)) ≫
        projectionMap Λ f A' B =
      projectionMap Λ f A B ≫
        (pushforward Λ f).map
          ((Functor.uncurry.obj (tensor Λ X)).map ((pullback Λ f).map a ×ₘ 𝟙 B)) := by
  have h := Stacks.Cohomology.AbstractKunnethMap.projectionMap_naturality
    (Functor.uncurry.obj (tensor Λ Y)) (Functor.uncurry.obj (tensor Λ X)) (adjunction Λ f)
    (pullbackTensorIso Λ f).hom a (𝟙 B)
  rwa [CategoryTheory.Functor.map_id] at h

/-- **The projection map is invertible at isomorphic first variables together.** -/
theorem isIso_projectionMap_iff_of_iso {A A' : DerivedModules Λ Y} (a : A ≅ A')
    (B : DerivedModules Λ X) :
    IsIso (projectionMap Λ f A B) ↔ IsIso (projectionMap Λ f A' B) := by
  have i₁ : IsIso (a.hom ×ₘ 𝟙 ((pushforward Λ f).obj B)) :=
    (Iso.prod a (Iso.refl _)).isIso_hom
  have i₂ : IsIso ((pullback Λ f).map a.hom ×ₘ 𝟙 B) :=
    (Iso.prod ((pullback Λ f).mapIso a) (Iso.refl _)).isIso_hom
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · exact IsIso.of_isIso_fac_left (projectionMap_naturality_left Λ f a.hom B)
  · exact IsIso.of_isIso_fac_right (projectionMap_naturality_left Λ f a.hom B).symm

/-- **The projection map as a natural transformation of its first variable**, for fixed
`B ∈ D(Y_étale, Λ)`: `A ⊗^L Rf_*B ⟶ Rf_*(f⁻¹A ⊗^L B)`. -/
def projectionNatTrans (B : DerivedModules Λ X) :
    (tensor Λ Y).flip.obj ((pushforward Λ f).obj B) ⟶
      pullback Λ f ⋙ (tensor Λ X).flip.obj B ⋙ pushforward Λ f where
  app A := projectionMap Λ f A B
  naturality A A' a := by
    simpa using projectionMap_naturality_left Λ f a B

/-- The component of `projectionNatTrans Λ f B` at `A` is `projectionMap Λ f A B`. -/
theorem projectionNatTrans_app (B : DerivedModules Λ X) (A : DerivedModules Λ Y) :
    (projectionNatTrans Λ f B).app A = projectionMap Λ f A B :=
  rfl

end Unfold

section Square

variable {X' X'' Y Y'' : Scheme.{u}} (π' : X'' ⟶ X') (h : Y ⟶ X') (hi : Y'' ⟶ X'')
  (ρ : Y'' ⟶ Y) (w : ρ ≫ h = hi ≫ π')

/-- The base change map `h⁻¹Rπ'_* ⟶ Rρ_*hᵢ⁻¹` of the square, as the abstract
`Stacks.CategoryTheory.BaseChange.map` for the identifications of the two composite inverse
images through `(hᵢ ≫ π')⁻¹`. -/
theorem baseChange_map_eq_baseChangeMap_app_left (E : DerivedModules Λ X'') :
    Stacks.CategoryTheory.BaseChange.map (adjunction Λ π') (adjunction Λ ρ)
        (pullbackCompIso Λ ρ h ≪≫ eqToIso (congrArg (fun m : Y'' ⟶ X' => pullback Λ m) w))
        (pullbackCompIso Λ hi π') E =
      (baseChangeMap Λ h π' ρ hi w).app E := by
  have hβ : (pullbackCompIso Λ ρ h ≪≫
        eqToIso (congrArg (fun m : Y'' ⟶ X' => pullback Λ m) w)).hom ≫
      (pullbackCompIso Λ hi π').inv =
      (pullbackCompIso Λ ρ h ≪≫ pullbackCongr Λ w ≪≫ (pullbackCompIso Λ hi π').symm).hom := by
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rfl
  simp only [Stacks.CategoryTheory.BaseChange.map, Stacks.CategoryTheory.BaseChange.twoSquare,
    Stacks.CategoryTheory.BaseChange.pullbackComparison, baseChangeMap,
    Stacks.Cohomology.AbstractKunnethMap.baseChangeMap]
  rw [hβ]

/-- The base change map `π'⁻¹Rh_* ⟶ Rhᵢ_*ρ⁻¹` of the square, as the abstract
`Stacks.CategoryTheory.BaseChange.map` for the same identifications. -/
theorem baseChange_map_eq_baseChangeMap_app_right (G : DerivedModules Λ Y) :
    Stacks.CategoryTheory.BaseChange.map (adjunction Λ h) (adjunction Λ hi)
        (pullbackCompIso Λ hi π')
        (pullbackCompIso Λ ρ h ≪≫ eqToIso (congrArg (fun m : Y'' ⟶ X' => pullback Λ m) w)) G =
      (baseChangeMap Λ π' h hi ρ w.symm).app G := by
  have hβ : (pullbackCompIso Λ hi π').hom ≫ (pullbackCompIso Λ ρ h ≪≫
        eqToIso (congrArg (fun m : Y'' ⟶ X' => pullback Λ m) w)).inv =
      (pullbackCompIso Λ hi π' ≪≫ pullbackCongr Λ w.symm ≪≫
        (pullbackCompIso Λ ρ h).symm).hom := by
    simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom]
    rfl
  simp only [Stacks.CategoryTheory.BaseChange.map, Stacks.CategoryTheory.BaseChange.twoSquare,
    Stacks.CategoryTheory.BaseChange.pullbackComparison, baseChangeMap,
    Stacks.Cohomology.AbstractKunnethMap.baseChangeMap]
  rw [hβ]

/-- **The projection map at a direct image.** For a commutative square `ρ ≫ h = hᵢ ≫ π'` of
schemes,

```
X'  <-h--  Y
^          ^
π'         ρ
X'' <-hᵢ-- Y''
```

`E ∈ D(X''_étale, Λ)` and `G ∈ D(Y_étale, Λ)`, the projection map
`Rπ'_*E ⊗^L Rh_*G ⟶ Rh_*(h⁻¹Rπ'_*E ⊗^L G)` of `h` is an isomorphism as soon as

* the projection formula map of `π'` at `(E, Rh_*G)` is,
* the base change map `π'⁻¹Rh_*G ⟶ Rhᵢ_*ρ⁻¹G` is,
* the projection map of `hᵢ` at `(E, ρ⁻¹G)` is,
* the base change map `h⁻¹Rπ'_*E ⟶ Rρ_*hᵢ⁻¹E` is, and
* the projection formula map of `ρ` at `(hᵢ⁻¹E, G)` is.

Pushed forward to `X'`, the two ways around the square agree
(`Stacks.AffineProjectionFormula.adjunctionTensorMap_pushforward_square`, whose one input is
`tensorComparisonCompatible_pullbackTensorIso`): the projection map of `h` followed by the second
base change map and the projection formula of `ρ` is the projection formula of `π'` followed by
`Rπ'_*` of the first base change map and of the projection map of `hᵢ`. -/
theorem isIso_projectionMap_pushforward (E : DerivedModules Λ X'') (G : DerivedModules Λ Y)
    (w' : hi ≫ π' = ρ ≫ h) (w'' : ρ ≫ h = hi ≫ π')
    (h₁ : IsIso (Stacks.Cohomology.ProjectionFormulaOnRingedTopoi.projectionFormulaMap
      (ringedToposHom Λ π') (isMorphismOfSites_ringedToposHom Λ π') E ((pushforward Λ h).obj G)))
    (h₂ : IsIso ((baseChangeMap Λ π' h hi ρ w').app G))
    (h₃ : IsIso (projectionMap Λ hi E ((pullback Λ ρ).obj G)))
    (h₄ : IsIso ((baseChangeMap Λ h π' ρ hi w'').app E))
    (h₅ : IsIso (Stacks.Cohomology.ProjectionFormulaOnRingedTopoi.projectionFormulaMap
      (ringedToposHom Λ ρ) (isMorphismOfSites_ringedToposHom Λ ρ) ((pullback Λ hi).obj E) G)) :
    IsIso (projectionMap Λ h ((pushforward Λ π').obj E) G) := by
  obtain rfl : w' = w''.symm := rfl
  have key := Stacks.AffineProjectionFormula.adjunctionTensorMap_pushforward_square
    (adjunction Λ π') (adjunction Λ h) (adjunction Λ ρ) (adjunction Λ hi)
    (pullbackCompIso Λ ρ h ≪≫ eqToIso (congrArg (fun m : Y'' ⟶ X' => pullback Λ m) w''))
    (pullbackCompIso Λ hi π')
    (Functor.uncurry.obj (tensor Λ X')) (Functor.uncurry.obj (tensor Λ X''))
    (Functor.uncurry.obj (tensor Λ Y)) (Functor.uncurry.obj (tensor Λ Y''))
    (pullbackTensorIso Λ π').hom (pullbackTensorIso Λ h).hom (pullbackTensorIso Λ ρ).hom
    (pullbackTensorIso Λ hi).hom E G
    (tensorComparisonCompatible_pullbackTensorIso Λ ρ h hi π' w'' _ _)
  rw [baseChange_map_eq_baseChangeMap_app_left Λ π' h hi ρ w'',
    baseChange_map_eq_baseChangeMap_app_right Λ π' h hi ρ w''] at key
  rw [projectionFormulaMap_eq_adjunctionTensorMap] at h₁ h₅
  rw [projectionMap_eq_adjunctionTensorMapSnd] at h₃ ⊢
  have i₂ : IsIso (𝟙 E ×ₘ (baseChangeMap Λ π' h hi ρ w''.symm).app G) :=
    (Iso.prod (Iso.refl _) (asIso ((baseChangeMap Λ π' h hi ρ w''.symm).app G))).isIso_hom
  have i₄ : IsIso ((baseChangeMap Λ h π' ρ hi w'').app E ×ₘ 𝟙 G) :=
    (Iso.prod (asIso ((baseChangeMap Λ h π' ρ hi w'').app E)) (Iso.refl _)).isIso_hom
  exact IsIso.of_isIso_fac_right key.symm

end Square

end Stacks.EtaleCohomology.EtaleCoefficients

end
