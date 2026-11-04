module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.DerivedSectionsOnAPoint
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafifyUnitIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal

/-!
# The one-point identification is monoidal

Let `R` be a commutative ring and let `({*}, R)` be the one-point ringed space.  Sheafification
of presheaves of modules is trivial there, every presheaf of modules on a one-point space being a
sheaf, so the tensor product of sheaves of modules — the sheafification of `U ↦ F(U) ⊗_{𝒪(U)}
G(U)` — needs no sheafification correction and

`Γ({*}, F) ⊗_{Γ({*}, 𝒪)} Γ({*}, G) ≅ Γ({*}, F ⊗_{𝒪} G)`

with the canonical map as the isomorphism.  Equivalently the identification
`Mod(Γ({*}, 𝒪)) ≌ Mod(𝒪_{({*}, R)})` carries the tensor product of modules to the tensor product
of sheaves of modules.  This is the abelian half of the identification of the derived tensor
product over `Γ(S, 𝒪_S)` with the derived tensor product over `𝒪_S` that Cohomology, Section
0FKU uses on the one-point space; it is the step that has no analogue on a general space, where
the canonical map on sections is not invertible.

## Main definitions

* `Stacks.Cohomology.DerivedSectionsOnAPoint.onePointTensorSectionsMap` — the canonical map
  `Γ({*}, F) ⊗_{Γ({*}, 𝒪)} Γ({*}, G) ⟶ Γ({*}, F ⊗_{𝒪} G)`, as a morphism of bifunctors.
* `Stacks.Cohomology.DerivedSectionsOnAPoint.onePointTensorSectionsIso` — **sections of a tensor
  product are the tensor product of sections** on `({*}, R)`, as an isomorphism of bifunctors
  `Γ({*}, -) ⊗ Γ({*}, -) ≅ Γ({*}, - ⊗_{𝒪} -)`.
* `Stacks.Cohomology.DerivedSectionsOnAPoint.onePointTensorComparisonIso` — **the one-point
  identification is monoidal**: the isomorphism of bifunctors
  `E(x ⊗_{Γ({*}, 𝒪)} y) ≅ E x ⊗_{𝒪} E y` for `E` the identification
  `Stacks.Cohomology.DerivedSectionsOnAPoint.onePointSectionsEquivalence`; its value at a pair of
  modules is `Stacks.Cohomology.DerivedSectionsOnAPoint.onePointTensorIso`.

## Main results

* `Stacks.Cohomology.DerivedSectionsOnAPoint.isIso_onePointSheafificationUnit` — sheafification of
  presheaves of modules on the one-point ringed space is trivial: its unit is an isomorphism.
* `Stacks.Cohomology.DerivedSectionsOnAPoint.onePointTensorSectionsMap_app` — **the section
  formula**: the canonical map is, on sections over the whole space, the sheafification unit of the
  presheaf `U ↦ F(U) ⊗_{𝒪(U)} G(U)`, whose sections over the whole space are
  `Γ({*}, F) ⊗_{Γ({*}, 𝒪)} Γ({*}, G)` on the nose.
* `Stacks.Cohomology.DerivedSectionsOnAPoint.isIso_onePointTensorSectionsMap` — that canonical map
  is an isomorphism.
* `Stacks.Cohomology.DerivedSectionsOnAPoint.onePointTensorIso_naturality_left` and
  `Stacks.Cohomology.DerivedSectionsOnAPoint.onePointTensorIso_naturality_right` — the monoidal
  comparison is natural in each variable separately, in the form a transport of total complexes
  along the identification asks for.

## Implementation notes

*Why no monoidal coherence is claimed.*  The tensor product of sheaves of modules carries its
associator and unitors from the localization of the presheaf-level monoidal structure along
sheafification, and those have no description on local sections; so the comparison is produced
here as an isomorphism of bifunctors, which is what a comparison of two tensor products asks for,
and not as a `CategoryTheory.Functor.Monoidal` structure.

*Where the isomorphism comes from.*  All three of the identifications
`Γ({*}, F) ⊗ Γ({*}, G) = (F ⊗_{pre} G)({*})`, `F ⊗_{𝒪} G = (F ⊗_{pre} G)^{#}` and
`Γ({*}, -) = Γ_{pre}({*}, -)` after forgetting the sheaf condition hold by definition, the
presheaf tensor product being objectwise and restriction of scalars along an identity being the
identity functor.  So the comparison *is* the sheafification unit, read on sections over the whole
space, and its naturality in both variables is the naturality of that unit.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.AssociatedSheaf
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.GlobalKunneth
open Stacks.SheafOfModules.Tensor
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.DerivedSectionsOnAPoint

variable (R : Type u) [CommRing R]

/-! ### Uncurried bifunctors on a morphism with an identity component -/

/-- An uncurried bifunctor precomposed with a product functor, on a morphism whose second
component is an identity. -/
private theorem prod_comp_uncurry_map_prod_id_right {A C D : Type*} [Category A] [Category C]
    [Category D] (P : A ⥤ C) (G : C ⥤ C ⥤ D) {X X' : A} (f : X ⟶ X') (Y : A) :
    ((P.prod P) ⋙ Functor.uncurry.obj G).map ((f : X ⟶ X') ×ₘ 𝟙 Y) =
      (G.map (P.map f)).app (P.obj Y) := by simp

/-- An uncurried bifunctor precomposed with a product functor, on a morphism whose first
component is an identity. -/
private theorem prod_comp_uncurry_map_prod_id_left {A C D : Type*} [Category A] [Category C]
    [Category D] (P : A ⥤ C) (G : C ⥤ C ⥤ D) (X : A) {Y Y' : A} (g : Y ⟶ Y') :
    ((P.prod P) ⋙ Functor.uncurry.obj G).map ((𝟙 X) ×ₘ (g : Y ⟶ Y')) =
      (G.obj (P.obj X)).map (P.map g) := by simp

/-! ### Sheafification on the one-point ringed space is trivial -/

/-- Presheaves of modules on the one-point ringed space. -/
abbrev onePointPresheafOfModules :=
  PresheafOfModules.{u} (structureSheafRing (onePointRingedSpace R)).obj

/-- The sheafification adjunction for presheaves of modules on the one-point ringed space. -/
abbrev onePointSheafificationAdjunction :=
  PresheafOfModules.sheafificationAdjunction (𝟙 (structureSheafRing (onePointRingedSpace R)).obj)

/-- **Sheafification of presheaves of modules on the one-point ringed space is trivial.**  Every
presheaf of modules there is a sheaf, so the unit of the sheafification adjunction is an
isomorphism. -/
instance isIso_onePointSheafificationUnit (N : onePointPresheafOfModules R) :
    IsIso ((onePointSheafificationAdjunction R).unit.app N) :=
  have := PresheafOfModules.isIso_toPresheaf_map_unit_app
    (𝟙 (structureSheafRing (onePointRingedSpace R)).obj) N
    (isSheaf_of_presheafOfModules_coefficientPoint N)
  isIso_of_reflects_iso _ (PresheafOfModules.toPresheaf _)

/-! ### Sections of a tensor product on the one-point ringed space -/

/-- The objectwise tensor product of the underlying presheaves of modules, as a bifunctor written
on pairs. -/
abbrev onePointPresheafTensor :
    SheafOfModules.{u} (structureSheafRing (onePointRingedSpace R)) ×
        SheafOfModules.{u} (structureSheafRing (onePointRingedSpace R)) ⥤
      onePointPresheafOfModules R :=
  ((SheafOfModules.forget _).prod (SheafOfModules.forget _)) ⋙
    Functor.uncurry.obj (PresheafOfModules.tensorBifunctor (onePointRingedSpace R).presheaf)

/-- The bifunctor `(F, G) ↦ Γ({*}, F) ⊗_{Γ({*}, 𝒪)} Γ({*}, G)` on the one-point ringed space. -/
abbrev onePointTensorOfSections :
    SheafOfModules.{u} (structureSheafRing (onePointRingedSpace R)) ×
        SheafOfModules.{u} (structureSheafRing (onePointRingedSpace R)) ⥤
      ModuleCat.{u} (baseRing (onePointRingedSpace R)) :=
  ((onePointSectionsEquivalence R).inverse.prod (onePointSectionsEquivalence R).inverse) ⋙
    Functor.uncurry.obj
      (MonoidalCategory.curriedTensor (ModuleCat.{u} (baseRing (onePointRingedSpace R))))

/-- The bifunctor `(F, G) ↦ Γ({*}, F ⊗_{𝒪} G)` on the one-point ringed space. -/
abbrev onePointSectionsOfTensor :
    SheafOfModules.{u} (structureSheafRing (onePointRingedSpace R)) ×
        SheafOfModules.{u} (structureSheafRing (onePointRingedSpace R)) ⥤
      ModuleCat.{u} (baseRing (onePointRingedSpace R)) :=
  Functor.uncurry.obj
      (sheafTensor ⟨(onePointRingedSpace R).presheaf, (onePointRingedSpace R).IsSheaf⟩) ⋙
    (onePointSectionsEquivalence R).inverse

/-- Sheafifying the objectwise tensor product of the underlying presheaves of modules is the
tensor product of sheaves of modules, written on pairs. -/
def onePointSheafifyPresheafTensorIso :
    onePointPresheafTensor R ⋙ PresheafOfModules.sheafification
        (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf
          ⟨(onePointRingedSpace R).presheaf, (onePointRingedSpace R).IsSheaf⟩).obj)
        (R := Stacks.SheafOfModules.Tensor.ringSheaf
          ⟨(onePointRingedSpace R).presheaf, (onePointRingedSpace R).IsSheaf⟩)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
          ⟨(onePointRingedSpace R).presheaf, (onePointRingedSpace R).IsSheaf⟩).obj) ≅
      (Functor.uncurry.obj
          (sheafTensor ⟨(onePointRingedSpace R).presheaf, (onePointRingedSpace R).IsSheaf⟩) :
        SheafOfModules.{u} (structureSheafRing (onePointRingedSpace R)) ×
            SheafOfModules.{u} (structureSheafRing (onePointRingedSpace R)) ⥤
          SheafOfModules.{u} (structureSheafRing (onePointRingedSpace R))) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ by
    simp only [Iso.refl_hom]
    exact (PresheafOfModules.sheafification
        (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf
          ⟨(onePointRingedSpace R).presheaf, (onePointRingedSpace R).IsSheaf⟩).obj)
        (R := Stacks.SheafOfModules.Tensor.ringSheaf
          ⟨(onePointRingedSpace R).presheaf, (onePointRingedSpace R).IsSheaf⟩)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
          ⟨(onePointRingedSpace R).presheaf, (onePointRingedSpace R).IsSheaf⟩).obj)).map_comp _ _

/-- **The canonical map from the tensor product of sections to the sections of the tensor
product** on the one-point ringed space, as a morphism of bifunctors: the sheafification unit of
the presheaf `U ↦ F(U) ⊗_{𝒪(U)} G(U)`, read on sections over the whole space. -/
def onePointTensorSectionsMap :
    onePointTensorOfSections R ⟶ onePointSectionsOfTensor R :=
  Functor.whiskerRight
      (Functor.whiskerLeft (onePointPresheafTensor R)
        (onePointSheafificationAdjunction R).unit)
      (PresheafOfModules.evaluation (structureSheafRing (onePointRingedSpace R)).obj (op ⊤)) ≫
    (Functor.isoWhiskerRight (onePointSheafifyPresheafTensorIso R)
      (onePointSectionsEquivalence R).inverse).hom

/-- **The section formula.**  The canonical map is the sheafification unit of the presheaf
`U ↦ F(U) ⊗_{𝒪(U)} G(U)`, taken on sections over the whole space; the source of that map is
`Γ({*}, F) ⊗_{Γ({*}, 𝒪)} Γ({*}, G)` by definition. -/
theorem onePointTensorSectionsMap_app
    (FG : SheafOfModules.{u} (structureSheafRing (onePointRingedSpace R)) ×
      SheafOfModules.{u} (structureSheafRing (onePointRingedSpace R))) :
    (onePointTensorSectionsMap R).app FG =
      PresheafOfModules.Hom.app
        ((onePointSheafificationAdjunction R).unit.app
          ((onePointPresheafTensor R).obj FG)) (op ⊤) := by
  rfl

/-- **Sections of a tensor product are the tensor product of sections** on the one-point ringed
space: the canonical map is an isomorphism, because sheafification there is trivial. -/
instance isIso_onePointTensorSectionsMap : IsIso (onePointTensorSectionsMap R) :=
  have : ∀ FG, IsIso ((onePointTensorSectionsMap R).app FG) := fun FG ↦ by
    rw [onePointTensorSectionsMap_app]
    exact inferInstanceAs (IsIso
      ((PresheafOfModules.evaluation (structureSheafRing (onePointRingedSpace R)).obj (op ⊤)).map
        ((onePointSheafificationAdjunction R).unit.app ((onePointPresheafTensor R).obj FG))))
  NatIso.isIso_of_isIso_app _

/-- **Sections of a tensor product are the tensor product of sections** on the one-point ringed
space, as an isomorphism of bifunctors

`Γ({*}, F) ⊗_{Γ({*}, 𝒪)} Γ({*}, G) ≅ Γ({*}, F ⊗_{𝒪} G)`. -/
def onePointTensorSectionsIso :
    onePointTensorOfSections R ≅ onePointSectionsOfTensor R :=
  asIso (onePointTensorSectionsMap R)

/-- The comparison of `Stacks.Cohomology.DerivedSectionsOnAPoint.onePointTensorSectionsIso` is
the canonical map, so the section formula applies to it. -/
@[simp]
theorem onePointTensorSectionsIso_hom :
    (onePointTensorSectionsIso R).hom = onePointTensorSectionsMap R := rfl

/-! ### The one-point identification is monoidal -/

/-- **The one-point identification is monoidal**: the isomorphism of bifunctors

`E(x ⊗_{Γ({*}, 𝒪)} y) ≅ E x ⊗_{𝒪} E y`

for `E` the identification `Mod(Γ({*}, 𝒪)) ≌ Mod(𝒪_{({*}, R)})`.  It is the comparison of
`Stacks.Cohomology.DerivedSectionsOnAPoint.onePointTensorSectionsIso` transported along the
equivalence. -/
def onePointTensorComparisonIso :
    Functor.uncurry.obj
          (MonoidalCategory.curriedTensor (ModuleCat.{u} (baseRing (onePointRingedSpace R)))) ⋙
        (onePointSectionsEquivalence R).functor ≅
      ((onePointSectionsEquivalence R).functor.prod (onePointSectionsEquivalence R).functor) ⋙
        Functor.uncurry.obj
          (sheafTensor ⟨(onePointRingedSpace R).presheaf, (onePointRingedSpace R).IsSheaf⟩) :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerRight
        ((onePointSectionsEquivalence R).prod (onePointSectionsEquivalence R)).unitIso
        (Functor.uncurry.obj (MonoidalCategory.curriedTensor
          (ModuleCat.{u} (baseRing (onePointRingedSpace R))))))
      (onePointSectionsEquivalence R).functor ≪≫
    Functor.isoWhiskerLeft
        ((onePointSectionsEquivalence R).functor.prod (onePointSectionsEquivalence R).functor)
        (Functor.isoWhiskerRight (onePointTensorSectionsIso R)
          (onePointSectionsEquivalence R).functor) ≪≫
      Functor.isoWhiskerLeft
        (((onePointSectionsEquivalence R).functor.prod
            (onePointSectionsEquivalence R).functor) ⋙
          Functor.uncurry.obj
            (sheafTensor ⟨(onePointRingedSpace R).presheaf, (onePointRingedSpace R).IsSheaf⟩))
        (onePointSectionsEquivalence R).counitIso

/-- **The one-point identification carries the tensor product of modules to the tensor product
of sheaves of modules**: `E(M ⊗_{Γ({*}, 𝒪)} N) ≅ E M ⊗_{𝒪} E N`. -/
abbrev onePointTensorIso (M N : ModuleCat.{u} (baseRing (onePointRingedSpace R))) :
    (onePointSectionsEquivalence R).functor.obj
        (MonoidalCategory.tensorObj M N) ≅
      ((sheafTensor ⟨(onePointRingedSpace R).presheaf, (onePointRingedSpace R).IsSheaf⟩).obj
          ((onePointSectionsEquivalence R).functor.obj M)).obj
        ((onePointSectionsEquivalence R).functor.obj N) :=
  (onePointTensorComparisonIso R).app (M, N)

/-- The comparison of `Stacks.Cohomology.DerivedSectionsOnAPoint.onePointTensorIso` is natural in
the first variable. -/
theorem onePointTensorIso_naturality_left
    {M M' : ModuleCat.{u} (baseRing (onePointRingedSpace R))} (u : M ⟶ M')
    (N : ModuleCat.{u} (baseRing (onePointRingedSpace R))) :
    (onePointSectionsEquivalence R).functor.map
          (((MonoidalCategory.curriedTensor
            (ModuleCat.{u} (baseRing (onePointRingedSpace R)))).map u).app N) ≫
        (onePointTensorIso R M' N).hom =
      (onePointTensorIso R M N).hom ≫
        ((sheafTensor ⟨(onePointRingedSpace R).presheaf, (onePointRingedSpace R).IsSheaf⟩).map
            ((onePointSectionsEquivalence R).functor.map u)).app
          ((onePointSectionsEquivalence R).functor.obj N) :=
  by
  simpa using ((onePointTensorComparisonIso R).hom.naturality (u ×ₘ 𝟙 N)).trans
    (congrArg (_ ≫ ·) (prod_comp_uncurry_map_prod_id_right _ _ _ _))

/-- The comparison of `Stacks.Cohomology.DerivedSectionsOnAPoint.onePointTensorIso` is natural in
the second variable. -/
theorem onePointTensorIso_naturality_right
    (M : ModuleCat.{u} (baseRing (onePointRingedSpace R)))
    {N N' : ModuleCat.{u} (baseRing (onePointRingedSpace R))} (v : N ⟶ N') :
    (onePointSectionsEquivalence R).functor.map
          (((MonoidalCategory.curriedTensor
            (ModuleCat.{u} (baseRing (onePointRingedSpace R)))).obj M).map v) ≫
        (onePointTensorIso R M N').hom =
      (onePointTensorIso R M N).hom ≫
        ((sheafTensor ⟨(onePointRingedSpace R).presheaf, (onePointRingedSpace R).IsSheaf⟩).obj
            ((onePointSectionsEquivalence R).functor.obj M)).map
          ((onePointSectionsEquivalence R).functor.map v) :=
  by
  simpa using ((onePointTensorComparisonIso R).hom.naturality (𝟙 M ×ₘ v)).trans
    (congrArg (_ ≫ ·) (prod_comp_uncurry_map_prod_id_left _ _ _ _))

end Stacks.Cohomology.DerivedSectionsOnAPoint

end
