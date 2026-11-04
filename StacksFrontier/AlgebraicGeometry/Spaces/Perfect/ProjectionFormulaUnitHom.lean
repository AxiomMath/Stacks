module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedPushforwardPullbackTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleProjectionFormulaIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackStructureSheaf
public import StacksFrontier.CategoryTheory.Adjunction.ProjectionFormulaMapCurried

/-!
# Morphisms out of the structure sheaf and the projection formula

Let `f : X ⟶ Y` be a morphism of algebraic spaces, `P ∈ D(𝒪_X)` and `M ∈ D(𝒪_Y)`.  The
projection formula map `Rf_*P ⊗^L M ⟶ Rf_*(P ⊗^L Lf^*M)` (Stacks 08IN), the adjunction
`Lf^* ⊣ Rf_*` and `Lf^*𝒪_Y = 𝒪_X` give a map

`Hom(𝒪_Y, Rf_*P ⊗^L M) ⟶ Hom(𝒪_X, P ⊗^L Lf^*M)`,

natural in `M`.  It is bijective when `f` is quasi-compact and quasi-separated and `P`, `M` have
quasi-coherent cohomology, since the projection formula map is then invertible.  Read at the
shifts `M⟦i⟧` this is the identification `H^i(Y, Rf_*P ⊗^L M) = H^i(X, P ⊗^L Lf^*M)` of the
proof of Stacks 0A1M (Leray and the projection formula); being natural in `M` for every morphism
of `D(𝒪_Y)`, it is compatible with the boundary maps of distinguished triangles.

## Main definitions

* `AlgebraicGeometry.Space.unitHomProjectionFormula`: the natural transformation above.

## Main results

* `AlgebraicGeometry.Space.isIso_unitHomProjectionFormula_app`: it is invertible at `M` in
  `D_QCoh(𝒪_Y)` for `f` quasi-compact and quasi-separated and `P ∈ D_QCoh(𝒪_X)`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.Cohomology.DerivedPushforward (derivedPushforward)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- `Lf^*𝒪_Y[0] ≅ 𝒪_X[0]` for a morphism of algebraic spaces. -/
def smallEtaleDerivedPullbackUnitIso (f : X ⟶ Y) :
    (smallEtaleDerivedModulePullback B S hS f).obj (structureDerived Y) ≅
      structureDerived X :=
  Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackUnitIsoGeneral
    (smallEtaleRingedToposHom B S hS f)

/-- The derived pushforward `Rf_*` along a morphism of algebraic spaces is additive. -/
instance (f : X ⟶ Y) : (derivedPushforward (X := smallEtaleRingedTopos B S hS _)
    (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f)).Additive :=
  Functor.IsTriangulated.instAdditive (derivedModulePushforward B S hS f)

/-- The derived pullback `Lf^*` along a morphism of algebraic spaces is additive, as a left
adjoint. -/
instance (f : X ⟶ Y) : (smallEtaleDerivedModulePullback B S hS f).Additive :=
  (smallEtaleDerivedModuleAdjunction B S hS f).left_adjoint_additive

/-- **The projection formula map is natural in its second argument.** -/
@[reassoc]
theorem smallEtaleProjectionFormulaMap_natural_right (f : X ⟶ Y)
    (P : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    {M M' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))}
    (k : M ⟶ M') :
    ((smallEtaleDerivedTensor B S hS Y).obj
        ((derivedPushforward (X := smallEtaleRingedTopos B S hS _)
          (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f)).obj P)).map k ≫
        smallEtaleProjectionFormulaMap B S hS f P M' =
      smallEtaleProjectionFormulaMap B S hS f P M ≫
        (derivedPushforward (X := smallEtaleRingedTopos B S hS _)
          (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f)).map
          (((smallEtaleDerivedTensor B S hS X).obj P).map
            ((smallEtaleDerivedModulePullback B S hS f).map k)) :=
  adjunctionTensorMap_natural_right_curried (smallEtaleDerivedModuleAdjunction B S hS f)
    (smallEtaleDerivedTensor B S hS Y) (smallEtaleDerivedTensor B S hS X)
    (smallEtaleDerivedPullbackTensorIso f).hom P k

/-- The component at `M` of `unitHomProjectionFormula`: a morphism `g : 𝒪_Y ⟶ Rf_*P ⊗^L M` goes
to the adjoint of `g` followed by the projection formula map, precomposed with
`𝒪_X ≅ Lf^*𝒪_Y`. -/
def unitHomProjectionFormulaApp (f : X ⟶ Y)
    (P : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) :
    (structureDerived Y ⟶ ((smallEtaleDerivedTensor B S hS Y).obj
        ((derivedPushforward (X := smallEtaleRingedTopos B S hS _)
          (Y := smallEtaleRingedTopos B S hS _)
          (smallEtaleRingedToposHom B S hS f)).obj P)).obj M) →+
      (structureDerived X ⟶ ((smallEtaleDerivedTensor B S hS X).obj P).obj
        ((smallEtaleDerivedModulePullback B S hS f).obj M)) :=
  (Preadditive.leftComp _ (smallEtaleDerivedPullbackUnitIso B S hS f).inv).comp
    ((((smallEtaleDerivedModuleAdjunction B S hS f).homAddEquiv _ _).symm.toAddMonoidHom).comp
      (Preadditive.rightComp _ (smallEtaleProjectionFormulaMap B S hS f P M)))

/-- `unitHomProjectionFormulaApp` sends `g` to `ε⁻¹ ≫ (g ≫ τ)♭`, where `τ` is the projection
formula map, `♭` the adjoint along `Lf^* ⊣ Rf_*` and `ε : Lf^*𝒪_Y ≅ 𝒪_X`. -/
theorem unitHomProjectionFormulaApp_apply (f : X ⟶ Y)
    (P : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (g : structureDerived Y ⟶ ((smallEtaleDerivedTensor B S hS Y).obj
        ((derivedPushforward (X := smallEtaleRingedTopos B S hS _)
          (Y := smallEtaleRingedTopos B S hS _)
          (smallEtaleRingedToposHom B S hS f)).obj P)).obj M) :
    unitHomProjectionFormulaApp B S hS f P M g =
      (smallEtaleDerivedPullbackUnitIso B S hS f).inv ≫
        ((smallEtaleDerivedModuleAdjunction B S hS f).homEquiv _ _).symm
          (g ≫ smallEtaleProjectionFormulaMap B S hS f P M) :=
  rfl

/-- `unitHomProjectionFormulaApp` is natural in `M ∈ D(𝒪_Y)`. -/
theorem unitHomProjectionFormulaApp_naturality (f : X ⟶ Y)
    (P : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    {M M' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))}
    (k : M ⟶ M')
    (g : structureDerived Y ⟶ ((smallEtaleDerivedTensor B S hS Y).obj
        ((derivedPushforward (X := smallEtaleRingedTopos B S hS _)
          (Y := smallEtaleRingedTopos B S hS _)
          (smallEtaleRingedToposHom B S hS f)).obj P)).obj M) :
    unitHomProjectionFormulaApp B S hS f P M' (g ≫ ((smallEtaleDerivedTensor B S hS Y).obj
        ((derivedPushforward (X := smallEtaleRingedTopos B S hS _)
          (Y := smallEtaleRingedTopos B S hS _)
          (smallEtaleRingedToposHom B S hS f)).obj P)).map k) =
      unitHomProjectionFormulaApp B S hS f P M g ≫
        ((smallEtaleDerivedTensor B S hS X).obj P).map
          ((smallEtaleDerivedModulePullback B S hS f).map k) := by
  simp only [unitHomProjectionFormulaApp_apply, Category.assoc,
    smallEtaleProjectionFormulaMap_natural_right]
  rw [← Category.assoc g, Adjunction.homEquiv_naturality_right_symm, ← Category.assoc]

/-- **`Hom(𝒪_Y, Rf_*P ⊗^L M) ⟶ Hom(𝒪_X, P ⊗^L Lf^*M)`, natural in `M ∈ D(𝒪_Y)`**: the
projection formula map, the adjunction `Lf^* ⊣ Rf_*` and `Lf^*𝒪_Y = 𝒪_X`. -/
def unitHomProjectionFormula (f : X ⟶ Y)
    (P : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    (smallEtaleDerivedTensor B S hS Y).obj
        ((derivedPushforward (X := smallEtaleRingedTopos B S hS _)
          (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS f)).obj P) ⋙
        preadditiveCoyoneda.obj (op (structureDerived Y)) ⟶
      smallEtaleDerivedModulePullback B S hS f ⋙ (smallEtaleDerivedTensor B S hS X).obj P ⋙
        preadditiveCoyoneda.obj (op (structureDerived X)) where
  app M := AddCommGrpCat.ofHom (unitHomProjectionFormulaApp B S hS f P M)
  naturality {M M'} k := by
    ext g
    exact unitHomProjectionFormulaApp_naturality B S hS f P k g

/-- **The map is bijective in the situation of Stacks 08IN**: for `f` quasi-compact and
quasi-separated, `P ∈ D_QCoh(𝒪_X)` and `M ∈ D_QCoh(𝒪_Y)`,
`Hom(𝒪_Y, Rf_*P ⊗^L M) ⟶ Hom(𝒪_X, P ⊗^L Lf^*M)` is an isomorphism. -/
theorem isIso_unitHomProjectionFormula_app (f : X ⟶ Y) (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom)
    (P : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hP : QcohDerived B S hS X P)
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hM : QcohDerived B S hS Y M) :
    IsIso ((unitHomProjectionFormula B S hS f P).app M) := by
  have := isIso_smallEtaleProjectionFormulaMap B S hS f hfqc hfqs P hP M hM
  let τ := smallEtaleProjectionFormulaMap B S hS f P M
  let ε := smallEtaleDerivedPullbackUnitIso B S hS f
  have hb : Function.Bijective (fun g : structureDerived Y ⟶ _ => g ≫ τ) :=
    ⟨fun a b h => by simpa using congrArg (· ≫ inv τ) h, fun c => ⟨c ≫ inv τ, by simp⟩⟩
  have hd : Function.Bijective (fun h : (smallEtaleDerivedModulePullback B S hS f).obj
      (structureDerived Y) ⟶ ((smallEtaleDerivedTensor B S hS X).obj P).obj
        ((smallEtaleDerivedModulePullback B S hS f).obj M) => ε.inv ≫ h) :=
    ⟨fun a b h => by simpa using congrArg (ε.hom ≫ ·) h, fun c => ⟨ε.hom ≫ c, by simp⟩⟩
  exact (ConcreteCategory.isIso_iff_bijective _).2
    (hd.comp ((((smallEtaleDerivedModuleAdjunction B S hS f).homEquiv _ _).symm.bijective).comp hb))

end AlgebraicGeometry.Space

end
