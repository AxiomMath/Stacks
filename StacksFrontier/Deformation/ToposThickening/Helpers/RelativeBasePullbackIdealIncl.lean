module

public import StacksFrontier.Deformation.ToposThickening.RelativeBaseIdeal
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesCompare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposUnitStructureMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnitValue
public import StacksFrontier.CategoryTheory.Adjunction.LeftAdjointUniqTranspose

/-!
# The ideal of the thickened base and the inclusions into `f'⁻¹O_{ℬ'}`

In the relative square of `Deformation.ToposThickening.relBase_comm`, the ideal `𝒥̃` of the
thickening `t̃ = (id, f'⁻¹t^♯)` is identified with the inverse image `f'⁻¹𝒥` of the ideal of `t`
(`Deformation.ToposThickening.relBaseIdealIso`). This file records that the identification is
compatible with the two inclusions into `f'⁻¹O_{ℬ'}`
(`Deformation.ToposThickening.relBaseIdealIso_hom_comp_map_incl`), and deduces the compatibility
of `f̃'^*𝒥̃ ≅ f'^*𝒥` (`Deformation.ToposThickening.relBasePullbackIdealIso`) with the canonical
maps into `O'`
(`Deformation.ToposThickening.relBasePullbackIdealIso_hom_comp_pullbackUnitStructureMap`).

## Main results

* `AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso_inv_app_comp_pullbackUnitStructureMap`:
  the comparison `f^*O ⟶ O'` of a composite, read through the comparison of pullbacks attached
  to an arbitrary comparison of the geometric direct images.
* `Deformation.ToposThickening.relBaseProjectionPullbackIso_inv_comp_pullbackUnitStructureMap`:
  read through `(projection)^*O_{ℬ'} ≅ f'⁻¹O_{ℬ'}`, the comparison of the projection is the
  identity.
* `Deformation.ToposThickening.relBasePullbackIdealIso_hom_comp_pullbackUnitStructureMap`:
  `f̃'^*𝒥̃ ≅ f'^*𝒥` is compatible with the maps into `O'`.

## Implementation notes

The same sheaf of rings `f'⁻¹O_{ℬ'}` occurs in several definitionally equal spellings (the inverse
image as a sheaf of rings, the structure sheaf of the thickened base, the pullback ring sheaf),
and the pullback along the projection as `(projection)^*` and as extension of scalars after the
inverse image. Equations whose two sides spell an intermediate object differently make the kernel
unfold the wrong side, so every chase is stated over abstract categories and functors
(`comp_chase`, `map_comp_comp_map_comp_comp`) and every transposition is stated with the
morphism as a variable fixed by an equation
(`relBaseProjection_fSharpAdjunction_homEquiv_pullbackIso_unit`).

## References

* [Stacks Project, Tag 08M7](https://stacks.math.columbia.edu/tag/08M7)
* [Stacks Project, Tag 0CYF](https://stacks.math.columbia.edu/tag/0CYF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.RingedToposModules (inverseImageModules)

universe v' u' w vS uS vS' uS'

namespace AlgebraicGeometry.RingedToposHom

section UnitComparisonFourField

universe v₁ u₁ w₁ v₂ u₂ w₂ v₃ u₃ w₃

variable {X : RingedTopos.{v₁, u₁, w₁}} {Y : RingedTopos.{v₂, u₂, w₂}}
  {Z : RingedTopos.{v₃, u₃, w₃}}
  [X.J.HasSheafCompose (forget RingCat.{w₁})]
  [Y.J.HasSheafCompose (forget RingCat.{w₂})]
  [Z.J.HasSheafCompose (forget RingCat.{w₃})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w₂} RingCat.{w₂})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w₃} RingCat.{w₃})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w₁})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w₂})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w₃})]
  [HasWeakSheafify X.J AddCommGrpCat.{w₁}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w₁}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w₂}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w₂}]

/-- A morphism into the source of a natural isomorphism, followed by its component, is the
morphism into the target followed back by the inverse component. -/
private theorem comp_inv_app_eq_of_comp_hom_app_eq {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (τ : F ≅ G) {A : C} {B : D} (a : B ⟶ F.obj A) (b : B ⟶ G.obj A)
    (h : a ≫ τ.hom.app A = b) : b ≫ τ.inv.app A = a := by
  rw [← h, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

omit [HasWeakSheafify X.J AddCommGrpCat.{w₁}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w₁}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w₂}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w₂}] in
/-- The unit-module structure map, read in the direct image of the modules development, is `f♯`
on underlying sheaves of sets. -/
theorem moduleSheafFunctor_map_unitStructureMap_comp_toModulesPushforwardIsoApp_inv
    (f : RingedToposHom X Y) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        (unitStructureMap f ≫ (f.toModulesPushforwardIsoApp
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).inv) =
      Stacks.Sheaves.RingedToposModules.fSharpSet f.toModulesHom := by
  rw [Functor.map_comp, moduleSheafFunctor_map_unitStructureMap]
  exact Category.comp_id _

/-- **The comparison `f^*O ⟶ O'` of a composite, through an arbitrary comparison of the direct
images.** Read through the comparison
`Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso` of the pullbacks attached to any
comparison `τ` of the geometric direct images carrying the composite structure map to that of
`f`, the comparison attached to `f` is the comparison of `p` pulled back along `r`, followed by
the comparison of `r`. -/
theorem pullbackModulesCompIso_inv_app_comp_pullbackUnitStructureMap
    (r : RingedToposHom X Y) (p : RingedToposHom Y Z) (f : RingedToposHom X Z)
    (τ : r.toModulesHom.toToposHom.pushforward ⋙ p.toModulesHom.toToposHom.pushforward ≅
      f.toModulesHom.toToposHom.pushforward)
    (hτ : Stacks.Sheaves.RingedToposModules.fSharpSetComp r.toModulesHom p.toModulesHom ≫
        τ.hom.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) =
      Stacks.Sheaves.RingedToposModules.fSharpSet f.toModulesHom) :
    (Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso r.toModulesHom p.toModulesHom
        f.toModulesHom τ hτ).inv.app
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ≫
        pullbackUnitStructureMap f =
      (r.toModulesHom.pullbackModules).map (pullbackUnitStructureMap p) ≫
        pullbackUnitStructureMap r := by
  apply (((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules p.toModulesHom).comp
    (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
      r.toModulesHom)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_eq_of_eq_leftAdjointUniq_inv_app_comp
      ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
          f.toModulesHom).ofNatIsoRight
        (Stacks.Sheaves.RingedToposModules.pushforwardModulesCompIso r.toModulesHom p.toModulesHom
          f.toModulesHom τ hτ).symm)
      ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules p.toModulesHom).comp
        (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules r.toModulesHom))
      (Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso r.toModulesHom p.toModulesHom
        f.toModulesHom τ hτ) rfl,
    Adjunction.homEquiv_ofNatIsoRight_apply, modulesHomEquiv_pullbackUnitStructureMap,
    Adjunction.comp_homEquiv]
  dsimp only [Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_left, modulesHomEquiv_pullbackUnitStructureMap,
    Adjunction.homEquiv_naturality_right, modulesHomEquiv_pullbackUnitStructureMap]
  refine Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor ?_
  have hl : (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
      ((Stacks.Sheaves.RingedToposModules.pushforwardModulesCompIso r.toModulesHom p.toModulesHom
        f.toModulesHom τ hτ).symm.hom.app
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) =
      τ.inv.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) := rfl
  have h1 := ((Functor.map_comp _ _ _).trans (congrArg₂ (· ≫ ·)
    (moduleSheafFunctor_map_unitStructureMap_comp_toModulesPushforwardIsoApp_inv f) hl))
  have h2 := ((Functor.map_comp _ _ _).trans (congrArg₂ (· ≫ ·)
    (moduleSheafFunctor_map_unitStructureMap_comp_toModulesPushforwardIsoApp_inv p)
    ((Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_pushforwardModules_map
      p.toModulesHom _).trans (congrArg p.toModulesHom.toToposHom.pushforward.map
        (moduleSheafFunctor_map_unitStructureMap_comp_toModulesPushforwardIsoApp_inv r)))))
  refine h1.trans (Eq.trans ?_ h2.symm)
  exact comp_inv_app_eq_of_comp_hom_app_eq τ _ _ hτ

/-- **The comparison `f^*O ⟶ O'` of a composite, through arbitrary four-field readings.** The
form of `pullbackModulesCompIso_inv_app_comp_pullbackUnitStructureMap` in which the three
four-field morphisms of ringed topoi are any morphisms equal to the readings
`AlgebraicGeometry.RingedToposHom.toModulesHom`, crossed by `eqToHom`. -/
theorem eqToHom_comp_pullbackModulesCompIso_inv_app_comp_pullbackUnitStructureMap
    (r : RingedToposHom X Y) (p : RingedToposHom Y Z) (f : RingedToposHom X Z)
    {φ : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y}
    {ψ : Stacks.Sheaves.RingedToposModules.RingedToposHom Y Z}
    {χ : Stacks.Sheaves.RingedToposModules.RingedToposHom X Z}
    (hφ : r.toModulesHom = φ) (hψ : p.toModulesHom = ψ) (hχ : f.toModulesHom = χ)
    (τ : φ.toToposHom.pushforward ⋙ ψ.toToposHom.pushforward ≅ χ.toToposHom.pushforward)
    (hτ : Stacks.Sheaves.RingedToposModules.fSharpSetComp φ ψ ≫
        τ.hom.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) =
      Stacks.Sheaves.RingedToposModules.fSharpSet χ) :
    eqToHom (congrArg (fun φ' => (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        φ').obj ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules ψ).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)))) hφ) ≫
      (Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso φ ψ χ τ hτ).inv.app
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ≫
        eqToHom (congrArg (fun χ' =>
            (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
          χ').obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))) hχ.symm) ≫
          pullbackUnitStructureMap f =
      (r.toModulesHom.pullbackModules).map
          (eqToHom (congrArg (fun ψ' =>
              (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
            ψ').obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))) hψ.symm) ≫
            pullbackUnitStructureMap p) ≫
        pullbackUnitStructureMap r := by
  subst hφ hψ hχ
  simp only [eqToHom_refl, Category.id_comp]
  exact pullbackModulesCompIso_inv_app_comp_pullbackUnitStructureMap r p f τ hτ

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w₁})]
  [HasWeakSheafify Y.J AddCommGrpCat.{w₂}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w₂}] in
/-- `eqToHom` between pullbacks along two equal four-field morphisms of ringed topoi is natural. -/
theorem eqToHom_comp_pullbackModules_map
    {φ₁ φ₂ : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y} (h : φ₁ = φ₂)
    {M N : SheafOfModules.{w₂} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)} (a : M ⟶ N) :
    eqToHom (congrArg (fun φ => (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        φ).obj M) h) ≫ φ₂.pullbackModules.map a =
      φ₁.pullbackModules.map a ≫
        eqToHom (congrArg (fun φ =>
            (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
          φ).obj N) h) := by
  subst h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

omit [HasWeakSheafify Y.J AddCommGrpCat.{w₂}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w₂}] in
/-- **The transpose of `f^*O ⟶ O'` along the extension of scalars alone**, for a four-field
morphism of ringed topoi equal to `AlgebraicGeometry.RingedToposHom.toModulesHom`. -/
theorem fSharpAdjunction_homEquiv_eqToHom_comp_pullbackUnitStructureMap
    (p : RingedToposHom X Y) {ψ : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y}
    (hψ : p.toModulesHom = ψ)
    {k : ψ.pullbackModules.obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (hk : eqToHom (congrArg (fun ψ' =>
        (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
          ψ').obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) hψ.symm) ≫
          pullbackUnitStructureMap p = k) :
    (Stacks.Sheaves.RingedToposModules.fSharpAdjunction ψ).homEquiv
        ((Stacks.Sheaves.RingedToposModules.inverseImageModules ψ.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) k =
      (Stacks.Sheaves.ToposPullback.pullbackModuleUnitIso X.J ψ.toToposHom.inverseImage
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).inv ≫
        Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit ψ.fSharpInverseImage := by
  subst hψ hk
  exact (congrArg ((Stacks.Sheaves.RingedToposModules.fSharpAdjunction p.toModulesHom).homEquiv _ _)
    (Category.id_comp (pullbackUnitStructureMap p))).trans
      (fSharpAdjunction_homEquiv_pullbackUnitStructureMap p)

end UnitComparisonFourField

end AlgebraicGeometry.RingedToposHom

namespace Deformation.ToposThickening

variable {X' : RingedTopos.{v', u', w}}
  {S : RingedTopos.{vS, uS, w}} {S' : RingedTopos.{vS', uS', w}}
  [X'.J.HasSheafCompose (forget RingCat.{w})]
  [S.J.HasSheafCompose (forget RingCat.{w})] [S'.J.HasSheafCompose (forget RingCat.{w})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [S.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [S'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (t : RingedToposHom S S') (f' : RingedToposHom X' S')
  [X'.J.HasSheafCompose (forget CommRingCat.{w})]
  [HasWeakSheafify X'.J AddCommGrpCat.{w}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X'.J AddCommGrpCat.{w}]

omit [X'.J.HasSheafCompose (forget RingCat.{w})] in
/-- A sectionwise isomorphism followed by an isomorphism `e` is compatible with the morphisms
into the common target, read through `e`. -/
theorem sectionwiseIsoOfRangeEq_trans_hom_comp {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    {M₁ M₂ M₃ N : SheafOfModules.{w} R} (ι₁ : M₁ ⟶ N) (ι₂ : M₂ ⟶ N)
    (h₁ : ∀ U, Function.Injective (ι₁.val.app U)) (h₂ : ∀ U, Function.Injective (ι₂.val.app U))
    (h : ∀ (U : Cᵒᵖ) (x : N.val.obj U), (∃ b, ι₁.val.app U b = x) ↔ (∃ b, ι₂.val.app U b = x))
    (e : M₂ ≅ M₃) (m : M₃ ⟶ N) (hm : e.hom ≫ m = ι₂) :
    (sectionwiseIsoOfRangeEq ι₁ ι₂ h₁ h₂ h ≪≫ e).hom ≫ m = ι₁ := by
  rw [Iso.trans_hom, Category.assoc, hm, sectionwiseIsoOfRangeEq_hom_comp]

/-- **`𝒥̃ ≅ f'⁻¹𝒥` is compatible with the inclusions into `f'⁻¹O_{ℬ'}`.** -/
theorem relBaseIdealIso_hom_comp_map_incl (ht : FirstOrderThickening t) :
    (relBaseIdealIso t f' ht).hom ≫
        (inverseImageModules f'.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).map
          ht.idealOfThickening.incl ≫
        (Stacks.Sheaves.ToposPullback.pullbackModuleUnitIso X'.J f'.toToposHom.inverseImage
          (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).inv =
      (relBaseThickeningFirstOrderThickening (f' := f') ht).idealOfThickening.incl :=
  sectionwiseIsoOfRangeEq_trans_hom_comp _ _ _ _ _ _ _ (Category.assoc _ _ _)

/-- Restriction of scalars of an `eqToHom` between restrictions of scalars along two equal
morphisms of sheaves of rings is the identity on underlying sheaves of sets. -/
private theorem moduleSheafFunctor_map_restrictScalars_map_eqToHom {C : Type*} [Category C]
    {J : GrothendieckTopology C} [J.HasSheafCompose (forget RingCat.{w})]
    [J.HasSheafCompose (forget AddCommGrpCat.{w})] {R R' R'' : Sheaf J RingCat.{w}}
    (γ : R'' ⟶ R) {α β : R ⟶ R'} (h : α = β) (N : SheafOfModules.{w} R') :
    (Sheaf.moduleSheafFunctor R'').map ((SheafOfModules.restrictScalars γ).map
        (eqToHom (congrArg (fun m => (SheafOfModules.restrictScalars m).obj N) h))) = 𝟙 _ := by
  subst h
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id]

/-- For an automorphism `e` of a sheaf of rings with `e.inv = 𝟙`, the transpose along the
equivalence `restrictScalars e.inv ⊣ restrictScalars e.hom` of `eqToHom` followed by `k` is `k`
on underlying sheaves of sets. -/
private theorem moduleSheafFunctor_map_restrictScalarsEquivalence_homEquiv_eqToHom_comp
    {C : Type*} [Category C] {J : GrothendieckTopology C} [J.HasSheafCompose (forget RingCat.{w})]
    [J.HasSheafCompose (forget AddCommGrpCat.{w})] {R : Sheaf J RingCat.{w}} (e : R ≅ R)
    (h : e.inv = 𝟙 R) (N : SheafOfModules.{w} R) {M : SheafOfModules.{w} R} (k : N ⟶ M) :
    (Sheaf.moduleSheafFunctor R).map
        ((Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso e).toAdjunction.homEquiv N M
          (eqToHom (congrArg (fun m => (SheafOfModules.restrictScalars m).obj N) h) ≫ k)) =
      (Sheaf.moduleSheafFunctor R).map k := by
  have hk : (Sheaf.moduleSheafFunctor R).map ((SheafOfModules.restrictScalars e.hom).map
      (eqToHom (congrArg (fun m => (SheafOfModules.restrictScalars m).obj N) h) ≫ k)) =
        (Sheaf.moduleSheafFunctor R).map ((SheafOfModules.restrictScalars e.hom).map k) :=
    (congrArg (Sheaf.moduleSheafFunctor R).map (Functor.map_comp _ _ _)).trans
      ((Functor.map_comp _ _ _).trans ((eq_whisker
        (moduleSheafFunctor_map_restrictScalars_map_eqToHom e.hom h N) _).trans
          (Category.id_comp _)))
  rw [Adjunction.homEquiv_unit, Functor.map_comp]
  refine (whisker_eq _ hk).trans ?_
  exact Sheaf.hom_ext_sections fun _ _ => rfl

omit [X'.J.HasSheafCompose (forget RingCat.{w})] in
/-- `eqToHom` between restrictions of scalars along two equal morphisms of sheaves of rings is
natural. -/
private theorem eqToHom_comp_restrictScalars_map {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R R' : Sheaf J RingCat.{w}} {α β : R ⟶ R'} (h : α = β)
    {M N : SheafOfModules.{w} R'} (b : M ⟶ N) :
    eqToHom (congrArg (fun m => (SheafOfModules.restrictScalars m).obj M) h) ≫
        (SheafOfModules.restrictScalars β).map b =
      (SheafOfModules.restrictScalars α).map b ≫
        eqToHom (congrArg (fun m => (SheafOfModules.restrictScalars m).obj N) h) := by
  subst h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

omit [HasSheafify X'.J AddCommGrpCat.{w}] in
/-- **The identification of the pullback along the projection with the inverse image is
natural.** -/
theorem relBaseProjectionPullbackIso_inv_naturality
    {M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)} (a : M ⟶ N) :
    (relBaseProjectionPullbackIso f' M).inv ≫
        (relBaseProjection f').toRingedToposModulesHom.pullbackModules.map a =
      (inverseImageModules f'.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).map a ≫
        (relBaseProjectionPullbackIso f' N).inv := by
  have h1 := ((relBaseProjection
    f').toRingedToposModulesHom.extendScalarsFSharpIsoRestrictScalarsOfIsIso).inv.naturality
    ((inverseImageModules f'.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).map a)
  have h2 := eqToHom_comp_restrictScalars_map (relBaseProjection_asIso_inv f').symm
    ((inverseImageModules f'.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).map a)
  exact (whisker_eq _ h1.symm).trans ((Category.assoc _ _ _).symm.trans
    ((eq_whisker h2 _).trans (Category.assoc _ _ _)))

omit [HasSheafify X'.J AddCommGrpCat.{w}] in
/-- The identification of the pullback along the projection with the inverse image is the
comparison of the two left adjoints of restriction of scalars along the structure map of the
projection, followed by `restrictScalars (𝟙) = id`. -/
theorem relBaseProjectionPullbackIso_hom_eq
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)) :
    (relBaseProjectionPullbackIso f' M).hom =
      ((Stacks.Sheaves.RingedToposModules.fSharpAdjunction
          (relBaseProjection f').toRingedToposModulesHom).leftAdjointUniq
        (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
          (asIso (relBaseProjection
            f').toRingedToposModulesHom.fSharpInverseImage)).toAdjunction).hom.app
          ((inverseImageModules f'.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).obj M) ≫
        eqToHom (congrArg (fun m => (SheafOfModules.restrictScalars m).obj
          ((inverseImageModules f'.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).obj M))
          (relBaseProjection_asIso_inv f')) :=
  rfl

omit [HasSheafify X'.J AddCommGrpCat.{w}] in
/-- `relBaseProjectionPullbackIso_hom_eq`, followed by a morphism. -/
theorem relBaseProjectionPullbackIso_hom_comp
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf S'.O))
    {Q : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (relBaseTop f').O)}
    (k : (inverseImageModules f'.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).obj M ⟶
      Q) :
    (relBaseProjectionPullbackIso f' M).hom ≫ k =
      ((Stacks.Sheaves.RingedToposModules.fSharpAdjunction
          (relBaseProjection f').toRingedToposModulesHom).leftAdjointUniq
        (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
          (asIso (relBaseProjection
            f').toRingedToposModulesHom.fSharpInverseImage)).toAdjunction).hom.app
          ((inverseImageModules f'.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).obj M) ≫
        eqToHom (congrArg (fun m => (SheafOfModules.restrictScalars m).obj
          ((inverseImageModules f'.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).obj M))
          (relBaseProjection_asIso_inv f')) ≫ k :=
  (eq_whisker (relBaseProjectionPullbackIso_hom_eq f' M) k).trans (Category.assoc _ _ _)

omit [HasSheafify X'.J AddCommGrpCat.{w}] in
/-- **The identification of the pullback of `O_{ℬ'}` along the projection with `f'⁻¹O_{ℬ'}`,
transposed along the extension of scalars**: it is the identity `f'⁻¹1 = 1` followed by the
inverse-image form of the (identity) structure map of the projection. -/
theorem relBaseProjection_fSharpAdjunction_homEquiv_pullbackIso_unit
    {k : (relBaseProjection f').toRingedToposModulesHom.pullbackModules.obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)) ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (relBaseTop f').O)}
    (hk : (relBaseProjectionPullbackIso f'
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S'.O))).hom ≫
          (Stacks.Sheaves.ToposPullback.pullbackModuleUnitIso (relBaseTop f').J
            (relBaseProjection f').toRingedToposModulesHom.toToposHom.inverseImage
            (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).inv = k) :
    (Stacks.Sheaves.RingedToposModules.fSharpAdjunction
        (relBaseProjection f').toRingedToposModulesHom).homEquiv
        ((inverseImageModules (relBaseProjection f').toRingedToposModulesHom.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).obj
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)))
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (relBaseTop f').O)) k =
      (Stacks.Sheaves.ToposPullback.pullbackModuleUnitIso (relBaseTop f').J
          (relBaseProjection f').toRingedToposModulesHom.toToposHom.inverseImage
          (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).inv ≫
        Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit
          (relBaseProjection f').toRingedToposModulesHom.fSharpInverseImage := by
  subst hk
  refine (congrArg ((Stacks.Sheaves.RingedToposModules.fSharpAdjunction
      (relBaseProjection f').toRingedToposModulesHom).homEquiv _ _)
    (relBaseProjectionPullbackIso_hom_comp f' _ _)).trans
    ((CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app_comp _ _ _).trans ?_)
  have hR : (Sheaf.moduleSheafFunctor (Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf
        (relBaseProjection f').toRingedToposModulesHom.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf S'.O))).map
      ((Stacks.Sheaves.ToposPullback.pullbackModuleUnitIso (relBaseTop f').J
          (relBaseProjection f').toRingedToposModulesHom.toToposHom.inverseImage
          (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).inv ≫
        Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit
          (relBaseProjection f').toRingedToposModulesHom.fSharpInverseImage) =
      (Sheaf.moduleSheafFunctor (Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf
        (relBaseProjection f').toRingedToposModulesHom.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf S'.O))).map
      (Stacks.Sheaves.ToposPullback.pullbackModuleUnitIso (relBaseTop f').J
          (relBaseProjection f').toRingedToposModulesHom.toToposHom.inverseImage
          (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).inv :=
    (Functor.map_comp _ _ _).trans ((whisker_eq _
      ((Stacks.SheafOfModules.ChangeOfRings.moduleSheafFunctor_map_unitToRestrictScalarsUnit
          _).trans
        ((congrArg (sheafCompose (relBaseTop f').J (forget RingCat.{w})).map
          (relBaseProjection_ringFsharpInverseImage f')).trans
            (CategoryTheory.Functor.map_id _ _)))).trans
      (Category.comp_id _))
  refine Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor (Eq.trans ?_ hR.symm)
  exact moduleSheafFunctor_map_restrictScalarsEquivalence_homEquiv_eqToHom_comp
    (@asIso _ _ _ _ (relBaseProjection f').toRingedToposModulesHom.fSharpInverseImage
      (isIso_relBaseProjection_fSharpInverseImage f'))
    (relBaseProjection_asIso_inv f') _ _

omit [HasSheafify X'.J AddCommGrpCat.{w}] in
/-- **The identification `(projection)^*O_{ℬ'} ≅ f'⁻¹O_{ℬ'}` against the comparison
`(projection)^*O_{ℬ'} ⟶ f'⁻¹O_{ℬ'}`**: the identification followed by `f'⁻¹1 = 1` is the
comparison attached to the projection. -/
theorem relBaseProjectionPullbackIso_hom_comp_pullbackModuleUnitIso_inv :
    (relBaseProjectionPullbackIso f'
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S'.O))).hom ≫
      (Stacks.Sheaves.ToposPullback.pullbackModuleUnitIso (relBaseTop f').J
        (relBaseProjection f').toRingedToposModulesHom.toToposHom.inverseImage
        (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).inv =
    eqToHom (congrArg (fun ψ => (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
          ψ).obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)))
        (relBaseProjection f').toModulesHom_eq_toRingedToposModulesHom.symm) ≫
      RingedToposHom.pullbackUnitStructureMap (relBaseProjection f') :=
  ((Stacks.Sheaves.RingedToposModules.fSharpAdjunction
      (relBaseProjection f').toRingedToposModulesHom).homEquiv _ _).injective
    ((relBaseProjection_fSharpAdjunction_homEquiv_pullbackIso_unit f' rfl).trans
      (RingedToposHom.fSharpAdjunction_homEquiv_eqToHom_comp_pullbackUnitStructureMap
        (relBaseProjection f') (relBaseProjection f').toModulesHom_eq_toRingedToposModulesHom
        rfl).symm)

omit [HasSheafify X'.J AddCommGrpCat.{w}] in
/-- **Read through `(projection)^*O_{ℬ'} ≅ f'⁻¹O_{ℬ'}`, the comparison attached to the projection
is the identity `f'⁻¹1 = 1`.** -/
theorem relBaseProjectionPullbackIso_inv_comp_pullbackUnitStructureMap :
    (relBaseProjectionPullbackIso f'
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S'.O))).inv ≫
      eqToHom (congrArg (fun ψ => (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
          ψ).obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)))
        (relBaseProjection f').toModulesHom_eq_toRingedToposModulesHom.symm) ≫
        RingedToposHom.pullbackUnitStructureMap (relBaseProjection f') =
      (Stacks.Sheaves.ToposPullback.pullbackModuleUnitIso (relBaseTop f').J
        (relBaseProjection f').toRingedToposModulesHom.toToposHom.inverseImage
        (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).inv :=
  (whisker_eq _ (relBaseProjectionPullbackIso_hom_comp_pullbackModuleUnitIso_inv f').symm).trans
    (Iso.inv_hom_id_assoc _ _)

/-- **`𝒥̃ ⟶ f'⁻¹𝒥 ≅ (projection)^*𝒥`, followed by the comparison of the projection, is the
inclusion of `𝒥̃`.** -/
theorem relBaseIdealIso_hom_comp_pullbackIso_inv_comp_pullbackUnitStructureMap
    (ht : FirstOrderThickening t) :
    (relBaseIdealIso t f' ht).hom ≫ (relBaseProjectionPullbackIso f' ht.idealOfThickening.I).inv ≫
        (relBaseProjection f').toRingedToposModulesHom.pullbackModules.map
          ht.idealOfThickening.incl ≫
        eqToHom (congrArg (fun ψ =>
            (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
            ψ).obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)))
          (relBaseProjection f').toModulesHom_eq_toRingedToposModulesHom.symm) ≫
          RingedToposHom.pullbackUnitStructureMap (relBaseProjection f') =
      (relBaseThickeningFirstOrderThickening (f' := f') ht).idealOfThickening.incl :=
  (whisker_eq _ ((Category.assoc _ _ _).symm.trans ((eq_whisker
      (relBaseProjectionPullbackIso_inv_naturality f' ht.idealOfThickening.incl) _).trans
        (Category.assoc _ _ _)))).trans
    ((whisker_eq _ (whisker_eq _
      (relBaseProjectionPullbackIso_inv_comp_pullbackUnitStructureMap f'))).trans
      (relBaseIdealIso_hom_comp_map_incl t f' ht))

/-- A diagram chase through the naturality square of a natural transformation `α : P ⋙ R ⟶ F` at a
morphism `i : M ⟶ O`. -/
private theorem comp_chase {C D E : Type*} [Category C] [Category D] [Category E]
    (P : E ⥤ D) (R : D ⥤ C) (F : E ⥤ C) (α : P ⋙ R ⟶ F) {M O : E} (i : M ⟶ O)
    {Y₀ Y₁ Y₄ Y₅ Q Q₁ W Z : C} {e₁ : Y₀ ⟶ Y₁} {r : Y₁ ⟶ F.obj M} {a : Y₁ ⟶ R.obj (P.obj M)}
    {e₂ : F.obj M ⟶ Y₄} {i' : Y₄ ⟶ Y₅} {u : Y₅ ⟶ Z} {a' : Y₀ ⟶ Q} {e₃ : Q ⟶ R.obj (P.obj M)}
    {e₄ : F.obj O ⟶ Y₅} {j' : Q ⟶ Q₁} {e₅ : Q₁ ⟶ R.obj (P.obj O)} {b : Q₁ ⟶ W} {u' : W ⟶ Z}
    (h₀ : r = a ≫ α.app M) (h₁ : e₁ ≫ a = a' ≫ e₃) (h₂ : e₂ ≫ i' = F.map i ≫ e₄)
    (h₄ : e₃ ≫ R.map (P.map i) = j' ≫ e₅) (h₅ : e₅ ≫ α.app O ≫ e₄ ≫ u = b ≫ u') :
    e₁ ≫ r ≫ e₂ ≫ i' ≫ u = a' ≫ j' ≫ b ≫ u' := by
  have h₃ : R.map (P.map i) ≫ α.app O = α.app M ≫ F.map i := α.naturality i
  rw [h₀, Category.assoc, reassoc_of% h₁, reassoc_of% h₂, ← reassoc_of% h₃, reassoc_of% h₄, h₅]

/-- A functor applied to a composite of five morphisms, regrouped. -/
private theorem map_comp_comp_map_comp_comp {C D : Type*} [Category C] [Category D] (G : D ⥤ C)
    {A B B' E F H : D} {Z : C} (a : A ⟶ B) (b : B ⟶ B') (c : B' ⟶ E) (d : E ⟶ F) (e : F ⟶ H)
    (z : G.obj H ⟶ Z) :
    G.map (a ≫ b) ≫ G.map c ≫ G.map (d ≫ e) ≫ z = G.map (a ≫ b ≫ c ≫ d ≫ e) ≫ z := by
  simp only [Functor.map_comp, Category.assoc]

/-- **`f̃'^*` applied to `𝒥̃ ⟶ (projection)^*𝒥 ⟶ (projection)^*O_{ℬ'} ⟶ f'⁻¹O_{ℬ'}`, followed by
the comparison of `f̃'`, is `f̃'^*` of the inclusion of `𝒥̃` followed by that comparison.** -/
theorem relBasePullbackIdealIso_chase_tail (ht : FirstOrderThickening t) :
    ((relBaseRight f').toModulesHom.pullbackModules).map
        ((relBaseIdealIso t f' ht).hom ≫
          (relBaseProjectionPullbackIso f' ht.idealOfThickening.I).inv) ≫
      ((relBaseRight f').toModulesHom.pullbackModules).map
        ((relBaseProjection f').toRingedToposModulesHom.pullbackModules.map
          ht.idealOfThickening.incl) ≫
      ((relBaseRight f').toModulesHom.pullbackModules).map
          (eqToHom (congrArg (fun ψ =>
              (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
            ψ).obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)))
            (relBaseProjection f').toModulesHom_eq_toRingedToposModulesHom.symm) ≫
            RingedToposHom.pullbackUnitStructureMap (relBaseProjection f')) ≫
        RingedToposHom.pullbackUnitStructureMap (relBaseRight f') =
      ((relBaseRight f').toModulesHom.pullbackModules).map
          (relBaseThickeningFirstOrderThickening (f' := f') ht).idealOfThickening.incl ≫
        RingedToposHom.pullbackUnitStructureMap (relBaseRight f') :=
  (map_comp_comp_map_comp_comp _ _ _ _ _ _ _).trans
    (congrArg (· ≫ RingedToposHom.pullbackUnitStructureMap (relBaseRight f'))
      (congrArg ((relBaseRight f').toModulesHom.pullbackModules).map
        (relBaseIdealIso_hom_comp_pullbackIso_inv_comp_pullbackUnitStructureMap t f' ht)))

/-- **`f̃'^*𝒥̃ ≅ f'^*𝒥` is compatible with the canonical maps into `O'`.** Read through the
identification `relBasePullbackIdealIso` of `f̃'^*𝒥̃` with `f'^*𝒥` (and the identifications of
the two four-field readings of `f̃'` and of `f'`), the map `f'^*𝒥 ⟶ f'^*O_{ℬ'} ⟶ O'` is the map
`f̃'^*𝒥̃ ⟶ f̃'^*(f'⁻¹O_{ℬ'}) ⟶ O'`. -/
theorem relBasePullbackIdealIso_hom_comp_pullbackUnitStructureMap (ht : FirstOrderThickening t) :
    eqToHom (congrArg (fun φ => (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        φ).obj (relBaseThickeningFirstOrderThickening (f' := f') ht).idealOfThickening.I)
        (relBaseRight f').toModulesHom_eq_toRingedToposModulesHom) ≫
      (relBasePullbackIdealIso t f' ht).hom ≫
        eqToHom (congrArg (fun φ =>
            (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
          φ).obj ht.idealOfThickening.I) f'.toModulesHom_eq_toRingedToposModulesHom.symm) ≫
          (f'.toModulesHom.pullbackModules).map ht.idealOfThickening.incl ≫
            RingedToposHom.pullbackUnitStructureMap f' =
      ((relBaseRight f').toModulesHom.pullbackModules).map
          (relBaseThickeningFirstOrderThickening (f' := f') ht).idealOfThickening.incl ≫
        RingedToposHom.pullbackUnitStructureMap (relBaseRight f') := by
  have h0 : (relBasePullbackIdealIso t f' ht).hom =
      (relBaseRight f').toRingedToposModulesHom.pullbackModules.map
          ((relBaseIdealIso t f' ht).hom ≫
            (relBaseProjectionPullbackIso f' ht.idealOfThickening.I).inv) ≫
        (relBasePullbackCompIso f').inv.app ht.idealOfThickening.I := rfl
  have h1 := RingedToposHom.eqToHom_comp_pullbackModules_map
    (relBaseRight f').toModulesHom_eq_toRingedToposModulesHom
    ((relBaseIdealIso t f' ht).hom ≫ (relBaseProjectionPullbackIso f' ht.idealOfThickening.I).inv)
  have h2 := RingedToposHom.eqToHom_comp_pullbackModules_map
    f'.toModulesHom_eq_toRingedToposModulesHom.symm ht.idealOfThickening.incl
  have h4 := RingedToposHom.eqToHom_comp_pullbackModules_map
    (relBaseRight f').toModulesHom_eq_toRingedToposModulesHom
    ((relBaseProjection f').toRingedToposModulesHom.pullbackModules.map ht.idealOfThickening.incl)
  have h5 : _ = _ :=
    RingedToposHom.eqToHom_comp_pullbackModulesCompIso_inv_app_comp_pullbackUnitStructureMap
      (relBaseRight f') (relBaseProjection f') f'
      (relBaseRight f').toModulesHom_eq_toRingedToposModulesHom
      (relBaseProjection f').toModulesHom_eq_toRingedToposModulesHom
      f'.toModulesHom_eq_toRingedToposModulesHom
      (Functor.leftUnitor f'.toToposHom.pushforward) (relBase_fSharpSetComp f')
  have h5' : eqToHom (congrArg (fun φ =>
      (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        φ).obj ((relBaseProjection f').toRingedToposModulesHom.pullbackModules.obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S'.O))))
        (relBaseRight f').toModulesHom_eq_toRingedToposModulesHom) ≫
      (relBasePullbackCompIso f').inv.app
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)) ≫
        eqToHom (congrArg (fun χ =>
            (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
          χ).obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)))
          f'.toModulesHom_eq_toRingedToposModulesHom.symm) ≫
          RingedToposHom.pullbackUnitStructureMap f' =
      ((relBaseRight f').toModulesHom.pullbackModules).map
          (eqToHom (congrArg (fun ψ =>
              (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
            ψ).obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)))
            (relBaseProjection f').toModulesHom_eq_toRingedToposModulesHom.symm) ≫
            RingedToposHom.pullbackUnitStructureMap (relBaseProjection f')) ≫
        RingedToposHom.pullbackUnitStructureMap (relBaseRight f') := h5
  exact (comp_chase _ _ _ (relBasePullbackCompIso f').inv ht.idealOfThickening.incl
    h0 h1 h2 h4 h5').trans (relBasePullbackIdealIso_chase_tail t f' ht)

end Deformation.ToposThickening

end
