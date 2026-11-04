module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardTestSections
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModuleAffineUnit
public import StacksFrontier.AlgebraicGeometry.Quot.PicardSplitSectionIso
public import StacksFrontier.AlgebraicGeometry.Quot.PicardPushforwardUnitIso
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackSection
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatDeformationMapGlobalSection
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineAssociatedModuleStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafPullbackUnitIsoComp
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackGlobalSection

/-!
# The functions on the base changes, and split sections of invertible modules

Let `f : X ⟶ B` be a morphism of algebraic spaces and `U` a test scheme over `B` with
`𝒪_U ≅ f_{U,*}𝒪_{X_U}`. Then the endomorphisms of `𝒪_{X_U}` are exactly the multiplications by
the functions of `U`: `a ↦ a · 𝟙` is a bijection `Γ(U, 𝒪_U) ⟶ End(𝒪_{X_U})`. Multiplication by
`a` is compatible with pulling back along a morphism of algebraic spaces.

In any monoidal category, a morphism `σ : 𝟙 ⟶ L` with a retraction is an isomorphism as soon as
tensoring by `L` is full; for invertible modules this says that a split section of an invertible
module trivializes it. Together these are the inputs of the proof of Stacks 0D23 which read
"a basis of sections `σ, τ` with `στ = 1` gives `𝒪 ≅ L`".

## Main results

* `AlgebraicGeometry.Space.modulePullbackUnitIso_inv_comp_map_unitModuleMul_comp`: multiplication
  by the pullback of a function commutes with pulling back.
* `AlgebraicGeometry.Space.PicardSituation.bijective_unitModuleMul_testFunctions`: `Γ(U, 𝒪_U) ≅
  End(𝒪_{X_U})` when `𝒪_U ≅ f_{U,*}𝒪_{X_U}`.
* `CategoryTheory.MonoidalCategory.isIso_of_comp_eq_id_of_full_tensorLeft`: a split morphism
  `𝟙 ⟶ L` is an isomorphism when tensoring by `L` is full.
* `AlgebraicGeometry.Space.isIso_of_comp_eq_id_of_isInvertibleModule`: a split section of an
  invertible module is an isomorphism.

## References

* [Stacks Project, Tag 0D23](https://stacks.math.columbia.edu/tag/0D23)
-/

@[expose] public noncomputable section

/- The global instance `Abelian (SheafOfModules.{max u v r w} O)` leaves a stuck universe
constraint against the `𝒪_X`-modules at the universe of the schemes; switched off locally as in
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePullbackGlobalSection.lean`. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory Stacks.Cohomology.SiteModules

universe u


namespace CategoryTheory

/-- **Conjugating a pulled back endomorphism through a composite of inverse images.** Given
functors `F_f : C_T ⥤ C_V`, `F_q : C_V ⥤ C_W` and `F_{qf} : C_T ⥤ C_W` with `F_f ⋙ F_q ≅ F_{qf}`,
and identifications `u_f : F_f O_T ≅ O_V`, `u_q : F_q O_V ≅ O_W`, `u_{qf} : F_{qf} O_T ≅ O_W`
compatible with it, pulling back the conjugate `u_f⁻¹ ≫ F_f m ≫ u_f` of an endomorphism `m` of
`O_T` along `F_q` is the conjugate `u_{qf}⁻¹ ≫ F_{qf} m ≫ u_{qf}`, through `u_q`. -/
theorem conj_map_conj_of_compIso {C_T C_V C_W : Type*} [Category C_T] [Category C_V]
    [Category C_W] (F_f : C_T ⥤ C_V) (F_q : C_V ⥤ C_W) (F_qf : C_T ⥤ C_W)
    (Θ : F_f ⋙ F_q ≅ F_qf) (O_T : C_T) {O_V : C_V} {O_W : C_W} (uf : F_f.obj O_T ≅ O_V)
    (uq : F_q.obj O_V ≅ O_W) (uqf : F_qf.obj O_T ≅ O_W)
    (hC : Θ.hom.app O_T ≫ uqf.hom = F_q.map uf.hom ≫ uq.hom) (m : O_T ⟶ O_T) :
    uq.inv ≫ F_q.map (uf.inv ≫ F_f.map m ≫ uf.hom) =
      (uqf.inv ≫ F_qf.map m ≫ uqf.hom) ≫ uq.inv := by
  have h1 : F_q.map uf.hom = Θ.hom.app O_T ≫ uqf.hom ≫ uq.inv := by
    rw [← Category.assoc, hC, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h2 : F_q.map uf.inv = uq.hom ≫ uqf.inv ≫ Θ.inv.app O_T := by
    rw [← cancel_mono (F_q.map uf.hom), ← F_q.map_comp, Iso.inv_hom_id, F_q.map_id, h1]
    simp
  have hn := Θ.hom.naturality m
  simp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc, h1, h2, Iso.inv_hom_id_assoc]
  rw [reassoc_of% hn, Iso.inv_hom_id_app_assoc]

end CategoryTheory

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The value of `globalFunctionsOfMap (𝟙 _) r` on the identity chart is `r`. -/
theorem globalFunctionsOfMap_id_selfChart (T : BigFppfOver B S hS) (r : baseRing B S hS T) :
    (show chartRing B S hS (schemeSpace T).1 (schemeSpace T).2 (selfChart B S hS T) from
      (globalFunctionsOfMap (𝟙 (schemeSpace T)) r).1 (op (selfChart B S hS T))) = r := by
  have h := chartToBase_id_selfChart B S hS (T := T)
  have h2 : ∀ x, (CommRingCat.Hom.hom (Scheme.Γ.map
      ((BigFppfOver.toScheme B S hS).map (𝟙 T)).op)) x = x := fun x => by
    simp only [op_id, CategoryTheory.Functor.map_id, CommRingCat.hom_id, RingHom.id_apply]
  dsimp only [globalFunctionsOfMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [h]
  exact h2 r

/-- **Multiplication by a global function is a bijection onto the endomorphisms of `𝒪_X`.** -/
theorem bijective_unitModuleMul (X : AlgebraicSpaces B S hS) :
    Function.Bijective (unitModuleMul B S hS X) := by
  have hs : Function.Bijective
      (unitSection (R := Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O)) :=
    ⟨fun a b hab => Subtype.ext (congrArg Subtype.val hab), fun t => ⟨⟨t.1, t.2⟩, rfl⟩⟩
  exact (Equiv.bijective _).comp hs

/-- Multiplication by the pullback of a function along `f : X ⟶ T` is the conjugate of the pullback
of multiplication by that function on `T`. -/
theorem unitModuleMul_globalFunctionsOfMap_eq {X : AlgebraicSpaces B S hS}
    {T : BigFppfOver B S hS} (f : X ⟶ schemeSpace T) (r : baseRing B S hS T) :
    unitModuleMul B S hS X (globalFunctionsOfMap f r) =
      (modulePullbackUnitIso B S hS f).inv ≫ (modulePullback B S hS f).map
        (unitModuleMul B S hS (schemeSpace T) (globalFunctionsOfMap (𝟙 (schemeSpace T)) r)) ≫
          (modulePullbackUnitIso B S hS f).hom :=
  ((Iso.comp_inv_eq _).mp (modulePullbackUnitIso_inv_comp_map_unitModuleMul B S hS f r).symm).trans
    (Category.assoc _ _ _)

/-- **Multiplication by the pullback of a function commutes with pulling back**: for
`q : W ⟶ V` and `f : V ⟶ T`, pulling back multiplication by `f^♯r` along `q` is multiplication
by `(q ≫ f)^♯r`, through `q^*𝒪_V ≅ 𝒪_W`. -/
theorem modulePullbackUnitIso_inv_comp_map_unitModuleMul_comp {W V : AlgebraicSpaces B S hS}
    {T : BigFppfOver B S hS} (q : W ⟶ V) (f : V ⟶ schemeSpace T) (r : baseRing B S hS T) :
    (modulePullbackUnitIso B S hS q).inv ≫
        (modulePullback B S hS q).map (unitModuleMul B S hS V (globalFunctionsOfMap f r)) =
      unitModuleMul B S hS W (globalFunctionsOfMap (q ≫ f) r) ≫
        (modulePullbackUnitIso B S hS q).inv := by
  have hC : (modulePullbackCompIso B S hS q f).hom.app
      (SheafOfModules.unit (structureRingSheaf B S hS (schemeSpace T))) ≫
      (modulePullbackUnitIso B S hS (q ≫ f)).hom =
      (modulePullback B S hS q).map (modulePullbackUnitIso B S hS f).hom ≫
        (modulePullbackUnitIso B S hS q).hom :=
    modulePullbackCompIso_hom_app_comp_modulePullbackUnitIso_hom B S hS q f
  have key := conj_map_conj_of_compIso (modulePullback B S hS f) (modulePullback B S hS q)
    (modulePullback B S hS (q ≫ f)) (modulePullbackCompIso B S hS q f)
    (SheafOfModules.unit (structureRingSheaf B S hS (schemeSpace T)))
    (modulePullbackUnitIso B S hS f) (modulePullbackUnitIso B S hS q)
    (modulePullbackUnitIso B S hS (q ≫ f)) hC
    (unitModuleMul B S hS (schemeSpace T) (globalFunctionsOfMap (𝟙 (schemeSpace T)) r))
  exact (congrArg (fun z => (modulePullbackUnitIso B S hS q).inv ≫
    (modulePullback B S hS q).map z) (unitModuleMul_globalFunctionsOfMap_eq f r)).trans
    (key.trans (congrArg (· ≫ (modulePullbackUnitIso B S hS q).inv)
      (unitModuleMul_globalFunctionsOfMap_eq (q ≫ f) r).symm))

/-- **The endomorphisms of `𝒪_X` are the functions of `T`** when `f : X ⟶ T` has
`𝒪_T ≅ f_*𝒪_X`: multiplication by `f^♯a` is a bijection `Γ(T, 𝒪_T) ⟶ End(𝒪_X)`. The functions
of `T` are the endomorphisms of `𝒪_T`, and `f^*` is bijective on those
(`AlgebraicGeometry.Space.bijective_modulePullback_map_of_isInvertibleModule`). -/
theorem bijective_unitModuleMul_globalFunctionsOfMap {X : AlgebraicSpaces B S hS}
    {T : BigFppfOver B S hS} (f : X ⟶ schemeSpace T) (hf : IsIso (structureSharp B S hS f)) :
    Function.Bijective (fun a : baseRing B S hS T =>
      unitModuleMul B S hS X (globalFunctionsOfMap f a)) := by
  have h1 : Function.Bijective (fun a : baseRing B S hS T =>
      unitModuleMul B S hS (schemeSpace T) (globalFunctionsOfMap (𝟙 (schemeSpace T)) a)) :=
    (bijective_unitModuleMul (schemeSpace T)).comp (bijective_globalFunctionsOfMap_id T)
  have h2 : Function.Bijective (fun φ : SheafOfModules.unit (structureRingSheaf B S hS
      (schemeSpace T)) ⟶ SheafOfModules.unit (structureRingSheaf B S hS (schemeSpace T)) =>
        (modulePullback B S hS f).map φ) :=
    bijective_modulePullback_map_of_isInvertibleModule f hf _
      (isInvertibleModule_structureModule (schemeSpace T))
  have h3 := ((modulePullbackUnitIso B S hS f).homCongr
    (modulePullbackUnitIso B S hS f)).bijective
  have key : (fun a : baseRing B S hS T => unitModuleMul B S hS X (globalFunctionsOfMap f a)) =
      ((modulePullbackUnitIso B S hS f).homCongr (modulePullbackUnitIso B S hS f)) ∘
        (fun φ : SheafOfModules.unit (structureRingSheaf B S hS (schemeSpace T)) ⟶
          SheafOfModules.unit (structureRingSheaf B S hS (schemeSpace T)) =>
            (modulePullback B S hS f).map φ) ∘
        (fun a : baseRing B S hS T =>
          unitModuleMul B S hS (schemeSpace T) (globalFunctionsOfMap (𝟙 (schemeSpace T)) a)) :=
    funext fun a => (unitModuleMul_globalFunctionsOfMap_eq f a).trans
      (Iso.homCongr_apply _ _ _).symm
  rw [key]
  exact h3.comp (h2.comp h1)

end AlgebraicGeometry.Space

end
