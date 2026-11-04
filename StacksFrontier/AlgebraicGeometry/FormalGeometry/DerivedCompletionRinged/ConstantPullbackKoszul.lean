module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.ConstantToposHom
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.ConstantNoetherianCompletion
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackGlobalSectionSmul
public import StacksFrontier.CategoryTheory.Preadditive.FunctorIsoOnSummands

/-!
# Pulling back constant sheaves of modules along a morphism of topoi

Let `f : Sh(𝒟) ⟶ Sh(𝒞)` be a morphism of topoi, `Λ` a commutative ring, and read `f` as the
morphism of ringed topoi `(Sh(𝒟), Λ̲) ⟶ (Sh(𝒞), Λ̲)` of
`MorphismOfTopoi.constantRingedToposHom`. The pullback `f^*` of sheaves of modules carries the
constant sheaf of modules `M̲` on a finite free `Λ`-module `M` to `M̲`, naturally in `M`: both
`M ↦ f^*M̲` and `M ↦ M̲` are additive, they agree on `Λ` by `f^*Λ̲ = Λ̲`, and under that
identification `f^*` carries multiplication by `a̲` to multiplication by `a̲`, which is the
action of `a ∈ Λ`. In particular `f^*` carries the constant sheaf of modules applied termwise to
a complex of finite free `Λ`-modules to the same on `𝒟`, naturally in the complex, and this
applies to the tower of Koszul complexes `K(Λ, g_1^{n+1}, …, g_r^{n+1})` through which the
derived completion along `IΛ̲` is computed in [Stacks, Tag 099M].

## Main results

* `MorphismOfTopoi.pullbackTerminalSection_constantSectionHom`: the image of the global section
  `a̲` under the structure map is `a̲`.
* `MorphismOfTopoi.pullbackModules_map_constantScalar`: `f^*` carries multiplication by `a̲` to
  multiplication by `a̲`.
* `MorphismOfTopoi.constantPullbackUnitIso` and
  `MorphismOfTopoi.constantPullbackUnitIso_naturality`: `f^*Λ̲ ≅ Λ̲` as constant sheaves of modules
  on `Λ`, compatibly with every endomorphism of `Λ`.
* `MorphismOfTopoi.constantKoszulPullbackSystemIso`: the tower `n ↦ f^*K(Λ, g^{n+1})̲` of
  complexes is the tower `n ↦ K(Λ, g^{n+1})̲`.

## References

* [Stacks Project, Tag 099M](https://stacks.math.columbia.edu/tag/099M)
* [Stacks Project, Tag 099N](https://stacks.math.columbia.edu/tag/099N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace MorphismOfTopoi

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {D : Type u} [Category.{u} D] {K : GrothendieckTopology D} (Λ : Type u) [CommRing Λ]
  (f : MorphismOfTopoi (Sheaf K (Type u)) (Sheaf J (Type u)))

/-- **The structure map of `MorphismOfTopoi.constantRingedToposHom` carries `a̲` to `a̲`**, as
global sections. -/
theorem pullbackTerminalSection_constantSectionHom (a : Λ) :
    Stacks.Sheaves.RingedToposModules.pullbackTerminalSection
        (constantRingedToposHom Λ f).toModulesHom (RingedTopos.constantSectionHom J Λ a) =
      RingedTopos.constantSectionHom K Λ a := by
  show f.inverseImageTerminalIso.inv ≫
    (f.inverseImage.map (RingedTopos.constantSectionHom J Λ a) ≫
      (sheafCompose K (forget RingCat.{u})).map
        (constantRingedToposHom Λ f).fSharpInverseImageRing) = _
  rw [map_constantSectionHom_comp_fSharpInverseImageRing, Iso.inv_hom_id_assoc]

/-- **The pullback carries multiplication by `a̲` to multiplication by `a̲`**, under the
identification `f^*Λ̲ ≅ Λ̲`. -/
theorem pullbackModules_map_constantScalar (a : Λ) :
    (constantRingedToposHom Λ f).toModulesHom.pullbackModules.map
        ((Stacks.SheafOfModules.globalSectionToEnd _ (RingedSite.constantSection J Λ a)).app
          (SheafOfModules.unit _)) ≫
        (Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso
          (constantRingedToposHom Λ f).toModulesHom).inv =
      (Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso
          (constantRingedToposHom Λ f).toModulesHom).inv ≫
        (Stacks.SheafOfModules.globalSectionToEnd _ (RingedSite.constantSection K Λ a)).app
          (SheafOfModules.unit _) := by
  have h := Stacks.Sheaves.RingedToposModules.pullbackModules_map_globalSectionToEnd_unit
    (constantRingedToposHom Λ f).toModulesHom (RingedTopos.constantSectionHom J Λ a)
  rw [pullbackTerminalSection_constantSectionHom] at h
  exact h

/-- The functor `M ↦ f^*M̲` from `Λ`-modules to sheaves of `Λ̲`-modules on `𝒟`. -/
abbrev constantPullbackFunctor :
    ModuleCat.{u} Λ ⥤ SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSite.constant K Λ).O) :=
  RingedSite.constantModuleFunctor J Λ ⋙ (constantRingedToposHom Λ f).toModulesHom.pullbackModules

/-- The pullback of sheaves of modules along `MorphismOfTopoi.constantRingedToposHom` is
additive. -/
instance : (constantRingedToposHom Λ f).toModulesHom.pullbackModules.Additive :=
  RingedToposHom.pullbackModules_additive (constantRingedToposHom Λ f)

/-- **`f^*Λ̲ ≅ Λ̲`**, read as constant sheaves of modules on `Λ`. -/
def constantPullbackUnitIso :
    (constantPullbackFunctor Λ f).obj (ModuleCat.of Λ Λ) ≅
      (RingedSite.constantModuleFunctor K Λ).obj (ModuleCat.of Λ Λ) :=
  (constantRingedToposHom Λ f).toModulesHom.pullbackModules.mapIso
      (RingedSite.constantModuleFunctorUnitIso J Λ) ≪≫
    (Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso
      (constantRingedToposHom Λ f).toModulesHom).symm ≪≫
    (RingedSite.constantModuleFunctorUnitIso K Λ).symm

/-- Every endomorphism of the `Λ`-module `Λ` is multiplication by its value at `1`. -/
theorem _root_.ModuleCat.self_hom_eq_smul_id (φ : ModuleCat.of Λ Λ ⟶ ModuleCat.of Λ Λ) :
    φ = (φ.hom (1 : Λ)) • 𝟙 (ModuleCat.of Λ Λ) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  show φ.hom x = φ.hom 1 • x
  rw [smul_eq_mul, mul_comm, ← smul_eq_mul, ← LinearMap.map_smul, smul_eq_mul, mul_one]

/-- **`f^*Λ̲ ≅ Λ̲` is compatible with the action of `Λ`**: it intertwines the two images of every
endomorphism of the `Λ`-module `Λ`. -/
theorem constantPullbackUnitIso_naturality (φ : ModuleCat.of Λ Λ ⟶ ModuleCat.of Λ Λ) :
    (constantPullbackFunctor Λ f).map φ ≫ (constantPullbackUnitIso Λ f).hom =
      (constantPullbackUnitIso Λ f).hom ≫ (RingedSite.constantModuleFunctor K Λ).map φ := by
  rw [ModuleCat.self_hom_eq_smul_id Λ φ]
  set a := φ.hom 1
  have hC := RingedSite.constantModuleFunctor_map_smul_unitIso J Λ a
  have hD := RingedSite.constantModuleFunctor_map_smul_unitIso K Λ a
  have hD' : (RingedSite.constantModuleFunctorUnitIso K Λ).inv ≫
      (RingedSite.constantModuleFunctor K Λ).map (a • 𝟙 (ModuleCat.of Λ Λ)) =
      (Stacks.SheafOfModules.globalSectionToEnd _ (RingedSite.constantSection K Λ a)).app
          (SheafOfModules.unit _) ≫ (RingedSite.constantModuleFunctorUnitIso K Λ).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hD, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  simp only [constantPullbackUnitIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Category.assoc, hD']
  show (constantRingedToposHom Λ f).toModulesHom.pullbackModules.map
      ((RingedSite.constantModuleFunctor J Λ).map (a • 𝟙 (ModuleCat.of Λ Λ))) ≫ _ = _
  rw [← Functor.map_comp_assoc, hC, Functor.map_comp_assoc, reassoc_of%
    pullbackModules_map_constantScalar Λ f a]

variable {r : ℕ} (x : Fin r → Λ)

/-- **The pullback of the constant Koszul complex**: `f^*K(Λ, x^{n+1})̲ ≅ K(Λ, x^{n+1})̲`,
degreewise the comparison of the finite sums of copies of `Λ̲` given by the exterior bases. -/
def constantKoszulPullbackIso (n : ℕ) :
    ((constantPullbackFunctor Λ f).mapHomologicalComplex _).obj
        (RingedSite.ringKoszulComplex x n) ≅
      ((RingedSite.constantModuleFunctor K Λ).mapHomologicalComplex _).obj
        (RingedSite.ringKoszulComplex x n) :=
  Functor.mapHomologicalComplexIsoOfSummands (constantPullbackUnitIso Λ f)
    (constantPullbackUnitIso_naturality Λ f) (RingedSite.ringKoszulComplex x n)
    (fun j => AlternatingCech.Idx r (-j)) (fun j S => RingedSite.ringKoszulCoord x n S)
    (fun j => Functor.summandsOfIsIsoPiLift (fun S => RingedSite.ringKoszulCoord x n S))
    (fun j => Functor.sum_comp_summandsOfIsIsoPiLift _)

/-- **The pullback of the tower of constant Koszul complexes is the tower of constant Koszul
complexes**, naturally in the exponent. -/
def constantKoszulPullbackSystemIso :
    RingedSite.ringKoszulSystem x ⋙ (constantPullbackFunctor Λ f).mapHomologicalComplex _ ≅
      RingedSite.ringKoszulSystem x ⋙
        (RingedSite.constantModuleFunctor K Λ).mapHomologicalComplex _ :=
  NatIso.ofComponents (fun n => constantKoszulPullbackIso Λ f x n.unop) (fun {a b} h =>
    Functor.mapHomologicalComplexIsoOfSummands_hom_naturality (constantPullbackUnitIso Λ f)
      (constantPullbackUnitIso_naturality Λ f) _ _ _ _ _ _ _ _ _ _ _)

/-- **The pullback of the tower of dual Koszul complexes on the constant site of `𝒞` is the tower
of dual Koszul complexes on the constant site of `𝒟`**, for the sections `x̲_1, …, x̲_r` on both
sides. -/
def koszulPowerDualComplexSystemPullbackIso :
    RingedSite.koszulPowerDualComplexSystem (RingedSite.constant J Λ)
        (fun i => RingedSite.constantGlobalSection J Λ (x i)) ⋙
      (constantRingedToposHom Λ f).toModulesHom.pullbackModules.mapHomologicalComplex _ ≅
      RingedSite.koszulPowerDualComplexSystem (RingedSite.constant K Λ)
        (fun i => RingedSite.constantGlobalSection K Λ (x i)) :=
  Functor.isoWhiskerRight (RingedSite.koszulPowerDualComplexSystemIso J Λ x).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (RingedSite.ringKoszulSystem x)
      (Functor.mapHomologicalComplexCompIso (Iso.refl (constantPullbackFunctor Λ f)) _) ≪≫
    constantKoszulPullbackSystemIso Λ f x ≪≫ RingedSite.koszulPowerDualComplexSystemIso K Λ x

end MorphismOfTopoi

end
