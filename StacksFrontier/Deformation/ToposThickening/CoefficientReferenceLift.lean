module

public import StacksFrontier.Deformation.ToposThickening.CoefficientSquareZeroReduction
public import StacksFrontier.Deformation.ToposThickening.DerivedExtensionOfScalarsCompAssoc
public import StacksFrontier.Deformation.ToposThickening.DerivedExtensionOfScalarsMinus

/-!
# The reference lifts `s^* K₀` over the trivial square-zero extensions `O₀[V]`

Let `O₀` be a sheaf of commutative rings on a site, with a `k`-algebra structure `θ`, and
`O₀[V] = O₀ ⊕ (O₀ ⊗_k V)` the trivial square-zero extension
(`Deformation.ComplexLift.coefficientRing`). The projection `O₀[V] ⟶ O₀` has the section
`s : O₀ ⟶ O₀[V]`, `a ↦ (a, 0)`, so every bounded above `K₀` has the *trivial lift*
`s^* K₀ = K₀ ⊗^L_{O₀} O₀[V]`, identified with `K₀` after base change back to `O₀` through
`(s^* K₀) ⊗^L O₀ ≅ K₀ ⊗^L_{O₀, 𝟙} O₀ ≅ K₀`
(`Deformation.ComplexLift.coefficientBaseLift`). It lies in `D^{≤ 0}` when `K₀` does, and it is
compatible with base change along `O₀[V] ⟶ O₀[W]` for linear maps `V ⟶ W`, by the associativity
of the identifications of derived base changes along composites
(`Deformation.ComplexLift.derivedExtensionOfScalarsCompIso_assoc`). In the proof of Stacks 0DLL
the trivial lift is `z^* E₀`.

Derived restriction and derived base change along the identity are the identity
(`Deformation.ComplexLift.restrictionOnDerivedIdIso`,
`Deformation.ComplexLift.derivedExtensionOfScalarsIdIso`).

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
* [Stacks Project, Tag 0DIZ](https://stacks.math.columbia.edu/tag/0DIZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe d d₀ v' u u'

namespace Deformation.ComplexLift

section Identity

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (O₀ : Sheaf J CommRingCat.{u})

/-- **Restriction of scalars along the identity is the identity**, on sheaves of modules: the
identity on the underlying presheaves. -/
def restrictScalarsIdIsoOf :
    SheafOfModules.restrictScalars.{u} (ringSheafMapOf J (𝟙 O₀)) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun M =>
    { hom := ⟨PresheafOfModules.homMk (𝟙 M.val.presheaf) (fun _ _ _ => rfl)⟩
      inv := ⟨PresheafOfModules.homMk (𝟙 M.val.presheaf) (fun _ _ _ => rfl)⟩
      hom_inv_id := rfl
      inv_hom_id := rfl }) (fun _ => rfl)

variable [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]

/-- **Derived restriction of scalars along the identity is the identity.** -/
def restrictionOnDerivedIdIso : restrictionOnDerived.{d₀, d₀} (𝟙 O₀) ≅ 𝟭 _ :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
      (ComplexShape.up ℤ))
    ((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J (𝟙 O₀))).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) DerivedCategory.Q _ _
    (Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex (restrictScalarsIdIsoOf O₀) (ComplexShape.up ℤ) ≪≫
        Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)) DerivedCategory.Q ≪≫
      DerivedCategory.Q.leftUnitor)

/-- **Derived base change along the identity is the identity**, by uniqueness of left adjoints
of derived restriction along the identity. -/
def derivedExtensionOfScalarsIdIso : derivedExtensionOfScalars.{d₀, d₀} (𝟙 O₀) ≅ 𝟭 _ :=
  (derivedAdjunction.{d₀, d₀} (𝟙 O₀)).leftAdjointUniq
    (Adjunction.id.ofNatIsoRight (restrictionOnDerivedIdIso.{d₀} O₀).symm)

end Identity

section Reference

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {k : Type u} [Field k] {O₀ : Sheaf J CommRingCat.{u}}
  (θ : Stacks.TensorByBaseModule.constantRingPresheaf (C := C) k ⟶ O₀.obj)

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The section `O₀ ⟶ O₀[M]` is compatible with the maps `O₀[M] ⟶ O₀[N]` induced by morphisms
`M ⟶ N`. -/
theorem sqZeroExtSheafAnySiteSection_comp_map
    {M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)} (φ : M ⟶ N) :
    sqZeroExtSheafAnySiteSection M ≫ sqZeroExtSheafAnySiteMap φ =
      sqZeroExtSheafAnySiteSection N := by
  ext U x
  exact PresheafOfModules.sqZeroExt_ext_anySite rfl (map_zero _)

variable [∀ V : FGModuleCat.{u} k, HasDerivedCategory.{d} (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (coefficientRing θ V)))]
  [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]
  (K₀ : DerivedCategory.Minus (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)))

/-- **The trivial lift `s^* K₀` of `K₀` to `O₀[V]`** (Stacks 0DIZ), for the section
`s : O₀ ⟶ O₀[V]`, `a ↦ (a, 0)`, of the projection, with the identification
`(s^* K₀) ⊗^L O₀ ≅ K₀ ⊗^L_{O₀, 𝟙} O₀ ≅ K₀`. -/
def coefficientBaseLift (V : FGModuleCat.{u} k) :
    DerivedLift (derivedExtensionOfScalarsData.{d, d₀}
      (sqZeroExtSheafAnySiteProj ((coefficientModule θ).obj V))) K₀ where
  K := ⟨(derivedExtensionOfScalars.{d₀, d}
      (sqZeroExtSheafAnySiteSection ((coefficientModule θ).obj V))).obj K₀.obj,
    (derivedExtensionOfScalarsData.{d₀, d} _).minus_baseChange_obj K₀.obj K₀.property⟩
  identification :=
    (derivedExtensionOfScalarsCompIso.{d₀, d, d₀}
        (sqZeroExtSheafAnySiteSection ((coefficientModule θ).obj V))
        (sqZeroExtSheafAnySiteSection_comp_proj _)).app K₀.obj ≪≫
      (derivedExtensionOfScalarsIdIso.{d₀} O₀).app K₀.obj

/-- **The trivial lifts lie in `D^{≤ 0}` when `K₀` does.** -/
theorem coefficientBaseLift_isLE [K₀.obj.IsLE 0] (V : FGModuleCat.{u} k) :
    (coefficientBaseLift.{d, d₀} θ K₀ V).K.obj.IsLE 0 :=
  (derivedExtensionOfScalarsData.{d₀, d} _).isLE_baseChange_obj K₀.obj 0

/-- **The trivial lifts are compatible with base change** along `O₀[V] ⟶ O₀[W]`. -/
theorem coefficientBaseLift_baseChange {V W : FGModuleCat.{u} k} (f : V ⟶ W) :
    DerivedLift.Isomorphic
      ((coefficientBaseLift.{d, d₀} θ K₀ V).baseChange
        (coefficientReductionBaseChange.{d, d₀} θ f))
      (coefficientBaseLift.{d, d₀} θ K₀ W) := by
  refine ⟨(derivedExtensionOfScalarsCompIso.{d₀, d, d}
      (sqZeroExtSheafAnySiteSection ((coefficientModule θ).obj V))
      (sqZeroExtSheafAnySiteSection_comp_map ((coefficientModule θ).map f))).app K₀.obj, ?_⟩
  have e := derivedExtensionOfScalarsCompIso_assoc.{d₀, d, d, d₀}
    (sqZeroExtSheafAnySiteSection ((coefficientModule θ).obj V)) (coefficientRingMap θ f)
    (sqZeroExtSheafAnySiteProj ((coefficientModule θ).obj W))
    (sqZeroExtSheafAnySiteSection_comp_map ((coefficientModule θ).map f))
    (coefficientRingMap_comp_proj θ f) (sqZeroExtSheafAnySiteSection_comp_proj _)
    (sqZeroExtSheafAnySiteSection_comp_proj _) K₀.obj
  exact (reassoc_of% e) _

end Reference

end Deformation.ComplexLift

end
