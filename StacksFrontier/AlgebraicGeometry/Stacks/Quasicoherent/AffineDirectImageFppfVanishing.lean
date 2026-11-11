module

public import StacksFrontier.AlgebraicGeometry.Stacks.AffineMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineFlatBaseChangeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineMorphismTerminalArrow
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorFlatFppf
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineObjectCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineObjectsFppfCovering
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfModulesBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfModulesDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfEtaleCohomologyComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfModulesEnoughInjectives
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentCartesian
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeAffineCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeProperty
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.VanishingFromSectionsFormula
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ModuleSections

/-!
# The direct image along an affine 1-morphism of algebraic stacks (Stacks 0GQI)

Let `f : 𝒳 ⟶ 𝒴` be an affine 1-morphism of algebraic stacks over `S` (**Stacks 0CHQ**).
**Stacks 0GQI** asserts that on `LQCoh^fbc(𝒪_𝒳)`

1. the direct image `f_*` is exact,
2. `f_*` commutes with direct sums, and
3. the higher direct images `Rⁱf_*` vanish for `i > 0`.

Everything is read in the source's default setting: modules on the **fppf** sites, at the module
universe `u` of the schemes, with the direct image `AlgebraicGeometry.Stack.fppfModulesPushforward`
and its right derived functors `AlgebraicGeometry.Stack.fppfModulesHigherDirectImage`, and with
`LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)` the subcategory
`AlgebraicGeometry.Stack.lqcohSheafFbcFppfModules` cut out by local quasi-coherence and the
(sheaf-level) flat base change property of **Stacks 0762**.

## The proof

The source reduces along charts to an affine morphism of schemes.  The argument here stays on the
site of `𝒳` and is the dimension-shifting argument behind Cohomology on Sites, Lemma 03F7.

* For `y` an object of `𝒴` lying over an affine scheme, the base change of `f` along `y` is an
  affine scheme, so `CostructuredArrow f y` has a terminal object `(x₀, f x₀ ⟶ y)` with `x₀` lying
  over an affine scheme, and `Γ(y, f_* M) = Γ(x₀, M)` naturally in `M`.
* A module `F` in `LQCoh^fbc(𝒪_𝒳)` is cartesian along flat morphisms of affines, so its Čech
  cohomology vanishes on finite fppf coverings by affine objects (Stacks 03FJ), hence
  `Hⁿ(x, F) = 0` for `n > 0` at every object `x` lying over an affine scheme (Stacks 03F9):
  `AlgebraicGeometry.Stack.isZero_rightDerived_evaluation_of_isAffine_algebraicStack`.
* The class of modules with this vanishing is effaceable for `f_*`: embedding into an injective
  keeps the cokernel in the class and makes `f_*` of the quotient map surjective on sections over
  the objects lying over affine schemes, which cover `𝒴`
  (`SheafOfModules.isZero_rightDerived_of_sectionsFormula`).  This is assertion (3).
* Assertion (1) is the vanishing of `R¹f_*` on the first term
  (`Stacks.Cohomology.RightDerivedDelta.shortExact_map_of_isZero_rightDerived_one`).
* Assertion (2) holds because sections over objects lying over affine schemes, which are
  quasi-compact, commute with direct sums (Stacks 0935), on `𝒴` and on `𝒳`
  (`SheafOfModules.preservesColimit_discrete_of_sectionsFormula`); it needs no hypothesis on the
  family.

## Main results

* `AlgebraicGeometry.Stack.stacks0GQI`: **Stacks 0GQI**, for the functor
  `AlgebraicGeometry.Stack.affineLqcohSheafFbcPushforward : LQCoh^fbc(𝒪_𝒳) ⥤ LQCoh^fbc(𝒪_𝒴)`.

* `AlgebraicGeometry.Stack.isZero_rightDerived_evaluation_of_isAffine_algebraicStack`: the
  affine acyclicity.
* `AlgebraicGeometry.Stack.stacks0GQI_of_isCartesianAlongFlatAffine`: the three assertions, from
  the cartesian condition on the objects of `LQCoh^fbc(𝒪_𝒳)`.

## References

* [Stacks Project, Tag 0GQI](https://stacks.math.columbia.edu/tag/0GQI)
* [Stacks Project, Tag 03F7](https://stacks.math.columbia.edu/tag/03F7)
* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 0935](https://stacks.math.columbia.edu/tag/0935)
* [Stacks Project, Tag 0CHQ](https://stacks.math.columbia.edu/tag/0CHQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

attribute [local instance 5000] SheafOfModules.instAbelian

namespace AlgebraicGeometry.Stack

attribute [local instance] FlatFppf.hasSheafify_fppf_addCommGrpCat
  FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

section Instances

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- Abelian sheaves on the fppf site of an algebraic stack, at the universe `u`, form a
Grothendieck abelian category: the site is essentially `u`-small. -/
theorem isGrothendieckAbelian_fppfSheaves :
    IsGrothendieckAbelian.{u}
      (Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf) AddCommGrpCat.{u}) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

set_option synthInstance.maxHeartbeats 400000 in
-- Lean v4.35.0: the `HasProducts` instance searches behind `hasExt_of_enoughInjectives`
-- exceed the default instance-synthesis limit.
set_option maxHeartbeats 800000 in
-- Lean v4.35.0: the `HasProducts` searches behind `hasExt_of_enoughInjectives` exceed the default.
/-- **Stacks 0GQI's affine acyclicity on an algebraic stack**: a module on the fppf site of an
algebraic stack which is cartesian along flat morphisms of affines has no higher cohomology over
an object lying over an affine scheme. -/
theorem isZero_rightDerived_evaluation_of_isAffine_algebraicStack
    (F : fppfModules B S hS 𝒳)
    (hF : FibredSite.IsCartesianAlongFlatAffines B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F)
    {x : 𝒳.val.val.obj} (hx : IsAffine (FibredSite.schemeOf B S hS 𝒳.val.val.p x)) (n : ℕ)
    (hn : 0 < n) :
    letI := enoughInjectives_fppfModules B S hS 𝒳
    IsZero (((SheafOfModules.evaluation (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids .fppf) (op x)).rightDerived n).obj F) := by
  let := enoughInjectives_fppfModules B S hS 𝒳
  let := isGrothendieckAbelian_fppfSheaves B S hS 𝒳
  let : HasExt.{u + 1}
      (Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf) AddCommGrpCat.{u}) :=
    hasExt_of_enoughInjectives _
  let : HasExt.{u + 1} (fppfModules B S hS 𝒳) := hasExt_of_enoughInjectives _
  exact FibredSite.isZero_rightDerived_evaluation_of_isAffine B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids F hF hx n hn

end Instances

section Terminal

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)

/-- The sections over `y` of an fppf module, read through `SheafOfModules.toSheaf` and
`sheafSections`, are its sections read through the underlying abelian presheaf. -/
def toSheafSectionsIsoEvaluation {𝒵 : AlgebraicStacks.{u, w} B S hS} (z : 𝒵.val.val.obj) :
    SheafOfModules.toSheaf (FibredSite.ringStructureSheafCore B S hS 𝒵.val.val.p
        𝒵.val.isFiberedInGroupoids .fppf) ⋙
      (sheafSections (BigFppfOver.associatedTopology B S hS 𝒵.val.val.p .fppf)
        AddCommGrpCat.{u}).obj (op z) ≅
    Stacks.SheafOfModules.toAbelianPresheaf.{u} _ ⋙
      (evaluation 𝒵.val.val.objᵒᵖ AddCommGrpCat.{u}).obj (op z) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- The sections formula of an affine 1-morphism, in the shape consumed below. -/
def pushforwardSectionsIsoOfIsTerminal {y : 𝒴.val.val.obj}
    {t : CostructuredArrow (CatFiberedInGroupoids.homFunctor f.hom) y} (ht : IsTerminal t) :
    fppfModulesPushforward B S hS f ⋙
      SheafOfModules.toSheaf (FibredSite.ringStructureSheafCore B S hS 𝒴.val.val.p
        𝒴.val.isFiberedInGroupoids .fppf) ⋙
      (sheafSections (BigFppfOver.associatedTopology B S hS 𝒴.val.val.p .fppf)
        AddCommGrpCat.{u}).obj (op y) ≅
    SheafOfModules.toSheaf (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids .fppf) ⋙
      (sheafSections (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf)
        AddCommGrpCat.{u}).obj (op t.left) :=
  Functor.isoWhiskerLeft _ (toSheafSectionsIsoEvaluation B S hS y) ≪≫
    fppfModulesPushforwardSectionsIsoOfIsTerminal B S hS f ht ≪≫
    (toSheafSectionsIsoEvaluation B S hS t.left).symm

end Terminal

section Assembly

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
  (hcart : ∀ F : fppfModules B S hS 𝒳, lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 F →
    FibredSite.IsCartesianAlongFlatAffines B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F)
  (x₀ : ∀ y : 𝒴.val.val.obj, IsAffine (FibredSite.schemeOf B S hS 𝒴.val.val.p y) →
    𝒳.val.val.obj)
  (hx₀ : ∀ y hy, IsAffine (FibredSite.schemeOf B S hS 𝒳.val.val.p (x₀ y hy)))
  (e : ∀ y hy, fppfModulesPushforward B S hS f ⋙
      SheafOfModules.toSheaf (FibredSite.ringStructureSheafCore B S hS 𝒴.val.val.p
        𝒴.val.isFiberedInGroupoids .fppf) ⋙
      (sheafSections (BigFppfOver.associatedTopology B S hS 𝒴.val.val.p .fppf)
        AddCommGrpCat.{u}).obj (op y) ≅
    SheafOfModules.toSheaf (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids .fppf) ⋙
      (sheafSections (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .fppf)
        AddCommGrpCat.{u}).obj (op (x₀ y hy)))

/-- The direct image of modules at universe `u` is left exact, being a right adjoint. -/
instance preservesFiniteLimits_fppfModulesPushforward :
    PreservesFiniteLimits (fppfModulesPushforward B S hS f) :=
  have := (fppfModulesPullbackPushforwardAdjunction B S hS f).rightAdjoint_preservesLimits
  inferInstance

include hcart hx₀ e in
/-- Assertion (3) of Stacks 0GQI from the sections formula. -/
theorem isZero_fppfModulesHigherDirectImage_of_sectionsFormula (i : ℕ) (hi : 0 < i)
    (F : fppfModules B S hS 𝒳) (hF : lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 F) :
    IsZero ((fppfModulesHigherDirectImage B S hS f i).obj F) := by
  let := enoughInjectives_fppfModules B S hS 𝒳
  exact SheafOfModules.isZero_rightDerived_of_sectionsFormula (fppfModulesPushforward B S hS f)
    (fun y => IsAffine (FibredSite.schemeOf B S hS 𝒴.val.val.p y))
    (FibredSite.mem_of_forall_isAffine B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids) x₀ e F
    (fun y hy n hn => isZero_rightDerived_evaluation_of_isAffine_algebraicStack B S hS 𝒳 F
      (hcart F hF) (hx₀ y hy) n hn) i hi

include hcart hx₀ e in
/-- Assertion (1) of Stacks 0GQI from the sections formula. -/
theorem shortExact_map_fppfModulesPushforward_of_sectionsFormula
    (Sq : ShortComplex (fppfModules B S hS 𝒳)) (hSq : Sq.ShortExact)
    (h₁ : lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 Sq.X₁) :
    (Sq.map (fppfModulesPushforward B S hS f)).ShortExact := by
  let := enoughInjectives_fppfModules B S hS 𝒳
  exact Stacks.Cohomology.RightDerivedDelta.shortExact_map_of_isZero_rightDerived_one _ hSq
    (isZero_fppfModulesHigherDirectImage_of_sectionsFormula B E h S hS f hcart x₀ hx₀ e 1
      one_pos _ h₁)

/-- Sections over an object lying over an affine scheme commute with direct sums. -/
private theorem preservesColimitsOfShape_sections_of_isAffine {𝒵 : AlgebraicStacks.{u, w} B S hS}
    (z : 𝒵.val.val.obj) (hz : IsAffine (FibredSite.schemeOf B S hS 𝒵.val.val.p z)) (ι : Type u) :
    PreservesColimitsOfShape (Discrete ι)
      (SheafOfModules.toSheaf (FibredSite.ringStructureSheafCore B S hS 𝒵.val.val.p
        𝒵.val.isFiberedInGroupoids .fppf) ⋙
      (sheafSections (BigFppfOver.associatedTopology B S hS 𝒵.val.val.p .fppf)
        AddCommGrpCat.{u}).obj (op z)) :=
  Stacks.Sites.sheafOfModules_sections_preserves_coproducts _ _ z
    (FibredSite.isQuasiCompactObject_of_isAffine B S hS 𝒵.val.val.p 𝒵.val.isFiberedInGroupoids z
      hz) ι

include hx₀ e in
/-- Assertion (2) of Stacks 0GQI from the sections formula. -/
theorem preservesColimit_fppfModulesPushforward_of_sectionsFormula {ι : Type u}
    (F : ι → fppfModules B S hS 𝒳) :
    PreservesColimit (Discrete.functor F) (fppfModulesPushforward B S hS f) := by
  let := enoughInjectives_fppfModules B S hS 𝒳
  let := enoughInjectives_fppfModules B S hS 𝒴
  let := isGrothendieckAbelian_fppfModules B S hS 𝒳
  let := isGrothendieckAbelian_fppfModules B S hS 𝒴
  exact SheafOfModules.preservesColimit_discrete_of_sectionsFormula
    (fppfModulesPushforward B S hS f)
    (fun y => IsAffine (FibredSite.schemeOf B S hS 𝒴.val.val.p y))
    (FibredSite.mem_of_forall_isAffine B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids) x₀ e F
    (fun y hy => (preservesColimitsOfShape_sections_of_isAffine B S hS y hy ι).preservesColimit)
    (fun y hy => (preservesColimitsOfShape_sections_of_isAffine B S hS (x₀ y hy) (hx₀ y hy)
      ι).preservesColimit)

end Assembly

section Affine

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
  (hf : AlgebraicStacks.IsAffineHom B S hS f)
  (hcart : ∀ F : fppfModules B S hS 𝒳, lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 F →
    IsCartesianAlongFlatAffine B S hS 𝒳 F)

/-- The terminal arrow of an affine 1-morphism into an object lying over an affine scheme. -/
def affineTerminalArrow (y : 𝒴.val.val.obj)
    (hy : IsAffine (FibredSite.schemeOf B S hS 𝒴.val.val.p y)) :
    CostructuredArrow (CatFiberedInGroupoids.homFunctor f.hom) y :=
  (AlgebraicStacks.exists_isTerminal_costructuredArrow_of_isAffineHom B S hS f hf y hy).choose

/-- `AlgebraicGeometry.Stack.affineTerminalArrow` is terminal. -/
def isTerminal_affineTerminalArrow (y : 𝒴.val.val.obj)
    (hy : IsAffine (FibredSite.schemeOf B S hS 𝒴.val.val.p y)) :
    IsTerminal (affineTerminalArrow B S hS f hf y hy) :=
  (AlgebraicStacks.exists_isTerminal_costructuredArrow_of_isAffineHom B S hS f hf y
    hy).choose_spec.1.some

/-- The source of `AlgebraicGeometry.Stack.affineTerminalArrow` lies over an affine scheme. -/
theorem isAffine_affineTerminalArrow_left (y : 𝒴.val.val.obj)
    (hy : IsAffine (FibredSite.schemeOf B S hS 𝒴.val.val.p y)) :
    IsAffine (FibredSite.schemeOf B S hS 𝒳.val.val.p (affineTerminalArrow B S hS f hf y hy).left) :=
  (AlgebraicStacks.exists_isTerminal_costructuredArrow_of_isAffineHom B S hS f hf y
    hy).choose_spec.2

include hf in
/-- **The direct image along an affine 1-morphism preserves cartesianness along flat arrows
between affine objects**: the arrow between the terminal arrows over `y ⟶ y'` lies over the base
change of the flat morphism under `y ⟶ y'`, which is flat
(`AlgebraicGeometry.Stack.isIso_restrictionBaseChange_stackModuleDirectImage_of_isAffineHom`). -/
theorem isCartesianAlongFlatAffine_fppfModulesPushforward (F : fppfModules B S hS 𝒳)
    (hF : IsCartesianAlongFlatAffine B S hS 𝒳 F) :
    IsCartesianAlongFlatAffine B S hS 𝒴 ((fppfModulesPushforward B S hS f).obj F) :=
  fun _ _ φ hfl hy hy' => isIso_restrictionBaseChange_stackModuleDirectImage_of_isAffineHom B S hS
    @Flat .fppf f hf F (fun _ _ ψ hx hx' hψ => hF ψ hψ hx hx') φ hy hy' hfl

include hf in
/-- **The direct image along an affine 1-morphism of a module cartesian along flat arrows between
affine objects is locally quasi-coherent** (Stacks 06WJ, through
`AlgebraicGeometry.Stack.isLocallyQuasicoherent_iff_forall_isIso_restrictionBaseChange`): étale
morphisms are flat. -/
theorem isLocallyQuasicoherent_fppfModulesPushforward (F : fppfModules B S hS 𝒳)
    (hF : IsCartesianAlongFlatAffine B S hS 𝒳 F) :
    IsLocallyQuasicoherent B E h S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
      ((fppfModulesPushforward B S hS f).obj F).val :=
  (isLocallyQuasicoherent_iff_forall_isIso_restrictionBaseChange B E h S hS 𝒴.val.val.p
    𝒴.val.isFiberedInGroupoids ⟨((fppfModulesPushforward B S hS f).obj F).val,
      ((fppfModulesPushforward B S hS f).obj F).isSheaf.of_le
        (BigFppfOver.associatedTopology_le_fppf B S hS 𝒴.val.val.p .etale)⟩).2
    fun _ _ φ hy hy' het => by
      have : Etale (B.inclusion.map (𝒴.val.val.p.map φ).left) := het
      exact isCartesianAlongFlatAffine_fppfModulesPushforward B S hS f hf F hF φ inferInstance hy
        hy'

include hf in
/-- **The direct image along an affine 1-morphism of a module cartesian along flat arrows between
affine objects lies in `LQCoh^fbc(𝒪_𝒴)`**: it is locally quasi-coherent
(`AlgebraicGeometry.Stack.isLocallyQuasicoherent_fppfModulesPushforward`) and cartesian along
flat arrows between affine objects, hence has the flat base change property (Stacks 0762) by the
affine criterion
`AlgebraicGeometry.Stack.hasSheafFlatBaseChangeProperty_of_isIso_restrictionBaseChange`. -/
theorem lqcohSheafFbcFppfModules_fppfModulesPushforward (F : fppfModules B S hS 𝒳)
    (hF : IsCartesianAlongFlatAffine B S hS 𝒳 F) :
    lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴 ((fppfModulesPushforward B S hS f).obj F) :=
  have hl := isLocallyQuasicoherent_fppfModulesPushforward B E h S hS f hf F hF
  ⟨hl, hasSheafFlatBaseChangeProperty_of_isIso_restrictionBaseChange B E h S hS 𝒴.val.val.p
    𝒴.val.isFiberedInGroupoids _ fun φ hy hy' hfl =>
      isCartesianAlongFlatAffine_fppfModulesPushforward B S hS f hf F hF φ hfl hy hy'⟩

include hf hcart in
/-- **The direct image along an affine 1-morphism, as a functor
`f_* : LQCoh^fbc(𝒪_𝒳) ⥤ LQCoh^fbc(𝒪_𝒴)`**, given that the objects of `LQCoh^fbc(𝒪_𝒳)` are
cartesian along flat arrows between affine objects (`hcart`): its values lie in `LQCoh^fbc(𝒪_𝒴)`
by `AlgebraicGeometry.Stack.lqcohSheafFbcFppfModules_fppfModulesPushforward`. -/
def lqcohSheafFbcPushforwardOfIsCartesian :
    (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).FullSubcategory ⥤
      (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴).FullSubcategory :=
  ObjectProperty.lift _ ((lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι ⋙
    fppfModulesPushforward B S hS f) fun F =>
      lqcohSheafFbcFppfModules_fppfModulesPushforward B E h S hS f hf F.obj (hcart F.obj F.property)

include hf hcart in
/-- The functor `f_* : LQCoh^fbc(𝒪_𝒳) ⥤ LQCoh^fbc(𝒪_𝒴)` is additive. -/
instance additive_lqcohSheafFbcPushforwardOfIsCartesian :
    (lqcohSheafFbcPushforwardOfIsCartesian B E h S hS f hf hcart).Additive :=
  haveI : (lqcohSheafFbcPushforwardOfIsCartesian B E h S hS f hf hcart ⋙
      (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴).ι).Additive :=
    inferInstanceAs ((lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι ⋙
      fppfModulesPushforward B S hS f).Additive
  Functor.additive_of_comp_faithful _ (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴).ι

include hf hcart in
/-- **The three assertions of Stacks 0GQI for an affine 1-morphism, given that the objects of
`LQCoh^fbc(𝒪_𝒳)` are cartesian along flat arrows between affine objects** (the step R2 of the
proof of Stacks 0779, the entry point `hcart`), for the functor
`f_* : LQCoh^fbc(𝒪_𝒳) ⥤ LQCoh^fbc(𝒪_𝒴)` of
`AlgebraicGeometry.Stack.lqcohSheafFbcPushforwardOfIsCartesian`:

1. `f_*` is exact: it carries a sequence of `LQCoh^fbc(𝒪_𝒳)` short exact in `Mod(𝒪_𝒳)` to a
   sequence short exact in `Mod(𝒪_𝒴)` (the subcategories are weak Serre, Stacks 0771 (2));
2. `f_*` commutes with direct sums indexed by any `ι : Type u`, and
3. `Rⁱf_* F = 0` for `i > 0` and `F` in `LQCoh^fbc(𝒪_𝒳)`. -/
theorem stacks0GQI_of_isCartesianAlongFlatAffine :
    (∀ Sq : ShortComplex (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).FullSubcategory,
        (Sq.map (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι).ShortExact →
        (Sq.map (lqcohSheafFbcPushforwardOfIsCartesian B E h S hS f hf hcart ⋙
          (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴).ι)).ShortExact) ∧
      (∀ ι : Type u, PreservesColimitsOfShape (Discrete ι)
        (lqcohSheafFbcPushforwardOfIsCartesian B E h S hS f hf hcart)) ∧
      (∀ (i : ℕ), 0 < i → ∀ F : fppfModules B S hS 𝒳,
        lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 F →
          IsZero ((fppfModulesHigherDirectImage B S hS f i).obj F)) := by
  have hc := fun F hF => isCartesianAlongFlatAffines_of_isIso_restrictionBaseChange B S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F fun φ hfl hz hx => hcart F hF φ hfl hz hx
  have hx := isAffine_affineTerminalArrow_left B S hS f hf
  have e := fun y hy => pushforwardSectionsIsoOfIsTerminal B S hS f
    (isTerminal_affineTerminalArrow B S hS f hf y hy)
  refine ⟨fun Sq hSq => ?_, fun ι => ?_, fun i hi F hF => ?_⟩
  · have h1 := shortExact_map_fppfModulesPushforward_of_sectionsFormula B E h S hS f hc _ hx e
      (Sq.map (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι) hSq Sq.X₁.property
    have h2 : (Sq.map ((lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι ⋙
        fppfModulesPushforward B S hS f)).ShortExact := by
      rw [ShortComplex.map_comp]
      exact h1
    exact ShortComplex.shortExact_of_iso (Sq.mapNatIso (ObjectProperty.liftCompιIso _ _ _)).symm
      h2
  · have h𝒳 := (lqcohSheafFbc_hasColimits_and_agree B E h S hS 𝒳).2.1
    have : PreservesColimitsOfShape (Discrete ι) (fppfModulesPushforward B S hS f) :=
      ⟨fun {K} => by
        have : PreservesColimit (Discrete.functor (K.obj ∘ Discrete.mk))
            (fppfModulesPushforward B S hS f) :=
          preservesColimit_fppfModulesPushforward_of_sectionsFormula B S hS f _ hx e
            (K.obj ∘ Discrete.mk)
        exact preservesColimit_of_iso_diagram _ (Discrete.natIsoFunctor (F := K)).symm⟩
    have : PreservesColimitsOfShape (Discrete ι)
        (lqcohSheafFbcPushforwardOfIsCartesian B E h S hS f hf hcart ⋙
          (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴).ι) :=
      inferInstanceAs (PreservesColimitsOfShape (Discrete ι)
        ((lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι ⋙ fppfModulesPushforward B S hS f))
    exact preservesColimitsOfShape_of_reflects_of_preserves _
      (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴).ι
  · exact isZero_fppfModulesHigherDirectImage_of_sectionsFormula B E h S hS f hc _ hx e i hi F hF

/-- **The direct image along an affine 1-morphism, `f_* : LQCoh^fbc(𝒪_𝒳) ⥤ LQCoh^fbc(𝒪_𝒴)`**:
the objects of `LQCoh^fbc(𝒪_𝒳)` are cartesian along flat arrows between affine objects
(`AlgebraicGeometry.Stack.isCartesianAlongFlatAffine_of_lqcohSheafFbcFppfModules`), so their
direct images lie in `LQCoh^fbc(𝒪_𝒴)`. -/
def affineLqcohSheafFbcPushforward :
    (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).FullSubcategory ⥤
      (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴).FullSubcategory :=
  lqcohSheafFbcPushforwardOfIsCartesian B E h S hS f hf
    (isCartesianAlongFlatAffine_of_lqcohSheafFbcFppfModules B E h S hS)

/-- The functor `f_* : LQCoh^fbc(𝒪_𝒳) ⥤ LQCoh^fbc(𝒪_𝒴)` of an affine 1-morphism is additive. -/
instance additive_affineLqcohSheafFbcPushforward :
    (affineLqcohSheafFbcPushforward B E h S hS f hf).Additive :=
  additive_lqcohSheafFbcPushforwardOfIsCartesian B E h S hS f hf _

/-- `AlgebraicGeometry.Stack.affineLqcohSheafFbcPushforward` is the direct image
`AlgebraicGeometry.Stack.fppfModulesPushforward` restricted to `LQCoh^fbc`. -/
def affineLqcohSheafFbcPushforwardCompιIso :
    affineLqcohSheafFbcPushforward B E h S hS f hf ⋙
        (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴).ι ≅
      (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι ⋙ fppfModulesPushforward B S hS f :=
  ObjectProperty.liftCompιIso _ _ _

/-- **Stacks 0GQI.** Let `f : 𝒳 ⟶ 𝒴` be an affine 1-morphism of algebraic stacks over `S`.  The
direct image restricts to a functor `f_* : LQCoh^fbc(𝒪_𝒳) ⥤ LQCoh^fbc(𝒪_𝒴)`
(`AlgebraicGeometry.Stack.affineLqcohSheafFbcPushforward`, which is
`AlgebraicGeometry.Stack.fppfModulesPushforward` on objects and morphisms by
`AlgebraicGeometry.Stack.affineLqcohSheafFbcPushforwardCompιIso`), and

1. `f_*` is exact: a sequence of `LQCoh^fbc(𝒪_𝒳)` which is short exact in `Mod(𝒪_𝒳)` goes to a
   sequence short exact in `Mod(𝒪_𝒴)`;
2. `f_*` commutes with direct sums (indexed by any `ι : Type u`);
3. `Rⁱf_* F = 0` for every `i > 0` and `F` in `LQCoh^fbc(𝒪_𝒳)`.

Modules are on the fppf sites at the module universe `u` of the schemes; `LQCoh^fbc` is
`AlgebraicGeometry.Stack.lqcohSheafFbcFppfModules`. -/
@[stacks 0GQI "all three assertions, for an affine 1-morphism f, on the fppf \
  sites at module universe u: f_* restricts to LQCoh^fbc(O_X) -> LQCoh^fbc(O_Y); (1) it is exact \
  (short exact sequences of LQCoh^fbc, read in Mod, go to short exact sequences); (2) it \
  commutes with direct sums; (3) R^i f_* F = 0 for i > 0 and F in LQCoh^fbc(O_X)"]
theorem stacks0GQI :
    (∀ Sq : ShortComplex (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).FullSubcategory,
        (Sq.map (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).ι).ShortExact →
        (Sq.map (affineLqcohSheafFbcPushforward B E h S hS f hf ⋙
          (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒴).ι)).ShortExact) ∧
      (∀ ι : Type u, PreservesColimitsOfShape (Discrete ι)
        (affineLqcohSheafFbcPushforward B E h S hS f hf)) ∧
      (∀ (i : ℕ), 0 < i → ∀ F : fppfModules B S hS 𝒳,
        lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 F →
          IsZero ((fppfModulesHigherDirectImage B S hS f i).obj F)) :=
  stacks0GQI_of_isCartesianAlongFlatAffine B E h S hS f hf
    (isCartesianAlongFlatAffine_of_lqcohSheafFbcFppfModules B E h S hS)

end Affine

end AlgebraicGeometry.Stack
