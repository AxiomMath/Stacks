module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftFiniteColimits
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuleSheafFunctoriality
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Equalizers
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.HigherDirectImageBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.HigherDirectImageSheafification
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Injectives
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.ModuleLowerShriek
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedFamily
public import StacksFrontier.CategoryTheory.Sites.PushforwardSectionsEquivalence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Higher direct images along a 1-morphism of algebraic stacks, via the cohomology of the fibres

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over a scheme `S` and let `τ` be one of the
Zariski, étale, smooth, syntomic and fppf topologies. For an object `y` of `𝒴` lying over a
scheme `V`, write `(Sch/V)_{fppf} ×_{y, 𝒴} 𝒳` for the 2-fibre product of `f` with the
1-morphism `y : (Sch/V)_{fppf} ⟶ 𝒴`, and `pr` for its projection to `𝒳`. Stacks 075G says that
for an abelian sheaf `ℱ` on `𝒳_τ` the higher direct image `Rⁱf_*ℱ` is the sheaf associated to the
presheaf

`y ↦ H^i_τ((Sch/V)_{fppf} ×_{y, 𝒴} 𝒳, pr⁻¹ℱ)`,

and likewise for a sheaf `ℱ` of `𝒪_𝒳`-modules, the cohomology then being that of the sheaf of
modules `pr⁻¹ℱ` and the sheafification being that of a presheaf of `𝒪_𝒴`-modules.

The proof is the source's. The direct image is right Kan extension followed by sheafification,
and sheafification is exact, so `Rⁱf_*ℱ` is the sheafification of the derived presheaf direct
image. The derived presheaf direct image is computed objectwise, and its value at `y` is the
`i`-th derived functor of `ℱ ↦ Γ((Sch/V)_{fppf} ×_{y, 𝒴} 𝒳, pr⁻¹ℱ)` (Stacks 06W6). Finally
`pr⁻¹` is exact and preserves injectives (Stacks 06X1, and Stacks 06X2 for modules): `pr` is
faithful, the scheme slice being faithful over the base, and the 2-fibre product has equalizers,
being equivalent to the comma category of arrows `f(x) ⟶ y` of the algebraic stack `𝒳`
(Stacks 06WY).

## Main definitions

* `AlgebraicGeometry.Stack.ObjectFibre`: the 2-fibre product `(Sch/V)_{fppf} ×_{y, 𝒴} 𝒳`, with its
  projection `objectFibreProjection` to `𝒳` and its topology `objectFibreTopology`.
* `AlgebraicGeometry.Stack.objectFibreCohomology`: `ℱ ↦ H^n_τ((Sch/V)_{fppf} ×_{y, 𝒴} 𝒳, pr⁻¹ℱ)`
  for abelian sheaves, and `AlgebraicGeometry.Stack.objectFibreModuleCohomology` for sheaves of
  modules.
* `AlgebraicGeometry.Stack.objectFibreCohomologyPresheaf` and
  `AlgebraicGeometry.Stack.objectFibreModuleCohomologyPresheaf`: the presheaf
  `y ↦ H^n_τ((Sch/V)_{fppf} ×_{y, 𝒴} 𝒳, pr⁻¹ℱ)` on `𝒴`.
* `AlgebraicGeometry.Stack.presheafDirectImage` and
  `AlgebraicGeometry.Stack.modulePresheafDirectImage`: the presheaf direct images of abelian
  sheaves (Stacks 06TK) and of sheaves of modules (Stacks 06WD).

## Main results

* `AlgebraicGeometry.Stack.preservesInjectiveObjects_objectFibreInverseImage` and
  `AlgebraicGeometry.Stack.preservesInjectiveObjects_objectFibreModuleInverseImage`: `pr⁻¹`
  preserves injective abelian sheaves and injective sheaves of modules.
* `AlgebraicGeometry.Stack.derivedPresheafDirectImageEvaluationIso`: the value at `y` of the
  derived presheaf direct image is the cohomology of the 2-fibre product.
* `AlgebraicGeometry.Stack.higherDirectImageIsoSheafifyFibreCohomology`: **Stacks 075G** for
  abelian sheaves.
* `AlgebraicGeometry.Stack.moduleHigherDirectImageIsoSheafify` and
  `AlgebraicGeometry.Stack.moduleHigherDirectImageIsoSheafifyFibreCohomology`: the sheafification
  step for sheaves of modules, and its reading on underlying abelian presheaves; the statement
  for sheaves of modules with their `𝒪_𝒴(y)`-module structures is in
  `StacksFrontier/AlgebraicGeometry/Stacks/Sheaves/HigherDirectImageFibreCohomologyScalars.lean`.

## Implementation notes

The 1-morphism `(Sch/V)_{fppf} ⟶ 𝒴` attached to `y` is the slice functor of a choice of pullbacks
for `𝒴`, the form in which Stacks 06W6 is available; any two such 1-morphisms are 2-isomorphic
(Stacks 004B). The big fppf site of `V` is the slice of the big fppf site of `S` over `V`, and
the topology of the 2-fibre product is the one Stacks 06TP attaches to it as a category over the
big fppf site of `S`. Cohomology on the 2-fibre product is the right derived functor of global
sections.

The restriction maps of the presheaf `y ↦ H^n_τ(…)` are not given by the source, which leaves
them implicit; here they are the maps induced on right derived functors by the restriction maps
of the presheaf direct image (`objectFibreCohomologyPresheaf_map`), which is what makes the
presheaf the derived presheaf direct image, and so makes the statement true. Its values are the
cohomology groups on the nose (`objectFibreCohomologyPresheaf_obj`).

For sheaves of modules this file identifies `Rⁿf_*ℱ` with the module sheafification of the
derived presheaf direct image of sheaves of modules, and the underlying abelian presheaf of the
latter, restriction maps included, with `y ↦ H^n_τ(…)`, the right derived functors of the global
sections of the underlying abelian sheaf, taken on sheaves of modules. The identification of the
`𝒪_𝒴(y)`-module structures is the subject of
`StacksFrontier/AlgebraicGeometry/Stacks/Sheaves/HigherDirectImageFibreCohomologyScalars.lean`.

## References

* [Stacks Project, Tag 075G](https://stacks.math.columbia.edu/tag/075G)
* [Stacks Project, Tag 06W6](https://stacks.math.columbia.edu/tag/06W6)
* [Stacks Project, Tag 06X1](https://stacks.math.columbia.edu/tag/06X1)
* [Stacks Project, Tag 06X2](https://stacks.math.columbia.edu/tag/06X2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w a

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Fibre

variable {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
  (c : 𝒴.val.p.ChoiceOfPullbacks) (τ : SiteKind)

local notation "g" => CatFiberedInGroupoids.homFunctor f

/-- The 2-fibre product `(Sch/V)_{fppf} ×_{y, 𝒴} 𝒳` of the 1-morphism `f` with the 1-morphism
`y : (Sch/V)_{fppf} ⟶ 𝒴` attached to an object `y` of `𝒴` lying over the scheme `V`, the latter
being the slice functor of the choice of pullbacks `c`. -/
abbrev ObjectFibre (y : 𝒴.val.obj) : Type (u + 1) :=
  TwoFibreProductOver (Over.forget (𝒴.val.p.obj y)) 𝒳.val.p 𝒴.val.p
    (c.sliceFunctor (Functor.Fiber.mk rfl)) g

/-- The projection `pr : (Sch/V)_{fppf} ×_{y, 𝒴} 𝒳 ⟶ 𝒳`. -/
abbrev objectFibreProjection (y : 𝒴.val.obj) : ObjectFibre B S hS f c y ⥤ 𝒳.val.obj :=
  TwoFibreProductOver.snd _ _ _ _ _

/-- The structure functor of the 2-fibre product, to the big fppf site of `S`. -/
abbrev objectFibreStructure (y : 𝒴.val.obj) : ObjectFibre B S hS f c y ⥤ BigFppfOver B S hS :=
  TwoFibreProductOver.structureFunctor _ _ _ _ _

/-- The 2-fibre product is fibred in groupoids over the big fppf site of `S` (Stacks 0041). -/
theorem isFiberedInGroupoids_objectFibreStructure (y : 𝒴.val.obj) :
    (objectFibreStructure B S hS f c y).IsFiberedInGroupoids :=
  TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _
    (Functor.IsFiberedInGroupoids.over_forget _) 𝒳.isFiberedInGroupoids 𝒴.isFiberedInGroupoids
    (c.sliceFunctor_comp _) (CatFiberedInGroupoids.homFunctor_comp_p f)

/-- The topology `τ` on the 2-fibre product, the one of Stacks 06TP. -/
abbrev objectFibreTopology (y : 𝒴.val.obj) : GrothendieckTopology (ObjectFibre B S hS f c y) :=
  BigFppfOver.associatedTopology B S hS (objectFibreStructure B S hS f c y) τ

/-- Abelian sheaves on the site attached by Stacks 06TP to a category over the big fppf site of
`S` admit sheafification, the site being essentially small in the universe of the sections. -/
instance hasSheafify_addCommGrpCat_associatedTopology_ofLargeSite
    {X : Type (u + 1)} [Category.{u} X]
    (p : X ⥤ BigFppfOver B S hS) (τ : SiteKind) :
    HasSheafify (BigFppfOver.associatedTopology B S hS p τ) AddCommGrpCat.{max (u + 1) a} :=
  Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u + 1, u, a}

/-- Abelian sheaves on the site attached by Stacks 06TP to a category over the big fppf site of
`S` have enough injectives: they form a Grothendieck abelian category. -/
instance enoughInjectives_sheafAddCommGrpCat_associatedTopology
    {X : Type (u + 1)} [Category.{u} X]
    (p : X ⥤ BigFppfOver B S hS) (τ : SiteKind) :
    EnoughInjectives (Sheaf (BigFppfOver.associatedTopology B S hS p τ)
      AddCommGrpCat.{max (u + 1) a}) :=
  Stacks.Cohomology.SiteModules.site_enoughInjectives_addCommGrp.{u + 1, u, a}

/-- The global sections functor on abelian sheaves is additive, being a right adjoint. -/
instance additive_globalSections_associatedTopology {X : Type (u + 1)} [Category.{u} X]
    (p : X ⥤ BigFppfOver B S hS) (τ : SiteKind) :
    (Sheaf.Γ (BigFppfOver.associatedTopology B S hS p τ) AddCommGrpCat.{max (u + 1) a}).Additive :=
  have := (constantSheafΓAdj (BigFppfOver.associatedTopology B S hS p τ)
    AddCommGrpCat.{max (u + 1) a}).rightAdjoint_preservesLimits.{0, 0}
  Functor.additive_of_preserves_binary_products _

/-- The 2-fibre product has equalizers when `𝒳` has: it is equivalent to the comma category of
arrows `f(x) ⟶ y` (`CategoryTheory.Presheaf.pushforwardIndexFunctor_isEquivalence`), which
inherits the equalizers of `𝒳`. -/
theorem hasEqualizers_objectFibre [HasEqualizers 𝒳.val.obj] (y : 𝒴.val.obj) :
    HasEqualizers (ObjectFibre B S hS f c y) := by
  have h := Presheaf.pushforwardIndexFunctor_isEquivalence 𝒳.val.p 𝒴.val.p g (c.sliceDatum y)
    𝒴.isFiberedInGroupoids (CatFiberedInGroupoids.homFunctor_comp_p f)
  exact @Adjunction.hasLimitsOfShape_of_equivalence _ _ _ _ _ _
    (Presheaf.pushforwardIndexFunctor 𝒳.val.p 𝒴.val.p g (c.sliceDatum y)) h _

end Fibre

section Abelian

open Stacks.Cohomology.SiteModules

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
  (c : 𝒴.val.val.p.ChoiceOfPullbacks) (τ : SiteKind) (y : 𝒴.val.val.obj)

local notation "g" => CatFiberedInGroupoids.homFunctor f.hom
local notation "JX" => BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ
local notation "JY" => BigFppfOver.associatedTopology B S hS 𝒴.val.val.p τ
local notation "Jf" => objectFibreTopology B S hS f.hom c τ y
local notation "pr" => objectFibreProjection B S hS f.hom c y

/-- The projection from the 2-fibre product is a 1-morphism of categories fibred in groupoids, so
it is continuous for the topologies of Stacks 06TP (Stacks 06NW). -/
instance isContinuous_objectFibreProjection : (pr).IsContinuous Jf JX :=
  have : (objectFibreStructure B S hS f.hom c y).IsFibered :=
    (isFiberedInGroupoids_objectFibreStructure B S hS f.hom c y).isFibered
  have : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  ((𝒳.val.isFiberedInGroupoids.isFibredOneMorphism
    TwoFibreProductOver.snd_comp_eq).isContinuous_and_isCocontinuous_inheritedTopology _).1

/-- The inverse image `pr⁻¹` of abelian sheaves along the projection from the 2-fibre product:
restriction along `pr` (Stacks 06TS). -/
abbrev objectFibreInverseImage :
    Sheaf JX AddCommGrpCat.{max (u + 1) a} ⥤ Sheaf Jf AddCommGrpCat.{max (u + 1) a} :=
  (pr).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) a} Jf JX

/-- The projection from the 2-fibre product as a 1-morphism of fibred categories. -/
theorem isFibredOneMorphism_objectFibreProjection :
    (objectFibreStructure B S hS f.hom c y).IsFibredOneMorphism 𝒳.val.val.p pr :=
  𝒳.val.isFiberedInGroupoids.isFibredOneMorphism TwoFibreProductOver.snd_comp_eq

/-- The inverse image along the projection from the 2-fibre product is additive. -/
instance additive_objectFibreInverseImage :
    (objectFibreInverseImage.{u, w, a} B S hS f c τ y).Additive :=
  have : (objectFibreStructure B S hS f.hom c y).IsFibered :=
    (isFiberedInGroupoids_objectFibreStructure B S hS f.hom c y).isFibered
  have : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  additive_sheafPushforwardContinuous.{u, u + 1, u + 1, u, u, max (u + 1) a} B S hS _ _ _ _
    (isFibredOneMorphism_objectFibreProjection B S hS f c y)

/-- The inverse image along the projection from the 2-fibre product is exact (Stacks 06NW). -/
instance preservesHomology_objectFibreInverseImage :
    (objectFibreInverseImage.{u, w, a} B S hS f c τ y).PreservesHomology :=
  have : (objectFibreStructure B S hS f.hom c y).IsFibered :=
    (isFiberedInGroupoids_objectFibreStructure B S hS f.hom c y).isFibered
  have : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  preservesHomology_sheafPushforwardContinuous.{u, u + 1, u + 1, u, u, max (u + 1) a} B S hS _ _ _ _
    (isFibredOneMorphism_objectFibreProjection B S hS f c y)

/-- **The inverse image along the projection from the 2-fibre product preserves injective
abelian sheaves.** This is Stacks 06X1 for `pr`, which is faithful because the scheme slice is
faithful over the base, and whose source has equalizers because `𝒳`, an algebraic stack, does
(Stacks 06WY). -/
instance preservesInjectiveObjects_objectFibreInverseImage :
    (objectFibreInverseImage.{u, w, a} B S hS f c τ y).PreservesInjectiveObjects where
  injective_obj {I} _ :=
    have := hasEqualizers_objectFibre B S hS f.hom c y
    injective_sheafPushforwardContinuous_obj B S hS _ _ _ _
      (isFiberedInGroupoids_objectFibreStructure B S hS f.hom c y) 𝒳.val.isFiberedInGroupoids
      TwoFibreProductOver.snd_comp_eq I

/-- `H^n_τ((Sch/V)_{fppf} ×_{y, 𝒴} 𝒳, pr⁻¹ℱ)`: the `n`-th cohomology of the inverse image of an
abelian sheaf on the 2-fibre product, as a functor of the sheaf. Cohomology is the right derived
functor of global sections, as for cohomology on any site in this library. -/
abbrev objectFibreCohomology (n : ℕ) :
    Sheaf JX AddCommGrpCat.{max (u + 1) a} ⥤ AddCommGrpCat.{max (u + 1) a} :=
  objectFibreInverseImage.{u, w, a} B S hS f c τ y ⋙
    (Sheaf.Γ Jf AddCommGrpCat.{max (u + 1) a}).rightDerived n

/-- The presheaf direct image of an abelian sheaf: its underlying presheaf followed by right Kan
extension along `f`, the functor `{}_p f` of Stacks 06TK. -/
abbrev presheafDirectImage :
    Sheaf JX AddCommGrpCat.{max (u + 1) a} ⥤ 𝒴.val.val.objᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) a} :=
  sheafToPresheaf JX AddCommGrpCat.{max (u + 1) a} ⋙ (g).op.ran

/-- The presheaf direct image is additive, both factors being right adjoints. -/
instance additive_presheafDirectImage : (presheafDirectImage.{u, w, a} B S hS f τ).Additive :=
  have := ((g).op.ranAdjunction AddCommGrpCat.{max (u + 1) a}).right_adjoint_additive
  inferInstance

/-- The sections of the presheaf direct image over `y` are additive in the sheaf. -/
instance additive_presheafDirectImage_comp_evaluation :
    (presheafDirectImage.{u, w, a} B S hS f τ ⋙
      (evaluation _ AddCommGrpCat.{max (u + 1) a}).obj (op y)).Additive :=
  inferInstance

/-- **Stacks 06W6.** The sections over `y` of the presheaf direct image of an abelian sheaf `ℱ`
are the global sections of `pr⁻¹ℱ` on the 2-fibre product `(Sch/V)_{fppf} ×_{y, 𝒴} 𝒳`,
naturally in `ℱ`. -/
def presheafDirectImageEvaluationIso :
    presheafDirectImage.{u, w, a} B S hS f τ ⋙
        (evaluation _ AddCommGrpCat.{max (u + 1) a}).obj (op y) ≅
      objectFibreInverseImage.{u, w, a} B S hS f c τ y ⋙ Sheaf.Γ Jf AddCommGrpCat.{max (u + 1) a} :=
  Functor.isoWhiskerLeft (sheafToPresheaf JX AddCommGrpCat.{max (u + 1) a})
      (Presheaf.ranEvaluationIsoLimTwoFibreProduct 𝒳.val.val.p 𝒴.val.val.p g (c.sliceDatum y)
        𝒴.val.isFiberedInGroupoids (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
        AddCommGrpCat.{max (u + 1) a}) ≪≫
    Functor.isoWhiskerLeft (objectFibreInverseImage.{u, w, a} B S hS f c τ y)
      (Sheaf.ΓNatIsoLim Jf AddCommGrpCat.{max (u + 1) a}).symm

/-- The derived functors of the sections over `y` of the presheaf direct image are the
cohomology groups of the 2-fibre product: the inverse image along `pr` is exact and preserves
injectives (`preservesInjectiveObjects_objectFibreInverseImage`), so it carries an injective
resolution of `ℱ` to one of `pr⁻¹ℱ`. -/
def derivedPresheafDirectImageEvaluationIso (n : ℕ) (F : Sheaf JX AddCommGrpCat.{max (u + 1) a}) :
    ((presheafDirectImage.{u, w, a} B S hS f τ ⋙
        (evaluation _ AddCommGrpCat.{max (u + 1) a}).obj (op y)).rightDerived n).obj F ≅
      (objectFibreCohomology.{u, w, a} B S hS f c τ y n).obj F :=
  (Functor.rightDerivedIsoOfNatIso (presheafDirectImageEvaluationIso.{u, w, a} B S hS f c τ y)
      n).app F ≪≫
    Functor.rightDerivedCompIsoOfPreservesInjectiveObjects
      (objectFibreInverseImage.{u, w, a} B S hS f c τ y)
      (Sheaf.Γ Jf AddCommGrpCat.{max (u + 1) a}) F n

/-- The family, indexed by the objects of `𝒴`, of the functors "sections over `y` of the presheaf
direct image"; its morphisms are the restriction maps of the presheaf direct image. -/
abbrev presheafDirectImageSections :
    𝒴.val.val.objᵒᵖ ⥤ Sheaf JX AddCommGrpCat.{max (u + 1) a} ⥤ AddCommGrpCat.{max (u + 1) a} :=
  (presheafDirectImage.{u, w, a} B S hS f τ).flip

/-- Taking sections over `y` of the presheaf direct image is an additive functor. -/
instance additive_presheafDirectImageSections_obj (y : 𝒴.val.val.objᵒᵖ) :
    ((presheafDirectImageSections.{u, w, a} B S hS f τ).obj y).Additive :=
  inferInstanceAs (presheafDirectImage.{u, w, a} B S hS f τ ⋙
    (evaluation _ AddCommGrpCat.{max (u + 1) a}).obj y).Additive

/-- **The presheaf `y ↦ H^n_τ((Sch/V)_{fppf} ×_{y, 𝒴} 𝒳, pr⁻¹ℱ)` of Stacks 075G**, for an abelian
sheaf `ℱ` on `𝒳`: its value at an object `y` of `𝒴` lying over the scheme `V` is the `n`-th
cohomology of `pr⁻¹ℱ` on the 2-fibre product (`objectFibreCohomologyPresheaf_obj`), and its
restriction maps are the maps induced on right derived functors by the restriction maps of the
presheaf direct image, read through the identification of the values
(`objectFibreCohomologyPresheaf_map`). -/
def objectFibreCohomologyPresheaf (n : ℕ) (F : Sheaf JX AddCommGrpCat.{max (u + 1) a}) :
    𝒴.val.val.objᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) a} :=
  (((presheafDirectImageSections.{u, w, a} B S hS f τ).rightDerivedFamily n).flip.obj F).copyObj
    (fun y => (objectFibreCohomology.{u, w, a} B S hS f c τ y.unop n).obj F)
    (fun y => derivedPresheafDirectImageEvaluationIso.{u, w, a} B S hS f c τ y.unop n F)

/-- The value of the presheaf of Stacks 075G at `y` is
`H^n_τ((Sch/V)_{fppf} ×_{y, 𝒴} 𝒳, pr⁻¹ℱ)`. -/
@[simp]
lemma objectFibreCohomologyPresheaf_obj (n : ℕ) (F : Sheaf JX AddCommGrpCat.{max (u + 1) a}) :
    (objectFibreCohomologyPresheaf.{u, w, a} B S hS f c τ n F).obj (op y) =
      (objectFibreCohomology.{u, w, a} B S hS f c τ y n).obj F := rfl

/-- The restriction map of the presheaf of Stacks 075G along a morphism `y' ⟶ y` of `𝒴` is the
map induced on right derived functors by the restriction map `(f_*-)(y) ⟶ (f_*-)(y')` of the
presheaf direct image, read through the identifications of the two values with the cohomology of
the two 2-fibre products. -/
lemma objectFibreCohomologyPresheaf_map (n : ℕ) (F : Sheaf JX AddCommGrpCat.{max (u + 1) a})
    {y y' : 𝒴.val.val.objᵒᵖ} (φ : y ⟶ y') :
    (objectFibreCohomologyPresheaf.{u, w, a} B S hS f c τ n F).map φ =
      (derivedPresheafDirectImageEvaluationIso.{u, w, a} B S hS f c τ y.unop n F).inv ≫
        (NatTrans.rightDerived (Functor.whiskerLeft (presheafDirectImage.{u, w, a} B S hS f τ)
          ((evaluation _ AddCommGrpCat.{max (u + 1) a}).map φ)) n).app F ≫
        (derivedPresheafDirectImageEvaluationIso.{u, w, a} B S hS f c τ y'.unop n F).hom := rfl

/-- **Stacks 075G, abelian sheaves.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over
`S` and `τ` one of the Zariski, étale, smooth, syntomic and fppf topologies. For an abelian sheaf
`ℱ` on `𝒳_τ`, the higher direct image `Rⁿf_*ℱ` is the sheaf associated to the presheaf
`y ↦ H^n_τ((Sch/V)_{fppf} ×_{y, 𝒴} 𝒳, pr⁻¹ℱ)`, `y` an object of `𝒴` lying over the scheme `V`.

The direct image is right Kan extension followed by sheafification, and sheafification is exact
(`abelianHigherDirectImage_iso_sheafify_fibreCohomology`); the derived presheaf direct image is
computed objectwise (`CategoryTheory.Functor.rightDerivedFlipObjIso`), and its value at `y` is the
cohomology of the 2-fibre product by Stacks 06W6 and Stacks 06X1
(`derivedPresheafDirectImageEvaluationIso`). -/
@[stacks 075G "abelian sheaves: R^n f_* F is the sheafification of y ↦ H^n((Sch/V) ×_{y,Y} X, \
pr^{-1} F)", sga "4 V 5.1" "clause 1"]
def higherDirectImageIsoSheafifyFibreCohomology (n : ℕ)
    (F : Sheaf JX AddCommGrpCat.{max (u + 1) a}) :
    (((g).sheafPushforwardCocontinuous AddCommGrpCat.{max (u + 1) a} JX JY).rightDerived n).obj F ≅
      (presheafToSheaf JY AddCommGrpCat.{max (u + 1) a}).obj
        (objectFibreCohomologyPresheaf.{u, w, a} B S hS f c τ n F) :=
  (abelianHigherDirectImage_iso_sheafify_fibreCohomology.{u, w, a} B S hS f τ n).app F ≪≫
    (presheafToSheaf JY AddCommGrpCat.{max (u + 1) a}).mapIso
      (Functor.rightDerivedFlipObjIso (presheafDirectImageSections.{u, w, a} B S hS f τ) n F ≪≫
        Functor.isoCopyObj _ _ _)

end Abelian

section Modules

/-- The inverse image of sheaves of modules of Stacks 06WE is restriction of scalars along the
identification of the structure sheaf of the source with the inverse image of the structure sheaf
of the target. -/
theorem modulePullback_eq_sheafOfModules_pushforward {X : Type*} [Category* X] {Y : Type*}
    [Category* Y] (p : X ⥤ BigFppfOver B S hS) (q : Y ⥤ BigFppfOver B S hS) (F : X ⥤ Y)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (hcomp : F ⋙ q = p)
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology) :
    letI : p.IsFibered := hp.isFibered
    letI : q.IsFibered := hq.isFibered
    letI := ((hq.isFibredOneMorphism hcomp).isContinuous_and_isCocontinuous_inheritedTopology
      (τ.over (B.obj hS))).1
    modulePullback.{u, _, _, a} B S hS p q hp hq F hcomp τ hτ =
      SheafOfModules.pushforward.{a} (ringStructureSheafCoreHom B S hS p q F τ hp hq hcomp hτ) := by
  cases hcomp
  rfl

open Stacks.Cohomology.SiteModules

/-- On the site attached by Stacks 06TP to a category over the big fppf site of `S`,
sheafification of abelian presheaves inverts exactly the locally bijective morphisms. -/
instance wEqualsLocallyBijective_addCommGrpCat_associatedTopology_ofLargeSite
    {X : Type (u + 1)} [Category.{u} X]
    (p : X ⥤ BigFppfOver B S hS) (τ : SiteKind) :
    (BigFppfOver.associatedTopology B S hS p τ).WEqualsLocallyBijective
      AddCommGrpCat.{max (u + 1) a} :=
  site_wEqualsLocallyBijective_addCommGrp.{u + 1, u, a}

/-- Sheaves of modules over the structure sheaf of a category fibred in groupoids over the big
fppf site of `S` have enough injectives: they form a Grothendieck abelian category. -/
instance enoughInjectives_moduleSheaves_associatedTopology {X : Type (u + 1)} [Category.{u} X]
    (p : X ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) (τ : SiteKind) :
    EnoughInjectives (SheafOfModules.{max (u + 1) a}
      (ringStructureSheafCore B S hS p hp (B.baseTopology τ) (B.baseTopology_le_topology τ))) :=
  moduleSheavesEnoughInjectives.{u + 1, u, u, max (u + 1) a} _

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
  (c : 𝒴.val.val.p.ChoiceOfPullbacks) (τ : SiteKind) (y : 𝒴.val.val.obj)

local notation "g" => CatFiberedInGroupoids.homFunctor f.hom
local notation "JX" => BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ
local notation "JY" => BigFppfOver.associatedTopology B S hS 𝒴.val.val.p τ
local notation "Jf" => objectFibreTopology B S hS f.hom c τ y
local notation "pr" => objectFibreProjection B S hS f.hom c y
local notation "OX" => ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
  (B.baseTopology τ) (B.baseTopology_le_topology τ)
local notation "OY" => ringStructureSheafCore B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
  (B.baseTopology τ) (B.baseTopology_le_topology τ)
local notation "Of" => ringStructureSheafCore B S hS (objectFibreStructure B S hS f.hom c y)
  (isFiberedInGroupoids_objectFibreStructure B S hS f.hom c y) (B.baseTopology τ)
  (B.baseTopology_le_topology τ)

/-- The inverse image `pr⁻¹` of sheaves of modules along the projection from the 2-fibre product
(Stacks 06WE): restriction along `pr`, the structure sheaf of the 2-fibre product being the
restriction of the one of `𝒳`. -/
abbrev objectFibreModuleInverseImage :
    SheafOfModules.{max (u + 1) a} OX ⥤ SheafOfModules.{max (u + 1) a} Of :=
  modulePullback B S hS (objectFibreStructure B S hS f.hom c y) 𝒳.val.val.p
    (isFiberedInGroupoids_objectFibreStructure B S hS f.hom c y) 𝒳.val.isFiberedInGroupoids pr
    TwoFibreProductOver.snd_comp_eq (B.baseTopology τ) (B.baseTopology_le_topology τ)

/-- The inverse image of sheaves of modules along the projection from the 2-fibre product is
additive: it is restriction along `pr`. -/
instance additive_objectFibreModuleInverseImage :
    (objectFibreModuleInverseImage.{u, w, a} B S hS f c τ y).Additive where
  map_add := by intros; ext; rfl

/-- The inverse image of sheaves of modules along the projection from the 2-fibre product is
left exact: on underlying abelian sheaves it is the inverse image of abelian sheaves, which is
left exact (Stacks 06NW), and forgetting the module structure reflects finite limits. -/
instance preservesFiniteLimits_objectFibreModuleInverseImage :
    PreservesFiniteLimits (objectFibreModuleInverseImage.{u, w, a} B S hS f c τ y) :=
  have : PreservesFiniteLimits (SheafOfModules.toSheaf.{max (u + 1) a} OX) := inferInstance
  have : (objectFibreStructure B S hS f.hom c y).IsFibered :=
    (isFiberedInGroupoids_objectFibreStructure B S hS f.hom c y).isFibered
  have : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  have : PreservesFiniteLimits (objectFibreInverseImage.{u, w, a} B S hS f c τ y) :=
    (isFibredOneMorphism_objectFibreProjection B S hS f c y).preservesFiniteLimits_inverseImage
      (J := BigFppfOver.baseOverTopology B S hS τ) (A := AddCommGrpCat.{max (u + 1) a})
  have : PreservesFiniteLimits (objectFibreModuleInverseImage.{u, w, a} B S hS f c τ y ⋙
      SheafOfModules.toSheaf Of) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf OX ⋙
      objectFibreInverseImage.{u, w, a} B S hS f c τ y))
  preservesFiniteLimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf Of)

/-- The inverse image of sheaves of modules along the projection from the 2-fibre product is
right exact, being left adjoint to the direct image (Stacks 06WE). -/
instance preservesColimits_objectFibreModuleInverseImage :
    PreservesColimits (objectFibreModuleInverseImage.{u, w, a} B S hS f c τ y) :=
  (moduleSheafAdjunction.{u, u + 1, u, a, u + 1, u} B S hS (objectFibreStructure B S hS f.hom c y)
    𝒳.val.val.p (isFiberedInGroupoids_objectFibreStructure B S hS f.hom c y)
    𝒳.val.isFiberedInGroupoids pr TwoFibreProductOver.snd_comp_eq (B.baseTopology τ)
    (B.baseTopology_le_topology τ)).leftAdjoint_preservesColimits

/-- The inverse image of sheaves of modules along the projection from the 2-fibre product is
exact. -/
instance preservesHomology_objectFibreModuleInverseImage :
    (objectFibreModuleInverseImage.{u, w, a} B S hS f c τ y).PreservesHomology :=
  inferInstance

/-- **The inverse image of sheaves of modules along the projection from the 2-fibre product
preserves injectives.** This is Stacks 06X2 for `pr`, which is faithful, and whose source has
equalizers. -/
instance preservesInjectiveObjects_objectFibreModuleInverseImage :
    (objectFibreModuleInverseImage.{u, w, a} B S hS f c τ y).PreservesInjectiveObjects where
  injective_obj {I} _ := by
    have := hasEqualizers_objectFibre B S hS f.hom c y
    have := injective_sheafOfModules_pushforward_obj_of_injective.{u, u + 1, u + 1, u, u,
      max (u + 1) a} B S hS _ _ pr (B.baseTopology τ)
      (isFiberedInGroupoids_objectFibreStructure B S hS f.hom c y) 𝒳.val.isFiberedInGroupoids
      TwoFibreProductOver.snd_comp_eq (B.baseTopology_le_topology τ) I
    rw [objectFibreModuleInverseImage, modulePullback_eq_sheafOfModules_pushforward]
    exact this

/-- The presheaf direct image of a sheaf of modules: its underlying presheaf of modules followed
by the direct image of presheaves of modules of Stacks 06WD. -/
abbrev modulePresheafDirectImage :
    SheafOfModules.{max (u + 1) a} OX ⥤ PresheafOfModules.{max (u + 1) a} (OY).obj :=
  SheafOfModules.forget OX ⋙
    (moduleFunctoriality.{u, u + 1, u, a, u + 1, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
      𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids g
      (CatFiberedInGroupoids.homFunctor_comp_p f.hom)).pushforward

/-- The inverse image of sheaves of modules along `f` is additive: it is restriction of scalars
along `f`. -/
instance additive_moduleInverseImage :
    (modulePullback.{u, u + 1, u, max (u + 1) a, u + 1, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
      𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids g
      (CatFiberedInGroupoids.homFunctor_comp_p f.hom) (B.baseTopology τ)
      (B.baseTopology_le_topology τ)).Additive where
  map_add := by intros; ext; rfl

/-- The direct image of sheaves of modules along `f` is additive, being a right adjoint. -/
instance additive_moduleSheafPushforward_homFunctor :
    (moduleSheafPushforward.{u, u + 1, u, a, u + 1, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
      𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids g
      (CatFiberedInGroupoids.homFunctor_comp_p f.hom) (B.baseTopology τ)
      (B.baseTopology_le_topology τ)).Additive :=
  (moduleSheafAdjunction.{u, u + 1, u, a, u + 1, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
    𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids g
    (CatFiberedInGroupoids.homFunctor_comp_p f.hom) (B.baseTopology τ)
    (B.baseTopology_le_topology τ)).right_adjoint_additive

/-- The presheaf direct image of sheaves of modules along `f` is additive. -/
instance additive_modulePresheafDirectImage :
    (modulePresheafDirectImage.{u, w, a} B S hS f τ).Additive :=
  have : (moduleFunctoriality.{u, u + 1, u, a, u + 1, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
      𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids g
      (CatFiberedInGroupoids.homFunctor_comp_p f.hom)).pullback.Additive :=
    ⟨by intros; ext; rfl⟩
  have := (moduleFunctoriality.{u, u + 1, u, a, u + 1, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
      𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids g
      (CatFiberedInGroupoids.homFunctor_comp_p f.hom)).adjunction.right_adjoint_additive
  ⟨fun {_ _} φ ψ => by
    change (moduleFunctoriality.{u, u + 1, u, a, u + 1, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
      𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids g
      (CatFiberedInGroupoids.homFunctor_comp_p f.hom)).pushforward.map
        ((SheafOfModules.forget OX).map (φ + ψ)) = _
    rw [Functor.map_add]
    exact Functor.map_add _⟩

/-- Sheafification of presheaves of modules is additive, being a left adjoint. -/
instance additive_sheafification_moduleSheaves :
    (PresheafOfModules.sheafification.{max (u + 1) a} (𝟙 (OY).obj)).Additive :=
  (PresheafOfModules.sheafificationAdjunction.{max (u + 1) a} (𝟙 (OY).obj)).left_adjoint_additive

/-- Sheafification of presheaves of modules preserves homology. -/
instance preservesHomology_sheafification_moduleSheaves :
    (PresheafOfModules.sheafification.{max (u + 1) a} (𝟙 (OY).obj)).PreservesHomology :=
  have := (PresheafOfModules.sheafificationAdjunction.{max (u + 1) a}
    (𝟙 (OY).obj)).leftAdjoint_preservesColimits
  inferInstance

/-- **Stacks 075G, sheaves of modules: the sheafification step.** The higher direct image of
sheaves of modules along `f` is the sheafification of the derived presheaf direct image.

The direct image of a sheaf of modules is its presheaf direct image, which is already a sheaf
(Stacks 06WE), so the direct image is the presheaf direct image followed by sheafification; and
sheafification of presheaves of modules is exact. -/
def moduleHigherDirectImageIsoSheafify (n : ℕ) :
    (moduleSheafPushforward.{u, u + 1, u, a, u + 1, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
      𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids g
      (CatFiberedInGroupoids.homFunctor_comp_p f.hom) (B.baseTopology τ)
      (B.baseTopology_le_topology τ)).rightDerived n ≅
      (modulePresheafDirectImage.{u, w, a} B S hS f τ).rightDerived n ⋙
        PresheafOfModules.sheafification.{max (u + 1) a} (𝟙 (OY).obj) :=
  let P := moduleSheafPushforward.{u, u + 1, u, a, u + 1, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
    𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids g
    (CatFiberedInGroupoids.homFunctor_comp_p f.hom) (B.baseTopology τ)
    (B.baseTopology_le_topology τ)
  let T := PresheafOfModules.sheafification.{max (u + 1) a} (𝟙 (OY).obj)
  let e : P ≅ modulePresheafDirectImage.{u, w, a} B S hS f τ ⋙ T :=
    (Functor.rightUnitor P).symm ≪≫
      Functor.isoWhiskerLeft P
        (asIso (PresheafOfModules.sheafificationAdjunction.{max (u + 1) a}
          (𝟙 (OY).obj)).counit).symm ≪≫
      (Functor.associator P (SheafOfModules.forget OY) T).symm
  Functor.rightDerivedIsoOfNatIso e n ≪≫
    Functor.rightDerivedCompIso (modulePresheafDirectImage.{u, w, a} B S hS f τ) T n

/-- `H^n_τ((Sch/V)_{fppf} ×_{y, 𝒴} 𝒳, pr⁻¹ℱ)` for a sheaf `ℱ` of `𝒪_𝒳`-modules: the `n`-th
cohomology of the inverse image of `ℱ` as a module over the structure sheaf of the 2-fibre
product, that is, the `n`-th right derived functor on sheaves of modules of the global sections
functor, read in abelian groups. -/
abbrev objectFibreModuleCohomology (n : ℕ) :
    SheafOfModules.{max (u + 1) a} OX ⥤ AddCommGrpCat.{max (u + 1) a} :=
  objectFibreModuleInverseImage.{u, w, a} B S hS f c τ y ⋙
    (SheafOfModules.toSheaf.{max (u + 1) a} Of ⋙
      Sheaf.Γ Jf AddCommGrpCat.{max (u + 1) a}).rightDerived n

/-- The family, indexed by the objects of `𝒴`, of the functors "sections over `y` of the
presheaf direct image" on sheaves of modules; its morphisms are the restriction maps. -/
abbrev modulePresheafDirectImageSections :
    𝒴.val.val.objᵒᵖ ⥤ SheafOfModules.{max (u + 1) a} OX ⥤ AddCommGrpCat.{max (u + 1) a} :=
  (SheafOfModules.toSheaf.{max (u + 1) a} OX ⋙ presheafDirectImage.{u, w, a} B S hS f τ).flip

/-- Taking sections over `y` of the presheaf direct image of sheaves of modules is an additive
functor. -/
instance additive_modulePresheafDirectImageSections_obj (y : 𝒴.val.val.objᵒᵖ) :
    ((modulePresheafDirectImageSections.{u, w, a} B S hS f τ).obj y).Additive :=
  inferInstanceAs (SheafOfModules.toSheaf.{max (u + 1) a} OX ⋙
    presheafDirectImage.{u, w, a} B S hS f τ ⋙
      (evaluation _ AddCommGrpCat.{max (u + 1) a}).obj y).Additive

/-- **Stacks 06W6 for sheaves of modules.** The sections over `y` of the presheaf direct image of
a sheaf of modules `ℱ` are the global sections of `pr⁻¹ℱ` on the 2-fibre product, naturally in
`ℱ`. -/
def modulePresheafDirectImageEvaluationIso :
    (SheafOfModules.toSheaf.{max (u + 1) a} OX ⋙ presheafDirectImage.{u, w, a} B S hS f τ) ⋙
        (evaluation _ AddCommGrpCat.{max (u + 1) a}).obj (op y) ≅
      objectFibreModuleInverseImage.{u, w, a} B S hS f c τ y ⋙
        (SheafOfModules.toSheaf.{max (u + 1) a} Of ⋙ Sheaf.Γ Jf AddCommGrpCat.{max (u + 1) a}) :=
  Functor.isoWhiskerLeft (SheafOfModules.toSheaf.{max (u + 1) a} OX)
    (presheafDirectImageEvaluationIso.{u, w, a} B S hS f c τ y)

/-- The derived functors of the sections over `y` of the presheaf direct image of sheaves of
modules are the cohomology groups of the 2-fibre product: the inverse image along `pr` is exact
and preserves injective sheaves of modules
(`preservesInjectiveObjects_objectFibreModuleInverseImage`). -/
def derivedModulePresheafDirectImageEvaluationIso (n : ℕ)
    (F : SheafOfModules.{max (u + 1) a} OX) :
    (((modulePresheafDirectImageSections.{u, w, a} B S hS f τ).obj (op y)).rightDerived n).obj F ≅
      (objectFibreModuleCohomology.{u, w, a} B S hS f c τ y n).obj F :=
  (Functor.rightDerivedIsoOfNatIso
      (modulePresheafDirectImageEvaluationIso.{u, w, a} B S hS f c τ y) n).app F ≪≫
    Functor.rightDerivedCompIsoOfPreservesInjectiveObjects
      (objectFibreModuleInverseImage.{u, w, a} B S hS f c τ y)
      (SheafOfModules.toSheaf.{max (u + 1) a} Of ⋙ Sheaf.Γ Jf AddCommGrpCat.{max (u + 1) a}) F n

/-- **The presheaf `y ↦ H^n_τ((Sch/V)_{fppf} ×_{y, 𝒴} 𝒳, pr⁻¹ℱ)` of Stacks 075G** for a sheaf
`ℱ` of `𝒪_𝒳`-modules: its value at `y` is the `n`-th cohomology of the sheaf of modules `pr⁻¹ℱ`
on the 2-fibre product (`objectFibreModuleCohomologyPresheaf_obj`), and its restriction maps are
induced on right derived functors by the restriction maps of the presheaf direct image
(`objectFibreModuleCohomologyPresheaf_map`). -/
def objectFibreModuleCohomologyPresheaf (n : ℕ) (F : SheafOfModules.{max (u + 1) a} OX) :
    𝒴.val.val.objᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) a} :=
  (((modulePresheafDirectImageSections.{u, w, a} B S hS f τ).rightDerivedFamily n).flip.obj
    F).copyObj
    (fun y => (objectFibreModuleCohomology.{u, w, a} B S hS f c τ y.unop n).obj F)
    (fun y => derivedModulePresheafDirectImageEvaluationIso.{u, w, a} B S hS f c τ y.unop n F)

/-- The value of the presheaf of Stacks 075G at `y` is
`H^n_τ((Sch/V)_{fppf} ×_{y, 𝒴} 𝒳, pr⁻¹ℱ)`. -/
@[simp]
lemma objectFibreModuleCohomologyPresheaf_obj (n : ℕ) (F : SheafOfModules.{max (u + 1) a} OX) :
    (objectFibreModuleCohomologyPresheaf.{u, w, a} B S hS f c τ n F).obj (op y) =
      (objectFibreModuleCohomology.{u, w, a} B S hS f c τ y n).obj F := rfl

/-- The restriction maps of the presheaf of Stacks 075G for sheaves of modules are induced on
right derived functors by the restriction maps of the presheaf direct image. -/
lemma objectFibreModuleCohomologyPresheaf_map (n : ℕ) (F : SheafOfModules.{max (u + 1) a} OX)
    {y y' : 𝒴.val.val.objᵒᵖ} (φ : y ⟶ y') :
    (objectFibreModuleCohomologyPresheaf.{u, w, a} B S hS f c τ n F).map φ =
      (derivedModulePresheafDirectImageEvaluationIso.{u, w, a} B S hS f c τ y.unop n F).inv ≫
        (NatTrans.rightDerived ((modulePresheafDirectImageSections.{u, w, a} B S hS f τ).map φ)
          n).app F ≫
        (derivedModulePresheafDirectImageEvaluationIso.{u, w, a} B S hS f c τ y'.unop n F).hom :=
  rfl

/-- On underlying abelian presheaves, the presheaf direct image of a sheaf of modules is the
presheaf direct image of its underlying abelian sheaf (Stacks 06WD). -/
def modulePresheafDirectImageCompToPresheafIso :
    modulePresheafDirectImage.{u, w, a} B S hS f τ ⋙
        PresheafOfModules.toPresheaf.{max (u + 1) a} (OY).obj ≅
      SheafOfModules.toSheaf.{max (u + 1) a} OX ⋙ presheafDirectImage.{u, w, a} B S hS f τ :=
  Functor.isoWhiskerLeft (SheafOfModules.forget OX)
    (moduleFunctoriality.{u, u + 1, u, a, u + 1, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
      𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids g
      (CatFiberedInGroupoids.homFunctor_comp_p f.hom)).pushforward_iso

/-- **Stacks 075G for sheaves of modules, read on underlying abelian presheaves.** For a sheaf `ℱ`
of `𝒪_𝒳`-modules, `Rⁿf_*ℱ` is the sheaf of `𝒪_𝒴`-modules associated to the `n`-th derived
presheaf direct image, whose underlying abelian presheaf is
`y ↦ H^n_τ((Sch/V)_{fppf} ×_{y, 𝒴} 𝒳, pr⁻¹ℱ)`, cohomology of the underlying abelian sheaf of
`pr⁻¹ℱ`, including its restriction maps. The form with the `𝒪_𝒴(y)`-module structures, with
module cohomology, is
`AlgebraicGeometry.Stack.moduleHigherDirectImageIsoSheafifyFibreModuleCohomology`.

The first isomorphism is `moduleHigherDirectImageIsoSheafify`. For the second, forgetting the
module structure is exact, so the underlying presheaf of the derived presheaf direct image is the
derived functor of the presheaf direct image of the underlying abelian sheaf; that is computed
objectwise (`CategoryTheory.Functor.rightDerivedFlipObjIso`), and its value at `y` is the
cohomology of the 2-fibre product by Stacks 06W6 and Stacks 06X2
(`derivedModulePresheafDirectImageEvaluationIso`). -/
def moduleHigherDirectImageIsoSheafifyFibreCohomology (n : ℕ)
    (F : SheafOfModules.{max (u + 1) a} OX) :
    (((moduleSheafPushforward.{u, u + 1, u, a, u + 1, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
        𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids g
        (CatFiberedInGroupoids.homFunctor_comp_p f.hom) (B.baseTopology τ)
        (B.baseTopology_le_topology τ)).rightDerived n).obj F ≅
        (PresheafOfModules.sheafification.{max (u + 1) a} (𝟙 (OY).obj)).obj
          (((modulePresheafDirectImage.{u, w, a} B S hS f τ).rightDerived n).obj F)) ×
      ((PresheafOfModules.toPresheaf.{max (u + 1) a} (OY).obj).obj
          (((modulePresheafDirectImage.{u, w, a} B S hS f τ).rightDerived n).obj F) ≅
        objectFibreModuleCohomologyPresheaf.{u, w, a} B S hS f c τ n F) :=
  ⟨(moduleHigherDirectImageIsoSheafify.{u, w, a} B S hS f τ n).app F,
    (Functor.rightDerivedCompIso (modulePresheafDirectImage.{u, w, a} B S hS f τ)
        (PresheafOfModules.toPresheaf.{max (u + 1) a} (OY).obj) n).symm.app F ≪≫
      (Functor.rightDerivedIsoOfNatIso
        (modulePresheafDirectImageCompToPresheafIso.{u, w, a} B S hS f τ) n).app F ≪≫
      Functor.rightDerivedFlipObjIso (modulePresheafDirectImageSections.{u, w, a} B S hS f τ) n F ≪≫
      Functor.isoCopyObj _ _ _⟩

/-- For a sheaf `ℱ` of `𝒪_𝒳`-modules, the underlying abelian sheaf of `Rⁿf_*ℱ` is the sheaf
associated to the presheaf `y ↦ H^n_τ((Sch/V)_{fppf} ×_{y, 𝒴} 𝒳, pr⁻¹ℱ)`: sheafification of
presheaves of modules is sheafification of the underlying abelian presheaves. -/
def moduleHigherDirectImageToSheafIso (n : ℕ) (F : SheafOfModules.{max (u + 1) a} OX) :
    (SheafOfModules.toSheaf.{max (u + 1) a} OY).obj
        (((moduleSheafPushforward.{u, u + 1, u, a, u + 1, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
          𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids g
          (CatFiberedInGroupoids.homFunctor_comp_p f.hom) (B.baseTopology τ)
          (B.baseTopology_le_topology τ)).rightDerived n).obj F) ≅
      (presheafToSheaf JY AddCommGrpCat.{max (u + 1) a}).obj
        (objectFibreModuleCohomologyPresheaf.{u, w, a} B S hS f c τ n F) :=
  (SheafOfModules.toSheaf.{max (u + 1) a} OY).mapIso
      (moduleHigherDirectImageIsoSheafifyFibreCohomology.{u, w, a} B S hS f c τ n F).1 ≪≫
    (PresheafOfModules.sheafificationCompToSheaf.{max (u + 1) a} (𝟙 (OY).obj)).app _ ≪≫
    (presheafToSheaf JY AddCommGrpCat.{max (u + 1) a}).mapIso
      (moduleHigherDirectImageIsoSheafifyFibreCohomology.{u, w, a} B S hS f c τ n F).2

end Modules

end AlgebraicGeometry.Stack

end
