module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageLocallyQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleModuleComparisonUnivLE

/-!
# The derived category with quasi-coherent cohomology, at a free module universe

The Verdier quotient

`D_QCoh(𝒪_𝒳) = D_{LQCoh^fbc}(𝒪_𝒳) / D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`

on the fppf modules of an algebraic stack, with module sections in a universe `t` subject only to
`UnivLE.{u, t}`, where `u` is the universe of the schemes. The flat base change half of the
membership condition is read at `t` by `AlgebraicGeometry.Stack.HasFlatBaseChangePropertyUnivLE`.
At `t = u` each construction is definitionally the corresponding one of
`AlgebraicGeometry.Stack.derivedCategoryQuasicoherent`. At `t = u + 1`, the section universe of
the direct images of module sheaves along 1-morphisms of algebraic stacks, the fppf modules are
abelian, have a derived category and have enough injectives.

## Main definitions

* `AlgebraicGeometry.Stack.fppfModulesUnivLE`: `Mod(𝒪_𝒳)` at a free module universe.
* `AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeFppfModulesUnivLE`: `LQCoh^fbc`
  at a free module universe.
* `AlgebraicGeometry.Stack.derivedLocallyQuasicoherentFlatBaseChangeUnivLE` and
  `AlgebraicGeometry.Stack.derivedParasiticLocallyQuasicoherentFlatBaseChangeUnivLE`: the two
  derived subcategories at a free module universe.
* `AlgebraicGeometry.Stack.derivedCategoryQuasicoherentUnivLE` and
  `AlgebraicGeometry.Stack.toDerivedCategoryQuasicoherentUnivLE`: the Verdier quotient and its
  quotient functor, at a free module universe.
* `AlgebraicGeometry.Stack.fppfModuleSheafPushforwardOfHom` and
  `AlgebraicGeometry.Stack.fppfDerivedPushforwardPlus`: the direct image on fppf modules along a
  1-morphism of algebraic stacks, and its total right derived functor
  `Rf_* : D⁺(𝒪_𝒳) ⥤ D⁺(𝒪_𝒴)`, both at module universe `u + 1`.
* `AlgebraicGeometry.Stack.IsLocallyQuasicoherentWithFlatBaseChangeFppfHigherDirectImage`: the
  assertion that `Rⁱf_*` carries `LQCoh^fbc(𝒪_𝒳)` into `LQCoh^fbc(𝒪_𝒴)`, with both read on the fppf
  site at module universe `u + 1`.

## Main results

* `AlgebraicGeometry.Stack.fibredSite_ringStructureSheafCore_eq`: the `SiteKind`-indexed and the
  topology-indexed structure sheaves agree.
* `AlgebraicGeometry.Stack.fppfModulesUnivLE_eq`,
  `AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeFppfModulesUnivLE_eq`,
  `AlgebraicGeometry.Stack.derivedLocallyQuasicoherentFlatBaseChangeUnivLE_eq`,
  `AlgebraicGeometry.Stack.derivedParasiticLocallyQuasicoherentFlatBaseChangeUnivLE_eq`,
  `AlgebraicGeometry.Stack.derivedQuasicoherentWUnivLE_eq`,
  `AlgebraicGeometry.Stack.derivedCategoryQuasicoherentUnivLE_eq` and
  `AlgebraicGeometry.Stack.toDerivedCategoryQuasicoherentUnivLE_eq`: at `t = u` every
  construction is the one at module universe `u`, definitionally.
* `AlgebraicGeometry.Stack.hasSheafify_fppfAssociatedTopology_of_category_succ` and
  `AlgebraicGeometry.Stack.wEqualsLocallyBijective_fppfAssociatedTopology_of_category_succ`:
  sheafification of abelian sheaves, and local isomorphisms are locally bijective, on the
  associated fppf site at section universe `u + 1`.
* `AlgebraicGeometry.Stack.abelian_fppfModulesSucc`,
  `AlgebraicGeometry.Stack.hasDerivedCategory_fppfModulesSucc` and
  `AlgebraicGeometry.Stack.enoughInjectives_fppfModuleSheavesSucc`: at `t = u + 1` the fppf
  modules are abelian, have a derived category and have enough injectives.

## References

* [Stacks Project, Tag 06TP](https://stacks.math.columbia.edu/tag/06TP)
* [Stacks Project, Tag 06TV](https://stacks.math.columbia.edu/tag/06TV)
* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 0773](https://stacks.math.columbia.edu/tag/0773)
* [Stacks Project, Tag 0775](https://stacks.math.columbia.edu/tag/0775)
* [Stacks Project, Tag 07B6](https://stacks.math.columbia.edu/tag/07B6)
* [Stacks Project, Tag 07BC](https://stacks.math.columbia.edu/tag/07BC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w t d

namespace AlgebraicGeometry.Stack

section StructureSheaf

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type w} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- The `SiteKind`-indexed structure sheaf `AlgebraicGeometry.FibredSite.ringStructureSheafCore`
is the topology-indexed `AlgebraicGeometry.Stack.ringStructureSheafCore` at the base topology of
that `SiteKind`. -/
theorem fibredSite_ringStructureSheafCore_eq (τ : SiteKind) :
    FibredSite.ringStructureSheafCore B S hS p hp τ =
      ringStructureSheafCore B S hS p hp (B.baseTopology τ) (B.baseTopology_le_topology τ) :=
  rfl

end StructureSheaf

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- The category `Mod(𝒪_𝒳)` of modules on the fppf site of an algebraic stack, at a module
universe `t` left free. At `t = u` this is `AlgebraicGeometry.Stack.fppfModules`. -/
abbrev fppfModulesUnivLE :=
  SheafOfModules.{t} (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids .fppf)

/-- At module universe `u`, `fppfModulesUnivLE` is `AlgebraicGeometry.Stack.fppfModules`. -/
theorem fppfModulesUnivLE_eq :
    fppfModulesUnivLE.{u, w, u} B S hS 𝒳 = fppfModules B S hS 𝒳 :=
  rfl

/-- The subcategory `LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)` at a module universe `t` above the universe of
the schemes: a module on the fppf site belongs to it when its restriction to the associated étale
site is locally quasi-coherent and has the flat base change property, the latter read at `t` by
`AlgebraicGeometry.Stack.HasFlatBaseChangePropertyUnivLE`. -/
abbrev locallyQuasicoherentFlatBaseChangeFppfModulesUnivLE [UnivLE.{u, t}] :
    ObjectProperty (fppfModulesUnivLE.{u, w, t} B S hS 𝒳) :=
  fun F => IsLocallyQuasicoherent B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F.val ∧
    HasFlatBaseChangePropertyUnivLE B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      (etaleTopology B) (etaleTopology_le_topology B) F.val

/-- At module universe `u`, `locallyQuasicoherentFlatBaseChangeFppfModulesUnivLE` is
`AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeFppfModules`. -/
theorem locallyQuasicoherentFlatBaseChangeFppfModulesUnivLE_eq :
    locallyQuasicoherentFlatBaseChangeFppfModulesUnivLE.{u, w, u} B E h S hS 𝒳 =
      locallyQuasicoherentFlatBaseChangeFppfModules B E h S hS 𝒳 :=
  rfl

section Sheafification

variable {𝒵 : Type (u + 1)} [Category.{u} 𝒵] (r : 𝒵 ⥤ BigFppfOver B S hS)

/-- The associated fppf site of a category whose objects lie in `Type (u + 1)` and whose
morphisms lie in `Type u` admits sheafification of abelian sheaves at section universe
`u + 1`. -/
theorem hasSheafify_fppfAssociatedTopology_of_category_succ :
    HasSheafify (BigFppfOver.associatedTopology B S hS r .fppf) AddCommGrpCat.{u + 1} :=
  have : EssentiallySmall.{u + 1, u, u + 1} 𝒵 := inferInstance
  hasSheafifyEssentiallySmallSite _ _

/-- The associated fppf site of a category whose objects lie in `Type (u + 1)` and whose
morphisms lie in `Type u` has the property that the local isomorphisms of abelian sheaves at
section universe `u + 1` are the locally bijective morphisms. -/
theorem wEqualsLocallyBijective_fppfAssociatedTopology_of_category_succ :
    (BigFppfOver.associatedTopology B S hS r .fppf).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} :=
  have : EssentiallySmall.{u + 1, u, u + 1} 𝒵 := inferInstance
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- At module universe `u + 1` the fppf modules over the structure sheaf are abelian. -/
@[instance_reducible]
def abelian_fppfModuleSheavesSucc (hr : r.IsFiberedInGroupoids) :
    Abelian (SheafOfModules.{u + 1} (FibredSite.ringStructureSheafCore B S hS r hr .fppf)) :=
  letI := hasSheafify_fppfAssociatedTopology_of_category_succ B S hS r
  letI := wEqualsLocallyBijective_fppfAssociatedTopology_of_category_succ B S hS r
  inferInstance

/-- At module universe `u + 1` the fppf modules over the structure sheaf have the standard derived
category. -/
@[instance_reducible]
def hasDerivedCategory_fppfModuleSheavesSucc (hr : r.IsFiberedInGroupoids) :
    letI := abelian_fppfModuleSheavesSucc B S hS r hr
    HasDerivedCategory.{u + 2}
      (SheafOfModules.{u + 1} (FibredSite.ringStructureSheafCore B S hS r hr .fppf)) :=
  letI := abelian_fppfModuleSheavesSucc B S hS r hr
  HasDerivedCategory.standard _

/-- At module universe `u + 1` the fppf modules over the structure sheaf have enough injectives. -/
theorem enoughInjectives_fppfModuleSheavesSucc (hr : r.IsFiberedInGroupoids) :
    letI := abelian_fppfModuleSheavesSucc B S hS r hr
    EnoughInjectives
      (SheafOfModules.{u + 1} (FibredSite.ringStructureSheafCore B S hS r hr .fppf)) :=
  let := hasSheafify_fppfAssociatedTopology_of_category_succ B S hS r
  let := wEqualsLocallyBijective_fppfAssociatedTopology_of_category_succ B S hS r
  let := abelian_fppfModuleSheavesSucc B S hS r hr
  enoughInjectives_moduleSheaves.{u, u + 1, u, u + 1} B S hS r hr (B.baseTopology .fppf)
    (B.baseTopology_le_topology .fppf)

/-- At module universe `u + 1` the fppf modules of an algebraic stack are abelian. -/
@[instance_reducible]
def abelian_fppfModulesSucc : Abelian (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒳) :=
  abelian_fppfModuleSheavesSucc B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids

/-- At module universe `u + 1` the fppf modules of an algebraic stack have the standard derived
category. -/
@[instance_reducible]
def hasDerivedCategory_fppfModulesSucc :
    letI := abelian_fppfModulesSucc.{u, w} B S hS 𝒳
    HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒳) :=
  hasDerivedCategory_fppfModuleSheavesSucc B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids

end Sheafification

section Derived

variable [Abelian (fppfModulesUnivLE.{u, w, t} B S hS 𝒳)]
  [HasDerivedCategory.{d} (fppfModulesUnivLE.{u, w, t} B S hS 𝒳)] [UnivLE.{u, t}]

/-- The subcategory `D_{LQCoh^fbc}(𝒪_𝒳) ⊆ D(𝒪_𝒳)` at a module universe `t` above the universe of
the schemes: the complexes of fppf modules all of whose cohomology modules are locally
quasi-coherent with the flat base change property. -/
abbrev derivedLocallyQuasicoherentFlatBaseChangeUnivLE :
    ObjectProperty (DerivedCategory (fppfModulesUnivLE.{u, w, t} B S hS 𝒳)) :=
  DerivedCategoryB.derivedCategoryB
    (locallyQuasicoherentFlatBaseChangeFppfModulesUnivLE.{u, w, t} B E h S hS 𝒳)

/-- The subcategory `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳) ⊆ D(𝒪_𝒳)` at a module universe `t` above the
universe of the schemes: the complexes of fppf modules all of whose cohomology modules are
parasitic *and* locally quasi-coherent with the flat base change property. -/
abbrev derivedParasiticLocallyQuasicoherentFlatBaseChangeUnivLE :
    ObjectProperty (DerivedCategory (fppfModulesUnivLE.{u, w, t} B S hS 𝒳)) :=
  DerivedCategoryB.derivedCategoryB
    (parasiticModules.{u, w, t} B S hS 𝒳 .fppf ⊓
      locallyQuasicoherentFlatBaseChangeFppfModulesUnivLE.{u, w, t} B E h S hS 𝒳)

/-- The class of morphisms of `D_{LQCoh^fbc}(𝒪_𝒳)` which the Verdier quotient `D_QCoh(𝒪_𝒳)`
inverts, at a module universe `t` above the universe of the schemes: those whose cone, taken in the
ambient derived category `D(𝒪_𝒳)`, lies in `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`. -/
abbrev derivedQuasicoherentWUnivLE :
    MorphismProperty
      (derivedLocallyQuasicoherentFlatBaseChangeUnivLE.{u, w, t, d}
        B E h S hS 𝒳).FullSubcategory :=
  MorphismProperty.inverseImage
    (derivedParasiticLocallyQuasicoherentFlatBaseChangeUnivLE.{u, w, t, d} B E h S hS 𝒳).trW
    (derivedLocallyQuasicoherentFlatBaseChangeUnivLE.{u, w, t, d} B E h S hS 𝒳).ι

/-- The Verdier quotient

`D_QCoh(𝒪_𝒳) = D_{LQCoh^fbc}(𝒪_𝒳) / D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`

at a module universe `t` above the universe of the schemes: the localization of
`D_{LQCoh^fbc}(𝒪_𝒳)` at the morphisms whose cone lies in `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`. -/
abbrev derivedCategoryQuasicoherentUnivLE :=
  (derivedQuasicoherentWUnivLE.{u, w, t, d} B E h S hS 𝒳).Localization

/-- The quotient functor `D_{LQCoh^fbc}(𝒪_𝒳) ⟶ D_QCoh(𝒪_𝒳)` of the Verdier quotient, at a module
universe `t` above the universe of the schemes. -/
abbrev toDerivedCategoryQuasicoherentUnivLE :
    (derivedLocallyQuasicoherentFlatBaseChangeUnivLE.{u, w, t, d}
        B E h S hS 𝒳).FullSubcategory ⥤
      derivedCategoryQuasicoherentUnivLE.{u, w, t, d} B E h S hS 𝒳 :=
  (derivedQuasicoherentWUnivLE.{u, w, t, d} B E h S hS 𝒳).Q

end Derived

section Agreement

variable [Abelian (fppfModules B S hS 𝒳)] [HasDerivedCategory.{d} (fppfModules B S hS 𝒳)]

/-- At module universe `u`, `derivedLocallyQuasicoherentFlatBaseChangeUnivLE` is
`AlgebraicGeometry.Stack.derivedLocallyQuasicoherentFlatBaseChange`. -/
theorem derivedLocallyQuasicoherentFlatBaseChangeUnivLE_eq :
    derivedLocallyQuasicoherentFlatBaseChangeUnivLE.{u, w, u, d} B E h S hS 𝒳 =
      derivedLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳 :=
  rfl

/-- At module universe `u`, `derivedParasiticLocallyQuasicoherentFlatBaseChangeUnivLE` is
`AlgebraicGeometry.Stack.derivedParasiticLocallyQuasicoherentFlatBaseChange`. -/
theorem derivedParasiticLocallyQuasicoherentFlatBaseChangeUnivLE_eq :
    derivedParasiticLocallyQuasicoherentFlatBaseChangeUnivLE.{u, w, u, d} B E h S hS 𝒳 =
      derivedParasiticLocallyQuasicoherentFlatBaseChange B E h S hS 𝒳 :=
  rfl

/-- At module universe `u`, `derivedQuasicoherentWUnivLE` is
`AlgebraicGeometry.Stack.derivedQuasicoherentW`. -/
theorem derivedQuasicoherentWUnivLE_eq :
    derivedQuasicoherentWUnivLE.{u, w, u, d} B E h S hS 𝒳 =
      derivedQuasicoherentW B E h S hS 𝒳 :=
  rfl

/-- At module universe `u`, `derivedCategoryQuasicoherentUnivLE` is
`AlgebraicGeometry.Stack.derivedCategoryQuasicoherent`. -/
theorem derivedCategoryQuasicoherentUnivLE_eq :
    derivedCategoryQuasicoherentUnivLE.{u, w, u, d} B E h S hS 𝒳 =
      derivedCategoryQuasicoherent B E h S hS 𝒳 :=
  rfl

/-- At module universe `u`, `toDerivedCategoryQuasicoherentUnivLE` is
`AlgebraicGeometry.Stack.toDerivedCategoryQuasicoherent`. -/
theorem toDerivedCategoryQuasicoherentUnivLE_eq :
    toDerivedCategoryQuasicoherentUnivLE.{u, w, u, d} B E h S hS 𝒳 =
      toDerivedCategoryQuasicoherent B E h S hS 𝒳 :=
  rfl

end Agreement

section DirectImage

variable {B S hS} {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)

/-- The direct image on fppf modules along a 1-morphism `f` of algebraic stacks, at module universe
`u + 1`, with the source of `f` presented strictly by
`CategoryTheory.CatFiberedInGroupoids.homFunctor`: its structure functor is
`homFunctor f.hom ⋙ 𝒴.val.val.p`. -/
abbrev fppfModuleSheafPushforwardOfHom :
    SheafOfModules.{u + 1} (ringStructureSheafCore B S hS
        (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
        (isFiberedInGroupoids_homFunctor_comp B S hS f.hom)
        (B.baseTopology .fppf) (B.baseTopology_le_topology .fppf)) ⥤
      SheafOfModules.{u + 1} (ringStructureSheafCore B S hS
        𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
        (B.baseTopology .fppf) (B.baseTopology_le_topology .fppf)) :=
  moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS
    (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p) 𝒴.val.val.p
    (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) 𝒴.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor f.hom) rfl (B.baseTopology .fppf)
    (B.baseTopology_le_topology .fppf)

variable
  [HasDerivedCategory.{u + 2} (SheafOfModules.{u + 1} (ringStructureSheafCore B S hS
    (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
    (isFiberedInGroupoids_homFunctor_comp B S hS f.hom)
    (B.baseTopology .fppf) (B.baseTopology_le_topology .fppf)))]
  [HasDerivedCategory.{u + 2} (SheafOfModules.{u + 1} (ringStructureSheafCore B S hS
    𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
    (B.baseTopology .fppf) (B.baseTopology_le_topology .fppf)))]

/-- The total derived direct image on bounded-below derived categories of fppf modules,

`Rf_* : D⁺(𝒪_𝒳) ⥤ D⁺(𝒪_𝒴)`,

along a 1-morphism of algebraic stacks, at module universe `u + 1`: the total right derived functor
of `AlgebraicGeometry.Stack.fppfModuleSheafPushforwardOfHom`. -/
abbrev fppfDerivedPushforwardPlus :
    DerivedCategory.Plus (SheafOfModules.{u + 1} (ringStructureSheafCore B S hS
        (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
        (isFiberedInGroupoids_homFunctor_comp B S hS f.hom)
        (B.baseTopology .fppf) (B.baseTopology_le_topology .fppf))) ⥤
      DerivedCategory.Plus (SheafOfModules.{u + 1} (ringStructureSheafCore B S hS
        𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
        (B.baseTopology .fppf) (B.baseTopology_le_topology .fppf))) :=
  letI := enoughInjectives_moduleSheaves.{u, u + 1, u, u + 1} B S hS _
    (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) (B.baseTopology .fppf)
    (B.baseTopology_le_topology .fppf)
  (fppfModuleSheafPushforwardOfHom f).rightDerivedFunctorPlus

variable (i : ℕ)

/-- The assertion that for every fppf module `ℱ` on the source of a 1-morphism `f : 𝒳 ⟶ 𝒴` of
algebraic stacks which lies in `LQCoh^fbc(𝒪_𝒳)`, the higher direct image `Rⁱf_*ℱ` lies in
`LQCoh^fbc(𝒪_𝒴)`, both read on the fppf site at module universe `u + 1`. -/
abbrev IsLocallyQuasicoherentWithFlatBaseChangeFppfHigherDirectImage : Prop :=
  letI := hasSheafify_fppfAssociatedTopology_of_category_succ B S hS
    (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
  letI := wEqualsLocallyBijective_fppfAssociatedTopology_of_category_succ B S hS
    (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
  letI := hasSheafify_fppfAssociatedTopology_of_category_succ B S hS 𝒴.val.val.p
  letI := wEqualsLocallyBijective_fppfAssociatedTopology_of_category_succ B S hS 𝒴.val.val.p
  ∀ ℱ : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS
      (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
      (isFiberedInGroupoids_homFunctor_comp B S hS f.hom)
      (B.baseTopology .fppf) (B.baseTopology_le_topology .fppf)),
    IsLocallyQuasicoherent B E h S hS
        (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
        (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) ℱ.val →
      HasFlatBaseChangePropertyUnivLE B E h S hS
          (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p)
          (isFiberedInGroupoids_homFunctor_comp B S hS f.hom)
          (etaleTopology B) (etaleTopology_le_topology B) ℱ.val →
        locallyQuasicoherentFlatBaseChangeFppfModulesUnivLE.{u, w, u + 1} B E h S hS 𝒴
          ((moduleSheafHigherDirectImage.{u, u + 1, u, u + 1, u} B S hS
            (CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p) 𝒴.val.val.p
            (isFiberedInGroupoids_homFunctor_comp B S hS f.hom) 𝒴.val.isFiberedInGroupoids
            (CatFiberedInGroupoids.homFunctor f.hom) rfl
            (B.baseTopology .fppf) (B.baseTopology_le_topology .fppf) i).obj ℱ)

end DirectImage

end AlgebraicGeometry.Stack

end
