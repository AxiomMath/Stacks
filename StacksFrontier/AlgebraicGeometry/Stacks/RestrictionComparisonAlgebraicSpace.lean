module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartCorrespondenceRingUniverse
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionToAlgebraicSpace
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.OneMorphismContinuity
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.EtaleLocalLift

/-!
# The comparison map of a 2-commutative triangle of categories representable by spaces

Let `S` be a scheme in a big fppf site and let

```
𝒰 --a--> 𝒱
  \      |
   f     g
    \    |
     v   v
       𝒳
```

be a 2-commutative triangle of 1-morphisms of categories fibred in groupoids over
`(Sch/S)_{fppf}`, with 2-morphism `φ : a ⋙ g ≅ f`, and assume that `𝒰` and `𝒱` are
representable by algebraic spaces `U` and `V`. Let `ℱ` be a sheaf on `𝒳_étale`, and write
`a_small : Sh(U_étale) ⟶ Sh(V_étale)` for the morphism of small étale topoi of the morphism
`U ⟶ V` of algebraic spaces corresponding to `a`. The *comparison map* is a map

```
c_φ : a_small⁻¹(g⁻¹ℱ|_{V_étale}) ⟶ f⁻¹ℱ|_{U_étale}
```

of sheaves on the small étale site of `U`. Here `g⁻¹` and `f⁻¹` are restriction along the
1-morphisms, `(f⁻¹ℱ)(x) = ℱ(f x)`, and `·|_{U_étale}` is restriction along the functor
`u_U : U_étale ⥤ 𝒰`. It is the adjoint, under `a_small⁻¹ ⊣ a_{small,*}`, of the map
`g⁻¹ℱ|_{V_étale} ⟶ a_{small,*}(f⁻¹ℱ|_{U_étale})` which on sections over a commutative diagram of
étale scheme charts

```
W ---d.g---> V'
|            |
v            v
U ---a---->  V
```

is the map `ℱ(g(u_V V')) ⟶ ℱ(f(u_U W))` induced by the morphism `a(u_U W) ⟶ u_V V'` of `𝒱`
that the square provides, followed by the 2-morphism `φ`.

For an `𝒪_𝒳`-module `ℱ` the same construction gives the comparison map

```
c_φ : a_small^*(g^*ℱ|_{V_étale}) ⟶ f^*ℱ|_{U_étale}
```

of `𝒪_U`-modules, with `a_small^*` the inverse image of modules, provided the components of `φ`
and of the identification `ha` of `a` with postcomposition by `U ⟶ V` lie over identities.

## Main definitions

* `AlgebraicGeometry.Space.etaleRestrictedInverseImage` is `f⁻¹ℱ|_{U_étale}`: the restriction to
  the small étale site of `U` of the inverse image of `ℱ` along a 1-morphism out of `𝒰`.
* `AlgebraicGeometry.Space.comparisonPushforwardHom` is the map
  `g⁻¹ℱ|_{V_étale} ⟶ a_{small,*}(f⁻¹ℱ|_{U_étale})` whose adjoint is the comparison map.
* `AlgebraicGeometry.Space.comparisonAlgebraicSpaces`: the comparison map `c_φ`.
* `AlgebraicGeometry.Space.etaleChartStructureHom` is the identification `𝒪_U = (u_U ∘ f)^*𝒪_𝒳`
  of structure sheaves, and
  `AlgebraicGeometry.Space.etaleRestrictedModuleInverseImage` is `f^*ℱ|_{U_étale}`: the same
  restriction, for an `𝒪_𝒳`-module, as an `𝒪_U`-module.
* `AlgebraicGeometry.Space.moduleComparisonPushforwardHom` is the map
  `g^*ℱ|_{V_étale} ⟶ a_{small,*}(f^*ℱ|_{U_étale})` of `𝒪_V`-modules whose adjoint is the
  module-level comparison map.
* `AlgebraicGeometry.Space.comparisonAlgebraicSpacesModules`: the comparison map `c_φ` on
  modules.

## Main results

* `AlgebraicGeometry.Space.comparisonFMap_app` and
  `AlgebraicGeometry.Space.moduleComparisonFMap_app`: on sections over a commutative diagram of
  étale scheme charts over `U ⟶ V`, the comparison is restriction of sections of `ℱ` along the
  morphism `AlgebraicGeometry.Space.comparisonMorphism` of `𝒳`.
* `AlgebraicGeometry.Space.isHomLift_comparisonMorphism`: that morphism of `𝒳` lies over the
  vertical morphism of schemes of the chart diagram, and
  `AlgebraicGeometry.Space.structureSheaf_map_comparisonMorphism`: pullback of regular functions
  along it is pullback along that vertical morphism.

## References

* [Stacks Project, Tag 076Q](https://stacks.math.columbia.edu/tag/076Q)
* [Stacks Project, Tag 076R](https://stacks.math.columbia.edu/tag/076R)
* [Stacks Project, Tag 073M](https://stacks.math.columbia.edu/tag/073M)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 06TV](https://stacks.math.columbia.edu/tag/06TV)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03G4](https://stacks.math.columbia.edu/tag/03G4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u v w v' w' v'' w'' m

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U V : AlgebraicSpaces B S hS}
  {𝒰 : Type v} [Category.{w} 𝒰] {𝒱 : Type v'} [Category.{w'} 𝒱]
  {𝒳 : Type v''} [Category.{w''} 𝒳]
  (p : 𝒰 ⥤ BigFppfOver B S hS) (q : 𝒱 ⥤ BigFppfOver B S hS)
  (r : 𝒳 ⥤ BigFppfOver B S hS)

/-- Two factorizations of one morphism give the same restriction of sections. -/
private theorem map_op_comp_apply_congr {C : Type*} [Category C] (K : Cᵒᵖ ⥤ Type u)
    {X Y Z Y' : C} (x : X ⟶ Y) (y : Y ⟶ Z) (x' : X ⟶ Y') (y' : Y' ⟶ Z)
    (h : x ≫ y = x' ≫ y') (t : K.obj (op Z)) :
    K.map x.op (K.map y.op t) = K.map x'.op (K.map y'.op t) := by
  rw [← K.map_comp_apply, ← K.map_comp_apply, ← op_comp, ← op_comp, h]

/-- Two factorizations of one morphism give the same restriction of sections of a presheaf of
modules. -/
private theorem module_map_op_comp_apply_congr {C : Type*} [Category C]
    {R : Cᵒᵖ ⥤ RingCat.{u}} (K : PresheafOfModules.{m} R)
    {X Y Z Y' : C} (x : X ⟶ Y) (y : Y ⟶ Z) (x' : X ⟶ Y') (y' : Y' ⟶ Z)
    (h : x ≫ y = x' ≫ y') (t : K.obj (op Z)) :
    K.map x.op (K.map y.op t) = K.map x'.op (K.map y'.op t) :=
  map_op_comp_apply_congr (K.presheaf ⋙ forget _) x y x' y' h t

/-- Two successive restrictions of a presheaf of rings along opposite morphisms are the
restriction along their composite. -/
private theorem ring_map_op_comp_apply {C : Type*} [Category C] (K : Cᵒᵖ ⥤ RingCat.{u})
    {X Y Z : C} (x : X ⟶ Y) (y : Y ⟶ Z) (t : K.obj (op Z)) :
    K.map x.op (K.map y.op t) = K.map (x ≫ y).op t :=
  (K.map_comp_apply y.op x.op t).symm

/-- Equal scalars act equally. -/
private theorem smul_congr_left {R : RingCat.{u}} {M : ModuleCat.{m} R} {x y : R}
    (h : x = y) (m : M) : x • m = y • m := by rw [h]

/-- The components of the isomorphism induced by an equality of functors `F = G` into `𝒳` lie
over identities. -/
theorem isHomLift_eqToIso_app {𝒜 : Type*} [Category 𝒜] {F G : 𝒜 ⥤ 𝒳} (h : F = G) (X : 𝒜) :
    r.IsHomLift (𝟙 (r.obj (F.obj X))) ((eqToIso h).hom.app X) ∧
      r.IsHomLift (𝟙 (r.obj (G.obj X))) ((eqToIso h).inv.app X) := by
  subst h
  exact ⟨IsHomLift.id rfl, IsHomLift.id rfl⟩

/-! ### The restriction of an inverse image to the small étale site of the representing space -/

/-- The restriction `f⁻¹ℱ|_{U_étale}` to the small étale site of the algebraic space `U`
representing `𝒰` of the inverse image, along a 1-morphism `f : 𝒰 ⥤ 𝒳` over the site, of a sheaf
on the inherited étale site of `𝒳`: restriction along `f`, followed by restriction along the
functor `u_U : U_étale ⥤ 𝒰`. -/
noncomputable abbrev etaleRestrictedInverseImage (hp : p.IsFiberedInGroupoids)
    (eU : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (U.1 ⋙ typeToCat)).p)
    (f : 𝒰 ⥤ 𝒳) (hf : p.IsFibredOneMorphism r f)
    (ℱ : Sheaf (BigFppfOver.associatedTopology B S hS r .etale) (Type u)) :
    Sheaf (SmallEtale.topology B S hS U.1) (Type u) :=
  letI := hp.isFibered
  letI := hf.isContinuous_inheritedTopology (BigFppfOver.baseOverTopology B S hS .etale)
  (restrictionSheafFunctor B S hS U.1 p hp eU).obj
    ((f.sheafPushforwardContinuous (Type u)
      (BigFppfOver.associatedTopology B S hS p .etale)
      (BigFppfOver.associatedTopology B S hS r .etale)).obj ℱ)

/-- The sections of `f⁻¹ℱ|_{U_étale}` over an étale chart `W` of `U` are the sections of `ℱ` over
the object `f(u_U W)` of `𝒳`. -/
theorem etaleRestrictedInverseImage_obj_obj (hp : p.IsFiberedInGroupoids)
    (eU : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (U.1 ⋙ typeToCat)).p)
    (f : 𝒰 ⥤ 𝒳) (hf : p.IsFibredOneMorphism r f)
    (ℱ : Sheaf (BigFppfOver.associatedTopology B S hS r .etale) (Type u))
    (W : SmallEtale B S hS U.1) :
    (etaleRestrictedInverseImage B S hS p r hp eU f hf ℱ).obj.obj (op W) =
      ℱ.obj.obj (op (f.obj ((restrictionFunctor B S hS U.1 p eU).obj W))) :=
  rfl

/-! ### The restriction of an inverse image of modules to the small étale site -/

/-- The `𝒪_𝒳`-modules on the inherited étale site of a category `𝒳` fibred in groupoids over
`(Sch/S)_{fppf}`: sheaves of modules, with sections in universe `m`, over the structure sheaf of
`𝒳` regarded as a sheaf of rings. -/
noncomputable abbrev inheritedEtaleModules (hr : r.IsFiberedInGroupoids) :=
  SheafOfModules.{m} (FibredSite.ringStructureSheafCore B S hS r hr .etale)

/-- The functor `U_étale ⥤ 𝒳` along which a sheaf or a module on the inherited étale site of
`𝒳` is restricted to the small étale site of the algebraic space `U` representing `𝒰`: the
functor `u_U : U_étale ⥤ 𝒰` followed by the 1-morphism `f : 𝒰 ⥤ 𝒳`. -/
noncomputable abbrev etaleChartToFibred
    (eU : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (U.1 ⋙ typeToCat)).p)
    (f : 𝒰 ⥤ 𝒳) : SmallEtale B S hS U.1 ⥤ 𝒳 :=
  restrictionFunctor B S hS U.1 p eU ⋙ f

/-- The composite `U_étale ⥤ 𝒳 ⥤ (Sch/S)_{fppf}` is the underlying-object functor of the small
étale site of `U`. -/
theorem etaleChartToFibred_comp
    (eU : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (U.1 ⋙ typeToCat)).p)
    (f : 𝒰 ⥤ 𝒳) (hf : p.IsFibredOneMorphism r f) :
    etaleChartToFibred B S hS p eU f ⋙ r = SmallEtale.toOver B S hS U.1 := by
  change (restrictionFunctor B S hS U.1 p eU ⋙ f) ⋙ r = _
  rw [Functor.assoc, hf.comp_eq, restrictionFunctor_comp]

/-- The functor `U_étale ⥤ 𝒳` of `AlgebraicGeometry.Space.etaleChartToFibred` is continuous for
the étale topologies. -/
theorem etaleChartToFibred_isContinuous (hp : p.IsFiberedInGroupoids)
    (eU : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (U.1 ⋙ typeToCat)).p)
    (f : 𝒰 ⥤ 𝒳) (hf : p.IsFibredOneMorphism r f) :
    (etaleChartToFibred B S hS p eU f).IsContinuous (SmallEtale.topology B S hS U.1)
      (BigFppfOver.associatedTopology B S hS r .etale) :=
  let := restrictionFunctor_isContinuous B S hS U.1 p hp eU
  let := hp.isFibered
  let := hf.isContinuous_inheritedTopology (BigFppfOver.baseOverTopology B S hS .etale)
  Functor.isContinuous_comp (restrictionFunctor B S hS U.1 p eU) f
    (SmallEtale.topology B S hS U.1) (BigFppfOver.associatedTopology B S hS p .etale)
    (BigFppfOver.associatedTopology B S hS r .etale)

/-- The identification of the structure sheaf of the small étale site of `U` with the restriction
of the structure sheaf of `𝒳` along `u_U` followed by `f`, as a homomorphism of sheaves of rings.

Both sheaves send an étale chart `W` of `U` to the ring of global regular functions on the scheme
underlying `W`: on the left because that is the definition of `𝒪_U`, on the right because the
composite functor `U_étale ⥤ 𝒳 ⥤ (Sch/S)_{fppf}` is the underlying-object functor
(`AlgebraicGeometry.Space.etaleChartToFibred_comp`); the homomorphism is the one induced by
that equality of functors. -/
noncomputable def etaleChartStructureHom (hp : p.IsFiberedInGroupoids)
    (hr : r.IsFiberedInGroupoids)
    (eU : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (U.1 ⋙ typeToCat)).p)
    (f : 𝒰 ⥤ 𝒳) (hf : p.IsFibredOneMorphism r f) :
    letI := etaleChartToFibred_isContinuous B S hS p r hp eU f hf
    structureRingSheaf B S hS U ⟶
      ((etaleChartToFibred B S hS p eU f).sheafPushforwardContinuous RingCat.{u}
          (SmallEtale.topology B S hS U.1)
          (BigFppfOver.associatedTopology B S hS r .etale)).obj
        (FibredSite.ringStructureSheafCore B S hS r hr .etale) :=
  letI := etaleChartToFibred_isContinuous B S hS p r hp eU f hf
  ⟨Functor.whiskerRight
    (NatTrans.op (eqToHom (etaleChartToFibred_comp B S hS p r eU f hf)))
    (BigFppfOver.structureSheaf B S hS).obj⟩

/-- The homomorphism of `AlgebraicGeometry.Space.etaleChartStructureHom` is, on sections over an
étale chart `W` of `U`, pullback of regular functions along the identification of the object of
`(Sch/S)_{fppf}` underlying `f(u_U W)` with the one underlying `W`. -/
theorem etaleChartStructureHom_app (hp : p.IsFiberedInGroupoids)
    (hr : r.IsFiberedInGroupoids)
    (eU : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (U.1 ⋙ typeToCat)).p)
    (f : 𝒰 ⥤ 𝒳) (hf : p.IsFibredOneMorphism r f) (W : SmallEtale B S hS U.1) :
    (etaleChartStructureHom B S hS p r hp hr eU f hf).hom.app (op W) =
      (BigFppfOver.structureSheaf B S hS).obj.map
        (eqToHom (Functor.congr_obj (etaleChartToFibred_comp B S hS p r eU f hf) W)).op := by
  change (BigFppfOver.structureSheaf B S hS).obj.map
      ((eqToHom (etaleChartToFibred_comp B S hS p r eU f hf)).app W).op = _
  rw [eqToHom_app]

/-- The restriction `f^*ℱ|_{U_étale}` to the small étale site of the algebraic space `U`
representing `𝒰` of the inverse image, along a 1-morphism `f : 𝒰 ⥤ 𝒳` over the site, of an
`𝒪_𝒳`-module `ℱ`: the pushforward of `ℱ` along `AlgebraicGeometry.Space.etaleChartToFibred`,
with coefficient homomorphism `AlgebraicGeometry.Space.etaleChartStructureHom`. -/
noncomputable def etaleRestrictedModuleInverseImage (hp : p.IsFiberedInGroupoids)
    (hr : r.IsFiberedInGroupoids)
    (eU : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (U.1 ⋙ typeToCat)).p)
    (f : 𝒰 ⥤ 𝒳) (hf : p.IsFibredOneMorphism r f)
    (ℱ : inheritedEtaleModules B S hS r hr) : Modules.{u, m} B S hS U.1 U.2 :=
  haveI := etaleChartToFibred_isContinuous B S hS p r hp eU f hf
  (SheafOfModules.pushforward
    (etaleChartStructureHom B S hS p r hp hr eU f hf)).obj ℱ

/-- The sections of `f^*ℱ|_{U_étale}` over an étale chart `W` of `U` are the sections of `ℱ` over
the object `f(u_U W)` of `𝒳`, with `𝒪_U(W)` acting through
`AlgebraicGeometry.Space.etaleChartStructureHom`. -/
theorem etaleRestrictedModuleInverseImage_obj (hp : p.IsFiberedInGroupoids)
    (hr : r.IsFiberedInGroupoids)
    (eU : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (U.1 ⋙ typeToCat)).p)
    (f : 𝒰 ⥤ 𝒳) (hf : p.IsFibredOneMorphism r f)
    (ℱ : inheritedEtaleModules B S hS r hr) (W : SmallEtale B S hS U.1) :
    (etaleRestrictedModuleInverseImage B S hS p r hp hr eU f hf ℱ).val.obj (op W) =
      (ModuleCat.restrictScalars
          ((etaleChartStructureHom B S hS p r hp hr eU f hf).hom.app (op W)).hom).obj
        (ℱ.val.obj (op (f.obj ((restrictionFunctor B S hS U.1 p eU).obj W)))) :=
  rfl

/-! ### The comparison map of a 2-commutative triangle -/

section Triangle

variable (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (eU : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (U.1 ⋙ typeToCat)).p)
  (eV : StacksRepresentableCFG.EquivalenceOver q
    (presheafOfCategories (V.1 ⋙ typeToCat)).p)
  (a : 𝒰 ⥤ 𝒱) (f : 𝒰 ⥤ 𝒳) (g : 𝒱 ⥤ 𝒳)
  (hf : p.IsFibredOneMorphism r f) (hg : q.IsFibredOneMorphism r g)
  (φ : a ⋙ g ≅ f) (aSpace : U ⟶ V)
  (ha : schemeChartFunctor B S hS U.1 p eU ⋙ a ≅
    CostructuredArrow.map aSpace.hom ⋙ schemeChartFunctor B S hS V.1 q eV)

/-- For every morphism `aSpace : U ⟶ V` of algebraic spaces there is a 1-morphism `𝒰 ⥤ 𝒱`
which is, through the presentations `AlgebraicGeometry.Space.schemeChartFunctor`,
postcomposition with `aSpace`. -/
theorem exists_comparisonChartFunctorIso (aSpace : U ⟶ V)
    (eU : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (U.1 ⋙ typeToCat)).p)
    (eV : StacksRepresentableCFG.EquivalenceOver q
      (presheafOfCategories (V.1 ⋙ typeToCat)).p) :
    ∃ a : 𝒰 ⥤ 𝒱, Nonempty (schemeChartFunctor B S hS U.1 p eU ⋙ a ≅
      CostructuredArrow.map aSpace.hom ⋙ schemeChartFunctor B S hS V.1 q eV) :=
  ⟨(schemeChartFunctor B S hS U.1 p eU).inv ⋙
      CostructuredArrow.map aSpace.hom ⋙ schemeChartFunctor B S hS V.1 q eV,
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (schemeChartFunctor B S hS U.1 p eU).asEquivalence.unitIso.symm _⟩⟩

/-- The morphism `a(u_U W) ⟶ u_V V'` of `𝒱` attached to a commutative diagram of étale scheme
charts over `aSpace : U ⟶ V`: the identification `ha` of `a(u_U W)` with the chart
`W ⟶ U ⟶ V` of `V`, followed by the vertical morphism `W ⟶ V'` as a morphism of charts of `V`. -/
noncomputable def comparisonChartHom
    (d : ChartDiagram B S hS U.1 V.1 aSpace.hom) :
    a.obj ((restrictionFunctor B S hS U.1 p eU).obj d.U) ⟶
      (restrictionFunctor B S hS V.1 q eV).obj d.V :=
  ha.hom.app d.U.1 ≫
    (schemeChartFunctor B S hS V.1 q eV).map (CostructuredArrow.homMk d.g d.comm.symm)

/-- The morphisms of `AlgebraicGeometry.Space.comparisonChartHom` are compatible with
simultaneous étale restriction of the two charts of a diagram. -/
theorem comparisonChartHom_naturality
    (d d' : ChartDiagram B S hS U.1 V.1 aSpace.hom) (i : d'.U ⟶ d.U) (j : d'.V ⟶ d.V)
    (hij : (SmallEtale.toOver B S hS U.1).map i ≫ d.g =
      d'.g ≫ (SmallEtale.toOver B S hS V.1).map j) :
    comparisonChartHom B S hS p q eU eV a aSpace ha d' ≫
        (restrictionFunctor B S hS V.1 q eV).map j =
      a.map ((restrictionFunctor B S hS U.1 p eU).map i) ≫
        comparisonChartHom B S hS p q eU eV a aSpace ha d := by
  have hc : (CostructuredArrow.homMk d'.g d'.comm.symm :
        (CostructuredArrow.map aSpace.hom).obj d'.U.1 ⟶ d'.V.1) ≫
          (SmallEtale.inclusion B S hS V.1).map j =
      (CostructuredArrow.map aSpace.hom).map ((SmallEtale.inclusion B S hS U.1).map i) ≫
        CostructuredArrow.homMk d.g d.comm.symm :=
    CostructuredArrow.hom_ext _ _ hij.symm
  have hnatha : a.map ((schemeChartFunctor B S hS U.1 p eU).map
          ((SmallEtale.inclusion B S hS U.1).map i)) ≫ ha.hom.app d.U.1 =
      ha.hom.app d'.U.1 ≫ (schemeChartFunctor B S hS V.1 q eV).map
        ((CostructuredArrow.map aSpace.hom).map ((SmallEtale.inclusion B S hS U.1).map i)) :=
    ha.hom.naturality _
  change (ha.hom.app d'.U.1 ≫ _) ≫ (schemeChartFunctor B S hS V.1 q eV).map
      ((SmallEtale.inclusion B S hS V.1).map j) =
    a.map ((schemeChartFunctor B S hS U.1 p eU).map
      ((SmallEtale.inclusion B S hS U.1).map i)) ≫ ha.hom.app d.U.1 ≫ _
  rw [Category.assoc, ← Functor.map_comp, hc, Functor.map_comp, ← Category.assoc,
    ← hnatha, Category.assoc]

/-- The map on sections over commutative diagrams of étale scheme charts defining the comparison
map: on the diagram with charts `W` of `U` and `V'` of `V` and vertical morphism
`d.g : W ⟶ V'`, it is the map `ℱ(g(u_V V')) ⟶ ℱ(f(u_U W))` induced by the morphism
`a(u_U W) ⟶ u_V V'` of `AlgebraicGeometry.Space.comparisonChartHom` and the 2-morphism `φ`. -/
noncomputable def comparisonFMap
    (ℱ : Sheaf (BigFppfOver.associatedTopology B S hS r .etale) (Type u)) :
    FMap B S hS U.1 V.1 aSpace.hom
      (etaleRestrictedInverseImage B S hS p r hp eU f hf ℱ).obj
      (etaleRestrictedInverseImage B S hS q r hq eV g hg ℱ).obj where
  app d := ℱ.obj.map (φ.inv.app ((restrictionFunctor B S hS U.1 p eU).obj d.U) ≫
    g.map (comparisonChartHom B S hS p q eU eV a aSpace ha d)).op
  naturality d d' i j hij s := by
    have hnat : f.map ((restrictionFunctor B S hS U.1 p eU).map i) ≫
          φ.inv.app ((restrictionFunctor B S hS U.1 p eU).obj d.U) =
        φ.inv.app ((restrictionFunctor B S hS U.1 p eU).obj d'.U) ≫
          g.map (a.map ((restrictionFunctor B S hS U.1 p eU).map i)) :=
      φ.inv.naturality _
    have hch := comparisonChartHom_naturality B S hS p q eU eV a aSpace ha d d' i j hij
    have key : (φ.inv.app ((restrictionFunctor B S hS U.1 p eU).obj d'.U) ≫
          g.map (comparisonChartHom B S hS p q eU eV a aSpace ha d')) ≫
            g.map ((restrictionFunctor B S hS V.1 q eV).map j) =
        f.map ((restrictionFunctor B S hS U.1 p eU).map i) ≫
          φ.inv.app ((restrictionFunctor B S hS U.1 p eU).obj d.U) ≫
            g.map (comparisonChartHom B S hS p q eU eV a aSpace ha d) := by
      rw [Category.assoc, ← Functor.map_comp, hch, Functor.map_comp, ← Category.assoc,
        ← hnat, Category.assoc]
    exact map_op_comp_apply_congr ℱ.obj _ _ _ _ key s

/-- The map of sections of `AlgebraicGeometry.Space.comparisonFMap` at a diagram of charts. -/
theorem comparisonFMap_app
    (ℱ : Sheaf (BigFppfOver.associatedTopology B S hS r .etale) (Type u))
    (d : ChartDiagram B S hS U.1 V.1 aSpace.hom)
    (s : (etaleRestrictedInverseImage B S hS q r hq eV g hg ℱ).obj.obj (op d.V)) :
    (comparisonFMap B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha ℱ).app d s =
      ℱ.obj.map (φ.inv.app ((restrictionFunctor B S hS U.1 p eU).obj d.U) ≫
        g.map (comparisonChartHom B S hS p q eU eV a aSpace ha d)).op s :=
  rfl

/-- The map `g⁻¹ℱ|_{V_étale} ⟶ a_{small,*}(f⁻¹ℱ|_{U_étale})` attached by the chart
correspondence `AlgebraicGeometry.Space.fMapEquivPushforwardHom_ringUniverse` to the maps of
sections `AlgebraicGeometry.Space.comparisonFMap`. -/
noncomputable def comparisonPushforwardHom
    (ℱ : Sheaf (BigFppfOver.associatedTopology B S hS r .etale) (Type u)) :
    etaleRestrictedInverseImage B S hS q r hq eV g hg ℱ ⟶
      (smallToposMorphismTypeU B S hS aSpace).pushforward.obj
        (etaleRestrictedInverseImage B S hS p r hp eU f hf ℱ) :=
  fMapEquivPushforwardHom_ringUniverse B S hS aSpace
    (etaleRestrictedInverseImage B S hS p r hp eU f hf ℱ)
    (etaleRestrictedInverseImage B S hS q r hq eV g hg ℱ)
    (comparisonFMap B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha ℱ)

/-- The comparison map

```
c_φ : a_small⁻¹(g⁻¹ℱ|_{V_étale}) ⟶ f⁻¹ℱ|_{U_étale}
```

of a 2-commutative triangle `φ : a ⋙ g ≅ f` of 1-morphisms of categories fibred in groupoids
over `(Sch/S)_{fppf}` whose two source categories `𝒰`, `𝒱` are representable by algebraic spaces
`U`, `V`, for a sheaf `ℱ` on the inherited étale site of `𝒳`.

Here `a_small` is the morphism of small étale topoi attached to the morphism `aSpace : U ⟶ V`
of algebraic spaces corresponding to `a`, and `c_φ` is the adjoint, under
`a_small⁻¹ ⊣ a_{small,*}`, of `AlgebraicGeometry.Space.comparisonPushforwardHom`. -/
@[stacks 076Q "the comparison map of a 2-commutative triangle, on sheaves of sets"]
noncomputable def comparisonAlgebraicSpaces
    (ℱ : Sheaf (BigFppfOver.associatedTopology B S hS r .etale) (Type u)) :
    (smallToposMorphismTypeU B S hS aSpace).inverseImage.obj
        (etaleRestrictedInverseImage B S hS q r hq eV g hg ℱ) ⟶
      etaleRestrictedInverseImage B S hS p r hp eU f hf ℱ :=
  ((smallToposMorphismTypeU B S hS aSpace).adj.homEquiv _ _).symm
    (comparisonPushforwardHom B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha ℱ)

/-- The comparison map `AlgebraicGeometry.Space.comparisonAlgebraicSpaces` is adjoint to
`AlgebraicGeometry.Space.comparisonPushforwardHom`: composing it, pushed forward, with the unit
of `a_small⁻¹ ⊣ a_{small,*}` gives that map back. -/
theorem comparisonAlgebraicSpaces_adjoint
    (ℱ : Sheaf (BigFppfOver.associatedTopology B S hS r .etale) (Type u)) :
    (smallToposMorphismTypeU B S hS aSpace).adj.homEquiv _ _
        (comparisonAlgebraicSpaces B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha ℱ) =
      comparisonPushforwardHom B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha ℱ :=
  Equiv.apply_symm_apply _ _

/-! ### The comparison map of a 2-commutative triangle, on modules -/

/-- The morphism `f(u_U W) ⟶ g(u_V V')` of `𝒳` attached to a diagram of étale scheme charts:
the 2-morphism `φ` followed by the image under `g` of the morphism of charts of `V` that the
commutative square provides. -/
noncomputable def comparisonMorphism (d : ChartDiagram B S hS U.1 V.1 aSpace.hom) :
    f.obj ((restrictionFunctor B S hS U.1 p eU).obj d.U) ⟶
      g.obj ((restrictionFunctor B S hS V.1 q eV).obj d.V) :=
  φ.inv.app ((restrictionFunctor B S hS U.1 p eU).obj d.U) ≫
    g.map (comparisonChartHom B S hS p q eU eV a aSpace ha d)

/-- On sections over a diagram of charts, `AlgebraicGeometry.Space.comparisonFMap` is
restriction along `AlgebraicGeometry.Space.comparisonMorphism`. -/
theorem comparisonFMap_app_comparisonMorphism
    (ℱ : Sheaf (BigFppfOver.associatedTopology B S hS r .etale) (Type u))
    (d : ChartDiagram B S hS U.1 V.1 aSpace.hom)
    (s : (etaleRestrictedInverseImage B S hS q r hq eV g hg ℱ).obj.obj (op d.V)) :
    (comparisonFMap B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha ℱ).app d s =
      ℱ.obj.map (comparisonMorphism B S hS p q eU eV a f g φ aSpace ha d).op s :=
  rfl

/-- The morphism of scheme charts of `V`, from the chart `W ⟶ U ⟶ V` to the chart `V'`, which
the commutative square of a diagram of étale scheme charts provides. -/
def chartDiagramChartHom (d : ChartDiagram B S hS U.1 V.1 aSpace.hom) :
    (CostructuredArrow.map aSpace.hom).obj d.U.1 ⟶ d.V.1 :=
  CostructuredArrow.homMk d.g d.comm.symm

/-- The morphism of scheme charts of `AlgebraicGeometry.Space.chartDiagramChartHom` lies over
the vertical morphism of schemes of the diagram. -/
theorem proj_map_chartDiagramChartHom (d : ChartDiagram B S hS U.1 V.1 aSpace.hom) :
    (CostructuredArrow.proj yoneda V.1).map (chartDiagramChartHom B S hS aSpace d) = d.g :=
  rfl

variable (hr : r.IsFiberedInGroupoids)
  (hφ : ∀ X : 𝒰, r.IsHomLift (𝟙 (r.obj (f.obj X))) (φ.inv.app X))
  (hab : ∀ Z : CostructuredArrow yoneda U.1,
    q.IsHomLift (𝟙 (q.obj (a.obj ((schemeChartFunctor B S hS U.1 p eU).obj Z))))
      (ha.hom.app Z))

include hg hr hφ hab

omit hr in
/-- The morphism `AlgebraicGeometry.Space.comparisonMorphism` lies over the vertical morphism
`d.g` of schemes of its chart diagram. -/
theorem isHomLift_comparisonMorphism (d : ChartDiagram B S hS U.1 V.1 aSpace.hom) :
    r.IsHomLift d.g (comparisonMorphism B S hS p q eU eV a f g φ aSpace ha d) := by
  have : (CostructuredArrow.proj yoneda V.1).IsHomLift d.g
      (chartDiagramChartHom B S hS aSpace d) :=
    IsHomLift.map (CostructuredArrow.proj yoneda V.1) (chartDiagramChartHom B S hS aSpace d)
  have : q.IsHomLift d.g ((schemeChartFunctor B S hS V.1 q eV).map
      (chartDiagramChartHom B S hS aSpace d)) :=
    Functor.isHomLift_map_of_comp_eq (schemeChartFunctor_comp B S hS V.1 q eV) d.g _
  have := hab d.U.1
  have := hφ ((restrictionFunctor B S hS U.1 p eU).obj d.U)
  have : q.IsHomLift d.g (comparisonChartHom B S hS p q eU eV a aSpace ha d) :=
    IsHomLift.comp_lift_id_left' q
      (q.obj (a.obj ((schemeChartFunctor B S hS U.1 p eU).obj d.U.1)))
      (ha.hom.app d.U.1) d.g
      ((schemeChartFunctor B S hS V.1 q eV).map (chartDiagramChartHom B S hS aSpace d))
  have := hg.map_isHomLift d.g (comparisonChartHom B S hS p q eU eV a aSpace ha d)
  exact IsHomLift.comp_lift_id_left' r
    (r.obj (f.obj ((restrictionFunctor B S hS U.1 p eU).obj d.U)))
    (φ.inv.app ((restrictionFunctor B S hS U.1 p eU).obj d.U)) d.g
    (g.map (comparisonChartHom B S hS p q eU eV a aSpace ha d))

/-- Pullback of regular functions along `AlgebraicGeometry.Space.comparisonMorphism` is
pullback along the vertical morphism `d.g` of the chart diagram: the two structure-sheaf
identifications `AlgebraicGeometry.Space.etaleChartStructureHom`, for `U` and for `V`, and
pullback along the comparison morphism and along `d.g`, form a commutative square. -/
theorem structureSheaf_map_comparisonMorphism
    (d : ChartDiagram B S hS U.1 V.1 aSpace.hom)
    (ρ : ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS V.1 V.2).O)).obj.obj (op d.V)) :
    (FibredSite.ringStructureSheafCore B S hS r hr .etale).obj.map
        (comparisonMorphism B S hS p q eU eV a f g φ aSpace ha d).op
        ((etaleChartStructureHom B S hS q r hq hr eV g hg).hom.app (op d.V) ρ) =
      (etaleChartStructureHom B S hS p r hp hr eU f hf).hom.app (op d.U)
        (chartDiagramPullback B S hS aSpace d ρ) := by
  have := isHomLift_comparisonMorphism B S hS p q r eU eV a f g hg φ aSpace ha hφ hab d
  have key := (IsHomLift.commSq r d.g
    (comparisonMorphism B S hS p q eU eV a f g φ aSpace ha d)).w
  rw [etaleChartStructureHom_app, etaleChartStructureHom_app]
  refine Eq.trans (ring_map_op_comp_apply (BigFppfOver.structureSheaf B S hS).obj
    (r.map (comparisonMorphism B S hS p q eU eV a f g φ aSpace ha d))
    (eqToHom (Functor.congr_obj (etaleChartToFibred_comp B S hS q r eV g hg) d.V)) ρ) ?_
  refine Eq.trans ?_ (ring_map_op_comp_apply (BigFppfOver.structureSheaf B S hS).obj
    (eqToHom (Functor.congr_obj (etaleChartToFibred_comp B S hS p r eU f hf) d.U))
    d.g ρ).symm
  exact congrArg (fun m : (etaleChartToFibred B S hS p eU f ⋙ r).obj d.U ⟶
      (SmallEtale.toOver B S hS V.1).obj d.V =>
    (BigFppfOver.structureSheaf B S hS).obj.map m.op ρ) key

/-- The module analogue of `AlgebraicGeometry.Space.comparisonFMap`: on a diagram of étale
scheme charts, restriction of sections of `ℱ` along `AlgebraicGeometry.Space.comparisonMorphism`,
an additive map, semilinear over pullback of regular functions along `d.g`. -/
noncomputable def moduleComparisonFMap (ℱ : inheritedEtaleModules B S hS r hr) :
    ModuleFMap B S hS aSpace
      (etaleRestrictedModuleInverseImage B S hS p r hp hr eU f hf ℱ)
      (etaleRestrictedModuleInverseImage B S hS q r hq hr eV g hg ℱ) where
  app d s := ℱ.val.map (comparisonMorphism B S hS p q eU eV a f g φ aSpace ha d).op s
  naturality d d' i j hij s := by
    have hnat : f.map ((restrictionFunctor B S hS U.1 p eU).map i) ≫
          φ.inv.app ((restrictionFunctor B S hS U.1 p eU).obj d.U) =
        φ.inv.app ((restrictionFunctor B S hS U.1 p eU).obj d'.U) ≫
          g.map (a.map ((restrictionFunctor B S hS U.1 p eU).map i)) :=
      φ.inv.naturality _
    have hch := comparisonChartHom_naturality B S hS p q eU eV a aSpace ha d d' i j hij
    have key : comparisonMorphism B S hS p q eU eV a f g φ aSpace ha d' ≫
          g.map ((restrictionFunctor B S hS V.1 q eV).map j) =
        f.map ((restrictionFunctor B S hS U.1 p eU).map i) ≫
          comparisonMorphism B S hS p q eU eV a f g φ aSpace ha d := by
      change (φ.inv.app _ ≫ g.map (comparisonChartHom B S hS p q eU eV a aSpace ha d')) ≫ _ =
        _ ≫ φ.inv.app _ ≫ g.map (comparisonChartHom B S hS p q eU eV a aSpace ha d)
      rw [Category.assoc, ← Functor.map_comp, hch, Functor.map_comp, ← Category.assoc,
        ← hnat, Category.assoc]
    exact module_map_op_comp_apply_congr ℱ.val _ _ _ _ key s
  map_add d s t :=
    map_add (ℱ.val.map
      (comparisonMorphism B S hS p q eU eV a f g φ aSpace ha d).op).hom s t
  map_smul d ρ s := by
    refine Eq.trans (ℱ.val.map_smul
      (comparisonMorphism B S hS p q eU eV a f g φ aSpace ha d).op
      ((etaleChartStructureHom B S hS q r hq hr eV g hg).hom.app (op d.V) ρ) s) ?_
    exact smul_congr_left (structureSheaf_map_comparisonMorphism B S hS p q r hp hq eU eV a f g
      hf hg φ aSpace ha hr hφ hab d ρ) _

/-- The map of sections of `AlgebraicGeometry.Space.moduleComparisonFMap` at a diagram of
charts: restriction of sections of `ℱ` along `AlgebraicGeometry.Space.comparisonMorphism`. -/
theorem moduleComparisonFMap_app (ℱ : inheritedEtaleModules B S hS r hr)
    (d : ChartDiagram B S hS U.1 V.1 aSpace.hom)
    (s : (etaleRestrictedModuleInverseImage B S hS q r hq hr eV g hg ℱ).val.obj (op d.V)) :
    (moduleComparisonFMap B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha hr hφ hab ℱ).app d s =
      ℱ.val.map (comparisonMorphism B S hS p q eU eV a f g φ aSpace ha d).op s :=
  rfl

/-- The map `g^*ℱ|_{V_étale} ⟶ a_{small,*}(f^*ℱ|_{U_étale})` of `𝒪_V`-modules attached by the
module-level chart correspondence `AlgebraicGeometry.Space.moduleFMapHom` to the maps of sections
`AlgebraicGeometry.Space.moduleComparisonFMap`. -/
noncomputable def moduleComparisonPushforwardHom (ℱ : inheritedEtaleModules B S hS r hr) :
    etaleRestrictedModuleInverseImage B S hS q r hq hr eV g hg ℱ ⟶
      (modulePushforward B S hS aSpace).obj
        (etaleRestrictedModuleInverseImage B S hS p r hp hr eU f hf ℱ) :=
  moduleFMapHom B S hS aSpace
    (etaleRestrictedModuleInverseImage B S hS p r hp hr eU f hf ℱ)
    (etaleRestrictedModuleInverseImage B S hS q r hq hr eV g hg ℱ)
    (moduleComparisonFMap B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha hr hφ hab ℱ)

/-- The comparison map

```
c_φ : a_small^*(g^*ℱ|_{V_étale}) ⟶ f^*ℱ|_{U_étale}
```

of a 2-commutative triangle `φ : a ⋙ g ≅ f` of 1-morphisms of categories fibred in groupoids
over `(Sch/S)_{fppf}` whose two source categories `𝒰`, `𝒱` are representable by algebraic
spaces `U`, `V`, for an `𝒪_𝒳`-module `ℱ` on the inherited étale site of `𝒳`.

Here `a_small^*` is the inverse image of modules (`AlgebraicGeometry.Space.modulePullback`)
for the morphism `aSpace : U ⟶ V` of algebraic spaces corresponding to `a`, and `c_φ` is the
adjoint, under `a_small^* ⊣ a_{small,*}`, of
`AlgebraicGeometry.Space.moduleComparisonPushforwardHom`. -/
@[stacks 076R "the comparison map of a 2-commutative triangle, on modules"]
noncomputable def comparisonAlgebraicSpacesModules
    (ℱ : inheritedEtaleModules B S hS r hr) :
    (modulePullback B S hS aSpace).obj
        (etaleRestrictedModuleInverseImage B S hS q r hq hr eV g hg ℱ) ⟶
      etaleRestrictedModuleInverseImage B S hS p r hp hr eU f hf ℱ :=
  ((modulePullbackAdjunction B S hS aSpace).homEquiv _ _).symm
    (moduleComparisonPushforwardHom B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha hr hφ hab ℱ)

/-- The comparison map `AlgebraicGeometry.Space.comparisonAlgebraicSpacesModules` is adjoint to
`AlgebraicGeometry.Space.moduleComparisonPushforwardHom`. -/
theorem comparisonAlgebraicSpacesModules_adjoint
    (ℱ : inheritedEtaleModules B S hS r hr) :
    (modulePullbackAdjunction B S hS aSpace).homEquiv _ _
        (comparisonAlgebraicSpacesModules B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha
          hr hφ hab ℱ) =
      moduleComparisonPushforwardHom B S hS p q r hp hq eU eV a f g hf hg φ aSpace ha
        hr hφ hab ℱ :=
  Equiv.apply_symm_apply _ _

end Triangle

end AlgebraicGeometry.Space

end
