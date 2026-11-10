module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafFiniteness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToSheafColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftFiniteColimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.FibrewiseModAbelian
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialModuleLowerShriekColim
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialSiteMooreSheaf
public import StacksFrontier.Cotangent.Triangle.DerivedFirstVertex
public import StacksFrontier.Homology.TotalComplexTransport

/-!
# The module-coefficient Moore complex, read on underlying abelian sheaves

Let `(C, J)` be a small site, let `O` be a sheaf of rings on it, let `π : Δ × C ⥤ C` be the
projection of [Stacks, Tag 09D0] and let `Δ × C` carry the topology it inherits from `(C, J)`
along `π`. There are two Moore-complex computations of `L π_!` on `Δ × C`:

* the **module-coefficient** one,
  `Stacks.SimplicialModules.derivedProjectionLowerShriekIsoMooreBicomplexTotalModules`, which for
  a complex `X^•` of sheaves of `π^{-1}O`-modules bounded above by `0` gives
  `L π_!(X^•) ≅ Q(Tot(Z))` in `D(Mod(O))`, with `Z^{p,q} = ((X^p)_•)^q` formed from
  `Stacks.SimplicialModules.fibrewiseMod` and the extended Moore complex;
* the **abelian-coefficient** one of [Stacks, Tag 09D2] on the simplicial site, whose conclusions,
  among them flat base change
  (`Stacks.SimplicialModules.quasiIso_mooreSheafBaseChange_app_of_flat`), are quasi-isomorphisms of
  complexes of **abelian sheaves** on `C` built from
  `Stacks.SimplicialModules.mooreAbSheafCochain`.

The natural isomorphism `Stacks.SimplicialModules.mooreSpliceIso` identifies the module-coefficient
Moore complex, with its module structure forgotten, with the abelian-coefficient one, and
`Stacks.SimplicialModules.totalMooreSpliceIso` does the same for the double complexes and their
total complexes, naturally in the complex. Consequently
(`Stacks.SimplicialModules.quasiIso_total_map_mooreModBicomplex_iff`) a map of bounded above
complexes of sheaves of `π^{-1}O`-modules induces a quasi-isomorphism on the module-coefficient
Moore total complexes **exactly when** it does on the abelian-coefficient ones.

Derived lower shriek itself does **not** commute with forgetting the module structure
(`Stacks.SheafOfModules.lowerShriekForget_not_isomorphic`), so the module-coefficient form of
Section 09D0 is not a consequence of the abelian one. The statements here are at the level of
complexes, where forgetting is harmless: `SheafOfModules.toSheaf` is exact and reflects
isomorphisms (`Stacks.SheafOfModules.Constant.reflectsIsomorphisms_toSheaf`), so it detects
quasi-isomorphisms.

## Main definitions

* `Stacks.SimplicialModules.mooreSpliceIso`: **the splice**, an isomorphism of functors
  `Mod(π^{-1}O) ⥤ CochainComplex (Ab(C)) ℤ`.
* `Stacks.SimplicialModules.mooreModBicomplexFunctor` and
  `Stacks.SimplicialModules.mooreAbBicomplexFunctor`: the two Moore double complexes of a complex.
* `Stacks.SimplicialModules.totalMooreSpliceIso`: the splice on total complexes.

## Main results

* `Stacks.SimplicialModules.mooreModBicomplexFunctor_obj`: the module-coefficient double complex
  is the one the module-coefficient computation of `L π_!` produces.
* `Stacks.SimplicialModules.totalMooreSpliceIso_hom_naturality`: the splice on total complexes is
  natural in the complex.
* `Stacks.SimplicialModules.quasiIso_total_map_mooreModBicomplex_iff`: **the transfer** — the
  module-coefficient Moore total complex sees exactly the quasi-isomorphisms the
  abelian-coefficient one sees.

## Scope

It is neither [Stacks, Tag 09D0] nor [Stacks, Tag 09D2], and it carries no tag: it states nothing
about `L π_!`, about the derived tensor product, or about an arbitrary object of a derived
category.

## References

* [Stacks Project, Tag 09D0](https://stacks.math.columbia.edu/tag/09D0)
* [Stacks Project, Tag 09D2](https://stacks.math.columbia.edu/tag/09D2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology

namespace Stacks.SimplicialModules

universe w

section Abelian

variable (C : Type w) [SmallCategory C] (J : GrothendieckTopology C)
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Sheafifying an abelian sheaf gives it back.** The counit of the sheafification adjunction
is invertible, so forgetting an abelian sheaf to a presheaf and sheafifying is the identity. -/
def sheafToPresheafCompPresheafToSheafIso :
    sheafToPresheaf J AddCommGrpCat.{w} ⋙ presheafToSheaf J AddCommGrpCat.{w} ≅
      𝟭 (Sheaf J AddCommGrpCat.{w}) :=
  haveI : IsIso (sheafificationAdjunction J AddCommGrpCat.{w}).counit :=
    NatIso.isIso_of_isIso_app _
  asIso (sheafificationAdjunction J AddCommGrpCat.{w}).counit

/-- **The fibrewise reading of an abelian sheaf on `Δ × C` is the currying of its underlying
presheaf, sheafified in each degree.** Restriction to the fibre `{n} × C` and the currying that
reads a presheaf on `Δ × C` as a simplicial presheaf on `C` are the same operation on sections, and
the restriction of a sheaf is already a sheaf, so the sheafification inserted on the right is the
counit. -/
def fibrewiseIsoCurry :
    fibrewise J AddCommGrpCat.{w} ≅
      (sheafToPresheaf (projectionTopology C J) AddCommGrpCat.{w} ⋙
          simplicialCurry (C := C) AddCommGrpCat.{w}) ⋙
        (Functor.whiskeringRight SimplexCategoryᵒᵖ (Cᵒᵖ ⥤ AddCommGrpCat.{w})
          (Sheaf J AddCommGrpCat.{w})).obj (presheafToSheaf J AddCommGrpCat.{w}) :=
  (Functor.isoWhiskerLeft (fibrewise J AddCommGrpCat.{w})
    ((Functor.whiskeringRight SimplexCategoryᵒᵖ (Sheaf J AddCommGrpCat.{w})
      (Sheaf J AddCommGrpCat.{w})).mapIso
        (sheafToPresheafCompPresheafToSheafIso C J))).symm

/-- **The Moore complex of the fibrewise reading of an abelian sheaf on `Δ × C` is `s(-)`**, the
complex `Stacks.SimplicialModules.mooreAbSheafCochain` of the abelian-coefficient development of
[Stacks, Tag 09D2]: the Moore complex of the curried simplicial presheaf, sheafified in each
degree. -/
def fibrewiseMooreAbSheafIso :
    fibrewise J AddCommGrpCat.{w} ⋙
        alternatingFaceMapCochainComplex (Sheaf J AddCommGrpCat.{w}) ≅
      sheafToPresheaf (projectionTopology C J) AddCommGrpCat.{w} ⋙ mooreAbSheafCochain J :=
  Functor.isoWhiskerRight (fibrewiseIsoCurry C J)
      (alternatingFaceMapCochainComplex (Sheaf J AddCommGrpCat.{w})) ≪≫
    Functor.isoWhiskerLeft
      (sheafToPresheaf (projectionTopology C J) AddCommGrpCat.{w} ⋙
        simplicialCurry (C := C) AddCommGrpCat.{w})
      (alternatingFaceMapCochainComplexCompMapHomologicalComplexIso
        (presheafToSheaf J AddCommGrpCat.{w})).symm

end Abelian

section Modules

variable (C : Type w) [SmallCategory C] (J : GrothendieckTopology C)
  [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)]
  (O : Sheaf J RingCat.{w})
  [HasWeakSheafify (projectionTopology C J) AddCommGrpCat.{w}]
  [(projectionTopology C J).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(SheafOfModules.pushforward.{w} (F := projection C)
    (Stacks.Cohomology.DerivedLowerShriek.idRingMap
      (projectionTopology C J) J (projection C) O)).IsRightAdjoint]

/-- **Forgetting the module structure of the Moore complex of a fibrewise reading.** The
module-coefficient Moore complex of `Stacks.SimplicialModules.fibrewiseMod`, read on underlying
abelian sheaves, is the Moore complex of the abelian fibrewise reading. -/
def mooreModToSheafIso :
    fibrewiseMod C J O ⋙ Stacks.ChaoticSite.GeneralValued.mooreCochainComplex
        (𝟭 SimplexCategory) (SheafOfModules.{w} O) ⋙
        (SheafOfModules.toSheaf.{w} O).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      SheafOfModules.toSheaf.{w} (projectionRing C J O) ⋙ fibrewise J AddCommGrpCat.{w} ⋙
        alternatingFaceMapCochainComplex (Sheaf J AddCommGrpCat.{w}) :=
  Functor.isoWhiskerLeft (fibrewiseMod C J O)
      (alternatingFaceMapCochainComplexCompMapHomologicalComplexIso
        (SheafOfModules.toSheaf.{w} O)) ≪≫
    eqToIso (congrArg (fun F => F ⋙ alternatingFaceMapCochainComplex
      (Sheaf J AddCommGrpCat.{w})) (fibrewiseMod_comp_toSheaf C J O))

/-- **The splice.** The module-coefficient Moore complex of a sheaf of `π^{-1}O`-modules, read on
underlying abelian sheaves, is the complex `s(-)` of its underlying abelian presheaf on `Δ × C`
that the abelian-coefficient development of [Stacks, Tag 09D2] computes with. -/
def mooreSpliceIso :
    fibrewiseMod C J O ⋙ Stacks.ChaoticSite.GeneralValued.mooreCochainComplex
        (𝟭 SimplexCategory) (SheafOfModules.{w} O) ⋙
        (SheafOfModules.toSheaf.{w} O).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      SheafOfModules.toSheaf.{w} (projectionRing C J O) ⋙
        sheafToPresheaf (projectionTopology C J) AddCommGrpCat.{w} ⋙ mooreAbSheafCochain J :=
  mooreModToSheafIso C J O ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.toSheaf.{w} (projectionRing C J O))
      (fibrewiseMooreAbSheafIso C J)

/-! ### The double complexes and their total complexes -/

section Total

/-- **The module-coefficient Moore double complex** of a complex of sheaves of `π^{-1}O`-modules,
`Z^{p,q} = ((X^p)_•)^q`, as a functor of the complex. -/
abbrev mooreModBicomplexFunctor :
    CochainComplex (SheafOfModules.{w} (projectionRing C J O)) ℤ ⥤
      HomologicalComplex₂ (SheafOfModules.{w} O) (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (fibrewiseMod C J O ⋙ Stacks.ChaoticSite.GeneralValued.mooreCochainComplex
    (𝟭 SimplexCategory) (SheafOfModules.{w} O)).mapHomologicalComplex (ComplexShape.up ℤ)

/-- **The abelian-coefficient Moore double complex** of the same complex: the degreewise `s(-)`
of the underlying abelian presheaves, which is the double complex of
`Stacks.SimplicialModules.mooreSheafBicomplex`. -/
abbrev mooreAbBicomplexFunctor :
    CochainComplex (SheafOfModules.{w} (projectionRing C J O)) ℤ ⥤
      HomologicalComplex₂ (Sheaf J AddCommGrpCat.{w}) (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (SheafOfModules.toSheaf.{w} (projectionRing C J O) ⋙
    sheafToPresheaf (projectionTopology C J) AddCommGrpCat.{w} ⋙
    mooreAbSheafCochain J).mapHomologicalComplex (ComplexShape.up ℤ)

variable (X : CochainComplex (SheafOfModules.{w} (projectionRing C J O)) ℤ)

omit [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)]
  [HasWeakSheafify (projectionTopology C J) AddCommGrpCat.{w}]
  [(projectionTopology C J).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(SheafOfModules.pushforward.{w} (F := projection C)
    (Stacks.Cohomology.DerivedLowerShriek.idRingMap
      (projectionTopology C J) J (projection C) O)).IsRightAdjoint] in
/-- The module-coefficient double complex is the one the module-coefficient computation of
`L π_!` produces, on the nose. -/
theorem mooreModBicomplexFunctor_obj :
    (mooreModBicomplexFunctor C J O).obj X =
      Stacks.ChaoticSite.GeneralValued.mooreBicomplex (𝟭 SimplexCategory)
        (((fibrewiseMod C J O).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) :=
  rfl

/-- The fibrewise reading of a complex bounded above by `0` is bounded above by `0`. -/
instance isStrictlyLE_fibrewiseMod_map [X.IsStrictlyLE 0] :
    CochainComplex.IsStrictlyLE
      (((fibrewiseMod C J O).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) 0 :=
  (CochainComplex.isStrictlyLE_iff _ 0).2 fun i hi =>
    Functor.map_isZero (fibrewiseMod C J O) (CochainComplex.isZero_of_isStrictlyLE X 0 i hi)

/-- The module-coefficient Moore double complex of a complex bounded above by `0` has a total
complex. -/
instance hasTotal_mooreModBicomplexFunctor_obj [X.IsStrictlyLE 0] :
    ((mooreModBicomplexFunctor C J O).obj X).HasTotal (ComplexShape.up ℤ) :=
  StacksDraft.TotalComplexQuasiIso.hasTotal_of_upperBound _ 0 0
    (fun p hp => Functor.map_isZero
      (fibrewiseMod C J O ⋙ Stacks.ChaoticSite.GeneralValued.mooreCochainComplex
        (𝟭 SimplexCategory) (SheafOfModules.{w} O))
      (CochainComplex.isZero_of_isStrictlyLE X 0 p hp))
    (fun _p q hq => Stacks.ChaoticSite.GeneralValued.isZero_mooreCochainComplex_X
      (𝟭 SimplexCategory) _ q hq)

/-- The module-coefficient Moore double complex of a complex bounded above by `0`, read on
underlying abelian sheaves, has a total complex. -/
instance hasTotal_mapBicomplex_mooreModBicomplexFunctor_obj [X.IsStrictlyLE 0] :
    (HomologicalComplex₂.mapBicomplex (SheafOfModules.toSheaf.{w} O)
      ((mooreModBicomplexFunctor C J O).obj X)).HasTotal (ComplexShape.up ℤ) :=
  StacksDraft.TotalComplexQuasiIso.hasTotal_of_upperBound _ 0 0
    (fun p hp => Functor.map_isZero
      ((SheafOfModules.toSheaf.{w} O).mapHomologicalComplex (ComplexShape.up ℤ))
      (Functor.map_isZero
        (fibrewiseMod C J O ⋙ Stacks.ChaoticSite.GeneralValued.mooreCochainComplex
          (𝟭 SimplexCategory) (SheafOfModules.{w} O))
        (CochainComplex.isZero_of_isStrictlyLE X 0 p hp)))
    (fun _p q hq => Functor.map_isZero (SheafOfModules.toSheaf.{w} O)
      (Stacks.ChaoticSite.GeneralValued.isZero_mooreCochainComplex_X
        (𝟭 SimplexCategory) _ q hq))

/-- The same instance, for the image of the complex under the composite of
`Stacks.SimplicialModules.mooreModBicomplexFunctor` with forgetting the module structure. -/
instance hasTotal_comp_mooreModBicomplexFunctor_obj [X.IsStrictlyLE 0] :
    HomologicalComplex₂.HasTotal
      ((mooreModBicomplexFunctor C J O ⋙
        ((SheafOfModules.toSheaf.{w} O).mapHomologicalComplex
          (ComplexShape.up ℤ)).mapHomologicalComplex (ComplexShape.up ℤ)).obj X)
      (ComplexShape.up ℤ) :=
  hasTotal_mapBicomplex_mooreModBicomplexFunctor_obj C J O X

/-- **The splice on double complexes**, as an isomorphism of functors. -/
def bicomplexSpliceNatIso :
    mooreModBicomplexFunctor C J O ⋙
        ((SheafOfModules.toSheaf.{w} O).mapHomologicalComplex
          (ComplexShape.up ℤ)).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      mooreAbBicomplexFunctor C J O :=
  Functor.mapHomologicalComplexCompIso (mooreSpliceIso C J O) (ComplexShape.up ℤ)

/-- The abelian-coefficient Moore double complex of a complex bounded above by `0` has a total
complex. -/
instance hasTotal_mooreAbBicomplexFunctor_obj [X.IsStrictlyLE 0] :
    ((mooreAbBicomplexFunctor C J O).obj X).HasTotal (ComplexShape.up ℤ) :=
  HomologicalComplex₂.hasTotal_of_iso ((bicomplexSpliceNatIso C J O).app X) _

/-- Forgetting the module structure preserves the coproducts a total complex is built from: they
are coproducts indexed by a set of pairs of integers, and `toSheaf` preserves all colimits that
abelian sheaves have. -/
instance preservesColimitsOfShape_discrete_toSheaf (S : Type) :
    Limits.PreservesColimitsOfShape (Discrete S) (SheafOfModules.toSheaf.{w} O) := by
  have : HasColimitsOfShape (Discrete S) AddCommGrpCat.{w} :=
    Limits.hasColimitsOfShape_of_equivalence
      (Discrete.equivalence (Equiv.ulift.{w, 0} (α := S)))
  exact SheafOfModules.preservesColimitsOfShape_toSheaf O

/-- **The splice on total complexes.** Forgetting the module structure of the total complex of the
module-coefficient Moore double complex gives the total complex of the abelian-coefficient one. -/
def totalMooreSpliceIso [X.IsStrictlyLE 0] :
    ((SheafOfModules.toSheaf.{w} O).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((mooreModBicomplexFunctor C J O).obj X).total (ComplexShape.up ℤ)) ≅
      ((mooreAbBicomplexFunctor C J O).obj X).total (ComplexShape.up ℤ) :=
  (HomologicalComplex₂.totalIso (SheafOfModules.toSheaf.{w} O)
      ((mooreModBicomplexFunctor C J O).obj X)).symm ≪≫
    HomologicalComplex₂.total.mapIso ((bicomplexSpliceNatIso C J O).app X) (ComplexShape.up ℤ)

variable {X}

omit [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)]
  [HasWeakSheafify (projectionTopology C J) AddCommGrpCat.{w}]
  [(projectionTopology C J).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(SheafOfModules.pushforward.{w} (F := projection C)
    (Stacks.Cohomology.DerivedLowerShriek.idRingMap
      (projectionTopology C J) J (projection C) O)).IsRightAdjoint] in
/-- The splice on total complexes is natural in the complex. -/
lemma totalMooreSpliceIso_hom_naturality
    {Y : CochainComplex (SheafOfModules.{w} (projectionRing C J O)) ℤ}
    [X.IsStrictlyLE 0] [Y.IsStrictlyLE 0] (g : X ⟶ Y) :
    ((SheafOfModules.toSheaf.{w} O).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (HomologicalComplex₂.total.map ((mooreModBicomplexFunctor C J O).map g)
            (ComplexShape.up ℤ)) ≫ (totalMooreSpliceIso C J O Y).hom =
      (totalMooreSpliceIso C J O X).hom ≫
        HomologicalComplex₂.total.map ((mooreAbBicomplexFunctor C J O).map g)
          (ComplexShape.up ℤ) := by
  have h1 := HomologicalComplex₂.totalMap_naturality (c₁₂ := ComplexShape.up ℤ)
    (SheafOfModules.toSheaf.{w} O) ((mooreModBicomplexFunctor C J O).obj X)
    ((mooreModBicomplexFunctor C J O).map g)
  have hnat := (bicomplexSpliceNatIso C J O).hom.naturality g
  have h4 : HomologicalComplex₂.total.map
        ((((SheafOfModules.toSheaf.{w} O).mapHomologicalComplex
            (ComplexShape.up ℤ)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((mooreModBicomplexFunctor C J O).map g)) (ComplexShape.up ℤ) ≫
        HomologicalComplex₂.total.map ((bicomplexSpliceNatIso C J O).app Y).hom
          (ComplexShape.up ℤ) =
      HomologicalComplex₂.total.map ((bicomplexSpliceNatIso C J O).app X).hom
          (ComplexShape.up ℤ) ≫
        HomologicalComplex₂.total.map ((mooreAbBicomplexFunctor C J O).map g)
          (ComplexShape.up ℤ) := by
    rw [← HomologicalComplex₂.total.map_comp, ← HomologicalComplex₂.total.map_comp]
    exact congrArg (fun t => HomologicalComplex₂.total.map t (ComplexShape.up ℤ)) hnat
  have h3 : (HomologicalComplex₂.totalIso (c₁₂ := ComplexShape.up ℤ)
          (SheafOfModules.toSheaf.{w} O) ((mooreModBicomplexFunctor C J O).obj X)).inv ≫
        HomologicalComplex₂.total.map
          ((((SheafOfModules.toSheaf.{w} O).mapHomologicalComplex
              (ComplexShape.up ℤ)).mapHomologicalComplex (ComplexShape.up ℤ)).map
            ((mooreModBicomplexFunctor C J O).map g)) (ComplexShape.up ℤ) =
      ((SheafOfModules.toSheaf.{w} O).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (HomologicalComplex₂.total.map ((mooreModBicomplexFunctor C J O).map g)
            (ComplexShape.up ℤ)) ≫
        (HomologicalComplex₂.totalIso (c₁₂ := ComplexShape.up ℤ)
          (SheafOfModules.toSheaf.{w} O) ((mooreModBicomplexFunctor C J O).obj Y)).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv,
      HomologicalComplex₂.totalIso_hom_eq_totalMap,
      HomologicalComplex₂.totalIso_hom_eq_totalMap]
    exact h1
  simp only [totalMooreSpliceIso, Iso.trans_hom, Iso.symm_hom,
    HomologicalComplex₂.total.mapIso_hom]
  rw [← Category.assoc, ← h3, Category.assoc, h4, Category.assoc]

omit [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)]
  [HasWeakSheafify (projectionTopology C J) AddCommGrpCat.{w}]
  [(projectionTopology C J).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(SheafOfModules.pushforward.{w} (F := projection C)
    (Stacks.Cohomology.DerivedLowerShriek.idRingMap
      (projectionTopology C J) J (projection C) O)).IsRightAdjoint] in
/-- **The transfer.** A map of complexes of sheaves of `π^{-1}O`-modules bounded above by `0`
induces a quasi-isomorphism on the module-coefficient Moore total complexes exactly when it
induces one on the abelian-coefficient Moore total complexes of [Stacks, Tag 09D2]:
`SheafOfModules.toSheaf` is exact and reflects isomorphisms, so it neither creates nor destroys
quasi-isomorphisms, and by `Stacks.SimplicialModules.totalMooreSpliceIso` the complex it produces
from the module-coefficient total complex is the abelian-coefficient one. -/
theorem quasiIso_total_map_mooreModBicomplex_iff
    {Y : CochainComplex (SheafOfModules.{w} (projectionRing C J O)) ℤ}
    [X.IsStrictlyLE 0] [Y.IsStrictlyLE 0] (g : X ⟶ Y) :
    QuasiIso (HomologicalComplex₂.total.map ((mooreModBicomplexFunctor C J O).map g)
        (ComplexShape.up ℤ)) ↔
      QuasiIso (HomologicalComplex₂.total.map ((mooreAbBicomplexFunctor C J O).map g)
        (ComplexShape.up ℤ)) := by
  have : PreservesFiniteColimits (SheafOfModules.toSheaf.{w} O) :=
    Stacks.SheafOfModules.toSheaf_preservesFiniteColimits.{w} O
  have : (SheafOfModules.toSheaf.{w} O).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  have : (SheafOfModules.toSheaf.{w} O).ReflectsIsomorphisms :=
    Stacks.SheafOfModules.Constant.reflectsIsomorphisms_toSheaf J
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    (HomologicalComplex₂.total.map ((mooreModBicomplexFunctor C J O).map g)
      (ComplexShape.up ℤ)) (SheafOfModules.toSheaf.{w} O)]
  exact quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (totalMooreSpliceIso C J O X) (totalMooreSpliceIso C J O Y)
      (totalMooreSpliceIso_hom_naturality C J O g).symm)

end Total

end Modules

end Stacks.SimplicialModules

end
