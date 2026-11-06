module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Geometry.RingedSpace.SheafedSpace
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Spectral.Hom
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianBaseChangeMap
public import StacksFrontier.Topology.Sheaves.Functors.Pushforward.Injective

/-!
# Cohomology on a cofiltered limit of spectral spaces: the encoding

For a compatible system of abelian sheaves on a cofiltered system of spectral spaces,
cohomology on the inverse limit should be the filtered colimit of cohomology at the stages,
both over the inverse image of a quasi-compact open at a fixed stage and globally.

This file sets up the statement of that assertion and proves the first inputs to it.  The
assertion itself is `SpectralAbelianSheafSystem.isIso_comparison` and
`SpectralAbelianSheafSystem.isIso_comparison_global`
(`Topology/Sheaves/Cohomology/SpectralSpaceLimit/ComparisonInEveryDegree.lean`).

## Main definitions

* `SpectralAbelianSheafSystem` records the spectral spaces, abelian sheaves, and compatible
  additive transition maps, as a functor into abelian sheafed spaces together with the
  spectrality hypotheses.
* `OpenCone` is a compatible system of opens in such a diagram together with an open on the
  vertex of a cone over it.
* `IsCohomologyMap` specifies the canonical map on sheaf cohomology by a map of injective
  resolutions extending a given map of sheaves, together with an identification of the
  cohomology groups with right-derived evaluation.
* `CohomologyCocone` is a presentation of the actual cohomology diagram and its canonical
  comparison cocone; `CohomologyCocone.cocone` and `CohomologyCocone.comparison` extract the
  cocone and the induced map out of the colimit.
* `SpectralAbelianSheafSystem.stageOpenCone` and `SpectralAbelianSheafSystem.globalOpenCone`
  are the two `OpenCone`s appearing in the statement of the tag.

## Main results

* `preservesInjectiveObjects_sheafPushforward`: the pushforward of abelian sheaves preserves
  injective objects, the inverse image along a continuous map being left exact
  (`Stacks.Cohomology.BaseChange.abelianInverseImage_preservesFiniteLimits`).
* `InjectiveResolution.descToComplex`: a map from an object into the zeroth term of a cochain
  complex of injective objects, killed by the first differential, extends to a map of complexes
  out of any injective resolution of that object.
* `exists_isCohomologyMap`: the specification `IsCohomologyMap` is satisfiable, i.e. for every
  map of sheaves over a continuous map and every choice of identifications with right-derived
  evaluation there is a map on cohomology induced by a map of injective resolutions.

## Implementation notes

A functor into abelian sheafed spaces encodes the additive transition maps and their identity
and composition laws.  A limiting cone in this category encodes both the inverse limit of
spaces and the sheaf `colim pᵢ⁻¹ Fᵢ`: a morphism over a projection is adjoint to a morphism
from the corresponding inverse-image sheaf, and the limit universal property is the colimit
universal property for these sheaves.

Cohomology is Mathlib's native `Sheaf.H'` on the original sheaf.  The hypotheses needed to
form it — `HasSheafify` for the site of opens and `HasExt` for the category of abelian sheaves
on it — are available from Mathlib: the site of opens of a topological space is small, so the
category of abelian sheaves on it is a Grothendieck abelian category, hence has enough
injectives and a well-behaved `Ext`.  No additional input about injectives of abelian sheaves
is required, and in particular nothing is taken from the statement of Tag 01DG.

`IsCohomologyMap` requires an actual lift to injective resolutions and an identification with
right-derived evaluation.  That specification is shown here to be satisfiable
(`exists_isCohomologyMap`), using that the pushforward of abelian sheaves preserves injective
objects, which in turn follows from left exactness of the inverse-image functor.

The identification `Sheaf.H' F p U ≅ ((sections X U).rightDerived p).obj F` of the native
`Ext`-valued cohomology with right-derived evaluation is
`Stacks.Cohomology.SpectralLimit.cohomologyIsoRightDerivedSections`
(in `StacksFrontier.Topology.Sheaves.Cohomology.SpectralSpaceLimit.NativeCohomologyCocones`), and
the uniqueness of the map specified by `IsCohomologyMap` is `IsCohomologyMap.eq`
(in `StacksFrontier.Topology.Sheaves.Cohomology.SpectralSpaceLimit.CohomologyMapUniqueness`), from
the homotopy uniqueness `CategoryTheory.InjectiveResolution.descHomotopy'` of a lift of an
injective resolution into a complex of injective objects.

## References

* [Stacks Project, Tag 0A37](https://stacks.math.columbia.edu/tag/0A37)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

universe u w v v'

namespace Stacks.Cohomology.SpectralLimit

/-! ### Exactness of the inverse image and injectivity of the pushforward -/

section Pushforward

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- The inverse-image functor on abelian sheaves preserves monomorphisms.  The content is the
instance `TopCat.Sheaf.pullback_preservesMonomorphisms`. -/
theorem preservesMonomorphisms_sheafPullback :
    (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).PreservesMonomorphisms :=
  TopCat.Sheaf.pullback_preservesMonomorphisms f

/-- The pushforward of abelian sheaves preserves injective objects, being right adjoint to the
left exact inverse-image functor.  The content is the instance
`TopCat.Sheaf.pushforward_preservesInjectiveObjects`. -/
theorem preservesInjectiveObjects_sheafPushforward :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).PreservesInjectiveObjects :=
  TopCat.Sheaf.pushforward_preservesInjectiveObjects f

end Pushforward

/-! ### Lifting an injective resolution into a complex of injective objects -/

section Desc

/-- The degree-zero term of an injective resolution of `G`, as the target of the resolution
map `I.ι.f 0` out of the single complex.  Writing the source of `I.ι.f 0` in this shape is what
lets the `Mono (I.ι.f 0)` instance apply. -/
abbrev single₀X {C : Type u} [Category.{v} C] [Abelian C] (G : C) : C :=
  ((CochainComplex.single₀ C).obj G).X 0

/-- Auxiliary construction for `descToComplex`: the degree-zero component, obtained by
extending `g` along the monomorphism `I.ι.f 0`. -/
def descToComplexZero {C : Type u} [Category.{v} C] [Abelian C] {G : C}
    (I : InjectiveResolution G) (T : CochainComplex C ℕ) (hT : ∀ n, Injective (T.X n))
    (g : G ⟶ T.X 0) : I.cocomplex.X 0 ⟶ T.X 0 :=
  letI := hT 0
  Injective.factorThru (show single₀X G ⟶ T.X 0 from g) (I.ι.f 0)

/-- The degree-zero component of the lift extends `g` along the resolution. -/
@[reassoc]
theorem ι_comp_descToComplexZero {C : Type u} [Category.{v} C] [Abelian C] {G : C}
    (I : InjectiveResolution G) (T : CochainComplex C ℕ) (hT : ∀ n, Injective (T.X n))
    (g : G ⟶ T.X 0) :
    I.ι.f 0 ≫ descToComplexZero I T hT g = (show single₀X G ⟶ T.X 0 from g) :=
  have := hT 0
  Injective.comp_factorThru (show single₀X G ⟶ T.X 0 from g) (I.ι.f 0)

/-- Auxiliary construction for `descToComplex`: the degree-one component, obtained from
exactness of the resolution at degree zero. -/
def descToComplexOne {C : Type u} [Category.{v} C] [Abelian C] {G : C}
    (I : InjectiveResolution G) (T : CochainComplex C ℕ) (hT : ∀ n, Injective (T.X n))
    (g : G ⟶ T.X 0) (hg : g ≫ T.d 0 1 = 0) : I.cocomplex.X 1 ⟶ T.X 1 :=
  letI := hT 1
  I.exact₀.descToInjective (descToComplexZero I T hT g ≫ T.d 0 1)
    (show I.ι.f 0 ≫ descToComplexZero I T hT g ≫ T.d 0 1 = 0 by
      rw [ι_comp_descToComplexZero_assoc]
      exact hg)

/-- The degree-zero and degree-one components of the lift form a commutative square. -/
theorem descToComplexOne_comm {C : Type u} [Category.{v} C] [Abelian C] {G : C}
    (I : InjectiveResolution G) (T : CochainComplex C ℕ) (hT : ∀ n, Injective (T.X n))
    (g : G ⟶ T.X 0) (hg : g ≫ T.d 0 1 = 0) :
    descToComplexZero I T hT g ≫ T.d 0 1 =
      I.cocomplex.d 0 1 ≫ descToComplexOne I T hT g hg :=
  have := hT 1
  (I.exact₀.comp_descToInjective _ _).symm

/-- A map `g : G ⟶ T.X 0` into the zeroth term of a cochain complex of injective objects
which is killed by the first differential extends to a map of complexes out of any injective
resolution of `G`.  This is the comparison theorem for injective resolutions in the form
where only the *target* is required to consist of injective objects. -/
def descToComplex {C : Type u} [Category.{v} C] [Abelian C] {G : C}
    (I : InjectiveResolution G) (T : CochainComplex C ℕ) (hT : ∀ n, Injective (T.X n))
    (g : G ⟶ T.X 0) (hg : g ≫ T.d 0 1 = 0) : I.cocomplex ⟶ T :=
  CochainComplex.mkHom _ _ (descToComplexZero I T hT g) (descToComplexOne I T hT g hg)
    (descToComplexOne_comm I T hT g hg)
    (fun n p =>
      letI := hT (n + 2)
      have hp : I.cocomplex.d n (n + 1) ≫ p.2.1 ≫ T.d (n + 1) (n + 2) = 0 := by
        rw [← Category.assoc, ← p.2.2, Category.assoc, HomologicalComplex.d_comp_d,
          Limits.comp_zero]
      ⟨(I.exact_succ n).descToInjective (p.2.1 ≫ T.d (n + 1) (n + 2)) hp,
        ((I.exact_succ n).comp_descToInjective _ hp).symm⟩)

/-- The lift of `g` out of an injective resolution extends `g`. -/
@[reassoc]
theorem ι_comp_descToComplex {C : Type u} [Category.{v} C] [Abelian C] {G : C}
    (I : InjectiveResolution G) (T : CochainComplex C ℕ) (hT : ∀ n, Injective (T.X n))
    (g : G ⟶ T.X 0) (hg : g ≫ T.d 0 1 = 0) :
    I.ι.f 0 ≫ (descToComplex I T hT g hg).f 0 = (show single₀X G ⟶ T.X 0 from g) :=
  ι_comp_descToComplexZero I T hT g

end Desc

/-! ### Sections of an abelian sheaf and the specification of the maps on cohomology -/

/-- Enlarge the values of a sheaf so that the coefficient universe contains the space
universe.  This leaves the input coefficient and space universes independent. -/
abbrev liftSheaf (X : TopCat.{u}) :
    X.Sheaf AddCommGrpCat.{w} ⥤ X.Sheaf AddCommGrpCat.{max u w} :=
  sheafCompose (Opens.grothendieckTopology X) AddCommGrpCat.uliftFunctor.{u, w}

/-- Sheafification is available after the coefficient universe has been enlarged. -/
instance hasSheafifyOpensMax (X : TopCat.{u}) :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u w} :=
  hasSheafifyEssentiallySmallSite.{_, _, _, _, max u w} _ _

/-- Evaluation of an abelian sheaf on an open subset. -/
abbrev sections (X : TopCat.{u}) (U : Opens X) :
    X.Sheaf AddCommGrpCat.{max u w} ⥤ AddCommGrpCat.{max u w} :=
  TopCat.Sheaf.forget _ X ⋙ (evaluation _ _).obj (op U)

/-- Evaluation of an abelian sheaf on an open subset is an additive functor. -/
instance (X : TopCat.{u}) (U : Opens X) : (sections.{u, w} X U).Additive := ⟨rfl⟩

/-- Evaluation of an abelian sheaf on an open subset preserves zero morphisms. -/
instance (X : TopCat.{u}) (U : Opens X) : (sections.{u, w} X U).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

/-- Pushforward of abelian sheaves along a continuous map is an additive functor. -/
instance {X Y : TopCat.{u}} (f : X ⟶ Y) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{max u w} f).Additive := ⟨rfl⟩

/-- Restriction from sections of a pushforward over `V` to sections over an open `U`
contained in the inverse image of `V`. -/
@[simps]
def restrictSections {X Y : TopCat.{u}} (f : X ⟶ Y)
    (V : Opens Y) (U : Opens X) (h : U ≤ (Opens.map f).obj V) :
    TopCat.Sheaf.pushforward AddCommGrpCat.{max u w} f ⋙ sections Y V ⟶ sections X U where
  app F := F.obj.map (homOfLE h).op
  naturality {_ _} φ := (φ.hom.naturality (homOfLE h).op).symm

/-- The map of section complexes induced by a map into a pushforward complex, followed
by restriction to the specified open. -/
def sectionsComplexMap {X Y : TopCat.{u}} (f : X ⟶ Y)
    {I : CochainComplex (Y.Sheaf AddCommGrpCat.{max u w}) ℕ}
    {J : CochainComplex (X.Sheaf AddCommGrpCat.{max u w}) ℕ}
    (ψ : I ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat f).mapHomologicalComplex _).obj J)
    (V : Opens Y) (U : Opens X) (h : U ≤ (Opens.map f).obj V) :
    ((sections.{u, w} Y V).mapHomologicalComplex _).obj I ⟶
      ((sections.{u, w} X U).mapHomologicalComplex _).obj J :=
  ((sections.{u, w} Y V).mapHomologicalComplex _).map ψ ≫
    ((restrictSections.{u, w} f V U h).mapHomologicalComplex _).app J

/-- A morphism on native sheaf cohomology is specified by a coherent identification with
right-derived evaluation and a map of injective resolutions extending the additive `f`-map. -/
def IsCohomologyMap {X Y : TopCat.{u}} (f : X ⟶ Y)
    {F : X.Sheaf AddCommGrpCat.{u}} {G : Y.Sheaf AddCommGrpCat.{u}}
    (φ : G ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F)
    (V : Opens Y) (U : Opens X) (h : U ≤ (Opens.map f).obj V) (p : ℕ)
    (eG : Sheaf.H'.{u, u, u} G p V ≅ ((sections.{u, u} Y V).rightDerived p).obj G)
    (eF : Sheaf.H'.{u, u, u} F p U ≅ ((sections.{u, u} X U).rightDerived p).obj F)
    (m : Sheaf.H'.{u, u, u} G p V ⟶ Sheaf.H'.{u, u, u} F p U) : Prop :=
  ∃ (I : InjectiveResolution G)
    (J : InjectiveResolution F)
    (ψ : I.cocomplex ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex _).obj J.cocomplex),
    (I.ι.f 0 ≫ ψ.f 0 = φ ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map (J.ι.f 0)) ∧
    (m = eG.hom ≫ (I.isoRightDerivedObj (sections.{u, u} Y V) p).hom ≫
      HomologicalComplex.homologyMap (sectionsComplexMap.{u, u} f ψ V U h) p ≫
      (J.isoRightDerivedObj (sections.{u, u} X U) p).inv ≫ eF.inv)

/-- The specification `IsCohomologyMap` is satisfiable: for any map of abelian sheaves over a
continuous map, any compatible pair of opens, any degree, and any identifications of the two
cohomology groups with right-derived evaluation, some map on cohomology is induced by a map of
injective resolutions. -/
theorem exists_isCohomologyMap {X Y : TopCat.{u}} (f : X ⟶ Y)
    {F : X.Sheaf AddCommGrpCat.{u}} {G : Y.Sheaf AddCommGrpCat.{u}}
    (φ : G ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F)
    (V : Opens Y) (U : Opens X) (h : U ≤ (Opens.map f).obj V) (p : ℕ)
    (eG : Sheaf.H'.{u, u, u} G p V ≅ ((sections.{u, u} Y V).rightDerived p).obj G)
    (eF : Sheaf.H'.{u, u, u} F p U ≅ ((sections.{u, u} X U).rightDerived p).obj F) :
    ∃ m, IsCohomologyMap f φ V U h p eG eF m := by
  let I : InjectiveResolution G := InjectiveResolution.of G
  let J : InjectiveResolution F := InjectiveResolution.of F
  have hT : ∀ n, Injective ((Functor.mapHomologicalComplex
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f) (ComplexShape.up ℕ)).obj
        J.cocomplex |>.X n) := fun n =>
    Functor.injective_obj_of_injective
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f) (J.injective n)
  have hz : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map (J.ι.f 0) ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map (J.cocomplex.d 0 1) = 0 := by
    rw [← Functor.map_comp, J.ι_f_zero_comp_complex_d, Functor.map_zero]
  have hg : (φ ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map (J.ι.f 0)) ≫
      ((Functor.mapHomologicalComplex (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)
        (ComplexShape.up ℕ)).obj J.cocomplex).d 0 1 = 0 :=
    (Category.assoc _ _ _).trans ((congrArg (fun t => φ ≫ t) hz).trans Limits.comp_zero)
  exact ⟨_, I, J, descToComplex I _ hT _ hg, ι_comp_descToComplex I _ hT _ hg, rfl⟩

/-! ### The cohomology cocone -/

/-- The additive sheaf map underlying a morphism of abelian sheafed spaces. -/
abbrev sheafMap {X Y : SheafedSpace.{_, _, u} AddCommGrpCat.{u}} (f : X ⟶ Y) :
    Y.sheaf ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.hom.base).obj X.sheaf :=
  ⟨f.hom.c⟩

/-- Compatible opens in a diagram and its cone.  The inequalities say exactly that the
transition maps and cone projections restrict to the specified opens. -/
structure OpenCone {K : Type v} [Category.{v'} K]
    (E : K ⥤ SheafedSpace.{_, _, u} AddCommGrpCat.{u}) (c : Cone E) where
  /-- The chosen open at each stage of the diagram. -/
  obj : ∀ k, Opens (E.obj k)
  /-- Each transition map carries the open at the source into the open at the target. -/
  map_le : ∀ {j i} (a : j ⟶ i), obj j ≤ (Opens.map (E.map a).hom.base).obj (obj i)
  /-- The chosen open on the vertex of the cone. -/
  pt : Opens c.pt
  /-- Each projection carries the open on the vertex into the open at that stage. -/
  leg_le : ∀ k, pt ≤ (Opens.map (c.π.app k).hom.base).obj (obj k)

/-- A presentation of the canonical cohomology cocone.  Every object is identified with
actual sheaf cohomology, and all arrows are prescribed by injective-resolution lifts of the
given sheaf maps. -/
structure CohomologyCocone {K : Type v} [Category.{v'} K]
    (E : K ⥤ SheafedSpace.{_, _, u} AddCommGrpCat.{u}) (c : Cone E)
    (O : OpenCone E c) (p : ℕ) where
  /-- The diagram of cohomology groups. -/
  diagram : Kᵒᵖ ⥤ AddCommGrpCat.{u}
  /-- Each object of the diagram is the sheaf cohomology of the stage sheaf on the stage open. -/
  objIso : ∀ k : K, diagram.obj (op k) ≅
    Sheaf.H'.{u, u, u} (E.obj k).sheaf p (O.obj k)
  /-- Each stage cohomology group is identified with right-derived evaluation. -/
  objDerivedIso : ∀ k : K,
    Sheaf.H'.{u, u, u} (E.obj k).sheaf p (O.obj k) ≅
      ((sections.{u, u} (E.obj k) (O.obj k)).rightDerived p).obj (E.obj k).sheaf
  /-- The cohomology on the vertex is identified with right-derived evaluation. -/
  vertexDerivedIso : Sheaf.H'.{u, u, u} c.pt.sheaf p O.pt ≅
    ((sections.{u, u} c.pt O.pt).rightDerived p).obj c.pt.sheaf
  /-- Each arrow of the diagram is the canonical map on cohomology. -/
  map_eq : ∀ {j i} (a : j ⟶ i),
    IsCohomologyMap (E.map a).hom.base (sheafMap (E.map a)) (O.obj i) (O.obj j)
      (O.map_le a) p (objDerivedIso i) (objDerivedIso j)
      ((objIso i).inv ≫ diagram.map a.op ≫ (objIso j).hom)
  /-- The comparison cocone. -/
  ι : diagram ⟶ (Functor.const Kᵒᵖ).obj (Sheaf.H'.{u, u, u} c.pt.sheaf p O.pt)
  /-- Each leg of the comparison cocone is the canonical map on cohomology. -/
  ι_eq : ∀ k,
    IsCohomologyMap (c.π.app k).hom.base (sheafMap (c.π.app k)) (O.obj k) O.pt
      (O.leg_le k) p (objDerivedIso k) vertexDerivedIso
      ((objIso k).inv ≫ ι.app (op k))

/-- The cocone with vertex the cohomology of the sheaf on the cone point. -/
@[simps]
def CohomologyCocone.cocone {K : Type v} [Category.{v'} K]
    {E : K ⥤ SheafedSpace.{_, _, u} AddCommGrpCat.{u}} {c : Cone E}
    {O : OpenCone E c} {p : ℕ} (D : CohomologyCocone E c O p) : Cocone D.diagram :=
  ⟨_, D.ι⟩

/-- The canonical comparison from the colimit of the stage cohomology groups.  Both the
diagram and the vertex are enlarged to accommodate the index universe. -/
def CohomologyCocone.comparison {K : Type v} [Category.{v'} K]
    {E : K ⥤ SheafedSpace.{_, _, u} AddCommGrpCat.{u}} {c : Cone E}
    {O : OpenCone E c} {p : ℕ} (D : CohomologyCocone E c O p) :
    colimit (D.diagram ⋙ AddCommGrpCat.uliftFunctor.{max v v'}) ⟶
      AddCommGrpCat.uliftFunctor.{max v v'}.obj (Sheaf.H'.{u, u, u} c.pt.sheaf p O.pt) :=
  colimit.desc _ (AddCommGrpCat.uliftFunctor.{max v v'}.mapCocone D.cocone)

/-- The comparison map restricts on each stage to the corresponding leg of the cocone. -/
@[reassoc (attr := simp)]
theorem CohomologyCocone.ι_comp_comparison {K : Type v} [Category.{v'} K]
    {E : K ⥤ SheafedSpace.{_, _, u} AddCommGrpCat.{u}} {c : Cone E}
    {O : OpenCone E c} {p : ℕ} (D : CohomologyCocone E c O p) (k : Kᵒᵖ) :
    colimit.ι (D.diagram ⋙ AddCommGrpCat.uliftFunctor.{max v v'}) k ≫ D.comparison =
      AddCommGrpCat.uliftFunctor.{max v v'}.map (D.ι.app k) :=
  colimit.ι_desc _ _

/-! ### The cofiltered system of spectral spaces -/

/-- A cofiltered system of spectral spaces and spectral maps, with abelian sheaves and
compatible additive `f`-maps.  Functoriality includes the identity and cocycle laws. -/
structure SpectralAbelianSheafSystem (K : Type v) [Category.{v'} K] [IsCofiltered K] where
  /-- The underlying diagram of abelian sheafed spaces. -/
  E : K ⥤ SheafedSpace.{_, _, u} AddCommGrpCat.{u}
  /-- Every stage is a spectral space. -/
  spectralSpace : ∀ k, SpectralSpace (E.obj k)
  /-- Every transition map is a spectral map. -/
  spectralMap : ∀ {j i} (a : j ⟶ i), IsSpectralMap (E.map a).hom.base

namespace SpectralAbelianSheafSystem

variable {K : Type v} [Category.{v'} K] [IsCofiltered K]
  (S : SpectralAbelianSheafSystem.{u, v, v'} K)

/-- The underlying inverse system of spaces. -/
abbrev baseDiagram : K ⥤ TopCat.{u} := S.E ⋙ SheafedSpace.forget _

/-- The opens `fₐ⁻¹ U` in the slice diagram, with open `pᵢ⁻¹ U` on the cone point. -/
@[simps obj pt]
def stageOpenCone (c : Cone S.E) (i : K) (U : Opens (S.E.obj i)) :
    OpenCone ((Over.forget i) ⋙ S.E) (c.whisker (Over.forget i)) where
  obj A := (Opens.map (S.E.map A.hom).hom.base).obj U
  map_le := by
    intro A B a x hx
    have he : (S.E.map a.left).hom.base ≫ (S.E.map B.hom).hom.base =
        (S.E.map A.hom).hom.base := by
      change S.baseDiagram.map a.left ≫ S.baseDiagram.map B.hom = S.baseDiagram.map A.hom
      rw [← Functor.map_comp, Over.w a]
    change ((S.E.map a.left).hom.base ≫ (S.E.map B.hom).hom.base) x ∈ U
    rwa [he]
  pt := (Opens.map (c.π.app i).hom.base).obj U
  leg_le := by
    intro A x hx
    have he : (c.π.app A.left).hom.base ≫ (S.E.map A.hom).hom.base =
        (c.π.app i).hom.base :=
      ((SheafedSpace.forget _).mapCone c).w A.hom
    change ((c.π.app A.left).hom.base ≫ (S.E.map A.hom).hom.base) x ∈ U
    rwa [he]

/-- The whole spaces, for the global cohomology comparison. -/
@[simps obj pt]
def globalOpenCone (c : Cone S.E) : OpenCone S.E c where
  obj _ := ⊤
  map_le _ := fun _ _ => trivial
  pt := ⊤
  leg_le _ := fun _ _ => trivial

end SpectralAbelianSheafSystem

end Stacks.Cohomology.SpectralLimit

end
