module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.EtaleComponentSheaves
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.EtaleStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.PhComparisonFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleStrictTotal
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackOfEquivalence
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.DenseSubsiteMorphism

/-!
# The small étale site of an augmented simplicial algebraic space against its spaces-étale site

Let `a : U → X` be an augmented simplicial algebraic space over a scheme `S`. Section 0DE7 of the
Stacks project forms the small étale site `U_étale` of `U` as the total site (Stacks 09WC) of the
simplicial object in sites `n ↦ U_{n, spaces, étale}`. The development has two models of it: the
total site of the strict components `AlgebraicGeometry.Space.EtaleComponent`, whose objects in
degree `n` are formal base changes realized by algebraic spaces étale over `U_n`, and the category
`AlgebraicGeometry.Space.SimplicialSpacesEtaleSite` of all algebraic spaces `V` étale over some
`U_n`, a morphism `V/U_n ⟶ W/U_m` being a simplex map `φ : [m] → [n]` together with a morphism
`V ⟶ W` lying over `U(φ)`.

Realizing the formal base changes compares the two: an object `(n, x)` of the total site goes to
the realization of `x` over `U_n`, and a morphism `(φ, g : x ⟶ u_φ(y))` to `g` followed by the
projection of the realization of `u_φ(y)` to that of `y`, a morphism over `U(φ)`. The comparison
is an equivalence of categories and a dense subsite, and it carries the structure sheaf of
`U_{spaces, étale}` to the structure sheaf of `U_étale` on the nose, both being global regular
functions on the realization. So it is an equivalence of ringed topoi, and its derived pullback is
an equivalence of derived categories of modules.

## Main definitions

* `AlgebraicGeometry.Space.etaleSiteComparison`: the comparison functor from the total site of the
  strict components to `SimplicialSpacesEtaleSite`.
* `AlgebraicGeometry.Space.etaleSiteComparisonRingedToposHom`: the induced equivalence of ringed
  topoi.

## Main results

* `AlgebraicGeometry.Space.etaleSiteComparison_comp_toSpaces`: followed by the underlying
  algebraic space, the comparison is the realization functor of `U_étale`.
* `AlgebraicGeometry.Space.etaleSiteComparison_isEquivalence` and
  `AlgebraicGeometry.Space.etaleSiteComparison_isDenseSubsite`.
* `AlgebraicGeometry.Space.isEquivalence_derivedPullback_etaleSiteComparisonRingedToposHom`.

## References

* [Stacks Project, Tag 0DE7](https://stacks.math.columbia.edu/tag/0DE7)
* [Stacks Project, Tag 09WC](https://stacks.math.columbia.edu/tag/09WC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Pseudofunctor

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (A : SimplicialObject.Augmented (AlgebraicSpaces B S hS))

open EtaleComponent SimplicialSpacesEtaleSite

/-- The formal base change of an object of the total site of the strict components. -/
abbrev EtaleTotal.obj (a : EtaleTotal A) : EtaleComponent A a.base.unop := a.fiber

variable {A} in
/-- The morphism `x ⟶ u_φ(y)` of formal base changes underlying a morphism of the total site. -/
abbrev EtaleTotal.fiberHom {a b : EtaleTotal A} (f : a ⟶ b) :
    EtaleTotal.obj A a ⟶ (transition (A := A) f.base.unop).obj (EtaleTotal.obj A b) :=
  f.fiber

/-- **The comparison of the small étale site of `U` with its spaces-étale site**: an object
`(n, x)` of the total site of the strict components goes to the realization of `x` over `U_n`,
and a morphism `(φ, g : x ⟶ u_φ(y))` to the morphism of realizations over `U(φ)` given by `g`
followed by the projection of the realization of `u_φ(y)` to that of `y`. -/
def etaleSiteComparison : EtaleTotal A ⥤ SimplicialSpacesEtaleSite B S hS A.left where
  obj a := ⟨a.base.unop, realize (A := A) (n := a.base.unop) (EtaleTotal.obj A a)⟩
  map {_ b} f := ⟨f.base.unop, (etaleTotalToSpaces A).map f,
    (Category.assoc _ _ _).trans ((congrArg ((EtaleTotal.fiberHom f).hom.hom.left ≫ ·)
      (comparison_hom f.base.unop (EtaleTotal.obj A b))).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ A.left.map f.base) (Over.w (EtaleTotal.fiberHom f).hom.hom))))⟩
  map_id a := Hom.ext rfl ((etaleTotalToSpaces A).map_id a)
  map_comp f g := Hom.ext rfl ((etaleTotalToSpaces A).map_comp f g)

/-- Followed by the underlying algebraic space, the comparison is the realization functor of
`U_étale`. -/
theorem etaleSiteComparison_comp_toSpaces :
    etaleSiteComparison A ⋙ toSpaces A.left = etaleTotalToSpaces A :=
  rfl

variable {A}

/-- The simplex map of the image of a morphism `f` under the comparison is that of `f`. -/
theorem etaleSiteComparison_map_base {a b : EtaleTotal A} (f : a ⟶ b) :
    ((etaleSiteComparison A).map f).base = f.base.unop :=
  rfl

/-- The morphism of algebraic spaces underlying the image of `f : (φ, g)` under the comparison is
`g` followed by the projection of the realization of `u_φ(y)` to that of `y`. -/
theorem etaleSiteComparison_map_hom {a b : EtaleTotal A} (f : a ⟶ b) :
    ((etaleSiteComparison A).map f).hom =
      (EtaleTotal.fiberHom f).hom.hom.left ≫ comparison f.base.unop (EtaleTotal.obj A b) :=
  rfl

/-- The comparison functor is faithful. -/
instance etaleSiteComparison_faithful : (etaleSiteComparison A).Faithful where
  map_injective {a b} f f' h := by
    obtain ⟨fb, ff⟩ := f
    obtain ⟨fb', ff'⟩ := f'
    obtain rfl : fb = fb' := Quiver.Hom.unop_inj (congrArg Hom.base h :)
    have hh : (ff : EtaleTotal.obj A a ⟶
          (transition (A := A) fb.unop).obj (EtaleTotal.obj A b)).hom.hom.left ≫
          comparison fb.unop (EtaleTotal.obj A b) =
        (ff' : EtaleTotal.obj A a ⟶
          (transition (A := A) fb.unop).obj (EtaleTotal.obj A b)).hom.hom.left ≫
          comparison fb.unop (EtaleTotal.obj A b) := congrArg Hom.hom h
    obtain rfl : ff = ff' := InducedCategory.hom_ext (ObjectProperty.hom_ext _
      (Over.OverMorphism.ext ((isPullback_comparison fb.unop (EtaleTotal.obj A b)).hom_ext hh
        ((Over.w (ff : EtaleTotal.obj A a ⟶ (transition (A := A) fb.unop).obj
            (EtaleTotal.obj A b)).hom.hom).trans
          (Over.w (ff' : EtaleTotal.obj A a ⟶ (transition (A := A) fb.unop).obj
            (EtaleTotal.obj A b)).hom.hom).symm))))
    rfl

/-- The morphism `x ⟶ u_φ(y)` of formal base changes lifting a morphism `t` of
`SimplicialSpacesEtaleSite` between the realizations: `t` and the structure map of `x`, into the
cartesian square of the comparison. -/
def etaleSiteComparisonPreimageFiber {a b : EtaleTotal A}
    (t : (etaleSiteComparison A).obj a ⟶ (etaleSiteComparison A).obj b) :
    EtaleTotal.obj A a ⟶ (transition (A := A) t.base).obj (EtaleTotal.obj A b) :=
  InducedCategory.homMk (ObjectProperty.homMk (Over.homMk
    ((isPullback_comparison t.base (EtaleTotal.obj A b)).lift t.hom
      (realize (EtaleTotal.obj A a)).obj.hom t.w)
    ((isPullback_comparison t.base (EtaleTotal.obj A b)).lift_snd _ _ _)))

/-- The lift `etaleSiteComparisonPreimageFiber t`, followed by the projection of realizations, is
the morphism of algebraic spaces underlying `t`. -/
theorem etaleSiteComparisonPreimageFiber_comparison {a b : EtaleTotal A}
    (t : (etaleSiteComparison A).obj a ⟶ (etaleSiteComparison A).obj b) :
    (etaleSiteComparisonPreimageFiber t).hom.hom.left ≫ comparison t.base (EtaleTotal.obj A b) =
      t.hom :=
  (isPullback_comparison t.base (EtaleTotal.obj A b)).lift_fst _ _ _

/-- The comparison functor is full. -/
instance etaleSiteComparison_full : (etaleSiteComparison A).Full where
  map_surjective {_ _} t :=
    ⟨⟨t.base.op, etaleSiteComparisonPreimageFiber t⟩,
      Hom.ext rfl (etaleSiteComparisonPreimageFiber_comparison t)⟩

/-- The comparison functor is essentially surjective: every algebraic space étale over some `U_n`
is isomorphic to the realization of a formal base change. -/
instance etaleSiteComparison_essSurj : (etaleSiteComparison A).EssSurj where
  mem_essImage V := ⟨⟨op V.degree, ofSpacesEtale (A := A) V.obj⟩,
    ⟨(degreeInclusion A.left V.degree).mapIso (realizeOfSpacesEtaleIso (A := A) V.obj)⟩⟩

/-- **The total site of the strict components is equivalent to `SimplicialSpacesEtaleSite`.** -/
instance etaleSiteComparison_isEquivalence : (etaleSiteComparison A).IsEquivalence where

/-! ### Compatibility with the topologies -/

/-- The comparison restricted to a component is the realization followed by the inclusion of
the degree. -/
theorem etaleSiteComparison_map_ι {b : SimplexCategoryᵒᵖ} {y z : EtaleComponent A b.unop}
    (g : y ⟶ z) :
    (etaleSiteComparison A).map
        ((CoGrothendieck.ι (etaleSimplicialSite A).totalPseudofunctor b).map g) =
      (degreeInclusion A.left b.unop).map ((realizeFunctor b.unop).map g) := by
  refine Hom.ext rfl ?_
  have h := (etaleTotalToSpacesιIso A b).hom.naturality g
  simp only [etaleTotalToSpacesιIso, CoGrothendieck.ιCompFunctorFrom] at h
  exact h

/-- The two restrictions of a sieve of the total site to `U_{n, spaces, étale}` agree: through
the component and the realization, and through the comparison and the degree. -/
theorem functorPushforward_functorPullback_ι_eq_etaleSiteComparison {U : EtaleTotal A}
    (R : Sieve U) :
    (R.functorPullback (CoGrothendieck.ι _ U.base)).functorPushforward
        (realizeFunctor (A := A) U.base.unop) =
      (R.functorPushforward (etaleSiteComparison A)).functorPullback
        (degreeInclusion A.left U.base.unop) := by
  apply le_antisymm
  · rintro W f ⟨y, g, h, hg, rfl⟩
    exact ⟨(CoGrothendieck.ι _ U.base).obj y, (CoGrothendieck.ι _ U.base).map g,
      (degreeInclusion A.left U.base.unop).map h, hg,
      (Functor.map_comp _ _ _).trans (congrArg (_ ≫ ·) (etaleSiteComparison_map_ι g).symm)⟩
  · rintro W f ⟨V', s, t, hs, ht⟩
    obtain ⟨W', ⟨e⟩⟩ : ∃ W' : EtaleComponent A U.base.unop,
        Nonempty ((realizeFunctor U.base.unop).obj W' ≅ W) :=
      ⟨_, ⟨realizeOfSpacesEtaleIso (A := A) W⟩⟩
    obtain ⟨τ, hτ⟩ := (etaleSiteComparison A).map_surjective
      (show (etaleSiteComparison A).obj ((CoGrothendieck.ι _ U.base).obj W') ⟶
        (etaleSiteComparison A).obj V' from (degreeInclusion A.left U.base.unop).map e.hom ≫ t)
    obtain ⟨g', hg'⟩ := (realizeFunctor (A := A) U.base.unop).map_surjective (X := W')
      (Y := EtaleTotal.obj A U) (e.hom ≫ f)
    have hι : (CoGrothendieck.ι _ U.base).map g' = τ ≫ s := by
      apply (etaleSiteComparison A).map_injective
      exact (etaleSiteComparison_map_ι g').trans
        ((congrArg (degreeInclusion A.left _).map hg').trans
          ((Functor.map_comp _ _ _).trans ((congrArg (_ ≫ ·) ht).trans
            ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hτ.symm).trans
              (Functor.map_comp _ _ _).symm)))))
    refine ⟨W', g', e.inv, ?_, ?_⟩
    · show R ((CoGrothendieck.ι _ U.base).map g')
      rw [hι]
      exact R.downward_closed hs τ
    · rw [hg', Iso.inv_hom_id_assoc]

/-- **The comparison is a dense subsite**: a sieve of the total site of the strict components
covers exactly when its image in `SimplicialSpacesEtaleSite` does. Hence it is an equivalence of
sites. -/
instance etaleSiteComparison_isDenseSubsite :
    (etaleSiteComparison A).IsDenseSubsite (etaleSimplicialSite A).totalTopology
      (topology A.left) where
  functorPushforward_mem_iff {U R} :=
    ((mem_topology_iff_functorPullback_degreeInclusion_mem
      (V := realize (A := A) (n := U.base.unop) (EtaleTotal.obj A U))
        (R.functorPushforward (etaleSiteComparison A))).trans
        ((Iff.of_eq (congrArg (· ∈ SpacesEtale.topology B S hS _
            (realize (A := A) (n := U.base.unop) (EtaleTotal.obj A U)))
          (functorPushforward_functorPullback_ι_eq_etaleSiteComparison R).symm)).trans
          (Functor.functorPushforward_mem_iff (precoverage (A := A) U.base.unop).toGrothendieck
            (SpacesEtale.topology B S hS _) (realizeFunctor U.base.unop)
            (S := R.functorPullback (CoGrothendieck.ι _ U.base))))).trans
      (CategoryTheory.SimplicialSite.mem_totalTopology_iff_simplicialSmallEtaleStrictTotal _ R).symm

variable (A)

/-- The comparison with `SimplicialSpacesEtaleSite` is a morphism of sites, being a dense
subsite. -/
theorem etaleSiteComparison_isMorphismOfSites :
    IsMorphismOfSites.{u + 1} (etaleSiteComparison A) (etaleSimplicialSite A).totalTopology
      (topology A.left) :=
  IsMorphismOfSites.ofIsDenseSubsite _

/-! ### The equivalence of ringed topoi -/

/-- **The structure sheaf of `U_étale` is the restriction of that of `U_{spaces, étale}`** along
the comparison: both are global regular functions on the realization. -/
def etaleStructureSheafIsoRestrict :
    etaleStructureSheaf A ≅ ((etaleSiteComparison A).sheafPushforwardContinuous CommRingCat.{u + 1}
      (etaleSimplicialSite A).totalTopology (topology A.left)).obj
        (SimplicialSpacesEtaleSite.structureSheaf A.left) :=
  Iso.refl _

/-- **The comparison of ringed topoi** `(Sh(U_{spaces, étale}), 𝒪) ⟶ (Sh(U_étale), 𝒪)`: the
morphism of topoi of the comparison of sites, whose direct image is restriction along the
comparison, with structure map the identification of the two structure sheaves. -/
def etaleSiteComparisonRingedToposHom :
    RingedToposHom (ringedTopos A.left)
      ((etaleSituation A).totalRingedTopos (etaleStructureSheaf A)) where
  toToposHom := (etaleSiteComparison_isMorphismOfSites A).morphismOfTopoi
  fSharp := (etaleStructureSheafIsoRestrict A).hom ≫
    (Stacks.Sheaves.ToposPullback.restrictionCommRingIso (etaleSimplicialSite A).totalTopology
      (topology A.left) (etaleSiteComparison A)
      (SimplicialSpacesEtaleSite.structureSheaf A.left)).inv

/-- The structure map of the comparison of ringed topoi is an isomorphism. -/
instance etaleSiteComparisonRingedToposHom_isIso_fSharp :
    IsIso (etaleSiteComparisonRingedToposHom A).fSharp :=
  Iso.isIso_hom ((etaleStructureSheafIsoRestrict A) ≪≫
    (Stacks.Sheaves.ToposPullback.restrictionCommRingIso (etaleSimplicialSite A).totalTopology
      (topology A.left) (etaleSiteComparison A)
      (SimplicialSpacesEtaleSite.structureSheaf A.left)).symm)

/-- The direct image of the comparison of ringed topoi is an equivalence of sheaf categories. -/
instance etaleSiteComparisonRingedToposHom_pushforward_isEquivalence :
    (etaleSiteComparisonRingedToposHom A).toToposHom.pushforward.IsEquivalence :=
  inferInstanceAs ((etaleSiteComparison A).sheafPushforwardContinuous (Type (u + 1))
    (etaleSimplicialSite A).totalTopology (topology A.left)).IsEquivalence

attribute [local instance] HasDerivedCategory.standard in
open Stacks.Cohomology.DerivedPullbackOfToposHom in
/-- **The derived pullback along the comparison of ringed topoi is an equivalence.** -/
theorem isEquivalence_derivedPullback_etaleSiteComparisonRingedToposHom :
    haveI := Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy
      (etaleSiteComparisonRingedToposHom A)
    (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback
      (etaleSiteComparisonRingedToposHom A)).IsEquivalence := by
  have := Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy
    (etaleSiteComparisonRingedToposHom A)
  exact isEquivalence_derivedPullback_of_isEquivalence_derivedPullbackOfEquivalence
    (etaleSiteComparisonRingedToposHom A)

end AlgebraicGeometry.Space

end
