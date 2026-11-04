module

public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineRefinement
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ModuleSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian

/-!
# Sections of a free module over a quasi-compact object, and over an affine étale chart

Let `R` be a sheaf of rings on a site and let `I` be a type.  Mathlib's
`SheafOfModules.free I` is the coproduct, taken in sheaves of `R`-modules, of `I` copies of the
unit module `R`.  Being a coproduct of *sheaves* it is the sheafification of the objectwise
direct sum, so its sections over an object `W` of the site are in general strictly larger than
`I →₀ R(W)`: a section is only *locally* a finite sum of the tautological sections.  Over a
**quasi-compact** object of the site the two agree, because a covering witnessing local
finiteness of the support can be refined by a finite one and the finitely many finite supports
have a finite union.

This file writes down the comparison map `I →₀ R(W) ⟶ (free I)(W)` and proves it bijective when
`W` is quasi-compact as an object of the site, and then specialises to the small étale site of
an algebraic space `F`, where the affine étale charts are quasi-compact objects.

## Main definitions

* `Stacks.Sites.freeSectionsMap` is the comparison `R(W)`-linear map
  `I →₀ R(W) ⟶ (free I)(W)` sending `Finsupp.single i x` to the image of `x` under the `i`-th
  coproduct injection `SheafOfModules.ιFree i`.
* `Stacks.Sites.freeSectionsIso` and
  `AlgebraicGeometry.Space.freeSectionsIsoOfIsAffine` are the resulting isomorphisms of modules.

## Main results

* `Stacks.Sites.bijective_freeSectionsMap` and `Stacks.Sites.isIso_freeSectionsMap`: over a
  quasi-compact object of the site the comparison map is bijective, so the sections of
  `SheafOfModules.free I` over it are the finitely supported `I`-indexed families of sections of
  the structure sheaf.
* `AlgebraicGeometry.Space.isQuasiCompactObject_of_isAffine`: an étale chart of `F` whose
  underlying scheme is affine is a quasi-compact object of the small étale site of `F`.
* `AlgebraicGeometry.Space.bijective_freeSectionsMap_of_isAffine`: the comparison map is
  bijective over an affine étale chart.

## Implementation notes

The quasi-compactness input is `AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_refinement`
and the colimit input is `Stacks.Sites.sheafOfModules_sections_preserves_coproducts`, the
module-coefficient half of Stacks 0935.  The latter is stated as preservation of coproducts by
the composite of `SheafOfModules.toSheaf` with the sections functor at the object, i.e. at the
level of the underlying *abelian groups* of the sections.  That is enough: the comparison map is
`R(W)`-linear by construction, so bijectivity may be checked after forgetting the module
structure, and it is checked by exhibiting the inverse as the map out of the colimiting cofan of
abelian groups whose `i`-th leg is `Finsupp.singleAddHom i`.

Affineness of `W` is necessary and not a convenience.  The objects of the small étale site of an
algebraic space include infinite disjoint unions of affine charts, over which a coproduct of
sheaves has strictly more sections than the direct sum of the sections: a section may have
infinite support, with a different finite support on each member of the disjoint union.  The
same phenomenon over the non-affine chart `Spec k[x, y] ∖ {(x, y)}` is what forces the
affineness hypotheses of `AlgebraicGeometry.Space.IsCartesianOnAffineCharts`; see the
implementation notes of `StacksFrontier/AlgebraicGeometry/Spaces/ChartSections.lean`.

The module universe is pinned to the universe `u` of the schemes, and this is forced by Mathlib
rather than by this repository's sheafification instances: `SheafOfModules.free` is declared only
for `I : Type u` and `R : Sheaf J RingCat.{u}`, with value in `SheafOfModules.{u} R`, so a free
module at an unrelated module universe does not exist to be talked about.

The two instances `AlgebraicGeometry.Space.smallEtaleRingedSite_hasWeakSheafify_addCommGrpCat`
and
`AlgebraicGeometry.Space.smallEtaleRingedSite_wEqualsLocallyBijective` exist for the reason
recorded in `StacksFrontier/AlgebraicGeometry/Spaces/RingedSite.lean`: the projections `.J` and `.C`
of `AlgebraicGeometry.Space.smallEtaleRingedSite` are not unfolded by instance search, so the
instances of `AlgebraicGeometry.Space.SmallEtale` do not fire at a goal phrased in terms of the
ringed site.  Their proofs are `change` followed by `infer_instance`.  They are the unsliced
companions of the two `..._over` instances already in that file, which `SheafOfModules.free`
needs in order to exist.

## References

* [Stacks Project, Tag 0935](https://stacks.math.columbia.edu/tag/0935)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

universe v' u' u

namespace Stacks.Sites

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The comparison map from the finitely supported `I`-indexed families of sections of `R` over
an object `X` to the sections of the free module `SheafOfModules.free I` over `X`: the
`R(X)`-linear map carrying `Finsupp.single i x` to the image of `x` under the `i`-th coproduct
injection `SheafOfModules.ιFree i`.

It is an isomorphism over a quasi-compact object of the site, by
`Stacks.Sites.isIso_freeSectionsMap`, but not in general. -/
noncomputable def freeSectionsMap (I : Type u) (X : Cᵒᵖ) :
    ModuleCat.of (R.obj.obj X) (I →₀ (R.obj.obj X)) ⟶ (free (R := R) I).val.obj X :=
  ModuleCat.ofHom (Finsupp.lsum ℕ (fun i => ((ιFree (R := R) i).val.app X).hom))

/-- The comparison map sends `Finsupp.single i x` to the image of `x` under the `i`-th
coproduct injection. -/
theorem freeSectionsMap_single (I : Type u) (X : Cᵒᵖ) (i : I) (x : R.obj.obj X) :
    (freeSectionsMap (R := R) I X).hom (Finsupp.single i x) =
      ((ιFree (R := R) i).val.app X).hom x :=
  Finsupp.lsum_single ℕ _ i x

/-- **The sections of a free module over a quasi-compact object of the site are the finitely
supported families of sections of the structure sheaf.**

A coproduct of sheaves of modules is the sheafification of the objectwise direct sum, so a
section of `SheafOfModules.free I` is only locally a finite sum of tautological sections; over a
quasi-compact object the covering witnessing that can be refined by a finite one, and the
finitely many finite supports have a finite union. -/
theorem bijective_freeSectionsMap (I : Type u) (W : C) (hW : J.IsQuasiCompactObject W) :
    Function.Bijective (freeSectionsMap (R := R) I (op W)).hom := by
  classical
  have hpres := sheafOfModules_sections_preserves_coproducts J R W hW I
  set G := SheafOfModules.toSheaf.{u} R ⋙ (sheafSections J AddCommGrpCat.{u}).obj (op W)
  have hcof : IsColimit (Cofan.mk (G.obj (free (R := R) I))
      (fun i => G.map (ιFree (R := R) i))) :=
    Cofan.isColimitMapCoconeEquiv G _ (freeCofan (R := R) I)
      (isColimitOfPreserves G (isColimitFreeCofan (R := R) I))
  let T : AddCommGrpCat.{u} := AddCommGrpCat.of (I →₀ (R.obj.obj (op W)))
  let ψ : G.obj (free (R := R) I) ⟶ T := Cofan.IsColimit.desc hcof
    (fun i => AddCommGrpCat.ofHom (Finsupp.singleAddHom (M := R.obj.obj (op W)) i))
  let φa : T ⟶ G.obj (free (R := R) I) :=
    AddCommGrpCat.ofHom ((freeSectionsMap (R := R) I (op W)).hom.toAddMonoidHom)
  have hfac (i : I) : G.map (ιFree (R := R) i) ≫ ψ =
      AddCommGrpCat.ofHom (Finsupp.singleAddHom (M := R.obj.obj (op W)) i) :=
    Cofan.IsColimit.fac hcof _ i
  have key (i : I) (x : R.obj.obj (op W)) :
      (G.map (ιFree (R := R) i)).hom x =
        (freeSectionsMap (R := R) I (op W)).hom (Finsupp.single i x) :=
    (freeSectionsMap_single I (op W) i x).symm
  have key2 (i : I) :
      AddCommGrpCat.ofHom (Finsupp.singleAddHom (M := R.obj.obj (op W)) i) ≫ φa
        = G.map (ιFree (R := R) i) := by
    ext x
    exact (key i x).symm
  have h1 : ψ ≫ φa = 𝟙 _ := by
    refine Cofan.IsColimit.hom_ext hcof _ _ (fun i => ?_)
    have hi : (Cofan.mk (G.obj (free (R := R) I))
        (fun i => G.map (ιFree (R := R) i))).inj i = G.map (ιFree (R := R) i) := rfl
    rw [hi, ← Category.assoc, hfac i]
    exact (key2 i).trans (Category.comp_id _).symm
  have h2 : φa ≫ ψ = 𝟙 T := AddCommGrpCat.hom_ext <| Finsupp.addHom_ext fun i x =>
    (congrArg ψ.hom (key i x).symm).trans
      (ConcreteCategory.congr_hom (hfac i) x)
  exact Function.bijective_iff_has_inverse.mpr
    ⟨ψ.hom, ConcreteCategory.congr_hom h2, ConcreteCategory.congr_hom h1⟩

/-- The comparison map of `Stacks.Sites.freeSectionsMap` is an isomorphism over a quasi-compact
object of the site. -/
theorem isIso_freeSectionsMap (I : Type u) (W : C) (hW : J.IsQuasiCompactObject W) :
    IsIso (freeSectionsMap (R := R) I (op W)) :=
  (ConcreteCategory.isIso_iff_bijective _).2 (bijective_freeSectionsMap I W hW)

/-- The sections of `SheafOfModules.free I` over a quasi-compact object `W` of the site,
identified with the finitely supported `I`-indexed families of sections of `R` over `W`. -/
noncomputable def freeSectionsIso (I : Type u) (W : C) (hW : J.IsQuasiCompactObject W) :
    ModuleCat.of (R.obj.obj (op W)) (I →₀ (R.obj.obj (op W))) ≅
      (free (R := R) I).val.obj (op W) :=
  haveI := isIso_freeSectionsMap (R := R) I W hW
  asIso (freeSectionsMap (R := R) I (op W))

end Stacks.Sites

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- Presheaves of abelian groups on the small étale ringed site of `F` have sheafification.

The content is `AlgebraicGeometry.Space.SmallEtale.instHasSheafify`; this restates it for the
projection `.J` of `AlgebraicGeometry.Space.smallEtaleRingedSite`, which instance search does not
unfold.  It is the unsliced companion of
`AlgebraicGeometry.Space.smallEtaleRingedSite_hasWeakSheafify_over`. -/
instance smallEtaleRingedSite_hasWeakSheafify_addCommGrpCat :
    HasWeakSheafify (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{u} := by
  change HasWeakSheafify (SmallEtale.topology B S hS F) AddCommGrpCat.{u}
  infer_instance

/-- **An étale chart of an algebraic space whose underlying scheme is affine is a quasi-compact
object of the small étale site.**

Quasi-compactness of an object of a site is Stacks 090H: every covering family of it is refined
by a covering family factoring through only finitely many of the original's members.  Here the
refinement is the finite affine one of
`AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_refinement`. -/
theorem isQuasiCompactObject_of_isAffine (W : SmallEtale B S hS F)
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W)) :
    (SmallEtale.topology B S hS F).IsQuasiCompactObject W := by
  classical
  intro 𝒰 h𝒰
  obtain ⟨ι, hι, V, f, -, hle, hcov⟩ :=
    SmallEtale.exists_finite_affine_refinement B S hS F W hW 𝒰.sieve₀ h𝒰
  let E₀ : PreZeroHypercover.{0} W := ⟨ι, V, f⟩
  let 𝒱 : PreZeroHypercover.{u + 1} W :=
    E₀.restrictIndex (Equiv.ulift.{u + 1, 0} (α := ι))
  have hsieve : 𝒱.sieve₀ = Sieve.ofArrows V f :=
    congrArg Sieve.generate (E₀.presieve₀_restrictIndex_equiv (Equiv.ulift.{u + 1, 0} (α := ι)))
  choose s α hα using fun i : 𝒱.I₀ =>
    (Sieve.mem_ofArrows_iff _ _ _).1 (hle _ (Sieve.ofArrows_mk V f i.down))
  refine ⟨𝒱, ⟨s, α, fun i => (hα i).symm⟩, ?_, ?_⟩
  · rwa [hsieve]
  · have : Finite 𝒱.I₀ := inferInstanceAs (Finite (ULift.{u + 1} ι))
    exact Set.toFinite _

/-- **The sections of a free `𝒪_F`-module over an affine étale chart of an algebraic space are
the finitely supported families of regular functions on the chart.**

This is the computation of `SheafOfModules.free I` on affine charts.  Mathlib characterises
`SheafOfModules.free` only by its universal property, and over a general étale chart of `F` the
statement is false: a coproduct of sheaves of modules is the sheafification of the objectwise
direct sum, and the objects of the small étale site of `F` include infinite disjoint unions of
affine charts, over which the two differ.  Affineness enters only through quasi-compactness of
the chart as an object of the site,
`AlgebraicGeometry.Space.isQuasiCompactObject_of_isAffine`. -/
theorem bijective_freeSectionsMap_of_isAffine (I : Type u)
    (W : (smallEtaleRingedSite B S hS F hF).C)
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W)) :
    Function.Bijective (Stacks.Sites.freeSectionsMap
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
      I (op W)).hom :=
  Stacks.Sites.bijective_freeSectionsMap I W (isQuasiCompactObject_of_isAffine B S hS F W hW)

/-- The sections of a free `𝒪_F`-module over an affine étale chart `W` of the algebraic
space `F`, identified with the finitely supported `I`-indexed families of elements of the ring
`𝒪_F(W)` of regular functions on the chart. -/
noncomputable def freeSectionsIsoOfIsAffine (I : Type u)
    (W : (smallEtaleRingedSite B S hS F hF).C)
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W)) :
    ModuleCat.of (chartRing B S hS F hF W) (I →₀ chartRing B S hS F hF W) ≅
      (free (R := (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O)) I).val.obj (op W) :=
  Stacks.Sites.freeSectionsIso I W (isQuasiCompactObject_of_isAffine B S hS F W hW)

end AlgebraicGeometry.Space

end
