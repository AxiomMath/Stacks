module

public import StacksFrontier.AlgebraicGeometry.Curves.NodeEtaleLocal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointSupport.Main
public import StacksFrontier.AlgebraicGeometry.Etale.DerivedLowerShriekQuasiFinite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Coefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sweep.EtaleStalkFunctor
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SliceEquivalence.Sheaves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.GlobalSectionsAtTerminal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.CohomologyOfALocalizedSite
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerived.DerivedDeltaFunctor

/-!
# An étale sheaf supported at closed points is acyclic over every quasi-compact object

Let `K` be a separably closed field, let `X` be a scheme locally of finite type over `K` and let
`F` be an abelian sheaf on the small étale site of `X` whose support consists of closed points.
For every object `V` of the small étale site of `X` whose underlying scheme is quasi-compact, the
higher cohomology of `F` over `V` vanishes. Cohomology over `V` is the right derived functor of
the sections functor `CategoryTheory.sheafSections` at `V`.

## Main definitions

* `AlgebraicGeometry.etaleStalkAbelianRestrictionIso`: the geometric stalk of the restriction of
  an abelian étale sheaf to an object `V` is the geometric stalk of the sheaf at the image
  geometric point.

## Main results

* `AlgebraicGeometry.abelianRestriction_preservesInjectiveObjects`: restriction of abelian étale
  sheaves to an object of the small étale site preserves injective sheaves.
* `AlgebraicGeometry.isZero_rightDerived_sections_of_subsingleton_sheafH_abelianRestriction`: if
  the cohomology of the restriction of `F` to the small étale site of `V` vanishes in degree `p`,
  then so does the `p`-th right derived functor of sections over `V` at `F`.
* `AlgebraicGeometry.supportSheaf_abelianRestriction_subset_closedPoints`: the support of a
  restriction consists of closed points as soon as the support of the sheaf does.
* `AlgebraicGeometry.isZero_rightDerived_sections_of_supportSheaf_subset_closedPoints`: for `F`
  supported at closed points and `V` a quasi-compact object of the small étale site of `X`, the
  right derived functors of sections over `V` vanish on `F` in positive degrees.

## References

* [Stacks Project, Tag 0F1F](https://stacks.math.columbia.edu/tag/0F1F)
* [Stacks Project, Tag 03S5](https://stacks.math.columbia.edu/tag/03S5)
* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

attribute [local instance] SmallEtale.isGrothendieckAbelian_sheaf_succ

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
  (V : SmallEtale B X hX)

/-- Restriction of abelian étale sheaves to an object of the small étale site preserves injective
sheaves. -/
public theorem abelianRestriction_preservesInjectiveObjects :
    (abelianRestriction B X hX V).PreservesInjectiveObjects := by
  have : PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback
      (smallEtalePostcompose B X hX V) AddCommGrpCat.{u + 1}
      (SmallEtale.topology B V.obj.left.1 V.obj.left.property)
      (SmallEtale.topology B X hX)) :=
    abelianExtensionByZero_preservesFiniteLimits B X hX V
  have : ((smallEtalePostcompose B X hX V).sheafPullback AddCommGrpCat.{u + 1}
      (SmallEtale.topology B V.obj.left.1 V.obj.left.property)
      (SmallEtale.topology B X hX)).PreservesMonomorphisms :=
    have : PreservesFiniteLimits ((smallEtalePostcompose B X hX V).sheafPullback
        AddCommGrpCat.{u + 1} (SmallEtale.topology B V.obj.left.1 V.obj.left.property)
        (SmallEtale.topology B X hX)) :=
      preservesFiniteLimits_of_natIso
        (Functor.sheafPullbackConstruction.sheafPullbackIso
          (smallEtalePostcompose B X hX V) AddCommGrpCat.{u + 1}
          (SmallEtale.topology B V.obj.left.1 V.obj.left.property)
          (SmallEtale.topology B X hX)).symm
    inferInstance
  open Stacks.Cohomology.SheafifiedHigherDirectImage in
  exact preservesInjectiveObjects_pushforwardOfContinuous
    (J := SmallEtale.topology B V.obj.left.1 V.obj.left.property)
    (K := SmallEtale.topology B X hX)
    AddCommGrpCat.{u + 1} (smallEtalePostcompose B X hX V)

/-- Let `F` be an abelian sheaf on the small étale site of `X` and `V` an object of that site. If
the `p`-th cohomology of the restriction of `F` over the small étale site of `V` vanishes, then
the `p`-th right derived functor of sections over `V` vanishes on `F`. -/
public theorem isZero_rightDerived_sections_of_subsingleton_sheafH_abelianRestriction
    (F : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}) (p : ℕ)
    (h : Subsingleton (Sheaf.H.{u + 1, u + 1} ((abelianRestriction B X hX V).obj F) p)) :
    IsZero ((((sheafSections (SmallEtale.topology B X hX)
      AddCommGrpCat.{u + 1}).obj (op V)).rightDerived p).obj F) := by
  have := abelianRestriction_preservesInjectiveObjects B X hX V
  have h1 : IsZero (((Sheaf.Γ (SmallEtale.topology B V.obj.left.1 V.obj.left.property)
      AddCommGrpCat.{u + 1}).rightDerived p).obj ((abelianRestriction B X hX V).obj F)) :=
    (Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{u, u, u + 1}
      _ _ p).1 h
  have h2 := (Stacks.Cohomology.CechDelta.rightDerivedIsoOfIso
    (Stacks.Cohomology.ΓNatIsoSectionsAtTerminal
      (SmallEtale.topology B V.obj.left.1 V.obj.left.property) AddCommGrpCat.{u + 1}
      (SmallEtale.finalIsTerminal B V.obj.left.1 V.obj.left.property)) p).app
      ((abelianRestriction B X hX V).obj F)
  have h3 := (Stacks.Cohomology.SheafifiedHigherDirectImage.pushforwardRightDerivedSectionsIso
    (J := SmallEtale.topology B V.obj.left.1 V.obj.left.property)
    (K := SmallEtale.topology B X hX)
    AddCommGrpCat.{u + 1} (smallEtalePostcompose B X hX V) p
    (SmallEtale.final B V.obj.left.1 V.obj.left.property)).app F
  exact (h1.of_iso h2.symm).of_iso h3.symm

/-- The geometric stalk at `p` of the restriction of `F` to an object `V` of the small étale site
is the geometric stalk of `F` at the image geometric point of `X`. -/
public def etaleStalkAbelianRestrictionIso (p : GeometricPoint V.obj.left.1)
    (F : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}) :
    etaleStalk B V.obj.left.1 V.obj.left.property p
        ((abelianRestriction B X hX V).obj F).obj ≅
      etaleStalk B X hX (p.map (B.inclusion.map V.obj.hom)) F.obj :=
  (etaleStalkPresheafFunctor B V.obj.left.1 V.obj.left.property p
      AddCommGrpCat.{u + 1}).mapIso
    ((sheafToPresheaf _ _).mapIso
      ((smallEtaleSheafPullbackIsoPostcompose B X hX V AddCommGrpCat.{u + 1}).app F).symm) ≪≫
  etaleStalkSmallEtalePullObjIso B V.obj.hom p AddCommGrpCat.{u + 1} F

/-- Let `X` be locally of finite type over a separably closed field `K` and `F` an abelian étale
sheaf on `X` whose support consists of closed points. Then the support of the restriction of `F`
to an object `V` of the small étale site consists of closed points. -/
public theorem supportSheaf_abelianRestriction_subset_closedPoints
    (K : Type u) [Field K] [IsSepClosed K] (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (F : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1})
    (hF : supportSheaf B X hX F ⊆ {x : X | IsClosed ({x} : Set X)}) :
    supportSheaf B V.obj.left.1 V.obj.left.property ((abelianRestriction B X hX V).obj F) ⊆
      {v : V.obj.left.1 | IsClosed ({v} : Set V.obj.left.1)} := by
  have : Etale (B.inclusion.map V.obj.hom) := V.property
  rintro v ⟨p, hp, hne⟩
  have h1 : ¬ IsZero (etaleStalk B V.obj.left.1 V.obj.left.property p
      ((abelianRestriction B X hX V).obj F).obj) := fun hz =>
    hne ((isZero_etaleStalk_ulift_iff B V.obj.left.1 V.obj.left.property
      ((abelianRestriction B X hX V).obj F) p).2 hz)
  have h2 : ¬ IsZero (etaleStalk B X hX (p.map (B.inclusion.map V.obj.hom)) F.obj) := fun hz =>
    h1 (hz.of_iso (etaleStalkAbelianRestrictionIso B X hX V p F))
  have h3 : (B.inclusion.map V.obj.hom).base v ∈ supportSheaf B X hX F := by
    refine ⟨p.map (B.inclusion.map V.obj.hom), ?_, fun hz => h2 ?_⟩
    · show (p.map (B.inclusion.map V.obj.hom)).hom default = _
      rw [← hp]; rfl
    · exact (isZero_etaleStalk_ulift_iff B X hX F (p.map (B.inclusion.map V.obj.hom))).1 hz
  exact (Stacks.Curves.isClosed_singleton_iff_of_etale f (B.inclusion.map V.obj.hom) v).1 (hF h3)

/-- **An abelian étale sheaf supported at closed points is acyclic over every quasi-compact
object of the small étale site.** Let `K` be separably closed, `X` locally of finite type over
`K`, `F` an abelian sheaf on the small étale site of `X` whose support consists of closed points,
and `V` an object of that site whose underlying scheme is quasi-compact. Then the right derived
functors of sections over `V` vanish on `F` in positive degrees. -/
public theorem isZero_rightDerived_sections_of_supportSheaf_subset_closedPoints
    (K : Type u) [Field K] [IsSepClosed K] (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (F : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1})
    (hF : supportSheaf B X hX F ⊆ {x : X | IsClosed ({x} : Set X)})
    (hV : CompactSpace V.obj.left.1) (p : ℕ) (hp : 0 < p) :
    IsZero ((((sheafSections (SmallEtale.topology B X hX)
      AddCommGrpCat.{u + 1}).obj (op V)).rightDerived p).obj F) := by
  have : Etale (B.inclusion.map V.obj.hom) := V.property
  have := hV
  exact isZero_rightDerived_sections_of_subsingleton_sheafH_abelianRestriction B X hX V F p
    ((subsingleton_sheafH_and_epi_counit_of_supportSheaf_subset_closedPoints B K
      V.obj.left (B.inclusion.map V.obj.hom ≫ f) ((abelianRestriction B X hX V).obj F)
      (supportSheaf_abelianRestriction_subset_closedPoints B X hX V K f F hF)).1 p hp)

end AlgebraicGeometry

end
