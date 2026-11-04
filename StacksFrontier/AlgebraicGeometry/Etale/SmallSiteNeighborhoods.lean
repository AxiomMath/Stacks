module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
import StacksFrontier.AlgebraicGeometry.Size.FiniteType

/-!
# Moving étale neighbourhoods into the chosen small étale site

A scheme étale over `S` need not belong to a chosen big étale site: the site has a size
cutoff, and nothing bounds the size of an arbitrary étale `S`-scheme. Its affine opens,
however, always do, because an affine scheme étale over `S` has size at most that of `S`. So
every étale neighbourhood can be refined, at the point one cares about, to an object of the
chosen small étale site of `S`.

## Main results

* `AlgebraicGeometry.exists_smallEtale_affine_open_of_etale`: a point of a scheme étale over
  `S` has an affine open neighbourhood which is an object of the chosen small étale site of
  `S`, mapping into the scheme by an open immersion over `S`.
* `AlgebraicGeometry.exists_smallEtale_lift_of_etaleNeighborhood`: an étale neighbourhood of
  an ordinary point `x` of `S`, in the sense of Stacks 02LE, and a geometric point of `S`
  lying over `x` together produce an object of the chosen small étale site carrying a lift of
  the geometric point, with the lift sitting at the distinguished point of the neighbourhood.

## Implementation notes

The size bound is `AlgebraicGeometry.Scheme.size_le_of_locallyOfFiniteType`, which needs the
source to be quasi-compact; that is why an affine open has to be chosen first, and why
neither result can produce the given étale scheme itself. Once an affine open `Spec R` of the
étale scheme is chosen, `Spec R ⟶ S` is again étale, hence locally of finite type, so
`(Spec R).size ≤ S.size` and `Spec R` is contained in the site.

The lift of the geometric point is produced in two steps. Mathlib's
`AlgebraicGeometry.Scheme.exists_fac_of_etale_of_isSepClosed` lifts the geometric point
through the étale structure morphism of the neighbourhood to a morphism hitting the
prescribed distinguished point — an algebraically closed field being in particular separably
closed. That lift then factors through the chosen affine open by
`AlgebraicGeometry.IsOpenImmersion.lift`, because the source of a geometric point has a
single topological point, which the first step placed inside the affine open.

The second result is the bridge between the two notions of étale neighbourhood in this
library: `AlgebraicGeometry.EtaleNeighborhood` of Stacks 02LE, which carries a distinguished
point of the underlying space, and the objects of the small étale site equipped with a lift of
a geometric point, which is what `AlgebraicGeometry.geometricPointFiber` parametrizes and
what the stalk of Stacks 040R is a colimit over. Nothing here carries a Stacks tag; these are
the two refinement steps that the stalk constructions and the étale-local statements over a
geometric point share, and the first is the public form of the affine-refinement argument
which `StacksFrontier/AlgebraicGeometry/EtaleCohomology/GeometricPointFiber.lean` and
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/PullbackStalk/SitePoint.lean` so far keep
private for their own cofiltration proofs.

## References

* [Stacks Project, Tag 02LE](https://stacks.math.columbia.edu/tag/02LE)
* [Stacks Project, Tag 03PO](https://stacks.math.columbia.edu/tag/03PO)
* [Stacks Project, Tag 040R](https://stacks.math.columbia.edu/tag/040R)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Every point of a scheme étale over `S` lies in an affine open which is an object of the
chosen small étale site of `S`. The open immersion onto that affine open is a morphism over
`S`, the structure morphism of the site object being its composite with the given étale
morphism. -/
public theorem exists_smallEtale_affine_open_of_etale {Y : Scheme.{u}} (g : Y ⟶ S) [Etale g]
    (y : Y) :
    ∃ (V : SmallEtale B S hS) (j : (SmallEtale.toScheme B S hS).obj V ⟶ Y),
      IsAffine ((SmallEtale.toScheme B S hS).obj V) ∧ IsOpenImmersion j ∧
        B.inclusion.map V.obj.hom = j ≫ g ∧ y ∈ Set.range j.base := by
  obtain ⟨R, j, hjopen, hy, -⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (x := y) (U := ⊤) (by simp)
  have hjg : Etale (j ≫ g) := inferInstance
  have hR : B.Contains (Spec R) :=
    (Scheme.size_le_of_locallyOfFiniteType (j ≫ g)).trans_lt hS
  refine ⟨⟨Over.mk (ObjectProperty.homMk (j ≫ g) : B.obj (Spec R) hR ⟶ B.obj S hS), hjg⟩, j,
    ?_, hjopen, rfl, hy⟩
  exact inferInstanceAs (IsAffine (Spec R))

/-- An étale neighbourhood of an ordinary point `x` of `S`, in the sense of Stacks 02LE, can be
shrunk to an object of the chosen small étale site of `S` carrying a lift of any geometric
point of `S` lying over `x`, in such a way that the lift sits at the distinguished point of the
neighbourhood. -/
public theorem exists_smallEtale_lift_of_etaleNeighborhood {x : S} (s : GeometricPoint S)
    (hs : s.LiesOver x) (U : EtaleNeighborhood S x) :
    ∃ (V : SmallEtale B S hS) (p : (geometricPointFiber B S hS s).obj V)
      (j : (SmallEtale.toScheme B S hS).obj V ⟶ U.scheme),
      IsAffine ((SmallEtale.toScheme B S hS).obj V) ∧ IsOpenImmersion j ∧
        B.inclusion.map V.obj.hom = j ≫ U.toBase ∧ (p.1 ≫ j) default = U.point := by
  obtain ⟨l, hl, hld⟩ := Scheme.exists_fac_of_etale_of_isSepClosed U.toBase s.hom U.point
    (U.map_point.trans hs.symm)
  obtain ⟨V, j, haffine, hjopen, hstruct, hy⟩ :=
    exists_smallEtale_affine_open_of_etale B S hS U.toBase U.point
  have hrange : Set.range l.base ⊆ Set.range j.base := by
    rintro _ ⟨a, rfl⟩
    rw [Subsingleton.elim a default]
    exact hld ▸ hy
  have hfac : IsOpenImmersion.lift j l hrange ≫ j = l := IsOpenImmersion.lift_fac j l hrange
  refine ⟨V, ⟨IsOpenImmersion.lift j l hrange, ?_⟩, j, haffine, hjopen, hstruct, ?_⟩
  · rw [hstruct, ← Category.assoc, hfac, hl]
  · rw [hfac]
    exact hld

end AlgebraicGeometry

end
