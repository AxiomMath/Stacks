module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkIsomorphismCriterion
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BoundedCovering
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Exactness of abelian étale sheaves is tested on the stalks at geometric points

Let `B` be a big étale site containing a scheme `S`. A short complex of abelian sheaves on the
small étale site of `S` is exact exactly when, at every geometric point of `S`, the induced short
complex of stalks is exact. This is Stacks 03PU for abelian coefficients on the chosen small étale
site.

The two halves are of different natures. Exactness is preserved by the stalk functors because a
stalk is a filtered colimit, so the forward implication is a general fact about the fibre functor
of a point of a site. The converse needs that the stalk functors at the geometric points *jointly
detect* equalities of morphisms of sheaves: two morphisms with the same germ at every geometric
point agree on a covering sieve of every object, hence agree. That is proved here directly, from
the criterion that a sieve whose arrows are jointly surjective on points is covering, because the
coefficient category `AddCommGrpCat.{max (u + 1) v}` is not concrete over the universe `u` of the
points of the site and so Mathlib's conservative-family API is unavailable.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.jointlyFaithful_etaleStalkSheafFiber` — the stalk functors at the geometric
  points are jointly faithful on abelian sheaves on the small étale site.
* `AlgebraicGeometry.exact_iff_etaleStalk_exact` — a short complex of abelian sheaves on the small
  étale site is exact exactly when its complexes of geometric stalks are exact.

## Implementation notes

The stalk at a geometric point is literally the fibre of the point
`AlgebraicGeometry.geometricPointSitePoint` of the small étale site — this is
`AlgebraicGeometry.etaleStalk_eq_presheafFiber` — so no comparison between the two needs to be
carried, and the statement may be read either way.

The geometric point used to test a point of an étale neighbourhood is
`AlgebraicGeometry.geometricPointOfEtalePoint`, the algebraic closure of the residue field there
pushed down to `S`; this is why the family of geometric points indexing the test is a family of
geometric points of `S` and not of the neighbourhood.

## References

* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
* [Stacks Project, Tag 04FM](https://stacks.math.columbia.edu/tag/04FM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

section Exactness

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A sieve which every lift of every geometric point factors through is a covering sieve: the
geometric point attached to a point of an étale neighbourhood lifts tautologically to it, so the
arrows of the sieve are jointly surjective. -/
private theorem mem_topology_of_forall_geometricPointFiber_lift
    {X : SmallEtale B S hS} (R : Sieve X)
    (hR : ∀ (s : GeometricPoint S) (q : (geometricPointFiber B S hS s).obj X),
      ∃ (Y : SmallEtale B S hS) (g : Y ⟶ X), R g ∧
        ∃ q' : (geometricPointFiber B S hS s).obj Y,
          (geometricPointFiber B S hS s).map g q' = q) :
    R ∈ SmallEtale.topology B S hS X := by
  refine SmallEtale.mem_topology_of_jointlySurjective fun t => ?_
  obtain ⟨Y, g, hg, q', hq'⟩ := hR (geometricPointOfEtalePoint B S hS X t)
    (geometricPointOfEtalePointLift B S hS X t)
  refine ⟨Y, g, hg, q'.1.base default, ?_⟩
  have h1 : q'.1 ≫ (SmallEtale.toScheme B S hS).map g =
      (geometricPointOfEtalePointLift B S hS X t).1 := congrArg Subtype.val hq'
  have h2 : ((SmallEtale.toScheme B S hS).map g).base (q'.1.base default) =
      (geometricPointOfEtalePointLift B S hS X t).1.base default :=
    congrArg (fun m : (geometricPointOfEtalePoint B S hS X t).source ⟶ _ =>
      m.base (default : ↥(geometricPointOfEtalePoint B S hS X t).source)) h1
  exact h2.trans (geometricPointOfEtalePointLift_base B S hS X t)

/-- **Stacks 03PU.** The stalk functors at the geometric points of `S` are jointly faithful on
abelian sheaves on the small étale site of `S`: two morphisms of sheaves inducing the same map on
every stalk are equal.

Two morphisms with the same germ at every geometric point agree, over each object of the site, on
the sieve of arrows along which the two sections become equal; that sieve is covering because
every point of the object carries a geometric point lifting to it, and a sheaf is separated for a
covering sieve. -/
@[stacks 03PU "the geometric stalks are jointly faithful on abelian étale sheaves",
  sga "4 VIII 3.7" "special case"]
public theorem jointlyFaithful_etaleStalkSheafFiber :
    JointlyFaithful (fun s : GeometricPoint S =>
      (geometricPointSitePoint B S hS s).sheafFiber (A := AddCommGrpCat.{max (u + 1) v})) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{max (u + 1) v}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max (u + 1) v, max (u + 1) v, u, u} _
  refine ⟨fun {F G} {φ ψ} h => ?_⟩
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  ext a
  have hcov : Presheaf.equalizerSieve (φ.1.app U a) (ψ.1.app U a) ∈
      SmallEtale.topology B S hS U.unop := by
    refine mem_topology_of_forall_geometricPointFiber_lift B S hS _ fun s q => ?_
    have heq : (geometricPointSitePoint B S hS s).toPresheafFiber U.unop q G.obj
          (φ.1.app U a) =
        (geometricPointSitePoint B S hS s).toPresheafFiber U.unop q G.obj (ψ.1.app U a) := by
      have hh := ConcreteCategory.congr_hom (h s)
        ((geometricPointSitePoint B S hS s).toPresheafFiber U.unop q F.obj a)
      change (geometricPointSitePoint B S hS s).presheafFiber.map φ.1
          ((geometricPointSitePoint B S hS s).toPresheafFiber U.unop q F.obj a) =
        (geometricPointSitePoint B S hS s).presheafFiber.map ψ.1
          ((geometricPointSitePoint B S hS s).toPresheafFiber U.unop q F.obj a) at hh
      exact (((geometricPointSitePoint B S hS s).toPresheafFiber_naturality_apply
          φ.1 U.unop q a).symm.trans hh).trans
        ((geometricPointSitePoint B S hS s).toPresheafFiber_naturality_apply ψ.1 U.unop q a)
    obtain ⟨V, g, y, hfiber, hsection⟩ :=
      ((geometricPointSitePoint B S hS s).toPresheafFiber_eq_iff' U.unop q _ _).mp heq
    exact ⟨V, g, hsection, y, hfiber⟩
  exact G.property.isSeparated _ _ hcov _ _ fun _ _ hf => hf

/-- **Stacks 03PU.** A short complex of abelian sheaves on the small étale site of `S` is exact
exactly when its short complex of stalks at every geometric point of `S` is exact.

A stalk is a filtered colimit, so the stalk functors are exact and the condition is necessary;
it is sufficient because the stalk functors are jointly faithful, so a sheaf whose stalks all
vanish vanishes, applied to the homology of the complex. -/
@[stacks 03PU "exactness of abelian étale sheaves is checked on geometric stalks"]
public theorem exact_iff_etaleStalk_exact
    (T : ShortComplex (Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{max (u + 1) v})) :
    T.Exact ↔ ∀ s : GeometricPoint S,
      let Φ := sheafToPresheaf (SmallEtale.topology B S hS) AddCommGrpCat.{max (u + 1) v} ⋙
        etaleStalkPresheafFunctor B S hS s AddCommGrpCat.{max (u + 1) v}
      ∀ b : Φ.obj T.X₂,
        ((Φ.map T.g).hom b = 0 ↔ ∃ a : Φ.obj T.X₁, (Φ.map T.f).hom a = b) := by
  have : AB5OfSize.{u, u} AddCommGrpCat.{max (u + 1) v} :=
    AB5OfSize_of_univLE.{u, u, max (u + 1) v, max (u + 1) v} _
  let Ψ := fun s : GeometricPoint S =>
    (geometricPointSitePoint B S hS s).sheafFiber (A := AddCommGrpCat.{max (u + 1) v})
  have hex : T.Exact ↔ ∀ s : GeometricPoint S, (T.map (Ψ s)).Exact := by
    refine ⟨fun h s => h.map (Ψ s), fun h => ?_⟩
    rw [T.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
    apply (jointlyFaithful_etaleStalkSheafFiber.{u, v} B S hS).map_injective
    intro s
    have hz : IsZero ((Ψ s).obj T.homology) :=
      (Iso.isZero_iff (T.mapHomologyIso (Ψ s))).1
        ((T.map (Ψ s)).exact_iff_isZero_homology.1 (h s))
    simpa using hz.eq_of_src (𝟙 _) 0
  rw [hex]
  refine forall_congr' fun s => ?_
  rw [ShortComplex.ab_exact_iff]
  refine forall_congr' fun b => ⟨fun hb => ⟨hb, ?_⟩, fun hb => hb.1⟩
  rintro ⟨a, rfl⟩
  exact ConcreteCategory.congr_hom (T.map (Ψ s)).zero a

end Exactness

end AlgebraicGeometry

end
