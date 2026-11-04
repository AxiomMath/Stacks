module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisDescentSheaf.FiberHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleTopos
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SchemesEtalePoint.Basic

/-!
# Galois descent for the fibres of a geometric point

Let `B` be a big étale site containing a scheme `S`, and let `s` be a geometric point of `S`.
For a set `M` the presheaf `U ↦ (geometricPointFiber B S hS s U → M)` on the small étale site
of `S` is a sheaf, and if a group `G` acts on the fibres of `s` naturally in `U` and also acts
on `M`, then the subpresheaf of equivariant maps is a sheaf as well.

This is the sheaf condition for the inverse of the stalk functor in [Stacks, Tag 03QT].  Over
a field `K` with absolute Galois group `G` at `s`, that inverse sends a continuous `G`-set `M`
to `U ↦ Hom_G(geometricPointFiber B (Spec K) hK s U, M)`, and
`AlgebraicGeometry.isSheaf_galoisEquivariantGeometricPointFiberHomPresheaf` says that this is
a sheaf.  Note that the inverse cannot be `M ↦ X` for an étale `K`-scheme `X` representing
`M`: the objects of `AlgebraicGeometry.SmallEtale` are cut below `B.cutoff`, so a continuous
Galois set of large cardinality is the fibre of no object of the site, and the sheaves of
`Type (max u v)` on `Spec K` are not all representable when `v > u`.

The argument is Galois descent in its set-theoretic form and it needs no decomposition of a
fibre product.  What it uses is that covering sieves act jointly surjectively on the fibres of
a geometric point — `AlgebraicGeometry.geometricPointFiber_jointly_surjective`, which rests on
the structure of schemes étale over a separably closed field — and that the pointed étale
neighbourhoods of `s` are cofiltered.  Both are packaged in
`AlgebraicGeometry.geometricPointSitePoint`, and the descent itself is
`Stacks.Sites.Point.isSheaf_fiberHomPresheaf`.

## Main definitions

* `AlgebraicGeometry.geometricPointFiberHomPresheaf` and
  `AlgebraicGeometry.geometricPointFiberHomSheaf` — the presheaf `U ↦ (fibre of s at U → M)`
  and the sheaf it defines.
* `AlgebraicGeometry.equivariantGeometricPointFiberHomPresheaf` and
  `AlgebraicGeometry.equivariantGeometricPointFiberHomSheaf` — their equivariant
  counterparts.
* `AlgebraicGeometry.continuousGSetSmul` — the action on the underlying set of a continuous
  set over a topological group.
* `AlgebraicGeometry.galoisEquivariantGeometricPointFiberHomSheaf` — the equivariant sheaf
  attached to a continuous set over the absolute Galois group of a geometric point of the
  spectrum of a field.

## Main results

* `AlgebraicGeometry.isSheaf_geometricPointFiberHomPresheaf` — the presheaf of maps out of the
  fibres of a geometric point is a sheaf on the small étale site.
* `AlgebraicGeometry.isSheaf_equivariantGeometricPointFiberHomPresheaf` — its equivariant
  subpresheaf is a sheaf.
* `AlgebraicGeometry.isSheaf_galoisEquivariantGeometricPointFiberHomPresheaf` — the sheaf
  condition for the inverse of the stalk functor of [Stacks, Tag 03QT], with the Galois action
  on the fibres supplied as an argument.

## Implementation notes

The action of a group on the fibres of `s` is taken as explicit data `ρ` together with its
naturality `hρ`, rather than through a typeclass, because the action of the absolute Galois
group on `geometricPointFiber` is not yet available: a Galois automorphism of the separable
closure of the residue field has to be extended to an automorphism of the algebraically closed
field of the geometric point, which is the surjectivity of
`Aut(κ(s̄)/κ(s)) → Gal(κ(s)^{sep}/κ(s))` asserted before [Stacks, Tag 03QT].  Everything
below is stated so that supplying that one action discharges the sheaf condition.

No declaration here carries the tag 03QT: that theorem is the equivalence between the small
étale topos of a field and continuous Galois sets, of which this is the sheaf condition for
one half.

## References

* [Stacks Project, Tag 03QT](https://stacks.math.columbia.edu/tag/03QT)
* [Stacks Project, Tag 04JL](https://stacks.math.columbia.edu/tag/04JL)
* [Stacks Project, Tag 040R](https://stacks.math.columbia.edu/tag/040R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-- The action of a topological group on the underlying set of a continuous `G`-set. -/
def continuousGSetSmul {G : Type u} [Group G] [TopologicalSpace G]
    (M : ContinuousGSet.{u, w} G) (σ : G) : M.obj.obj.V → M.obj.obj.V :=
  ConcreteCategory.hom (M.obj.obj.ρ σ)

section Plain

variable (M : Type max u v)

/-- The presheaf on the small étale site of `S` whose sections over `U` are the maps from the
lifts of a geometric point `s` to `U` into a fixed set. -/
def geometricPointFiberHomPresheaf : (SmallEtale B S hS)ᵒᵖ ⥤ Type max u v :=
  Stacks.Sites.Point.fiberHomPresheaf (geometricPointSitePoint B S hS s) M

/-- The sections of `geometricPointFiberHomPresheaf` over `U` are the maps from the fibre of `s`
at `U` to `M`. -/
@[simp]
theorem geometricPointFiberHomPresheaf_obj (U : SmallEtale B S hS) :
    (geometricPointFiberHomPresheaf.{u, v} B S hS s M).obj (op U) =
      ((geometricPointFiber B S hS s).obj U → M) :=
  rfl

/-- Restriction along `f` in `geometricPointFiberHomPresheaf` is precomposition with the induced
map of fibres. -/
@[simp]
theorem geometricPointFiberHomPresheaf_map_apply {U V : (SmallEtale B S hS)ᵒᵖ} (f : U ⟶ V)
    (g : (geometricPointFiberHomPresheaf.{u, v} B S hS s M).obj U)
    (p : (geometricPointFiber B S hS s).obj V.unop) :
    (geometricPointFiberHomPresheaf.{u, v} B S hS s M).map f g p =
      g ((geometricPointFiber B S hS s).map f.unop p) :=
  rfl

/-- **Galois descent for the fibres of a geometric point.**  The presheaf of maps from the
lifts of a geometric point into a fixed set is a sheaf on the small étale site. -/
theorem isSheaf_geometricPointFiberHomPresheaf :
    Presieve.IsSheaf (SmallEtale.topology B S hS)
      (geometricPointFiberHomPresheaf.{u, v} B S hS s M) :=
  Stacks.Sites.Point.isSheaf_fiberHomPresheaf (geometricPointSitePoint B S hS s) M

/-- The sheaf of maps from the lifts of a geometric point into a fixed set, as an object of
the small étale topos of `S`. -/
def geometricPointFiberHomSheaf : smallEtaleTopos.{u, max u v} B S hS :=
  ⟨geometricPointFiberHomPresheaf.{u, v} B S hS s M,
    (isSheaf_iff_isSheaf_of_type _ _).2 (isSheaf_geometricPointFiberHomPresheaf.{u, v} B S hS s M)⟩

/-- The underlying presheaf of `geometricPointFiberHomSheaf` is
`geometricPointFiberHomPresheaf`. -/
@[simp]
theorem geometricPointFiberHomSheaf_obj :
    (geometricPointFiberHomSheaf.{u, v} B S hS s M).obj =
      geometricPointFiberHomPresheaf.{u, v} B S hS s M :=
  rfl

end Plain

section Equivariant

variable {G : Type w}
  (ρ : G → ∀ ⦃U : SmallEtale B S hS⦄,
    (geometricPointFiber B S hS s).obj U → (geometricPointFiber B S hS s).obj U)
  (hρ : ∀ (σ : G) ⦃U V : SmallEtale B S hS⦄ (f : U ⟶ V)
    (p : (geometricPointFiber B S hS s).obj U),
    (geometricPointFiber B S hS s).map f (ρ σ p) = ρ σ ((geometricPointFiber B S hS s).map f p))
  {M : Type max u v} (μ : G → M → M)

/-- The subpresheaf of `AlgebraicGeometry.geometricPointFiberHomPresheaf` of those maps which
intertwine a natural action `ρ` on the lifts of the geometric point with an action `μ` on the
target. -/
def equivariantGeometricPointFiberHomPresheaf : (SmallEtale B S hS)ᵒᵖ ⥤ Type max u v :=
  Stacks.Sites.Point.equivariantFiberHomPresheaf (geometricPointSitePoint B S hS s) ρ hρ μ

/-- The sections of `equivariantGeometricPointFiberHomPresheaf` over `U` are the maps `g` from
the fibre of `s` at `U` to `M` with `g (ρ σ p) = μ σ (g p)` for all `σ` and `p`. -/
@[simp]
theorem equivariantGeometricPointFiberHomPresheaf_obj (U : SmallEtale B S hS) :
    (equivariantGeometricPointFiberHomPresheaf.{u, v} B S hS s ρ hρ μ).obj (op U) =
      {g : (geometricPointFiber B S hS s).obj U → M //
        ∀ (σ : G) (p : (geometricPointFiber B S hS s).obj U), g (ρ σ p) = μ σ (g p)} :=
  rfl

/-- **Galois descent for equivariant maps out of the fibres of a geometric point.**  The
presheaf of equivariant maps from the lifts of a geometric point into a set with an action is a
sheaf on the small étale site. -/
theorem isSheaf_equivariantGeometricPointFiberHomPresheaf :
    Presieve.IsSheaf (SmallEtale.topology B S hS)
      (equivariantGeometricPointFiberHomPresheaf.{u, v} B S hS s ρ hρ μ) :=
  Stacks.Sites.Point.isSheaf_equivariantFiberHomPresheaf
    (geometricPointSitePoint B S hS s) ρ hρ μ

/-- The sheaf of equivariant maps from the lifts of a geometric point into a set with an
action, as an object of the small étale topos of `S`. -/
def equivariantGeometricPointFiberHomSheaf : smallEtaleTopos.{u, max u v} B S hS :=
  ⟨equivariantGeometricPointFiberHomPresheaf.{u, v} B S hS s ρ hρ μ,
    (isSheaf_iff_isSheaf_of_type _ _).2
      (isSheaf_equivariantGeometricPointFiberHomPresheaf.{u, v} B S hS s ρ hρ μ)⟩

/-- The underlying presheaf of `equivariantGeometricPointFiberHomSheaf` is
`equivariantGeometricPointFiberHomPresheaf`. -/
@[simp]
theorem equivariantGeometricPointFiberHomSheaf_obj :
    (equivariantGeometricPointFiberHomSheaf.{u, v} B S hS s ρ hρ μ).obj =
      equivariantGeometricPointFiberHomPresheaf.{u, v} B S hS s ρ hρ μ :=
  rfl

end Equivariant

section Galois

variable (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (sbar : GeometricPoint (Spec (.of K)))
  (ρ : GeometricPoint.absoluteGaloisGroup sbar →
    ∀ ⦃U : SmallEtale B (Spec (.of K)) hK⦄,
      (geometricPointFiber B (Spec (.of K)) hK sbar).obj U →
        (geometricPointFiber B (Spec (.of K)) hK sbar).obj U)
  (hρ : ∀ (σ : GeometricPoint.absoluteGaloisGroup sbar)
    ⦃U V : SmallEtale B (Spec (.of K)) hK⦄ (f : U ⟶ V)
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U),
    (geometricPointFiber B (Spec (.of K)) hK sbar).map f (ρ σ p) =
      ρ σ ((geometricPointFiber B (Spec (.of K)) hK sbar).map f p))
  (M : ContinuousGSet.{u, max u v} (GeometricPoint.absoluteGaloisGroup sbar))

/-- **The sheaf condition for the inverse of the stalk functor of Stacks 03QT.**  Let `K` be a
field, `sbar` a geometric point of `Spec K` and `G` its absolute Galois group.  For a
continuous `G`-set `M`, the presheaf on the small étale site of `Spec K` whose sections over
`U` are the `G`-equivariant maps from the lifts of `sbar` to `U` into `M` is a sheaf.  The
`G`-action on the lifts is supplied as the argument `ρ`, together with its naturality `hρ`. -/
theorem isSheaf_galoisEquivariantGeometricPointFiberHomPresheaf :
    Presieve.IsSheaf (SmallEtale.topology B (Spec (.of K)) hK)
      (equivariantGeometricPointFiberHomPresheaf.{u, v} B (Spec (.of K)) hK sbar ρ hρ
        (continuousGSetSmul M)) :=
  isSheaf_equivariantGeometricPointFiberHomPresheaf.{u, v} B (Spec (.of K)) hK sbar ρ hρ _

/-- The sheaf on the small étale site of `Spec K` attached to a continuous set over the
absolute Galois group of a geometric point: its sections over `U` are the equivariant maps
from the lifts of the geometric point to `U`.  This is the value of the inverse of the stalk
functor of [Stacks, Tag 03QT], with the Galois action on the lifts supplied as `ρ`. -/
def galoisEquivariantGeometricPointFiberHomSheaf :
    smallEtaleTopos.{u, max u v} B (Spec (.of K)) hK :=
  equivariantGeometricPointFiberHomSheaf.{u, v} B (Spec (.of K)) hK sbar ρ hρ
    (continuousGSetSmul M)

end Galois

end AlgebraicGeometry

end
