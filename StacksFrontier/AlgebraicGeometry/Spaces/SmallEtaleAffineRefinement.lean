module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.ChosenEtaleSite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite affine refinements of coverings of the small étale site

Descent along a covering family on the small étale site of an algebraic space `X` is carried out
over the rings of global functions on the schemes underlying the members of the family, so it can
only start from a family which is *finite* and whose members are *affine*, and which is a
faithfully flat family of schemes.  This file produces such a family inside any covering sieve of
an étale chart whose underlying scheme is affine, and records the two structural consequences of
the construction: the affine étale charts over a chart form a covering family of it, and an étale
chart with affine underlying scheme has the finite subcovering property.

The three steps are the three steps of the corresponding fppf statement
`AlgebraicGeometry.FibredSite.exists_finite_affine_fppf_ofArrows_le`, but none of them is that
statement: the small étale site of an algebraic space is not the site a category fibred in
groupoids inherits from a big fppf site, its covering families are étale rather than flat, and the
projection to schemes is not fibred in groupoids.

*From a sieve to a family.*  The small étale precoverage is the chosen étale precoverage of
`Sch_κ` restricted along the projection taking a chart to its underlying scheme
(`AlgebraicGeometry.Space.SmallEtale.precoverage_eq_comap`), and the chosen étale families
contain the isomorphisms and are stable under base change and refinement, so a covering sieve
contains a covering family.

*Refining by affine charts.*  The affine opens of the scheme underlying a chart are again étale
charts (`AlgebraicGeometry.Space.openChart`), and they cover it, so each member of the family can
be replaced by its affine opens; the composite family is again étale because the chosen étale
precoverage is stable under refinement.

*Cutting the family down.*  An étale morphism is flat and locally of finite presentation, hence an
open map, so the images of the members form an open cover of the target; an affine scheme is
quasi-compact, so finitely many of them already cover, and the subfamily they index is again
jointly surjective with étale members.

## Main results

* `AlgebraicGeometry.Scheme.etalePrecoverage_hasIsos` and
  `AlgebraicGeometry.Scheme.etalePrecoverage_isStableUnderComposition`: the two closure
  properties of the étale precoverage of schemes which the passage from a covering sieve to a
  covering family needs.
* `AlgebraicGeometry.BigFppfSite.etalePrecoverage_eq_comap`: the chosen étale precoverage of a
  big fppf site is the étale precoverage of schemes restricted along its inclusion.
* `AlgebraicGeometry.Space.SmallEtale.mem_topology_iff`: **a sieve of the small étale site is
  covering exactly when it contains a covering family of charts.**
* `AlgebraicGeometry.Scheme.exists_finset_ofArrows_mem_etalePrecoverage`: **quasi-compactness cuts
  an étale covering family down to a finite subfamily.**
* `AlgebraicGeometry.Space.SmallEtale.exists_affine_etale_ofArrows` and
  `AlgebraicGeometry.Space.SmallEtale.exists_affine_ofArrows_over`: **every étale chart, and every
  object of a slice of the small étale site, carries a covering family by charts with affine
  underlying scheme.**
* `AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_etale_ofArrows_le` and
  `AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_etale_ofArrows_le_over`: **a covering
  sieve of an étale chart with affine underlying scheme, and of an object of a slice, contains a
  finite family of affine charts whose image in schemes is an étale, hence flat, covering
  family.**
* `AlgebraicGeometry.Space.SmallEtale.hasFiniteSubcovering` and
  `AlgebraicGeometry.Space.SmallEtale.hasFiniteSubcovering_over`: **an étale chart with affine
  underlying scheme, and an object of a slice with affine underlying scheme, has the finite
  subcovering property**, which is what makes the sections of a coproduct of copies of the
  structure sheaf computable there.

## Implementation notes

The two closure properties of `AlgebraicGeometry.Scheme.etalePrecoverage` are proved rather than
found by instance search because `AlgebraicGeometry.Scheme.etalePrecoverage` is a plain
definition, which instance search does not unfold, and because the parent projections of
`CategoryTheory.MorphismProperty.IsMultiplicative` are not instances, so the composition
property of étale morphisms has to be named.  They are stated as theorems, not instances, for the
same reason the fppf file states its own: an instance about a definition instance search cannot
unfold never fires.

The finite subfamily is produced as a `Finset` of the index type, as in
`AlgebraicGeometry.Scheme.exists_finset_ofArrows_mem_fppfPrecoverage`, and converted to a family
indexed by `Fin` through `Finset.equivFin`.

The refinement is cut down inside the étale precoverage and not inside the fppf one, although the
only use of the cut-down family is as a flat covering: a subfamily of an fppf family is fppf but
not étale, and the conclusion has to be a covering family of the *small étale* site as well as a
flat family of schemes.  The flat conclusion is then
`AlgebraicGeometry.Scheme.etalePrecoverage_le_fppfPrecoverage`.

Both finiteness statements are about an étale chart with affine underlying scheme; the morphism an
object of a slice sits over plays no part, exactly as in
`AlgebraicGeometry.FibredSite.hasFiniteSubcovering_over_of_isAffineOver`.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 03FF](https://stacks.math.columbia.edu/tag/03FF)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The precoverage of jointly surjective families of morphisms with a property stable under
composition is stable under composition.

This is stated for a variable morphism property on purpose.  At the fixed property
`AlgebraicGeometry.Etale` the instance of Mathlib behind it fails to apply, because unifying the
class-valued `AlgebraicGeometry.Etale` with the morphism-property argument of that instance is a
unification of two terms which are definitionally equal and differ in binder information. -/
private alias schemePrecoverage_isStableUnderComposition := schemePrecoverage_stableUnderComposition

/-- A family of morphisms of schemes is an étale covering family exactly when it is jointly
surjective with étale members.

This is `AlgebraicGeometry.Scheme.ofArrows_mem_precoverage_iff` at the étale morphism property.
It is named because rewriting with that lemma requires unfolding
`AlgebraicGeometry.Scheme.etalePrecoverage` first, and the unfolded term is not type-correct at
the transparency `rw` type-checks at: `AlgebraicGeometry.Etale` is a class, so its reading as a
morphism property differs from a morphism property in binder information only. -/
theorem Scheme.ofArrows_mem_etalePrecoverage_iff {T : Scheme.{u}} {I : Type*}
    {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ T} :
    Presieve.ofArrows X f ∈ Scheme.etalePrecoverage T ↔
      (∀ x, ∃ i, x ∈ Set.range (f i)) ∧ ∀ i, Etale (f i) :=
  Scheme.ofArrows_mem_precoverage_iff (P := @Etale)

/-- The étale precoverage of schemes contains the isomorphisms.

An isomorphism is an open immersion, hence étale, and it is surjective; this is the isomorphism
axiom of the étale pretopology. -/
theorem Scheme.etalePrecoverage_hasIsos : Scheme.etalePrecoverage.{u}.HasIsos :=
  ⟨fun {_ T} f _ => by
    show Presieve.singleton f ∈ Scheme.etalePretopology T
    exact Scheme.etalePretopology.has_isos f⟩

/-- The étale precoverage of schemes is stable under refinement by étale covering families:
étale morphisms compose, and a composite of jointly surjective families is jointly
surjective. -/
theorem Scheme.etalePrecoverage_isStableUnderComposition :
    Scheme.etalePrecoverage.{u}.IsStableUnderComposition := by
  have : MorphismProperty.IsStableUnderComposition (@Etale : MorphismProperty Scheme.{u}) :=
    (inferInstance : MorphismProperty.IsMultiplicative
      (@Etale : MorphismProperty Scheme.{u})).toIsStableUnderComposition
  unfold Scheme.etalePrecoverage
  exact schemePrecoverage_isStableUnderComposition _

/-- **The chosen étale precoverage of a big fppf site is the étale precoverage of schemes
restricted along its inclusion.**  The size bound on the index types of the chosen families
imposes nothing on the presieves they generate, because
`AlgebraicGeometry.BigFppfSite.presieve₀_mem_etalePrecoverage` replaces an arbitrary étale
covering family by a combinatorially equivalent chosen one. -/
theorem BigFppfSite.etalePrecoverage_eq_comap (B : BigFppfSite.{u}) :
    B.etalePrecoverage = Scheme.etalePrecoverage.comap B.inclusion := by
  ext X R
  rw [BigFppfSite.mem_chosenPrecoverage_iff, Precoverage.mem_comap_iff]
  constructor
  · rintro ⟨E, rfl, hE⟩
    simpa only [IsEtaleCovering, PreZeroHypercover.presieve₀_map] using hE.2
  · intro hR
    obtain ⟨E, rfl⟩ := R.exists_eq_preZeroHypercover
    exact B.presieve₀_mem_etalePrecoverage E
      (by rwa [IsEtaleCovering, PreZeroHypercover.presieve₀_map])

/-- The chosen étale covering families of a big fppf site contain the isomorphisms. -/
theorem BigFppfSite.hasIsos_etalePrecoverage (B : BigFppfSite.{u}) :
    B.etalePrecoverage.HasIsos :=
  have := Scheme.etalePrecoverage_hasIsos.{u}
  B.etalePrecoverage_eq_comap ▸ inferInstance

/-- The chosen étale covering families of a big fppf site are stable under refinement by chosen
étale covering families. -/
theorem BigFppfSite.isStableUnderComposition_etalePrecoverage (B : BigFppfSite.{u}) :
    B.etalePrecoverage.IsStableUnderComposition :=
  have := Scheme.etalePrecoverage_isStableUnderComposition.{u}
  B.etalePrecoverage_eq_comap ▸ inferInstance

namespace Scheme

/-- **Quasi-compactness cuts an étale covering family down to a finite subfamily.**  An étale
morphism is flat and locally of finite presentation, hence an open map, so the images of the
members of the family form an open cover of the target; a quasi-compact target is covered by
finitely many of them, and the subfamily they index is again jointly surjective with étale
members.

This is `AlgebraicGeometry.Scheme.exists_finset_ofArrows_mem_fppfPrecoverage` for the étale
precoverage.  The étale conclusion is what the small étale site needs: a subfamily of an fppf
family is fppf but need not be étale, so the fppf statement cannot be used and its conclusion
relaxed. -/
theorem exists_finset_ofArrows_mem_etalePrecoverage {T : Scheme.{u}} [CompactSpace T]
    {I : Type*} {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ T}
    (hf : Presieve.ofArrows X f ∈ Scheme.etalePrecoverage T) :
    ∃ s : Finset I, Presieve.ofArrows (fun i : {i // i ∈ s} ↦ X i.1) (fun i ↦ f i.1) ∈
      Scheme.etalePrecoverage T := by
  classical
  rw [Scheme.ofArrows_mem_etalePrecoverage_iff] at hf
  obtain ⟨hsurj, hprop⟩ := hf
  have hopen : ∀ i, IsOpen (Set.range (f i)) := fun i ↦ by
    have hfi : Etale (f i) := hprop i
    have hpr := (Etale.iff_flat_and_formallyUnramified).mp hfi
    have : Flat (f i) := hpr.1
    have : LocallyOfFinitePresentation (f i) := hpr.2.2
    exact (f i).isOpenMap.isOpen_range
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun i ↦ Set.range (f i)) hopen
    (fun x _ ↦ by obtain ⟨i, hi⟩ := hsurj x; exact Set.mem_iUnion.2 ⟨i, hi⟩)
  refine ⟨s, ?_⟩
  rw [Scheme.ofArrows_mem_etalePrecoverage_iff]
  refine ⟨fun x ↦ ?_, fun i ↦ hprop i.1⟩
  obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
  exact ⟨⟨i, hi⟩, hx⟩

/-- **Membership in the étale precoverage transports along a reindexing of the family.**  This is
`AlgebraicGeometry.Scheme.mem_fppfPrecoverage_of_equiv` for the étale precoverage, and it is what
turns the subfamily indexed by a `Finset` which
`AlgebraicGeometry.Scheme.exists_finset_ofArrows_mem_etalePrecoverage` produces into one indexed
by `Fin`. -/
theorem mem_etalePrecoverage_of_equiv {T : Scheme.{u}} {I J : Type*} (e : J ≃ I)
    {X : I → Scheme.{u}} {g : ∀ i, X i ⟶ T}
    (hg : Presieve.ofArrows X g ∈ Scheme.etalePrecoverage T) :
    Presieve.ofArrows (fun j ↦ X (e j)) (fun j ↦ g (e j)) ∈ Scheme.etalePrecoverage T := by
  rw [Scheme.ofArrows_mem_etalePrecoverage_iff] at hg ⊢
  refine ⟨fun z ↦ ?_, fun j ↦ hg.2 (e j)⟩
  obtain ⟨i, hi⟩ := hg.1 z
  exact ⟨e.symm i, by rwa [e.apply_symm_apply]⟩

end Scheme

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

namespace SmallEtale

/-- The covering families of the small étale site contain the isomorphisms. -/
theorem hasIsos_precoverage : (SmallEtale.precoverage B S hS F).HasIsos :=
  have := B.hasIsos_etalePrecoverage
  SmallEtale.precoverage_eq_comap B S hS F ▸ inferInstance

/-- The covering families of the small étale site are stable under refinement by covering
families. -/
theorem isStableUnderComposition_precoverage :
    (SmallEtale.precoverage B S hS F).IsStableUnderComposition :=
  have := B.isStableUnderComposition_etalePrecoverage
  SmallEtale.precoverage_eq_comap B S hS F ▸ inferInstance

/-- **A sieve of the small étale site is covering exactly when it contains a covering family of
charts.**  This is the pretopology-style description of
`AlgebraicGeometry.Space.SmallEtale.topology`, which is defined as the topology *generated* by
the covering families of charts; it holds because those families contain the isomorphisms, are
stable under base change — which is
`AlgebraicGeometry.Space.SmallEtale.precoverage_isStableUnderBaseChange` — and are stable under
refinement. -/
@[sga "4 II 1.4" "special case"]
theorem mem_topology_iff {X : SmallEtale B S hS F} {T : Sieve X} :
    T ∈ SmallEtale.topology B S hS F X ↔
      ∃ R ∈ SmallEtale.precoverage B S hS F X, R ≤ T.arrows :=
  have := hasIsos_precoverage B S hS F
  have := isStableUnderComposition_precoverage B S hS F
  Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition

/-- A family of charts over a chart whose family of underlying morphisms of schemes is an étale
covering family generates a covering sieve of the small étale site.

Unlike `AlgebraicGeometry.Space.SmallEtale.IsCovering` this takes no size bound on the index
type: by `AlgebraicGeometry.Space.SmallEtale.precoverage_eq_comap` and
`AlgebraicGeometry.BigFppfSite.etalePrecoverage_eq_comap` membership in the small étale
precoverage only depends on the presieve the family generates in schemes. -/
theorem ofArrows_mem_topology {W : SmallEtale B S hS F} {ι : Type*}
    (Y : ι → SmallEtale B S hS F) (a : ∀ j, Y j ⟶ W)
    (h : Presieve.ofArrows
        (fun j ↦ (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Y j)))
        (fun j ↦ (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map (a j))) ∈
      Scheme.etalePrecoverage
        ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W))) :
    Sieve.ofArrows Y a ∈ SmallEtale.topology B S hS F W := by
  refine Precoverage.generate_mem_toGrothendieck ?_
  rw [SmallEtale.precoverage_eq_comap, Precoverage.mem_comap_iff, Presieve.map_ofArrows,
    B.etalePrecoverage_eq_comap, Precoverage.mem_comap_iff, Presieve.map_ofArrows]
  exact h

/-- The affine opens of the scheme underlying an étale chart, read as étale charts over it, form
an étale covering family of schemes.

This is the geometric content of `AlgebraicGeometry.Space.SmallEtale.coversTop_affineCharts`
isolated from its conclusion about covering sieves: an affine open inclusion is an open
immersion, hence étale, and the affine opens of a scheme cover it. -/
theorem etalePrecoverage_openChartInclusion (W : SmallEtale B S hS F) :
    Presieve.ofArrows
        (fun O : ((BigFppfOver.toScheme B S hS).obj
            ((SmallEtale.toOver B S hS F).obj W)).affineOpens ↦
          (BigFppfOver.toScheme B S hS).obj
            ((SmallEtale.toOver B S hS F).obj (openChart B S hS F W O.1)))
        (fun O ↦ (BigFppfOver.toScheme B S hS).map
          ((SmallEtale.toOver B S hS F).map (openChartInclusion B S hS F W O.1))) ∈
      Scheme.etalePrecoverage
        ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W)) := by
  rw [Scheme.ofArrows_mem_etalePrecoverage_iff]
  refine ⟨fun x ↦ ?_, fun O ↦ etale_toScheme_toOver_map B S hS F
    (openChartInclusion B S hS F W O.1)⟩
  have hx : x ∈ (⊤ : ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj W)).Opens) := trivial
  rw [← iSup_affineOpens_eq_top] at hx
  obtain ⟨O, hO⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  refine ⟨O, ?_⟩
  obtain ⟨y, hy⟩ := (Scheme.Opens.range_ι (X := (BigFppfOver.toScheme B S hS).obj
    ((SmallEtale.toOver B S hS F).obj W)) (O : _)).ge hO
  refine ⟨y, ?_⟩
  rw [toScheme_map_toOver_map_openChartInclusion B S hS F W (O : _)]
  exact hy

/-- **Every étale chart carries a covering family by charts with affine underlying scheme.**  The
affine opens of the scheme underlying the chart are again étale charts of `F`
(`AlgebraicGeometry.Space.openChart`), they are affine, and they cover; the covering is recorded
both as a covering sieve of the small étale site and as an étale covering family of schemes,
which is what a refinement argument consumes. -/
theorem exists_affine_etale_ofArrows (W : SmallEtale B S hS F) :
    ∃ (I : Type (u + 1)) (Y : I → SmallEtale B S hS F) (a : ∀ j, Y j ⟶ W),
      (∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj (Y j)))) ∧
        Sieve.ofArrows Y a ∈ SmallEtale.topology B S hS F W ∧
        Presieve.ofArrows
            (fun j ↦ (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (Y j)))
            (fun j ↦ (BigFppfOver.toScheme B S hS).map
              ((SmallEtale.toOver B S hS F).map (a j))) ∈
          Scheme.etalePrecoverage
            ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj W)) := by
  have hpre := Scheme.mem_etalePrecoverage_of_equiv
    (Equiv.ulift.{u + 1} (α := ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj W)).affineOpens))
    (etalePrecoverage_openChartInclusion B S hS F W)
  refine ⟨ULift.{u + 1} ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj W)).affineOpens,
    fun O ↦ openChart B S hS F W O.down.1,
    fun O ↦ openChartInclusion B S hS F W O.down.1, fun O ↦ ?_,
    ofArrows_mem_topology B S hS F _ _ hpre, hpre⟩
  exact inferInstanceAs (IsAffine (O.down : _))

/-- **Every object of a slice of the small étale site carries a covering family by objects with
affine underlying scheme.**  The family of
`AlgebraicGeometry.Space.SmallEtale.exists_affine_etale_ofArrows` at the underlying chart, each
member equipped with the composite structure morphism. -/
theorem exists_affine_ofArrows_over (V : SmallEtale B S hS F) (W : Over V) :
    ∃ (I : Type (u + 1)) (Y : I → Over V) (a : ∀ j, Y j ⟶ W),
      (∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj (Y j).left))) ∧
        Sieve.ofArrows Y a ∈ ((SmallEtale.topology B S hS F).over V) W := by
  obtain ⟨I, y, φ, hyaff, hcov, -⟩ := exists_affine_etale_ofArrows B S hS F W.left
  refine ⟨I, fun j ↦ Over.mk (φ j ≫ W.hom), fun j ↦ Over.homMk (φ j), hyaff, ?_⟩
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact hcov

/-- **A covering sieve of an étale chart with affine underlying scheme contains a finite family of
charts with affine underlying scheme whose image in schemes is an étale covering family.**

The sieve contains a covering family of charts
(`AlgebraicGeometry.Space.SmallEtale.mem_topology_iff`); refining each of its members by the
affine opens of its underlying scheme
(`AlgebraicGeometry.Space.SmallEtale.exists_affine_etale_ofArrows`) keeps the composite family
inside the sieve, makes every underlying scheme affine, and keeps it étale because the étale
precoverage of schemes is stable under refinement; and the underlying scheme of an affine chart
is quasi-compact, so finitely many members of the composite family already cover
(`AlgebraicGeometry.Scheme.exists_finset_ofArrows_mem_etalePrecoverage`). -/
theorem exists_finite_affine_etale_ofArrows_le {x : SmallEtale B S hS F}
    (hx : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj x)))
    {Sv : Sieve x} (hSv : Sv ∈ SmallEtale.topology B S hS F x) :
    ∃ (n : ℕ) (z : Fin n → SmallEtale B S hS F) (φ : ∀ i, z i ⟶ x),
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj (z i)))) ∧ (∀ i, Sv (φ i)) ∧
        Sieve.ofArrows z φ ∈ SmallEtale.topology B S hS F x ∧
        Presieve.ofArrows
            (fun i ↦ (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (z i)))
            (fun i ↦ (BigFppfOver.toScheme B S hS).map
              ((SmallEtale.toOver B S hS F).map (φ i))) ∈
          Scheme.etalePrecoverage
            ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj x)) := by
  classical
  obtain ⟨R, hR, hRS⟩ := (mem_topology_iff B S hS F).1 hSv
  obtain ⟨E, rfl, hE⟩ := (SmallEtale.mem_precoverage_iff B S hS F).1 hR
  have hEet : Presieve.ofArrows
      (fun i ↦ (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj (E.X i)))
      (fun i ↦ (BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS F).map (E.f i))) ∈
      Scheme.etalePrecoverage
        ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj x)) := by
    have h := hE.2
    rwa [IsEtaleCovering, PreZeroHypercover.presieve₀_map, PreZeroHypercover.presieve₀,
      Presieve.map_ofArrows] at h
  choose Ji yi ψi haffi -- the affine refinement of each member
    hcovi hetalei using fun i ↦ exists_affine_etale_ofArrows B S hS F (E.X i)
  have hcomp : Presieve.ofArrows
      (fun k : Σ i, Ji i ↦ (BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj (yi k.1 k.2)))
      (fun k : Σ i, Ji i ↦ (BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS F).map (ψi k.1 k.2 ≫ E.f k.1))) ∈
      Scheme.etalePrecoverage
        ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj x)) := by
    have := Scheme.etalePrecoverage_isStableUnderComposition.{u}
    have h := Precoverage.comp_mem_coverings
      (J := Scheme.etalePrecoverage)
      (fun i ↦ (BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS F).map (E.f i))) hEet
      (fun i j ↦ (BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS F).map (ψi i j))) hetalei
    simpa only [Functor.map_comp] using h
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj x)) := have := hx; inferInstance
  obtain ⟨s, hs⟩ := Scheme.exists_finset_ofArrows_mem_etalePrecoverage hcomp
  have hfin := Scheme.mem_etalePrecoverage_of_equiv s.equivFin.symm hs
  simp only [Functor.map_comp] at hfin
  exact ⟨s.card, fun i ↦ yi (s.equivFin.symm i).1.1 (s.equivFin.symm i).1.2,
    fun i ↦ ψi (s.equivFin.symm i).1.1 (s.equivFin.symm i).1.2 ≫ E.f (s.equivFin.symm i).1.1,
    fun i ↦ haffi _ _, fun i ↦ Sv.downward_closed (hRS _ _ (Presieve.ofArrows.mk _)) _,
    ofArrows_mem_topology B S hS F _ _ hfin, hfin⟩

/-- **A covering sieve of an object of a slice of the small étale site whose underlying scheme is
affine contains a finite family of objects with affine underlying scheme whose image in schemes
is a flat covering family.**  This is
`AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_etale_ofArrows_le` transported to the
slice by the correspondence between covering sieves of `CategoryTheory.Over.mk f` and covering
sieves of its underlying chart, which changes neither the underlying schemes nor the morphisms
between them.

The flat conclusion is the one descent needs: the ring map a member of the family induces on
global functions is faithfully flat, because the member is flat and the family is jointly
surjective, so the Amitsur complex of that ring map computes the sections over the affine
object. -/
theorem exists_finite_affine_etale_ofArrows_le_over {x y : SmallEtale B S hS F} (f : y ⟶ x)
    (hy : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj y)))
    (S' : Sieve (Over.mk f))
    (hS' : S' ∈ ((SmallEtale.topology B S hS F).over x) (Over.mk f)) :
    ∃ (n : ℕ) (Y : Fin n → Over x) (a : ∀ i, Y i ⟶ Over.mk f),
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj (Y i).left))) ∧ (∀ i, S' (a i)) ∧
        Sieve.ofArrows Y a ∈ ((SmallEtale.topology B S hS F).over x) (Over.mk f) ∧
        Presieve.ofArrows
            (fun i ↦ (BigFppfOver.toScheme B S hS).obj
              ((SmallEtale.toOver B S hS F).obj (Y i).left))
            (fun i ↦ (BigFppfOver.toScheme B S hS).map
              ((SmallEtale.toOver B S hS F).map (a i).left)) ∈
          Scheme.fppfPrecoverage
            ((BigFppfOver.toScheme B S hS).obj
              ((SmallEtale.toOver B S hS F).obj (Over.mk f).left)) := by
  rw [GrothendieckTopology.mem_over_iff] at hS'
  obtain ⟨n, z, φ, haff, hmem, hcov, hetale⟩ :=
    exists_finite_affine_etale_ofArrows_le B S hS F hy hS'
  refine ⟨n, fun i ↦ Over.mk (φ i ≫ f), fun i ↦ Over.homMk (φ i), haff,
    fun i ↦ (Sieve.overEquiv_iff S' (φ i)).1 (hmem i), ?_, ?_⟩
  · rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact hcov
  · exact Scheme.etalePrecoverage_le_fppfPrecoverage _ hetale

/-- **An étale chart whose underlying scheme is affine has the finite subcovering property.**  A
covering sieve contains a covering family of charts, and
`AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_etale_ofArrows_le` cuts it down to a
finite one which is still covering. -/
theorem hasFiniteSubcovering (x : SmallEtale B S hS F)
    (hx : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj x))) :
    (SmallEtale.topology B S hS F).HasFiniteSubcovering x := by
  intro Sv hSv
  obtain ⟨n, z, φ, -, hmem, hcov, -⟩ :=
    exists_finite_affine_etale_ofArrows_le B S hS F hx hSv
  exact ⟨n, z, φ, hmem, hcov⟩

/-- **An object of a slice of the small étale site whose underlying scheme is affine has the
finite subcovering property.**  This is the shape in which the computation of the sections of a
coproduct of copies of the structure sheaf over an affine consumes it: the slice at the chart
over which a quasi-coherent module is presented, and in it an object whose underlying scheme is
affine.

The morphism the object sits over plays no part: an object of a slice has the property as soon as
its own underlying chart does. -/
theorem hasFiniteSubcovering_over {x : SmallEtale B S hS F} (W : Over x)
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj W.left))) :
    ((SmallEtale.topology B S hS F).over x).HasFiniteSubcovering W :=
  (SmallEtale.topology B S hS F).hasFiniteSubcovering_over W
    (hasFiniteSubcovering B S hS F W.left hW)

end SmallEtale

end Space

end AlgebraicGeometry

end
