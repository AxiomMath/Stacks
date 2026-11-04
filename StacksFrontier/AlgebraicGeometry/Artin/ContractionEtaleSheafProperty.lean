module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionEtaleDescentTransport

/-!
# Stacks 0GHG: the étale sheaf property of Artin's contraction functor

**Stacks 0GHG** says that in the situation of Stacks 0GH8 the functor `F` of Stacks 0GHA —
`AlgebraicGeometry.Artin.contractionFunctor` — satisfies the sheaf property for all étale
coverings of locally Noetherian schemes over `S`. This file proves it, modulo the two inputs
named in the attribute and discussed below. The statement itself, and the vocabulary it is
phrased in, are
`AlgebraicGeometry.Artin.ContractionSituation.SatisfiesEtaleSheafProperty` and its unfolding
`AlgebraicGeometry.Artin.ContractionSituation.satisfiesEtaleSheafProperty_iff`.

Let `{V_i ⟶ V}` be an étale covering of the locally Noetherian site over `S` and let
`t_i = (Z_i, u'_i, x̂_i)` be a compatible family of triples. The amalgamation is assembled
component by component.

1. *The closed subset.* `Z` is `AlgebraicGeometry.Artin.ContractionSituation.descendZ`, the
   complement of the union of the images of the `|V_i| ∖ Z_i`; it is closed because an étale
   morphism is open, and its inverse images are the `Z_i` because two points of two members
   with the same image in `|V|` come from one point of a field spectrum in the site, which is
   Noetherian and so an object to which the compatibility datum applies.
2. *The morphism `u' : V ∖ Z ⟶ U'`.* The family `{V_i ∖ Z_i ⟶ V ∖ Z}` of open subspaces
   generates an fppf covering sieve of sections of `V ∖ Z`, and `U'` is an fppf sheaf, so the
   `u'_i` glue.
3. *The morphism `x̂ : V_{/Z} ⟶ W`.* Likewise the completions `V_{i,/Z_i}` cover the
   completion subfunctor of `V` along `Z`, and the `x̂_i` glue there; the universal property of
   fppf sheafification then carries the glued morphism to one out of `V_{/Z}` itself.
4. *The two conditions.* That the glued `x̂` is adic, and that the glued pair `(u', x̂)` is
   compatible, are the two carried inputs.

In each of (2) and (3) the compatibility datum has to be fed a pair of morphisms out of an
*arbitrary* object of the big fppf site, whereas it is given only over locally Noetherian
objects. The overlaps `V_i ×_V V_j` bridge that gap: they are objects of the locally
Noetherian site, because the second projection is a base change of an étale morphism, and
inside the big fppf site they are the fibre products, so every such pair factors through one
of them.

Uniqueness, `AlgebraicGeometry.Artin.ContractionSituation.eq_of_mapTriple_eq`, needs neither
carried input and no compatibility hypothesis at all.

## Main definitions

* `AlgebraicGeometry.Artin.ContractionSituation.CompatibilityIsLocalOnBase` and
  `AlgebraicGeometry.Artin.ContractionSituation.AdicIsLocalOnBase`: the two carried inputs.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.eq_of_mapTriple_eq`: the uniqueness half of
  Stacks 0GHG, proved outright.
* `AlgebraicGeometry.Artin.ContractionSituation.exists_mapTriple_eq`: the existence half.
* `AlgebraicGeometry.Artin.ContractionSituation.satisfiesEtaleSheafProperty`: **Stacks
  0GHG**.

## What is assumed

Two things, both named in the attribute on
`AlgebraicGeometry.Artin.ContractionSituation.satisfiesEtaleSheafProperty` and both stated
for an arbitrary situation of Stacks 0GH8, an arbitrary covering family of the big fppf site
over `S` and an arbitrary candidate datum.

* `AlgebraicGeometry.Artin.ContractionSituation.CompatibilityIsLocalOnBase`, that the
  compatibility condition of Stacks 0GHA may be checked after pulling back along a covering
  family. This is the form in which **Stacks 0ADV**, étale descent for algebraic spaces,
  enters the source's argument: a witness over `V` is obtained by glueing the algebraic spaces
  `V'_i` and the morphisms `p_i`, `j_i`, `x̂'_i`, `x'_i` of the witnesses over the `V_i` out of
  a descent datum, whose comparison isomorphisms over the overlaps come from the uniqueness
  part of the main theorem on dilatations. This library has neither Stacks 0ADV — it has
  `@[stacks 04TR]` for sheaves on an abstract site and nothing for algebraic spaces — nor that
  uniqueness statement.
* `AlgebraicGeometry.Artin.ContractionSituation.AdicIsLocalOnBase`, that adicness may be
  checked after pulling back along a covering family. Stacks 0APY and Stacks 0APV, the two
  facts about adicness that the construction of `F` uses, yield adicness of a *composite*
  and never of a factor, so this does not follow from them.

Neither mentions the étale site of locally Noetherian schemes, the family of triples, or the
existence of an amalgamation: each is a statement about one already-given datum over the base
of an arbitrary covering family. The source's proof of Stacks 0GHG is omitted — the hint is
only that "morphisms may be defined étale locally" — so neither is a named citation of it.

Nothing else is assumed: the functor `F` of Stacks 0GHA is itself unconditional.

## References

* [Stacks Project, Tag 0ADV](https://stacks.math.columbia.edu/tag/0ADV)
* [Stacks Project, Tag 0AMC](https://stacks.math.columbia.edu/tag/0AMC)
* [Stacks Project, Tag 0AQ2](https://stacks.math.columbia.edu/tag/0AQ2)
* [Stacks Project, Tag 0GE1](https://stacks.math.columbia.edu/tag/0GE1)
* [Stacks Project, Tag 0GE4](https://stacks.math.columbia.edu/tag/0GE4)
* [Stacks Project, Tag 0GH8](https://stacks.math.columbia.edu/tag/0GH8)
* [Stacks Project, Tag 0GHA](https://stacks.math.columbia.edu/tag/0GHA)
* [Stacks Project, Tag 0GHG](https://stacks.math.columbia.edu/tag/0GHG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace Artin

attribute [local instance] Space.pointTopology

namespace ContractionSituation

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The two carried inputs -/

/-- **Stacks 0ADV, carried: the compatibility condition is local on the base.** Let `c` be any
situation of Stacks 0GH8, let `{V_i ⟶ V}` be any family of morphisms of the big fppf site over
`S` generating a covering sieve, and let `Z`, `u' : V ∖ Z ⟶ U'` and `x̂ : V_{/Z} ⟶ W` be any
candidate second and third components of a triple over `V`. If the restriction of `(u', x̂)` to
each `V_i` is compatible, then `(u', x̂)` is compatible.

This is a statement about *one given* pair `(u', x̂)` over `V`: it asserts that the condition of
`AlgebraicGeometry.Artin.ContractionSituation.CompatibilityWitness` may be checked after
pulling back along a covering family. It asserts nothing about the existence of `Z`, `u'` or
`x̂`, and it mentions no particular situation, family or covering: it is an assertion about
every situation and every covering family of the big fppf site at once.

It is the form in which **Stacks 0ADV**, étale descent for algebraic spaces, is used in the
proof of Stacks 0GHG: a witness over `V` is obtained by glueing the algebraic spaces `V'_i` and
the morphisms `p_i`, `j_i`, `x̂'_i`, `x'_i` of the witnesses over the `V_i` out of a descent
datum, the comparison isomorphisms over the overlaps being supplied by the uniqueness part of
the main theorem on dilatations. Neither Stacks 0ADV nor that uniqueness statement is available
in this library, and the source's proof of Stacks 0GHG is omitted, so neither is a named
citation of it. -/
def CompatibilityIsLocalOnBase : Prop :=
  ∀ (c : ContractionSituation B S hS) {V : BigFppfOver B S hS} {I : Type (u + 1)}
    (Vi : I → BigFppfOver B S hS) (f : ∀ i, Vi i ⟶ V),
    Sieve.ofArrows Vi f ∈ BigFppfOver.topology B S hS V →
    ∀ (Z : Set (Space.points B S hS (yoneda.obj V)))
      (u : (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).toFunctor ⟶ c.U'.toFunctor)
      (xhat : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ c.W),
      (∀ i, Nonempty (CompatibilityWitness c (Vi i)
        (Space.pointsMap B S hS (yoneda.obj (Vi i)) (yoneda.map (f i)) ⁻¹' Z)
        (Space.openSubspaceOfPointsRestrict B S hS (yoneda.map (f i)) _ Zᶜ
          (fun _ hz => hz) ≫ u)
        (Space.completionSheafRestrict B S hS (yoneda.map (f i)) _ Z
          (fun _ hz => hz) ≫ xhat))) →
      Nonempty (CompatibilityWitness c V Z u xhat)

/-- **Carried: adicness is local on the base.** Let `{V_i ⟶ V}` be any family of morphisms of
the big fppf site over `S` generating a covering sieve, let `Z` be any set of points of `V`,
let `W` be any fppf sheaf of `Type (u + 1)` over `S` and let `x̂ : V_{/Z} ⟶ W` be any morphism.
If the restriction of `x̂` to each completion `V_{i,/Z_i}` is adic, then `x̂` is adic.

The library supplies only that a composition of morphisms representable by algebraic spaces
is one (Stacks 0APY) and that a completion morphism along an inverse image is one (Stacks
0APV); from those two one can conclude that a composite is adic, never that a *factor* is, so
this is a genuinely new assumption. It is the standard fact that adicness of a
morphism of formal algebraic spaces may be checked locally on the base, and it is a statement
about *one given* morphism `x̂`: it mentions no particular family, no triple and no situation of
Stacks 0GH8 at all. The source's proof of Stacks 0GHG is omitted, so it is not a named citation
of it. -/
def AdicIsLocalOnBase : Prop :=
  ∀ {V : BigFppfOver B S hS} {I : Type (u + 1)} (Vi : I → BigFppfOver B S hS)
    (f : ∀ i, Vi i ⟶ V),
    Sieve.ofArrows Vi f ∈ BigFppfOver.topology B S hS V →
    ∀ (Z : Set (Space.points B S hS (yoneda.obj V))) (W : FormalSpace.FppfSheaf B S hS)
      (xhat : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ W),
      (∀ i, Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (Space.completionSheafRestrict B S hS (yoneda.map (f i))
          (Space.pointsMap B S hS (yoneda.obj (Vi i)) (yoneda.map (f i)) ⁻¹' Z) Z
          (fun _ hz => hz) ≫ xhat).hom) →
      Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS xhat.hom

/-! ### Separatedness: a triple is determined by its pullbacks -/

/-- The members of an étale covering of the locally Noetherian site generate a covering sieve of
the big fppf site. -/
private theorem ofArrows_mem_topology_of_isEtaleCovering
    {E : Covering (LocallyNoetherianOver B S hS)}
    (hE : LocallyNoetherianOver.IsEtaleCovering B S hS E) :
    Sieve.ofArrows (fun i => (E.2.X i).obj) (fun i => (E.2.f i).hom) ∈
      BigFppfOver.topology B S hS E.1.obj :=
  LocallyNoetherianOver.ofArrows_mem_topology_of_isCovering B S hS
    (LocallyNoetherianOver.isCovering_of_isEtaleCovering B S hS hE)

/-- **A section of `F` is determined étale locally.** Two triples over the base of an étale
covering family of the locally Noetherian site whose pullbacks to the members agree are equal.

This is the uniqueness half of Stacks 0GHG, and it needs none of the carried inputs: the first
components agree by joint surjectivity
(`AlgebraicGeometry.Artin.ContractionSituation.Z_eq_of_mapTriple_eq`), and then the second and
third agree because a morphism out of an open subspace, resp. out of a completion, into an fppf
sheaf is determined by its restrictions. -/
theorem eq_of_mapTriple_eq {c : ContractionSituation B S hS}
    {E : Covering (LocallyNoetherianOver B S hS)}
    (hE : LocallyNoetherianOver.IsEtaleCovering B S hS E) {s s' : Triple c E.1.obj}
    (h : ∀ i, mapTriple c (E.2.f i).hom s = mapTriple c (E.2.f i).hom s') : s = s' := by
  have hcov := ofArrows_mem_topology_of_isEtaleCovering B S hS hE
  obtain ⟨Z, hcZ, u, x, a, w⟩ := s
  obtain ⟨Z', hcZ', u', x', a', w'⟩ := s'
  have hZ : Z = Z' := Z_eq_of_mapTriple_eq hE h
  subst hZ
  have hu : ∀ i, Space.openSubspaceOfPointsRestrict B S hS (yoneda.map (E.2.f i).hom)
        (Space.pointsMap B S hS (yoneda.obj (E.2.X i).obj)
          (yoneda.map (E.2.f i).hom) ⁻¹' Z)ᶜ Zᶜ (fun _ hz => hz) ≫ u =
      Space.openSubspaceOfPointsRestrict B S hS (yoneda.map (E.2.f i).hom)
        (Space.pointsMap B S hS (yoneda.obj (E.2.X i).obj)
          (yoneda.map (E.2.f i).hom) ⁻¹' Z)ᶜ Zᶜ (fun _ hz => hz) ≫ u' :=
    fun i => u_restrict_eq_of_mapTriple_eq c (E.2.f i).hom (E.2.f i).hom _ _ (h i) _ rfl
      (fun _ hz => hz) (fun _ hz => hz)
  have hx : ∀ i, Space.completionSheafRestrict B S hS (yoneda.map (E.2.f i).hom)
        (Space.pointsMap B S hS (yoneda.obj (E.2.X i).obj)
          (yoneda.map (E.2.f i).hom) ⁻¹' Z) Z (fun _ hz => hz) ≫ x =
      Space.completionSheafRestrict B S hS (yoneda.map (E.2.f i).hom)
        (Space.pointsMap B S hS (yoneda.obj (E.2.X i).obj)
          (yoneda.map (E.2.f i).hom) ⁻¹' Z) Z (fun _ hz => hz) ≫ x' :=
    fun i => xhat_restrict_eq_of_mapTriple_eq c (E.2.f i).hom (E.2.f i).hom _ _ (h i) _ rfl
      (fun _ hz => hz) (fun _ hz => hz)
  refine Triple.mk_congr rfl (heq_of_eq ?_) (heq_of_eq ?_)
  · exact Space.hom_ext_openSubspaceOfPoints B S hS (fun i => (E.2.X i).obj)
      (fun i => (E.2.f i).hom) hcov Zᶜ
      (fun i => (Space.pointsMap B S hS (yoneda.obj (E.2.X i).obj)
        (yoneda.map (E.2.f i).hom) ⁻¹' Z)ᶜ) (fun _ => Set.preimage_compl.symm)
      c.isOpenSubspace_U'.1.isSheaf u u' hu
  · exact Space.hom_ext_completionSheaf B S hS (fun i => (E.2.X i).obj)
      (fun i => (E.2.f i).hom) hcov Z
      (fun i => Space.pointsMap B S hS (yoneda.obj (E.2.X i).obj)
        (yoneda.map (E.2.f i).hom) ⁻¹' Z) (fun _ => rfl) x x' hx

/-! ### The amalgamation: existence -/

/-- **The existence half of Stacks 0GHG.** A compatible family of triples on an étale covering
family of the locally Noetherian site over `S` has an amalgamation: the closed subset is the
descended one of `AlgebraicGeometry.Artin.ContractionSituation.descendZ`, and the second and
third components are glued from the given ones. The two carried inputs supply the adicness of
the glued third component and the compatibility of the glued pair; everything else is
proved. -/
theorem exists_mapTriple_eq (c : ContractionSituation B S hS)
    (h0ADV : CompatibilityIsLocalOnBase B S hS) (hadic : AdicIsLocalOnBase B S hS)
    {E : Covering (LocallyNoetherianOver B S hS)}
    (hE : LocallyNoetherianOver.IsEtaleCovering B S hS E)
    (t : (i : E.2.I₀) → Triple c (E.2.X i).obj)
    (ht : ∀ (i j : E.2.I₀) (Y : LocallyNoetherianOver B S hS) (gi : Y ⟶ E.2.X i)
      (gj : Y ⟶ E.2.X j), gi ≫ E.2.f i = gj ≫ E.2.f j →
        mapTriple c gi.hom (t i) = mapTriple c gj.hom (t j)) :
    ∃ s : Triple c E.1.obj, ∀ i, mapTriple c (E.2.f i).hom s = t i := by
  have hetale : ∀ i, Etale ((BigFppfOver.toScheme B S hS).map (E.2.f i).hom) := fun i =>
    LocallyNoetherianOver.etale_of_isEtaleCovering B S hS hE i
  have hcov := ofArrows_mem_topology_of_isEtaleCovering B S hS hE
  have hpre : ∀ i, Space.pointsMap B S hS (yoneda.obj (E.2.X i).obj)
      (yoneda.map (E.2.f i).hom) ⁻¹' descendZ c t = (t i).Z :=
    fun i => pointsMap_preimage_descendZ c t ht i
  have hZi : ∀ i, (t i).Z = Space.pointsMap B S hS (yoneda.obj (E.2.X i).obj)
      (yoneda.map (E.2.f i).hom) ⁻¹' descendZ c t := fun i => (hpre i).symm
  have hWi : ∀ i, ((t i).Z)ᶜ = Space.pointsMap B S hS (yoneda.obj (E.2.X i).obj)
      (yoneda.map (E.2.f i).hom) ⁻¹' (descendZ c t)ᶜ := fun i => by
    rw [Set.preimage_compl, hpre i]
  have htij : ∀ i j, mapTriple c
        (LocallyNoetherianOver.overlapFst B S hS (E.2.f i) (E.2.f j) (hetale i)).hom (t i) =
      mapTriple c
        (LocallyNoetherianOver.overlapSnd B S hS (E.2.f i) (E.2.f j) (hetale i)).hom (t j) :=
    fun i j => ht i j _ _ _ (LocallyNoetherianOver.overlapFst_comp_f B S hS _ _ _)
  have hZij : ∀ i j, Space.pointsMap B S hS
        (yoneda.obj (LocallyNoetherianOver.overlap B S hS (E.2.f i) (E.2.f j) (hetale i)).obj)
        (yoneda.map (LocallyNoetherianOver.overlapFst B S hS (E.2.f i) (E.2.f j)
          (hetale i)).hom) ⁻¹' (t i).Z =
      Space.pointsMap B S hS
        (yoneda.obj (LocallyNoetherianOver.overlap B S hS (E.2.f i) (E.2.f j) (hetale i)).obj)
        (yoneda.map (LocallyNoetherianOver.overlapSnd B S hS (E.2.f i) (E.2.f j)
          (hetale i)).hom) ⁻¹' (t j).Z := fun i j => congrArg Triple.Z (htij i j)
  have hWij₂ : ∀ i j, (Space.pointsMap B S hS
        (yoneda.obj (LocallyNoetherianOver.overlap B S hS (E.2.f i) (E.2.f j) (hetale i)).obj)
        (yoneda.map (LocallyNoetherianOver.overlapFst B S hS (E.2.f i) (E.2.f j)
          (hetale i)).hom) ⁻¹' (t i).Z)ᶜ =
      Space.pointsMap B S hS
        (yoneda.obj (LocallyNoetherianOver.overlap B S hS (E.2.f i) (E.2.f j) (hetale i)).obj)
        (yoneda.map (LocallyNoetherianOver.overlapSnd B S hS (E.2.f i) (E.2.f j)
          (hetale i)).hom) ⁻¹' ((t j).Z)ᶜ := fun i j => by
    rw [Set.preimage_compl, hZij i j]
  have hcompatU := Space.compatible_of_overlap_openSubspaceOfPoints B S hS
    (fun i => (E.2.X i).obj) (fun i => (E.2.f i).hom) (descendZ c t)ᶜ
    (fun i => ((t i).Z)ᶜ) hWi (fun i => (t i).u)
    (fun i j => (LocallyNoetherianOver.overlap B S hS (E.2.f i) (E.2.f j) (hetale i)).obj)
    (fun i j =>
      (LocallyNoetherianOver.overlapFst B S hS (E.2.f i) (E.2.f j) (hetale i)).hom)
    (fun i j =>
      (LocallyNoetherianOver.overlapSnd B S hS (E.2.f i) (E.2.f j) (hetale i)).hom)
    (fun i j => (Space.pointsMap B S hS
      (yoneda.obj (LocallyNoetherianOver.overlap B S hS (E.2.f i) (E.2.f j) (hetale i)).obj)
      (yoneda.map (LocallyNoetherianOver.overlapFst B S hS (E.2.f i) (E.2.f j)
        (hetale i)).hom) ⁻¹' (t i).Z)ᶜ)
    (fun i j => Set.preimage_compl.symm) hWij₂
    (fun i j Y a b hab =>
      LocallyNoetherianOver.exists_lift_overlap B S hS (E.2.f i) (E.2.f j) (hetale i) Y a b hab)
    (fun i j => u_restrict_eq_of_mapTriple_eq c _ _ (t i) (t j) (htij i j) _ rfl
      (fun _ hz => hz) (hWij₂ i j).subset)
  obtain ⟨uG, huG, -⟩ := Space.glueHom_openSubspaceOfPoints B S hS
    (fun i => (E.2.X i).obj) (fun i => (E.2.f i).hom) hcov (descendZ c t)ᶜ
    (fun i => ((t i).Z)ᶜ) hWi c.isOpenSubspace_U'.1.isSheaf (fun i => (t i).u) hcompatU
  have hcompatX := Space.compatible_of_overlap_completionSubfunctor B S hS
    (fun i => (E.2.X i).obj) (fun i => (E.2.f i).hom) (descendZ c t)
    (fun i => (t i).Z) hZi
    (fun i => (BigFppfOver.topology B S hS).toSheafify
      (Space.completionSubfunctor B S hS (yoneda.obj (E.2.X i).obj) (t i).Z).toFunctor ≫
        (t i).xhat.hom)
    (fun i j => (LocallyNoetherianOver.overlap B S hS (E.2.f i) (E.2.f j) (hetale i)).obj)
    (fun i j =>
      (LocallyNoetherianOver.overlapFst B S hS (E.2.f i) (E.2.f j) (hetale i)).hom)
    (fun i j =>
      (LocallyNoetherianOver.overlapSnd B S hS (E.2.f i) (E.2.f j) (hetale i)).hom)
    (fun i j => Space.pointsMap B S hS
      (yoneda.obj (LocallyNoetherianOver.overlap B S hS (E.2.f i) (E.2.f j) (hetale i)).obj)
      (yoneda.map (LocallyNoetherianOver.overlapFst B S hS (E.2.f i) (E.2.f j)
        (hetale i)).hom) ⁻¹' (t i).Z)
    (fun i j => rfl) hZij
    (fun i j Y a b hab =>
      LocallyNoetherianOver.exists_lift_overlap B S hS (E.2.f i) (E.2.f j) (hetale i) Y a b hab)
    (fun i j => completionSubfunctorRestrict_comp_eq_of_mapTriple_eq c _ _ (t i) (t j)
      (htij i j) _ rfl (fun _ hz => hz) (hZij i j).subset)
  obtain ⟨ψ₀, hψ₀, -⟩ := Space.glueHom_completionSubfunctor B S hS
    (fun i => (E.2.X i).obj) (fun i => (E.2.f i).hom) hcov (descendZ c t)
    (fun i => (t i).Z) hZi c.W.property
    (fun i => (BigFppfOver.topology B S hS).toSheafify
      (Space.completionSubfunctor B S hS (yoneda.obj (E.2.X i).obj) (t i).Z).toFunctor ≫
        (t i).xhat.hom) hcompatX
  obtain ⟨xG, hxG⟩ := Space.exists_hom_completionSheaf B S hS
    (fun i => (E.2.X i).obj) (fun i => (E.2.f i).hom) (descendZ c t)
    (fun i => (t i).Z) (fun i => (hZi i).subset) (fun i => (t i).xhat) ψ₀ hψ₀
  refine ⟨{ Z := descendZ c t
            isClosed_Z := isClosed_descendZ c hE t
            u := uG
            xhat := xG
            adic_xhat := ?_
            compatible := ?_ }, ?_⟩
  · refine hadic (fun i => (E.2.X i).obj) (fun i => (E.2.f i).hom) hcov (descendZ c t)
      c.W xG fun i => ?_
    refine (adic_completionSheafRestrict_congr (yoneda.map (E.2.f i).hom) (hpre i)
      (fun _ hz => hz) (hZi i).subset xG).mpr ?_
    rw [hxG i]
    exact (t i).adic_xhat
  · refine h0ADV c (fun i => (E.2.X i).obj) (fun i => (E.2.f i).hom) hcov
      (descendZ c t) uG xG fun i => ?_
    refine nonempty_compatibilityWitness_congr c (hZi i) ?_ ?_ (t i).compatible
    · exact (heq_of_eq (huG i).symm).trans
        (Space.heq_openSubspaceOfPointsRestrict_source B S hS (yoneda.map (E.2.f i).hom)
          (congrArg compl (hZi i)) (hWi i).subset (fun _ hz => hz) uG)
    · exact (heq_of_eq (hxG i).symm).trans
        (Space.heq_completionSheafRestrict_source B S hS (yoneda.map (E.2.f i).hom)
          (hZi i) (hZi i).subset (fun _ hz => hz) xG)
  · intro i
    refine Triple.ext_of_heq c ((mapTriple_Z_eq_preimage c _ _).trans (hpre i)) ?_ ?_
    · rw [mapTriple_u]
      refine HEq.trans ?_ (heq_of_eq (huG i))
      exact Space.heq_openSubspaceOfPointsRestrict_source B S hS
        (yoneda.map (E.2.f i).hom) (congrArg compl (hpre i))
        (W := (descendZ c t)ᶜ) (fun _ hz => hz) (hWi i).subset uG
    · rw [mapTriple_xhat]
      refine HEq.trans ?_ (heq_of_eq (hxG i))
      exact Space.heq_completionSheafRestrict_source B S hS (yoneda.map (E.2.f i).hom)
        (hpre i) (T := descendZ c t) (fun _ hz => hz) (hZi i).subset xG


/-! ### Stacks 0GHG -/

/-- **Stacks 0GHG.** In the situation of Stacks 0GH8 the functor `F` of Stacks 0GHA satisfies
the sheaf property for every étale covering of locally Noetherian schemes over `S`: a
compatible family of triples on such a covering has a unique amalgamation.

Existence is `AlgebraicGeometry.Artin.ContractionSituation.exists_mapTriple_eq` and uses the
two carried inputs; uniqueness is
`AlgebraicGeometry.Artin.ContractionSituation.eq_of_mapTriple_eq` and uses neither.
**The two carried inputs, and why neither is equivalent to the conclusion.**

`h0ADV` is the locality on the base of the compatibility condition of [Stacks, Tag 0GHA].  It is
the form in which [Stacks, Tag 0ADV], étale descent for algebraic spaces, enters the source's
argument: a witness over `V` is glued from the algebraic spaces `V'_i` and the morphisms
`p_i, j_i, x̂'_i, x'_i` of the witnesses over the `V_i`, out of a descent datum whose comparison
isomorphisms come from the uniqueness part of the main theorem on dilatations.  This library has
neither Tag 0ADV for algebraic spaces nor that uniqueness statement.

`hadic` is the locality on the base of the adicness condition of [Stacks, Tag 0AQ2].  It does not
follow from [Stacks, Tag 0APY] and [Stacks, Tag 0APV], the two facts about adicness the functor
`F` is built from: both are closure rules, so every derivation from them concludes adicness of a
composite built from restrictions, never of a factor.

Each is stated for an arbitrary situation of [Stacks, Tag 0GH8], an arbitrary covering family of
the big fppf site over `S`, and an arbitrary candidate datum over its base; each constrains one
already-given datum.  Neither mentions the étale site of locally Noetherian schemes, the family of
triples, or the existence of an amalgamation, so neither contains the conclusion.  The source's
proof of this lemma is omitted — the hint is only that morphisms may be defined étale locally — so
neither is a named citation of it.
-/
@[stacks 0GHG "both the existence and the uniqueness of the amalgamation, granting the \
locality on the base of the compatibility condition of Stacks 0GHA as h0ADV (the form in which \
Stacks 0ADV enters the source's argument) and of the adicness condition of Stacks 0AQ2 as hadic"]
theorem satisfiesEtaleSheafProperty (c : ContractionSituation B S hS)
    (h0ADV : CompatibilityIsLocalOnBase B S hS)
    (hadic : AdicIsLocalOnBase B S hS) :
    SatisfiesEtaleSheafProperty c := by
  rw [satisfiesEtaleSheafProperty_iff]
  intro E hE t ht
  obtain ⟨s, hs⟩ := exists_mapTriple_eq B S hS c h0ADV hadic hE t ht
  exact ⟨s, hs, fun s' hs' =>
    eq_of_mapTriple_eq B S hS hE fun i => (hs' i).trans (hs i).symm⟩

end ContractionSituation

end Artin

end AlgebraicGeometry

end

