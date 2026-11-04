module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.IntersectionInvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.Components
public import StacksFrontier.AlgebraicGeometry.Spaces.BranchCount

/-!
# Stalks of the two complementary ideal sheaves

Let `X` be a curve over a field with at-worst-nodal singularities and let `Y ⊆ X` be a reduced
closed subscheme, cut out by `I`; let `Z` be the scheme-theoretic closure of the complement,
cut out by `complementaryCurveIdeal I`. This module computes the stalks of `I` at a point in
terms of the irreducible components of `X` through that point.

Two ingredients make the computation local. First, the stalk at `x` of the vanishing ideal of a
closed set depends only on the intersection of that closed set with an open neighbourhood of
`x`, because the sections of a vanishing ideal over an affine open are the vanishing ideal of
the preimage of the closed set there. Second, the irreducible components of `X` are locally
finite, so `x` has an open neighbourhood met only by the components through `x`.

Away from `Z` the subscheme `Y` is all of `X`: every point outside the support of
`complementaryCurveIdeal I` lies on a component contained in `Y`, so the support of `I` contains
the whole open complement of `Z` and the stalk of `I` there vanishes.

At a point lying on exactly two components the minimal primes of the local ring are the stalks of
the vanishing ideals of those two components, by the correspondence between components through a
point and minimal primes of the local ring there (Tag 00ET).

## Main results

* `AlgebraicGeometry.IdealSheafData.stalk_vanishingIdeal_congr` — the stalk of a vanishing ideal
  at `x` depends only on the closed set near `x`.
* `TopologicalSpace.exists_isOpen_mem_forall_mem_of_locallyFinite_irreducibleComponents` — an open
  neighbourhood met only by the components through the point.
* `Stacks.Curves.compl_support_complementaryCurveIdeal_subset_support` — the open complement of
  `Z` lies in `Y`.
* `Stacks.Curves.stalk_eq_bot_of_notMem_support_complementaryCurveIdeal` — and the stalk of `I`
  vanishes there.
* `Stacks.Curves.irreducibleComponentsThrough_eq_pair` — two distinct components through a point
  with only two components through it are all of them.
* `AlgebraicGeometry.stalk_vanishingIdeal_ne_of_ne` — distinct components through a point give
  distinct minimal primes of the local ring.
* `AlgebraicGeometry.minimalPrimes_stalk_eq_pair` — and those two exhaust the minimal primes.

## References

* [Stacks Project, Tag 0E38](https://stacks.math.columbia.edu/tag/0E38)
* [Stacks Project, Tag 00ET](https://stacks.math.columbia.edu/tag/00ET)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The stalk of the vanishing ideal of a closed set depends only on that closed set near the
point.** On an affine open neighbourhood contained in the given open, the sections of the
vanishing ideal are the vanishing ideal of the preimage of the closed set, and that preimage only
sees the part of the closed set inside the affine open. -/
theorem IdealSheafData.stalk_vanishingIdeal_congr {X : Scheme.{u}} {S T : Closeds X}
    {V : X.Opens} {x : X} (hx : x ∈ V)
    (h : (S : Set X) ∩ (V : Set X) = (T : Set X) ∩ (V : Set X)) :
    IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal S) x =
      IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal T) x := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx V.2
  have hideal : (Scheme.IdealSheafData.vanishingIdeal S).ideal ⟨U, hU⟩ =
      (Scheme.IdealSheafData.vanishingIdeal T).ideal ⟨U, hU⟩ := by
    simp only [Scheme.IdealSheafData.vanishingIdeal_ideal]
    congr 1
    refine Set.ext fun p => ?_
    have hmem : hU.fromSpec.base p ∈ (V : Set X) := hUV (hU.range_fromSpec.subset ⟨p, rfl⟩)
    exact ⟨fun hp => (h.subset ⟨hp, hmem⟩).1, fun hp => (h.superset ⟨hp, hmem⟩).1⟩
  rw [IdealSheafData.stalk_eq_map_germ _ x ⟨U, hU⟩ hxU,
    IdealSheafData.stalk_eq_map_germ _ x ⟨U, hU⟩ hxU, hideal]

end AlgebraicGeometry

namespace TopologicalSpace

/-- **A point of a space whose irreducible components are locally finite has an open neighbourhood
met only by the components through it.** Local finiteness gives a neighbourhood met by finitely
many components; removing the finitely many of those which avoid the point leaves an open
neighbourhood of the point. -/
theorem exists_isOpen_mem_forall_mem_of_locallyFinite_irreducibleComponents
    {X : Type u} [TopologicalSpace X]
    (hlf : LocallyFinite (fun C : irreducibleComponents X => (C : Set X))) (x : X) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      ∀ C ∈ irreducibleComponents X, (C ∩ V).Nonempty → x ∈ C := by
  classical
  obtain ⟨t, ht, hfin⟩ := hlf x
  obtain ⟨V₀, hV₀t, hV₀open, hxV₀⟩ := mem_nhds_iff.mp ht
  set F : Set (irreducibleComponents X) :=
    {C | ((C : Set X) ∩ t).Nonempty ∧ x ∉ (C : Set X)}
  have hFfin : F.Finite := hfin.subset fun C hC => hC.1
  refine ⟨V₀ ∩ ⋂ C ∈ F, ((C : Set X))ᶜ, hV₀open.inter (hFfin.isOpen_biInter fun C _ =>
      (isClosed_of_mem_irreducibleComponents (C : Set X) C.2).isOpen_compl), ?_, ?_⟩
  · exact ⟨hxV₀, Set.mem_iInter₂.mpr fun C hC => hC.2⟩
  · rintro C hC ⟨z, hzC, hzV₀, hzI⟩
    by_contra hxC
    exact Set.mem_iInter₂.mp hzI ⟨C, hC⟩ ⟨⟨z, hzC, hV₀t hzV₀⟩, hxC⟩ hzC

end TopologicalSpace

namespace AlgebraicGeometry

/-- **Distinct irreducible components through a point give distinct minimal primes of the local
ring there.** Under the correspondence between the components through the point and the minimal
primes of the local ring, the prime attached to a component has the generic point of that
component as its image, and the stalk of the component's vanishing ideal is that prime. -/
theorem stalk_vanishingIdeal_ne_of_ne {X : Scheme.{u}} {x : X} {C D : Set X}
    (hC : C ∈ irreducibleComponents X) (hD : D ∈ irreducibleComponents X) (hCD : C ≠ D)
    (hxC : x ∈ C) (hxD : x ∈ D) :
    IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal
        ⟨C, isClosed_of_mem_irreducibleComponents C hC⟩) x ≠
      IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal
        ⟨D, isClosed_of_mem_irreducibleComponents D hD⟩) x := by
  classical
  set e := irreducibleComponentsEquivMinimalPrimes x with he
  have key : ∀ (W : Set X) (hW : W ∈ irreducibleComponents X) (hxW : x ∈ W),
      IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal
          ⟨W, isClosed_of_mem_irreducibleComponents W hW⟩) x =
        (e ⟨⟨W, hW⟩, hxW⟩).1.asIdeal := by
    intro W hW hxW
    refine stalk_vanishingIdeal_eq_of_mem_minimalPrimes x ⟨W, hW⟩ hxW _
      (e ⟨⟨W, hW⟩, hxW⟩).2 ?_
    rw [he, fromSpecStalk_irreducibleComponentsEquivMinimalPrimes x ⟨⟨W, hW⟩, hxW⟩]
    have hgen := genericPoints.isGenericPoint_ofComponent (⟨W, hW⟩ : irreducibleComponents X)
    have hmem := subset_closure
      (Set.mem_singleton (genericPoints.ofComponent (⟨W, hW⟩ : irreducibleComponents X)).1)
    rwa [hgen] at hmem
  rw [key C hC hxC, key D hD hxD]
  exact fun hcontra => hCD (congrArg (fun W : {W : irreducibleComponents X // x ∈ (W : Set X)} =>
    (W.1 : Set X)) (e.injective (Subtype.ext (PrimeSpectrum.ext hcontra))))

/-- **At a point of a scheme with exactly two minimal primes in its local ring, the minimal primes
are the stalks of the vanishing ideals of two distinct components through the point.** Each of the
two stalks is a minimal prime, the two are distinct, and there are only two minimal primes. -/
theorem minimalPrimes_stalk_eq_pair {X : Scheme.{u}} {x : X} {C D : Set X}
    (hC : C ∈ irreducibleComponents X) (hD : D ∈ irreducibleComponents X) (hCD : C ≠ D)
    (hxC : x ∈ C) (hxD : x ∈ D)
    (htwo : Set.encard (minimalPrimes (X.presheaf.stalk x)) = 2) :
    minimalPrimes (X.presheaf.stalk x) =
      {IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal
          ⟨C, isClosed_of_mem_irreducibleComponents C hC⟩) x,
        IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal
          ⟨D, isClosed_of_mem_irreducibleComponents D hD⟩) x} := by
  refine ((Set.toFinite _).eq_of_subset_of_encard_le
    (Set.pair_subset (stalk_vanishingIdeal_mem_minimalPrimes x ⟨C, hC⟩ hxC)
      (stalk_vanishingIdeal_mem_minimalPrimes x ⟨D, hD⟩ hxD)) ?_).symm
  rw [htwo, Set.encard_pair (stalk_vanishingIdeal_ne_of_ne hC hD hCD hxC hxD)]

end AlgebraicGeometry

namespace Stacks.Curves

/-- **Two distinct irreducible components through a point at which the scheme has only two
components are all of them.** -/
theorem irreducibleComponentsThrough_eq_pair {X : Scheme.{u}} {x : X} {C D : Set X}
    (hC : C ∈ irreducibleComponents X) (hD : D ∈ irreducibleComponents X) (hCD : C ≠ D)
    (hxC : x ∈ C) (hxD : x ∈ D)
    (htwo : Set.encard {Z ∈ irreducibleComponents X | x ∈ Z} = 2) :
    {Z ∈ irreducibleComponents X | x ∈ Z} = {C, D} := by
  refine ((Set.toFinite _).eq_of_subset_of_encard_le
    (Set.pair_subset (s := {Z ∈ irreducibleComponents X | x ∈ Z}) ⟨hC, hxC⟩ ⟨hD, hxD⟩) ?_).symm
  rw [htwo, Set.encard_pair hCD]

/-- **Every point outside the closure of the complement of a closed subscheme of a nodal curve
lies in that subscheme.** The component of the point either lies inside the subscheme, and then so
does the point, or is one of the components making up the closure of the complement, and then the
point lies in that closure. -/
theorem compl_support_complementaryCurveIdeal_subset_support
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (hX_nodal : HasAtWorstNodalSingularities k X) (I : X.IdealSheafData) :
    ((complementaryCurveIdeal I).support : Set X)ᶜ ⊆ (I.support : Set X) := by
  classical
  have : IsReduced X := isReduced_of_hasAtWorstNodalSingularities k X hX_nodal
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let Zcomps := {C : Set X // C ∈ irreducibleComponents X ∧ ¬ C ⊆ (I.support : Set X)}
  have hZcomp : complementaryCurveIdeal I = Scheme.IdealSheafData.vanishingIdeal
      (⨆ C : Zcomps, Closeds.closure C.1) :=
    complementaryCurveIdeal_eq_union_irreducibleComponents hX_nodal I
  have hcomponents : LocallyFinite (fun C : irreducibleComponents X => (C : Set X)) := by
    simpa using locallyFinite_irreducibleComponents_image (𝟙 X)
  have hZcomps_closed : IsClosed (⋃ C : Zcomps, (C.1 : Set X)) :=
    (locallyFinite_component_subfamily hcomponents _).isClosed_iUnion fun C =>
      isClosed_of_mem_irreducibleComponents C.1 C.2.1
  have hZsup : (↑(⨆ C : Zcomps, Closeds.closure C.1) : Set X) = ⋃ C : Zcomps, (C.1 : Set X) :=
    coe_iSup_closure_eq_iUnion_of_isClosed (fun C : Zcomps => C.1)
      (fun C => isClosed_of_mem_irreducibleComponents C.1 C.2.1) hZcomps_closed
  intro z hz
  by_contra hzI
  refine hz ?_
  rw [hZcomp, Scheme.IdealSheafData.coe_support_vanishingIdeal, hZsup]
  exact Set.mem_iUnion.mpr ⟨⟨irreducibleComponent z,
    irreducibleComponent_mem_irreducibleComponents z,
    fun h => hzI (h mem_irreducibleComponent)⟩, mem_irreducibleComponent⟩

/-- **The ideal sheaf of a reduced closed subcurve vanishes outside the closure of the complement
of that subcurve.** The open complement of the closure of the complement is contained in the
support of the ideal sheaf, so near such a point the vanishing ideal of the support is the
vanishing ideal of the whole space, which is zero because the curve is reduced. -/
theorem stalk_eq_bot_of_notMem_support_complementaryCurveIdeal
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (hX_nodal : HasAtWorstNodalSingularities k X)
    (I : X.IdealSheafData) [IsReduced I.subscheme] {x : X}
    (hx : x ∉ ((complementaryCurveIdeal I).support : Set X)) :
    IdealSheafData.stalk I x = ⊥ := by
  have : IsReduced X := isReduced_of_hasAtWorstNodalSingularities k X hX_nodal
  let V : X.Opens := ⟨((complementaryCurveIdeal I).support : Set X)ᶜ,
    (complementaryCurveIdeal I).support.isClosed.isOpen_compl⟩
  have hinter : (I.support : Set X) ∩ (V : Set X) = ((⊤ : Closeds X) : Set X) ∩ (V : Set X) :=
    Set.Subset.antisymm (fun z hz => ⟨trivial, hz.2⟩) fun z hz =>
      ⟨compl_support_complementaryCurveIdeal_subset_support hX_nodal I hz.2, hz.2⟩
  calc IdealSheafData.stalk I x
      = IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal I.support) x := by
        rw [← Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme I I.support rfl]
    _ = IdealSheafData.stalk
          (Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds X)) x :=
        IdealSheafData.stalk_vanishingIdeal_congr (V := V) hx hinter
    _ = ⊥ := by
        rw [Scheme.IdealSheafData.vanishingIdeal_top, Scheme.nilradical_eq_bot]
        simp [AlgebraicGeometry.IdealSheafData.stalk]

end Stacks.Curves

end
