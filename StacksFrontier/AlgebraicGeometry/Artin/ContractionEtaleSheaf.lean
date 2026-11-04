module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionFunctor
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ChosenCoverings
public import StacksFrontier.Examples.Sites.NoetherianSiteNotMorphismOfSites

/-!
# The étale sheaf property of Artin's contraction functor (Stacks 0GHG)

**Stacks 0GHG** says that in the situation of Stacks 0GH8 the functor `F` of Stacks 0GHA —
`AlgebraicGeometry.Artin.contractionFunctor` — satisfies the sheaf property for all étale
coverings of locally Noetherian schemes over `S`. The source omits the proof, with the hint
that morphisms may be defined étale locally.

This file fixes the vocabulary that statement needs and writes the statement down. The
category of locally Noetherian schemes over `S` is `AlgebraicGeometry.LocallyNoetherianOver`
of Stacks 0GE4, and its fppf covering families are
`AlgebraicGeometry.LocallyNoetherianOver.IsCovering`; what is added here is the étale analogue
of those: a family of locally Noetherian objects is an étale covering exactly when its
underlying family of morphisms of schemes is a chosen étale covering family of the big fppf
site in the sense of `AlgebraicGeometry.BigFppfSite.etaleCovering` (Stacks 03FF), together
with the precoverage and the topology they present.

## Main definitions

* `AlgebraicGeometry.LocallyNoetherianOver.IsEtaleCovering`,
  `AlgebraicGeometry.LocallyNoetherianOver.etalePrecoverage` and
  `AlgebraicGeometry.LocallyNoetherianOver.etaleTopology`: the étale covering families of the
  locally Noetherian site over `S`, the precoverage they present, and the topology it
  generates.
* `AlgebraicGeometry.Artin.ContractionSituation.SatisfiesEtaleSheafProperty`: the assertion of
  Stacks 0GHG, written in that vocabulary.

## Main results

* `AlgebraicGeometry.LocallyNoetherianOver.etaleTopology_le_fppfTopology`: the étale topology
  of the locally Noetherian site is coarser than its fppf topology, so every fppf sheaf on it
  is an étale sheaf.
* `AlgebraicGeometry.LocallyNoetherianOver.exists_mem_range_pointsMap_of_isEtaleCovering`: an
  étale covering family of the locally Noetherian site is jointly surjective on the points of
  the algebraic spaces its members represent.
* `AlgebraicGeometry.Artin.ContractionSituation.satisfiesEtaleSheafProperty_iff`: the sheaf
  property of `F`, unfolded into the familiar form — a compatible family of triples on an
  étale covering has a unique amalgamation.
* `AlgebraicGeometry.Artin.ContractionSituation.Z_eq_of_mapTriple_eq`: the closed subset `Z`
  of a triple is determined étale locally.

## What is and is not proved

**Stacks 0GHG itself is not proved, and carries no attribute.** What is delivered is the
faithful statement — `SatisfiesEtaleSheafProperty`, a `Prop`-valued definition, not a theorem —
together with the vocabulary it is phrased in and the two fragments of its proof that are
reachable from what the library has.

Nothing is assumed: every declaration here is proved outright.

The missing part is the descent of a triple `(Z, u', x̂)` along an étale covering
`{V_i ⟶ V}`. Each of its three components, and the compatibility witness, needs a descent
statement this library does not have:

1. *The closed subset.* Gluing closed subsets `Z_i ⊆ |V_i|` into a closed `Z ⊆ |V|` with the
   `Z_i` as preimages needs the fibre products `V_i ×_V V_j` as objects of
   `AlgebraicGeometry.LocallyNoetherianOver` — hence that an étale morphism with locally
   Noetherian target has locally Noetherian source and that the fibre product is small enough
   for the site, which is Stacks 0GE1 (3) and is not in the library — and that the map on
   points of an étale morphism is open, the étale counterpart of
   `AlgebraicGeometry.Space.isClosedMap_pointsMap_yoneda_iff`, which is also absent. Only the
   uniqueness direction is available here, as
   `AlgebraicGeometry.Artin.ContractionSituation.Z_eq_of_mapTriple_eq`, since that needs
   nothing but joint surjectivity.
2. *The morphism `u' : V ∖ Z ⟶ U'`.* The open subspaces `V_i ∖ Z_i` are subfunctors of the
   `V_i`, not objects of the site, so the sheaf property of the algebraic space `U'` cannot be
   applied directly: what is needed is that the family `{V_i ∖ Z_i ⟶ V ∖ Z}` of open
   subspaces generates an fppf covering sieve of the subfunctor `V ∖ Z`. The library has no
   such statement.
3. *The morphism `x̂ : V_{/Z} ⟶ W`.* Likewise one needs that the completions
   `V_{i,/Z_i} ⟶ V_{/Z}` of Stacks 0AMC cover `V_{/Z}`, that is that
   `AlgebraicGeometry.Space.completionSheaf` carries an étale covering to a jointly
   epimorphic family of fppf sheaves. Absent.
4. *The compatibility witness.* `AlgebraicGeometry.Artin.ContractionSituation.mapTriple`
   transports a witness forwards; descending one requires gluing the algebraic spaces `V'_i`
   and the morphisms `p_i`, `j_i`, `x̂'_i`, `x'_i` out of a descent datum, which is étale
   descent for algebraic spaces (Stacks 0ADV). The library has `@[stacks 04TR]` for sheaves on
   a site (`CategoryTheory.Sites.Glueing.GlueingSheaves`) but nothing for algebraic spaces,
   and no declaration carries Stacks 0ADV.

## Implementation notes

The étale covering families are not defined from scratch: they are
`AlgebraicGeometry.BigFppfSite.etaleCovering` applied to the underlying family, exactly as
`AlgebraicGeometry.LocallyNoetherianOver.IsCovering` is
`AlgebraicGeometry.BigFppfOver.IsCovering` applied to it. That predicate already is the
conjunction of membership in the chosen, cardinal-bounded fppf system of the site with being
an étale covering of schemes, which keeps all the choices made for the big fppf site — the
cutoff and the covering bound are not re-chosen — and makes
`AlgebraicGeometry.LocallyNoetherianOver.etalePrecoverage_le_precoverage` immediate. The two
definitions `etalePrecoverage` and `etaleTopology` carry no Stacks attribute, matching their
fppf counterparts, which the library also leaves untagged.

Stacks 0GHG speaks of the sheaf property *for all étale coverings*, so
`SatisfiesEtaleSheafProperty` is stated family by family, as
`CategoryTheory.Presieve.IsSheafFor` on each étale covering presieve, rather than as
`CategoryTheory.Presieve.IsSheaf` for `etaleTopology`. The latter is a priori stronger, and
`AlgebraicGeometry.Artin.ContractionSituation.satisfiesEtaleSheafProperty_of_isSheaf` records
the implication; the converse would need the étale precoverage to be stable under base change,
which is the same missing fibre-product input as item (1) above.

## References

* [Stacks Project, Tag 03FF](https://stacks.math.columbia.edu/tag/03FF)
* [Stacks Project, Tag 0ADV](https://stacks.math.columbia.edu/tag/0ADV)
* [Stacks Project, Tag 0AMC](https://stacks.math.columbia.edu/tag/0AMC)
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

namespace LocallyNoetherianOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A family of locally Noetherian objects over `S` is an *étale covering* exactly when its
underlying family is a chosen étale covering family of the ambient big fppf site, that is one
of `AlgebraicGeometry.BigFppfSite.etaleCovering`: a chosen fppf covering family which is an
étale covering of schemes. This is the étale counterpart of
`AlgebraicGeometry.LocallyNoetherianOver.IsCovering`; by Stacks 0GE1 (3) the sources of a
covering family of a locally Noetherian object are automatically locally Noetherian, so no
further condition is needed. -/
abbrev IsEtaleCovering (E : Covering (LocallyNoetherianOver B S hS)) : Prop :=
  B.etaleCovering
    ⟨(toBigFppfOver B S hS ⋙ BigFppfOver.forget B S hS).obj E.1,
      E.2.map (toBigFppfOver B S hS ⋙ BigFppfOver.forget B S hS)⟩

/-- The precoverage presented by the étale covering families of locally Noetherian objects. -/
def etalePrecoverage : Precoverage (LocallyNoetherianOver B S hS) where
  coverings X := {R | ∃ E : PreZeroHypercover.{u + 1} X,
    R = E.presieve₀ ∧ IsEtaleCovering B S hS ⟨X, E⟩}

/-- Membership in the étale precoverage of the locally Noetherian site is characterized by a
presenting étale covering family. -/
theorem mem_etalePrecoverage_iff {X : LocallyNoetherianOver B S hS} {R : Presieve X} :
    R ∈ etalePrecoverage B S hS X ↔ ∃ E : PreZeroHypercover.{u + 1} X,
      R = E.presieve₀ ∧ IsEtaleCovering B S hS ⟨X, E⟩ :=
  Iff.rfl

/-- The étale topology on the locally Noetherian objects of the big fppf site over `S`. -/
abbrev etaleTopology : GrothendieckTopology (LocallyNoetherianOver B S hS) :=
  (etalePrecoverage B S hS).toGrothendieck

/-- An étale covering family of the locally Noetherian site is a covering family. -/
theorem isCovering_of_isEtaleCovering {E : Covering (LocallyNoetherianOver B S hS)}
    (hE : IsEtaleCovering B S hS E) : IsCovering B S hS E := hE.1

/-- The étale precoverage of the locally Noetherian site is contained in its fppf
precoverage. -/
theorem etalePrecoverage_le_precoverage :
    etalePrecoverage B S hS ≤ precoverage B S hS :=
  fun _ _ ⟨E, hR, hE⟩ => ⟨E, hR, hE.1⟩

/-- The étale topology of the locally Noetherian site is coarser than its fppf topology. -/
theorem etaleTopology_le_fppfTopology :
    etaleTopology B S hS ≤ fppfTopology B S hS :=
  Precoverage.toGrothendieck_mono (etalePrecoverage_le_precoverage B S hS)

/-- The underlying family of scheme morphisms of an étale covering family of the locally
Noetherian site over `S` is an étale covering presieve of schemes. -/
theorem ofArrows_mem_etalePrecoverage_of_isEtaleCovering
    {E : Covering (LocallyNoetherianOver B S hS)} (hE : IsEtaleCovering B S hS E) :
    Presieve.ofArrows (fun i => (toScheme B S hS).obj (E.2.X i))
        (fun i => (toScheme B S hS).map (E.2.f i)) ∈
      Scheme.etalePrecoverage ((toScheme B S hS).obj E.1) :=
  hE.2

/-- An étale covering family of the locally Noetherian site over `S` is jointly surjective on
points: every point of the algebraic space represented by the target is in the image of the
points of one of the members. -/
theorem exists_mem_range_pointsMap_of_isEtaleCovering
    {E : Covering (LocallyNoetherianOver B S hS)} (hE : IsEtaleCovering B S hS E)
    (x : Space.points B S hS (yoneda.obj E.1.obj)) :
    ∃ i : E.2.I₀, x ∈ Set.range (Space.pointsMap B S hS
      (yoneda.obj (E.2.X i).obj) (yoneda.map (E.2.f i).hom)) := by
  obtain ⟨i, y, hy⟩ := ((Scheme.ofArrows_mem_precoverage_iff
      (P := (@Etale.{u} : MorphismProperty Scheme.{u}))).mp
    (ofArrows_mem_etalePrecoverage_of_isEtaleCovering B S hS hE)).1
      (Space.pointsToScheme B S hS E.1.obj x)
  obtain ⟨z, hz⟩ := Space.surjective_pointsToScheme B S hS (E.2.X i).obj y
  refine ⟨i, z, Space.injective_pointsToScheme B S hS E.1.obj ?_⟩
  rw [Space.pointsToScheme_pointsMap_yoneda, hz]
  exact hy

end LocallyNoetherianOver

namespace Artin

namespace ContractionSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0GHG** as a statement: in the situation of Stacks 0GH8 the functor `F` of
Stacks 0GHA satisfies the sheaf property for every étale covering of locally Noetherian
schemes over `S`. -/
def SatisfiesEtaleSheafProperty (c : ContractionSituation B S hS)
    : Prop :=
  ∀ E : Covering (LocallyNoetherianOver B S hS),
    LocallyNoetherianOver.IsEtaleCovering B S hS E →
      Presieve.IsSheafFor (contractionFunctor c) E.2.presieve₀

/-- The sheaf property of `F` for the étale covering families, written out: for every étale
covering `{V_i ⟶ V}` of locally Noetherian schemes over `S` and every family of triples
`t_i ∈ F(V_i)` which agree on overlaps, there is a unique triple `t ∈ F(V)` whose pullback
to `V_i` is `t_i`. -/
theorem satisfiesEtaleSheafProperty_iff (c : ContractionSituation B S hS)
    :
    SatisfiesEtaleSheafProperty c ↔
      ∀ E : Covering (LocallyNoetherianOver B S hS),
        LocallyNoetherianOver.IsEtaleCovering B S hS E →
        ∀ t : (i : E.2.I₀) → Triple c (E.2.X i).obj,
          (∀ (i j : E.2.I₀) (Y : LocallyNoetherianOver B S hS) (gi : Y ⟶ E.2.X i)
              (gj : Y ⟶ E.2.X j), gi ≫ E.2.f i = gj ≫ E.2.f j →
            mapTriple c gi.hom (t i) = mapTriple c gj.hom (t j)) →
          ∃! s : Triple c E.1.obj, ∀ i, mapTriple c (E.2.f i).hom s = t i :=
  forall_congr' fun _ => forall_congr' fun _ => Presieve.isSheafFor_arrows_iff _ _

/-- The first component of a section of `F` is determined étale locally: two triples over a
locally Noetherian scheme `V` over `S` whose pullbacks to the members of an étale covering
of `V` agree have the same closed subset `Z`. This is the part of the separatedness half of
Stacks 0GHG that joint surjectivity of an étale covering gives on its own. -/
theorem Z_eq_of_mapTriple_eq {c : ContractionSituation B S hS}
    {E : Covering (LocallyNoetherianOver B S hS)}
    (hE : LocallyNoetherianOver.IsEtaleCovering B S hS E) {s s' : Triple c E.1.obj}
    (h : ∀ i, mapTriple c (E.2.f i).hom s = mapTriple c (E.2.f i).hom s') :
    s.Z = s'.Z := by
  ext x
  obtain ⟨i, z, hz⟩ :=
    LocallyNoetherianOver.exists_mem_range_pointsMap_of_isEtaleCovering B S hS hE x
  have hpre : Space.pointsMap B S hS (yoneda.obj (E.2.X i).obj)
        (yoneda.map (E.2.f i).hom) ⁻¹' s.Z =
      Space.pointsMap B S hS (yoneda.obj (E.2.X i).obj)
        (yoneda.map (E.2.f i).hom) ⁻¹' s'.Z :=
    congrArg Triple.Z (h i)
  subst hz
  exact Set.ext_iff.mp hpre z

/-- If `F` is a sheaf for the étale topology of the locally Noetherian site, then it
satisfies the sheaf property for every étale covering family. -/
theorem satisfiesEtaleSheafProperty_of_isSheaf (c : ContractionSituation B S hS)
    (h : Presieve.IsSheaf (LocallyNoetherianOver.etaleTopology B S hS)
      (contractionFunctor c)) :
    SatisfiesEtaleSheafProperty c :=
  fun E hE => h.isSheafFor_of_mem_precoverage ⟨E.2, rfl, hE⟩

end ContractionSituation

end Artin

end AlgebraicGeometry

end
