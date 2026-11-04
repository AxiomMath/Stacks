module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveTheoryGeometricReduction
public import StacksFrontier.Deformation.Artin.Versality.Openness
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityOpenness
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityTag

/-!
# Openness of versality from a naive obstruction theory

Let `S` be a locally Noetherian scheme and let `𝒳` be a category fibred in groupoids over the
big fppf site of `S` which satisfies (RS*) and carries a naive obstruction theory in the sense
of Stacks 07YP. Stacks 07YU asserts that openness of versality then holds for `𝒳`, provided
the complexes `E_x` of that definition have finitely generated cohomology groups for the pairs
`(A, x)` with `A` of finite type over `S`. This file proves that.

The source deduces the tag from Stacks 07YN, which is the same conclusion at a *single* object
`x` of `𝒳` over an affine `Spec A` of finite type over an affine open `Spec Λ ⊆ S`, for a
morphism `ξ : E ⟶ NL_{A/Λ}` of `D⁻(A)` satisfying the two assumptions collected in
`Deformation.Artin.NaiveObstructionAt`. Two steps separate the two. The first is reading the
fields of a naive obstruction theory at one charted object: the complex `E = E_x`, the map
`ξ = ξ_x`, the boundedness of `E` and both assumptions of Stacks 07YN are *derived* there, and
the proviso of the source supplies the finiteness assumption. The second is the geometric
reduction at the start of the proof of the source, carried out in
`StacksFrontier.Deformation.Artin.Obstruction.NaiveTheoryGeometricReduction`: an arbitrary base
`U` locally of finite type over `S` and an arbitrary finite type point `u₀` of it are replaced
by an affine open `Spec A ⊆ U` in which `u₀` is closed and whose structure morphism factors
through an affine open `Spec Λ ⊆ S`.

## Main definitions

* `Deformation.Artin.NaiveObstructionTheory.naiveObstructionAt` — the data of Stacks 07YN at a
  charted object `(A, x)`, read off the fields of a naive obstruction theory: the lifting
  criterion across a deformation situation is clause (v) of Stacks 07YP at `x`, and the
  isomorphism of functors `T_x(−) ⟶ Ext⁰_A(E_x, −)` carrying the canonical element to
  `E_x ⟶ NL_{A/Λ} ⟶ Ω_{A/Λ}` is clauses (2), (iii) and (iv) at `x`.

## Main results

* `Deformation.Artin.exists_isOpen_isVersalAt_of_naiveObstructionTheory` — the one-chart form:
  for a naive obstruction theory whose complexes `E_x` have finitely generated cohomology
  groups over every `A` of finite type over the chart, versality of `x` at a closed point of
  `Spec A` propagates to every finite type point of an open neighbourhood.
* `Deformation.Artin.isOpenVersality_of_naiveObstructionTheory` — **Stacks 07YU**: openness of
  versality for `𝒳`.

## Implementation notes

A naive obstruction theory is a datum relative to one affine chart `Spec Λ ⊆ S` in this
library, as it must be for clause (1) of Stacks 07YP to compare `NL_{A/Λ}` with `NL_{B/Λ}`;
`A` being of finite type over `S` is then `A` being of finite type over `Λ`. The source's
"`𝒳` has a naive obstruction theory" is accordingly read as one such datum for every affine
chart, which is what the source's indexing by pairs `(A, x)` together with an affine open the
structure morphism factors through amounts to; the finiteness proviso is quantified the same
way. The boundedness of `E_x` needs no hypothesis: clause (1) of Stacks 07YP already produces
an object of `D⁻(A)`, and the `Deformation.Artin.NaiveObstructionTheory.complex` field records
exactly that.

The versality criterion of Stacks 07YM enters only through Stacks 07YN, which takes it as the
hypothesis `Deformation.Artin.NaiveVersalityCriterion`; it is supplied by
`Deformation.Artin.naiveVersalityCriterion`, which is that tag, so it is no hypothesis of the
statements below. Its own side conditions are the source's: `S` locally Noetherian, `A` of
finite type over `Λ`, and `E` bounded above — the last being the second component of the
`Deformation.Artin.NaiveObstructionTheory.complex` field.

The conclusion is the body of the predicate `Deformation.Artin.IsOpenVersality` of
Stacks 07XQ, written out rather than named — the `example` at the end of the file checks that
the two are the same proposition. The predicate takes an argument asserting that
`p ⋙ Over.post B.inclusion` is fibred in groupoids, which its body does not use and which is
not available: the slice `Over S` contains objects whose size exceeds the site's cutoff, and
`CategoryTheory.Functor.IsFiberedInGroupoids` demands lifts along morphisms into *every* object
of the base category. Naming the predicate would therefore have put an unprovable hypothesis in
the statement.

The side condition `hΩ` of the canonical element — that the spectrum of the square-zero
extension `A[Ω_{A/Λ}]` lies in the site — is not a hypothesis of the tag: it is discharged by
`Deformation.Artin.contains_spec_squareZeroRing_differentials` from the finite type of `A` over
`Λ`.

## References

* [Stacks Project, Tag 07YU](https://stacks.math.columbia.edu/tag/07YU)
* [Stacks Project, Tag 07YP](https://stacks.math.columbia.edu/tag/07YP)
* [Stacks Project, Tag 07YN](https://stacks.math.columbia.edu/tag/07YN)
* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
* [Stacks Project, Tag 07XQ](https://stacks.math.columbia.edu/tag/07XQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace Deformation.Artin

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} {c : AffineChart S}
variable {hp : p.IsFiberedInGroupoids} {hRS : SatisfiesRSStar B S hS p hp}

/-! ### The assumptions of Stacks 07YN at one object of the fibred category -/

/-- Assumptions (1) and (2) of Stacks 07YN at a charted object `(A, x)`, derived from a naive
obstruction theory for the same chart: the complex is `E_x`, the map is `ξ_x`, the lifting
criterion is clause (v) of Stacks 07YP at `x`, and the isomorphism of functors
`T_x(−) ⟶ Ext⁰_A(E_x, −)` carrying the canonical element to `E_x ⟶ NL_{A/Λ} ⟶ Ω_{A/Λ}` is
assembled from clauses (2), (iii) and (iv) at `x`. -/
public def NaiveObstructionTheory.naiveObstructionAt
    (N : NaiveObstructionTheory B S hS p hp hRS c) (P : ChartedObject B S hS p c)
    (hΩ : B.Contains (Spec (squareZeroRing P.ring (differentialsModule c.ring P.ring)))) :
    NaiveObstructionAt hp hRS P hΩ (N.complex P).obj (N.xi P) where
  hasLift_iff_xi_comp_eq_zero := N.hasLift_iff_xi_comp_eq_zero P
  tangentMap := N.tangentMap P
  tangentMap_add := N.tangentMap_add P
  tangentMap_natural := N.tangentMap_natural P
  tangentMap_bijective := N.tangentMap_bijective P
  tangentMap_canonicalElement := N.tangentMap_canonicalElement P hΩ

/-! ### Openness of versality -/

/-- **Stacks 07YU**, at a charted object. Let `S` be a locally Noetherian scheme and `𝒳` a
category fibred in groupoids over the big fppf site of `S` satisfying (RS*) and carrying a
naive obstruction theory `N` relative to an affine chart `Spec Λ ⊆ S`. Assume the proviso of
the source: for every object `x` of `𝒳` over the spectrum of a `Λ`-algebra `A` of finite type
mapping into the chart, the cohomology groups of `E_x` are finite `A`-modules. Let `x` be such
an object, over `U = Spec A`, and let `u₀ ∈ U` be a closed point at which `x` is versal. Then
`x` is versal at every finite type point of an open neighbourhood of `u₀`.

Nothing about the lifting obstruction is assumed: the complex `E_x`, the map
`ξ_x : E_x ⟶ NL_{A/Λ}`, the boundedness of `E_x` and assumptions (1) and (2) of Stacks 07YN all
come from `N`, through
`Deformation.Artin.NaiveObstructionTheory.naiveObstructionAt`; the finiteness assumption of
Stacks 07YN comes from the proviso `hFinite`, and its versality criterion from
`Deformation.Artin.naiveVersalityCriterion`, which is Stacks 07YM.

This is the one-chart form of the statement. The full tag — openness of versality for `𝒳`,
over an arbitrary base locally of finite type over `S` and at an arbitrary finite type point —
is `Deformation.Artin.isOpenVersality_of_naiveObstructionTheory`, which reduces to this one by
the geometric reduction of
`Deformation.Artin.exists_chartedData`. -/
public theorem exists_isOpen_isVersalAt_of_naiveObstructionTheory [IsLocallyNoetherian S]
    (N : NaiveObstructionTheory B S hS p hp hRS c)
    (hFinite : ∀ (Q : ChartedObject B S hS p c), Algebra.FiniteType c.ring Q.ring →
      ∀ n : ℤ, Module.Finite Q.ring
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} Q.ring) n).obj (N.complex Q).obj))
    (P : ChartedObject B S hS p c) [Algebra.FiniteType c.ring P.ring]
    (hΩ : B.Contains (Spec (squareZeroRing P.ring (differentialsModule c.ring P.ring))))
    (u₀ : Spec (.of P.ring)) (hu₀ : IsClosed ({u₀} : Set (Spec (.of P.ring))))
    (hversal : IsVersalAt (Over.mk P.obj.alg.toScheme) (p ⋙ Over.post B.inclusion) u₀ P.point
      P.overScheme_eq) :
    ∃ V : Set (Spec (.of P.ring)), IsOpen V ∧ u₀ ∈ V ∧
      ∀ u ∈ V, IsFiniteTypePoint u →
        IsVersalAt (Over.mk P.obj.alg.toScheme) (p ⋙ Over.post B.inclusion) u P.point
          P.overScheme_eq := by
  refine exists_isOpen_isVersalAt_of_naiveObstructionAt hp hRS P hΩ (N.complex P).obj (N.xi P)
    (N.complex P).property (N.naiveObstructionAt P hΩ) (hFinite P inferInstance) ?_ u₀ hu₀ hversal
  exact naiveVersalityCriterion hp hRS P hΩ (N.complex P).obj (N.complex P).property (N.xi P)

/-! ### Openness of versality for the whole fibred category -/

/-- **Stacks 07YU.** Let `S` be a locally Noetherian scheme and `𝒳` a category fibred in
groupoids over the big fppf site of `S`. Assume that `𝒳` satisfies (RS*) and that `𝒳` has a
naive obstruction theory, and assume the proviso of the source: the complexes `E_x` of
Stacks 07YP have finitely generated cohomology groups for the pairs `(A, x)` with `A` of finite
type over `S`. Then openness of versality holds for `𝒳`: if `U` is a scheme locally of finite
type over `S`, `x` an object of `𝒳` over `U` and `u₀` a finite type point of `U` at which `x`
is versal, then there is an open neighbourhood of `u₀` at every finite type point of which `x`
is versal.

The conclusion is the body of `Deformation.Artin.IsOpenVersality`, written out; see the
implementation notes of this file for why the predicate itself cannot be used. -/
@[stacks 07YU]
public theorem isOpenVersality_of_naiveObstructionTheory [IsLocallyNoetherian S]
    (N : ∀ c : AffineChart S, NaiveObstructionTheory B S hS p hp hRS c)
    (hFinite : ∀ (c : AffineChart S) (Q : ChartedObject B S hS p c),
      Algebra.FiniteType c.ring Q.ring → ∀ n : ℤ, Module.Finite Q.ring
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} Q.ring) n).obj ((N c).complex Q).obj))
    (U : Over S) (hUft : LocallyOfFiniteType U.hom) (x : X)
    (hx : (p ⋙ Over.post B.inclusion).obj x = U) (u₀ : U.left)
    (hu₀ : IsFiniteTypePoint u₀)
    (hversal : IsVersalAt U (p ⋙ Over.post B.inclusion) u₀ x hx) :
    ∃ V : U.left.Opens, u₀ ∈ V.1 ∧
      ∀ u ∈ V.1, IsFiniteTypePoint u →
        IsVersalAt U (p ⋙ Over.post B.inclusion) u x hx := by
  subst hx
  have : LocallyOfFiniteType (B.inclusion.map (p.obj x).hom) := hUft
  obtain ⟨D, w₀, hw₀, hw₀c⟩ := exists_chartedData B S hS p x (p.obj x).left.2 u₀ hu₀
  obtain ⟨obj, ρ, hρ⟩ := exists_restrictedLift B S hS p x D.mem D.immersion hp
  let P : ChartedObject B S hS p D.chart :=
    restrictedChartedObject B S hS p x D.mem D.immersion D.mapsIntoAffineOpen D.chart
      D.factorization obj
  have hPfin : Algebra.FiniteType D.chart.ring P.ring := D.finiteType
  have hΩ : B.Contains (Spec (squareZeroRing P.ring
      (differentialsModule D.chart.ring P.ring))) :=
    contains_spec_squareZeroRing_differentials B D.mem
  -- every point of `Spec A` has its image in `S` inside the chart
  have hrange : ∀ t : Spec (CommRingCat.of D.ring),
      (B.inclusion.map (p.obj x).hom).base (D.immersion.base t) ∈
        Set.range D.chart.immersion.base := fun t =>
    ⟨(Spec.map (CommRingCat.ofHom (algebraMap D.chart.ring D.ring))).base t,
      congrArg (fun m : Spec (CommRingCat.of D.ring) ⟶ S => m.base t) D.factorization⟩
  have htoS : P.obj.alg.toScheme = D.immersion ≫ B.inclusion.map (p.obj x).hom :=
    toScheme_restrictedSiteAlgebra B S hS p x D.mem D.immersion
  -- versality at a point of `Spec A` is versality at its image in `U`
  have hiff : ∀ t : Spec (CommRingCat.of D.ring),
      IsVersalAt (Over.mk P.obj.alg.toScheme) (p ⋙ Over.post B.inclusion) t P.point
          P.overScheme_eq ↔
        IsVersalAt ((p ⋙ Over.post B.inclusion).obj x) (p ⋙ Over.post B.inclusion)
          (D.immersion.base t) x rfl := fun t =>
    isVersalAt_iff_restrict B S hS p hp D.chart.immersion rfl P.overScheme_eq ρ D.immersion
      D.isOpenImmersion hρ t (range_residuePoint_subset S _ _ D.chart.immersion (hrange t))
      (range_residuePoint_subset S _ _ D.chart.immersion (htoS ▸ hrange t))
  have hversal' : IsVersalAt (Over.mk P.obj.alg.toScheme) (p ⋙ Over.post B.inclusion) w₀
      P.point P.overScheme_eq := by
    rw [hiff w₀, hw₀]
    exact hversal
  obtain ⟨V', hV'open, hw₀V', hV'⟩ :=
    exists_isOpen_isVersalAt_of_naiveObstructionTheory (N D.chart) (hFinite D.chart) P hΩ
      w₀ hw₀c hversal'
  refine ⟨⟨D.immersion.base '' V', D.immersion.isOpenEmbedding.isOpenMap V' hV'open⟩,
    ⟨w₀, hw₀V', hw₀⟩, ?_⟩
  rintro u ⟨t, htV', rfl⟩ hft
  exact (hiff t).mp (hV' t htV' (isFiniteTypePoint_of_isOpenImmersion D.immersion t hft))

/-- The conclusion of `Deformation.Artin.isOpenVersality_of_naiveObstructionTheory` is the
predicate `Deformation.Artin.IsOpenVersality` of Stacks 07XQ, written out. -/
example (hq : (p ⋙ Over.post B.inclusion).IsFiberedInGroupoids) :
    IsOpenVersality (p ⋙ Over.post B.inclusion) hq =
      ∀ (U : Over S), LocallyOfFiniteType U.hom →
        ∀ (x : X) (hx : (p ⋙ Over.post B.inclusion).obj x = U) (u₀ : U.left),
          IsFiniteTypePoint u₀ →
          IsVersalAt U (p ⋙ Over.post B.inclusion) u₀ x hx →
          ∃ V : U.left.Opens, u₀ ∈ V.1 ∧
            ∀ u ∈ V.1, IsFiniteTypePoint u →
              IsVersalAt U (p ⋙ Over.post B.inclusion) u x hx :=
  rfl

end Deformation.Artin

end
