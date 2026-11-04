module

public import StacksFrontier.RingTheory.Flat.HenselianFlattening

/-!
# The outstanding hypotheses of the local flattening theorem are that theorem

`StacksFrontier.RingTheory.Flat.HenselianFlattening` reduces Stacks Tag 05PG — the assertion that
the functor `F_lf` of Stacks Tag 05MK is corepresented by a quotient `A ⧸ I` — to three
statements about the ideals of `A` which *flatten* the situation, i.e. over whose quotient the
flatness condition of Stacks Tag 05ML holds:
`Module.FlatAtPointSituation.FlattensSInf` (the flattening ideals are closed under
intersections), `Module.FlatAtPointSituation.FlattensKer` (the kernel of a local `A`-algebra
satisfying the condition flattens) and `Module.FlatAtPointSituation.FlattensFGApprox` (a
flattening ideal contains a finitely generated one). The third is genuine extra content and is
proved in `StacksFrontier.RingTheory.Flat.FlatteningFGApprox` from the limit preservation of
Stacks Tag 05MN. The first two are not: this file proves that they are, *together*, logically
equivalent to the conclusion of Stacks Tag 05PG itself.

The reason is that corepresentability by `A ⧸ I` is exactly the statement that the flattening
ideals are the ideals containing `I`, together with the fact that the condition over an arbitrary
local `A`-algebra `R` is detected by the kernel of `A → R`. Reading the corepresentability
statement on the quotients `A ⧸ J` recovers `FlattensSInf`, reading it on `R` recovers
`FlattensKer`, and reading it on `I` itself recovers `FlattensFGApprox` once `I` is known to be
finitely generated. Consequently a proof of either hypothesis is a proof of Stacks Tag 05PG, and
the theorems of `StacksFrontier.RingTheory.Flat.HenselianFlattening` which take them as hypotheses
do not establish Stacks Tag 05PG. The dévissage argument of the source does, and is carried out in
`StacksFrontier.RingTheory.Flat.HenselianFlatteningTheorem`.

## Main results

* `Module.FlatAtPointSituation.flattens_iff_le_of_condition_iff`: if `I` corepresents the
  flatness condition then the flattening ideals are exactly the ideals containing `I`.
* `Module.FlatAtPointSituation.flattensSInf_and_flattensKer_iff_exists_ideal`: the conjunction of
  the two outstanding hypotheses is equivalent to the first conclusion of Stacks Tag 05PG.
* `Module.FlatAtPointSituation.flattensSInf_and_flattensKer_and_flattensFGApprox_iff_exists_fg`:
  the conjunction of all three is equivalent to the second conclusion of Stacks Tag 05PG.
* `Module.FlatAtPointSituation.flattensSInf_iff_flattens_flatteningIdeal`: `FlattensSInf` says no
  more and no less than that the smallest flattening ideal flattens the situation.
* `Module.FlatAtPointSituation.conditionOn_ulift_iff`: the flatness condition is invariant under
  a change of universe, which is what lets the quotient `A ⧸ J`, a ring of universe `u`, be
  tested against a statement about local `A`-algebras of another universe.

## Implementation notes

The corepresentability statement quantifies over `LocalAlgCat.{u, y} S.A`, the local `A`-algebras
whose carrier lives in `Type y`, while the quotients `A ⧸ J` live in `Type u`. Only for `u ≤ y`
can a quotient be tested, and then only after a universe lift; this is why the equivalences below
are stated at `y = max u x`, which ranges over exactly the universes above `u`. The restriction is
not an artefact: for a universe `y` not above `u` the category `LocalAlgCat.{u, y} S.A` can be
empty, in which case the corepresentability statement holds vacuously with `I = ⊥` and implies
nothing. The reverse implication, that the two hypotheses give corepresentability, holds in every
universe and is `Module.FlatAtPointSituation.exists_ideal_conditionOn_iff_map_eq_bot`.

The universe lift needs `IsLocalRing (ULift R)` and the locality of `A → ULift R`, neither of
which Mathlib has; they are supplied here as instances.

## References

* [Stacks Project, Tag 05MK](https://stacks.math.columbia.edu/tag/05MK)
* [Stacks Project, Tag 05ML](https://stacks.math.columbia.edu/tag/05ML)
* [Stacks Project, Tag 05PG](https://stacks.math.columbia.edu/tag/05PG)
-/

@[expose] public section

open IsLocalRing

universe u v w x y

namespace ULift

/-- A universe lift of a local ring is a local ring. -/
instance instIsLocalRing {R : Type u} [CommRing R] [IsLocalRing R] :
    IsLocalRing (ULift.{y} R) :=
  IsLocalRing.of_surjective' (ULift.ringEquiv (R := R)).symm.toRingHom fun z ↦ ⟨z.down, rfl⟩

/-- The structure map of a universe lift of a local algebra is again a local homomorphism. -/
instance instIsLocalHomAlgebraMap {A : Type u} {R : Type v} [CommRing A] [CommRing R]
    [IsLocalRing A] [IsLocalRing R] [Algebra A R] [IsLocalHom (algebraMap A R)] :
    IsLocalHom (algebraMap A (ULift.{y} R)) where
  map_nonunit a ha :=
    IsLocalHom.map_nonunit (f := algebraMap A R) a (ha.map (ULift.ringEquiv (R := R)))

/-- A universe lift does not change the kernel of the structure map of an algebra. -/
theorem ker_algebraMap {A : Type u} (R : Type v) [CommRing A] [CommRing R] [Algebra A R] :
    RingHom.ker (algebraMap A (ULift.{y} R)) = RingHom.ker (algebraMap A R) := by
  ext a
  simp only [RingHom.mem_ker]
  exact ⟨fun h ↦ congrArg ULift.down h, fun h ↦ congrArg ULift.up h⟩

end ULift

namespace Module.FlatAtPointSituation

/-- The flatness condition of Stacks Tag 05ML is transported along an isomorphism of local
`A`-algebras; the source and the target may live in different universes. -/
theorem ConditionOn.of_algEquiv {S : FlatAtPointSituation.{u, v, w}} {R : Type x} {T : Type y}
    [CommRing R] [IsLocalRing R] [Algebra S.A R] [CommRing T] [IsLocalRing T] [Algebra S.A T]
    (e : R ≃ₐ[S.A] T) (h : S.ConditionOn R) : S.ConditionOn T := by
  let _ : Algebra R T := e.toRingEquiv.toRingHom.toAlgebra
  have _ : IsScalarTower S.A R T := IsScalarTower.of_algebraMap_eq fun a ↦ (e.commutes a).symm
  have _ : IsLocalHom (algebraMap R T) :=
    IsLocalHom.of_surjective (algebraMap R T) e.surjective
  exact ConditionOn.of_isLocalHom R T h

/-- The flatness condition of Stacks Tag 05ML is invariant under a change of universe. -/
theorem conditionOn_ulift_iff (S : FlatAtPointSituation.{u, v, w}) (R : Type x) [CommRing R]
    [IsLocalRing R] [Algebra S.A R] : S.ConditionOn (ULift.{y} R) ↔ S.ConditionOn R :=
  ⟨ConditionOn.of_algEquiv (ULift.algEquiv (R := S.A) (A := R)),
    ConditionOn.of_algEquiv (ULift.algEquiv (R := S.A) (A := R)).symm⟩

/-- If an ideal `I` of `A` corepresents the flatness condition of Stacks Tag 05ML, then the
ideals which flatten the situation are exactly the ideals containing `I`.

For a proper ideal `J` the quotient `A ⧸ J` is itself a local `A`-algebra, lifted into the
universe of the test algebras by `Module.FlatAtPointSituation.conditionOn_ulift_iff`, and the
kernel of `A → A ⧸ J` is `J`. The improper ideal flattens the situation for want of a prime to
test. -/
theorem flattens_iff_le_of_condition_iff {S : FlatAtPointSituation.{u, v, w}} {I : Ideal S.A}
    (hI : ∀ R : LocalAlgCat.{u, max u x} S.A,
      S.Condition R ↔ Ideal.map (algebraMap S.A R) I = ⊥) (J : Ideal S.A) :
    S.Flattens J ↔ I ≤ J := by
  rcases eq_or_ne J ⊤ with rfl | hJ
  · exact ⟨fun _ ↦ le_top, fun _ ↦ S.flattens_top⟩
  have _ : Nontrivial (S.A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have _ : IsLocalRing (S.A ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have _ : IsLocalHom (algebraMap S.A (S.A ⧸ J)) :=
    IsLocalHom.of_surjective _ (by
      rw [Ideal.Quotient.algebraMap_eq]
      exact Ideal.Quotient.mk_surjective)
  have hquot : S.Flattens J ↔ S.ConditionOn (S.A ⧸ J) := by
    unfold Flattens ConditionOn
    rw [maximalIdeal_quotient hJ]
  have hlift : S.ConditionOn (ULift.{x} (S.A ⧸ J)) ↔
      Ideal.map (algebraMap S.A (ULift.{x} (S.A ⧸ J))) I = ⊥ :=
    hI { carrier := ULift.{x} (S.A ⧸ J) }
  refine hquot.trans (((S.conditionOn_ulift_iff (S.A ⧸ J)).symm.trans hlift).trans ?_)
  rw [Ideal.map_eq_bot_iff_le_ker, ULift.ker_algebraMap, Ideal.Quotient.algebraMap_eq,
    Ideal.mk_ker]

/-- The corepresentability statement of Stacks Tag 05PG, read on an unbundled local
`A`-algebra. -/
theorem conditionOn_iff_map_eq_bot_of_condition_iff {S : FlatAtPointSituation.{u, v, w}}
    {I : Ideal S.A}
    (hI : ∀ R : LocalAlgCat.{u, y} S.A, S.Condition R ↔ Ideal.map (algebraMap S.A R) I = ⊥)
    (R : Type y) [CommRing R] [IsLocalRing R] [Algebra S.A R]
    [IsLocalHom (algebraMap S.A R)] :
    S.ConditionOn R ↔ Ideal.map (algebraMap S.A R) I = ⊥ :=
  hI { carrier := R }

/-- **The two outstanding hypotheses of Stacks Tag 05PG are Stacks Tag 05PG.** That the
flattening ideals are closed under intersections and that the kernel of a local `A`-algebra
satisfying the flatness condition flattens the situation are, together, equivalent to the
existence of an ideal of `A` corepresenting the condition.

So the reduction carried out in `StacksFrontier.RingTheory.Flat.HenselianFlattening` is a
restatement, not a proof: `Module.FlatAtPointSituation.exists_ideal_conditionOn_iff_map_eq_bot`
is the forward implication here, and no proof of either hypothesis can avoid the dévissage
argument of the source. -/
theorem flattensSInf_and_flattensKer_iff_exists_ideal (S : FlatAtPointSituation.{u, v, w}) :
    (S.FlattensSInf ∧ S.FlattensKer.{u, v, w, max u x}) ↔
      ∃ I : Ideal S.A, ∀ R : LocalAlgCat.{u, max u x} S.A,
        S.Condition R ↔ Ideal.map (algebraMap S.A R) I = ⊥ := by
  refine ⟨fun h ↦ S.exists_ideal_conditionOn_iff_map_eq_bot h.1 h.2, ?_⟩
  rintro ⟨I, hI⟩
  refine ⟨fun 𝒥 _ h𝒥 ↦ (flattens_iff_le_of_condition_iff hI _).mpr
    (le_sInf fun J hJ ↦ (flattens_iff_le_of_condition_iff hI J).mp (h𝒥 J hJ)),
    fun R _ _ _ _ hR ↦ (flattens_iff_le_of_condition_iff hI _).mpr
      ((Ideal.map_eq_bot_iff_le_ker _).mp
        ((conditionOn_iff_map_eq_bot_of_condition_iff hI R).mp hR))⟩

/-- **All three hypotheses of Stacks Tag 05PG are Stacks Tag 05PG.** Adding the approximation of
a flattening ideal by a finitely generated one to the two outstanding hypotheses gives a
conjunction equivalent to the finite-generation half of Stacks Tag 05PG: a finitely generated
corepresenting ideal is itself the finitely generated approximation of every flattening ideal. -/
theorem flattensSInf_and_flattensKer_and_flattensFGApprox_iff_exists_fg
    (S : FlatAtPointSituation.{u, v, w}) :
    (S.FlattensSInf ∧ S.FlattensKer.{u, v, w, max u x} ∧ S.FlattensFGApprox) ↔
      ∃ I : Ideal S.A, I.FG ∧ ∀ R : LocalAlgCat.{u, max u x} S.A,
        S.Condition R ↔ Ideal.map (algebraMap S.A R) I = ⊥ := by
  refine ⟨fun h ↦ S.exists_fg_ideal_conditionOn_iff_map_eq_bot h.1 h.2.1 h.2.2, ?_⟩
  rintro ⟨I, hIfg, hI⟩
  obtain ⟨h₁, h₂⟩ := (flattensSInf_and_flattensKer_iff_exists_ideal S).mpr ⟨I, hI⟩
  exact ⟨h₁, h₂, fun I' hI' ↦ ⟨I, (flattens_iff_le_of_condition_iff hI I').mp hI', hIfg,
    (flattens_iff_le_of_condition_iff hI I).mpr le_rfl⟩⟩

/-- The closure of the flattening ideals under intersections says no more and no less than that
the smallest flattening ideal flattens the situation: the smallest flattening ideal is below
every member of a family of flattening ideals, hence below its infimum, and the flattening ideals
are closed upwards. -/
theorem flattensSInf_iff_flattens_flatteningIdeal (S : FlatAtPointSituation.{u, v, w}) :
    S.FlattensSInf ↔ S.Flattens S.flatteningIdeal :=
  ⟨flattens_flatteningIdeal, fun h _𝒥 _ h𝒥 ↦ h.mono (le_sInf fun J hJ ↦ sInf_le (h𝒥 J hJ))⟩

end Module.FlatAtPointSituation

end
