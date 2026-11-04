module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.NoDeformations.KoszulDeformationJoined
public import StacksFrontier.RingTheory.Flat.RegularSequenceOverBase
public import StacksFrontier.RingTheory.Koszul.DerivedQuotientModel
public import StacksCore.Tactic.StacksAttribute

/-!
# The lifted sequence of a flat local Koszul deformation is regular with flat quotient

`AlgebraicGeometry.exists_koszulDescription_of_fibrewise_koszul` produces, for a flat local
Koszul deformation situation, a sequence `f₁, …, f_r` in `A` lifting the given fibrewise regular
sequence and a Koszul description `K ≅ K(A; f₁, …, f_r)` in `D(A)`. [Stacks, Tag 0G0N] asserts two
further properties of that sequence: it is regular in `A`, and the quotient `A/(f₁, …, f_r)` is
flat over `R`. This file adds them.

Both are needed by Case II of [Stacks, Tag 0G0R]: the regularity is what makes the closed
subscheme the sequence cuts out a regular immersion, and the flatness of the quotient is what
makes that subscheme flat over the base, which is the hypothesis the spreading-out step and
[Stacks, Tag 0G0Q] consume.

## Main results

* `AlgebraicGeometry.exists_koszulDescription_and_flat_quotient_of_fibrewise_koszul` — the
  sequence of [Stacks, Tag 0G0N] with all three of its properties: it lifts the fibrewise
  sequence, it is regular in `A`, its quotient is flat over `R`, and its Koszul complex
  represents `K`.
* `AlgebraicGeometry.exists_quotient_description_and_flat_quotient_of_fibrewise_koszul` — the
  same, with the Koszul complex replaced by what it represents: `K` is `A ⧸ (f_1, …, f_r)` placed
  in degree zero. A regular sequence is Koszul-regular ([Stacks, Tag 062F]) and the Koszul complex
  of a Koszul-regular sequence is a resolution of the quotient, so the two descriptions are the
  same statement; this is the form a consumer that wants a *module* rather than a complex -- for
  instance one computing the annihilator of `H^0` -- can use.

## Implementation notes

The witness is the one `AlgebraicGeometry.exists_koszulDescription_of_fibrewise_koszul` already
produces; nothing of the free-lift construction is repeated. The two extra conclusions depend only
on the lifting property, through
`Module.Flat.isRegular_and_flat_quotient_ofList_smul_of_isRegular_maximalIdeal`
([Stacks, Tag 0470]) applied to the module `M = A`: its hypothesis is regularity of the lifted
sequence on `A ⧸ 𝔪_R A`, which is the regularity the deformation situation carries for the
fibrewise sequence, transported along `A → A/𝔪_R A` by
`RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff` for the weakly regular half and by
`Ideal.smul_restrictScalars` for the nonvanishing half.

Tag 0470 yields flatness of every partial quotient by
`Ideal.ofList ((List.ofFn f).take i) • (⊤ : Submodule A A)`; at `i = r` the list is all of
`List.ofFn f`, whose `Ideal.ofList` is `Ideal.span (Set.range f)` by `List.mem_ofFn`, and
smul of the top submodule of `A` over itself returns the ideal.

The essential finite presentation of the algebra map is carried by the deformation situation as
`IsEssentiallyOfFinitePresentation`, while Tag 0470 takes it in the `RingHom` spelling
`RingHom.EssentiallyOfFinitePresentation`; the two are the same data and the conversion is
unfolding the witness tower.

## References

* [Stacks Project, Tag 0G0N](https://stacks.math.columbia.edu/tag/0G0N)
* [Stacks Project, Tag 0470](https://stacks.math.columbia.edu/tag/0470)
* [Stacks Project, Tag 0G0R](https://stacks.math.columbia.edu/tag/0G0R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-- A lift `f` of the fibrewise regular sequence is regular on the closed fibre `A ⧸ 𝔪_R A`, the
hypothesis of [Stacks, Tag 0470]. -/
public theorem FlatLocalKoszulDeformationSituation.isRegular_quotient_of_lift
    (S : FlatLocalKoszulDeformationSituation.{u}) (f : Fin S.r → S.A) :
    let I := Ideal.map (algebraMap S.R S.A) (IsLocalRing.maximalIdeal S.R)
    (∀ i, Ideal.Quotient.mk I (f i) = S.residueSequence i) →
      RingTheory.Sequence.IsRegular (S.A ⧸ (I • (⊤ : Submodule S.A S.A))) (List.ofFn f) := by
  intro I hfbar
  let L := S.A ⧸ I
  have hmap : List.map (Ideal.Quotient.mk I) (List.ofFn f) = List.ofFn S.residueSequence := by
    rw [List.map_ofFn]
    exact congrArg List.ofFn (funext hfbar)
  have hweak : RingTheory.Sequence.IsWeaklyRegular L (List.ofFn f) := by
    have hmapweak : RingTheory.Sequence.IsWeaklyRegular L
        ((List.ofFn f).map (Ideal.Quotient.mk I)) := by
      rw [hmap]
      exact S.residueSequence_regular.toIsWeaklyRegular
    exact (RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff
      (S := L) (M := L) (List.ofFn f)).mp hmapweak
  have htop : (⊤ : Submodule S.A L) ≠ Ideal.ofList (List.ofFn f) • (⊤ : Submodule S.A L) := by
    intro h
    have heq :
        (Ideal.ofList (List.ofFn S.residueSequence) • (⊤ : Submodule L L)).restrictScalars S.A =
          Ideal.ofList (List.ofFn f) • (⊤ : Submodule S.A L) := by
      rw [← hmap, ← Ideal.map_ofList]
      exact (Ideal.smul_restrictScalars (Ideal.ofList (List.ofFn f))
        (⊤ : Submodule L L)).trans (by simp)
    have hrestrict : (⊤ : Submodule L L).restrictScalars S.A =
        (Ideal.ofList (List.ofFn S.residueSequence) •
          (⊤ : Submodule L L)).restrictScalars S.A := by
      rw [Submodule.restrictScalars_top, h, heq]
    exact S.residueSequence_regular.top_ne_smul
      ((Submodule.restrictScalars_inj S.A L L).mp hrestrict)
  rw [show I • (⊤ : Submodule S.A S.A) = I by simp]
  exact ⟨hweak, htop⟩

/-- **The lifted sequence of [Stacks, Tag 0G0N] is regular with flat quotient.** In a flat local
deformation situation `R → A` whose closed fibre is Koszul on the regular sequence `f̄`, there is a
sequence `f` in `A` reducing to `f̄` modulo `𝔪_R A` which is regular in `A`, whose quotient
`A/(f)` is flat over `R`, and whose Koszul complex represents the deformed perfect complex `K` in
`D(A)`. -/
@[stacks 0G0N "The hypotheses are packaged as `FlatLocalKoszulDeformationSituation`. The Koszul
complex is Mathlib's exterior-algebra complex `Koszul.seqComplex`, placed in cohomological degrees
by `ComplexShape.embeddingDownNat`, and `K` is identified with its image under
`DerivedCategory.Q`. The ideal `(f₁, …, f_r)` is `Ideal.span (Set.range f)` and \"regular
sequence\" is Mathlib's `RingTheory.Sequence.IsRegular`, which is Definition 00LF verbatim."]
public theorem exists_koszulDescription_and_flat_quotient_of_fibrewise_koszul
    (S : FlatLocalKoszulDeformationSituation.{u}) :
    letI : CommRing S.A := S.commRingA
    let I := Ideal.map (algebraMap S.R S.A) (IsLocalRing.maximalIdeal S.R)
    ∃ f : Fin S.r → S.A,
      (∀ i, Ideal.Quotient.mk I (f i) = S.residueSequence i) ∧
        RingTheory.Sequence.IsRegular S.A (List.ofFn f) ∧
          Module.Flat S.R (S.A ⧸ Ideal.span (Set.range f)) ∧
            Nonempty (S.K ≅ DerivedCategory.Q.obj
              ((Koszul.seqComplex f).extend ComplexShape.embeddingDownNat)) := by
  classical
  intro I
  obtain ⟨f, hfbar, hiso⟩ := exists_koszulDescription_of_fibrewise_koszul S
  have hfp : (algebraMap S.R S.A).EssentiallyOfFinitePresentation := by
    rcases S.essentiallyOfFinitePresentation with ⟨T, hT, hRT, hfin, M, hTS, hTower, hLoc⟩
    let : CommRing T := hT
    let : Algebra S.R T := hRT
    let : Algebra T S.A := hTS
    exact ⟨T, inferInstance, inferInstance, inferInstance, hTower, hfin, M, hLoc⟩
  obtain ⟨hreg, hflat⟩ :=
    Module.Flat.isRegular_and_flat_quotient_ofList_smul_of_isRegular_maximalIdeal
      (M := S.A) hfp (List.ofFn f) (S.isRegular_quotient_of_lift f hfbar)
  have hspan : Ideal.ofList ((List.ofFn f).take S.r) • (⊤ : Submodule S.A S.A) =
      (Ideal.span (Set.range f) : Submodule S.A S.A) := by
    rw [List.take_of_length_le (by simp),
      show Ideal.ofList (List.ofFn f) = Ideal.span (Set.range f) from
        congrArg Ideal.span (Set.ext fun _ => List.mem_ofFn)]
    simp
  refine ⟨f, hfbar, hreg, ?_, hiso⟩
  have := hflat S.r
  rwa [hspan] at this

/-- **[Stacks, Tag 0G0N] with its Koszul complex replaced by the module it resolves.** In a flat
local deformation situation `R → A` whose closed fibre is Koszul on the regular sequence `f̄`,
there is a sequence `f` in `A` reducing to `f̄` modulo `𝔪_R A` which is regular in `A`, whose
quotient `A/(f)` is flat over `R`, and for which the deformed perfect complex `K` is that
quotient placed in degree zero.

A regular sequence is Koszul-regular ([Stacks, Tag 062F]) and the Koszul complex of a
Koszul-regular sequence is a resolution of the quotient
(`Koszul.nonempty_Q_obj_seqCochainComplex_iso_single`), so this is the preceding statement read
through that resolution. -/
public theorem exists_quotient_description_and_flat_quotient_of_fibrewise_koszul
    (S : FlatLocalKoszulDeformationSituation.{u}) :
    letI : CommRing S.A := S.commRingA
    let I := Ideal.map (algebraMap S.R S.A) (IsLocalRing.maximalIdeal S.R)
    ∃ f : Fin S.r → S.A,
      (∀ i, Ideal.Quotient.mk I (f i) = S.residueSequence i) ∧
        RingTheory.Sequence.IsRegular S.A (List.ofFn f) ∧
          Module.Flat S.R (S.A ⧸ Ideal.span (Set.range f)) ∧
            Nonempty (S.K ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} S.A) 0).obj
              (ModuleCat.of S.A (S.A ⧸ Ideal.span (Set.range f)))) := by
  intro I
  obtain ⟨f, hfbar, hreg, hflat, ⟨hiso⟩⟩ :=
    exists_koszulDescription_and_flat_quotient_of_fibrewise_koszul S
  refine ⟨f, hfbar, hreg, hflat, ?_⟩
  obtain ⟨hquot⟩ := Koszul.nonempty_Q_obj_seqCochainComplex_iso_single f
    (Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular (M := S.A) |>.2.2 hreg)
  exact ⟨hiso ≪≫ hquot⟩

end AlgebraicGeometry

end
