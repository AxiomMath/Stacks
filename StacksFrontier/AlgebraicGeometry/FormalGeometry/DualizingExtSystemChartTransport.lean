module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DualizingExtFunctorBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DualizingExtFunctorShift
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DualizingExtLimitBaseChange
public import StacksFrontier.Homology.HomComplex.Evaluation.TensorHomRestrictKFlat
public import StacksFrontier.RingTheory.Dualizing.DimensionFunction
public import StacksFrontier.RingTheory.Dualizing.TotalDerivedExtensionScalarsDualizing

/-!
# The Ext system transported along `A → A_f → B → B_𝔮`

The route of [Stacks, Tag 0EHK] forms its cocone not over `A` but over the chart ring
`B = (A_f)^∧_{I A_f}`, and reads its per-point step at the local rings `B_𝔮`. This file composes
the base changes of `Stacks.Algebraization.dualizingExtSystem` along the three maps
`A → A_f → B → B_𝔮` into a single isomorphism of systems, and carries the hypotheses of each
step along the chain.

The two base changes of the chain and their cocone compatibilities already exist
(`Stacks.Algebraization.dualizingExtSystemLocalizationNatIso`,
`Stacks.Algebraization.dualizingExtSystemAdicCompletionNatIso`). What was missing, and is what
this file supplies, is the *chaining*: each step replaces `ω` by
`(totalDerivedExtensionScalars _).functor.obj ω` and asks again for a dualizing complex and for
finite terms at the new ring, so the steps do not compose until those two hypotheses are
re-established there.

## Main definitions

* `Stacks.Algebraization.dualizingExtSystemChartTransport` — the composite along `A → A_f → B`.
* `Stacks.Algebraization.dualizingExtSystemChartPrimeTransport` — the composite along
  `A → A_f → B → B_𝔮`.

## Main results

* `Stacks.Algebraization.isDualizingComplex_chartTransportComplex` and
  `Stacks.Algebraization.isDualizingComplex_chartPrimeTransportComplex` — the transported
  complex is dualizing at `B` and at `B_𝔮`.
* `Stacks.Algebraization.dualizingExtSystemChartTransport_hom_app` and
  `Stacks.Algebraization.dualizingExtSystemChartPrimeTransport_hom_app` — the component
  formulas.
* `Stacks.Algebraization.dualizingExtSystemChartTransport_hom_naturality` and
  `Stacks.Algebraization.dualizingExtSystemChartPrimeTransport_hom_naturality` — compatibility
  with the transition maps.
* `Stacks.Algebraization.dualizingExtSystemChartTransport_hom_app_comp_dualizingExtSystemToLimit`
  and its `ChartPrime` counterpart
  `..._dualizingExtSystemChartPrimeTransport_hom_app_comp_dualizingExtSystemToLimit`
  — compatibility with the cocone `α`, for the two-step and the three-step composite. Each
  carries the chain's `CategoryTheory.Limits.limit.post` factors, none of which is invertible,
  so they transport a cocone *forward* along the chain and give no descent back.
* `Stacks.Algebraization.isNormalizedDualizingComplex_chartPrimeTransportComplex_shift` — the
  landing on a *normalized* dualizing complex at `𝔮`, and
  `Stacks.Algebraization.dualizingExtSystemChartPrimeTransportShift` — the matching degree
  shift on the system.

## Implementation notes

**The cocone clause is not the per-step clauses read in turn.** Composing them leaves an earlier
step's `CategoryTheory.Limits.limit.post` factor on the wrong side of the next base change, and
moving it across is that base change's own naturality at that map. The chase is carried out once,
in the abstract, by `Stacks.Algebraization.comp_eq_map_comp_twoStep`, and the two composites below
are instances of it: the three-step one takes the two-step statement as its factorisation. The
abstract form is needed and not merely tidy — the objects of the concrete goal are spelled in
defeq-but-not-syntactic ways (`dualizingExtLimit M ω i` against
`(dualizingExtFunctor ω i).obj (op (limit M))`, the transported terms of a system against the
terms of the transported system), and the rewrites of the chase cannot be keyed on them.

**Neither hypothesis of a step needs new mathematics at the next ring, and both are discharged
here rather than assumed.**

*Dualizing.* `Dualizing.isDualizingComplex_totalDerivedExtensionScalars_isLocalization` and
`Dualizing.isDualizingComplex_totalDerivedExtensionScalars_adicCompletion` are [Stacks, Tag
0A7G] and [Stacks, Tag 0DWD] stated at exactly the functor the base change of an `Ext` system
produces, which is `(totalDerivedExtensionScalars _).functor` and not
`StacksDraft.PseudoCoherence.derivedExtensionScalars`. That change of functor is the reason the
chain closes, and it is why nothing here has to compare two spellings of the base change.

*Boundedness.* The hypothesis `hωge` of each step is `∃ b, ω.IsGE b`, and that is part of being
dualizing: it is `hω.bounded.1`. So the dualizing hypothesis carries the boundedness hypothesis
with it and the chain needs only the former.

*Finite terms.* `Stacks.DerivedTensorHomDiagonal.finite_extendScalars`, at each step.

**Why the target of a step is literally the Ext system of the base-changed data.**
`Stacks.Algebraization.dualizingExtSystemBaseChangeNatIso` states its target as
`M.rightOp ⋙ (ModuleCat.extendScalars _).op ⋙ dualizingExtFunctor _ i`, and
`Stacks.Algebraization.dualizingExtSystem` is `M.rightOp ⋙ dualizingExtFunctor _ i`
(`Stacks.Algebraization.dualizingExtSystem_eq`). Those two agree because
`(M ⋙ F).rightOp = M.rightOp ⋙ F.op` holds by definition — both send `n` to
`op (F.obj (M.obj (op n)))`. So no transport is needed to read a step's target as a system, and
the composites below are literal composites of the two existing isomorphisms.

**`B` is not local and the normalization at `𝔮` does not need it to be.** The last step of the
chain localizes at a prime of `B`, and `Dualizing.dualizingDimension_spec` gives a normalized
dualizing complex at a prime of *any* Noetherian ring carrying a dualizing complex, with the
normalizing shift named by `Dualizing.dualizingDimension`. The local hypothesis of
`Dualizing.isNormalizedDualizingComplex_localizationAtPrime_shift`, which
`Stacks.Algebraization.isNormalizedDualizingComplex_localizationAtPrime_shift_distanceToZ`
consumes at a point of `U ∩ Y`, is therefore not in the way here.

**The degree range is not shifted along this chain.** The bootstrap situation at `𝔮` that the
per-point step is read over is
`(Stacks.Algebraization.BootstrapSituation.chartCompletion f).atPrime 𝔮`, and both
`Stacks.Algebraization.BootstrapSituation.chartCompletion_s` and
`Stacks.Algebraization.BootstrapSituation.atPrime_s` are the identity on `s`. The shift by
`δ(𝔮)` that `StacksDraft.AlgebraicGeometry.FormalGeometry.DualizingNormalizedShiftAtPoint`
carries belongs to the *other* route to a situation at a point, the one of [Stacks, Tag 0EJ4]
part (3), where `B.s = s - δ^Y_Z(y)`. The last result below records the shift for the chain's
own route, where it is the normalizing shift of the transported complex and nothing else.

## References

* [Stacks Project, Tag 0EHK](https://stacks.math.columbia.edu/tag/0EHK), the consumer.
* [Stacks Project, Tag 0A7G](https://stacks.math.columbia.edu/tag/0A7G), the localization step.
* [Stacks Project, Tag 0DWD](https://stacks.math.columbia.edu/tag/0DWD), the completion step.
* [Stacks Project, Tag 0A7W](https://stacks.math.columbia.edu/tag/0A7W), the dimension function.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars)

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- **A dualizing complex is bounded below.** The hypothesis `hωge` that each base-change step
of the chain asks for is part of being dualizing, so the chain carries only the latter. -/
theorem exists_isGE_of_isDualizingComplex {R : Type u} [CommRing R] [IsNoetherianRing R]
    (K : DerivedCategory (ModuleCat.{u} R)) (hK : Dualizing.IsDualizingComplex K) :
    ∃ b : ℤ, K.IsGE b := by
  obtain ⟨b, hb⟩ := hK.bounded.1
  exact ⟨b, hb⟩

/-! ### The first two steps, `A → A_f → B` -/

section Chart

variable (I : Ideal A) (f : A) (ω : DerivedCategory (ModuleCat.{u} A))

/-- **Extension of scalars `A → A_f`**, the first step of the chain. A reducible name for the
functor the base changes below are read through; nothing about it is new. -/
abbrev chartAwayScalars : ModuleCat.{u} A ⥤ ModuleCat.{u} (Localization.Away f) :=
  ModuleCat.extendScalars.{u, u, u} (algebraMap A (Localization.Away f))

/-- **Extension of scalars `A_f → B = (A_f)^∧_{I A_f}`**, the second step of the chain. -/
abbrev chartCompletionScalars :
    ModuleCat.{u} (Localization.Away f) ⥤
      ModuleCat.{u}
        (AdicCompletion (I.map (algebraMap A (Localization.Away f)))
          (Localization.Away f)) :=
  ModuleCat.extendScalars.{u, u, u}
    (algebraMap (Localization.Away f)
      (AdicCompletion (I.map (algebraMap A (Localization.Away f)))
        (Localization.Away f)))

/-- **`ω` transported to the chart ring `B = (A_f)^∧_{I A_f}`.** The two base changes of the
route of [Stacks, Tag 0EHK], applied in turn to `ω`. -/
abbrev chartTransportComplex :
    DerivedCategory (ModuleCat.{u}
      (AdicCompletion (I.map (algebraMap A (Localization.Away f))) (Localization.Away f))) :=
  (totalDerivedExtensionScalars.{u, u, u}
      (algebraMap (Localization.Away f)
        (AdicCompletion (I.map (algebraMap A (Localization.Away f)))
          (Localization.Away f)))).functor.obj
    ((totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A (Localization.Away f))).functor.obj ω)

/-- **The module system transported to the chart ring.** -/
abbrev chartTransportSystem (M : ℕᵒᵖ ⥤ ModuleCat.{u} A) :
    ℕᵒᵖ ⥤ ModuleCat.{u}
      (AdicCompletion (I.map (algebraMap A (Localization.Away f))) (Localization.Away f)) :=
  (M ⋙ ModuleCat.extendScalars.{u, u, u} (algebraMap A (Localization.Away f))) ⋙
    ModuleCat.extendScalars.{u, u, u}
      (algebraMap (Localization.Away f)
        (AdicCompletion (I.map (algebraMap A (Localization.Away f)))
          (Localization.Away f)))

/-- **`ω` localized away from `f` is a dualizing complex over `A_f`**, [Stacks, Tag 0A7G] at the
functor the base change of the `Ext` system produces. -/
theorem isDualizingComplex_awayTransportComplex (hω : Dualizing.IsDualizingComplex ω) :
    Dualizing.IsDualizingComplex
      ((totalDerivedExtensionScalars.{u, u, u}
        (algebraMap A (Localization.Away f))).functor.obj ω) :=
  Dualizing.isDualizingComplex_totalDerivedExtensionScalars_isLocalization
    (B := Localization.Away f) (Submonoid.powers f) ω hω

/-- **`Stacks.Algebraization.chartTransportComplex` is a dualizing complex over the chart
ring.** [Stacks, Tag 0A7G] then [Stacks, Tag 0DWD], each at the total derived functor of
extension of scalars. -/
theorem isDualizingComplex_chartTransportComplex (hω : Dualizing.IsDualizingComplex ω) :
    Dualizing.IsDualizingComplex (chartTransportComplex I f ω) :=
  Dualizing.isDualizingComplex_totalDerivedExtensionScalars_adicCompletion _ _
    (isDualizingComplex_awayTransportComplex f ω hω)

omit [IsNoetherianRing A] in
/-- The terms of `Stacks.Algebraization.chartTransportSystem` are finite over the chart ring. -/
theorem finite_chartTransportSystem (M : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hfin : ∀ n : ℕ, Module.Finite A (M.obj (op n))) (n : ℕ) :
    Module.Finite
      (AdicCompletion (I.map (algebraMap A (Localization.Away f))) (Localization.Away f))
      ((chartTransportSystem I f M).obj (op n)) :=
  let : Module.Finite A (M.obj (op n)) := hfin n
  let : Module.Finite (Localization.Away f)
      ((M ⋙ ModuleCat.extendScalars.{u, u, u}
        (algebraMap A (Localization.Away f))).obj (op n)) :=
    Stacks.DerivedTensorHomDiagonal.finite_extendScalars
      (algebraMap A (Localization.Away f)) (M.obj (op n))
  Stacks.DerivedTensorHomDiagonal.finite_extendScalars _ _

/-- **The `Ext` system transported to the chart ring `B = (A_f)^∧_{I A_f}`.** The composite of
`Stacks.Algebraization.dualizingExtSystemLocalizationNatIso` at the powers of `f` with
`Stacks.Algebraization.dualizingExtSystemAdicCompletionNatIso` at the extended ideal.

The two steps compose because the dualizing hypothesis is re-established at `A_f` by
`Stacks.Algebraization.isDualizingComplex_awayTransportComplex` and carries with it the
boundedness each step asks for, and because the terms stay finite by
`Stacks.Algebraization.finite_chartTransportSystem`. See the implementation notes of this
file. -/
def dualizingExtSystemChartTransport (hω : Dualizing.IsDualizingComplex ω) (i : ℤ)
    (M : ℕᵒᵖ ⥤ ModuleCat.{u} A) (hfin : ∀ n : ℕ, Module.Finite A (M.obj (op n))) :
    (dualizingExtSystem M ω i ⋙
        ModuleCat.extendScalars.{u, u, u} (algebraMap A (Localization.Away f))) ⋙
      ModuleCat.extendScalars.{u, u, u}
        (algebraMap (Localization.Away f)
          (AdicCompletion (I.map (algebraMap A (Localization.Away f)))
            (Localization.Away f))) ≅
      dualizingExtSystem (chartTransportSystem I f M) (chartTransportComplex I f ω) i :=
  Functor.isoWhiskerRight
      (dualizingExtSystemLocalizationNatIso (Submonoid.powers f) ω
        (exists_isGE_of_isDualizingComplex ω hω) i M hfin)
      (ModuleCat.extendScalars.{u, u, u}
        (algebraMap (Localization.Away f)
          (AdicCompletion (I.map (algebraMap A (Localization.Away f)))
            (Localization.Away f)))) ≪≫
    dualizingExtSystemAdicCompletionNatIso (I.map (algebraMap A (Localization.Away f)))
      ((totalDerivedExtensionScalars.{u, u, u}
        (algebraMap A (Localization.Away f))).functor.obj ω)
      (exists_isGE_of_isDualizingComplex _ (isDualizingComplex_awayTransportComplex f ω hω)) i
      (M ⋙ ModuleCat.extendScalars.{u, u, u} (algebraMap A (Localization.Away f)))
      (fun n =>
        letI : Module.Finite A (M.obj (op n)) := hfin n
        Stacks.DerivedTensorHomDiagonal.finite_extendScalars
          (algebraMap A (Localization.Away f)) (M.obj (op n)))

/-- **The components of `Stacks.Algebraization.dualizingExtSystemChartTransport`** are the
components of the two flat comparisons of the chain, the first one base changed along the
second. -/
theorem dualizingExtSystemChartTransport_hom_app (hω : Dualizing.IsDualizingComplex ω) (i : ℤ)
    (M : ℕᵒᵖ ⥤ ModuleCat.{u} A) (hfin : ∀ n : ℕ, Module.Finite A (M.obj (op n))) (n : ℕ) :
    (dualizingExtSystemChartTransport I f ω hω i M hfin).hom.app n =
      (ModuleCat.extendScalars.{u, u, u}
            (algebraMap (Localization.Away f)
              (AdicCompletion (I.map (algebraMap A (Localization.Away f)))
                (Localization.Away f)))).map
          ((dualizingExtFunctorLocalizationBaseChange (Submonoid.powers f) ω i).app
            (op (M.obj (op n)))) ≫
        (dualizingExtFunctorAdicCompletionBaseChange
            (I.map (algebraMap A (Localization.Away f)))
            ((totalDerivedExtensionScalars.{u, u, u}
              (algebraMap A (Localization.Away f))).functor.obj ω) i).app
          (op ((M ⋙ ModuleCat.extendScalars.{u, u, u}
            (algebraMap A (Localization.Away f))).obj (op n))) :=
  rfl

/-- **`Stacks.Algebraization.dualizingExtSystemChartTransport` is compatible with the transition
maps**, being an isomorphism of systems and not merely a family of isomorphisms of modules.
This is its naturality, and it is what the route of [Stacks, Tag 0EHK] needs: the equality of
transition images it proves over `B` is a statement about the transition maps. -/
theorem dualizingExtSystemChartTransport_hom_naturality (hω : Dualizing.IsDualizingComplex ω)
    (i : ℤ) (M : ℕᵒᵖ ⥤ ModuleCat.{u} A) (hfin : ∀ n : ℕ, Module.Finite A (M.obj (op n)))
    {m n : ℕ} (h : m ≤ n) :
    ((dualizingExtSystem M ω i ⋙
            ModuleCat.extendScalars.{u, u, u} (algebraMap A (Localization.Away f))) ⋙
          ModuleCat.extendScalars.{u, u, u}
            (algebraMap (Localization.Away f)
              (AdicCompletion (I.map (algebraMap A (Localization.Away f)))
                (Localization.Away f)))).map (homOfLE h) ≫
        (dualizingExtSystemChartTransport I f ω hω i M hfin).hom.app n =
      (dualizingExtSystemChartTransport I f ω hω i M hfin).hom.app m ≫
        (dualizingExtSystem (chartTransportSystem I f M)
          (chartTransportComplex I f ω) i).map (homOfLE h) :=
  (dualizingExtSystemChartTransport I f ω hω i M hfin).hom.naturality (homOfLE h)

/-- **`Stacks.Algebraization.dualizingExtSystemChartTransport` carries the cocone `α` of the
system over `A` to the cocone `α` of the transported system over the chart ring**, up to the
comparison of the two base changes with the limit of the system.

This is the cocone clause of the composite, and it is *not* the two per-step clauses
`Stacks.Algebraization.extendScalars_map_dualizingExtSystemToLimit_comp_localizationBaseChange`
and
`Stacks.Algebraization.extendScalars_map_dualizingExtSystemToLimit_comp_adicCompletionBaseChange`
read in turn: composing them moves the first step's `CategoryTheory.Limits.limit.post` factor
across the second base change, which is the naturality of
`Stacks.Algebraization.dualizingExtFunctorAdicCompletionBaseChange` at that very map. What comes
out is the single factor
`F₂.map (limit.post M F₁) ≫ limit.post (M ⋙ F₁) F₂` below, written as the honest composite of
the two comparisons rather than as `limit.post M (F₁ ⋙ F₂)`.

**The factor is not invertible and this statement does not claim it is.** For the adic quotient
tower the comparison of the completion with the limit is not an isomorphism — see the docstring
of
`Stacks.Algebraization.extendScalars_map_dualizingExtSystemToLimit_comp_adicCompletionBaseChange`
— so this clause transports the cocone *forward* along the chain and supplies no descent
backwards along it. Forward is the direction the route of [Stacks, Tag 0EHK] uses it in: the
cocone whose transition images are compared lives over the chart ring. -/
theorem dualizingExtSystemChartTransport_hom_app_comp_dualizingExtSystemToLimit
    (hω : Dualizing.IsDualizingComplex ω) (i : ℤ) (M : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hfin : ∀ n : ℕ, Module.Finite A (M.obj (op n))) (n : ℕ) :
    (ModuleCat.extendScalars.{u, u, u}
            (algebraMap (Localization.Away f)
              (AdicCompletion (I.map (algebraMap A (Localization.Away f)))
                (Localization.Away f)))).map
          ((ModuleCat.extendScalars.{u, u, u} (algebraMap A (Localization.Away f))).map
            (dualizingExtSystemToLimit M ω i n)) ≫
        (ModuleCat.extendScalars.{u, u, u}
              (algebraMap (Localization.Away f)
                (AdicCompletion (I.map (algebraMap A (Localization.Away f)))
                  (Localization.Away f)))).map
            ((dualizingExtFunctorLocalizationBaseChange (Submonoid.powers f) ω i).app
              (op (CategoryTheory.Limits.limit M))) ≫
          (dualizingExtFunctorAdicCompletionBaseChange
              (I.map (algebraMap A (Localization.Away f)))
              ((totalDerivedExtensionScalars.{u, u, u}
                (algebraMap A (Localization.Away f))).functor.obj ω) i).app
            (op ((ModuleCat.extendScalars.{u, u, u}
              (algebraMap A (Localization.Away f))).obj
                (CategoryTheory.Limits.limit M))) =
      (dualizingExtSystemChartTransport I f ω hω i M hfin).hom.app n ≫
        dualizingExtSystemToLimit (chartTransportSystem I f M)
            (chartTransportComplex I f ω) i n ≫
          (dualizingExtFunctor (chartTransportComplex I f ω) i).map
            ((ModuleCat.extendScalars.{u, u, u}
                  (algebraMap (Localization.Away f)
                    (AdicCompletion (I.map (algebraMap A (Localization.Away f)))
                      (Localization.Away f)))).map
                (CategoryTheory.Limits.limit.post M
                  (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Localization.Away f)))) ≫
              CategoryTheory.Limits.limit.post
                (M ⋙ ModuleCat.extendScalars.{u, u, u} (algebraMap A (Localization.Away f)))
                (ModuleCat.extendScalars.{u, u, u}
                  (algebraMap (Localization.Away f)
                    (AdicCompletion (I.map (algebraMap A (Localization.Away f)))
                      (Localization.Away f))))).op := by
  let D₁ := totalDerivedExtensionScalars.{u, u, u} (algebraMap A (Localization.Away f))
  let D₂ := totalDerivedExtensionScalars.{u, u, u}
    (algebraMap (Localization.Away f)
      (AdicCompletion (I.map (algebraMap A (Localization.Away f))) (Localization.Away f)))
  let cmp₁ : DerivedCategory.Q ⋙ D₁.functor ⟶
      (ModuleCat.extendScalars.{u, u, u}
          (algebraMap A (Localization.Away f))).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q := D₁.comparison
  let cmp₂ : DerivedCategory.Q ⋙ D₂.functor ⟶
      (ModuleCat.extendScalars.{u, u, u}
          (algebraMap (Localization.Away f)
            (AdicCompletion (I.map (algebraMap A (Localization.Away f)))
              (Localization.Away f)))).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q := D₂.comparison
  let : D₁.functor.IsLeftDerivedFunctor cmp₁
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) := D₁.isLeftDerived
  let : D₂.functor.IsLeftDerivedFunctor cmp₂
      (HomologicalComplex.quasiIso (ModuleCat.{u} (Localization.Away f))
        (ComplexShape.up ℤ)) :=
    D₂.isLeftDerived
  exact extendScalars_map_dualizingExtSystemToLimit_comp_baseChange_twoStep
    D₁.functor cmp₁ D₂.functor cmp₂
    (RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat (Localization.Away f) (Submonoid.powers f)))
    (RingHom.flat_algebraMap_iff.mpr inferInstance) ω i M n

end Chart

/-! ### The third step, `B → B_𝔮` -/

section ChartPrime

variable (I : Ideal A) (f : A) (ω : DerivedCategory (ModuleCat.{u} A))
  (𝔮 : PrimeSpectrum
    (AdicCompletion (I.map (algebraMap A (Localization.Away f))) (Localization.Away f)))

/-- **Extension of scalars `B → B_𝔮`**, the third step of the chain. -/
abbrev chartPrimeScalars :
    ModuleCat.{u}
        (AdicCompletion (I.map (algebraMap A (Localization.Away f)))
          (Localization.Away f)) ⥤
      ModuleCat.{u} (Localization.AtPrime 𝔮.asIdeal) :=
  ModuleCat.extendScalars.{u, u, u}
    (algebraMap
      (AdicCompletion (I.map (algebraMap A (Localization.Away f))) (Localization.Away f))
      (Localization.AtPrime 𝔮.asIdeal))

/-- **`ω` transported to the local ring `B_𝔮` of the chart ring at a prime.** The third base
change of the route of [Stacks, Tag 0EHK], applied to
`Stacks.Algebraization.chartTransportComplex`. -/
abbrev chartPrimeTransportComplex :
    DerivedCategory (ModuleCat.{u} (Localization.AtPrime 𝔮.asIdeal)) :=
  (totalDerivedExtensionScalars.{u, u, u}
      (algebraMap
        (AdicCompletion (I.map (algebraMap A (Localization.Away f))) (Localization.Away f))
        (Localization.AtPrime 𝔮.asIdeal))).functor.obj (chartTransportComplex I f ω)

/-- **The module system transported to `B_𝔮`.** -/
abbrev chartPrimeTransportSystem (M : ℕᵒᵖ ⥤ ModuleCat.{u} A) :
    ℕᵒᵖ ⥤ ModuleCat.{u} (Localization.AtPrime 𝔮.asIdeal) :=
  chartTransportSystem I f M ⋙
    ModuleCat.extendScalars.{u, u, u}
      (algebraMap
        (AdicCompletion (I.map (algebraMap A (Localization.Away f))) (Localization.Away f))
        (Localization.AtPrime 𝔮.asIdeal))

/-- **`Stacks.Algebraization.chartPrimeTransportComplex` is a dualizing complex over `B_𝔮`.**
[Stacks, Tag 0A7G] once more, at the prime `𝔮` of the chart ring. -/
theorem isDualizingComplex_chartPrimeTransportComplex (hω : Dualizing.IsDualizingComplex ω) :
    Dualizing.IsDualizingComplex (chartPrimeTransportComplex I f ω 𝔮) :=
  have : 𝔮.asIdeal.IsPrime := 𝔮.isPrime
  Dualizing.isDualizingComplex_totalDerivedExtensionScalars_isLocalization
    (B := Localization.AtPrime 𝔮.asIdeal) 𝔮.asIdeal.primeCompl _
    (isDualizingComplex_chartTransportComplex I f ω hω)

/-- **The `Ext` system transported all the way to `B_𝔮`.** The composite of
`Stacks.Algebraization.dualizingExtSystemChartTransport` with
`Stacks.Algebraization.dualizingExtSystemLocalizationNatIso` at `𝔮.asIdeal.primeCompl`, which
that isomorphism permits because it is stated for an arbitrary submonoid.

This is the system the per-point step of the route of [Stacks, Tag 0EHK] is read on:
`Stacks.Algebraization.exists_range_transitionMap_eq_dualizingExtSystem_bootstrap` asks only for
a *dualizing* complex at the ring, which
`Stacks.Algebraization.isDualizingComplex_chartPrimeTransportComplex` supplies, and its degree
range `i ≤ B.s` is the original `s` by
`Stacks.Algebraization.BootstrapSituation.chartCompletion_s` and
`Stacks.Algebraization.BootstrapSituation.atPrime_s`. -/
def dualizingExtSystemChartPrimeTransport (hω : Dualizing.IsDualizingComplex ω) (i : ℤ)
    (M : ℕᵒᵖ ⥤ ModuleCat.{u} A) (hfin : ∀ n : ℕ, Module.Finite A (M.obj (op n))) :
    ((dualizingExtSystem M ω i ⋙
          ModuleCat.extendScalars.{u, u, u} (algebraMap A (Localization.Away f))) ⋙
        ModuleCat.extendScalars.{u, u, u}
          (algebraMap (Localization.Away f)
            (AdicCompletion (I.map (algebraMap A (Localization.Away f)))
              (Localization.Away f)))) ⋙
      ModuleCat.extendScalars.{u, u, u}
        (algebraMap
          (AdicCompletion (I.map (algebraMap A (Localization.Away f))) (Localization.Away f))
          (Localization.AtPrime 𝔮.asIdeal)) ≅
      dualizingExtSystem (chartPrimeTransportSystem I f 𝔮 M)
        (chartPrimeTransportComplex I f ω 𝔮) i :=
  Functor.isoWhiskerRight (dualizingExtSystemChartTransport I f ω hω i M hfin) _ ≪≫
    dualizingExtSystemLocalizationNatIso 𝔮.asIdeal.primeCompl _
      (exists_isGE_of_isDualizingComplex _
        (isDualizingComplex_chartTransportComplex I f ω hω)) i _
      (finite_chartTransportSystem I f M hfin)

/-- **The components of `Stacks.Algebraization.dualizingExtSystemChartPrimeTransport**: the
component of the two-step transport, base changed to `B_𝔮`, followed by the component of the
localization comparison at `𝔮`. -/
theorem dualizingExtSystemChartPrimeTransport_hom_app (hω : Dualizing.IsDualizingComplex ω)
    (i : ℤ) (M : ℕᵒᵖ ⥤ ModuleCat.{u} A) (hfin : ∀ n : ℕ, Module.Finite A (M.obj (op n)))
    (n : ℕ) :
    (dualizingExtSystemChartPrimeTransport I f ω 𝔮 hω i M hfin).hom.app n =
      (ModuleCat.extendScalars.{u, u, u}
            (algebraMap
              (AdicCompletion (I.map (algebraMap A (Localization.Away f)))
                (Localization.Away f))
              (Localization.AtPrime 𝔮.asIdeal))).map
          ((dualizingExtSystemChartTransport I f ω hω i M hfin).hom.app n) ≫
        (dualizingExtFunctorLocalizationBaseChange 𝔮.asIdeal.primeCompl
            (chartTransportComplex I f ω) i).app
          (op ((chartTransportSystem I f M).obj (op n))) :=
  rfl

/-- **`Stacks.Algebraization.dualizingExtSystemChartPrimeTransport` is compatible with the
transition maps.** Its naturality. -/
theorem dualizingExtSystemChartPrimeTransport_hom_naturality
    (hω : Dualizing.IsDualizingComplex ω) (i : ℤ) (M : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hfin : ∀ n : ℕ, Module.Finite A (M.obj (op n))) {m n : ℕ} (h : m ≤ n) :
    (((dualizingExtSystem M ω i ⋙
              ModuleCat.extendScalars.{u, u, u} (algebraMap A (Localization.Away f))) ⋙
            ModuleCat.extendScalars.{u, u, u}
              (algebraMap (Localization.Away f)
                (AdicCompletion (I.map (algebraMap A (Localization.Away f)))
                  (Localization.Away f)))) ⋙
          ModuleCat.extendScalars.{u, u, u}
            (algebraMap
              (AdicCompletion (I.map (algebraMap A (Localization.Away f)))
                (Localization.Away f))
              (Localization.AtPrime 𝔮.asIdeal))).map (homOfLE h) ≫
        (dualizingExtSystemChartPrimeTransport I f ω 𝔮 hω i M hfin).hom.app n =
      (dualizingExtSystemChartPrimeTransport I f ω 𝔮 hω i M hfin).hom.app m ≫
        (dualizingExtSystem (chartPrimeTransportSystem I f 𝔮 M)
          (chartPrimeTransportComplex I f ω 𝔮) i).map (homOfLE h) :=
  (dualizingExtSystemChartPrimeTransport I f ω 𝔮 hω i M hfin).hom.naturality (homOfLE h)

/-- **`Stacks.Algebraization.dualizingExtSystemChartPrimeTransport` carries the cocone `α` of
the system over `A` to the cocone `α` of the transported system over `B_𝔮`**, up to the
comparison of the three base changes of the chain with the limit of the system. This is the
cocone clause of the three-step composite, and it is what the per-point step of
[Stacks, Tag 0EHK] is read against.

It is `Stacks.Algebraization.comp_eq_map_comp_twoStep` with
`Stacks.Algebraization.dualizingExtSystemChartTransport_hom_app_comp_dualizingExtSystemToLimit`
as the factorisation over `B` and the localization comparison at `𝔮` as the third step — not a
fresh chase, and not the two-step statement read again either: the third base change has to be
carried past the comparison factor already present, which is its own naturality at that map.

The comparison factor is left as the composite of the two `H^{-i}(RHom_{B_𝔮}(-, -))` of the
chain's halves rather than collapsed into one; the two forms differ by a single
`CategoryTheory.Functor.map_comp` with `CategoryTheory.op_comp`, and this is the form in which
each half can be recognised.

**No half of the factor is invertible and this statement does not claim any is.** For the first
two see the docstring of
`Stacks.Algebraization.dualizingExtSystemChartTransport_hom_app_comp_dualizingExtSystemToLimit`;
the third is `CategoryTheory.Limits.limit.post` for a localization, which does not commute with
the limit of the adic quotient tower either. So this transports the cocone forward to `B_𝔮` and
gives no descent back along the chain. -/
theorem dualizingExtSystemChartPrimeTransport_hom_app_comp_dualizingExtSystemToLimit
    (hω : Dualizing.IsDualizingComplex ω) (i : ℤ) (M : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hfin : ∀ n : ℕ, Module.Finite A (M.obj (op n))) (n : ℕ) :
    (chartPrimeScalars I f 𝔮).map
          ((chartCompletionScalars I f).map
            ((chartAwayScalars f).map (dualizingExtSystemToLimit M ω i n))) ≫
        (chartPrimeScalars I f 𝔮).map
            ((chartCompletionScalars I f).map
                ((dualizingExtFunctorLocalizationBaseChange (Submonoid.powers f) ω i).app
                  (op (CategoryTheory.Limits.limit M))) ≫
              (dualizingExtFunctorAdicCompletionBaseChange
                  (I.map (algebraMap A (Localization.Away f)))
                  ((totalDerivedExtensionScalars.{u, u, u}
                    (algebraMap A (Localization.Away f))).functor.obj ω) i).app
                (op ((chartAwayScalars f).obj (CategoryTheory.Limits.limit M)))) ≫
          (dualizingExtFunctorLocalizationBaseChange 𝔮.asIdeal.primeCompl
              (chartTransportComplex I f ω) i).app
            (op ((chartCompletionScalars I f).obj
              ((chartAwayScalars f).obj (CategoryTheory.Limits.limit M)))) =
      ((chartPrimeScalars I f 𝔮).map
            ((dualizingExtSystemChartTransport I f ω hω i M hfin).hom.app n) ≫
          (dualizingExtFunctorLocalizationBaseChange 𝔮.asIdeal.primeCompl
              (chartTransportComplex I f ω) i).app
            (op ((chartTransportSystem I f M).obj (op n)))) ≫
        dualizingExtSystemToLimit (chartPrimeTransportSystem I f 𝔮 M)
            (chartPrimeTransportComplex I f ω 𝔮) i n ≫
          ((dualizingExtFunctor (chartPrimeTransportComplex I f ω 𝔮) i).map
              (CategoryTheory.Limits.limit.post (chartTransportSystem I f M)
                (chartPrimeScalars I f 𝔮)).op ≫
            (dualizingExtFunctor (chartPrimeTransportComplex I f ω 𝔮) i).map
              ((chartPrimeScalars I f 𝔮).map
                ((chartCompletionScalars I f).map
                    (CategoryTheory.Limits.limit.post M (chartAwayScalars f)) ≫
                  CategoryTheory.Limits.limit.post (M ⋙ chartAwayScalars f)
                    (chartCompletionScalars I f))).op) := by
  have : 𝔮.asIdeal.IsPrime := 𝔮.isPrime
  have h1 := dualizingExtSystemChartTransport_hom_app_comp_dualizingExtSystemToLimit
    I f ω hω i M hfin n
  have h2 := extendScalars_map_dualizingExtSystemToLimit_comp_localizationBaseChange
    (A := AdicCompletion (I.map (algebraMap A (Localization.Away f))) (Localization.Away f))
    (T := 𝔮.asIdeal.primeCompl) (chartTransportComplex I f ω) i (chartTransportSystem I f M) n
  have h3 := (dualizingExtFunctorLocalizationBaseChange 𝔮.asIdeal.primeCompl
      (chartTransportComplex I f ω) i).naturality
    ((chartCompletionScalars I f).map
          (CategoryTheory.Limits.limit.post M (chartAwayScalars f)) ≫
        CategoryTheory.Limits.limit.post (M ⋙ chartAwayScalars f)
          (chartCompletionScalars I f)).op
  simp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op] at h3
  exact comp_eq_map_comp_twoStep _ _ _ _ _ _ h1 _ _ _ h3 _ _ _ h2 _ rfl

/-- **The landing on a normalized dualizing complex at `𝔮`.** The transported complex is
dualizing at `B_𝔮` but not normalized; shifting it by minus
`Dualizing.dualizingDimension` of the transported complex at `𝔮` normalizes it, and the `Ext`
system against the transported complex in degree `i` is the system against that normalized
choice in degree `i` minus the same integer, compatibly with the transition maps.

The shift is named rather than quantified: it is
`Dualizing.dualizingDimension (Stacks.Algebraization.chartTransportComplex I f ω) 𝔮`, and the
comparison of the systems is `Stacks.Algebraization.dualizingExtSystemShiftNeg`, which needs no
hypothesis. `Dualizing.dualizingDimension_spec` holds at a prime of any Noetherian ring with a
dualizing complex, so the chart ring `B` does not have to be local. -/
theorem isNormalizedDualizingComplex_chartPrimeTransportComplex_shift
    (hω : Dualizing.IsDualizingComplex ω) :
    Dualizing.IsNormalizedDualizingComplex.{u, u}
      ((chartPrimeTransportComplex I f ω 𝔮)⟦
        -Dualizing.dualizingDimension.{u, u} (chartTransportComplex I f ω) 𝔮⟧) := by
  have : 𝔮.asIdeal.IsPrime := 𝔮.isPrime
  let : CategoryTheory.Limits.PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u}
        (algebraMap
          (AdicCompletion (I.map (algebraMap A (Localization.Away f))) (Localization.Away f))
          (Localization.AtPrime 𝔮.asIdeal))) :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, u} _
      (RingHom.flat_algebraMap_iff.mpr
        (IsLocalization.flat (Localization.AtPrime 𝔮.asIdeal) 𝔮.asIdeal.primeCompl))
  -- the two spellings of the base change agree because extension of scalars is exact here
  have e : (StacksDraft.PseudoCoherence.derivedExtensionScalars
        (algebraMap
          (AdicCompletion (I.map (algebraMap A (Localization.Away f))) (Localization.Away f))
          (Localization.AtPrime 𝔮.asIdeal))).obj (chartTransportComplex I f ω) ≅
      chartPrimeTransportComplex I f ω 𝔮 :=
    (Dualizing.derivedExtensionScalarsIsoExtendScalars _).app _ ≪≫
      ((Dualizing.totalDerivedExtensionScalarsIsoExtendScalars _).app _).symm
  exact (Dualizing.isNormalizedDualizingComplex_congr
      ((CategoryTheory.shiftFunctor
        (DerivedCategory (ModuleCat.{u} (Localization.AtPrime 𝔮.asIdeal)))
        (-Dualizing.dualizingDimension.{u, u} (chartTransportComplex I f ω) 𝔮)).mapIso e)).mp
    (Dualizing.dualizingDimension_spec.{u, u} _
      (isDualizingComplex_chartTransportComplex I f ω hω) 𝔮)

/-- **The degree shift at `𝔮` for the chain's own route.** The `Ext` system against the
transported complex in degree `i` is the system against its normalizing shift in degree
`i - δ(𝔮)`, where `δ` is the dimension function of
`Stacks.Algebraization.chartTransportComplex`. -/
def dualizingExtSystemChartPrimeTransportShift (i : ℤ)
    (N : ℕᵒᵖ ⥤ ModuleCat.{u} (Localization.AtPrime 𝔮.asIdeal)) :
    dualizingExtSystem N (chartPrimeTransportComplex I f ω 𝔮) i ≅
      dualizingExtSystem N
        ((chartPrimeTransportComplex I f ω 𝔮)⟦
          -Dualizing.dualizingDimension.{u, u} (chartTransportComplex I f ω) 𝔮⟧)
        (i - Dualizing.dualizingDimension.{u, u} (chartTransportComplex I f ω) 𝔮) :=
  dualizingExtSystemShiftNeg N (chartPrimeTransportComplex I f ω 𝔮)
    (Dualizing.dualizingDimension.{u, u} (chartTransportComplex I f ω) 𝔮) i

end ChartPrime

end Stacks.Algebraization

end
