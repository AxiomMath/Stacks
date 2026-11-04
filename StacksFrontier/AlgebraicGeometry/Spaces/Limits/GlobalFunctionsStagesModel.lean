module

public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.GlobalFunctionsStagesColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.SpecGlobalFunctionsChartSquare

/-!
# Stacks 07SI for the structure sheaf, as a directed system of `u`-rings

`AlgebraicGeometry.Space.LimitSituation.isStagesColimit_globalFunctions_of_chartsBounded` asserts
Stacks 07SI for
the structure sheaf over `AlgebraicGeometry.Space.globalFunctions'`, the compatible families of
regular functions on the étale charts. That ring is a subtype of a product indexed by the charts
and so lives in `Type (u + 1)`, whereas a statement about the spectrum of the ring — and in
particular the commutative-algebra descent of
`StacksFrontier.RingTheory.Etale.DirectedColimitPresentation` — needs a `u`-ring.

This file transports the colimit assertion to the canonical `u`-model
`AlgebraicGeometry.Space.globalFunctionsModel` of each stage and to an *arbitrary* `u`-model of
the global functions of the limit, and records the resulting directed system of `u`-rings
together with the three clauses in which the commutative-algebra results consume it.

## Main definitions

* `AlgebraicGeometry.Space.LimitSituation.stageModel`: the canonical `u`-model of the ring of
  global functions of a stage.
* `AlgebraicGeometry.Space.LimitSituation.stageModelTransition` and `.modelProjection`: the
  transition homomorphisms of the system of models and the homomorphisms into a model of the
  global functions of the limit.

## Main results

* `AlgebraicGeometry.Space.LimitSituation.isStagesColimit_stageModel`: **Stacks 07SI for the
  structure sheaf, on `u`-models.**
* `AlgebraicGeometry.Space.LimitSituation.modelProjection_stageModelTransition`,
  `.exists_stageModel_eq` and `.exists_stageModelTransition_eq_zero`: the three clauses, in the
  shape `MvPolynomial.exists_ge_etale_quotient_of_directed` and its companions ask for.

## Implementation notes

*Why a model and not the ring itself.* `AlgebraicGeometry.Space.globalFunctions` is `u`-small —
`AlgebraicGeometry.Space.small_globalFunctions`, proved and not assumed, by restriction to a
chart carrying a surjective étale atlas — so `Shrink` of it is a `u`-ring isomorphic to it. The
model is the one `AlgebraicGeometry.Space.commSq_chart_specOfGlobalFunctions` is already stated
for, through an arbitrary `u`-model and its identification.

*Why the model of the limit is left arbitrary.* The consumer of these clauses in the proof of
Stacks 07SQ has the limit presented as a representable presheaf, so the model it wants for the
global functions of the limit is the ring of regular functions of the representing scheme, not
`Shrink` of anything; the identification is
`AlgebraicGeometry.Space.globalFunctionsYonedaEquiv`. Keeping the model a parameter avoids
transporting the polynomial presentation along a ring isomorphism afterwards.

*Why the transport is not formal nonsense.* The transition homomorphisms of the model are
conjugates of the pullbacks of global functions, so the directed-system laws and the colimit
clauses are those of `AlgebraicGeometry.Space.globalFunctionsMap`, which are functoriality
(`AlgebraicGeometry.Space.globalFunctionsMap_id` and `_comp`) and
`Stacks.IsStagesColimit.ofEquiv`.

*The vanishing clause.* `Stacks.IsStagesColimit` asserts that two sections of one stage with the
same image agree at a later stage; the commutative-algebra results ask the special case of a
section whose image vanishes, which follows because the transition maps are ring homomorphisms
and so kill zero.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

namespace LimitSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (A : LimitSituation B S hS hZ X)

/-- The `u`-model of the ring of global regular functions of a stage of a limit situation. -/
abbrev stageModel (i : A.Stages) : Type u :=
  globalFunctionsModel B S hS (A.stage i.1)

/-- The identification of the model of a stage with the ring of global functions of that
stage. -/
abbrev stageModelEquiv (i : A.Stages) :
    A.stageModel i ≃+* globalFunctions B S hS (A.stage i.1).obj :=
  globalFunctionsModelEquiv B S hS (A.stage i.1)

/-- The transition homomorphism of the system of models: the pullback of global functions along
the transition morphism of the situation, conjugated by the identifications. -/
def stageModelTransition (i j : A.Stages) (h : i ≤ j) : A.stageModel i →+* A.stageModel j :=
  (A.stageModelEquiv j).symm.toRingHom.comp
    ((globalFunctionsMap B S hS (A.transition (show i.1 ≤ j.1 from h))).comp
      (A.stageModelEquiv i).toRingHom)

/-- The transition homomorphism of the system of models sends `x` to the image under the inverse
identification of the pullback of the global function corresponding to `x`. -/
@[simp]
theorem stageModelTransition_apply (i j : A.Stages) (h : i ≤ j) (x : A.stageModel i) :
    A.stageModelTransition i j h x =
      (A.stageModelEquiv j).symm
        (globalFunctionsMap B S hS (A.transition (show i.1 ≤ j.1 from h))
          (A.stageModelEquiv i x)) :=
  rfl

/-- The transition morphism of a limit situation at a reflexivity proof is the identity. -/
theorem transition_self (i : A.I) : A.transition (le_refl i) = 𝟙 (A.stage i) := by
  apply ObjectProperty.hom_ext
  show A.system.map (homOfLE (le_refl i)).op = 𝟙 _
  rw [show (homOfLE (le_refl i)).op = 𝟙 (op i) from rfl, A.system.map_id]

/-- **The models of the stages form a directed system of `u`-rings.** The laws are the
functoriality of pullback of global functions. -/
instance directedSystem_stageModelTransition :
    DirectedSystem A.stageModel fun i j h => A.stageModelTransition i j h where
  map_self i x := by
    rw [stageModelTransition_apply, A.transition_self, globalFunctionsMap_id]
    simp
  map_map {i j k} hij hjk x := by
    rw [stageModelTransition_apply, stageModelTransition_apply, stageModelTransition_apply,
      RingEquiv.apply_symm_apply, ← RingHom.comp_apply, ← globalFunctionsMap_comp,
      A.transition_comp]

section LimitModel

variable (hX : IsAlgebraicSpace B S hS X) {Alim : Type u} [CommRing Alim]
  (eA : Alim ≃+* globalFunctions B S hS (A.limitSpace hX).obj)

/-- The homomorphism from the model of a stage into a model of the global functions of the limit:
the pullback of global functions along the projection of the limiting cone, conjugated by the
identifications. -/
def modelProjection (i : A.Stages) : A.stageModel i →+* Alim :=
  eA.symm.toRingHom.comp
    ((globalFunctionsMap B S hS (A.projection hX i.1)).comp (A.stageModelEquiv i).toRingHom)

/-- The homomorphism `modelProjection` sends `x` to the image under `eA.symm` of the pullback,
along the projection of the limiting cone, of the global function corresponding to `x`. -/
@[simp]
theorem modelProjection_apply (i : A.Stages) (x : A.stageModel i) :
    A.modelProjection hX eA i x =
      eA.symm (globalFunctionsMap B S hS (A.projection hX i.1) (A.stageModelEquiv i x)) :=
  rfl

variable {U₀ R₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ A.system.obj (op A.base)}
  {t : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj R₀) ⟶
    yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀)}
  {s : (BigAffineFppf.inclusion B S hS).obj R₀ ⟶ (BigAffineFppf.inclusion B S hS).obj U₀}

/-- **Stacks 07SI for the structure sheaf, on `u`-models.** The ring of global regular functions
of the limit of a limit situation is the filtered colimit of those of its stages, read on the
canonical `u`-models of the stages and on an arbitrary `u`-model of the global functions of the
limit.

The hypotheses are those of Stacks 07SF, exactly as for
`AlgebraicGeometry.Space.LimitSituation.isStagesColimit_globalFunctions_of_chartsBounded`, which
this transports
along the identifications of the models. -/
theorem isStagesColimit_stageModel (hI : A.ChartsBounded)
    (hf₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk f₀))
    (hsurj : IsSurjective B S hS f₀) (hpb : IsPullback t (yoneda.map s) f₀ f₀) :
    Stacks.IsStagesColimit (fun i j h x => A.stageModelTransition i j h x)
      (fun i x => A.modelProjection hX eA i x) :=
  Stacks.IsStagesColimit.ofEquiv _ _ (fun i => (A.stageModelEquiv i).toEquiv) eA.toEquiv
    (fun i j h x => by
      rw [stageModelTransition_apply]
      exact (A.stageModelEquiv j).apply_symm_apply _)
    (fun i x => by
      rw [modelProjection_apply]
      exact eA.apply_symm_apply _)
    (A.isStagesColimit_globalFunctions_of_chartsBounded hX hI hf₀ hsurj hpb)

/-- The first clause: the homomorphisms into the model of the limit are compatible with the
transition homomorphisms. -/
theorem modelProjection_stageModelTransition (hI : A.ChartsBounded)
    (hf₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk f₀))
    (hsurjf : IsSurjective B S hS f₀) (hpb : IsPullback t (yoneda.map s) f₀ f₀)
    (i j : A.Stages) (h : i ≤ j) (x : A.stageModel i) :
    A.modelProjection hX eA j (A.stageModelTransition i j h x) = A.modelProjection hX eA i x :=
  (A.isStagesColimit_stageModel hX eA hI hf₀ hsurjf hpb).ι_trans i j h x

/-- The second clause: every global function on the limit comes from a stage. -/
theorem exists_stageModel_eq (hI : A.ChartsBounded)
    (hf₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk f₀))
    (hsurjf : IsSurjective B S hS f₀) (hpb : IsPullback t (yoneda.map s) f₀ f₀) (a : Alim) :
    ∃ (i : A.Stages) (x : A.stageModel i), A.modelProjection hX eA i x = a :=
  (A.isStagesColimit_stageModel hX eA hI hf₀ hsurjf hpb).exists_stage a

/-- The third clause: a global function on a stage whose image on the limit vanishes already
vanishes at a later stage. -/
theorem exists_stageModelTransition_eq_zero (hI : A.ChartsBounded)
    (hf₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk f₀))
    (hsurjf : IsSurjective B S hS f₀) (hpb : IsPullback t (yoneda.map s) f₀ f₀)
    (i : A.Stages) (x : A.stageModel i) (hx : A.modelProjection hX eA i x = 0) :
    ∃ (j : A.Stages) (h : i ≤ j), A.stageModelTransition i j h x = 0 := by
  obtain ⟨j, hij, hj⟩ :=
    (A.isStagesColimit_stageModel hX eA hI hf₀ hsurjf hpb).exists_trans_eq i x 0
      (by rw [hx, map_zero])
  exact ⟨j, hij, by rw [hj, map_zero]⟩

end LimitModel

end LimitSituation

end AlgebraicGeometry.Space

end
