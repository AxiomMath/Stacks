module

public import StacksFrontier.AlgebraicGeometry.Perfect.LimitHomDescent.AffineCore
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectExtensionAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalFunctionsSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.GlobalFunctionsColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.GlobalFunctionsStagesModel
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DescentSituationBaseChangeSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomAffineLeafAffineStages

/-!
# The ring system of the affine leaf of Stacks 09RI

In Situation 09RH let `g : W₀ ⟶ X₀` be a morphism onto the chosen stage with `W₀` an **affine**
algebraic space.  The base-changed system
`AlgebraicGeometry.Space.DescentSituation.baseChangeSystem` of `g` — the fibre products
`W_i = X_i ×_{X₀} W₀` over `W₀` with vertex `W = X ×_{X₀} W₀` — then consists of affine
algebraic spaces, and this file turns it into the ring-level datum that Stacks 09RE consumes:
a `Stacks.LimitHomDescent.Affine.RingSystem` over `Γ(W₀)` whose stages are the `Γ(W_i)` and
whose vertex is `Γ(W)`, together with the assertion that `Γ(W)` is the filtered colimit of the
`Γ(W_i)`.

## The two hypotheses, and that `ChartsBounded` is not one of them

`AlgebraicGeometry.Space.DescentSituation.isStagesColimit_stageRingSystem` of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/AffineStagesPerfectHomDescent.lean` — the same
statement for a situation's *own* system — asks for
`AlgebraicGeometry.Space.ChartsBounded`.  That hypothesis is **not** needed here, for two
independent reasons, and neither is an approximation:

* `AlgebraicGeometry.Space.DescentSituation.isGlobalFunctionsColimit` proves Stacks 07SI for the
  structure sheaf from `#I < B.cutoff.ord.cof` alone, for any situation whose index set lies in
  the universe of the site.  That is the route taken below.
* Even where `ChartsBounded` is wanted it is free at these hypotheses:
  `AlgebraicGeometry.Space.chartsBounded_of_mk_lt_cof_ord_op` — the inverse-system case of
  `AlgebraicGeometry.Space.chartsBounded_of_lt_cof_ord`, whose bound on the morphism types is
  automatic in a preorder — gives `ChartsBounded B S hS D.system` from `#I < B.cutoff.ord.cof`
  and nothing else.  `AlgebraicGeometry.Space.DescentSituation.chartsBounded_of_lt_cof_ord_stages`
  below records the consequence for the base-changed situation.

So the only hypotheses are the ones Stacks 09RI already carries: `#I < B.cutoff.ord.cof` (the
size bound of Stacks 07SF, which Situation 09RH needs anyway for the projection `X ⟶ X₀` to be
affine) and affineness of `W₀` (which is what makes this the *affine leaf* of the dévissage).

## Main definitions

* `AlgebraicGeometry.Space.DescentSituation.baseChangeSituation`: the base change of
  Situation 09RH along `g`, as Situation 09RH again.  It is
  `AlgebraicGeometry.Space.DescentSituation.stagesBaseChangeAlong`, whose quasi-compactness and
  quasi-separatedness hypotheses affineness of `W₀` supplies.
* `AlgebraicGeometry.Space.DescentSituation.baseChangeRingSystem`: the ring system over a ring
  `A₀ ⟶ Γ(W₀)` with stages `Γ(W_i)` and vertex a ring `A ≅ Γ(W)`.

## Main results

* `AlgebraicGeometry.Space.DescentSituation.baseChangeSituation_stage`,
  `baseChangeSituation_limitSpace`, `baseChangeSituation_transition` and
  `baseChangeSituation_projection`: the base-changed situation *is* the base-changed system —
  all four hold by `rfl`.
* `AlgebraicGeometry.Space.DescentSituation.isStagesColimit_baseChangeGlobalFunctions`:
  **`Γ(W) = colim_{i ≥ 0} Γ(W_i)`** (Stacks 07SI for the structure sheaf on the base change).
* `AlgebraicGeometry.Space.DescentSituation.isStagesColimit_baseChangeRingSystem`: the same
  assertion for `baseChangeRingSystem`, which is what
  `Stacks.LimitHomDescent.Affine.RingSystem.exists_Q_map_ext_single_eq` and its companions take
  as their colimit hypothesis.

## References

* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Situation 75.24.1 (Tag 09RH)](https://stacks.math.columbia.edu/tag/09RH)
* [Stacks Project, Lemma 36.29.2 (Tag 09RE)](https://stacks.math.columbia.edu/tag/09RE)
* [Stacks Project, Lemma 07SI](https://stacks.math.columbia.edu/tag/07SI)
* [Stacks Project, Lemma 07SF](https://stacks.math.columbia.edu/tag/07SF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

namespace DescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  {D : DescentSituation B S hS hZ I} {W₀ : AlgebraicSpaces B S hS}
  (g : W₀ ⟶ D.stage D.base)

/-! ### The base change along an affine space over the chosen stage, as Situation 09RH -/


/-- **The base change of Situation 09RH along `g : W₀ ⟶ X₀` with `W₀` affine, as Situation 09RH
again.**  This is `AlgebraicGeometry.Space.DescentSituation.stagesBaseChangeAlong`: its
hypotheses on `W₀` are that it is an algebraic space, quasi-compact and quasi-separated, and an
affine algebraic space is all three
(`AlgebraicGeometry.Space.IsAffineSpace.isQuasiCompactSpace` and
`AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isAffineSpace`). -/
abbrev baseChangeSituation (hW₀ : IsAffineSpace B S hS W₀.1) :
    DescentSituation B S hS hZ D.Stages :=
  DescentSituation.stagesBaseChangeAlong (D := D) W₀.property
    (IsAffineSpace.isQuasiCompactSpace hW₀)
    (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hW₀) g.hom

/-- **The ring of global functions of a stage of the base-changed system is `u`-small.**  This
is `AlgebraicGeometry.Space.small_globalFunctions` at `W_i = X_i ×_{X₀} W₀`, declared as an
instance in this form because `AlgebraicGeometry.Space.DescentSituation.baseChangeStage` is
reducible: instance search unfolds it to a `CategoryTheory.Limits.pullback` and then cannot
solve `?X.obj =?= pullback …` for the general instance. -/
instance small_globalFunctions_baseChangeStage (j : D.Stages) :
    Small.{u} (globalFunctions' B S hS (baseChangeStage g j).1) :=
  small_globalFunctions B S hS (baseChangeStage g j)

variable (hW₀ : IsAffineSpace B S hS W₀.1)

/-- Each stage of the base-changed situation is the corresponding stage of the base-changed
system. -/
theorem baseChangeSituation_stage (i : D.Stages) :
    (baseChangeSituation g hW₀).stage i = baseChangeStage g i := rfl

/-- The limit of the base-changed situation is the vertex of the base-changed system. -/
theorem baseChangeSituation_limitSpace :
    (baseChangeSituation g hW₀).limitSpace = baseChangeLimit g := rfl

/-- The transition morphisms of the base-changed situation are those of the base-changed
system. -/
theorem baseChangeSituation_transition {i j : D.Stages} (h : i ≤ j) :
    (baseChangeSituation g hW₀).transition h = baseChangeTransition g h := rfl

/-- The projections of the base-changed situation are those of the base-changed system. -/
theorem baseChangeSituation_projection (i : D.Stages) :
    (baseChangeSituation g hW₀).projection i = baseChangeProjection g i := rfl

/-- **The charts of the base-changed situation are bounded**, from the size hypothesis of
Stacks 07SF and nothing else: the index category is the opposite of the preorder of stages,
which is no larger than `I`, so
`AlgebraicGeometry.Space.chartsBounded_of_mk_lt_cof_ord_op` applies.

This is recorded because the companion statement for a situation's own system,
`AlgebraicGeometry.Space.DescentSituation.isStagesColimit_stageRingSystem`, asks for
`AlgebraicGeometry.Space.ChartsBounded`; nothing below uses it, the route taken being
`AlgebraicGeometry.Space.DescentSituation.isGlobalFunctionsColimit`. -/
theorem chartsBounded_of_lt_cof_ord_stages (hI : #I < B.cutoff.ord.cof) :
    ChartsBounded B S hS (baseChangeSituation g hW₀).system :=
  chartsBounded_of_mk_lt_cof_ord_op B S hS _
    (lt_of_le_of_lt (mk_subtype_le fun i => D.base ≤ i) hI)

/-! ### Stacks 07SI for the structure sheaf on the base change -/

include hW₀ in
/-- **`Γ(W) = colim_{i ≥ 0} Γ(W_i)`** for the base change of Situation 09RH along a morphism
`g : W₀ ⟶ X₀` with `W₀` affine: the ring of global regular functions of the vertex
`W = X ×_{X₀} W₀` is the filtered colimit of those of the stages `W_i = X_i ×_{X₀} W₀`, along
the pullbacks of global functions.

This is Stacks 07SI for the structure sheaf
(`AlgebraicGeometry.Space.DescentSituation.isGlobalFunctionsColimit`) applied to the
base-changed situation, whose stages, vertex, transition morphisms and projections are those of
the base-changed system by `AlgebraicGeometry.Space.DescentSituation.baseChangeSituation_stage`
and its companions.  The size hypothesis is inherited: the stages of a situation are no more
numerous than its indices. -/
theorem isStagesColimit_baseChangeGlobalFunctions (hI : #I < B.cutoff.ord.cof) :
    Stacks.IsStagesColimit
      (G := fun i : D.Stages => globalFunctions' B S hS (baseChangeStage g i).1)
      (T := globalFunctions' B S hS (baseChangeLimit g).1)
      (fun (_ _ : D.Stages) (h : _ ≤ _) s =>
        globalFunctionsMap B S hS (baseChangeTransition g h) s)
      (fun (i : D.Stages) s => globalFunctionsMap B S hS (baseChangeProjection g i) s) :=
  (baseChangeSituation g hW₀).isGlobalFunctionsColimit
    (lt_of_le_of_lt (mk_subtype_le fun i => D.base ≤ i) hI)

/-! ### The ring system -/

/-- **The transition morphism of the base-changed system attached to `i ≤ i` is the identity.**
It is the base change of the transition morphism of Situation 09RH attached to `i ≤ i`, which is
the identity. -/
theorem baseChangeTransition_refl (i : D.Stages) :
    baseChangeTransition g (le_refl i) = 𝟙 (baseChangeStage g i) := by
  have h0 : ∀ h : i.1 ≤ i.1, D.transition h = 𝟙 (D.stage i.1) := fun _ =>
    D.toLimitSituation.transition_self i.1
  refine baseChange_hom_ext g ?_ ?_
  · rw [baseChangeTransition_comp_toStage, Category.id_comp, h0, Category.comp_id]
  · rw [baseChangeTransition_comp_toBase, Category.id_comp]

variable {A₀ : Type u} [CommRing A₀] (ψ₀ : A₀ →+* globalFunctions' B S hS W₀.1)
  {A : Type u} [CommRing A] (σ : A ≃+* globalFunctions' B S hS (baseChangeLimit g).1)

/-- **The rings of global functions of the stages `W_i = X_i ×_{X₀} W₀` as algebras over a ring
`A₀ ⟶ Γ(W₀)`**, with vertex a ring `A ≅ Γ(W)`: the stage rings are the shrunk rings `Γ(W_i)`,
with structure maps the pullbacks along the projections `W_i ⟶ W₀` of the base-changed system,
and the maps to the vertex are the pullbacks along `W ⟶ W_i`.

This is the shape in which Stacks 09RE — `Stacks.LimitHomDescent.Affine.RingSystem` and the
statements about it — consumes the affine leaf of the dévissage of Stacks 09RI. -/
def baseChangeRingSystem :
    Stacks.LimitHomDescent.Affine.RingSystem.{u, u} (CommRingCat.of A₀) D.Stages where
  A j := CommRingCat.of (Shrink.{u} (globalFunctions' B S hS (baseChangeStage g j).1))
  φ j := CommRingCat.ofHom ((Shrink.ringEquiv _).symm.toRingHom.comp
    ((globalFunctionsMap B S hS (baseChangeToBase g j)).comp ψ₀))
  β h := CommRingCat.ofHom ((Shrink.ringEquiv _).symm.toRingHom.comp
    ((globalFunctionsMap B S hS (baseChangeTransition g h)).comp (Shrink.ringEquiv _).toRingHom))
  φ_β {i j} h := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    change (Shrink.ringEquiv _).symm (globalFunctionsMap B S hS (baseChangeTransition g h)
        (Shrink.ringEquiv _ ((Shrink.ringEquiv _).symm
          (globalFunctionsMap B S hS (baseChangeToBase g i) (ψ₀ x))))) =
      (Shrink.ringEquiv _).symm (globalFunctionsMap B S hS (baseChangeToBase g j) (ψ₀ x))
    rw [RingEquiv.apply_symm_apply, ← RingHom.comp_apply, ← globalFunctionsMap_comp,
      baseChangeTransition_comp_toBase]
  β_β {i j k} h h' := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    change (Shrink.ringEquiv _).symm (globalFunctionsMap B S hS (baseChangeTransition g h')
        (Shrink.ringEquiv _ ((Shrink.ringEquiv _).symm
          (globalFunctionsMap B S hS (baseChangeTransition g h) (Shrink.ringEquiv _ x))))) =
      (Shrink.ringEquiv _).symm (globalFunctionsMap B S hS
        (baseChangeTransition g (h.trans h')) (Shrink.ringEquiv _ x))
    rw [RingEquiv.apply_symm_apply, ← RingHom.comp_apply, ← globalFunctionsMap_comp,
      show baseChangeTransition g h' ≫ baseChangeTransition g h =
        baseChangeTransition g (h.trans h') from (baseChangeSystem g).transition_comp h h']
  β_refl i := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    change (Shrink.ringEquiv _).symm (globalFunctionsMap B S hS
      (baseChangeTransition g (le_refl i)) (Shrink.ringEquiv _ x)) = x
    rw [baseChangeTransition_refl, globalFunctionsMap_id, RingHom.id_apply,
      RingEquiv.symm_apply_apply]
  lim := CommRingCat.of A
  φlim := CommRingCat.ofHom (σ.symm.toRingHom.comp
    ((globalFunctionsMap B S hS (baseChangeLimitToBase g)).comp ψ₀))
  γ j := CommRingCat.ofHom (σ.symm.toRingHom.comp
    ((globalFunctionsMap B S hS (baseChangeProjection g j)).comp (Shrink.ringEquiv _).toRingHom))
  φ_γ j := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    change σ.symm (globalFunctionsMap B S hS (baseChangeProjection g j)
        (Shrink.ringEquiv _ ((Shrink.ringEquiv _).symm
          (globalFunctionsMap B S hS (baseChangeToBase g j) (ψ₀ x))))) =
      σ.symm (globalFunctionsMap B S hS (baseChangeLimitToBase g) (ψ₀ x))
    rw [RingEquiv.apply_symm_apply, ← RingHom.comp_apply, ← globalFunctionsMap_comp,
      baseChangeProjection_comp_toBase]
  β_γ {i j} h := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    change σ.symm (globalFunctionsMap B S hS (baseChangeProjection g j)
        (Shrink.ringEquiv _ ((Shrink.ringEquiv _).symm
          (globalFunctionsMap B S hS (baseChangeTransition g h) (Shrink.ringEquiv _ x))))) =
      σ.symm (globalFunctionsMap B S hS (baseChangeProjection g i) (Shrink.ringEquiv _ x))
    rw [RingEquiv.apply_symm_apply, ← RingHom.comp_apply, ← globalFunctionsMap_comp,
      show baseChangeProjection g j ≫ baseChangeTransition g h = baseChangeProjection g i from
        (baseChangeSystem g).proj_transition h]

/-- The ring of a stage of `AlgebraicGeometry.Space.DescentSituation.baseChangeRingSystem` is
the ring of global functions of that stage of the base-changed system. -/
def baseChangeRingEquiv (j : D.Stages) :
    (baseChangeRingSystem g ψ₀ σ).A j ≃+* globalFunctions' B S hS (baseChangeStage g j).1 :=
  Shrink.ringEquiv (globalFunctions' B S hS (baseChangeStage g j).1)

/-- The structure map of `AlgebraicGeometry.Space.DescentSituation.baseChangeRingSystem` at a
stage is the pullback of global functions along the projection `W_i ⟶ W₀`. -/
theorem globalFunctionsMap_baseChangeToBase_apply (j : D.Stages) (a : A₀) :
    globalFunctionsMap B S hS (baseChangeToBase g j) (ψ₀ a) =
      baseChangeRingEquiv g ψ₀ σ j (((baseChangeRingSystem g ψ₀ σ).φ j).hom a) :=
  ((Shrink.ringEquiv (globalFunctions' B S hS (baseChangeStage g j).1)).apply_symm_apply _).symm

/-- The structure map of `AlgebraicGeometry.Space.DescentSituation.baseChangeRingSystem` at the
vertex is the pullback of global functions along the projection `W ⟶ W₀`. -/
theorem globalFunctionsMap_baseChangeLimitToBase_apply (a : A₀) :
    globalFunctionsMap B S hS (baseChangeLimitToBase g) (ψ₀ a) =
      σ ((baseChangeRingSystem g ψ₀ σ).φlim.hom a) :=
  (σ.apply_symm_apply _).symm

/-- The map to the vertex of `AlgebraicGeometry.Space.DescentSituation.baseChangeRingSystem` is
the pullback of global functions along the projection `W ⟶ W_i`. -/
theorem globalFunctionsMap_baseChangeProjection_apply (j : D.Stages)
    (x : (baseChangeRingSystem g ψ₀ σ).A j) :
    globalFunctionsMap B S hS (baseChangeProjection g j) (baseChangeRingEquiv g ψ₀ σ j x) =
      σ (((baseChangeRingSystem g ψ₀ σ).γ j).hom x) :=
  (σ.apply_symm_apply _).symm

include hW₀ in
/-- **`A = colim_{i ≥ 0} Γ(W_i)` for the ring system of the affine leaf of Stacks 09RI.**  This
is the colimit hypothesis that `Stacks.LimitHomDescent.Affine.RingSystem.exists_Q_map_ext_eq`,
`exists_le_Q_map_ext_eq` and their `R[0]` specialisations take, for
`AlgebraicGeometry.Space.DescentSituation.baseChangeRingSystem`.

It is `AlgebraicGeometry.Space.DescentSituation.isStagesColimit_baseChangeGlobalFunctions`
transported along the shrinking equivalences at the stages and along `σ` at the vertex. -/
theorem isStagesColimit_baseChangeRingSystem (hI : #I < B.cutoff.ord.cof) :
    Stacks.IsStagesColimit
      (fun (i j : D.Stages) (h : i ≤ j) (x : (baseChangeRingSystem g ψ₀ σ).A i) =>
        (baseChangeRingSystem g ψ₀ σ).β h x)
      (fun (j : D.Stages) (x : (baseChangeRingSystem g ψ₀ σ).A j) =>
        (baseChangeRingSystem g ψ₀ σ).γ j x) :=
  Stacks.IsStagesColimit.ofEquiv _ _ (fun _ => (Shrink.ringEquiv _).toEquiv) σ.toEquiv
    (fun _ _ _ _ => RingEquiv.apply_symm_apply _ _)
    (fun _ _ => σ.apply_symm_apply _)
    (isStagesColimit_baseChangeGlobalFunctions g hW₀ hI)

end DescentSituation

end AlgebraicGeometry.Space

end
