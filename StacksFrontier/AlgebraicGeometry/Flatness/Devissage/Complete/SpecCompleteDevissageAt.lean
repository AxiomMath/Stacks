module

public import StacksFrontier.AlgebraicGeometry.Descent.FpqcQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.FibreDimensionTranslation
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.SpecOneStepAt
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.SpecTranslation

/-!
# Stacks 05I0 (2) as an equivalence

Let `A → B` be a ring map of finite type, let `N` be a finite `B`-module and let `q` be a prime
of `B`. Writing `X = Spec B`, `S = Spec A` and `ℱ = Ñ`, Stacks 05I0 (2) asserts that a complete
dévissage of `ℱ/X/S` at the point of `q` exists exactly when a complete dévissage of `N/B/A` at
`q` does. A complete dévissage of `N/B/A` at `q` carries the relative dimension condition of
Stacks 05HZ (4), which Stacks 05I0 identifies with the fibre-dimension condition of Stacks 05H4
(5); it is read fibre by fibre, as
`Module.NonemptyCompleteDevissageAt.relativeDimension_eq_support` together with
`Module.CompleteDevissageAt.FibresHaveRelativeDimension`. The direction from sheaves to modules is
`AlgebraicGeometry.exists_completeDevissageAt_fibresHaveRelativeDimension_of_spec`; this file
supplies the converse and records the equivalence.

The converse is the structural recursion on the stages of the algebraic dévissage. One stage of
an algebraic complete dévissage at `q`, with its pointed datum, is already a pointed stage of a
scheme-theoretic dévissage, by `Module.DevissageStage.toPointedStage`. What a stage does not
carry is the geometric reading of the module dévissed next: the algebraic tail dévisses the
quotient `M ⧸ range α`, while the next geometric stage dévisses the cokernel of the stage's map
of sheaves. The two are identified by `AlgebraicGeometry.cokernelTildeIso`, and the chain built
for the quotient is carried over to the cokernel by
`AlgebraicGeometry.DevissageChain.ofModuleIso`.

## Main results

* `Module.nonempty_completeDevissageAt_iff`: **Stacks 05I0 (2)**, as an equivalence. A complete
  dévissage of `Ñ/Spec B/Spec A` at the point of `q` exists if and only if a complete dévissage
  of `N/B/A` at `q` does whose stages have fibres of their relative dimension.

## Implementation notes

The recursion runs on the number of stages of the algebraic dévissage rather than on a chain
datatype, because `Module.PointedCompleteDevissage` records its stages as a family indexed by a
`Fin` and is destructed by `Module.PointedCompleteDevissage.tail`, which shortens that family by
one. The base prime is carried as an independent parameter together with the equation
identifying it with `q.under R`, as in `Module.PointedCompleteDevissage` itself: the tail of a
dévissage at `q` is taken at the lower prime of the first stage, whose contraction to the base
is only *equal* to the contraction of `q`.

Two frictions of this corner are worked around exactly as in
`StacksFrontier/AlgebraicGeometry/Flatness/Devissage/Complete/SpecDevissageAt.lean` and
`StacksFrontier/AlgebraicGeometry/Flatness/Devissage/Complete/SpecOneStepAt.lean`. The stages are
passed to the two constructors as abstract terms rather than as `Module.CompleteDevissage.head`
of the dévissage in hand, since that projection standing between a goal and the instances of a
stage makes instance synthesis exceed the depth this project sets. And the base point of a chain
is moved along an equality of points of `Spec` by `exists_chain_congr`, a transport by
substitution, because the point occupies a dependent position in the type of a chain and `rw`
cannot cross it.

## References

* [Stacks Project, Tag 05HI](https://stacks.math.columbia.edu/tag/05HI)
* [Stacks Project, Tag 05HZ](https://stacks.math.columbia.edu/tag/05HZ)
* [Stacks Project, Tag 05I0](https://stacks.math.columbia.edu/tag/05I0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CommRingCat

universe u

attribute [local instance] AlgebraicGeometry.locallyOfFiniteType_specMap_algebraMap

/-- A chain of stages with compatible distinguished points exists over a point of the base as
soon as it exists over an equal point. The statement is needed because the base point occupies a
dependent position in the type of `AlgebraicGeometry.DevissageChain`, so that `rw` cannot move
across the equality. -/
private theorem exists_chain_congr {X T : Scheme.{u}} (f : X ⟶ T) (F : X.Modules)
    (hl : LocallyOfFiniteType f) (hq : F.IsQuasicoherent) (ht : F.IsFiniteType) (x : X)
    {s s' : T} (h : s = s')
    (hC : ∃ C : DevissageChain s X f F hl hq ht,
      Nonempty (PointedDevissageChain s X f F hl hq ht x C)) :
    ∃ C : DevissageChain s' X f F hl hq ht,
      Nonempty (PointedDevissageChain s' X f F hl hq ht x C) := by
  subst h
  exact hC

namespace Module.DevissageStage

variable {R S N : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
  [AddCommGroup N] [Module S N] [Module.Finite S N] {r : Ideal R} [r.IsPrime]
  (st : Module.DevissageStage R S N r)

/-- The map of `B`-modules whose associated sheaf is the free-module map of the geometric stage:
the map `α` of the stage, read on the index type `ULift (Fin m)` of the free sheaf. -/
private def liftedAlpha :
    ModuleCat.of (CommRingCat.of st.B) (ULift.{u} (Fin st.multiplicity) →₀ st.B) ⟶
      ModuleCat.of (CommRingCat.of st.B) st.M :=
  ModuleCat.ofHom (st.alpha ∘ₗ (Finsupp.domLCongr (M := st.B) (R := st.B)
    (Equiv.ulift.{u, 0} (α := Fin st.multiplicity))).toLinearMap)

/-- The range of `Module.DevissageStage.liftedAlpha` is the range of `α`: the two differ by an
isomorphism of the source. -/
private theorem range_liftedAlpha :
    LinearMap.range st.liftedAlpha.hom = LinearMap.range st.alpha := by
  rw [liftedAlpha, ModuleCat.hom_ofHom, LinearMap.range_comp, LinearEquiv.range,
    Submodule.map_top]

/-- The free sheaf of rank the multiplicity of a stage, identified with the sheaf attached to a
finite free module over the lower algebra of the stage. -/
private def freeIso := (AlgebraicGeometry.tildeFinsupp (R := CommRingCat.of st.B)
  (ULift.{u} (Fin st.multiplicity))).symm

/-- The pushforward of the sheaf attached to the stage module along the finite map of the stage,
identified with the sheaf attached to that module read over the lower algebra. -/
private def pushforwardIso :=
  (AlgebraicGeometry.pushforwardTildeIso (CommRingCat.of st.B) (CommRingCat.of st.A)
    (CommRingCat.ofHom st.toLeft.toRingHom)).app (ModuleCat.of (CommRingCat.of st.A) st.M)

/-- The free-module map of the geometric stage of a stage is the sheaf associated with
`Module.DevissageStage.liftedAlpha`, conjugated by the identification of the free sheaf with the
sheaf of a finite free module and by the pushforward of a sheaf along a finite map.

The two cancellations are spelled out as a term rather than left to `simp`: the type of the free
sheaf on `Spec B` is not type-correct at the transparency `rw` and `simp` use to key their
matching, since `AlgebraicGeometry.Scheme.ringCatSheaf` is a sheaf on the space of the scheme and
`CategoryTheory.SheafOfModules` wants one on its site of opens. -/
private theorem alpha_toGeometricStage_comm (hdim) :
    (st.toGeometricStage hdim).alpha ≫ st.pushforwardIso.hom =
      st.freeIso.hom ≫ (tilde.functor (CommRingCat.of st.B)).map st.liftedAlpha :=
  (Category.assoc st.freeIso.hom
      ((tilde.functor (CommRingCat.of st.B)).map st.liftedAlpha ≫ st.pushforwardIso.inv)
      st.pushforwardIso.hom).trans
    (congrArg (fun k => st.freeIso.hom ≫ k)
      ((Category.assoc ((tilde.functor (CommRingCat.of st.B)).map st.liftedAlpha)
            st.pushforwardIso.inv st.pushforwardIso.hom).trans
        ((congrArg (fun k => (tilde.functor (CommRingCat.of st.B)).map st.liftedAlpha ≫ k)
            st.pushforwardIso.inv_hom_id).trans (Category.comp_id _))))

/-- **The cokernel of the free-module map of the final geometric stage vanishes.** The map `α`
of a final stage is surjective, hence so is the map of modules whose associated sheaf the stage's
map is, and the tilde functor carries epimorphisms to epimorphisms. -/
private theorem isZero_coker_toGeometricStage (hdim)
    (hsurj : Function.Surjective st.alpha) : IsZero (st.toGeometricStage hdim).coker :=
  AlgebraicGeometry.isZero_cokernel_of_surjective_of_tilde_comm
    (st.toGeometricStage hdim).alpha st.freeIso st.pushforwardIso st.liftedAlpha
    (st.alpha_toGeometricStage_comm hdim)
    (hsurj.comp (Finsupp.domLCongr (M := st.B) (R := st.B)
      (Equiv.ulift.{u, 0} (α := Fin st.multiplicity))).surjective)

/-- **The cokernel of the free-module map of a geometric stage is the sheaf attached to the
module the algebraic dévissage passes to**, namely the quotient of the stage module by the range
of `α`. -/
private def cokerToGeometricStageIso (hdim) :
    (st.toGeometricStage hdim).coker ≅
      tilde (ModuleCat.of (CommRingCat.of st.B) (st.M ⧸ LinearMap.range st.alpha)) :=
  AlgebraicGeometry.cokernelTildeIso (st.toGeometricStage hdim).alpha st.freeIso
      st.pushforwardIso st.liftedAlpha (st.alpha_toGeometricStage_comm hdim) ≪≫
    (tilde.functor (CommRingCat.of st.B)).mapIso
      (Submodule.quotEquivOfEq _ _ st.range_liftedAlpha).toModuleIso

end Module.DevissageStage

namespace Module

variable {R S N : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
  [AddCommGroup N] [Module S N] [Module.Finite S N] {q : Ideal S} [hqp : q.IsPrime]

/-- **A final pointed stage of an algebraic complete dévissage is a chain of one geometric
stage, pointed at the point of `q`.** -/
private theorem exists_chain_of_last (st : Module.DevissageStage R S N (q.under R))
    (P : st.toData.Pointed) (hst : st.toData.FibresHaveRelativeDimension)
    (hinit : P.upperPrime.comap st.toA₀.toRingHom = q)
    (hsurj : Function.Surjective st.alpha) :
    ∃ C : AlgebraicGeometry.DevissageChain
        (Spec.map (CommRingCat.ofHom (algebraMap R S))
          (⟨q, hqp⟩ : Spec (CommRingCat.of S)))
        (Spec (CommRingCat.of S)) (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (tilde (ModuleCat.of (CommRingCat.of S) N)) inferInstance inferInstance
        ((AlgebraicGeometry.tilde_isFiniteType_iff _).2 inferInstance),
      Nonempty (AlgebraicGeometry.PointedDevissageChain
        (Spec.map (CommRingCat.ofHom (algebraMap R S))
          (⟨q, hqp⟩ : Spec (CommRingCat.of S)))
        (Spec (CommRingCat.of S)) (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (tilde (ModuleCat.of (CommRingCat.of S) N)) inferInstance inferInstance
        ((AlgebraicGeometry.tilde_isFiniteType_iff _).2 inferInstance)
        (⟨q, hqp⟩ : Spec (CommRingCat.of S)) C) :=
  have hdim := st.geometricFiberDim P hst hinit
  have hzero := st.isZero_coker_toGeometricStage hdim hsurj
  ⟨.last (st.toGeometricStage hdim) hzero,
    ⟨.last _ (st.toGeometricStage hdim) hzero (st.toPointedStage P hst hinit)⟩⟩

/-- **A nonfinal pointed stage of an algebraic complete dévissage, followed by a chain for the
module the dévissage passes to, is a chain pointed at the point of `q`.** The chain supplied for
the quotient `M ⧸ range α` is carried over to the cokernel of the stage's map of sheaves by
`Module.DevissageStage.cokerToGeometricStageIso`, and its base point is moved from the point of
the stage's lower prime to the point of `q`, the two being equal because the lower prime lies
over the contraction of `q`. -/
private theorem exists_chain_of_cons (st : Module.DevissageStage R S N (q.under R))
    (P : st.toData.Pointed) (hst : st.toData.FibresHaveRelativeDimension)
    (hinit : P.upperPrime.comap st.toA₀.toRingHom = q)
    (htail : ∃ C : AlgebraicGeometry.DevissageChain
        (Spec.map (CommRingCat.ofHom (algebraMap R st.B))
          (⟨P.lowerPrime, P.lowerPrime_isPrime⟩ : Spec (CommRingCat.of st.B)))
        (Spec (CommRingCat.of st.B)) (Spec.map (CommRingCat.ofHom (algebraMap R st.B)))
        (tilde (ModuleCat.of (CommRingCat.of st.B) (st.M ⧸ LinearMap.range st.alpha)))
        inferInstance inferInstance
        ((AlgebraicGeometry.tilde_isFiniteType_iff _).2 inferInstance),
      Nonempty (AlgebraicGeometry.PointedDevissageChain
        (Spec.map (CommRingCat.ofHom (algebraMap R st.B))
          (⟨P.lowerPrime, P.lowerPrime_isPrime⟩ : Spec (CommRingCat.of st.B)))
        (Spec (CommRingCat.of st.B)) (Spec.map (CommRingCat.ofHom (algebraMap R st.B)))
        (tilde (ModuleCat.of (CommRingCat.of st.B) (st.M ⧸ LinearMap.range st.alpha)))
        inferInstance inferInstance
        ((AlgebraicGeometry.tilde_isFiniteType_iff _).2 inferInstance)
        (⟨P.lowerPrime, P.lowerPrime_isPrime⟩ : Spec (CommRingCat.of st.B)) C)) :
    ∃ C : AlgebraicGeometry.DevissageChain
        (Spec.map (CommRingCat.ofHom (algebraMap R S))
          (⟨q, hqp⟩ : Spec (CommRingCat.of S)))
        (Spec (CommRingCat.of S)) (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (tilde (ModuleCat.of (CommRingCat.of S) N)) inferInstance inferInstance
        ((AlgebraicGeometry.tilde_isFiniteType_iff _).2 inferInstance),
      Nonempty (AlgebraicGeometry.PointedDevissageChain
        (Spec.map (CommRingCat.ofHom (algebraMap R S))
          (⟨q, hqp⟩ : Spec (CommRingCat.of S)))
        (Spec (CommRingCat.of S)) (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (tilde (ModuleCat.of (CommRingCat.of S) N)) inferInstance inferInstance
        ((AlgebraicGeometry.tilde_isFiniteType_iff _).2 inferInstance)
        (⟨q, hqp⟩ : Spec (CommRingCat.of S)) C) := by
  have hdim := st.geometricFiberDim P hst hinit
  have hpt : (Spec.map (CommRingCat.ofHom (algebraMap R st.B))
        (⟨P.lowerPrime, P.lowerPrime_isPrime⟩ : Spec (CommRingCat.of st.B)) :
      Spec (CommRingCat.of R)) =
      Spec.map (CommRingCat.ofHom (algebraMap R S)) (⟨q, hqp⟩ : Spec (CommRingCat.of S)) :=
    PrimeSpectrum.ext P.lowerPrime_liesOver.over.symm
  have hbase : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R st.B))) :=
    AlgebraicGeometry.locallyOfFiniteType_specMap_algebraMap R st.B
  have hq0 : (tilde (ModuleCat.of (CommRingCat.of st.B)
      (st.M ⧸ LinearMap.range st.alpha))).IsQuasicoherent := inferInstance
  have ht0 : (tilde (ModuleCat.of (CommRingCat.of st.B)
      (st.M ⧸ LinearMap.range st.alpha))).IsFiniteType :=
    (AlgebraicGeometry.tilde_isFiniteType_iff _).2 inferInstance
  have hqc : (st.toGeometricStage hdim).coker.IsQuasicoherent :=
    Stacks.Descent.isQuasicoherent_of_iso (st.cokerToGeometricStageIso hdim).symm hq0
  have hft : (st.toGeometricStage hdim).coker.IsFiniteType :=
    AlgebraicGeometry.isFiniteType_of_iso (st.cokerToGeometricStageIso hdim).symm ht0
  obtain ⟨C, ⟨PC⟩⟩ := htail
  obtain ⟨C', ⟨PC'⟩⟩ := exists_chain_congr
    (Spec.map (CommRingCat.ofHom (algebraMap R st.B))) (st.toGeometricStage hdim).coker
    hbase hqc hft (⟨P.lowerPrime, P.lowerPrime_isPrime⟩ : Spec (CommRingCat.of st.B))
    hpt ⟨C.ofModuleIso (hl := hbase) (hq := hq0) (ht := ht0) (hq' := hqc) (ht' := hft)
        (st.cokerToGeometricStageIso hdim),
      ⟨PC.ofModuleIso (hl := hbase) (hq := hq0) (ht := ht0) (hq' := hqc) (ht' := hft)
        (st.cokerToGeometricStageIso hdim)⟩⟩
  exact ⟨.more (st.toGeometricStage hdim) hqc hft hbase C',
    ⟨.more _ (st.toGeometricStage hdim) hqc hft hbase C'
      (st.toPointedStage P hst hinit) PC'⟩⟩

end Module

/-- **The first map of a pointed complete dévissage with a single stage is surjective.** That
stage is the final one, and the cokernel of the final map of a complete dévissage vanishes. -/
private theorem surjective_head_alpha_of_stepCount_eq_zero {R S N : Type u} [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.FiniteType R S] [AddCommGroup N] [Module S N]
    [Module.Finite S N] {r : Ideal R} [r.IsPrime] {q : Ideal S} [q.IsPrime]
    (E : Module.PointedCompleteDevissage R S N r q) (h0 : E.toCompleteDevissage.stepCount = 0) :
    Function.Surjective E.toCompleteDevissage.head.alpha :=
  E.toCompleteDevissage.final_surjective_of_eq_last 0 (Fin.ext (by simp [h0]))

/-- **An algebraic complete dévissage at `q` with a prescribed number of stages gives a chain of
geometric stages with compatible distinguished points.** This is the recursion behind the
converse direction of Stacks 05I0 (2); the induction is on the number of stages. -/
private theorem exists_pointedChain {R : Type u} [CommRing R] {r : Ideal R} [r.IsPrime] :
    ∀ (n : ℕ) {S N : Type u} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
      [AddCommGroup N] [Module S N] [Module.Finite S N] {q : Ideal S} [hqp : q.IsPrime]
      (E : Module.PointedCompleteDevissage R S N r q)
      (_hE : E.toCompleteDevissage.FibresHaveRelativeDimension)
      (_hn : E.toCompleteDevissage.stepCount = n) (_hr : q.under R = r),
      ∃ C : AlgebraicGeometry.DevissageChain
          (Spec.map (CommRingCat.ofHom (algebraMap R S))
            (⟨q, hqp⟩ : Spec (CommRingCat.of S)))
          (Spec (CommRingCat.of S)) (Spec.map (CommRingCat.ofHom (algebraMap R S)))
          (tilde (ModuleCat.of (CommRingCat.of S) N)) inferInstance inferInstance
          ((AlgebraicGeometry.tilde_isFiniteType_iff _).2 inferInstance),
        Nonempty (AlgebraicGeometry.PointedDevissageChain
          (Spec.map (CommRingCat.ofHom (algebraMap R S))
            (⟨q, hqp⟩ : Spec (CommRingCat.of S)))
          (Spec (CommRingCat.of S)) (Spec.map (CommRingCat.ofHom (algebraMap R S)))
          (tilde (ModuleCat.of (CommRingCat.of S) N)) inferInstance inferInstance
          ((AlgebraicGeometry.tilde_isFiniteType_iff _).2 inferInstance)
          (⟨q, hqp⟩ : Spec (CommRingCat.of S)) C) := by
  intro n
  induction n with
  | zero =>
    intro S N _ _ _ _ _ _ q hqp E hE hn hr
    subst hr
    exact Module.exists_chain_of_last E.toCompleteDevissage.head (E.pointed 0) (hE 0)
      E.initial_under
      (surjective_head_alpha_of_stepCount_eq_zero E hn)
  | succ n ih =>
    intro S N _ _ _ _ _ _ q hqp E hE hn hr
    subst hr
    have hpos : E.toCompleteDevissage.stepCount ≠ 0 := by rw [hn]; omega
    refine Module.exists_chain_of_cons E.toCompleteDevissage.head (E.pointed 0) (hE 0)
      E.initial_under ?_
    have : (show Ideal E.toCompleteDevissage.head.B from (E.pointed 0).lowerPrime).IsPrime :=
      (E.pointed 0).lowerPrime_isPrime
    exact ih (E.tail hpos)
      (fun i => hE (Fin.cast (Nat.succ_pred_eq_of_ne_zero hpos) i).succ)
      (show E.toCompleteDevissage.stepCount - 1 = n by omega)
      (E.pointed 0).lowerPrime_liesOver.over.symm

/-- **The converse direction of Stacks 05I0 (2):** a complete dévissage of `N/B/A` at a prime `q`
of `B` gives a complete dévissage of `Ñ/Spec B/Spec A` at the point of `q`.

The empty dévissage of a trivial module gives the empty dévissage of the zero sheaf, the tilde
functor being additive. A nonempty one is read as a `Module.PointedCompleteDevissage` over
`q.under A` and fed to `exists_pointedChain`. -/
private theorem nonempty_completeDevissageAt_of_algebraic (A B : Type u) [CommRing A]
    [CommRing B] [Algebra A B] [Algebra.FiniteType A B] (N : Type u) [AddCommGroup N]
    [Module B N] [Module.Finite B N] (q : PrimeSpectrum B)
    (D : @Module.CompleteDevissageAt A B N _ _ _ _ _ _ _ q.asIdeal q.isPrime)
    (hD : D.FibresHaveRelativeDimension) :
    Nonempty (@AlgebraicGeometry.CompleteDevissageAt (Spec (.of B)) (Spec (.of A))
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (tilde (R := .of B) (ModuleCat.of B N)) q
      (AlgebraicGeometry.locallyOfFiniteType_specMap_algebraMap A B) inferInstance
      ((AlgebraicGeometry.tilde_isFiniteType_iff (R := .of B) (ModuleCat.of B N)).2
        inferInstance)) := by
  have : q.asIdeal.IsPrime := q.isPrime
  match D, hD with
  | .empty hsub, _ =>
    have := hsub
    have := AlgebraicGeometry.KunnethQcqs.tilde_additive (CommRingCat.of B)
    exact ⟨.empty ((tilde.functor (CommRingCat.of B)).map_isZero
      (ModuleCat.isZero_of_subsingleton (ModuleCat.of B N)))⟩
  | .nonempty data, hD =>
    obtain ⟨C, ⟨PC⟩⟩ := exists_pointedChain data.toCompleteDevissage.stepCount
      (q := q.asIdeal)
      { toCompleteDevissage := data.toCompleteDevissage, pointed := data.pointedStages,
        initial_under := data.initial_under, transition_under := data.transition_under }
      hD rfl rfl
    exact ⟨.nonempty { toNonemptyCompleteDevissage := ⟨C⟩, pointed := PC }⟩

/-- **Stacks Project, Tag 05I0 (2)**, as an equivalence. For a ring map `A → B` of finite type,
a finite `B`-module `N` and a prime `q` of `B`, a complete dévissage of `Ñ/Spec B/Spec A` at the
point of `q` exists if and only if a complete dévissage of `N/B/A` at `q` exists.

The relative dimension condition of Stacks 05HZ (4) is read fibre by fibre, as Stacks 05I0
describes it: every fibre of `Spec Bᵢ → Spec A` has the dimension
`dim_{qᵢ}(Supp(Mᵢ ⊗ κ(r)))`. That is the supremum condition
`Module.NonemptyCompleteDevissageAt.relativeDimension_eq_support` of the dévissage together with
`Module.CompleteDevissageAt.FibresHaveRelativeDimension`.

The direction from sheaves to modules is
`AlgebraicGeometry.exists_completeDevissageAt_fibresHaveRelativeDimension_of_spec`; the converse
is `nonempty_completeDevissageAt_of_algebraic`. -/
@[stacks 05I0 "(2): a complete dévissage at a point exists for the sheaf exactly when it \
exists for the module"]
public theorem Module.nonempty_completeDevissageAt_iff (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.FiniteType A B] (N : Type u) [AddCommGroup N] [Module B N]
    [Module.Finite B N] (q : PrimeSpectrum B) :
    Nonempty (@AlgebraicGeometry.CompleteDevissageAt (Spec (.of B)) (Spec (.of A))
        (Spec.map (CommRingCat.ofHom (algebraMap A B)))
        (tilde (R := .of B) (ModuleCat.of B N)) q
        (AlgebraicGeometry.locallyOfFiniteType_specMap_algebraMap A B) inferInstance
        ((AlgebraicGeometry.tilde_isFiniteType_iff (R := .of B) (ModuleCat.of B N)).2
          inferInstance)) ↔
      ∃ D : @Module.CompleteDevissageAt A B N _ _ _ _ _ _ _ q.asIdeal q.isPrime,
        D.FibresHaveRelativeDimension :=
  ⟨AlgebraicGeometry.exists_completeDevissageAt_fibresHaveRelativeDimension_of_spec A B N q,
    fun ⟨D, hD⟩ => nonempty_completeDevissageAt_of_algebraic A B N q D hD⟩

end
