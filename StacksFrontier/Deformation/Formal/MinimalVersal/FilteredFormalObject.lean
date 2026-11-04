module

public import StacksFrontier.Deformation.Formal.MinimalVersal.StageTowerFiltration

/-!
# The minimal stages as a filtered formal object

The minimal stages assemble into a formal object filtered by the kernels of the projections of the
stage tower limit. To compare such a filtered formal object with the adic filtration one uses, for
every `n`, the filtration index `toAdicIndex` whose ideal lies inside the `n`-th adic ideal; this
file sets up the composite transition maps of a filtration and the projections of the filtration
quotients onto the adic truncations.

## Main definitions

* `Deformation.minimalStagesFilteredFormalObject`: the minimal stages, assembled into a formal
  object filtered by `stageBaseTowerIdealFiltration`.
* `Deformation.filteredObjectPath`: the composite transition morphism of a filtered formal object
  from level `n` down to level `m ≤ n`.
* `Deformation.stageFormalQuotientToAdic`: the projection from the quotient of
  `stageBaseTowerCompleteLocal` at index `toAdicIndex I n` onto its `n`-th adic truncation.
* `Deformation.stageAdicBasePath`: the composite transition map of the adic truncations of
  `stageBaseTowerCompleteLocal` from index `n` down to index `m ≤ n`.

## Main results

* `Deformation.filteredObjectPath_self`: `filteredObjectPath` at a reflexive inequality is the
  identity.
* `Deformation.filteredObjectPath_succ`: `filteredObjectPath` from a successor is the transition
  morphism followed by the shorter path.
* `Deformation.filteredObjectPath_lift`: `filteredObjectPath` lies over `filteredBasePath`.
* `Deformation.stageFormalQuotientToAdic_mk`: `stageFormalQuotientToAdic` is the canonical map of
  quotients, computed on representatives.
* `Deformation.stageAdicBasePath_self`: `stageAdicBasePath` at a reflexive inequality is the
  identity.
* `Deformation.stageAdicBasePath_succ`: `stageAdicBasePath` to a successor is the truncation
  transition followed by the shorter path.
* `Deformation.stageAdicBasePath_mk`: `stageAdicBasePath` is the canonical map of quotients,
  computed on representatives.
* `Deformation.stageFormalQuotient_square`: the projections `stageFormalQuotientToAdic` commute
  with the transition maps of the filtration and of the adic truncations.
* `Deformation.stageFormalPsi_lift`: the transition morphism of a filtered formal object, taken
  along `toAdicIndex`, lies over the composite of `stageFormalQuotientToAdic` with the
  truncation transition.

## References

* [Stacks Project, Tag 06T2](https://stacks.math.columbia.edu/tag/06T2)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u v w uF vF

namespace Deformation

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]
variable {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}


section
variable [IsNoetherianRing Λ] [Module.Finite Λ k]
/-- The minimal stages, assembled into a formal object filtered by `stageBaseTowerIdealFiltration`.
The minimal stages, assembled into a formal object filtered by `stageBaseTowerIdealFiltration`. -/
noncomputable def minimalStagesFilteredFormalObject
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (hbound : ∃ d : ℕ, ∀ n,
      Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) ≤ d) :
    FilteredFormalObject p
      (stageBaseTowerCompleteLocal hp hS1 ξ hbound)
      (stageBaseTowerIdealFiltration hp hS1 ξ hbound) := by
  let I := stageBaseTowerIdealFiltration hp hS1 ξ hbound
  let e (n : ℕ) := stageBaseTowerQuotientIso hp hS1 ξ hbound n
  let level (n : ℕ) := cofiberedPushforwardObj hp (e n).inv
    (minimalStages hp hS1 ξ n).obj.left rfl
  let inclusion (n : ℕ) := cofiberedPushforwardMap hp (e n).inv
    (minimalStages hp hS1 ξ n).obj.left rfl
  let transition (n : ℕ) :=
    cofiberedPushforwardDesc hp (e (n + 1)).inv (I.transition n)
      (minimalStages hp hS1 ξ (n + 1)).obj.left (level n) rfl
      (stageObjectTransition hp hS1 ξ n ≫ inclusion n) (by
        have hmap : p.map (stageObjectTransition hp hS1 ξ n) =
            stageBaseTowerTransition hp hS1 ξ n :=
          stageObjectTransition_map hp hS1 ξ n
        let : p.IsHomLift (stageBaseTowerTransition hp hS1 ξ n)
            (stageObjectTransition hp hS1 ξ n) :=
          hmap.symm ▸
            IsHomLift.map (p := p) (stageObjectTransition hp hS1 ξ n)
        let := cofiberedPushforwardMap_lift hp (e n).inv
          (minimalStages hp hS1 ξ n).obj.left rfl
        have hcomp : p.IsHomLift
            (stageBaseTowerTransition hp hS1 ξ n ≫ (e n).inv)
            (stageObjectTransition hp hS1 ξ n ≫ inclusion n) := inferInstance
        exact (stageBaseTowerQuotientIso_inv_transition_fac hp hS1 ξ hbound n).symm ▸ hcomp)
  have transition_lift (n : ℕ) : p.IsHomLift (I.transition n) (transition n) :=
    cofiberedPushforwardDesc_lift hp (e (n + 1)).inv (I.transition n)
      (minimalStages hp hS1 ξ (n + 1)).obj.left (level n) rfl
      (stageObjectTransition hp hS1 ξ n ≫ inclusion n) (by
        have hmap : p.map (stageObjectTransition hp hS1 ξ n) =
            stageBaseTowerTransition hp hS1 ξ n :=
          stageObjectTransition_map hp hS1 ξ n
        let : p.IsHomLift (stageBaseTowerTransition hp hS1 ξ n)
            (stageObjectTransition hp hS1 ξ n) :=
          hmap.symm ▸
            IsHomLift.map (p := p) (stageObjectTransition hp hS1 ξ n)
        let := cofiberedPushforwardMap_lift hp (e n).inv
          (minimalStages hp hS1 ξ n).obj.left rfl
        have hcomp : p.IsHomLift
            (stageBaseTowerTransition hp hS1 ξ n ≫ (e n).inv)
            (stageObjectTransition hp hS1 ξ n ≫ inclusion n) := inferInstance
        exact (stageBaseTowerQuotientIso_inv_transition_fac hp hS1 ξ hbound n).symm ▸ hcomp)
  exact
    { level := level
      level_eq := fun n => cofiberedPushforwardObj_eq hp (e n).inv
        (minimalStages hp hS1 ξ n).obj.left rfl
      transition := transition
      transition_lift := transition_lift }

/-- The composite transition morphism of a filtered formal object from level `n` down to level `m ≤
n`. -/
noncomputable def filteredObjectPath
    {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    (I : IdealFiltration R)
    (X : FilteredFormalObject p R I)
    {m n : ℕ} (h : m ≤ n) : X.level n ⟶ X.level m :=
  Nat.leRecOn h (fun {j} f => X.transition j ≫ f) (𝟙 (X.level m))

omit [IsNoetherianRing Λ] [Module.Finite Λ k] in
/-- `filteredObjectPath` at a reflexive inequality is the identity. -/
lemma filteredObjectPath_self
    {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    (I : IdealFiltration R)
    (X : FilteredFormalObject p R I) (n : ℕ) :
    filteredObjectPath I X le_rfl = 𝟙 (X.level n) := by
  unfold filteredObjectPath
  exact Nat.leRecOn_self _

omit [IsNoetherianRing Λ] [Module.Finite Λ k] in
/-- `filteredObjectPath` from a successor is the transition morphism followed by the shorter path.
`filteredObjectPath` from a successor is the transition morphism followed by the shorter path. -/
lemma filteredObjectPath_succ
    {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    (I : IdealFiltration R)
    (X : FilteredFormalObject p R I)
    (n m : ℕ) (h : n ≤ m) :
    filteredObjectPath I X (h.trans (Nat.le_succ m)) =
      X.transition m ≫ filteredObjectPath I X h := by
  unfold filteredObjectPath
  exact Nat.leRecOn_succ h _

omit [IsNoetherianRing Λ] [Module.Finite Λ k] in
/-- `filteredObjectPath` lies over `filteredBasePath`. -/
theorem filteredObjectPath_lift
    {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    (I : IdealFiltration R)
    (X : FilteredFormalObject p R I)
    {m n : ℕ} (h : m ≤ n) :
    p.IsHomLift (filteredBasePath I m n h) (filteredObjectPath I X h) := by
  induction n, h using Nat.le_induction with
  | base =>
      rw [filteredBasePath_self, filteredObjectPath_self]
      exact IsHomLift.id (X.level_eq m)
  | succ n h ih =>
      rw [filteredBasePath_succ I m n h,
        filteredObjectPath_succ I X m n h]
      let := X.transition_lift n
      let := ih
      infer_instance

/-- The projection from the quotient of `stageBaseTowerCompleteLocal` at index `toAdicIndex I
n` onto its `n`-th adic truncation. -/
noncomputable def stageFormalQuotientToAdic
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (hbound : ∃ d : ℕ, ∀ n,
      Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) ≤ d)
    (n : ℕ) :
    (stageBaseTowerIdealFiltration hp hS1 ξ hbound).quotient
        (toAdicIndex (stageBaseTowerIdealFiltration hp hS1 ξ hbound) n) ⟶
      AdicTruncation.obj (stageBaseTowerCompleteLocal hp hS1 ξ hbound) n := by
  let I := stageBaseTowerIdealFiltration hp hS1 ξ hbound
  let R := stageBaseTowerCompleteLocal hp hS1 ξ hbound
  let m := toAdicIndex I n
  let h := toAdicIndex_le I n
  let f := Ideal.Quotient.factorₐ Λ h
  have hsource : I.ideal m < ⊤ := I.isProper m
  letI : Nontrivial (R ⧸ I.ideal m) :=
    Ideal.Quotient.nontrivial_iff.mpr hsource.ne
  letI : IsLocalRing (R ⧸ I.ideal m) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (I.ideal m))
      Ideal.Quotient.mk_surjective
  have hproper : AdicTruncation.ideal R n < ⊤ :=
    (Ideal.pow_le_self (Nat.succ_ne_zero n)).trans_lt (maximalIdeal.isMaximal R).lt_top
  letI : Nontrivial (R ⧸ AdicTruncation.ideal R n) :=
    Ideal.Quotient.nontrivial_iff.mpr hproper.ne
  letI : IsLocalRing (R ⧸ AdicTruncation.ideal R n) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (AdicTruncation.ideal R n))
      Ideal.Quotient.mk_surjective
  refine
    { hom := f
      isLocal := IsLocalHom.of_surjective f.toRingHom
        (Ideal.Quotient.factor_surjective h)
      residue_comm := ?_ }
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  change AdicTruncation.residueEquiv R n
      (residue (AdicTruncation.obj R n)
        (f (Ideal.Quotient.mk (I.ideal m) r))) =
    I.residueEquiv m (residue (I.quotient m) (Ideal.Quotient.mk (I.ideal m) r))
  rw [Ideal.Quotient.factorₐ_apply_mk]
  exact (AdicTruncation.residueEquiv_residue_mk R n r).trans
    (I.residueEquiv_residue_mk m r).symm

/-- `stageFormalQuotientToAdic` is the canonical map of quotients, computed on representatives. -/
lemma stageFormalQuotientToAdic_mk
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (hbound : ∃ d : ℕ, ∀ n,
      Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) ≤ d)
    (n : ℕ) (r : stageBaseTowerCompleteLocal hp hS1 ξ hbound) :
    (stageFormalQuotientToAdic hp hS1 ξ hbound n).hom
      (Ideal.Quotient.mk
        ((stageBaseTowerIdealFiltration hp hS1 ξ hbound).ideal
          (toAdicIndex (stageBaseTowerIdealFiltration hp hS1 ξ hbound) n)) r) =
    Ideal.Quotient.mk (AdicTruncation.ideal
      (stageBaseTowerCompleteLocal hp hS1 ξ hbound) n) r := rfl

/-- The composite transition map of the adic truncations of `stageBaseTowerCompleteLocal` from
index `n` down to index `m ≤ n`. -/
noncomputable def stageAdicBasePath
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (n m : ℕ) (h : n ≤ m) :
    AdicTruncation.obj R m ⟶ AdicTruncation.obj R n :=
  Nat.leRecOn h (fun {j} f => AdicTruncation.transition R j ≫ f)
    (𝟙 (AdicTruncation.obj R n))


omit [IsNoetherianRing Λ] [Module.Finite Λ k] in
/-- `stageAdicBasePath` at a reflexive inequality is the identity. -/
lemma stageAdicBasePath_self
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (n : ℕ) :
    stageAdicBasePath R n n le_rfl = 𝟙 (AdicTruncation.obj R n) := by
  unfold stageAdicBasePath
  exact Nat.leRecOn_self _

omit [IsNoetherianRing Λ] [Module.Finite Λ k] in
/-- `stageAdicBasePath` to a successor is the truncation transition followed by the shorter path.
`stageAdicBasePath` to a successor is the truncation transition followed by the shorter path. -/
lemma stageAdicBasePath_succ
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (n m : ℕ) (h : n ≤ m) :
    stageAdicBasePath R n (m + 1) (h.trans (Nat.le_succ m)) =
      AdicTruncation.transition R m ≫ stageAdicBasePath R n m h := by
  unfold stageAdicBasePath
  exact Nat.leRecOn_succ h _

omit [IsNoetherianRing Λ] [Module.Finite Λ k] in
/-- `stageAdicBasePath` is the canonical map of quotients, computed on representatives. -/
lemma stageAdicBasePath_mk
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (n m : ℕ) (h : n ≤ m) (r : R) :
    (stageAdicBasePath R n m h).hom
      (Ideal.Quotient.mk (AdicTruncation.ideal R m) r) =
        Ideal.Quotient.mk (AdicTruncation.ideal R n) r := by
  induction m, h using Nat.le_induction with
  | base => rw [stageAdicBasePath_self]; rfl
  | succ m hm ih =>
      rw [stageAdicBasePath_succ R n m hm, ArtinianLocalAlgCat.comp_hom]
      change (stageAdicBasePath R n m hm).hom
        ((AdicTruncation.transition R m).hom
          (Ideal.Quotient.mk (AdicTruncation.ideal R (m + 1)) r)) = _
      change (stageAdicBasePath R n m hm).hom
        (Ideal.Quotient.mk (AdicTruncation.ideal R m) r) = _
      exact ih

/-- The projections `stageFormalQuotientToAdic` commute with the transition maps of the filtration
and of the adic truncations. -/
lemma stageFormalQuotient_square
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (hbound : ∃ d : ℕ, ∀ n,
      Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) ≤ d)
    (n m : ℕ) (h : n ≤ m) :
    stageFormalQuotientToAdic hp hS1 ξ hbound m ≫
        stageAdicBasePath (stageBaseTowerCompleteLocal hp hS1 ξ hbound) n m h =
      filteredBasePath (stageBaseTowerIdealFiltration hp hS1 ξ hbound)
          (toAdicIndex (stageBaseTowerIdealFiltration hp hS1 ξ hbound) n)
          (toAdicIndex (stageBaseTowerIdealFiltration hp hS1 ξ hbound) m)
          (toAdicIndex_mono
            (stageBaseTowerIdealFiltration hp hS1 ξ hbound) h) ≫
        stageFormalQuotientToAdic hp hS1 ξ hbound n := by
  let I := stageBaseTowerIdealFiltration hp hS1 ξ hbound
  let R := stageBaseTowerCompleteLocal hp hS1 ξ hbound
  let b := toAdicIndex I
  apply ArtinianLocalAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  change (stageAdicBasePath R n m h).hom
      ((stageFormalQuotientToAdic hp hS1 ξ hbound m).hom
        (Ideal.Quotient.mk (I.ideal (b m)) r)) =
    (stageFormalQuotientToAdic hp hS1 ξ hbound n).hom
      ((filteredBasePath I (toAdicIndex I n) (toAdicIndex I m)
          (toAdicIndex_mono I h)).hom
        (Ideal.Quotient.mk (I.ideal (b m)) r))
  rw [stageFormalQuotientToAdic_mk, stageAdicBasePath_mk,
    filteredBasePath_mk, stageFormalQuotientToAdic_mk]

/-- The transition morphism of a filtered formal object, taken along `toAdicIndex`, lies over
the composite of `stageFormalQuotientToAdic` with the truncation transition. -/
theorem stageFormalPsi_lift
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (hbound : ∃ d : ℕ, ∀ n,
      Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) ≤ d)
    (X : FilteredFormalObject p
      (stageBaseTowerCompleteLocal hp hS1 ξ hbound)
      (stageBaseTowerIdealFiltration hp hS1 ξ hbound))
    (n : ℕ) :
    p.IsHomLift
      (stageFormalQuotientToAdic hp hS1 ξ hbound (n + 1) ≫
        AdicTruncation.transition (stageBaseTowerCompleteLocal hp hS1 ξ hbound) n)
      (filteredObjectPath (stageBaseTowerIdealFiltration hp hS1 ξ hbound) X
          (toAdicIndex_mono
            (stageBaseTowerIdealFiltration hp hS1 ξ hbound) (Nat.le_succ n)) ≫
        cofiberedPushforwardMap hp
          (stageFormalQuotientToAdic hp hS1 ξ hbound n)
          (X.level (toAdicIndex
            (stageBaseTowerIdealFiltration hp hS1 ξ hbound) n))
          (X.level_eq (toAdicIndex
            (stageBaseTowerIdealFiltration hp hS1 ξ hbound) n))) := by
  let I := stageBaseTowerIdealFiltration hp hS1 ξ hbound
  let R := stageBaseTowerCompleteLocal hp hS1 ξ hbound
  let b := toAdicIndex I
  let h := toAdicIndex_mono I (Nat.le_succ n)
  let := filteredObjectPath_lift I X h
  let := cofiberedPushforwardMap_lift hp (stageFormalQuotientToAdic hp hS1 ξ hbound n)
    (X.level (b n)) (X.level_eq (b n))
  have hcomp : p.IsHomLift
      (filteredBasePath I (toAdicIndex I n) (toAdicIndex I (n + 1)) h ≫
        stageFormalQuotientToAdic hp hS1 ξ hbound n)
      (filteredObjectPath I X h ≫
        cofiberedPushforwardMap hp (stageFormalQuotientToAdic hp hS1 ξ hbound n)
          (X.level (b n)) (X.level_eq (b n))) := inferInstance
  have htr : stageAdicBasePath R n (n + 1) (Nat.le_succ n) =
      AdicTruncation.transition R n := by
    rw [stageAdicBasePath_succ R n n le_rfl, stageAdicBasePath_self,
      Category.comp_id]
  have hsq := stageFormalQuotient_square hp hS1 ξ hbound n (n + 1)
    (Nat.le_succ n)
  rw [htr] at hsq
  rw [← hsq] at hcomp
  exact hcomp

end

end Deformation

end
