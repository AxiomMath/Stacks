module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import StacksFrontier.Examples.Completion.PadicDirectSumNotDerivedComplete
public import StacksFrontier.Homology.DerivedComplete.CompletionAdjunction
public import StacksFrontier.Homology.DerivedComplete.PseudoCoherentComplete
import StacksCore.Tactic.StacksAttribute

/-!
# The category of derived complete modules

For a commutative ring `A` and an ideal `I`, the derived complete `A`-modules form an abelian
category whose inclusion into all `A`-modules is exact and preserves limits, and which has all
colimits when `I` is finitely generated. Nothing better is true: the inclusion does not preserve
colimits, not even countable direct sums; filtered colimits in the category are not exact; and it
is not a Grothendieck abelian category.

All three failures happen over `ℤ_[2]` with `I = (2)`. For colimits and direct sums the witness
is the direct sum of countably many copies of the ring: it is a coproduct of derived complete
modules whose underlying module is not derived complete, so the coproduct computed in the
subcategory cannot be the one computed in modules. For filtered colimits, take the constant
sequential diagram on `A/(2)` and map it to the tower `A/(2) → A/(4) → ⋯` whose transition maps
are multiplication by `2`; each component is a monomorphism, and the colimit of the tower is
zero because any cocone out of it is determined by a solution of the recurrence
`xₙ = 2·xₙ₊₁`, which derived completeness of the target forces to vanish. A sequential colimit
that destroys a monomorphism contradicts exactness, hence also AB5, hence Grothendieckness.

## Main results

* `Stacks.Examples.derivedCompleteModules_abelian_exact_colimits_not_grothendieck`: the whole of
  Stacks 0ARD, the positive statements for every ring and ideal together with the failures over
  `ℤ_[2]`.
* `Stacks.Examples.derivedCompleteModules_not_exactColimits_nat`: sequential colimits of
  derived complete modules are not exact.
* `Stacks.Examples.derivedCompleteModules_inclusion_not_preservesCoproducts`: the inclusion
  does not preserve countable coproducts.
* `Stacks.Examples.derivedCompleteModules_inclusion_not_preservesColimits`: hence it does not
  preserve arbitrary colimits.
* `Stacks.Examples.derivedCompleteModules_not_isGrothendieckAbelian`: the category is not
  Grothendieck abelian.

## Implementation notes

The category is the full subcategory of `ModuleCat A` cut out by `IsDerivedCompleteModule I`,
not the full subcategory of the derived category on all derived complete objects. As in Mathlib's
`HasExactColimitsOfShape`, exactness of colimits is stated relative to their existence, which the
main statement asserts alongside it. The positive statements coincide with Stacks 0GLP and are
deduced from `CompletionAdjunction.derivedCompleteModules_abelian_hasLimits_exact_hasColimits`.

## References

* [Stacks Project, Tag 0ARD](https://stacks.math.columbia.edu/tag/0ARD)
* [Stacks Project, Tag 0GLP](https://stacks.math.columbia.edu/tag/0GLP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Examples

private theorem spanPower_dvd_cancel {A : Type*} [CommRing A] [IsDomain A]
    {f x : A} (hf : f ≠ 0) (n : ℕ)
    (h : f ^ n * x ∈ (Ideal.span {f} : Ideal A) ^ (n + 1)) :
    x ∈ Ideal.span {f} := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
  obtain ⟨y, hy⟩ := h
  rw [Ideal.mem_span_singleton]
  exact ⟨y, mul_left_cancel₀ (pow_ne_zero n hf)
    (by simpa [pow_succ, mul_assoc] using hy)⟩

/-- The `n`-th stage `A ⧸ I^{n+1}` of the tower. -/
private def quotientStage (A : Type*) [CommRing A] (I : Ideal A) (n : ℕ) :
    ModuleCat A := ModuleCat.of A (A ⧸ I ^ (n + 1))

private theorem quotientStage_isDerivedComplete (A : Type*) [CommRing A]
    (I : Ideal A) [HasProductsOfShape ℕ (DerivedCategory (ModuleCat A))] (n : ℕ) :
    IsDerivedCompleteModule I (quotientStage A I n) := by
  rw [isDerivedCompleteModule_iff_isDerivedComplete]
  intro a ha
  apply isDerivedCompleteAt_of_isNilpotent
  refine ⟨n + 1, ?_⟩
  rw [smul_id_pow]
  have hM : a ^ (n + 1) • 𝟙 (quotientStage A I n) = 0 := by
    ext x
    induction x using Submodule.Quotient.induction_on with | _ x =>
      change Submodule.Quotient.mk (a ^ (n + 1) * x) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      simpa [mul_comm] using
        Ideal.mul_mem_left (I ^ (n + 1)) x (Ideal.pow_mem_pow ha (n + 1))
  simpa using congrArg ((DerivedCategory.singleFunctor (ModuleCat A) 0).map) hM

/-- Multiplication by `f`, from the `n`-th stage of the tower to the next. -/
private def quotientStageTransition (A : Type*) [CommRing A] (f : A) (I : Ideal A)
    (hf : f ∈ I) (n : ℕ) : quotientStage A I n ⟶ quotientStage A I (n + 1) := by
  let m : A →ₗ[A] A := f • LinearMap.id
  refine ModuleCat.ofHom ((I ^ (n + 1)).mapQ (I ^ (n + 2)) m ?_)
  intro x hx
  change f * x ∈ I ^ (n + 2)
  rw [show n + 2 = (n + 1) + 1 by omega, Submodule.pow_succ]
  simpa [mul_comm] using Ideal.mul_mem_mul hx hf

private theorem quotientStageTransition_apply_mk_one (A : Type*) [CommRing A]
    (f : A) (I : Ideal A) (hf : f ∈ I) (n : ℕ) :
    (quotientStageTransition A f I hf n).hom (Submodule.Quotient.mk (1 : A)) =
      f • (Submodule.Quotient.mk (1 : A) : quotientStage A I (n + 1)) := by
  let m : A →ₗ[A] A := f • LinearMap.id
  have hm : ∀ x ∈ I ^ (n + 1), m x ∈ I ^ (n + 2) := by
    intro x hx
    change f * x ∈ I ^ (n + 2)
    rw [show n + 2 = (n + 1) + 1 by omega, Submodule.pow_succ]
    simpa [mul_comm] using Ideal.mul_mem_mul hx hf
  change (I ^ (n + 1)).mapQ (I ^ (n + 2)) m hm
    (Submodule.Quotient.mk (1 : A)) = _
  rw [Submodule.mapQ_apply]
  simpa [m] using (Submodule.Quotient.mk_smul (I ^ (n + 2)) f (1 : A))

/-- Multiplication by `f ^ n`, from the bottom stage of the tower to the `n`-th. -/
private def quotientStageMap (A : Type*) [CommRing A] (f : A) (I : Ideal A)
    (hf : f ∈ I) (n : ℕ) : quotientStage A I 0 ⟶ quotientStage A I n := by
  let m : A →ₗ[A] A := f ^ n • LinearMap.id
  refine ModuleCat.ofHom ((I ^ 1).mapQ (I ^ (n + 1)) m ?_)
  intro x hx
  change f ^ n * x ∈ I ^ (n + 1)
  rw [Submodule.pow_succ]
  simpa [mul_comm] using Ideal.mul_mem_mul hx (Ideal.pow_mem_pow hf n)

private theorem quotientStageMap_injective {A : Type*} [CommRing A] [IsDomain A]
    (f : A) (hf : f ∈ Ideal.span {f}) (hf0 : f ≠ 0) (n : ℕ) :
    Function.Injective (quotientStageMap A f (Ideal.span {f}) hf n).hom := by
  intro x y hxy
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    induction y using Submodule.Quotient.induction_on with
    | _ y =>
      change Submodule.Quotient.mk (f ^ n * x) =
        Submodule.Quotient.mk (f ^ n * y) at hxy
      have hmem : f ^ n * x - f ^ n * y ∈ (Ideal.span {f} : Ideal A) ^ (n + 1) :=
        (Submodule.Quotient.eq _).mp hxy
      apply (Submodule.Quotient.eq _).2
      rw [pow_one]
      exact spanPower_dvd_cancel (x := x - y) hf0 n (by simpa [mul_sub] using hmem)

private theorem quotientStageMap_comp_transition (A : Type*) [CommRing A] (f : A) (I : Ideal A)
    (hf : f ∈ I) (n : ℕ) :
    quotientStageMap A f I hf n ≫ quotientStageTransition A f I hf n =
      quotientStageMap A f I hf (n + 1) := by
  apply ModuleCat.hom_ext
  ext x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    change Submodule.Quotient.mk (f * (f ^ n * x)) = Submodule.Quotient.mk (f ^ (n + 1) * x)
    rw [pow_succ]
    congr 1
    ring

private theorem quotientStage_hom_eq_zero {A : Type u} [CommRing A]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))] (f : A) (I : Ideal A)
    (hf : f ∈ I) {M : ModuleCat.{u} A} (hM : IsDerivedCompleteModule I M)
    (g : ∀ n, quotientStage A I n ⟶ M)
    (hg : ∀ n, quotientStageTransition A f I hf n ≫ g (n + 1) = g n) (n : ℕ) : g n = 0 := by
  let x : ℕ → M := fun n => (g n).hom (Submodule.Quotient.mk 1)
  have hrec (n : ℕ) : x n - f • x (n + 1) = 0 := by
    have hv := congrArg (fun φ : quotientStage A I n ⟶ M =>
      φ.hom (Submodule.Quotient.mk (1 : A))) (hg n)
    change (g (n + 1)).hom ((quotientStageTransition A f I hf n).hom
      (Submodule.Quotient.mk (1 : A))) = x n at hv
    rw [quotientStageTransition_apply_mk_one] at hv
    exact sub_eq_zero.mpr ((map_smul (g (n + 1)).hom f _).symm.trans hv).symm
  have hx : x = 0 := ((bijective_recurrence_iff_isDerivedCompleteModule I M).mp hM f hf).1
    (funext fun n => by simp [hrec n])
  apply ModuleCat.hom_ext
  ext z
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
    change (g n).hom (Submodule.Quotient.mk z) = 0
    calc
      (g n).hom (Submodule.Quotient.mk z) =
          (g n).hom (Submodule.Quotient.mk (z • (1 : A))) := by simp
      _ = (g n).hom (z • Submodule.Quotient.mk (1 : A)) :=
        congrArg (g n).hom (Submodule.Quotient.mk_smul (I ^ (n + 1)) z (1 : A))
      _ = z • x n := map_smul _ _ _
      _ = 0 := by simp [hx]

private theorem padicInt_two_mk_one_ne_zero :
    (Submodule.Quotient.mk (1 : ℤ_[2]) : ℤ_[2] ⧸ Ideal.span {(2 : ℤ_[2])} ^ 1) ≠ 0 := by
  intro h
  have h₁ := (Submodule.Quotient.mk_eq_zero _).mp h
  rw [pow_one, Ideal.mem_span_singleton] at h₁
  obtain ⟨a, ha⟩ := h₁
  exact PadicInt.p_nonunit (p := 2)
    (by simpa using (IsUnit.of_mul_eq_one a ha.symm : IsUnit (2 : ℤ_[2])))

/-- Sequential filtered colimits of derived complete modules over the `2`-adic
integers, with respect to `(2)`, are not exact. -/
theorem derivedCompleteModules_not_exactColimits_nat :
    letI : HasProductsOfShape ℕ (DerivedCategory (ModuleCat (ℤ_[2]))) :=
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    let P : ObjectProperty (ModuleCat (ℤ_[2])) := fun M =>
      IsDerivedCompleteModule (Ideal.span {(2 : ℤ_[2])}) M
    let C := P.FullSubcategory
    ∀ [HasColimitsOfShape ℕ C], ¬ HasExactColimitsOfShape ℕ C := by
  intro _ _ _ _
  let A := ℤ_[2]
  let f : A := 2
  let I : Ideal A := Ideal.span {f}
  let P : ObjectProperty (ModuleCat A) := fun M => IsDerivedCompleteModule I M
  let C := P.FullSubcategory
  have hf : f ∈ I := Ideal.subset_span (by simp)
  have hcomplete (n : ℕ) : IsDerivedCompleteModule I (quotientStage A I n) :=
    quotientStage_isDerivedComplete A I n
  let source : C := ⟨quotientStage A I 0, hcomplete 0⟩
  let Ybase : ℕ ⥤ ModuleCat A := Functor.ofSequence (X := fun n => quotientStage A I n)
    (fun n => quotientStageTransition A f I hf n)
  let Y : ℕ ⥤ C := P.lift Ybase hcomplete
  let αbase : (Functor.const ℕ).obj (quotientStage A I 0) ⟶ Ybase :=
    NatTrans.ofSequence (fun n => quotientStageMap A f I hf n) fun n => by
      simp only [Functor.const_obj_map, Ybase, Functor.ofSequence_map_homOfLE_succ]
      exact (quotientStageMap_comp_transition A f I hf n).symm
  let α : (Functor.const ℕ).obj source ⟶ Y :=
    { app := fun n => P.homMk (αbase.app n)
      naturality := fun _ _ g => P.hom_ext (αbase.naturality g) }
  have hα : Mono α := by
    have (n : ℕ) : Mono (α.app n) := P.ι.mono_of_mono_map <| by
      change Mono (αbase.app n)
      rw [ModuleCat.mono_iff_injective]
      exact quotientStageMap_injective f hf (by norm_num [f]) n
    exact NatTrans.mono_of_mono_app α
  let zeroModule : ModuleCat A := ModuleCat.of A (A ⧸ (⊤ : Submodule A A))
  have hzmod : Subsingleton zeroModule := by infer_instance
  let zeroObj : C := ⟨zeroModule, IsDerivedCompleteModule.of_subsingleton zeroModule⟩
  let cY : Cocone Y :=
    { pt := zeroObj
      ι := { app := fun _ => 0, naturality := fun _ _ _ => by simp } }
  have coneZero (s : Cocone Y) (n : ℕ) : s.ι.app n = 0 := by
    apply ObjectProperty.hom_ext
    refine quotientStage_hom_eq_zero f I hf s.pt.2 (fun n => (s.ι.app n).hom) (fun n => ?_) n
    have hw := congrArg (fun g => g.hom) (s.w (homOfLE (Nat.le_add_right n 1)))
    change Ybase.map (homOfLE (Nat.le_add_right n 1)) ≫ (s.ι.app (n + 1)).hom =
      (s.ι.app n).hom at hw
    rwa [Functor.ofSequence_map_homOfLE_succ] at hw
  have hcY : IsColimit cY :=
    ⟨fun _ => 0, fun s n => by simp [coneZero s n], fun s m _ =>
      P.hom_ext (ModuleCat.hom_ext (LinearMap.ext fun z => by simp [hzmod.elim z 0]))⟩
  have hsource : 𝟙 source = 0 := by
    have : Mono (0 : source ⟶ zeroObj) := colim.map_mono' α (isColimitConstCocone ℕ source) hcY 0
      fun _ => comp_zero.trans comp_zero.symm
    exact (cancel_mono (0 : source ⟶ zeroObj)).1 (by simp)
  exact padicInt_two_mk_one_ne_zero
    (congrArg (fun g : source ⟶ source => g.hom (Submodule.Quotient.mk (1 : A))) hsource)

/-- The inclusion of derived complete modules over the `p`-adic integers does
not preserve countable coproducts. -/
theorem derivedCompleteModules_inclusion_not_preservesCoproducts
    (p : ℕ) [Fact p.Prime] :
    letI : HasProductsOfShape ℕ (DerivedCategory (ModuleCat (PadicInt p))) :=
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    let P : ObjectProperty (ModuleCat (PadicInt p)) := fun M =>
      IsDerivedCompleteModule (Ideal.span {(p : PadicInt p)}) M
    ¬ PreservesColimitsOfShape (Discrete ℕ+) P.ι := by
  dsimp only
  intro hpres
  let A := PadicInt p
  let I : Ideal A := Ideal.span {(p : A)}
  let P : ObjectProperty (ModuleCat A) := fun M => IsDerivedCompleteModule I M
  let C := P.FullSubcategory
  let _ : HasColimitsOfSize C :=
    ((CompletionAdjunction.derivedCompleteModules_abelian_hasLimits_exact_hasColimits A
      I).2.2.2.2 (Submodule.fg_span_singleton (p : A))).1
  let x : C := ⟨ModuleCat.of A A, pAdicInt_summand_isDerivedComplete p⟩
  let D : Discrete ℕ+ ⥤ C := (Functor.const (Discrete ℕ+)).obj x
  let K : Discrete ℕ+ ⥤ ModuleCat A := D ⋙ P.ι
  have : PreservesColimit D P.ι := hpres.preservesColimit
  let e : P.ι.obj (colimit D) ≅ colimit K :=
    (isColimitOfPreserves P.ι (colimit.isColimit D)).coconePointUniqueUpToIso
      (colimit.isColimit K)
  exact (pAdicDirectSum_not_isDerivedComplete p)
    ((colimit D).property.of_iso (e ≪≫
      ModuleCat.coprodIsoDirectSum (fun _ : ℕ+ => ModuleCat.of A A)))

/-- The inclusion of derived complete modules over the `p`-adic integers,
complete with respect to `(p)`, does not preserve arbitrary colimits. -/
theorem derivedCompleteModules_inclusion_not_preservesColimits
    (p : ℕ) [Fact p.Prime] :
    letI : HasProductsOfShape ℕ (DerivedCategory (ModuleCat (PadicInt p))) :=
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    let P : ObjectProperty (ModuleCat (PadicInt p)) := fun M =>
      IsDerivedCompleteModule (Ideal.span {(p : PadicInt p)}) M
    ¬ PreservesColimits P.ι := fun hpres =>
  derivedCompleteModules_inclusion_not_preservesCoproducts p hpres.preservesColimitsOfShape

/-- Derived complete modules over the `2`-adic integers do not form a
Grothendieck abelian category. -/
theorem derivedCompleteModules_not_isGrothendieckAbelian :
    letI : HasProductsOfShape ℕ (DerivedCategory (ModuleCat (ℤ_[2]))) :=
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    let P : ObjectProperty (ModuleCat (ℤ_[2])) := fun M =>
      IsDerivedCompleteModule (Ideal.span {(2 : ℤ_[2])}) M
    let C := P.FullSubcategory
    ∀ [Abelian C], ¬ IsGrothendieckAbelian C := by
  intro P C _ hGrothendieck
  let _ : HasExactColimitsOfShape (ULiftHom (ULift ℕ)) C := hGrothendieck.ab5OfSize.ofShape _
  let _ : HasColimitsOfShape ℕ C :=
    hasColimitsOfShape_of_equivalence (ULiftHomULiftCategory.equiv ℕ).symm
  exact derivedCompleteModules_not_exactColimits_nat
    (HasExactColimitsOfShape.of_domain_equivalence C (ULiftHomULiftCategory.equiv ℕ).symm)

/-- **Stacks 0ARD.** Let `A` be a ring and `I ⊂ A` an ideal. The category `C` of derived complete
`A`-modules is abelian, and the inclusion `F : C ⥤ ModuleCat A` is exact and preserves all limits.
If `I` is finitely generated, then `C` has all direct sums and all colimits.

These are not preserved by `F` in general, and filtered colimits in `C` are not exact in general,
so that `C` is not a Grothendieck abelian category: all of this fails for `A = ℤ_[2]` and
`I = (2)`, where `F` does not preserve countable direct sums or colimits, sequential colimits in
`C` are not exact, `C` does not satisfy AB5, and no abelian structure on `C` is Grothendieck. -/
@[stacks 0ARD]
theorem derivedCompleteModules_abelian_exact_colimits_not_grothendieck :
    (∀ (A : Type u) [CommRing A] (I : Ideal A),
      letI : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A)) :=
        Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
      let P : ObjectProperty (ModuleCat.{u} A) := fun M => IsDerivedCompleteModule I M
      let C := P.FullSubcategory
      let F : C ⥤ ModuleCat.{u} A := P.ι
      Nonempty (Abelian C) ∧ PreservesFiniteLimits F ∧ PreservesFiniteColimits F ∧
        HasLimits C ∧ PreservesLimits F ∧
        (I.FG → HasCoproducts.{u} C ∧ HasColimits C)) ∧
    (letI : HasProductsOfShape ℕ (DerivedCategory (ModuleCat (ℤ_[2]))) :=
        Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
      let I : Ideal ℤ_[2] := Ideal.span {2}
      let P : ObjectProperty (ModuleCat (ℤ_[2])) := fun M => IsDerivedCompleteModule I M
      let C := P.FullSubcategory
      let F : C ⥤ ModuleCat (ℤ_[2]) := P.ι
      I.FG ∧ ¬ PreservesColimitsOfShape (Discrete ℕ) F ∧ ¬ PreservesColimits F ∧
        (∃ _ : HasColimitsOfShape ℕ C, ¬ HasExactColimitsOfShape ℕ C) ∧
        (∃ _ : HasFilteredColimits C, ¬ AB5 C) ∧
        ∀ [Abelian C], ¬ IsGrothendieckAbelian C) := by
  refine ⟨fun A _ I => ?_, ?_⟩
  · obtain ⟨hab, hlim, hpres, ⟨hfl, hfc⟩, hcol⟩ :=
      CompletionAdjunction.derivedCompleteModules_abelian_hasLimits_exact_hasColimits A I
    refine ⟨hab, hfl, hfc, hlim, hpres, fun hI => ?_⟩
    have := (hcol hI).1
    exact ⟨fun _ => inferInstance, this⟩
  · dsimp only
    have hFG : (Ideal.span {(2 : ℤ_[2])}).FG := Submodule.fg_span_singleton _
    have hcol := ((CompletionAdjunction.derivedCompleteModules_abelian_hasLimits_exact_hasColimits
      (ℤ_[2]) (Ideal.span {(2 : ℤ_[2])})).2.2.2.2 hFG).1
    refine ⟨hFG, fun h => ?_, derivedCompleteModules_inclusion_not_preservesColimits 2,
      ⟨inferInstance, derivedCompleteModules_not_exactColimits_nat⟩,
      ⟨inferInstance, fun h => derivedCompleteModules_not_exactColimits_nat (h.ofShape ℕ)⟩,
      derivedCompleteModules_not_isGrothendieckAbelian⟩
    exact derivedCompleteModules_inclusion_not_preservesCoproducts 2
      (preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.pnatEquivNat.symm) _)

end Stacks.Examples

end
