module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.Independence
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.PowerSumComplex

/-!
# The power sums of a complex depend only on its derived object

Let `Y` be locally of finite type over the base of chapter 42. **Stacks 0ESZ** says that the
classes `P_p(ℰ^•) ∈ A^p(Y)` and `ch_p(ℰ^•) ∈ A^p(Y) ⊗ 𝐐` of a locally bounded complex `ℰ^•` of
finite locally free `𝒪_Y`-modules depend only on the object of `D(𝒪_Y)` it represents. The
source proves this for the total Chern class and says the other two cases "follow by the same
arguments using Lemma 0F9C instead of Lemma 02UI". This file carries out that argument.

By Stacks 0F9C (`Stacks.Chow.powerSumOfFiniteLocallyFree_eq_add_of_shortExact`) the power sum
`P_p` is additive on short exact sequences of finite locally free modules, so it factors through
`K_0(Vect(Y))` (`Stacks.Chow.powerSumKHom`), and on a bounded complex `P_p(ℰ^•)` is the image of
the alternating class `∑_n (-1)^n [ℰ^n]`. On an integral locally Noetherian scheme over which
the cohomology modules are perfect of Tor dimension at most one, the alternating classes of two
complexes representing the same object agree
(`Stacks.Chow.alternatingKClass_eq_of_iso_derivedCategory`, from Stacks 0F8J and Schanuel's
lemma). The reduction to that case is the source's: Stacks 02UC
and the admissible blowup of Stacks 0ESR, exactly as in
`Stacks.Chow.complexChern_eq_of_iso`.

## Main definitions

* `Stacks.Chow.powerSumKHom` — `P_p : K_0(Vect(Y)) ⟶ ∏_q A^q(Y)`.

## Main results

* `Stacks.Chow.powerSumComplex_eq_of_iso` — **Stacks 0ESZ for `P_p`**: two locally bounded
  complexes of finite locally free modules, of arbitrary ranks, isomorphic in `D(𝒪_Y)`, have equal
  classes `P_p(ℰ^•) = ∑_n (-1)^n P_p(ℰ^n)`, the power sums of Stacks 0F9B being constructed, not
  carried.
* `Stacks.Chow.chernCharacterComplex_eq_of_iso` — **Stacks 0ESZ for `ch`**, in every degree `p`,
  that is, for the family `ch(ℰ^•) ∈ ∏_{p ≥ 0} A^p(Y) ⊗ 𝐐` read componentwise.

## References

* [Stacks Project, Tag 0ESZ](https://stacks.math.columbia.edu/tag/0ESZ)
* [Stacks Project, Tag 0F9C](https://stacks.math.columbia.edu/tag/0F9C)
* [Stacks Project, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.PerfectComplexes Stacks.Cohomology.TorAmplitude

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Power sums through `K_0(Vect(Y))` -/

section KTheory

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]

open Classical in
/-- `ℰ ↦ P_p(ℰ)` on modules, zero off the finite locally free ones. -/
def powerSumKFun (p : ℕ) (M : Y.Modules) : TotalChowClass C sY :=
  if h : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) M then
    @powerSumOfFiniteLocallyFree C _ sY _ M h p
  else 0

/-- On a finite locally free module `ℰ`, `powerSumKFun` is `P_p(ℰ)`. -/
theorem powerSumKFun_eq (p : ℕ) (M : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M] :
    powerSumKFun C sY p M = powerSumOfFiniteLocallyFree C sY M p := by
  have h : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) M :=
    ⟨(‹AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M›
      ).exists_isFiniteLocallyFreeData⟩
  rw [powerSumKFun, dite_eq_left h]

/-- The homomorphism `P_p : K_0(Vect(Y)) → ∏_q A^q(Y)` sending the class of a finite locally free
module `ℰ` to `P_p(ℰ)`, well defined since `P_p` is additive on short exact sequences. -/
def powerSumKHom (p : ℕ) : AlgebraicGeometry.VectorBundleKZero Y →+ TotalChowClass C sY :=
  AlgebraicGeometry.VectorBundleKZero.liftAddHom (powerSumKFun C sY p)
    (fun M hM => dite_eq_right hM)
    (fun {E F G} f g w hE hF hG hmono hepi hex => by
      rw [powerSumKFun_eq, powerSumKFun_eq, powerSumKFun_eq]
      exact powerSumOfFiniteLocallyFree_eq_add_of_shortExact C sY (ShortComplex.mk f g w)
        { exact := hex } p)

/-- `powerSumKHom` sends the class `[ℰ]` of a finite locally free module `ℰ` to `P_p(ℰ)`. -/
theorem powerSumKHom_classOf (p : ℕ) (M : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M] :
    powerSumKHom C sY p (AlgebraicGeometry.VectorBundleKZero.classOf Y M) =
      powerSumOfFiniteLocallyFree C sY M p :=
  (AlgebraicGeometry.VectorBundleKZero.liftAddHom_classOf _ _ _ M).trans
    (powerSumKFun_eq C sY p M)

/-- **On a bounded complex of constant ranks `P_p(ℰ^•)` is the image of the alternating class**
`∑_n (-1)^n [ℰ^n]`, over any window `a, …, a + k` outside of which the ranks vanish. -/
theorem powerSumComplexBounded_eq_powerSumKHom (P : CochainComplex Y.Modules ℤ) (ρ : ℤ →₀ ℕ)
    (hP : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) (ρ n))
    (p : ℕ) (a : ℤ) (k : ℕ) (hρ : ∀ n, (n < a ∨ a + (k : ℤ) < n) → ρ n = 0) :
    powerSumComplexBounded C sY P ρ hP p = powerSumKHom C sY p (alternatingKClass Y P a k) := by
  rw [powerSumComplexBounded_eq_sum C sY P ρ hP p (Finset.Icc a (a + (k : ℤ))) fun n hn =>
      hρ n (by rw [Finset.mem_Icc] at hn; omega),
    alternatingKClass_eq_sum_Icc, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  let := hP n
  have := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    (P.X n) (ρ n)
  rw [map_zsmul, powerSumKHom_classOf, powerSumOfFiniteLocallyFree_eq_powerSumTotal C sY _ (ρ n)]

end KTheory

/-! ### Stacks 0ESZ for the power sums -/

section Independence

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  {P P' : CochainComplex Y.Modules ℤ} (hP : IsLocallyBoundedFiniteLocallyFree P)
  (hP' : IsLocallyBoundedFiniteLocallyFree P')

/-- **On an integral scheme whose cohomology is perfect of Tor dimension at most one**, two
bounded complexes of finite locally free modules of constant ranks representing the same object
have the same power sums. -/
theorem powerSumComplexBounded_eq_of_iso {W : Scheme.{u}} (sW : W ⟶ C.S)
    [LocallyOfFiniteType sW] [IsIntegral W] [IsLocallyNoetherian W]
    (Q Q' : CochainComplex W.Modules ℤ) (ρ σ : ℤ →₀ ℕ)
    (hQ : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (Q.X n) (ρ n))
    (hQ' : ∀ n,
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (Q'.X n) (σ n))
    (e : DerivedCategory.Q.obj Q ≅ DerivedCategory.Q.obj Q')
    (hE : ∀ i : ℤ,
      IsPerfect.{u, u, u + 1} ((DerivedCategory.singleFunctor W.Modules 0).obj
        ((DerivedCategory.homologyFunctor W.Modules i).obj (DerivedCategory.Q.obj Q))) ∧
      HasTorAmplitude W.toRingedSpace ((DerivedCategory.singleFunctor W.Modules 0).obj
        ((DerivedCategory.homologyFunctor W.Modules i).obj (DerivedCategory.Q.obj Q))) (-1) 0)
    (p : ℕ) :
    powerSumComplexBounded C sW Q ρ hQ p = powerSumComplexBounded C sW Q' σ hQ' p := by
  obtain ⟨a, k, hρ, hσ⟩ := exists_window_of_finsupp ρ σ
  rw [powerSumComplexBounded_eq_powerSumKHom C sW Q ρ hQ p a k hρ,
    powerSumComplexBounded_eq_powerSumKHom C sW Q' σ hQ' p a k hσ,
    alternatingKClass_eq_of_iso_derivedCategory Q Q' a k
      (fun n ↦ have := hQ n
        GenuineChern.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank (Q.X n) (ρ n))
      (fun n ↦ have := hQ' n
        GenuineChern.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank (Q'.X n) (σ n))
      (fun n hn ↦ @Stacks.Chow.isZero_of_isFiniteLocallyFreeOfRank_zero _ _ ((hρ n hn) ▸ hQ n))
      (fun n hn ↦ @Stacks.Chow.isZero_of_isFiniteLocallyFreeOfRank_zero _ _ ((hσ n hn) ▸ hQ' n))
      (DerivedCategory.Q.obj Q) ⟨Iso.refl _⟩ ⟨e⟩ hE]

/-- Stacks 0ESZ for `P_p` along a morphism from an integral scheme over which the cohomology is
perfect of Tor dimension at most one: the two classes operate in the same way there. -/
theorem op_powerSumComplex_eq_of_iso_of_isIntegral {W : Scheme.{u}} [IsIntegral W] (f : W ⟶ Y)
    [LocallyOfFiniteType f] (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj P')
    (hE : ∀ i : ℤ,
      IsPerfect.{u, u, u + 1} ((DerivedCategory.singleFunctor W.Modules 0).obj
        ((DerivedCategory.homologyFunctor W.Modules i).obj
          (DerivedCategory.Q.obj (pullbackComplex f P)))) ∧
      HasTorAmplitude W.toRingedSpace ((DerivedCategory.singleFunctor W.Modules 0).obj
        ((DerivedCategory.homologyFunctor W.Modules i).obj
          (DerivedCategory.Q.obj (pullbackComplex f P)))) (-1) 0) (p : ℕ) :
    (powerSumComplex C sY hP p).op f = (powerSumComplex C sY hP' p).op f := by
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sY)
  obtain ⟨x⟩ : Nonempty W := inferInstance
  have key := fun {R : CochainComplex Y.Modules ℤ} (hR : IsLocallyBoundedFiniteLocallyFree R) ↦
    res_powerSumComplex_eq_powerSumComplexBounded C sY hR f rfl _
      (isFiniteLocallyFreeOfRank_complexRank
        (Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback f R hR) x) p
  have h := (key hP).trans
    ((powerSumComplexBounded_eq_of_iso C (f ≫ sY) _ _ _ _ _ _
      (pullbackComplexQIso hP hP' f e) hE p).trans (key hP').symm)
  have h' := congrArg (fun c : TotalChowClass C (f ≫ sY) => c.op (𝟙 W)) h
  exact eq_of_heq ((((TotalChowClass.op_heq_congr _ (Category.id_comp f)).symm.trans
    (TotalChowClass.op_res f rfl _ (𝟙 W)).symm).trans (heq_of_eq h')).trans
    ((TotalChowClass.op_res f rfl _ (𝟙 W)).trans
      (TotalChowClass.op_heq_congr _ (Category.id_comp f))))

/-- The proper birational modification of the proof of Stacks 0ESZ, for `P_p`. -/
theorem exists_isBirational_op_powerSumComplex_eq_of_iso {T : Scheme.{u}} [IsIntegral T]
    (g : T ⟶ Y) [LocallyOfFiniteType g] (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj P')
    (p : ℕ) :
    ∃ (T' : Scheme.{u}) (π : T' ⟶ T) (_ : IsProper π), AlgebraicGeometry.IsBirational π ∧
      (powerSumComplex C sY hP p).op (π ≫ g) = (powerSumComplex C sY hP' p).op (π ≫ g) := by
  have hPg := Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback g P hP
  have hperf : IsPerfect.{u, u, u + 1} (X := T.toRingedSpace)
      (DerivedCategory.Q.obj (pullbackComplex g P)) :=
    ⟨pullbackComplex g P,
      Stacks.BlowUpComplexes.isPerfectComplex_of_isLocallyBoundedFiniteLocallyFree _ hPg,
      ⟨Iso.refl _⟩⟩
  obtain ⟨U, -, hU, -, T', b, hb, hE⟩ :=
    exists_nonempty_open_admissibleBlowup_forall_isHomologyPerfectTorLEOne T
      (DerivedCategory.Q.obj (pullbackComplex g P)) hperf
  have := hb.isProper
  have := hb.isIntegral hU
  refine ⟨T', b, inferInstance, hb.isBirational hU,
    op_powerSumComplex_eq_of_iso_of_isIntegral C sY hP hP' (b ≫ g) e (fun i ↦ ?_) p⟩
  let ε : DerivedCategory.Q.obj (pullbackComplex (b ≫ g) P) ≅
      (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback b.toLRSHom.toShHom).obj
        (DerivedCategory.Q.obj (pullbackComplex g P)) :=
    (DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso (Scheme.Modules.pullbackComp b g)
        (ComplexShape.up ℤ)).app P)).symm ≪≫
      (Cohomology.derivedPullbackIsoPullbackOfKFlat b.toLRSHom.toShHom (pullbackComplex g P)
        (Stacks.BlowUpComplexes.kFlatComplex_of_isLocallyBoundedFiniteLocallyFree _ hPg)).symm
  exact AlgebraicGeometry.IsPerfectTorLEOne.of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso ε.symm) (hE i)

/-- Let `P`, `P'` be locally bounded complexes of finite locally free `𝒪_Y`-modules representing
the same object of `D(𝒪_Y)`. Then `P_p(P) = P_p(P') ∈ A^p(Y)` for every `p`. -/
@[stacks 0ESZ "the classes P_p(E^bullet) of a locally bounded complex of finite locally free \
modules, ranks varying, depend only on its object of D(O_Y)"]
theorem powerSumComplex_eq_of_iso (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj P')
    (p : ℕ) : powerSumComplex C sY hP p = powerSumComplex C sY hP' p :=
  TotalChowClass.eq_of_op_fundamentalChowClass_eq fun g _ _ ↦ by
    obtain ⟨T', π, hπ, hbir, h⟩ :=
      exists_isBirational_op_powerSumComplex_eq_of_iso C sY hP hP' g e p
    exact ⟨T', π, hπ, hbir, fun k q ↦ by rw [h]⟩

/-- `ch_p(P) = ch_p(P') ∈ A^p(Y) ⊗ 𝐐` for locally bounded complexes `P`, `P'` of finite locally
free modules representing the same object of `D(𝒪_Y)`. -/
@[stacks 0ESZ "the Chern character ch(E^bullet) = sum_p P_p(E^bullet)/p! of a locally bounded \
complex of finite locally free modules, ranks varying, depends only on its object of D(O_Y)"]
theorem chernCharacterComplex_eq_of_iso (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj P')
    (p : ℕ) : chernCharacterComplex C sY hP p = chernCharacterComplex C sY hP' p := by
  rw [chernCharacterComplex, chernCharacterComplex, powerSumComplexClass, powerSumComplexClass,
    powerSumComplex_eq_of_iso C sY hP hP' e p]

end Independence

end Stacks.Chow

end
