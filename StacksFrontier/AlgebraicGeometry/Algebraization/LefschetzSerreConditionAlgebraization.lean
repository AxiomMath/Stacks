module

public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzCompletedStalkDepthCriterion
public import StacksFrontier.AlgebraicGeometry.Algebraization.CompletedStalkFreeOfFiniteLocallyFreeAdic
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorInvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzFormalModuleAlgebraization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Algebraization of formal modules on proper `(S₃)` varieties

Let `k` be a field, `X` a proper variety over `k` and `Y ⊂ X` an effective Cartier divisor with
`𝒪_X(Y)` ample, with sheaf of ideals `𝓘`. Let `(𝓔ₙ)` be an object of `Coh(X, 𝓘)` whose terms are
finite locally free over the infinitesimal neighbourhoods `Yₙ`. Stacks 0EL6 lists the special
cases of the algebraization criterion of Stacks 0EL5 for `(𝓔ₙ)`:

1. if `X` is a curve or a surface, the criterion says nothing;
2. if `X` is a Cohen–Macaulay threefold, `(𝓔ₙ)` is the completion of a coherent `𝒪_X`-module `𝓔`;
3. if `dim(X) ≥ 3` and `X` is `(S₃)`, `(𝓔ₙ)` is the completion of a coherent `𝒪_X`-module `𝓔`;

and such an `𝓔` is finite locally free on an open neighbourhood of `Y`.

## Main results

* `Stacks.Algebraization.not_two_lt_completedStalkDepth_of_dim_le_two`: Stacks 0EL6, clause (1):
  on a curve or a surface the inequality of Stacks 0EL5 fails at every point of `Y` with nonzero
  completed stalk and every prime of the completed local ring.
* `Stacks.Algebraization.exists_completion_iso_of_isCohenMacaulay_of_dim_eq_three`: Stacks 0EL6,
  clause (2): on a Cohen–Macaulay threefold `(𝓔ₙ)` is the completion of a coherent module, finite
  locally free on an open neighbourhood of `Y`.
* `Stacks.Algebraization.exists_completion_iso_of_hasPropertySk_three`: Stacks 0EL6, clause (3):
  if `dim(X) ≥ 3` and `X` is `(S₃)`, `(𝓔ₙ)` is the completion of a coherent module, finite locally
  free on an open neighbourhood of `Y`.
* `Stacks.Algebraization.two_lt_completedStalkDepth_of_hasPropertySk_three`: the inequality of
  Stacks 0EL5 holds at every point of `Y` when `dim(X) ≥ 3` and `X` is `(S₃)`.
* `Stacks.Algebraization.depth_le_depth_self_of_free`: a nonzero finite free module over a
  Noetherian local ring has depth at most that of the ring.

## References

* [Stacks Project, Tag 0EL6](https://stacks.math.columbia.edu/tag/0EL6)
* [Stacks Project, Tag 0EL5](https://stacks.math.columbia.edu/tag/0EL5), the criterion.
* [Stacks Project, Tag 0EHW](https://stacks.math.columbia.edu/tag/0EHW), depth under completion.
* [Stacks Project, Tag 033Q](https://stacks.math.columbia.edu/tag/033Q), Serre's conditions.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace Stacks.Algebraization

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- **The criterion of Stacks 0EL5 on a proper `(S₃)` variety of dimension at least three.** Let
`X` be a proper variety over a field, `Y ⊆ X` a closed subscheme and `(𝓔ₙ)` an object of
`Coh(X, 𝓘_Y)` whose terms are finite locally free over the infinitesimal neighbourhoods. If
`dim(X) ≥ 3` and `X` is `(S₃)`, then at every `q ∈ Y` and every prime `𝔭` of `𝒪_{X,q}^∧` off
`V(𝓘𝒪_{X,q}^∧)`,

`depth((𝓔_q^∧)_𝔭) + dim(𝒪_{X,q}^∧/𝔭) + dim({q}‾) > 2`,

in the extended integers in which Stacks 0EL5 is stated. -/
theorem two_lt_completedStalkDepth_of_hasPropertySk_three (f : X ⟶ Spec (.of k))
    [IsProperVariety k f] [IsLocallyNoetherian X] (Y : X.IdealSheafData)
    (E : Stacks.Coherent.CoherentAdicSystems Y) (hfree : IsFiniteLocallyFreeAdic Y E)
    (hdim : ((3 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim X) (hS₃ : HasPropertySk X 3)
    {q : X} (hq : q ∈ Y.support) (p : PrimeSpectrum (completedLocalRing Y q))
    (hp : ¬ completedLocalIdeal Y q ≤ p.asIdeal) :
    (2 : EInt) < enatToEInt (completedStalkDepth Y E q p) +
      krullDimToEInt (ringKrullDim (completedLocalRing Y q ⧸ p.asIdeal)) +
      krullDimToEInt (dimClosureAt X q) := by
  have hform : ∀ x : X,
      ringKrullDim (X.presheaf.stalk x) + dimClosureAt X x = topologicalKrullDim X :=
    ringKrullDim_stalk_add_dimClosureAt k X f
  refine two_lt_enatToEInt_add_krullDimToEInt_add ?_
  exact two_lt_completedStalkDepth_add_of_two_lt_localDepthAddDimClosure k f Y E
    (fun x _ => two_lt_depth_add_dimClosure_of_hasPropertySk_three X hS₃ hdim hform x) hq
    (free_completedStalk_of_isFiniteLocallyFreeAdic Y E hfree hq) p hp

/-! ### Curves and surfaces -/

/-- A nonzero finite free module over a Noetherian local ring has depth at most that of the
ring. -/
@[sga "2 X 2.1" "partial"]
theorem depth_le_depth_self_of_free {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (F : Type*) [AddCommGroup F] [Module R F] [Module.Free R F]
    [Module.Finite R F] [Nontrivial F] :
    Module.depth R (IsLocalRing.maximalIdeal R) F ≤
      Module.depth R (IsLocalRing.maximalIdeal R) R := by
  classical
  set m := IsLocalRing.maximalIdeal R
  have hfin : Module.depth R m R ≠ ⊤ := by
    intro h
    have hle := Module.depth_le_ringKrullDim R
    rw [h] at hle
    exact ringKrullDim_ne_top (top_le_iff.mp hle)
  have hpi : ∀ n : ℕ, Module.depth R m (Fin (n + 1) → R) = Module.depth R m R := by
    intro n
    induction n with
    | zero => exact Module.depth_eq_depth_of_linearEquiv _ (LinearEquiv.funUnique (Fin 1) R R)
    | succ n ih =>
      have e : (Fin (n + 1 + 1) → R) ≃ₗ[R] R × (Fin (n + 1) → R) :=
        { toFun := fun g => (g 0, fun i => g i.succ)
          invFun := fun v => Fin.cons v.1 v.2
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl
          left_inv := fun g => Fin.cons_self_tail g
          right_inv := fun v => by ext <;> simp }
      rw [Module.depth_eq_depth_of_linearEquiv _ e]
      have hex := Module.min_depth_le_depth_of_exact (R := R) m
        (N' := R) (N := R × (Fin (n + 1) → R)) (N'' := (Fin (n + 1) → R))
        Function.Exact.inl_snd LinearMap.inl_injective LinearMap.snd_surjective
      refine le_antisymm ?_ ?_
      · rcases min_le_iff.mp hex.2.2 with h' | h'
        · exact h'
        · rw [ih] at h'
          exact absurd ((ENat.add_one_le_iff hfin).mp h') (lt_irrefl _)
      · simpa only [ih, min_self] using hex.1
  obtain ⟨n, ⟨b⟩⟩ : ∃ n : ℕ, Nonempty (Module.Basis (Fin n) R F) :=
    ⟨_, ⟨(Module.Free.chooseBasis R F).reindex (Fintype.equivFin _)⟩⟩
  cases n with
  | zero => exact absurd b.equivFun.toEquiv.subsingleton (not_subsingleton F)
  | succ n => rw [Module.depth_eq_depth_of_linearEquiv _ b.equivFun, hpi n]

/-- Let `X` be a proper variety over a field with an effective Cartier divisor `Y` whose sheaf
`𝒪_X(Y)` is ample, and let `(𝓔ₙ)` be an object of `Coh(X, 𝓘)` whose terms are finite locally free
over the infinitesimal neighbourhoods. If `X` is a curve or a surface, the hypothesis

`depth((𝓔_q^∧)_𝔭) + dim(𝒪_{X,q}^∧/𝔭) + dim({q}‾) > 2`

of Stacks 0EL5 fails at every point `q` of `Y` where the completed stalk is nonzero and every
prime `𝔭` of `𝒪_{X,q}^∧`. -/
@[stacks 0EL6 "clause (1): for a curve or a surface the inequality of 0EL5 fails at every point \
 of Y with nonzero completed stalk and every prime off the completed ideal"]
theorem not_two_lt_completedStalkDepth_of_dim_le_two (f : X ⟶ Spec (.of k))
    [IsProperVariety k f] (Y : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor Y]
    (_hample : AlgebraicGeometry.Scheme.Modules.IsAmple X (Stacks.Divisors.divisorSheaf Y))
    (E : Stacks.Coherent.CoherentAdicSystems Y) (hfree : IsFiniteLocallyFreeAdic Y E)
    (hdim : topologicalKrullDim X ≤ ((2 : ℕ) : WithBot ℕ∞))
    {q : X} (hq : q ∈ Y.support) [Nontrivial (completedStalk Y E q)]
    (p : PrimeSpectrum (completedLocalRing Y q)) :
    ¬ (2 : EInt) < enatToEInt (completedStalkDepth Y E q p) +
      krullDimToEInt (ringKrullDim (completedLocalRing Y q ⧸ p.asIdeal)) +
      krullDimToEInt (dimClosureAt X q) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : Module.Free (completedLocalRing Y q) (completedStalk Y E q) :=
    free_completedStalk_of_isFiniteLocallyFreeAdic Y E hfree hq
  have : Module.Finite (completedLocalRing Y q) (completedStalk Y E q) :=
    finite_completedStalk Y E q
  have : Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl (completedStalk Y E q)) :=
    Module.free_of_isLocalizedModule p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (completedStalk Y E q))
  have : Nontrivial (LocalizedModule p.asIdeal.primeCompl (completedStalk Y E q)) := by
    let b := Module.Free.chooseBasis (completedLocalRing Y q) (completedStalk Y E q)
    obtain ⟨i⟩ := b.index_nonempty
    exact nontrivial_of_ne _ _ (((IsLocalizedModule.isBaseChange p.asIdeal.primeCompl
      (Localization.AtPrime p.asIdeal)
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (completedStalk Y E q))).basis b).ne_zero i)
  set x := X.fromSpecStalk q
    (PrimeSpectrum.comap (algebraMap (X.presheaf.stalk q) (completedLocalRing Y q)) p)
  have hid := depth_add_ringKrullDim_add_dimClosureAt_completedLocalRing k f Y hq p
  have hdepthE : (completedStalkDepth Y E q p : WithBot ℕ∞) ≤
      (Module.depth (Localization.AtPrime p.asIdeal)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl (completedLocalRing Y q)) : WithBot ℕ∞) := by
    rw [completedStalkDepth,
      Module.depth_eq_depth_of_linearEquiv _ (localizedRingEquiv p.asIdeal)]
    exact WithBot.coe_le_coe.mpr (depth_le_depth_self_of_free _)
  have hbound : (completedStalkDepth Y E q p : WithBot ℕ∞) +
      ringKrullDim (completedLocalRing Y q ⧸ p.asIdeal) + dimClosureAt X q ≤
        ((2 : ℕ) : WithBot ℕ∞) := by
    calc _ ≤ _ := add_le_add_left (add_le_add_left hdepthE _) _
      _ = _ := hid
      _ ≤ ringKrullDim (X.presheaf.stalk x) + dimClosureAt X x :=
          add_le_add_left (Module.depth_le_ringKrullDim _) _
      _ = topologicalKrullDim X := ringKrullDim_stalk_add_dimClosureAt k X f x
      _ ≤ _ := hdim
  intro hlt
  have hm := krullDimToEInt_mono hbound
  rw [krullDimToEInt_add, krullDimToEInt_add, krullDimToEInt_coe] at hm
  exact absurd (hlt.trans_le hm) (lt_irrefl _)

/-! ### Threefolds and `(S₃)` varieties -/

/-- Let `X` be a proper variety over a field `k`, `Y ⊂ X` an effective Cartier divisor such that
`𝒪_X(Y)` is ample, with ideal sheaf `𝓘`, and `(𝓔ₙ)` an object of `Coh(X, 𝓘)` whose terms are
finite locally free over the infinitesimal neighbourhoods. If `dim(X) ≥ 3` and `X` is `(S₃)`, then
`(𝓔ₙ)` is the completion of a coherent `𝒪_X`-module `𝓔`, and `𝓔` is finite locally free on an
open neighbourhood of `Y`. -/
@[stacks 0EL6 "clause (3) with the closing remark: dim X >= 3 and X is (S_3); the freeness of \
 E_n is read over the infinitesimal neighbourhoods Y_n",
  sga "2 X 2.2" "(ii)",
  sga "2 XII 3.1" "special case",
  sga "2 XII 3.4" "Clause b), special case"]
theorem exists_completion_iso_of_hasPropertySk_three (f : X ⟶ Spec (.of k))
    [IsProperVariety k f] (Y : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor Y]
    (hample : AlgebraicGeometry.Scheme.Modules.IsAmple X (Stacks.Divisors.divisorSheaf Y))
    (E : Stacks.Coherent.CoherentAdicSystems Y) (hfree : IsFiniteLocallyFreeAdic Y E)
    (hdim : ((3 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim X) :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    HasPropertySk X 3 →
      ∃ G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf,
        Nonempty (((completionFunctor X Y).obj G).obj ≅ E.obj) ∧
          ∃ V : X.Opens, (Y.support : Set X) ⊆ (V : Set X) ∧
            AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree
              (Scheme.Modules.restrict (show X.Modules from G.obj) V.ι) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  intro hS₃
  have hL : Stacks.Ample.IsAmple X (Stacks.Divisors.divisorSheaf Y) :=
    (Stacks.AmpleBridge.isAmple_iff_isAmple X _).mpr hample
  have key : ∀ (I : X.IdealSheafData)
      (_ : zeroScheme X (Stacks.Divisors.divisorSheaf Y)
        (Stacks.Divisors.divisorSheafGlobalSection Y) = I)
      (F : Stacks.Coherent.CoherentAdicSystems I),
      (∀ q ∈ I.support, ∀ p : PrimeSpectrum (completedLocalRing I q),
        ¬ completedLocalIdeal I q ≤ p.asIdeal →
        (2 : EInt) < enatToEInt (completedStalkDepth I F q p) +
          krullDimToEInt (ringKrullDim (completedLocalRing I q ⧸ p.asIdeal)) +
          krullDimToEInt (dimClosureAt X q)) →
      IsCompletionOfCoherent I F := by
    rintro I rfl F hF
    exact isCompletionOfCoherent_of_two_lt_depth_add_dim k f (Stacks.Divisors.divisorSheaf Y) hL
      (Stacks.Divisors.divisorSheafGlobalSection Y) F hF
  obtain ⟨G, ⟨e⟩⟩ := key Y (Stacks.Divisors.zeroScheme_canonicalSection Y) E fun q hq p hp =>
    two_lt_completedStalkDepth_of_hasPropertySk_three f Y E hfree hdim hS₃ hq p hp
  exact ⟨G, ⟨e⟩, exists_isFiniteLocallyFree_restrict_of_completion_iso Y E hfree G e⟩

/-- In the situation of `exists_completion_iso_of_hasPropertySk_three`, if `X` is a Cohen–Macaulay
threefold then `(𝓔ₙ)` is the completion of a coherent `𝒪_X`-module `𝓔`, finite locally free on an
open neighbourhood of `Y`. -/
@[stacks 0EL6 "clause (2) with the closing remark: X a Cohen-Macaulay threefold; the freeness \
 of E_n is read over the infinitesimal neighbourhoods Y_n"]
theorem exists_completion_iso_of_isCohenMacaulay_of_dim_eq_three (f : X ⟶ Spec (.of k))
    [IsProperVariety k f] (Y : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor Y]
    (hample : AlgebraicGeometry.Scheme.Modules.IsAmple X (Stacks.Divisors.divisorSheaf Y))
    (E : Stacks.Coherent.CoherentAdicSystems Y) (hfree : IsFiniteLocallyFreeAdic Y E)
    (hCM : AlgebraicGeometry.IsCohenMacaulay X)
    (hdim : topologicalKrullDim X = ((3 : ℕ) : WithBot ℕ∞)) :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    ∃ G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf,
      Nonempty (((completionFunctor X Y).obj G).obj ≅ E.obj) ∧
        ∃ V : X.Opens, (Y.support : Set X) ⊆ (V : Set X) ∧
          AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree
            (Scheme.Modules.restrict (show X.Modules from G.obj) V.ι) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact exists_completion_iso_of_hasPropertySk_three f Y hample E hfree hdim.ge
    ((AlgebraicGeometry.isCohenMacaulay_iff_forall_hasPropertySk X).mp hCM 3)

end Stacks.Algebraization

end
