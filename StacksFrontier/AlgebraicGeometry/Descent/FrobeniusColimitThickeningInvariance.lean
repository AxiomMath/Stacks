module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitFrobeniusFactorization
public import StacksFrontier.AlgebraicGeometry.Divisors.Norm.Reduction
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.FittingIdeals
public import StacksFrontier.AlgebraicGeometry.LiftInvertible.NilpotentUnits
public import StacksFrontier.AlgebraicGeometry.Scheme.Reduction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `colim_F Vect` does not see thickenings of finite type

Let `p` be a prime and `T'` a quasi-compact scheme in characteristic `p`. A quasi-coherent ideal
sheaf `I` of finite type on `T'` all of whose sections are nilpotent is killed by a power of the
absolute Frobenius of `T'`: on each of finitely many affine opens covering `T'` it is a finitely
generated ideal of nilpotents, hence nilpotent, so `I ^ N = 0` for some `N`, and then every
section `x` of `I` has `x ^ (p ^ N) = 0`.

Consequently, for a thickening `i : T ⟶ T'` (a surjective closed immersion) whose ideal sheaf is
of finite type, with `T'` quasi-compact and quasi-separated, pullback along `i` is an equivalence
`colim_F Vect(T') ≌ colim_F Vect(T)`. This is the remark in the proof of Stacks Tag 0EXH that
"if `T ⊂ T'` is a thickening ... then `colim_F Vect(T) = colim_F Vect(T')`":

* full faithfulness is part (1) of 0EXH,
  `AlgebraicGeometry.frobeniusColimitVectModelPullback_full_faithful`, since a thickening is
  proper, surjective, and universally injective, hence has geometrically connected fibres
  (`AlgebraicGeometry.geometricallyConnected_of_surjective_of_universallyInjective`);
* essential surjectivity holds because `F_{T'}^n` factors through `i` as soon as the ideal of `i`
  is killed by `F_{T'}^n`, and then `F_T^n` factors as `i ≫ g`
  (`AlgebraicGeometry.frobeniusColimitVectModelPullback_essSurj_of_comp_eq_frobPow`).

The case of the reduction `T'_red ⟶ T'` of a Noetherian scheme is recorded separately.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.exists_pow_eq_bot_of_isFiniteType_of_le_nilradical`.
* `AlgebraicGeometry.exists_le_ker_frobPow_of_isFiniteType_of_le_nilradical`: a finite type ideal
  sheaf of nilpotents on a quasi-compact scheme is killed by a power of the Frobenius.
* `AlgebraicGeometry.exists_nilradical_le_ker_frobPow`: the case of the nilradical of a Noetherian
  scheme.
* `AlgebraicGeometry.frobeniusColimitVectModelPullback_isEquivalence_of_isThickening`.
* `AlgebraicGeometry.frobeniusColimitVectModelPullback_isEquivalence_subschemeι`.
* `AlgebraicGeometry.frobeniusColimitVectModelPullback_isEquivalence_reductionι`.

## Implementation notes

The iterated Frobenius `frobPow p hT (𝟙 T) n` of the Frobenius colimit files is a composite of
`n` absolute Frobenii, so its inverse images of opens are only propositionally the opens
themselves. It is identified (`AlgebraicGeometry.frobPow_id_eq_frobeniusPow`) with
`Stacks.Divisors.frobeniusPow`, whose underlying map is literally the identity, and the kernel is
computed on the latter.

## References

* [Stacks Project, Tag 0EXH](https://stacks.math.columbia.edu/tag/0EXH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Frobenius

universe u

namespace AlgebraicGeometry

/-! ### Surjective universally injective morphisms -/

/-- **A surjective universally injective morphism has geometrically connected fibres**: every
base change to the spectrum of a field is a bijection onto a point, so it is a point. -/
theorem geometricallyConnected_of_surjective_of_universallyInjective {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Surjective f] [UniversallyInjective f] : GeometricallyConnected f := by
  refine ⟨fun K _ y Z fst snd h ↦ ?_⟩
  have : Surjective snd := MorphismProperty.of_isPullback (P := @Surjective) h ‹_›
  have : UniversallyInjective snd :=
    MorphismProperty.of_isPullback (P := @UniversallyInjective) h ‹_›
  have : Subsingleton Z := ⟨fun a b ↦ snd.injective (Subsingleton.elim _ _)⟩
  obtain ⟨z, -⟩ := snd.surjective (default : Spec (.of K))
  exact { isPreconnected_univ := Set.subsingleton_of_subsingleton.isPreconnected
          toNonempty := ⟨z⟩ }

/-! ### The iterated Frobenius -/

section Frobenius

variable {T : Scheme.{u}} (p : ℕ) [Fact p.Prime] (hT : IsInCharacteristic T p)

/-- The zeroth Frobenius power is the identity. -/
lemma frobeniusPow_zero_eq_id : Stacks.Divisors.frobeniusPow T p hT 0 = 𝟙 T := by
  refine Scheme.Hom.ext rfl fun U ↦ ?_
  ext s
  change T.presheaf.map (𝟙 (Opposite.op U)) ((Stacks.Divisors.frobeniusPow T p hT 0).app U s) = s
  rw [T.presheaf.map_id]
  change (Stacks.Divisors.frobeniusPow T p hT 0).app U s = s
  rw [Stacks.Divisors.frobeniusPow_app_apply, pow_zero, pow_one]

/-- `F ≫ F^e = F^{e+1}`. -/
lemma absoluteFrobenius_comp_frobeniusPow (h : IsInCharacteristic T p) (e : ℕ) :
    absoluteFrobenius T p h ≫ Stacks.Divisors.frobeniusPow T p hT e =
      Stacks.Divisors.frobeniusPow T p hT (e + 1) := by
  refine Scheme.Hom.ext rfl fun U ↦ ?_
  ext s
  change T.presheaf.map (𝟙 (Opposite.op U)) ((absoluteFrobenius T p h).app U
      ((Stacks.Divisors.frobeniusPow T p hT e).app U s)) =
    (Stacks.Divisors.frobeniusPow T p hT (e + 1)).app U s
  rw [T.presheaf.map_id]
  change (absoluteFrobenius T p h).app U ((Stacks.Divisors.frobeniusPow T p hT e).app U s) =
    (Stacks.Divisors.frobeniusPow T p hT (e + 1)).app U s
  exact (congrArg (fun t ↦ (absoluteFrobenius T p h).app U t)
    (Stacks.Divisors.frobeniusPow_app_apply T p hT e U s)).trans
      ((absoluteFrobenius_app_apply T p h U _).trans ((pow_mul s _ _).symm.trans
        ((congrArg (s ^ ·) (pow_succ p e).symm).trans
          (Stacks.Divisors.frobeniusPow_app_apply T p hT (e + 1) U s).symm)))

/-- The iterated absolute Frobenius `frobPow p hT (𝟙 T) n` of the Frobenius colimit is the
`n`-fold absolute Frobenius `Stacks.Divisors.frobeniusPow T p hT n`. -/
theorem frobPow_id_eq_frobeniusPow :
    ∀ n, frobPow p hT (𝟙 T) n = Stacks.Divisors.frobeniusPow T p hT n
  | 0 => (frobeniusPow_zero_eq_id p hT).symm
  | n + 1 => by
    change frobOf p hT (frobPow p hT (𝟙 T) n) ≫ frobPow p hT (𝟙 T) n = _
    rw [frobPow_id_eq_frobeniusPow n]
    exact absoluteFrobenius_comp_frobeniusPow p hT _ n

end Frobenius

/-! ### Finite type ideal sheaves of nilpotents -/

/-- **On a quasi-compact scheme, a finite type ideal sheaf of nilpotents is nilpotent.** On each
of finitely many affine opens covering the scheme it is a finitely generated ideal contained in
the nilradical, hence nilpotent (`Ideal.FG.isNilpotent_iff_le_nilradical`); the largest of the
finitely many exponents works everywhere. -/
@[ega "I 6.1.6" "more general"]
theorem Scheme.IdealSheafData.exists_pow_eq_bot_of_isFiniteType_of_le_nilradical
    {T : Scheme.{u}} [CompactSpace T] (I : T.IdealSheafData) (hfin : I.IsFiniteType)
    (hnil : I ≤ T.nilradical) : ∃ N : ℕ, I ^ N = ⊥ := by
  classical
  let 𝒰 := T.affineCover.finiteSubcover
  let V (i : 𝒰.I₀) : T.affineOpens := ⟨(𝒰.f i).opensRange, isAffineOpen_opensRange (𝒰.f i)⟩
  have hV : (⨆ i, (V i).1 : T.Opens) = ⊤ := by rw [← 𝒰.iSup_opensRange]
  have : Fintype 𝒰.I₀ := Fintype.ofFinite _
  have hnp (i : 𝒰.I₀) : IsNilpotent (I.ideal (V i)) :=
    (hfin (V i)).isNilpotent_iff_le_nilradical.mpr (Scheme.IdealSheafData.le_def.mp hnil (V i))
  choose n hn using hnp
  refine ⟨Finset.univ.sup n, Scheme.IdealSheafData.ext_of_iSup_eq_top V hV fun i ↦ ?_⟩
  change (I.ideal (V i)) ^ (Finset.univ.sup n) = ⊥
  refine le_antisymm ?_ bot_le
  calc (I.ideal (V i)) ^ (Finset.univ.sup n) ≤ (I.ideal (V i)) ^ n i :=
        Ideal.pow_le_pow_right (Finset.le_sup (Finset.mem_univ i))
    _ = ⊥ := (hn i).trans Ideal.zero_eq_bot

/-- **A finite type ideal sheaf of nilpotents on a quasi-compact scheme in characteristic `p` is
killed by a power of the absolute Frobenius.** If `I ^ N = 0` then every section `x` of `I` has
`x ^ (p ^ N) = 0`, as `N ≤ p ^ N`. -/
theorem exists_le_ker_frobPow_of_isFiniteType_of_le_nilradical {T : Scheme.{u}} (p : ℕ)
    [Fact p.Prime] (hT : IsInCharacteristic T p) [CompactSpace T] (I : T.IdealSheafData)
    (hfin : I.IsFiniteType) (hnil : I ≤ T.nilradical) :
    ∃ n : ℕ, I ≤ (frobPow p hT (𝟙 T) n).ker := by
  obtain ⟨N, hN⟩ :=
    Scheme.IdealSheafData.exists_pow_eq_bot_of_isFiniteType_of_le_nilradical I hfin hnil
  refine ⟨N, ?_⟩
  rw [frobPow_id_eq_frobeniusPow]
  change I ≤ Scheme.IdealSheafData.ofIdeals _
  rw [Scheme.IdealSheafData.le_ofIdeals_iff]
  intro U x hx
  have hxN : x ^ N = 0 := by
    have hpow : (I ^ N).ideal U = (I.ideal U) ^ N :=
      congrFun (Scheme.IdealSheafData.ideal_pow I N) U
    have h : x ^ N ∈ (I ^ N).ideal U := hpow ▸ Ideal.pow_mem_pow hx N
    rw [hN] at h
    exact (Ideal.mem_bot).mp h
  have hle : N ≤ p ^ N := (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
  refine RingHom.mem_ker.mpr ?_
  rw [Stacks.Divisors.frobeniusPow_app_apply, show p ^ N = N + (p ^ N - N) by omega, pow_add,
    hxN, zero_mul]
  rfl

/-- Every quasi-coherent ideal sheaf on a Noetherian scheme is of finite type. -/
private theorem isFiniteType_of_isNoetherian {T : Scheme.{u}} [IsNoetherian T]
    (I : T.IdealSheafData) : I.IsFiniteType := fun U ↦ by
  have : IsNoetherianRing Γ(T, U) := IsLocallyNoetherian.component_noetherian U
  exact IsNoetherian.noetherian _

/-- **On a Noetherian scheme in characteristic `p` the nilradical is killed by a power of the
absolute Frobenius**: it is of finite type, every ideal of a Noetherian ring being finitely
generated. -/
theorem exists_nilradical_le_ker_frobPow (p : ℕ) [Fact p.Prime] (T : Scheme.{u}) [IsNoetherian T]
    (hT : IsInCharacteristic T p) : ∃ n : ℕ, T.nilradical ≤ (frobPow p hT (𝟙 T) n).ker :=
  exists_le_ker_frobPow_of_isFiniteType_of_le_nilradical p hT T.nilradical
    (isFiniteType_of_isNoetherian _) le_rfl

/-! ### Invariance of `colim_F Vect` under thickenings -/

section Thickening

variable {T T' : Scheme.{u}} (i : T ⟶ T') (p : ℕ) [Fact p.Prime]
  (hT : IsInCharacteristic T p) (hT' : IsInCharacteristic T' p)

/-- **A thickening whose ideal sheaf is killed by a Frobenius power induces an essentially
surjective functor on `colim_F Vect`.** If `i.ker ≤ ker F_{T'}^n`, the closed immersion `i`
lifts `F_{T'}^n` to `g : T' ⟶ T`, and then `i ≫ g = F_T^n`. -/
theorem frobeniusColimitVectModelPullback_essSurj_of_le_ker_frobPow [IsClosedImmersion i]
    (n : ℕ) (hn : i.ker ≤ (frobPow p hT' (𝟙 T') n).ker) :
    (frobeniusColimitVectModelPullback i p hT hT').EssSurj := by
  refine frobeniusColimitVectModelPullback_essSurj_of_comp_eq_frobPow i
    (IsClosedImmersion.lift i _ hn) p hT hT' n ?_
  rw [← cancel_mono i, Category.assoc, IsClosedImmersion.lift_fac,
    comp_frobPow i (Category.comp_id _) n, frobPow_comp p (hY := hT) (hY' := hT') (𝟙 _) i n,
    Category.id_comp]

/-- **Stacks Tag 0EXH, the thickening remark.** Let `i : T ⟶ T'` be a thickening of schemes in
characteristic `p` (a closed immersion which is surjective on points) whose ideal sheaf is of
finite type, with `T'` quasi-compact and quasi-separated. Then pullback along `i` is an
equivalence `colim_F Vect(T') ≌ colim_F Vect(T)`. -/
theorem frobeniusColimitVectModelPullback_isEquivalence_of_isThickening [CompactSpace T']
    [QuasiSeparatedSpace T'] (hi : Stacks.Thickenings.IsThickening i) (hfin : i.ker.IsFiniteType) :
    (frobeniusColimitVectModelPullback i p hT hT').IsEquivalence := by
  have := hi.1
  have : Surjective i := ⟨hi.2⟩
  have : GeometricallyConnected i := geometricallyConnected_of_surjective_of_universallyInjective i
  obtain ⟨hfull, hfaith⟩ := frobeniusColimitVectModelPullback_full_faithful i p hT hT'
  obtain ⟨n, hn⟩ := exists_le_ker_frobPow_of_isFiniteType_of_le_nilradical p hT' i.ker hfin
    (Stacks.LiftInvertible.ker_le_nilradical_of_surjective i hi.2)
  exact { full := hfull, faithful := hfaith,
          essSurj := frobeniusColimitVectModelPullback_essSurj_of_le_ker_frobPow i p hT hT' n hn }

/-- **Pullback to the closed subscheme cut out by a finite type ideal sheaf of nilpotents is an
equivalence on `colim_F Vect`**, for `T'` quasi-compact and quasi-separated: such a closed
subscheme is a thickening whose ideal sheaf is of finite type. -/
theorem frobeniusColimitVectModelPullback_isEquivalence_subschemeι [CompactSpace T']
    [QuasiSeparatedSpace T'] (I : T'.IdealSheafData) (hfin : I.IsFiniteType)
    (hnil : I ≤ T'.nilradical) (hS : IsInCharacteristic I.subscheme p) :
    (frobeniusColimitVectModelPullback I.subschemeι p hS hT').IsEquivalence := by
  have hsupp : I.support = ⊤ := top_le_iff.mp (by
    simpa [Scheme.support_nilradical] using Scheme.IdealSheafData.support_antitone hnil)
  refine frobeniusColimitVectModelPullback_isEquivalence_of_isThickening _ p hS hT'
    ((Scheme.IdealSheafData.isThickening_subschemeι_iff I).mpr hsupp) ?_
  rw [Scheme.IdealSheafData.ker_subschemeι]
  exact hfin

/-- **Pullback to the reduction is an equivalence on `colim_F Vect`.** For a Noetherian scheme
`T'` in characteristic `p`, pullback along `T'_red ⟶ T'` is an equivalence
`colim_F Vect(T') ≌ colim_F Vect(T'_red)`. -/
theorem frobeniusColimitVectModelPullback_isEquivalence_reductionι [IsNoetherian T']
    (hred : IsInCharacteristic T'.reduction p) :
    (frobeniusColimitVectModelPullback T'.reductionι p hred hT').IsEquivalence := by
  refine frobeniusColimitVectModelPullback_isEquivalence_of_isThickening _ p hred hT'
    (Scheme.isThickening_reductionι T')
    (isFiniteType_of_isNoetherian _)

end Thickening

end AlgebraicGeometry

end
