module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveFaithfullyFlat
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautFormalSpectrumRepresentable
import all StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveFaithfullyFlat

/-!
# Stacks 0AQY without a representability hypothesis

`AlgebraicGeometry.FormalSpace.isRigSurjective_formalSpectrumMap_iff_faithfullyFlat` proves
Stacks 0AQY carrying `hAdicRepresentable`, the representability of the adic points of `Spf A`.
That hypothesis is an instance of the implication (3) ⟹ (1) of **Stacks 0AN5**, which the
library proves as
`AlgebraicGeometry.FormalSpace.isRepresentableByAlgebraicSpacesULift_formalSpectrumMap_of_isTaut`.
This file discharges it and states the criterion with no such hypothesis.

`AlgebraicGeometry.FormalSpace.IsRigSurjective` renders adicness of its quantified point as
representability by algebraic spaces, so the adic point `Spf R → Spf A` that the source proof
constructs — produced as a `RingHom.IsAdic` — has to be turned into a representable morphism
before rig-surjectivity can be applied to it. An adic homomorphism is taut
(`RingHom.isTaut_of_isAdic`, Stacks 0GBS part (1)), and 0AN5 identifies tautness with
representability. Its hypotheses are all available where it is used: weak admissibility of `R`
is `TopologicalRing.isWeaklyAdmissible_of_isAdic`, `R` being adic and adically complete; and its
site condition `DR.HasLargeSite` of Stacks 0AIF is `hasLargeSite_of_mk_lt_cutoff` applied to the
bound `#R < B.cutoff` which the construction of `R` already establishes.

## Main results

* `AlgebraicGeometry.FormalSpace.isRigSurjective_formalSpectrumMap_iff_faithfullyFlat'`:
  **Stacks 0AQY**.
* `AlgebraicGeometry.FormalSpace.exists_isPrime_comap_eq_of_isRigSurjective'`: the geometric
  half of Stacks 0AQY, that rig-surjectivity makes every maximal ideal of `A` containing `I`
  a contraction of a prime of `C`.

## References

* [Stacks Project, Tag 0AQY](https://stacks.math.columbia.edu/tag/0AQY)
* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
-/

@[expose] public noncomputable section

open Cardinal CategoryTheory

namespace AlgebraicGeometry.FormalSpace

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- An ideal whose image in `L` is not contained in `q` has nonzero image along any ring map
`L → L ⧸ q → R` whose second factor is injective. -/
theorem map_ne_bot_of_not_map_le {A L R : Type*} [CommRing A] [CommRing L] [CommRing R]
    (φ : A →+* L) (q : Ideal L) (b : L ⧸ q →+* R) (hb : Function.Injective b) (I : Ideal A)
    (hI : ¬ I.map φ ≤ q) : I.map ((b.comp (Ideal.Quotient.mk q)).comp φ) ≠ ⊥ := by
  intro hbot
  refine hI (Ideal.map_le_iff_le_comap.mpr fun z hz => ?_)
  change φ z ∈ q
  exact Ideal.Quotient.eq_zero_iff_mem.mp (hb ((Ideal.mem_bot.mp
    (hbot ▸ Ideal.mem_map_of_mem _ hz)).trans (map_zero b).symm))

/-- A subring of the fraction field of a quotient of a localization of a ring smaller than the
cutoff is itself smaller than the cutoff. -/
theorem mk_subalgebra_fractionRing_lt_cutoff {A : Type u} [CommRing A] (hA : #A < B.cutoff)
    (m : Ideal A) [m.IsPrime] (q : Ideal (Localization.AtPrime m))
    (V : Subalgebra (Localization.AtPrime m ⧸ q) (FractionRing (Localization.AtPrime m ⧸ q))) :
    #V < B.cutoff := by
  have hL : #(Localization.AtPrime m) < B.cutoff :=
    (Cardinal.mk_le_of_isLocalization m.primeCompl _).trans_lt (max_lt B.aleph0_lt_cutoff hA)
  set R₀ := Localization.AtPrime m ⧸ q
  exact (mk_le_of_injective (f := fun z : V => (z : FractionRing R₀))
    Subtype.val_injective).trans_lt ((Cardinal.mk_le_of_isLocalization (nonZeroDivisors R₀)
      (FractionRing R₀)).trans_lt (max_lt B.aleph0_lt_cutoff (mk_quotient_le.trans_lt hL)))

section Criterion

variable {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
  [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
  [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
  [IsNoetherianRing A]

omit [IsNoetherianRing A] in
/-- A rig-surjective `Spf C → Spf A` lifts every adic point `A → R` into a small complete
discrete valuation ring: the maximal ideal of `A` it contracts to is the contraction of a prime
of `C`. -/
theorem exists_isPrime_comap_eq_of_isRigSurjective_of_isAdic (I : Ideal A)
    (hAadic : IsAdic I) (hAcomplete : IsAdicComplete I A)
    (hCadic : IsAdic (I.map (algebraMap A C)))
    (hCcomplete : IsAdicComplete (I.map (algebraMap A C)) C)
    {D : QuotientSystem B S hS A} {E : QuotientSystem B S hS C}
    (f : ContinuousHom D E) (hf : f.toRingHom = algebraMap A C)
    (hrig : IsRigSurjective B S hS
      (formalSpectrumMap
        (TopologicalRing.isWeaklyAdmissible_of_isAdic hAadic hAcomplete) f))
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R]
    (hRtop : IsAdic (IsLocalRing.maximalIdeal R))
    (hRcomplete : IsAdicComplete (IsLocalRing.maximalIdeal R) R) (hRcard : #R < B.cutoff)
    (r : A →+* R) (hrcont : Continuous r) (hradic : RingHom.IsAdic r) :
    ∃ n : Ideal C, n.IsPrime ∧
      n.comap (algebraMap A C) = (IsLocalRing.maximalIdeal R).comap r := by
  set hAweak := TopologicalRing.isWeaklyAdmissible_of_isAdic hAadic hAcomplete
  have hCweak : TopologicalRing.IsWeaklyAdmissible C :=
    TopologicalRing.isWeaklyAdmissible_of_isAdic hCadic hCcomplete
  have hRweak : TopologicalRing.IsWeaklyAdmissible R :=
    TopologicalRing.isWeaklyAdmissible_of_isAdic hRtop hRcomplete
  obtain ⟨DR, p, hp⟩ := exists_quotientSystem_continuousHom hAweak D r hrcont hRcard
  obtain ⟨R', hR'ring, hR'dom, hR'dvr, hR'alg, hR'ext, hR'top, hR'topring, hR'lin,
    hR'adic, hR'complete, DR', e, y, he, hy⟩ :=
    hrig R hRtop hRcomplete hRweak DR (formalSpectrumMap hAweak p)
      (isRepresentableByAlgebraicSpacesULift_formalSpectrumMap_of_isTaut B S hS hAweak hRweak
        D DR (hasLargeSite_of_mk_lt_cutoff DR hRcard) p
        (RingHom.isTaut_of_isAdic p.toRingHom (by rwa [hp])))
  let : CommRing R' := hR'ring
  have : IsDomain R' := hR'dom
  have : IsDiscreteValuationRing R' := hR'dvr
  let : Algebra R R' := hR'alg
  let : TopologicalSpace R' := hR'top
  have : IsTopologicalRing R' := hR'topring
  have : IsLinearTopology R' R' := hR'lin
  have : IsDiscreteValuationRing.IsExtension R R' := hR'ext
  have hR'weak : TopologicalRing.IsWeaklyAdmissible R' :=
    TopologicalRing.isWeaklyAdmissible_of_isAdic hR'adic hR'complete
  obtain ⟨g, hg, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hCweak hR'weak y
  obtain ⟨fg, hfg⟩ := exists_continuousHom_comp hAweak f g hCweak
  obtain ⟨pe, hpe⟩ := exists_continuousHom_comp hAweak p e hRweak
  have hhom : fg = pe := by
    obtain ⟨k, -, huniq⟩ :=
      existsUnique_continuousHom_formalSpectrumMap_eq hAweak hR'weak
        (formalSpectrumMap hAweak pe)
    refine (huniq fg ?_).trans (huniq pe rfl).symm
    change formalSpectrumMap hAweak fg = formalSpectrumMap hAweak pe
    rw [← formalSpectrumMap_comp hAweak hCweak f g fg hfg,
      ← formalSpectrumMap_comp hAweak hRweak p e pe hpe, hg]
    exact hy
  have hring : g.toRingHom.comp (algebraMap A C) = (algebraMap R R').comp r := by
    have hh := congrArg ContinuousHom.toRingHom hhom
    rwa [hfg, hpe, hf, he, hp] at hh
  refine ⟨(IsLocalRing.maximalIdeal R').comap g.toRingHom,
    Ideal.comap_isPrime g.toRingHom _, ?_⟩
  rw [Ideal.comap_comap, hring, ← Ideal.comap_comap, IsLocalRing.maximalIdeal_comap]

/-- The geometric step of Stacks 0AQY: if `Spf C → Spf A` is rig-surjective then every maximal
ideal `I ⊆ 𝔪 ⊆ A` is the contraction of a prime of `C`.

The vanishing `I`-torsion yields a prime `𝔮` of `A_𝔪` missing a regular element of `I`, hence a
one-dimensional local domain `A_𝔪 ⧸ 𝔮` dominated by a discrete valuation ring `V`
(Stacks 00PH); its completion `R` is a complete discrete valuation ring (Stacks 0AP1) and
`A → R` is adic because the image of `I` is a nonzero proper ideal of `R`. Rig-surjectivity
lifts `Spf R → Spf A` to `Spf C` over an extension `R ⊆ R'`, the lift is `Spf` of a ring map
`g : C → R'` (Stacks 0AN0), and full faithfulness identifies `g ∘ (A → C)` with `A → R → R'`.
So `g⁻¹ 𝔪_{R'}` contracts to `𝔪`. -/
theorem exists_isPrime_comap_eq_of_isRigSurjective' (I : Ideal A)
    (hAadic : IsAdic I) (hAcomplete : IsAdicComplete I A)
    (hCadic : IsAdic (I.map (algebraMap A C)))
    (hCcomplete : IsAdicComplete (I.map (algebraMap A C)) C)
    (hTorsion : Submodule.torsionBySet A A (I : Set A) = ⊥)
    {D : QuotientSystem B S hS A} {E : QuotientSystem B S hS C}
    (f : ContinuousHom D E) (hf : f.toRingHom = algebraMap A C)
    (hrig : IsRigSurjective B S hS
      (formalSpectrumMap
        (TopologicalRing.isWeaklyAdmissible_of_isAdic hAadic hAcomplete) f))
    (m : Ideal A) [m.IsMaximal] (hIm : I ≤ m) :
    ∃ n : Ideal C, n.IsPrime ∧ n.comap (algebraMap A C) = m := by
  classical
  have hAcard : #A < B.cutoff := mk_lt_cutoff_of_quotientSystem hAadic hAcomplete D
  obtain ⟨q, hqprime, hIavoid, V, hVdvr, hVfrac, hVlocal⟩ :=
    exists_prime_not_le_map_of_torsionBySet_eq_bot I m hIm hTorsion
  set L := Localization.AtPrime m
  set R₀ := L ⧸ q
  have : q.IsPrime := hqprime
  have : IsDomain R₀ := Ideal.Quotient.isDomain q
  have : IsLocalRing R₀ :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
  have : IsDiscreteValuationRing V := hVdvr
  have : IsFractionRing V (FractionRing R₀) := hVfrac
  have : IsLocalRing V := hVdvr.toIsLocalRing
  -- `R` is the completion of `V`, a complete discrete valuation ring
  set R : Type u := AdicCompletion (IsLocalRing.maximalIdeal V) V
  obtain ⟨hRdom, hRdvr⟩ :=
    (isDiscreteValuationRing_iff_adicCompletion_maximalIdeal (A := V)).mp ⟨inferInstance, hVdvr⟩
  have : IsDomain R := hRdom
  have : IsDiscreteValuationRing R := hRdvr
  let : TopologicalSpace R := (IsLocalRing.maximalIdeal R).adicTopology
  have hRtopring : IsTopologicalRing R :=
    (IsLocalRing.maximalIdeal R).ringFilterBasis.isTopologicalRing
  have hRlin : IsLinearTopology R R := (IsLocalRing.maximalIdeal R).isLinearTopology
  have hRtop : IsAdic (IsLocalRing.maximalIdeal R) := rfl
  have hRcomplete : IsAdicComplete (IsLocalRing.maximalIdeal R) R := inferInstance
  have hRcard : #R < B.cutoff :=
    mk_adicCompletion_lt_cutoff _ (mk_subalgebra_fractionRing_lt_cutoff hAcard m q V)
  -- the adic ring map `r : A → R`
  have : IsLocalHom (algebraMap R₀ V) := hVlocal
  have : IsLocalHom (Ideal.Quotient.mk q) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  set b : R₀ →+* R := (algebraMap V R).comp (algebraMap R₀ V)
  set r : A →+* R := (b.comp (Ideal.Quotient.mk q)).comp (algebraMap A L) with hrdef
  have hbinj : Function.Injective b :=
    (AdicCompletion.of_injective (IsLocalRing.maximalIdeal V) V).comp fun x y h =>
      IsFractionRing.injective R₀ (FractionRing R₀)
        (congrArg (fun z : V => (z : FractionRing R₀)) h)
  have hrmax : (IsLocalRing.maximalIdeal R).comap r = m := by
    rw [hrdef, ← Ideal.comap_comap, IsLocalRing.maximalIdeal_comap]
    exact IsLocalization.AtPrime.under_maximalIdeal L m
  have hIr : I.map r ≤ IsLocalRing.maximalIdeal R := by
    rwa [Ideal.map_le_iff_le_comap, hrmax]
  have hIrne : I.map r ≠ ⊥ := map_ne_bot_of_not_map_le _ q b hbinj I hIavoid
  have hrcont : Continuous r := continuous_of_isAdic_of_map_le hAadic hRtop r hIr
  have hradic : RingHom.IsAdic r :=
    ⟨I, hAadic, isAdic_of_ne_bot_of_ne_top hRtop _ hIrne
      (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top hIr)⟩
  obtain ⟨n, hn, hnm⟩ := exists_isPrime_comap_eq_of_isRigSurjective_of_isAdic I hAadic
    hAcomplete hCadic hCcomplete f hf hrig R hRtop hRcomplete hRcard r hrcont hradic
  exact ⟨n, hn, hnm.trans hrmax⟩

/-- **Stacks 0AQY.** Let `A` be a Noetherian ring complete with respect to an ideal `I` whose
`I`-torsion vanishes, and let `C` be an `I`-adically complete `A`-algebra such that
`A/Iⁿ → C/IⁿC` is flat and of finite type for every `n`. Then `Spf C → Spf A` is rig-surjective
if and only if `A/I → C/IC` is faithfully flat.

Faithful flatness gives rig-surjectivity by Stacks 0AQX. Conversely, a closed point of
`Spec(A/I)` is a maximal ideal `I ⊆ 𝔪 ⊆ A`, and
`exists_isPrime_comap_eq_of_isRigSurjective'` contracts a prime of `C` onto it; so
`Spec(C/IC) → Spec(A/I)` meets every closed point, which for a flat map is faithful flatness
(Stacks 00HQ). -/
@[stacks 0AQY]
theorem isRigSurjective_formalSpectrumMap_iff_faithfullyFlat' (I : Ideal A)
    (hAadic : IsAdic I) (hAcomplete : IsAdicComplete I A)
    (hCadic : IsAdic (I.map (algebraMap A C)))
    (hCcomplete : IsAdicComplete (I.map (algebraMap A C)) C)
    (hTorsion : Submodule.torsionBySet A A (I : Set A) = ⊥)
    (hfinite : ∀ n : ℕ, Algebra.FiniteType (A ⧸ I ^ n) (C ⧸ (I ^ n).map (algebraMap A C)))
    (hflat : ∀ n : ℕ, Module.Flat (A ⧸ I ^ n) (C ⧸ (I ^ n).map (algebraMap A C)))
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C)
    (f : ContinuousHom D E) (hf : f.toRingHom = algebraMap A C) :
    IsRigSurjective B S hS
      (formalSpectrumMap
        (TopologicalRing.isWeaklyAdmissible_of_isAdic hAadic hAcomplete) f) ↔
      Module.FaithfullyFlat (A ⧸ I) (C ⧸ I.map (algebraMap A C)) := by
  classical
  refine ⟨fun hrig => ?_, fun hff =>
    isRigSurjective_formalSpectrumMap I hAadic hAcomplete hCadic hCcomplete hfinite hflat hff
      D E f hf⟩
  have hflat1 : Module.Flat (A ⧸ I) (C ⧸ I.map (algebraMap A C)) := by
    convert hflat 1 using 2 <;> rw [pow_one]
  set φ := algebraMap (A ⧸ I) (C ⧸ I.map (algebraMap A C))
  have hflatRH : RingHom.Flat φ := RingHom.flat_algebraMap_iff.mpr hflat1
  refine RingHom.faithfullyFlat_algebraMap_iff.mp
    (((faithfullyFlat_tfae00HQ φ hflatRH).out 3 1).mp fun x hx => ?_)
  -- a closed point of `Spec (A ⧸ I)` is a maximal ideal `I ≤ m` of `A`
  obtain ⟨m, hmmax, hIm, hmap⟩ := exists_isMaximal_map_eq I x.asIdeal
    ((PrimeSpectrum.isClosed_singleton_iff_isMaximal x).mp hx)
  have : m.IsMaximal := hmmax
  obtain ⟨n, hnprime, hncomap⟩ := exists_isPrime_comap_eq_of_isRigSurjective' I hAadic
    hAcomplete hCadic hCcomplete hTorsion f hf hrig m hIm
  have hIn : I.map (algebraMap A C) ≤ n := by
    rwa [Ideal.map_le_iff_le_comap, hncomap]
  set n' := n.map (Ideal.Quotient.mk (I.map (algebraMap A C)))
  have hn' : n'.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hIn
  refine ⟨⟨n', hn'⟩, PrimeSpectrum.ext ?_⟩
  change n'.comap φ = x.asIdeal
  rw [← hmap]
  refine Ideal.comap_injective_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective ?_
  rw [Ideal.comap_map_mk hIm, Ideal.comap_comap,
    show φ.comp (Ideal.Quotient.mk I) =
      (Ideal.Quotient.mk (I.map (algebraMap A C))).comp (algebraMap A C) from rfl,
    ← Ideal.comap_comap, Ideal.comap_map_mk hIn, hncomap]

end Criterion

end AlgebraicGeometry.FormalSpace

end
