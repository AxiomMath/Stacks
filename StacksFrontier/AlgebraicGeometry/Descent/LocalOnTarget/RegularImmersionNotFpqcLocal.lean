module

public import Mathlib.NumberTheory.Padics.RingHoms
public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorQuotient
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.RegularImmersionFpqcCounterexampleBaseChange
public import StacksCore.Tactic.StacksAttribute

/-!
# Regular immersions are not fpqc local on the target

Stacks tag 0694 asserts that each of the three conditions Koszul-regular, `H₁`-regular and
quasi-regular on an immersion is fpqc local on the base. Read for arbitrary morphisms, in the
sense of Stacks tag 02KO, this is false, and this file proves so: for each of the three
conditions, the morphism property "an immersion satisfying the condition" is not local on the
target for the fpqc precoverage.

The counterexample is `f : ∐ₚ Spec 𝔽ₚ ⟶ Spec ℤ` against the one-member fpqc covering
`Spec (∏ₚ ℤₚ) ⟶ Spec ℤ`. The morphism `f` is not an immersion
(`Stacks.Descent.not_isImmersion_counterexampleHom`), while its base change is
`∐ₚ Spec 𝔽ₚ ⟶ Spec (∏ₚ ℤₚ)` (`Stacks.Descent.isPullback_counterexampleBaseChange`). That base
change is the coproduct of the closed immersions `Spec 𝔽ₚ ⟶ Spec ℤₚ`, each cut out by the
nonzerodivisor `p`, followed by the open immersion `∐ₚ Spec ℤₚ ⟶ Spec (∏ₚ ℤₚ)`; so it is a
Koszul-regular immersion, closed in an open subscheme, but not quasi-compact. This is why the
library's true forms of tag 0694 restrict either to quasi-compact morphisms
(`AlgebraicGeometry.isLocalAtTarget_koszulRegularImmersion_inf_quasiCompact_fpqc`), to
morphisms that are already immersions
(`AlgebraicGeometry.isKoszulRegularImmersion_iff_of_fpqcZeroHypercover`), or to the fppf
topology (`AlgebraicGeometry.isLocalAtTarget_koszulRegularImmersion_fppf`).

## Main results

* `AlgebraicGeometry.isPullback_sigmaι_sigmaMap`: the base change of a coproduct of morphisms of
  schemes along a coproduct inclusion of the target is the corresponding member, for an
  arbitrary small index type.
* `AlgebraicGeometry.IsZariskiLocalAtTarget.sigmaMap_of_small`: a property Zariski local at the
  target is stable under arbitrary small disjoint unions.
* `Stacks.Descent.immersionProperty_counterexampleBaseChangeHom`: the base change of the
  counterexample morphism satisfies every condition on immersions that is read off the kernel of
  a closed factor, is stable under flat ring maps, glues Zariski locally, and holds for the
  one-term sequence `p` in `ℤₚ`.
* `Stacks.Descent.not_isLocalAtTarget_koszulRegularImmersion_fpqc`,
  `Stacks.Descent.not_isLocalAtTarget_h1RegularImmersion_fpqc`,
  `Stacks.Descent.not_isLocalAtTarget_quasiRegularImmersion_fpqc`: the three conditions of
  Stacks tag 0694 are not fpqc local on the target.

## Implementation notes

The van Kampen square for an infinite coproduct is checked directly: the coproduct inclusions
are open immersions with pairwise disjoint ranges, so the square is cartesian by
`AlgebraicGeometry.IsOpenImmersion.isPullback` once the preimage of the `i`-th summand is
computed pointwise. The refutation is stated in universe `0`, where the counterexample lives.

## References

* [Stacks Project, Lemma 35.23.34 (Tag 0694)](https://stacks.math.columbia.edu/tag/0694)
* [Stacks Project, Definition 35.22.1 (Tag 02KO)](https://stacks.math.columbia.edu/tag/02KO)
* [Stacks Project, Section 35.24 (Tag 02YL)](https://stacks.math.columbia.edu/tag/02YL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MorphismProperty
open Stacks.AlgebraicGeometry Stacks.AlgebraicGeometry.RegularIdealSheaf

universe v u

namespace AlgebraicGeometry

/-- The coproduct of a family of morphisms, evaluated on a point of a summand, is the image of
that point under the corresponding member. -/
theorem sigmaMap_sigmaι_apply {ι : Type v} [Small.{u} ι] {Y X : ι → Scheme.{u}}
    (α : ∀ i, Y i ⟶ X i) (j : ι) (z : Y j) :
    Limits.Sigma.map α (Sigma.ι Y j z) = Sigma.ι X j (α j z) := by
  rw [← Scheme.Hom.comp_apply, Sigma.ι_map, Scheme.Hom.comp_apply]

/-- **The van Kampen square of a coproduct of schemes.** The base change of `∐ Y ⟶ ∐ X` along
the `i`-th coproduct inclusion of the target is the `i`-th member `Y i ⟶ X i`, for an arbitrary
small index type. -/
theorem isPullback_sigmaι_sigmaMap {ι : Type v} [Small.{u} ι] {Y X : ι → Scheme.{u}}
    (α : ∀ i, Y i ⟶ X i) (i : ι) :
    IsPullback (α i) (Sigma.ι Y i) (Sigma.ι X i) (Limits.Sigma.map α) := by
  apply IsOpenImmersion.isPullback _ _ _ _ (by simp)
  ext y
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨j, z, rfl⟩ := (sigmaOpenCover Y).exists_eq y
    change Sigma.ι X i x = Limits.Sigma.map α (Sigma.ι Y j z) at hx
    obtain rfl : i = j := congrArg Sigma.fst
      ((sigmaι_eq_iff X i j x (α j z)).mp (hx.trans (sigmaMap_sigmaι_apply α j z)))
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨α i z, (sigmaMap_sigmaι_apply α i z).symm⟩

/-- **A property Zariski local at the target is stable under small disjoint unions.** The
coproduct inclusions of the target form an open cover, along which the coproduct of the family
pulls back to its members. -/
theorem IsZariskiLocalAtTarget.sigmaMap_of_small {P : MorphismProperty Scheme.{u}}
    [IsZariskiLocalAtTarget P] {ι : Type v} [Small.{u} ι] {X Y : ι → Scheme.{u}}
    (g : ∀ j, X j ⟶ Y j) (hg : ∀ j, P (g j)) :
    P (Limits.Sigma.map g) := by
  refine IsZariskiLocalAtTarget.of_openCover (P := P) (sigmaOpenCover Y) fun j => ?_
  have : HasPullback (Limits.Sigma.map g) (Sigma.ι Y j) :=
    (isPullback_sigmaι_sigmaMap g j).flip.hasPullback
  exact pullbackSnd_of_isPullback P (isPullback_sigmaι_sigmaMap g j).flip (hg j)

end AlgebraicGeometry

namespace Stacks.Descent

open _root_.AlgebraicGeometry

/-! ### The base change of the counterexample is a regular immersion -/

/-- The reduction `ℤₚ ⟶ 𝔽ₚ` is surjective, so `Spec 𝔽ₚ ⟶ Spec ℤₚ` is a closed immersion. -/
instance isClosedImmersion_specMap_toZMod (p : Nat.Primes) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (PadicInt.toZMod (p := (p : ℕ))))) :=
  IsClosedImmersion.spec_of_surjective _ (ZMod.ringHom_surjective _)

/-- The coproduct of the closed immersions `Spec 𝔽ₚ ⟶ Spec ℤₚ` is a closed immersion. -/
instance isClosedImmersion_padicIntSigmaReduce : IsClosedImmersion padicIntSigmaReduce :=
  IsZariskiLocalAtTarget.sigmaMap_of_small (P := @IsClosedImmersion) _ fun _ => inferInstance

/-- The base change of the counterexample morphism is an immersion: a closed immersion followed
by an open immersion. -/
instance isImmersion_counterexampleBaseChangeHom : IsImmersion counterexampleBaseChangeHom := by
  rw [counterexampleBaseChangeHom_eq]
  infer_instance

variable {Seq : ∀ {A : Type} [CommRing A] {r : ℕ}, (Fin r → A) → Prop}
  {Pred : ∀ {Z X : Scheme.{0}} (i : Z ⟶ X) [IsImmersion i], Prop}

/-- The closed immersion `Spec 𝔽ₚ ⟶ Spec ℤₚ` has its kernel generated, on the whole of
`Spec ℤₚ`, by the image of `p`. -/
theorem kerGeneratedBy_specMap_toZMod
    (hSeq : ∀ {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B), φ.Flat →
      ∀ {r : ℕ} (f : Fin r → A), Seq f → Seq fun i => φ (f i))
    (p : Nat.Primes) (hp : Seq fun _ : Fin 1 => ((p : ℕ) : ℤ_[p])) :
    KerGeneratedBy Seq (Spec.map (CommRingCat.ofHom (PadicInt.toZMod (p := (p : ℕ))))) := by
  intro _ _
  let e := Scheme.ΓSpecIso (CommRingCat.of ℤ_[p])
  refine ⟨⟨⊤, isAffineOpen_top _⟩, trivial, 1, fun _ => e.inv.hom ((p : ℕ) : ℤ_[p]), ?_,
    hSeq e.inv.hom (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso e.inv)) _ hp⟩
  show RingHom.ker (Spec.map _).appTop.hom = _
  rw [ker_appTop_Spec_map, CommRingCat.hom_ofHom, PadicInt.ker_toZMod,
    PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, Set.range_const]

/-- **The base change of the counterexample morphism is a regular immersion.** Any condition on
immersions which is read off the kernel of a closed factor, is stable under flat ring maps, glues
Zariski locally, and holds for the one-term sequence `p` in each `ℤₚ`, holds for
`Stacks.Descent.counterexampleBaseChangeHom`. -/
theorem immersionProperty_counterexampleBaseChangeHom
    (hSeq : ∀ {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B), φ.Flat →
      ∀ {r : ℕ} (f : Fin r → A), Seq f → Seq fun i => φ (f i))
    (hPred : ∀ {Z X : Scheme.{0}} (i : Z ⟶ X) [IsImmersion i] (V : X.Opens)
      (jV : Z ⟶ V.toScheme) [IsClosedImmersion jV], jV ≫ V.ι = i →
        (Pred i ↔ KerGeneratedBy Seq jV))
    (hglue : ∀ {Z X : Scheme.{0}} (i : Z ⟶ X) [IsImmersion i] {ι : Type} (V : ι → X.Opens),
      iSup V = ⊤ → (∀ k, Pred (i.resLE (V k) (i ⁻¹ᵁ V k) le_rfl)) → Pred i)
    (hp : ∀ p : Nat.Primes, Seq fun _ : Fin 1 => ((p : ℕ) : ℤ_[p])) :
    immersionProperty Pred counterexampleBaseChangeHom := by
  have _ := immersionProperty_isZariskiLocalAtTarget hSeq hPred hglue (Pred := Pred)
  have hred : immersionProperty Pred padicIntSigmaReduce :=
    IsZariskiLocalAtTarget.sigmaMap_of_small (P := immersionProperty Pred) _ fun p =>
      ⟨inferInstance, (pred_iff_kerGeneratedBy_of_isClosedImmersion hSeq hPred _).mpr
        (kerGeneratedBy_specMap_toZMod hSeq p (hp p))⟩
  have hker : KerGeneratedBy Seq padicIntSigmaReduce :=
    (pred_iff_kerGeneratedBy_of_isClosedImmersion hSeq hPred _).mp hred.2
  let s := sigmaSpec fun q : Nat.Primes => CommRingCat.of ℤ_[q]
  have hfac : (padicIntSigmaReduce ≫ s.isoOpensRange.hom) ≫ s.opensRange.ι =
      counterexampleBaseChangeHom := by
    rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, counterexampleBaseChangeHom_eq]
  exact ⟨inferInstance, (hPred _ s.opensRange _ hfac).mpr
    (kerGeneratedBy_comp_iso hSeq padicIntSigmaReduce s.isoOpensRange hker)⟩

/-! ### The refutation -/

/-- **A condition on immersions as above is not fpqc local on the target.** Locality would
descend the condition from the base change of `Stacks.Descent.counterexampleHom` along the
fpqc covering `Spec (∏ₚ ℤₚ) ⟶ Spec ℤ` to `Stacks.Descent.counterexampleHom` itself, which is not
an immersion. -/
theorem not_isLocalAtTarget_immersionProperty_fpqc
    (hSeq : ∀ {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B), φ.Flat →
      ∀ {r : ℕ} (f : Fin r → A), Seq f → Seq fun i => φ (f i))
    (hPred : ∀ {Z X : Scheme.{0}} (i : Z ⟶ X) [IsImmersion i] (V : X.Opens)
      (jV : Z ⟶ V.toScheme) [IsClosedImmersion jV], jV ≫ V.ι = i →
        (Pred i ↔ KerGeneratedBy Seq jV))
    (hglue : ∀ {Z X : Scheme.{0}} (i : Z ⟶ X) [IsImmersion i] {ι : Type} (V : ι → X.Opens),
      iSup V = ⊤ → (∀ k, Pred (i.resLE (V k) (i ⁻¹ᵁ V k) le_rfl)) → Pred i)
    (hp : ∀ p : Nat.Primes, Seq fun _ : Fin 1 => ((p : ℕ) : ℤ_[p])) :
    ¬ (immersionProperty Pred).IsLocalAtTarget Scheme.fpqcPrecoverage := by
  intro hloc
  obtain ⟨_, _⟩ := flat_and_surjective_specMap_padicIntProd
  have _ : Flat counterexampleCover := ‹_›
  have _ : Surjective counterexampleCover := ‹_›
  refine not_isImmersion_counterexampleHom
    (MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd (P := immersionProperty Pred)
      counterexampleCover.singleton_mem_fpqcPrecoverage ?_).1
  rintro _ _ _ ⟨⟩
  exact pullbackSnd_of_isPullback _ isPullback_counterexampleBaseChange
    (immersionProperty_counterexampleBaseChangeHom hSeq hPred hglue hp)

/-- `p` is a regular element of `ℤₚ`: a nonzero element of a domain, lying in the maximal ideal of
a local ring. -/
theorem isRegular_ofFn_padicInt_p (p : Nat.Primes) :
    RingTheory.Sequence.IsRegular ℤ_[p] (List.ofFn fun _ : Fin 1 => ((p : ℕ) : ℤ_[p])) := by
  have hl : List.ofFn (fun _ : Fin 1 => ((p : ℕ) : ℤ_[p])) = [((p : ℕ) : ℤ_[p])] := rfl
  rw [hl, IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal (by
      intro r hr
      rw [List.mem_singleton.mp hr, PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.mem_span_singleton_self _),
    RingTheory.Sequence.isWeaklyRegular_singleton_iff]
  exact IsSMulRegular.of_ne_zero (M := ℤ_[p]) (Nat.cast_ne_zero.mpr p.2.ne_zero)

/-- `p` is a Koszul-regular sequence of length one in `ℤₚ`. -/
theorem isKoszulRegular_padicInt_p (p : Nat.Primes) :
    Koszul.IsKoszulRegular fun _ : Fin 1 => ((p : ℕ) : ℤ_[p]) :=
  (Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular (M := ℤ_[p])).2.2
    (isRegular_ofFn_padicInt_p p)

/-- **Stacks Project, Tag 0694, the Koszul-regular clause, is false for the fpqc topology.**
Being a Koszul-regular immersion is not local on the target for the fpqc precoverage. -/
@[stacks 0694 "koszul_regular, counterexample: false for fpqc coverings without quasi-compactness"]
theorem not_isLocalAtTarget_koszulRegularImmersion_fpqc :
    ¬ MorphismProperty.IsLocalAtTarget
      (fun _ _ f => ∃ hf : IsImmersion f, @IsKoszulRegularImmersion _ _ f hf)
      Scheme.fpqcPrecoverage.{0} :=
  not_isLocalAtTarget_immersionProperty_fpqc
    (Seq := fun f => Koszul.IsKoszulRegular f)
    (Pred := fun i => IsKoszulRegularImmersion i)
    isKoszulRegular_of_ringHomFlat
    (by
      intro Z X i _ V jV _ hij
      exact (isKoszulRegularImmersion_iff_of_open i V jV hij).trans
        (isKoszulRegularIdealSheaf_iff_kerGeneratedBy jV))
    isKoszulRegularImmersion_of_resLE isKoszulRegular_padicInt_p

/-- **Stacks Project, Tag 0694, the `H₁`-regular clause, is false for the fpqc topology.**
Being an `H₁`-regular immersion is not local on the target for the fpqc precoverage. -/
@[stacks 0694 "h1_regular, counterexample: false for fpqc coverings without quasi-compactness"]
theorem not_isLocalAtTarget_h1RegularImmersion_fpqc :
    ¬ MorphismProperty.IsLocalAtTarget
      (fun _ _ f => ∃ hf : IsImmersion f, @IsH1RegularImmersion _ _ f hf)
      Scheme.fpqcPrecoverage.{0} :=
  not_isLocalAtTarget_immersionProperty_fpqc
    (Seq := fun f => Koszul.IsH1Regular f)
    (Pred := fun i => IsH1RegularImmersion i)
    isH1Regular_of_ringHomFlat
    (by
      intro Z X i _ V jV _ hij
      exact (isH1RegularImmersion_iff_of_open i V jV hij).trans
        (isH1RegularIdealSheaf_iff_kerGeneratedBy jV))
    isH1RegularImmersion_of_resLE fun p => isKoszulRegular_padicInt_p p 1 one_ne_zero

/-- **Stacks Project, Tag 0694, the quasi-regular clause, is false for the fpqc topology.**
Being a quasi-regular immersion is not local on the target for the fpqc precoverage. -/
@[stacks 0694 "quasi_regular, counterexample: false for fpqc coverings without quasi-compactness"]
theorem not_isLocalAtTarget_quasiRegularImmersion_fpqc :
    ¬ MorphismProperty.IsLocalAtTarget
      (fun _ _ f => ∃ hf : IsImmersion f, @RegularIdealSheaf.IsQuasiRegularImmersion _ _ f hf)
      Scheme.fpqcPrecoverage.{0} :=
  not_isLocalAtTarget_immersionProperty_fpqc
    (Seq := fun {A} _ _ f => RingTheory.Sequence.IsQuasiRegular A (List.ofFn f))
    (Pred := fun i => RegularIdealSheaf.IsQuasiRegularImmersion i)
    isQuasiRegular_of_ringHomFlat
    (by
      intro Z X i _ V jV _ hij
      exact (RegularIdealSheaf.isQuasiRegularImmersion_iff_of_open i V jV hij).trans
        (isQuasiRegularIdealSheaf_iff_kerGeneratedBy jV))
    RegularIdealSheaf.isQuasiRegularImmersion_of_resLE fun p =>
      Koszul.isQuasiRegular_of_isH1RegularOn
        ((Koszul.isH1RegularOn_self_iff _).2 (isKoszulRegular_padicInt_p p 1 one_ne_zero))

end Stacks.Descent

end
