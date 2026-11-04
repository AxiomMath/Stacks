module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.RegularImmersion
public import StacksCore.Tactic.StacksAttribute

/-!
# The regularity conditions on an immersion are fpqc local on the target

Let `i : Z ⟶ X` be an immersion of schemes. Stacks tag 0694 asserts that each of the three
conditions Koszul-regular, `H₁`-regular and quasi-regular of Stacks tag 063J is local on the
target for the fpqc topology, with no finiteness hypothesis. This file proves that for a morphism
which is already known to be an immersion, with no quasi-compactness: for `i` an immersion and
`{Xⱼ ⟶ X}` an fpqc covering, `i` satisfies one of the three conditions if and only if every base
change `Z ×_X Xⱼ ⟶ Xⱼ` does.

What is **not** proved here is that a morphism whose base changes along an fpqc covering are
immersions is itself an immersion. That statement is false, and with it Stacks tag 0694 read
literally, as a statement about an arbitrary morphism of schemes — which is what "fpqc local on
the base" asks for. Being an immersion is fpqc local on the target for *quasi-compact*
immersions, Stacks tag 02L8
(`AlgebraicGeometry.isLocalAtTarget_isImmersion_inf_quasiCompact_fpqc`); without
quasi-compactness it holds for the fppf topology, Stacks tag 02YM
(`Stacks.Descent.isImmersion_descendsAlong_fppf`), whose proof uses that a surjective flat
morphism locally of finite presentation is open, which a surjective flat quasi-compact morphism
need not be. Stacks tag 02YL, the section in which tag 02YM sits, collects the properties for
which the Stacks Project "could not (yet)" show fpqc locality on the base, and being an
immersion is the first of them.

The counterexample, which applies to all three clauses at once. Let `f : ∐ₚ Spec 𝔽ₚ ⟶ Spec ℤ`
be the coproduct, over the prime numbers, of the closed immersions cut out by `p`. Its range is
the set of closed points of `Spec ℤ`, whose closure is all of `Spec ℤ` and which is not open
there, so the range is not locally closed and `f` is not an immersion — a fortiori none of the
three conditions holds for `f`. Let `B = ∏ₚ ℤₚ`, which is torsion-free, hence flat over `ℤ`
(the simpler `∏ₚ 𝔽ₚ` is not: it has torsion). The morphism `Spec B ⟶ Spec ℤ` is surjective,
and affine, hence quasi-compact, so `{Spec B ⟶ Spec ℤ}` is an fpqc covering. Since `q` is a
unit in `ℤ_q` for `q ≠ p`, the ideal `pB` is everything outside the `p`-th factor and `pℤₚ`
inside it, so `B ⧸ pB = ℤₚ ⧸ pℤₚ = 𝔽ₚ`, and the base
change of `f` along that covering is `∐ₚ Spec 𝔽ₚ ⟶ Spec B`. It factors through the open
`⋃ₚ D(eₚ)`, where `eₚ` is the idempotent of the `p`-th factor, and over each
`D(eₚ) = Spec ℤₚ` it is the closed immersion cut out by the single nonzerodivisor `p`; so it is
a closed immersion onto that open, i.e. an immersion, and it is a regular immersion, hence
Koszul-regular, `H₁`-regular and quasi-regular. The base change satisfies all three conditions
and `f` is not even an immersion. The failure is exactly the non-quasi-compactness of `f`.

The Stacks proof of tag 0694 passes over this. It discharges hypothesis (3) of the criterion of
Stacks tag 02KP — for `g : S' ⟶ S` a surjective flat morphism of affines and *any* `f : X ⟶ S`,
`P (S' ×_S X ⟶ S')` implies `P f` — by the algebra statement More on Algebra, Lemma 15.33.4
(tag 068N), which presupposes the morphism to be an immersion and so settles only the
ideal-theoretic half of that hypothesis; the other half is the fpqc descent of being an
immersion, which the counterexample refutes.

## Main results

* `AlgebraicGeometry.immersionProperty_iff_of_fpqcZeroHypercover`: the uniform statement. A
  condition on immersions that is read off the kernel of a closed factor, whose family predicate
  is stable under flat ring maps and whose ideal-theoretic form descends along faithfully flat
  ring maps, and which glues along open covers of the target, is fpqc local on the target among
  immersions.
* `AlgebraicGeometry.isKoszulRegularImmersion_iff_of_fpqcZeroHypercover`,
  `AlgebraicGeometry.isH1RegularImmersion_iff_of_fpqcZeroHypercover` and
  `AlgebraicGeometry.isQuasiRegularImmersion_iff_of_fpqcZeroHypercover`: the three clauses of
  Stacks tag 0694, for the fpqc topology and with no quasi-compactness, for an immersion. These
  are registered for the tag, each clause string naming the `IsImmersion` hypothesis they add.

The two self-contained halves of the counterexample below are formalized in
`StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.RegularImmersionFpqcCounterexample`, whose
and the counterexample is assembled in
`Stacks.Descent.not_isLocalAtTarget_koszulRegularImmersion_fpqc` and its two companions.

## Implementation notes

The criterion used is `Stacks.Descent.iff_of_fpqcZeroHypercover_of_affineDescent`, the form of
Stacks tag 02KP whose descent hypothesis is assumed only on a class `C` of morphisms stable under
base change and whose conclusion is likewise restricted to `C`; here `C` is `IsImmersion`. The
descent step it consumes is
`AlgebraicGeometry.immersionProperty_of_pullbackSnd_of_isAffine`, which is the affine descent step
with the quasi-compactness of the morphism replaced by the hypothesis that it is an immersion:
the affine-open condition is read off the canonical *closed* factor of the immersion, and a closed
immersion is affine, hence quasi-compact, whatever the immersion it factors. Every other
ingredient — Zariski locality, stability under flat base change, the affine dictionary and the
faithfully flat descent of the ideal-theoretic condition — is already free of quasi-compactness in
`StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.RegularImmersionFpqc`.

The statements registered for Stacks tag 0694 in this development are therefore the four true
readings of a tag which is false as stated, and each clause string names the hypothesis it adds
or the topology it shrinks to.
The fpqc clauses of `StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.RegularImmersionFpqc`
add quasi-compactness, which is tag 02L8's hypothesis and exactly what the counterexample above
violates. The fppf clauses of
`StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.RegularImmersionFppf` shrink the topology
to the largest one for which the descent of being an immersion holds, tag 02YM, and add nothing
at all to the morphism; that is the strongest true form of the tag, and the étale clauses of
`StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.RegularImmersion` are a special case of it,
an étale covering being an fppf covering. The clauses here are the remaining
reading, restricting the morphism rather than the topology or the finiteness: they assume
`IsImmersion i`, which is not in the source, but it is precisely the hypothesis under which the
Stacks proof's own appeal to More on Algebra, Lemma 15.33.4 discharges hypothesis (3) of tag
02KP, so this reading is the one closest to the argument the source gives. It is not comparable
with the fppf reading: it keeps the tag's own topology and restricts the morphism instead.

## References

* [Stacks Project, Lemma 35.23.34 (Tag 0694)](https://stacks.math.columbia.edu/tag/0694)
* [Stacks Project, Lemma 35.22.4 (Tag 02KP)](https://stacks.math.columbia.edu/tag/02KP)
* [Stacks Project, Lemma 35.23.23 (Tag 02L8)](https://stacks.math.columbia.edu/tag/02L8)
* [Stacks Project, Section 35.24 (Tag 02YL)](https://stacks.math.columbia.edu/tag/02YL)
* [Stacks Project, Lemma 35.24.1 (Tag 02YM)](https://stacks.math.columbia.edu/tag/02YM)
* [Stacks Project, Lemma 15.33.4 (Tag 068N)](https://stacks.math.columbia.edu/tag/068N)
* [Stacks Project, Definition 31.22.1 (Tag 063J)](https://stacks.math.columbia.edu/tag/063J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MorphismProperty
open Stacks.AlgebraicGeometry
open Stacks.AlgebraicGeometry.RegularIdealSheaf

namespace AlgebraicGeometry

universe w u

variable {Seq : ∀ {A : Type u} [CommRing A] {r : ℕ}, (Fin r → A) → Prop}
variable {Pred : ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i], Prop}

/-- **The uniform form of Stacks tag 0694 for the fpqc topology, with no quasi-compactness.** A
condition on immersions that is read off the kernel of a closed factor through any open in which
the immersion is closed, whose family predicate is stable under flat ring maps and whose
ideal-theoretic form descends along faithfully flat ring maps, and which glues along open covers
of the target, holds for an immersion if and only if it holds for the base changes of that
immersion along the members of an fpqc covering of the target.

The hypothesis that `i` is an immersion is not in Stacks tag 0694; it stands in for the fpqc
descent of the property of being an immersion, which holds for quasi-compact immersions (Stacks
tag 02L8) and is false in general, so the hypothesis cannot be dropped. The module docstring
has the counterexample. -/
theorem immersionProperty_iff_of_fpqcZeroHypercover
    (hSeq : ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B), φ.Flat →
      ∀ {r : ℕ} (f : Fin r → A), Seq f → Seq fun i => φ (f i))
    (hdescSeq : ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B), φ.FaithfullyFlat →
      ∀ I : Ideal A, (I.map φ).IsLocallySpannedBy Seq → I.IsLocallySpannedBy Seq)
    (hPred : ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (V : X.Opens)
      (jV : Z ⟶ V.toScheme) [IsClosedImmersion jV], jV ≫ V.ι = i →
        (Pred i ↔ KerGeneratedBy Seq jV))
    (hglue : ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] {ι : Type u} (V : ι → X.Opens),
      iSup V = ⊤ → (∀ k, Pred (i.resLE (V k) (i ⁻¹ᵁ V k) le_rfl)) → Pred i)
    {Z X : Scheme.{u}} (i : Z ⟶ X) (hi : IsImmersion i)
    (𝒰 : Precoverage.ZeroHypercover.{w} Scheme.fpqcPrecoverage X) :
    immersionProperty Pred i ↔
      ∀ k, immersionProperty Pred (pullback.snd i (𝒰.f k)) := by
  have _ := immersionProperty_respectsIso hSeq hPred (Pred := Pred)
  have _ := immersionProperty_isStableUnderFlatBaseChange hSeq hPred (Pred := Pred)
  have _ := immersionProperty_isZariskiLocalAtTarget hSeq hPred hglue (Pred := Pred)
  refine Stacks.Descent.iff_of_fpqcZeroHypercover_of_affineDescent _
    (@IsImmersion : MorphismProperty Scheme.{u}) ?_ i hi 𝒰
  intro S S' T _ _ g hsurj hflat f hf hP
  have _ : Surjective g := hsurj
  have _ : Flat g := hflat
  exact immersionProperty_of_pullbackSnd_of_isAffine hSeq hdescSeq hPred g f hf hP

/-- Unwrapping `immersionProperty`: for an immersion, a condition holds iff it holds on the base
changes, provided the same is true of `immersionProperty Pred`. -/
private theorem pred_iff_of_immersionProperty_iff {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (𝒰 : Precoverage.ZeroHypercover.{w} Scheme.fpqcPrecoverage X)
    (key : immersionProperty Pred i ↔
      ∀ k, immersionProperty Pred (pullback.snd i (𝒰.f k))) :
    Pred i ↔ ∀ k, Pred (pullback.snd i (𝒰.f k)) :=
  ⟨fun h k => (key.mp ⟨inferInstance, h⟩ k).2,
    fun h => (key.mpr fun k => ⟨inferInstance, h k⟩).2⟩

/-! ### The three clauses of Stacks tag 0694 for an immersion -/

/-- **Stacks Project, Tag 0694, the Koszul-regular clause, for an immersion.** An immersion of
schemes is Koszul-regular if and only if its base changes along the members of an fpqc covering
of the target are, with no quasi-compactness. -/
@[stacks 0694 "koszul_regular, erratum: morphisms that are immersions; fpqc, no quasi-compactness",
  sga "6 VII 1.5"]
theorem isKoszulRegularImmersion_iff_of_fpqcZeroHypercover
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (𝒰 : Precoverage.ZeroHypercover.{w} Scheme.fpqcPrecoverage X) :
    IsKoszulRegularImmersion i ↔ ∀ k, IsKoszulRegularImmersion (pullback.snd i (𝒰.f k)) := by
  have key := immersionProperty_iff_of_fpqcZeroHypercover
    (Seq := fun f => Koszul.IsKoszulRegular f)
    (Pred := fun i => IsKoszulRegularImmersion i)
    isKoszulRegular_of_ringHomFlat
    (by intro A B _ _ φ hφ I h; exact (Koszul.regular_ideals_of_faithfullyFlat φ hφ I).1 h)
    (by
      intro Z X i _ V jV _ hij
      exact (isKoszulRegularImmersion_iff_of_open i V jV hij).trans
        (isKoszulRegularIdealSheaf_iff_kerGeneratedBy jV))
    isKoszulRegularImmersion_of_resLE i inferInstance 𝒰
  exact pred_iff_of_immersionProperty_iff i 𝒰 key

/-- **Stacks Project, Tag 0694, the `H₁`-regular clause, for an immersion.** An immersion of
schemes is `H₁`-regular if and only if its base changes along the members of an fpqc covering of
the target are, with no quasi-compactness. -/
@[stacks 0694 "h1_regular, erratum: morphisms that are immersions; fpqc, no quasi-compactness"]
theorem isH1RegularImmersion_iff_of_fpqcZeroHypercover
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (𝒰 : Precoverage.ZeroHypercover.{w} Scheme.fpqcPrecoverage X) :
    IsH1RegularImmersion i ↔ ∀ k, IsH1RegularImmersion (pullback.snd i (𝒰.f k)) := by
  have key := immersionProperty_iff_of_fpqcZeroHypercover
    (Seq := fun f => Koszul.IsH1Regular f)
    (Pred := fun i => IsH1RegularImmersion i)
    isH1Regular_of_ringHomFlat
    (by intro A B _ _ φ hφ I h; exact (Koszul.regular_ideals_of_faithfullyFlat φ hφ I).2.1 h)
    (by
      intro Z X i _ V jV _ hij
      exact (isH1RegularImmersion_iff_of_open i V jV hij).trans
        (isH1RegularIdealSheaf_iff_kerGeneratedBy jV))
    isH1RegularImmersion_of_resLE i inferInstance 𝒰
  exact pred_iff_of_immersionProperty_iff i 𝒰 key

/-- **Stacks Project, Tag 0694, the quasi-regular clause, for an immersion.** An immersion of
schemes is quasi-regular if and only if its base changes along the members of an fpqc covering of
the target are, with no quasi-compactness. -/
@[stacks 0694 "quasi_regular, erratum: morphisms that are immersions; fpqc, no quasi-compactness",
  ega "IV 19.1.5" "more general"]
theorem isQuasiRegularImmersion_iff_of_fpqcZeroHypercover
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (𝒰 : Precoverage.ZeroHypercover.{w} Scheme.fpqcPrecoverage X) :
    RegularIdealSheaf.IsQuasiRegularImmersion i ↔
      ∀ k, RegularIdealSheaf.IsQuasiRegularImmersion (pullback.snd i (𝒰.f k)) := by
  have key := immersionProperty_iff_of_fpqcZeroHypercover
    (Seq := fun {A} _ _ f => RingTheory.Sequence.IsQuasiRegular A (List.ofFn f))
    (Pred := fun i => RegularIdealSheaf.IsQuasiRegularImmersion i)
    isQuasiRegular_of_ringHomFlat
    (by
      intro A B _ _ φ hφ I h
      exact (Ideal.isQuasiregularIdeal_iff_isLocallySpannedBy I).mp
        ((Koszul.regular_ideals_of_faithfullyFlat φ hφ I).2.2
          ((Ideal.isQuasiregularIdeal_iff_isLocallySpannedBy (I.map φ)).mpr h)))
    (by
      intro Z X i _ V jV _ hij
      exact (RegularIdealSheaf.isQuasiRegularImmersion_iff_of_open i V jV hij).trans
        (isQuasiRegularIdealSheaf_iff_kerGeneratedBy jV))
    RegularIdealSheaf.isQuasiRegularImmersion_of_resLE i inferInstance 𝒰
  exact pred_iff_of_immersionProperty_iff i 𝒰 key

end AlgebraicGeometry

end
