module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.RegularImmersion
public import StacksCore.Tactic.StacksAttribute

/-!
# The regularity conditions on an immersion are fppf local on the target

Let `i : Z ⟶ X` be a morphism of schemes. Stacks tag 0694 asserts that each of the three
conditions Koszul-regular, `H₁`-regular and quasi-regular of Stacks tag 063J is local on the
target for the fpqc topology, with no hypothesis whatever on `i`: by Stacks tag 02KO, "local on
the base" is an equivalence quantified over *every* morphism to the base and every covering.

Read that way the tag is **false**, and this file proves the sharpest statement that is true: the
same three clauses for the **fppf** topology, with no quasi-compactness and no hypothesis that
`i` is an immersion. Since an fppf covering is an fpqc covering, this is the strongest weakening
of the tag which shrinks only the topology, and the counterexample shows the topology cannot be
enlarged back to fpqc; so the single point at which the tag fails is isolated exactly.

The reason the fppf statement holds and the fpqc one does not is one ingredient only. Each of the
three conditions entails being an immersion, so the tag contains the descent of the property of
being an immersion. A member of an fppf covering is flat and locally of finite presentation,
hence an open map, and local closedness of a subset descends along an open surjection; this is
Stacks tag 02YM, `Stacks.Descent.isImmersion_descendsAlong_fppf`. A member of an fpqc covering is
flat and quasi-compact but need not be open, and that descent fails: Stacks tag 02YL, the section
in which 02YM sits, collects the properties the Stacks Project "could not (yet)" show fpqc local
on the base, and being an immersion is the first of them. The module docstring of
`StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.RegularImmersionFpqcOfImmersion` has the
counterexample, and
`StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.RegularImmersionFpqcCounterexample`
formalizes the parts of it that do not need infinite coproducts of schemes.

Every other ingredient of the argument is already free of quasi-compactness, because the affine
criteria of Stacks tags 063D and 063G are applied to the canonical *closed* factor of the
immersion, and a closed immersion is affine, hence quasi-compact, whatever the immersion it
factors.

## Main results

* `AlgebraicGeometry.exists_surjective_flat_lfp_onto_openImage`: a flat morphism locally of finite
  presentation factors as a surjective such morphism onto the open subscheme which is its image.
* `AlgebraicGeometry.isLocalAtTarget_fppfPrecoverage_of_descendsAlong_fppf`: a property of
  morphisms of schemes which is Zariski local on the target, stable under flat base change and
  descends along surjective flat morphisms locally of finite presentation is fppf local on the
  target. This is the fppf case of Stacks tag 02KP with the base-change hypothesis weakened to
  flat base change, which is all that the regularity conditions satisfy.
* `AlgebraicGeometry.isLocalAtTarget_immersionProperty_fppf`: the uniform form of Stacks tag 0694
  for the fppf topology.
* `AlgebraicGeometry.isLocalAtTarget_koszulRegularImmersion_fppf`,
  `AlgebraicGeometry.isLocalAtTarget_h1RegularImmersion_fppf` and
  `AlgebraicGeometry.isLocalAtTarget_quasiRegularImmersion_fppf`: **Stacks tag 0694** for the fppf
  topology, the three clauses, each for the bare regularity condition.

## Implementation notes

The criterion `AlgebraicGeometry.isLocalAtTarget_fppfPrecoverage_of_descendsAlong_fppf` is the
fppf analogue of `AlgebraicGeometry.isLocalAtTarget_etalePrecoverage_of_descendsAlong_fppf` and
its proof is the same: a member of the covering family is factored through the open subscheme
which is its image, the opens so obtained cover the target because the family is jointly
surjective, and over each of them the surjective flat morphism locally of finite presentation is
removed by the descent hypothesis. What makes the factorization available is that a flat morphism
locally of finite presentation is universally open, so its image is open.

It is *not* an instance of `Stacks.Descent.isLocalAtTarget_fppfPrecoverage_of_descendsAlong`,
which asks for stability under arbitrary base change. None of the three conditions has that:
being a Koszul-regular immersion is preserved under *flat* base change only (Divisors, Lemma
31.22.4). The hypothesis is weakened here to
`Stacks.Descent.IsStableUnderFlatBaseChange`, which suffices because every morphism one base
changes along in the proof — a member of an fppf covering, and the inclusion of an open — is
flat.

The descent hypothesis is supplied by
`AlgebraicGeometry.immersionProperty_descendsAlong_fppf`, which is already stated with no
quasi-compactness and no hypothesis that the morphism is an immersion: it recovers the latter from
Stacks tag 02YM.

## References

* [Stacks Project, Lemma 35.23.34 (Tag 0694)](https://stacks.math.columbia.edu/tag/0694)
* [Stacks Project, Definition 35.22.1 (Tag 02KO)](https://stacks.math.columbia.edu/tag/02KO)
* [Stacks Project, Lemma 35.22.4 (Tag 02KP)](https://stacks.math.columbia.edu/tag/02KP)
* [Stacks Project, Section 35.24 (Tag 02YL)](https://stacks.math.columbia.edu/tag/02YL)
* [Stacks Project, Lemma 35.24.1 (Tag 02YM)](https://stacks.math.columbia.edu/tag/02YM)
* [Stacks Project, Definition 31.22.1 (Tag 063J)](https://stacks.math.columbia.edu/tag/063J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MorphismProperty
open Stacks.AlgebraicGeometry
open Stacks.AlgebraicGeometry.RegularIdealSheaf

namespace AlgebraicGeometry

universe u

/-! ### Upgrading Zariski locality to fppf locality through fppf descent -/

/-- A flat morphism locally of finite presentation factors as a surjective flat morphism locally
of finite presentation onto the open subscheme which is its image, followed by the inclusion of
that open subscheme. The image is open because such a morphism is universally open. -/
theorem exists_surjective_flat_lfp_onto_openImage
    {V X : Scheme.{u}} (g : V ⟶ X) [Flat g] [LocallyOfFinitePresentation g] :
    ∃ (O : X.Opens) (gO : V ⟶ O.toScheme),
      (∀ x : X, x ∈ Set.range g.base → x ∈ O) ∧
        Surjective gO ∧ Flat gO ∧ LocallyOfFinitePresentation gO ∧ gO ≫ O.ι = g := by
  let O : X.Opens := ⟨Set.range g.base, g.isOpenMap.isOpen_range⟩
  have hgRange : (⊤ : V.Opens) ≤ g ⁻¹ᵁ O := fun y _ => ⟨y, rfl⟩
  let gO : V ⟶ O.toScheme := V.topIso.inv ≫ g.resLE O ⊤ hgRange
  have hgOι : gO ≫ O.ι = g := by
    change V.topIso.inv ≫ (g.resLE O ⊤ hgRange ≫ O.ι) = g
    rw [Scheme.Hom.resLE_comp_ι, ← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp]
  have hflat : Flat gO := by
    dsimp only [gO]
    infer_instance
  have hlfp : LocallyOfFinitePresentation gO := by
    dsimp only [gO]
    infer_instance
  have hsurj : Surjective gO := by
    refine ⟨fun z => ?_⟩
    obtain ⟨y, hy⟩ := z.2
    exact ⟨y, Subtype.ext ((congrArg (fun a : V ⟶ X => a y) hgOι).trans hy)⟩
  exact ⟨O, gO, fun _ hx => hx, hsurj, hflat, hlfp, hgOι⟩

/-- **Stacks Project, Tag 02KP** for the fppf topology, with the base-change hypothesis weakened
to flat base change. A property of morphisms of schemes which is Zariski local on the target,
stable under flat base change and descends along surjective flat morphisms locally of finite
presentation is fppf local on the target.

This is the fppf analogue of
`AlgebraicGeometry.isLocalAtTarget_etalePrecoverage_of_descendsAlong_fppf`: a member of an fppf
covering family is flat and locally of finite presentation, hence universally open, so it factors
as a surjective morphism of the same kind onto the open subscheme which is its image; the opens
so obtained cover the target, and over each of them the descent hypothesis removes the covering
morphism.

Unlike `Stacks.Descent.isLocalAtTarget_fppfPrecoverage_of_descendsAlong` this does not ask for
stability under arbitrary base change, which the regularity conditions on immersions do not
have. -/
theorem isLocalAtTarget_fppfPrecoverage_of_descendsAlong_fppf (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P] [Stacks.Descent.IsStableUnderFlatBaseChange P]
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)] :
    MorphismProperty.IsLocalAtTarget P Scheme.fppfPrecoverage := by
  refine MorphismProperty.IsLocalAtTarget.mk_of_iff fun X Y f R hR =>
    ⟨fun hf U g hg _ => ?_, fun h => ?_⟩
  · have hg' : (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) g := hR.2 ‹_›
    have _ : Flat g := hg'.1
    exact (Stacks.Descent.IsStableUnderFlatBaseChange.isStableUnderBaseChangeAlong
      (P := P) g).of_isPullback (IsPullback.of_hasPullback f g) hf
  · obtain ⟨ι, Z, fam, rfl⟩ := R.exists_eq_ofArrows
    have hR' : Presieve.ofArrows Z fam ∈
        Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u})
          Y := hR
    obtain ⟨hjs, hfam⟩ := Iff.mp (Scheme.ofArrows_mem_precoverage_iff _) hR'
    choose j hj using hjs
    refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := P) fun y => ?_
    have _ : Flat (fam (j y)) := (hfam (j y)).1
    have _ : LocallyOfFinitePresentation (fam (j y)) := (hfam (j y)).2
    obtain ⟨O, gO, hmem, hsurjO, hflatO, hlfpO, hfac⟩ :=
      exists_surjective_flat_lfp_onto_openImage (fam (j y))
    refine ⟨O, hmem y (hj y), ?_⟩
    have htot : IsPullback (pullback.snd f (fam (j y))) (pullback.fst f (fam (j y)))
        (gO ≫ O.ι) f := by
      rw [hfac]
      exact (IsPullback.of_hasPullback f (fam (j y))).flip
    have hsnd : P (pullback.snd f O.ι) :=
      MorphismProperty.of_isPullback_of_descendsAlong
        (Q := (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}))
        (IsPullback.of_bot' htot (IsPullback.of_hasPullback f O.ι).flip) ⟨⟨hsurjO, hflatO⟩, hlfpO⟩
        (h _ ⟨j y⟩)
    have hres : P (f ∣_ O.ι.opensRange) :=
      (MorphismProperty.arrow_mk_iso_iff P (morphismRestrictOpensRange f O.ι)).mpr hsnd
    rwa [Scheme.Opens.opensRange_ι] at hres

/-! ### The regularity conditions, with no quasi-compactness and no immersion hypothesis -/

variable {Seq : ∀ {A : Type u} [CommRing A] {r : ℕ}, (Fin r → A) → Prop}
variable {Pred : ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i], Prop}

/-- **The uniform form of Stacks tag 0694 for the fppf topology.** A condition on immersions that
is read off the kernel of a closed factor through any open in which the immersion is closed, whose
family predicate is stable under flat ring maps and whose ideal-theoretic form descends along
faithfully flat ring maps, and which glues along open covers of the target, is fppf local on the
target — with no quasi-compactness and no hypothesis that the morphism is an immersion.

This is the strongest form of the tag that is true. The tag asserts the same for the fpqc
topology, which is false; see the module docstring. -/
theorem isLocalAtTarget_immersionProperty_fppf
    (hSeq : ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B), φ.Flat →
      ∀ {r : ℕ} (f : Fin r → A), Seq f → Seq fun i => φ (f i))
    (hdesc : ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B), φ.FaithfullyFlat →
      ∀ I : Ideal A, (I.map φ).IsLocallySpannedBy Seq → I.IsLocallySpannedBy Seq)
    (hPred : ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (V : X.Opens)
      (jV : Z ⟶ V.toScheme) [IsClosedImmersion jV], jV ≫ V.ι = i →
        (Pred i ↔ KerGeneratedBy Seq jV))
    (hglue : ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] {ι : Type u} (V : ι → X.Opens),
      iSup V = ⊤ → (∀ k, Pred (i.resLE (V k) (i ⁻¹ᵁ V k) le_rfl)) → Pred i) :
    MorphismProperty.IsLocalAtTarget (immersionProperty Pred) Scheme.fppfPrecoverage := by
  have _ := immersionProperty_respectsIso hSeq hPred (Pred := Pred)
  have _ := immersionProperty_isStableUnderFlatBaseChange hSeq hPred (Pred := Pred)
  have _ := immersionProperty_isZariskiLocalAtTarget hSeq hPred hglue (Pred := Pred)
  have _ := immersionProperty_descendsAlong_fppf hSeq hdesc hPred hglue (Pred := Pred)
  exact isLocalAtTarget_fppfPrecoverage_of_descendsAlong_fppf _

/-! ### The three clauses of Stacks tag 0694 for the fppf topology -/

/-- **Stacks Project, Tag 0694, the Koszul-regular clause, for the fppf topology.** Being a
Koszul-regular immersion of schemes is local on the target for the fppf topology, with no
quasi-compactness and no hypothesis that the morphism is an immersion.

The tag asserts this for the fpqc topology, where it is false. -/
@[stacks 0694 "koszul_regular, erratum: fppf in place of fpqc; \
    counterexample Stacks.Descent.counterexampleHom",
  sga "6 VII 1.5" "special case"]
theorem isLocalAtTarget_koszulRegularImmersion_fppf :
    MorphismProperty.IsLocalAtTarget
      (fun _ _ f => ∃ hf : IsImmersion f, @IsKoszulRegularImmersion _ _ f hf)
      Scheme.fppfPrecoverage.{u} :=
  isLocalAtTarget_immersionProperty_fppf
    (Seq := fun f => Koszul.IsKoszulRegular f)
    (Pred := fun i => IsKoszulRegularImmersion i)
    isKoszulRegular_of_ringHomFlat
    (fun φ hφ I => (Koszul.regular_ideals_of_faithfullyFlat φ hφ I).1)
    (fun i _ V jV _ hij => (isKoszulRegularImmersion_iff_of_open i V jV hij).trans
      (isKoszulRegularIdealSheaf_iff_kerGeneratedBy jV))
    isKoszulRegularImmersion_of_resLE

/-- **Stacks Project, Tag 0694, the `H₁`-regular clause, for the fppf topology.** Being an
`H₁`-regular immersion of schemes is local on the target for the fppf topology, with no
quasi-compactness and no hypothesis that the morphism is an immersion.

The tag asserts this for the fpqc topology, where it is false. -/
@[stacks 0694
    "h1_regular, erratum: fppf in place of fpqc; counterexample Stacks.Descent.counterexampleHom"]
theorem isLocalAtTarget_h1RegularImmersion_fppf :
    MorphismProperty.IsLocalAtTarget
      (fun _ _ f => ∃ hf : IsImmersion f, @IsH1RegularImmersion _ _ f hf)
      Scheme.fppfPrecoverage.{u} :=
  isLocalAtTarget_immersionProperty_fppf
    (Seq := fun f => Koszul.IsH1Regular f)
    (Pred := fun i => IsH1RegularImmersion i)
    isH1Regular_of_ringHomFlat
    (fun φ hφ I => (Koszul.regular_ideals_of_faithfullyFlat φ hφ I).2.1)
    (fun i _ V jV _ hij => (isH1RegularImmersion_iff_of_open i V jV hij).trans
      (isH1RegularIdealSheaf_iff_kerGeneratedBy jV))
    isH1RegularImmersion_of_resLE

/-- **Stacks Project, Tag 0694, the quasi-regular clause, for the fppf topology.** Being a
quasi-regular immersion of schemes is local on the target for the fppf topology, with no
quasi-compactness and no hypothesis that the morphism is an immersion.

The tag asserts this for the fpqc topology, where it is false. -/
@[stacks 0694 "quasi_regular, erratum: fppf in place of fpqc; \
    counterexample Stacks.Descent.counterexampleHom",
  ega "IV 19.1.5" "(ii), special case"]
theorem isLocalAtTarget_quasiRegularImmersion_fppf :
    MorphismProperty.IsLocalAtTarget
      (fun _ _ f => ∃ hf : IsImmersion f,
        @RegularIdealSheaf.IsQuasiRegularImmersion _ _ f hf)
      Scheme.fppfPrecoverage.{u} :=
  isLocalAtTarget_immersionProperty_fppf
    (Seq := fun {A} _ _ f => RingTheory.Sequence.IsQuasiRegular A (List.ofFn f))
    (Pred := fun i => RegularIdealSheaf.IsQuasiRegularImmersion i)
    isQuasiRegular_of_ringHomFlat
    (fun φ hφ I h => (Ideal.isQuasiregularIdeal_iff_isLocallySpannedBy I).mp
      ((Koszul.regular_ideals_of_faithfullyFlat φ hφ I).2.2
        ((Ideal.isQuasiregularIdeal_iff_isLocallySpannedBy (I.map φ)).mpr h)))
    (fun i _ V jV _ hij =>
      (RegularIdealSheaf.isQuasiRegularImmersion_iff_of_open i V jV hij).trans
        (isQuasiRegularIdealSheaf_iff_kerGeneratedBy jV))
    RegularIdealSheaf.isQuasiRegularImmersion_of_resLE

end AlgebraicGeometry

end
