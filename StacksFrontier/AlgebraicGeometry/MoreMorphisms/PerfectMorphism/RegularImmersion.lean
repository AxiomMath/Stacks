module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.AffineLocal
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.Composition
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.Flat
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.Implications
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.KoszulRegularSmoothCover
public import StacksFrontier.RingTheory.PseudoCoherentMap.CompleteIntersection
public import StacksCore.Tactic.StacksAttribute

/-!
# Regular immersions are perfect

A Koszul-regular immersion of schemes is a perfect morphism, and hence so is a regular immersion:
this is **Stacks 068C**.

## Main results

* `AlgebraicGeometry.perfect_of_isKoszulRegularImmersion`: a Koszul-regular immersion of schemes
  is perfect.
* `AlgebraicGeometry.perfect_of_isRegularImmersion`: a regular immersion of schemes is perfect.

## Implementation notes

An immersion factors as the closed immersion `i.liftCoborder` into the open subscheme
`i.coborderRange` followed by the open immersion `i.coborderRange.ι`, and Koszul-regularity of
`i` is by definition Koszul-regularity of the defining ideal sheaf of that closed factor. The
open immersion is flat and locally of finite presentation, hence perfect by Stacks 068A, and
perfectness is stable under composition by Stacks 0689, so everything reduces to the closed
factor.

For a closed immersion `j : X ⟶ Y` with Koszul-regular defining ideal sheaf, perfectness is
checked on an open cover of `Y`: it is local on the target, and over an affine open whose
preimage is affine it is perfectness of the map on sections, because perfectness is the
affine-local property attached to `RingHom.Perfect` (`AlgebraicGeometry.hasRingHomProperty_perfect`,
read through Mathlib's `AlgebraicGeometry.IsZariskiLocalAtTarget.of_iSup_eq_top` and
`AlgebraicGeometry.HasRingHomProperty.of_iSup_eq_top`; this is Stacks 0686). The cover is assembled
from two kinds of affine opens: those missing the image of `j`, over which the preimage is empty,
so that the restriction of `j` is an open immersion, perfect by Stacks 068A, and those supplied by
the affine criterion of Stacks 063G in the form of
`Stacks.AlgebraicGeometry.exists_affine_koszul_kernel`, over which the kernel on sections is
spanned by a Koszul-regular family. Together these two families cover `Y`, because the image of a
closed immersion is closed. Over an affine open `V` of the second kind the preimage `j ⁻¹ᵁ V` is
affine, `Γ(Y, V) ⟶ Γ(X, j ⁻¹ᵁ V)` is surjective, and its kernel is spanned by a Koszul-regular
family, so it is a local complete intersection homomorphism through the presentation with no
variables; Stacks 07EN then makes it a perfect ring map.

That the presentation with no variables is admissible uses that `A` is the localization of
`MvPolynomial (Fin 0) A` away from `1`, which turns transport of Koszul-regularity across the
canonical isomorphism into
`Stacks.RingTheory.KoszulRegularIdealSheaf.isKoszulRegular_localization`.

## References

* [The Stacks Project, Lemma 37.61.5 (068C)](https://stacks.math.columbia.edu/tag/068C)
* [The Stacks Project, Lemma 37.61.1 (0686)](https://stacks.math.columbia.edu/tag/0686)
* [The Stacks Project, Lemma 37.61.4 (068A)](https://stacks.math.columbia.edu/tag/068A)
* [The Stacks Project, Lemma 37.61.2 (0689)](https://stacks.math.columbia.edu/tag/0689)
* [The Stacks Project, Lemma 15.83.17 (07EN)](https://stacks.math.columbia.edu/tag/07EN)
* [The Stacks Project, Definition 31.21.4 (063J)](https://stacks.math.columbia.edu/tag/063J)
-/

public section

open CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace AlgebraicGeometry

/-- A surjective ring homomorphism whose kernel is spanned by a Koszul-regular family is a local
complete intersection homomorphism.

The presentation witnessing this uses no variables: the target is the quotient of the source by a
Koszul-regular ideal, so `MvPolynomial (Fin 0) A ⟶ B` already is a finite polynomial
presentation, and its kernel is the image of the original kernel under the canonical isomorphism
`A ≃ MvPolynomial (Fin 0) A`. That isomorphism exhibits `MvPolynomial (Fin 0) A` as the
localization of `A` away from `1`, which is how Koszul-regularity is transported along it. -/
private theorem isLocalCompleteIntersection_of_ker_eq_span_range
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (hφ : Function.Surjective φ)
    {r : ℕ} (f : Fin r → A) (hf : Koszul.IsKoszulRegular f)
    (hker : RingHom.ker φ = Ideal.span (Set.range f)) :
    RingHom.IsLocalCompleteIntersection φ := by
  let : Algebra A B := φ.toAlgebra
  let e : MvPolynomial (Fin 0) A ≃ₐ[A] A := MvPolynomial.isEmptyAlgEquiv A (Fin 0)
  let p : MvPolynomial (Fin 0) A →ₐ[A] B := (Algebra.ofId A B).comp e.toAlgHom
  have hpcomp : p.toRingHom = φ.comp (e.toRingEquiv : MvPolynomial (Fin 0) A →+* A) := rfl
  have hcomm : ∀ a : A, e (algebraMap A (MvPolynomial (Fin 0) A) a) = a :=
    fun a => by simpa using e.commutes a
  have hinv : ∀ x : MvPolynomial (Fin 0) A,
      x = algebraMap A (MvPolynomial (Fin 0) A) (e x) :=
    fun x => e.injective (hcomm (e x)).symm
  have hp : Function.Surjective p := by
    intro b
    obtain ⟨a, ha⟩ := hφ b
    exact ⟨algebraMap A (MvPolynomial (Fin 0) A) a, by
      simpa [p, Algebra.ofId, RingHom.algebraMap_toAlgebra, hcomm a] using ha⟩
  have hkerp : RingHom.ker p.toRingHom
      = Ideal.span (Set.range fun i => algebraMap A (MvPolynomial (Fin 0) A) (f i)) := by
    have hspan : Ideal.span (Set.range fun i => algebraMap A (MvPolynomial (Fin 0) A) (f i))
        = Ideal.map (algebraMap A (MvPolynomial (Fin 0) A)) (Ideal.span (Set.range f)) := by
      rw [Ideal.map_span, ← Set.range_comp]
      rfl
    rw [hpcomp, ← RingHom.comap_ker, hker, hspan]
    refine le_antisymm (fun x hx => ?_) ?_
    · rw [hinv x]
      exact Ideal.mem_map_of_mem _ hx
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      simp only [Ideal.mem_comap]
      rwa [show (e.toRingEquiv : MvPolynomial (Fin 0) A →+* A)
        (algebraMap A (MvPolynomial (Fin 0) A) a) = a from hcomm a]
  have hloc : IsLocalization.Away (1 : A) (MvPolynomial (Fin 0) A) :=
    IsLocalization.away_of_isUnit_of_bijective _ isUnit_one
      ⟨fun x y h => by simpa [hcomm] using congrArg e h, fun x => ⟨e x, (hinv x).symm⟩⟩
  have hfP : Koszul.IsKoszulRegular fun i => algebraMap A (MvPolynomial (Fin 0) A) (f i) :=
    Stacks.RingTheory.KoszulRegularIdealSheaf.isKoszulRegular_localization
      (Submonoid.powers (1 : A)) (MvPolynomial (Fin 0) A) f hf
  refine ⟨by
    rw [RingHom.FiniteType]
    exact Algebra.FiniteType.of_surjective (Algebra.ofId A B) hφ, 0, p, hp, ?_⟩
  rw [hkerp]
  intro q _
  refine ⟨1, q.isPrime.one_notMem, r,
    fun i => algebraMap (MvPolynomial (Fin 0) A)
      (Localization.Away (1 : MvPolynomial (Fin 0) A))
      (algebraMap A (MvPolynomial (Fin 0) A) (f i)), ?_, ?_⟩
  · exact Stacks.RingTheory.KoszulRegularIdealSheaf.isKoszulRegular_localization
      (Submonoid.powers (1 : MvPolynomial (Fin 0) A))
      (Localization.Away (1 : MvPolynomial (Fin 0) A)) _ hfP
  · rw [Ideal.map_span, ← Set.range_comp]
    rfl

/-- A closed immersion of schemes whose defining ideal sheaf is Koszul-regular is perfect.

Perfectness is local on the target and is tested on an affine open cover of it. Over an affine
open missing the image of the immersion the restriction has empty source, so it is an open
immersion, perfect by Stacks 068A; over one of the affine opens produced by the affine criterion of
Stacks 063G the preimage is affine and the map on sections is surjective with kernel spanned by a
Koszul-regular family, hence a local complete intersection homomorphism, hence a perfect ring map
by Stacks 07EN. -/
@[sga "6 III 1.1.2",
  sga "6 III 4.1.1" "special case",
  sga "6 VII 1.9",
  sga "6 VIII 1.7" "special case",
  sga "6 X 7.1" "more general",
  sga "6 X 7.12" "partial"]
private theorem perfect_of_isKoszulRegularIdealSheaf_definingIdealOfHom {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsClosedImmersion j]
    (hj : IsKoszulRegularIdealSheaf Y.toRingedSpace (definingIdealOfHom j)) :
    Perfect j := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @Perfect)
    (fun V : {V : Y.affineOpens // j ⁻¹ᵁ V.1 = ⊥ ∨
      ∃ (r : ℕ) (f : Fin r → Γ(Y, V.1)), Koszul.IsKoszulRegular f ∧
        RingHom.ker (j.app V.1).hom = Ideal.span (Set.range f)} => V.1.1) ?_ ?_
  · refine le_antisymm le_top fun y _ => ?_
    rw [Opens.mem_iSup]
    by_cases hy : y ∈ Set.range j.base
    · obtain ⟨z, rfl⟩ := hy
      obtain ⟨V, hzV, r, f, hf, hker, -⟩ :=
        _root_.Stacks.AlgebraicGeometry.exists_affine_koszul_kernel j hj z
      exact ⟨⟨V, Or.inr ⟨r, f, hf, hker⟩⟩, hzV⟩
    · obtain ⟨-, ⟨V, hV, rfl⟩, hyV, hVsub⟩ :=
        Y.isBasis_affineOpens.exists_subset_of_mem_open hy
          j.isClosedEmbedding.isClosed_range.isOpen_compl
      refine ⟨⟨⟨V, hV⟩, Or.inl ?_⟩, hyV⟩
      refine le_antisymm (fun x hx => ?_) bot_le
      exact absurd (Set.mem_range_self x) (hVsub hx)
  · rintro ⟨V, hVbot | ⟨r, f, hf, hker⟩⟩
    · have : IsEmpty (j ⁻¹ᵁ V.1).toScheme :=
        ⟨fun x => by simpa [hVbot] using (j ⁻¹ᵁ V.1).range_ι.le ⟨x, rfl⟩⟩
      infer_instance
    · have : IsAffine (j ⁻¹ᵁ V.1) := V.2.preimage j
      refine HasRingHomProperty.of_iSup_eq_top (P := @Perfect)
        (fun _ : PUnit.{u + 1} => ⟨⊤, isAffineOpen_top _⟩) iSup_const fun _ => ?_
      refine (congrArg (fun φ => φ.hom.Perfect)
        (morphismRestrict_appLE j V.1 ⊤ ⊤ le_top)).mpr ?_
      refine (j.appLE_congr _ V.1.ι_image_top (j ⁻¹ᵁ V.1).ι_image_top
        fun φ => φ.hom.Perfect).mpr ?_
      have happ : j.appLE V.1 (j ⁻¹ᵁ V.1) le_rfl = j.app V.1 :=
        Scheme.Hom.appLE_eq_app j
      have hsurj : Function.Surjective (j.appLE V.1 (j ⁻¹ᵁ V.1) le_rfl).hom := by
        rw [happ]
        exact j.app_surjective V.1 V.2
      have hker' : RingHom.ker (j.appLE V.1 (j ⁻¹ᵁ V.1) le_rfl).hom
          = Ideal.span (Set.range f) := by rwa [happ]
      exact (isLocalCompleteIntersection_of_ker_eq_span_range _ hsurj f hf hker').perfect

/-- **Stacks 068C.** A Koszul-regular immersion of schemes is a perfect morphism.

The immersion factors as its closed factor into the canonical open, whose defining ideal sheaf is
Koszul-regular by definition, followed by an open immersion, which is flat and locally of finite
presentation and hence perfect by Stacks 068A; perfectness composes by Stacks 0689. -/
@[stacks 068C "Koszul-regular immersion",
  sga "6 III 4.1.1" "reg. immersion perfect",
  sga "6 III 1.1.2",
  sga "6 VII 1.9" "more general",
  sga "6 VIII 1.7" "special case",
  sga "6 X 7.1" "partial"]
theorem perfect_of_isKoszulRegularImmersion {X S : Scheme.{u}} (i : X ⟶ S) [IsImmersion i]
    (hi : IsKoszulRegularImmersion i) : Perfect i := by
  have h := @perfect_comp _ _ _ i.liftCoborder i.coborderRange.ι
    (perfect_of_isKoszulRegularIdealSheaf_definingIdealOfHom i.liftCoborder hi) inferInstance
  rwa [i.liftCoborder_ι] at h

/-- **Stacks 068C.** A regular immersion of schemes is a perfect morphism, because a regular
immersion is Koszul-regular by Stacks 063K. -/
@[stacks 068C "regular immersion",
  sga "6 III 4.1.1" "reg. immersion perfect",
  sga "6 III 1.1.2",
  sga "6 VIII 1.7" "special case",
  sga "6 X 7.1" "partial"]
theorem perfect_of_isRegularImmersion {X S : Scheme.{u}} (i : X ⟶ S) [IsImmersion i]
    (hi : IsRegularImmersion i) : Perfect i :=
  perfect_of_isKoszulRegularImmersion i (isKoszulRegularImmersion_of_isRegularImmersion i hi)

end AlgebraicGeometry

end
