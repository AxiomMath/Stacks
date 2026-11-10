module

public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.PrimePowerAlg
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.SquareCubeAlg
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.SpecialElement
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.TwoOutOfThree
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.Ring
public import StacksFrontier.AlgebraicGeometry.Seminormalization.CandidatePresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.WeakNormalization.RingUniversalProperty

/-!
# When an algebra is the absolute weak normalization of its base

Let `A` be a commutative ring. A terminal object of the category of `A`-algebras whose spectrum
morphism to `Spec A` is a universal homeomorphism is an absolutely weakly normal ring, and
conversely an absolutely weakly normal such algebra is terminal, that is the canonical map
from it to `Algebra.AbsoluteWeakNormalization A` is an isomorphism.

## Main results

* `Algebra.existsUnique_sq_cube_of_isTerminal` and
  `Algebra.existsUnique_pow_mul_of_isTerminal`: in a terminal object of a full subcategory of
  `CommAlgCat A` closed under the two root adjunctions of Tag 0EUI, the two defining unique-root
  conditions of absolute weak normality hold.
* `Algebra.isAbsolutelyWeaklyNormalRing_of_isTerminal`: a terminal object of
  `Algebra.AbsoluteWeakNormalizationCategory A` is absolutely weakly normal.
* `Algebra.isIso_toAbsoluteWeakNormalization_iff_isAbsolutelyWeaklyNormalRing`: the canonical
  map from a universal-homeomorphism `A`-algebra to the absolute weak normalization of `A` is
  an isomorphism exactly when that algebra is absolutely weakly normal.

## Implementation notes

The two unique-root statements are one argument carried out twice, for the two algebras
`R[t]/(t² - x, t³ - y)` and `R[t]/(tᵖ - x, pt - y)` of Tag 0EUI: in both cases the terminal
object receives the root algebra, the structure map back is a retraction of the inclusion, and
the image of `t` is the required root; uniqueness comes from the evaluation map at any other
root, which is a second morphism to the terminal object. They are stated for an arbitrary
object property on `CommAlgCat A` so that both the absolute weak normalization and the
seminormalization category can use them.

The converse direction is Tag 0CNC: if the canonical map `B → Aᵃʷⁿ` were not surjective its
image would be a proper subring with a universal homeomorphism on spectra, hence would contain a
square-and-cube or prime-power special element, and the uniqueness clauses of absolute weak
normality of `B` and of `Aᵃʷⁿ` force that element into the image. Injectivity is reducedness of
`B` together with dominance of the map on spectra.

Everything lives in a single universe `u`, as `AlgebraicGeometry.UniversalHomeomorphism` is
available only for `Scheme.{u}`.

## References

* [Stacks Project, Tag 0EUR](https://stacks.math.columbia.edu/tag/0EUR)
* [Stacks Project, Tag 0EUI](https://stacks.math.columbia.edu/tag/0EUI)
* [Stacks Project, Tag 0CNC](https://stacks.math.columbia.edu/tag/0CNC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

universe u

namespace Algebra

/-! ### Unique roots in a terminal object -/

/-- If `Spec R ⟶ Spec A` and `Spec S ⟶ Spec R` are universal homeomorphisms in a tower of
algebras, so is `Spec S ⟶ Spec A`. -/
theorem universalHomeomorphism_specMap_tower (A R S : Type u) [CommRing A] [CommRing R]
    [CommRing S] [Algebra A R] [Algebra R S] [Algebra A S] [IsScalarTower A R S]
    (hAR : UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A R))))
    (hRS : UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap R S)))) :
    UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A S))) :=
  universalHomeomorphism_specMap_comp_algHom ((Algebra.ofId R S).restrictScalars A) hAR hRS

/-- The square-cube root algebra of Tag 0EUI over a universal-homeomorphism `A`-algebra is
again a universal homeomorphism over `A`. -/
theorem isAbsoluteWeakNormalizationCandidate_squareCubeAlgebra (A R : Type u) [CommRing A]
    [CommRing R] [Algebra A R] (x y : R) (hxy : x ^ 3 = y ^ 2)
    (hR : IsAbsoluteWeakNormalizationCandidate A (CommAlgCat.of A R)) :
    IsAbsoluteWeakNormalizationCandidate A (CommAlgCat.of A (SquareCubeAlgebra R x y)) :=
  universalHomeomorphism_specMap_tower A R _ hR
    (squareCubeSpecMap_universalHomeomorphism R x y hxy)

/-- In a terminal object of a full subcategory of `CommAlgCat A` which contains the quotient of the
polynomial ring by `(f, g)`, the polynomials `f, g` have a unique common root. -/
private theorem existsUnique_aeval_eq_zero_of_isTerminal (A : Type u) [CommRing A]
    (P : ObjectProperty (CommAlgCat.{u} A)) (R : P.FullSubcategory) (hR : IsTerminal R)
    (f g : Polynomial (R.obj : Type u))
    (hT : P (CommAlgCat.of A (Polynomial (R.obj : Type u) ⧸ Ideal.span {f, g}))) :
    ∃! a : (R.obj : Type u), Polynomial.aeval a f = 0 ∧ Polynomial.aeval a g = 0 := by
  let I : Ideal (Polynomial (R.obj : Type u)) := Ideal.span {f, g}
  let S := Polynomial (R.obj : Type u) ⧸ I
  let q : S := Ideal.Quotient.mk I Polynomial.X
  let T : P.FullSubcategory := ⟨CommAlgCat.of A S, hT⟩
  let iAlg : (R.obj : Type u) →ₐ[A] S :=
    AlgHom.restrictScalars A (Algebra.ofId (R.obj : Type u) S)
  let i : R ⟶ T := ⟨CommAlgCat.ofHom iAlg⟩
  let h : T ⟶ R := hR.from T
  have hhi : i ≫ h = 𝟙 R := hR.hom_ext _ _
  have hrestrict (r : (R.obj : Type u)) :
      h.1.hom (algebraMap (R.obj : Type u) S r) = r := by
    simpa [i, iAlg] using show h.1.hom (i.1.hom r) = r from congrArg (fun f : R ⟶ R => f r) hhi
  let gR : S →ₐ[(R.obj : Type u)] (R.obj : Type u) :=
    { h.1.hom.toRingHom with commutes' := hrestrict }
  let a : (R.obj : Type u) := gR q
  have hroot : ∀ z ∈ I, Polynomial.aeval a z = 0 := fun z hz => by
    have hq : Polynomial.aeval q = Ideal.Quotient.mkₐ (R.obj : Type u) I :=
      Polynomial.algHom_ext (by rw [Polynomial.aeval_X]; rfl)
    rw [Polynomial.aeval_algHom_apply, hq, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem.mpr hz, map_zero]
  refine ⟨a, ⟨hroot f (Ideal.subset_span (by simp)), hroot g (Ideal.subset_span (by simp))⟩, ?_⟩
  rintro b ⟨hbf, hbg⟩
  let ev : Polynomial (R.obj : Type u) →ₐ[(R.obj : Type u)] (R.obj : Type u) := Polynomial.aeval b
  have hI : ∀ z ∈ I, ev z = 0 := fun z hz => by
    have hker : I ≤ RingHom.ker (ev : Polynomial (R.obj : Type u) →+* (R.obj : Type u)) :=
      Ideal.span_le.mpr (Set.insert_subset_iff.mpr ⟨hbf, Set.singleton_subset_iff.mpr hbg⟩)
    exact RingHom.mem_ker.mp (hker hz)
  let e : S →ₐ[(R.obj : Type u)] (R.obj : Type u) := Ideal.Quotient.liftₐ I ev hI
  let eSub : T ⟶ R := ⟨CommAlgCat.ofHom (AlgHom.restrictScalars A e)⟩
  have heh : eSub = h := hR.hom_ext _ _
  have heval : e q = b := by
    have h := congrArg (fun k : Polynomial (R.obj : Type u) →ₐ[(R.obj : Type u)]
      (R.obj : Type u) => k Polynomial.X) (Ideal.Quotient.liftₐ_comp I ev hI)
    exact h.trans (Polynomial.aeval_X b)
  have hea : e q = a := by
    simpa [eSub, a, gR] using
      show eSub.1.hom q = h.1.hom q from congrArg (fun k : T ⟶ R => k q) heh
  exact heval.symm.trans hea

/-- In a terminal object of a full subcategory of `CommAlgCat A` which contains the square-cube
root algebra of Tag 0EUI, any `x, y` have a unique common square and cube root. -/
theorem existsUnique_sq_cube_of_isTerminal (A : Type u) [CommRing A]
    (P : ObjectProperty (CommAlgCat.{u} A)) (R : P.FullSubcategory) (hR : IsTerminal R)
    (x y : (R.obj : Type u))
    (hT : P (CommAlgCat.of A (SquareCubeAlgebra (R.obj : Type u) x y))) :
    ∃! a : (R.obj : Type u), x = a ^ 2 ∧ y = a ^ 3 := by
  simpa [sub_eq_zero, eq_comm] using existsUnique_aeval_eq_zero_of_isTerminal A P R hR
    (Polynomial.X ^ 2 - Polynomial.C x) (Polynomial.X ^ 3 - Polynomial.C y) hT

/-- In a terminal object of a full subcategory of `CommAlgCat A` which contains the prime-power
root algebra of Tag 0EUI, any `x, y` have a unique common `p`-th root in the prescribed
sense. -/
theorem existsUnique_pow_mul_of_isTerminal (A : Type u) [CommRing A]
    (P : ObjectProperty (CommAlgCat.{u} A)) (R : P.FullSubcategory) (hR : IsTerminal R)
    (p : ℕ) (x y : (R.obj : Type u))
    (hT : P (CommAlgCat.of A (Polynomial (R.obj : Type u) ⧸ Ideal.span
      {Polynomial.X ^ p - Polynomial.C x,
        Polynomial.C (p : (R.obj : Type u)) * Polynomial.X - Polynomial.C y}))) :
    ∃! a : (R.obj : Type u), x = a ^ p ∧ y = (p : (R.obj : Type u)) * a := by
  simpa [sub_eq_zero, eq_comm] using existsUnique_aeval_eq_zero_of_isTerminal A P R hR
    (Polynomial.X ^ p - Polynomial.C x)
    (Polynomial.C (p : (R.obj : Type u)) * Polynomial.X - Polynomial.C y) hT

/-- A terminal object of the category of `A`-algebras which are universal homeomorphisms over
`A` is an absolutely weakly normal ring. -/
theorem isAbsolutelyWeaklyNormalRing_of_isTerminal (A : Type u) [CommRing A]
    (R : AbsoluteWeakNormalizationCategory A) (hR : IsTerminal R) :
    IsAbsolutelyWeaklyNormalRing (R.obj : Type u) := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    simpa using existsUnique_sq_cube_of_isTerminal A
      (IsAbsoluteWeakNormalizationCandidate A) R hR x y
      (isAbsoluteWeakNormalizationCandidate_squareCubeAlgebra A (R.obj : Type u) x y hxy
        R.property)
  · intro p hp x y hxy
    let B := Polynomial (R.obj : Type u) ⧸ Ideal.span
      {Polynomial.X ^ p - Polynomial.C x,
        Polynomial.C (p : (R.obj : Type u)) * Polynomial.X - Polynomial.C y}
    have hRB : UniversalHomeomorphism
        (Spec.map (CommRingCat.ofHom (algebraMap (R.obj : Type u) B))) := by
      simpa [B] using universalHomeomorphism_spec_quotient_of_pPower_mul
        (A := (R.obj : Type u)) x y p hp hxy
    have hB : IsAbsoluteWeakNormalizationCandidate A (CommAlgCat.of A B) :=
      universalHomeomorphism_specMap_tower A (R.obj : Type u) B R.property hRB
    simpa using existsUnique_pow_mul_of_isTerminal A
      (IsAbsoluteWeakNormalizationCandidate A) R hR p x y hB

/-! ### The characterization -/

/-- **Stacks 0EUR.** For an `A`-algebra `B` whose spectrum morphism to `Spec A` is a universal
homeomorphism, the canonical map `B ⟶ Aᵃʷⁿ` is an isomorphism exactly when `B` is absolutely
weakly normal. -/
@[stacks 0EUR "awn_characterization"]
theorem isIso_toAbsoluteWeakNormalization_iff_isAbsolutelyWeaklyNormalRing
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (huniv : UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :
    IsIso ((absoluteWeakNormalizationCandidate_isTerminal A).from
        (⟨CommAlgCat.of A B, huniv⟩ : AbsoluteWeakNormalizationCategory A)) ↔
      IsAbsolutelyWeaklyNormalRing B := by
  let T := absoluteWeakNormalizationCandidate_isTerminal A
  let X : AbsoluteWeakNormalizationCategory A := ⟨CommAlgCat.of A B, huniv⟩
  let f := T.from X
  change IsIso f ↔ IsAbsolutelyWeaklyNormalRing B
  refine ⟨fun _ => isAbsolutelyWeaklyNormalRing_of_isTerminal A X
    (IsTerminal.ofIso T (asIso f).symm), fun hB => ?_⟩
  · let R := absoluteWeakNormalizationCandidate A
    have hR : IsAbsolutelyWeaklyNormalRing (R.obj : Type u) :=
      isAbsolutelyWeaklyNormalRing_of_isTerminal A R T
    let fRing : B →+* (R.obj : Type u) := f.1.hom.toRingHom
    have hcomp : Spec.map (CommRingCat.ofHom fRing) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A B)) =
        Spec.map (CommRingCat.ofHom (algebraMap A (R.obj : Type u))) := by
      rw [← Spec.map_comp]
      congr 1
      ext x
      simp [fRing]
    have hfSpec : UniversalHomeomorphism (Spec.map (CommRingCat.ofHom fRing)) := by
      refine universalHomeomorphism_hasTwoOutOfThreeProperty.of_postcomp
        (Spec.map (CommRingCat.ofHom fRing)) (Spec.map (CommRingCat.ofHom (algebraMap A B)))
        huniv ?_
      rw [hcomp]
      exact R.property
    have hfHomeo : IsHomeomorph (Spec.map (CommRingCat.ofHom fRing)) :=
      hfSpec.universally_isHomeomorph _ _ _ IsPullback.of_id_snd
    have hinj : Function.Injective fRing := by
      have _ : IsReduced (CommRingCat.of B) := by
        simpa only [CommRingCat.coe_of] using absolutelyWeaklyNormalRing_isReduced hB
      have hsurjSpec : Function.Surjective (PrimeSpectrum.comap fRing) := by
        intro q
        obtain ⟨r, hr⟩ := hfHomeo.surjective q
        rw [Spec.map_apply] at hr
        exact ⟨r, hr⟩
      refine (RingHom.injective_iff_ker_eq_bot fRing).mpr (bot_unique ?_)
      rw [← nilradical_eq_bot_iff.mpr ‹IsReduced (CommRingCat.of B)›]
      exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical fRing).mp
        hsurjSpec.denseRange
    let C : Subring (R.obj : Type u) := fRing.range
    let e : B ≃+* C := RingEquiv.ofBijective fRing.rangeRestrict
      ⟨fun x y hxy => hinj (congrArg Subtype.val hxy), RingHom.rangeRestrict_surjective fRing⟩
    have hfactor : Spec.map (CommRingCat.ofHom C.subtype) ≫
        Spec.map (CommRingCat.ofHom e.toRingHom) = Spec.map (CommRingCat.ofHom fRing) := by
      rw [← Spec.map_comp]
      rfl
    have hiso : IsIso (Spec.map (CommRingCat.ofHom e.toRingHom)) :=
      isIso_SpecMap_iff.2 e.bijective
    have heSpec : UniversalHomeomorphism (Spec.map (CommRingCat.ofHom e.toRingHom)) :=
      @universalHomeomorphism_of_isIso _ _ _ hiso
    have hCSpec : UniversalHomeomorphism (Spec.map (CommRingCat.ofHom C.subtype)) := by
      refine universalHomeomorphism_hasTwoOutOfThreeProperty.of_postcomp
        (Spec.map (CommRingCat.ofHom C.subtype)) (Spec.map (CommRingCat.ofHom e.toRingHom))
        heSpec ?_
      rw [hfactor]
      exact hfSpec
    have hsurj : Function.Surjective fRing := by
      by_contra hsurj
      have _ : UniversalHomeomorphism
          (Scheme.Spec.map (CommRingCat.ofHom C.subtype).op) := hCSpec
      rcases exists_special_element_of_universalHomeomorphism C
          (fun htop => hsurj (RingHom.range_eq_top.mp htop)) with
        ⟨b, hb, hb2, hb3⟩ | ⟨p, hp, b, hb, hpb, hbp⟩
      · obtain ⟨x, hx⟩ := RingHom.mem_range.mp hb2
        obtain ⟨y, hy⟩ := RingHom.mem_range.mp hb3
        have hxy : x ^ 3 = y ^ 2 := by
          apply hinj
          rw [map_pow, map_pow, hx, hy]
          ring
        obtain ⟨a, ha, _⟩ := hB.1.existsUnique_of_cube_eq_square hxy
        have hfa2 : fRing a ^ 2 = b ^ 2 := by simpa [← hx, ← ha.1] using (map_pow fRing a 2).symm
        have hfa3 : fRing a ^ 3 = b ^ 3 := by simpa [← hy, ← ha.2] using (map_pow fRing a 3).symm
        obtain ⟨_, _, huniqR⟩ := hR.1.existsUnique_of_cube_eq_square
          (x := b ^ 2) (y := b ^ 3) (by ring)
        have hb_eq : b = fRing a :=
          (huniqR b ⟨rfl, rfl⟩).trans (huniqR (fRing a) ⟨hfa2.symm, hfa3.symm⟩).symm
        exact hb (hb_eq ▸ RingHom.mem_range_self fRing a)
      · obtain ⟨x, hx⟩ := RingHom.mem_range.mp hbp
        obtain ⟨y, hy⟩ := RingHom.mem_range.mp hpb
        have hxy : (p : B) ^ p * x = y ^ p := by
          apply hinj
          rw [map_mul, map_pow, map_pow, map_natCast, hx, hy]
          ring
        obtain ⟨a, ha, _⟩ := hB.2 p hp x y hxy
        have hfa_pow : fRing a ^ p = b ^ p := by
          simpa [← hx, ← ha.1] using (map_pow fRing a p).symm
        have hfa_mul : (p : (R.obj : Type u)) * fRing a = (p : (R.obj : Type u)) * b := by
          simpa [← hy, ← ha.2] using (map_mul fRing (p : B) a).symm
        obtain ⟨_, _, huniqR⟩ := hR.existsUnique_of_prime_pow_mul_eq_pow hp
          (x := b ^ p) (y := (p : (R.obj : Type u)) * b) (by ring)
        have hb_eq : b = fRing a :=
          (huniqR b ⟨rfl, rfl⟩).trans
            (huniqR (fRing a) ⟨hfa_pow.symm, hfa_mul.symm⟩).symm
        exact hb (hb_eq ▸ RingHom.mem_range_self fRing a)
    let eFull : X ≅ R := (IsAbsoluteWeakNormalizationCandidate A).isoMk
      (CommAlgCat.isoMk (AlgEquiv.ofBijective f.1.hom ⟨hinj, hsurj⟩))
    have hfEq : f = eFull.hom := T.hom_ext _ _
    rw [hfEq]
    infer_instance

end Algebra

end
