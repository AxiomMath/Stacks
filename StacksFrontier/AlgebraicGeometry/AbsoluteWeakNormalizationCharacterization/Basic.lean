module

public import StacksFrontier.AlgebraicGeometry.Topologies.WeakNormalization.RingCharacterization
public import StacksFrontier.AlgebraicGeometry.AbsoluteWeakNormalizationTerminal.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.PrimePowerAlg
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.SpecialElement
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.SquareCubeAlg
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.Ring

/-!
# Characterization of the absolute weak normalization

Let `A → B` be a map of commutative rings inducing a universal homeomorphism on spectra.  The
canonical map from `B` to the absolute weak normalization of `A` is an isomorphism exactly when
`B` is absolutely weakly normal.

## Main results

* `AlgebraicGeometry.isAbsolutelyWeaklyNormalRing_of_isTerminal`: a terminal
  universal-homeomorphism `A`-algebra is absolutely weakly normal.
* `AlgebraicGeometry.isIso_lift_to_absoluteWeakNormalization_iff_isAbsolutelyWeaklyNormalRing`:
  the canonical map from `B` to the absolute weak normalization of `A` is an isomorphism exactly
  when `B` is absolutely weakly normal.

## Implementation notes

The canonical map is the lift from the terminal-object property of the absolute weak
normalization, `AlgebraicGeometry.absoluteWeakNormalizationCategoryObject_isTerminal`.
Expressing it in the category of `A`-algebras retains its compatibility with the given map
from `A`.

Terminality forces absolute weak normality because the two defining equations have solutions
after an explicit elementary extension — `AlgebraicGeometry.SquareCubeAlgebra` for the
square-and-cube equation and the prime-power quotient of Tag 0EUI for the other — and both
extensions are again universal homeomorphisms over `A`, hence again objects of the category,
so the unique map back to the terminal object produces the solution and the unique map forward
makes it unique.

For the converse, the canonical map is injective because its source is reduced and its spectrum
map is surjective, so the question is surjectivity of `B → Aᵃʷⁿ`.  If the image subring were
proper, the special-element criterion of Tag 0CNC
(`AlgebraicGeometry.exists_special_element_of_universalHomeomorphism`) would produce an element
outside it whose square and cube, or whose `p`-th power and `p`-multiple, lie inside; absolute
weak normality of `B` supplies a preimage, and uniqueness in `Aᵃʷⁿ` identifies the two, a
contradiction.

The seminormality half of the same terminality argument is not reproduced here: it would need
the seminormalization counterpart of
`AlgebraicGeometry.absoluteWeakNormalizationCategoryObject_isTerminal`, which is Tag 0EUR's
`sn_final` label and is not formalized in this library.

Everything lives in a single universe `u`, as `AlgebraicGeometry.UniversalHomeomorphism` is
available only for `Scheme.{u}`.

No hypothesis beyond those of Tag 0EUR is used: `A` and `B` are arbitrary commutative rings,
with no Noetherian or reducedness assumption.

## What is not done

Nothing here is about schemes other than spectra of rings.  The initiality of
`AlgebraicGeometry.UniversalHomeomorphismOver X` for a general scheme `X`, and the
characterization of when its canonical map to another universal homeomorphism is an
isomorphism, are Tag 0EUS's `absolute_weak_normalization_initial` and
`absolute_weak_normalization_iso_iff` labels and are still unproved after this file.

## References

* [Stacks Project, Tag 0CNC](https://stacks.math.columbia.edu/tag/0CNC)
* [Stacks Project, Tag 0EUI](https://stacks.math.columbia.edu/tag/0EUI)
* [Stacks Project, Tag 0EUR](https://stacks.math.columbia.edu/tag/0EUR)
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry


/-- For a tower `A → R → S`, the spectrum map of `A → S` is the composite of those of `R → S`
and `A → R`. -/
public theorem specMap_composite
    (A R S : Type u) [CommRing A] [CommRing R] [CommRing S]
    [Algebra A R] [Algebra R S] [Algebra A S] [IsScalarTower A R S] :
    Scheme.Spec.map (CommRingCat.ofHom (algebraMap A S)).op =
      Scheme.Spec.map (CommRingCat.ofHom (algebraMap R S)).op ≫
        Scheme.Spec.map (CommRingCat.ofHom (algebraMap A R)).op := by
  have h : CommRingCat.ofHom (algebraMap A S) =
      CommRingCat.ofHom (algebraMap A R) ≫ CommRingCat.ofHom (algebraMap R S) :=
    CommRingCat.hom_ext (IsScalarTower.algebraMap_eq A R S)
  rw [congrArg Quiver.Hom.op h]
  simp only [op_comp, Scheme.Spec.map_comp]

/-- For a tower `A → R → S`, if `Spec R → Spec A` and `Spec S → Spec R` are universal
homeomorphisms, so is `Spec S → Spec A`. -/
public theorem universalHomeomorphism_composite
    (A R S : Type u) [CommRing A] [CommRing R] [CommRing S]
    [Algebra A R] [Algebra R S] [Algebra A S] [IsScalarTower A R S]
    (hAR : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A R)).op))
    (hRS : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R S)).op)) :
    UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A S)).op) := by
  let : (topologically @IsHomeomorph).IsStableUnderComposition :=
    AlgebraicGeometry.topologically_isStableUnderComposition _ (by
      intro X Y Z _ _ _ f g hf hg
      exact hg.comp hf)
  let : ((topologically @IsHomeomorph).universally).IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.universally _
  rw [specMap_composite A R S]
  exact ⟨(topologically @IsHomeomorph).universally.comp_mem _ _
    hRS.universally_isHomeomorph hAR.universally_isHomeomorph⟩

/-- For a tower `A → R → S`, if `Spec R → Spec A` and `Spec S → Spec R` induce isomorphisms on
all residue fields, so does `Spec S → Spec A`. -/
public theorem residueFieldIsomorphisms_composite
    (A R S : Type u) [CommRing A] [CommRing R] [CommRing S]
    [Algebra A R] [Algebra R S] [Algebra A S] [IsScalarTower A R S]
    (hAR : ∀ z : Spec (.of R), IsIso
      ((Scheme.Spec.map (CommRingCat.ofHom (algebraMap A R)).op).residueFieldMap z))
    (hRS : ∀ z : Spec (.of S), IsIso
      ((Scheme.Spec.map (CommRingCat.ofHom (algebraMap R S)).op).residueFieldMap z)) :
    ∀ z : Spec (.of S), IsIso
      ((Scheme.Spec.map (CommRingCat.ofHom (algebraMap A S)).op).residueFieldMap z) := by
  intro z
  rw [specMap_composite A R S, Scheme.residueFieldMap_comp]
  exact IsIso.comp_isIso' (hAR _) (hRS z)

/-- If `R` is terminal in a full subcategory of `A`-algebras containing `R[X]/(s)`, then the
polynomials in `s` have a unique common root in `R`. -/
private theorem terminal_quotient_existsUnique
    (A : Type u) [CommRing A]
    (P : ObjectProperty (CommAlgCat.{u} A))
    (R : P.FullSubcategory) (hR : IsTerminal R)
    (s : Set (Polynomial R.1))
    (hT : P (CommAlgCat.of A (Polynomial R.1 ⧸ Ideal.span s))) :
    ∃! a : R.1, ∀ z ∈ s, Polynomial.aeval a z = 0 := by
  let I : Ideal (Polynomial R.1) := Ideal.span s
  let S := Polynomial R.1 ⧸ I
  let q : S := Ideal.Quotient.mk I Polynomial.X
  let T : P.FullSubcategory := ⟨CommAlgCat.of A S, hT⟩
  let iAlg : R.1 →ₐ[A] S := AlgHom.restrictScalars A (Algebra.ofId R.1 S)
  let i : R ⟶ T := ⟨CommAlgCat.ofHom iAlg⟩
  let g : T ⟶ R := hR.from T
  have hgi : i ≫ g = 𝟙 R := hR.hom_ext _ _
  have hrestrict (r : R.1) : g.1.hom (algebraMap R.1 S r) = r := by
    have h := congrArg (fun f : R ⟶ R => f r) hgi
    change g.1.hom (i.1.hom r) = r at h
    simpa [i, iAlg] using h
  let a : R.1 := g.1.hom q
  have hga (z : Polynomial R.1) : g.1.hom (Ideal.Quotient.mk I z) = Polynomial.aeval a z := by
    have h : g.1.hom.toRingHom.comp (Ideal.Quotient.mk I) =
        (Polynomial.aeval a : Polynomial R.1 →ₐ[R.1] R.1).toRingHom :=
      by
      refine Polynomial.ringHom_ext (fun r => ?_) ?_
      · exact (hrestrict r).trans (Polynomial.aeval_C a r).symm
      · simp [a, q]
    exact RingHom.congr_fun h z
  refine ⟨a, fun z hz => ?_, fun b hb => ?_⟩
  · rw [← hga, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span hz), map_zero]
  · let ev : Polynomial R.1 →ₐ[R.1] R.1 := Polynomial.aeval b
    have hI : ∀ z ∈ I, ev z = 0 := fun z hz =>
      RingHom.mem_ker.mp ((Ideal.span_le (I := RingHom.ker (ev : Polynomial R.1 →+* R.1))).2 hb hz)
    let f : S →ₐ[R.1] R.1 := Ideal.Quotient.liftₐ I ev hI
    let fA : S →ₐ[A] R.1 := AlgHom.restrictScalars A f
    let fSub : T ⟶ R := ⟨CommAlgCat.ofHom fA⟩
    have hfg : fSub = g := hR.hom_ext _ _
    have heval : f q = b := by
      have hcomp : f.comp (Ideal.Quotient.mkₐ R.1 I) = ev :=
        Ideal.Quotient.liftₐ_comp I ev hI
      have h := congrArg (fun k : Polynomial R.1 →ₐ[R.1] R.1 => k Polynomial.X) hcomp
      change f (Ideal.Quotient.mkₐ R.1 I Polynomial.X) = b
      exact h.trans (Polynomial.aeval_X b)
    have hfa : f q = a := by
      have h := congrArg (fun k : T ⟶ R => k q) hfg
      change fSub.1.hom q = a at h
      simpa [fSub, fA, a] using h
    rw [heval] at hfa
    exact hfa

/-- If `R` is terminal in a full subcategory of `A`-algebras containing the square-and-cube
extension `SquareCubeAlgebra R x y`, then there is a unique `a ∈ R` with `x = a²` and
`y = a³`. -/
public theorem terminal_squareCube_existsUnique
    (A : Type u) [CommRing A]
    (P : ObjectProperty (CommAlgCat.{u} A))
    (R : P.FullSubcategory) (hR : IsTerminal R)
    (x y : R.1)
    (hT : P (CommAlgCat.of A
      (SquareCubeAlgebra R.1 x y))) :
    ∃! a : R.1, x = a ^ 2 ∧ y = a ^ 3 := by
  simpa [sub_eq_zero, eq_comm] using terminal_quotient_existsUnique A P R hR
    {Polynomial.X ^ 2 - Polynomial.C x, Polynomial.X ^ 3 - Polynomial.C y} hT

/-- If `R` is terminal in a full subcategory of `A`-algebras containing the prime-power extension
`R[X]/(Xᵖ - x, pX - y)`, then there is a unique `a ∈ R` with `x = aᵖ` and `y = p a`. -/
public theorem terminal_primePower_existsUnique
    (A : Type u) [CommRing A]
    (P : ObjectProperty (CommAlgCat.{u} A))
    (R : P.FullSubcategory) (hR : IsTerminal R)
    (p : ℕ) (x y : R.1)
    (hT : P (CommAlgCat.of A
      (Polynomial R.1 ⧸ Ideal.span
        {Polynomial.X ^ p - Polynomial.C x,
          Polynomial.C (p : R.1) * Polynomial.X - Polynomial.C y}))) :
    ∃! a : R.1, x = a ^ p ∧ y = (p : R.1) * a := by
  simpa [sub_eq_zero, eq_comm] using terminal_quotient_existsUnique A P R hR
    {Polynomial.X ^ p - Polynomial.C x,
      Polynomial.C (p : R.1) * Polynomial.X - Polynomial.C y} hT

/-- A terminal universal-homeomorphism `A`-algebra is absolutely weakly normal. -/
public theorem isAbsolutelyWeaklyNormalRing_of_isTerminal
    (A : Type u) [CommRing A]
    (R : AbsoluteWeakNormalizationCategory A)
    (hR : IsTerminal R) :
    IsAbsolutelyWeaklyNormalRing R.1 := by
  refine ⟨fun x y hxy => ?_, fun p hp x y hxy => ?_⟩
  · simpa using terminal_squareCube_existsUnique A
      (IsAbsoluteWeakNormalizationCandidate A) R hR x y
      (Algebra.isAbsoluteWeakNormalizationCandidate_squareCubeAlgebra A R.1 x y hxy R.property)
  · let B := Polynomial R.1 ⧸ Ideal.span
      {Polynomial.X ^ p - Polynomial.C x,
        Polynomial.C (p : R.1) * Polynomial.X - Polynomial.C y}
    have hB : IsAbsoluteWeakNormalizationCandidate A (CommAlgCat.of A B) := by
      show UniversalHomeomorphism
        (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op)
      have hRB : UniversalHomeomorphism
          (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R.1 B)).op) := by
        simpa [B] using
          universalHomeomorphism_spec_quotient_of_pPower_mul
            (A := R.1) x y p hp hxy
      exact universalHomeomorphism_composite A R.1 B R.property hRB
    simpa using terminal_primePower_existsUnique A
      (IsAbsoluteWeakNormalizationCandidate A) R hR p x y hB


/-- A universally homeomorphic `A`-algebra is the absolute weak normalization of `A`
precisely when its underlying ring is absolutely weakly normal. -/
@[stacks 0EUR "awn_characterization"]
public theorem isIso_lift_to_absoluteWeakNormalization_iff_isAbsolutelyWeaklyNormalRing
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (huniv : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op)) :
    IsIso ((absoluteWeakNormalizationCategoryObject_isTerminal A).from
      (⟨CommAlgCat.of A B, huniv⟩ :
        AbsoluteWeakNormalizationCategory A)) ↔
      IsAbsolutelyWeaklyNormalRing B := by
  let T := absoluteWeakNormalizationCategoryObject_isTerminal A
  let X : AbsoluteWeakNormalizationCategory A := ⟨CommAlgCat.of A B, huniv⟩
  let f := T.from X
  show IsIso f ↔ IsAbsolutelyWeaklyNormalRing B
  constructor
  · intro hf
    let : IsIso f := hf
    exact isAbsolutelyWeaklyNormalRing_of_isTerminal A X (IsTerminal.ofIso T (asIso f).symm)
  · intro hB
    let R := absoluteWeakNormalizationCategoryObject A
    have hR : IsAbsolutelyWeaklyNormalRing R.1 := isAbsolutelyWeaklyNormalRing_of_isTerminal A R T
    let fRing : B →+* R.1 := f.hom.hom.toRingHom
    let fSpec : Spec (CommRingCat.of R.1) ⟶ Spec (CommRingCat.of B) :=
      Scheme.Spec.map (CommRingCat.ofHom fRing).op
    let abSpec : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
      Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op
    let arSpec : Spec (CommRingCat.of R.1) ⟶ Spec (CommRingCat.of A) :=
      Scheme.Spec.map (CommRingCat.ofHom (algebraMap A R.1)).op
    have hAR : UniversalHomeomorphism arSpec := R.property
    have hcomp : fSpec ≫ abSpec = arSpec := by
      dsimp [fSpec, abSpec, arSpec]
      rw [← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      ext x
      simp [fRing]
    let : HasOfPostcompProperty (@UniversalHomeomorphism.{u}) (@UniversalHomeomorphism.{u}) :=
      universalHomeomorphism_hasTwoOutOfThreeProperty.toHasOfPostcompProperty
    have hfSpec : UniversalHomeomorphism fSpec := by
      apply MorphismProperty.of_postcomp
        (W := @UniversalHomeomorphism.{u}) fSpec abSpec huniv
      simpa [hcomp] using hAR
    have hfHomeo : IsHomeomorph fSpec :=
      hfSpec.universally_isHomeomorph _ _ _ IsPullback.of_id_snd
    have hinj : Function.Injective fRing := by
      let fRingObj := (CommRingCat.ofHom fRing).hom
      have : _root_.IsReduced (CommRingCat.of B) := by
        simpa only [CommRingCat.coe_of] using
          absolutelyWeaklyNormalRing_isReduced hB
      have hsurjSpec : Function.Surjective (PrimeSpectrum.comap fRingObj) := by
        intro q
        obtain ⟨r, hr⟩ := hfHomeo.surjective q
        have hr' : PrimeSpectrum.comap fRingObj r = q := by
          change (Spec.map (CommRingCat.ofHom fRing)) r = q at hr
          rw [Spec.map_apply] at hr
          exact hr
        exact ⟨r, hr'⟩
      have hInjObj : Function.Injective fRingObj :=
        (RingHom.injective_iff_ker_eq_bot fRingObj).mpr (bot_unique (by
          rw [← nilradical_eq_bot_iff.mpr ‹_root_.IsReduced (CommRingCat.of B)›]
          exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical fRingObj).mp
            hsurjSpec.denseRange))
      intro x y hxy
      apply hInjObj
      simpa [fRingObj, CommRingCat.coe_of] using hxy
    let C : Subring R.1 := fRing.range
    let e : B ≃+* C := RingEquiv.ofBijective fRing.rangeRestrict
      ⟨fun x y hxy => hinj (congrArg Subtype.val hxy), RingHom.rangeRestrict_surjective fRing⟩
    let cSpec : Spec (CommRingCat.of R.1) ⟶ Spec (CommRingCat.of C) :=
      Scheme.Spec.map (CommRingCat.ofHom C.subtype).op
    let eSpec : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of B) :=
      Scheme.Spec.map (CommRingCat.ofHom e.toRingHom).op
    have hfactor : cSpec ≫ eSpec = fSpec := by
      dsimp [cSpec, eSpec, fSpec]
      rw [← Spec.map_comp]
      rfl
    have hIsoSpec : IsIso (Spec.map (CommRingCat.ofHom e.toRingHom)) :=
      (isIso_SpecMap_iff).2 e.bijective
    have : IsIso eSpec := by
      dsimp [eSpec]
      exact hIsoSpec
    have heSpec : UniversalHomeomorphism eSpec := by
      rw [universalHomeomorphism_iff]
      intro X' Y' i₁ i₂ f' hpull
      have : IsIso eSpec := by assumption
      have hIsoF' : IsIso f' := hpull.isIso_fst_of_isIso
      exact (TopCat.homeoOfIso (asIso f'.base)).isHomeomorph
    have hCSpec : UniversalHomeomorphism cSpec := by
      apply MorphismProperty.of_postcomp
        (W := @UniversalHomeomorphism.{u}) cSpec eSpec heSpec
      simpa [hfactor] using hfSpec
    have hsurj : Function.Surjective fRing := by
      by_contra hsurj
      let : UniversalHomeomorphism
          (Scheme.Spec.map (CommRingCat.ofHom C.subtype).op) := hCSpec
      rcases exists_special_element_of_universalHomeomorphism C
          (by intro htop; exact hsurj (RingHom.range_eq_top.mp htop)) with
        ⟨b, hb, hb2, hb3⟩ | ⟨p, hp, b, hb, hpb, hbp⟩
      · obtain ⟨x, hx⟩ := RingHom.mem_range.mp hb2
        obtain ⟨y, hy⟩ := RingHom.mem_range.mp hb3
        have hxy : x ^ 3 = y ^ 2 := by
          apply hinj
          rw [map_pow, map_pow, hx, hy]
          ring
        obtain ⟨a, ha, huniqB⟩ := hB.1.existsUnique_of_cube_eq_square hxy
        have hfa2 : fRing a ^ 2 = b ^ 2 := by simpa [← hx, ← ha.1] using (map_pow fRing a 2).symm
        have hfa3 : fRing a ^ 3 = b ^ 3 := by simpa [← hy, ← ha.2] using (map_pow fRing a 3).symm
        obtain ⟨_, _, huniqR⟩ :=
          hR.1.existsUnique_of_cube_eq_square (x := b ^ 2) (y := b ^ 3) (by ring)
        have hb_eq : b = fRing a :=
          (huniqR b ⟨rfl, rfl⟩).trans (huniqR (fRing a) ⟨hfa2.symm, hfa3.symm⟩).symm
        exact hb (hb_eq ▸ RingHom.mem_range_self fRing a)
      · obtain ⟨x, hx⟩ := RingHom.mem_range.mp hbp
        obtain ⟨y, hy⟩ := RingHom.mem_range.mp hpb
        have hxy : (p : B) ^ p * x = y ^ p := by
          apply hinj
          rw [map_mul, map_pow, map_pow, map_natCast, hx, hy]
          ring
        obtain ⟨a, ha, huniqB⟩ := hB.2 p hp x y hxy
        have hfa_pow : fRing a ^ p = b ^ p := by simpa [← hx, ← ha.1] using (map_pow fRing a p).symm
        have hfa_mul : (p : R.1) * fRing a = (p : R.1) * b := by
          simpa [← hy, ← ha.2] using (map_mul fRing (p : B) a).symm
        obtain ⟨_, _, huniqR⟩ := hR.existsUnique_of_prime_pow_mul_eq_pow hp (x := b ^ p)
          (y := (p : R.1) * b) (by ring)
        have hb_eq : b = fRing a :=
          (huniqR b ⟨rfl, rfl⟩).trans (huniqR (fRing a) ⟨hfa_pow.symm, hfa_mul.symm⟩).symm
        exact hb (hb_eq ▸ RingHom.mem_range_self fRing a)
    let eAlg : B ≃ₐ[A] R.1 := AlgEquiv.ofBijective f.hom.hom ⟨hinj, hsurj⟩
    let eBase : CommAlgCat.of A B ≅ CommAlgCat.of A R.1 := CommAlgCat.isoMk (R := A) eAlg
    let eFull : X ≅ R := (IsAbsoluteWeakNormalizationCandidate A).isoMk eBase
    have hfEq : f = eFull.hom := T.hom_ext _ _
    rw [hfEq]
    infer_instance

end AlgebraicGeometry

end
