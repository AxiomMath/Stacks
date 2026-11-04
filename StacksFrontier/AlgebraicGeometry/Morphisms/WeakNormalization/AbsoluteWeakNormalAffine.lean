module

public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.Data.Nat.Choose.Dvd
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.PrimePowerAlg
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.SpecialElement
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.SquareCubeAlg
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.TwoOutOfThree
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Reduction
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.Initial
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.Scheme
public import StacksFrontier.AlgebraicGeometry.Scheme.Reduction
public import StacksFrontier.AlgebraicGeometry.Seminormalization.Defs

/-!
# The initial universal homeomorphism over an affine scheme

An initial object of the category of universal homeomorphisms onto a scheme is reduced, because
the closed immersion of its reduction is again a universal homeomorphism onto the base and
initiality forces that closed immersion to be an isomorphism.

When the base is affine the initial object is affine as well, and its ring of sections is
absolutely weakly normal: adjoining a square-and-cube root, or a prime-power root, produces
another universal homeomorphism onto the base, so initiality supplies the root. Conversely a
universal homeomorphism onto the base whose ring of sections is absolutely weakly normal
receives an isomorphism from the initial object: the comparison map is injective because its
target is reduced, and it is surjective because a proper subring extension which is a universal
homeomorphism on spectra has a square-and-cube or a prime-power special element, which absolute
weak normality forces to lie in the subring already.

## Main results

* `AlgebraicGeometry.isReduced_of_isInitial_universalHomeomorphismOver`: an initial universal
  homeomorphism is reduced.
* `AlgebraicGeometry.isSeminormalRing_of_sections`: the sections of a reduced affine scheme form
  a seminormal ring as soon as every universal homeomorphism onto it which induces isomorphisms
  on residue fields has a section.
* `AlgebraicGeometry.isAbsolutelyWeaklyNormalRing_of_isInitial_universalHomeomorphismOver`: over
  an affine base the sections of the initial universal homeomorphism form an absolutely weakly
  normal ring.
* `AlgebraicGeometry.injective_of_universalHomeomorphism_specMap` and
  `AlgebraicGeometry.universalHomeomorphism_specMap_range_subtype`: a ring map whose morphism of
  spectra is a universal homeomorphism onto a reduced ring is injective, and the inclusion of
  its range is again a universal homeomorphism on spectra.
* `AlgebraicGeometry.isIso_of_isInitial_universalHomeomorphismOver`: over an affine base the
  canonical morphism from the initial universal homeomorphism to another one is an isomorphism
  as soon as the target has absolutely weakly normal sections.

## Implementation notes

Both root constructions are handled in the same two steps: initiality produces a section of a
morphism of spectra, and the section becomes a ring retraction by full faithfulness of `Spec`,
whose value on the adjoined variable is the required root. Uniqueness of the roots is automatic
in a reduced ring; for prime-power roots this is the binomial expansion, in which every
intermediate coefficient is divisible by the prime and therefore annihilates the difference of
two roots.

## References

* [Stacks Project, Tag 0EUS](https://stacks.math.columbia.edu/tag/0EUS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- In a reduced ring an element is determined by its `p`-th power together with its product
with the prime number `p`. -/
private theorem eq_of_pow_eq_of_natCast_mul_eq {A : Type u} [CommRing A] [_root_.IsReduced A]
    {p : ℕ} (hp : p.Prime) {a b : A} (hpow : a ^ p = b ^ p)
    (hmul : (p : A) * a = (p : A) * b) : a = b := by
  have hd : (p : A) * (a - b) = 0 := by linear_combination hmul
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, (Nat.sub_add_cancel hp.one_le).symm⟩
  have hzero : ∀ k ∈ Finset.range m,
      (a - b) ^ (k + 1) * b ^ (m + 1 - (k + 1)) * (((m + 1).choose (k + 1) : ℕ) : A) = 0 := by
    intro k hk
    obtain ⟨c, hc⟩ := Nat.Prime.dvd_choose_self hp (Nat.succ_ne_zero k)
      (Nat.succ_lt_succ (Finset.mem_range.mp hk))
    rw [hc, Nat.cast_mul]
    calc (a - b) ^ (k + 1) * b ^ (m + 1 - (k + 1)) * (((m + 1 : ℕ) : A) * (c : A))
        = ((a - b) ^ k * b ^ (m + 1 - (k + 1)) * (c : A)) * (((m + 1 : ℕ) : A) * (a - b)) := by
          ring
      _ = 0 := by rw [hd, mul_zero]
  have hadd := add_pow (a - b) b (m + 1)
  rw [sub_add_cancel, Finset.sum_range_succ, Finset.sum_range_succ',
    Finset.sum_eq_zero hzero] at hadd
  simp only [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one, zero_add,
    Nat.sub_zero, Nat.choose_zero_right, one_mul] at hadd
  rw [hpow] at hadd
  exact sub_eq_zero.mp (IsReduced.eq_zero _ ⟨m + 1, by linear_combination -hadd⟩)

/-- A section of the morphism of spectra induced by an algebra map is a ring retraction. -/
private theorem exists_retraction_of_section {R : Type u} [CommRing R] (B : Type u) [CommRing B]
    [Algebra R B] (s : Spec (.of R) ⟶ Spec (.of B))
    (hs : s ≫ Scheme.Spec.map (CommRingCat.ofHom (algebraMap R B)).op = 𝟙 _) :
    ∃ φ : CommRingCat.of B ⟶ CommRingCat.of R, ∀ r : R, φ.hom (algebraMap R B r) = r := by
  refine ⟨(Spec.fullyFaithful.preimage s).unop, fun r => ?_⟩
  have hφ : CommRingCat.ofHom (algebraMap R B) ≫ (Spec.fullyFaithful.preimage s).unop =
      𝟙 (CommRingCat.of R) := by
    apply Quiver.Hom.op_inj
    apply Scheme.Spec.map_injective
    simpa [Functor.map_comp] using hs
  exact congrArg (fun k : CommRingCat.of R ⟶ CommRingCat.of R => k.hom r) hφ

/-- Evaluating a polynomial of an ideal at the class of the variable in the quotient gives zero. -/
private theorem aeval_root_eq_zero {R : Type u} [CommRing R] {I : Ideal (Polynomial R)}
    {f : Polynomial R} (hf : f ∈ I) :
    Polynomial.aeval (Ideal.Quotient.mk I Polynomial.X) f = 0 := by
  have : Polynomial.aeval (Ideal.Quotient.mk I Polynomial.X) = Ideal.Quotient.mkₐ R I :=
    Polynomial.algHom_ext (by simp)
  rw [this]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hf

/-- The source of a universal homeomorphism onto an affine scheme is affine. -/
theorem isAffine_of_universalHomeomorphism {Y Z : Scheme.{u}} [IsAffine Z] (f : Y ⟶ Z)
    (hf : UniversalHomeomorphism f) : IsAffine Y := by
  have : IsIntegralHom f :=
    ((universalHomeomorphism_iff_integral_universallyInjective_surjective f).mp hf).1
  exact isAffine_of_isAffineHom f

section Sections

variable {P : Scheme.{u}} [IsAffine P]

/-- An affine scheme is a retract of the spectrum of an algebra over its sections as soon as
the morphism of spectra, compared with the scheme itself through `Scheme.isoSpec`, admits a
section. -/
private theorem exists_retraction_of_section_isoSpec (B : Type u) [CommRing B]
    [Algebra Γ(P, ⊤) B] (s : P ⟶ Spec (.of B))
    (hs : s ≫ (Scheme.Spec.map (CommRingCat.ofHom (algebraMap Γ(P, ⊤) B)).op ≫
      P.isoSpec.inv) = 𝟙 P) :
    ∃ φ : CommRingCat.of B ⟶ CommRingCat.of Γ(P, ⊤),
      ∀ r : Γ(P, ⊤), φ.hom (algebraMap Γ(P, ⊤) B r) = r := by
  refine exists_retraction_of_section B (P.isoSpec.inv ≫ s) ?_
  refine (cancel_mono P.isoSpec.inv).mp ?_
  rw [Category.assoc, Category.assoc, hs, Category.comp_id, Category.id_comp]

/-- The sections of a reduced affine scheme form a seminormal ring as soon as every universal
homeomorphism onto it which induces isomorphisms on all residue fields has a section: the
square-and-cube extension is such a universal homeomorphism, so the section supplies the
common square and cube root. -/
theorem isSeminormalRing_of_sections [IsReduced P]
    (hsec : ∀ {Z : Scheme.{u}} (h : Z ⟶ P), UniversalHomeomorphism h →
      (∀ z : Z, IsIso (h.residueFieldMap z)) → ∃ s : P ⟶ Z, s ≫ h = 𝟙 P) :
    IsSeminormalRing Γ(P, ⊤) := by
  intro x y hxy
  have hgq : UniversalHomeomorphism (squareCubeSpecMap Γ(P, ⊤) x y ≫ P.isoSpec.inv) :=
    universalHomeomorphism_hasTwoOutOfThreeProperty.comp_mem _ _
      (squareCubeSpecMap_universalHomeomorphism Γ(P, ⊤) x y hxy)
      (universalHomeomorphism_of_isIso _)
  have hinvres : ∀ w : Spec Γ(P, ⊤), IsIso (P.isoSpec.inv.residueFieldMap w) :=
    fun w => inferInstance
  have hgqres : ∀ z, IsIso ((squareCubeSpecMap Γ(P, ⊤) x y ≫ P.isoSpec.inv).residueFieldMap z) :=
    fun z => by
      rw [Scheme.residueFieldMap_comp]
      exact IsIso.comp_isIso' (hinvres _)
        (isIso_residueFieldMap_squareCubeSpecMap Γ(P, ⊤) x y hxy z)
  obtain ⟨s, hs⟩ := hsec _ hgq hgqres
  obtain ⟨φ, hφ⟩ := exists_retraction_of_section_isoSpec (SquareCubeAlgebra Γ(P, ⊤) x y) s hs
  set relations : Ideal (Polynomial Γ(P, ⊤)) := Ideal.span
    ({Polynomial.X ^ 2 - Polynomial.C x, Polynomial.X ^ 3 - Polynomial.C y} :
      Set (Polynomial Γ(P, ⊤)))
  set root : SquareCubeAlgebra Γ(P, ⊤) x y := Ideal.Quotient.mk relations Polynomial.X
  have hroot₂ : root ^ 2 = algebraMap Γ(P, ⊤) (SquareCubeAlgebra Γ(P, ⊤) x y) x := by
    simpa [sub_eq_zero] using aeval_root_eq_zero (I := relations)
      (Ideal.subset_span (by simp) : Polynomial.X ^ 2 - Polynomial.C x ∈ relations)
  have hroot₃ : root ^ 3 = algebraMap Γ(P, ⊤) (SquareCubeAlgebra Γ(P, ⊤) x y) y := by
    simpa [sub_eq_zero] using aeval_root_eq_zero (I := relations)
      (Ideal.subset_span (by simp) : Polynomial.X ^ 3 - Polynomial.C y ∈ relations)
  have hx : x = φ.hom root ^ 2 := by
    simpa only [map_pow, hφ] using (congrArg φ.hom hroot₂).symm
  have hy : y = φ.hom root ^ 3 := by
    simpa only [map_pow, hφ] using (congrArg φ.hom hroot₃).symm
  exact ⟨φ.hom root, ⟨hx, hy⟩, fun b hb =>
    Stacks.RingTheory.Seminormal.eq_of_sq_eq_of_cube_eq
      (by rw [← hb.1, ← hx]) (by rw [← hb.2, ← hy])⟩

/-- An affine scheme all of whose universal homeomorphisms have a section is a retract of the
spectrum of any algebra over its sections whose spectrum is a universal homeomorphism. -/
private theorem exists_retraction_of_sections (B : Type u) [CommRing B] [Algebra Γ(P, ⊤) B]
    (hsec : ∀ {Z : Scheme.{u}} (h : Z ⟶ P), UniversalHomeomorphism h →
      ∃ s : P ⟶ Z, s ≫ h = 𝟙 P)
    (hB : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap Γ(P, ⊤) B)).op)) :
    ∃ φ : CommRingCat.of B ⟶ CommRingCat.of Γ(P, ⊤),
      ∀ r : Γ(P, ⊤), φ.hom (algebraMap Γ(P, ⊤) B r) = r := by
  have hgq : UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (algebraMap Γ(P, ⊤) B)).op ≫ P.isoSpec.inv) :=
    universalHomeomorphism_hasTwoOutOfThreeProperty.comp_mem _ _ hB
      (universalHomeomorphism_of_isIso _)
  obtain ⟨s, hs⟩ := hsec _ hgq
  exact exists_retraction_of_section_isoSpec B s hs

/-- The sections of an affine scheme all of whose universal homeomorphisms have a section are
an absolutely weakly normal ring, provided the scheme is reduced. -/
private theorem isAbsolutelyWeaklyNormalRing_of_sections [IsReduced P]
    (hsec : ∀ {Z : Scheme.{u}} (h : Z ⟶ P), UniversalHomeomorphism h →
      ∃ s : P ⟶ Z, s ≫ h = 𝟙 P) :
    IsAbsolutelyWeaklyNormalRing Γ(P, ⊤) := by
  refine ⟨isSeminormalRing_of_sections fun h hh _ => hsec h hh, ?_⟩
  intro p hp x y hxy
  set relations : Ideal (Polynomial Γ(P, ⊤)) := Ideal.span
    {Polynomial.X ^ p - Polynomial.C x,
      Polynomial.C ((p : Γ(P, ⊤))) * Polynomial.X - Polynomial.C y}
  obtain ⟨φ, hφ⟩ := exists_retraction_of_sections (Polynomial Γ(P, ⊤) ⧸ relations) hsec
    (universalHomeomorphism_spec_quotient_of_pPower_mul x y p hp hxy)
  set root : Polynomial Γ(P, ⊤) ⧸ relations := Ideal.Quotient.mk relations Polynomial.X
  have hroot₁ : root ^ p = algebraMap Γ(P, ⊤) (Polynomial Γ(P, ⊤) ⧸ relations) x := by
    simpa [sub_eq_zero] using aeval_root_eq_zero (I := relations)
      (Ideal.subset_span (by simp) : Polynomial.X ^ p - Polynomial.C x ∈ relations)
  have hroot₂ : algebraMap Γ(P, ⊤) (Polynomial Γ(P, ⊤) ⧸ relations) (p : Γ(P, ⊤)) * root =
      algebraMap Γ(P, ⊤) (Polynomial Γ(P, ⊤) ⧸ relations) y := by
    simpa [sub_eq_zero] using aeval_root_eq_zero (I := relations)
      (Ideal.subset_span (by simp) :
        Polynomial.C (p : Γ(P, ⊤)) * Polynomial.X - Polynomial.C y ∈ relations)
  have hx : x = φ.hom root ^ p := by
    simpa only [map_pow, hφ] using (congrArg φ.hom hroot₁).symm
  have hy : y = (p : Γ(P, ⊤)) * φ.hom root := by
    simpa only [map_mul, hφ] using (congrArg φ.hom hroot₂).symm
  exact ⟨φ.hom root, ⟨hx, hy⟩, fun b hb => eq_of_pow_eq_of_natCast_mul_eq hp
    (by rw [← hb.1, ← hx]) (by rw [← hb.2, ← hy])⟩

end Sections

variable {X : Scheme.{u}} {I : UniversalHomeomorphismOver X}

/-- Initiality turns a universal homeomorphism onto the initial universal homeomorphism into a
retraction: the initial object maps back, and the composite is the identity. -/
theorem exists_section_of_isInitial_universalHomeomorphismOver (hI : IsInitial I)
    {Z : Scheme.{u}} (h : Z ⟶ I.obj.left) (hh : UniversalHomeomorphism h) :
    ∃ s : I.obj.left ⟶ Z, s ≫ h = 𝟙 I.obj.left := by
  let T : UniversalHomeomorphismOver X :=
    ⟨Over.mk (h ≫ I.obj.hom),
      universalHomeomorphism_hasTwoOutOfThreeProperty.comp_mem h I.obj.hom hh I.property⟩
  let k : T ⟶ I := ObjectProperty.homMk (Over.homMk h rfl)
  exact ⟨(hI.to T).hom.left,
    congrArg (fun m : I ⟶ I => m.hom.left) (hI.hom_ext (hI.to T ≫ k) (𝟙 I))⟩

/-- An initial object of the category of universal homeomorphisms onto a scheme is reduced. -/
theorem isReduced_of_isInitial_universalHomeomorphismOver (hI : IsInitial I) :
    IsReduced I.obj.left := by
  obtain ⟨s, hs⟩ := exists_section_of_isInitial_universalHomeomorphismOver hI
    I.obj.left.reductionι (universalHomeomorphism_nilradical_subschemeι I.obj.left)
  have hrs : I.obj.left.reductionι ≫ s = 𝟙 I.obj.left.reduction :=
    (cancel_mono I.obj.left.reductionι).mp (by
      rw [Category.assoc, hs, Category.comp_id, Category.id_comp])
  have : IsIso I.obj.left.reductionι := ⟨s, hrs, hs⟩
  exact isReduced_of_isOpenImmersion (inv I.obj.left.reductionι)

section Affine

variable [IsAffine X]

/-- **Stacks Project, Tag 0EUS.** Over an affine base the ring of sections of the initial
universal homeomorphism is absolutely weakly normal. -/
theorem isAbsolutelyWeaklyNormalRing_of_isInitial_universalHomeomorphismOver
    (hI : IsInitial I) : IsAbsolutelyWeaklyNormalRing Γ(I.obj.left, ⊤) := by
  have : IsAffine I.obj.left := isAffine_of_universalHomeomorphism I.obj.hom I.property
  have : IsReduced I.obj.left := isReduced_of_isInitial_universalHomeomorphismOver hI
  exact isAbsolutelyWeaklyNormalRing_of_sections
    (exists_section_of_isInitial_universalHomeomorphismOver hI)

end Affine

/-- A ring map out of a reduced ring whose morphism of spectra is a universal homeomorphism is
injective: the morphism of spectra is surjective, hence dominant, so the kernel is contained in
the nilradical and therefore vanishes. -/
theorem injective_of_universalHomeomorphism_specMap {S R : Type u} [CommRing S] [CommRing R]
    [_root_.IsReduced S] (ψ : S →+* R)
    (hψ : UniversalHomeomorphism (Scheme.Spec.map (CommRingCat.ofHom ψ).op)) :
    Function.Injective ψ := by
  have hsurj : Function.Surjective (PrimeSpectrum.comap ψ) := by
    have h := MorphismProperty.universally_le _ _ hψ.universally_isHomeomorph
    change IsHomeomorph (PrimeSpectrum.comap ψ) at h
    exact h.surjective
  have hker : RingHom.ker ψ = ⊥ := by
    refine le_antisymm ?_ bot_le
    simpa [nilradical_eq_zero] using
      (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical ψ).mp hsurj.denseRange
  exact (RingHom.injective_iff_ker_eq_bot ψ).2 hker

/-- An injective ring map and the inclusion of its range induce the same morphism of spectra up
to the isomorphism of the spectrum of the range with the spectrum of the source. -/
theorem exists_specMap_range_subtype_iso {S R : Type u} [CommRing S] [CommRing R]
    (ψ : S →+* R) (hinj : Function.Injective ψ) :
    ∃ e : Spec (CommRingCat.of (ψ.range : Subring R)) ≅ Spec (CommRingCat.of S),
      Scheme.Spec.map (CommRingCat.ofHom (ψ.range : Subring R).subtype).op ≫ e.hom =
        Scheme.Spec.map (CommRingCat.ofHom ψ).op := by
  let eR : S ≃+* (ψ.range : Subring R) := RingEquiv.ofBijective ψ.rangeRestrict
    ⟨fun u v h => hinj (congrArg Subtype.val h), RingHom.rangeRestrict_surjective ψ⟩
  refine ⟨Scheme.Spec.mapIso eR.toCommRingCatIso.op, ?_⟩
  have he : (Scheme.Spec.mapIso eR.toCommRingCatIso.op).hom =
      Scheme.Spec.map (CommRingCat.ofHom eR.toRingHom).op := rfl
  rw [he, ← Functor.map_comp, ← op_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- The inclusion of the range of an injective ring map induces a universal homeomorphism on
spectra as soon as the map itself does. -/
theorem universalHomeomorphism_specMap_range_subtype {S R : Type u} [CommRing S] [CommRing R]
    (ψ : S →+* R) (hinj : Function.Injective ψ)
    (hψ : UniversalHomeomorphism (Scheme.Spec.map (CommRingCat.ofHom ψ).op)) :
    UniversalHomeomorphism
      (Scheme.Spec.map (CommRingCat.ofHom (ψ.range : Subring R).subtype).op) := by
  obtain ⟨e, hfactor⟩ := exists_specMap_range_subtype_iso ψ hinj
  refine universalHomeomorphism_hasTwoOutOfThreeProperty.of_postcomp _ e.hom
    (universalHomeomorphism_of_isIso _) ?_
  rwa [hfactor]

/-- A ring map onto a reduced ring whose morphism of spectra is a universal homeomorphism is
bijective as soon as its source is absolutely weakly normal: injectivity is dominance, and an
element outside the image would be a special element of Stacks Tag 0CNC for the image subring,
hence already a power root in the source. -/
private theorem bijective_of_universalHomeomorphism_of_isAbsolutelyWeaklyNormalRing
    {S R : Type u} [CommRing S] [CommRing R] [_root_.IsReduced R] (ψ : S →+* R)
    (hψ : UniversalHomeomorphism (Scheme.Spec.map (CommRingCat.ofHom ψ).op))
    (hS : IsAbsolutelyWeaklyNormalRing S) : Function.Bijective ψ := by
  have : _root_.IsReduced S := absolutelyWeaklyNormalRing_isReduced hS
  have hinj : Function.Injective ψ := injective_of_universalHomeomorphism_specMap ψ hψ
  refine ⟨hinj, ?_⟩
  set C : Subring R := ψ.range
  have hCsub : UniversalHomeomorphism (Scheme.Spec.map (CommRingCat.ofHom C.subtype).op) :=
    universalHomeomorphism_specMap_range_subtype ψ hinj hψ
  intro b
  by_contra hb
  have hCtop : C ≠ ⊤ := fun htop => hb (RingHom.range_eq_top.mp htop b)
  rcases exists_special_element_of_universalHomeomorphism C hCtop with
    ⟨c, hc, hc₂, hc₃⟩ | ⟨p, hp, c, hc, hpc, hcp⟩
  · obtain ⟨x, hx⟩ := RingHom.mem_range.mp hc₂
    obtain ⟨y, hy⟩ := RingHom.mem_range.mp hc₃
    have hxy : x ^ 3 = y ^ 2 := hinj <| by
      rw [map_pow, map_pow, hx, hy]
      ring
    obtain ⟨a, ha, -⟩ := hS.isSeminormalRing x y hxy
    exact hc (RingHom.mem_range.2 ⟨a, Stacks.RingTheory.Seminormal.eq_of_sq_eq_of_cube_eq
      (by rw [← map_pow, ← ha.1, hx]) (by rw [← map_pow, ← ha.2, hy])⟩)
  · obtain ⟨x, hx⟩ := RingHom.mem_range.mp hcp
    obtain ⟨y, hy⟩ := RingHom.mem_range.mp hpc
    have hxy : (p : S) ^ p * x = y ^ p := hinj <| by
      rw [map_mul, map_pow, map_pow, map_natCast, hx, hy]
      ring
    obtain ⟨a, ha, -⟩ := hS.existsUnique_of_prime_pow_mul_eq_pow hp hxy
    refine hc (RingHom.mem_range.2 ⟨a, ?_⟩)
    refine eq_of_pow_eq_of_natCast_mul_eq hp ?_ ?_
    · rw [← map_pow, ← ha.1, hx]
    · calc (p : R) * ψ a = ψ ((p : S) * a) := by rw [map_mul, map_natCast]
        _ = ψ y := by rw [← ha.2]
        _ = (p : R) * c := hy

/-- **Stacks Project, Tag 0EUS.** Over an affine base the canonical morphism from the initial
universal homeomorphism to a universal homeomorphism with absolutely weakly normal sections is
an isomorphism. -/
theorem isIso_of_isInitial_universalHomeomorphismOver [IsAffine X] (hI : IsInitial I)
    (T : UniversalHomeomorphismOver X)
    (hT : IsAbsolutelyWeaklyNormalRing Γ(T.obj.left, ⊤)) :
    IsIso ((hI.to T).hom.left) := by
  have : IsAffine I.obj.left := isAffine_of_universalHomeomorphism I.obj.hom I.property
  have : IsAffine T.obj.left := isAffine_of_universalHomeomorphism T.obj.hom T.property
  have : IsReduced I.obj.left := isReduced_of_isInitial_universalHomeomorphismOver hI
  have hfU : UniversalHomeomorphism ((hI.to T).hom.left) := by
    refine universalHomeomorphism_hasTwoOutOfThreeProperty.of_postcomp _ T.obj.hom
      T.property ?_
    rw [(hI.to T).hom.w]
    exact I.property
  have hSpec : UniversalHomeomorphism (Spec.map ((hI.to T).hom.left).appTop) := by
    rw [universalHomeomorphism_iff] at hfU ⊢
    exact ((MorphismProperty.universally (topologically @IsHomeomorph)).arrow_mk_iso_iff
      (arrowIsoSpecΓOfIsAffine ((hI.to T).hom.left))).mp hfU
  rw [← MorphismProperty.isomorphisms.iff,
    (MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (arrowIsoSpecΓOfIsAffine ((hI.to T).hom.left)),
    MorphismProperty.isomorphisms.iff, isIso_SpecMap_iff]
  refine bijective_of_universalHomeomorphism_of_isAbsolutelyWeaklyNormalRing
    ((hI.to T).hom.left).appTop.hom ?_ hT
  rwa [CommRingCat.ofHom_hom]

end AlgebraicGeometry

end
