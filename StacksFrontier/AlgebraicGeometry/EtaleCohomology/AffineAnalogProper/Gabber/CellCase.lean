module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.Gabber.ConstantCase
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.Gabber.Devissage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AlgClosedCase
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FiniteSupportRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.DenseOpenRestriction

/-!
# Gabber's theorem for a sheaf supported on a basic locally closed set of an absolutely
integrally closed cover

Let `(A, I)` be a henselian pair, `i : Z = Spec (A ⧸ I) ⟶ X = Spec A`, and let `C` be an
absolutely integrally closed ring integral over `A`, with `f : Spec C ⟶ X`. If an abelian sheaf
`H` on `(Spec C)_étale` vanishes off a basic locally closed set `V(B) ∩ D(c)` and is constant with
finite value `E` on it, then restriction `H^q(X, f_* H) → H^q(Z, (f_* H)|_Z)` is bijective in
every degree.

Indeed `H` is the direct image, along the closed immersion of the reduced subscheme
`T = V(B)`, of the extension by zero of the constant sheaf `E` from the open `D(c) ∩ T`; and on
`T` the sequence `0 → j_! E → E → i_* E → 0` of the open `D(c)` and its closed complement reduces
the claim to direct images of constant sheaves from the absolutely integrally closed rings
`C/√(B)` and `(C/√(B))/(c)`, which is
`Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_directImage_constant`.

## Main results

* `Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_directImage_of_cellSet`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

/-- For an `A`-algebra `D` and an ideal `J` of `D`, the morphism `Spec (D ⧸ J) ⟶ Spec A` is the
closed immersion `Spec (D ⧸ J) ⟶ Spec D` followed by `Spec D ⟶ Spec A`. -/
theorem specMap_algebraMap_quotient_eq (A : Type u) [CommRing A] (D : Type u) [CommRing D]
    [Algebra A D] (J : Ideal D) :
    Spec.map (CommRingCat.ofHom (algebraMap A (D ⧸ J))) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A D)) := by
  rw [← Spec.map_comp]
  rfl

variable (A : Type u) [CommRing A] (I : Ideal A) (hI : HenselianPair A I)
include hI

/-- **Gabber's theorem for the extension by zero of a finite constant sheaf from a basic open
of an absolutely integrally closed cover.** -/
theorem bijective_etaleCohomologyRestrictionMap_directImage_extensionByZero_constant
    (D : Type u) [CommRing D] [Algebra A D] [Algebra.IsIntegral A D]
    (hD : IsAbsolutelyIntegrallyClosed D) (d : D) (E : AddCommGrpCat.{u + 1}) [Finite E]
    (q : ℕ) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      ((etaleAbelianDirectImage.{u, 0} (Spec.map (CommRingCat.ofHom (algebraMap A D)))).obj
        ((EtaleCohomology.extensionByZero.{u, 0} (basicOpenImmersion d)).obj
          ((etaleRestriction.{u, 0} (basicOpenImmersion d)).obj
            ((constantSheaf (Spec (.of D)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj E))))
      q) := by
  let gD := Spec.map (CommRingCat.ofHom (algebraMap A D))
  have : IsIntegralHom gD :=
    IsIntegralHom.SpecMap_iff.mpr fun x => Algebra.IsIntegral.isIntegral (R := A) x
  have : PreservesFiniteColimits (etaleAbelianDirectImage.{u, 0} gD) :=
    preservesFiniteColimits_etaleAbelianDirectImage_of_isIntegralHom.{u, 0} gD
  have : (etaleAbelianDirectImage.{u, 0} gD).IsRightAdjoint :=
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} gD).isRightAdjoint
  let ED := (constantSheaf (Spec (.of D)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj E
  obtain ⟨_, hS⟩ := shortExact_extensionByZero_etaleAbelianDirectImage.{u, 0}
    (zeroLocusImmersion d) (basicOpenImmersion d) (range_basicOpenImmersion_eq_compl d) ED
  refine etaleCohomologyRestrictionMap_bijective_of_shortExact_X₁.{u, 0, u + 1} _
    (hS.map_of_exact (etaleAbelianDirectImage.{u, 0} gD))
    (bijective_etaleCohomologyRestrictionMap_directImage_constant A I hI D hD E)
    (fun q => ?_) q
  let g' := Spec.map (CommRingCat.ofHom (algebraMap A (D ⧸ Ideal.span {d})))
  refine bijective_etaleCohomologyRestrictionMap_of_iso _
    (((etaleAbelianDirectImageCompIso'.{u, 0} (zeroLocusImmersion d) gD g'
      (specMap_algebraMap_quotient_eq A D _)).app _) ≪≫
      (etaleAbelianDirectImage.{u, 0} g').mapIso
        ((etaleAbelianInverseImageConstantIso.{u, 0} (zeroLocusImmersion d)).app E)).symm q
    (bijective_etaleCohomologyRestrictionMap_directImage_constant A I hI _
      (isAbsolutelyIntegrallyClosed_quotient D (Ideal.span {d}) hD) E q)

omit hI in
/-- The image of a point `z` of `Spec S` under `Spec φ` for a ring map `φ : R →+* S` is the prime
ideal `φ⁻¹(z)` of `R`. -/
theorem specMap_base_asIdeal {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (z : Spec (.of S)) :
    ((Spec.map (CommRingCat.ofHom φ)).base z).asIdeal = z.asIdeal.comap φ := by
  rw [Spec.map_base]
  rfl

omit hI in
/-- The closed immersion `Spec (C ⧸ √(B)) ⟶ Spec C` has image `V(B)`. -/
theorem mem_range_specMap_quotient_radical_span_iff {C : Type u} [CommRing C] (B : List C)
    (x : Spec (.of C)) :
    x ∈ Set.range (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Ideal.span {b | b ∈ B}).radical))).base ↔ ∀ b ∈ B, b ∈ x.asIdeal := by
  have h := range_comap_of_surjective _ _
    (Ideal.Quotient.mk_surjective (I := (Ideal.span {b | b ∈ B}).radical))
  rw [Ideal.mk_ker] at h
  change x ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {b | b ∈ B}).radical))
    ↔ _
  rw [h]
  change (Ideal.span {b | b ∈ B}).radical ≤ x.asIdeal ↔ _
  rw [x.isPrime.radical_le_iff, Ideal.span_le]
  exact Iff.rfl

omit hI in
/-- For a ring map `φ : C →+* D`, the image in `Spec C` of `V(φ c) ⊆ Spec D` lies in `V(c)`. -/
theorem mem_asIdeal_zeroLocusImmersion_comp_specMap {C D : Type u} [CommRing C] [CommRing D]
    (φ : C →+* D) (c : C) (y : Spec (.of (D ⧸ Ideal.span {φ c}))) :
    c ∈ ((zeroLocusImmersion (φ c) ≫ Spec.map (CommRingCat.ofHom φ)).base y).asIdeal := by
  rw [Scheme.Hom.comp_apply, specMap_base_asIdeal]
  exact (mem_range_zeroLocusImmersion (φ c) _).mp ⟨y, rfl⟩

omit hI in
/-- For a ring map `φ : C →+* D`, the image in `Spec C` of `D(φ c) ⊆ Spec D` lies in `D(c)`. -/
theorem notMem_asIdeal_basicOpenImmersion_comp_specMap {C D : Type u} [CommRing C]
    [CommRing D] (φ : C →+* D) (c : C) (y : Spec (.of (Localization.Away (φ c)))) :
    c ∉ ((basicOpenImmersion (φ c) ≫ Spec.map (CommRingCat.ofHom φ)).base y).asIdeal := by
  rw [Scheme.Hom.comp_apply, specMap_base_asIdeal]
  exact (mem_range_basicOpenImmersion (φ c) _).mp ⟨y, rfl⟩

omit hI in
/-- An abelian sheaf vanishing off a subset of the image of a closed immersion `t` is the direct
image of its inverse image along `t`. -/
theorem isIso_unit_app_of_vanishesOffSet {X Y : Scheme.{u}} (t : Y ⟶ X) [IsClosedImmersion t]
    {H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {S : Set X}
    (hv : VanishesOffSet H S) (hS : S ⊆ Set.range t.base) :
    IsIso ((etaleAbelianInverseImageDirectImageAdj.{u, 0} t).unit.app H) := by
  let U₀ : X.Opens := ⟨(Set.range t.base)ᶜ, t.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  obtain ⟨_, hS₀⟩ := shortExact_extensionByZero_etaleAbelianDirectImage.{u, 0} t U₀.ι
    (by rw [Scheme.Opens.range_ι]; rfl) H
  have : (EtaleCohomology.extensionByZero.{u, 0} U₀.ι).IsLeftAdjoint :=
    (extensionByZeroAdj.{u, 0} U₀.ι).isLeftAdjoint
  refine hS₀.isIso_g_iff.mpr ((EtaleCohomology.extensionByZero.{u, 0} U₀.ι).map_isZero
    ((hv U₀.ι ?_).of_iso ((etaleAbelianInverseImageRestrictionIso.{u, 0} U₀.ι).app H).symm))
  rw [Scheme.Opens.range_ι, Set.disjoint_left]
  exact fun x hx hxS => hx (hS hxS)

omit hI in
/-- An abelian sheaf on `Spec D` whose inverse image to `V(d)` vanishes is the extension by zero
of its restriction to `D(d)`. -/
theorem isIso_counit_app_basicOpenImmersion {D : Type u} [CommRing D] (d : D)
    {G : Sheaf (Spec (.of D)).smallEtaleTopology AddCommGrpCat.{u + 1}}
    (hG : IsZero ((etaleAbelianInverseImage.{u, 0} (zeroLocusImmersion d)).obj G)) :
    IsIso ((extensionByZeroAdj.{u, 0} (basicOpenImmersion d)).counit.app G) := by
  obtain ⟨_, hS₁⟩ := shortExact_extensionByZero_etaleAbelianDirectImage.{u, 0}
    (zeroLocusImmersion d) (basicOpenImmersion d) (range_basicOpenImmersion_eq_compl d) G
  have : (etaleAbelianDirectImage.{u, 0} (zeroLocusImmersion d)).IsRightAdjoint :=
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} (zeroLocusImmersion d)).isRightAdjoint
  exact hS₁.isIso_f_iff.mpr
    (Functor.map_isZero (etaleAbelianDirectImage.{u, 0} (zeroLocusImmersion d)) hG)

/-- **Gabber's theorem for a sheaf supported on a basic locally closed set of an absolutely
integrally closed cover.** Let `C` be absolutely integrally closed and integral over `A`, and let
`H` be an abelian sheaf on `(Spec C)_étale` which vanishes off `V(B) ∩ D(c)` and is constant there
with finite value. Then restriction to `Spec (A ⧸ I)` is bijective in every degree on the
cohomology of its direct image to `Spec A`. -/
theorem bijective_etaleCohomologyRestrictionMap_directImage_of_cellSet
    (C : Type u) [CommRing C] [Algebra A C] [Algebra.IsIntegral A C]
    (hC : IsAbsolutelyIntegrallyClosed C) (B : List C) (c : C) (E : AddCommGrpCat.{u + 1})
    [Finite E] (H : Sheaf (Spec (.of C)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hv : VanishesOffSet H (cellSet B c)) (hc : IsConstantOnSet H (cellSet B c) E) (q : ℕ) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      ((etaleAbelianDirectImage.{u, 0} (Spec.map (CommRingCat.ofHom (algebraMap A C)))).obj H)
      q) := by
  let 𝔟 : Ideal C := (Ideal.span {b | b ∈ B}).radical
  let D := C ⧸ 𝔟
  have : IsReduced D := (Ideal.isRadical_iff_quotient_reduced 𝔟).mp (Ideal.radical_isRadical _)
  let t : Spec (.of D) ⟶ Spec (.of C) := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔟))
  have : IsClosedImmersion t := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have e₁ : IsIso ((etaleAbelianInverseImageDirectImageAdj.{u, 0} t).unit.app H) :=
    isIso_unit_app_of_vanishesOffSet t hv fun x hx =>
      (mem_range_specMap_quotient_radical_span_iff B x).mpr hx.1
  let d : D := Ideal.Quotient.mk 𝔟 c
  let HT := (etaleAbelianInverseImage.{u, 0} t).obj H
  have e₂ : IsIso ((extensionByZeroAdj.{u, 0} (basicOpenImmersion d)).counit.app HT) := by
    refine isIso_counit_app_basicOpenImmersion d ((hv (zeroLocusImmersion d ≫ t) ?_).of_iso
      ((etaleAbelianInverseImageCompIso'.{u, 0} (zeroLocusImmersion d) t _ rfl).app H).symm)
    rw [Set.disjoint_left]
    rintro _ ⟨y, rfl⟩ hx
    exact hx.2 (mem_asIdeal_zeroLocusImmersion_comp_specMap (Ideal.Quotient.mk 𝔟) c y)
  have hW : Set.range (basicOpenImmersion d ≫ t).base ⊆ cellSet B c := by
    rintro _ ⟨y, rfl⟩
    exact ⟨(mem_range_specMap_quotient_radical_span_iff B _).mp ⟨_, rfl⟩,
      notMem_asIdeal_basicOpenImmersion_comp_specMap (Ideal.Quotient.mk 𝔟) c y⟩
  obtain ⟨e₃⟩ := hc (basicOpenImmersion d ≫ t) hW
  let ET := (constantSheaf (Spec (.of D)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj E
  let eres : (etaleRestriction.{u, 0} (basicOpenImmersion d)).obj HT ≅
      (etaleRestriction.{u, 0} (basicOpenImmersion d)).obj ET :=
    ((etaleAbelianInverseImageRestrictionIso.{u, 0} (basicOpenImmersion d)).app HT).symm ≪≫
      ((etaleAbelianInverseImageCompIso'.{u, 0} (basicOpenImmersion d) t _ rfl).app H).symm ≪≫
      e₃ ≪≫ ((etaleAbelianInverseImageConstantIso.{u, 0} (basicOpenImmersion d)).app E).symm ≪≫
      ((etaleAbelianInverseImageRestrictionIso.{u, 0} (basicOpenImmersion d)).app ET)
  let f := Spec.map (CommRingCat.ofHom (algebraMap A C))
  let gD := Spec.map (CommRingCat.ofHom (algebraMap A D))
  let eH : (etaleAbelianDirectImage.{u, 0} f).obj H ≅
      (etaleAbelianDirectImage.{u, 0} gD).obj
        ((EtaleCohomology.extensionByZero.{u, 0} (basicOpenImmersion d)).obj
          ((etaleRestriction.{u, 0} (basicOpenImmersion d)).obj ET)) :=
    (etaleAbelianDirectImage.{u, 0} f).mapIso
      (asIso ((etaleAbelianInverseImageDirectImageAdj.{u, 0} t).unit.app H) ≪≫
        (etaleAbelianDirectImage.{u, 0} t).mapIso
          ((asIso ((extensionByZeroAdj.{u, 0} (basicOpenImmersion d)).counit.app HT)).symm ≪≫
            (EtaleCohomology.extensionByZero.{u, 0} (basicOpenImmersion d)).mapIso eres)) ≪≫
      (etaleAbelianDirectImageCompIso'.{u, 0} t f gD
        (specMap_algebraMap_quotient_eq A C 𝔟)).app _
  exact bijective_etaleCohomologyRestrictionMap_of_iso _ eH.symm q
    (bijective_etaleCohomologyRestrictionMap_directImage_extensionByZero_constant A I hI D
      (isAbsolutelyIntegrallyClosed_quotient C 𝔟 hC) d E q)

end Stacks.EtaleCohomology
