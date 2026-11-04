module

public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.RegularImmersion
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.RegularImmersionFpqc
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularImmersionComposition
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Defs
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Perfect
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.KoszulRegularSmoothCover
public import StacksFrontier.RingTheory.CompleteIntersection.RingMap.Criteria
public import StacksFrontier.RingTheory.Koszul.Concatenation
public import StacksFrontier.RingTheory.Koszul.Localization
public import StacksFrontier.RingTheory.Smooth.Syntomic
public import StacksCore.Tactic.StacksAttribute

/-!
# Local complete intersection morphisms of affine schemes

A morphism of affine schemes is a local complete intersection morphism exactly when the induced
homomorphism of their rings of global sections is a local complete intersection homomorphism.

## Main results

* `AlgebraicGeometry.isLocalCompleteIntersectionMorphism_iff_appTop`: **Stacks 07DB**.

## Implementation notes

The morphism side is `AlgebraicGeometry.IsLocalCompleteIntersectionMorphism`, Stacks 069F, and the
ring side is `RingHom.IsLocalCompleteIntersection`, Stacks 07D0. Affineness is carried by instances
on the source and the target rather than by chosen presentations as spectra, so the ring map of the
statement is `f.appTop.hom : Γ(S, ⊤) →+* Γ(X, ⊤)`.

Being Koszul at a point provides an immersion of a neighbourhood into *some* scheme smooth over
the target, and the affine criterion for Koszul-regular ideal sheaves, Stacks 063G, shrinks it to
a Koszul-regular closed immersion of an affine open of the source into an affine open of that
smooth scheme. Over an affine target such a chart presents the sections of the source as the
quotient of a smooth algebra by a Koszul-regular ideal; a smooth algebra is syntomic and hence a
local complete intersection by Stacks 07D3, so concatenating Koszul-regular generators of the two
ideals, Stacks 0669, makes the chart a local complete intersection over the target. Locality of
the property on the target, Stacks 07D1, assembles the charts. No independence of the chosen
smooth ambient scheme is needed: one arbitrary smooth affine ambient already carries its own
Koszul-regular presentation.

Conversely a finite polynomial presentation with Koszul-regular kernel realizes the morphism as a
Koszul-regular closed immersion into affine space over the target followed by the smooth
projection, which is the factorization the definition asks for at every point of the source. That
the closed immersion is Koszul-regular is read off its kernel on global sections, for which the
coborder range of a closed immersion is the whole target and therefore constrains no
neighbourhood.

## References

* [Stacks Project, Tag 07DB](https://stacks.math.columbia.edu/tag/07DB)
* [Stacks Project, Tag 069F](https://stacks.math.columbia.edu/tag/069F)
* [Stacks Project, Tag 07D0](https://stacks.math.columbia.edu/tag/07D0)
* [Stacks Project, Tag 07D1](https://stacks.math.columbia.edu/tag/07D1)
* [Stacks Project, Tag 07D3](https://stacks.math.columbia.edu/tag/07D3)
* [Stacks Project, Tag 063G](https://stacks.math.columbia.edu/tag/063G)
* [Stacks Project, Tag 0669](https://stacks.math.columbia.edu/tag/0669)
-/

@[expose] public section

open CategoryTheory
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace AlgebraicGeometry

/-! ### Quotients of smooth algebras by Koszul-regular ideals -/

/-- Koszul-regularity of a finite family is preserved by a flat ring homomorphism. -/
private theorem koszulRegular_of_flat {R S : Type u} [CommRing R] [CommRing S]
    (ψ : R →+* S) (hψ : ψ.Flat) {r : ℕ} (f : Fin r → R) (hf : Koszul.IsKoszulRegular f) :
    Koszul.IsKoszulRegular fun i => ψ (f i) := by
  let _ := ψ.toAlgebra
  have : Module.Flat R S := hψ
  simpa only [RingHom.algebraMap_toAlgebra] using Koszul.isKoszulRegular_map_of_flat (S := S) f hf

/-- The ideal spanned by a concatenation of two families is the sum of the two spans. -/
private theorem span_range_append {R : Type*} [CommRing R] {n m : ℕ} (f : Fin n → R)
    (g : Fin m → R) :
    Ideal.span (Set.range (Fin.append f g)) =
      Ideal.span (Set.range f) ⊔ Ideal.span (Set.range g) := by
  refine le_antisymm (Ideal.span_le.mpr ?_) (sup_le (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_))
  · rintro x ⟨i, rfl⟩
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · exact Ideal.mem_sup_left (Ideal.subset_span ⟨i, by simp⟩)
    · exact Ideal.mem_sup_right (Ideal.subset_span ⟨j, by simp⟩)
  · rintro x ⟨i, rfl⟩
    exact Ideal.subset_span ⟨Fin.castAdd m i, by simp⟩
  · rintro x ⟨j, rfl⟩
    exact Ideal.subset_span ⟨Fin.natAdd n j, by simp⟩

/-- The image of the ideal spanned by a family is spanned by the image family. -/
private theorem map_span_range {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S) {r : ℕ}
    (fam : Fin r → R) :
    Ideal.map g (Ideal.span (Set.range fam)) = Ideal.span (Set.range fun i => g (fam i)) := by
  rw [Ideal.map_span, ← Set.range_comp]
  rfl

/-- If `p` presents `C` over `A` and `φ : C → D` is surjective with Koszul-regular kernel of
`φ ∘ p`, then `φ ∘ algebraMap A C` is a local complete intersection. -/
private theorem isLocalCompleteIntersection_comp_of_ker {A C D : Type u} [CommRing A] [CommRing C]
    [CommRing D] [Algebra A C] {φ : C →+* D} (hφ : Function.Surjective φ) {n : ℕ}
    (p : MvPolynomial (Fin n) A →ₐ[A] C) (hp : Function.Surjective p)
    (hk : Ideal.IsKoszulRegular (RingHom.ker (φ.comp p.toRingHom))) :
    RingHom.IsLocalCompleteIntersection (φ.comp (algebraMap A C)) := by
  let _ : Algebra A D := (φ.comp (algebraMap A C)).toAlgebra
  let p' : MvPolynomial (Fin n) A →ₐ[A] D :=
    { toRingHom := φ.comp p.toRingHom, commutes' := fun x => congrArg φ (p.commutes x) }
  exact ⟨Algebra.FiniteType.of_surjective p' (hφ.comp hp), n, p', hφ.comp hp, hk⟩

/-- A smooth ring homomorphism is a local complete intersection homomorphism, because a smooth
algebra is syntomic and a syntomic ring map is flat and a local complete intersection. -/
private theorem isLocalCompleteIntersection_of_smooth {A C : Type u} [CommRing A] [CommRing C]
    {a : A →+* C} (ha : a.Smooth) : RingHom.IsLocalCompleteIntersection a := by
  let _ : Algebra A C := a.toAlgebra
  have : Algebra.Smooth A C := ha
  exact ((RingHom.syntomic_iff_flat_and_isLocalCompleteIntersection a).mp
    (Algebra.Smooth.syntomic A C)).2

/-- **The quotient of a smooth algebra by a Koszul-regular ideal is a local complete
intersection.** If `A → C` is smooth and `C → D` is surjective with kernel spanned by a
Koszul-regular family, then `A → D` is a local complete intersection homomorphism. -/
private theorem isLocalCompleteIntersection_of_smooth_of_ker_eq_span
    {A C D : Type u} [CommRing A] [CommRing C] [CommRing D]
    {a : A →+* C} (ha : a.Smooth) {φ : C →+* D} (hφ : Function.Surjective φ)
    {r : ℕ} (fam : Fin r → C) (hfam : Koszul.IsKoszulRegular fam)
    (hker : RingHom.ker φ = Ideal.span (Set.range fam)) :
    RingHom.IsLocalCompleteIntersection (φ.comp a) := by
  classical
  let _ : Algebra A C := a.toAlgebra
  obtain ⟨-, n, p, hp, hkerp⟩ := isLocalCompleteIntersection_of_smooth ha
  choose famhat hfamhat using fun i => hp (fam i)
  have hmapfam : Ideal.map p.toRingHom (Ideal.span (Set.range famhat)) =
      Ideal.span (Set.range fam) := by
    rw [map_span_range]
    exact congrArg _ (congrArg Set.range (funext hfamhat))
  have hkerq : RingHom.ker (φ.comp p.toRingHom)
      = Ideal.span (Set.range famhat) ⊔ RingHom.ker p.toRingHom := by
    rw [← RingHom.comap_ker, hker, ← hmapfam, Ideal.comap_map_of_surjective p.toRingHom hp,
      ← RingHom.ker_eq_comap_bot]
  have hkosq : Ideal.IsKoszulRegular (RingHom.ker (φ.comp p.toRingHom)) := by
    intro P hP
    have hle : RingHom.ker p.toRingHom ≤ P.asIdeal :=
      le_trans (by rw [hkerq]; exact le_sup_right) hP
    obtain ⟨g, hg, s, e, he, hspan⟩ := hkerp P hle
    have hmaphat : Ideal.map (algebraMap (MvPolynomial (Fin n) A) (Localization.Away g))
        (Ideal.span (Set.range famhat))
        = Ideal.span (Set.range fun i =>
            algebraMap (MvPolynomial (Fin n) A) (Localization.Away g) (famhat i)) :=
      map_span_range _ _
    refine ⟨g, hg, s + r,
      Fin.append e fun i => algebraMap (MvPolynomial (Fin n) A) (Localization.Away g) (famhat i),
      ?_, ?_⟩
    · refine Koszul.koszul_regular_append e _ he ?_
      rw [← hspan]
      have hzero : ∀ x ∈ RingHom.ker p.toRingHom,
          ((Ideal.Quotient.mk (Ideal.map
              (algebraMap (MvPolynomial (Fin n) A) (Localization.Away g))
              (RingHom.ker p.toRingHom))).comp
            (algebraMap (MvPolynomial (Fin n) A) (Localization.Away g))) x = 0 := fun x hx =>
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hx)
      let ρ : C →+* (Localization.Away g) ⧸ Ideal.map
            (algebraMap (MvPolynomial (Fin n) A) (Localization.Away g))
            (RingHom.ker p.toRingHom) :=
        (Ideal.Quotient.lift (RingHom.ker p.toRingHom) _ hzero).comp
          (RingHom.quotientKerEquivOfSurjective hp).symm.toRingHom
      have hρ : ∀ x : MvPolynomial (Fin n) A, ρ (p x) =
          Ideal.Quotient.mk _
            (algebraMap (MvPolynomial (Fin n) A) (Localization.Away g) x) := by
        intro x
        have hx : (RingHom.quotientKerEquivOfSurjective hp).symm (p.toRingHom x)
            = Ideal.Quotient.mk (RingHom.ker p.toRingHom) x := by
          rw [RingEquiv.symm_apply_eq]
          rfl
        show (Ideal.Quotient.lift _ _ hzero)
          ((RingHom.quotientKerEquivOfSurjective hp).symm (p.toRingHom x)) = _
        rw [hx]
        rfl
      let _ : Algebra C ((Localization.Away g) ⧸ Ideal.map
          (algebraMap (MvPolynomial (Fin n) A) (Localization.Away g))
          (RingHom.ker p.toRingHom)) := ρ.toAlgebra
      have hloc : IsLocalization ((Submonoid.powers g).map p.toRingHom)
          ((Localization.Away g) ⧸ Ideal.map
            (algebraMap (MvPolynomial (Fin n) A) (Localization.Away g))
            (RingHom.ker p.toRingHom)) := by
        refine IsLocalization.of_surjective (Submonoid.powers g) (Localization.Away g)
          p.toRingHom hp (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective ?_ ?_
        · exact RingHom.ext fun x => (hρ x).symm
        · rw [Ideal.mk_ker]
      have hmf : Module.Flat C ((Localization.Away g) ⧸ Ideal.map
          (algebraMap (MvPolynomial (Fin n) A) (Localization.Away g))
          (RingHom.ker p.toRingHom)) :=
        IsLocalization.flat _ ((Submonoid.powers g).map p.toRingHom)
      have hflat : ρ.Flat := hmf
      have heq : ∀ i, Ideal.Quotient.mk (Ideal.map
          (algebraMap (MvPolynomial (Fin n) A) (Localization.Away g))
          (RingHom.ker p.toRingHom))
            (algebraMap (MvPolynomial (Fin n) A) (Localization.Away g) (famhat i))
          = ρ (fam i) := fun i => by rw [← hfamhat i, hρ]
      simpa only [heq] using koszulRegular_of_flat ρ hflat fam hfam
    · rw [hkerq, Ideal.map_sup, hspan, hmaphat, span_range_append, sup_comm]
  exact isLocalCompleteIntersection_comp_of_ker hφ p hp hkosq

/-- A local complete intersection homomorphism stays one after an isomorphism of the target. -/
private theorem isLocalCompleteIntersection_ringEquiv
    {A D D' : Type u} [CommRing A] [CommRing D] [CommRing D']
    {ψ : A →+* D} (ε : D ≃+* D') (h : RingHom.IsLocalCompleteIntersection ψ) :
    RingHom.IsLocalCompleteIntersection (ε.toRingHom.comp ψ) := by
  let _ : Algebra A D := ψ.toAlgebra
  obtain ⟨-, n, p, hp, hk⟩ := h
  exact isLocalCompleteIntersection_comp_of_ker ε.surjective p hp
    (by rwa [RingHom.ker_equiv_comp])

/-- A local complete intersection homomorphism into a ring is one into any other model of the
same principal localization. -/
private theorem isLocalCompleteIntersection_of_away
    {A B T T' : Type u} [CommRing A] [CommRing B] [CommRing T] [CommRing T']
    [Algebra B T] [Algebra B T'] (ψ : A →+* B) (b : B)
    [IsLocalization.Away b T] [IsLocalization.Away b T']
    (h : RingHom.IsLocalCompleteIntersection ((algebraMap B T).comp ψ)) :
    RingHom.IsLocalCompleteIntersection ((algebraMap B T').comp ψ) := by
  have hcomp : (algebraMap B T').comp ψ
      = (IsLocalization.algEquiv (Submonoid.powers b) T T').toRingEquiv.toRingHom.comp
        ((algebraMap B T).comp ψ) := by
    ext x
    exact ((IsLocalization.algEquiv (Submonoid.powers b) T T').commutes (ψ x)).symm
  rw [hcomp]
  exact isLocalCompleteIntersection_ringEquiv _ h

/-- **The principal localizations of a quotient of a smooth algebra by a Koszul-regular ideal are
local complete intersections.** -/
private theorem isLocalCompleteIntersection_away_of_smooth_of_ker_eq_span
    {A C D Dd : Type u} [CommRing A] [CommRing C] [CommRing D] [CommRing Dd] [Algebra D Dd]
    {a : A →+* C} (ha : a.Smooth) {φ : C →+* D} (hφ : Function.Surjective φ)
    {r : ℕ} (fam : Fin r → C) (hfam : Koszul.IsKoszulRegular fam)
    (hker : RingHom.ker φ = Ideal.span (Set.range fam))
    (c : C) (hc : IsLocalization.Away (φ c) Dd) :
    RingHom.IsLocalCompleteIntersection ((algebraMap D Dd).comp (φ.comp a)) := by
  classical
  let _ := hc
  have hmp : (Submonoid.powers c).map φ = Submonoid.powers (φ c) := Submonoid.map_powers φ c
  have hloc : IsLocalization ((Submonoid.powers c).map φ) Dd := by rw [hmp]; infer_instance
  let _ := hloc
  have hflatc : (algebraMap C (Localization.Away c)).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ (Submonoid.powers c))
  have ha' : ((algebraMap C (Localization.Away c)).comp a).Smooth :=
    RingHom.Smooth.comp ha (RingHom.Smooth.holdsForLocalizationAway (Localization.Away c) c)
  let φ' : Localization.Away c →+* Dd :=
    IsLocalization.map Dd φ (Submonoid.le_comap_map (Submonoid.powers c))
  have hφ' : Function.Surjective φ' :=
    IsLocalization.map_surjective_of_surjective (Submonoid.powers c) (Localization.Away c) Dd hφ
  have hkerφ' : RingHom.ker φ' = Ideal.span (Set.range fun i =>
      algebraMap C (Localization.Away c) (fam i)) := by
    have h := IsLocalization.ker_map (M := Submonoid.powers c) (S := Localization.Away c) Dd φ
      (rfl : (Submonoid.powers c).map φ = (Submonoid.powers c).map φ)
    rw [show φ' = _ from rfl, h, hker, map_span_range]
  have hfam' : Koszul.IsKoszulRegular fun i => algebraMap C (Localization.Away c) (fam i) :=
    koszulRegular_of_flat _ hflatc fam hfam
  have hmain := isLocalCompleteIntersection_of_smooth_of_ker_eq_span ha' hφ' _ hfam' hkerφ'
  have hcomp : φ'.comp ((algebraMap C (Localization.Away c)).comp a)
      = (algebraMap D Dd).comp (φ.comp a) := by
    rw [← RingHom.comp_assoc, show φ'.comp (algebraMap C (Localization.Away c))
      = (algebraMap D Dd).comp φ from IsLocalization.map_comp _, RingHom.comp_assoc]
  rwa [hcomp] at hmain

/-! ### The affine chart supplied by the Koszul condition at a point -/

/-- At a point where a morphism to an affine scheme is Koszul, every principal open of a suitable
affine open neighbourhood is a local complete intersection over the target. -/
private theorem isLocalCompleteIntersection_appLE_basicOpen_of_koszulAt
    {X S : Scheme.{u}} [IsAffine S] {f : X ⟶ S} {x : X} (hx : KoszulAt f x) :
    ∃ V : X.affineOpens, x ∈ V.1 ∧ ∀ d : Γ(X, V.1),
      RingHom.IsLocalCompleteIntersection (f.appLE ⊤ (X.basicOpen d) le_top).hom := by
  obtain ⟨-, U, hxU, P, i, π, hi, hreg, hπ, hfact⟩ := hx
  let _ := hi
  let _ := hπ
  obtain ⟨V₀, hzV₀, r, fam, hfam, hkerfam, -⟩ :=
    Stacks.AlgebraicGeometry.exists_affine_koszul_kernel i.liftCoborder hreg ⟨x, hxU⟩
  have hWaff : IsAffineOpen (i.liftCoborder ⁻¹ᵁ V₀.1) := V₀.2.preimage i.liftCoborder
  have hOaff : IsAffineOpen (i.coborderRange.ι ''ᵁ V₀.1) :=
    V₀.2.image_of_isOpenImmersion i.coborderRange.ι
  set VX := U.ι ''ᵁ (i.liftCoborder ⁻¹ᵁ V₀.1) with hVX
  have hVXaff : IsAffineOpen VX := hWaff.image_of_isOpenImmersion U.ι
  have eWO : (i.liftCoborder ⁻¹ᵁ V₀.1) ≤ i ⁻¹ᵁ (i.coborderRange.ι ''ᵁ V₀.1) :=
    le_of_eq (i.liftCoborder_preimage V₀.1)
  set φ := i.appLE (i.coborderRange.ι ''ᵁ V₀.1) (i.liftCoborder ⁻¹ᵁ V₀.1) eWO with hφ
  set a := π.appLE ⊤ (i.coborderRange.ι ''ᵁ V₀.1) le_top with ha
  -- the ambient affine chart is smooth over the target
  have hasm : RingHom.Smooth a.hom :=
    HasRingHomProperty.appLE (@Smooth) π ‹Smooth π› ⟨⊤, isAffineOpen_top S⟩ ⟨_, hOaff⟩ le_top
  -- on that chart the morphism is a surjection with Koszul-regular kernel
  have hiapp : φ = i.liftCoborder.app V₀.1 := by
    rw [hφ, liftCoborder_app, Scheme.Hom.appLE]
    congr 2
  have hsurj : Function.Surjective φ.hom := by
    rw [hiapp]; exact i.liftCoborder.app_surjective V₀.1 V₀.2
  have hkerφ : RingHom.ker φ.hom = Ideal.span (Set.range fam) := by
    rw [hiapp]; exact hkerfam
  -- and the morphism factors through it on sections
  have h1 : (U.ι ≫ f).appLE ⊤ (i.liftCoborder ⁻¹ᵁ V₀.1) le_top = f.appLE ⊤ VX le_top :=
    appLE_opens_ι_comp f U ⊤ _ le_top le_top
  have h2 : (i ≫ π).appLE ⊤ (i.liftCoborder ⁻¹ᵁ V₀.1) le_top = a ≫ φ :=
    (Scheme.Hom.appLE_comp_appLE i π ⊤ (i.coborderRange.ι ''ᵁ V₀.1)
      (i.liftCoborder ⁻¹ᵁ V₀.1) le_top eWO).symm
  have h3 : (U.ι ≫ f).appLE ⊤ (i.liftCoborder ⁻¹ᵁ V₀.1) le_top
      = (i ≫ π).appLE ⊤ (i.liftCoborder ⁻¹ᵁ V₀.1) le_top := by rw [hfact]
  have hfac : f.appLE ⊤ VX le_top = a ≫ φ := h1.symm.trans (h3.trans h2)
  obtain ⟨ψ, hψsurj, hψker, hψfac⟩ :
      ∃ ψ : Γ(P, i.coborderRange.ι ''ᵁ V₀.1) →+* Γ(X, VX),
        Function.Surjective ψ ∧ RingHom.ker ψ = Ideal.span (Set.range fam) ∧
          ψ.comp a.hom = (f.appLE ⊤ VX le_top).hom :=
    ⟨φ.hom, hsurj, hkerφ, by rw [hfac]; rfl⟩
  refine ⟨⟨_, hVXaff⟩, ⟨⟨x, hxU⟩, hzV₀, rfl⟩, ?_⟩
  intro d
  have hinst : IsLocalization.Away d Γ(X, X.basicOpen d) := hVXaff.isLocalization_basicOpen d
  obtain ⟨c, hc⟩ := hψsurj d
  have hmain := isLocalCompleteIntersection_away_of_smooth_of_ker_eq_span
    (Dd := Γ(X, X.basicOpen d)) hasm hψsurj fam hfam hψker c (by rw [hc]; exact hinst)
  have hstep : f.appLE ⊤ VX le_top ≫ X.presheaf.map (homOfLE (X.basicOpen_le d)).op
      = f.appLE ⊤ (X.basicOpen d) le_top :=
    Scheme.Hom.appLE_map f le_top (homOfLE (X.basicOpen_le d)).op
  have hcomp : (algebraMap Γ(X, VX) Γ(X, X.basicOpen d)).comp (ψ.comp a.hom)
      = (f.appLE ⊤ (X.basicOpen d) le_top).hom := by
    rw [hψfac, RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, hstep]
  rw [← hcomp]
  exact hmain

/-! ### The forward implication -/

/-- A local complete intersection morphism of affine schemes induces a local complete
intersection homomorphism on global sections. -/
private theorem isLocalCompleteIntersection_appTop_of_isLocalCompleteIntersectionMorphism
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] {f : X ⟶ S}
    (hf : IsLocalCompleteIntersectionMorphism f) :
    RingHom.IsLocalCompleteIntersection f.appTop.hom := by
  classical
  have key : ∀ x : X, ∃ b : Γ(X, ⊤), x ∈ X.basicOpen b ∧
      RingHom.IsLocalCompleteIntersection
        ((algebraMap Γ(X, ⊤) (Localization.Away b)).comp f.appTop.hom) := by
    intro x
    obtain ⟨V, hxV, H⟩ := isLocalCompleteIntersection_appLE_basicOpen_of_koszulAt (hf x)
    obtain ⟨b, hbV, hxb⟩ :=
      (isAffineOpen_top X).exists_basicOpen_le (V := V.1) ⟨x, hxV⟩ (Set.mem_univ x)
    refine ⟨b, hxb, ?_⟩
    have hdb : X.basicOpen (X.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op b)
        = X.basicOpen b := by
      rw [Scheme.basicOpen_res]
      exact inf_eq_right.mpr hbV
    have hH := H (X.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op b)
    rw [hdb] at hH
    have hAway : IsLocalization.Away b Γ(X, X.basicOpen b) :=
      (isAffineOpen_top X).isLocalization_basicOpen b
    have heq : (f.appLE ⊤ (X.basicOpen b) le_top).hom
        = (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen b)).comp f.appTop.hom := by
      rw [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp]
      rfl
    rw [heq] at hH
    exact isLocalCompleteIntersection_of_away (T := Γ(X, X.basicOpen b)) f.appTop.hom b hH
  choose b hxb hlci using key
  have hspan : Ideal.span (Set.range b) = ⊤ := by
    rw [← (isAffineOpen_top X).self_le_iSup_basicOpen_iff]
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨b x, Set.mem_range_self x⟩, hxb x⟩
  obtain ⟨t, hts, ht1⟩ := Submodule.mem_span_finite_of_mem_span
    (show (1 : Γ(X, ⊤)) ∈ Ideal.span (Set.range b) by rw [hspan]; trivial)
  refine RingHom.isLocalCompleteIntersection_of_localization_away f.appTop.hom
    (fun j : Fin (Fintype.card ↥t) => ((Fintype.equivFin ↥t).symm j : Γ(X, ⊤))) ?_ ?_
  · have hr : Set.range (fun j : Fin (Fintype.card ↥t) =>
        ((Fintype.equivFin ↥t).symm j : Γ(X, ⊤))) = (t : Set Γ(X, ⊤)) := by
      ext y
      refine ⟨?_, fun hy => ⟨Fintype.equivFin ↥t ⟨y, hy⟩, by simp⟩⟩
      rintro ⟨j, rfl⟩
      exact ((Fintype.equivFin ↥t).symm j).2
    rw [hr]
    exact Ideal.eq_top_of_isUnit_mem _ ht1 isUnit_one
  · intro j
    obtain ⟨x, hx⟩ := hts ((Fintype.equivFin ↥t).symm j).2
    rw [← hx]
    exact hlci x

/-! ### The affine bridge for the converse -/

/-- Koszul-regularity of an ideal is invariant under a ring isomorphism. -/
private theorem isKoszulRegular_map_ringEquiv {R T : Type u} [CommRing R] [CommRing T]
    (ε : R ≃+* T) {I : Ideal R} (hI : Ideal.IsKoszulRegular I) :
    Ideal.IsKoszulRegular (I.map (ε : R →+* T)) := by
  intro q hq
  obtain ⟨g, hg, r, e, he, hspan⟩ := hI (PrimeSpectrum.comap ε.toRingHom q)
    (Ideal.map_le_iff_le_comap.mp hq)
  have hM : (Submonoid.powers g).map (ε : R →* T) = Submonoid.powers (ε g) :=
    Submonoid.map_powers (ε : R →* T) g
  let ε' : Localization.Away g ≃+* Localization.Away (ε g) :=
    IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers g)
      (Localization.Away g) (Localization.Away (ε g)) ε hM
  have hcomm : ε'.toRingHom.comp (algebraMap R (Localization.Away g))
      = (algebraMap T (Localization.Away (ε g))).comp (ε : R →+* T) :=
    RingHom.ext fun x =>
      IsLocalization.ringEquivOfRingEquiv_eq (S := Localization.Away g)
        (Q := Localization.Away (ε g)) hM x
  refine ⟨ε g, hg, r, fun i => ε' (e i), ?_, ?_⟩
  · exact koszulRegular_of_flat ε'.toRingHom (RingHom.Flat.of_bijective ε'.bijective) e he
  · rw [Ideal.map_map, ← hcomm, ← Ideal.map_map, hspan, map_span_range]
    rfl

/-- Koszul-regularity of an ideal is invariant under pulling back along a ring isomorphism. -/
private theorem isKoszulRegular_comap_ringEquiv {R T : Type u} [CommRing R] [CommRing T]
    (ε : R ≃+* T) {I : Ideal T} (hI : Ideal.IsKoszulRegular I) :
    Ideal.IsKoszulRegular (I.comap (ε : R →+* T)) := by
  have h := isKoszulRegular_map_ringEquiv ε.symm hI
  rwa [Ideal.map_comap_of_equiv ε.symm, RingEquiv.symm_symm] at h

/-- A closed immersion whose defining ideal sheaf on the target is Koszul-regular is a
Koszul-regular immersion: for a closed immersion the canonical open of Stacks 063J is the whole
target, so it places no constraint on the witnessing neighbourhoods. -/
private theorem isKoszulRegularImmersion_of_isKoszulRegularIdealSheaf
    {Z Y : Scheme.{u}} (j : Z ⟶ Y) [IsClosedImmersion j]
    (hj : IsKoszulRegularIdealSheaf Y.toLocallyRingedSpace.toRingedSpace
      (definingIdealOfHom j)) :
    IsKoszulRegularImmersion j := by
  have hcb : ∀ y : Y, y ∈ j.coborderRange := by
    intro y
    show y ∈ coborder (Set.range j.base)
    rw [j.isClosedEmbedding.isClosed_range.coborder_eq]
    exact Set.mem_univ y
  refine (isKoszulRegularImmersion_iff j _
    (restrictSubmodule_coborderRange_definingIdealOfHom j)).mpr ?_
  refine (isKoszulRegularIdealSheaf_restrictSubmodule_iff j.coborderRange
    (definingIdealOfHom j)).mpr ?_
  intro y _ hy
  obtain ⟨U, hyU, r, fam, hK, hG⟩ := hj y hy
  exact ⟨U, hyU, fun z _ => hcb z, r, fam, hK, hG⟩

/-- **The affine criterion for a Koszul-regular closed immersion.** A closed immersion into an
affine scheme whose kernel on global sections is a Koszul-regular ideal is a Koszul-regular
immersion. -/
private theorem isKoszulRegularImmersion_of_isKoszulRegular_ker
    {Z Y : Scheme.{u}} [IsAffine Y] (j : Z ⟶ Y) [IsClosedImmersion j]
    (hj : Ideal.IsKoszulRegular (RingHom.ker j.appTop.hom)) :
    IsKoszulRegularImmersion j :=
  isKoszulRegularImmersion_of_isKoszulRegularIdealSheaf j
    ((isKoszulRegularIdealSheaf_iff_kerGeneratedBy j).mpr
      (kerGeneratedBy_of_isLocallySpannedBy
        (by intro A B _ _ φ hφ r fam hfam; exact koszulRegular_of_flat φ hφ fam hfam) j
        ((Ideal.isKoszulRegular_iff_isLocallySpannedBy _).mp hj)))

/-- The spectrum of a surjection with Koszul-regular kernel is a Koszul-regular immersion. -/
private theorem isKoszulRegularImmersion_specMap {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (hφ : Function.Surjective φ) (hk : Ideal.IsKoszulRegular (RingHom.ker φ.hom)) :
    letI : IsClosedImmersion (Spec.map φ) := IsClosedImmersion.spec_of_surjective φ hφ
    IsKoszulRegularImmersion (Spec.map φ) := by
  have : IsClosedImmersion (Spec.map φ) := IsClosedImmersion.spec_of_surjective φ hφ
  refine isKoszulRegularImmersion_of_isKoszulRegular_ker (Spec.map φ) ?_
  have hker : RingHom.ker (Spec.map φ).appTop.hom
      = (RingHom.ker φ.hom).comap
        ((Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv : Γ(Spec A, ⊤) →+* A) := by
    rw [show ((Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv : Γ(Spec A, ⊤) →+* A)
      = (Scheme.ΓSpecIso A).hom.hom from rfl]
    rw [← RingHom.ker_equiv_comp _ (Scheme.ΓSpecIso B).commRingCatIsoToRingEquiv,
      RingEquiv.toRingHom_eq_coe, Iso.commRingCatIsoToRingEquiv_toRingHom,
      ← CommRingCat.hom_comp, Scheme.ΓSpecIso_naturality, CommRingCat.hom_comp,
      RingHom.comap_ker]
  rw [hker]
  exact isKoszulRegular_comap_ringEquiv
    (Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv hk

/-- The spectrum of a surjection of rings with Koszul-regular kernel is a Koszul-regular
immersion. -/
alias isKoszulRegularImmersion_specMap_of_surjective := isKoszulRegularImmersion_specMap

/-! ### The converse implication -/

/-- A local complete intersection homomorphism of the rings of global sections makes a morphism of
affine schemes a local complete intersection morphism. -/
private theorem isLocalCompleteIntersectionMorphism_of_isLocalCompleteIntersection_appTop
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] {f : X ⟶ S}
    (hf : RingHom.IsLocalCompleteIntersection f.appTop.hom) :
    IsLocalCompleteIntersectionMorphism f := by
  let : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  obtain ⟨hft, n, p, hp, hkerp⟩ := hf
  -- the presentation of `f` by affine space over `S`
  let φ : CommRingCat.of (MvPolynomial (Fin n) Γ(S, ⊤)) ⟶ Γ(X, ⊤) :=
    CommRingCat.ofHom p.toRingHom
  have hφ : Function.Surjective φ := hp
  have : IsClosedImmersion (Spec.map φ) := IsClosedImmersion.spec_of_surjective φ hφ
  have hreg0 : IsKoszulRegularImmersion (Spec.map φ) :=
    isKoszulRegularImmersion_specMap φ hφ hkerp
  let i : X ⟶ Spec (CommRingCat.of (MvPolynomial (Fin n) Γ(S, ⊤))) := X.isoSpec.hom ≫ Spec.map φ
  have hi : IsClosedImmersion i := IsClosedImmersion.comp _ _
  have hregi : IsKoszulRegularImmersion i :=
    Stacks.AlgebraicGeometry.isKoszulRegularImmersion_iso_hom_comp
      X.isoSpec (Spec.map φ) hreg0
  -- the smooth structure morphism of affine space
  let ψ : Γ(S, ⊤) ⟶ CommRingCat.of (MvPolynomial (Fin n) Γ(S, ⊤)) :=
    CommRingCat.ofHom (algebraMap Γ(S, ⊤) (MvPolynomial (Fin n) Γ(S, ⊤)))
  have hψsm : Smooth (Spec.map ψ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    show RingHom.Smooth (algebraMap Γ(S, ⊤) (MvPolynomial (Fin n) Γ(S, ⊤)))
    rw [RingHom.smooth_algebraMap]
    exact ⟨inferInstance, inferInstance⟩
  let π : Spec (CommRingCat.of (MvPolynomial (Fin n) Γ(S, ⊤))) ⟶ S :=
    Spec.map ψ ≫ S.isoSpec.inv
  have hπ : Smooth π := by dsimp only [π]; infer_instance
  -- they compose to `f`
  have hcomm : φ.hom.comp ψ.hom = f.appTop.hom := by
    ext a
    exact p.commutes a
  have hmaps : Spec.map φ ≫ Spec.map ψ = Spec.map f.appTop := by
    rw [← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext hcomm)
  have hfac : i ≫ π = f := by
    dsimp only [i, π]
    rw [Category.assoc, ← Category.assoc (Spec.map φ), hmaps]
    have hn := Scheme.isoSpec_hom_naturality f
    simpa using congrArg (fun k => k ≫ S.isoSpec.inv) hn
  -- the factorization at every point
  have hlft : LocallyOfFiniteType f :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mpr hft
  intro x
  refine ⟨?_, ⊤, trivial, _, (⊤ : X.Opens).ι ≫ i, π, inferInstance, ?_, hπ, ?_⟩
  · exact (HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFiniteType)
      (Q := @RingHom.FiniteType)
      (RingHom.finiteType_stableUnderComposition.stableUnderCompositionWithLocalizationAway
        RingHom.finiteType_holdsForLocalizationAway).left).mp hlft x
  · exact Stacks.AlgebraicGeometry.isKoszulRegularImmersion_iso_hom_comp
      (Scheme.topIso X) i hregi
  · rw [Category.assoc, hfac]

/-! ### The affine criterion -/

/-- **Stacks 07DB.** A morphism of affine schemes is a local complete intersection morphism
exactly when the induced homomorphism of the rings of global sections is a local complete
intersection homomorphism. -/
@[stacks 07DB]
theorem isLocalCompleteIntersectionMorphism_iff_appTop {X S : Scheme.{u}} [IsAffine X]
    [IsAffine S] (f : X ⟶ S) :
    IsLocalCompleteIntersectionMorphism f ↔ f.appTop.hom.IsLocalCompleteIntersection :=
  ⟨isLocalCompleteIntersection_appTop_of_isLocalCompleteIntersectionMorphism,
    isLocalCompleteIntersectionMorphism_of_isLocalCompleteIntersection_appTop⟩

end AlgebraicGeometry

end
