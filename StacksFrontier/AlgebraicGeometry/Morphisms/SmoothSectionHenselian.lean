module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.RingTheory.Etale.LiftSmoothMap
public import StacksFrontier.RingTheory.Henselian.FiniteType.StrictlyHenselian
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.PicardOfCurve
public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.StrictlyHenselian

/-!
# Sections of smooth morphisms over a henselian local ring

Let `R` be a henselian local ring with residue field `κ` and `p : Y ⟶ Spec R` a smooth morphism.
Every `κ`-point of `Y` over the closed point extends to a section of `p`. Choose an affine open
`V = Spec B` of `Y` containing the point; `B` is a smooth `R`-algebra and the point is an
`R`-algebra map `B ⟶ κ = R/𝔪`. By [Stacks, Tag 07M7] it lifts to an étale `R`-algebra `A'` with
`A'/𝔪A' = κ`, and by the henselian property ([Stacks, Tag 04GG]) `A'` has an `R`-algebra
retraction `A' ⟶ R`; the composite `B ⟶ A' ⟶ R` is the section.

If moreover `κ` is separably closed, the closed fibre of `p`, if nonempty, has a `κ`-point
([Stacks, Tag 056U]), so `p` has a section.

## Main results

* `AlgebraicGeometry.exists_section_of_smooth_of_henselian`: the extension of a point.
* `AlgebraicGeometry.exists_section_of_smooth_of_strictlyHenselian`: a smooth morphism to the
  spectrum of a henselian local ring with separably closed residue field whose closed fibre is
  nonempty has a section.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

/-- A smooth algebra over a henselian local ring `R` with an `R`-algebra map to the residue field
`R ⧸ 𝔪` has an `R`-algebra map to `R`. -/
private theorem exists_algHom_of_smooth_of_henselian (R : Type u) [CommRing R]
    [HenselianLocalRing R] {B : Type u} [CommRing B] [Algebra R B] [Algebra.Smooth R B]
    (f : B →ₐ[R] R ⧸ maximalIdeal R) :
    Nonempty (B →ₐ[R] R) := by
  -- the étale lift of [Stacks, Tag 07M7]
  obtain ⟨A', _, _, hA', hq, f', -⟩ := exists_etale_lift_of_smooth (maximalIdeal R) f
  let J := (maximalIdeal R).map (algebraMap R A')
  let q : (R ⧸ maximalIdeal R) →+* (A' ⧸ J) :=
    Ideal.quotientMap J (algebraMap R A') Ideal.le_comap_map
  -- `J` is a maximal ideal lying over `𝔪` with residue field `κ`
  have hJmax : J.IsMaximal := by
    rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
    exact MulEquiv.isField (Ideal.Quotient.field (maximalIdeal R)).toIsField
      (RingEquiv.ofBijective q hq).symm.toMulEquiv
  have : J.IsPrime := hJmax.isPrime
  have : J.LiesOver (maximalIdeal R) :=
    ⟨(IsLocalRing.maximalIdeal.isMaximal R).eq_of_le (Ideal.IsPrime.ne_top inferInstance)
      Ideal.le_comap_map⟩
  have hbij : Function.Bijective (Ideal.ResidueField.mapₐ (maximalIdeal R) J (Algebra.ofId R A')
      (Ideal.LiesOver.over)) := by
    refine ⟨RingHom.injective _, fun w => ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.algebraMap_residueField_surjective J w
    obtain ⟨b, hb⟩ := hq.2 (Ideal.Quotient.mk J a)
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hab : algebraMap R A' b - a ∈ J := by
      rw [← Ideal.Quotient.eq]
      exact hb
    refine ⟨algebraMap R (maximalIdeal R).ResidueField b, ?_⟩
    show Ideal.ResidueField.map (maximalIdeal R) J (algebraMap R A') Ideal.LiesOver.over
      (algebraMap R _ b) = _
    rwa [Ideal.ResidueField.map_algebraMap, ← sub_eq_zero, ← map_sub,
      Ideal.algebraMap_residueField_eq_zero]
  obtain ⟨σ₀, -⟩ := henselian_etale_exists_section R A' J hbij
  exact ⟨σ₀.comp f'⟩

namespace AlgebraicGeometry

/-- **A point of the closed fibre with residue field `κ` extends to a section** of a smooth
morphism to the spectrum of a henselian local ring. -/
theorem exists_section_of_smooth_of_henselian (R : Type u) [CommRing R] [HenselianLocalRing R]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of R)) [Smooth p]
    (y : Spec (.of (ResidueField R)) ⟶ Y)
    (hy : y ≫ p = Spec.map (CommRingCat.ofHom (residue R))) :
    ∃ σ : Spec (.of R) ⟶ Y, σ ≫ p = 𝟙 _ := by
  -- an affine open neighbourhood of the point
  let pt : Spec (.of (ResidueField R)) := IsLocalRing.closedPoint _
  obtain ⟨V, hV, hpt, -⟩ := exists_isAffineOpen_mem_and_subset (x := y.base pt) (U := ⊤) trivial
  -- the point factors through `Spec B → Y`, `B = Γ(Y, V)`
  have hrange : Set.range y.base ⊆ Set.range hV.fromSpec.base := by
    rw [hV.range_fromSpec]
    rintro _ ⟨q, rfl⟩
    obtain rfl : q = pt := Subsingleton.elim _ _
    exact hpt
  let z : Spec (.of (ResidueField R)) ⟶ Spec Γ(Y, V) := IsOpenImmersion.lift hV.fromSpec y hrange
  have e : V ≤ p ⁻¹ᵁ ⊤ := by simp
  -- the `R`-algebra structure of `B`
  let φ : CommRingCat.of R ⟶ Γ(Y, V) :=
    (Scheme.ΓSpecIso (.of R)).inv ≫ p.appLE ⊤ V e
  let : Algebra R Γ(Y, V) := φ.hom.toAlgebra
  have : Algebra.Smooth R Γ(Y, V) := by
    have h1 := HasRingHomProperty.appLE (P := @Smooth) p (inferInstance : Smooth p)
      ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ e
    have h0 : (Scheme.ΓSpecIso (.of R)).inv.hom.Smooth :=
      RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso _)
    exact (RingHom.Smooth.comp h0 h1).toAlgebra
  -- the point as an `R`-algebra map `B ⟶ R/𝔪`
  let ψ : Γ(Y, V) ⟶ CommRingCat.of (ResidueField R) := Spec.preimage z
  have htop : (isAffineOpen_top (Spec (.of R))).fromSpec =
      Spec.map (Scheme.ΓSpecIso (.of R)).inv := by
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  have hsq := IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top (Spec (.of R))) hV e
  have hψ : ψ.hom.comp φ.hom = residue R := by
    have hφ : Spec.map φ =
        Spec.map (p.appLE ⊤ V e) ≫ Spec.map (Scheme.ΓSpecIso (.of R)).inv := Spec.map_comp _ _
    have h2 : Spec.map (φ ≫ ψ) = Spec.map (CommRingCat.ofHom (residue R)) := by
      rw [Spec.map_comp, Spec.map_preimage, hφ, ← htop, hsq, ← Category.assoc,
        IsOpenImmersion.lift_fac, hy]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h2)
  let f : Γ(Y, V) →ₐ[R] R ⧸ maximalIdeal R :=
    { ψ.hom with commutes' := DFunLike.congr_fun hψ }
  obtain ⟨g⟩ := exists_algHom_of_smooth_of_henselian R f
  -- the section
  refine ⟨Spec.map (CommRingCat.ofHom g.toRingHom) ≫ hV.fromSpec, ?_⟩
  rw [Category.assoc, ← hsq, ← Spec.map_comp_assoc]
  have hcomp : p.appLE ⊤ V e ≫ CommRingCat.ofHom g.toRingHom =
      (Scheme.ΓSpecIso (.of R)).hom := by
    have hg : φ ≫ CommRingCat.ofHom g.toRingHom = 𝟙 _ := by
      ext r
      exact g.commutes r
    rw [← Iso.hom_inv_id_assoc (Scheme.ΓSpecIso (.of R)) (p.appLE ⊤ V e), Category.assoc]
    show (Scheme.ΓSpecIso (.of R)).hom ≫ φ ≫ _ = _
    rw [hg, Category.comp_id]
  rw [hcomp, htop, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]

/-- **A smooth morphism to the spectrum of a henselian local ring with separably closed residue
field has a section** as soon as its closed fibre is nonempty: the closed fibre is smooth over the
separably closed residue field, so it has a rational point ([Stacks, Tag 056U]), which extends to
a section (`AlgebraicGeometry.exists_section_of_smooth_of_henselian`). -/
theorem exists_section_of_smooth_of_strictlyHenselian (R : Type u) [CommRing R]
    [StrictlyHenselianLocalRing R] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of R)) [Smooth p]
    (hne : ∃ y : Y, p.base y = IsLocalRing.closedPoint R) :
    ∃ σ : Spec (.of R) ⟶ Y, σ ≫ p = 𝟙 _ := by
  let r : Spec (.of (ResidueField R)) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (residue R))
  obtain ⟨y, hy⟩ := hne
  have hr : r.base (IsLocalRing.closedPoint (ResidueField R)) = IsLocalRing.closedPoint R :=
    IsLocalRing.comap_closedPoint (residue R)
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := r) y
    (IsLocalRing.closedPoint (ResidueField R)) (hy.trans hr.symm)
  have : Nonempty ↥(pullback p r) := ⟨z⟩
  obtain ⟨τ, hτ⟩ := Stacks.RigidifiedPicard.exists_section_of_smooth_of_isSepClosed
    (ResidueField R) (pullback.snd p r)
  refine exists_section_of_smooth_of_henselian R p (τ ≫ pullback.fst p r) ?_
  rw [Category.assoc, pullback.condition, ← Category.assoc, hτ, Category.id_comp]

end AlgebraicGeometry

end
