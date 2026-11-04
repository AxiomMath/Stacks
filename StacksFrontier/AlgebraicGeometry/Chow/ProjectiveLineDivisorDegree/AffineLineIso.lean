module

public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.GraphLineProjectionFlat
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor.ZeroCartier
import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.PointSectionCartier

/-!
# The affine line over `Spec R` is `Spec R[T]`, compatibly with everything

`Stacks.AlgebraicGeometry.GenericPointDecomposition.affineLineOverIsoSpecPolynomial` identifies
the affine line `𝔸¹_{Spec R}` of this development with `Spec R[T]`. On its own that isomorphism
says nothing about the *structure* of `𝔸¹_{Spec R}`: it is an isomorphism of bare schemes,
obtained by crossing to Mathlib's affine space `𝔸(PUnit; Spec R)` and then renaming the single
variable. This file pins it down in the three respects the degree computation of Stacks 02RU
needs — it lies over `Spec R`, it carries the coordinate `T` to the canonical coordinate of `𝔸¹_S`,
and it carries the origin to the point cut out by `T`.

## Main results

* `Stacks.AlgebraicGeometry.GenericPointDecomposition.affineLineOverIsoSpecPolynomial_inv_comp`:
  the identification is an identification over `Spec R`, carrying the structure morphism of
  `𝔸¹_{Spec R}` to `Spec` of the inclusion of constants `R ⟶ R[T]`.
* `Stacks.Chow.appTop_affineLineOverIsoSpecPolynomial_hom`: it carries the coordinate `T` of
  `Spec R[T]` to `Stacks.Chow.affineCoordinate`.
* `Stacks.Chow.asIdeal_affineLineOverIsoSpecPolynomial_hom_base_origin`: over a field it carries
  the origin, the constant section
  `Stacks.AlgebraicGeometry.GenericPointDecomposition.affineLineConstantSection` at
  `Stacks.Chow.integralAffineZeroSection`, to the point of `Spec R[T]` whose prime is `(T)`.

## Implementation notes

The first two results factor through the three ingredients of the isomorphism separately. The
comparison `Stacks.AlgebraicGeometry.GenericPointDecomposition.affineLineOverIsoAffineSpace` of
`𝔸¹_S` with `𝔸(PUnit; S)` is pinned down by `Stacks.Chow.toAffineSpace_fst` and
`Stacks.Chow.toAffineSpace_snd`, and — once it is identified with
`Stacks.AlgebraicGeometry.GenericPointDecomposition.affineLineToAffineSpace`, which is *defined* by
its coordinate — by
`Stacks.AlgebraicGeometry.GenericPointDecomposition.affineLineToAffineSpace_appTop_coord`. The
identification `AlgebraicGeometry.AffineSpace.SpecIso` of `𝔸(PUnit; Spec R)` with `Spec R[PUnit]`
is pinned down in Mathlib by `AlgebraicGeometry.AffineSpace.SpecIso_inv_over` and
`AlgebraicGeometry.AffineSpace.SpecIso_inv_appTop_coord`. What is left is the renaming
`Stacks.Chow.specPolynomialIsoSpecMvPolynomialOfBase`, and it commutes with both the inclusions of
constants and with the two variables because `MvPolynomial.uniqueAlgEquiv` is an `R`-algebra
equivalence sending the unique variable to `T`. The first result is the analogue, for the
one-variable polynomial ring, of the computation inside
`Stacks.Chow.relativeDimension_affineLineOver_genericPoint`.

The third result carries the hypothesis `IsField ↑R`, and is false without it. The composite of
the origin with the identification is `Spec` of evaluation at `0`, so the prime it produces at a
point `s` of `Spec R` is the contraction `{p | p(0) ∈ s}`, which is `(T) ⊔ s.map Polynomial.C` and
hence not `(T)` unless `s = ⊥`; over a field the only prime is `⊥`. The proof does not construct
that composite. It only shows that `T` lies in the prime — the origin kills
`Stacks.Chow.affineCoordinate`, so the basic open of `T` pulls back to the empty set — and then
uses that `(T)` is the only prime of `R[T]` containing `T` when `R` is a field.

Several steps are term-mode rather than `rw`: `AlgebraicGeometry.AffineSpace` is a pullback by
definition but not syntactically, so a motive mentioning both `Stacks.Chow.toAffineSpace` and
`AlgebraicGeometry.AffineSpace.SpecIso` is not type-correct at the transparency `rw` uses.

## References

* [Stacks Project, Tag 02RU](https://stacks.math.columbia.edu/tag/02RU)
* [Stacks Project, Tag 01JE](https://stacks.math.columbia.edu/tag/01JE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Unfolding lemmas -/

/-- Taking global sections along a composite of morphisms of schemes. -/
private theorem comp_appTop_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : Γ(Z, ⊤)) :
    (f ≫ g).appTop x = f.appTop (g.appTop x) :=
  rfl

/-- The comparison `𝔸¹_S ⟶ 𝔸(PUnit; S)` of
`Stacks.AlgebraicGeometry.GenericPointDecomposition.affineLineOverIsoAffineSpace` is the one
determined by the coordinate: the two agree on both projections of the defining pullback. -/
private theorem toAffineSpace_eq (S : Scheme.{u}) :
    toAffineSpace S = affineLineToAffineSpace S :=
  pullback.hom_ext ((toAffineSpace_fst S).trans (affineLineToAffineSpace_over S).symm)
    ((toAffineSpace_snd S).trans (affineLineToAffineSpace_toSpecMvPoly S).symm)

/-- The renaming `Spec R[T] ≅ Spec R[PUnit]` is `Spec` of the inverse of
`MvPolynomial.uniqueAlgEquiv`. -/
private theorem specPolynomialIsoSpecMvPolynomialOfBase_inv_eq (R : CommRingCat.{u}) :
    (specPolynomialIsoSpecMvPolynomialOfBase R).inv
      = Spec.map (CommRingCat.ofHom
          (MvPolynomial.uniqueAlgEquiv (↑R) PUnit.{u + 1}).toRingEquiv.symm.toRingHom) :=
  rfl

/-- The isomorphism `𝔸¹_{Spec R} ≅ Spec R[T]`, postcomposed with any morphism, written out as the
composite of its three ingredients. -/
private theorem affineLineOverIsoSpecPolynomial_hom_comp (R : CommRingCat.{u}) {T : Scheme.{u}}
    (f : Spec (CommRingCat.of (Polynomial ↑R)) ⟶ T) :
    (affineLineOverIsoSpecPolynomial R).hom ≫ f
      = toAffineSpace (Spec R) ≫ (AffineSpace.SpecIso PUnit.{u + 1} R).hom ≫
          (specPolynomialIsoSpecMvPolynomialOfBase R).inv ≫ f :=
  (Category.assoc _ _ _).trans
    (congrArg (fun g : AffineSpace PUnit.{u + 1} (Spec R) ⟶ T => toAffineSpace (Spec R) ≫ g)
      (Category.assoc _ _ _))

/-- Taking global sections along the isomorphism `𝔸¹_{Spec R} ≅ Spec R[T]`, written out as the
composite of its three ingredients. -/
private theorem appTop_affineLineOverIsoSpecPolynomial_hom_apply (R : CommRingCat.{u})
    (x : Γ(Spec (CommRingCat.of (Polynomial ↑R)), ⊤)) :
    (affineLineOverIsoSpecPolynomial R).hom.appTop x
      = (toAffineSpace (Spec R)).appTop ((AffineSpace.SpecIso PUnit.{u + 1} R).hom.appTop
          ((specPolynomialIsoSpecMvPolynomialOfBase R).inv.appTop x)) :=
  rfl

/-! ### The identification is an identification over the base -/

/-- The renaming `Spec R[T] ≅ Spec R[PUnit]` commutes with the two inclusions of constants,
because `MvPolynomial.uniqueAlgEquiv` is an `R`-algebra equivalence. -/
private theorem specPolynomialIsoSpecMvPolynomialOfBase_inv_comp_C (R : CommRingCat.{u}) :
    (specPolynomialIsoSpecMvPolynomialOfBase R).inv ≫
        Spec.map (CommRingCat.ofHom (Polynomial.C : ↑R →+* Polynomial ↑R))
      = Spec.map (CommRingCat.ofHom
          (MvPolynomial.C : ↑R →+* MvPolynomial PUnit.{u + 1} ↑R)) := by
  rw [specPolynomialIsoSpecMvPolynomialOfBase_inv_eq, ← Spec.map_comp]
  congr 1
  ext x
  simp

/-- The identification of the affine line over `Spec R` with `Spec R[T]` is an identification over
`Spec R`: it carries the structure morphism of `𝔸¹_{Spec R}` to `Spec` of the inclusion of
constants. -/
theorem affineLineOverIsoSpecPolynomial_inv_comp (R : CommRingCat.{u}) :
    (affineLineOverIsoSpecPolynomial R).inv ≫
        pullback.fst (terminal.from (Spec R))
          (terminal.from (Spec (CommRingCat.of (Polynomial (ULift.{u} ℤ)))))
      = Spec.map (CommRingCat.ofHom (Polynomial.C : ↑R →+* Polynomial ↑R)) := by
  have h0 : (AffineSpace.SpecIso PUnit.{u + 1} R).hom ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := PUnit.{u + 1}) (R := ↑R)))
        = (AffineSpace PUnit.{u + 1} (Spec R) ↘ Spec R) := by
    rw [← AffineSpace.SpecIso_inv_over (n := PUnit.{u + 1}) R, Iso.hom_inv_id_assoc]
  have hfst : (affineLineOverIsoSpecPolynomial R).hom ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : ↑R →+* Polynomial ↑R))
        = pullback.fst (terminal.from (Spec R))
            (terminal.from (Spec (CommRingCat.of (Polynomial (ULift.{u} ℤ))))) := by
    rw [affineLineOverIsoSpecPolynomial_hom_comp,
      specPolynomialIsoSpecMvPolynomialOfBase_inv_comp_C]
    exact (congrArg (toAffineSpace (Spec R) ≫ ·) h0).trans (toAffineSpace_fst _)
  rw [← hfst, Iso.inv_hom_id_assoc]

/-! ### The identification carries the coordinate to the coordinate -/

/-- The renaming `Spec R[T] ≅ Spec R[PUnit]` carries the coordinate `T` to the unique variable,
because `MvPolynomial.uniqueAlgEquiv` sends that variable to `T`. -/
private theorem appTop_specPolynomialIsoSpecMvPolynomialOfBase_inv (R : CommRingCat.{u}) :
    (specPolynomialIsoSpecMvPolynomialOfBase R).inv.appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ↑R))).inv Polynomial.X)
      = (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial PUnit.{u + 1} ↑R))).inv
          (MvPolynomial.X PUnit.unit) := by
  rw [specPolynomialIsoSpecMvPolynomialOfBase_inv_eq, ← CommRingCat.comp_apply,
    ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  congr 1
  simp

/-- Mathlib's identification of `𝔸(PUnit; Spec R)` with `Spec R[PUnit]` carries the variable to
the standard coordinate. -/
private theorem appTop_affineSpace_specIso_hom (R : CommRingCat.{u}) (i : PUnit.{u + 1}) :
    (AffineSpace.SpecIso PUnit.{u + 1} R).hom.appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial PUnit.{u + 1} ↑R))).inv
          (MvPolynomial.X i))
      = AffineSpace.coord (Spec R) i := by
  have h2 : (AffineSpace.SpecIso PUnit.{u + 1} R).hom.appTop
        ((AffineSpace.SpecIso PUnit.{u + 1} R).inv.appTop (AffineSpace.coord (Spec R) i))
      = (AffineSpace.SpecIso PUnit.{u + 1} R).hom.appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial PUnit.{u + 1} ↑R))).inv
          (MvPolynomial.X i)) :=
    congrArg (fun x => (AffineSpace.SpecIso PUnit.{u + 1} R).hom.appTop x)
      (AffineSpace.SpecIso_inv_appTop_coord (n := PUnit.{u + 1}) R i)
  rw [← h2, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Iso.hom_inv_id,
    Scheme.Hom.id_appTop]
  simp

/-- The comparison with Mathlib's affine space carries the standard coordinate to
`Stacks.Chow.affineCoordinate`. -/
private theorem appTop_toAffineSpace (S : Scheme.{u}) (i : PUnit.{u + 1}) :
    (toAffineSpace S).appTop (AffineSpace.coord S i) = affineCoordinate S := by
  rw [toAffineSpace_eq]
  exact affineLineToAffineSpace_appTop_coord S i

/-- The identification carries the coordinate `T` of `Spec R[T]` to the canonical coordinate of
the affine line. -/
theorem appTop_affineLineOverIsoSpecPolynomial_hom (R : CommRingCat.{u}) :
    (affineLineOverIsoSpecPolynomial R).hom.appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ↑R))).inv Polynomial.X)
      = affineCoordinate (Spec R) := by
  rw [appTop_affineLineOverIsoSpecPolynomial_hom_apply,
    appTop_specPolynomialIsoSpecMvPolynomialOfBase_inv, appTop_affineSpace_specIso_hom]
  exact appTop_toAffineSpace _ _

/-! ### The identification carries the origin to the point cut out by the coordinate -/

/-- A constant section of `𝔸¹_S`, read in the integral model, is the corresponding point
of `𝔸¹_ℤ`. -/
private theorem affineLineConstantSection_snd (S : Scheme.{u})
    (e : (⊤_ Scheme.{u}) ⟶ Spec (CommRingCat.of (Polynomial (ULift.{u} ℤ)))) :
    affineLineConstantSection S e ≫ pullback.snd (terminal.from S)
        (terminal.from (Spec (CommRingCat.of (Polynomial (ULift.{u} ℤ)))))
      = terminal.from S ≫ e :=
  pullback.lift_snd _ _ _

/-- The canonical coordinate of `𝔸¹_S` is the coordinate of `𝔸¹_ℤ`, pulled back. -/
public theorem affineCoordinate_eq (S : Scheme.{u}) :
    affineCoordinate S
      = (pullback.snd (terminal.from S)
            (terminal.from (Spec (CommRingCat.of (Polynomial (ULift.{u} ℤ)))))).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial (ULift.{u} ℤ)))).inv Polynomial.X) :=
  rfl

/-- The origin of `𝔸¹_ℤ` kills the coordinate: it is cut out by it. -/
private theorem appTop_integralAffineZeroSection_X :
    integralAffineZeroSection.{u}.appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial (ULift.{u} ℤ)))).inv Polynomial.X) = 0 := by
  have hmem : (Scheme.ΓSpecIso (CommRingCat.of (Polynomial (ULift.{u} ℤ)))).inv Polynomial.X
      ∈ integralAffineZeroSection.{u}.ker.ideal ⟨⊤, isAffineOpen_top _⟩ := by
    rw [ker_ideal_top_integralAffineZeroSection]
    exact Ideal.mem_span_singleton_self _
  rw [Scheme.Hom.ker_apply] at hmem
  exact hmem

/-- Alias of `affineLineConstantSection_appTop_affineCoordinate_zero`. -/
private alias appTop_affineLineConstantSection_affineCoordinate :=
  affineLineConstantSection_appTop_affineCoordinate_zero

/-- For `R` a field, `(T)` is the only prime ideal of `R[T]` containing `T`: modulo `T` every
polynomial is a constant, and a nonzero constant is a unit. -/
private theorem eq_span_X_of_isPrime_of_mem {R : CommRingCat.{u}} (hR : IsField ↑R)
    (q : Ideal (Polynomial ↑R)) (hq : q.IsPrime) (hX : (Polynomial.X : Polynomial ↑R) ∈ q) :
    q = Ideal.span {(Polynomial.X : Polynomial ↑R)} := by
  refine le_antisymm (fun p hp => ?_) (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hX))
  have hsub : p - Polynomial.C (p.coeff 0) ∈ q := by
    obtain ⟨c, hc⟩ := Polynomial.X_dvd_iff.mpr
      (show (p - Polynomial.C (p.coeff 0)).coeff 0 = 0 by simp)
    rw [hc]
    exact q.mul_mem_right _ hX
  have hC : Polynomial.C (p.coeff 0) ∈ q := by
    have h := q.sub_mem hp hsub
    simpa using h
  have hzero : p.coeff 0 = 0 := by
    by_contra hne
    obtain ⟨b, hb⟩ := hR.mul_inv_cancel hne
    exact hq.ne_top (Ideal.eq_top_of_isUnit_mem q hC
      (Polynomial.isUnit_C.mpr (isUnit_iff_exists_inv.mpr ⟨b, hb⟩)))
  exact Ideal.mem_span_singleton.mpr (Polynomial.X_dvd_iff.mpr hzero)

/-- The identification carries the origin of the affine line to the point cut out by `T`.

The hypothesis that `R` is a field is necessary: in general the prime obtained at a point `s` of
`Spec R` is the contraction of `s` along evaluation at `0`, which is `(T) ⊔ s.map Polynomial.C`.
See the implementation notes. -/
theorem asIdeal_affineLineOverIsoSpecPolynomial_hom_base_origin (R : CommRingCat.{u})
    (hR : IsField ↑R) (s : Spec R) :
    ((affineLineOverIsoSpecPolynomial R).hom.base
        ((affineLineConstantSection (Spec R) integralAffineZeroSection).base s)).asIdeal
      = Ideal.span {(Polynomial.X : Polynomial ↑R)} := by
  have hzero : (affineLineConstantSection (Spec R) integralAffineZeroSection ≫
      (affineLineOverIsoSpecPolynomial R).hom).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ↑R))).inv Polynomial.X) = 0 := by
    rw [comp_appTop_apply, appTop_affineLineOverIsoSpecPolynomial_hom,
      appTop_affineLineConstantSection_affineCoordinate]
  have hpre := Scheme.preimage_basicOpen_top
    (affineLineConstantSection (Spec R) integralAffineZeroSection ≫
      (affineLineOverIsoSpecPolynomial R).hom)
    ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ↑R))).inv Polynomial.X)
  rw [hzero, Scheme.basicOpen_zero, basicOpen_eq_of_affine] at hpre
  have hnot : (affineLineOverIsoSpecPolynomial R).hom.base
      ((affineLineConstantSection (Spec R) integralAffineZeroSection).base s)
        ∉ PrimeSpectrum.basicOpen (Polynomial.X : Polynomial ↑R) := by
    intro hin
    have hs : s ∈ (affineLineConstantSection (Spec R) integralAffineZeroSection ≫
        (affineLineOverIsoSpecPolynomial R).hom) ⁻¹ᵁ
          PrimeSpectrum.basicOpen (Polynomial.X : Polynomial ↑R) := hin
    rw [hpre] at hs
    exact hs
  exact eq_span_X_of_isPrime_of_mem hR _ (PrimeSpectrum.isPrime _)
    (not_not.mp fun h => hnot ((PrimeSpectrum.mem_basicOpen _ _).mpr h))

end Stacks.Chow

end
