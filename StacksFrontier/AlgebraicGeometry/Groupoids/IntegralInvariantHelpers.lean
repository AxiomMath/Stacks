module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Polynomial.Subring

/-!
# Helpers for integrality over a ring of invariant functions

The global functions of the affine line over an affine scheme form a univariate polynomial ring
over the global functions of the base, naturally in the base. On the algebraic side, a
polynomial whose two images under a pair of ring maps agree descends to the equalizer of that
pair, and reflecting a multiple of `1 - xX` with constant coefficient one produces a monic
polynomial annihilating `x`.

## Main results

* `AlgebraicGeometry.affineLineSectionsEquiv`: the global functions of the affine line over an
  affine scheme, identified with a univariate polynomial ring, and
  `AlgebraicGeometry.affineLineSectionsEquiv_map`: its naturality.
* `RingHom.polynomial_descends_to_eqLocus` and
  `RingHom.isIntegral_of_monic_polynomial_invariant`: descent of a polynomial to the equalizer
  of two ring maps, and the integrality it yields.
* `Polynomial.monic_relation_of_divisor`: reflecting a multiple of `1 - xX` with constant
  coefficient one gives a monic polynomial annihilating `x`.
* `AlgebraicGeometry.appTop_comp_of_section`: a section of a morphism of schemes splits the
  induced map on global functions.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

/-! ### The affine line over an affine scheme and its global functions -/

/-- Global functions on the affine line over an affine scheme, read on the spectrum of the
polynomial ring. -/
def affineLineGammaEquiv {X : Scheme.{u}} [IsAffine X] :
    Γ(AffineSpace (ULift.{u} PUnit) X, ⊤) ≃+*
      Γ(Spec (CommRingCat.of (MvPolynomial (ULift.{u} PUnit) Γ(X, ⊤))), ⊤) :=
  (Scheme.Γ.mapIso
    (AffineSpace.isoOfIsAffine (ULift.{u} PUnit) X).symm.op).commRingCatIsoToRingEquiv

/-- Global functions on the affine line over an affine scheme form the univariate polynomial
ring over the global functions of that scheme. -/
def affineLineSectionsEquiv {X : Scheme.{u}} [IsAffine X] :
    Γ(AffineSpace (ULift.{u} PUnit) X, ⊤) ≃+* Polynomial Γ(X, ⊤) :=
  affineLineGammaEquiv.trans
    (((Scheme.ΓSpecIso
        (CommRingCat.of (MvPolynomial (ULift.{u} PUnit) Γ(X, ⊤)))).commRingCatIsoToRingEquiv).trans
      (MvPolynomial.uniqueAlgEquiv Γ(X, ⊤) (ULift.{u} PUnit)).toRingEquiv)

/-- An element of the global functions of the affine line is sent to the image of `m` in the
polynomial ring when its pullback to the spectrum is the corresponding section. -/
private theorem affineLineSectionsEquiv_eq_of_inv_appTop {X : Scheme.{u}} [IsAffine X]
    (z : Γ(AffineSpace (ULift.{u} PUnit) X, ⊤))
    (m : MvPolynomial (ULift.{u} PUnit) Γ(X, ⊤))
    (h : (AffineSpace.isoOfIsAffine (ULift.{u} PUnit) X).inv.appTop z =
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} PUnit) Γ(X, ⊤)))).inv m) :
    affineLineSectionsEquiv z = MvPolynomial.uniqueAlgEquiv Γ(X, ⊤) (ULift.{u} PUnit) m := by
  have h' : affineLineGammaEquiv z =
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} PUnit) Γ(X, ⊤)))).inv m := h
  change MvPolynomial.uniqueAlgEquiv Γ(X, ⊤) (ULift.{u} PUnit)
    ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} PUnit) Γ(X, ⊤)))).hom
      (affineLineGammaEquiv z)) = _
  rw [h']
  simp

/-- Constant polynomials correspond to the functions pulled back from the base. -/
theorem affineLineSectionsEquiv_symm_C {X : Scheme.{u}} [IsAffine X] (a : Γ(X, ⊤)) :
    (affineLineSectionsEquiv (X := X)).symm (Polynomial.C a) =
      (AffineSpace (ULift.{u} PUnit) X ↘ X).appTop a := by
  apply (affineLineSectionsEquiv (X := X)).injective
  rw [RingEquiv.apply_symm_apply,
    affineLineSectionsEquiv_eq_of_inv_appTop _ (MvPolynomial.C a) ?_]
  · exact (MvPolynomial.eval₂_C _ _ _).symm
  · let M := MvPolynomial (ULift.{u} PUnit) Γ(X, ⊤)
    have h := congrArg (fun g : Spec (CommRingCat.of M) ⟶ X => g.appTop.hom a)
      (AffineSpace.isoOfIsAffine_inv_over (n := ULift.{u} PUnit) (S := X))
    have hn : (Scheme.ΓSpecIso (CommRingCat.of M)).inv (MvPolynomial.C a) =
        (Spec.map (CommRingCat.ofHom MvPolynomial.C)).appTop (X.isoSpec.inv.appTop a) := by
      have hspecInv : X.isoSpec.inv.appTop =
          (Scheme.ΓSpecIso (CommRingCat.of Γ(X, ⊤))).inv := by
        have h1 := congrArg Scheme.Hom.appTop (Scheme.toSpecΓ_isoSpec_inv X)
        simp only [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Scheme.Hom.id_appTop] at h1
        exact (cancel_mono (Scheme.ΓSpecIso (CommRingCat.of Γ(X, ⊤))).hom).1
          (h1.trans (Scheme.ΓSpecIso (CommRingCat.of Γ(X, ⊤))).inv_hom_id.symm)
      have hnat := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
        (MvPolynomial.C : Γ(X, ⊤) →+* MvPolynomial (ULift.{u} PUnit) Γ(X, ⊤)))
      have hnat' := congrArg
        (fun g : CommRingCat.of Γ(X, ⊤) ⟶
          CommRingCat.of Γ(Spec (CommRingCat.of M), ⊤) => g.hom a) hnat
      change (Scheme.ΓSpecIso (CommRingCat.of M)).inv (MvPolynomial.C a) =
        (Spec.map (CommRingCat.ofHom MvPolynomial.C)).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of Γ(X, ⊤))).inv a) at hnat'
      rw [← hspecInv] at hnat'
      exact hnat'
    have h' : (AffineSpace.isoOfIsAffine (ULift.{u} PUnit) X).inv.appTop
        ((AffineSpace (ULift.{u} PUnit) X ↘ X).appTop a) =
        (Spec.map (CommRingCat.ofHom MvPolynomial.C)).appTop (X.isoSpec.inv.appTop a) := by
      simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] using h
    exact h'.trans hn.symm

/-- The variable corresponds to the standard coordinate function on the affine line. -/
theorem affineLineSectionsEquiv_symm_X {X : Scheme.{u}} [IsAffine X] :
    (affineLineSectionsEquiv (X := X)).symm Polynomial.X =
      AffineSpace.coord X (default : ULift.{u} PUnit) := by
  apply (affineLineSectionsEquiv (X := X)).injective
  rw [RingEquiv.apply_symm_apply, affineLineSectionsEquiv_eq_of_inv_appTop _
    (MvPolynomial.X (default : ULift.{u} PUnit))
    (AffineSpace.isoOfIsAffine_inv_appTop_coord _ _)]
  exact (MvPolynomial.eval₂_X Polynomial.C (fun _ => Polynomial.X) default).symm


/-- A morphism of affine schemes induces the coefficientwise map on the global functions of the
affine lines above them. -/
theorem affineLineSectionsEquiv_map {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) :
    RingHom.comp
        (RingHom.comp (affineLineSectionsEquiv (X := X)).toRingHom
          (AffineSpace.map (ULift.{u} PUnit) f).appTop.hom)
        (affineLineSectionsEquiv (X := Y)).symm.toRingHom =
      Polynomial.mapRingHom f.appTop.hom := by
  apply Polynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C]
    change affineLineSectionsEquiv (X := X)
      ((AffineSpace.map (ULift.{u} PUnit) f).appTop
        ((affineLineSectionsEquiv (X := Y)).symm (Polynomial.C a))) = _
    rw [affineLineSectionsEquiv_symm_C]
    have hsections : (AffineSpace.map (ULift.{u} PUnit) f).appTop
        ((AffineSpace (ULift.{u} PUnit) Y ↘ Y).appTop a) =
        (AffineSpace (ULift.{u} PUnit) X ↘ X).appTop (f.appTop a) := by
      have h := congrArg (fun g : AffineSpace (ULift.{u} PUnit) X ⟶ Y => g.appTop.hom a)
        (AffineSpace.map_over (n := ULift.{u} PUnit) f)
      simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using h
    rw [hsections, ← affineLineSectionsEquiv_symm_C, RingEquiv.apply_symm_apply]
  · simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X]
    change affineLineSectionsEquiv (X := X)
      ((AffineSpace.map (ULift.{u} PUnit) f).appTop
        ((affineLineSectionsEquiv (X := Y)).symm Polynomial.X)) = Polynomial.X
    rw [affineLineSectionsEquiv_symm_X, AffineSpace.map_appTop_coord,
      ← affineLineSectionsEquiv_symm_X, RingEquiv.apply_symm_apply]

/-- A section of a morphism of schemes splits the induced map on global functions. -/
theorem appTop_comp_of_section {X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ X)
    (h : g ≫ f = 𝟙 Y) : g.appTop.hom.comp f.appTop.hom = RingHom.id Γ(Y, ⊤) := by
  ext x
  simpa only [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop, CommRingCat.hom_comp,
    CommRingCat.hom_id, RingHom.comp_apply, RingHom.id_apply] using
    congrArg (fun k : Y ⟶ Y => k.appTop.hom x) h

end AlgebraicGeometry

namespace RingHom

/-- A polynomial with the same image under two ring maps has its coefficients in their
equalizer. -/
theorem polynomial_descends_to_eqLocus {A B : Type*} [CommRing A] [CommRing B]
    (s t : A →+* B) (p : Polynomial A) (h : p.map s = p.map t) :
    ∃ q : Polynomial (s.eqLocus t), q.map (Subring.subtype (s.eqLocus t)) = p := by
  have hc (n : ℕ) : p.coeff n ∈ s.eqLocus t := by
    change s (p.coeff n) = t (p.coeff n)
    simpa only [Polynomial.coeff_map] using congrArg (fun q : Polynomial B => q.coeff n) h
  refine ⟨p.toSubring (s.eqLocus t) ?_, ?_⟩
  · intro a ha
    obtain ⟨n, hn, rfl⟩ := Polynomial.mem_coeffs_iff.mp ha
    exact hc n
  · exact Polynomial.map_toSubring p (s.eqLocus t) _

/-- An element annihilated by a monic polynomial whose coefficients lie in the equalizer of two
ring maps is integral over that equalizer. -/
theorem isIntegral_of_monic_polynomial_invariant {A B : Type*} [CommRing A] [CommRing B]
    (s t : A →+* B) (x : A) (p : Polynomial A) (hp : p.Monic) (hroot : p.eval x = 0)
    (hinv : p.map s = p.map t) :
    (Subring.subtype (s.eqLocus t)).IsIntegralElem x := by
  obtain ⟨q, hq⟩ := polynomial_descends_to_eqLocus s t p hinv
  refine ⟨q, Polynomial.monic_of_injective (Subring.subtype_injective (s.eqLocus t))
    (hq ▸ hp), ?_⟩
  change Polynomial.eval₂ (Subring.subtype (s.eqLocus t)) x q = 0
  rw [← Polynomial.eval_map, hq]
  exact hroot

end RingHom

namespace Polynomial

/-- Reflecting a multiple of `1 - xX` with constant coefficient one gives a monic polynomial
annihilating `x`. -/
theorem monic_relation_of_divisor {A : Type*} [CommRing A] (x : A) (p : A[X])
    (hp : p.coeff 0 = 1) (hd : 1 - C x * X ∣ p) :
    ∃ N : ℕ, (p.reflect N).Monic ∧ (p.reflect N).eval x = 0 := by
  classical
  obtain ⟨q, hq⟩ := hd
  have hb : (1 - C x * X).natDegree ≤ 1 := by
    refine (natDegree_sub_le _ _).trans (max_le (by simp) ?_)
    exact natDegree_mul_le.trans (by simpa using (natDegree_X_le (R := A)))
  have hdeg : p.natDegree ≤ 1 + q.natDegree := by
    rw [hq]
    exact natDegree_mul_le.trans (Nat.add_le_add_right hb _)
  refine ⟨1 + q.natDegree, ?_, ?_⟩
  · refine monic_of_natDegree_le_of_coeff_eq_one (1 + q.natDegree)
      (natDegree_reflect_le.trans (max_le le_rfl hdeg)) ?_
    simpa only [coeff_reflect, revAt_le le_rfl, Nat.sub_self] using hp
  · rw [hq, reflect_mul _ _ hb le_rfl, eval_mul]
    have hlin : (reflect 1 (1 - C x * X)).eval x = 0 := by
      simp [reflect_sub, reflect_C_mul]
    rw [hlin, zero_mul]

end Polynomial

end

end
