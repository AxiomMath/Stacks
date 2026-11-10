module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartGlue.AlgFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Defs
public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothScheme

/-!
# A relatively formally étale point gives a formally étale chart on algebras

Let `R` be an `A'`-algebra whose spectrum belongs to the site and let `g₀` be a section of `X` over
`Spec R` lying over `y`. Suppose `g₀` is *formally étale relative to `T'`*: every infinitesimal
lifting problem over `T'` for a section of `X` over `y` against `g₀` has exactly one solution.
Then `R`, with the points `w ↦ g₀|_{Spec w}`, is a formally étale chart of the functor of points
over `y` on algebras, in the sense of `Stacks.ChartGlue.FormallyEtaleChart`.

## Main definitions

* `AlgebraicGeometry.Space.ChartGlue.RelFormallyEtale`: relative formal étaleness of a point.
* `AlgebraicGeometry.Space.ChartGlue.algChart`: the formally étale chart.

## Main results

* `AlgebraicGeometry.Space.ChartGlue.existsUnique_specMap_eq`: a morphism of spectra over `T'` is
  the spectrum of exactly one algebra map.
* `AlgebraicGeometry.Space.ChartGlue.isSquareZeroClosedImmersion_specMap`: the spectrum of a
  surjection with square-zero kernel is a square-zero closed immersion.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space.ChartGlue

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (T' : BigFppfOver B S hS)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]

/-- **A morphism of spectra over `T'` is the spectrum of exactly one algebra map.** -/
theorem existsUnique_specMap_eq {C D : Type u} [CommRing C] [Algebra (ringOf B S hS T') C]
    [CommRing D] [Algebra (ringOf B S hS T') D] (hC : B.Contains (Spec (CommRingCat.of C)))
    (hD : B.Contains (Spec (CommRingCat.of D)))
    (h : specObj B S hS T' D hD ⟶ specObj B S hS T' C hC)
    (hh : h ≫ specToT B S hS T' C hC = specToT B S hS T' D hD) :
    ∃! φ : C →ₐ[ringOf B S hS T'] D, specMap B S hS T' hC hD φ = h := by
  let φ₀ : CommRingCat.of C ⟶ CommRingCat.of D :=
    Spec.preimage ((BigFppfOver.toScheme B S hS).map h)
  have hφ₀ : Spec.map φ₀ = (BigFppfOver.toScheme B S hS).map h := Spec.map_preimage _
  have hcomm : ∀ a, φ₀ (algebraMap (ringOf B S hS T') C a) = algebraMap (ringOf B S hS T') D a := by
    have h1 : Spec.map φ₀ ≫ specStr B S hS T' C = specStr B S hS T' D := by
      rw [hφ₀]
      exact ((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans
        (congrArg (BigFppfOver.toScheme B S hS).map hh)
    simp only [specStr] at h1
    rw [← Category.assoc, cancel_mono, ← Spec.map_comp] at h1
    exact fun a ↦ congrArg (fun ψ : CommRingCat.of (ringOf B S hS T') ⟶ CommRingCat.of D ↦ ψ a)
      (Spec.map_injective h1)
  let φ : C →ₐ[ringOf B S hS T'] D :=
    { toRingHom := φ₀.hom, commutes' := hcomm }
  refine ⟨φ, ?_, fun ψ hψ ↦ ?_⟩
  · apply (BigFppfOver.toScheme B S hS).map_injective
    rw [toScheme_map_specMap, ← hφ₀]
    rfl
  · apply AlgHom.toRingHom_injective
    have h1 := congrArg (BigFppfOver.toScheme B S hS).map hψ
    rw [toScheme_map_specMap, ← hφ₀] at h1
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)

/-- **The spectrum of a surjection with square-zero kernel is a square-zero closed immersion.** -/
theorem isSquareZeroClosedImmersion_specMap {C D : Type u} [CommRing C]
    [Algebra (ringOf B S hS T') C] [CommRing D] [Algebra (ringOf B S hS T') D]
    (hC : B.Contains (Spec (CommRingCat.of C))) (hD : B.Contains (Spec (CommRingCat.of D)))
    (π : C →ₐ[ringOf B S hS T'] D) (hπ : Function.Surjective π)
    (hsq : RingHom.ker π ^ 2 = ⊥) :
    IsSquareZeroClosedImmersion B S hS (specMap B S hS T' hC hD π) := by
  refine ⟨AlgebraicGeometry.IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (π : C →+* D)) hπ, ?_⟩
  suffices H : (Spec.map (CommRingCat.ofHom (π : C →+* D))).ker ^ 2 = ⊥ from H
  rw [Stacks.Smooth.ker_pow_eq_bot_iff_of_isAffine]
  have hker : RingHom.ker (Spec.map (CommRingCat.ofHom (π : C →+* D))).appTop.hom =
      (RingHom.ker (π : C →+* D)).comap (Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom := by
    have e := congrArg CommRingCat.Hom.hom
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (π : C →+* D)))
    rw [← RingHom.ker_comp_of_injective _
      (Scheme.ΓSpecIso (CommRingCat.of D)).commRingCatIsoToRingEquiv.injective,
      RingHom.comap_ker]
    exact congrArg RingHom.ker e
  rw [hker, pow_two, eq_bot_iff, Ideal.mul_le]
  intro x hx y hy
  rw [Ideal.mem_comap] at hx hy
  rw [Ideal.mem_bot]
  have hxy : (Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom (x * y) = 0 := by
    rw [map_mul, ← Ideal.mem_bot, ← show RingHom.ker (π : C →+* D) ^ 2 = ⊥ from hsq, pow_two]
    exact Ideal.mul_mem_mul hx hy
  exact (Scheme.ΓSpecIso (CommRingCat.of C)).commRingCatIsoToRingEquiv.injective
    (hxy.trans (map_zero _).symm)

section Chart

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (y : Y.obj (op T'))

/-- **Relative formal étaleness** of a section `g₀` of `X` over an object `E` lying over `T'`:
for every square-zero closed immersion `j : D₀ ⟶ C₀` of affine objects over `T'`, every section
`g` of `X` over `C₀` lying over `y`, and every `e₀ : D₀ ⟶ E` over `T'` with `g₀|_{e₀} = g|_{D₀}`,
there is exactly one `e : C₀ ⟶ E` over `T'` extending `e₀` with `g₀|_e = g`. -/
def RelFormallyEtale {E : BigFppfOver B S hS} (eT : E ⟶ T') (g₀ : X.obj (op E)) : Prop :=
  ∀ (C₀ D₀ : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj C₀) →
    IsAffine ((BigFppfOver.toScheme B S hS).obj D₀) → ∀ (j : D₀ ⟶ C₀),
      IsSquareZeroClosedImmersion B S hS j → ∀ (c : C₀ ⟶ T') (g : X.obj (op C₀)),
        f.app _ g = Y.map c.op y → ∀ (e₀ : D₀ ⟶ E), e₀ ≫ eT = j ≫ c →
          X.map e₀.op g₀ = X.map j.op g →
            ∃! e : C₀ ⟶ E, j ≫ e = e₀ ∧ e ≫ eT = c ∧ X.map e.op g₀ = g

variable (P : ObjectProperty (CommAlgCat.{u} (ringOf B S hS T')))
  (hP : ∀ C : P.FullSubcategory, B.Contains (Spec (CommRingCat.of C.obj)))
  (R : Type u) [CommRing R] [Algebra (ringOf B S hS T') R]
  (hR : B.Contains (Spec (CommRingCat.of R))) (g₀ : X.obj (op (specObj B S hS T' R hR)))
  (hg₀ : f.app _ g₀ = Y.map (specToT B S hS T' R hR).op y)
  (hrel : RelFormallyEtale B S hS T' f y (specToT B S hS T' R hR) g₀)

/-- The point of the functor over `y` attached to an algebra map out of `R`. -/
def chartPt (C : P.FullSubcategory) (w : R →ₐ[ringOf B S hS T'] C.obj) :
    (algFunctor B S hS T' P hP f y).obj C :=
  ⟨X.map (specMap B S hS T' hR (hP C) w).op g₀, by
    rw [f.naturality_apply, hg₀, ← Functor.map_comp_apply, ← op_comp, specMap_specToT]⟩

include hrel in
/-- **The formally étale chart** of the functor of points over `y`, given by a relatively formally
étale point over an affine spectrum. -/
def algChart : Stacks.ChartGlue.FormallyEtaleChart P (algFunctor B S hS T' P hP f y) R where
  pt C w := chartPt B S hS T' f y P hP R hR g₀ hg₀ C w
  pt_comp {C D} h w := by
    apply Subtype.ext
    change X.map (specMap B S hS T' hR (hP D) (h.hom.hom.comp w)).op g₀ =
      X.map (specMap B S hS T' (hP C) (hP D) h.hom.hom).op
        (X.map (specMap B S hS T' hR (hP C) w).op g₀)
    rw [specMap_comp B S hS T' hR (hP C) (hP D), op_comp, Functor.map_comp_apply]
  existsUnique_lift {C D} π hπ hsq g w₀ hw₀ := by
    have hj := isSquareZeroClosedImmersion_specMap B S hS T' (hP C) (hP D) π.hom.hom hπ hsq
    have hw₀' : X.map (specMap B S hS T' hR (hP D) w₀).op g₀ =
        X.map (specMap B S hS T' (hP C) (hP D) π.hom.hom).op g.1 := congrArg Subtype.val hw₀
    obtain ⟨e, ⟨he₁, he₂, he₃⟩, heu⟩ := hrel (specObj B S hS T' C.obj (hP C))
      (specObj B S hS T' D.obj (hP D))
      (inferInstanceAs (IsAffine (Spec (CommRingCat.of C.obj))))
      (inferInstanceAs (IsAffine (Spec (CommRingCat.of D.obj))))
      (specMap B S hS T' (hP C) (hP D) π.hom.hom)
      (isSquareZeroClosedImmersion_specMap B S hS T' (hP C) (hP D) π.hom.hom hπ hsq)
      (specToT B S hS T' C.obj (hP C)) g.1 g.2
      (specMap B S hS T' hR (hP D) w₀)
      (by rw [specMap_specToT, specMap_specToT]) (congrArg Subtype.val hw₀)
    obtain ⟨w, hw, hwu⟩ := existsUnique_specMap_eq B S hS T' hR (hP C) e he₂
    refine ⟨w, ⟨?_, ?_⟩, fun w' ⟨hw'₁, hw'₂⟩ ↦ ?_⟩
    · have := congrArg (fun k ↦ specMap B S hS T' (hP C) (hP D) π.hom.hom ≫ k) hw
      rw [← specMap_comp, he₁] at this
      exact (existsUnique_specMap_eq B S hS T' hR (hP D) _ (by
        rw [specMap_specToT])).unique this rfl
    · apply Subtype.ext
      change X.map (specMap B S hS T' hR (hP C) w).op g₀ = g.1
      rw [hw, he₃]
    · refine hwu w' (heu _ ⟨?_, specMap_specToT _ _ _ _ _ _ _, congrArg Subtype.val hw'₂⟩)
      rw [← specMap_comp]
      exact congrArg _ hw'₁

end Chart

end AlgebraicGeometry.Space.ChartGlue

end
