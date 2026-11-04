module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackCategory
public import StacksFrontier.AlgebraicGeometry.Quot.PicardDescent.Reading

/-!
# The comparison of modules of two morphisms of `Picardstack_{X/B}` with a common source

A morphism `m : P ⟶ A` of `Picardstack_{X/B}` carries an isomorphism `(X_m)^*L_A ≅ L_P` of the
inverse image of the module of its target with the module of its source.  Two morphisms
`m₁ : P ⟶ A₁` and `m₂ : P ⟶ A₂` out of one object therefore give an isomorphism

`Θ(m₁, m₂) : (X_{m₁})^*L_{A₁} ≅ (X_{m₂})^*L_{A₂}`

on the base change `X_P`, through the module of `P`.  This file records how `Θ` behaves: it
composes, it is the identity on a repeated morphism, it is read along the base change of a
morphism `r : P' ⟶ P` precomposed with both, and it detects equality of two morphisms with the
same target.

## Main definitions

* `AlgebraicGeometry.Space.PicardHom.theta`: the isomorphism `Θ(m₁, m₂)`.

## Main results

* `AlgebraicGeometry.Space.PicardHom.theta_trans`, `AlgebraicGeometry.Space.PicardHom.theta_self`.
* `AlgebraicGeometry.Space.PicardHom.theta_comp`: `Θ(r ≫ m₁, r ≫ m₂)` is the reading of
  `Θ(m₁, m₂)` along `X_r`.
* `AlgebraicGeometry.Space.PicardHom.eq_of_theta`: two morphisms with equal base maps whose
  comparison is the transport along the equality are equal.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Functor

/-- A composite of fibre morphisms, as an isomorphism: the component of the comparison, the
image of the second factor and the first factor. -/
theorem asIso_fibreComp {C₀ : Type*} {C₁ : Type*} {C₂ : Type*} [Category* C₀] [Category* C₁]
    [Category* C₂] {La : C₁ ⥤ C₀} {Lb : C₂ ⥤ C₁} {Lab : C₂ ⥤ C₀} (τ : Lab ≅ Lb ⋙ La)
    {M : C₀} {M' : C₁} {M'' : C₂} (a : La.obj M' ⟶ M) (b : Lb.obj M'' ⟶ M') [IsIso a] [IsIso b]
    [IsIso (fibreComp τ a b)] :
    asIso (fibreComp τ a b) = τ.app M'' ≪≫ La.mapIso (asIso b) ≪≫ asIso a := by
  ext
  rfl

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The comparison of Stacks 03LU for a morphism equal to a composite, applied to a module, is
the comparison of iterated inverse images of
`AlgebraicGeometry.Space.QuasiCoherentDescent.pullbackComparison`. -/
theorem modulePullbackTriangle_app {X Y Z : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y ⟶ Z}
    {k : X ⟶ Z} (hk : f ≫ g = k) (M : Modules.{u, u} B S hS Z.1 Z.2) :
    (modulePullbackTriangle B S hS hk).app M =
      QuasiCoherentDescent.pullbackComparison B S hS f g k hk M := by
  subst hk
  rw [modulePullbackTriangle_rfl, QuasiCoherentDescent.pullbackComparison_rfl]
  rfl

namespace PicardHom

variable {s : PicardSituation B S hS}

/-- The base map of a composite is the composite of the base maps. -/
theorem comp_base {P' P A : PicardObject s} (r : PicardHom P' P) (m : PicardHom P A) :
    (r.comp m).base = r.base ≫ m.base :=
  rfl

/-- The base change of the base map of a composite is the composite of the base changes. -/
theorem baseChangeMap_comp_base {P' P A : PicardObject s} (r : PicardHom P' P)
    (m : PicardHom P A) :
    baseChangeMap s.f r.base ≫ baseChangeMap s.f m.base = baseChangeMap s.f (r.comp m).base := by
  rw [comp_base, baseChangeMap_comp]

/-- **The comparison of modules of two morphisms of `Picardstack_{X/B}` with a common source**:
`(X_{m₁})^*L_{A₁} ≅ L_P ≅ (X_{m₂})^*L_{A₂}`. -/
def theta {P A₁ A₂ : PicardObject s} (m₁ : PicardHom P A₁) (m₂ : PicardHom P A₂) :
    (modulePullback B S hS (baseChangeMap s.f m₁.base)).obj A₁.lineBundle ≅
      (modulePullback B S hS (baseChangeMap s.f m₂.base)).obj A₂.lineBundle :=
  asIso m₁.fibre ≪≫ (asIso m₂.fibre).symm

variable {P P' A₁ A₂ A₃ : PicardObject s}

/-- The comparisons compose. -/
theorem theta_trans (m₁ : PicardHom P A₁) (m₂ : PicardHom P A₂) (m₃ : PicardHom P A₃) :
    theta m₁ m₂ ≪≫ theta m₂ m₃ = theta m₁ m₃ := by
  simp only [theta, Iso.trans_assoc, Iso.symm_self_id_assoc]

/-- The comparison of a morphism with itself is the identity. -/
theorem theta_self (m : PicardHom P A₁) : theta m m = Iso.refl _ := by
  simp only [theta, Iso.self_symm_id]

/-- The comparison reverses with the two morphisms. -/
theorem theta_symm (m₁ : PicardHom P A₁) (m₂ : PicardHom P A₂) :
    (theta m₁ m₂).symm = theta m₂ m₁ := by
  simp only [theta, Iso.trans_symm, Iso.symm_symm_eq]

/-- The comparison of modules of a composite, as an isomorphism: the comparison of Stacks 03LU
for the composite, the inverse image of the comparison of the second factor, and the comparison
of the first. -/
theorem asIso_comp_fibre (r : PicardHom P' P) (m : PicardHom P A₁) :
    asIso (r.comp m).fibre =
      QuasiCoherentDescent.pullbackComparison B S hS (baseChangeMap s.f r.base)
          (baseChangeMap s.f m.base) (baseChangeMap s.f (r.comp m).base)
          (baseChangeMap_comp_base r m) A₁.lineBundle ≪≫
        (modulePullback B S hS (baseChangeMap s.f r.base)).mapIso (asIso m.fibre) ≪≫
          asIso r.fibre := by
  have : IsIso (Functor.fibreComp (baseChangeCompComparison s.f r.base m.base) r.fibre
      m.fibre) := (r.comp m).isIso_fibre
  have e₁ : asIso (r.comp m).fibre = asIso (Functor.fibreComp
      (baseChangeCompComparison s.f r.base m.base) r.fibre m.fibre) := rfl
  have e₂ : (baseChangeCompComparison s.f r.base m.base).app A₁.lineBundle =
      QuasiCoherentDescent.pullbackComparison B S hS (baseChangeMap s.f r.base)
        (baseChangeMap s.f m.base) (baseChangeMap s.f (r.base ≫ m.base))
        (baseChangeMap_comp s.f r.base m.base).symm A₁.lineBundle := by
    rw [baseChangeCompComparison, modulePullbackTriangle_app]
  refine e₁.trans ((Functor.asIso_fibreComp _ _ _).trans ?_)
  rw [e₂]
  rfl

/-- **`Θ(r ≫ m₁, r ≫ m₂)` is the reading of `Θ(m₁, m₂)` along the base change of `r`.** -/
theorem theta_comp (r : PicardHom P' P) (m₁ : PicardHom P A₁) (m₂ : PicardHom P A₂) :
    theta (r.comp m₁) (r.comp m₂) =
      QuasiCoherentDescent.readIso (baseChangeMap s.f r.base)
        (baseChangeMap_comp_base r m₁) (baseChangeMap_comp_base r m₂) (theta m₁ m₂) := by
  unfold QuasiCoherentDescent.readIso
  rw [theta, asIso_comp_fibre, asIso_comp_fibre, theta,
    Iso.trans_symm, Iso.trans_symm, Functor.mapIso_trans, Functor.mapIso_symm]
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc]

/-- The reading of a comparison depends on the two morphisms only. -/
theorem readIso_theta_congr {Z : AlgebraicSpaces B S hS}
    (c : Z ⟶ baseChangeSpace s.f P.T) {m₁ m₁' : PicardHom P A₁} {m₂ m₂' : PicardHom P A₂}
    (e₁ : m₁ = m₁') (e₂ : m₂ = m₂') {v₁ : Z ⟶ baseChangeSpace s.f A₁.T}
    {v₂ : Z ⟶ baseChangeSpace s.f A₂.T} (h₁ : c ≫ baseChangeMap s.f m₁.base = v₁)
    (h₂ : c ≫ baseChangeMap s.f m₂.base = v₂) (h₁' : c ≫ baseChangeMap s.f m₁'.base = v₁)
    (h₂' : c ≫ baseChangeMap s.f m₂'.base = v₂) :
    QuasiCoherentDescent.readIso c h₁ h₂ (theta m₁ m₂) =
      QuasiCoherentDescent.readIso c h₁' h₂' (theta m₁' m₂') := by
  subst e₁ e₂
  rfl

/-- **Two morphisms with equal base maps are equal as soon as their comparison is the transport
along the equality of the base maps.** -/
theorem eq_of_theta {C : PicardObject s} {m n : PicardHom P C} (hb : m.base = n.base)
    (h : theta m n = eqToIso (congrArg (fun k : P.T ⟶ C.T =>
      (modulePullback B S hS (baseChangeMap s.f k)).obj C.lineBundle) hb)) : m = n := by
  obtain ⟨mb, mf, mi⟩ := m
  obtain ⟨nb, nf, ni⟩ := n
  dsimp only at hb
  subst hb
  have h₁ := congrArg Iso.hom h
  simp only [theta, Iso.trans_hom, asIso_hom, Iso.symm_hom, asIso_inv, eqToIso_refl,
    Iso.refl_hom] at h₁
  have hmn : mf = nf := (comp_inv_eq_id nf).1 h₁
  subst hmn
  rfl

end PicardHom

end AlgebraicGeometry.Space

end
