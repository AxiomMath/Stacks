module

public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.AffineOpenDeRhamSquare
public import StacksFrontier.AlgebraicGeometry.DeRham.PullbackComplexDegreewise
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBlowupFormsDirectImage
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBlowupLaurentForms
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.GradedForms

/-!
# Generators of the sheaves of differential forms

For a morphism of schemes `f : X ⟶ S` and an open `U ⊆ X`, the *generator* attached to sections
`g₁, …, g_a` of `𝒪_X` over `U` is the form `d g₁ ∧ ⋯ ∧ d g_a` over `U`. This file records how
generators behave: under restriction, under the comparison map `Ω^a_{X/S} ⟶ f_*Ω^a_{Y/S}` of a
morphism `f : Y ⟶ X`, and under the identification of the forms over an affine open with an
exterior power of Kähler differentials; and that the generators span the forms over an affine
open.

## Main results

* `Stacks.DeRham.FormsGenerators.res_smul_gen`: restriction of `c • d g₁ ∧ ⋯ ∧ d g_a`.
* `Stacks.DeRham.FormsGenerators.formsDirectImageComparison_smul_gen`: the comparison map on a
  generator.
* `Stacks.DeRham.FormsGenerators.induction_on_affine`: the generators span the forms over an
  affine open.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.DeRham.FormsGenerators

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The generator `d g₁ ∧ ⋯ ∧ d g_a` of `Ω^a_{X/S}` over `U`. -/
def gen (U : X.Opens) {a : ℕ} (g : Fin a → Γ(X, U)) :
    Γ(Scheme.Hom.relativeDifferentialForms f (a : ℤ), U) :=
  (Scheme.Hom.deRhamAlgebras f).exterior.toPresheafGradedAlgebra.homogeneousProdLeft (op U) a
    fun i => _root_.AlgebraicGeometry.SheafOfModules.exactOne (Scheme.Hom.deRhamAlgebras f)
      (op U) (g i)

/-- Restriction of a generator. -/
theorem res_gen {U V : X.Opens} (h : V ≤ U) {a : ℕ} (g : Fin a → Γ(X, U)) :
    (Scheme.Hom.relativeDifferentialForms f (a : ℤ)).presheaf.map (homOfLE h).op (gen f U g) =
      gen f V fun i => X.presheaf.map (homOfLE h).op (g i) := by
  refine ((Scheme.Hom.deRhamAlgebras f).exterior.toPresheafGradedAlgebra
    |>.homogeneousProdLeft_naturality (homOfLE h).op a _).trans ?_
  exact congrArg
    (fun z => (Scheme.Hom.deRhamAlgebras f).exterior.toPresheafGradedAlgebra.homogeneousProdLeft
      _ a z)
    (funext fun i => AlgebraicGeometry.SheafOfModules.exactOne_map _ (homOfLE h).op _)

/-- Restriction of `c • d g₁ ∧ ⋯ ∧ d g_a`. -/
theorem res_smul_gen {U V : X.Opens} (h : V ≤ U) {a : ℕ} (c : Γ(X, U)) (g : Fin a → Γ(X, U)) :
    (Scheme.Hom.relativeDifferentialForms f (a : ℤ)).presheaf.map (homOfLE h).op (c • gen f U g) =
      X.presheaf.map (homOfLE h).op c • gen f V fun i => X.presheaf.map (homOfLE h).op (g i) := by
  rw [← res_gen f h g]
  exact (Scheme.Hom.relativeDifferentialForms f (a : ℤ)).val.map_smul (homOfLE h).op c _

/-- Over an affine open, a generator is the image of the wedge of Kähler differentials. -/
private theorem gen_eq_formsSectionsIso_inv {U : X.Opens} {V : S.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V) {a : ℕ} (g : Fin a → Γ(X, U)) :
    gen f U g = (Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso f hU hV e a).inv
      (exteriorPower.ιMulti Γ(X, U) a fun i => CommRingCat.KaehlerDifferential.d (g i)) :=
  (Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso_inv_ιMulti_d f hU hV e a g).symm

/-- The identification of the forms over an affine open with Kähler differentials, on a
generator. -/
theorem formsSectionsIso_hom_smul_gen {U : X.Opens} {V : S.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V) {a : ℕ} (c : Γ(X, U)) (g : Fin a → Γ(X, U)) :
    (Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso f hU hV e a).hom (c • gen f U g) =
      c • exteriorPower.ιMulti Γ(X, U) a fun i => CommRingCat.KaehlerDifferential.d (g i) := by
  rw [gen_eq_formsSectionsIso_inv f hU hV e, ← map_smul,
    (Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso f hU hV e a).inv_hom_id_apply]

/-- The frame map of `StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBlowupLaurentForms`, on a
generator over an affine open. -/
theorem formsFrame_formsSectionsIso_smul_gen {R : Type u} [CommRing R] {mm nn : ℕ} {U : X.Opens}
    {V : S.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V)
    (lam : Γ(X, U) →+* Stacks.DeRham.CoordinateCech.Lau R mm nn)
    (hlam : ∀ r s, Stacks.DeRham.CoordinateCech.frameOp s (lam (f.appLE V U e r)) = 0) {a : ℕ}
    (c : Γ(X, U)) (g : Fin a → Γ(X, U)) :
    Stacks.DeRham.CoordinateCech.formsFrame (f.appLE V U e) lam hlam a
        ((Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso f hU hV e a).hom
          (c • gen f U g)) =
      lam c • exteriorPower.ιMulti _ a fun i =>
        Stacks.DeRham.CoordinateCech.frameD (lam (g i)) := by
  rw [formsSectionsIso_hom_smul_gen, Stacks.DeRham.CoordinateCech.formsFrame_smul_ιMulti_d]

/-- A generator with a zero factor vanishes, over an affine open. -/
theorem gen_eq_zero {U : X.Opens} {V : S.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (e : U ≤ f ⁻¹ᵁ V) {a : ℕ} (g : Fin a → Γ(X, U)) (i : Fin a) (hi : g i = 0) :
    gen f U g = 0 := by
  have hd : CommRingCat.KaehlerDifferential.d (f := f.appLE V U e) (g i) = 0 := by
    rw [hi]
    have := (CommRingCat.KaehlerDifferential.D (f.appLE V U e)).d_add 0 0
    rw [add_zero] at this
    exact left_eq_add.1 this
  rw [gen_eq_formsSectionsIso_inv f hU hV e, (exteriorPower.ιMulti _ a).map_coord_zero i hd,
    map_zero]

/-- **The generators span the forms over an affine open.** -/
theorem induction_on_affine {U : X.Opens} {V : S.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V) {a : ℕ}
    {P : Γ(Scheme.Hom.relativeDifferentialForms f (a : ℤ), U) → Prop} (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y))
    (hgen : ∀ (c : Γ(X, U)) (g : Fin a → Γ(X, U)), P (c • gen f U g))
    (ω : Γ(Scheme.Hom.relativeDifferentialForms f (a : ℤ), U)) : P ω := by
  set ι := Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso f hU hV e a
  have hinv : ∀ (c : Γ(X, U)) (g : Fin a → Γ(X, U)),
      ι.inv (c • exteriorPower.ιMulti Γ(X, U) a fun i => CommRingCat.KaehlerDifferential.d (g i)) =
        c • gen f U g := fun c g => by
    rw [gen_eq_formsSectionsIso_inv f hU hV e, map_smul]
  have key : ∀ x, ∀ c : Γ(X, U), P (ι.inv (c • x)) := by
    intro x
    induction x using Stacks.DeRham.CoordinateCech.formsFrame_induction (f.appLE V U e) with
    | h0 => intro c; simpa using h0
    | hadd x y hx hy => intro c; rw [smul_add, map_add]; exact hadd _ _ (hx c) (hy c)
    | hsmul c' x hx => intro c; rw [smul_smul]; exact hx _
    | hgen g => intro c; rw [hinv]; exact hgen c g
  simpa using key (ι.hom ω) 1

/-- The comparison map `Ω^a_{X/S} ⟶ j_*Ω^a_{Y/S}` is the degree-`a` part of the canonical map of
graded algebras of the square `j ≫ f = (j ≫ f) ≫ 𝟙`. -/
theorem formsDirectImageComparison_eq {Y : Scheme.{u}} (j : Y ⟶ X) (a : ℤ) :
    Scheme.Hom.formsDirectImageComparison j f a =
      (Scheme.Hom.deRhamFormsPushforwardHom j f (j ≫ f) (𝟙 S) (by simp)).app a := by
  rw [← Scheme.Hom.homEquiv_relativeDifferentialFormsMap]
  rfl

/-- **The comparison map on a generator**:
`c • d g₁ ∧ ⋯ ∧ d g_a ↦ j^♯c • d j^♯g₁ ∧ ⋯ ∧ d j^♯g_a`. -/
theorem formsDirectImageComparison_app_smul_gen {Y : Scheme.{u}} (j : Y ⟶ X) (U : X.Opens)
    {a : ℕ} (c : Γ(X, U)) (g : Fin a → Γ(X, U)) :
    (Scheme.Hom.formsDirectImageComparison j f (a : ℤ)).app U (c • gen f U g) =
      (j.app U).hom c • gen (j ≫ f) (j ⁻¹ᵁ U) fun i => (j.app U).hom (g i) := by
  rw [formsDirectImageComparison_eq]
  refine (Stacks.AlgebraicGeometry.AffineOpenDeRham.deRhamFormsPushforwardSections_smul j f
    (j ≫ f) (𝟙 S) (by simp) a c (gen f U g)).trans ?_
  congr 1
  exact Scheme.Hom.deRhamFormsPushforwardHom_homogeneousProdLeft j f (j ≫ f) (𝟙 S) (by simp)
    (op U) a g

end Stacks.DeRham.FormsGenerators
