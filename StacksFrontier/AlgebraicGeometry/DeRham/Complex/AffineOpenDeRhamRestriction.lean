module

public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.AffineOpenDeRhamWedge
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.Connection
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.GradedForms
public import StacksFrontier.RingTheory.DeRham.PolynomialHomotopy

/-!
# The comparison of forms over affine opens commutes with restriction

Let `f : X ⟶ S` be a morphism of schemes, let `V ⊆ S` be an affine open and let `U' ⊆ U ⊆ X` be
affine opens mapping into `V`. Over each of them the sections of the relative differential
`p`-forms are the Kähler forms of the ring of functions over `Γ(S, V)`
(`Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso`). This file shows that these
identifications are compatible with restriction: restricting a relative form from `U` to `U'` is
the map of Kähler forms induced by the restriction of functions `Γ(X, U) ⟶ Γ(X, U')`.

## Main definitions

* `Stacks.AlgebraicGeometry.AffineOpenDeRham.formsRestriction`: the map
  `⋀^p Ω[Γ(X, U)⁄Γ(S, V)] ⟶ ⋀^p Ω[Γ(X, U')⁄Γ(S, V)]` induced by restriction of functions.

## Main results

* `Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso_inv_restrict` and
  `Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso_hom_restrict`: the comparison of
  forms commutes with restriction.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.AffineOpenDeRham

/-! ### Kähler forms along a map of rings under a common base -/

section Generic

variable {R B B' : CommRingCat.{u}} (φ : R ⟶ B) (φ' : R ⟶ B') (ρ : B ⟶ B') (hρ : φ ≫ ρ = φ')

include hρ in
/-- `ρ` is a map of `R`-algebras. -/
theorem isScalarTower_of_comp_eq :
    letI := φ.hom.toAlgebra
    letI := φ'.hom.toAlgebra
    letI := ρ.hom.toAlgebra
    IsScalarTower R B B' := by
  let := φ.hom.toAlgebra
  let := φ'.hom.toAlgebra
  let := ρ.hom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq fun r => ?_
  change φ' r = ρ (φ r)
  rw [← hρ]
  rfl

/-- **The map of Kähler forms** `⋀^p Ω[B⁄R] ⟶ ⋀^p Ω[B'⁄R]` induced by a map `ρ : B ⟶ B'` of
rings under `R`. -/
def formsMap (p : ℕ) (x : ⋀[B]^p ↑(CommRingCat.KaehlerDifferential φ)) :
    ⋀[B']^p ↑(CommRingCat.KaehlerDifferential φ') :=
  letI := φ.hom.toAlgebra
  letI := φ'.hom.toAlgebra
  letI := ρ.hom.toAlgebra
  haveI := isScalarTower_of_comp_eq φ φ' ρ hρ
  KaehlerDifferential.mapExteriorPower R B B' p x

/-- `formsMap` is additive. -/
theorem formsMap_add (p : ℕ) (x y : ⋀[B]^p ↑(CommRingCat.KaehlerDifferential φ)) :
    formsMap φ φ' ρ hρ p (x + y) = formsMap φ φ' ρ hρ p x + formsMap φ φ' ρ hρ p y := by
  let := φ.hom.toAlgebra
  let := φ'.hom.toAlgebra
  let := ρ.hom.toAlgebra
  have := isScalarTower_of_comp_eq φ φ' ρ hρ
  exact map_add (KaehlerDifferential.mapExteriorPower R B B' p) x y

/-- `formsMap` sends `0` to `0`. -/
theorem formsMap_zero (p : ℕ) : formsMap φ φ' ρ hρ p 0 = 0 := by
  let := φ.hom.toAlgebra
  let := φ'.hom.toAlgebra
  let := ρ.hom.toAlgebra
  have := isScalarTower_of_comp_eq φ φ' ρ hρ
  exact map_zero (KaehlerDifferential.mapExteriorPower R B B' p)

/-- `formsMap` is semilinear along `ρ`: it sends `b • x` to `ρ b • formsMap x`. -/
theorem formsMap_smul (p : ℕ) (b : B) (x : ⋀[B]^p ↑(CommRingCat.KaehlerDifferential φ)) :
    formsMap φ φ' ρ hρ p (b • x) = ρ b • formsMap φ φ' ρ hρ p x := by
  let := φ.hom.toAlgebra
  let := φ'.hom.toAlgebra
  let := ρ.hom.toAlgebra
  have := isScalarTower_of_comp_eq φ φ' ρ hρ
  exact (map_smul (KaehlerDifferential.mapExteriorPower R B B' p) b x).trans
    (algebraMap_smul B' b _).symm

/-- `formsMap` sends the wedge `d a₁ ∧ ⋯ ∧ d a_p` to the wedge `d (ρ a₁) ∧ ⋯ ∧ d (ρ a_p)`. -/
theorem formsMap_ιMulti_d (p : ℕ) (a : Fin p → B) :
    formsMap φ φ' ρ hρ p
        (exteriorPower.ιMulti B p fun i ↦ CommRingCat.KaehlerDifferential.d (f := φ) (a i)) =
      exteriorPower.ιMulti B' p fun i ↦ CommRingCat.KaehlerDifferential.d (f := φ') (ρ (a i)) := by
  let := φ.hom.toAlgebra
  let := φ'.hom.toAlgebra
  let := ρ.hom.toAlgebra
  have := isScalarTower_of_comp_eq φ φ' ρ hρ
  change KaehlerDifferential.mapExteriorPower R B B' p
      (exteriorPower.ιMulti B p fun i ↦ KaehlerDifferential.D R B (a i)) =
    exteriorPower.ιMulti B' p fun i ↦ KaehlerDifferential.D R B' (algebraMap B B' (a i))
  rw [KaehlerDifferential.mapExteriorPower_ιMulti]
  congr 1
  funext i
  exact KaehlerDifferential.map_D R R B B' (a i)

/-- A morphism out of `⋀^p` of a module, read as a `ModuleCat` object, is additive. -/
theorem moduleCat_hom_exteriorPower_add {M N : ModuleCat.{u} B} (p : ℕ)
    (g : ModuleCat.of B (⋀[B]^p M) ⟶ N) (x y : ⋀[B]^p M) : g (x + y) = g x + g y :=
  map_add g.hom x y

/-- The forms `c₀ · (d c₁ ∧ ⋯ ∧ d c_p)` span the exterior powers of the Kähler differentials of
a map of commutative rings. -/
theorem span_smul_ιMulti_d_eq_top {A B : CommRingCat.{u}} (φ : A ⟶ B) (p : ℕ) :
    Submodule.span B (Set.range fun c : Fin (p + 1) → B ↦
      c 0 • exteriorPower.ιMulti B p fun i ↦
        CommRingCat.KaehlerDifferential.d (f := φ) (c i.succ)) = ⊤ := by
  let := φ.hom.toAlgebra
  exact Crystalline.span_range_smul_ιMulti_eq_top (R := B) (KaehlerDifferential.D A B)
    (KaehlerDifferential.span_range_derivation _ _) p

/-- Two functions out of `⋀^p` of the Kähler differentials of a map of commutative rings agree
when they agree on the wedges of differentials and their agreement is stable under sums and
under the scalar action. -/
theorem eq_of_smul_ιMulti_d {A B : CommRingCat.{u}} (φ : A ⟶ B) (p : ℕ) {N : Type*}
    (F G : ⋀[B]^p ↑(CommRingCat.KaehlerDifferential φ) → N) (h0 : F 0 = G 0)
    (hadd : ∀ y z, F y = G y → F z = G z → F (y + z) = G (y + z))
    (hsmul : ∀ (b : B) (y : ⋀[B]^p ↑(CommRingCat.KaehlerDifferential φ)), F y = G y →
      F (b • y) = G (b • y))
    (hgen : ∀ c : Fin p → B, F (exteriorPower.ιMulti B p fun i ↦
        CommRingCat.KaehlerDifferential.d (f := φ) (c i)) =
      G (exteriorPower.ιMulti B p fun i ↦ CommRingCat.KaehlerDifferential.d (f := φ) (c i)))
    (x : ⋀[B]^p ↑(CommRingCat.KaehlerDifferential φ)) : F x = G x := by
  have hx := (Submodule.eq_top_iff'.1 (span_smul_ιMulti_d_eq_top φ p)) x
  induction hx using Submodule.span_induction with
  | mem _ hy =>
    obtain ⟨c, rfl⟩ := hy
    exact hsmul (c 0) _ (hgen fun i ↦ c i.succ)
  | zero => exact h0
  | add y z _ _ hy hz => exact hadd y z hy hz
  | smul b y _ hy => exact hsmul b y hy

end Generic

variable {X S : Scheme.{u}} (f : X ⟶ S) {U U' : X.Opens} {V : S.Opens}

/-- **The restriction of Kähler forms** along `Γ(X, U) ⟶ Γ(X, U')`, over `Γ(S, V)`: the map
`⋀^p Ω[Γ(X, U)⁄Γ(S, V)] ⟶ ⋀^p Ω[Γ(X, U')⁄Γ(S, V)]` induced by restriction of functions. -/
abbrev formsRestriction (e : U ≤ f ⁻¹ᵁ V) (e' : U' ≤ f ⁻¹ᵁ V) (h : U' ≤ U) (p : ℕ) :=
  formsMap (f.appLE V U e) (f.appLE V U' e') (X.presheaf.map (homOfLE h).op)
    (by rw [Scheme.Hom.appLE_map]) p

variable {f} (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (hV : IsAffineOpen V)

include hU hU' hV in
/-- **The comparison of forms over affine opens commutes with restriction**, read through its
inverse. -/
theorem formsSectionsIso_inv_restrict (e : U ≤ f ⁻¹ᵁ V) (e' : U' ≤ f ⁻¹ᵁ V) (h : U' ≤ U) (p : ℕ)
    (x : ⋀[Γ(X, U)]^p ↥(CommRingCat.KaehlerDifferential (f.appLE V U e))) :
    (Scheme.Hom.relativeDifferentialForms f (p : ℤ)).presheaf.map (homOfLE h).op
        ((formsSectionsIso f hU hV e p).inv x) =
      (formsSectionsIso f hU' hV e' p).inv (formsRestriction f e e' h p x) := by
  have hstep : ∀ (b : Γ(X, U))
      (y : ⋀[Γ(X, U)]^p ↥(CommRingCat.KaehlerDifferential (f.appLE V U e))),
      (Scheme.Hom.relativeDifferentialForms f (p : ℤ)).presheaf.map (homOfLE h).op
          ((formsSectionsIso f hU hV e p).inv y) =
        (formsSectionsIso f hU' hV e' p).inv (formsRestriction f e e' h p y) →
      (Scheme.Hom.relativeDifferentialForms f (p : ℤ)).presheaf.map (homOfLE h).op
          ((formsSectionsIso f hU hV e p).inv (b • y)) =
        (formsSectionsIso f hU' hV e' p).inv (formsRestriction f e e' h p (b • y)) := by
    intro b y hy
    unfold formsRestriction at hy ⊢
    have e₁ : (formsSectionsIso f hU hV e p).inv (b • y) =
        b • (formsSectionsIso f hU hV e p).inv y :=
      map_smul (formsSectionsIso f hU hV e p).inv.hom b y
    have e₂ : (formsSectionsIso f hU' hV e' p).inv
        (X.presheaf.map (homOfLE h).op b • formsRestriction f e e' h p y) =
        X.presheaf.map (homOfLE h).op b •
          (formsSectionsIso f hU' hV e' p).inv (formsRestriction f e e' h p y) :=
      map_smul (formsSectionsIso f hU' hV e' p).inv.hom _ _
    rw [e₁, Scheme.Modules.map_smul, hy, formsMap_smul]
    exact e₂.symm
  have hgen : ∀ c : Fin p → Γ(X, U),
      (Scheme.Hom.relativeDifferentialForms f (p : ℤ)).presheaf.map (homOfLE h).op
          ((formsSectionsIso f hU hV e p).inv
            (exteriorPower.ιMulti Γ(X, U) p fun i ↦ CommRingCat.KaehlerDifferential.d (c i))) =
        (formsSectionsIso f hU' hV e' p).inv (formsRestriction f e e' h p
          (exteriorPower.ιMulti Γ(X, U) p fun i ↦ CommRingCat.KaehlerDifferential.d (c i))) := by
    intro c
    unfold formsRestriction
    rw [formsMap_ιMulti_d]
    refine (congrArg (fun z => (Scheme.Hom.relativeDifferentialForms f (p : ℤ)).presheaf.map
      (homOfLE h).op z) (formsSectionsIso_inv_ιMulti_d f hU hV e p c)).trans ?_
    refine Eq.trans ?_ (formsSectionsIso_inv_ιMulti_d f hU' hV e' p
      fun i ↦ X.presheaf.map (homOfLE h).op (c i)).symm
    refine ((Scheme.Hom.deRhamAlgebras f).exterior.toPresheafGradedAlgebra
      |>.homogeneousProdLeft_naturality (homOfLE h).op p _).trans ?_
    congr 1
    funext i
    exact _root_.AlgebraicGeometry.SheafOfModules.exactOne_map (Scheme.Hom.deRhamAlgebras f)
      (homOfLE h).op (c i)
  refine eq_of_smul_ιMulti_d (f.appLE V U e) p
    (fun y ↦ (Scheme.Hom.relativeDifferentialForms f (p : ℤ)).presheaf.map (homOfLE h).op
      ((formsSectionsIso f hU hV e p).inv y))
    (fun y ↦ (formsSectionsIso f hU' hV e' p).inv (formsRestriction f e e' h p y)) ?_ ?_ hstep
    hgen x
  · have h₁ : (formsSectionsIso f hU hV e p).inv 0 = 0 :=
      map_zero (formsSectionsIso f hU hV e p).inv.hom
    have h₂ : (formsSectionsIso f hU' hV e' p).inv (formsRestriction f e e' h p 0) = 0 := by
      unfold formsRestriction
      rw [formsMap_zero]
      exact map_zero (formsSectionsIso f hU' hV e' p).inv.hom
    rw [h₁, h₂]
    exact map_zero
      ((Scheme.Hom.relativeDifferentialForms f (p : ℤ)).presheaf.map (homOfLE h).op).hom
  · intro y z hy hz
    beta_reduce at hy hz ⊢
    unfold formsRestriction at hy hz ⊢
    simp only [formsMap_add, map_add]
    exact congrArg₂ (· + ·) hy hz

include hU hU' hV in
/-- **The comparison of forms over affine opens commutes with restriction.** -/
theorem formsSectionsIso_hom_restrict (e : U ≤ f ⁻¹ᵁ V) (e' : U' ≤ f ⁻¹ᵁ V) (h : U' ≤ U) (p : ℕ)
    (y : Γ(Scheme.Hom.relativeDifferentialForms f (p : ℤ), U)) :
    (formsSectionsIso f hU' hV e' p).hom
        ((Scheme.Hom.relativeDifferentialForms f (p : ℤ)).presheaf.map (homOfLE h).op y) =
      formsRestriction f e e' h p ((formsSectionsIso f hU hV e p).hom y) := by
  have := formsSectionsIso_inv_restrict hU hU' hV e e' h p ((formsSectionsIso f hU hV e p).hom y)
  rw [Iso.hom_inv_id_apply] at this
  rw [this, Iso.inv_hom_id_apply]

end Stacks.AlgebraicGeometry.AffineOpenDeRham

end
