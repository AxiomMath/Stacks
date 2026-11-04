module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.SmoothLift.RingData
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff

/-!
# The affine objects of a square-zero thickening in the big fppf site

Fix an affine first-order thickening `Spec (A' ⧸ C) ⊂ Spec A'` over a scheme `S` of a big fppf
site, given by an ideal `C` with `C * C = 0` and a structure morphism `Spec A' ⟶ S`.  For an
`A'`-algebra `R` of size below the cutoff of the site, this file realises as objects of the big
fppf site over `S` the spectra of the rings of
`StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.SmoothLift.RingData`:

* `O R = Spec R`, its reduction `O₀ R = Spec (R ⧸ CR)`, the tangent thickening
  `Oₑ R = Spec (R ⧸ CR ⊕ CR)` and the pushout `Oₚ R = Spec (E ×_Q R)`;
* the morphisms between them, and their functoriality in `R`.

## References

* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
-/

@[expose] public section

open CategoryTheory Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space.SmoothLift

open Stacks.SmoothLift

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The spectrum of a ring of size below the cutoff is contained in the site. -/
theorem contains_spec {Rc : CommRingCat.{u}} (h : #Rc < B.cutoff) : B.Contains (Spec Rc) := by
  show (Spec Rc).size < B.cutoff
  rw [Scheme.size_Spec]
  exact max_lt B.aleph0_lt_cutoff h

variable (B S hS)

/-- The data of an affine first-order thickening over `S`: a ring `A'` of size below the cutoff,
a square-zero ideal `C` of it, and a structure morphism `Spec A' ⟶ S`. -/
structure Base (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) where
  /-- The ring of the ambient affine scheme. -/
  A : Type u
  [commRing : CommRing A]
  /-- The square-zero ideal. -/
  C : Ideal A
  [sq : Fact (C * C = ⊥)]
  /-- The structure morphism. -/
  pS : Spec (CommRingCat.of A) ⟶ S
  /-- The size bound. -/
  size : #A < B.cutoff

attribute [instance] Base.commRing Base.sq

variable {B S hS} (D : Base B S hS)

/-- An `A'`-algebra of size below the cutoff. -/
structure Alg where
  /-- The carrier. -/
  R : Type u
  [commRing : CommRing R]
  [algebra : Algebra D.A R]
  /-- The size bound. -/
  size : #R < B.cutoff

attribute [instance] Alg.commRing Alg.algebra

variable {D}

/-- The object of the site attached to a ring with a map from `A'`. -/
noncomputable def objOf (Rc : CommRingCat.{u}) (φ : CommRingCat.of D.A ⟶ Rc)
    (h : #Rc < B.cutoff) : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS (contains_spec h) (Spec.map φ ≫ D.pS)

/-- The morphism of the site attached to a ring map compatible with the maps from `A'`. -/
noncomputable def homOf {Rc Rc' : CommRingCat.{u}} {φ : CommRingCat.of D.A ⟶ Rc}
    {φ' : CommRingCat.of D.A ⟶ Rc'} {h : #Rc < B.cutoff} {h' : #Rc' < B.cutoff}
    (ψ : Rc ⟶ Rc') (hψ : φ ≫ ψ = φ') : objOf Rc' φ' h' ⟶ objOf Rc φ h :=
  BigFppfOver.homMk B S hS (contains_spec h) (Spec.map φ ≫ D.pS) (Spec.map ψ) (by
    change Spec.map ψ ≫ Spec.map φ ≫ D.pS = Spec.map φ' ≫ D.pS
    rw [← Category.assoc, ← Spec.map_comp, hψ])

/-- The morphism of schemes underlying `homOf ψ hψ` is `Spec.map ψ`. -/
@[simp] theorem toScheme_map_homOf {Rc Rc' : CommRingCat.{u}} {φ : CommRingCat.of D.A ⟶ Rc}
    {φ' : CommRingCat.of D.A ⟶ Rc'} {h : #Rc < B.cutoff} {h' : #Rc' < B.cutoff}
    (ψ : Rc ⟶ Rc') (hψ : φ ≫ ψ = φ') :
    (BigFppfOver.toScheme B S hS).map (homOf (h := h) (h' := h') ψ hψ) = Spec.map ψ := rfl

/-- `homOf` sends a composite of ring maps to the composite of the morphisms. -/
theorem homOf_comp {Rc Rc' Rc'' : CommRingCat.{u}} {φ : CommRingCat.of D.A ⟶ Rc}
    {φ' : CommRingCat.of D.A ⟶ Rc'} {φ'' : CommRingCat.of D.A ⟶ Rc''} {h : #Rc < B.cutoff}
    {h' : #Rc' < B.cutoff} {h'' : #Rc'' < B.cutoff} (ψ : Rc ⟶ Rc') (ψ' : Rc' ⟶ Rc'')
    (hψ : φ ≫ ψ = φ') (hψ' : φ' ≫ ψ' = φ'') :
    homOf (h := h') (h' := h'') ψ' hψ' ≫ homOf (h := h) (h' := h') ψ hψ =
      homOf (h := h) (h' := h'') (ψ ≫ ψ') (by rw [← Category.assoc, hψ, hψ']) :=
  (BigFppfOver.toScheme B S hS).map_injective (by
    rw [Functor.map_comp, toScheme_map_homOf, toScheme_map_homOf, toScheme_map_homOf,
      Spec.map_comp]; rfl)

/-- `homOf` depends only on the ring map. -/
theorem homOf_ext {Rc Rc' : CommRingCat.{u}} {φ : CommRingCat.of D.A ⟶ Rc}
    {φ' : CommRingCat.of D.A ⟶ Rc'} {h : #Rc < B.cutoff} {h' : #Rc' < B.cutoff}
    {ψ₁ ψ₂ : Rc ⟶ Rc'} (hψ₁ : φ ≫ ψ₁ = φ') (hψ₂ : φ ≫ ψ₂ = φ') (e : ψ₁ = ψ₂) :
    homOf (h := h) (h' := h') ψ₁ hψ₁ = homOf (h := h) (h' := h') ψ₂ hψ₂ := by
  subst e; rfl

/-- `homOf` sends the identity ring map to the identity. -/
theorem homOf_id {Rc : CommRingCat.{u}} {φ : CommRingCat.of D.A ⟶ Rc} {h : #Rc < B.cutoff} :
    homOf (h := h) (h' := h) (𝟙 Rc) (Category.comp_id φ) = 𝟙 (objOf Rc φ h) :=
  (BigFppfOver.toScheme B S hS).map_injective (by
    rw [toScheme_map_homOf, Spec.map_id]
    exact ((BigFppfOver.toScheme B S hS).map_id (objOf Rc φ h)).symm)

/-! ### Cardinal bounds -/

/-- The reduction `R ⧸ CR` has size below the cutoff. -/
theorem mk_Q_lt (R : Alg D) : #(Q D.C R.R) < B.cutoff :=
  lt_of_le_of_lt (Cardinal.mk_le_of_surjective Ideal.Quotient.mk_surjective) R.size

/-- The ideal `CR` has size below the cutoff. -/
theorem mk_M_lt (R : Alg D) : #(M D.C R.R) < B.cutoff :=
  lt_of_le_of_lt (Cardinal.mk_subtype_le _) R.size

/-- The ring `R ⧸ CR ⊕ CR` has size below the cutoff. -/
theorem mk_E_lt (R : Alg D) : #(E D.C R.R) < B.cutoff := by
  have : #(E D.C R.R) = #(Q D.C R.R × M D.C R.R) := rfl
  rw [this, Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
  exact Cardinal.mul_lt_of_lt B.aleph0_lt_cutoff.le (mk_Q_lt R) (mk_M_lt R)

/-- The fibre product `E ×_Q R` has size below the cutoff. -/
theorem mk_P_lt (R : Alg D) : #(P D.C R.R) < B.cutoff := by
  refine lt_of_le_of_lt (Cardinal.mk_subtype_le _) ?_
  rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
  exact Cardinal.mul_lt_of_lt B.aleph0_lt_cutoff.le (mk_E_lt R) R.size

/-! ### The rings, as commutative rings under `A'` -/

variable (R : Alg D)

/-- The structure map `A' → R`. -/
noncomputable abbrev φO : CommRingCat.of D.A ⟶ CommRingCat.of R.R :=
  CommRingCat.ofHom (algebraMap D.A R.R)

/-- The structure map `A' → R ⧸ CR`. -/
noncomputable abbrev φQ : CommRingCat.of D.A ⟶ CommRingCat.of (Q D.C R.R) :=
  φO R ≫ CommRingCat.ofHom (Ideal.Quotient.mk (sqIdeal D.C R.R))

/-- The structure map `A' → E`. -/
noncomputable abbrev φE : CommRingCat.of D.A ⟶ CommRingCat.of (E D.C R.R) :=
  φQ R ≫ CommRingCat.ofHom (inlE D.C R.R)

/-- The diagonal ring map `R → E ×_Q R`, `r ↦ ((r̄, 0), r)`. -/
noncomputable def pDiag : R.R →+* P D.C R.R where
  toFun r := ⟨((inlE D.C R.R) (Ideal.Quotient.mk _ r), r), rfl⟩
  map_one' := by ext <;> simp
  map_mul' _ _ := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' _ _ := by ext <;> simp

/-- The action map `σ : E ×_Q R → R` is a retraction of the diagonal `R → E ×_Q R`. -/
theorem sigma_comp_pDiag : (sigma D.C R.R).comp (pDiag R) = RingHom.id _ := by
  ext r
  show r + (((inlE D.C R.R (Ideal.Quotient.mk _ r)).snd : M D.C R.R) : R.R) = r
  simp

/-- The projection `E ×_Q R → R` is a retraction of the diagonal `R → E ×_Q R`. -/
theorem pullbackSnd_comp_pDiag :
    ((fstE D.C R.R).pullbackSnd (Ideal.Quotient.mk (sqIdeal D.C R.R))).comp (pDiag R) =
      RingHom.id _ := rfl

/-- The diagonal `R → E ×_Q R` followed by the projection to `E` is `r ↦ (r̄, 0)`. -/
theorem pullbackFst_comp_pDiag :
    ((fstE D.C R.R).pullbackFst (Ideal.Quotient.mk (sqIdeal D.C R.R))).comp (pDiag R) =
      (inlE D.C R.R).comp (Ideal.Quotient.mk _) := rfl

/-- The structure map `A' → E ×_Q R`. -/
noncomputable abbrev φP : CommRingCat.of D.A ⟶ CommRingCat.of (P D.C R.R) :=
  φO R ≫ CommRingCat.ofHom (pDiag R)

/-! ### The objects -/

/-- `Spec R`. -/
noncomputable abbrev O : BigFppfOver B S hS := objOf (CommRingCat.of R.R) (φO R) R.size

/-- `Spec (R ⧸ CR)`. -/
noncomputable abbrev O₀ : BigFppfOver B S hS :=
  objOf (CommRingCat.of (Q D.C R.R)) (φQ R) (mk_Q_lt R)

/-- `Spec (R ⧸ CR ⊕ CR)`. -/
noncomputable abbrev Oₑ : BigFppfOver B S hS :=
  objOf (CommRingCat.of (E D.C R.R)) (φE R) (mk_E_lt R)

/-- `Spec (E ×_Q R)`, the pushout `O ⊔_{O₀} Oₑ`. -/
noncomputable abbrev Oₚ : BigFppfOver B S hS :=
  objOf (CommRingCat.of (P D.C R.R)) (φP R) (mk_P_lt R)

/-! ### The morphisms -/

/-- The closed immersion `O₀ ⟶ O`. -/
noncomputable def incl : O₀ R ⟶ O R :=
  homOf (CommRingCat.ofHom (Ideal.Quotient.mk (sqIdeal D.C R.R))) rfl

/-- The zero section `O₀ ⟶ Oₑ`. -/
noncomputable def zeroSec : O₀ R ⟶ Oₑ R :=
  homOf (CommRingCat.ofHom (fstE D.C R.R)) rfl

/-- The retraction `Oₑ ⟶ O₀`. -/
noncomputable def retr : Oₑ R ⟶ O₀ R :=
  homOf (CommRingCat.ofHom (inlE D.C R.R)) rfl

/-- The first leg `O ⟶ Oₚ` of the pushout. -/
noncomputable def pInl : O R ⟶ Oₚ R :=
  homOf (CommRingCat.ofHom ((fstE D.C R.R).pullbackSnd (Ideal.Quotient.mk (sqIdeal D.C R.R))))
    rfl

/-- The second leg `Oₑ ⟶ Oₚ` of the pushout. -/
noncomputable def pInr : Oₑ R ⟶ Oₚ R :=
  homOf (CommRingCat.ofHom ((fstE D.C R.R).pullbackFst (Ideal.Quotient.mk (sqIdeal D.C R.R))))
    rfl

/-- The action morphism `O ⟶ Oₚ`, given by `σ`. -/
noncomputable def actHom : O R ⟶ Oₚ R :=
  homOf (CommRingCat.ofHom (sigma D.C R.R)) (by
    change CommRingCat.ofHom (algebraMap D.A R.R) ≫ CommRingCat.ofHom (pDiag R) ≫
      CommRingCat.ofHom (sigma D.C R.R) = _
    rw [← CommRingCat.ofHom_comp, sigma_comp_pDiag]
    rfl)

/-- The projection `Oₚ ⟶ O` given by the diagonal. -/
noncomputable def pProj : Oₚ R ⟶ O R :=
  homOf (CommRingCat.ofHom (pDiag R)) rfl

/-- Multiplication of the tangent direction by a scalar of the reduction. -/
noncomputable def smulHom (a : Q D.C R.R) : Oₑ R ⟶ Oₑ R :=
  homOf (CommRingCat.ofHom (smulE D.C R.R a)) (by
    change _ ≫ CommRingCat.ofHom (inlE D.C R.R) ≫ CommRingCat.ofHom (smulE D.C R.R a) = _
    rw [← CommRingCat.ofHom_comp, smulE_comp_inlE])

/-! ### Functoriality in the algebra -/

variable {R} {R' R'' : Alg D}

/-- `homOf` sends a commutative square of ring maps to a commutative square of the site. -/
theorem homOf_comm {Rc₁ Rc₂ Rc₃ Rc₄ : CommRingCat.{u}} {φ₁ : CommRingCat.of D.A ⟶ Rc₁}
    {φ₂ : CommRingCat.of D.A ⟶ Rc₂} {φ₃ : CommRingCat.of D.A ⟶ Rc₃}
    {φ₄ : CommRingCat.of D.A ⟶ Rc₄} {h₁ : #Rc₁ < B.cutoff} {h₂ : #Rc₂ < B.cutoff}
    {h₃ : #Rc₃ < B.cutoff} {h₄ : #Rc₄ < B.cutoff}
    (a : Rc₁ ⟶ Rc₂) (b : Rc₂ ⟶ Rc₄) (c : Rc₁ ⟶ Rc₃) (d : Rc₃ ⟶ Rc₄)
    (ha : φ₁ ≫ a = φ₂) (hb : φ₂ ≫ b = φ₄) (hc : φ₁ ≫ c = φ₃) (hd : φ₃ ≫ d = φ₄)
    (e : a ≫ b = c ≫ d) :
    homOf (h := h₂) (h' := h₄) b hb ≫ homOf (h := h₁) (h' := h₂) a ha =
      homOf (h := h₃) (h' := h₄) d hd ≫ homOf (h := h₁) (h' := h₃) c hc := by
  rw [homOf_comp, homOf_comp]
  exact homOf_ext _ _ e

/-- An `A'`-algebra map `R → R'` commutes with the structure maps from `A'`. -/
theorem φO_comp (h : R.R →ₐ[D.A] R'.R) : φO R ≫ CommRingCat.ofHom h.toRingHom = φO R' := by
  ext a
  exact h.commutes a

/-- `Spec R' ⟶ Spec R` for an algebra map `R → R'`. -/
noncomputable def mO (h : R.R →ₐ[D.A] R'.R) : O R' ⟶ O R :=
  homOf (CommRingCat.ofHom h.toRingHom) (φO_comp h)

/-- The map of reductions. -/
noncomputable def mO₀ (h : R.R →ₐ[D.A] R'.R) : O₀ R' ⟶ O₀ R :=
  homOf (CommRingCat.ofHom (qMap D.C h)) (by
    change φO R ≫ CommRingCat.ofHom (Ideal.Quotient.mk _) ≫ CommRingCat.ofHom (qMap D.C h) =
      φO R' ≫ CommRingCat.ofHom (Ideal.Quotient.mk _)
    rw [← CommRingCat.ofHom_comp, qMap_comp_mk, CommRingCat.ofHom_comp, ← Category.assoc,
      φO_comp])

/-- The map of tangent thickenings induced by `h` sends `(r̄, 0)` to `((h r)‾, 0)`. -/
theorem eMap_inlE_mk (h : R.R →ₐ[D.A] R'.R) (r : R.R) :
    eMap D.C h (inlE D.C R.R (Ideal.Quotient.mk _ r)) =
      inlE D.C R'.R (Ideal.Quotient.mk _ (h r)) := by
  ext <;> simp [qMap_mk]

/-- The map of tangent thickenings. -/
noncomputable def mOₑ (h : R.R →ₐ[D.A] R'.R) : Oₑ R' ⟶ Oₑ R :=
  homOf (CommRingCat.ofHom (eMap D.C h)) (CommRingCat.hom_ext (RingHom.ext fun a => by
    change eMap D.C h (inlE D.C R.R (Ideal.Quotient.mk _ (algebraMap D.A R.R a))) =
      inlE D.C R'.R (Ideal.Quotient.mk _ (algebraMap D.A R'.R a))
    rw [eMap_inlE_mk, h.commutes]))

/-- The diagonal `R → E ×_Q R` is natural in the algebra `R`. -/
theorem pMap_comp_pDiag (h : R.R →ₐ[D.A] R'.R) :
    (pMap D.C h).comp (pDiag R) = (pDiag R').comp h.toRingHom :=
  RingHom.ext fun r => Subtype.ext (Prod.ext (eMap_inlE_mk h r) rfl)

/-- The map of pushouts. -/
noncomputable def mOₚ (h : R.R →ₐ[D.A] R'.R) : Oₚ R' ⟶ Oₚ R :=
  homOf (CommRingCat.ofHom (pMap D.C h)) (by
    change φO R ≫ CommRingCat.ofHom (pDiag R) ≫ CommRingCat.ofHom (pMap D.C h) =
      φO R' ≫ CommRingCat.ofHom (pDiag R')
    rw [← CommRingCat.ofHom_comp, pMap_comp_pDiag, CommRingCat.ofHom_comp, ← Category.assoc,
      φO_comp])

/-- Two morphisms between objects of the site agree as soon as their underlying morphisms of
schemes do. -/
theorem ext_toScheme {U V : BigFppfOver B S hS} {f g : U ⟶ V}
    (h : (BigFppfOver.toScheme B S hS).map f = (BigFppfOver.toScheme B S hS).map g) : f = g :=
  (BigFppfOver.toScheme B S hS).map_injective h

/-- `Spec` sends a commutative square of rings to a commutative square of schemes. -/
theorem specMap_comp_eq {A₁ A₂ A₃ A₄ : CommRingCat.{u}} (a : A₁ ⟶ A₂) (b : A₂ ⟶ A₄)
    (c : A₁ ⟶ A₃) (d : A₃ ⟶ A₄) (e : a ≫ b = c ≫ d) :
    Spec.map b ≫ Spec.map a = Spec.map d ≫ Spec.map c := by
  rw [← Spec.map_comp, ← Spec.map_comp, e]

/-- If `a ≫ b = 𝟙` then `Spec.map b ≫ Spec.map a = 𝟙`. -/
theorem specMap_comp_eq_id {A₁ A₂ : CommRingCat.{u}} (a : A₁ ⟶ A₂) (b : A₂ ⟶ A₁)
    (e : a ≫ b = 𝟙 _) : Spec.map b ≫ Spec.map a = 𝟙 _ := by
  rw [← Spec.map_comp, e, Spec.map_id]

/-- `Spec` of a composite of ring homomorphisms is the composite of the `Spec`s. -/
private theorem specMap_ofHom_comp {A₁ A₂ A₃ : Type u} [CommRing A₁] [CommRing A₂] [CommRing A₃]
    {a : A₁ →+* A₂} {b : A₂ →+* A₃} {c : A₁ →+* A₃} (e : b.comp a = c) :
    Spec.map (CommRingCat.ofHom b) ≫ Spec.map (CommRingCat.ofHom a) =
      Spec.map (CommRingCat.ofHom c) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, e]

/-- `Spec` sends a commutative square of ring homomorphisms to a commutative square. -/
private theorem specMap_ofHom_comp_eq {A₁ A₂ A₃ A₄ : Type u} [CommRing A₁] [CommRing A₂]
    [CommRing A₃] [CommRing A₄] {a : A₁ →+* A₂} {b : A₂ →+* A₄} {c : A₁ →+* A₃} {d : A₃ →+* A₄}
    (e : b.comp a = d.comp c) :
    Spec.map (CommRingCat.ofHom b) ≫ Spec.map (CommRingCat.ofHom a) =
      Spec.map (CommRingCat.ofHom d) ≫ Spec.map (CommRingCat.ofHom c) :=
  specMap_comp_eq _ _ _ _ (by rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e])

/-- The closed immersion `O₀ ⟶ O` is natural in the algebra. -/
theorem incl_mO (h : R.R →ₐ[D.A] R'.R) : incl R' ≫ mO h = mO₀ h ≫ incl R :=
  ext_toScheme (specMap_comp_eq _ _ _ _ rfl)

/-- The zero section `O₀ ⟶ Oₑ` is natural in the algebra. -/
theorem zeroSec_mOₑ (h : R.R →ₐ[D.A] R'.R) : zeroSec R' ≫ mOₑ h = mO₀ h ≫ zeroSec R :=
  ext_toScheme (specMap_ofHom_comp_eq (fstE_comp_eMap _ h))

/-- The retraction `Oₑ ⟶ O₀` is natural in the algebra. -/
theorem retr_mO₀ (h : R.R →ₐ[D.A] R'.R) : retr R' ≫ mO₀ h = mOₑ h ≫ retr R :=
  ext_toScheme (specMap_ofHom_comp_eq (eMap_comp_inlE _ h).symm)

/-- The first leg `O ⟶ Oₚ` of the pushout is natural in the algebra. -/
theorem pInl_mOₚ (h : R.R →ₐ[D.A] R'.R) : pInl R' ≫ mOₚ h = mO h ≫ pInl R :=
  ext_toScheme (specMap_comp_eq _ _ _ _ rfl)

/-- The second leg `Oₑ ⟶ Oₚ` of the pushout is natural in the algebra. -/
theorem pInr_mOₚ (h : R.R →ₐ[D.A] R'.R) : pInr R' ≫ mOₚ h = mOₑ h ≫ pInr R :=
  ext_toScheme (specMap_comp_eq _ _ _ _ rfl)

/-- The action morphism `O ⟶ Oₚ` is natural in the algebra. -/
theorem actHom_mOₚ (h : R.R →ₐ[D.A] R'.R) : actHom R' ≫ mOₚ h = mO h ≫ actHom R :=
  ext_toScheme (specMap_ofHom_comp_eq (sigma_comp_pMap _ h))

/-- Multiplication by `a` on `Oₑ` is natural in the algebra, the scalar `a` being carried along
the map of reductions. -/
theorem smul_mOₑ (h : R.R →ₐ[D.A] R'.R) (a : Q D.C R.R) :
    smulHom R' (qMap D.C h a) ≫ mOₑ h = mOₑ h ≫ smulHom R a :=
  ext_toScheme (specMap_ofHom_comp_eq (eMap_comp_smulE _ h a).symm)

/-- `mO` sends a composite of algebra maps to the composite of the morphisms. -/
theorem mO_comp (h : R.R →ₐ[D.A] R'.R) (h' : R'.R →ₐ[D.A] R''.R) :
    mO h' ≫ mO h = mO (h'.comp h) :=
  ext_toScheme (specMap_ofHom_comp rfl)

/-- `mO₀` sends a composite of algebra maps to the composite of the morphisms. -/
theorem mO₀_comp (h : R.R →ₐ[D.A] R'.R) (h' : R'.R →ₐ[D.A] R''.R) :
    mO₀ h' ≫ mO₀ h = mO₀ (h'.comp h) :=
  ext_toScheme (specMap_ofHom_comp (qMap_comp _ h h').symm)

/-- `mOₑ` sends a composite of algebra maps to the composite of the morphisms. -/
theorem mOₑ_comp (h : R.R →ₐ[D.A] R'.R) (h' : R'.R →ₐ[D.A] R''.R) :
    mOₑ h' ≫ mOₑ h = mOₑ (h'.comp h) :=
  ext_toScheme (specMap_ofHom_comp (eMap_comp _ h h').symm)

/-- `mOₚ` sends a composite of algebra maps to the composite of the morphisms. -/
theorem mOₚ_comp (h : R.R →ₐ[D.A] R'.R) (h' : R'.R →ₐ[D.A] R''.R) :
    mOₚ h' ≫ mOₚ h = mOₚ (h'.comp h) :=
  ext_toScheme (specMap_ofHom_comp (pMap_comp _ h h').symm)

/-! ### The relations of the pushout square -/

/-- The pushout square commutes: `incl ≫ pInl = zeroSec ≫ pInr`. -/
theorem incl_pInl : incl R ≫ pInl R = zeroSec R ≫ pInr R :=
  ext_toScheme (specMap_ofHom_comp_eq ((fstE D.C R.R).pullback_comm_sq _).symm)

/-- The action morphism and the first leg `O ⟶ Oₚ` agree on `O₀`. -/
theorem incl_actHom : incl R ≫ actHom R = incl R ≫ pInl R :=
  ext_toScheme (specMap_ofHom_comp_eq
    ((mk_comp_sigma _ _).trans ((fstE D.C R.R).pullback_comm_sq _)))

/-- The projection `Oₚ ⟶ O` is a retraction of the first leg `O ⟶ Oₚ`. -/
theorem pInl_pProj : pInl R ≫ pProj R = 𝟙 _ :=
  ext_toScheme ((specMap_comp_eq_id _ _ (by
    rw [← CommRingCat.ofHom_comp, pullbackSnd_comp_pDiag]; rfl)).trans
    ((BigFppfOver.toScheme B S hS).map_id (O R)).symm)

/-- The second leg `Oₑ ⟶ Oₚ` followed by the projection `Oₚ ⟶ O` is `retr ≫ incl`. -/
theorem pInr_pProj : pInr R ≫ pProj R = retr R ≫ incl R :=
  ext_toScheme (specMap_comp_eq _ _ _ _ rfl)

/-- The projection `Oₚ ⟶ O` is a retraction of the action morphism `O ⟶ Oₚ`. -/
theorem actHom_pProj : actHom R ≫ pProj R = 𝟙 _ :=
  ext_toScheme ((specMap_comp_eq_id _ _ (by
    rw [← CommRingCat.ofHom_comp, sigma_comp_pDiag]; rfl)).trans
    ((BigFppfOver.toScheme B S hS).map_id (O R)).symm)

/-- The retraction `Oₑ ⟶ O₀` is a retraction of the zero section `O₀ ⟶ Oₑ`. -/
theorem zeroSec_retr : zeroSec R ≫ retr R = 𝟙 _ :=
  ext_toScheme ((specMap_comp_eq_id _ _ rfl).trans
    ((BigFppfOver.toScheme B S hS).map_id (O₀ R)).symm)

/-- Multiplication by a scalar on `Oₑ` fixes the zero section. -/
theorem zeroSec_smul (a : Q D.C R.R) : zeroSec R ≫ smulHom R a = zeroSec R :=
  ext_toScheme (specMap_ofHom_comp (fstE_comp_smulE _ _ a))

/-- Multiplication by a scalar on `Oₑ` commutes with the retraction `Oₑ ⟶ O₀`. -/
theorem smul_retr (a : Q D.C R.R) : smulHom R a ≫ retr R = retr R :=
  ext_toScheme (specMap_ofHom_comp (smulE_comp_inlE _ _ a))

end AlgebraicGeometry.Space.SmoothLift
