module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Artin.FormalObject
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.Deformation.FormalObject.Basic

/-!
# The predeformation formal object of a formal object

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category over the big fppf site of a locally Noetherian
scheme and let `ξ = (R, ξ_n, f_n)` be a formal object of `p`: a Noetherian complete local
ring `R` over `S` together with objects `ξ_n` of `𝒳` over the infinitesimal thickenings
`Spec (R / 𝔪 ^ (n + 1))` of the closed point and transitions between them. Put
`k = R / 𝔪` and `x₀ = ξ_0`, and fix a ring `Λ` through which the structure morphism
`Spec R ⟶ S` factors.

Then `ξ` is the same data as a formal object of the predeformation category `𝓕_{𝒳,k,x₀}`
over `𝒞_Λ`. The level `n` of the predeformation formal object is the deformation `x₀ ⟶ ξ_n`
over `R / 𝔪 ^ (n + 1)` whose arrow is the composite `ξ_0 ⟶ ξ_1 ⟶ ⋯ ⟶ ξ_n`, and its
transitions are the arrows `f_n` of `ξ` read backwards.

## Main definitions

* `Deformation.Artin.FormalObject.closedPointArrow` is the composite arrow from the closed
  fibre of a formal object to a given infinitesimal level.
* `Deformation.Artin.FormalObject.completeLocalBase` regards the complete local base of a
  formal object as an object of `\widehat{𝒞}_Λ` for a chosen `Λ`.
* `Deformation.Artin.FormalObject.predeformationLevel` and
  `Deformation.Artin.FormalObject.predeformationTransition` are the levels and transitions
  of the resulting formal object of the predeformation category.

## Main results

* `Deformation.Artin.FormalObject.exists_predeformationFormalObject`: a formal object gives a
  formal object of the predeformation category of its closed fibre, with the same levels,
  transition maps and complete local base.

## References

* [Stacks Project, Tag 0CXH](https://stacks.math.columbia.edu/tag/0CXH)
-/

@[expose] public noncomputable section

namespace Deformation.Artin

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u v w

/-! ### Quotients of a ring over a base scheme -/

section Quotients

variable {S : Scheme.{u}}

/-- Over a base scheme, the structure morphism of `Spec (R / I)` coming from a chosen
`Λ`-algebra structure is the quotient map followed by the structure morphism of
`Spec R`. -/
theorem spec_algebraMap_quotient_comp (R : Type u) [CommRing R]
    (Λ : Type u) [CommRing Λ] [Algebra Λ R] (I : Ideal R)
    (iΛ : Spec (.of Λ) ⟶ S) (toS : Spec (.of R) ⟶ S)
    (hΛ : Spec.map (CommRingCat.ofHom (algebraMap Λ R)) ≫ iΛ = toS) :
    Spec.map (CommRingCat.ofHom (algebraMap Λ (R ⧸ I))) ≫ iΛ
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ toS := by
  rw [← hΛ, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- Equal ideals give the same object of `Over S`, through the quotient's canonical
`Λ`-algebra structure. -/
theorem overMk_quotient_congr (R : Type u) [CommRing R]
    (Λ : Type u) [CommRing Λ] [Algebra Λ R] {I J : Ideal R} (h : I = J)
    (iΛ : Spec (.of Λ) ⟶ S) :
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ (R ⧸ I))) ≫ iΛ) : Over S)
      = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ (R ⧸ J))) ≫ iΛ) := by
  subst h; rfl

end Quotients

/-- A morphism lifts any arrow of the base that its image is equal to. -/
theorem isHomLift_of_map_eq {𝒜 : Type*} [Category 𝒜] {ℬ : Type*} [Category ℬ]
    (P : ℬ ⥤ 𝒜) {a b : ℬ} (φ : a ⟶ b) {f : P.obj a ⟶ P.obj b} (hf : P.map φ = f) :
    P.IsHomLift f φ := hf ▸ .map φ

/-- The spectrum of a composite of ring maps, written through `CommRingCat.ofHom`, is the
composite of the spectra in the opposite order. -/
theorem specMap_ofHom_comp {A C D : Type u} [CommRing A] [CommRing C] [CommRing D]
    (f : A →+* C) (g : C →+* D) :
    Spec.map (CommRingCat.ofHom (g.comp f))
      = Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

/-- The identification of `Spec (R / I)` with `Spec (R / J)` coming from `I = J` is the
spectrum of any ring map between the quotients that respects the quotient maps. -/
theorem eqToHom_spec_quotient {R : Type u} [CommRing R] {I J : Ideal R} (h : I = J)
    (θ : R ⧸ I →+* R ⧸ J)
    (hθ : ∀ r : R, θ (Ideal.Quotient.mk I r) = Ideal.Quotient.mk J r)
    (e : Spec (CommRingCat.of (R ⧸ J)) = Spec (CommRingCat.of (R ⧸ I))) :
    eqToHom e = Spec.map (CommRingCat.ofHom θ) := by
  subst h
  have hθ' : θ = RingHom.id _ :=
    Ideal.Quotient.ringHom_ext (RingHom.ext fun r ↦ hθ r)
  rw [hθ', CommRingCat.ofHom_id, Spec.map_id]
  rfl

/-! ### Truncations of a complete local algebra -/

section Truncation

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The residue map of the `n`-th adic truncation of `A` sends the class of `r` to the
class of `r` in `k`. -/
theorem residueMap_obj_mk (A : CompleteLocalAlgCat.{u, u, u} Λ k) (n : ℕ) (r : A) :
    residueMap (AdicTruncation.obj A n)
        (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1)) r)
      = A.residueEquiv (residue A r) :=
  AdicTruncation.residueEquiv_residue_mk A n r

/-- The transition of adic truncations is the quotient map on classes. -/
theorem transition_hom_mk (A : CompleteLocalAlgCat.{u, u, u} Λ k) (n : ℕ) (r : A) :
    (AdicTruncation.transition A n).hom
        (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1 + 1)) r)
      = Ideal.Quotient.mk (maximalIdeal A ^ (n + 1)) r := rfl

end Truncation

/-! ### The data attached to a formal object -/

section

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : Type v} [Category.{w} F] {p : F ⥤ BigFppfOver B S hS}

/-- The canonical arrow from the closed fibre of a formal object to its `n`-th
infinitesimal level, the composite of the first `n` transition maps. -/
def FormalObject.closedPointArrow (ξ : FormalObject B S hS p) :
    (n : ℕ) → ξ.level 0 ⟶ ξ.level n
  | 0 => 𝟙 _
  | n + 1 => FormalObject.closedPointArrow ξ n ≫ ξ.transition n

/-- The complete local base of a formal object, as an object of `\widehat{𝒞}_Λ` over a
chosen ring `Λ` with its canonical residue-field identification. -/
def FormalObject.completeLocalBase (ξ : FormalObject B S hS p)
    (Λ : Type u) [CommRing Λ] [Algebra Λ ξ.base.R] :
    CompleteLocalAlgCat.{u, u, u} Λ (ResidueField ξ.base.R) where
  carrier := ξ.base.R
  completeLocal := ⟨ξ.base.noetherian, ξ.base.localRing, ξ.base.complete⟩
  residueEquiv := AlgEquiv.refl

variable (ξ : FormalObject B S hS p)

/-- The level `n` of a formal object, as an object over `S`, is the `n`-th infinitesimal
thickening of its base. -/
theorem FormalObject.truncBase (n : ℕ) :
    (p ⋙ Over.post B.inclusion).obj (ξ.level n)
      = (Over.post B.inclusion).obj (truncationOver B S hS ξ.base ξ.contains n) :=
  congrArg (Over.post B.inclusion).obj (ξ.level_eq n)

/-- The transition map of a formal object lies over the canonical closed immersion of
infinitesimal thickenings. -/
theorem FormalObject.transitionLeft (n : ℕ) :
    eqToHom (congrArg Over.left (ξ.truncBase n)).symm ≫
        ((p ⋙ Over.post B.inclusion).map (ξ.transition n)).left ≫
        eqToHom (congrArg Over.left (ξ.truncBase (n + 1)))
      = adicThickeningSucc ξ.base.R (maximalIdeal ξ.base.R) n := by
  have hl := ξ.transition_lift n
  have hfac := CategoryTheory.IsHomLift.fac' p
    (truncationOverSucc B S hS ξ.base ξ.contains n) (ξ.transition n)
  rw [Functor.comp_map, hfac]
  simp only [Functor.map_comp, eqToHom_map, Over.comp_left, Over.eqToHom_left,
    Category.assoc, eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    Category.comp_id]
  rfl

/-- The composite arrow from the closed fibre to level `n` lies over the canonical
projection `R / 𝔪 ^ (n + 1) → R / 𝔪 ^ 1`: it agrees with the spectrum of any ring map
between those quotients respecting the quotient maps. -/
theorem FormalObject.closedPointArrowLeft (n : ℕ)
    (ψ : (ξ.base.R ⧸ maximalIdeal ξ.base.R ^ (n + 1)) →+*
      (ξ.base.R ⧸ maximalIdeal ξ.base.R ^ 1))
    (hψ : ∀ r : ξ.base.R, ψ (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ r) :
    eqToHom (congrArg Over.left (ξ.truncBase 0)).symm ≫
        ((p ⋙ Over.post B.inclusion).map (FormalObject.closedPointArrow ξ n)).left ≫
        eqToHom (congrArg Over.left (ξ.truncBase n))
      = Spec.map (CommRingCat.ofHom ψ) := by
  induction n with
  | zero =>
      have h0 : (p ⋙ Over.post B.inclusion).map (FormalObject.closedPointArrow ξ 0)
          = 𝟙 _ :=
        CategoryTheory.Functor.map_id (p ⋙ Over.post B.inclusion) (ξ.level 0)
      rw [h0, Over.id_left, Category.id_comp, eqToHom_trans]
      exact eqToHom_spec_quotient rfl ψ hψ _
  | succ n ih =>
      have hsplit : FormalObject.closedPointArrow ξ (n + 1)
          = FormalObject.closedPointArrow ξ n ≫ ξ.transition n := rfl
      have hcancel :
          eqToHom (congrArg Over.left (ξ.truncBase 0)).symm ≫
            (((p ⋙ Over.post B.inclusion).map (FormalObject.closedPointArrow ξ n)).left ≫
              ((p ⋙ Over.post B.inclusion).map (ξ.transition n)).left) ≫
            eqToHom (congrArg Over.left (ξ.truncBase (n + 1)))
          = (eqToHom (congrArg Over.left (ξ.truncBase 0)).symm ≫
              ((p ⋙ Over.post B.inclusion).map (FormalObject.closedPointArrow ξ n)).left ≫
              eqToHom (congrArg Over.left (ξ.truncBase n))) ≫
            (eqToHom (congrArg Over.left (ξ.truncBase n)).symm ≫
              ((p ⋙ Over.post B.inclusion).map (ξ.transition n)).left ≫
              eqToHom (congrArg Over.left (ξ.truncBase (n + 1)))) := by
        simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      have hcomp : ψ = (Ideal.Quotient.factorPow (maximalIdeal ξ.base.R)
            (Nat.succ_le_succ (Nat.zero_le n))).comp
          (Ideal.Quotient.factorPow (maximalIdeal ξ.base.R) (Nat.le_succ (n + 1))) :=
        Ideal.Quotient.ringHom_ext (RingHom.ext fun r ↦ by
          simpa [Ideal.Quotient.factorPow] using hψ r)
      rw [hcomp, CommRingCat.ofHom_comp, Spec.map_comp, hsplit, Functor.map_comp,
        Over.comp_left, hcancel,
        ih (Ideal.Quotient.factorPow (maximalIdeal ξ.base.R)
            (Nat.succ_le_succ (Nat.zero_le n)))
          (fun r ↦ by simp [Ideal.Quotient.factorPow]),
        ξ.transitionLeft n]
      rfl

variable (Λ : Type u) [CommRing Λ] [Algebra Λ ξ.base.R]
    (iΛ : Spec (.of Λ) ⟶ S)
    (hΛ : Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.R)) ≫ iΛ = ξ.base.toS)

include hΛ

/-- The level `n` of a formal object lies over `Spec` of the `n`-th adic truncation of its
complete local base, as an object over `S`. -/
theorem FormalObject.levelBase (n : ℕ) :
    (p ⋙ Over.post B.inclusion).obj (ξ.level n)
      = Over.mk (Spec.map (CommRingCat.ofHom
          (algebraMap Λ (AdicTruncation.obj (ξ.completeLocalBase Λ) n))) ≫ iΛ) :=
  (ξ.truncBase n).trans
    (congrArg Over.mk
      (spec_algebraMap_quotient_comp ξ.base.R Λ (maximalIdeal ξ.base.R ^ (n + 1)) iΛ
        ξ.base.toS hΛ).symm)

/-- The closed fibre of a formal object lies over `Spec` of its residue field, as an
object over `S`. -/
theorem FormalObject.basePoint :
    (p ⋙ Over.post B.inclusion).obj (ξ.level 0)
      = Over.mk (Spec.map (CommRingCat.ofHom
          (algebraMap Λ (ResidueField ξ.base.R))) ≫ iΛ) :=
  (ξ.levelBase Λ iΛ hΛ 0).trans
    (overMk_quotient_congr ξ.base.R Λ (pow_one (maximalIdeal ξ.base.R)) iΛ)

/-- The composite arrow from the closed fibre to level `n` lies over the canonical
closed-point map of the `n`-th adic truncation. -/
theorem FormalObject.arrowBase (n : ℕ) :
    eqToHom (congrArg Over.left (ξ.basePoint Λ iΛ hΛ)).symm ≫
        ((p ⋙ Over.post B.inclusion).map (FormalObject.closedPointArrow ξ n)).left ≫
        eqToHom (congrArg Over.left (ξ.levelBase Λ iΛ hΛ n))
      = Spec.map (CommRingCat.ofHom
          (residueMap (AdicTruncation.obj (ξ.completeLocalBase Λ) n))) := by
  have step1 :
      eqToHom (congrArg Over.left (ξ.basePoint Λ iΛ hΛ)).symm ≫
          eqToHom (congrArg Over.left (ξ.truncBase 0))
        = Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.factor (le_of_eq (pow_one (maximalIdeal ξ.base.R))))) := by
    rw [eqToHom_trans]
    exact eqToHom_spec_quotient (pow_one (maximalIdeal ξ.base.R)) _ (fun _ ↦ rfl) _
  have step2 := ξ.closedPointArrowLeft n
    (Ideal.Quotient.factorPow (maximalIdeal ξ.base.R) (Nat.succ_le_succ (Nat.zero_le n)))
    (fun r ↦ by simp [Ideal.Quotient.factorPow])
  have hfin : residueMap (AdicTruncation.obj (ξ.completeLocalBase Λ) n)
      = (Ideal.Quotient.factor (le_of_eq (pow_one (maximalIdeal ξ.base.R)))).comp
        (Ideal.Quotient.factorPow (maximalIdeal ξ.base.R)
          (Nat.succ_le_succ (Nat.zero_le n))) :=
    Ideal.Quotient.ringHom_ext
      (RingHom.ext fun r ↦ residueMap_obj_mk (ξ.completeLocalBase Λ) n r)
  have hsplit :
      eqToHom (congrArg Over.left (ξ.basePoint Λ iΛ hΛ)).symm ≫
          ((p ⋙ Over.post B.inclusion).map (FormalObject.closedPointArrow ξ n)).left ≫
          eqToHom (congrArg Over.left (ξ.levelBase Λ iΛ hΛ n))
        = (eqToHom (congrArg Over.left (ξ.basePoint Λ iΛ hΛ)).symm ≫
              eqToHom (congrArg Over.left (ξ.truncBase 0))) ≫
            (eqToHom (congrArg Over.left (ξ.truncBase 0)).symm ≫
              ((p ⋙ Over.post B.inclusion).map (FormalObject.closedPointArrow ξ n)).left ≫
              eqToHom (congrArg Over.left (ξ.truncBase n))) := by
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rfl
  rw [hsplit, step1, step2]
  exact (specMap_ofHom_comp _ _).symm.trans
    (congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f)) hfin).symm

/-- Level `n` of the formal object of the predeformation category: the deformation
`ξ.level 0 ⟶ ξ.level n` over the `n`-th adic truncation of the complete local base. -/
def FormalObject.predeformationLevel (n : ℕ) :
    DeformationObject iΛ (p ⋙ Over.post B.inclusion) (ξ.level 0)
      (ξ.basePoint Λ iΛ hΛ) where
  algebra := AdicTruncation.obj (ξ.completeLocalBase Λ) n
  point := ξ.level n
  arrow := FormalObject.closedPointArrow ξ n
  base := ξ.levelBase Λ iΛ hΛ n
  arrow_base := ξ.arrowBase Λ iΛ hΛ n

/-- The transition of the formal object of the predeformation category: the transition map
of `ξ`, read as a reversed arrow of deformations. -/
def FormalObject.predeformationTransition (n : ℕ) :
    DeformationMorphism iΛ (p ⋙ Over.post B.inclusion) (ξ.level 0)
      (ξ.basePoint Λ iΛ hΛ) (ξ.predeformationLevel Λ iΛ hΛ (n + 1))
      (ξ.predeformationLevel Λ iΛ hΛ n) where
  ringHom := AdicTruncation.transition (ξ.completeLocalBase Λ) n
  arrow := ξ.transition n
  triangle := rfl
  arrow_base := by
    have hring : Ideal.Quotient.factorPow (maximalIdeal ξ.base.R) (Nat.le_succ (n + 1))
        = (AdicTruncation.transition (ξ.completeLocalBase Λ) n).hom.toRingHom :=
      Ideal.Quotient.ringHom_ext (RingHom.ext fun _ ↦ rfl)
    exact (ξ.transitionLeft n).trans
      (congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f)) hring)

end

/-! ### The predeformation formal object -/

section

variable {Λ : Type u}

/-- A formal object of a category over the big fppf site of `S` gives a formal object of
the predeformation category of its closed fibre, with the same levels, the same transition
maps and the same complete local base. -/
@[stacks 0CXH]
theorem FormalObject.exists_predeformationFormalObject
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : Type v} [Category.{w} F]
    (p : F ⥤ BigFppfOver B S hS)
    (ξ : FormalObject B S hS p)
    (Λ : Type u) [CommRing Λ] [Algebra Λ ξ.base.R]
    (iΛ : Spec (.of Λ) ⟶ S)
    (hR : Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.R)) ≫ iΛ =
      ξ.base.toS) :
    let R := ξ.base.R
    letI : CommRing R := ξ.base.commRing
    letI : IsLocalRing R := ξ.base.localRing
    let k := ResidueField R
    letI : Field k := ResidueField.field R
    letI : Algebra Λ k := ResidueField.algebra R
    let q : F ⥤ Over S := p ⋙ Over.post B.inclusion
    ∃ hx₀ : q.obj (ξ.level 0) = Over.mk
        (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ),
      let C := predeformationCategory iΛ q (ξ.level 0) hx₀
      letI : Category C.carrier := C.category
      ∃ η : Deformation.FormalObject C.projection,
        η.base = ξ.completeLocalBase Λ ∧
          (∀ n, (C.objects (η.level n)).point = ξ.level n) ∧
          (∀ n, HEq (C.objects (η.level n)).arrow
            (FormalObject.closedPointArrow ξ n)) ∧
          (∀ n, HEq (C.morphisms (η.level (n + 1)) (η.level n)
            (η.transition n)).arrow (ξ.transition n)) := by
  dsimp only
  refine ⟨ξ.basePoint Λ iΛ hR, ?_⟩
  let : Category (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) (ξ.level 0)
      (ξ.basePoint Λ iΛ hR)).carrier :=
    (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) (ξ.level 0)
      (ξ.basePoint Λ iΛ hR)).category
  refine ⟨{ base := ξ.completeLocalBase Λ
            level := fun n ↦ ξ.predeformationLevel Λ iΛ hR n
            level_eq := fun _ ↦ rfl
            transition := fun n ↦ ξ.predeformationTransition Λ iΛ hR n
            transition_lift := fun n ↦ isHomLift_of_map_eq
              (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) (ξ.level 0)
                (ξ.basePoint Λ iΛ hR)).projection
              (ξ.predeformationTransition Λ iΛ hR n) rfl },
    rfl, fun _ ↦ rfl, fun _ ↦ HEq.rfl, fun _ ↦ HEq.rfl⟩

end

end Deformation.Artin

end
