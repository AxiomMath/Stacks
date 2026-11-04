module

public import StacksFrontier.AlgebraicGeometry.SectionRingProjQuasicoherent.Multiplication
public import StacksFrontier.AlgebraicGeometry.TwistedSectionModule.TensorPow
public import StacksFrontier.AlgebraicGeometry.TensorPowerAssoc.Basic
public import StacksFrontier.AlgebraicGeometry.SectionRingProjTheta.TwistShift

/-!
# The monoidal identities behind the twist square of Stacks Tag 01QK

Stacks Tag 01QK compares, on a scheme `X` with an ample invertible `𝓛`, the comparison
`θ_𝓕 : f^*M̃ ⟶ 𝓕` of Tag 01QJ with the multiplication `M̃ ⊗ 𝒪_Y(n) ⟶ M(n)~` of Equation 01MQ.
On a chart `X_s` the comparison `θ_𝓕` is pinned by multiplication by powers of `s`, so the square
of the Remark comes down to two identities between morphisms in the monoidal category of
`𝒪_X`-modules. They involve only the monoidal structure, the braiding, and the hypothesis that the
self-braiding of `𝓛` is trivial, so this file proves them in an arbitrary braided monoidal
category `C`. Write `A ⊙ m` for `Stacks.TwistedSections.twistPow A L m` and `L ^⊗ m` for
`Stacks.TensorPowers.natTensorPow L m`.

* **The external product.** `extProd F N i b : (F ⊙ i) ⊗ (N ⊙ b) ⟶ (F ⊗ N) ⊙ (b + i)` moves the
  `i` copies of `L` of the first factor past all of `N ⊙ b`. It is the product of a twisted
  section of `F` with a twisted section of `N`.
* **Multiplication by sections is multiplicative** (`smulRight_tensorHom_extProd`): multiplying
  `F` by `a` and `N` by `b` and then taking the external product is multiplying `F ⊗ N` by the
  product `b a` of the section ring.
* **The base change.** Given an isomorphism `β : L ^⊗ e ≅ N ⊙ k`, `baseIso F β` is the induced
  isomorphism `F ⊙ e ≅ (F ⊗ N) ⊙ k`. The identity `extProd_baseIso` says that the external product
  of a twisted section `t` of `F` with the image under `β` of a section `x` of `L ^⊗ (e + j)` is
  the image under `baseIso F β` of the module product `x · t`. This is the content of the
  "obvious identification" `M(n) = Γ_*(X, 𝓛, 𝓕 ⊗ 𝓛^{⊗ n})` the Remark uses.

## Main definitions

* `Stacks.SectionRingProjTheta.twistTensorIso`: `(F ⊗ A) ⊙ m ≅ F ⊗ (A ⊙ m)`.
* `Stacks.SectionRingProjTheta.smulRight`: multiplication by a section `a` of `L ^⊗ i`,
  `A ⟶ A ⊙ i`.
* `Stacks.SectionRingProjTheta.extProd`: the external product.
* `Stacks.SectionRingProjTheta.baseIso`: the base change of an isomorphism `L ^⊗ e ≅ N ⊙ k`.

## Main results

* `Stacks.SectionRingProjTheta.smulRight_tensorHom_extProd`.
* `Stacks.SectionRingProjTheta.extProd_baseIso`.

## References

* [Stacks Project, Tag 01QK](https://stacks.math.columbia.edu/tag/01QK)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powSections mul mulMap powAdd powCongr sectionRing)
open Stacks.TwistedSections (twistPow twistSections twistPowMap twistPowTensorIso actMap gsmul
  twistCongr)

universe v u

namespace Stacks.SectionRingProjTheta

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

section Monoidal

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow
  Stacks.TwistedSections.twistPow

variable {L : C}

/-- **`(F ⊗ A) ⊙ m ≅ F ⊗ (A ⊙ m)`**: the `m` copies of `L` whiskered onto `F ⊗ A` are
regrouped onto `A`. -/
def twistTensorIso (F A L : C) : (m : ℕ) → (twistPow (F ⊗ A) L m ≅ F ⊗ twistPow A L m)
  | 0 => Iso.refl _
  | m + 1 => whiskerRightIso (twistTensorIso F A L m) L ≪≫ α_ F (twistPow A L m) L

/-- `twistTensorIso F A L 0` is the identity of `F ⊗ A`. -/
theorem twistTensorIso_zero (F A L : C) : twistTensorIso F A L 0 = Iso.refl _ := rfl

/-- `twistTensorIso F A L (m + 1)` is `twistTensorIso F A L m` whiskered by `L`, followed by the
associator. -/
theorem twistTensorIso_succ (F A L : C) (m : ℕ) :
    twistTensorIso F A L (m + 1) =
      whiskerRightIso (twistTensorIso F A L m) L ≪≫ α_ F (twistPow A L m) L := rfl

/-- `twistTensorIso` read through the grouped forms `A ⊙ m ≅ A ⊗ L ^⊗ m`: it is the
associator. -/
theorem twistTensorIso_hom_whiskerLeft (F A L : C) : ∀ m : ℕ,
    (twistTensorIso F A L m).hom ≫ F ◁ (twistPowTensorIso A L m).hom =
      (twistPowTensorIso (F ⊗ A) L m).hom ≫ (α_ F A (natTensorPow L m)).hom
  | 0 => by
      show 𝟙 _ ≫ F ◁ (ρ_ A).inv = (ρ_ (F ⊗ A)).inv ≫ (α_ F A (𝟙_ C)).hom
      monoidal
  | m + 1 => by
      have ih := twistTensorIso_hom_whiskerLeft F A L m
      show ((twistTensorIso F A L m).hom ▷ L ≫ (α_ F (twistPow A L m) L).hom) ≫
          F ◁ ((twistPowTensorIso A L m).hom ▷ L ≫ (α_ A (natTensorPow L m) L).hom) =
        ((twistPowTensorIso (F ⊗ A) L m).hom ▷ L ≫ (α_ (F ⊗ A) (natTensorPow L m) L).hom) ≫
          (α_ F A (natTensorPow L m ⊗ L)).hom
      have ih' := congrArg (· ▷ L) ih
      simp only [comp_whiskerRight] at ih'
      calc ((twistTensorIso F A L m).hom ▷ L ≫ (α_ F (twistPow A L m) L).hom) ≫
            F ◁ ((twistPowTensorIso A L m).hom ▷ L ≫ (α_ A (natTensorPow L m) L).hom)
          = ((twistTensorIso F A L m).hom ▷ L ≫ (F ◁ (twistPowTensorIso A L m).hom) ▷ L) ≫
              (α_ F (A ⊗ natTensorPow L m) L).hom ≫ F ◁ (α_ A (natTensorPow L m) L).hom := by
            simp only [whiskerLeft_comp, Category.assoc, associator_naturality_middle_assoc]
        _ = ((twistPowTensorIso (F ⊗ A) L m).hom ▷ L ≫ (α_ F A (natTensorPow L m)).hom ▷ L) ≫
              (α_ F (A ⊗ natTensorPow L m) L).hom ≫ F ◁ (α_ A (natTensorPow L m) L).hom := by
            rw [ih']
        _ = ((twistPowTensorIso (F ⊗ A) L m).hom ▷ L ≫ (α_ (F ⊗ A) (natTensorPow L m) L).hom) ≫
              (α_ F A (natTensorPow L m ⊗ L)).hom := by
            simp only [Category.assoc]
            congr 1
            monoidal

/-- **`twistTensorIso` is natural in the second factor.** -/
theorem twistPowMap_whiskerLeft_twistTensorIso (F : C) {A A' : C} (φ : A ⟶ A') : ∀ m : ℕ,
    twistPowMap L (F ◁ φ) m ≫ (twistTensorIso F A' L m).hom =
      (twistTensorIso F A L m).hom ≫ F ◁ twistPowMap L φ m
  | 0 => by
      show F ◁ φ ≫ 𝟙 _ = 𝟙 _ ≫ F ◁ φ
      simp
  | m + 1 => by
      have ih := twistPowMap_whiskerLeft_twistTensorIso F φ m
      show twistPowMap L (F ◁ φ) m ▷ L ≫
          ((twistTensorIso F A' L m).hom ▷ L ≫ (α_ F (twistPow A' L m) L).hom) =
        ((twistTensorIso F A L m).hom ▷ L ≫ (α_ F (twistPow A L m) L).hom) ≫
          F ◁ (twistPowMap L φ m ▷ L)
      rw [← Category.assoc, ← comp_whiskerRight, ih, comp_whiskerRight, Category.assoc,
        associator_naturality_middle, Category.assoc]

/-- **Multiplication by a section `a` of `L ^⊗ i`**, as a morphism `A ⟶ A ⊙ i`: the section
tensored in on the right, read in the grouped form `A ⊗ L ^⊗ i ≅ A ⊙ i`. -/
def smulRight (A : C) {i : ℕ} (a : 𝟙_ C ⟶ natTensorPow L i) : A ⟶ twistPow A L i :=
  (ρ_ A).inv ≫ A ◁ a ≫ (twistPowTensorIso A L i).inv

/-- `Stacks.SectionRingProjQuasicoherent.twistPowAddIso` in degree `0` is the grouped form, up to
the transport `0 + i = i`. -/
theorem twistPowAddIso_zero_hom (A L : C) : ∀ i : ℕ,
    (Stacks.SectionRingProjQuasicoherent.twistPowAddIso A L 0 i).hom =
      eqToHom (congrArg (twistPow A L) (Nat.zero_add i)) ≫ (twistPowTensorIso A L i).hom
  | 0 => by
      show (ρ_ A).inv = 𝟙 _ ≫ (ρ_ A).inv
      rw [Category.id_comp]
  | i + 1 => by
      have ih := twistPowAddIso_zero_hom A L i
      show (Stacks.SectionRingProjQuasicoherent.twistPowAddIso A L 0 i).hom ▷ L ≫
          (α_ (twistPow A L 0) (natTensorPow L i) L).hom =
        eqToHom (congrArg (twistPow A L) (Nat.zero_add (i + 1))) ≫
          ((twistPowTensorIso A L i).hom ▷ L ≫ (α_ A (natTensorPow L i) L).hom)
      rw [ih]
      show (eqToHom (congrArg (twistPow A L) (Nat.zero_add i)) ≫
          (twistPowTensorIso A L i).hom) ▷ L ≫ (α_ A (natTensorPow L i) L).hom = _
      rw [comp_whiskerRight, eqToHom_whiskerRight, Category.assoc]

/-- **`twistMul` in degree `0` is `smulRight`**, up to the transport `0 + i = i`. -/
theorem twistMul_zero_eq (A : C) {i : ℕ} (a : powSections L i) :
    Stacks.SectionRingProjQuasicoherent.twistMul (F := A) a 0 ≫
        eqToHom (congrArg (twistPow A L) (Nat.zero_add i)) = smulRight A a := by
  have h : (Stacks.SectionRingProjQuasicoherent.twistPowAddIso A L 0 i).inv ≫
      eqToHom (congrArg (twistPow A L) (Nat.zero_add i)) =
        (twistPowTensorIso A L i).inv := by
    rw [Iso.inv_comp_eq, twistPowAddIso_zero_hom, Category.assoc]
    show _ = _ ≫ (twistPowTensorIso A L i).hom ≫ (twistPowTensorIso A L i).inv
    rw [Iso.hom_inv_id, Category.comp_id]
  show ((ρ_ A).inv ≫ A ◁ a ≫
      (Stacks.SectionRingProjQuasicoherent.twistPowAddIso A L 0 i).inv) ≫
    eqToHom (congrArg (twistPow A L) (Nat.zero_add i)) = _
  rw [Category.assoc, Category.assoc, h]
  rfl

end Monoidal

/-! ### The grouped forms of the action and of the shift -/

section Grouped

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow
  Stacks.TwistedSections.twistPow

variable {L : C}

/-- Reindexing a twisted object is reindexing the tensor power in the grouped form. -/
theorem eqToHom_twistPowTensorIso_hom (F : C) {a b : ℕ} (h : a = b) :
    eqToHom (congrArg (twistPow F L) h) ≫ (twistPowTensorIso F L b).hom =
      (twistPowTensorIso F L a).hom ≫ F ◁ powCongr L h := by
  subst h
  simp

/-- **The action of a twisted section on a tensor power, in the grouped form**: tensor the section
in on the left and add the powers. -/
theorem actMap_twistPowTensorIso_hom {F : C} {i : ℕ} (t : twistSections F L i) : ∀ p : ℕ,
    actMap t p ≫ (twistPowTensorIso F L (i + p)).hom =
      (λ_ (natTensorPow L p)).inv ≫ (t ≫ (twistPowTensorIso F L i).hom) ▷ natTensorPow L p ≫
        (α_ F (natTensorPow L i) (natTensorPow L p)).hom ≫ F ◁ powAdd L i p
  | 0 => by
      show t ≫ (twistPowTensorIso F L i).hom =
        (λ_ (𝟙_ C)).inv ≫ (t ≫ (twistPowTensorIso F L i).hom) ▷ 𝟙_ C ≫
          (α_ F (natTensorPow L i) (𝟙_ C)).hom ≫ F ◁ (ρ_ (natTensorPow L i)).hom
      monoidal
  | p + 1 => by
      have ih := actMap_twistPowTensorIso_hom t p
      show actMap t p ▷ L ≫ ((twistPowTensorIso F L (i + p)).hom ▷ L ≫
          (α_ F (natTensorPow L (i + p)) L).hom) =
        (λ_ (natTensorPow L p ⊗ L)).inv ≫
          (t ≫ (twistPowTensorIso F L i).hom) ▷ (natTensorPow L p ⊗ L) ≫
            (α_ F (natTensorPow L i) (natTensorPow L p ⊗ L)).hom ≫
              F ◁ ((α_ (natTensorPow L i) (natTensorPow L p) L).inv ≫ powAdd L i p ▷ L)
      rw [← Category.assoc, ← comp_whiskerRight, ih]
      monoidal

/-- **`L ^⊗ n ⊙ j` is `L ^⊗ (n + j)`**: both recurse by tensoring with `L` on the right. -/
theorem twistPow_natTensorPow (L : C) (n : ℕ) : ∀ j : ℕ,
    twistPow (natTensorPow L n) L j = natTensorPow L (n + j)
  | 0 => rfl
  | j + 1 => congrArg (· ⊗ L) (twistPow_natTensorPow L n j)

/-- The grouped form of `L ^⊗ n ⊙ j`, followed by the addition, is the identification
`twistPow_natTensorPow`. -/
theorem twistPowTensorIso_hom_powAdd (L : C) (n : ℕ) : ∀ j : ℕ,
    (twistPowTensorIso (natTensorPow L n) L j).hom ≫ powAdd L n j =
      eqToHom (twistPow_natTensorPow L n j)
  | 0 => by
      show (ρ_ (natTensorPow L n)).inv ≫ (ρ_ (natTensorPow L n)).hom = eqToHom rfl
      simp
  | j + 1 => by
      have ih := twistPowTensorIso_hom_powAdd L n j
      show ((twistPowTensorIso (natTensorPow L n) L j).hom ▷ L ≫
          (α_ (natTensorPow L n) (natTensorPow L j) L).hom) ≫
        ((α_ (natTensorPow L n) (natTensorPow L j) L).inv ≫ powAdd L n j ▷ L) = _
      rw [Category.assoc, Iso.hom_inv_id_assoc, ← comp_whiskerRight, ih, eqToHom_whiskerRight]

/-- **The shift `(F ⊙ n) ⊙ q = F ⊙ (n + q)`, in the grouped forms**: it is the associator
followed by the addition of the powers. -/
theorem twistPowTensorIso_twistPow (F L : C) (n : ℕ) : ∀ q : ℕ,
    eqToHom (Stacks.SectionRingProjTheta.twistPow_twistPow F L n q).symm ≫
        twistPowMap L (twistPowTensorIso F L n).hom q ≫
          (twistPowTensorIso (F ⊗ natTensorPow L n) L q).hom ≫
            (α_ F (natTensorPow L n) (natTensorPow L q)).hom ≫ F ◁ powAdd L n q =
      (twistPowTensorIso F L (n + q)).hom
  | 0 => by
      show 𝟙 _ ≫ (twistPowTensorIso F L n).hom ≫ (ρ_ (F ⊗ natTensorPow L n)).inv ≫
          (α_ F (natTensorPow L n) (𝟙_ C)).hom ≫ F ◁ (ρ_ (natTensorPow L n)).hom =
        (twistPowTensorIso F L n).hom
      simp
  | q + 1 => by
      have ih := twistPowTensorIso_twistPow F L n q
      have he : eqToHom (Stacks.SectionRingProjTheta.twistPow_twistPow F L n (q + 1)).symm =
          eqToHom (Stacks.SectionRingProjTheta.twistPow_twistPow F L n q).symm ▷ L := by
        rw [eqToHom_whiskerRight]
      rw [he]
      show eqToHom (Stacks.SectionRingProjTheta.twistPow_twistPow F L n q).symm ▷ L ≫
          twistPowMap L (twistPowTensorIso F L n).hom q ▷ L ≫
            ((twistPowTensorIso (F ⊗ natTensorPow L n) L q).hom ▷ L ≫
              (α_ (F ⊗ natTensorPow L n) (natTensorPow L q) L).hom) ≫
            (α_ F (natTensorPow L n) (natTensorPow L q ⊗ L)).hom ≫
              F ◁ ((α_ (natTensorPow L n) (natTensorPow L q) L).inv ≫ powAdd L n q ▷ L) =
        (twistPowTensorIso F L (n + q)).hom ▷ L ≫ (α_ F (natTensorPow L (n + q)) L).hom
      rw [← ih]
      monoidal

/-- `twistPowTensorIso_twistPow` in the direction the external product meets it. -/
theorem twistPowMap_inv_twistPow (F L : C) (n q : ℕ) :
    twistPowMap L (twistPowTensorIso F L n).inv q ≫
        eqToHom (Stacks.SectionRingProjTheta.twistPow_twistPow F L n q) ≫
          (twistPowTensorIso F L (n + q)).hom =
      (twistPowTensorIso (F ⊗ natTensorPow L n) L q).hom ≫
        (α_ F (natTensorPow L n) (natTensorPow L q)).hom ≫ F ◁ powAdd L n q := by
  rw [← twistPowTensorIso_twistPow F L n q, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, ← Category.assoc, ← Stacks.TwistedSections.twistPowMap_comp,
    Iso.inv_hom_id, Stacks.TwistedSections.twistPowMap_id, Category.id_comp]


/-- **Multiplication by a section is natural in the object multiplied.** -/
theorem smulRight_twistPowMap {A A' : C} (φ : A ⟶ A') {i : ℕ} (a : 𝟙_ C ⟶ natTensorPow L i) :
    smulRight A a ≫ twistPowMap L φ i = φ ≫ smulRight A' a := by
  have hn := Stacks.TwistedSections.twistPowTensorIso_hom_naturality L φ i
  have hinv : (twistPowTensorIso A L i).inv ≫ twistPowMap L φ i =
      φ ▷ natTensorPow L i ≫ (twistPowTensorIso A' L i).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hn, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [smulRight, smulRight, Category.assoc, Category.assoc, hinv, whisker_exchange_assoc,
    rightUnitor_inv_naturality_assoc]

/-- `twistPowTensorIso_twistPow`, solved for the shift. -/
@[reassoc]
theorem eqToHom_twistPow_twistPow_hom (F L : C) (n q : ℕ) :
    eqToHom (Stacks.SectionRingProjTheta.twistPow_twistPow F L n q) ≫
        (twistPowTensorIso F L (n + q)).hom =
      (twistPowTensorIso (twistPow F L n) L q).hom ≫ (twistPowTensorIso F L n).hom ▷
        natTensorPow L q ≫ (α_ F (natTensorPow L n) (natTensorPow L q)).hom ≫
          F ◁ powAdd L n q := by
  rw [← twistPowTensorIso_twistPow F L n q, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, ← Category.assoc, Stacks.TwistedSections.twistPowTensorIso_hom_naturality,
    Category.assoc]

/-- `twistTensorIso_hom_whiskerLeft`, solved for the inverse. -/
theorem twistTensorIso_inv_twistPowTensorIso_hom (F A L : C) (m : ℕ) :
    (twistTensorIso F A L m).inv ≫ (twistPowTensorIso (F ⊗ A) L m).hom =
      F ◁ (twistPowTensorIso A L m).hom ≫ (α_ F A (natTensorPow L m)).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, twistTensorIso_hom_whiskerLeft, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- The naturality of the grouped form, through an inverse. -/
@[reassoc]
theorem twistPowMap_twistPowTensorIso_hom {A A' : C} (φ : A ⟶ A') (m : ℕ) :
    twistPowMap L φ m ≫ (twistPowTensorIso A' L m).hom =
      (twistPowTensorIso A L m).hom ≫ φ ▷ natTensorPow L m :=
  Stacks.TwistedSections.twistPowTensorIso_hom_naturality L φ m

end Grouped

/-! ### Reindexing the addition morphisms -/

section Reindex

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

variable (L : C)

/-- Reindexing the second factor commutes with `powAdd L a b : L ^⊗ a ⊗ L ^⊗ b ⟶ L ^⊗ (a + b)`. -/
@[reassoc]
theorem whiskerLeft_powCongr_powAdd (a : ℕ) {b b' : ℕ} (h : b = b') :
    natTensorPow L a ◁ powCongr L h ≫ powAdd L a b' =
      powAdd L a b ≫ powCongr L (congrArg (a + ·) h) := by
  subst h
  simp

/-- Reindexing the first factor commutes with `powAdd L a b : L ^⊗ a ⊗ L ^⊗ b ⟶ L ^⊗ (a + b)`. -/
@[reassoc]
theorem powCongr_whiskerRight_powAdd {a a' : ℕ} (h : a = a') (b : ℕ) :
    powCongr L h ▷ natTensorPow L b ≫ powAdd L a' b =
      powAdd L a b ≫ powCongr L (congrArg (· + b) h) := by
  subst h
  simp

end Reindex

section Braided

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow
  Stacks.TwistedSections.twistPow

variable [BraidedCategory C] {L : C}

/-- **The external product** `(F ⊙ i) ⊗ (N ⊙ b) ⟶ (F ⊗ N) ⊙ (b + i)`: in the grouped forms, the
`i` copies of `L` of the first factor are braided past `N ⊗ L ^⊗ b` and then added to the `b`
copies of the second. -/
def extProd (F N : C) (i b : ℕ) :
    twistPow F L i ⊗ twistPow N L b ⟶ twistPow (F ⊗ N) L (b + i) :=
  ((twistPowTensorIso F L i).hom ⊗ₘ (twistPowTensorIso N L b).hom) ≫
    (α_ F (natTensorPow L i) (N ⊗ natTensorPow L b)).hom ≫
      F ◁ ((β_ (natTensorPow L i) (N ⊗ natTensorPow L b)).hom ≫
        (α_ N (natTensorPow L b) (natTensorPow L i)).hom ≫ N ◁ powAdd L b i) ≫
      (α_ F N (natTensorPow L (b + i))).inv ≫ (twistPowTensorIso (F ⊗ N) L (b + i)).inv

/-- **Multiplication by sections is multiplicative for the external product**: multiplying `F` by
`a` and `N` by `b` and taking the external product is multiplying `F ⊗ N` by `b a`. -/
theorem smulRight_tensorHom_extProd (F N : C) {i j : ℕ} (a : powSections L i)
    (b : powSections L j) :
    (smulRight F a ⊗ₘ smulRight N b) ≫ extProd F N i j = smulRight (F ⊗ N) (mul b a) := by
  rw [smulRight, smulRight, smulRight, extProd, Stacks.GradedSections.mul_eq,
    tensorHom_comp_tensorHom_assoc, Category.assoc, Category.assoc, Category.assoc,
    Category.assoc, Iso.inv_hom_id, Iso.inv_hom_id, Category.comp_id, Category.comp_id]
  simp only [← Category.assoc]
  congr 1
  simp only [Category.assoc]
  have h2 : ((F ◁ a) ⊗ₘ (N ◁ b)) ≫ (α_ F (natTensorPow L i) (N ⊗ natTensorPow L j)).hom =
      (α_ F (𝟙_ C) (N ⊗ 𝟙_ C)).hom ≫ F ◁ (a ⊗ₘ (N ◁ b)) := by
    have := associator_naturality (𝟙 F) a (N ◁ b)
    rwa [id_tensorHom, id_tensorHom] at this
  have h3 : (a ⊗ₘ (N ◁ b)) ≫ (β_ (natTensorPow L i) (N ⊗ natTensorPow L j)).hom ≫
        (α_ N (natTensorPow L j) (natTensorPow L i)).hom =
      (β_ (𝟙_ C) (N ⊗ 𝟙_ C)).hom ≫ (α_ N (𝟙_ C) (𝟙_ C)).hom ≫ N ◁ (b ⊗ₘ a) := by
    have := associator_naturality (𝟙 N) b a
    rw [id_tensorHom, id_tensorHom] at this
    rw [BraidedCategory.braiding_naturality_assoc, this]
  rw [← tensorHom_comp_tensorHom, Category.assoc, reassoc_of% h2, ← whiskerLeft_comp_assoc,
    reassoc_of% h3, braiding_tensorUnit_left]
  monoidal

/-- **The external product with a section of a tensor power is the module action**, through the
identification `L ^⊗ n ⊙ j = L ^⊗ (n + j)` on the second factor and
`(F ⊗ L ^⊗ n) ⊙ (j + i) ≅ (F ⊙ n) ⊙ (j + i) = F ⊙ (n + (j + i))` on the target. This is the
"obvious identification" `M(n) = Γ_*(X, 𝓛, 𝓕 ⊗ 𝓛^{⊗ n})` of Stacks Tag 01QK, read on the
product of a twisted section `m` of `F` with a section `x` of the section ring. -/
theorem extProd_gsmul [Stacks.GradedSections.HasTrivialSelfBraiding L] (F : C) {n i j : ℕ}
    (m : twistSections F L i) (x : powSections L (n + j)) :
    (λ_ (𝟙_ C)).inv ≫ (m ⊗ₘ (x ≫ eqToHom (twistPow_natTensorPow L n j).symm)) ≫
        extProd F (natTensorPow L n) i j ≫
          twistPowMap L (twistPowTensorIso F L n).inv (j + i) ≫
            eqToHom (Stacks.SectionRingProjTheta.twistPow_twistPow F L n (j + i)) =
      gsmul x m ≫ eqToHom (congrArg (twistPow F L) (by omega : n + j + i = n + (j + i))) := by
  rw [← cancel_mono (twistPowTensorIso F L (n + (j + i))).hom]
  simp only [Category.assoc]
  rw [twistPowMap_inv_twistPow, extProd]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  -- the second factor, read in the grouped form, is `x` followed by the inverse of the addition
  have hkey : (eqToHom (twistPow_natTensorPow L n j).symm ≫
        (twistPowTensorIso (natTensorPow L n) L j).hom) ▷ natTensorPow L i ≫
        (α_ (natTensorPow L n) (natTensorPow L j) (natTensorPow L i)).hom ≫
          natTensorPow L n ◁ powAdd L j i ≫ powAdd L n (j + i) =
      powAdd L (n + j) i ≫ powCongr L (Nat.add_assoc n j i) := by
    have ha := Stacks.GradedSections.powAdd_assoc L n j i
    have hT := twistPowTensorIso_hom_powAdd L n j
    have ha' : (α_ (natTensorPow L n) (natTensorPow L j) (natTensorPow L i)).hom ≫
        natTensorPow L n ◁ powAdd L j i ≫ powAdd L n (j + i) =
          powAdd L n j ▷ natTensorPow L i ≫ powAdd L (n + j) i ≫
            powCongr L (Nat.add_assoc n j i) := by
      rw [reassoc_of% ha]
      simp
    rw [ha', ← comp_whiskerRight_assoc, Category.assoc, hT, eqToHom_trans, eqToHom_refl,
      id_whiskerRight, Category.id_comp]
  have hsplit : (m ⊗ₘ (x ≫ eqToHom (twistPow_natTensorPow L n j).symm)) ≫
      ((twistPowTensorIso F L i).hom ⊗ₘ (twistPowTensorIso (natTensorPow L n) L j).hom) =
        ((m ≫ (twistPowTensorIso F L i).hom) ⊗ₘ x) ≫ (F ⊗ natTensorPow L i) ◁
          (eqToHom (twistPow_natTensorPow L n j).symm ≫
            (twistPowTensorIso (natTensorPow L n) L j).hom) := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, Category.comp_id,
      Category.assoc]
  rw [reassoc_of% hsplit, associator_naturality_right_assoc, ← whiskerLeft_comp_assoc,
    ← whiskerLeft_comp]
  simp only [Category.assoc]
  have hb := Stacks.GradedSections.braiding_comp_powAdd L i (n + j)
  rw [BraidedCategory.braiding_naturality_right_assoc, hkey, reassoc_of% hb]
  rw [Stacks.TwistedSections.gsmul_def, twistCongr, Category.assoc, eqToHom_trans_assoc,
    eqToHom_twistPowTensorIso_hom, Category.assoc, ← Category.assoc (actMap m (n + j)),
    actMap_twistPowTensorIso_hom]
  · simp only [Category.assoc]
    rw [reassoc_of% (Stacks.GradedSections.comp_leftUnitor_inv x), tensorHom_def']
    simp only [Category.assoc, whiskerLeft_comp, eqToHom_trans]
  · omega

/-- **The external product is natural in the second factor.** -/
theorem whiskerLeft_twistPowMap_extProd (F : C) {B B' : C} (φ : B ⟶ B') (i j : ℕ) :
    (twistPow F L i ◁ twistPowMap L φ j) ≫ extProd F B' i j =
      extProd F B i j ≫ twistPowMap L (F ◁ φ) (j + i) := by
  rw [← cancel_mono (twistPowTensorIso (F ⊗ B') L (j + i)).hom]
  simp only [extProd, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [Stacks.TwistedSections.twistPowTensorIso_hom_naturality, Iso.inv_hom_id_assoc]
  have h1 : (twistPow F L i ◁ twistPowMap L φ j) ≫
      ((twistPowTensorIso F L i).hom ⊗ₘ (twistPowTensorIso B' L j).hom) =
        ((twistPowTensorIso F L i).hom ⊗ₘ (twistPowTensorIso B L j).hom) ≫
          (F ⊗ natTensorPow L i) ◁ (φ ▷ natTensorPow L j) := by
    rw [← id_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
      Stacks.TwistedSections.twistPowTensorIso_hom_naturality, Category.id_comp,
      Category.comp_id]
  rw [reassoc_of% h1, associator_naturality_right_assoc, ← whiskerLeft_comp_assoc,
    BraidedCategory.braiding_naturality_right_assoc]
  simp only [whiskerLeft_comp, Category.assoc]
  congr 3
  have hφ : φ ▷ natTensorPow L j ▷ natTensorPow L i ≫
      (α_ B' (natTensorPow L j) (natTensorPow L i)).hom ≫ B' ◁ powAdd L j i =
        (α_ B (natTensorPow L j) (natTensorPow L i)).hom ≫ B ◁ powAdd L j i ≫
          φ ▷ natTensorPow L (j + i) := by
    rw [associator_naturality_left_assoc, whisker_exchange]
  rw [← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc, Category.assoc, hφ]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [associator_inv_naturality_middle]





/-- **The external product is compatible with the shift `(B ⊙ k) ⊙ j = B ⊙ (k + j)` of the
second factor.** -/
theorem whiskerLeft_eqToHom_extProd (F B : C) (i k j : ℕ) :
    (twistPow F L i ◁ eqToHom (Stacks.SectionRingProjTheta.twistPow_twistPow B L k j)) ≫
        extProd F B i (k + j) =
      extProd F (twistPow B L k) i j ≫ twistPowMap L (twistTensorIso F B L k).inv (j + i) ≫
        eqToHom (Stacks.SectionRingProjTheta.twistPow_twistPow (F ⊗ B) L k (j + i)) ≫
          eqToHom (congrArg (twistPow (F ⊗ B) L) (Nat.add_assoc k j i).symm) := by
  rw [← cancel_mono (twistPowTensorIso (F ⊗ B) L (k + j + i)).hom]
  simp only [extProd, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [eqToHom_twistPowTensorIso_hom _ (Nat.add_assoc k j i).symm,
    eqToHom_twistPow_twistPow_hom_assoc,
    twistPowMap_twistPowTensorIso_hom_assoc, Iso.inv_hom_id_assoc,
    ← comp_whiskerRight_assoc, twistTensorIso_inv_twistPowTensorIso_hom]
  have h1 : (twistPow F L i ◁ eqToHom (Stacks.SectionRingProjTheta.twistPow_twistPow B L k j)) ≫
      ((twistPowTensorIso F L i).hom ⊗ₘ (twistPowTensorIso B L (k + j)).hom) =
        ((twistPowTensorIso F L i).hom ⊗ₘ (twistPowTensorIso (twistPow B L k) L j).hom) ≫
          (F ⊗ natTensorPow L i) ◁ ((twistPowTensorIso B L k).hom ▷ natTensorPow L j ≫
            (α_ B (natTensorPow L k) (natTensorPow L j)).hom ≫ B ◁ powAdd L k j) := by
    rw [← id_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
      eqToHom_twistPow_twistPow_hom, Category.id_comp, Category.comp_id]
  rw [reassoc_of% h1]
  congr 1
  rw [associator_naturality_right_assoc, ← whiskerLeft_comp_assoc,
    BraidedCategory.braiding_naturality_right_assoc]
  congr 1
  have ha : powAdd L k j ▷ natTensorPow L i ≫ powAdd L (k + j) i =
      (α_ (natTensorPow L k) (natTensorPow L j) (natTensorPow L i)).hom ≫
        natTensorPow L k ◁ powAdd L j i ≫ powAdd L k (j + i) ≫
          powCongr L (Nat.add_assoc k j i).symm := Stacks.GradedSections.powAdd_assoc L k j i
  simp only [comp_whiskerRight, Category.assoc]
  rw [associator_naturality_middle_assoc, ← whiskerLeft_comp, ha]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc]
  monoidal

/-- **The base change of an isomorphism `β : L ^⊗ e ≅ N ⊙ k`**: `F ⊙ e ≅ F ⊗ L ^⊗ e ≅
F ⊗ (N ⊙ k) ≅ (F ⊗ N) ⊙ k`. -/
def baseIso (F : C) {N : C} {e k : ℕ} (β : natTensorPow L e ≅ twistPow N L k) :
    twistPow F L e ≅ twistPow (F ⊗ N) L k :=
  twistPowTensorIso F L e ≪≫ whiskerLeftIso F β ≪≫ (twistTensorIso F N L k).symm

/-- **The external product against the base change.** For `β : L ^⊗ e ≅ N ⊙ k`, a twisted section
`t` of `F` of degree `i` and a section `x` of `L ^⊗ (e + j)`, the external product of `t` with
the image of `x` under `β` is the image of the module product `x · t` under the base change
`baseIso F β`. -/
theorem extProd_baseIso [Stacks.GradedSections.HasTrivialSelfBraiding L] (F N : C) {e k : ℕ}
    (β : natTensorPow L e ≅ twistPow N L k) {i j : ℕ} (t : twistSections F L i)
    (x : powSections L (e + j)) :
    (λ_ (𝟙_ C)).inv ≫ (t ⊗ₘ (x ≫ eqToHom (twistPow_natTensorPow L e j).symm ≫
        twistPowMap L β.hom j ≫ eqToHom (Stacks.SectionRingProjTheta.twistPow_twistPow N L k j))) ≫
          extProd F N i (k + j) =
      gsmul x t ≫ eqToHom ((congrArg (twistPow F L) (Nat.add_assoc e j i)).trans
          (Stacks.SectionRingProjTheta.twistPow_twistPow F L e (j + i)).symm) ≫
        twistPowMap L (baseIso F β).hom (j + i) ≫
          eqToHom (Stacks.SectionRingProjTheta.twistPow_twistPow (F ⊗ N) L k (j + i)) ≫
            eqToHom (congrArg (twistPow (F ⊗ N) L) (Nat.add_assoc k j i).symm) := by
  have hg := congrArg (· ≫ eqToHom (Stacks.SectionRingProjTheta.twistPow_twistPow F L e
    (j + i)).symm ≫ twistPowMap L (twistPowTensorIso F L e).hom (j + i)) (extProd_gsmul F t x)
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    ← Stacks.TwistedSections.twistPowMap_comp, Iso.inv_hom_id,
    Stacks.TwistedSections.twistPowMap_id, Category.comp_id] at hg
  have hsplit : t ⊗ₘ (x ≫ eqToHom (twistPow_natTensorPow L e j).symm ≫
        twistPowMap L β.hom j ≫ eqToHom (Stacks.SectionRingProjTheta.twistPow_twistPow N L k j)) =
      (t ⊗ₘ (x ≫ eqToHom (twistPow_natTensorPow L e j).symm)) ≫
        (twistPow F L i ◁ twistPowMap L β.hom j) ≫
          (twistPow F L i ◁ eqToHom (Stacks.SectionRingProjTheta.twistPow_twistPow N L k j)) := by
    rw [← id_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
    simp
  rw [hsplit, Category.assoc, Category.assoc, whiskerLeft_eqToHom_extProd,
    ← Category.assoc (twistPow F L i ◁ twistPowMap L β.hom j),
    whiskerLeft_twistPowMap_extProd]
  simp only [Category.assoc]
  rw [reassoc_of% hg, baseIso]
  simp only [Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom,
    Stacks.TwistedSections.twistPowMap_comp, Category.assoc]

/-- Reindexing both factors of the external product. -/
theorem twistCongr_tensorHom_extProd (F G : C) {i i' j j' : ℕ} (hi : i = i') (hj : j = j')
    (t : twistSections F L i) (t' : twistSections G L j) :
    (twistCongr hi t ⊗ₘ twistCongr hj t') ≫ extProd F G i' j' =
      (t ⊗ₘ t') ≫ extProd F G i j ≫ eqToHom (congrArg (twistPow (F ⊗ G) L) (by omega)) := by
  subst hi; subst hj
  simp

/-- **The external product with a section of a tensor power is the module action**, in the
form the comparison of numerators uses: if `t'` is `x` read in `L ^⊗ n ⊙ j` and the shift of `z`
is `x · t`, then `z` is the external product of `t` and `t'`. -/
theorem eq_extProd_of_gsmul [Stacks.GradedSections.HasTrivialSelfBraiding L] (F : C)
    {n i j e k : ℕ} (t : twistSections F L i) (t' : twistSections (natTensorPow L n) L j)
    (x : powSections L e) (z : twistSections (F ⊗ natTensorPow L n) L k) (he : e = n + j)
    (hk : j + i = k)
    (h1 : t' ≫ eqToHom (twistPow_natTensorPow L n j) = x ≫ powCongr L he)
    (h2 : z ≫ twistPowMap L (twistPowTensorIso F L n).inv k ≫
        eqToHom (Stacks.SectionRingProjTheta.twistPow_twistPow F L n k) =
      gsmul x t ≫ eqToHom (congrArg (twistPow F L) (by omega))) :
    z = (λ_ (𝟙_ C)).inv ≫ (t ⊗ₘ t') ≫ extProd F (natTensorPow L n) i j ≫
      eqToHom (congrArg (twistPow (F ⊗ natTensorPow L n) L) hk) := by
  subst he hk
  have ht' : t' = x ≫ eqToHom (twistPow_natTensorPow L n j).symm := by
    have := congrArg (· ≫ eqToHom (twistPow_natTensorPow L n j).symm) h1
    simpa using this
  subst ht'
  have : IsIso (twistPowMap L (twistPowTensorIso F L n).inv (j + i)) :=
    ⟨⟨twistPowMap L (twistPowTensorIso F L n).hom (j + i), by
      rw [← Stacks.TwistedSections.twistPowMap_comp, Iso.inv_hom_id,
        Stacks.TwistedSections.twistPowMap_id], by
      rw [← Stacks.TwistedSections.twistPowMap_comp, Iso.hom_inv_id,
        Stacks.TwistedSections.twistPowMap_id]⟩⟩
  rw [← cancel_mono (twistPowMap L (twistPowTensorIso F L n).inv (j + i) ≫
    eqToHom (Stacks.SectionRingProjTheta.twistPow_twistPow F L n (j + i))), h2]
  simp only [eqToHom_refl, Category.comp_id, Category.assoc]
  rw [extProd_gsmul]

/-- **The numerator identity behind the twist square**, for the base change of `β`: if `π`
corresponds to `x` under `β` and `z` corresponds to `x · t` under `baseIso F β`, then the shift
of `z` is the external product of `t` and the shift of `π`. -/
theorem eq_extProd_of_baseIso [Stacks.GradedSections.HasTrivialSelfBraiding L] (F N : C)
    {e k : ℕ} (β : natTensorPow L e ≅ twistPow N L k) {i j : ℕ} (t : twistSections F L i)
    (π : twistSections (twistPow N L k) L j) (x : powSections L (e + j))
    (z : twistSections (twistPow (F ⊗ N) L k) L (j + i))
    (h1 : π ≫ twistPowMap L β.inv j ≫ eqToHom (twistPow_natTensorPow L e j) = x)
    (h2 : z ≫ twistPowMap L (baseIso F β).inv (j + i) =
      gsmul x t ≫ eqToHom ((congrArg (twistPow F L) (Nat.add_assoc e j i)).trans
        (Stacks.SectionRingProjTheta.twistPow_twistPow F L e (j + i)).symm)) :
    z ≫ eqToHom (Stacks.SectionRingProjTheta.twistPow_twistPow (F ⊗ N) L k (j + i)) ≫
        eqToHom (congrArg (twistPow (F ⊗ N) L) (Nat.add_assoc k j i).symm) =
      (λ_ (𝟙_ C)).inv ≫ (t ⊗ₘ (π ≫ eqToHom (Stacks.SectionRingProjTheta.twistPow_twistPow N L k
        j))) ≫ extProd F N i (k + j) := by
  have hπ : π = x ≫ eqToHom (twistPow_natTensorPow L e j).symm ≫ twistPowMap L β.hom j := by
    rw [← h1]
    simp [← Stacks.TwistedSections.twistPowMap_comp]
  have hz : z = gsmul x t ≫ eqToHom ((congrArg (twistPow F L) (Nat.add_assoc e j i)).trans
        (Stacks.SectionRingProjTheta.twistPow_twistPow F L e (j + i)).symm) ≫
      twistPowMap L (baseIso F β).hom (j + i) := by
    rw [← reassoc_of% h2]
    simp [← Stacks.TwistedSections.twistPowMap_comp]
  rw [hπ, hz]
  simp only [Category.assoc]
  rw [extProd_baseIso]

end Braided

/-! ### The identifications of graded modules -/

section Identification

open Stacks.TwistedSections (twistModule moduleGrading twistModuleLinearMap twistModuleHom
  twistModuleHom_of twistSectionsMap)
open Stacks.GradedModule (shiftedGrading)

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

variable [Preadditive C] [BraidedCategory C] {L : C} [(tensorRight L).Additive]
  [Stacks.GradedSections.HasTrivialSelfBraiding L]

/-- **The left leg of the identification `M(n) ~ Γ_*(X, 𝓛, 𝓕 ⊗ N)`**: undo the base change
`baseIso F β : F ⊙ e ≅ (F ⊗ N) ⊙ k`, then shift by `e`. -/
noncomputable def identLeft (F N : C) {e k : ℕ} (β : natTensorPow L e ≅ twistPow N L k) :
    twistModule (twistPow (F ⊗ N) L k) L →ₗ[sectionRing L] twistModule F L :=
  (twistShiftLinearMap F L e).comp (twistModuleLinearMap (baseIso F β).inv)

omit [BraidedCategory C] [(tensorRight L).Additive]
  [Stacks.GradedSections.HasTrivialSelfBraiding L] in
/-- Membership in a grading indexed by an integer depends only on the integer. -/
theorem mem_moduleGrading_of_eq {F : C} {i j : ℤ} (h : i = j) {x : twistModule F L}
    (hx : x ∈ moduleGrading F L i) : x ∈ moduleGrading F L j := h ▸ hx

/-- **The left leg is graded**, from the shift by `-k` to the shift by `n`, when `e = n + k`. -/
theorem identLeft_mem (F N : C) {e k : ℕ} (β : natTensorPow L e ≅ twistPow N L k) {n : ℤ}
    (he : (e : ℤ) = n + k) (i : ℤ) (x : twistModule (twistPow (F ⊗ N) L k) L)
    (hx : x ∈ shiftedGrading (moduleGrading (twistPow (F ⊗ N) L k) L) (-(k : ℤ)) i) :
    identLeft F N β x ∈ shiftedGrading (moduleGrading F L) n i := by
  have h1 := Stacks.TwistedSections.twistModuleHom_mem_moduleGrading (L := L)
    (baseIso F β).inv _ x hx
  have h2 := twistShiftLinearMap_mem (F := F) (L := L) e _ _ h1
  exact mem_moduleGrading_of_eq (by omega) h2

/-- **The right leg of the identification**: the shift by `k`. -/
theorem identRight_mem (G : C) (k : ℕ) (i : ℤ) (x : twistModule (twistPow G L k) L)
    (hx : x ∈ shiftedGrading (moduleGrading (twistPow G L k) L) (-(k : ℤ)) i) :
    twistShiftLinearMap G L k x ∈ moduleGrading G L i := by
  have h2 := twistShiftLinearMap_mem (F := G) (L := L) k _ _ hx
  exact mem_moduleGrading_of_eq (by omega) h2

/-- The shift by `k` is injective on the homogeneous elements of degree `i` of the shifted
grading. -/
theorem identRight_injective (G : C) (k : ℕ) (i : ℤ) (x : twistModule (twistPow G L k) L)
    (hx : x ∈ shiftedGrading (moduleGrading (twistPow G L k) L) (-(k : ℤ)) i)
    (h : twistShiftLinearMap G L k x = 0) : x = 0 :=
  twistShiftLinearMap_injective_of_mem k _ x hx h

/-- For `k ≤ i`, every element of degree `i` of `G` is the shift by `k` of an element of degree
`i` of the shifted grading. -/
theorem identRight_surjective (G : C) (k : ℕ) (i : ℤ) (hi : (k : ℤ) ≤ i) (y : twistModule G L)
    (hy : y ∈ moduleGrading G L i) :
    ∃ x : twistModule (twistPow G L k) L,
      x ∈ shiftedGrading (moduleGrading (twistPow G L k) L) (-(k : ℤ)) i ∧
        twistShiftLinearMap G L k x = y :=
  exists_mem_twistShiftLinearMap_eq k (i + -(k : ℤ)) (by omega) y
    (mem_moduleGrading_of_eq (by omega) hy)

omit [BraidedCategory C] [(tensorRight L).Additive]
  [Stacks.GradedSections.HasTrivialSelfBraiding L] in
/-- The induced map of an isomorphism has the induced map of the inverse as a left inverse. -/
theorem twistModuleHom_inv_hom {A B : C} (φ : A ≅ B) (x : twistModule A L) :
    twistModuleHom (L := L) φ.inv (twistModuleHom (L := L) φ.hom x) = x := by
  rw [← AddMonoidHom.comp_apply, ← Stacks.TwistedSections.twistModuleHom_comp, φ.hom_inv_id,
    Stacks.TwistedSections.twistModuleHom_id, AddMonoidHom.id_apply]

/-- If the shift of the image under `φ.inv` of a homogeneous element vanishes, so does the
element. -/
private theorem eq_zero_of_twistShiftLinearMap_inv {F B : C} {e : ℕ} (φ : twistPow F L e ≅ B)
    {j : ℤ} {x : twistModule B L} (hx : x ∈ moduleGrading B L j)
    (h : twistShiftLinearMap F L e (twistModuleHom (L := L) φ.inv x) = 0) : x = 0 := by
  have h0 := twistShiftLinearMap_injective_of_mem e _ _
    (Stacks.TwistedSections.twistModuleHom_mem_moduleGrading (L := L) φ.inv _ x hx) h
  rw [← twistModuleHom_inv_hom φ.symm x]
  change twistModuleHom (L := L) φ.hom (twistModuleHom (L := L) φ.inv x) = 0
  rw [h0, map_zero]

/-- `identLeft F N β` is injective on the homogeneous elements of degree `i` of the shifted
grading. -/
theorem identLeft_injective (F N : C) {e k : ℕ} (β : natTensorPow L e ≅ twistPow N L k) (i : ℤ)
    (x : twistModule (twistPow (F ⊗ N) L k) L)
    (hx : x ∈ shiftedGrading (moduleGrading (twistPow (F ⊗ N) L k) L) (-(k : ℤ)) i)
    (h : identLeft F N β x = 0) : x = 0 :=
  eq_zero_of_twistShiftLinearMap_inv (baseIso F β) hx h

/-- When `e = n + k` and `k ≤ i`, every element of degree `i` of the shift of `F` by `n` is the
image under `identLeft F N β` of an element of degree `i` of the shifted grading. -/
theorem identLeft_surjective (F N : C) {e k : ℕ} (β : natTensorPow L e ≅ twistPow N L k) {n : ℤ}
    (he : (e : ℤ) = n + k) (i : ℤ) (hi : (k : ℤ) ≤ i) (y : twistModule F L)
    (hy : y ∈ shiftedGrading (moduleGrading F L) n i) :
    ∃ x : twistModule (twistPow (F ⊗ N) L k) L,
      x ∈ shiftedGrading (moduleGrading (twistPow (F ⊗ N) L k) L) (-(k : ℤ)) i ∧
        identLeft F N β x = y := by
  obtain ⟨x', hx', hxy⟩ := exists_mem_twistShiftLinearMap_eq (F := F) (L := L) e
    (i + -(k : ℤ)) (by omega) y
    (mem_moduleGrading_of_eq (by omega) hy)
  refine ⟨twistModuleHom (L := L) (baseIso F β).hom x',
    Stacks.TwistedSections.twistModuleHom_mem_moduleGrading (L := L) _ _ _ hx', ?_⟩
  show twistShiftLinearMap F L e (twistModuleHom (L := L) (baseIso F β).inv
    (twistModuleHom (L := L) (baseIso F β).hom x')) = y
  rw [twistModuleHom_inv_hom, hxy]

/-- **The identification `Γ_*(X, 𝓛, 𝓕 ⊗ 𝓛^{⊗ n}) ⟶ Γ_*(X, 𝓛, 𝓕)(n)`** for `n ≥ 0`: regroup
`𝓕 ⊗ 𝓛^{⊗ n} ≅ 𝓕 ⊙ n`, then shift by `n`. -/
noncomputable def identNat (F : C) (n : ℕ) :
    twistModule (F ⊗ natTensorPow L n) L →ₗ[sectionRing L] twistModule F L :=
  (twistShiftLinearMap F L n).comp (twistModuleLinearMap (twistPowTensorIso F L n).inv)

/-- `identNat F n` sends degree `i` to degree `i` of the shift of `F` by `n`. -/
theorem identNat_mem (F : C) (n : ℕ) (i : ℤ) (x : twistModule (F ⊗ natTensorPow L n) L)
    (hx : x ∈ moduleGrading (F ⊗ natTensorPow L n) L i) :
    identNat F n x ∈ shiftedGrading (moduleGrading F L) n i :=
  twistShiftLinearMap_mem (F := F) (L := L) n _ _
    (Stacks.TwistedSections.twistModuleHom_mem_moduleGrading (L := L) _ _ x hx)

/-- `identNat F n` is injective on the homogeneous elements of each degree. -/
theorem identNat_injective (F : C) (n : ℕ) (i : ℤ) (x : twistModule (F ⊗ natTensorPow L n) L)
    (hx : x ∈ moduleGrading (F ⊗ natTensorPow L n) L i) (h : identNat F n x = 0) : x = 0 :=
  eq_zero_of_twistShiftLinearMap_inv (twistPowTensorIso F L n) hx h

/-- For `0 ≤ i`, every element of degree `i` of the shift of `F` by `n` is the image under
`identNat F n` of an element of degree `i`. -/
theorem identNat_surjective (F : C) (n : ℕ) (i : ℤ) (hi : 0 ≤ i) (y : twistModule F L)
    (hy : y ∈ shiftedGrading (moduleGrading F L) n i) :
    ∃ x : twistModule (F ⊗ natTensorPow L n) L,
      x ∈ moduleGrading (F ⊗ natTensorPow L n) L i ∧ identNat F n x = y := by
  obtain ⟨x', hx', hxy⟩ := exists_mem_twistShiftLinearMap_eq (F := F) (L := L) n i hi y hy
  refine ⟨twistModuleHom (L := L) (twistPowTensorIso F L n).hom x',
    Stacks.TwistedSections.twistModuleHom_mem_moduleGrading (L := L) _ _ _ hx', ?_⟩
  show twistShiftLinearMap F L n (twistModuleHom (L := L) (twistPowTensorIso F L n).inv
    (twistModuleHom (L := L) (twistPowTensorIso F L n).hom x')) = y
  rw [twistModuleHom_inv_hom, hxy]

end Identification

/-! ### `Γ_*(X, 𝓛, 𝓛^{⊗ n})` against the section ring -/

section Unit

open Stacks.TwistedSections (twistModule moduleGrading twistModuleHom twistModuleHom_of
  twistSectionsMap)

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow
  Stacks.TwistedSections.twistPow

/-- A twisted element in negative degree is zero. -/
private theorem eq_zero_of_mem_moduleGrading_of_neg [Preadditive C] {L F : C} {i : ℤ} (hi : i < 0)
    {x : twistModule F L} (hx : x ∈ moduleGrading F L i) : x = 0 := by
  rwa [moduleGrading_eq_bot_of_neg _ _ hi, AddSubgroup.mem_bot] at hx

variable [Preadditive C] [BraidedCategory C] {L : C} [(tensorRight L).Additive]
  [Stacks.GradedSections.HasTrivialSelfBraiding L]

omit [Preadditive C] [BraidedCategory C] [(tensorRight L).Additive]
  [Stacks.GradedSections.HasTrivialSelfBraiding L] in
/-- **The action of a twisted section of `L ^⊗ n` is multiplication in the section ring**, after
the identification `L ^⊗ n ⊙ j = L ^⊗ (n + j)`. -/
@[reassoc]
theorem actMap_eqToHom_twistPow_natTensorPow {n j : ℕ}
    (t : twistSections (natTensorPow L n) L j) : ∀ k : ℕ,
    actMap t k ≫ eqToHom (twistPow_natTensorPow L n (j + k)) =
      mulMap (t ≫ eqToHom (twistPow_natTensorPow L n j)) k ≫
        powCongr L (Nat.add_assoc n j k)
  | 0 => by simp
  | k + 1 => by
      have ih := actMap_eqToHom_twistPow_natTensorPow t k
      rw [Stacks.TwistedSections.actMap_succ, Stacks.GradedSections.mulMap_succ]
      have he : eqToHom (twistPow_natTensorPow L n (j + (k + 1))) =
          eqToHom (twistPow_natTensorPow L n (j + k)) ▷ L := by
        rw [eqToHom_whiskerRight]
      rw [he, ← comp_whiskerRight, ih, comp_whiskerRight, eqToHom_whiskerRight]

/-- The degreewise map of `unitShiftLinearMap`. -/
def unitShiftHom (L : C) (n : ℕ) : twistModule (natTensorPow L n) L →+ sectionRing L :=
  DirectSum.toAddMonoid fun j =>
    (DirectSum.of (powSections L) (n + j)).comp
      (Preadditive.rightComp _ (eqToHom (twistPow_natTensorPow L n j)))

omit [BraidedCategory C] [(tensorRight L).Additive]
  [Stacks.GradedSections.HasTrivialSelfBraiding L] in
/-- `unitShiftHom L n` sends a twisted section `t` of degree `j` to the section of `L ^⊗ (n + j)`
it names, in degree `n + j`. -/
@[simp] theorem unitShiftHom_of (n j : ℕ) (t : twistSections (natTensorPow L n) L j) :
    unitShiftHom L n (DirectSum.of (twistSections (natTensorPow L n) L) j t) =
      DirectSum.of (powSections L) (n + j) (t ≫ eqToHom (twistPow_natTensorPow L n j)) :=
  DirectSum.toAddMonoid_of _ _ _

/-- Under the identification `L ^⊗ n ⊙ j = L ^⊗ (n + j)`, the action `gsmul a t` of a section
`a` of `L ^⊗ k` is the product of `a` with the image of `t` in the section ring. -/
theorem unitShiftHom_gsmul {n j k : ℕ} (a : powSections L k)
    (t : twistSections (natTensorPow L n) L j) :
    DirectSum.of (powSections L) (n + (k + j))
        (gsmul a t ≫ eqToHom (twistPow_natTensorPow L n (k + j))) =
      DirectSum.of (powSections L) k a *
        DirectSum.of (powSections L) (n + j) (t ≫ eqToHom (twistPow_natTensorPow L n j)) := by
  rw [DirectSum.of_mul_of]
  apply DirectSum.of_eq_of_gradedMonoid_eq
  refine (Stacks.GradedSections.mk_eq (by omega : n + (k + j) = k + (n + j)) _).trans ?_
  congr 1
  have hc := Stacks.GradedSections.mul_comm'
    (t ≫ eqToHom (twistPow_natTensorPow L n j)) a
  show _ = mul a (t ≫ eqToHom (twistPow_natTensorPow L n j))
  rw [← hc, Stacks.GradedSections.mul_def, Stacks.TwistedSections.gsmul_def, twistCongr]
  simp only [Category.assoc]
  have key := congrArg (· ≫ eqToHom (congrArg (natTensorPow L)
    (show n + (j + k) = k + (n + j) by omega))) (actMap_eqToHom_twistPow_natTensorPow t k)
  simp only [Category.assoc, eqToHom_trans] at key ⊢
  rw [key]

/-- **`Γ_*(X, 𝓛, 𝓛^{⊗ n}) ⟶ Γ_*(X, 𝓛)`**, degree `j` to degree `n + j`, linear over the
section ring. It is the shift `Γ_*(X, 𝓛, 𝓛^{⊗ n}) ⟶ S(n)` of the identification the Remark calls
obvious. -/
def unitShiftLinearMap (L : C) [(tensorRight L).Additive]
    [Stacks.GradedSections.HasTrivialSelfBraiding L] (n : ℕ) :
    twistModule (natTensorPow L n) L →ₗ[sectionRing L] sectionRing L where
  toFun := unitShiftHom L n
  map_add' := map_add _
  map_smul' r x := by
    induction r using DirectSum.induction_on with
    | zero => simp
    | of k a =>
        induction x using DirectSum.induction_on with
        | zero => simp
        | of j t =>
            rw [Stacks.TwistedSections.of_smul_of, unitShiftHom_of, unitShiftHom_of,
              RingHom.id_apply, smul_eq_mul, unitShiftHom_gsmul]
        | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
    | add r r' hr hr' => rw [add_smul, map_add, hr, hr', map_add, add_smul]

/-- `unitShiftLinearMap L n` acts as `unitShiftHom L n`. -/
@[simp] theorem unitShiftLinearMap_apply (n : ℕ) (x : twistModule (natTensorPow L n) L) :
    unitShiftLinearMap L n x = unitShiftHom L n x := rfl

/-- **The left leg of the identification `S(n) ~ Γ_*(X, 𝓛, N)`**: undo `β : L ^⊗ e ≅ N ⊙ k`,
then shift into the section ring. -/
noncomputable def unitIdent (N : C) {e k : ℕ} (β : natTensorPow L e ≅ twistPow N L k) :
    twistModule (twistPow N L k) L →ₗ[sectionRing L] sectionRing L :=
  (unitShiftLinearMap L e).comp (Stacks.TwistedSections.twistModuleLinearMap β.inv)

open AlgebraicGeometry.ProjectiveSpectrum.Proj (integerGrading) in
/-- **The left leg is graded**, from the shift by `-k` to the twist `S(n)`, when `e = n + k`. -/
theorem unitIdent_mem (N : C) {e k : ℕ} (β : natTensorPow L e ≅ twistPow N L k) {n : ℤ}
    (he : (e : ℤ) = n + k) (i : ℤ) (x : twistModule (twistPow N L k) L)
    (hx : x ∈ Stacks.GradedModule.shiftedGrading (moduleGrading (twistPow N L k) L)
      (-(k : ℤ)) i) :
    unitIdent N β x ∈ integerGrading (Stacks.TwistedSections.sectionGrading L) (i + n) := by
  rcases lt_or_ge (i + -(k : ℤ)) 0 with hneg | hpos
  · rw [eq_zero_of_mem_moduleGrading_of_neg hneg hx, map_zero]
    exact zero_mem _
  · obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le hpos
    change x ∈ moduleGrading (twistPow N L k) L (i + -(k : ℤ)) at hx
    rw [hj, Stacks.TwistedSections.moduleGrading_natCast] at hx
    obtain ⟨t, rfl⟩ := hx
    rw [show i + n = ((e + j : ℕ) : ℤ) by push_cast; omega,
      AlgebraicGeometry.ProjectiveSpectrum.Proj.integerGrading_natCast]
    show unitShiftHom L e (twistModuleHom (L := L) β.inv
      (DirectSum.of (twistSections (twistPow N L k) L) j t)) ∈ _
    rw [twistModuleHom_of, unitShiftHom_of]
    exact Stacks.ExternalGrading.of_mem_summand _ _

/-- `unitIdent N β` is injective on the homogeneous elements of degree `i` of the shifted
grading. -/
theorem unitIdent_injective (N : C) {e k : ℕ} (β : natTensorPow L e ≅ twistPow N L k) (i : ℤ)
    (x : twistModule (twistPow N L k) L)
    (hx : x ∈ Stacks.GradedModule.shiftedGrading (moduleGrading (twistPow N L k) L)
      (-(k : ℤ)) i)
    (h : unitIdent N β x = 0) : x = 0 := by
  rcases lt_or_ge (i + -(k : ℤ)) 0 with hneg | hpos
  · exact eq_zero_of_mem_moduleGrading_of_neg hneg hx
  · obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le hpos
    change x ∈ moduleGrading (twistPow N L k) L (i + -(k : ℤ)) at hx
    rw [hj, Stacks.TwistedSections.moduleGrading_natCast] at hx
    obtain ⟨t, rfl⟩ := hx
    change unitShiftHom L e (twistModuleHom (L := L) β.inv
      (DirectSum.of (twistSections (twistPow N L k) L) j t)) = 0 at h
    rw [twistModuleHom_of, unitShiftHom_of] at h
    have h0 := DirectSum.of_injective (β := powSections L) (e + j) (h.trans (map_zero _).symm)
    have ht : t = 0 := by
      have := congrArg (· ≫ eqToHom (twistPow_natTensorPow L e j).symm ≫
        twistPowMap L β.hom j) h0
      simpa [twistSectionsMap, ← Stacks.TwistedSections.twistPowMap_comp] using this
    rw [ht, map_zero]

open AlgebraicGeometry.ProjectiveSpectrum.Proj (integerGrading) in
/-- When `e = n + k` and `k ≤ i`, every element of degree `i + n` of the section ring is the image
under `unitIdent N β` of an element of degree `i` of the shifted grading. -/
theorem unitIdent_surjective (N : C) {e k : ℕ} (β : natTensorPow L e ≅ twistPow N L k) {n : ℤ}
    (he : (e : ℤ) = n + k) (i : ℤ) (hi : (k : ℤ) ≤ i) (y : sectionRing L)
    (hy : y ∈ integerGrading (Stacks.TwistedSections.sectionGrading L) (i + n)) :
    ∃ x : twistModule (twistPow N L k) L,
      x ∈ Stacks.GradedModule.shiftedGrading (moduleGrading (twistPow N L k) L)
        (-(k : ℤ)) i ∧ unitIdent N β x = y := by
  obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ i + -(k : ℤ) by omega)
  rw [show i + n = ((e + j : ℕ) : ℤ) by push_cast; omega,
    AlgebraicGeometry.ProjectiveSpectrum.Proj.integerGrading_natCast] at hy
  obtain ⟨y', rfl⟩ := hy
  refine ⟨DirectSum.of (twistSections (twistPow N L k) L) j
    (y' ≫ eqToHom (twistPow_natTensorPow L e j).symm ≫ twistPowMap L β.hom j), ?_, ?_⟩
  · show _ ∈ moduleGrading (twistPow N L k) L (i + -(k : ℤ))
    rw [hj, Stacks.TwistedSections.moduleGrading_natCast]
    exact Stacks.ExternalGrading.of_mem_summand _ _
  · show unitShiftHom L e (twistModuleHom (L := L) β.inv
      (DirectSum.of (twistSections (twistPow N L k) L) j _)) = _
    rw [twistModuleHom_of, unitShiftHom_of]
    congr 1
    simp [twistSectionsMap, ← Stacks.TwistedSections.twistPowMap_comp]

open AlgebraicGeometry.ProjectiveSpectrum.Proj (integerGrading) in
/-- **`Γ_*(X, 𝓛, 𝓛^{⊗ n}) ⟶ S(n)` is graded.** -/
theorem unitShiftLinearMap_mem (n : ℕ) (i : ℤ) (x : twistModule (natTensorPow L n) L)
    (hx : x ∈ moduleGrading (natTensorPow L n) L i) :
    unitShiftLinearMap L n x ∈
      integerGrading (Stacks.TwistedSections.sectionGrading L) (i + n) := by
  rcases lt_or_ge i 0 with hneg | hpos
  · rw [eq_zero_of_mem_moduleGrading_of_neg hneg hx, map_zero]
    exact zero_mem _
  · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hpos
    rw [Stacks.TwistedSections.moduleGrading_natCast] at hx
    obtain ⟨t, rfl⟩ := hx
    rw [show (j : ℤ) + n = ((n + j : ℕ) : ℤ) by push_cast; omega,
      AlgebraicGeometry.ProjectiveSpectrum.Proj.integerGrading_natCast, unitShiftLinearMap_apply,
      unitShiftHom_of]
    exact Stacks.ExternalGrading.of_mem_summand _ _

/-- `unitShiftLinearMap L n` is injective on the homogeneous elements of each degree. -/
theorem unitShiftLinearMap_injective (n : ℕ) (i : ℤ) (x : twistModule (natTensorPow L n) L)
    (hx : x ∈ moduleGrading (natTensorPow L n) L i) (h : unitShiftLinearMap L n x = 0) :
    x = 0 := by
  rcases lt_or_ge i 0 with hneg | hpos
  · exact eq_zero_of_mem_moduleGrading_of_neg hneg hx
  · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hpos
    rw [Stacks.TwistedSections.moduleGrading_natCast] at hx
    obtain ⟨t, rfl⟩ := hx
    rw [unitShiftLinearMap_apply, unitShiftHom_of] at h
    have h0 := DirectSum.of_injective (β := powSections L) (n + j) (h.trans (map_zero _).symm)
    have ht : t = 0 := by
      have := congrArg (· ≫ eqToHom (twistPow_natTensorPow L n j).symm) h0
      simpa using this
    rw [ht, map_zero]

open AlgebraicGeometry.ProjectiveSpectrum.Proj (integerGrading) in
/-- For `0 ≤ i`, every element of degree `i + n` of the section ring is the image under
`unitShiftLinearMap L n` of an element of degree `i`. -/
theorem unitShiftLinearMap_surjective (n : ℕ) (i : ℤ) (hi : 0 ≤ i) (y : sectionRing L)
    (hy : y ∈ integerGrading (Stacks.TwistedSections.sectionGrading L) (i + n)) :
    ∃ x : twistModule (natTensorPow L n) L,
      x ∈ moduleGrading (natTensorPow L n) L i ∧ unitShiftLinearMap L n x = y := by
  obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hi
  rw [show (j : ℤ) + n = ((n + j : ℕ) : ℤ) by push_cast; omega,
    AlgebraicGeometry.ProjectiveSpectrum.Proj.integerGrading_natCast] at hy
  obtain ⟨y', rfl⟩ := hy
  refine ⟨DirectSum.of (twistSections (natTensorPow L n) L) j
    (y' ≫ eqToHom (twistPow_natTensorPow L n j).symm), ?_, ?_⟩
  · rw [Stacks.TwistedSections.moduleGrading_natCast]
    exact Stacks.ExternalGrading.of_mem_summand _ _
  · rw [unitShiftLinearMap_apply, unitShiftHom_of]
    simp

omit [Preadditive C] [(tensorRight L).Additive]
  [Stacks.GradedSections.HasTrivialSelfBraiding L] in
open Stacks.TwistedSections (twistModule twistModuleHom twistSectionsMap) in
/-- **The numerator identity of the twist square, on graded-module elements.** If `r''` names
the section `r₀` of `L ^⊗ (n + j)` under `Γ_*(X, 𝓛, 𝓛^{⊗ n}) ⟶ S(n)`, and `z` names `r₀ · t`
under `Γ_*(X, 𝓛, 𝓕 ⊗ 𝓛^{⊗ n}) ⟶ M(n)`, then `z` is the external product of `t` and `t'`. -/
theorem eq_extProd_of_ident [Preadditive C] [(tensorRight L).Additive]
    [Stacks.GradedSections.HasTrivialSelfBraiding L] (F : C) {n i j k : ℕ}
    (t : twistSections F L i) (t' : twistSections (natTensorPow L n) L j)
    (r₀ : powSections L (n + j)) (z : twistSections (F ⊗ natTensorPow L n) L k)
    (hk : j + i = k)
    (h1 : unitShiftLinearMap L n (DirectSum.of (twistSections (natTensorPow L n) L) j t') =
      DirectSum.of (powSections L) (n + j) r₀)
    (h2 : identNat F n (DirectSum.of (twistSections (F ⊗ natTensorPow L n) L) k z) =
      DirectSum.of (powSections L) (n + j) r₀ • DirectSum.of (twistSections F L) i t) :
    z = (λ_ (𝟙_ C)).inv ≫ (t ⊗ₘ t') ≫ extProd F (natTensorPow L n) i j ≫
      eqToHom (congrArg (twistPow (F ⊗ natTensorPow L n) L) hk) := by
  refine eq_extProd_of_gsmul F t t' r₀ z rfl hk ?_ ?_
  · rw [unitShiftLinearMap_apply, unitShiftHom_of] at h1
    simpa using DirectSum.of_injective (β := powSections L) (n + j) h1
  · rw [Stacks.TwistedSections.of_smul_of] at h2
    change twistShiftHom F L n (twistModuleHom (L := L) (twistPowTensorIso F L n).inv
      (DirectSum.of _ k z)) = _ at h2
    rw [twistModuleHom_of, twistShiftHom_of, ← of_twistCongr (show n + j + i = n + k by omega)]
      at h2
    have := DirectSum.of_injective (β := twistSections F L) (n + k) h2
    simpa [twistShiftSection, twistSectionsMap, twistCongr] using this

omit [Preadditive C] [(tensorRight L).Additive]
  [Stacks.GradedSections.HasTrivialSelfBraiding L] in
/-- **The numerator identity behind the twist square, read through the identifications**: if
the image of `z` under the left leg of `M(n) ≅ Γ_*(X, 𝓛, 𝓕 ⊗ N)` is the product of the image of
`π` in `S` with `t`, then the shift of `z` is the external product of `t` and the shift of `π`. -/
theorem eq_extProd_of_identLeft [Preadditive C] [(tensorRight L).Additive]
    [Stacks.GradedSections.HasTrivialSelfBraiding L] (F N : C) {e k : ℕ}
    (β : natTensorPow L e ≅ twistPow N L k) {i j : ℕ} (t : twistSections F L i)
    (π : twistSections (twistPow N L k) L j)
    (z : twistSections (twistPow (F ⊗ N) L k) L (j + i))
    (h2 : identLeft F N β (DirectSum.of (twistSections (twistPow (F ⊗ N) L k) L) (j + i) z) =
      unitIdent N β (DirectSum.of (twistSections (twistPow N L k) L) j π) •
        DirectSum.of (twistSections F L) i t) :
    z ≫ eqToHom (Stacks.SectionRingProjTheta.twistPow_twistPow (F ⊗ N) L k (j + i)) ≫
        eqToHom (congrArg (twistPow (F ⊗ N) L) (Nat.add_assoc k j i).symm) =
      (λ_ (𝟙_ C)).inv ≫ (t ⊗ₘ (π ≫ eqToHom (Stacks.SectionRingProjTheta.twistPow_twistPow N L k
        j))) ≫ extProd F N i (k + j) := by
  refine eq_extProd_of_baseIso F N β t π _ z rfl ?_
  change twistShiftHom F L e (twistModuleHom (L := L) (baseIso F β).inv
      (DirectSum.of _ (j + i) z)) = unitShiftHom L e (twistModuleHom (L := L) β.inv
        (DirectSum.of _ j π)) • _ at h2
  rw [twistModuleHom_of, twistModuleHom_of, twistShiftHom_of, unitShiftHom_of,
    Stacks.TwistedSections.of_smul_of,
    ← of_twistCongr (show e + j + i = e + (j + i) by omega)] at h2
  have := DirectSum.of_injective (β := twistSections F L) (e + (j + i)) h2
  have h3 := congrArg (· ≫ eqToHom
    (Stacks.SectionRingProjTheta.twistPow_twistPow F L e (j + i)).symm) this
  simp only [twistShiftSection, twistSectionsMap, twistCongr, Category.assoc, eqToHom_trans,
    eqToHom_refl, Category.comp_id] at h3
  rw [h3]

end Unit

end Stacks.SectionRingProjTheta

end
