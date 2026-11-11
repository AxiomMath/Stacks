module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.RingTheory.EssentialFiniteness
public import StacksFrontier.AlgebraicGeometry.Thickenings.SectionDeformations

/-!
# Points of a group scheme trivial on a thickening

Let `G` be a group scheme over `S`, with unit section `e : S ⟶ G`, and let `y` be a point of `G`
to which every point of `e(S)` specializes (for `S` local, the unit at the closed point). For a
scheme `T` over `S` with a first-order thickening `T₀ ⟶ T`, the points `a : T ⟶ G` restricting to
the unit on `T₀` are described by the derivations of the local ring `𝒪_{G, y}`
(`AlgebraicGeometry.Scheme.Hom.stalkDiff`). This file proves that this description turns the
group law of `G` into addition of derivations, the classical computation that the group law
induces addition on the tangent space at the identity.

## Main results

* `AlgebraicGeometry.Scheme.exists_forall_specializes_of_isLocalRing`: an affine scheme with
  local ring of global functions has a point to which every point specializes.
* `AlgebraicGeometry.Scheme.Hom.formallySmooth_essFiniteType_stalk`: the local ring of a smooth
  scheme over an affine `S` is formally smooth and essentially of finite type over `Γ(S, 𝒪_S)`.
* `AlgebraicGeometry.GrpObj.stalkDiff_mul`: the difference of a product of two points trivial on
  the thickening is the sum of the differences.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MonoidalCategory
  CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

/-- **An affine scheme with local global functions has a closed point to which every point
specializes**: the image of the closed point of `Spec Γ(S, 𝒪_S)`. -/
theorem Scheme.exists_forall_specializes_of_isLocalRing (S : Scheme.{u}) [IsAffine S]
    [IsLocalRing Γ(S, ⊤)] : ∃ s₀ : S, ∀ s : S, s ⤳ s₀ := by
  refine ⟨S.isoSpec.inv.base (IsLocalRing.closedPoint Γ(S, ⊤)), fun s ↦ ?_⟩
  have h := (IsLocalRing.specializes_closedPoint (S.isoSpec.hom.base s)).map
    S.isoSpec.inv.continuous
  have e : S.isoSpec.inv.base (S.isoSpec.hom.base s) = s := by
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl
  rwa [e] at h

/-- **The local ring of a smooth scheme is formally smooth and essentially of finite type**
over the global functions of an affine base, for the structure map
`Γ(S, 𝒪_S) ⟶ Γ(X, 𝒪_X) ⟶ 𝒪_{X, y}`. -/
theorem Scheme.Hom.formallySmooth_essFiniteType_stalk {S X : Scheme.{u}} [IsAffine S]
    (p : X ⟶ S) [Smooth p] (y : X) :
    letI := (p.appTop ≫ X.presheaf.germ ⊤ y trivial).hom.toAlgebra
    Algebra.FormallySmooth Γ(S, ⊤) (X.presheaf.stalk y) ∧
      Algebra.EssFiniteType Γ(S, ⊤) (X.presheaf.stalk y) := by
  let iRB : Algebra Γ(S, ⊤) (X.presheaf.stalk y) :=
    (p.appTop ≫ X.presheaf.germ ⊤ y trivial).hom.toAlgebra
  let iAB : Algebra (S.presheaf.stalk (p.base y)) (X.presheaf.stalk y) :=
    (p.stalkMap y).hom.toAlgebra
  let iRA : Algebra Γ(S, ⊤) (S.presheaf.stalk (p.base y)) :=
    (S.presheaf.germ ⊤ (p.base y) trivial).hom.toAlgebra
  have : IsScalarTower Γ(S, ⊤) (S.presheaf.stalk (p.base y)) (X.presheaf.stalk y) :=
    IsScalarTower.of_algebraMap_eq' (by
      exact congrArg CommRingCat.Hom.hom (Scheme.Hom.germ_stalkMap p ⊤ y trivial).symm)
  have hloc : IsLocalization.AtPrime (S.presheaf.stalk (p.base y))
      ((isAffineOpen_top S).primeIdealOf ⟨p.base y, trivial⟩).asIdeal :=
    (isAffineOpen_top S).isLocalization_stalk ⟨p.base y, trivial⟩
  have : Algebra.FormallySmooth Γ(S, ⊤) (S.presheaf.stalk (p.base y)) :=
    Algebra.FormallySmooth.of_isLocalization
      ((isAffineOpen_top S).primeIdealOf ⟨p.base y, trivial⟩).asIdeal.primeCompl
  have : Algebra.EssFiniteType Γ(S, ⊤) (S.presheaf.stalk (p.base y)) :=
    Algebra.EssFiniteType.of_isLocalization _
      ((isAffineOpen_top S).primeIdealOf ⟨p.base y, trivial⟩).asIdeal.primeCompl
  have : Algebra.FormallySmooth (S.presheaf.stalk (p.base y)) (X.presheaf.stalk y) :=
    Scheme.Hom.mem_smoothLocus.mp (by rw [p.smoothLocus_eq_top]; trivial)
  have : Algebra.EssFiniteType (S.presheaf.stalk (p.base y)) (X.presheaf.stalk y) :=
    LocallyOfFiniteType.stalkMap p y
  exact ⟨Algebra.FormallySmooth.comp _ (S.presheaf.stalk (p.base y)) _,
    Algebra.EssFiniteType.comp _ (S.presheaf.stalk (p.base y)) _⟩

namespace GrpObj

variable {S : Scheme.{u}} (G : Over S) [GrpObj G]

/-- The unit section `S ⟶ G` of a group scheme over `S`. -/
abbrev unitSection : S ⟶ G.left := (η : 𝟙_ (Over S) ⟶ G).left

/-- The unit section is a section of the structure morphism. -/
theorem unitSection_comp_hom : unitSection G ≫ G.hom = 𝟙 S :=
  Over.w (η : 𝟙_ (Over S) ⟶ G)

/-- The unit of the group of points `T ⟶ G` is the composite of the structure morphism of `T`
with the unit section. -/
theorem one_left (T : Over S) : (1 : T ⟶ G).left = T.hom ≫ unitSection G :=
  rfl

/-- A point of `G` restricting to the unit along `i` agrees on the source of `i` with the trivial
point. -/
theorem left_comp_eq_of_comp_eq_one {T₀ T : Over S} (i : T₀ ⟶ T) {a : T ⟶ G} (h : i ≫ a = 1) :
    i.left ≫ a.left = i.left ≫ T.hom ≫ unitSection G := by
  have e := congrArg Over.Hom.left h
  rw [Over.comp_left] at e
  rw [e, one_left, ← Category.assoc, Over.w i]

variable (s₀ : S) (hs₀ : ∀ s : S, s ⤳ s₀)

include hs₀ in
/-- Every point of the unit section specializes to the unit at `s₀`. -/
theorem specializes_unitSection (s : S) :
    (unitSection G).base s ⤳ (unitSection G).base s₀ :=
  (hs₀ s).map (unitSection G).continuous

variable {T₀ T : Over S} (i : T₀ ⟶ T) (hi : Function.Surjective i.left.base)

include hs₀ hi in
/-- A point of `G` restricting to the unit along a surjective `i` lands in the generizations of
the unit at `s₀`. -/
theorem specializes_of_comp_eq_one {a : T ⟶ G} (h : i ≫ a = 1) (t : T.left) :
    a.left.base t ⤳ (unitSection G).base s₀ :=
  Scheme.Hom.specializes_of_comp_eq T.hom (unitSection G) _ (specializes_unitSection G s₀ hs₀) hi
    (left_comp_eq_of_comp_eq_one G i h) t

/-- **The group law is addition of derivations.** Let `G` be a group scheme over `S`, `s₀` a
point to which every point of `S` specializes, and `i : T₀ ⟶ T` a surjection over `S` whose kernel
on global functions is square-zero. For points `a`, `b : T ⟶ G` restricting to the unit along `i`,
the difference of `a * b` with the unit is the sum of those of `a` and `b`, as maps on
`𝒪_{G, e(s₀)}`. -/
theorem stalkDiff_mul [IsAffine S]
    (h2 : ∀ c d : Γ(T.left, ⊤), i.left.appTop.hom c = 0 → i.left.appTop.hom d = 0 → c * d = 0)
    (a b : T ⟶ G) (ha : i ≫ a = 1) (hb : i ≫ b = 1) :
    Scheme.Hom.stalkDiff T.hom (unitSection G) _ (specializes_unitSection G s₀ hs₀) (a * b).left
        (specializes_of_comp_eq_one G s₀ hs₀ i hi
          (by rw [MonObj.comp_mul, ha, hb, mul_one])) =
      Scheme.Hom.stalkDiff T.hom (unitSection G) _ (specializes_unitSection G s₀ hs₀) a.left
          (specializes_of_comp_eq_one G s₀ hs₀ i hi ha) +
        Scheme.Hom.stalkDiff T.hom (unitSection G) _ (specializes_unitSection G s₀ hs₀) b.left
          (specializes_of_comp_eq_one G s₀ hs₀ i hi hb) := by
  -- notation
  set σ := unitSection G with hσdef
  set q := T.hom
  set y := σ.base s₀
  set σ₂ : S ⟶ (G ⊗ G).left := (lift (η : 𝟙_ (Over S) ⟶ G) η).left
  set y₂ := σ₂.base s₀
  have hy₂ : ∀ s : S, σ₂.base s ⤳ y₂ := fun s ↦ (hs₀ s).map σ₂.continuous
  have hη : (1 : 𝟙_ (Over S) ⟶ G) = η := by
    rw [Hom.one_def, toUnit_unit, Category.id_comp]
  have hσ₂fst : σ₂ ≫ (fst G G).left = σ := by
    rw [← Over.comp_left, lift_fst]
  have hσ₂snd : σ₂ ≫ (snd G G).left = σ := by
    rw [← Over.comp_left, lift_snd]
  have hσ₂μ : σ₂ ≫ (μ : G ⊗ G ⟶ G).left = σ := by
    rw [← Over.comp_left, ← hη, ← Hom.mul_def, mul_one, hη]
  have hσ₂p : σ₂ ≫ (G ⊗ G).hom = 𝟙 S := Over.w (lift (η : 𝟙_ (Over S) ⟶ G) η)
  -- points of `G ⊗ G` trivial along `i`
  have hcond : ∀ c : T ⟶ G ⊗ G, i ≫ c ≫ fst G G = 1 → i ≫ c ≫ snd G G = 1 →
      i ≫ c = toUnit T₀ ≫ lift (η : 𝟙_ (Over S) ⟶ G) η := by
    intro c h₁ h₂
    refine hom_ext _ _ ?_ ?_
    · rw [Category.assoc, h₁, Category.assoc, lift_fst, Hom.one_def]
    · rw [Category.assoc, h₂, Category.assoc, lift_snd, Hom.one_def]
  have hleft : ∀ c : T ⟶ G ⊗ G, i ≫ c = toUnit T₀ ≫ lift (η : 𝟙_ (Over S) ⟶ G) η →
      i.left ≫ c.left = i.left ≫ q ≫ σ₂ := fun c hc ↦ by
    have e := congrArg Over.Hom.left hc
    rw [Over.comp_left] at e
    rw [e, Over.comp_left, ← Category.assoc, Over.w i]
    rfl
  have hspec₂ : ∀ c : T ⟶ G ⊗ G, i ≫ c = toUnit T₀ ≫ lift (η : 𝟙_ (Over S) ⟶ G) η →
      ∀ t, c.left.base t ⤳ y₂ := fun c hc ↦
    Scheme.Hom.specializes_of_comp_eq q σ₂ y₂ hy₂ hi (hleft c hc)
  have hc₁ := hcond (lift a 1) (by rw [lift_fst, ha]) (by rw [lift_snd, MonObj.comp_one])
  have hc₂ := hcond (lift 1 b) (by rw [lift_fst, MonObj.comp_one]) (by rw [lift_snd, hb])
  -- the sum of the two differences on `𝒪_{G ⊗ G, (e, e)}`
  let δ : (G ⊗ G).left.presheaf.stalk y₂ →+ Γ(T.left, ⊤) :=
    { toFun := fun f ↦ Scheme.Hom.stalkDiff q σ₂ y₂ hy₂ (lift a 1).left (hspec₂ _ hc₁) f +
        Scheme.Hom.stalkDiff q σ₂ y₂ hy₂ (lift 1 b).left (hspec₂ _ hc₂) f
      map_zero' := by
        simp only [Scheme.Hom.stalkDiff_apply, map_zero, sub_self, add_zero]
      map_add' := fun f g ↦ by
        rw [Scheme.Hom.stalkDiff_add, Scheme.Hom.stalkDiff_add]
        abel }
  have hδ : ∀ f, δ f = Scheme.Hom.stalkDiff q σ₂ y₂ hy₂ (lift a 1).left (hspec₂ _ hc₁) f +
      Scheme.Hom.stalkDiff q σ₂ y₂ hy₂ (lift 1 b).left (hspec₂ _ hc₂) f := fun _ ↦ rfl
  obtain ⟨cl, hcl, hclp, -, hcld⟩ := Scheme.Hom.exists_stalkDiff_eq q σ₂ y₂ hy₂ hσ₂p i.left h2 δ
    (fun f ↦ by
      rw [hδ, map_add, Scheme.Hom.appTop_stalkDiff q σ₂ y₂ hy₂ i.left _ _ (hleft _ hc₁),
        Scheme.Hom.appTop_stalkDiff q σ₂ y₂ hy₂ i.left _ _ (hleft _ hc₂), add_zero])
    (fun f g ↦ by
      rw [hδ, hδ, hδ, Scheme.Hom.stalkDiff_mul q σ₂ y₂ hy₂ i.left h2 _ _ (hleft _ hc₁),
        Scheme.Hom.stalkDiff_mul q σ₂ y₂ hy₂ i.left h2 _ _ (hleft _ hc₂)]
      ring)
    (fun r ↦ by
      rw [hδ, Scheme.Hom.stalkDiff_germ_appTop q σ₂ y₂ hy₂ hσ₂p _ _ (Over.w (lift a 1)),
        Scheme.Hom.stalkDiff_germ_appTop q σ₂ y₂ hy₂ hσ₂p _ _ (Over.w (lift 1 b)), add_zero])
  -- composing with a map `G ⊗ G ⟶ G` carrying the unit to the unit
  have hmapspec : ∀ (c : T.left ⟶ (G ⊗ G).left) (_ : ∀ t, c.base t ⤳ y₂)
      (φ : (G ⊗ G).left ⟶ G.left) (t : T.left), (c ≫ φ).base t ⤳ φ.base y₂ :=
    fun c hc φ t ↦ by rw [Scheme.Hom.comp_apply]; exact (hc t).map φ.continuous
  have hσspec : ∀ (φ : (G ⊗ G).left ⟶ G.left) (_ : σ₂ ≫ φ = σ) (s : S),
      σ.base s ⤳ φ.base y₂ := fun φ hφ s ↦ by
    rw [← hφ, Scheme.Hom.comp_apply]; exact (hy₂ s).map φ.continuous
  have hsum : ∀ (φ : (G ⊗ G).left ⟶ G.left) (hφ : σ₂ ≫ φ = σ) (f),
      Scheme.Hom.stalkDiff q σ (φ.base y₂) (hσspec φ hφ) (cl ≫ φ) (hmapspec cl hcl φ) f =
        Scheme.Hom.stalkDiff q σ (φ.base y₂) (hσspec φ hφ) ((lift a 1).left ≫ φ)
            (hmapspec _ (hspec₂ _ hc₁) φ) f +
          Scheme.Hom.stalkDiff q σ (φ.base y₂) (hσspec φ hφ) ((lift 1 b).left ≫ φ)
            (hmapspec _ (hspec₂ _ hc₂) φ) f := fun φ hφ f ↦ by
    rw [Scheme.Hom.stalkDiff_comp_right q σ₂ y₂ hy₂ φ hφ _ cl hcl,
      Scheme.Hom.stalkDiff_comp_right q σ₂ y₂ hy₂ φ hφ _ _ (hspec₂ _ hc₁),
      Scheme.Hom.stalkDiff_comp_right q σ₂ y₂ hy₂ φ hφ _ _ (hspec₂ _ hc₂), hcld, hδ]
  -- the trivial point has vanishing difference
  have hone : ∀ (y' : G.left) (hy' : ∀ s : S, σ.base s ⤳ y') (c : T ⟶ G) (_ : c = 1)
      (hcs : ∀ t, c.left.base t ⤳ y'), Scheme.Hom.stalkDiff q σ y' hy' c.left hcs = 0 := by
    rintro y' hy' c rfl hcs
    exact Scheme.Hom.stalkDiff_self q σ y' hy' hcs
  -- the components of the deformation `cl` are `a` and `b`
  have hcomp : ∀ (φ : (G ⊗ G).left ⟶ G.left) (hφ : σ₂ ≫ φ = σ) (a' : T ⟶ G)
      (e₁ : (lift a 1).left ≫ φ = a'.left) (e₂ : (lift 1 b).left ≫ φ = (1 : T ⟶ G).left),
      cl ≫ φ = a'.left := by
    intro φ hφ a' e₁ e₂
    have ha' : ∀ t, a'.left.base t ⤳ φ.base y₂ := by
      rw [← e₁]; exact hmapspec _ (hspec₂ _ hc₁) φ
    refine Scheme.Hom.eq_of_stalkDiff_eq q σ (φ.base y₂) (hσspec φ hφ) (hmapspec cl hcl φ) ha' ?_
    funext f
    rw [hsum φ hφ f, Scheme.Hom.stalkDiff_congr q σ (φ.base y₂) (hσspec φ hφ) e₁ _ ha',
      Scheme.Hom.stalkDiff_congr q σ (φ.base y₂) (hσspec φ hφ) e₂ _
        (by rw [← e₂]; exact hmapspec _ (hspec₂ _ hc₂) φ),
      hone _ _ 1 rfl, Pi.zero_apply, add_zero]
  have hcomp' : ∀ (φ : (G ⊗ G).left ⟶ G.left) (hφ : σ₂ ≫ φ = σ) (b' : T ⟶ G)
      (e₁ : (lift a 1).left ≫ φ = (1 : T ⟶ G).left) (e₂ : (lift 1 b).left ≫ φ = b'.left),
      cl ≫ φ = b'.left := by
    intro φ hφ b' e₁ e₂
    have hb' : ∀ t, b'.left.base t ⤳ φ.base y₂ := by
      rw [← e₂]; exact hmapspec _ (hspec₂ _ hc₂) φ
    refine Scheme.Hom.eq_of_stalkDiff_eq q σ (φ.base y₂) (hσspec φ hφ) (hmapspec cl hcl φ) hb' ?_
    funext f
    rw [hsum φ hφ f, Scheme.Hom.stalkDiff_congr q σ (φ.base y₂) (hσspec φ hφ) e₂ _ hb',
      Scheme.Hom.stalkDiff_congr q σ (φ.base y₂) (hσspec φ hφ) e₁ _
        (by rw [← e₁]; exact hmapspec _ (hspec₂ _ hc₁) φ),
      hone _ _ 1 rfl, Pi.zero_apply, zero_add]
  have hfst : cl ≫ (fst G G).left = a.left :=
    hcomp _ hσ₂fst a (by rw [← Over.comp_left, lift_fst]) (by rw [← Over.comp_left, lift_fst])
  have hsnd : cl ≫ (snd G G).left = b.left :=
    hcomp' _ hσ₂snd b (by rw [← Over.comp_left, lift_snd]) (by rw [← Over.comp_left, lift_snd])
  have hc' : (Over.homMk cl hclp : T ⟶ G ⊗ G) = lift a b := by
    refine hom_ext _ _ ?_ ?_
    · rw [lift_fst]
      apply Over.OverMorphism.ext
      change cl ≫ (fst G G).left = a.left
      exact hfst
    · rw [lift_snd]
      apply Over.OverMorphism.ext
      change cl ≫ (snd G G).left = b.left
      exact hsnd
  have hab : (a * b).left = cl ≫ (μ : G ⊗ G ⟶ G).left := by
    rw [Hom.mul_def, ← hc', Over.comp_left]
    rfl
  have e₁μ : (lift a 1).left ≫ (μ : G ⊗ G ⟶ G).left = a.left := by
    rw [← Over.comp_left, ← Hom.mul_def, mul_one]
  have e₂μ : (lift 1 b).left ≫ (μ : G ⊗ G ⟶ G).left = b.left := by
    rw [← Over.comp_left, ← Hom.mul_def, one_mul]
  have key : ∀ (y' : G.left) (hy' : ∀ s : S, σ.base s ⤳ y')
      (_ : (μ : G ⊗ G ⟶ G).left.base y₂ = y') (hab' : ∀ t, (a * b).left.base t ⤳ y')
      (ha' : ∀ t, a.left.base t ⤳ y') (hb' : ∀ t, b.left.base t ⤳ y'),
      Scheme.Hom.stalkDiff q σ y' hy' (a * b).left hab' =
        Scheme.Hom.stalkDiff q σ y' hy' a.left ha' +
          Scheme.Hom.stalkDiff q σ y' hy' b.left hb' := by
    rintro y' hy' rfl hab' ha' hb'
    funext f
    rw [Pi.add_apply, Scheme.Hom.stalkDiff_congr q σ _ hy' hab _ (hmapspec cl hcl _),
      hsum _ hσ₂μ f, Scheme.Hom.stalkDiff_congr q σ _ (hσspec _ hσ₂μ) e₁μ _ ha',
      Scheme.Hom.stalkDiff_congr q σ _ (hσspec _ hσ₂μ) e₂μ _ hb']
  exact key y (specializes_unitSection G s₀ hs₀) (by rw [← Scheme.Hom.comp_apply, hσ₂μ]) _ _ _

section Coordinates

variable [IsAffine S]
  [Algebra Γ(S, ⊤) (G.left.presheaf.stalk ((unitSection G).base s₀))]
  (halg : ∀ r, algebraMap Γ(S, ⊤) (G.left.presheaf.stalk ((unitSection G).base s₀)) r =
    (G.left.presheaf.germ ⊤ _ trivial).hom (G.hom.appTop.hom r))
  (ε : G.left.presheaf.stalk ((unitSection G).base s₀) →ₐ[Γ(S, ⊤)] Γ(S, ⊤))
  (hε : ∀ f, ε f = ((unitSection G).stalkToΓOfSpecializes _
    (specializes_unitSection G s₀ hs₀)).hom f)
  {g : ℕ} (v : Fin g → G.left.presheaf.stalk ((unitSection G).base s₀))
  (h2 : ∀ c d : Γ(T.left, ⊤), i.left.appTop.hom c = 0 → i.left.appTop.hom d = 0 → c * d = 0)

omit [IsAffine S] in
include halg hε h2 in
/-- The difference of a point trivial along `i`, with values in the kernel of `i^#` regarded as a
`Γ(S, 𝒪_S)`-module through `T`, is a derivation at the counit `ε`. -/
theorem exists_linearMap_stalkDiff (a : T ⟶ G) (ha : i ≫ a = 1) :
    letI : Module Γ(S, ⊤) (RingHom.ker i.left.appTop.hom) :=
      Module.compHom _ T.hom.appTop.hom
    ∃ D : G.left.presheaf.stalk ((unitSection G).base s₀) →ₗ[Γ(S, ⊤)]
        RingHom.ker i.left.appTop.hom,
      (∀ f f', D (f * f') = ε f • D f' + ε f' • D f) ∧
      ∀ f, (D f : Γ(T.left, ⊤)) = Scheme.Hom.stalkDiff T.hom (unitSection G) _
        (specializes_unitSection G s₀ hs₀) a.left
          (specializes_of_comp_eq_one G s₀ hs₀ i hi ha) f := by
  let : Module Γ(S, ⊤) (RingHom.ker i.left.appTop.hom) := Module.compHom _ T.hom.appTop.hom
  have hia := left_comp_eq_of_comp_eq_one G i ha
  have hsa := specializes_of_comp_eq_one G s₀ hs₀ i hi ha
  have hy := specializes_unitSection G s₀ hs₀
  -- the map of the trivial deformation is `ε` followed by `q^#`
  have hφ₀ : ∀ f, ((T.hom ≫ unitSection G).stalkToΓOfSpecializes _
      (Scheme.Hom.specializes_comp_section T.hom (unitSection G) _ hy)).hom f =
      T.hom.appTop.hom (ε f) := fun f ↦ by
    rw [Scheme.Hom.stalkToΓOfSpecializes_comp_section, hε]
    rfl
  have hsmul : ∀ (r : Γ(S, ⊤)) (m : RingHom.ker i.left.appTop.hom),
      ((r • m : RingHom.ker i.left.appTop.hom) : Γ(T.left, ⊤)) = T.hom.appTop.hom r * m :=
    fun _ _ ↦ rfl
  let D : G.left.presheaf.stalk ((unitSection G).base s₀) →ₗ[Γ(S, ⊤)]
      RingHom.ker i.left.appTop.hom :=
    { toFun := fun f ↦ ⟨Scheme.Hom.stalkDiff T.hom (unitSection G) _ hy a.left hsa f,
        Scheme.Hom.appTop_stalkDiff T.hom (unitSection G) _ hy i.left a.left hsa hia f⟩
      map_add' := fun f f' ↦ Subtype.ext
        (Scheme.Hom.stalkDiff_add T.hom (unitSection G) _ hy a.left hsa f f')
      map_smul' := fun r f ↦ Subtype.ext (by
        change Scheme.Hom.stalkDiff T.hom (unitSection G) _ hy a.left hsa (r • f) =
          T.hom.appTop.hom r * Scheme.Hom.stalkDiff T.hom (unitSection G) _ hy a.left hsa f
        rw [Algebra.smul_def, halg,
          Scheme.Hom.stalkDiff_mul T.hom (unitSection G) _ hy i.left h2 _ hsa hia,
          Scheme.Hom.stalkDiff_germ_appTop T.hom (unitSection G) _ hy (unitSection_comp_hom G)
            _ hsa (Over.w a), mul_zero, add_zero,
          Scheme.Hom.stalkToΓOfSpecializes_germ_appTop T.hom _ _ _
            (by rw [Category.assoc, unitSection_comp_hom, Category.comp_id])]) }
  have hD : ∀ f, (D f : Γ(T.left, ⊤)) =
      Scheme.Hom.stalkDiff T.hom (unitSection G) _ hy a.left hsa f := fun _ ↦ rfl
  refine ⟨D, fun f f' ↦ Subtype.ext ?_, hD⟩
  rw [Submodule.coe_add, hsmul, hsmul, hD, hD, hD,
    Scheme.Hom.stalkDiff_mul T.hom (unitSection G) _ hy i.left h2 _ hsa hia, hφ₀, hφ₀]

omit [IsAffine S] in
include halg hε h2 in
/-- **The coordinates determine the point.** If every derivation at `ε` vanishing at the `vₖ`
vanishes, two points trivial along `i` with the same values at the `vₖ` of their differences are
equal. -/
theorem eq_of_stalkDiff_coordinates_eq
    (hv : ∀ (M : Type u) [AddCommGroup M] [Module Γ(S, ⊤) M]
      (D : G.left.presheaf.stalk ((unitSection G).base s₀) →ₗ[Γ(S, ⊤)] M),
      (∀ a b, D (a * b) = ε a • D b + ε b • D a) → (∀ k, D (v k) = 0) → D = 0)
    (a b : T ⟶ G) (ha : i ≫ a = 1) (hb : i ≫ b = 1)
    (h : ∀ k, Scheme.Hom.stalkDiff T.hom (unitSection G) _ (specializes_unitSection G s₀ hs₀)
        a.left (specializes_of_comp_eq_one G s₀ hs₀ i hi ha) (v k) =
      Scheme.Hom.stalkDiff T.hom (unitSection G) _ (specializes_unitSection G s₀ hs₀)
        b.left (specializes_of_comp_eq_one G s₀ hs₀ i hi hb) (v k)) : a = b := by
  let : Module Γ(S, ⊤) (RingHom.ker i.left.appTop.hom) := Module.compHom _ T.hom.appTop.hom
  obtain ⟨Da, hDa, hDa'⟩ := exists_linearMap_stalkDiff G s₀ hs₀ i hi halg ε hε h2 a ha
  obtain ⟨Db, hDb, hDb'⟩ := exists_linearMap_stalkDiff G s₀ hs₀ i hi halg ε hε h2 b hb
  have h0 := hv _ (Da - Db) (fun f f' ↦ by
      simp only [LinearMap.sub_apply, hDa, hDb, smul_sub]
      abel)
    (fun k ↦ by
      rw [LinearMap.sub_apply, sub_eq_zero]
      exact Subtype.ext ((hDa' (v k)).trans ((h k).trans (hDb' (v k)).symm)))
  refine Over.OverMorphism.ext (Scheme.Hom.eq_of_stalkDiff_eq T.hom (unitSection G) _
    (specializes_unitSection G s₀ hs₀) (specializes_of_comp_eq_one G s₀ hs₀ i hi ha)
    (specializes_of_comp_eq_one G s₀ hs₀ i hi hb) (funext fun f ↦ ?_))
  rw [← hDa', ← hDb']
  exact congrArg Subtype.val (sub_eq_zero.mp (LinearMap.congr_fun h0 f))

include halg hε h2 in
/-- **Every family of elements of the kernel is the family of coordinates of a point.** If every
family of `g` elements of a module is the family of values at the `vₖ` of a derivation at `ε`,
then every family of `g` elements of the kernel of `i^#` is the family of coordinates of a point
trivial along `i`. -/
theorem exists_stalkDiff_coordinates_eq
    (hv : ∀ (M : Type u) [AddCommGroup M] [Module Γ(S, ⊤) M] (m : Fin g → M),
      ∃ D : G.left.presheaf.stalk ((unitSection G).base s₀) →ₗ[Γ(S, ⊤)] M,
        (∀ a b, D (a * b) = ε a • D b + ε b • D a) ∧ ∀ k, D (v k) = m k)
    (m : Fin g → Γ(T.left, ⊤)) (hm : ∀ k, i.left.appTop.hom (m k) = 0) :
    ∃ (a : T ⟶ G) (ha : i ≫ a = 1), ∀ k,
      Scheme.Hom.stalkDiff T.hom (unitSection G) _ (specializes_unitSection G s₀ hs₀)
        a.left (specializes_of_comp_eq_one G s₀ hs₀ i hi ha) (v k) = m k := by
  let : Module Γ(S, ⊤) (RingHom.ker i.left.appTop.hom) := Module.compHom _ T.hom.appTop.hom
  have hy := specializes_unitSection G s₀ hs₀
  have hsmul : ∀ (r : Γ(S, ⊤)) (m : RingHom.ker i.left.appTop.hom),
      ((r • m : RingHom.ker i.left.appTop.hom) : Γ(T.left, ⊤)) = T.hom.appTop.hom r * m :=
    fun _ _ ↦ rfl
  have hφ₀ : ∀ f, ((T.hom ≫ unitSection G).stalkToΓOfSpecializes _
      (Scheme.Hom.specializes_comp_section T.hom (unitSection G) _ hy)).hom f =
      T.hom.appTop.hom (ε f) := fun f ↦ by
    rw [Scheme.Hom.stalkToΓOfSpecializes_comp_section, hε]
    rfl
  obtain ⟨D, hDL, hDv⟩ := hv (RingHom.ker i.left.appTop.hom) (fun k ↦ ⟨m k, hm k⟩)
  have hD1 : D 1 = 0 := by
    have h := hDL 1 1
    simp only [mul_one, map_one, one_smul] at h
    simpa using h
  let δ : G.left.presheaf.stalk ((unitSection G).base s₀) →+ Γ(T.left, ⊤) :=
    (RingHom.ker i.left.appTop.hom).subtype.toAddMonoidHom.comp D.toAddMonoidHom
  have hδ : ∀ f, δ f = D f := fun _ ↦ rfl
  obtain ⟨al, hal, halp, hial, hald⟩ := Scheme.Hom.exists_stalkDiff_eq T.hom (unitSection G) _ hy
    (unitSection_comp_hom G) i.left h2 δ (fun f ↦ (D f).2)
    (fun f f' ↦ by
      rw [hδ, hδ, hδ, hDL, Submodule.coe_add, hsmul, hsmul, hφ₀, hφ₀])
    (fun r ↦ by
      rw [hδ, ← halg, ← mul_one (algebraMap _ _ r), ← Algebra.smul_def, map_smul, hD1, smul_zero]
      rfl)
  have ha : i ≫ Over.homMk al halp = 1 := by
    apply Over.OverMorphism.ext
    change i.left ≫ al = (1 : T₀ ⟶ G).left
    rw [hial, one_left, ← Category.assoc, Over.w i]
  refine ⟨Over.homMk al halp, ha, fun k ↦ ?_⟩
  change Scheme.Hom.stalkDiff T.hom (unitSection G) _ hy al _ (v k) = m k
  rw [hald, hδ, hDv]

end Coordinates

end GrpObj

end AlgebraicGeometry

end
