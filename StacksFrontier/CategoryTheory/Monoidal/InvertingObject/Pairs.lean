module

public import StacksFrontier.CategoryTheory.Monoidal.BraidedProd
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObjectFunctor
public import StacksFrontier.CategoryTheory.Monoidal.InvertingObject.Graph
public import StacksFrontier.CategoryTheory.Monoidal.TensorPow

/-!
# Pairs of morphisms presented together

Let `K : 𝒜 ⥤ ℳ` be a fully faithful braided functor and `F : 𝒜 ⥤ 𝒞` a braided functor between
symmetric monoidal categories, `ℓ : K(L) ⊗ T ≅ 𝟙` and `V` an inverse of `F(L)`. Applying
`StacksFrontier.CategoryTheory.Monoidal.InvertingObject.Graph` to `K.prod' F : 𝒜 ⥤ ℳ × 𝒞` and
`(T, V)` gives a symmetric monoidal category `Pairs` whose morphisms are pairs of morphisms of
`ℳ` and `𝒞` presented by a common morphism of `𝒜`. Its first projection `Pairs.pr₁ : Pairs ⥤ ℳ`
is fully faithful: the second component of a pair is determined by the first, and every
morphism of `ℳ` has a partner.

## Main definitions

* `CategoryTheory.InvertingObject.Pairs`, with its projections `Pairs.pr₁` and `Pairs.pr₂`.

## Main results

* `CategoryTheory.InvertingObject.Pairs.pr₁_faithful`,
  `CategoryTheory.InvertingObject.Pairs.pr₁_full`,
  `CategoryTheory.InvertingObject.Pairs.pr₁_essSurj`.
-/

@[expose] public noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.InvertingObject

open MonoidalCategory BraidedCategory Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
open Expr

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] [MonoidalCategory 𝒜] [SymmetricCategory 𝒜]
  {ℳ : Type u₂} [Category.{v₂} ℳ] [MonoidalCategory ℳ] [SymmetricCategory ℳ]
  {𝒞 : Type u₃} [Category.{v₃} 𝒞] [MonoidalCategory 𝒞] [SymmetricCategory 𝒞]
  (K : 𝒜 ⥤ ℳ) [K.Braided] (F : 𝒜 ⥤ 𝒞) [F.Braided] {L : 𝒜} {T : ℳ}
  (ℓ : K.obj L ⊗ T ≅ 𝟙_ ℳ) (hL : HasInverse (F.obj L))

/-- The pairing of `(K(L), F(L))` with `(T, V)` in `ℳ × 𝒞`. -/
def pairing : (K.prod' F).obj L ⊗ ((T, hL.inv) : ℳ × 𝒞) ≅ 𝟙_ (ℳ × 𝒞) :=
  Iso.prod ℓ hL.isoLeft

/-- The symmetric monoidal category of formal expressions and pairs of morphisms of `ℳ` and `𝒞`
presented by a common morphism of `𝒜`. -/
abbrev Pairs : Type u₁ := Graph L (K.prod' F) ((T, hL.inv) : ℳ × 𝒞) (pairing K F ℓ hL)

namespace Pairs

/-- The first projection. -/
abbrev pr₁ : Pairs K F ℓ hL ⥤ ℳ := Graph.incl _ _ _ _ ⋙ Prod.fst ℳ 𝒞

/-- The second projection. -/
abbrev pr₂ : Pairs K F ℓ hL ⥤ 𝒞 := Graph.incl _ _ _ _ ⋙ Prod.snd ℳ 𝒞

variable {K F ℓ hL}

omit [MonoidalCategory 𝒜] [SymmetricCategory 𝒜] [SymmetricCategory ℳ] [SymmetricCategory 𝒞]
  [K.Braided] [F.Braided] in
/-- If `(K(X), F(X))` is invertible in `ℳ × 𝒞`, then `K(X)` is invertible. -/
theorem isInvertible_prod_fst {X : 𝒜} (h : IsInvertible ((K.prod' F).obj X)) :
    IsInvertible (K.obj X) :=
  IsInvertible.mapOfTensorIsos (Prod.fst ℳ 𝒞) h (εIso _) (μIso _)

omit [MonoidalCategory 𝒜] [SymmetricCategory 𝒜] [SymmetricCategory ℳ] [SymmetricCategory 𝒞]
  [K.Braided] [F.Braided] in
/-- If `(K(X), F(X))` is invertible in `ℳ × 𝒞`, then `F(X)` is invertible. -/
theorem isInvertible_prod_snd {X : 𝒜} (h : IsInvertible ((K.prod' F).obj X)) :
    IsInvertible (F.obj X) :=
  IsInvertible.mapOfTensorIsos (Prod.snd ℳ 𝒞) h (εIso _) (μIso _)

section Components

variable {e e' : Expr 𝒜}
  {u : (ev (K.prod' F) ((T, hL.inv) : ℳ × 𝒞)).obj e ⟶ (ev (K.prod' F) ((T, hL.inv) : ℳ × 𝒞)).obj e'}
  {X Y : 𝒜} {φ : (pad L).obj e ⊗ X ≅ (pad L).obj e' ⊗ Y} {c : (base).obj e ⊗ X ⟶ (base).obj e' ⊗ Y}

/-- The first component of a presentation. -/
theorem relX_fst (h : RelX L (K.prod' F) ((T, hL.inv) : ℳ × 𝒞) (pairing K F ℓ hL) u X Y φ c) :
    u.1 ▷ K.obj ((pad L).obj e ⊗ X) ≫ ((ev (K.prod' F) ((T, hL.inv) : ℳ × 𝒞)).obj e').1 ◁
      K.map φ.hom ≫ (θ L (K.prod' F) ((T, hL.inv) : ℳ × 𝒞) (pairing K F ℓ hL) e' Y).hom.1 =
      (θ L (K.prod' F) ((T, hL.inv) : ℳ × 𝒞) (pairing K F ℓ hL) e X).hom.1 ≫ K.map c :=
  (congrArg _root_.Prod.fst h :)

/-- The second component of a presentation. -/
theorem relX_snd (h : RelX L (K.prod' F) ((T, hL.inv) : ℳ × 𝒞) (pairing K F ℓ hL) u X Y φ c) :
    u.2 ▷ F.obj ((pad L).obj e ⊗ X) ≫ ((ev (K.prod' F) ((T, hL.inv) : ℳ × 𝒞)).obj e').2 ◁
      F.map φ.hom ≫ (θ L (K.prod' F) ((T, hL.inv) : ℳ × 𝒞) (pairing K F ℓ hL) e' Y).hom.2 =
      (θ L (K.prod' F) ((T, hL.inv) : ℳ × 𝒞) (pairing K F ℓ hL) e X).hom.2 ≫ F.map c :=
  (congrArg _root_.Prod.snd h :)

variable [K.Faithful]

/-- **The second component is determined by the first.** Two morphisms presented with the same
source padding and with equal first components are equal. -/
theorem eq_of_relX {u' : (ev (K.prod' F) ((T, hL.inv) : ℳ × 𝒞)).obj e ⟶
      (ev (K.prod' F) ((T, hL.inv) : ℳ × 𝒞)).obj e'} {Y' : 𝒜}
    {φ' : (pad L).obj e ⊗ X ≅ (pad L).obj e' ⊗ Y'} {c' : (base).obj e ⊗ X ⟶ (base).obj e' ⊗ Y'}
    (hY : LeftCancel ((pad L).obj e')) (hP : RightCancel (F.obj ((pad L).obj e ⊗ X)))
    (h : RelX L (K.prod' F) ((T, hL.inv) : ℳ × 𝒞) (pairing K F ℓ hL) u X Y φ c)
    (h' : RelX L (K.prod' F) ((T, hL.inv) : ℳ × 𝒞) (pairing K F ℓ hL) u' X Y' φ' c')
    (h₁ : u.1 = u'.1) : u = u' := by
  obtain ⟨χ, hχ⟩ := (hY (A := Y) (B := Y')).2 (φ.inv ≫ φ'.hom)
  have k := h.changeRightHom χ φ' (by
    change (pad L).obj e' ◁ χ = φ.inv ≫ φ'.hom at hχ
    rw [hχ, Iso.hom_inv_id_assoc])
  have hc : c ≫ (base).obj e' ◁ χ = c' := by
    apply K.map_injective
    have a := relX_fst k
    rw [h₁] at a
    exact (cancel_epi ((Prod.fst ℳ 𝒞).mapIso
      (θ L (K.prod' F) ((T, hL.inv) : ℳ × 𝒞) (pairing K F ℓ hL) e X)).hom).1
        (a.symm.trans (relX_fst h'))
  have a := relX_snd k
  have b := relX_snd h'
  rw [hc, ← b] at a
  refine Prod.hom_ext h₁ (hP.1 ?_)
  exact (cancel_mono (whiskerLeftIso _ (F.mapIso φ') ≪≫ (Prod.snd ℳ 𝒞).mapIso
    (θ L (K.prod' F) ((T, hL.inv) : ℳ × 𝒞) (pairing K F ℓ hL) e' Y')).hom).1 a

end Components

variable [K.Full] [K.Faithful]

omit [SymmetricCategory 𝒞] [F.Braided] in
/-- The padding of an object is left cancellable. -/
theorem leftCancel_pad (X : Pairs K F ℓ hL) : LeftCancel ((pad L).obj X.expr) :=
  LeftCancel.of_map K (Functor.FullyFaithful.ofFullyFaithful K)
    (IsInvertible.leftCancel (isInvertible_prod_fst X.isInvertible))

variable (K F ℓ hL)

/-- The first projection `Pairs.pr₁` is faithful. -/
instance pr₁_faithful : (pr₁ K F ℓ hL).Faithful where
  map_injective {X Y f g} hfg := by
    obtain ⟨X₁, Y₁, φ₁, c₁, hX₁, -, h₁⟩ := f.2
    obtain ⟨X₂, Y₂, φ₂, c₂, hX₂, -, h₂⟩ := g.2
    exact Graph.hom_ext (eq_of_relX (leftCancel_pad Y)
      (IsInvertible.rightCancel (isInvertible_prod_snd (IsInvertible.map_tensor (K.prod' F)
        X.isInvertible (IsInvertible.map_tensor _ hX₁ hX₂))))
      (h₁.padRight X₂) ((h₂.padRight X₁).changeLeft (β_ X₁ X₂)) hfg)

/-- The first projection `Pairs.pr₁` is full. -/
instance pr₁_full : (pr₁ K F ℓ hL).Full where
  map_surjective {X Y} m := by
    let N := whiskerLeftIso ((ev (K.prod' F) ((T, hL.inv) : ℳ × 𝒞)).obj Y.expr)
        ((K.prod' F).mapIso (β_ ((pad L).obj X.expr) ((pad L).obj Y.expr))) ≪≫
      θ L (K.prod' F) ((T, hL.inv) : ℳ × 𝒞) (pairing K F ℓ hL) Y.expr ((pad L).obj X.expr)
    let θX := θ L (K.prod' F) ((T, hL.inv) : ℳ × 𝒞) (pairing K F ℓ hL) X.expr
      ((pad L).obj Y.expr)
    let c := K.preimage (θX.inv.1 ≫ m ▷ K.obj ((pad L).obj X.expr ⊗ (pad L).obj Y.expr) ≫
      N.hom.1)
    have hR : RightCancel (F.obj ((pad L).obj X.expr ⊗ (pad L).obj Y.expr)) :=
      IsInvertible.rightCancel (isInvertible_prod_snd (IsInvertible.map_tensor (K.prod' F)
        X.isInvertible Y.isInvertible))
    obtain ⟨u₂, hu₂⟩ := (hR (A := ((ev (K.prod' F) ((T, hL.inv) : ℳ × 𝒞)).obj X.expr).2)
      (B := ((ev (K.prod' F) ((T, hL.inv) : ℳ × 𝒞)).obj Y.expr).2)).2
        (θX.hom.2 ≫ F.map c ≫ N.inv.2)
    refine ⟨⟨(m, u₂), (pad L).obj Y.expr, (pad L).obj X.expr,
      β_ ((pad L).obj X.expr) ((pad L).obj Y.expr), c, Y.isInvertible, X.isInvertible,
      Prod.hom_ext ?_ ?_⟩, rfl⟩
    · change m ▷ _ ≫ N.hom.1 = θX.hom.1 ≫ K.map c
      rw [Functor.map_preimage]
      exact (((Prod.fst ℳ 𝒞).mapIso θX).hom_inv_id_assoc _).symm
    · change u₂ ▷ F.obj ((pad L).obj X.expr ⊗ (pad L).obj Y.expr) ≫ N.hom.2 = θX.hom.2 ≫ F.map c
      change u₂ ▷ F.obj ((pad L).obj X.expr ⊗ (pad L).obj Y.expr) = _ at hu₂
      have hN : N.inv.2 ≫ N.hom.2 = 𝟙 _ := ((Prod.snd ℳ 𝒞).mapIso N).inv_hom_id
      rw [hu₂, Category.assoc, Category.assoc, hN]
      exact congrArg (θX.hom.2 ≫ ·) (Category.comp_id (F.map c))

variable {K F ℓ hL}

omit [MonoidalCategory 𝒜] [SymmetricCategory 𝒜] [K.Braided] [F.Braided] [K.Full] [K.Faithful] in
/-- `(K(L), F(L))` is invertible, with inverse `(T, V)`. -/
theorem isInvertible_obj_L (ℓ : K.obj L ⊗ T ≅ 𝟙_ ℳ) (hL : HasInverse (F.obj L)) :
    IsInvertible ((K.prod' F).obj L) :=
  ⟨⟨((T, hL.inv) : ℳ × 𝒞), pairing K F ℓ hL, β_ _ _ ≪≫ pairing K F ℓ hL⟩⟩

omit [K.Full] [K.Faithful] in
/-- The image under `K.prod' F` of the padding of `inv^{⊗ n}` is invertible. -/
theorem isInvertible_pad_tensorPow_inv (ℓ : K.obj L ⊗ T ≅ 𝟙_ ℳ) (hL : HasInverse (F.obj L))
    (n : ℕ) : IsInvertible ((K.prod' F).obj ((pad L).obj (tensorPow (Expr.inv : Expr 𝒜) n))) := by
  induction n with
  | zero => exact isInvertible_map_tensorUnit _
  | succ n ih => exact IsInvertible.map_tensor _ ih (isInvertible_obj_L ℓ hL)

variable (K F ℓ hL) in
/-- The object `atom A ⊗ inv^{⊗ n}`. -/
def powObj (A : 𝒜) (n : ℕ) : Pairs K F ℓ hL :=
  ⟨atom A ⊗ tensorPow Expr.inv n,
    IsInvertible.map_tensor _ (isInvertible_map_tensorUnit _)
      (isInvertible_pad_tensorPow_inv ℓ hL n)⟩

/-- The evaluation of `inv^{⊗ n}` in `ℳ` is `T^{⊗ n}`. -/
def evPowIso : ∀ n : ℕ,
    ((ev (K.prod' F) ((T, hL.inv) : ℳ × 𝒞)).obj (tensorPow (Expr.inv : Expr 𝒜) n)).1 ≅ tensorPow T n
  | 0 => Iso.refl _
  | n + 1 => tensorIso (evPowIso n) (Iso.refl T)

/-- The first projection of `atom A ⊗ inv^{⊗ n}` is `K(A) ⊗ T^{⊗ n}`. -/
def pr₁PowObjIso (A : 𝒜) (n : ℕ) :
    (pr₁ K F ℓ hL).obj (powObj K F ℓ hL A n) ≅ K.obj A ⊗ tensorPow T n :=
  whiskerLeftIso (K.obj A) (evPowIso (K := K) (F := F) (hL := hL) n)

omit [K.Full] [K.Faithful] in
variable (K F ℓ hL) in
/-- Under the hypothesis on the objects of `ℳ`, the first projection is essentially surjective. -/
theorem pr₁_essSurj (hess : ∀ M : ℳ, ∃ (A : 𝒜) (n : ℕ), Nonempty (M ≅ K.obj A ⊗ tensorPow T n)) :
    (pr₁ K F ℓ hL).EssSurj where
  mem_essImage M := by
    obtain ⟨A, n, ⟨i⟩⟩ := hess M
    exact ⟨powObj K F ℓ hL A n, ⟨pr₁PowObjIso A n ≪≫ i.symm⟩⟩

end Pairs

end CategoryTheory.InvertingObject
