module

public import StacksFrontier.CategoryTheory.Shift.DetectingCommShift
public import StacksFrontier.CategoryTheory.Shift.DetectingCommShiftTwo

/-!
# Detecting the commutation with the shift on a class of resolutions

`StacksFrontier/CategoryTheory/Shift/DetectingCommShift.lean` tests
`CategoryTheory.NatTrans.CommShift η M` after restriction along an **essentially surjective**
shift-compatible functor.  That is the right tool for a localization functor, and the wrong tool
for the situation this file addresses: a transformation `η : F ⟶ G` whose *source* `F` inverts a
class of morphisms which `G` does not, known to be compatible with the shift only on a class of
objects — the K-flat complexes — which is **not** essentially surjective in the ambient category
of complexes.

What replaces essential surjectivity is far weaker and is exactly what the proof uses: it is
enough that every object `X` receive a morphism `p : P ⟶ X` from the class with `F.map p`
invertible.  `F` does not have to invert `p` for any structural reason and `G` need not do
anything: the commutation equation at `X`, precomposed with the isomorphism `F.map (p⟦a⟧)`, *is*
the equation at `P` postcomposed with `(G.map p)⟦a⟧`.

For a transformation of **bifunctors** the same observation applies twice, and in the *fixed*
variable it is cheaper still: there the condition is a one-variable
`CategoryTheory.NatTrans.CommShift` of a component of `η`, and a component at `X₁` is the conjugate
of the component at `P` by `G₁.map p` and `G₂.map p`, both shift-compatible by the `commShift_map`
field of `CategoryTheory.Functor.CommShift₂`.  So no per-object equation has to be reopened: only
`G₁.map p` has to be invertible, and `G₂.map p` need not be.

## Main results

* `CategoryTheory.NatTrans.shift_app_comm_of_whiskerLeft`: the commutation equation of `η` at an
  object of the form `q.obj P`, read off from the compatibility of `Functor.whiskerLeft q η`.
  This is the half of `CategoryTheory.NatTrans.commShift_of_whiskerLeft` which does not use
  essential surjectivity, named so that it can be used where that hypothesis is unavailable.
* `CategoryTheory.NatTrans.isIso_map_shiftFunctor_map`: a functor commuting with the shift
  inverts `p⟦a⟧` as soon as it inverts `p`, so the hypothesis of the transfer is available at
  every `a` from the single fact at the morphism itself.
* `CategoryTheory.NatTrans.shift_app_comm_of_isIso_map`: **the transfer** — the commutation
  equation at `X` follows from the equation at `P` as soon as `F.map (p⟦a⟧)` is invertible for
  some `p : P ⟶ X`.
* `CategoryTheory.NatTrans.commShift_of_whiskerLeft_of_resolution`: **the detection principle**.
  It specialises to `commShift_of_whiskerLeft` by taking `p` to be the comparison isomorphism of
  an essentially surjective `q`.
* `CategoryTheory.NatTrans.CommShift₂.commShift_app_of_isIso_map` and
  `commShift_flipApp_of_isIso_map`: the transfer in the **fixed** variable of a transformation of
  bifunctors, which asks only that the image of `p` under the source bifunctor be invertible.
  These are the `IsIso`-hypothesis counterparts of
  `CategoryTheory.NatTrans.commShift_app_of_iso` and `commShift_flipApp_of_iso`.
* `CategoryTheory.NatTrans.CommShift₂.of_resolution`: **the two-variable detection principle** —
  compatibility with the shifts in both variables, tested on a class of resolutions in each
  variable.  This is the form `CategoryTheory.NatTrans.CommShift₂.of_essSurj` takes when the two
  classes of models are not essentially surjective but only resolve every object.

## Implementation notes

**Why the hypothesis is about `F.map (p⟦a⟧)` and not about `p`.**  The equation at `X` lives on
`F.obj (X⟦a⟧)`, so what has to be inverted is the image of the *shifted* morphism.  In the
intended application `F` factors through a localization functor and `p` is a quasi-isomorphism, so
`p⟦a⟧` is one too and both images are invertible; stating the hypothesis at `p⟦a⟧` keeps that
step with the caller, where the shift-stability of the morphism class is known, instead of
demanding a `CategoryTheory.MorphismProperty.IsCompatibleWithShift` datum here.

**Why the fixed variable needs no resolution hypothesis of its own.**  The two statements for a
bifunctor are not symmetric in effort: in the varying variable the conclusion is an equation at
every object and the transfer has to be done object by object, while in the fixed variable the
conclusion is itself a `CategoryTheory.NatTrans.CommShift`, and a transformation equal to a
composite of three shift-compatible ones is shift-compatible by
`CategoryTheory.NatTrans.commShift_of_eq`.  That is why `commShift_app_of_isIso_map` is three
lines and `commShift_of_whiskerLeft_of_resolution` is not.
-/

@[expose] public section

universe v u v' u' v'' u''

namespace CategoryTheory.NatTrans

open Category Functor

section OneVariable

variable {V : Type u} [Category.{v} V] {H : Type u'} [Category.{v'} H]
  {E : Type u''} [Category.{v''} E] {M : Type*} [AddMonoid M]
  [HasShift V M] [HasShift H M] [HasShift E M]

/-- **The commutation equation at an object in the image of `q`**, read off from the
compatibility of `Functor.whiskerLeft q η` with the shift.  This is
`CategoryTheory.NatTrans.commShift_of_whiskerLeft` with its appeal to essential surjectivity
removed: the two equations differ by the naturality square of `η` at the component of the
commutation of `q` with the shift, which is invertible. -/
theorem shift_app_comm_of_whiskerLeft (q : V ⥤ H) [q.CommShift M]
    {F G : H ⥤ E} [F.CommShift M] [G.CommShift M] (η : F ⟶ G)
    (h : NatTrans.CommShift (Functor.whiskerLeft q η) M) (a : M) (P : V) :
    (F.commShiftIso a).hom.app (q.obj P) ≫ (shiftFunctor E a).map (η.app (q.obj P)) =
      η.app ((shiftFunctor H a).obj (q.obj P)) ≫ (G.commShiftIso a).hom.app (q.obj P) := by
  have hc := NatTrans.shift_app_comm (Functor.whiskerLeft q η) a P
  have hn := η.naturality ((q.commShiftIso a).hom.app P)
  dsimp at hc hn ⊢
  rw [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_hom_app] at hc
  rw [← cancel_epi (F.map ((q.commShiftIso a).hom.app P)), ← Category.assoc, hc,
    ← Category.assoc, ← hn, Category.assoc]

/-- **A functor commuting with the shift inverts the shift of a morphism it inverts.**  The
image of `p⟦a⟧` is the conjugate of the shift of the image of `p` by the commutation isomorphism,
so no compatibility of the morphism class with the shift has to be known: the caller who knows
`F.map p` invertible gets `F.map (p⟦a⟧)` invertible for free.  This is what feeds the hypothesis
of `shift_app_comm_of_isIso_map` at every `a` from the single fact at `a = 0`. -/
theorem isIso_map_shiftFunctor_map {F : H ⥤ E} [F.CommShift M] {X Y : H} (p : X ⟶ Y)
    [IsIso (F.map p)] (a : M) : IsIso (F.map ((shiftFunctor H a).map p)) := by
  have h : F.map ((shiftFunctor H a).map p) =
      (F.commShiftIso a).hom.app X ≫ (shiftFunctor E a).map (F.map p) ≫
        (F.commShiftIso a).inv.app Y := by
    rw [← Category.assoc, ← F.commShiftIso_hom_naturality p a, Category.assoc,
      Iso.hom_inv_id_app]
    simp
  rw [h]
  infer_instance

/-- **The transfer of the commutation equation along a morphism inverted by the source.**  The
equation at `X` precomposed with the isomorphism `F.map (p⟦a⟧)` is the equation at `P`
postcomposed with `(G.map p)⟦a⟧`, by naturality of `η` and of the two commutation isomorphisms;
so the first follows from the second. -/
theorem shift_app_comm_of_isIso_map {F G : H ⥤ E} [F.CommShift M] [G.CommShift M] (η : F ⟶ G)
    (a : M) {P X : H} (p : P ⟶ X) [IsIso (F.map ((shiftFunctor H a).map p))]
    (hP : (F.commShiftIso a).hom.app P ≫ (shiftFunctor E a).map (η.app P) =
      η.app ((shiftFunctor H a).obj P) ≫ (G.commShiftIso a).hom.app P) :
    (F.commShiftIso a).hom.app X ≫ (shiftFunctor E a).map (η.app X) =
      η.app ((shiftFunctor H a).obj X) ≫ (G.commShiftIso a).hom.app X := by
  have h₁ := F.commShiftIso_hom_naturality p a
  have h₂ := G.commShiftIso_hom_naturality p a
  have h₃ := η.naturality p
  have h₄ := η.naturality ((shiftFunctor H a).map p)
  dsimp at h₁ h₂ h₃ h₄ ⊢
  rw [← cancel_epi (F.map ((shiftFunctor H a).map p)), ← Category.assoc, h₁, Category.assoc,
    ← Functor.map_comp, h₃, Functor.map_comp, ← Category.assoc, hP, Category.assoc, ← h₂,
    ← Category.assoc, ← h₄, Category.assoc]

/-- **Commutation with the shift is detected on a class of objects which receives a morphism
inverted by the source into every object.**  The class is given as the image of a
shift-compatible functor `q`, exactly as in
`CategoryTheory.NatTrans.commShift_of_whiskerLeft`, but `q` is *not* assumed essentially
surjective: what replaces that is `hres`. -/
theorem commShift_of_whiskerLeft_of_resolution (q : V ⥤ H) [q.CommShift M]
    {F G : H ⥤ E} [F.CommShift M] [G.CommShift M] (η : F ⟶ G)
    (hres : ∀ (a : M) (X : H), ∃ (P : V) (p : q.obj P ⟶ X),
      IsIso (F.map ((shiftFunctor H a).map p)))
    (h : NatTrans.CommShift (Functor.whiskerLeft q η) M) :
    NatTrans.CommShift η M := by
  apply NatTrans.CommShift.of_core
  intro a
  constructor
  refine NatTrans.ext (funext fun X ↦ ?_)
  obtain ⟨P, p, _⟩ := hres a X
  have := shift_app_comm_of_isIso_map η a p (shift_app_comm_of_whiskerLeft q η h a P)
  dsimp at this ⊢
  exact this

end OneVariable

section TwoVariables

variable {C₁ : Type u} {C₂ : Type u'} {D : Type u''}
  [Category.{v} C₁] [Category.{v'} C₂] [Category.{v''} D]
  {M : Type*} [AddCommMonoid M] [HasShift C₁ M] [HasShift C₂ M] [HasShift D M]
  {G₁ G₂ : C₁ ⥤ C₂ ⥤ D} (τ : G₁ ⟶ G₂) (h : CommShift₂Setup D M)
  [G₁.CommShift₂ h] [G₂.CommShift₂ h]

namespace CommShift₂

/-- Shift-compatibility transfers along a naturality square whose two parallel sides are
shift-compatible and the first of them invertible. -/
private theorem commShift_of_naturality_square {C' : Type*} [Category C'] [HasShift C' M]
    {A B A' B' : C' ⥤ D} (α : A ⟶ B) (β : A' ⟶ B') (σ : A ⟶ A') (σ' : B ⟶ B') [IsIso α]
    [A.CommShift M] [B.CommShift M] [A'.CommShift M] [B'.CommShift M]
    [NatTrans.CommShift α M] [NatTrans.CommShift β M] (hσ : NatTrans.CommShift σ M)
    (hn : α ≫ σ' = σ ≫ β) : NatTrans.CommShift σ' M := by
  have : NatTrans.CommShift (inv α) M := NatTrans.CommShift.of_isIso _ M
  exact commShift_of_eq (θ := inv α ≫ σ ≫ β) (by rw [← hn, IsIso.inv_hom_id_assoc])

/-- **The condition in the second variable transfers along a morphism of the first variable whose
image under the source bifunctor is invertible.**  By naturality `τ.app X₁` is
`(G₁.map p)⁻¹ ≫ τ.app P ≫ G₂.map p`, and both `G₁.map p` and `G₂.map p` are shift-compatible
because a `CategoryTheory.Functor.CommShift₂` structure makes every `G.map f` shift-compatible.
Only the source's image has to be invertible.

This is the `IsIso`-hypothesis counterpart of `CategoryTheory.NatTrans.commShift_app_of_iso`,
which asks for an isomorphism of `C₁` and is therefore unavailable when the two objects are
merely connected by a quasi-isomorphism. -/
theorem commShift_app_of_isIso_map {P X₁ : C₁} (p : P ⟶ X₁) [IsIso (G₁.map p)]
    (hτ : NatTrans.CommShift (τ.app P) M) : NatTrans.CommShift (τ.app X₁) M := by
  have : NatTrans.CommShift (G₁.map p) M :=
    Functor.CommShift₂.commShift_map (G := G₁) (h := h) p
  have : NatTrans.CommShift (G₂.map p) M :=
    Functor.CommShift₂.commShift_map (G := G₂) (h := h) p
  exact commShift_of_naturality_square (G₁.map p) (G₂.map p) _ _ hτ (τ.naturality p)

/-- **The condition in the first variable transfers along a morphism of the second variable whose
image under the source bifunctor is invertible**, the mirror of `commShift_app_of_isIso_map`
through `CategoryTheory.Functor.flip`. -/
theorem commShift_flipApp_of_isIso_map {P X₂ : C₂} (p : P ⟶ X₂) [IsIso (G₁.flip.map p)]
    (hτ : NatTrans.CommShift (τ.flipApp P) M) : NatTrans.CommShift (τ.flipApp X₂) M := by
  have : NatTrans.CommShift (G₁.flip.map p) M :=
    Functor.CommShift₂.commShift_flip_map (G := G₁) (h := h) p
  have : NatTrans.CommShift (G₂.flip.map p) M :=
    Functor.CommShift₂.commShift_flip_map (G := G₂) (h := h) p
  exact commShift_of_naturality_square (G₁.flip.map p) (G₂.flip.map p) _ _ hτ
    (((flipFunctor C₁ C₂ D).map τ).naturality p)

variable {V₁ : Type*} {V₂ : Type*} [Category V₁] [Category V₂]
  [HasShift V₁ M] [HasShift V₂ M]

/-- **Compatibility with the shifts in both variables, detected on a class of resolutions in
each variable.**  This is the two-variable form of
`CategoryTheory.NatTrans.commShift_of_whiskerLeft_of_resolution`, and it is the form a
transformation of bifunctors whose *source* factors through a localization in each variable is
proved shift-compatible in: the two conditions are tested at objects of the image of `q₁` and
`q₂`, which need not be essentially surjective, so
`CategoryTheory.NatTrans.CommShift₂.of_essSurj` does not apply.

Each half takes two steps.  The *fixed* variable is replaced by a resolution by
`commShift_app_of_isIso_map`, which costs nothing because the conclusion there is itself a
`CategoryTheory.NatTrans.CommShift`; the *varying* variable is then handled by
`commShift_of_whiskerLeft_of_resolution`, which reopens the equation at each object.  Only the
**source** bifunctor has to invert the resolutions. -/
theorem of_resolution (q₁ : V₁ ⥤ C₁) [q₁.CommShift M] (q₂ : V₂ ⥤ C₂) [q₂.CommShift M]
    (hres₁ : ∀ (a : M) (X₁ : C₁), ∃ (P : V₁) (p : q₁.obj P ⟶ X₁),
      IsIso (G₁.map p) ∧ IsIso (G₁.map ((shiftFunctor C₁ a).map p)))
    (hres₂ : ∀ (a : M) (X₂ : C₂), ∃ (P : V₂) (p : q₂.obj P ⟶ X₂),
      IsIso (G₁.flip.map p) ∧ IsIso (G₁.flip.map ((shiftFunctor C₂ a).map p)))
    (h₁ : ∀ P : V₁, NatTrans.CommShift (Functor.whiskerLeft q₂ (τ.app (q₁.obj P))) M)
    (h₂ : ∀ P : V₂, NatTrans.CommShift (Functor.whiskerLeft q₁ (τ.flipApp (q₂.obj P))) M) :
    NatTrans.CommShift₂ τ h where
  commShift_app X₁ := by
    obtain ⟨P₁, p₁, _, -⟩ := hres₁ 0 X₁
    refine commShift_app_of_isIso_map τ h p₁ ?_
    refine commShift_of_whiskerLeft_of_resolution q₂ _ (fun a X₂ ↦ ?_) (h₁ P₁)
    obtain ⟨P₂, p₂, -, _⟩ := hres₂ a X₂
    exact ⟨P₂, p₂, inferInstanceAs
      (IsIso ((G₁.flip.map ((shiftFunctor C₂ a).map p₂)).app (q₁.obj P₁)))⟩
  commShift_flipApp X₂ := by
    obtain ⟨P₂, p₂, _, -⟩ := hres₂ 0 X₂
    refine commShift_flipApp_of_isIso_map τ h p₂ ?_
    refine commShift_of_whiskerLeft_of_resolution q₁ _ (fun a X₁ ↦ ?_) (h₂ P₂)
    obtain ⟨P₁, p₁, -, _⟩ := hres₁ a X₁
    exact ⟨P₁, p₁, inferInstanceAs
      (IsIso ((G₁.map ((shiftFunctor C₁ a).map p₁)).app (q₂.obj P₂)))⟩

end CommShift₂

end TwoVariables

end CategoryTheory.NatTrans

end
