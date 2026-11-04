module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsBilinearPairing
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearNaturality
public import StacksCore.Tactic.StacksAttribute

/-! # Naturality in the sheaf of values of the trilinear bijections

This file supplies the naturality in the sheaf of values `N` which the Yoneda step of
**Tag 03EL** needs of the three-variable chain, and which
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsBilinearPairing` records as missing:
the trilinear analogues of `Stacks.SheafOfModules.IsBilinearPairing.comp`, of
`Stacks.SheafOfModules.tensorHomOfPairing_comp`, of
`Stacks.SheafOfModules.tensorSheafHomEquivPresheafTensorHom_symm_naturality` and of
`Stacks.SheafOfModules.bilinearEquivTensorSheafHom_naturality`, and then the naturality of
**step 4** in its three-variable form,
`Stacks.SheafOfModules.extendScalarsTrilinearEquiv_naturality`.

## Main results

* `Stacks.SheafOfModules.IsTrilinearPairing.comp`: a trilinear pairing composed with a morphism
  of sheaves of modules is trilinear. This is the action of `Trilin_O(F × G × H, -)` on
  morphisms, and what makes "natural in `N`" mean anything at all here.
* `Stacks.SheafOfModules.tensorHomOfPairing₃_comp`: the morphism out of the double objectwise
  tensor product determined by a trilinear pairing is natural in the sheaf of values.
* `Stacks.SheafOfModules.doubleTensorSheafHomEquivPresheafTensorHom_naturality` and
  `Stacks.SheafOfModules.doubleTensorSheafHomEquivPresheafTensorHom_symm_naturality`: the
  bijection between morphisms out of `(F ⊗_A G) ⊗_A H` and morphisms of presheaves of modules
  out of `(F ⊗ G) ⊗ H` is natural in the sheaf of values, in both directions.
* `Stacks.SheafOfModules.trilinearEquivTensorSheafHom_naturality` and its `symm` form: **the
  double tensor product sheaf represents trilinear pairings naturally in the sheaf of values.**
* `Stacks.SheafOfModules.extendScalarsTrilinearEquiv_naturality`: **step 4 of the chain of
  Tag 03EL is natural in the sheaf of values in its three-variable form.**

## Implementation notes

Each statement mirrors its binary original, with the same universes: only the *source* of the
pairing grows with the arity, from a double to a triple product of underlying sheaves of sets,
and the operation on the target stays binary. In particular nothing here needs a square of
linearity to be transported, exactly as for the binary step 4.

Two of the proofs are written in term mode. `Stacks.SheafOfModules.trilinearEquivTensorSheafHom`
spells the index of its sheaves of modules `Stacks.Sheaves.RingedToposModules.commRingSheaf J A hA`
while `Stacks.SheafOfModules.Tensor.sheafTensor` spells it
`Stacks.SheafOfModules.TensorSheafification.structureSheaf A hA`; the two are definitionally but
not syntactically equal, so `rw` and `simp only` refuse a step whose pattern is visibly present
("target expression is not type-correct under the `implicit` transparency level") while a
`congrArg` at default transparency takes it. This is the discipline of
`Stacks.SheafOfModules.extendScalarsBilinearEquiv_naturality`.

For the same reason the naturality of
`Stacks.SheafOfModules.doubleTensorSheafHomEquivPresheafTensorHom` is proved in the *forward*
direction first and its inverse obtained by `Equiv.symm_apply_eq`: the forward direction is where
`Stacks.SheafOfModules.homCongr_refl_comp` disposes of the `Iso.homCongr` by the isomorphism
`Stacks.SheafOfModules.sheafifyDoubleTensorIso` which is the only thing the three-variable
bijection has over the binary one.

`Stacks.SheafOfModules.monoidalCategoryPresheafOfModules` is activated as a local instance,
fully qualified, in each namespace where an objectwise tensor product at the index
`Stacks.SheafOfModules.TensorSheafification.structureSheaf A hA` occurs: at that index Mathlib's
monoidal structure, keyed on a composite with `forget₂ CommRingCat RingCat`, is invisible to
instance search.

Nothing here carries a `@[stacks]` attribute: naturality of the chain of bijections is an
auxiliary of Tag 03EL and not a tagged statement of the source, exactly as for
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearNaturality`.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules
open Stacks.Sheaves.ToposPullback

universe w v u

namespace Stacks.SheafOfModules

/-! ## Post-composition of a triple pairing with a morphism of sheaves of modules -/

section Comp

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  {R : Sheaf J RingCat.{w}} {A B D N N' : SheafOfModules.{w} R}

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The value on a triple of local sections of a triple pairing composed with a morphism of
sheaves of modules: apply the morphism to the value of the original pairing. -/
lemma pairingApp₃_comp
    (p : (moduleSheaf R A ⨯ moduleSheaf R B) ⨯ moduleSheaf R D ⟶ moduleSheaf R N)
    (k : N ⟶ N') (U : Cᵒᵖ) (a : (sectionsFunctor J U).obj (moduleSheaf R A))
    (b : (sectionsFunctor J U).obj (moduleSheaf R B))
    (c : (sectionsFunctor J U).obj (moduleSheaf R D)) :
    pairingApp₃ R (p ≫ (moduleSheafFunctor R).map k) U a b c =
      (sectionsFunctor J U).map ((moduleSheafFunctor R).map k) (pairingApp₃ R p U a b c) :=
  (sectionsFunctor J U).map_comp_apply p ((moduleSheafFunctor R).map k) _

/-- A trilinear pairing composed with a morphism of sheaves of modules is trilinear, because a
morphism of sheaves of modules is additive and linear on sections. This is the action of
`Trilin_O(A × B × D, -)` on morphisms, and the three-variable form of
`Stacks.SheafOfModules.IsBilinearPairing.comp`. -/
lemma IsTrilinearPairing.comp
    {p : (moduleSheaf R A ⨯ moduleSheaf R B) ⨯ moduleSheaf R D ⟶ moduleSheaf R N}
    (hp : IsTrilinearPairing R p) (k : N ⟶ N') :
    IsTrilinearPairing R (p ≫ (moduleSheafFunctor R).map k) where
  add_left U a a' b c := by
    rw [pairingApp₃_comp, pairingApp₃_comp, pairingApp₃_comp, hp.add_left,
      sectionsFunctor_map_moduleSheafFunctor_map_add]
  add_mid U a b b' c := by
    rw [pairingApp₃_comp, pairingApp₃_comp, pairingApp₃_comp, hp.add_mid,
      sectionsFunctor_map_moduleSheafFunctor_map_add]
  add_right U a b c c' := by
    rw [pairingApp₃_comp, pairingApp₃_comp, pairingApp₃_comp, hp.add_right,
      sectionsFunctor_map_moduleSheafFunctor_map_add]
  smul_left U r a b c := by
    rw [pairingApp₃_comp, pairingApp₃_comp, hp.smul_left,
      sectionsFunctor_map_moduleSheafFunctor_map_smul]
  smul_mid U r a b c := by
    rw [pairingApp₃_comp, pairingApp₃_comp, hp.smul_mid,
      sectionsFunctor_map_moduleSheafFunctor_map_smul]
  smul_right U r a b c := by
    rw [pairingApp₃_comp, pairingApp₃_comp, hp.smul_right,
      sectionsFunctor_map_moduleSheafFunctor_map_smul]

end Comp

/-! ## Naturality of the presheaf-level three-variable universal property -/

section PresheafTensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  {O : Cᵒᵖ ⥤ CommRingCat.{w}} {hO : Presheaf.IsSheaf J
    (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf O)}
  {A B D N N' : SheafOfModules.{w} (commRingSheaf J O hO)}

/-- The morphism out of the double objectwise tensor product determined by a trilinear pairing is
natural in the sheaf of values. The three-variable form of
`Stacks.SheafOfModules.tensorHomOfPairing_comp`. -/
lemma tensorHomOfPairing₃_comp
    {p : (moduleSheaf (commRingSheaf J O hO) A ⨯ moduleSheaf (commRingSheaf J O hO) B) ⨯
      moduleSheaf (commRingSheaf J O hO) D ⟶ moduleSheaf (commRingSheaf J O hO) N}
    (hp : IsTrilinearPairing (commRingSheaf J O hO) p) (k : N ⟶ N') :
    tensorHomOfPairing₃ (hp.comp k) = tensorHomOfPairing₃ hp ≫ k.val := by
  refine PresheafOfModules.hom_ext fun U ↦ ?_
  refine ModuleCat.MonoidalCategory.tensor_ext₃' fun a b c ↦ ?_
  exact pairingApp₃_comp p k U a b c

/-- **The universal property of the double objectwise tensor product is natural in the sheaf of
values.** -/
lemma trilinearEquivPresheafTensorHom_naturality
    (p : { p : (moduleSheaf (commRingSheaf J O hO) A ⨯
        moduleSheaf (commRingSheaf J O hO) B) ⨯ moduleSheaf (commRingSheaf J O hO) D ⟶
          moduleSheaf (commRingSheaf J O hO) N //
      IsTrilinearPairing (commRingSheaf J O hO) p }) (k : N ⟶ N') :
    trilinearEquivPresheafTensorHom
        ⟨p.1 ≫ (moduleSheafFunctor (commRingSheaf J O hO)).map k, p.2.comp k⟩ =
      trilinearEquivPresheafTensorHom p ≫ k.val :=
  tensorHomOfPairing₃_comp p.2 k

end PresheafTensor

/-! ## Naturality of the three-variable universal property of the tensor product sheaf -/

section TensorSheaf

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {A : Cᵒᵖ ⥤ CommRingCat.{w}} {hA : Presheaf.IsSheaf J
    (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A)}
  {F G H N N' : SheafOfModules.{w} (commRingSheaf J A hA)}

/-- If `e` and `e'` commute with post-composition operations `f` and `g`, so do their inverses. -/
private theorem symm_apply_comp_of_apply_comp {α α' β β' : Sort*} (e : α ≃ β) (e' : α' ≃ β')
    (f : α → α') (g : β → β') (h : ∀ x, e' (f x) = g (e x)) (y : β) :
    e'.symm (g y) = f (e.symm y) :=
  e'.symm_apply_eq.2 (by rw [h, e.apply_symm_apply])

omit [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- `Stacks.SheafOfModules.doubleTensorSheafHomEquivPresheafTensorHom` is natural in the sheaf of
values: the `Iso.homCongr` by
`Stacks.SheafOfModules.sheafifyDoubleTensorIso` commutes with post-composition, and the rest is
the right-hand naturality of the sheafification adjunction. -/
lemma doubleTensorSheafHomEquivPresheafTensorHom_naturality
    (u : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨A, Presheaf.isSheaf_of_isSheaf_comp _ A (forget₂ CommRingCat RingCat) hA⟩).obj
          (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨A, Presheaf.isSheaf_of_isSheaf_comp _ A (forget₂ CommRingCat RingCat) hA⟩).obj
          (F)).obj (G))))).obj (H)) ⟶ N) (k : N ⟶ N') :
    doubleTensorSheafHomEquivPresheafTensorHom (A := A) (hA := hA) (u ≫ k) =
      doubleTensorSheafHomEquivPresheafTensorHom (A := A) (hA := hA) (F := F) (G := G) (H := H) u ≫
        k.val :=
  (congrArg (fun z ↦ (PresheafOfModules.sheafificationAdjunction
        (R := commRingSheaf J A hA) (𝟙 _)).homEquiv ((F.val ⊗ G.val) ⊗ H.val) N' z)
      (homCongr_refl_comp
        (sheafifyDoubleTensorIso (A := A) (hA := hA) (F := F) (G := G) (H := H)).symm u k)).trans
    ((PresheafOfModules.sheafificationAdjunction
      (R := commRingSheaf J A hA) (𝟙 _)).homEquiv_naturality_right _ k)

omit [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The inverse of `Stacks.SheafOfModules.doubleTensorSheafHomEquivPresheafTensorHom` is natural
in the sheaf of values. The three-variable form of
`Stacks.SheafOfModules.tensorSheafHomEquivPresheafTensorHom_symm_naturality`. -/
lemma doubleTensorSheafHomEquivPresheafTensorHom_symm_naturality
    (t : (F.val ⊗ G.val) ⊗ H.val ⟶ N.val) (k : N ⟶ N') :
    (doubleTensorSheafHomEquivPresheafTensorHom (A := A) (hA := hA)
          (F := F) (G := G) (H := H) (N := N')).symm (t ≫ k.val) =
      (doubleTensorSheafHomEquivPresheafTensorHom (A := A) (hA := hA)
        (F := F) (G := G) (H := H) (N := N)).symm t ≫ k := by
  exact symm_apply_comp_of_apply_comp _ _ (· ≫ k) (· ≫ k.val)
    (fun u ↦ doubleTensorSheafHomEquivPresheafTensorHom_naturality u k) t

/-- **The double tensor product sheaf represents trilinear pairings naturally in the sheaf of
values.** The three-variable form of
`Stacks.SheafOfModules.bilinearEquivTensorSheafHom_naturality`. -/
lemma trilinearEquivTensorSheafHom_naturality
    (p : { p : (moduleSheaf (commRingSheaf J A hA) F ⨯ moduleSheaf (commRingSheaf J A hA) G) ⨯
        moduleSheaf (commRingSheaf J A hA) H ⟶ moduleSheaf (commRingSheaf J A hA) N //
      IsTrilinearPairing (commRingSheaf J A hA) p }) (k : N ⟶ N') :
    trilinearEquivTensorSheafHom (A := A) (hA := hA)
        ⟨p.1 ≫ (moduleSheafFunctor (commRingSheaf J A hA)).map k, p.2.comp k⟩ =
      trilinearEquivTensorSheafHom (A := A) (hA := hA) p ≫ k :=
  (congrArg (fun t ↦ (doubleTensorSheafHomEquivPresheafTensorHom (A := A) (hA := hA)
        (F := F) (G := G) (H := H) (N := N')).symm t)
      (tensorHomOfPairing₃_comp (hO := hA) p.2 k)).trans
    (doubleTensorSheafHomEquivPresheafTensorHom_symm_naturality _ k)

/-- The inverse of `Stacks.SheafOfModules.trilinearEquivTensorSheafHom` is natural in the sheaf
of values: the trilinear pairing of a morphism composed with `k` is the original pairing composed
with `k`. This is the direction the chain of bijections of Tag 03EL traverses. -/
lemma trilinearEquivTensorSheafHom_symm_naturality
    (t : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨A, Presheaf.isSheaf_of_isSheaf_comp _ A (forget₂ CommRingCat RingCat) hA⟩).obj
          (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨A, Presheaf.isSheaf_of_isSheaf_comp _ A (forget₂ CommRingCat RingCat) hA⟩).obj
          (F)).obj (G))))).obj (H)) ⟶ N) (k : N ⟶ N') :
    (trilinearEquivTensorSheafHom (A := A) (hA := hA) (F := F) (G := G) (H := H)
        (N := N')).symm (t ≫ k) =
      ⟨((trilinearEquivTensorSheafHom (A := A) (hA := hA) (F := F) (G := G) (H := H)
          (N := N)).symm t).1 ≫
          (moduleSheafFunctor (commRingSheaf J A hA)).map k,
        ((trilinearEquivTensorSheafHom (A := A) (hA := hA)
          (F := F) (G := G) (H := H) (N := N)).symm t).2.comp k⟩ := by
  exact symm_apply_comp_of_apply_comp
    (trilinearEquivTensorSheafHom (A := A) (hA := hA) (F := F) (G := G) (H := H) (N := N))
    (trilinearEquivTensorSheafHom (A := A) (hA := hA) (F := F) (G := G) (H := H) (N := N'))
    (fun x ↦ ⟨x.1 ≫ (moduleSheafFunctor (commRingSheaf J A hA)).map k, x.2.comp k⟩) (· ≫ k)
    (fun u ↦ trilinearEquivTensorSheafHom_naturality u k) t

end TensorSheaf

/-! ## Naturality of step 4 in its three-variable form -/

section BaseChange

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {A₁ A₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (θ : A₁ ⟶ A₂)
  (h₁ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₁))
  (h₂ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₂))

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **Base change of trilinear pairings is natural in the sheaf of values.** This is what the
Yoneda step of Tag 03EL needs of the three-variable form of step 4; its three ingredients are
the naturality of the three-variable universal property of the double tensor product sheaf on
each side and the right-hand naturality of the adjunction of Tag 03CZ.

It is proved in term mode, for the reason recorded for
`Stacks.SheafOfModules.extendScalarsBilinearEquiv_naturality`: its two sides spell the index of
the sheaves of modules two ways, and the two spellings are definitionally but not syntactically
equal. -/
lemma extendScalarsTrilinearEquiv_naturality
    (F G H : SheafOfModules.{w} (commRingSheaf J A₁ h₁))
    {N N' : SheafOfModules.{w} (commRingSheaf J A₂ h₂)} (k : N ⟶ N')
    (q : { q : (moduleSheaf (commRingSheaf J A₁ h₁) F ⨯
        moduleSheaf (commRingSheaf J A₁ h₁) G) ⨯ moduleSheaf (commRingSheaf J A₁ h₁) H ⟶
          moduleSheaf (commRingSheaf J A₁ h₁)
            ((SheafOfModules.restrictScalars (commRingSheafMap J θ h₁ h₂)).obj N) //
      IsTrilinearPairing (commRingSheaf J A₁ h₁) q }) :
    extendScalarsTrilinearEquiv θ h₁ h₂ F G H N'
        ⟨q.1 ≫ (moduleSheafFunctor (commRingSheaf J A₁ h₁)).map
            ((SheafOfModules.restrictScalars (commRingSheafMap J θ h₁ h₂)).map k),
          q.2.comp _⟩ =
      ⟨(extendScalarsTrilinearEquiv θ h₁ h₂ F G H N q).1 ≫
          (moduleSheafFunctor (commRingSheaf J A₂ h₂)).map k,
        (extendScalarsTrilinearEquiv θ h₁ h₂ F G H N q).2.comp k⟩ :=
  (congrArg (fun t ↦ (trilinearEquivTensorSheafHom (A := A₂) (hA := h₂)
        (F := (extendScalars J θ h₁ h₂).obj F) (G := (extendScalars J θ h₁ h₂).obj G)
        (H := (extendScalars J θ h₁ h₂).obj H) (N := N')).symm
        ((extendScalarsTensorIso₃ θ h₁ h₂ F G H).homCongr (Iso.refl N')
          (((extendRestrictScalarsAdjunction J θ h₁ h₂).homEquiv
              ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨A₁, Presheaf.isSheaf_of_isSheaf_comp _ A₁ (forget₂ CommRingCat RingCat) h₁⟩).obj
          (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨A₁, Presheaf.isSheaf_of_isSheaf_comp _ A₁ (forget₂ CommRingCat RingCat) h₁⟩).obj
          (F)).obj (G))))).obj (H))) N').symm t)))
      (trilinearEquivTensorSheafHom_naturality q
        ((SheafOfModules.restrictScalars (commRingSheafMap J θ h₁ h₂)).map k))).trans
    ((congrArg (fun t ↦ (trilinearEquivTensorSheafHom (A := A₂) (hA := h₂)
          (F := (extendScalars J θ h₁ h₂).obj F) (G := (extendScalars J θ h₁ h₂).obj G)
          (H := (extendScalars J θ h₁ h₂).obj H) (N := N')).symm
          ((extendScalarsTensorIso₃ θ h₁ h₂ F G H).homCongr (Iso.refl N') t))
        ((extendRestrictScalarsAdjunction J θ h₁ h₂).homEquiv_naturality_right_symm
          (trilinearEquivTensorSheafHom (A := A₁) (hA := h₁)
            (F := F) (G := G) (H := H) q) k)).trans
      ((congrArg (fun t ↦ (trilinearEquivTensorSheafHom (A := A₂) (hA := h₂)
          (F := (extendScalars J θ h₁ h₂).obj F) (G := (extendScalars J θ h₁ h₂).obj G)
          (H := (extendScalars J θ h₁ h₂).obj H) (N := N')).symm t)
          (homCongr_refl_comp (extendScalarsTensorIso₃ θ h₁ h₂ F G H) _ k)).trans
        (trilinearEquivTensorSheafHom_symm_naturality (A := A₂) (hA := h₂)
          (F := (extendScalars J θ h₁ h₂).obj F) (G := (extendScalars J θ h₁ h₂).obj G)
          (H := (extendScalars J θ h₁ h₂).obj H) _ k)))

end BaseChange

end Stacks.SheafOfModules

end
