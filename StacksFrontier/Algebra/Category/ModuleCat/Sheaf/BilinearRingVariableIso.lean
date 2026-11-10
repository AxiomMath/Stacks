module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearRingVariable
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageFullyFaithful

/-!
# The ring variable of the universal property of the tensor product sheaf, along an isomorphism

`Stacks.SheafOfModules.tensorSheafRestrictScalarsHom` is the comparison

`(F|_{A₁}) ⊗_{A₁} (G|_{A₁}) ⟶ (F ⊗_{A₂} G)|_{A₁}`

of the two tensor products attached to a morphism `a : A₁ ⟶ A₂` of sheaves of rings, the lax
structure map of restriction of scalars. Restriction of scalars is not monoidal, so for a general
`a` that is all there is. For an `a` which is an **isomorphism** the comparison is an isomorphism,
and that is what is proved here.

## Main results

* `Stacks.SheafOfModules.isIso_tensorSheafRestrictScalarsHom`: **the comparison of the two tensor
  products is an isomorphism when the morphism of sheaves of rings is.** This is what lets the
  composition law `Stacks.SheafOfModules.pullbackTensorStep4_comp` for step 4 of the chain of
  Tag 03EL be solved for step 4 at a composite: the comparison of the two readings of the base
  ring there is `Stacks.Sheaves.RingedToposModules.inverseImageRingSheafCompIso`, an isomorphism.

## Implementation notes

*The inverse.* Restriction of scalars along an isomorphism is an equivalence of categories of
sheaves of modules, with quasi-inverse the restriction along `a⁻¹`
(`Stacks.SheafOfModules.RestrictScalars.equivalence`); its unit and counit
`Stacks.SheafOfModules.RestrictScalars.compIso` are the identity on underlying sheaves of sets.
The inverse comparison is built from the universal property over `A₂`: the universal
`A₁`-bilinear pairing of `(F|_{A₁}) ⊗_{A₁} (G|_{A₁})` is `A₂`-bilinear after restriction along
`a⁻¹` — which is `Stacks.SheafOfModules.IsBilinearPairing.restrictScalars` at `a⁻¹`, nothing new
— and its two arguments are identified with `F` and `G` by that counit. The morphism out of
`F ⊗_{A₂} G` it determines, restricted along `a` and followed by the unit, is the inverse.

*Why two identities are needed and where each comes from.* That the comparison followed by the
inverse is the identity is
`Stacks.SheafOfModules.bilinearEquivTensorSheafHom_restrictScalars` — the law in the ring
variable — followed by the naturality of the universal property in the sheaf of values: both
sides are the morphism out of `(F|_{A₁}) ⊗_{A₁} (G|_{A₁})` which the universal `A₁`-bilinear
pairing determines, and that one is the identity. The other composite is a pair of morphisms out
of `(F ⊗_{A₂} G)|_{A₁}`, which the universal property over `A₁` cannot compare, since that sheaf
is not a tensor product over `A₁`. It is compared over `A₂` instead: restriction of scalars along
an isomorphism is full, so the inverse comparison followed by the comparison is the restriction
of a morphism out of `F ⊗_{A₂} G`, and the universal property over `A₂` identifies *that*
morphism with the identity.

*The seams, and why the cancellations below are stated for a variable sheaf of modules.*
`Stacks.Sheaves.RingedToposModules.moduleSheaf_restrictScalars` holds by `rfl`, so each pairing
below is literally a pairing of the restricted modules as well, and the unit and counit are
literally the identity of a sheaf of sets. But the equation is not type-correct at `implicit`
transparency, so no `rw` crosses it; and checking it where the sheaf of modules is a tensor
product sheaf — a sheafification — is expensive, because the elaborator unfolds that
sheafification on both sides of the comparison. Both problems are avoided in the same way: the
two cancellations are stated once for a *variable* sheaf of modules (`prod_map_compIso_inv_app_comp`
and `compIso_hom_app_comp` below, over `comp_of_eq_id` and `prod_map_comp_of_eq_id` for an
abstract category), where the equation holds for free, and the tensor product sheaf is
substituted into them. Every other step is `congrArg` and `Eq.trans`.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open Stacks.Sheaves.RingedToposModules

namespace Stacks.SheafOfModules

universe w v u

/-! ## Cancelling a morphism which is the identity, for an abstract category -/

section Abstract

variable {𝒜 : Type u} [Category.{v} 𝒜]

/-- Postcomposition with a morphism which happens to be the identity does nothing. The source of
that morphism is *not* assumed to be syntactically the object it is the identity of, which is the
point: the morphisms cancelled below are the identity of a sheaf of sets with two spellings, one
through a restriction of scalars. -/
private lemma comp_of_eq_id {X Y : 𝒜} (q : X ⟶ Y) (k : Y ⟶ Y) (hk : k = 𝟙 Y) : q ≫ k = q := by
  rw [hk, Category.comp_id]

/-- Precomposition with a product of two morphisms which happen to be the identity does
nothing. -/
private lemma prod_map_comp_of_eq_id [HasBinaryProducts 𝒜] {X Y Z : 𝒜} (f : X ⟶ X) (g : Y ⟶ Y)
    (q r : X ⨯ Y ⟶ Z) (hf : f = 𝟙 X) (hg : g = 𝟙 Y) (h : q = r) :
    prod.map f g ≫ q = r := by
  rw [hf, hg, prod.map_id_id, Category.id_comp, h]

end Abstract

/-! ## The two coherence isomorphisms on underlying sheaves of sets -/

section Underlying

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  {S T : Sheaf J RingCat.{w}} (α : S ⟶ T) (β : T ⟶ S)

omit [J.HasSheafCompose (forget RingCat.{w})]

/-- Restricting scalars along `α` and then along a section `β` of it is the identity on
underlying sheaves of sets. -/
private lemma moduleSheafFunctor_map_compIso_hom_app (h : β ≫ α = 𝟙 T)
    (M : SheafOfModules.{w} T) :
    (Sheaf.moduleSheafFunctor T).map ((RestrictScalars.compIso.{w} α β h).hom.app M) =
      𝟙 (Sheaf.moduleSheaf T M) :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

/-- The same identification read in the other direction. -/
private lemma moduleSheafFunctor_map_compIso_inv_app (h : β ≫ α = 𝟙 T)
    (M : SheafOfModules.{w} T) :
    (Sheaf.moduleSheafFunctor T).map ((RestrictScalars.compIso.{w} α β h).inv.app M) =
      𝟙 (Sheaf.moduleSheaf T M) :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

/-- A pairing of the restrictions along `α` of two sheaves of `T`-modules, precomposed with the
identification of each of them with its restriction along `α` and back, and followed by a morphism
which cancels against the pairing, is the cancelled pairing. This is the cancellation the two
halves of `Stacks.SheafOfModules.isIso_tensorSheafRestrictScalarsHom` come down to.

The identifications are the identity on underlying sheaves of sets, and the sheaf of values is a
variable: the morphisms are used at a tensor product sheaf, where neither the elaborator nor a `rw`
can be asked to see through the two spellings of a restricted sheaf of modules. -/
private lemma prod_map_compIso_inv_app_comp (hα : β ≫ α = 𝟙 T) (A B : SheafOfModules.{w} T)
    {Z W : Sheaf J (Type w)}
    (q : Sheaf.moduleSheaf S ((SheafOfModules.restrictScalars α).obj A) ⨯
        Sheaf.moduleSheaf S ((SheafOfModules.restrictScalars α).obj B) ⟶ Z)
    (k : Z ⟶ W) (r : Sheaf.moduleSheaf S ((SheafOfModules.restrictScalars α).obj A) ⨯
        Sheaf.moduleSheaf S ((SheafOfModules.restrictScalars α).obj B) ⟶ W) (h : q ≫ k = r) :
    (prod.map ((Sheaf.moduleSheafFunctor T).map ((RestrictScalars.compIso.{w} α β hα).inv.app A))
      ((Sheaf.moduleSheafFunctor T).map ((RestrictScalars.compIso.{w} α β hα).inv.app B)) ≫
        q) ≫ k = r :=
  (Category.assoc _ _ _).trans (prod_map_comp_of_eq_id _ _ _ _
    (moduleSheafFunctor_map_compIso_inv_app α β hα A)
    (moduleSheafFunctor_map_compIso_inv_app α β hα B) h)

/-- The identification of a sheaf of `S`-modules with its restriction along `β` and back is the
identity on underlying sheaves of sets, so it drops out of a composite. Stated for an abstract
morphism and a variable sheaf of modules, for the same reason as `prod_map_compIso_inv_app_comp`. -/
private lemma compIso_hom_app_comp (M : SheafOfModules.{w} S) {X Y : Sheaf J (Type w)}
    (e : Sheaf.moduleSheaf S ((SheafOfModules.restrictScalars β ⋙
        SheafOfModules.restrictScalars α).obj M) ⟶ Sheaf.moduleSheaf S M)
    (he : e = 𝟙 (Sheaf.moduleSheaf S M))
    (q : X ⟶ Sheaf.moduleSheaf S M) (m : Sheaf.moduleSheaf S M ⟶ Y) :
    q ≫ (e ≫ m) = q ≫ m :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (fun z ↦ z ≫ m) (comp_of_eq_id q e he))

end Underlying

/-! ## The comparison of the two tensor products along an isomorphism -/

section TensorRingIso

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {A₁ A₂ : Cᵒᵖ ⥤ CommRingCat.{w}}
  {h₁ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₁)}
  {h₂ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₂)}
  (a : commRingSheaf J A₁ h₁ ⟶ commRingSheaf J A₂ h₂) [IsIso a]
  (F G : SheafOfModules.{w} (commRingSheaf J A₂ h₂))

/-- Restricting the scalars of a sheaf of `A₂`-modules along `a` and then back along `a⁻¹`
returns it. -/
private abbrev restrictBackIso :
    SheafOfModules.restrictScalars a ⋙ SheafOfModules.restrictScalars (inv a) ≅
      𝟭 (SheafOfModules.{w} (commRingSheaf J A₂ h₂)) :=
  RestrictScalars.compIso.{w} a (inv a) (IsIso.inv_hom_id a)

/-- Restricting the scalars of a sheaf of `A₁`-modules along `a⁻¹` and then back along `a`
returns it. -/
private abbrev restrictForthIso :
    SheafOfModules.restrictScalars (inv a) ⋙ SheafOfModules.restrictScalars a ≅
      𝟭 (SheafOfModules.{w} (commRingSheaf J A₁ h₁)) :=
  RestrictScalars.compIso.{w} (inv a) a (IsIso.hom_inv_id a)

/-- The `A₂`-bilinear pairing of `F` and `G` with values in the restriction along `a⁻¹` of
`(F|_{A₁}) ⊗_{A₁} (G|_{A₁})`: the universal `A₁`-bilinear pairing of that tensor product, which
is `A₂`-bilinear after restriction of scalars along `a⁻¹`, with its two arguments identified with
`F` and `G`. -/
private def tensorRestrictInvPairing :
    { q : Sheaf.moduleSheaf (commRingSheaf J A₂ h₂) F ⨯
          Sheaf.moduleSheaf (commRingSheaf J A₂ h₂) G ⟶
        Sheaf.moduleSheaf (commRingSheaf J A₂ h₂)
          ((SheafOfModules.restrictScalars (inv a)).obj
            ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨A₁, Presheaf.isSheaf_of_isSheaf_comp _ A₁
                (forget₂ CommRingCat RingCat) h₁⟩).obj
                ((SheafOfModules.restrictScalars a).obj F)).obj
                ((SheafOfModules.restrictScalars a).obj G)))) //
      IsBilinearPairing (commRingSheaf J A₂ h₂) q } :=
  ⟨_, ((tensorSheafUniversalPairing ((SheafOfModules.restrictScalars a).obj F)
      ((SheafOfModules.restrictScalars a).obj G)).2.restrictScalars (inv a)).precomp
    ((restrictBackIso a).inv.app F) ((restrictBackIso a).inv.app G)⟩

/-- **The inverse of the comparison of the two tensor products**, for an isomorphism `a` of
sheaves of rings: the morphism out of `F ⊗_{A₂} G` which the universal `A₁`-bilinear pairing of
`(F|_{A₁}) ⊗_{A₁} (G|_{A₁})` determines over `A₂`, restricted along `a`. -/
private def tensorSheafRestrictScalarsInv :
    (SheafOfModules.restrictScalars a).obj ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨A₂, Presheaf.isSheaf_of_isSheaf_comp _ A₂
        (forget₂ CommRingCat RingCat) h₂⟩).obj F).obj G)) ⟶
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨A₁, Presheaf.isSheaf_of_isSheaf_comp _ A₁
          (forget₂ CommRingCat RingCat) h₁⟩).obj ((SheafOfModules.restrictScalars a).obj F)).obj
          ((SheafOfModules.restrictScalars a).obj G)) :=
  (SheafOfModules.restrictScalars a).map
      (bilinearEquivTensorSheafHom (hA := h₂) (tensorRestrictInvPairing a F G)) ≫
    (restrictForthIso a).hom.app _

/-- The comparison of the two tensor products followed by its inverse is the identity: both are
the morphism out of `(F|_{A₁}) ⊗_{A₁} (G|_{A₁})` which the universal `A₁`-bilinear pairing
determines. -/
private lemma tensorSheafRestrictScalarsHom_comp_inv :
    tensorSheafRestrictScalarsHom a F G ≫ tensorSheafRestrictScalarsInv a F G = 𝟙 _ := by
  have hone := Equiv.apply_symm_apply (bilinearEquivTensorSheafHom (hA := h₁)
    (F := (SheafOfModules.restrictScalars a).obj F)
    (G := (SheafOfModules.restrictScalars a).obj G)
    (N := (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨A₁, Presheaf.isSheaf_of_isSheaf_comp _ A₁
        (forget₂ CommRingCat RingCat) h₁⟩).obj ((SheafOfModules.restrictScalars a).obj F)).obj
        ((SheafOfModules.restrictScalars a).obj G)))) (𝟙 _)
  have hpair := prod_map_compIso_inv_app_comp a (inv a) (IsIso.inv_hom_id a) F G
    (tensorSheafUniversalPairing ((SheafOfModules.restrictScalars a).obj F)
      ((SheafOfModules.restrictScalars a).obj G)).1 _ _
    (comp_of_eq_id _ _ (moduleSheafFunctor_map_compIso_hom_app (inv a) a (IsIso.hom_inv_id a)
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨A₁, Presheaf.isSheaf_of_isSheaf_comp _ A₁
          (forget₂ CommRingCat RingCat) h₁⟩).obj ((SheafOfModules.restrictScalars a).obj F)).obj
          ((SheafOfModules.restrictScalars a).obj G)))))
  change tensorSheafRestrictScalarsHom a F G ≫
      ((SheafOfModules.restrictScalars a).map
          (bilinearEquivTensorSheafHom (hA := h₂) (tensorRestrictInvPairing a F G)) ≫
        (restrictForthIso a).hom.app _) = 𝟙 _
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun m ↦ m ≫ (restrictForthIso a).hom.app
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨A₁, Presheaf.isSheaf_of_isSheaf_comp _ A₁
          (forget₂ CommRingCat RingCat) h₁⟩).obj ((SheafOfModules.restrictScalars a).obj F)).obj
          ((SheafOfModules.restrictScalars a).obj G))))
    (bilinearEquivTensorSheafHom_restrictScalars a F G (tensorRestrictInvPairing a F G))) ?_
  refine Eq.trans (bilinearEquivTensorSheafHom_naturality (hA := h₁) _ _).symm ?_
  exact Eq.trans (congrArg (bilinearEquivTensorSheafHom (hA := h₁)
      (F := (SheafOfModules.restrictScalars a).obj F)
      (G := (SheafOfModules.restrictScalars a).obj G)
      (N := (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨A₁, Presheaf.isSheaf_of_isSheaf_comp _ A₁
          (forget₂ CommRingCat RingCat) h₁⟩).obj ((SheafOfModules.restrictScalars a).obj F)).obj
          ((SheafOfModules.restrictScalars a).obj G)))) (Subtype.ext hpair)) hone

omit [IsIso a] in
/-- The universal `A₁`-bilinear pairing of `(F|_{A₁}) ⊗_{A₁} (G|_{A₁})` followed by the
comparison of the two tensor products is the universal `A₂`-bilinear pairing of `F ⊗_{A₂} G`:
the comparison is the morphism that pairing determines, and the inverse of the universal
property is natural in the sheaf of values. -/
private lemma universalPairing_comp_tensorSheafRestrictScalarsHom :
    (tensorSheafUniversalPairing ((SheafOfModules.restrictScalars a).obj F)
          ((SheafOfModules.restrictScalars a).obj G)).1 ≫
        (Sheaf.moduleSheafFunctor (commRingSheaf J A₁ h₁)).map
          (tensorSheafRestrictScalarsHom a F G) =
      (tensorSheafUniversalPairing F G).1 :=
  (congrArg Subtype.val
      (((congrArg (bilinearEquivTensorSheafHom (hA := h₁)
            (F := (SheafOfModules.restrictScalars a).obj F)
            (G := (SheafOfModules.restrictScalars a).obj G)
            (N := (SheafOfModules.restrictScalars a).obj
              ((((Stacks.SheafOfModules.Tensor.sheafTensor
                  ⟨A₂, Presheaf.isSheaf_of_isSheaf_comp _ A₂
                  (forget₂ CommRingCat RingCat) h₂⟩).obj F).obj G)))).symm
          (Category.id_comp (tensorSheafRestrictScalarsHom a F G))).trans
        (Equiv.symm_apply_apply _ _)).symm.trans
      (bilinearEquivTensorSheafHom_symm_naturality (hA := h₁)
        (F := (SheafOfModules.restrictScalars a).obj F)
        (G := (SheafOfModules.restrictScalars a).obj G)
        (𝟙 _) (tensorSheafRestrictScalarsHom a F G)))).symm

/-- A morphism out of the restriction along `a⁻¹` of `(F|_{A₁}) ⊗_{A₁} (G|_{A₁})` whose
restriction along `a` is the comparison of the two tensor products — preceded by the
identification of the source with itself restricted and back — carries the universal
`A₁`-bilinear pairing to the universal `A₂`-bilinear pairing of `F ⊗_{A₂} G`. -/
private lemma universalPairing_comp_moduleSheafFunctor_map
    (k : (SheafOfModules.restrictScalars (inv a)).obj ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨A₁, Presheaf.isSheaf_of_isSheaf_comp _ A₁ (forget₂ CommRingCat RingCat) h₁⟩).obj
        ((SheafOfModules.restrictScalars a).obj F)).obj
        ((SheafOfModules.restrictScalars a).obj G))) ⟶
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨A₂, Presheaf.isSheaf_of_isSheaf_comp _ A₂
            (forget₂ CommRingCat RingCat) h₂⟩).obj F).obj G))
    (hk : (SheafOfModules.restrictScalars a).map k =
      (restrictForthIso a).hom.app ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨A₁, Presheaf.isSheaf_of_isSheaf_comp _ A₁ (forget₂ CommRingCat RingCat) h₁⟩).obj
          ((SheafOfModules.restrictScalars a).obj F)).obj
          ((SheafOfModules.restrictScalars a).obj G))) ≫
        tensorSheafRestrictScalarsHom a F G) :
    (tensorSheafUniversalPairing ((SheafOfModules.restrictScalars a).obj F)
          ((SheafOfModules.restrictScalars a).obj G)).1 ≫
        (Sheaf.moduleSheafFunctor (commRingSheaf J A₂ h₂)).map k =
      (tensorSheafUniversalPairing F G).1 := by
  refine Eq.trans (congrArg (fun m ↦ (tensorSheafUniversalPairing
      ((SheafOfModules.restrictScalars a).obj F)
      ((SheafOfModules.restrictScalars a).obj G)).1 ≫ m)
    ((moduleSheafFunctor_map_restrictScalars_map a k).symm.trans
      ((congrArg (Sheaf.moduleSheafFunctor (commRingSheaf J A₁ h₁)).map hk).trans
        ((Sheaf.moduleSheafFunctor (commRingSheaf J A₁ h₁)).map_comp _ _)))) ?_
  refine Eq.trans (compIso_hom_app_comp a (inv a)
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨A₁, Presheaf.isSheaf_of_isSheaf_comp _ A₁
        (forget₂ CommRingCat RingCat) h₁⟩).obj ((SheafOfModules.restrictScalars a).obj F)).obj
        ((SheafOfModules.restrictScalars a).obj G))) _
    (moduleSheafFunctor_map_compIso_hom_app (inv a) a (IsIso.hom_inv_id a) _)
    (tensorSheafUniversalPairing ((SheafOfModules.restrictScalars a).obj F)
      ((SheafOfModules.restrictScalars a).obj G)).1 _) ?_
  exact universalPairing_comp_tensorSheafRestrictScalarsHom a F G

/-- The inverse of the comparison of the two tensor products followed by the comparison is the
identity. Restriction of scalars along an isomorphism is full, so this composite is the
restriction of a morphism out of `F ⊗_{A₂} G`, and the universal property over `A₂` identifies
that morphism with the identity. -/
private lemma tensorSheafRestrictScalarsInv_comp_hom :
    tensorSheafRestrictScalarsInv a F G ≫ tensorSheafRestrictScalarsHom a F G = 𝟙 _ := by
  obtain ⟨k, hk⟩ := (SheafOfModules.restrictScalars a).map_surjective
    ((restrictForthIso a).hom.app ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨A₁, Presheaf.isSheaf_of_isSheaf_comp _ A₁ (forget₂ CommRingCat RingCat) h₁⟩).obj
        ((SheafOfModules.restrictScalars a).obj F)).obj
        ((SheafOfModules.restrictScalars a).obj G))) ≫
      tensorSheafRestrictScalarsHom a F G)
  have hfinal := prod_map_compIso_inv_app_comp a (inv a) (IsIso.inv_hom_id a) F G _ _ _
    (universalPairing_comp_moduleSheafFunctor_map a F G k hk)
  have key : bilinearEquivTensorSheafHom (hA := h₂) (tensorRestrictInvPairing a F G) ≫ k =
      𝟙 ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨A₂, Presheaf.isSheaf_of_isSheaf_comp _ A₂
          (forget₂ CommRingCat RingCat) h₂⟩).obj F).obj G)) := by
    refine (bilinearEquivTensorSheafHom (hA := h₂) (F := F) (G := G)
      (N := (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨A₂, Presheaf.isSheaf_of_isSheaf_comp _ A₂
          (forget₂ CommRingCat RingCat) h₂⟩).obj F).obj G))).symm.injective ?_
    refine Eq.trans (bilinearEquivTensorSheafHom_symm_naturality (hA := h₂) _ _) ?_
    refine Subtype.ext ?_
    exact Eq.trans (congrArg (fun z ↦ z ≫
        (Sheaf.moduleSheafFunctor (commRingSheaf J A₂ h₂)).map k)
      (congrArg Subtype.val (Equiv.symm_apply_apply
        (bilinearEquivTensorSheafHom (hA := h₂) (F := F) (G := G)
          (N := (SheafOfModules.restrictScalars (inv a)).obj
            ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨A₁, Presheaf.isSheaf_of_isSheaf_comp _ A₁
                (forget₂ CommRingCat RingCat) h₁⟩).obj
                ((SheafOfModules.restrictScalars a).obj F)).obj
                ((SheafOfModules.restrictScalars a).obj G)))))
        (tensorRestrictInvPairing a F G)))) hfinal
  change ((SheafOfModules.restrictScalars a).map
        (bilinearEquivTensorSheafHom (hA := h₂) (tensorRestrictInvPairing a F G)) ≫
      (restrictForthIso a).hom.app _) ≫ tensorSheafRestrictScalarsHom a F G = 𝟙 _
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun m ↦ (SheafOfModules.restrictScalars a).map
    (bilinearEquivTensorSheafHom (hA := h₂) (tensorRestrictInvPairing a F G)) ≫ m) hk.symm) ?_
  refine Eq.trans ((SheafOfModules.restrictScalars a).map_comp _ _).symm ?_
  refine Eq.trans (congrArg (SheafOfModules.restrictScalars a).map key) ?_
  exact (SheafOfModules.restrictScalars a).map_id _

/-- **The comparison of the two tensor products is an isomorphism when the morphism of sheaves of
rings is.** For an isomorphism `a : A₁ ⟶ A₂` of sheaves of rings and sheaves of `A₂`-modules `F`
and `G`, the lax structure map
`(F|_{A₁}) ⊗_{A₁} (G|_{A₁}) ⟶ (F ⊗_{A₂} G)|_{A₁}` of restriction of scalars is invertible:
restriction of scalars along an isomorphism is an equivalence, and it carries the universal
property of the tensor product over `A₂` to the universal property over `A₁`. -/
instance isIso_tensorSheafRestrictScalarsHom :
    IsIso (tensorSheafRestrictScalarsHom a F G) :=
  ⟨⟨tensorSheafRestrictScalarsInv a F G, tensorSheafRestrictScalarsHom_comp_inv a F G,
    tensorSheafRestrictScalarsInv_comp_hom a F G⟩⟩

end TensorRingIso

end Stacks.SheafOfModules

end
