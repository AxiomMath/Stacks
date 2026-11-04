module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Yoneda
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability

/-!
# The lower shriek of the structure sheaf of a full subcategory of a big site

Let `X` be a scheme and let `C₁ ⊆ C₂` be full subcategories of the big fppf category over `X`,
each carrying the topology inherited from a topology on the ambient category, and write
`g : Sh(C₁) ⟶ Sh(C₂)` for the morphism of topoi of the inclusion. The structure sheaf `O` of the
ambient site has sections `O(V) = Γ(V, O_V)`, and `O_t` denotes its restriction to `C_t`.

This file proves that the canonical map

`g_!O₁ ⟶ O₂`

is an isomorphism provided `C₁` contains the affine line and the affine plane over `X`, where
`g_!` is the lower shriek on abelian sheaves — the left adjoint of restriction along the
inclusion. This is part (b) of **Stacks 07AJ**. At the level of presheaves it says that `O₂` is
the left Kan extension of `O₁` along the inclusion, which holds because `O` is represented by
the affine line and `O × O` by the affine plane.

## Main definitions

* `CategoryTheory.Presheaf.classify`: the morphism to a representing object classifying a
  section of a presheaf of abelian groups.
* `CategoryTheory.Presheaf.extend`: the extension of a morphism of restricted presheaves to the
  whole presheaf, along the classifying morphisms.
* `AlgebraicGeometry.bigOverPresheafAb`: the structure presheaf of abelian groups of the big
  fppf category over `X`.
* `AlgebraicGeometry.structureSheafAb`: its restriction to a full subcategory, as a sheaf.
* `AlgebraicGeometry.lowerShriekStructureSheafHom`: the canonical map `g_!O₁ ⟶ O₂`.

## Main results

* `CategoryTheory.Presheaf.bijective_whiskerLeft`: restriction along a fully faithful functor is
  bijective on morphisms out of a presheaf of abelian groups represented, together with its
  square, by objects of the source.
* `AlgebraicGeometry.bijective_map_coord`: affine `n`-space over `X`, when present in the big
  fppf category over `X`, represents the `n`-fold product of the structure presheaf.
* `AlgebraicGeometry.bijective_whiskerLeft_bigOverPresheafAb`: **Stacks 07AJ (b)** at the level
  of presheaves — the structure presheaf of `C₂` is the left Kan extension of that of `C₁`.
* `AlgebraicGeometry.isIso_lowerShriekStructureSheafHom`: **Stacks 07AJ (b)** — the canonical map
  `g_!O₁ ⟶ O₂` is an isomorphism.

## References

* [Stacks Project, Tag 04BF](https://stacks.math.columbia.edu/tag/04BF)
* [Stacks Project, Tag 04BG](https://stacks.math.columbia.edu/tag/04BG)
* [Stacks Project, Tag 0789](https://stacks.math.columbia.edu/tag/0789)
* [Stacks Project, Tag 0798](https://stacks.math.columbia.edu/tag/0798)
* [Stacks Project, Tag 07AJ](https://stacks.math.columbia.edu/tag/07AJ)
-/

@[expose] public section

open CategoryTheory Opposite

namespace CategoryTheory.Presheaf

universe w v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {O : Dᵒᵖ ⥤ AddCommGrpCat.{w}}

section Classify

variable {A : C} {s : O.obj (op (F.obj A))}
  (hs : ∀ V : D, Function.Bijective fun f : V ⟶ F.obj A => (O.map f.op) s)

/-- The morphism to `F.obj A` classifying a section. -/
noncomputable def classify {V : D} (h : O.obj (op V)) : V ⟶ F.obj A :=
  (Equiv.ofBijective _ (hs V)).symm h

/-- The classifying morphism of a section pulls the universal section back to it. -/
@[simp]
lemma map_classify {V : D} (h : O.obj (op V)) : (O.map (classify hs h).op) s = h :=
  (Equiv.ofBijective _ (hs V)).apply_symm_apply h

/-- Every morphism to the representing object is the classifying morphism of the section it
pulls the universal section back to. -/
lemma classify_map {V : D} (f : V ⟶ F.obj A) : classify hs ((O.map f.op) s) = f :=
  (Equiv.ofBijective _ (hs V)).symm_apply_apply f

/-- Classifying morphisms are natural: precomposing the classifying morphism of a section with
a morphism classifies the restricted section. -/
lemma comp_classify {W V : D} (g : W ⟶ V) (h : O.obj (op V)) :
    g ≫ classify hs h = classify hs ((O.map g.op) h) := by
  refine (hs W).injective ?_
  change (O.map (g ≫ classify hs h).op) s = (O.map (classify hs ((O.map g.op) h)).op) s
  rw [map_classify, op_comp, Functor.map_comp]
  change (O.map g.op) ((O.map (classify hs h).op) s) = _
  rw [map_classify]

end Classify

section Extend

variable {A A' : C} {s : O.obj (op (F.obj A))} {x₀ x₁ : O.obj (op (F.obj A'))}
  {G : Dᵒᵖ ⥤ AddCommGrpCat.{w}}
  (hs : ∀ V : D, Function.Bijective fun f : V ⟶ F.obj A => (O.map f.op) s)
  (hs' : ∀ V : D,
    Function.Bijective fun f : V ⟶ F.obj A' => ((O.map f.op) x₀, (O.map f.op) x₁))

/-- The morphism to `F.obj A'` classifying a pair of sections. -/
noncomputable def classifyPair {V : D} (h₀ h₁ : O.obj (op V)) : V ⟶ F.obj A' :=
  (Equiv.ofBijective _ (hs' V)).symm (h₀, h₁)

/-- The morphism classifying a pair of sections pulls the first universal section back to the
first member of the pair. -/
@[simp]
lemma map_classifyPair_fst {V : D} (h₀ h₁ : O.obj (op V)) :
    (O.map (classifyPair hs' h₀ h₁).op) x₀ = h₀ :=
  (Prod.ext_iff.mp ((Equiv.ofBijective _ (hs' V)).apply_symm_apply (h₀, h₁))).1

/-- The morphism classifying a pair of sections pulls the second universal section back to the
second member of the pair. -/
@[simp]
lemma map_classifyPair_snd {V : D} (h₀ h₁ : O.obj (op V)) :
    (O.map (classifyPair hs' h₀ h₁).op) x₁ = h₁ :=
  (Prod.ext_iff.mp ((Equiv.ofBijective _ (hs' V)).apply_symm_apply (h₀, h₁))).2

include hs in
/-- **Restriction along a fully faithful functor is injective on morphisms out of a represented
presheaf of abelian groups.** A morphism out of `O` is determined by its value at the universal
section. -/
lemma injective_whiskerLeft :
    Function.Injective fun β : O ⟶ G => Functor.whiskerLeft F.op β := by
  intro β₁ β₂ hβ
  refine NatTrans.ext (funext fun X => ?_)
  obtain ⟨V⟩ := X
  have key : β₁.app (op (F.obj A)) s = β₂.app (op (F.obj A)) s :=
    congrArg (fun γ : F.op ⋙ O ⟶ F.op ⋙ G => γ.app (op A) s) hβ
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun h => ?_)
  rw [← map_classify hs h, NatTrans.naturality_apply, NatTrans.naturality_apply, key]

variable [F.Full] (α : F.op ⋙ O ⟶ F.op ⋙ G)

include hs in
/-- The value of the prospective extension at a classified section is computed by `α` already
at the classifying object, whatever object of `C` the section was classified by. -/
lemma map_classify_map_apply {A'' : C} {V : D} (ψ : V ⟶ F.obj A'')
    (t : O.obj (op (F.obj A''))) :
    (G.map (classify hs ((O.map ψ.op) t)).op) (α.app (op A) s) =
      (G.map ψ.op) (α.app (op A'') t) := by
  obtain ⟨c, hc⟩ : ∃ c : A'' ⟶ A, F.map c = classify hs t :=
    ⟨F.preimage _, F.map_preimage _⟩
  have h₁ : classify hs ((O.map ψ.op) t) = ψ ≫ F.map c := by
    rw [hc, comp_classify]
  have h₂ : α.app (op A'') t = (G.map (F.map c).op) (α.app (op A) s) := by
    rw [← show (O.map (F.map c).op) s = t by rw [hc, map_classify]]
    exact NatTrans.naturality_apply α c.op s
  rw [h₁, h₂, op_comp, Functor.map_comp]
  rfl

include hs hs' in
/-- The prospective extension is additive: transporting `α.app (op A) s` along the morphism
classifying `h₀ + h₁` gives the sum of its transports along the morphisms classifying `h₀` and
`h₁`. -/
lemma map_classify_add_apply {V : D} (h₀ h₁ : O.obj (op V)) :
    (G.map (classify hs (h₀ + h₁)).op) (α.app (op A) s) =
      (G.map (classify hs h₀).op) (α.app (op A) s) +
        (G.map (classify hs h₁).op) (α.app (op A) s) := by
  set ψ := classifyPair hs' h₀ h₁
  have e₀ : (O.map ψ.op) x₀ = h₀ := map_classifyPair_fst hs' h₀ h₁
  have e₁ : (O.map ψ.op) x₁ = h₁ := map_classifyPair_snd hs' h₀ h₁
  have esum : (O.map ψ.op) (x₀ + x₁) = h₀ + h₁ := by rw [map_add, e₀, e₁]
  rw [← esum, ← e₀, ← e₁, map_classify_map_apply hs α ψ (x₀ + x₁),
    map_classify_map_apply hs α ψ x₀, map_classify_map_apply hs α ψ x₁, map_add, map_add]

/-- The extension of `α` to all of `O`: a section `h` of `O` over `V` is sent to the value of
`α` at the universal section, transported along the morphism classifying `h`. -/
noncomputable def extend : O ⟶ G where
  app Y := AddCommGrpCat.ofHom (AddMonoidHom.mk'
    (fun h : O.obj Y => (G.map (classify hs (V := Y.unop) h).op) (α.app (op A) s))
    (fun h₀ h₁ => map_classify_add_apply hs hs' α (V := Y.unop) h₀ h₁))
  naturality Y Y' g := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun h => ?_)
    change (G.map (classify hs (V := Y'.unop) ((O.map g) h)).op) (α.app (op A) s) =
      (G.map g) ((G.map (classify hs (V := Y.unop) h).op) (α.app (op A) s))
    have e : classify hs (V := Y'.unop) ((O.map g) h) =
        g.unop ≫ classify hs (V := Y.unop) h := (comp_classify hs g.unop h).symm
    rw [e, op_comp, Functor.map_comp]
    rfl

/-- The extension evaluated at a section, by definition. -/
@[simp]
lemma extend_app_apply {V : D} (h : O.obj (op V)) :
    (extend hs hs' α).app (op V) h = (G.map (classify hs h).op) (α.app (op A) s) := rfl

include hs hs' in
/-- The extension restricts to the morphism it extends. -/
lemma whiskerLeft_extend : Functor.whiskerLeft F.op (extend hs hs' α) = α := by
  refine NatTrans.ext (funext fun X => ?_)
  obtain ⟨U⟩ := X
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun h => ?_)
  change (G.map (classify hs (V := F.obj U) h).op) (α.app (op A) s) = α.app (op U) h
  simpa using map_classify_map_apply hs α (𝟙 (F.obj U)) h

include hs hs' in
/-- **Restriction along a fully faithful functor is bijective on morphisms out of a presheaf of
abelian groups that is represented, together with its square, by objects of the source.**
Equivalently: such a presheaf is the left Kan extension of its own restriction.

Here `A` carries a section `s` of `O` whose classifying maps exhaust `Hom(-, F.obj A)`, so that
`O` is represented by `F.obj A`, and `A'` carries a pair of sections representing `O × O`. -/
theorem bijective_whiskerLeft :
    Function.Bijective fun β : O ⟶ G => Functor.whiskerLeft F.op β :=
  ⟨injective_whiskerLeft hs, fun α => ⟨extend hs hs' α, whiskerLeft_extend hs hs' α⟩⟩

end Extend

end CategoryTheory.Presheaf

/-! ## The structure presheaf of the big site of a scheme -/

namespace AlgebraicGeometry

open AffineSpace CategoryTheory.Presheaf

universe t

variable (B : BigFppfSite.{t}) (X : Scheme.{t}) (hX : B.Contains X)

/-- The structure presheaf of abelian groups of the big fppf category over `X`: its sections
over `V/X` are the global functions on `V`, with their additive group structure. -/
noncomputable abbrev bigOverPresheafAb : (BigFppfOver B X hX)ᵒᵖ ⥤ AddCommGrpCat.{t} :=
  (BigFppfOver.toScheme B X hX).op ⋙ Scheme.Γ ⋙
    forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat

/-- The structure morphism to `X` of an object of the big fppf category over `X`. -/
abbrev BigFppfOver.str (V : BigFppfOver B X hX) :
    (BigFppfOver.toScheme B X hX).obj V ⟶ X :=
  B.inclusion.map V.hom

section Represent

variable {B X hX} {n : Type t} {A : BigFppfOver B X hX}
  (e : (BigFppfOver.toScheme B X hX).obj A ≅ 𝔸(n; X))
  (he : e.hom ≫ 𝔸(n; X) ↘ X = BigFppfOver.str B X hX A)

include he in
/-- **Affine `n`-space over `X`, when it is present in the big fppf category over `X`,
represents the `n`-fold product of the structure presheaf.** A morphism of the site into it is
the same thing as an `n`-tuple of global functions on the source: the tuple of pullbacks of the
standard coordinates. -/
lemma bijective_map_coord (V : BigFppfOver B X hX) :
    Function.Bijective fun f : V ⟶ A => fun i : n =>
      ((BigFppfOver.toScheme B X hX).map f).appTop (e.hom.appTop (coord X i)) := by
  have hw : ∀ {V' : BigFppfOver B X hX} (f : V' ⟶ A),
      (BigFppfOver.toScheme B X hX).map f ≫ BigFppfOver.str B X hX A =
        BigFppfOver.str B X hX V' := by
    intro V' f
    calc (BigFppfOver.toScheme B X hX).map f ≫ BigFppfOver.str B X hX A
        = B.inclusion.map (f.left ≫ A.hom) := by rw [B.inclusion.map_comp]; rfl
      _ = BigFppfOver.str B X hX V' := by rw [Over.w]
  refine ⟨fun f₁ f₂ hf => BigFppfOver.map_toScheme_injective B X hX ?_, fun v => ?_⟩
  · have key : (BigFppfOver.toScheme B X hX).map f₁ ≫ e.hom =
        (BigFppfOver.toScheme B X hX).map f₂ ≫ e.hom := by
      refine AffineSpace.hom_ext ?_ fun i => ?_
      · rw [Category.assoc, Category.assoc, he, hw f₁, hw f₂]
      · simp only [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply]
        exact congrFun hf i
    simpa using congrArg (fun g => g ≫ e.inv) key
  · have w : (homOfVector (BigFppfOver.str B X hX V) v ≫ e.inv) ≫
        BigFppfOver.str B X hX A = BigFppfOver.str B X hX V := by
      rw [← he, Category.assoc, Iso.inv_hom_id_assoc, homOfVector_over]
    refine ⟨Over.homMk (ObjectProperty.homMk
      (homOfVector (BigFppfOver.str B X hX V) v ≫ e.inv))
      (by apply ObjectProperty.hom_ext; exact w), ?_⟩
    funext i
    change ((homOfVector (BigFppfOver.str B X hX V) v ≫ e.inv)).appTop
      (e.hom.appTop (coord X i)) = v i
    rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, Category.assoc,
      Iso.inv_hom_id, Category.comp_id, homOfVector_appTop_coord]

end Represent

/-- The two-element type `ULift Bool`, indexing the coordinates of the affine plane over `X`. -/
abbrev AffinePlaneIndex := ULift.{t} Bool

/-- Pairs of sections are the same thing as families of sections indexed by the two-element
type `AffinePlaneIndex`. -/
@[simps]
def affinePlaneIndexArrowEquiv (M : Type*) : (AffinePlaneIndex.{t} → M) ≃ M × M where
  toFun u := (u (ULift.up false), u (ULift.up true))
  invFun p b := bif b.down then p.2 else p.1
  left_inv u := by funext b; obtain ⟨b⟩ := b; cases b <;> rfl
  right_inv p := rfl

section Restriction

variable {B X hX} (P₁ P₂ : ObjectProperty (BigFppfOver B X hX)) (h₁₂ : P₁ ≤ P₂)
  {A A' : P₁.FullSubcategory}
  (e : (BigFppfOver.toScheme B X hX).obj A.obj ≅ 𝔸(PUnit.{t + 1}; X))
  (he : e.hom ≫ 𝔸(PUnit.{t + 1}; X) ↘ X = BigFppfOver.str B X hX A.obj)
  (e' : (BigFppfOver.toScheme B X hX).obj A'.obj ≅ 𝔸(AffinePlaneIndex.{t}; X))
  (he' : e'.hom ≫ 𝔸(AffinePlaneIndex.{t}; X) ↘ X = BigFppfOver.str B X hX A'.obj)

include he in
/-- The affine line over `X`, present in `C₁`, represents the structure presheaf of `C₂`. -/
private lemma bijective_line (V : P₂.FullSubcategory) :
    Function.Bijective fun f : V ⟶ (ObjectProperty.ιOfLE h₁₂).obj A =>
      (((P₂.ι).op ⋙ bigOverPresheafAb B X hX).map f.op)
        (e.hom.appTop (coord X PUnit.unit)) := by
  exact (Equiv.funUnique PUnit.{t + 1} _).bijective.comp
    ((bijective_map_coord e he (P₂.ι.obj V)).comp (P₂.fullyFaithfulι.map_bijective _ _))

include he' in
/-- The affine plane over `X`, present in `C₁`, represents the square of the structure presheaf
of `C₂`. -/
private lemma bijective_plane (V : P₂.FullSubcategory) :
    Function.Bijective fun f : V ⟶ (ObjectProperty.ιOfLE h₁₂).obj A' =>
      ((((P₂.ι).op ⋙ bigOverPresheafAb B X hX).map f.op)
          (e'.hom.appTop (coord X (ULift.up false))),
        (((P₂.ι).op ⋙ bigOverPresheafAb B X hX).map f.op)
          (e'.hom.appTop (coord X (ULift.up true)))) := by
  exact (affinePlaneIndexArrowEquiv _).bijective.comp
    ((bijective_map_coord e' he' (P₂.ι.obj V)).comp (P₂.fullyFaithfulι.map_bijective _ _))

include he he' in
/-- **Stacks 07AJ (b), at the level of presheaves of abelian groups.** For full subcategories
`C₁ ⊆ C₂` of the big fppf category over a scheme `X`, if `C₁` contains the affine line and the
affine plane over `X`, then restriction along `C₁ ⊆ C₂` is bijective on morphisms out of the
structure presheaf of `C₂`; that is, the structure presheaf of `C₂` is the left Kan extension
along `C₁ ⊆ C₂` of the structure presheaf of `C₁`. -/
theorem bijective_whiskerLeft_bigOverPresheafAb
    (G : P₂.FullSubcategoryᵒᵖ ⥤ AddCommGrpCat.{t}) :
    Function.Bijective fun β : ((P₂.ι).op ⋙ bigOverPresheafAb B X hX) ⟶ G =>
      Functor.whiskerLeft (ObjectProperty.ιOfLE h₁₂).op β :=
  bijective_whiskerLeft (bijective_line P₁ P₂ h₁₂ e he) (bijective_plane P₁ P₂ h₁₂ e' he')

end Restriction

section Sheaf

variable {B X hX} {P₁ P₂ : ObjectProperty (BigFppfOver B X hX)} (h₁₂ : P₁ ≤ P₂)
  (J₁ : GrothendieckTopology P₁.FullSubcategory)
  (J₂ : GrothendieckTopology P₂.FullSubcategory)
  (hsh : Presheaf.IsSheaf J₂ (P₂.ι.op ⋙ bigOverPresheafAb B X hX))

/-- The structure sheaf of abelian groups of a full subcategory of the big fppf category over
`X`, for a topology in which the structure presheaf is a sheaf. -/
noncomputable def structureSheafAb : Sheaf J₂ AddCommGrpCat.{t} :=
  ⟨P₂.ι.op ⋙ bigOverPresheafAb B X hX, hsh⟩

variable [(ObjectProperty.ιOfLE h₁₂).IsContinuous J₁ J₂]
  [((ObjectProperty.ιOfLE h₁₂).sheafPushforwardContinuous
    AddCommGrpCat.{t} J₁ J₂).IsRightAdjoint]

/-- **The canonical map `g_!O₁ ⟶ O₂` of Stacks 07AJ (b)**: the adjoint transpose, under
`g_! ⊣ g⁻¹`, of the identity of the restricted structure sheaf. Here `g_!` is the lower shriek
on abelian sheaves of **Stacks 04BF**, the left adjoint of restriction along the inclusion of
the full subcategory. -/
noncomputable def lowerShriekStructureSheafHom :
    ((ObjectProperty.ιOfLE h₁₂).sheafPullback AddCommGrpCat.{t} J₁ J₂).obj
        (((ObjectProperty.ιOfLE h₁₂).sheafPushforwardContinuous AddCommGrpCat.{t} J₁ J₂).obj
          (structureSheafAb J₂ hsh)) ⟶
      structureSheafAb J₂ hsh :=
  (((ObjectProperty.ιOfLE h₁₂).sheafAdjunctionContinuous AddCommGrpCat.{t} J₁ J₂).homEquiv
    _ (structureSheafAb J₂ hsh)).symm (𝟙 _)

variable {A A' : P₁.FullSubcategory}
  (e : (BigFppfOver.toScheme B X hX).obj A.obj ≅ 𝔸(PUnit.{t + 1}; X))
  (he : e.hom ≫ 𝔸(PUnit.{t + 1}; X) ↘ X = BigFppfOver.str B X hX A.obj)
  (e' : (BigFppfOver.toScheme B X hX).obj A'.obj ≅ 𝔸(AffinePlaneIndex.{t}; X))
  (he' : e'.hom ≫ 𝔸(AffinePlaneIndex.{t}; X) ↘ X = BigFppfOver.str B X hX A'.obj)

include he he' in
/-- **Stacks 07AJ (b).** For full subcategories `C₁ ⊆ C₂` of the big fppf category over a
scheme `X`, with `C₁` containing the affine line and the affine plane over `X`, the canonical
map `g_!O₁ ⟶ O₂` from the lower shriek of the restricted structure sheaf to the structure sheaf
is an isomorphism. -/
theorem isIso_lowerShriekStructureSheafHom :
    IsIso (lowerShriekStructureSheafHom h₁₂ J₁ J₂ hsh) := by
  set F := ObjectProperty.ιOfLE h₁₂
  set R := F.sheafPushforwardContinuous AddCommGrpCat.{t} J₁ J₂
  set adj := F.sheafAdjunctionContinuous AddCommGrpCat.{t} J₁ J₂
  refine isIso_of_coyoneda_map_bijective _ fun T => ?_
  have hpre := bijective_whiskerLeft_bigOverPresheafAb P₁ P₂ h₁₂ e he e' he' T.obj
  have hres : Function.Bijective fun x : structureSheafAb J₂ hsh ⟶ T => R.map x :=
    ⟨fun x y hxy => Sheaf.hom_ext (hpre.injective
      (congrArg (fun z : R.obj (structureSheafAb J₂ hsh) ⟶ R.obj T => z.hom) hxy)),
    fun y => let ⟨β, hβ⟩ := hpre.surjective y.hom; ⟨ObjectProperty.homMk β, Sheaf.hom_ext hβ⟩⟩
  have hcomp : (fun x : structureSheafAb J₂ hsh ⟶ T =>
        lowerShriekStructureSheafHom h₁₂ J₁ J₂ hsh ≫ x) =
      (adj.homEquiv _ T).symm ∘ fun x : structureSheafAb J₂ hsh ⟶ T => R.map x := by
    funext x
    rw [Function.comp_apply, Equiv.eq_symm_apply, Adjunction.homEquiv_naturality_right,
      lowerShriekStructureSheafHom, Equiv.apply_symm_apply, Category.id_comp]
  rw [hcomp]
  exact (adj.homEquiv _ T).symm.bijective.comp hres

end Sheaf

end AlgebraicGeometry

end
