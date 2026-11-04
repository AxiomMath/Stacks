module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import Mathlib.CategoryTheory.Products.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Comparing two iterated 2-fibre products along diagonals (Stacks 02XF)

We work in the (2,1)-category of categories, with `×` denoting the explicit 2-fibre product of
Example 003R, i.e. Mathlib's `CategoryTheory.Limits.CategoricalPullback`: objects of
`CategoricalPullback F G` for `F : A ⥤ T`, `G : B ⥤ T` are triples `(a, b, f)` with
`f : F a ≅ G b`, and morphisms are pairs `(α, β)` with `F α ≫ f' = f ≫ G β`.

Let `G₁, G₂ : 𝒞 ⥤ 𝒮` and write `G₁ × G₂ : 𝒞 ⥤ 𝒮 × 𝒮` for `c ↦ (G₁ c, G₂ c)` and `Δ` for a
diagonal functor. Put `P := 𝒞 ×_𝒮 𝒞 = CategoricalPullback G₁ G₂`, let
`(p, q) : P ⥤ 𝒞 × 𝒞` be its combined projection, and form
* the source `P ×_{𝒞 × 𝒞} 𝒞` of the comparison, along `Δ : 𝒞 ⥤ 𝒞 × 𝒞`, and
* the target `𝒞 ×_{𝒮 × 𝒮} 𝒮`, along `Δ : 𝒮 ⥤ 𝒮 × 𝒮`,
the latter being the explicit model of the 2-fibre product of `G₁ × G₂` and `Δ`.

The comparison functor sends `((c₁, c₂, φ), c₃, ψ)` to `(c₃, G₁ c₁, (G₁ ψ₁⁻¹, φ⁻¹ ∘ G₂ ψ₂⁻¹))`
and `((α₁, α₂), α₃)` to `(α₃, G₁ α₁)`, and the content of the tag is that it is an equivalence.

The literal source statement claims a canonical *isomorphism* of categories; that is incorrect
(Stacks Section 4.31 comments #5394, #5627) and only an equivalence holds. For a counterexample
to a strict isomorphism take `𝒞` terminal and `𝒮` the walking-isomorphism groupoid with
`G₁ = G₂`: the target then has two objects and the source one, so no functor between them is
bijective on objects, although both are equivalent to the terminal category. Accordingly the
formalization asserts the equivalence, proved by showing the comparison functor faithful, full
and essentially surjective. Faithfulness and fullness rest on the observation that the
`P`-component `(α₁, α₂)` of a morphism of the source is determined by its `𝒞`-component `α₃`,
since the defining square reads `αᵢ = (ψᵢ)_X ≫ α₃ ≫ (ψᵢ)_Y⁻¹`.
-/

@[expose] public section


universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Limits.CategoricalPullback

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]
variable {𝒞 : Type u₂} [Category.{v₂} 𝒞]
variable (G₁ G₂ : 𝒞 ⥤ 𝒮)

/-- The combined projection `(p, q) : 𝒞 ×_𝒮 𝒞 ⥤ 𝒞 × 𝒞` of a 2-fibre product. -/
abbrev projProd : CategoricalPullback G₁ G₂ ⥤ 𝒞 × 𝒞 :=
  (π₁ G₁ G₂).prod' (π₂ G₁ G₂)

/-- The source of the comparison functor of Stacks 02XF: `(𝒞 ×_𝒮 𝒞) ×_{𝒞 × 𝒞} 𝒞`, the 2-fibre
product of `(p, q)` and the diagonal of `𝒞`. -/
abbrev diagComparisonSource : Type _ :=
  CategoricalPullback (projProd G₁ G₂) (Functor.diag 𝒞)

/-- The target of the comparison functor of Stacks 02XF: the explicit model
`𝒞 ×_{𝒮 × 𝒮} 𝒮` of the 2-fibre product of `G₁ × G₂` and the diagonal of `𝒮`. Its objects are
triples `(c, s, φ)` with `φ : (G₁ c, G₂ c) ≅ (s, s)`. -/
abbrev diagComparisonTarget : Type _ :=
  CategoricalPullback (G₁.prod' G₂) (Functor.diag 𝒮)

/-- The first structural isomorphism `ψ₁ : c₁ ≅ c₃` of an object of `diagComparisonSource`. -/
def diagComparisonFstIso (X : diagComparisonSource G₁ G₂) : X.fst.fst ≅ X.snd :=
  (CategoryTheory.Prod.fst 𝒞 𝒞).mapIso X.iso

/-- The second structural isomorphism `ψ₂ : c₂ ≅ c₃` of an object of `diagComparisonSource`. -/
def diagComparisonSndIso (X : diagComparisonSource G₁ G₂) : X.fst.snd ≅ X.snd :=
  (CategoryTheory.Prod.snd 𝒞 𝒞).mapIso X.iso

/-- Naturality of a family of isomorphisms, in terms of inverses. -/
private theorem comp_inv_eq_inv_comp_of_comp_hom_eq {C : Type*} [Category C] {a b a' b' : C}
    (eX : a ≅ b) (eY : a' ≅ b') {f : a ⟶ a'} {g : b ⟶ b'}
    (h : f ≫ eY.hom = eX.hom ≫ g) : g ≫ eY.inv = eX.inv ≫ f := by
  rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq, h]

/-- A morphism `k` is recovered from `g` and isomorphisms `eX`, `eY` as `eX ≫ g ≫ eY⁻¹`. -/
private theorem eq_hom_comp_comp_inv_of_comp_inv_eq {C : Type*} [Category C] {a b a' b' : C}
    (eX : a ≅ b) (eY : a' ≅ b') {g : a ⟶ a'} {k : b ⟶ b'}
    (h : k ≫ eY.inv = eX.inv ≫ g) : g = eX.hom ≫ k ≫ eY.inv := by
  rw [h, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- Naturality of `diagComparisonFstIso`, in terms of inverses. -/
lemma diagComparisonFstIso_inv_naturality {X Y : diagComparisonSource G₁ G₂} (f : X ⟶ Y) :
    f.snd ≫ (diagComparisonFstIso G₁ G₂ Y).inv =
      (diagComparisonFstIso G₁ G₂ X).inv ≫ f.fst.fst :=
  comp_inv_eq_inv_comp_of_comp_hom_eq _ _ (congrArg (·.1) f.w)

/-- Naturality of `diagComparisonSndIso`, in terms of inverses. -/
lemma diagComparisonSndIso_inv_naturality {X Y : diagComparisonSource G₁ G₂} (f : X ⟶ Y) :
    f.snd ≫ (diagComparisonSndIso G₁ G₂ Y).inv =
      (diagComparisonSndIso G₁ G₂ X).inv ≫ f.fst.snd :=
  comp_inv_eq_inv_comp_of_comp_hom_eq _ _ (congrArg (·.2) f.w)

/-- **Stacks 02XF.** The comparison functor `(𝒞 ×_𝒮 𝒞) ×_{𝒞 × 𝒞} 𝒞 ⥤ 𝒞 ×_{𝒮 × 𝒮} 𝒮`. On objects
it sends `((c₁, c₂, φ), c₃, ψ)` to `(c₃, G₁ c₁, (G₁ ψ₁⁻¹, φ⁻¹ ∘ G₂ ψ₂⁻¹))`, and on morphisms
`((α₁, α₂), α₃)` to `(α₃, G₁ α₁)`. -/
@[stacks 02XF, implicit_reducible]
def diagComparison : diagComparisonSource G₁ G₂ ⥤ diagComparisonTarget G₁ G₂ where
  obj X :=
    { fst := X.snd
      snd := G₁.obj X.fst.fst
      iso := (G₁.mapIso (diagComparisonFstIso G₁ G₂ X).symm).prod
              ((G₂.mapIso (diagComparisonSndIso G₁ G₂ X).symm) ≪≫ X.fst.iso.symm) }
  map {X Y} f :=
    { fst := f.snd
      snd := G₁.map f.fst.fst
      w := by
        apply Prod.ext
        · simp only [Functor.prod'_map, Functor.diag_map, prod_comp_fst, Iso.prod_hom,
            Functor.mapIso_hom, Iso.symm_hom]
          rw [← G₁.map_comp, ← G₁.map_comp, diagComparisonFstIso_inv_naturality]
        · simp only [Functor.prod'_map, Functor.diag_map, prod_comp_snd, Iso.prod_hom,
            Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
          have hp : G₂.map f.fst.snd ≫ Y.fst.iso.inv
                  = X.fst.iso.inv ≫ G₁.map f.fst.fst := by
            rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]; exact f.fst.w.symm
          rw [← G₂.map_comp_assoc, diagComparisonSndIso_inv_naturality, G₂.map_comp,
            Category.assoc, hp] }
  map_id := by
    intro X
    apply hom_ext <;> simp
  map_comp := by
    intro X Y Z f g
    apply hom_ext <;> simp

/-- The `𝒮`-component of the comparison functor on a morphism is `G₁ α₁`. -/
@[simp] lemma diagComparison_map_snd {X Y : diagComparisonSource G₁ G₂} (f : X ⟶ Y) :
    ((diagComparison G₁ G₂).map f).snd = G₁.map f.fst.fst := rfl

/-- The `fst.fst` component `α₁` of a morphism of `diagComparisonSource` is determined by its
`snd` component `α₃`: it is `(ψ₁)_X ≫ α₃ ≫ (ψ₁)_Y⁻¹`. -/
lemma diagComparisonSource_hom_fst_fst {X Y : diagComparisonSource G₁ G₂} (f : X ⟶ Y) :
    f.fst.fst = (diagComparisonFstIso G₁ G₂ X).hom ≫ f.snd ≫
      (diagComparisonFstIso G₁ G₂ Y).inv :=
  eq_hom_comp_comp_inv_of_comp_inv_eq _ _ (diagComparisonFstIso_inv_naturality G₁ G₂ f)

/-- The `fst.snd` component `α₂` of a morphism of `diagComparisonSource` is determined by its
`snd` component `α₃`: it is `(ψ₂)_X ≫ α₃ ≫ (ψ₂)_Y⁻¹`. -/
lemma diagComparisonSource_hom_fst_snd {X Y : diagComparisonSource G₁ G₂} (f : X ⟶ Y) :
    f.fst.snd = (diagComparisonSndIso G₁ G₂ X).hom ≫ f.snd ≫
      (diagComparisonSndIso G₁ G₂ Y).inv :=
  eq_hom_comp_comp_inv_of_comp_inv_eq _ _ (diagComparisonSndIso_inv_naturality G₁ G₂ f)

/-- The comparison functor is faithful: the `𝒞`-component of a morphism is read off from its
image, and it determines the two `P`-components. -/
instance faithful_diagComparison : (diagComparison G₁ G₂).Faithful where
  map_injective {X Y f g} h := by
    have hr : f.snd = g.snd := congrArg Hom.fst h
    refine hom_ext (hom_ext ?_ ?_) hr
    · rw [diagComparisonSource_hom_fst_fst, diagComparisonSource_hom_fst_fst, hr]
    · rw [diagComparisonSource_hom_fst_snd, diagComparisonSource_hom_fst_snd, hr]

/-- The comparison functor is full: a morphism `(g, h)` of the target has a unique possible
preimage, namely the morphism with `𝒞`-component `g` and `P`-components
`(ψᵢ)_X ≫ g ≫ (ψᵢ)_Y⁻¹`, and the two squares it must satisfy are exactly the two `𝒮 × 𝒮`
components of the square satisfied by `(g, h)`. -/
instance full_diagComparison : (diagComparison G₁ G₂).Full where
  map_surjective {X Y} h := by
    have hw1 := congrArg (·.1) h.w
    have hw2 := congrArg (·.2) h.w
    simp only [Functor.prod'_map, Functor.diag_map, prod_comp_fst, prod_comp_snd,
      Functor.diag_obj] at hw1 hw2
    have e1 : G₁.map h.fst ≫ G₁.map (diagComparisonFstIso G₁ G₂ Y).inv
            = G₁.map (diagComparisonFstIso G₁ G₂ X).inv ≫ h.snd := hw1
    have e2 : G₂.map h.fst ≫ (G₂.map (diagComparisonSndIso G₁ G₂ Y).inv ≫ Y.fst.iso.inv)
            = (G₂.map (diagComparisonSndIso G₁ G₂ X).inv ≫ X.fst.iso.inv) ≫ h.snd := hw2
    refine ⟨{ fst := { fst := (diagComparisonFstIso G₁ G₂ X).hom ≫ h.fst ≫
                          (diagComparisonFstIso G₁ G₂ Y).inv
                       snd := (diagComparisonSndIso G₁ G₂ X).hom ≫ h.fst ≫
                          (diagComparisonSndIso G₁ G₂ Y).inv
                       w := ?_ }
              snd := h.fst
              w := ?_ }, ?_⟩
    · have hr : h.snd
              = G₁.map ((diagComparisonFstIso G₁ G₂ X).hom ≫ h.fst ≫
                  (diagComparisonFstIso G₁ G₂ Y).inv) := by
        rw [G₁.map_comp, G₁.map_comp, e1, ← Category.assoc, ← G₁.map_comp, Iso.hom_inv_id,
            G₁.map_id, Category.id_comp]
      have e2' : G₂.map h.fst ≫ G₂.map (diagComparisonSndIso G₁ G₂ Y).inv ≫ Y.fst.iso.inv
               = G₂.map (diagComparisonSndIso G₁ G₂ X).inv ≫ X.fst.iso.inv ≫ h.snd := by
        simpa only [Category.assoc] using e2
      have key2 : G₂.map ((diagComparisonSndIso G₁ G₂ X).hom ≫ h.fst ≫
                    (diagComparisonSndIso G₁ G₂ Y).inv) ≫ Y.fst.iso.inv
                = X.fst.iso.inv ≫ h.snd := by
        rw [G₂.map_comp, G₂.map_comp]
        simp only [Category.assoc]
        rw [e2', ← Category.assoc, ← G₂.map_comp, Iso.hom_inv_id, G₂.map_id, Category.id_comp]
      rw [← hr]
      rw [Iso.comp_inv_eq] at key2
      rw [key2, ← Category.assoc, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    · apply Prod.ext
      -- The square is stated through `π₁`/`π₂` of `projProd`; restate it on `ψ₁`/`ψ₂`.
      · change ((diagComparisonFstIso G₁ G₂ X).hom ≫ h.fst ≫
              (diagComparisonFstIso G₁ G₂ Y).inv) ≫ (diagComparisonFstIso G₁ G₂ Y).hom
              = (diagComparisonFstIso G₁ G₂ X).hom ≫ h.fst
        rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      · change ((diagComparisonSndIso G₁ G₂ X).hom ≫ h.fst ≫
              (diagComparisonSndIso G₁ G₂ Y).inv) ≫ (diagComparisonSndIso G₁ G₂ Y).hom
              = (diagComparisonSndIso G₁ G₂ X).hom ≫ h.fst
        rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · apply hom_ext
      · rfl
      · rw [diagComparison_map_snd, G₁.map_comp, G₁.map_comp, e1, ← Category.assoc,
          ← G₁.map_comp, Iso.hom_inv_id, G₁.map_id, Category.id_comp]

-- `(Y.fst, Y.fst)` is `(projProd G₁ G₂).obj ⟨…⟩` only past Mathlib's plain `def`s `π₁`, `π₂`.
set_option backward.isDefEq.respectTransparency false in
/-- The comparison functor is essentially surjective: an object `(c, s, (φ₁, φ₂))` of the target
is the image, up to the isomorphism with components `(𝟙, φ₁)`, of the source object
`((c, c, φ₁ ∘ φ₂⁻¹), c, 𝟙)`. -/
instance essSurj_diagComparison : (diagComparison G₁ G₂).EssSurj where
  mem_essImage Y := by
    refine ⟨{ fst := { fst := Y.fst, snd := Y.fst,
                       iso := ((CategoryTheory.Prod.fst 𝒮 𝒮).mapIso Y.iso)
                              ≪≫ ((CategoryTheory.Prod.snd 𝒮 𝒮).mapIso Y.iso).symm }
              snd := Y.fst
              -- The identity is pinned at `(Y.fst, Y.fst)`: with `Iso.refl _` the object it is
              -- taken at is spelled `(projProd G₁ G₂).obj ⟨…⟩`, and then the `𝟙` that surfaces
              -- downstream is invisible to `Functor.map_id` (`rw`/`simp` unify at reducible
              -- transparency, which no longer unfolds the plain `def` `π₂`).
              iso := Iso.refl (Y.fst, Y.fst) }, ⟨?_⟩⟩
    refine mkIso (Iso.refl _) ((CategoryTheory.Prod.fst 𝒮 𝒮).mapIso Y.iso) ?_
    apply Prod.ext
    · simp [diagComparison, diagComparisonFstIso, diagComparisonSndIso]
    · simp only [diagComparison, diagComparisonFstIso, diagComparisonSndIso]
      have h : Y.iso.inv.1 ≫ Y.iso.hom.1 = 𝟙 _ := congrArg (·.1) Y.iso.inv_hom_id
      simp [h]

/-- **Stacks 02XF.** The comparison functor `(𝒞 ×_𝒮 𝒞) ×_{𝒞 × 𝒞} 𝒞 ⥤ 𝒞 ×_{𝒮 × 𝒮} 𝒮` is an
equivalence of categories. (The source asserts an isomorphism of categories; that is corrected to
an equivalence per the Stacks comments #5394 and #5627, since the functor is in general not
bijective on objects.) -/
@[stacks 02XF]
theorem isEquivalence_diagComparison : (diagComparison G₁ G₂).IsEquivalence :=
  { }

end CategoryTheory.Limits.CategoricalPullback
