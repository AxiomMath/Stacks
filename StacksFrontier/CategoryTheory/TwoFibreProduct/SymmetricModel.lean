module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The symmetric model of the 2-fibre product of categories (Stacks 06RL)

Fix categories `𝒜`, `ℬ`, `𝒞` and functors `F : 𝒜 ⥤ 𝒞`, `G : ℬ ⥤ 𝒞`. Besides the standard
construction of the 2-fibre product `𝒜 ×_𝒞 ℬ` of Example 003R, there is a symmetric variant
whose objects are *quintuples* `(A, B, C, a, b)` consisting of objects `A : 𝒜`, `B : ℬ`, `C : 𝒞`
and isomorphisms `a : F A ≅ C`, `b : G B ≅ C`; a morphism
`(A, B, C, a, b) ⟶ (A', B', C', a', b')` is a triple `(f, g, h)` making both squares
`F f ≫ a' = a ≫ h` and `G g ≫ b' = b ≫ h` commute. This file defines that category as
`CategoricalPullback.Quintuple F G` and shows it is equivalent to the standard model.

The comparison functor `Quintuple.toCategoricalPullback` forgets the middle object, sending
`(A, B, C, a, b)` to `(A, B, b⁻¹ ∘ a)` and `(f, g, h)` to `(f, g)`; it is fully faithful because
the `𝒞`-component `h` of a morphism is determined by `f` through the invertible `a`, and
essentially surjective because `(A, B, φ)` is the image of `(A, B, G B, φ, 𝟙)`. The standard
model is Mathlib's `CategoryTheory.Limits.CategoricalPullback`; note that Mathlib names the
common codomain of the cospan `B`, which is the category called `𝒞` here.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Limits.CategoricalPullback

variable {𝒜 : Type u₁} {ℬ : Type u₂} {𝒞 : Type u₃}
variable [Category.{v₁} 𝒜] [Category.{v₂} ℬ] [Category.{v₃} 𝒞]
variable (F : 𝒜 ⥤ 𝒞) (G : ℬ ⥤ 𝒞)

/-- **Stacks 06RL.** The symmetric model of the 2-fibre product `𝒜 ×_𝒞 ℬ`: an object is a
quintuple `(A, B, C, a, b)` with `A : 𝒜`, `B : ℬ`, `C : 𝒞` and isomorphisms `a : F A ≅ C`,
`b : G B ≅ C`. -/
@[stacks_fixed 06RL]
structure Quintuple where
  /-- The object of `𝒜`. -/
  A : 𝒜
  /-- The object of `ℬ`. -/
  B : ℬ
  /-- The object of `𝒞`. -/
  C : 𝒞
  /-- The structure isomorphism `F.obj A ≅ C`. -/
  a : F.obj A ≅ C
  /-- The structure isomorphism `G.obj B ≅ C`. -/
  b : G.obj B ≅ C

namespace Quintuple

variable {F G}

/-- A morphism of quintuples: a triple `(f, g, h)` compatible with the structure
isomorphisms via the two commuting squares. -/
@[ext]
structure Hom (X Y : Quintuple F G) where
  /-- The `𝒜`-component. -/
  f : X.A ⟶ Y.A
  /-- The `ℬ`-component. -/
  g : X.B ⟶ Y.B
  /-- The `𝒞`-component. -/
  h : X.C ⟶ Y.C
  /-- Compatibility with `a, a'`. -/
  wa : F.map f ≫ Y.a.hom = X.a.hom ≫ h := by cat_disch
  /-- Compatibility with `b, b'`. -/
  wb : G.map g ≫ Y.b.hom = X.b.hom ≫ h := by cat_disch

attribute [reassoc] Hom.wa Hom.wb

/-- The category structure on `Quintuple F G`: identities and composition are
componentwise; two morphisms are equal iff their three components agree (this is
the `@[ext]` lemma `Hom.ext`). -/
@[simps]
instance : Category (Quintuple F G) where
  Hom := Hom
  id X := { f := 𝟙 _, g := 𝟙 _, h := 𝟙 _ }
  comp {X Y Z} φ ψ :=
    { f := φ.f ≫ ψ.f
      g := φ.g ≫ ψ.g
      h := φ.h ≫ ψ.h
      wa := by rw [F.map_comp, Category.assoc, ψ.wa, φ.wa_assoc]
      wb := by rw [G.map_comp, Category.assoc, ψ.wb, φ.wb_assoc] }

/-- **Stacks 06RL.** The comparison functor from the symmetric model to the standard 2-fibre
product: on objects it sends `(A, B, C, a, b)` to `(A, B, a ≪≫ b.symm)`, whose structural
morphism is `b⁻¹ ∘ a`, and on morphisms it sends `(f, g, h)` to `(f, g)`. -/
@[stacks 06RL, simps]
def toCategoricalPullback : Quintuple F G ⥤ CategoricalPullback F G where
  obj X := { fst := X.A, snd := X.B, iso := X.a ≪≫ X.b.symm }
  map {X Y} φ :=
    { fst := φ.f
      snd := φ.g
      w := by
        have hwb : φ.h ≫ Y.b.inv = X.b.inv ≫ G.map φ.g := by
          rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, ← φ.wb]
        dsimp
        rw [φ.wa_assoc, Category.assoc, hwb] }

/-- A natural quasi-inverse to `Quintuple.toCategoricalPullback`, sending an object
`(A, B, φ : F A ≅ G B)` of `CategoricalPullback F G` to the quintuple
`(A, B, G B, φ, 𝟙)`. -/
@[simps]
def ofCategoricalPullback : CategoricalPullback F G ⥤ Quintuple F G where
  obj P := { A := P.fst, B := P.snd, C := G.obj P.snd, a := P.iso, b := Iso.refl _ }
  map {P Q} ψ :=
    { f := ψ.fst
      g := ψ.snd
      h := G.map ψ.snd
      wa := by simp [ψ.w]
      wb := by simp }

/-- `Quintuple.toCategoricalPullback` is faithful: the `h`-component of a quintuple morphism is
determined by its `f`-component via the `wa` square (cancel the iso `X.a`), and `f, g` are read
off directly from the image morphism. -/
instance : (toCategoricalPullback (F := F) (G := G)).Faithful where
  map_injective {X Y} φ ψ hfg := by
    have hf : φ.f = ψ.f := congrArg (·.fst) hfg
    have hg : φ.g = ψ.g := congrArg (·.snd) hfg
    apply Quintuple.Hom.ext
    · exact hf
    · exact hg
    · have h1 := φ.wa
      have h2 := ψ.wa
      rw [hf] at h1
      have : X.a.hom ≫ φ.h = X.a.hom ≫ ψ.h := by rw [← h1, ← h2]
      exact (Iso.cancel_iso_hom_left X.a φ.h ψ.h).mp this

/-- `Quintuple.toCategoricalPullback` is full: a pullback morphism `(fst, snd)` lifts to the
quintuple morphism with `h := X.a.inv ≫ F.map fst ≫ Y.a.hom`; the `wa` square is immediate, and
`wb` follows from the pullback `w`-condition. -/
instance : (toCategoricalPullback (F := F) (G := G)).Full where
  map_surjective {X Y} φ := by
    -- `φ.fst`, `φ.snd` have their types spelled through `toCategoricalPullback.obj`, so the
    -- implicit endpoints of `F.map`/`G.map` are pinned to the quintuple's own components: the
    -- two spellings agree only after unfolding a plain `def`, which `simp` does not do.
    have hwa : F.map (X := X.A) (Y := Y.A) φ.fst ≫ Y.a.hom
        = X.a.hom ≫ (X.a.inv ≫ F.map (X := X.A) (Y := Y.A) φ.fst ≫ Y.a.hom) := by
      simp
    have hwb : G.map (X := X.B) (Y := Y.B) φ.snd ≫ Y.b.hom
        = X.b.hom ≫ (X.a.inv ≫ F.map (X := X.A) (Y := Y.A) φ.fst ≫ Y.a.hom) := by
      have hw := φ.w
      dsimp [toCategoricalPullback] at hw
      simp only [Category.assoc] at hw
      have key : G.map (X := X.B) (Y := Y.B) φ.snd
          = X.b.hom ≫ X.a.inv ≫ F.map (X := X.A) (Y := Y.A) φ.fst ≫ Y.a.hom ≫ Y.b.inv := by
        simp [hw]
      rw [key]
      simp
    exact ⟨{ f := φ.fst, g := φ.snd, h := X.a.inv ≫ F.map φ.fst ≫ Y.a.hom
             wa := hwa, wb := hwb }, rfl⟩

/-- `Quintuple.toCategoricalPullback` is essentially surjective: every pullback object `P` is
isomorphic to the image of `ofCategoricalPullback.obj P` via identity components. -/
instance : (toCategoricalPullback (F := F) (G := G)).EssSurj where
  mem_essImage P := by
    refine ⟨ofCategoricalPullback.obj P, ⟨mkIso (Iso.refl _) (Iso.refl _) ?_⟩⟩
    dsimp [toCategoricalPullback, ofCategoricalPullback]
    simp

/-- **Stacks 06RL.** The comparison functor from the symmetric quintuple model of the 2-fibre
product to the standard model `CategoricalPullback F G` is an equivalence of categories. -/
@[stacks 06RL]
theorem isEquivalence_toCategoricalPullback :
    (toCategoricalPullback (F := F) (G := G)).IsEquivalence :=
  { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }

end Quintuple

end CategoryTheory.Limits.CategoricalPullback
