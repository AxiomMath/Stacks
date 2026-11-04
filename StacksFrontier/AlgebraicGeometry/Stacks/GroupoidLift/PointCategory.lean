module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.Inf

/-!
# The groupoid of points over an algebra

For a groupoid `G` in presheaves on `κ`-small `A'`-algebras and an algebra `C`, the points
`P → C` and the arrows of `G` over `C` form a groupoid in the sense of category theory
(`AlgebraicGeometry.Stack.GroupoidLift.Groupoid.Pt`). Identities between composites of arrows
of `G` are proved there, where the bookkeeping of sources and targets is done by the types.

## Main definitions

* `AlgebraicGeometry.Stack.GroupoidLift.Groupoid.Pt`: the points over `C`, a groupoid.
* `AlgebraicGeometry.Stack.GroupoidLift.Groupoid.toHom`: an arrow with named endpoints.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.Space.ChartDescent

namespace AlgebraicGeometry.Stack.GroupoidLift

universe u

variable {A' : Type u} [CommRing A'] {κ : Cardinal.{u}} {P : Type u} [CommRing P] [Algebra A' P]

/-- The points of a groupoid over `C`, the objects of the groupoid of points. -/
structure Groupoid.Pt (G : Groupoid A' κ P) (C : SmallAlg A' κ) : Type u where
  /-- The point. -/
  pt : P →ₐ[A'] C.obj

variable (G : Groupoid A' κ P) {C : SmallAlg A' κ}

/-- **The groupoid of points** over `C`: morphisms are the arrows of `G` with the given source
and target; `f ≫ g` is `g` after `f`. -/
instance Groupoid.instGroupoidPt (C : SmallAlg A' κ) : CategoryTheory.Groupoid.{u} (G.Pt C) where
  Hom x y := {g : G.arr.obj C // G.src g = x.pt ∧ G.tgt g = y.pt}
  id x := ⟨G.idt x.pt, G.src_idt _, G.tgt_idt _⟩
  comp f g := ⟨G.comp g.1 f.1 (g.2.1.trans f.2.2.symm), (G.src_comp _ _ _).trans f.2.1,
    (G.tgt_comp _ _ _).trans g.2.2⟩
  id_comp f := Subtype.ext ((G.comp_eq' rfl (congrArg G.idt f.2.1.symm) _
    (G.tgt_idt _).symm).trans (G.comp_idt f.1))
  comp_id f := Subtype.ext ((G.comp_eq' (congrArg G.idt f.2.2.symm) rfl _
    (G.src_idt _)).trans (G.idt_comp f.1))
  assoc f g h := Subtype.ext (G.assoc h.1 g.1 f.1 _ _).symm
  inv f := ⟨G.inv f.1, (G.src_inv _).trans f.2.2, (G.tgt_inv _).trans f.2.1⟩
  inv_comp f := Subtype.ext ((G.comp_inv f.1).trans (congrArg G.idt f.2.2))
  comp_inv f := Subtype.ext ((G.inv_comp f.1).trans (congrArg G.idt f.2.1))

/-- An arrow of `G` as a morphism between its source and target. -/
def Groupoid.toHom {x y : G.Pt C} (g : G.arr.obj C) (hs : G.src g = x.pt) (ht : G.tgt g = y.pt) :
    x ⟶ y :=
  ⟨g, hs, ht⟩

/-- The underlying arrow of `G.toHom g hs ht` is `g`. -/
@[simp]
theorem Groupoid.toHom_val {x y : G.Pt C} (g : G.arr.obj C) (hs : G.src g = x.pt)
    (ht : G.tgt g = y.pt) : (G.toHom g hs ht).1 = g := rfl

/-- Equal arrows give equal morphisms under `Groupoid.toHom`, whatever the endpoint proofs. -/
theorem Groupoid.toHom_congr {x y : G.Pt C} {g g' : G.arr.obj C} (h : g = g')
    (hs : G.src g = x.pt) (ht : G.tgt g = y.pt) (hs' : G.src g' = x.pt) (ht' : G.tgt g' = y.pt) :
    G.toHom g hs ht = G.toHom g' hs' ht' :=
  Subtype.ext h

/-- The underlying arrow of `f ≫ g` is the composite of `g` after `f` in `G`. -/
theorem Groupoid.comp_val {x y z : G.Pt C} (f : x ⟶ y) (g : y ⟶ z) :
    (f ≫ g).1 = G.comp g.1 f.1 (g.2.1.trans f.2.2.symm) := rfl

/-- The underlying arrow of the inverse of `f` is the inverse of `f` in `G`. -/
theorem Groupoid.inv_val {x y : G.Pt C} (f : x ⟶ y) :
    (CategoryTheory.Groupoid.inv f).1 = G.inv f.1 := rfl

/-- The underlying arrow of the identity of `x` is the identity arrow of `G` at `x.pt`. -/
theorem Groupoid.id_val (x : G.Pt C) : (𝟙 x : x ⟶ x).1 = G.idt x.pt := rfl

/-- The source of the underlying arrow of a morphism `x ⟶ y` is `x.pt`. -/
theorem Groupoid.src_val {x y : G.Pt C} (f : x ⟶ y) : G.src f.1 = x.pt := f.2.1

/-- The target of the underlying arrow of a morphism `x ⟶ y` is `y.pt`. -/
theorem Groupoid.tgt_val {x y : G.Pt C} (f : x ⟶ y) : G.tgt f.1 = y.pt := f.2.2

/-- Pulling the underlying arrow of `f ≫ g` back along `φ` gives the composite of the pulled-back
arrows. -/
theorem Groupoid.map_comp_val {D : SmallAlg A' κ} (φ : C ⟶ D) {x y z : G.Pt C} (f : x ⟶ y)
    (g : y ⟶ z) :
    G.arr.map φ (f ≫ g).1 = G.comp (G.arr.map φ g.1) (G.arr.map φ f.1)
      (by rw [G.src_map, G.tgt_map, g.2.1, f.2.2]) :=
  G.comp_map φ g.1 f.1 _

/-- Pulling the underlying arrow of the inverse of `f` back along `φ` gives the inverse of the
pulled-back arrow. -/
theorem Groupoid.map_inv_val {D : SmallAlg A' κ} (φ : C ⟶ D) {x y : G.Pt C} (f : x ⟶ y) :
    G.arr.map φ (CategoryTheory.Groupoid.inv f).1 = G.inv (G.arr.map φ f.1) :=
  G.inv_map φ f.1

/-- An arrow after another one after the inverse of their composite is an identity. -/
theorem Groupoid.comp_comp_inv_comp (a b : G.arr.obj C) (h : G.src a = G.tgt b)
    (h₁ : G.src b = G.tgt (G.inv (G.comp a b h)))
    (h₂ : G.src a = G.tgt (G.comp b (G.inv (G.comp a b h)) h₁)) :
    G.comp a (G.comp b (G.inv (G.comp a b h)) h₁) h₂ = G.idt (G.tgt a) := by
  let x : G.Pt C := ⟨G.src b⟩
  let y : G.Pt C := ⟨G.tgt b⟩
  let z : G.Pt C := ⟨G.tgt a⟩
  let B : x ⟶ y := G.toHom b rfl rfl
  let A : y ⟶ z := G.toHom a h rfl
  exact congrArg Subtype.val
    (show (CategoryTheory.Groupoid.inv (B ≫ A) ≫ B) ≫ A = 𝟙 z by simp)

/-- If `c` is the composite of `a` after `b` (up to the equalities `a = a'`, `b = b'`, `c = c'`),
then `a` after `b` after the inverse of `c` is an identity. -/
theorem Groupoid.comp_comp_inv_idt {a b c : G.arr.obj C} (h₁ : G.src b = G.tgt (G.inv c))
    (h₂ : G.src a = G.tgt (G.comp b (G.inv c) h₁)) {a' b' c' : G.arr.obj C} (ha : a = a')
    (hb : b = b') (hc : c = c') (h : G.src a' = G.tgt b') (hcomp : G.comp a' b' h = c') :
    G.comp a (G.comp b (G.inv c) h₁) h₂ = G.idt (G.tgt a') := by
  subst ha hb hc hcomp
  exact G.comp_comp_inv_comp _ _ h _ _

/-- The arrow `a` after `b` after the inverse of `c` depends only on `a`, `b` and `c`, not on the
proofs that the composites are defined. -/
theorem Groupoid.comp_comp_inv_congr {a b c a' b' c' : G.arr.obj C}
    (h₁ : G.src b = G.tgt (G.inv c)) (h₂ : G.src a = G.tgt (G.comp b (G.inv c) h₁))
    (h₁' : G.src b' = G.tgt (G.inv c')) (h₂' : G.src a' = G.tgt (G.comp b' (G.inv c') h₁'))
    (ha : a = a') (hb : b = b') (hc : c = c') :
    G.comp a (G.comp b (G.inv c) h₁) h₂ = G.comp a' (G.comp b' (G.inv c') h₁') h₂' := by
  subst ha hb hc
  rfl

/-- If an arrow after another one after the inverse of a third is an identity, the composite of
the first two is the third. -/
theorem Groupoid.comp_eq_of_comp_comp_inv {a b c : G.arr.obj C} (h : G.src a = G.tgt b)
    (h₁ : G.src b = G.tgt (G.inv c)) (h₂ : G.src a = G.tgt (G.comp b (G.inv c) h₁))
    (hc : G.comp a (G.comp b (G.inv c) h₁) h₂ = G.idt (G.tgt a)) :
    G.comp a b h = c := by
  let x : G.Pt C := ⟨G.src b⟩
  let y : G.Pt C := ⟨G.tgt b⟩
  let z : G.Pt C := ⟨G.tgt a⟩
  have hcs : G.src c = x.pt := (G.tgt_inv c).symm.trans h₁.symm
  have hct : G.tgt c = z.pt := by
    rw [← G.src_inv c]
    have := congrArg G.src hc
    rwa [G.src_comp, G.src_comp, G.src_idt] at this
  let B : x ⟶ y := G.toHom b rfl rfl
  let A : y ⟶ z := G.toHom a h rfl
  let Cc : x ⟶ z := G.toHom c hcs hct
  have h' : (CategoryTheory.Groupoid.inv Cc ≫ B) ≫ A = 𝟙 z := Subtype.ext hc
  rw [CategoryTheory.Groupoid.inv_eq_inv, Category.assoc, IsIso.inv_comp_eq,
    Category.comp_id] at h'
  exact congrArg Subtype.val h'

/-- **The cocycle identity of defects**, in any groupoid: for arrows `rᵢⱼ` between four objects,
the defects of the faces `0, 2` compose to the defects of the faces `1, 3`, the last one
conjugated back along `r₂₃`. -/
theorem _root_.CategoryTheory.Groupoid.defect_word {𝒞 : Type*} [CategoryTheory.Groupoid 𝒞]
    {Y₀ Y₁ Y₂ Y₃ : 𝒞} (r₀₁ : Y₀ ⟶ Y₁) (r₀₂ : Y₀ ⟶ Y₂) (r₀₃ : Y₀ ⟶ Y₃) (r₁₂ : Y₁ ⟶ Y₂)
    (r₁₃ : Y₁ ⟶ Y₃) (r₂₃ : Y₂ ⟶ Y₃) :
    ((CategoryTheory.Groupoid.inv r₀₃ ≫ r₀₁) ≫ r₁₃) ≫
        ((CategoryTheory.Groupoid.inv r₁₃ ≫ r₁₂) ≫ r₂₃) =
      ((CategoryTheory.Groupoid.inv r₀₃ ≫ r₀₂) ≫ r₂₃) ≫
        ((CategoryTheory.Groupoid.inv r₂₃ ≫
          ((CategoryTheory.Groupoid.inv r₀₂ ≫ r₀₁) ≫ r₁₂)) ≫ r₂₃) := by
  simp

/-- **The defect after a change of the arrow**, in any groupoid: changing the three arrows by
automorphisms of their targets changes the defect by those automorphisms, the one at the
middle vertex conjugated along `p₀`. -/
theorem _root_.CategoryTheory.Groupoid.defect_change_word {𝒞 : Type*}
    [CategoryTheory.Groupoid 𝒞] {X₀ X₁ X₂ : 𝒞} (p₁ : X₀ ⟶ X₂) (p₂ : X₀ ⟶ X₁) (p₀ : X₁ ⟶ X₂)
    (b₁ : X₂ ⟶ X₂) (b₂ : X₁ ⟶ X₁) (b₀ : X₂ ⟶ X₂) :
    (CategoryTheory.Groupoid.inv (p₁ ≫ b₁) ≫ (p₂ ≫ b₂)) ≫ (p₀ ≫ b₀) =
      CategoryTheory.Groupoid.inv b₁ ≫ (((CategoryTheory.Groupoid.inv p₁ ≫ p₂) ≫ p₀) ≫
        (((CategoryTheory.Groupoid.inv p₀ ≫ b₂) ≫ p₀) ≫ b₀)) := by
  simp

/-- `defect_change_word` with the old defect and the conjugate named. -/
theorem _root_.CategoryTheory.Groupoid.defect_change_word' {𝒞 : Type*}
    [CategoryTheory.Groupoid 𝒞] {X₀ X₁ X₂ : 𝒞} {p₁ : X₀ ⟶ X₂} {p₂ : X₀ ⟶ X₁} {p₀ : X₁ ⟶ X₂}
    {b₁ : X₂ ⟶ X₂} {b₂ : X₁ ⟶ X₁} {b₀ : X₂ ⟶ X₂} {δ c : X₂ ⟶ X₂}
    (hδ : (CategoryTheory.Groupoid.inv p₁ ≫ p₂) ≫ p₀ = δ)
    (hc : (CategoryTheory.Groupoid.inv p₀ ≫ b₂) ≫ p₀ = c) :
    (CategoryTheory.Groupoid.inv (p₁ ≫ b₁) ≫ (p₂ ≫ b₂)) ≫ (p₀ ≫ b₀) =
      CategoryTheory.Groupoid.inv b₁ ≫ (δ ≫ (c ≫ b₀)) := by
  rw [CategoryTheory.Groupoid.defect_change_word, hδ, hc]

end AlgebraicGeometry.Stack.GroupoidLift

end
