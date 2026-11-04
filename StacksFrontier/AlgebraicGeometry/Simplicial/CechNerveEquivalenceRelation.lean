module

public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.CategoryTheory.EquivalenceRelation
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equifibered
import StacksCore.Tactic.StacksAttribute

/-!
# Cartesian morphisms to Čech nerves give equivalence relations

Let `f : X ⟶ S` be a morphism in a category with finite limits and let `Y` be a simplicial
object equipped with a cartesian morphism `π : Y ⟶ (Arrow.mk f).cechNerve`. Then the two face
maps `Y.δ 1, Y.δ 0 : Y₁ ⟶ Y₀` form an internal equivalence relation.

The proof is the one in the source. Joint monicity of the two face maps comes from
cartesianness of `π` in the degree-one face, which turns the question into joint monicity of
the two coordinates of the Čech nerve; reflexivity is the degeneracy `Y.σ 0`, and symmetry and
transitivity are produced by lifting an explicitly constructed two-simplex of the Čech nerve
through the cartesian square in degree two.

## Main results

* `CategoryTheory.SimplicialObject.isEquivalenceRelation_faceMaps_of_equifibered`: the face maps
  in degrees one and zero of a simplicial object mapping cartesianly to the Čech nerve of a
  morphism define an internal equivalence relation.

## Implementation notes

The assertion is stated in an arbitrary category with finite limits; taking the category of
schemes recovers the source statement. The Čech nerve is Mathlib's
`CategoryTheory.Arrow.cechNerve`, and the cartesianness of the simplicial morphism is
`CategoryTheory.NatTrans.Equifibered`. Joint monicity of the two face maps is used in the form
`CategoryTheory.JointlyMono₂`, which is equivalent to monicity of their map to the fibre product
over the base since both face maps are morphisms over the base.

## References

* [Stacks Project, Tag 024E](https://stacks.math.columbia.edu/tag/024E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]

@[sga "3 X 9.7.1" "more general", sga "4 Vbis 1.2.7" "partial"]
private noncomputable abbrev cechObj {X S : C} (f : X ⟶ S) (n : ℕ) : C :=
  widePullback.{0} S (fun _ : Fin (n + 1) => X) (fun _ => f)

private noncomputable abbrev cechCoord {X S : C} (f : X ⟶ S) (n : ℕ) (i : Fin (n + 1)) :
    cechObj f n ⟶ X :=
  WidePullback.π (fun _ : Fin (n + 1) => f) i

@[sga "4 Vbis 1.2.7" "partial"]
private noncomputable abbrev cechBase {X S : C} (f : X ⟶ S) (n : ℕ) : cechObj f n ⟶ S :=
  WidePullback.base (fun _ : Fin (n + 1) => f)

private lemma cech_map_coord {X S : C} (f : X ⟶ S) {m n : ℕ}
    (g : (Opposite.op (SimplexCategory.mk m) : SimplexCategoryᵒᵖ) ⟶
      Opposite.op (SimplexCategory.mk n)) (i : Fin (n + 1)) :
    (Arrow.mk f).cechNerve.map g ≫ cechCoord f n i =
      cechCoord f m (g.unop.toOrderHom i) := by
  simp [cechCoord, Arrow.cechNerve_map, Arrow.cechNerve_obj, WidePullback.lift_π]

private lemma face_coord {X S : C} (f : X ⟶ S) {Y : SimplicialObject C}
    (π : Y ⟶ (Arrow.mk f).cechNerve) (i : Fin 2) :
    Y.δ i ≫ π.app (Opposite.op (SimplexCategory.mk 0)) ≫ cechCoord f 0 0 =
      π.app (Opposite.op (SimplexCategory.mk 1)) ≫
        cechCoord f 1 (((SimplexCategory.δ i).toOrderHom) 0) := by
  have h := π.naturality ((SimplexCategory.δ i).op)
  change Y.δ i ≫ π.app (Opposite.op (SimplexCategory.mk 0)) =
    π.app (Opposite.op (SimplexCategory.mk 1)) ≫
      (Arrow.mk f).cechNerve.map ((SimplexCategory.δ i).op) at h
  rw [← Category.assoc, h, Category.assoc, cech_map_coord]
  rfl

private lemma cech_map_base {X S : C} (f : X ⟶ S) {m n : ℕ}
    (g : (Opposite.op (SimplexCategory.mk m) : SimplexCategoryᵒᵖ) ⟶
      Opposite.op (SimplexCategory.mk n)) :
    (Arrow.mk f).cechNerve.map g ≫ cechBase f n = cechBase f m := by
  simp [cechBase, Arrow.cechNerve_map, WidePullback.lift_base]

private def triple {W X : C} (x₀ x₁ x₂ : W ⟶ X) : Fin 3 → (W ⟶ X) :=
  Fin.cons (α := fun _ : Fin 3 => W ⟶ X) x₀
    (Fin.cons (α := fun _ : Fin 2 => W ⟶ X) x₁ (fun _ => x₂))

omit [HasFiniteLimits C] in
private lemma triple_compat {W X S : C} (f : X ⟶ S) (x₀ x₁ x₂ : W ⟶ X)
    (h₁ : x₀ ≫ f = x₁ ≫ f) (h₂ : x₀ ≫ f = x₂ ≫ f) :
    ∀ i : Fin 3, triple x₀ x₁ x₂ i ≫ f = x₀ ≫ f := by
  intro i
  fin_cases i
  · show x₀ ≫ f = x₀ ≫ f
    rfl
  · show x₁ ≫ f = x₀ ≫ f
    exact h₁.symm
  · show x₂ ≫ f = x₀ ≫ f
    exact h₂.symm

private noncomputable def cechTwoSimplex {X S : C} (f : X ⟶ S) {W : C}
    (x₀ x₁ x₂ : W ⟶ X) (h₁ : x₀ ≫ f = x₁ ≫ f) (h₂ : x₀ ≫ f = x₂ ≫ f) :
  W ⟶ cechObj f 2 :=
  WidePullback.lift (x₀ ≫ f) (triple x₀ x₁ x₂)
    (triple_compat f x₀ x₁ x₂ h₁ h₂)

private lemma cechTwoSimplex_coord {X S : C} (f : X ⟶ S) {W : C}
    (x₀ x₁ x₂ : W ⟶ X) (h₁ : x₀ ≫ f = x₁ ≫ f) (h₂ : x₀ ≫ f = x₂ ≫ f)
    (i : Fin 3) :
    cechTwoSimplex f x₀ x₁ x₂ h₁ h₂ ≫ cechCoord f 2 i =
      triple x₀ x₁ x₂ i := by
  simpa [cechTwoSimplex, cechCoord] using
    (WidePullback.lift_π (fun _ : Fin 3 => f) (x₀ ≫ f)
      (triple x₀ x₁ x₂)
      (triple_compat f x₀ x₁ x₂ h₁ h₂) i)

private lemma cechTwoSimplex_base {X S : C} (f : X ⟶ S) {W : C}
    (x₀ x₁ x₂ : W ⟶ X) (h₁ : x₀ ≫ f = x₁ ≫ f) (h₂ : x₀ ≫ f = x₂ ≫ f) :
    cechTwoSimplex f x₀ x₁ x₂ h₁ h₂ ≫ cechBase f 2 = x₀ ≫ f := by
  dsimp [cechTwoSimplex, cechBase]
  rw [WidePullback.lift_base]

private lemma post_cech_map_coord {X S : C} (f : X ⟶ S) {W : C}
    {m n : ℕ} (g : (Opposite.op (SimplexCategory.mk m) : SimplexCategoryᵒᵖ) ⟶
      Opposite.op (SimplexCategory.mk n)) (a : W ⟶ cechObj f m) (i : Fin (n + 1)) :
    a ≫ (Arrow.mk f).cechNerve.map g ≫ cechCoord f n i =
      a ≫ cechCoord f m (g.unop.toOrderHom i) := by
  calc
    a ≫ (Arrow.mk f).cechNerve.map g ≫ cechCoord f n i =
        a ≫ ((Arrow.mk f).cechNerve.map g ≫ cechCoord f n i) := by
          simp
    _ = a ≫ cechCoord f m (g.unop.toOrderHom i) :=
      congrArg (fun k => a ≫ k) (cech_map_coord f g i)

private lemma post_cech_map_base {X S : C} (f : X ⟶ S) {W : C}
    {m n : ℕ} (g : (Opposite.op (SimplexCategory.mk m) : SimplexCategoryᵒᵖ) ⟶
      Opposite.op (SimplexCategory.mk n)) (a : W ⟶ cechObj f m) :
    a ≫ (Arrow.mk f).cechNerve.map g ≫ cechBase f n = a ≫ cechBase f m := by
  calc
    a ≫ (Arrow.mk f).cechNerve.map g ≫ cechBase f n =
        a ≫ ((Arrow.mk f).cechNerve.map g ≫ cechBase f n) := by
          simp
    _ = a ≫ cechBase f m := congrArg (fun k => a ≫ k) (cech_map_base f g)

private lemma cechTwoSimplex_face2 {X S : C} (f : X ⟶ S) {W : C}
    (x₀ x₁ x₂ : W ⟶ X) (h₁ : x₀ ≫ f = x₁ ≫ f) (h₂ : x₀ ≫ f = x₂ ≫ f)
    (e : W ⟶ cechObj f 1)
    (he₀ : e ≫ cechCoord f 1 0 = x₀) (he₁ : e ≫ cechCoord f 1 1 = x₁)
    (heb : e ≫ cechBase f 1 = x₀ ≫ f) :
    cechTwoSimplex f x₀ x₁ x₂ h₁ h₂ ≫
      (Arrow.mk f).cechNerve.map ((SimplexCategory.δ (2 : Fin 3)).op) = e := by
  let z := cechTwoSimplex f x₀ x₁ x₂ h₁ h₂
  let g : (Opposite.op (SimplexCategory.mk 2) : SimplexCategoryᵒᵖ) ⟶
      Opposite.op (SimplexCategory.mk 1) := (SimplexCategory.δ (2 : Fin 3)).op
  show z ≫ (Arrow.mk f).cechNerve.map g = e
  have hg₀ : g.unop.toOrderHom (0 : Fin 2) = 0 := by decide
  have hg₁ : g.unop.toOrderHom (1 : Fin 2) = 1 := by decide
  apply WidePullback.hom_ext (fun _ : Fin 2 => f)
  · intro i
    fin_cases i
    · calc
        (z ≫ (Arrow.mk f).cechNerve.map g) ≫ cechCoord f 1 0 =
            z ≫ cechCoord f 2 (g.unop.toOrderHom 0) := by
              simpa [Category.assoc] using post_cech_map_coord f g z 0
        _ = e ≫ cechCoord f 1 0 := by simpa [z, hg₀, cechTwoSimplex_coord, triple] using he₀.symm
    · calc
        (z ≫ (Arrow.mk f).cechNerve.map g) ≫ cechCoord f 1 1 =
            z ≫ cechCoord f 2 (g.unop.toOrderHom 1) := by
              simpa [Category.assoc] using post_cech_map_coord f g z 1
        _ = e ≫ cechCoord f 1 1 := by simpa [z, hg₁, cechTwoSimplex_coord, triple] using he₁.symm
  · calc
      (z ≫ (Arrow.mk f).cechNerve.map g) ≫ cechBase f 1 = z ≫ cechBase f 2 := by
        simpa [Category.assoc] using post_cech_map_base f g z
      _ = x₀ ≫ f := cechTwoSimplex_base f x₀ x₁ x₂ h₁ h₂
      _ = e ≫ cechBase f 1 := heb.symm

private lemma cechTwoSimplex_face0 {X S : C} (f : X ⟶ S) {W : C}
    (x₀ x₁ x₂ : W ⟶ X) (h₁ : x₀ ≫ f = x₁ ≫ f) (h₂ : x₀ ≫ f = x₂ ≫ f)
    (e : W ⟶ cechObj f 1)
    (he₀ : e ≫ cechCoord f 1 0 = x₁) (he₁ : e ≫ cechCoord f 1 1 = x₂)
    (heb : e ≫ cechBase f 1 = x₀ ≫ f) :
    cechTwoSimplex f x₀ x₁ x₂ h₁ h₂ ≫
      (Arrow.mk f).cechNerve.map ((SimplexCategory.δ (0 : Fin 3)).op) = e := by
  let z := cechTwoSimplex f x₀ x₁ x₂ h₁ h₂
  let g : (Opposite.op (SimplexCategory.mk 2) : SimplexCategoryᵒᵖ) ⟶
      Opposite.op (SimplexCategory.mk 1) := (SimplexCategory.δ (0 : Fin 3)).op
  show z ≫ (Arrow.mk f).cechNerve.map g = e
  have hg₀ : g.unop.toOrderHom (0 : Fin 2) = 1 := by decide
  have hg₁ : g.unop.toOrderHom (1 : Fin 2) = 2 := by decide
  apply WidePullback.hom_ext (fun _ : Fin 2 => f)
  · intro i
    fin_cases i
    · calc
        (z ≫ (Arrow.mk f).cechNerve.map g) ≫ cechCoord f 1 0 =
            z ≫ cechCoord f 2 (g.unop.toOrderHom 0) := by
              simpa [Category.assoc] using post_cech_map_coord f g z 0
        _ = e ≫ cechCoord f 1 0 := by simpa [z, hg₀, cechTwoSimplex_coord, triple] using he₀.symm
    · calc
        (z ≫ (Arrow.mk f).cechNerve.map g) ≫ cechCoord f 1 1 =
            z ≫ cechCoord f 2 (g.unop.toOrderHom 1) := by
              simpa [Category.assoc] using post_cech_map_coord f g z 1
        _ = e ≫ cechCoord f 1 1 := by
          rw [hg₁]
          have hz : z ≫ cechCoord f 2 2 = x₂ := by
            calc
              z ≫ cechCoord f 2 2 = triple x₀ x₁ x₂ 2 := by
                simpa [z] using cechTwoSimplex_coord f x₀ x₁ x₂ h₁ h₂ 2
              _ = x₂ := by rfl
          exact hz.trans he₁.symm
  · calc
      (z ≫ (Arrow.mk f).cechNerve.map g) ≫ cechBase f 1 = z ≫ cechBase f 2 := by
        simpa [Category.assoc] using post_cech_map_base f g z
      _ = x₀ ≫ f := cechTwoSimplex_base f x₀ x₁ x₂ h₁ h₂
      _ = e ≫ cechBase f 1 := heb.symm

private lemma cechTwoSimplex_face1 {X S : C} (f : X ⟶ S) {W : C}
    (x₀ x₁ x₂ : W ⟶ X) (h₁ : x₀ ≫ f = x₁ ≫ f) (h₂ : x₀ ≫ f = x₂ ≫ f)
    (e : W ⟶ cechObj f 1)
    (he₀ : e ≫ cechCoord f 1 0 = x₀) (he₁ : e ≫ cechCoord f 1 1 = x₂)
    (heb : e ≫ cechBase f 1 = x₀ ≫ f) :
    cechTwoSimplex f x₀ x₁ x₂ h₁ h₂ ≫
      (Arrow.mk f).cechNerve.map ((SimplexCategory.δ (1 : Fin 3)).op) = e := by
  let z := cechTwoSimplex f x₀ x₁ x₂ h₁ h₂
  let g : (Opposite.op (SimplexCategory.mk 2) : SimplexCategoryᵒᵖ) ⟶
      Opposite.op (SimplexCategory.mk 1) := (SimplexCategory.δ (1 : Fin 3)).op
  have hg₀ : g.unop.toOrderHom (0 : Fin 2) = 0 := by decide
  have hg₁ : g.unop.toOrderHom (1 : Fin 2) = 2 := by decide
  show z ≫ (Arrow.mk f).cechNerve.map g = e
  apply WidePullback.hom_ext (fun _ : Fin 2 => f)
  · intro i
    fin_cases i
    · calc
        (z ≫ (Arrow.mk f).cechNerve.map g) ≫ cechCoord f 1 0 =
            z ≫ cechCoord f 2 (g.unop.toOrderHom 0) := by
              simpa [Category.assoc] using post_cech_map_coord f g z 0
        _ = e ≫ cechCoord f 1 0 := by
          simpa [z, hg₀, cechTwoSimplex_coord, triple] using he₀.symm
    · calc
        (z ≫ (Arrow.mk f).cechNerve.map g) ≫ cechCoord f 1 1 =
            z ≫ cechCoord f 2 (g.unop.toOrderHom 1) := by
              simpa [Category.assoc] using post_cech_map_coord f g z 1
        _ = e ≫ cechCoord f 1 1 := by
          rw [hg₁]
          have hz : z ≫ cechCoord f 2 2 = x₂ := by
            calc
              z ≫ cechCoord f 2 2 = triple x₀ x₁ x₂ 2 := by
                simpa [z] using cechTwoSimplex_coord f x₀ x₁ x₂ h₁ h₂ 2
              _ = x₂ := by rfl
          exact hz.trans he₁.symm
  · calc
      (z ≫ (Arrow.mk f).cechNerve.map g) ≫ cechBase f 1 = z ≫ cechBase f 2 := by
        simpa [Category.assoc] using post_cech_map_base f g z
      _ = x₀ ≫ f := cechTwoSimplex_base f x₀ x₁ x₂ h₁ h₂
      _ = e ≫ cechBase f 1 := heb.symm

private lemma faceMaps_jointlyMono {X S : C} (f : X ⟶ S)
    {Y : SimplicialObject C} (π : Y ⟶ (Arrow.mk f).cechNerve)
    (hπ : NatTrans.Equifibered π) :
    JointlyMono₂ (Y.δ (1 : Fin 2)) (Y.δ (0 : Fin 2)) := by
  constructor
  intro T a b h₁ h₀
  let g₁ : (Opposite.op (SimplexCategory.mk 1) : SimplexCategoryᵒᵖ) ⟶
      Opposite.op (SimplexCategory.mk 0) := (SimplexCategory.δ (1 : Fin 2)).op
  let π₀ := π.app (Opposite.op (SimplexCategory.mk 0))
  let π₁ := π.app (Opposite.op (SimplexCategory.mk 1))
  have hδ₀ : (SimplexCategory.δ (0 : Fin 2)).toOrderHom (0 : Fin 1) = 1 := by decide
  have hδ₁ : (SimplexCategory.δ (1 : Fin 2)).toOrderHom (0 : Fin 1) = 0 := by decide
  have hnatCoord₁ : Y.δ (1 : Fin 2) ≫ π₀ ≫ cechCoord f 0 0 = π₁ ≫ cechCoord f 1 0 := by
    simpa only [hδ₁] using face_coord f π 1
  have hnatCoord₀ : Y.δ (0 : Fin 2) ≫ π₀ ≫ cechCoord f 0 0 = π₁ ≫ cechCoord f 1 1 := by
    simpa only [hδ₀] using face_coord f π 0
  have hcoord₀ : a ≫ π₁ ≫ cechCoord f 1 0 = b ≫ π₁ ≫ cechCoord f 1 0 := by
    calc
      a ≫ π₁ ≫ cechCoord f 1 0 = a ≫ Y.δ (1 : Fin 2) ≫ π₀ ≫ cechCoord f 0 0 :=
        congrArg (fun k => a ≫ k) hnatCoord₁.symm
      _ = b ≫ Y.δ (1 : Fin 2) ≫ π₀ ≫ cechCoord f 0 0 := by
        simpa [Category.assoc] using congrArg (fun k => k ≫ π₀ ≫ cechCoord f 0 0) h₁
      _ = b ≫ π₁ ≫ cechCoord f 1 0 := congrArg (fun k => b ≫ k) hnatCoord₁
  have hcoord₁ : a ≫ π₁ ≫ cechCoord f 1 1 = b ≫ π₁ ≫ cechCoord f 1 1 := by
    calc
      a ≫ π₁ ≫ cechCoord f 1 1 = a ≫ Y.δ (0 : Fin 2) ≫ π₀ ≫ cechCoord f 0 0 :=
        congrArg (fun k => a ≫ k) hnatCoord₀.symm
      _ = b ≫ Y.δ (0 : Fin 2) ≫ π₀ ≫ cechCoord f 0 0 := by
        simpa [Category.assoc] using congrArg (fun k => k ≫ π₀ ≫ cechCoord f 0 0) h₀
      _ = b ≫ π₁ ≫ cechCoord f 1 1 := congrArg (fun k => b ≫ k) hnatCoord₀
  have hpiEdge : a ≫ π₁ = b ≫ π₁ := by
    apply WidePullback.hom_ext (fun _ : Fin 2 => f)
    · intro i
      fin_cases i
      · simpa [Category.assoc] using hcoord₀
      · simpa [Category.assoc] using hcoord₁
    · calc
        (a ≫ π₁) ≫ cechBase f 1 = (a ≫ π₁) ≫ cechCoord f 1 0 ≫ f := by
          simp [cechBase, cechCoord]
        _ = (b ≫ π₁) ≫ cechCoord f 1 0 ≫ f := by
          simpa [Category.assoc] using congrArg (fun k => k ≫ f) hcoord₀
        _ = (b ≫ π₁) ≫ cechBase f 1 := by simp [cechBase, cechCoord]
  have htop : a ≫ Y.map g₁ = b ≫ Y.map g₁ := by
    simpa [SimplicialObject.δ, g₁] using h₁
  exact (hπ g₁).hom_ext htop hpiEdge

private def faceMaps_reflexive {X S : C} (f : X ⟶ S)
    {Y : SimplicialObject C} (π : Y ⟶ (Arrow.mk f).cechNerve)
    (hπ : NatTrans.Equifibered π) :
    ReflexiveRelation (Y.δ (1 : Fin 2)) (Y.δ (0 : Fin 2)) where
  __ := faceMaps_jointlyMono f π hπ
  r := Y.σ (0 : Fin 1)
  reflexivity₁ := by simpa using Y.δ_comp_σ_succ (i := (0 : Fin 1))
  reflexivity₂ := by simpa using Y.δ_comp_σ_self (i := (0 : Fin 1))

private noncomputable def faceMaps_transitive {X S : C} (f : X ⟶ S)
    {Y : SimplicialObject C} (π : Y ⟶ (Arrow.mk f).cechNerve)
    (hπ : NatTrans.Equifibered π) :
    TransitiveRelation (Y.δ (1 : Fin 2)) (Y.δ (0 : Fin 2)) := by
  let p₁ := Y.δ (1 : Fin 2)
  let p₂ := Y.δ (0 : Fin 2)
  let P := pullback p₂ p₁
  let a := pullback.fst p₂ p₁
  let b := pullback.snd p₂ p₁
  have hab : a ≫ p₂ = b ≫ p₁ := pullback.condition
  let π₁ := π.app (Opposite.op (SimplexCategory.mk 1))
  let e0 := a ≫ π₁ ≫ cechCoord f 1 0
  let e1 := a ≫ π₁ ≫ cechCoord f 1 1
  let e2 := b ≫ π₁ ≫ cechCoord f 1 1
  have hδ₀ : (SimplexCategory.δ (0 : Fin 2)).toOrderHom (0 : Fin 1) = 1 := by decide
  have hδ₁ : (SimplexCategory.δ (1 : Fin 2)).toOrderHom (0 : Fin 1) = 0 := by decide
  have hface₀ : Y.δ (0 : Fin 2) ≫ π.app (Opposite.op (SimplexCategory.mk 0)) ≫
      cechCoord f 0 0 = π₁ ≫ cechCoord f 1 1 := by
    simpa [hδ₀] using face_coord f π (0 : Fin 2)
  have hface₁ : Y.δ (1 : Fin 2) ≫ π.app (Opposite.op (SimplexCategory.mk 0)) ≫
      cechCoord f 0 0 = π₁ ≫ cechCoord f 1 0 := by
    simpa [hδ₁] using face_coord f π (1 : Fin 2)
  have hmiddle : e1 = b ≫ π₁ ≫ cechCoord f 1 0 := by
    calc
      e1 = a ≫ p₂ ≫ π.app (Opposite.op (SimplexCategory.mk 0)) ≫ cechCoord f 0 0 := by
        dsimp [e1, p₂]
        simpa [Category.assoc] using congrArg (fun k => a ≫ k)
          hface₀.symm
      _ = b ≫ p₁ ≫ π.app (Opposite.op (SimplexCategory.mk 0)) ≫ cechCoord f 0 0 := by
        simpa [Category.assoc] using congrArg
          (fun k => k ≫ π.app (Opposite.op (SimplexCategory.mk 0)) ≫ cechCoord f 0 0) hab
      _ = b ≫ π₁ ≫ cechCoord f 1 0 := by
        dsimp [p₁]
        simpa [Category.assoc] using congrArg (fun k => b ≫ k)
          hface₁
  have h01 : e0 ≫ f = e1 ≫ f := by
    simp [e0, e1, cechCoord, Category.assoc]
  have h12 : e1 ≫ f = e2 ≫ f := by
    simpa [e1, e2, Category.assoc] using congrArg (fun k => k ≫ f) hmiddle
  have h02 : e0 ≫ f = e2 ≫ f := h01.trans h12
  have haBase : a ≫ π₁ ≫ cechBase f 1 = e0 ≫ f := by
    simp [e0, cechCoord, cechBase, Category.assoc]
  have hbBase : b ≫ π₁ ≫ cechBase f 1 = e2 ≫ f := by
    simp [e2, cechCoord, cechBase, Category.assoc]
  have haBase' : (a ≫ π₁) ≫ cechBase f 1 = e0 ≫ f := by
    simpa [Category.assoc] using haBase
  have hbBase' : (b ≫ π₁) ≫ cechBase f 1 = e0 ≫ f := by
    simpa [Category.assoc] using hbBase.trans h02.symm
  have ha0 : a ≫ π₁ ≫ cechCoord f 1 0 = e0 := rfl
  have ha1 : a ≫ π₁ ≫ cechCoord f 1 1 = e1 := rfl
  have hb0 : b ≫ π₁ ≫ cechCoord f 1 0 = e1 := hmiddle.symm
  have hb1 : b ≫ π₁ ≫ cechCoord f 1 1 = e2 := rfl
  have ha0' : (a ≫ π₁) ≫ cechCoord f 1 0 = e0 := by simpa [Category.assoc] using ha0
  have ha1' : (a ≫ π₁) ≫ cechCoord f 1 1 = e1 := by simpa [Category.assoc] using ha1
  have hb0' : (b ≫ π₁) ≫ cechCoord f 1 0 = e1 := by simpa [Category.assoc] using hb0
  have hb1' : (b ≫ π₁) ≫ cechCoord f 1 1 = e2 := by simpa [Category.assoc] using hb1
  let z := cechTwoSimplex f e0 e1 e2 h01 h02
  let g₂ : (Opposite.op (SimplexCategory.mk 2) : SimplexCategoryᵒᵖ) ⟶
      Opposite.op (SimplexCategory.mk 1) := (SimplexCategory.δ (2 : Fin 3)).op
  let g₀ : (Opposite.op (SimplexCategory.mk 2) : SimplexCategoryᵒᵖ) ⟶
      Opposite.op (SimplexCategory.mk 1) := (SimplexCategory.δ (0 : Fin 3)).op
  have hz₂ : z ≫ (Arrow.mk f).cechNerve.map g₂ = a ≫ π₁ := by
    simpa [z, g₂, Category.assoc] using
      cechTwoSimplex_face2 f e0 e1 e2 h01 h02 (a ≫ π₁) ha0' ha1' haBase'
  have hz₀ : z ≫ (Arrow.mk f).cechNerve.map g₀ = b ≫ π₁ := by
    simpa [z, g₀, Category.assoc] using
      cechTwoSimplex_face0 f e0 e1 e2 h01 h02 (b ≫ π₁) hb0' hb1' hbBase'
  let q := (hπ g₂).lift a z hz₂.symm
  let q' := (hπ g₀).lift b z hz₀.symm
  have hq₂ : q ≫ Y.map g₂ = a := by simp [q]
  have hq'₀ : q' ≫ Y.map g₀ = b := by simp [q']
  have hq₂' : q ≫ Y.δ (2 : Fin 3) = a := by simpa [g₂, SimplicialObject.δ] using hq₂
  have hq'₀' : q' ≫ Y.δ (0 : Fin 3) = b := by simpa [g₀, SimplicialObject.δ] using hq'₀
  have hqπ : q ≫ π.app (Opposite.op (SimplexCategory.mk 2)) =
      q' ≫ π.app (Opposite.op (SimplexCategory.mk 2)) := by
    simp [q, q']
  let g₁ : (Opposite.op (SimplexCategory.mk 1) : SimplexCategoryᵒᵖ) ⟶
      Opposite.op (SimplexCategory.mk 0) := (SimplexCategory.δ (1 : Fin 2)).op
  let gm : (Opposite.op (SimplexCategory.mk 2) : SimplexCategoryᵒᵖ) ⟶
      Opposite.op (SimplexCategory.mk 0) :=
        (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 2) 1).op
  have hg₂₀ : g₂ ≫ (SimplexCategory.δ (0 : Fin 2)).op = gm := by
    apply Quiver.Hom.unop_inj
    ext i
    fin_cases i
    decide
  have hg₀₁ : g₀ ≫ g₁ = gm := by
    apply Quiver.Hom.unop_inj
    ext i
    fin_cases i
    decide
  have hmap₂₀ : Y.map g₂ ≫ Y.map ((SimplexCategory.δ (0 : Fin 2)).op) = Y.map gm := by
    rw [← Y.map_comp, hg₂₀]
  have hmap₀₁ : Y.map g₀ ≫ Y.map g₁ = Y.map gm := by
    rw [← Y.map_comp, hg₀₁]
  have hmidq : q ≫ Y.map gm = q' ≫ Y.map gm := by
    calc
      q ≫ Y.map gm = q ≫ (Y.map g₂ ≫ Y.map ((SimplexCategory.δ (0 : Fin 2)).op)) := by
        rw [← hmap₂₀]
      _ = (q ≫ Y.map g₂) ≫ Y.map ((SimplexCategory.δ (0 : Fin 2)).op) := by
        simp [Category.assoc]
      _ = a ≫ p₂ := by
        have h := congrArg (fun k => k ≫ Y.map ((SimplexCategory.δ (0 : Fin 2)).op)) hq₂
        simpa [p₂, g₂, SimplicialObject.δ] using h
      _ = b ≫ p₁ := hab
      _ = q' ≫ Y.map gm := by
        rw [← hmap₀₁]
        calc
          b ≫ p₁ = b ≫ Y.map g₁ := rfl
          _ = (q' ≫ Y.map g₀) ≫ Y.map g₁ := by rw [← hq'₀]
          _ = q' ≫ (Y.map g₀ ≫ Y.map g₁) := by simp [Category.assoc]
  have hqq' : q = q' := (hπ gm).hom_ext hmidq hqπ
  refine
    { __ := faceMaps_jointlyMono f π hπ
      c := pullback.cone p₂ p₁
      isLimit := pullback.isLimit p₂ p₁
      t := q ≫ Y.δ (1 : Fin 3)
      transitivity₁ := ?_
      transitivity₂ := ?_ }
  · calc
      (q ≫ Y.δ (1 : Fin 3)) ≫ p₁ =
          q ≫ (Y.δ (1 : Fin 3) ≫ Y.δ (1 : Fin 2)) := by simp [Category.assoc, p₁]
      _ = q ≫ (Y.δ (2 : Fin 3) ≫ Y.δ (1 : Fin 2)) := by
        simpa using congrArg (fun k => q ≫ k) (Y.δ_comp_δ_self (i := (1 : Fin 2)))
      _ = (q ≫ Y.δ (2 : Fin 3)) ≫ p₁ := by simp [Category.assoc, p₁]
      _ = a ≫ p₁ := congrArg (fun k => k ≫ p₁) hq₂'
  · calc
      (q ≫ Y.δ (1 : Fin 3)) ≫ p₂ =
          q ≫ (Y.δ (1 : Fin 3) ≫ Y.δ (0 : Fin 2)) := by simp [Category.assoc, p₂]
      _ = q ≫ (Y.δ (0 : Fin 3) ≫ Y.δ (0 : Fin 2)) := by
        simpa using congrArg (fun k => q ≫ k) (Y.δ_comp_δ_self (i := (0 : Fin 2))).symm
      _ = (q ≫ Y.δ (0 : Fin 3)) ≫ p₂ := by simp [Category.assoc, p₂]
      _ = b ≫ p₂ := by rw [hqq', hq'₀']

private noncomputable def faceMaps_symmetric {X S : C} (f : X ⟶ S)
    {Y : SimplicialObject C} (π : Y ⟶ (Arrow.mk f).cechNerve)
    (hπ : NatTrans.Equifibered π) :
    SymmetricRelation (Y.δ (1 : Fin 2)) (Y.δ (0 : Fin 2)) := by
  let p₁ := Y.δ (1 : Fin 2)
  let p₂ := Y.δ (0 : Fin 2)
  let π₀ := π.app (Opposite.op (SimplexCategory.mk 0))
  let π₁ := π.app (Opposite.op (SimplexCategory.mk 1))
  let v₀ := p₁
  let x₀ := π₁ ≫ cechCoord f 1 0
  let x₁ := π₁ ≫ cechCoord f 1 1
  have hδ₁ : (SimplexCategory.δ (1 : Fin 2)).toOrderHom (0 : Fin 1) = 0 := by decide
  have hvcoord : v₀ ≫ π₀ ≫ cechCoord f 0 0 = x₀ := by
    change p₁ ≫ π₀ ≫ cechCoord f 0 0 = π₁ ≫ cechCoord f 1 0
    simpa only [hδ₁] using face_coord f π (1 : Fin 2)
  have h01 : x₀ ≫ f = x₁ ≫ f := by
    simp [x₀, x₁, cechCoord, Category.assoc]
  have h02 : x₀ ≫ f = x₀ ≫ f := rfl
  have hedgeBase : π₁ ≫ cechBase f 1 = x₀ ≫ f := by
    simp [x₀, cechCoord, cechBase, Category.assoc]
  let z := cechTwoSimplex f x₀ x₁ x₀ h01 h02
  let g₂ : (Opposite.op (SimplexCategory.mk 2) : SimplexCategoryᵒᵖ) ⟶
      Opposite.op (SimplexCategory.mk 1) := (SimplexCategory.δ (2 : Fin 3)).op
  let g₀ : (Opposite.op (SimplexCategory.mk 2) : SimplexCategoryᵒᵖ) ⟶
      Opposite.op (SimplexCategory.mk 1) := (SimplexCategory.δ (0 : Fin 3)).op
  have hz₂ : z ≫ (Arrow.mk f).cechNerve.map g₂ = π₁ := by
    simpa [z, g₂, Category.assoc] using
      cechTwoSimplex_face2 f x₀ x₁ x₀ h01 h02 π₁ rfl rfl hedgeBase
  let q := (hπ g₂).lift (𝟙 _) z (by simpa [Category.id_comp] using hz₂.symm)
  have hq₂ : q ≫ Y.map g₂ = 𝟙 _ := by simp [q]
  have hq₂' : q ≫ Y.δ (2 : Fin 3) = 𝟙 _ := by simpa [g₂, SimplicialObject.δ] using hq₂
  have hqπ : q ≫ π.app (Opposite.op (SimplexCategory.mk 2)) = z := by simp [q]
  let gσ : (Opposite.op (SimplexCategory.mk 0) : SimplexCategoryᵒᵖ) ⟶
      Opposite.op (SimplexCategory.mk 1) := (SimplexCategory.σ (0 : Fin 1)).op
  have hσ₀ : gσ.unop.toOrderHom (0 : Fin 2) = 0 := by decide
  have hσ₁ : gσ.unop.toOrderHom (1 : Fin 2) = 0 := by decide
  let e₀ := (v₀ ≫ π₀) ≫ (Arrow.mk f).cechNerve.map gσ
  have he₀ : e₀ ≫ cechCoord f 1 0 = x₀ := by
    calc
      e₀ ≫ cechCoord f 1 0 = (v₀ ≫ π₀) ≫ (Arrow.mk f).cechNerve.map gσ ≫
          cechCoord f 1 0 := by simp [e₀, Category.assoc]
      _ = (v₀ ≫ π₀) ≫ cechCoord f 0 (gσ.unop.toOrderHom 0) := by
        simpa [Category.assoc] using post_cech_map_coord f gσ (v₀ ≫ π₀) 0
      _ = x₀ := by simpa [hσ₀] using hvcoord
  have he₁ : e₀ ≫ cechCoord f 1 1 = x₀ := by
    calc
      e₀ ≫ cechCoord f 1 1 = (v₀ ≫ π₀) ≫ (Arrow.mk f).cechNerve.map gσ ≫
          cechCoord f 1 1 := by simp [e₀, Category.assoc]
      _ = (v₀ ≫ π₀) ≫ cechCoord f 0 (gσ.unop.toOrderHom 1) := by
        simpa [Category.assoc] using post_cech_map_coord f gσ (v₀ ≫ π₀) 1
      _ = x₀ := by simpa [hσ₁] using hvcoord
  have heb : e₀ ≫ cechBase f 1 = x₀ ≫ f := by
    calc
      e₀ ≫ cechBase f 1 = (v₀ ≫ π₀) ≫ (Arrow.mk f).cechNerve.map gσ ≫
          cechBase f 1 := by simp [e₀, Category.assoc]
      _ = (v₀ ≫ π₀) ≫ cechBase f 0 := by
        simpa [Category.assoc] using post_cech_map_base f gσ (v₀ ≫ π₀)
      _ = x₀ ≫ f := by
        have hbase0 : cechBase f 0 = cechCoord f 0 0 ≫ f := by
          simp [cechBase, cechCoord]
        rw [hbase0]
        simpa [x₀, Category.assoc] using congrArg (fun k => k ≫ f) hvcoord
  have hlong : (q ≫ Y.δ (1 : Fin 3)) ≫ π₁ = e₀ := by
    calc
      (q ≫ Y.δ (1 : Fin 3)) ≫ π₁ = q ≫ (Y.δ (1 : Fin 3) ≫ π₁) := by simp [Category.assoc]
      _ = q ≫ (π.app (Opposite.op (SimplexCategory.mk 2)) ≫
          (Arrow.mk f).cechNerve.map ((SimplexCategory.δ (1 : Fin 3)).op)) :=
            congrArg (fun k => q ≫ k) (SimplicialObject.δ_naturality π (1 : Fin 3))
      _ = (q ≫ π.app (Opposite.op (SimplexCategory.mk 2))) ≫
          (Arrow.mk f).cechNerve.map ((SimplexCategory.δ (1 : Fin 3)).op) := by
            simp [Category.assoc]
      _ = z ≫ (Arrow.mk f).cechNerve.map ((SimplexCategory.δ (1 : Fin 3)).op) := by rw [hqπ]
      _ = e₀ := by
        simpa [z, gσ, e₀] using
          cechTwoSimplex_face1 f x₀ x₁ x₀ h01 h02 e₀ he₀ he₁ heb
  let w := (hπ gσ).lift (q ≫ Y.δ (1 : Fin 3)) (v₀ ≫ π₀) hlong
  have hwσ : w ≫ Y.map gσ = q ≫ Y.δ (1 : Fin 3) := by simp [w]
  have hsource : (q ≫ Y.δ (1 : Fin 3)) ≫ Y.δ (1 : Fin 2) = v₀ := by
    calc
      (q ≫ Y.δ (1 : Fin 3)) ≫ Y.δ (1 : Fin 2) =
          q ≫ (Y.δ (1 : Fin 3) ≫ Y.δ (1 : Fin 2)) := by simp [Category.assoc]
      _ = q ≫ (Y.δ (2 : Fin 3) ≫ Y.δ (1 : Fin 2)) := by
        simpa using congrArg (fun k => q ≫ k)
          (Y.δ_comp_δ_self (i := (1 : Fin 2)))
      _ = (q ≫ Y.δ (2 : Fin 3)) ≫ Y.δ (1 : Fin 2) := by simp [Category.assoc]
      _ = v₀ := by simpa [v₀, p₁] using congrArg (fun k => k ≫ Y.δ (1 : Fin 2)) hq₂'
  have hw : w = v₀ := by
    calc
      w = w ≫ 𝟙 _ := by simp
      _ = w ≫ (Y.σ (0 : Fin 1) ≫ Y.δ (1 : Fin 2)) :=
        congrArg (fun k => w ≫ k) (Y.δ_comp_σ_succ (i := (0 : Fin 1))).symm
      _ = (w ≫ Y.σ (0 : Fin 1)) ≫ Y.δ (1 : Fin 2) := by simp [Category.assoc]
      _ = (w ≫ Y.map gσ) ≫ Y.δ (1 : Fin 2) := by
        simp [gσ, SimplicialObject.σ]
      _ = (q ≫ Y.δ (1 : Fin 3)) ≫ Y.δ (1 : Fin 2) := by rw [hwσ]
      _ = v₀ := hsource
  have hdeg : q ≫ Y.δ (1 : Fin 3) = v₀ ≫ Y.σ (0 : Fin 1) := by
    calc
      q ≫ Y.δ (1 : Fin 3) = w ≫ Y.map gσ := hwσ.symm
      _ = v₀ ≫ Y.σ (0 : Fin 1) := by
        rw [hw]
        simp [gσ, SimplicialObject.σ]
  refine
    { __ := faceMaps_jointlyMono f π hπ
      s := q ≫ Y.δ (0 : Fin 3)
      symmetry₁ := ?_
      symmetry₂ := ?_ }
  · calc
      (q ≫ Y.δ (0 : Fin 3)) ≫ p₁ =
          q ≫ (Y.δ (0 : Fin 3) ≫ Y.δ (1 : Fin 2)) := by simp [Category.assoc, p₁]
      _ = q ≫ (Y.δ (2 : Fin 3) ≫ Y.δ (0 : Fin 2)) := by
        have htri : Y.δ (0 : Fin 3) ≫ Y.δ (1 : Fin 2) =
            Y.δ (2 : Fin 3) ≫ Y.δ (0 : Fin 2) := by
          simpa using (Y.δ_comp_δ (i := (0 : Fin 2)) (j := (1 : Fin 2))
            (by decide : (0 : Fin 2) ≤ 1)).symm
        exact congrArg (fun k => q ≫ k) htri
      _ = (q ≫ Y.δ (2 : Fin 3)) ≫ p₂ := by simp [Category.assoc, p₂]
      _ = p₂ := by simpa [p₂] using congrArg (fun k => k ≫ p₂) hq₂'
  · calc
      (q ≫ Y.δ (0 : Fin 3)) ≫ p₂ =
          q ≫ (Y.δ (0 : Fin 3) ≫ Y.δ (0 : Fin 2)) := by simp [Category.assoc, p₂]
      _ = q ≫ (Y.δ (1 : Fin 3) ≫ Y.δ (0 : Fin 2)) := by
        simpa using congrArg (fun k => q ≫ k)
          (Y.δ_comp_δ_self (i := (0 : Fin 2)))
      _ = (q ≫ Y.δ (1 : Fin 3)) ≫ Y.δ (0 : Fin 2) := by simp [Category.assoc]
      _ = v₀ := by
        rw [hdeg]
        calc
          (v₀ ≫ Y.σ (0 : Fin 1)) ≫ Y.δ (0 : Fin 2) =
              v₀ ≫ (Y.σ (0 : Fin 1) ≫ Y.δ (0 : Fin 2)) := by simp [Category.assoc]
          _ = v₀ ≫ 𝟙 _ :=
            congrArg (fun k => v₀ ≫ k) (Y.δ_comp_σ_self (i := (0 : Fin 1)))
          _ = v₀ := by simp

/-- If a simplicial object maps cartesianly to the Čech nerve of `f`, its two
face maps from degree one form an internal equivalence relation. -/
@[stacks 024E, sga "4 I 10.9" "special case"]
theorem isEquivalenceRelation_faceMaps_of_equifibered {X S : C} (f : X ⟶ S)
    {Y : SimplicialObject C} (π : Y ⟶ (Arrow.mk f).cechNerve)
    (hπ : NatTrans.Equifibered π) :
    IsEquivalenceRelation (Y.δ (1 : Fin 2)) (Y.δ (0 : Fin 2)) := by
  let hsym := faceMaps_symmetric f π hπ
  let htrans := faceMaps_transitive f π hπ
  refine ⟨⟨{
    toReflexiveRelation := faceMaps_reflexive f π hπ
    s := hsym.s
    symmetry₁ := hsym.symmetry₁
    symmetry₂ := hsym.symmetry₂
    c := htrans.c
    isLimit := htrans.isLimit
    t := htrans.t
    transitivity₁ := htrans.transitivity₁
    transitivity₂ := htrans.transitivity₂
  }⟩⟩

end CategoryTheory.SimplicialObject

end
