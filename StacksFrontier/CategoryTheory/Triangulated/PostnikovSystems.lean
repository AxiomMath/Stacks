module

public import StacksFrontier.CategoryTheory.Triangulated.Elementary
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.ReduceModChar

/-!
# Postnikov systems

Let `D` be a pretriangulated category and let `Xₙ ⟶ Xₙ₋₁ ⟶ ⋯ ⟶ X₀` be a complex in `D`, with
morphisms `d i : Xᵢ₊₁ ⟶ Xᵢ`. A *Postnikov system* for it, `CategoryTheory.Triangulated.
PostnikovSystem`, is a family of objects `Y₀, …, Yₙ` together with an isomorphism `Y₀ ⟶ X₀` and
distinguished triangles `Yᵢ₊₁ ⟶ Xᵢ₊₁ ⟶ Yᵢ ⟶ Yᵢ₊₁⟦1⟧` in which the composition
`Xᵢ₊₁ ⟶ Yᵢ ⟶ Xᵢ` is the given `d i`. The last object `Yₙ` is a *totalization* of the complex, and
this file settles when such a system exists, when a morphism of complexes extends to one of
systems, and when the extension is unique on the totalizations.

## Main definitions

* `CategoryTheory.Triangulated.PostnikovSystem`: a Postnikov system for a complex.
* `CategoryTheory.Triangulated.PostnikovSystem.Hom`: a morphism of Postnikov systems over a
  family of morphisms of the two complexes, with its identity and composition.

## Main results

* `CategoryTheory.Triangulated.nonempty_postnikovSystem_of_length_le_two`: a complex of length
  `n ≤ 2` admits a Postnikov system.
* `CategoryTheory.Triangulated.PostnikovSystem.hom_shift_obj_eq_zero_and_exists_hom`: the
  vanishing of `Hom(Xᵢ⟦i - j - 1⟧, X'ⱼ)` for `i > j + 1` passes to the objects of a Postnikov
  system, and a morphism of complexes then extends to a (nonunique) morphism of Postnikov systems.
* `CategoryTheory.Triangulated.nonempty_postnikovSystem_of_hom_shift_eq_zero`: a complex all of
  whose `Hom(Xᵢ⟦i - j - 2⟧, Xⱼ)` with `i > j + 2` vanish admits a Postnikov system.
* `CategoryTheory.Triangulated.PostnikovSystem.exists_iso`: if every `Hom(Xᵢ⟦i - j - 1⟧, Xⱼ)`
  with `i > j + 1` vanishes, any two Postnikov systems over isomorphic complexes are isomorphic
  over the given isomorphism.
* `CategoryTheory.Triangulated.PostnikovSystem.subsingleton_hom_last`: under any one of the three
  vanishing hypotheses, two morphisms of Postnikov systems over the same morphism of complexes
  agree on the totalizations.
* `CategoryTheory.Triangulated.PostnikovSystem.subsingleton_hom_of_hom_shift_eq_zero`: under the
  third vanishing hypothesis there is at most one morphism of Postnikov systems over a given
  morphism of complexes. Under the first two the intermediate components are not determined
  (`StacksFrontier.CategoryTheory.Triangulated.PostnikovSystemsCounterexample`).
* `CategoryTheory.Triangulated.PostnikovSystem.map`: a triangulated functor carries a Postnikov
  system to a Postnikov system for the image complex.

## Implementation notes

The ambient category is assumed pretriangulated throughout: only the existence of distinguished
triangles, the rotation axiom and TR3 are used, never the octahedron axiom, so nothing here needs
`IsTriangulated D`.

Vanishing hypotheses are stated as "every morphism of this type is zero" rather than as the
vanishing of a `Hom`-group, and the shift appearing in them is an arbitrary integer equal to the
intended one: the utilities `eq_zero_of_shift_eq`, `eq_zero_of_shift_shift` and
`eq_zero_of_shift_iso` move a hypothesis between `A⟦a⟧`, `A⟦b⟧⟦c⟧` and `A⟦a'⟧` for `a = a'`, so a
caller never has to produce a shift in a particular normal form.

The uniqueness statement is phrased as `Set.Subsingleton` of the image of the set of morphisms of
Postnikov systems under evaluation at the last index, which says exactly that the totalization
component is determined without asserting that any such morphism exists — the existence being the
separate statement above.

## References

* [Stacks project, Tag 0D81](https://stacks.math.columbia.edu/tag/0D81)
* [Stacks project, Tag 0D82](https://stacks.math.columbia.edu/tag/0D82)
* [Stacks project, Tag 0D83](https://stacks.math.columbia.edu/tag/0D83)
* [Stacks project, Tag 0FXE](https://stacks.math.columbia.edu/tag/0FXE)
* [Stacks project, Tag 0D7Z](https://stacks.math.columbia.edu/tag/0D7Z)
* [Dmitri Orlov, *Derived categories of coherent sheaves and equivalences between them*]
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

universe v u

namespace CategoryTheory.Triangulated

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-! ### The definition of a Postnikov system -/

/-- A *Postnikov system* for a complex `Xₙ ⟶ Xₙ₋₁ ⟶ ⋯ ⟶ X₀` in a pretriangulated category,
the morphisms of the complex being `d i : X i.succ ⟶ X i.castSucc`: objects `Y₀, …, Yₙ` together
with an isomorphism `Y₀ ⟶ X₀` and distinguished triangles
`Yᵢ₊₁ ⟶ Xᵢ₊₁ ⟶ Yᵢ ⟶ Yᵢ₊₁⟦1⟧` in which the composition `Xᵢ₊₁ ⟶ Yᵢ ⟶ Xᵢ` is the given morphism
`Xᵢ₊₁ ⟶ Xᵢ`. The morphisms of Postnikov systems, the second notion of this Stacks definition, are
`CategoryTheory.Triangulated.PostnikovSystem.Hom`. -/
@[stacks 0D7Z "Postnikov system; the morphisms of Postnikov systems are `PostnikovSystem.Hom`"]
public structure PostnikovSystem {n : ℕ} (X : Fin (n + 1) → D)
    (d : ∀ i : Fin n, X i.succ ⟶ X i.castSucc) where
  /-- the objects `Yᵢ` of the Postnikov system -/
  obj : Fin (n + 1) → D
  /-- the morphisms `Yᵢ ⟶ Xᵢ` to the terms of the complex -/
  π : ∀ i, obj i ⟶ X i
  /-- the morphism `Y₀ ⟶ X₀` is an isomorphism -/
  isIso_π_zero : IsIso (π 0) := by infer_instance
  /-- the morphisms `Xᵢ₊₁ ⟶ Yᵢ` -/
  p : ∀ i : Fin n, X i.succ ⟶ obj i.castSucc
  /-- the connecting morphisms `Yᵢ ⟶ Yᵢ₊₁⟦1⟧` -/
  δ : ∀ i : Fin n, obj i.castSucc ⟶ (obj i.succ)⟦(1 : ℤ)⟧
  /-- the triangles `Yᵢ₊₁ ⟶ Xᵢ₊₁ ⟶ Yᵢ ⟶ Yᵢ₊₁⟦1⟧` are distinguished -/
  distinguished : ∀ i : Fin n, Triangle.mk (π i.succ) (p i) (δ i) ∈ distTriang D
  /-- the composition `Xᵢ₊₁ ⟶ Yᵢ ⟶ Xᵢ` is the morphism `Xᵢ₊₁ ⟶ Xᵢ` of the complex -/
  p_comp_π : ∀ i : Fin n, p i ≫ π i.castSucc = d i

attribute [instance] PostnikovSystem.isIso_π_zero

/-! ### Morphisms of Postnikov systems -/

namespace PostnikovSystem

variable {n : ℕ} {X X' X'' : Fin (n + 1) → D} {d : ∀ i : Fin n, X i.succ ⟶ X i.castSucc}
  {d' : ∀ i : Fin n, X' i.succ ⟶ X' i.castSucc} {d'' : ∀ i : Fin n, X'' i.succ ⟶ X'' i.castSucc}

/-- A *morphism of Postnikov systems* `S ⟶ S'` lying over a family of morphisms
`f i : Xᵢ ⟶ X'ᵢ` between two complexes `Xₙ ⟶ ⋯ ⟶ X₀` and `X'ₙ ⟶ ⋯ ⟶ X'₀` of the same length:
morphisms `hom i : Yᵢ ⟶ Y'ᵢ` making every diagram of the two systems commute, that is compatible
with the morphisms `Yᵢ ⟶ Xᵢ`, `Xᵢ₊₁ ⟶ Yᵢ` and `Yᵢ ⟶ Yᵢ₊₁⟦1⟧`. Equivalently, `f` and `hom`
form morphisms of all the distinguished triangles `Yᵢ₊₁ ⟶ Xᵢ₊₁ ⟶ Yᵢ ⟶ Yᵢ₊₁⟦1⟧` of the two
systems. That `f` is a morphism of complexes is not imposed: it follows, see `Hom.comm_d`. -/
@[stacks 0D7Z "morphism of Postnikov systems"]
public structure Hom (f : ∀ i, X i ⟶ X' i) (S : PostnikovSystem X d)
    (S' : PostnikovSystem X' d') where
  /-- the components `Yᵢ ⟶ Y'ᵢ` of the morphism -/
  hom : ∀ i, S.obj i ⟶ S'.obj i
  /-- compatibility with the morphisms `Yᵢ ⟶ Xᵢ` and `Y'ᵢ ⟶ X'ᵢ` -/
  comm_π : ∀ i, hom i ≫ S'.π i = S.π i ≫ f i
  /-- compatibility with the morphisms `Xᵢ₊₁ ⟶ Yᵢ` and `X'ᵢ₊₁ ⟶ Y'ᵢ` -/
  comm_p : ∀ i : Fin n, S.p i ≫ hom i.castSucc = f i.succ ≫ S'.p i
  /-- compatibility with the connecting morphisms `Yᵢ ⟶ Yᵢ₊₁⟦1⟧` and `Y'ᵢ ⟶ Y'ᵢ₊₁⟦1⟧` -/
  comm_δ : ∀ i : Fin n, S.δ i ≫ (hom i.succ)⟦(1 : ℤ)⟧' = hom i.castSucc ≫ S'.δ i

namespace Hom

/-- The family of morphisms underlying a morphism of Postnikov systems is a morphism of
complexes. -/
lemma comm_d {f : ∀ i, X i ⟶ X' i} {S : PostnikovSystem X d} {S' : PostnikovSystem X' d'}
    (g : Hom f S S') (i : Fin n) : d i ≫ f i.castSucc = f i.succ ≫ d' i := by
  rw [← S.p_comp_π, ← S'.p_comp_π, Category.assoc, ← g.comm_π, ← Category.assoc, g.comm_p,
    Category.assoc]

/-- The `i`-th component of a morphism of Postnikov systems, together with the morphisms of the
complexes, is a morphism of the `i`-th distinguished triangles. -/
@[simps]
def triangleHom {f : ∀ i, X i ⟶ X' i} {S : PostnikovSystem X d} {S' : PostnikovSystem X' d'}
    (g : Hom f S S') (i : Fin n) :
    Triangle.mk (S.π i.succ) (S.p i) (S.δ i) ⟶ Triangle.mk (S'.π i.succ) (S'.p i) (S'.δ i) where
  hom₁ := g.hom i.succ
  hom₂ := f i.succ
  hom₃ := g.hom i.castSucc
  comm₁ := (g.comm_π i.succ).symm
  comm₂ := g.comm_p i
  comm₃ := g.comm_δ i

/-- The identity morphism of a Postnikov system, over the identity of the complex. -/
@[simps]
def id (S : PostnikovSystem X d) : Hom (fun i => 𝟙 (X i)) S S where
  hom i := 𝟙 _
  comm_π i := by simp
  comm_p i := by simp
  comm_δ i := by simp

/-- The composition of morphisms of Postnikov systems, over the composition of the morphisms of
complexes. -/
@[simps]
def comp {f : ∀ i, X i ⟶ X' i} {f' : ∀ i, X' i ⟶ X'' i} {S : PostnikovSystem X d}
    {S' : PostnikovSystem X' d'} {S'' : PostnikovSystem X'' d''} (g : Hom f S S')
    (g' : Hom f' S' S'') : Hom (fun i => f i ≫ f' i) S S'' where
  hom i := g.hom i ≫ g'.hom i
  comm_π i := by rw [Category.assoc, g'.comm_π, ← Category.assoc, g.comm_π, Category.assoc]
  comm_p i := by rw [← Category.assoc, g.comm_p, Category.assoc, g'.comm_p, Category.assoc]
  comm_δ i := by
    rw [Functor.map_comp, ← Category.assoc, g.comm_δ, Category.assoc, g'.comm_δ, Category.assoc]

/-- Two morphisms of Postnikov systems over the same family `f` are equal as soon as their
components are. -/
@[ext]
lemma ext {f : ∀ i, X i ⟶ X' i} {S : PostnikovSystem X d} {S' : PostnikovSystem X' d'}
    {g g' : Hom f S S'} (h : ∀ i, g.hom i = g'.hom i) : g = g' := by
  cases g; cases g'; congr; funext i; exact h i

end Hom

end PostnikovSystem

/-! ### Vanishing of `Hom`-groups out of, and into, a shifted object -/

omit [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] in
/-- Vanishing of `Hom(A⟦a⟧, B)` depends on the shift `a` only through its value. -/
private lemma eq_zero_of_shift_eq {A B : D} {a a' : ℤ} (haa' : a = a')
    (h : ∀ v : A⟦a⟧ ⟶ B, v = 0) (u : A⟦a'⟧ ⟶ B) : u = 0 := by
  subst haa'; exact h u

omit [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] in
/-- Vanishing of `Hom(A⟦a⟧, B)` is inherited by `Hom(A⟦b⟧⟦c⟧, B)` when `b + c = a`. -/
private lemma eq_zero_of_shift_shift {A B : D} {a b c : ℤ} (habc : b + c = a)
    (h : ∀ v : A⟦a⟧ ⟶ B, v = 0) (u : (A⟦b⟧)⟦c⟧ ⟶ B) : u = 0 := by
  have e := (shiftFunctorAdd' D b c a habc).app A
  rw [← cancel_epi e.hom, h (e.hom ≫ u), comp_zero]

omit [HasZeroObject D] [Pretriangulated D] in
/-- If `Hom(A⟦1⟧, B) = 0` then `Hom(A, B⟦-1⟧) = 0`. -/
private lemma eq_zero_of_shift_hom_eq_zero {A B : D} (h : ∀ v : A⟦(1 : ℤ)⟧ ⟶ B, v = 0)
    (u : A ⟶ B⟦(-1 : ℤ)⟧) : u = 0 := by
  apply (shiftFunctor D (1 : ℤ)).map_injective
  rw [Functor.map_zero,
    ← cancel_mono ((shiftFunctorCompIsoId D (-1) (1 : ℤ) (by ring)).app B).hom, zero_comp,
    h (u⟦(1 : ℤ)⟧' ≫ ((shiftFunctorCompIsoId D (-1) (1 : ℤ) (by ring)).app B).hom)]

omit [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] in
/-- Vanishing of a `Hom` group transfers along isomorphisms in both variables. -/
private lemma eq_zero_of_iso {A A' B B' : D} (eA : A ≅ A') (eB : B ≅ B')
    (h : ∀ u : A' ⟶ B', u = 0) (u : A ⟶ B) : u = 0 := by
  calc u = eA.hom ≫ (eA.inv ≫ u ≫ eB.hom) ≫ eB.inv := by simp
    _ = 0 := by rw [h (eA.inv ≫ u ≫ eB.hom)]; simp

omit [HasZeroObject D] [Pretriangulated D] in
/-- Vanishing of a `Hom` group is preserved by shifting both variables. -/
private lemma eq_zero_shift {A B : D} (m : ℤ) (h : ∀ u : A ⟶ B, u = 0)
    (u : A⟦m⟧ ⟶ B⟦m⟧) : u = 0 := by
  obtain ⟨v, rfl⟩ := (shiftFunctor D m).map_surjective u
  rw [h v, Functor.map_zero]

/-- The comparison isomorphism `A⟦c⟧ ≅ A⟦a⟧⟦b⟧` attached to an equation `a + b = c`. -/
private abbrev shiftShiftIso (A : D) {a b c : ℤ} (h : a + b = c) : A⟦c⟧ ≅ (A⟦a⟧)⟦b⟧ :=
  (shiftFunctorAdd' D a b c h).app A

/-- The comparison isomorphism `A ≅ A⟦a⟧⟦b⟧` attached to an equation `a + b = 0`. -/
private abbrev shiftShiftIsoSelf (A : D) {a b : ℤ} (h : a + b = 0) : A ≅ (A⟦a⟧)⟦b⟧ :=
  ((shiftFunctorCompIsoId D a b h).app A).symm

omit [HasZeroObject D] [Pretriangulated D] in
/-- Vanishing of a `Hom` group transfers to the shift of both of its variables, along any two
comparison isomorphisms. -/
private lemma eq_zero_of_shift_iso {A B A' B' : D} (b : ℤ) (H : ∀ u : A ⟶ B, u = 0)
    (eA : A' ≅ A⟦b⟧) (eB : B' ≅ B⟦b⟧) (u : A' ⟶ B') : u = 0 :=
  eq_zero_of_iso eA eB (eq_zero_shift b H) u

/-! ### Exactness of `Hom(W, -)` along a distinguished triangle -/

/-- A morphism into the second object of a distinguished triangle `A ⟶ B ⟶ C` is determined by
its corestriction to `C` as soon as `Hom(W, A) = 0`. -/
private lemma hom_ext_obj₂ {T : Triangle D} (hT : T ∈ distTriang D) {W : D}
    (h : ∀ u : W ⟶ T.obj₁, u = 0) {a b : W ⟶ T.obj₂} (hab : a ≫ T.mor₂ = b ≫ T.mor₂) : a = b := by
  obtain ⟨c, hc⟩ := T.coyoneda_exact₂ hT (a - b) (by rw [Preadditive.sub_comp, hab, sub_self])
  rw [h c, zero_comp, sub_eq_zero] at hc
  exact hc

/-- A morphism into the first object of a distinguished triangle `A ⟶ B ⟶ C` is determined by
its corestriction to `B` as soon as `Hom(W⟦1⟧, C) = 0`. -/
private lemma hom_ext_obj₁ {T : Triangle D} (hT : T ∈ distTriang D) {W : D}
    (h : ∀ u : W⟦(1 : ℤ)⟧ ⟶ T.obj₃, u = 0) {a b : W ⟶ T.obj₁}
    (hab : a ≫ T.mor₁ = b ≫ T.mor₁) : a = b :=
  hom_ext_obj₂ (inv_rot_of_distTriang _ hT) (eq_zero_of_shift_hom_eq_zero h) hab

/-- A morphism into the first object of a distinguished triangle `A ⟶ B ⟶ C` is determined by
its corestriction to `B` as soon as `Hom(W, C⟦-1⟧) = 0`. -/
private lemma hom_ext_obj₁' {T : Triangle D} (hT : T ∈ distTriang D) {W : D}
    (h : ∀ u : W ⟶ T.obj₃⟦(-1 : ℤ)⟧, u = 0) {a b : W ⟶ T.obj₁}
    (hab : a ≫ T.mor₁ = b ≫ T.mor₁) : a = b :=
  hom_ext_obj₂ (inv_rot_of_distTriang _ hT) h hab

/-- Exactness of `Hom(W, -)`: if `Hom(W, B) = 0` and `Hom(W⟦1⟧, C) = 0` for a distinguished
triangle `A ⟶ B ⟶ C`, then `Hom(W, A) = 0`. -/
private lemma eq_zero_obj₁ {T : Triangle D} (hT : T ∈ distTriang D) {W : D}
    (h₂ : ∀ u : W ⟶ T.obj₂, u = 0) (h₃ : ∀ u : W⟦(1 : ℤ)⟧ ⟶ T.obj₃, u = 0) (u : W ⟶ T.obj₁) :
    u = 0 :=
  hom_ext_obj₁ hT h₃ (a := u) (b := 0) (by rw [h₂ (u ≫ T.mor₁), zero_comp])

/-- Exactness of `Hom(W, -)`: if `Hom(W, A) = 0` and `Hom(W, C) = 0` for a distinguished
triangle `A ⟶ B ⟶ C`, then `Hom(W, B) = 0`. -/
private lemma eq_zero_obj₂ {T : Triangle D} (hT : T ∈ distTriang D) {W : D}
    (h₁ : ∀ u : W ⟶ T.obj₁, u = 0) (h₃ : ∀ u : W ⟶ T.obj₃, u = 0)
    (u : W ⟶ T.obj₂) : u = 0 :=
  hom_ext_obj₂ hT h₁ (a := u) (b := 0) (by rw [h₃ (u ≫ T.mor₂), zero_comp])

/-- Exactness of `Hom(W, -)`: if `Hom(W, B) = 0` and `Hom(W, C⟦-1⟧) = 0` for a distinguished
triangle `A ⟶ B ⟶ C`, then `Hom(W, A) = 0`. -/
private lemma eq_zero_obj₁' {T : Triangle D} (hT : T ∈ distTriang D) {W : D}
    (h₂ : ∀ u : W ⟶ T.obj₂, u = 0) (h₃ : ∀ u : W ⟶ T.obj₃⟦(-1 : ℤ)⟧, u = 0)
    (u : W ⟶ T.obj₁) : u = 0 :=
  eq_zero_obj₂ (inv_rot_of_distTriang _ hT) h₃ h₂ u

/-! ### Exactness of `Hom(-, W)` along a distinguished triangle -/

/-- A morphism out of the second object of a distinguished triangle `A ⟶ B ⟶ C` is determined
by its restriction to `A` as soon as `Hom(C, W) = 0`. -/
private lemma hom_ext_hom_obj₂ {T : Triangle D} (hT : T ∈ distTriang D) {W : D}
    (h : ∀ u : T.obj₃ ⟶ W, u = 0) {a b : T.obj₂ ⟶ W}
    (hab : T.mor₁ ≫ a = T.mor₁ ≫ b) : a = b := by
  obtain ⟨c, hc⟩ := T.yoneda_exact₂ hT (a - b) (by rw [Preadditive.comp_sub, hab, sub_self])
  rw [h c, comp_zero, sub_eq_zero] at hc
  exact hc

/-- Exactness of `Hom(-, W)`: if `Hom(A, W) = 0` and `Hom(C, W) = 0` for a distinguished
triangle `A ⟶ B ⟶ C`, then `Hom(B, W) = 0`. -/
private lemma eq_zero_hom_obj₂ {T : Triangle D} (hT : T ∈ distTriang D) {W : D}
    (h₁ : ∀ u : T.obj₁ ⟶ W, u = 0) (h₃ : ∀ u : T.obj₃ ⟶ W, u = 0)
    (u : T.obj₂ ⟶ W) : u = 0 :=
  hom_ext_hom_obj₂ hT h₃ (a := u) (b := 0) (by rw [h₁ (T.mor₁ ≫ u), comp_zero])

/-- Exactness of `Hom(-, W)`: if `Hom(B, W) = 0` and `Hom(C⟦-1⟧, W) = 0` for a distinguished
triangle `A ⟶ B ⟶ C`, then `Hom(A, W) = 0`. -/
private lemma eq_zero_hom_obj₁ {T : Triangle D} (hT : T ∈ distTriang D) {W : D}
    (h₂ : ∀ u : T.obj₂ ⟶ W, u = 0) (h₃ : ∀ u : T.obj₃⟦(-1 : ℤ)⟧ ⟶ W, u = 0)
    (u : T.obj₁ ⟶ W) : u = 0 :=
  eq_zero_hom_obj₂ (inv_rot_of_distTriang _ hT) h₃ h₂ u

/-! ### Existence for complexes of length at most two -/

/-- A complex of length `0`, that is a single object `X₀`, carries the Postnikov system
`Y₀ = X₀` with the identity as its isomorphism `Y₀ ⟶ X₀`. -/
private lemma nonempty_postnikovSystem_of_length_zero (X : Fin 1 → D)
    (d : ∀ i : Fin 0, X i.succ ⟶ X i.castSucc) : Nonempty (PostnikovSystem X d) :=
  ⟨{ obj := X
     π := fun _ => 𝟙 _
     p := fun i => i.elim0
     δ := fun i => i.elim0
     distinguished := fun i => i.elim0
     p_comp_π := fun i => i.elim0 }⟩

/-- A complex `X₁ ⟶ X₀` of length `1` carries a Postnikov system. -/
private lemma nonempty_postnikovSystem_of_length_one (X : Fin 2 → D)
    (d : ∀ i : Fin 1, X i.succ ⟶ X i.castSucc) : Nonempty (PostnikovSystem X d) := by
  obtain ⟨Y₁, a, e₀, hT⟩ := distinguished_cocone_triangle₁ (d 0)
  refine ⟨{ obj := ![X 0, Y₁]
            π := fun i => match i with
              | ⟨0, _⟩ => 𝟙 _
              | ⟨1, _⟩ => a
            p := fun i => match i with
              | ⟨0, _⟩ => d 0
            δ := fun i => match i with
              | ⟨0, _⟩ => e₀
            isIso_π_zero := ?_
            distinguished := ?_
            p_comp_π := ?_ }⟩
  · exact inferInstanceAs (IsIso (𝟙 (X 0)))
  · intro i
    match i with
    | ⟨0, _⟩ => exact hT
  · intro i
    match i with
    | ⟨0, _⟩ => exact Category.comp_id _

/-- A complex `X₂ ⟶ X₁ ⟶ X₀` of length `2` whose composition vanishes carries a Postnikov
system. -/
private lemma nonempty_postnikovSystem_of_length_two (X : Fin 3 → D)
    (d : ∀ i : Fin 2, X i.succ ⟶ X i.castSucc) (hd : d 1 ≫ d 0 = 0) :
    Nonempty (PostnikovSystem X d) := by
  obtain ⟨Y₁, a, e₀, hT₀⟩ := distinguished_cocone_triangle₁ (d 0)
  obtain ⟨q, hq⟩ : ∃ q : X 2 ⟶ Y₁, d 1 = q ≫ a :=
    (Triangle.mk a (d 0) e₀).coyoneda_exact₂ hT₀ (d 1) hd
  obtain ⟨Y₂, b, e₁, hT₁⟩ := distinguished_cocone_triangle₁ q
  refine ⟨{ obj := ![X 0, Y₁, Y₂]
            π := fun i => match i with
              | ⟨0, _⟩ => 𝟙 _
              | ⟨1, _⟩ => a
              | ⟨2, _⟩ => b
            p := fun i => match i with
              | ⟨0, _⟩ => d 0
              | ⟨1, _⟩ => q
            δ := fun i => match i with
              | ⟨0, _⟩ => e₀
              | ⟨1, _⟩ => e₁
            isIso_π_zero := ?_
            distinguished := ?_
            p_comp_π := ?_ }⟩
  · exact inferInstanceAs (IsIso (𝟙 (X 0)))
  · intro i
    match i with
    | ⟨0, _⟩ => exact hT₀
    | ⟨1, _⟩ => exact hT₁
  · intro i
    match i with
    | ⟨0, _⟩ => exact Category.comp_id _
    | ⟨1, _⟩ => exact hq.symm

/-- A complex `Xₙ ⟶ Xₙ₋₁ ⟶ ⋯ ⟶ X₀` of length `n ≤ 2` in a pretriangulated category admits a
Postnikov system. The bound is sharp: for `n > 2` Postnikov systems do not always exist, see
`postnikovSystem_small_cases`. -/
theorem nonempty_postnikovSystem_of_length_le_two {n : ℕ}
    (hn : n ≤ 2) (X : Fin (n + 1) → D) (d : ∀ i : Fin n, X i.succ ⟶ X i.castSucc)
    (hd : ∀ (i : Fin n) (h : (i : ℕ) + 1 < n), d ⟨(i : ℕ) + 1, h⟩ ≫ d i = 0) :
    Nonempty (PostnikovSystem X d) := by
  interval_cases n
  · exact nonempty_postnikovSystem_of_length_zero X d
  · exact nonempty_postnikovSystem_of_length_one X d
  · exact nonempty_postnikovSystem_of_length_two X d (hd 0 (by norm_num))

/-! ### Vanishing along a Postnikov system -/

/-- Let `S` be a Postnikov system for `Xₙ ⟶ ⋯ ⟶ X₀`, with objects `Yⱼ`, let `W` be an object and
let `c` be an integer. If `Hom(W⟦c - k⟧, Xₖ) = 0` for all `k ≤ j` then `Hom(W⟦c - j⟧, Yⱼ) = 0`. -/
private lemma eq_zero_of_hom_shift_eq_zero {m : ℕ} {X : Fin (m + 1) → D}
    {d : ∀ i : Fin m, X i.succ ⟶ X i.castSucc} (S : PostnikovSystem X d) {W : D} (c : ℤ) :
    ∀ j : Fin (m + 1), (∀ k : Fin (m + 1), (k : ℕ) ≤ (j : ℕ) →
        ∀ u : W⟦c - ((k : ℕ) : ℤ)⟧ ⟶ X k, u = 0) →
      ∀ u : W⟦c - ((j : ℕ) : ℤ)⟧ ⟶ S.obj j, u = 0 := by
  intro j
  induction j using Fin.induction with
  | zero =>
    intro h u
    rw [← cancel_mono (S.π 0), h 0 le_rfl (u ≫ S.π 0), zero_comp]
  | succ j ih =>
    intro h u
    refine eq_zero_obj₁ (S.distinguished j) (h j.succ le_rfl) (fun v => ?_) u
    refine eq_zero_of_shift_shift (by simp only [Fin.val_succ, Fin.val_castSucc]; push_cast; ring)
      (ih (fun k hk => h k (by simp only [Fin.val_castSucc, Fin.val_succ] at hk ⊢; omega))) v

/-- A morphism `α : W ⟶ Yᵢ` into an object of a Postnikov system which dies against the morphism
`Yᵢ ⟶ Xᵢ` is zero, provided `Hom(W⟦1⟧, Yᵢ₋₁) = 0`. -/
private lemma eq_zero_of_comp_π_eq_zero {m : ℕ} {X : Fin (m + 1) → D}
    {d : ∀ i : Fin m, X i.succ ⟶ X i.castSucc} (S : PostnikovSystem X d) {W : D} :
    ∀ i : Fin (m + 1), (∀ k : Fin (m + 1), (k : ℕ) + 1 = (i : ℕ) →
        ∀ v : W⟦(1 : ℤ)⟧ ⟶ S.obj k, v = 0) →
      ∀ α : W ⟶ S.obj i, α ≫ S.π i = 0 → α = 0 := by
  intro i
  induction i using Fin.cases with
  | zero =>
    intro _ α hα
    rw [← cancel_mono (S.π 0), hα, zero_comp]
  | succ k =>
    intro hW α hα
    exact hom_ext_obj₁ (S.distinguished k) (hW k.castSucc (by simp)) (b := 0) (by simpa using hα)

/-! ### Extending a morphism of complexes -/

section Extend

variable {n : ℕ} {X X' : Fin (n + 1) → D} {d : ∀ i : Fin n, X i.succ ⟶ X i.castSucc}
  {d' : ∀ i : Fin n, X' i.succ ⟶ X' i.castSucc}

/-- The vanishing of every `Hom(Xᵢ⟦i - j - 1⟧, X'ⱼ)` with `i > j + 1` passes to the objects `Y'ⱼ`
of a Postnikov system for `X'ₙ ⟶ ⋯ ⟶ X'₀`. -/
private lemma hom_shift_obj_eq_zero (S' : PostnikovSystem X' d')
    (h : ∀ i j : Fin (n + 1), (j : ℕ) + 1 < (i : ℕ) →
      ∀ u : (X i)⟦((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) - 1⟧ ⟶ X' j, u = 0) (i j : Fin (n + 1))
    (hij : (j : ℕ) + 1 < (i : ℕ)) (u : (X i)⟦((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) - 1⟧ ⟶ S'.obj j) :
    u = 0 := by
  refine eq_zero_of_shift_eq (a := ((i : ℕ) : ℤ) - 1 - ((j : ℕ) : ℤ)) (by ring)
    (eq_zero_of_hom_shift_eq_zero S' (((i : ℕ) : ℤ) - 1) j fun k hk v => ?_) u
  exact eq_zero_of_shift_eq (by ring) (h i k (by omega)) v

/-- Let `g : Yⱼ ⟶ Y'ⱼ` be compatible with the morphisms `Yⱼ ⟶ Xⱼ`, `Y'ⱼ ⟶ X'ⱼ` and let `fc`, `fs`
commute with the morphisms `d j`, `d' j` of the complexes. Then the square `Xⱼ₊₁ ⟶ Yⱼ ⟶ Y'ⱼ`,
`Xⱼ₊₁ ⟶ X'ⱼ₊₁ ⟶ Y'ⱼ` commutes as soon as `Hom(Xⱼ₊₁⟦1⟧, Y'ⱼ₋₁) = 0`. -/
private lemma p_comp_eq_of_comp_π_eq (S : PostnikovSystem X d) (S' : PostnikovSystem X' d')
    {j : Fin n} {fc : X j.castSucc ⟶ X' j.castSucc} {fs : X j.succ ⟶ X' j.succ}
    (hf : d j ≫ fc = fs ≫ d' j) {g : S.obj j.castSucc ⟶ S'.obj j.castSucc}
    (hg : g ≫ S'.π j.castSucc = S.π j.castSucc ≫ fc)
    (hv : ∀ k : Fin (n + 1), (k : ℕ) + 1 = (j : ℕ) →
      ∀ v : (X j.succ)⟦(1 : ℤ)⟧ ⟶ S'.obj k, v = 0) :
    S.p j ≫ g = fs ≫ S'.p j := by
  rw [← sub_eq_zero]
  refine eq_zero_of_comp_π_eq_zero S' j.castSucc (by simpa using hv) _ ?_
  rw [Preadditive.sub_comp, Category.assoc, hg, ← Category.assoc, S.p_comp_π j, Category.assoc,
    S'.p_comp_π j, hf, sub_self]

/-- TR3 for the `j`-th triangles `Yⱼ₊₁ ⟶ Xⱼ₊₁ ⟶ Yⱼ ⟶ Yⱼ₊₁⟦1⟧` of two Postnikov systems: a
commuting square `Xⱼ₊₁ ⟶ Yⱼ ⟶ Y'ⱼ`, `Xⱼ₊₁ ⟶ X'ⱼ₊₁ ⟶ Y'ⱼ` extends to a morphism `Yⱼ₊₁ ⟶ Y'ⱼ₊₁`
compatible with the morphisms `Yⱼ₊₁ ⟶ Xⱼ₊₁` and with the connecting morphisms. -/
private lemma exists_hom_succ (S : PostnikovSystem X d) (S' : PostnikovSystem X' d') {j : Fin n}
    {fs : X j.succ ⟶ X' j.succ} {g : S.obj j.castSucc ⟶ S'.obj j.castSucc}
    (hsq : S.p j ≫ g = fs ≫ S'.p j) :
    ∃ a : S.obj j.succ ⟶ S'.obj j.succ, a ≫ S'.π j.succ = S.π j.succ ≫ fs ∧
      S.δ j ≫ a⟦(1 : ℤ)⟧' = g ≫ S'.δ j := by
  obtain ⟨a, ha₁, ha₃⟩ := complete_distinguished_triangle_morphism₁
    (Triangle.mk (S.π j.succ) (S.p j) (S.δ j)) (Triangle.mk (S'.π j.succ) (S'.p j) (S'.δ j))
    (S.distinguished j) (S'.distinguished j) fs g (by simpa using hsq)
  exact ⟨a, by simpa using ha₁.symm, by simpa using ha₃⟩

/-- Partial extension of a morphism of complexes to a morphism of Postnikov systems: for every
index `m` there is a family `g i : Yᵢ ⟶ Y'ᵢ` whose compatibility with the morphisms `Yᵢ ⟶ Xᵢ`,
`Xᵢ₊₁ ⟶ Yᵢ` and `Yᵢ ⟶ Yᵢ₊₁⟦1⟧` of the two systems holds in degrees `≤ m`, the components in higher
degrees being zero. -/
private lemma exists_hom_le (S : PostnikovSystem X d) (S' : PostnikovSystem X' d')
    (f : ∀ i, X i ⟶ X' i) (hf : ∀ i : Fin n, d i ≫ f i.castSucc = f i.succ ≫ d' i)
    (hY : ∀ i k : Fin (n + 1), (k : ℕ) + 1 < (i : ℕ) →
      ∀ u : (X i)⟦((i : ℕ) : ℤ) - ((k : ℕ) : ℤ) - 1⟧ ⟶ S'.obj k, u = 0) (m : Fin (n + 1)) :
    ∃ g : ∀ i, S.obj i ⟶ S'.obj i,
      (∀ i : Fin (n + 1), (i : ℕ) ≤ (m : ℕ) → g i ≫ S'.π i = S.π i ≫ f i) ∧
      (∀ i : Fin n, (i : ℕ) < (m : ℕ) → S.p i ≫ g i.castSucc = f i.succ ≫ S'.p i) ∧
      (∀ i : Fin n, (i : ℕ) < (m : ℕ) →
        S.δ i ≫ (g i.succ)⟦(1 : ℤ)⟧' = g i.castSucc ≫ S'.δ i) := by
  induction m using Fin.induction with
  | zero =>
    refine ⟨Fin.cases (S.π 0 ≫ f 0 ≫ inv (S'.π 0)) fun _ => 0, fun i hi => ?_,
      fun i hi => absurd hi (by simp), fun i hi => absurd hi (by simp)⟩
    obtain rfl : i = 0 := Fin.val_inj.mp (by simpa using hi)
    simp
  | succ j ih =>
    obtain ⟨g, h1, h2, h3⟩ := ih
    have hsq : S.p j ≫ g j.castSucc = f j.succ ≫ S'.p j :=
      p_comp_eq_of_comp_π_eq S S' (hf j) (h1 j.castSucc le_rfl) fun k hk v =>
        eq_zero_of_shift_eq (by simp only [Fin.val_succ]; omega)
          (hY j.succ k (by simp only [Fin.val_succ]; omega)) v
    obtain ⟨a, ha₁, ha₃⟩ := exists_hom_succ S S' hsq
    have hupd : ∀ i : Fin (n + 1), (i : ℕ) ≤ (j : ℕ) → Function.update g j.succ a i = g i :=
      fun i hi => Function.update_of_ne (Fin.ne_of_val_ne (by simp only [Fin.val_succ]; omega)) _ _
    refine ⟨Function.update g j.succ a, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
    · rcases eq_or_ne i j.succ with rfl | hij
      · rw [Function.update_self]; exact ha₁
      · rw [Function.update_of_ne hij]
        refine h1 i ?_
        have hv := Fin.val_ne_of_ne hij
        simp only [Fin.val_succ, Fin.val_castSucc] at hv hi ⊢
        omega
    · simp only [Fin.val_succ] at hi
      rw [hupd i.castSucc (by simp only [Fin.val_castSucc]; omega)]
      rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hi) with heq | hlt
      · obtain rfl : i = j := Fin.val_inj.mp heq
        exact hsq
      · exact h2 i (by simp only [Fin.val_castSucc]; omega)
    · simp only [Fin.val_succ] at hi
      rw [hupd i.castSucc (by simp only [Fin.val_castSucc]; omega)]
      rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hi) with heq | hlt
      · obtain rfl : i = j := Fin.val_inj.mp heq
        rw [Function.update_self]
        exact ha₃
      · rw [hupd i.succ (by simp only [Fin.val_succ]; omega)]
        exact h3 i (by simp only [Fin.val_castSucc]; omega)

end Extend

/-- Let `Xₙ ⟶ ⋯ ⟶ X₀` and `X'ₙ ⟶ ⋯ ⟶ X'₀` be complexes in a pretriangulated category, let `S'`
be a Postnikov system for the second one, and assume that every morphism `Xᵢ⟦i - j - 1⟧ ⟶ X'ⱼ`
with `i > j + 1` is zero. Then

1. every morphism `Xᵢ⟦i - j - 1⟧ ⟶ Y'ⱼ` with `i > j + 1` is zero, and
2. for every Postnikov system `S` for the first complex, every morphism of complexes
   `f i : Xᵢ ⟶ X'ᵢ` extends to a (nonunique) morphism of Postnikov systems `S ⟶ S'`, i.e. to a
   family `g i : Yᵢ ⟶ Y'ᵢ` compatible with the morphisms `Yᵢ ⟶ Xᵢ`, `Xᵢ₊₁ ⟶ Yᵢ` and
   `Yᵢ ⟶ Yᵢ₊₁⟦1⟧` of the two systems. -/
@[stacks 0D82]
theorem PostnikovSystem.hom_shift_obj_eq_zero_and_exists_hom {n : ℕ}
    (X : Fin (n + 1) → D) (d : ∀ i : Fin n, X i.succ ⟶ X i.castSucc)
    {X' : Fin (n + 1) → D} {d' : ∀ i : Fin n, X' i.succ ⟶ X' i.castSucc}
    (S' : PostnikovSystem X' d')
    (h : ∀ i j : Fin (n + 1), (j : ℕ) + 1 < (i : ℕ) →
      ∀ f : (X i)⟦((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) - 1⟧ ⟶ X' j, f = 0) :
    (∀ i j : Fin (n + 1), (j : ℕ) + 1 < (i : ℕ) →
        ∀ f : (X i)⟦((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) - 1⟧ ⟶ S'.obj j, f = 0) ∧
      ∀ (S : PostnikovSystem X d) (f : ∀ i, X i ⟶ X' i),
        (∀ i : Fin n, d i ≫ f i.castSucc = f i.succ ≫ d' i) →
        ∃ g : ∀ i, S.obj i ⟶ S'.obj i,
          (∀ i, g i ≫ S'.π i = S.π i ≫ f i) ∧
          (∀ i : Fin n, S.p i ≫ g i.castSucc = f i.succ ≫ S'.p i) ∧
          (∀ i : Fin n, S.δ i ≫ (g i.succ)⟦(1 : ℤ)⟧' = g i.castSucc ≫ S'.δ i) := by
  refine ⟨hom_shift_obj_eq_zero S' h, fun S f hf => ?_⟩
  obtain ⟨g, h1, h2, h3⟩ := exists_hom_le S S' f hf (hom_shift_obj_eq_zero S' h) (Fin.last n)
  exact ⟨g, fun i => h1 i (by simpa using Nat.lt_succ_iff.mp i.isLt), fun i => h2 i (by simp),
    fun i => h3 i (by simp)⟩

/-! ### The lift `Xₙ ⟶ Yₙ₋₁` -/

/-- Let `S` be a Postnikov system for a complex `Xₙ₋₁ ⟶ ⋯ ⟶ X₀` of length `n - 1 ≥ 2`, and let
`u : W ⟶ Xₙ₋₁` be a morphism whose composition with `Xₙ₋₁ ⟶ Xₙ₋₂` vanishes. If
`Hom(W⟦1⟧, Yₙ₋₃) = 0` then `u` lifts along `Yₙ₋₁ ⟶ Xₙ₋₁`. -/
private lemma exists_lift_π {m : ℕ} {X : Fin (m + 3) → D}
    {d : ∀ i : Fin (m + 2), X i.succ ⟶ X i.castSucc} (S : PostnikovSystem X d) {W : D}
    (u : W ⟶ X (Fin.last (m + 2))) (hu : u ≫ d (Fin.last (m + 1)) = 0)
    (hW : ∀ v : W⟦(1 : ℤ)⟧ ⟶ S.obj ((Fin.last m).castSucc.castSucc), v = 0) :
    ∃ q : W ⟶ S.obj (Fin.last (m + 2)), q ≫ S.π (Fin.last (m + 2)) = u := by
  have hp : u ≫ S.p (Fin.last (m + 1)) = 0 := by
    refine hom_ext_obj₁ (S.distinguished ((Fin.last m).castSucc)) hW (b := 0) ?_
    have hpπ : S.p (Fin.last (m + 1)) ≫ S.π ((Fin.last m).castSucc.succ) =
      d (Fin.last (m + 1)) := S.p_comp_π (Fin.last (m + 1))
    simp only [Triangle.mk_mor₁, Category.assoc, hpπ, hu, zero_comp]
  obtain ⟨q, hq⟩ := Triangle.coyoneda_exact₂ _ (S.distinguished (Fin.last (m + 1))) u hp
  exact ⟨q, hq.symm⟩

/-! ### Extending a Postnikov system by one triangle -/

omit [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] in
/-- Composing an isomorphism with a transport along an equality of objects gives an
isomorphism. -/
private lemma isIso_eqToHom_comp {A B C : D} (h : A = B) (g : B ⟶ C) (hg : IsIso g) :
    IsIso (eqToHom h ≫ g) := by
  subst h
  simpa using hg

/-- A Postnikov system for the truncated complex `Xₙ₋₁ ⟶ ⋯ ⟶ X₀`, together with a morphism
`q : Xₙ ⟶ Yₙ₋₁` lifting the morphism `Xₙ ⟶ Xₙ₋₁` of the complex, extends to a Postnikov system for
`Xₙ ⟶ ⋯ ⟶ X₀`. -/
private lemma nonempty_postnikovSystem_snoc {m : ℕ} {X : Fin (m + 2) → D}
    {d : ∀ i : Fin (m + 1), X i.succ ⟶ X i.castSucc}
    (S : PostnikovSystem (fun i : Fin (m + 1) => X i.castSucc) (fun i : Fin m => d i.castSucc))
    (q : X (Fin.last (m + 1)) ⟶ S.obj (Fin.last m))
    (hq : q ≫ S.π (Fin.last m) = d (Fin.last m)) : Nonempty (PostnikovSystem X d) := by
  obtain ⟨Z, a, c, hT⟩ := distinguished_cocone_triangle₁ q
  set Y : Fin (m + 2) → D := Fin.snoc S.obj Z with hY
  have hlast : Y (Fin.last (m + 1)) = Z := by simp [hY]
  have hcast : ∀ j : Fin (m + 1), Y j.castSucc = S.obj j := by intro j; simp [hY]
  let π : ∀ i : Fin (m + 2), Y i ⟶ X i :=
    Fin.lastCases (eqToHom hlast ≫ a) (fun j => eqToHom (hcast j) ≫ S.π j)
  let p : ∀ i : Fin (m + 1), X i.succ ⟶ Y i.castSucc :=
    Fin.lastCases (q ≫ eqToHom (hcast (Fin.last m)).symm)
      (fun j => S.p j ≫ eqToHom (hcast j.castSucc).symm)
  let δ : ∀ i : Fin (m + 1), Y i.castSucc ⟶ (Y i.succ)⟦(1 : ℤ)⟧ :=
    Fin.lastCases (eqToHom (hcast (Fin.last m)) ≫ c ≫ (eqToHom hlast.symm)⟦(1 : ℤ)⟧')
      (fun j => eqToHom (hcast j.castSucc) ≫ S.δ j ≫ (eqToHom (hcast j.succ).symm)⟦(1 : ℤ)⟧')
  have hπl : π (Fin.last m).succ = eqToHom hlast ≫ a := Fin.lastCases_last
  have hπc : ∀ j : Fin (m + 1), π j.castSucc = eqToHom (hcast j) ≫ S.π j := fun j =>
    Fin.lastCases_castSucc j
  have hpl : p (Fin.last m) = q ≫ eqToHom (hcast (Fin.last m)).symm := Fin.lastCases_last
  have hpc : ∀ j : Fin m, p j.castSucc = S.p j ≫ eqToHom (hcast j.castSucc).symm := fun j =>
    Fin.lastCases_castSucc j
  have hδl : δ (Fin.last m) =
      eqToHom (hcast (Fin.last m)) ≫ c ≫ (eqToHom hlast.symm)⟦(1 : ℤ)⟧' := Fin.lastCases_last
  have hδc : ∀ j : Fin m, δ j.castSucc =
      eqToHom (hcast j.castSucc) ≫ S.δ j ≫ (eqToHom (hcast j.succ).symm)⟦(1 : ℤ)⟧' := fun j =>
    Fin.lastCases_castSucc j
  refine ⟨{ obj := Y, π := π, p := p, δ := δ, isIso_π_zero := ?_, distinguished := ?_,
            p_comp_π := ?_ }⟩
  · rw [show π 0 = eqToHom (hcast 0) ≫ S.π 0 from hπc 0]
    exact isIso_eqToHom_comp _ _ S.isIso_π_zero
  · intro i
    induction i using Fin.lastCases with
    | last =>
      rw [hπl, hpl, hδl]
      refine isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ (eqToIso hlast) (Iso.refl _)
        (eqToIso (hcast (Fin.last m))) ?_ ?_ ?_) <;> simp
    | cast j =>
      rw [show π j.castSucc.succ = eqToHom (hcast j.succ) ≫ S.π j.succ from
            Fin.lastCases_castSucc j.succ, hpc j, hδc j]
      refine isomorphic_distinguished _ (S.distinguished j) _
        (Triangle.isoMk _ _ (eqToIso (hcast j.succ)) (Iso.refl _)
          (eqToIso (hcast j.castSucc)) ?_ ?_ ?_) <;> simp
  · intro i
    induction i using Fin.lastCases with
    | last => rw [hpl, hπc (Fin.last m)]; simp [hq]
    | cast j => rw [hpc j, hπc j.castSucc]; simpa using S.p_comp_π j

/-! ### Existence under a vanishing hypothesis -/

/-- A complex `Xₙ ⟶ ⋯ ⟶ X₀` all of whose morphisms `Xᵢ⟦i - j - 2⟧ ⟶ Xⱼ` with `i > j + 2` vanish
admits a Postnikov system. -/
private lemma nonempty_postnikovSystem : ∀ (n : ℕ) (X : Fin (n + 1) → D)
    (d : ∀ i : Fin n, X i.succ ⟶ X i.castSucc),
    (∀ (i : Fin n) (h : (i : ℕ) + 1 < n), d ⟨(i : ℕ) + 1, h⟩ ≫ d i = 0) →
    (∀ i j : Fin (n + 1), (j : ℕ) + 2 < (i : ℕ) →
      ∀ u : (X i)⟦((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) - 2⟧ ⟶ X j, u = 0) →
    Nonempty (PostnikovSystem X d) := by
  intro n
  induction n with
  | zero => exact fun X d hd _ => nonempty_postnikovSystem_of_length_le_two (by omega) X d hd
  | succ m ih =>
    intro X d hd h
    rcases le_or_gt (m + 1) 2 with hm | hm
    · exact nonempty_postnikovSystem_of_length_le_two hm X d hd
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    obtain ⟨S⟩ := ih (fun i => X i.castSucc) (fun i => d i.castSucc)
      (fun i hi => hd i.castSucc (by simp only [Fin.val_castSucc]; omega))
      (fun i j hij => by simpa using h i.castSucc j.castSucc (by simpa using hij))
    obtain ⟨q, hq⟩ := exists_lift_π S (d (Fin.last (k + 2)))
      (hd (Fin.last (k + 1)).castSucc (by simp only [Fin.val_castSucc, Fin.val_last]; omega))
      (eq_zero_of_shift_eq (by simp) (eq_zero_of_hom_shift_eq_zero S ((k : ℤ) + 1) _
        (fun j hj => eq_zero_of_shift_eq
          (by simp only [Fin.val_last, Fin.val_castSucc]; push_cast; ring)
          (h (Fin.last (k + 3)) j.castSucc (by
            simp only [Fin.val_castSucc, Fin.val_last] at hj ⊢; omega)))))
    exact nonempty_postnikovSystem_snoc S q hq

/-- A complex `Xₙ ⟶ ⋯ ⟶ X₀` in a pretriangulated category, with morphisms `d i : Xᵢ₊₁ ⟶ Xᵢ`,
admits a Postnikov system as soon as every morphism `Xᵢ⟦i - j - 2⟧ ⟶ Xⱼ` with `i > j + 2` is
zero. Without that vanishing condition Postnikov systems need not exist once `n > 2`; for
`n ≤ 2` the condition is vacuous and this is
`CategoryTheory.Triangulated.nonempty_postnikovSystem_of_length_le_two`. -/
@[stacks 0D83]
theorem nonempty_postnikovSystem_of_hom_shift_eq_zero {n : ℕ} (X : Fin (n + 1) → D)
    (d : ∀ i : Fin n, X i.succ ⟶ X i.castSucc)
    (hd : ∀ (i : Fin n) (h : (i : ℕ) + 1 < n), d ⟨(i : ℕ) + 1, h⟩ ≫ d i = 0)
    (h : ∀ i j : Fin (n + 1), (j : ℕ) + 2 < (i : ℕ) →
      ∀ u : (X i)⟦((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) - 2⟧ ⟶ X j, u = 0) :
    Nonempty (PostnikovSystem X d) :=
  nonempty_postnikovSystem n X d hd h

/-! ### Uniqueness up to isomorphism -/

/-- Every component of a morphism `g` of Postnikov systems lying over an isomorphism `f` of
complexes is an isomorphism. -/
private lemma isIso_of_hom_postnikovSystem {n : ℕ} {X X' : Fin (n + 1) → D}
    {d : ∀ i : Fin n, X i.succ ⟶ X i.castSucc} {d' : ∀ i : Fin n, X' i.succ ⟶ X' i.castSucc}
    {S : PostnikovSystem X d} {S' : PostnikovSystem X' d'} {f : ∀ i, X i ⟶ X' i}
    (hf : ∀ i, IsIso (f i)) {g : ∀ i, S.obj i ⟶ S'.obj i}
    (hgπ : ∀ i, g i ≫ S'.π i = S.π i ≫ f i)
    (hgp : ∀ i : Fin n, S.p i ≫ g i.castSucc = f i.succ ≫ S'.p i)
    (hgδ : ∀ i : Fin n, S.δ i ≫ (g i.succ)⟦(1 : ℤ)⟧' = g i.castSucc ≫ S'.δ i) (i : Fin (n + 1)) :
    IsIso (g i) := by
  induction i using Fin.induction with
  | zero =>
    have := hf 0
    rw [show g 0 = (S.π 0 ≫ f 0) ≫ inv (S'.π 0) by rw [← hgπ 0]; simp]
    infer_instance
  | succ j ih =>
    exact isIso₁_of_isIso₂₃ (T := Triangle.mk (S.π j.succ) (S.p j) (S.δ j))
      (T' := Triangle.mk (S'.π j.succ) (S'.p j) (S'.δ j))
      { hom₁ := g j.succ
        hom₂ := f j.succ
        hom₃ := g j.castSucc
        comm₁ := (hgπ j.succ).symm
        comm₂ := hgp j
        comm₃ := hgδ j } (S.distinguished j) (S'.distinguished j) (hf j.succ) ih

/-- If every morphism `Xᵢ⟦i - j - 1⟧ ⟶ Xⱼ` with `i > j + 1` vanishes, any two Postnikov systems
for complexes isomorphic to `Xₙ ⟶ ⋯ ⟶ X₀` are isomorphic over the given isomorphism of
complexes. -/
private lemma exists_iso_aux {n : ℕ} {X : Fin (n + 1) → D}
    {d : ∀ i : Fin n, X i.succ ⟶ X i.castSucc}
    (h : ∀ i j : Fin (n + 1), (j : ℕ) + 1 < (i : ℕ) →
      ∀ u : (X i)⟦((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) - 1⟧ ⟶ X j, u = 0)
    {X' : Fin (n + 1) → D} {d' : ∀ i : Fin n, X' i.succ ⟶ X' i.castSucc}
    (S : PostnikovSystem X d) (S' : PostnikovSystem X' d') (f : ∀ i, X i ≅ X' i)
    (hf : ∀ i : Fin n, d i ≫ (f i.castSucc).hom = (f i.succ).hom ≫ d' i) :
    ∃ g : ∀ i, S.obj i ≅ S'.obj i,
      (∀ i, (g i).hom ≫ S'.π i = S.π i ≫ (f i).hom) ∧
      (∀ i : Fin n, S.p i ≫ (g i.castSucc).hom = (f i.succ).hom ≫ S'.p i) ∧
      (∀ i : Fin n, S.δ i ≫ ((g i.succ).hom)⟦(1 : ℤ)⟧' = (g i.castSucc).hom ≫ S'.δ i) := by
  have h' : ∀ i j : Fin (n + 1), (j : ℕ) + 1 < (i : ℕ) →
      ∀ u : (X i)⟦((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) - 1⟧ ⟶ X' j, u = 0 := fun i j hij u =>
    eq_zero_of_iso (Iso.refl _) (f j).symm (h i j hij) u
  obtain ⟨g, hgπ, hgp, hgδ⟩ :=
    (PostnikovSystem.hom_shift_obj_eq_zero_and_exists_hom X d S' h').2 S (fun i => (f i).hom) hf
  exact ⟨fun i => @asIso _ _ _ _ (g i)
    (isIso_of_hom_postnikovSystem (fun i => inferInstance) hgπ hgp hgδ i), hgπ, hgp, hgδ⟩

/-- Let `Xₙ ⟶ ⋯ ⟶ X₀` be a diagram in a pretriangulated category, with morphisms
`d i : Xᵢ₊₁ ⟶ Xᵢ`, such that every morphism `Xᵢ⟦i - j - 1⟧ ⟶ Xⱼ` with `i > j + 1` is zero. Then
for every diagram `X'ₙ ⟶ ⋯ ⟶ X'₀` and every isomorphism `f i : Xᵢ ≅ X'ᵢ` of diagrams, any
Postnikov systems `S`, `S'` for the two are isomorphic over `f`: there is a family of isomorphisms
`g i : Yᵢ ≅ Y'ᵢ` compatible with the morphisms `Yᵢ ⟶ Xᵢ`, `Xᵢ₊₁ ⟶ Yᵢ` and `Yᵢ ⟶ Yᵢ₊₁⟦1⟧` of the
two systems. In particular, at `X' = X`, `d' = d` and `f = 𝟙`, any two Postnikov systems for
`Xₙ ⟶ ⋯ ⟶ X₀` are isomorphic. -/
@[stacks 0D83]
theorem PostnikovSystem.exists_iso {n : ℕ} {X X' : Fin (n + 1) → D}
    {d : ∀ i : Fin n, X i.succ ⟶ X i.castSucc} {d' : ∀ i : Fin n, X' i.succ ⟶ X' i.castSucc}
    (h : ∀ i j : Fin (n + 1), (j : ℕ) + 1 < (i : ℕ) →
      ∀ u : (X i)⟦((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) - 1⟧ ⟶ X j, u = 0)
    (S : PostnikovSystem X d) (S' : PostnikovSystem X' d') (f : ∀ i, X i ≅ X' i)
    (hf : ∀ i : Fin n, d i ≫ (f i.castSucc).hom = (f i.succ).hom ≫ d' i) :
    ∃ g : ∀ i, S.obj i ≅ S'.obj i,
      (∀ i, (g i).hom ≫ S'.π i = S.π i ≫ (f i).hom) ∧
      (∀ i : Fin n, S.p i ≫ (g i.castSucc).hom = (f i.succ).hom ≫ S'.p i) ∧
      (∀ i : Fin n, S.δ i ≫ ((g i.succ).hom)⟦(1 : ℤ)⟧' =
        (g i.castSucc).hom ≫ S'.δ i) :=
  exists_iso_aux h S S' f hf

/-! ### Uniqueness of the morphism on the totalizations -/

section Uniqueness

variable {n : ℕ} {X X' : Fin (n + 1) → D} {d : ∀ i : Fin n, X i.succ ⟶ X i.castSucc}
  {d' : ∀ i : Fin n, X' i.succ ⟶ X' i.castSucc} {S : PostnikovSystem X d}
  {S' : PostnikovSystem X' d'} {f : ∀ i, X i ⟶ X' i} {g g' : ∀ i, S.obj i ⟶ S'.obj i}

/-- The bottom component of a morphism of Postnikov systems over `f` is determined by `f 0`. -/
private lemma hom_zero_eq (hg : ∀ i, g i ≫ S'.π i = S.π i ≫ f i)
    (hg' : ∀ i, g' i ≫ S'.π i = S.π i ≫ f i) : g 0 = g' 0 := by
  rw [← cancel_mono (S'.π 0), hg 0, hg' 0]

/-- Case (1) of [Stacks, Tag 0FXE]: if `Hom(Xᵢ⟦i⟧, Y'ₙ⟦n⟧) = 0` for `i ≥ 1`, the top components
of two morphisms of Postnikov systems over `f` agree. -/
private lemma hom_last_eq_of_hom_shift_obj_last_eq_zero
    (hg : ∀ i, g i ≫ S'.π i = S.π i ≫ f i) (hg' : ∀ i, g' i ≫ S'.π i = S.π i ≫ f i)
    (hgδ : ∀ i : Fin n, S.δ i ≫ (g i.succ)⟦(1 : ℤ)⟧' = g i.castSucc ≫ S'.δ i)
    (hg'δ : ∀ i : Fin n, S.δ i ≫ (g' i.succ)⟦(1 : ℤ)⟧' = g' i.castSucc ≫ S'.δ i)
    (h : ∀ i : Fin (n + 1), 0 < (i : ℕ) →
      ∀ u : (X i)⟦((i : ℕ) : ℤ)⟧ ⟶ (S'.obj (Fin.last n))⟦(n : ℤ)⟧, u = 0) :
    g (Fin.last n) = g' (Fin.last n) := by
  have key : ∀ (i : Fin (n + 1)) (V : D),
      (∀ k : Fin (n + 1), 0 < (k : ℕ) → (k : ℕ) ≤ (i : ℕ) → ∀ m : ℤ,
        m = ((k : ℕ) : ℤ) - ((i : ℕ) : ℤ) → ∀ u : (X k)⟦m⟧ ⟶ V, u = 0) →
      ∀ q : S'.obj i ⟶ V, g i ≫ q = g' i ≫ q := by
    intro i
    induction i using Fin.induction with
    | zero => intro V _ q; rw [hom_zero_eq hg hg']
    | succ i ih =>
      intro V hV q
      have hc : ((i.castSucc : Fin (n + 1)) : ℕ) = (i : ℕ) := rfl
      have hs : ((i.succ : Fin (n + 1)) : ℕ) = (i : ℕ) + 1 := rfl
      apply (shiftFunctor D (1 : ℤ)).map_injective
      rw [Functor.map_comp, Functor.map_comp]
      refine hom_ext_hom_obj₂ (rot_of_distTriang _ (rot_of_distTriang _ (S.distinguished i)))
        ?_ ?_
      · intro u
        refine eq_zero_shift (1 : ℤ) ?_ u
        intro v
        exact eq_zero_of_iso ((shiftFunctorZero D ℤ).app (X i.succ)).symm (Iso.refl V)
          (hV i.succ (by omega) (by omega) 0 (by omega)) v
      · change S.δ i ≫ _ = S.δ i ≫ _
        simp only [← Category.assoc, hgδ i, hg'δ i]
        simp only [Category.assoc]
        refine ih (V⟦(1 : ℤ)⟧) ?_ (S'.δ i ≫ q⟦(1 : ℤ)⟧')
        intro k hk hki m hm u
        exact eq_zero_of_shift_iso (1 : ℤ) (hV k hk (by omega) (m - 1) (by omega))
          (shiftShiftIso (X k) (by ring)) (Iso.refl _) u
  have hV : ∀ k : Fin (n + 1), 0 < (k : ℕ) → (k : ℕ) ≤ ((Fin.last n : Fin (n + 1)) : ℕ) →
      ∀ m : ℤ, m = ((k : ℕ) : ℤ) - ((Fin.last n : Fin (n + 1)) : ℕ) →
      ∀ u : (X k)⟦m⟧ ⟶ S'.obj (Fin.last n), u = 0 := by
    intro k hk _ m hm u
    simp only [Fin.val_last] at hm
    exact eq_zero_of_shift_iso (-(n : ℤ)) (h k hk) (shiftShiftIso (X k) (by omega))
      (shiftShiftIsoSelf (S'.obj (Fin.last n)) (by ring)) u
  simpa using key (Fin.last n) (S'.obj (Fin.last n)) hV (𝟙 _)

/-- Case (2) of [Stacks, Tag 0FXE]: if `Hom(Yₙ⟦n⟧, X'ⱼ⟦j⟧) = 0` for `j < n`, the top components
of two morphisms of Postnikov systems over `f` agree. -/
private lemma hom_last_eq_of_hom_shift_last_obj_eq_zero
    (hg : ∀ i, g i ≫ S'.π i = S.π i ≫ f i) (hg' : ∀ i, g' i ≫ S'.π i = S.π i ≫ f i)
    (h : ∀ j : Fin (n + 1), (j : ℕ) < n →
      ∀ u : (S.obj (Fin.last n))⟦(n : ℤ)⟧ ⟶ (X' j)⟦((j : ℕ) : ℤ)⟧, u = 0) :
    g (Fin.last n) = g' (Fin.last n) := by
  have key : ∀ j : Fin (n + 1), (j : ℕ) < n → ∀ m : ℤ, m = (n : ℤ) - ((j : ℕ) : ℤ) →
      ∀ u : (S.obj (Fin.last n))⟦m⟧ ⟶ S'.obj j, u = 0 := by
    intro j
    induction j using Fin.induction with
    | zero =>
      intro hj m hm u
      have h0 := h 0 hj
      simp only [Fin.val_zero, Nat.cast_zero] at h0 hm
      refine eq_zero_of_shift_eq (a := (n : ℤ)) (by omega) ?_ u
      intro v
      exact eq_zero_of_iso (Iso.refl _)
        ((asIso (S'.π 0)).trans ((shiftFunctorZero D ℤ).app (X' 0)).symm) h0 v
    | succ j ih =>
      intro hj m hm u
      have hc : ((j.castSucc : Fin (n + 1)) : ℕ) = (j : ℕ) := rfl
      have hs : ((j.succ : Fin (n + 1)) : ℕ) = (j : ℕ) + 1 := rfl
      refine eq_zero_obj₁' (S'.distinguished j) ?_ ?_ u
      · intro w
        exact eq_zero_of_shift_iso (-(((j.succ : Fin (n + 1)) : ℕ) : ℤ)) (h j.succ hj)
          (shiftShiftIso (S.obj (Fin.last n)) (by omega))
          (shiftShiftIsoSelf (X' j.succ) (by ring)) w
      · intro w
        exact eq_zero_of_shift_iso (-1 : ℤ) (ih (by omega) (m + 1) (by omega))
          (shiftShiftIso (S.obj (Fin.last n)) (by ring)) (Iso.refl _) w
  rcases Fin.eq_zero_or_eq_succ (Fin.last n) with h0 | ⟨j, hj⟩
  · rw [h0]
    exact hom_zero_eq hg hg'
  · have hc : ((j.castSucc : Fin (n + 1)) : ℕ) = (j : ℕ) := rfl
    have hjn : (j : ℕ) + 1 = n := by
      have hv := congrArg Fin.val hj
      simpa using hv.symm
    have hvan : ∀ w : S.obj (Fin.last n) ⟶ (S'.obj j.castSucc)⟦(-1 : ℤ)⟧, w = 0 := by
      intro w
      exact eq_zero_of_shift_iso (-1 : ℤ) (key j.castSucc (by omega) 1 (by omega))
        (shiftShiftIsoSelf (S.obj (Fin.last n)) (by ring)) (Iso.refl _) w
    rw [hj] at hvan ⊢
    exact hom_ext_obj₁' (S'.distinguished j) hvan
      (by simp only [Triangle.mk_mor₁]; rw [hg j.succ, hg' j.succ])

/-- Case (3) of [Stacks, Tag 0FXE]: if `Hom(Xᵢ⟦i - j + 1⟧, X'ⱼ) = 0` and `Hom(Xⱼ, X'ᵢ⟦i - j⟧) = 0`
for `i < j`, then two morphisms of Postnikov systems over `f` agree in every component. -/
private lemma hom_eq_of_hom_shift_eq_zero
    (hg : ∀ i, g i ≫ S'.π i = S.π i ≫ f i) (hg' : ∀ i, g' i ≫ S'.π i = S.π i ≫ f i)
    (hgp : ∀ i : Fin n, S.p i ≫ g i.castSucc = f i.succ ≫ S'.p i)
    (hg'p : ∀ i : Fin n, S.p i ≫ g' i.castSucc = f i.succ ≫ S'.p i)
    (hgδ : ∀ i : Fin n, S.δ i ≫ (g i.succ)⟦(1 : ℤ)⟧' = g i.castSucc ≫ S'.δ i)
    (hg'δ : ∀ i : Fin n, S.δ i ≫ (g' i.succ)⟦(1 : ℤ)⟧' = g' i.castSucc ≫ S'.δ i)
    (h : ∀ i j : Fin (n + 1), (i : ℕ) < (j : ℕ) →
      ∀ u : (X i)⟦((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) + 1⟧ ⟶ X' j, u = 0)
    (h' : ∀ i j : Fin (n + 1), (i : ℕ) < (j : ℕ) →
      ∀ u : X j ⟶ (X' i)⟦((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)⟧, u = 0) (i : Fin (n + 1)) :
    g i = g' i := by
  have hA : ∀ i j : Fin (n + 1), (i : ℕ) < (j : ℕ) → ∀ m : ℤ,
      m = ((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) + 1 → ∀ u : (S.obj i)⟦m⟧ ⟶ X' j, u = 0 := by
    intro i
    induction i using Fin.induction with
    | zero =>
      intro j hij m hm u
      subst hm
      exact eq_zero_of_iso ((shiftFunctor D _).mapIso (asIso (S.π 0))) (Iso.refl _)
        (h 0 j hij) u
    | succ i ih =>
      intro j hij m hm u
      have hc : ((i.castSucc : Fin (n + 1)) : ℕ) = (i : ℕ) := rfl
      have hs : ((i.succ : Fin (n + 1)) : ℕ) = (i : ℕ) + 1 := rfl
      refine eq_zero_of_shift_iso m ?_ (Iso.refl _)
        (shiftShiftIsoSelf (X' j) (a := -m) (b := m) (h := by ring)) u
      intro v
      refine eq_zero_hom_obj₁ (S.distinguished i) ?_ ?_ v
      · intro w
        exact eq_zero_of_shift_iso (-m) (h i.succ j hij)
          (shiftShiftIsoSelf (X i.succ) (by omega)) (Iso.refl _) w
      · intro w
        exact eq_zero_of_shift_iso (-m) (ih j (by omega) (m - 1) (by omega))
          (shiftShiftIso (S.obj i.castSucc) (by ring)) (Iso.refl _) w
  have hB : ∀ i j : Fin (n + 1), (i : ℕ) < (j : ℕ) → ∀ m : ℤ,
      m = ((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) → ∀ u : X j ⟶ (S'.obj i)⟦m⟧, u = 0 := by
    intro i
    induction i using Fin.induction with
    | zero =>
      intro j hij m hm u
      subst hm
      exact eq_zero_of_iso (Iso.refl _) ((shiftFunctor D _).mapIso (asIso (S'.π 0)))
        (h' 0 j hij) u
    | succ i ih =>
      intro j hij m hm u
      have hc : ((i.castSucc : Fin (n + 1)) : ℕ) = (i : ℕ) := rfl
      have hs : ((i.succ : Fin (n + 1)) : ℕ) = (i : ℕ) + 1 := rfl
      refine eq_zero_of_shift_iso m ?_
        (shiftShiftIsoSelf (X j) (a := -m) (b := m) (h := by ring)) (Iso.refl _) u
      intro v
      refine eq_zero_obj₁' (S'.distinguished i) ?_ ?_ v
      · intro w
        exact eq_zero_of_shift_iso (-m) (h' i.succ j hij) (Iso.refl _)
          (shiftShiftIsoSelf (X' i.succ) (by omega)) w
      · intro w
        exact eq_zero_of_shift_iso (-m) (ih j (by omega) (m - 1) (by omega)) (Iso.refl _)
          (shiftShiftIso (S'.obj i.castSucc) (by ring)) w
  induction i using Fin.induction with
  | zero => exact hom_zero_eq hg hg'
  | succ i ih =>
    have hc : ((i.castSucc : Fin (n + 1)) : ℕ) = (i : ℕ) := rfl
    have hs : ((i.succ : Fin (n + 1)) : ℕ) = (i : ℕ) + 1 := rfl
    let φ : Triangle.mk (S.π i.succ) (S.p i) (S.δ i) ⟶
        Triangle.mk (S'.π i.succ) (S'.p i) (S'.δ i) :=
      Triangle.homMk _ _ (g i.succ) (f i.succ) (g i.castSucc) (hg i.succ).symm (hgp i) (hgδ i)
    let ψ : Triangle.mk (S.π i.succ) (S.p i) (S.δ i) ⟶
        Triangle.mk (S'.π i.succ) (S'.p i) (S'.δ i) :=
      Triangle.homMk _ _ (g' i.succ) (f i.succ) (g' i.castSucc) (hg' i.succ).symm (hg'p i) (hg'δ i)
    have key : (rotate D).map ((rotate D).map φ) = (rotate D).map ((rotate D).map ψ) := by
      refine Triangle.hom_ext_of_hom₁_eq_of_hom₃_eq
        (rot_of_distTriang _ (rot_of_distTriang _ (S.distinguished i)))
        (rot_of_distTriang _ (rot_of_distTriang _ (S'.distinguished i))) _ _ ih rfl
        (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))))
      · intro w
        exact eq_zero_of_shift_iso (1 : ℤ) (hA i.castSucc i.succ (by omega) 0 (by omega))
          (shiftShiftIso (S.obj i.castSucc) (by ring)) (Iso.refl _) w
      · intro w
        exact eq_zero_of_shift_iso (1 : ℤ) (hB i.castSucc i.succ (by omega) (-1) (by omega))
          (Iso.refl _) (shiftShiftIsoSelf (S'.obj i.castSucc) (by ring)) w
    have h2 : (g i.succ)⟦(1 : ℤ)⟧' = (g' i.succ)⟦(1 : ℤ)⟧' := congrArg (fun α => α.hom₂) key
    exact (shiftFunctor D (1 : ℤ)).map_injective h2

end Uniqueness

/-- Let `Xₙ ⟶ ⋯ ⟶ X₀` and `X'ₙ ⟶ ⋯ ⟶ X'₀` be complexes in a pretriangulated category, let
`f i : Xᵢ ⟶ X'ᵢ` be a family of morphisms, and let `S`, `S'` be Postnikov systems for the two
complexes, with objects `Yᵢ`, `Y'ᵢ`. If

1. every morphism `Xᵢ⟦i⟧ ⟶ Y'ₙ⟦n⟧` with `i ≥ 1` is zero, or
2. every morphism `Yₙ⟦n⟧ ⟶ X'ⱼ⟦j⟧` with `j < n` is zero, or
3. every morphism `Xᵢ⟦i - j + 1⟧ ⟶ X'ⱼ` and every morphism `Xⱼ ⟶ X'ᵢ⟦i - j⟧` with `i < j` is
   zero,

then any two morphisms of Postnikov systems `S ⟶ S'` over `f` — families `g i : Yᵢ ⟶ Y'ᵢ`
compatible with the morphisms `Yᵢ ⟶ Xᵢ`, `Xᵢ₊₁ ⟶ Yᵢ` and `Yᵢ ⟶ Yᵢ₊₁⟦1⟧` of the two systems —
induce the same morphism `Yₙ ⟶ Y'ₙ` on the totalizations. Under (3) they agree in every
component (`PostnikovSystem.subsingleton_hom_of_hom_shift_eq_zero`); under (1) or (2) the
intermediate components need not agree (`PostnikovSystem.exists_not_subsingleton_hom` in
`StacksFrontier.CategoryTheory.Triangulated.PostnikovSystemsCounterexample`), and the
uniqueness of the totalization component is the corrected form of these two cases. -/
@[stacks 0FXE "(1), (2), (3): uniqueness of the component on the totalizations"]
theorem PostnikovSystem.subsingleton_hom_last {n : ℕ}
    {X X' : Fin (n + 1) → D} {d : ∀ i : Fin n, X i.succ ⟶ X i.castSucc}
    {d' : ∀ i : Fin n, X' i.succ ⟶ X' i.castSucc}
    (S : PostnikovSystem X d) (S' : PostnikovSystem X' d') (f : ∀ i, X i ⟶ X' i)
    (h : (∀ i : Fin (n + 1), 0 < (i : ℕ) →
            ∀ u : (X i)⟦((i : ℕ) : ℤ)⟧ ⟶ (S'.obj (Fin.last n))⟦(n : ℤ)⟧, u = 0) ∨
         (∀ j : Fin (n + 1), (j : ℕ) < n →
            ∀ u : (S.obj (Fin.last n))⟦(n : ℤ)⟧ ⟶ (X' j)⟦((j : ℕ) : ℤ)⟧, u = 0) ∨
         ((∀ i j : Fin (n + 1), (i : ℕ) < (j : ℕ) →
            ∀ u : (X i)⟦((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) + 1⟧ ⟶ X' j, u = 0) ∧
          (∀ i j : Fin (n + 1), (i : ℕ) < (j : ℕ) →
            ∀ u : X j ⟶ (X' i)⟦((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)⟧, u = 0))) :
    ((fun g : ∀ i, S.obj i ⟶ S'.obj i => g (Fin.last n)) ''
      {g : ∀ i, S.obj i ⟶ S'.obj i |
        (∀ i, g i ≫ S'.π i = S.π i ≫ f i) ∧
        (∀ i : Fin n, S.p i ≫ g i.castSucc = f i.succ ≫ S'.p i) ∧
        (∀ i : Fin n, S.δ i ≫ (g i.succ)⟦(1 : ℤ)⟧' = g i.castSucc ≫ S'.δ i)}).Subsingleton := by
  rintro _ ⟨g, ⟨hgπ, hgp, hgδ⟩, rfl⟩ _ ⟨g', ⟨hgπ', hgp', hgδ'⟩, rfl⟩
  rcases h with h₁ | h₂ | ⟨h₃, h₃'⟩
  · exact hom_last_eq_of_hom_shift_obj_last_eq_zero hgπ hgπ' hgδ hgδ' h₁
  · exact hom_last_eq_of_hom_shift_last_obj_eq_zero hgπ hgπ' h₂
  · exact hom_eq_of_hom_shift_eq_zero hgπ hgπ' hgp hgp' hgδ hgδ' h₃ h₃' (Fin.last n)

/-- Let `Xₙ ⟶ ⋯ ⟶ X₀` and `X'ₙ ⟶ ⋯ ⟶ X'₀` be complexes in a pretriangulated category, let
`f i : Xᵢ ⟶ X'ᵢ` be a family of morphisms, and let `S`, `S'` be Postnikov systems for the two
complexes, with objects `Yᵢ`, `Y'ᵢ`. If every morphism `Xᵢ⟦i - j + 1⟧ ⟶ X'ⱼ` and every morphism
`Xⱼ ⟶ X'ᵢ⟦i - j⟧` with `i < j` is zero (case (3) of the Stacks lemma), then there is at most one
morphism of Postnikov systems `S ⟶ S'` over `f`: any two families `g i : Yᵢ ⟶ Y'ᵢ` compatible
with the morphisms `Yᵢ ⟶ Xᵢ`, `Xᵢ₊₁ ⟶ Yᵢ` and `Yᵢ ⟶ Yᵢ₊₁⟦1⟧` of the two systems agree in every
component. -/
@[stacks 0FXE "(3): at most one morphism of Postnikov systems, all components"]
theorem PostnikovSystem.subsingleton_hom_of_hom_shift_eq_zero {n : ℕ}
    {X X' : Fin (n + 1) → D} {d : ∀ i : Fin n, X i.succ ⟶ X i.castSucc}
    {d' : ∀ i : Fin n, X' i.succ ⟶ X' i.castSucc}
    (S : PostnikovSystem X d) (S' : PostnikovSystem X' d') (f : ∀ i, X i ⟶ X' i)
    (h : ∀ i j : Fin (n + 1), (i : ℕ) < (j : ℕ) →
      ∀ u : (X i)⟦((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) + 1⟧ ⟶ X' j, u = 0)
    (h' : ∀ i j : Fin (n + 1), (i : ℕ) < (j : ℕ) →
      ∀ u : X j ⟶ (X' i)⟦((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)⟧, u = 0) :
    {g : ∀ i, S.obj i ⟶ S'.obj i |
      (∀ i, g i ≫ S'.π i = S.π i ≫ f i) ∧
      (∀ i : Fin n, S.p i ≫ g i.castSucc = f i.succ ≫ S'.p i) ∧
      (∀ i : Fin n, S.δ i ≫ (g i.succ)⟦(1 : ℤ)⟧' = g i.castSucc ≫ S'.δ i)}.Subsingleton := by
  rintro g ⟨hgπ, hgp, hgδ⟩ g' ⟨hgπ', hgp', hgδ'⟩
  funext i
  exact hom_eq_of_hom_shift_eq_zero hgπ hgπ' hgp hgp' hgδ hgδ' h h' i

/-! ### The image of a Postnikov system under a triangulated functor -/

section Map

universe v' u'

variable {E : Type u'} [Category.{v'} E] [HasZeroObject E] [HasShift E ℤ] [Preadditive E]
  [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E]

/-- A triangulated functor `F` carries a Postnikov system for `Xₙ ⟶ ⋯ ⟶ X₀` to a Postnikov
system for `F Xₙ ⟶ ⋯ ⟶ F X₀`, with objects `F Yᵢ`. Nothing is chosen: `F` preserves the
isomorphism `Y₀ ⟶ X₀` and the distinguished triangles, and its commutation with the shift turns
`F (Yᵢ ⟶ Yᵢ₊₁⟦1⟧)` into a morphism `F Yᵢ ⟶ (F Yᵢ₊₁)⟦1⟧`. -/
def PostnikovSystem.map {n : ℕ} {X : Fin (n + 1) → D}
    {d : ∀ i : Fin n, X i.succ ⟶ X i.castSucc} (S : PostnikovSystem X d) (F : D ⥤ E)
    [F.CommShift ℤ] [F.IsTriangulated] :
    PostnikovSystem (fun i ↦ F.obj (X i)) (fun i ↦ F.map (d i)) where
  obj i := F.obj (S.obj i)
  π i := F.map (S.π i)
  p i := F.map (S.p i)
  δ i := F.map (S.δ i) ≫ (F.commShiftIso (1 : ℤ)).hom.app (S.obj i.succ)
  distinguished i := F.map_distinguished _ (S.distinguished i)
  p_comp_π i := by rw [← F.map_comp, S.p_comp_π]

/-- The `i`-th object of `S.map F` is `F.obj (S.obj i)`. -/
@[simp]
theorem PostnikovSystem.map_obj {n : ℕ} {X : Fin (n + 1) → D}
    {d : ∀ i : Fin n, X i.succ ⟶ X i.castSucc} (S : PostnikovSystem X d) (F : D ⥤ E)
    [F.CommShift ℤ] [F.IsTriangulated] (i : Fin (n + 1)) :
    (S.map F).obj i = F.obj (S.obj i) :=
  rfl

/-- The `i`-th morphism `π` of `S.map F` is `F.map (S.π i)`. -/
@[simp]
theorem PostnikovSystem.map_π {n : ℕ} {X : Fin (n + 1) → D}
    {d : ∀ i : Fin n, X i.succ ⟶ X i.castSucc} (S : PostnikovSystem X d) (F : D ⥤ E)
    [F.CommShift ℤ] [F.IsTriangulated] (i : Fin (n + 1)) :
    (S.map F).π i = F.map (S.π i) :=
  rfl

/-- The `i`-th morphism `p` of `S.map F` is `F.map (S.p i)`. -/
@[simp]
theorem PostnikovSystem.map_p {n : ℕ} {X : Fin (n + 1) → D}
    {d : ∀ i : Fin n, X i.succ ⟶ X i.castSucc} (S : PostnikovSystem X d) (F : D ⥤ E)
    [F.CommShift ℤ] [F.IsTriangulated] (i : Fin n) :
    (S.map F).p i = F.map (S.p i) :=
  rfl

/-- The `i`-th connecting morphism of `S.map F` is `F.map (S.δ i)` followed by the commutation
isomorphism of `F` with the shift by `1`. -/
@[simp]
theorem PostnikovSystem.map_δ {n : ℕ} {X : Fin (n + 1) → D}
    {d : ∀ i : Fin n, X i.succ ⟶ X i.castSucc} (S : PostnikovSystem X d) (F : D ⥤ E)
    [F.CommShift ℤ] [F.IsTriangulated] (i : Fin n) :
    (S.map F).δ i =
      F.map (S.δ i) ≫ (F.commShiftIso (1 : ℤ)).hom.app (S.obj i.succ) :=
  rfl

end Map

end CategoryTheory.Triangulated

end
