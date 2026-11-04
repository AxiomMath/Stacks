module

public import StacksFrontier.CategoryTheory.Triangulated.Localization.Pretriangulated
import StacksCore.Tactic.StacksAttribute

/-!
# The filtered index category of a distinguished triangle

Let `C` be a pre-triangulated category and `W` a saturated multiplicative system compatible
with the triangulated structure. The index category of a distinguished triangle `T` is the
category `ℐ` of morphisms of triangles `T ⟶ T'` with `T'` distinguished and all three
components in `W`. It is filtered, and reading off the first, second or third component gives
a cofinal functor from `ℐ` to the category of `W`-morphisms out of the corresponding vertex of
`T`. The whole argument is one construction — the Ore condition MS2 completes a morphism of
`W` out of a vertex to a morphism of triangles, by TR1 and MS6 — run at the three vertices,
the second and third following from the first by rotating triangles.

## Main results

* `CategoryTheory.MorphismProperty.IsSaturated.isFiltered_and_final_component`: the category
  of `W`-morphisms of distinguished triangles out of a distinguished triangle `T` is filtered,
  and the three component functors to the categories of `W`-morphisms out of the vertices of
  `T` are cofinal.

## References

* [Stacks, Tag 05R9](https://stacks.math.columbia.edu/tag/05R9).
* The categories `X/W` and their filteredness are [Stacks, Tag 05Q0], and cofinal functors
  are [Stacks, Tag 04E6].
-/

@[expose] public section

universe v u

/-! ### The filtered index category of a distinguished triangle -/

section Index

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.MorphismProperty

section General

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C}

/-- A saturated multiplicative system contains every isomorphism: MS4 applied to the two
composites `u⁻¹ ≫ u = 𝟙` and `u ≫ u⁻¹ = 𝟙`, both of which lie in `W` by MS1. -/
private lemma isomorphisms_le_of_isSaturated (hW : W.IsSaturated) :
    MorphismProperty.isomorphisms C ≤ W := by
  have := hW.isMultiplicative
  intro A B u hu
  have : IsIso u := hu
  refine hW.mem_of_comp_mem_comp (inv u) u (inv u) ?_ ?_
  · simpa only [IsIso.inv_hom_id] using W.id_mem B
  · simpa only [IsIso.hom_inv_id] using W.id_mem A

/-- The Ore condition MS2: a morphism `f : X ⟶ Y` and a morphism `s : X ⟶ X'` of `W` are
completed by a commutative square `f ≫ t = s ≫ f'` with `t` in `W`. -/
lemma exists_leftSquare [W.HasLeftCalculusOfFractions] {X Y X' : C} (f : X ⟶ Y)
    (s : X ⟶ X') (hs : W s) :
    ∃ (Y' : C) (t : Y ⟶ Y') (_ : W t) (f' : X' ⟶ Y'), f ≫ t = s ≫ f' := by
  obtain ⟨ψ, hψ⟩ := (MorphismProperty.RightFraction.mk s hs f).exists_leftFraction
  exact ⟨ψ.Y', ψ.s, ψ.hs, ψ.f, hψ⟩

end General

/-- Every morphism out of `e.functor.obj X`, for `e` an equivalence, is the image under
`e.functor` of a morphism out of `X`, up to a canonical isomorphism of the target. -/
private lemma exists_desc {C D : Type*} [Category C] [Category D] (e : C ≌ D) {X : C} {V : D}
    (w : e.functor.obj X ⟶ V) :
    ∃ (V' : C) (v : X ⟶ V') (k : V ≅ e.functor.obj V'), w ≫ k.hom = e.functor.map v := by
  refine ⟨e.inverse.obj V, e.unitIso.hom.app X ≫ e.inverse.map w,
    (e.counitIso.app V).symm, ?_⟩
  rw [Iso.symm_hom, Iso.comp_inv_eq, Functor.map_comp, Category.assoc]
  simp

section Completion

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] {W : MorphismProperty C}

/-- `Completes W π` says that the vertex `π` of a distinguished triangle can be moved along
`W`: every morphism `v` of `W` out of `π.obj S`, for `S` distinguished, is dominated by `π` of
a morphism of distinguished triangles out of `S` all of whose components lie in `W`. It holds
at each of the three vertices, and it is the only property of a vertex that the proof of the
filteredness and cofinality statement uses. -/
private def Completes (W : MorphismProperty C) (π : Triangle C ⥤ C) : Prop :=
  ∀ (S : Triangle C), S ∈ distTriang C → ∀ (V : C) (v : π.obj S ⟶ V), W v →
    ∃ (S' : Triangle C) (_ : S' ∈ distTriang C) (φ : S ⟶ S') (u : V ⟶ π.obj S'),
      v ≫ u = π.map φ ∧ W φ.hom₁ ∧ W φ.hom₂ ∧ W φ.hom₃

omit [HasZeroObject C] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- A morphism of `W` out of `X⟦n⟧` is dominated by the `n`-fold shift of a morphism of `W`
out of `X`: the shift is an equivalence and `W` is stable under it. -/
private lemma exists_shift_desc (hW : W.IsSaturated) [W.IsCompatibleWithShift ℤ] {X V : C}
    (n : ℤ) (w : X⟦n⟧ ⟶ V) (hw : W w) :
    ∃ (V' : C) (v : X ⟶ V') (_ : W v) (k : V ≅ V'⟦n⟧), w ≫ k.hom = v⟦n⟧' := by
  obtain ⟨V', v, k, hk⟩ := exists_desc (shiftEquiv C n) w
  have := hW.isMultiplicative
  refine ⟨V', v, (MorphismProperty.IsCompatibleWithShift.iff W v n).1 ?_, k, hk⟩
  rw [show v⟦n⟧' = w ≫ k.hom from hk.symm]
  exact W.comp_mem _ _ hw (isomorphisms_le_of_isSaturated hW k.hom inferInstance)

/-- Completion is inherited by a shifted vertex: `π ⋙ shiftFunctor C n` completes as soon as
`π` does. This is what makes the third side of a triangle, which lands in
`π₁ ⋙ shiftFunctor C 1`, no different from the other two. -/
private lemma completes_shift (hW : W.IsSaturated) [W.IsCompatibleWithShift ℤ]
    {π : Triangle C ⥤ C} (hπ : Completes W π) (n : ℤ) :
    Completes W (π ⋙ shiftFunctor C n) := by
  intro S hS V w hw
  obtain ⟨V', v, hv, k, hk⟩ := exists_shift_desc hW n w hw
  obtain ⟨S', hS', φ, u, hu, h₁, h₂, h₃⟩ := hπ S hS V' v hv
  refine ⟨S', hS', φ, k.hom ≫ u⟦n⟧', ?_, h₁, h₂, h₃⟩
  rw [← Category.assoc, hk, ← Functor.map_comp, hu]
  rfl

variable [W.IsCompatibleWithTriangulation] [W.HasLeftCalculusOfFractions]

/-- **Completion at the first vertex**, the one construction the whole proof rests on: MS2
completes `v` and `S.mor₁` to a commutative square, TR1 puts a distinguished triangle on the
resulting morphism, and MS6 — compatibility of `W` with the triangulation — produces the third
component. -/
private lemma completes_π₁ : Completes W Triangle.π₁ := by
  intro S hS V v hv
  obtain ⟨Y', t, ht, f', hf'⟩ := exists_leftSquare S.mor₁ v hv
  obtain ⟨Z', g', h', hS'⟩ := distinguished_cocone_triangle f'
  obtain ⟨c, hc, hc₂, hc₃⟩ :=
    MorphismProperty.compatible_with_triangulation (W := W) S (Triangle.mk f' g' h') hS hS'
      v t hv ht hf'
  exact ⟨Triangle.mk f' g' h', hS', Triangle.homMk _ _ v t c hf' hc₂ hc₃, 𝟙 _,
    Category.comp_id v, hv, ht, hc⟩

omit [W.HasLeftCalculusOfFractions] in
/-- Transport of a completion along the rotation of triangles: a `W`-morphism of triangles out
of `T.rotate` gives one out of `T` into the inverse rotation of its target, with the
components shifted back by one place. -/
private lemma exists_invRotate_hom (hW : W.IsSaturated) {T S : Triangle C} (φ : T.rotate ⟶ S)
    (h₁ : W φ.hom₁) (h₂ : W φ.hom₂) (h₃ : W φ.hom₃) :
    ∃ ψ : T ⟶ S.invRotate, W ψ.hom₁ ∧ W ψ.hom₂ ∧ W ψ.hom₃ ∧
      ψ.hom₂ = φ.hom₁ ∧ ψ.hom₃ = φ.hom₂ := by
  have := hW.isMultiplicative
  refine ⟨rotCompInvRot.hom.app T ≫ (invRotate C).map φ, ?_, ?_, ?_,
    Category.id_comp _, Category.id_comp _⟩
  · exact W.comp_mem _ _
      (isomorphisms_le_of_isSaturated hW
        ((shiftFunctorCompIsoId C (1 : ℤ) (-1) (by omega)).inv.app T.obj₁) inferInstance)
      ((MorphismProperty.IsCompatibleWithShift.iff W φ.hom₃ (-1 : ℤ)).2 h₃)
  · exact W.comp_mem _ _ (W.id_mem T.obj₂) h₁
  · exact W.comp_mem _ _ (W.id_mem T.obj₃) h₂

/-- **Completion at the second vertex**, deduced from the first by rotation. -/
private lemma completes_π₂ (hW : W.IsSaturated) : Completes W Triangle.π₂ := by
  intro T hT V v hv
  obtain ⟨S, hS, φ, u, hu, h₁, h₂, h₃⟩ := completes_π₁ T.rotate (rot_of_distTriang T hT) V v hv
  obtain ⟨ψ, k₁, k₂, k₃, e₂, _⟩ := exists_invRotate_hom hW φ h₁ h₂ h₃
  exact ⟨S.invRotate, inv_rot_of_distTriang S hS, ψ, u, hu.trans e₂.symm, k₁, k₂, k₃⟩

/-- **Completion at the third vertex**, deduced from the second by rotation. -/
private lemma completes_π₃ (hW : W.IsSaturated) : Completes W Triangle.π₃ := by
  intro T hT V v hv
  obtain ⟨S, hS, φ, u, hu, h₁, h₂, h₃⟩ :=
    completes_π₂ hW T.rotate (rot_of_distTriang T hT) V v hv
  obtain ⟨ψ, k₁, k₂, k₃, _, e₃⟩ := exists_invRotate_hom hW φ h₁ h₂ h₃
  exact ⟨S.invRotate, inv_rot_of_distTriang S hS, ψ, u, hu.trans e₃.symm, k₁, k₂, k₃⟩

end Completion

section Objects

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The property of an object of `Under T` of being an object of the index category `ℐ`: its
target is a distinguished triangle and the three components of its structural morphism lie in
`W`. -/
private def objProp (W : MorphismProperty C) (T : Triangle C) : ObjectProperty (Under T) :=
  fun A => A.right ∈ distTriang C ∧ W A.hom.hom₁ ∧ W A.hom.hom₂ ∧ W A.hom.hom₃

omit [HasZeroObject C] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- The image under a vertex `π` of `CategoryTheory.Under.w`: at every vertex, the structural
morphism of `B` is the structural morphism of `A` followed by a morphism `A ⟶ B` of
`Under T`. -/
private lemma map_under_w {T : Triangle C} (π : Triangle C ⥤ C) {A B : Under T} (β : A ⟶ B) :
    π.map A.hom ≫ π.map β.right = π.map B.hom := by
  rw [← π.map_comp, CategoryTheory.Under.w]

omit [HasZeroObject C] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- Agreement of two morphisms of `Under T` at one vertex survives postcomposition. -/
private lemma map_right_congr {T : Triangle C} {π : Triangle C ⥤ C} {A B Z : Under T}
    {f g : A ⟶ B} (β : B ⟶ Z) (h : π.map f.right = π.map g.right) :
    π.map (f ≫ β).right = π.map (g ≫ β).right := by
  simp only [CategoryTheory.Under.comp_right, π.map_comp, h]

omit [HasZeroObject C] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- A square between two vertices stays commuting when its target triangle is replaced by a
further one: this is naturality of `μ` at the replacing morphism. -/
private lemma comp_sq {π ρ : Triangle C ⥤ C} (μ : π ⟶ ρ) {A B B' : Triangle C}
    (p : π.obj A ⟶ π.obj B) (r : ρ.obj A ⟶ ρ.obj B) (β : B ⟶ B')
    (h : μ.app A ≫ r = p ≫ μ.app B) :
    μ.app A ≫ r ≫ ρ.map β = (p ≫ π.map β) ≫ μ.app B' := by
  rw [← Category.assoc, h, Category.assoc, ← μ.naturality, ← Category.assoc]

/-- A candidate for a morphism of the index category from `A` to `B`: three components
compatible with the structural morphisms out of `T`, not yet required to form a morphism of
triangles. -/
private structure Cand {T : Triangle C} (A B : Under T) where
  /-- The component at the first vertex. -/
  app₁ : A.right.obj₁ ⟶ B.right.obj₁
  /-- The component at the second vertex. -/
  app₂ : A.right.obj₂ ⟶ B.right.obj₂
  /-- The component at the third vertex. -/
  app₃ : A.right.obj₃ ⟶ B.right.obj₃
  /-- Compatibility with the structural morphisms at the first vertex. -/
  w₁ : A.hom.hom₁ ≫ app₁ = B.hom.hom₁
  /-- Compatibility with the structural morphisms at the second vertex. -/
  w₂ : A.hom.hom₂ ≫ app₂ = B.hom.hom₂
  /-- Compatibility with the structural morphisms at the third vertex. -/
  w₃ : A.hom.hom₃ ≫ app₃ = B.hom.hom₃

/-- Push a candidate along a morphism of `Under T`. -/
private def Cand.comp {T : Triangle C} {A B B' : Under T} (c : Cand A B) (β : B ⟶ B') :
    Cand A B' where
  app₁ := c.app₁ ≫ β.right.hom₁
  app₂ := c.app₂ ≫ β.right.hom₂
  app₃ := c.app₃ ≫ β.right.hom₃
  w₁ := by rw [← Category.assoc, c.w₁]; exact map_under_w Triangle.π₁ β
  w₂ := by rw [← Category.assoc, c.w₂]; exact map_under_w Triangle.π₂ β
  w₃ := by rw [← Category.assoc, c.w₃]; exact map_under_w Triangle.π₃ β

omit [HasZeroObject C] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- The first component of `Cand.comp`, shifted — the shape in which the third square of a
candidate is stated. -/
private lemma Cand.comp_app₁_shift {T : Triangle C} {A B B' : Under T} (c : Cand A B)
    (β : B ⟶ B') : (c.comp β).app₁⟦(1 : ℤ)⟧' =
      c.app₁⟦(1 : ℤ)⟧' ≫ (Triangle.π₁ ⋙ shiftFunctor C (1 : ℤ)).map β.right :=
  Functor.map_comp _ _ _

/-- A candidate whose three squares commute is a morphism of `Under T`. -/
private def Cand.toHom {T : Triangle C} {A B : Under T} (c : Cand A B)
    (h₁ : A.right.mor₁ ≫ c.app₂ = c.app₁ ≫ B.right.mor₁)
    (h₂ : A.right.mor₂ ≫ c.app₃ = c.app₂ ≫ B.right.mor₂)
    (h₃ : A.right.mor₃ ≫ c.app₁⟦(1 : ℤ)⟧' = c.app₃ ≫ B.right.mor₃) : A ⟶ B :=
  CategoryTheory.Under.homMk (Triangle.homMk _ _ c.app₁ c.app₂ c.app₃ h₁ h₂ h₃)
    (Triangle.hom_ext _ _ c.w₁ c.w₂ c.w₃)

variable {W : MorphismProperty C} [W.IsCompatibleWithTriangulation]
  [W.HasLeftCalculusOfFractions]

omit [W.IsCompatibleWithTriangulation] in
/-- **Replacement.** An object `A` of the index category and a morphism `v` of `W` out of the
`π`-vertex of its target are dominated by a further object receiving a morphism from `A`: this
is `Completes W π` with the structural morphism of `A` composed in. -/
private lemma exists_extension {T : Triangle C} {π : Triangle C ⥤ C} (hπ : Completes W π)
    {A : Under T} (hA : objProp W T A) {V : C} (v : π.obj A.right ⟶ V) (hv : W v) :
    ∃ (B : Under T) (_ : objProp W T B) (β : A ⟶ B) (u : V ⟶ π.obj B.right),
      v ≫ u = π.map β.right := by
  obtain ⟨S, hS, φ, u, hu, h₁, h₂, h₃⟩ := hπ A.right hA.1 V v hv
  exact ⟨CategoryTheory.Under.mk (A.hom ≫ φ),
    ⟨hS, W.comp_mem _ _ hA.2.1 h₁, W.comp_mem _ _ hA.2.2.1 h₂, W.comp_mem _ _ hA.2.2.2 h₃⟩,
    CategoryTheory.Under.homMk φ rfl, u, hu⟩

omit [W.IsCompatibleWithTriangulation] in
/-- **Cancellation, then replacement** — the step that closes every commutativity obligation
in this proof. Two morphisms into the `π`-vertex of an object `B` that agree after
precomposition with a morphism `w` of `W` agree outright once `B` is replaced by a further
object: MS3 produces a morphism of `W` equalizing them, and `exists_extension` turns that
morphism into a morphism of the index category. -/
private lemma exists_extension_comp_eq {T : Triangle C} {π : Triangle C ⥤ C}
    (hπ : Completes W π) {B : Under T} (hB : objProp W T B) {U U' : C}
    (f g : U ⟶ π.obj B.right) (w : U' ⟶ U) (hw : W w) (h : w ≫ f = w ≫ g) :
    ∃ (B' : Under T) (_ : objProp W T B') (β : B ⟶ B'),
      f ≫ π.map β.right = g ≫ π.map β.right := by
  obtain ⟨V, s, hs, hsq⟩ := MorphismProperty.HasLeftCalculusOfFractions.ext f g w hw h
  obtain ⟨B', hB', β, u, hu⟩ := exists_extension hπ hB s hs
  refine ⟨B', hB', β, ?_⟩
  rw [← hu]
  simp only [← Category.assoc]
  rw [hsq]

omit [W.IsCompatibleWithTriangulation] in
/-- **A common target at one vertex.** Given objects `A`, `B` of the index category, some
object `B'` receiving a morphism from `B` receives, at the `π`-vertex, a morphism from `A`
compatible with the structural morphisms out of `T`. This is the Ore condition MS2 followed by
a replacement. -/
private lemma exists_component {T : Triangle C} {π : Triangle C ⥤ C} (hπ : Completes W π)
    {A B : Under T} (hA : W (π.map A.hom)) (hB : objProp W T B) :
    ∃ (B' : Under T) (_ : objProp W T B') (_ : B ⟶ B') (a : π.obj A.right ⟶ π.obj B'.right),
      π.map A.hom ≫ a = π.map B'.hom := by
  obtain ⟨V, t, ht, a, ha⟩ := exists_leftSquare (π.map B.hom) (π.map A.hom) hA
  obtain ⟨B', hB', β, u, hu⟩ := exists_extension hπ hB t ht
  exact ⟨B', hB', β, a ≫ u, by rw [← Category.assoc, ← ha, Category.assoc, hu, map_under_w]⟩

omit [HasZeroObject C] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [W.IsCompatibleWithTriangulation] in
/-- A component compatible with the structural morphisms out of `T` stays compatible when its
target is replaced by a further object of `Under T`. -/
private lemma comp_component {T : Triangle C} {π : Triangle C ⥤ C} {A B B' : Under T}
    (a : π.obj A.right ⟶ π.obj B.right) (β : B ⟶ B')
    (h : π.map A.hom ≫ a = π.map B.hom) :
    π.map A.hom ≫ a ≫ π.map β.right = π.map B'.hom := by
  rw [← Category.assoc, h, map_under_w]

omit [W.IsCompatibleWithTriangulation] in
/-- **Equalizing at one vertex.** Two parallel morphisms of `Under T` between objects of the
index category agree at the `π`-vertex after a further morphism. -/
private lemma exists_equalize {T : Triangle C} {π : Triangle C ⥤ C} (hπ : Completes W π)
    {A B : Under T} (hA : W (π.map A.hom)) (hB : objProp W T B) (f g : A ⟶ B) :
    ∃ (Z : Under T) (_ : objProp W T Z) (β : B ⟶ Z),
      π.map (f ≫ β).right = π.map (g ≫ β).right := by
  obtain ⟨Z, hZ, β, hβ⟩ := exists_extension_comp_eq hπ hB (π.map f.right) (π.map g.right)
    (π.map A.hom) hA (by rw [map_under_w, map_under_w])
  exact ⟨Z, hZ, β, by simpa only [CategoryTheory.Under.comp_right, π.map_comp] using hβ⟩

omit [W.IsCompatibleWithTriangulation] in
/-- **Making a square commute.** Two components `p` and `r`, at the ends of a natural
transformation `μ : π ⟶ ρ` and each compatible with the structural morphisms out of `T`, make
`μ`'s square commute once `B` is replaced by a further object: the two ways round the square
already agree after precomposition with the structural morphism of `A`, which lies in `W`, so
this is `exists_extension_comp_eq`. -/
private lemma exists_sq {T : Triangle C} {π ρ : Triangle C ⥤ C} (μ : π ⟶ ρ)
    (hρ : Completes W ρ) {A B : Under T} (hA : W (π.map A.hom)) (hB : objProp W T B)
    (p : π.obj A.right ⟶ π.obj B.right) (r : ρ.obj A.right ⟶ ρ.obj B.right)
    (hp : π.map A.hom ≫ p = π.map B.hom) (hr : ρ.map A.hom ≫ r = ρ.map B.hom) :
    ∃ (B' : Under T) (_ : objProp W T B') (β : B ⟶ B'),
      μ.app A.right ≫ r ≫ ρ.map β.right = (p ≫ π.map β.right) ≫ μ.app B'.right := by
  obtain ⟨B', hB', β, hβ⟩ := exists_extension_comp_eq hρ hB (μ.app A.right ≫ r)
    (p ≫ μ.app B.right) (π.map A.hom) hA (by
      rw [← Category.assoc, μ.naturality, Category.assoc, hr, ← Category.assoc, hp,
        μ.naturality])
  refine ⟨B', hB', β, ?_⟩
  rw [Category.assoc, μ.naturality]
  simp only [← Category.assoc]
  exact hβ

/-- **The three components.** Three successive replacements of `B`, one at each vertex,
produce a candidate morphism out of `A`: the Ore condition MS2 at the first, second and third
vertex. -/
private lemma exists_cand (hW : W.IsSaturated) {T : Triangle C} {A B : Under T}
    (hA : objProp W T A) (hB : objProp W T B) :
    ∃ (B' : Under T) (_ : objProp W T B') (_ : B ⟶ B'), Nonempty (Cand A B') := by
  obtain ⟨B₁, hB₁, β₁, a₁, e₁⟩ := exists_component completes_π₁ (A := A) hA.2.1 hB
  obtain ⟨B₂, hB₂, β₂, a₂, e₂⟩ := exists_component (completes_π₂ hW) (A := A) hA.2.2.1 hB₁
  obtain ⟨B₃, hB₃, β₃, a₃, e₃⟩ := exists_component (completes_π₃ hW) (A := A) hA.2.2.2 hB₂
  exact ⟨B₃, hB₃, β₁ ≫ β₂ ≫ β₃,
    ⟨⟨_, _, a₃, comp_component a₁ (β₂ ≫ β₃) e₁, comp_component a₂ β₃ e₂, e₃⟩⟩⟩

/-- **Condition (2) of filteredness**: two objects of the index category admit a common
target. The target of the second is replaced six times: three times to produce a candidate
(`exists_cand`), and three more to make its three squares commute, each `exists_sq`
preserving — by `comp_sq` — the squares already made to commute. -/
private lemma exists_cocone (hW : W.IsSaturated) {T : Triangle C} {A B : Under T}
    (hA : objProp W T A) (hB : objProp W T B) :
    ∃ (Z : Under T) (_ : objProp W T Z), Nonempty (A ⟶ Z) ∧ Nonempty (B ⟶ Z) := by
  obtain ⟨B₀, hB₀, β₀, ⟨c⟩⟩ := exists_cand hW hA hB
  obtain ⟨B₁, hB₁, γ₁, s₁⟩ := exists_sq Triangle.π₁Toπ₂ (completes_π₂ hW) hA.2.1 hB₀
    c.app₁ c.app₂ c.w₁ c.w₂
  let c₁ := c.comp γ₁
  obtain ⟨B₂, hB₂, γ₂, s₂⟩ := exists_sq Triangle.π₂Toπ₃ (completes_π₃ hW) hA.2.2.1 hB₁
    c₁.app₂ c₁.app₃ c₁.w₂ c₁.w₃
  let c₂ := c₁.comp γ₂
  obtain ⟨B₃, hB₃, γ₃, s₃⟩ := exists_sq Triangle.π₃Toπ₁ (completes_shift hW completes_π₁ 1)
    hA.2.2.2 hB₂ c₂.app₃ (c₂.app₁⟦(1 : ℤ)⟧') c₂.w₃
    (((shiftFunctor C (1 : ℤ)).map_comp _ _).symm.trans
      (congrArg (shiftFunctor C (1 : ℤ)).map c₂.w₁))
  exact ⟨B₃, hB₃, ⟨Cand.toHom (c₂.comp γ₃)
      (comp_sq Triangle.π₁Toπ₂ c₂.app₁ c₂.app₂ γ₃.right
        (comp_sq Triangle.π₁Toπ₂ c₁.app₁ c₁.app₂ γ₂.right s₁))
      (comp_sq Triangle.π₂Toπ₃ c₂.app₂ c₂.app₃ γ₃.right s₂)
      (by rw [Cand.comp_app₁_shift]; exact s₃)⟩,
    ⟨β₀ ≫ γ₁ ≫ γ₂ ≫ γ₃⟩⟩

/-- **Condition (3) of filteredness**: two parallel morphisms between objects of the index
category are equalized by a further morphism, one vertex at a time. -/
private lemma exists_coeq (hW : W.IsSaturated) {T : Triangle C} {A B : Under T}
    (hA : objProp W T A) (hB : objProp W T B) (f g : A ⟶ B) :
    ∃ (Z : Under T) (_ : objProp W T Z) (β : B ⟶ Z), f ≫ β = g ≫ β := by
  obtain ⟨Z₁, hZ₁, β₁, q₁⟩ := exists_equalize completes_π₁ hA.2.1 hB f g
  obtain ⟨Z₂, hZ₂, β₂, q₂⟩ :=
    exists_equalize (completes_π₂ hW) hA.2.2.1 hZ₁ (f ≫ β₁) (g ≫ β₁)
  obtain ⟨Z₃, hZ₃, β₃, q₃⟩ :=
    exists_equalize (completes_π₃ hW) hA.2.2.2 hZ₂ ((f ≫ β₁) ≫ β₂) ((g ≫ β₁) ≫ β₂)
  refine ⟨Z₃, hZ₃, β₁ ≫ β₂ ≫ β₃, ?_⟩
  simp only [← Category.assoc]
  exact CategoryTheory.Under.UnderMorphism.ext (Triangle.hom_ext _ _
    (map_right_congr β₃ (map_right_congr β₂ q₁)) (map_right_congr β₃ q₂) q₃)

omit [W.IsCompatibleWithTriangulation] in
/-- **Cofinality of a component functor.** Finality of a functor out of a filtered category
asks that every object of `T.objᵢ/W` admit a morphism to the image of an object of the index
category — this is `Completes W π` at `T` itself — and that two morphisms into the same image
be equalized, which is `exists_extension_comp_eq`. -/
private lemma final_component {T : Triangle C} (hT : T ∈ distTriang C)
    {ℐ : ObjectProperty (Under T)} (hℐ : ∀ A : Under T, ℐ A ↔ objProp W T A)
    [IsFilteredOrEmpty ℐ.FullSubcategory] {π : Triangle C ⥤ C} (hπ : Completes W π)
    (hP : ∀ A : ℐ.FullSubcategory, W (π.map A.obj.hom)) :
    (MorphismProperty.Comma.lift (ℐ.ι ⋙ CategoryTheory.Under.post π) hP
      (fun _ => trivial) (fun _ => trivial) :
        ℐ.FullSubcategory ⥤ W.Under ⊤ (π.obj T)).Final := by
  refine Functor.final_of_exists_of_isFiltered _ (fun d => ?_) (fun {d c} s s' => ?_)
  · obtain ⟨S, hS, φ, u, hu, h₁, h₂, h₃⟩ := hπ T hT d.right d.hom d.prop
    exact ⟨⟨CategoryTheory.Under.mk φ, (hℐ _).2 ⟨hS, h₁, h₂, h₃⟩⟩,
      ⟨MorphismProperty.Under.homMk u hu⟩⟩
  · have key : d.hom ≫ s.right = d.hom ≫ s'.right := by
      rw [MorphismProperty.Under.w, MorphismProperty.Under.w]
    obtain ⟨Z, hZ, β, hβ⟩ := exists_extension_comp_eq hπ ((hℐ _).1 c.2) s.right s'.right
      d.hom d.prop key
    exact ⟨⟨Z, (hℐ _).2 hZ⟩, ObjectProperty.homMk β, MorphismProperty.Under.Hom.ext hβ⟩

end Objects

end Index

section IndexMain

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Let `W` be a saturated multiplicative system of a pre-triangulated category `C`, compatible
with the triangulated structure, and let `T = (X, Y, Z, f, g, h)` be a distinguished triangle of
`C`. Let `ℐ` be the category of `W`-morphisms of triangles out of `T`: the full subcategory of
`Under T` in `Triangle C` whose objects are the morphisms of triangles `(s, s', s'') : T ⟶ T'` with
`T'` distinguished and `s, s', s''` in `W`.

Then `ℐ` is filtered, and the three functors `ℐ ⥤ X/W`, `ℐ ⥤ Y/W`, `ℐ ⥤ Z/W` given by
`(s, s', s'') ↦ s`, `s'`, `s''` — the projections `Triangle.π₁`, `Triangle.π₂`, `Triangle.π₃` read
on morphisms under `T` — are cofinal. -/
@[stacks 05R9, sga "4 XVII 1.2.2.1"]
theorem CategoryTheory.MorphismProperty.IsSaturated.isFiltered_and_final_component
    {W : MorphismProperty C} (hW : W.IsSaturated) [W.IsCompatibleWithTriangulation]
    {T : Triangle C} (hT : T ∈ distTriang C) (ℐ : ObjectProperty (Under T))
    (hℐ : ∀ A : Under T, ℐ A ↔
      A.right ∈ distTriang C ∧ W A.hom.hom₁ ∧ W A.hom.hom₂ ∧ W A.hom.hom₃) :
    IsFiltered ℐ.FullSubcategory ∧
      (MorphismProperty.Comma.lift (ℐ.ι ⋙ Under.post Triangle.π₁)
        (fun A => ((hℐ _).1 A.2).2.1) (fun _ => trivial) (fun _ => trivial) :
          ℐ.FullSubcategory ⥤ W.Under ⊤ T.obj₁).Final ∧
      (MorphismProperty.Comma.lift (ℐ.ι ⋙ Under.post Triangle.π₂)
        (fun A => ((hℐ _).1 A.2).2.2.1) (fun _ => trivial) (fun _ => trivial) :
          ℐ.FullSubcategory ⥤ W.Under ⊤ T.obj₂).Final ∧
      (MorphismProperty.Comma.lift (ℐ.ι ⋙ Under.post Triangle.π₃)
        (fun A => ((hℐ _).1 A.2).2.2.2) (fun _ => trivial) (fun _ => trivial) :
          ℐ.FullSubcategory ⥤ W.Under ⊤ T.obj₃).Final := by
  have := hW.hasLeftCalculusOfFractions
  have := hW.isMultiplicative
  have : IsFilteredOrEmpty ℐ.FullSubcategory := by
    constructor
    · intro X Y
      obtain ⟨Z, hZ, ⟨α⟩, ⟨β⟩⟩ := exists_cocone hW ((hℐ _).1 X.2) ((hℐ _).1 Y.2)
      exact ⟨⟨Z, (hℐ _).2 hZ⟩, ObjectProperty.homMk α, ObjectProperty.homMk β, trivial⟩
    · intro X Y f g
      obtain ⟨Z, hZ, β, hβ⟩ := exists_coeq hW ((hℐ _).1 X.2) ((hℐ _).1 Y.2) f.hom g.hom
      exact ⟨⟨Z, (hℐ _).2 hZ⟩, ObjectProperty.homMk β, ObjectProperty.hom_ext _ hβ⟩
  exact ⟨{ nonempty := ⟨⟨CategoryTheory.Under.mk (𝟙 T),
      (hℐ _).2 ⟨hT, W.id_mem _, W.id_mem _, W.id_mem _⟩⟩⟩ },
    final_component hT hℐ completes_π₁ _,
    final_component hT hℐ (completes_π₂ hW) _,
    final_component hT hℐ (completes_π₃ hW) _⟩

end IndexMain

end
