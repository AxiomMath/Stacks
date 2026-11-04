module

public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Opposite.Basic
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import StacksFrontier.CategoryTheory.EssentiallyConstant.Cofinal
import StacksFrontier.CategoryTheory.EssentiallyConstant.IndObject
public import StacksFrontier.CategoryTheory.Functor.Derived.DefinedAt
import StacksFrontier.CategoryTheory.Functor.Derived.Morphisms
public import StacksFrontier.CategoryTheory.Localization.Saturated.Defs
import StacksFrontier.CategoryTheory.Triangulated.Localization
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.CategoryTheory.Functor.Derived.Triangle.EssentiallyConstant

/-!
# The right derived functor along a distinguished triangle

Saturated systems respect isomorphisms, and definedness of `RF` at two vertices of a
distinguished triangle gives it at the third, with a distinguished triangle of values. Part of
the proof of [Stacks, Tag 05SC].
-/

section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

open scoped CategoryTheory.Pretriangulated.Opposite

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace DerivedFunctorValues

section Saturation

variable {C : Type u₁} [Category.{v₁} C]

/-- A saturated multiplicative system contains every isomorphism: MS4 applied to the two
composites `u⁻¹ ≫ u = 𝟙` and `u ≫ u⁻¹ = 𝟙`, both of which lie in `W` by MS1. -/
lemma isomorphisms_le_of_isSaturated {W : MorphismProperty C} (hW : W.IsSaturated) :
    MorphismProperty.isomorphisms C ≤ W := by
  have := hW.isMultiplicative
  intro A B u hu
  have : IsIso u := hu
  refine hW.mem_of_comp_mem_comp (inv u) u (inv u) ?_ ?_
  · simpa only [IsIso.inv_hom_id] using W.id_mem B
  · simpa only [IsIso.hom_inv_id] using W.id_mem A

/-- A saturated multiplicative system respects isomorphisms: it contains them and is stable under
composition. -/
lemma respectsIso_of_isSaturated {W : MorphismProperty C} (hW : W.IsSaturated) :
    W.RespectsIso :=
  have := hW.isMultiplicative
  MorphismProperty.respectsIso_of_isStableUnderComposition (isomorphisms_le_of_isSaturated hW)

end Saturation

section Triangulated

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {H : Type u₂} [Category.{v₂} H] [HasZeroObject H] [HasShift H ℤ] [Preadditive H]
  [∀ n : ℤ, (shiftFunctor H n).Additive] [Pretriangulated H]

omit [HasZeroObject C] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [HasZeroObject H] [Preadditive H]
  [∀ n : ℤ, (shiftFunctor H n).Additive] [Pretriangulated H] in
/-- The shift of a split idempotent situation: a section is carried to a section by `(-)⟦n⟧`. -/
private lemma shift_comp_eq_id {P Q : H} {f : P ⟶ Q} {g : Q ⟶ P} (h : f ≫ g = 𝟙 P) (n : ℤ) :
    (f⟦n⟧') ≫ (g⟦n⟧') = 𝟙 (P⟦n⟧) := by
  rw [← (shiftFunctor H n).map_comp, h, (shiftFunctor H n).map_id]

/-- Morphisms into the source of a split monomorphism are equal if they are after it. -/
private lemma eq_of_comp_eq_of_split {D : Type*} [Category D] {P Q V : D} {f : P ⟶ Q} {g : Q ⟶ P}
    (h : f ≫ g = 𝟙 P) {x y : V ⟶ P} (hxy : x ≫ f = y ≫ f) : x = y :=
  have := IsSplitMono.mk' ⟨g, h⟩
  (cancel_mono f).1 hxy

omit [HasZeroObject H] [Preadditive H] [∀ n : ℤ, (shiftFunctor H n).Additive]
  [Pretriangulated H] in
/-- **Transport of a factorization property along the shift.** Let `M : I ⥤ H` be a diagram, `P`
an object and `φ` a family of morphisms `P ⟶ M(i)`. If every morphism `V ⟶ M(i)` factors as
`h ≫ φ(k)` after a transition `i ⟶ k` — the surjectivity half of the comparison map
`Mor(V, P) ⟶ colim_i Mor(V, M(i))` of Tag 05PY(4), spelled out without a colimit — then the same
holds for the shifted diagram and family. The shift functor is an equivalence, so a morphism
`V ⟶ M(i)⟦n⟧` is the shift of a morphism `V⟦-n⟧ ⟶ M(i)` up to the canonical isomorphism
`V⟦-n⟧⟦n⟧ ≅ V`. -/
private lemma exists_factorization_shift {I : Type*} [Category I] (M : I ⥤ H)
    (P : H) (φ : ∀ i, P ⟶ M.obj i) (n : ℤ)
    (hsurj : ∀ (V : H) (i : I) (g : V ⟶ M.obj i),
      ∃ (k : I) (τ : i ⟶ k) (h : V ⟶ P), g ≫ M.map τ = h ≫ φ k)
    (V : H) (i : I) (g : V ⟶ (M.obj i)⟦n⟧) :
    ∃ (k : I) (τ : i ⟶ k) (h : V ⟶ P⟦n⟧),
      g ≫ (M.map τ)⟦n⟧' = h ≫ (φ k)⟦n⟧' := by
  set e := (shiftFunctorCompIsoId H (-n) n (neg_add_cancel n)).app V with he
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : V⟦-n⟧ ⟶ M.obj i, g₀⟦n⟧' = e.hom ≫ g :=
    ⟨(shiftFunctor H n).preimage (e.hom ≫ g), (shiftFunctor H n).map_preimage _⟩
  obtain ⟨k, τ, h₀, hk⟩ := hsurj _ i g₀
  refine ⟨k, τ, e.inv ≫ h₀⟦n⟧', ?_⟩
  have key : h₀⟦n⟧' ≫ (φ k)⟦n⟧' = e.hom ≫ g ≫ (M.map τ)⟦n⟧' := by
    rw [← Functor.map_comp, ← hk, Functor.map_comp, hg₀, Category.assoc]
  rw [Category.assoc, key, Iso.inv_hom_id_assoc]

/-- **The five lemma for a system of distinguished triangles over an essentially constant one.**
Let `N : I ⥤ Triangle H` be a diagram of distinguished triangles, `T₀` a distinguished triangle
and `φ` a family of morphisms of triangles `T₀ ⟶ N(i)`, compatible with the transitions. Assume
that at the first and second vertices every morphism `V ⟶ N(i).objₘ` factors through some
`φ(k).homₘ` after a transition, and that `φ(i).hom₂` is a split monomorphism. Then the same
factorization property holds at the third vertex.

*Argument (the source's, with the colimits replaced by the transition data that witnesses
equality of classes in them).* Given `g : V ⟶ N(i).obj₃`, push it into `N(i).obj₁⟦1⟧` along
`N(i).mor₃` and factor it as `h₁ ≫ φ(k).hom₁⟦1⟧`. Then `h₁ ≫ T₀.mor₁⟦1⟧` dies against the split
monomorphism `φ(k).hom₂⟦1⟧`, hence vanishes, so `h₁ = h ≫ T₀.mor₃` for some `h : V ⟶ T₀.obj₃` by
exactness of `Mor(V, -)` on `T₀`. The difference `g ≫ N(τ).hom₃ - h ≫ φ(k).hom₃` then dies
against `N(k).mor₃`, so it is `e ≫ N(k).mor₂` by exactness on `N(k)`; factoring `e` at the second
vertex and using the two commuting squares of `φ` and of `N(τ')` exhibits `g` as
`(h + h₂ ≫ T₀.mor₂) ≫ φ(l).hom₃` after the transition `τ ≫ τ'`. -/
private lemma exists_factorization_hom₃ {I : Type*} [Category I] (N : I ⥤ Triangle H)
    (hN : ∀ i, N.obj i ∈ distTriang H) {T₀ : Triangle H} (hT₀ : T₀ ∈ distTriang H)
    (φ : ∀ i, T₀ ⟶ N.obj i) (hφ : ∀ {i j : I} (τ : i ⟶ j), φ i ≫ N.map τ = φ j)
    (hsurj₁ : ∀ (V : H) (i : I) (g : V ⟶ (N.obj i).obj₁),
      ∃ (k : I) (τ : i ⟶ k) (h : V ⟶ T₀.obj₁), g ≫ (N.map τ).hom₁ = h ≫ (φ k).hom₁)
    (hsurj₂ : ∀ (V : H) (i : I) (g : V ⟶ (N.obj i).obj₂),
      ∃ (k : I) (τ : i ⟶ k) (h : V ⟶ T₀.obj₂), g ≫ (N.map τ).hom₂ = h ≫ (φ k).hom₂)
    (hsplit₂ : ∀ i, ∃ e : (N.obj i).obj₂ ⟶ T₀.obj₂, (φ i).hom₂ ≫ e = 𝟙 _)
    (V : H) (i : I) (g : V ⟶ (N.obj i).obj₃) :
    ∃ (k : I) (τ : i ⟶ k) (h : V ⟶ T₀.obj₃), g ≫ (N.map τ).hom₃ = h ≫ (φ k).hom₃ := by
  obtain ⟨k, τ, h₁, hk⟩ := exists_factorization_shift (N ⋙ Triangle.π₁) T₀.obj₁
    (fun i => (φ i).hom₁) 1 hsurj₁ V i (g ≫ (N.obj i).mor₃)
  have hk' : g ≫ (N.map τ).hom₃ ≫ (N.obj k).mor₃ = h₁ ≫ ((φ k).hom₁)⟦(1 : ℤ)⟧' := by
    have := (N.map τ).comm₃
    calc g ≫ (N.map τ).hom₃ ≫ (N.obj k).mor₃ = (g ≫ (N.obj i).mor₃) ≫ ((N.map τ).hom₁)⟦(1:ℤ)⟧' := by
          rw [Category.assoc, ← this]
      _ = h₁ ≫ ((φ k).hom₁)⟦(1 : ℤ)⟧' := hk
  -- h₁ kills T₀.mor₁⟦1⟧
  obtain ⟨e₂, he₂⟩ := hsplit₂ k
  have hzero : h₁ ≫ (T₀.mor₁)⟦(1 : ℤ)⟧' = 0 := by
    have step : (h₁ ≫ (T₀.mor₁)⟦(1 : ℤ)⟧') ≫ ((φ k).hom₂)⟦(1 : ℤ)⟧' = 0 := by
      calc (h₁ ≫ (T₀.mor₁)⟦(1 : ℤ)⟧') ≫ ((φ k).hom₂)⟦(1 : ℤ)⟧'
          = h₁ ≫ (T₀.mor₁ ≫ (φ k).hom₂)⟦(1 : ℤ)⟧' := by
            rw [Functor.map_comp]; simp only [Category.assoc]
        _ = h₁ ≫ ((φ k).hom₁ ≫ (N.obj k).mor₁)⟦(1 : ℤ)⟧' := by rw [(φ k).comm₁]
        _ = (h₁ ≫ ((φ k).hom₁)⟦(1 : ℤ)⟧') ≫ ((N.obj k).mor₁)⟦(1 : ℤ)⟧' := by
            rw [Functor.map_comp]; simp only [Category.assoc]
        _ = g ≫ (N.map τ).hom₃ ≫ (N.obj k).mor₃ ≫ ((N.obj k).mor₁)⟦(1 : ℤ)⟧' := by
            rw [← hk']; simp only [Category.assoc]
        _ = 0 := by rw [comp_distTriang_mor_zero₃₁ _ (hN k), comp_zero, comp_zero]
    exact eq_of_comp_eq_of_split (shift_comp_eq_id he₂ 1) (by rw [step, zero_comp])
  obtain ⟨h, hh⟩ := Triangle.coyoneda_exact₁ _ hT₀ h₁ hzero
  have hδ3 : (g ≫ (N.map τ).hom₃ - h ≫ (φ k).hom₃) ≫ (N.obj k).mor₃ = 0 := by
    rw [Preadditive.sub_comp, Category.assoc, Category.assoc, ← (φ k).comm₃,
      show g ≫ (N.map τ).hom₃ ≫ (N.obj k).mor₃ = h₁ ≫ ((φ k).hom₁)⟦(1 : ℤ)⟧' from hk', hh]
    simp only [Category.assoc, sub_self]
  obtain ⟨ee, hee⟩ := Triangle.coyoneda_exact₃ _ (hN k) _ hδ3
  obtain ⟨l, τ', h₂, hl⟩ := hsurj₂ V k ee
  refine ⟨l, τ ≫ τ', h + h₂ ≫ T₀.mor₂, ?_⟩
  have hnat₃ : (φ k).hom₃ ≫ (N.map τ').hom₃ = (φ l).hom₃ :=
    congrArg TriangleMorphism.hom₃ (hφ τ')
  have hδ' : (g ≫ (N.map τ).hom₃ - h ≫ (φ k).hom₃) ≫ (N.map τ').hom₃
      = (h₂ ≫ T₀.mor₂) ≫ (φ l).hom₃ := by
    calc (g ≫ (N.map τ).hom₃ - h ≫ (φ k).hom₃) ≫ (N.map τ').hom₃
        = ee ≫ (N.obj k).mor₂ ≫ (N.map τ').hom₃ := by rw [hee]; simp only [Category.assoc]
      _ = ee ≫ (N.map τ').hom₂ ≫ (N.obj l).mor₂ := by rw [(N.map τ').comm₂]
      _ = (ee ≫ (N.map τ').hom₂) ≫ (N.obj l).mor₂ := (Category.assoc _ _ _).symm
      _ = (h₂ ≫ (φ l).hom₂) ≫ (N.obj l).mor₂ := by rw [hl]
      _ = h₂ ≫ T₀.mor₂ ≫ (φ l).hom₃ := by rw [Category.assoc, (φ l).comm₂]
      _ = (h₂ ≫ T₀.mor₂) ≫ (φ l).hom₃ := (Category.assoc _ _ _).symm
  have hmap : (N.map (τ ≫ τ')).hom₃ = (N.map τ).hom₃ ≫ (N.map τ').hom₃ :=
    congrArg TriangleMorphism.hom₃ (N.map_comp τ τ')
  have expand : g ≫ (N.map (τ ≫ τ')).hom₃
      = (g ≫ (N.map τ).hom₃ - h ≫ (φ k).hom₃) ≫ (N.map τ').hom₃
        + (h ≫ (φ k).hom₃) ≫ (N.map τ').hom₃ := by
    rw [hmap, Preadditive.sub_comp]
    simp only [Category.assoc]
    abel
  rw [expand, hδ']
  simp only [Category.assoc]
  rw [hnat₃, Preadditive.add_comp]
  simp only [Category.assoc]
  abel

/-- **The five lemma at the third vertex, injectivity half.** With the data of
`exists_factorization_hom₃` — a diagram `N` of distinguished triangles, a distinguished `T₀` and a
compatible family of morphisms of triangles `φ i : T₀ ⟶ N i` — if every morphism `V ⟶ N(i).obj₁`
factors through some `φ(k).hom₁` after a transition, and `φ(i).hom₁` and `φ(i).hom₂` are split
monomorphisms, then `φ(i).hom₃` is a monomorphism on the nose: two morphisms `V ⟶ T₀.obj₃` that
agree after it are equal. Together with `exists_factorization_hom₃` this is the bijectivity of
`Mor(V, T₀.obj₃) ⟶ colim_i Mor(V, N(i).obj₃)` that the criterion of Tag 05PY(4) consumes.

*Argument (the source's chase, on `δ = h - h'`).* `δ ≫ T₀.mor₃` dies against the split
monomorphism `φ(i).hom₁⟦1⟧`, hence vanishes, so `δ = e ≫ T₀.mor₂` by exactness of `Mor(V, -)` on
`T₀`. Then `e ≫ φ(i).hom₂` dies against `N(i).mor₂`, so it is `y ≫ N(i).mor₁` by exactness on
`N(i)`; factoring `y` at the first vertex and using the two commuting squares exhibits
`e ≫ φ(k).hom₂` as `(z ≫ T₀.mor₁) ≫ φ(k).hom₂`, whence `e = z ≫ T₀.mor₁` because `φ(k).hom₂` is
split mono, and `δ = z ≫ T₀.mor₁ ≫ T₀.mor₂ = 0`. -/
private lemma eq_of_comp_hom₃ {I : Type*} [Category I] (N : I ⥤ Triangle H)
    (hN : ∀ i, N.obj i ∈ distTriang H) {T₀ : Triangle H} (hT₀ : T₀ ∈ distTriang H)
    (φ : ∀ i, T₀ ⟶ N.obj i) (hφ : ∀ {i j : I} (τ : i ⟶ j), φ i ≫ N.map τ = φ j)
    (hsurj₁ : ∀ (V : H) (i : I) (g : V ⟶ (N.obj i).obj₁),
      ∃ (k : I) (τ : i ⟶ k) (h : V ⟶ T₀.obj₁), g ≫ (N.map τ).hom₁ = h ≫ (φ k).hom₁)
    (hsplit₁ : ∀ i, ∃ e : (N.obj i).obj₁ ⟶ T₀.obj₁, (φ i).hom₁ ≫ e = 𝟙 _)
    (hsplit₂ : ∀ i, ∃ e : (N.obj i).obj₂ ⟶ T₀.obj₂, (φ i).hom₂ ≫ e = 𝟙 _)
    {V : H} {i : I} (h h' : V ⟶ T₀.obj₃) (hh : h ≫ (φ i).hom₃ = h' ≫ (φ i).hom₃) : h = h' := by
  have hδ0 : (h - h') ≫ (φ i).hom₃ = 0 := by
    rw [Preadditive.sub_comp, hh, sub_self]
  have h1 : (h - h') ≫ T₀.mor₃ = 0 := by
    obtain ⟨e₁, he₁⟩ := hsplit₁ i
    have step : ((h - h') ≫ T₀.mor₃) ≫ ((φ i).hom₁)⟦(1 : ℤ)⟧' = 0 := by
      rw [Category.assoc, (φ i).comm₃, ← Category.assoc, hδ0, zero_comp]
    exact eq_of_comp_eq_of_split (shift_comp_eq_id he₁ 1) (by rw [step, zero_comp])
  obtain ⟨e, he⟩ := Triangle.coyoneda_exact₃ _ hT₀ _ h1
  have h3 : (e ≫ (φ i).hom₂) ≫ (N.obj i).mor₂ = 0 := by
    rw [Category.assoc, ← (φ i).comm₂, ← Category.assoc, ← he, hδ0]
  obtain ⟨y, hy⟩ := Triangle.coyoneda_exact₂ _ (hN i) _ h3
  obtain ⟨k, τ, z, hz⟩ := hsurj₁ V i y
  obtain ⟨e₂, he₂⟩ := hsplit₂ k
  have hnat₂ : (φ i).hom₂ ≫ (N.map τ).hom₂ = (φ k).hom₂ :=
    congrArg TriangleMorphism.hom₂ (hφ τ)
  have key : e ≫ (φ k).hom₂ = (z ≫ T₀.mor₁) ≫ (φ k).hom₂ := by
    calc e ≫ (φ k).hom₂ = (e ≫ (φ i).hom₂) ≫ (N.map τ).hom₂ := by
          rw [← hnat₂, Category.assoc]
      _ = (y ≫ (N.obj i).mor₁) ≫ (N.map τ).hom₂ := by rw [hy]
      _ = y ≫ (N.map τ).hom₁ ≫ (N.obj k).mor₁ := by rw [Category.assoc, (N.map τ).comm₁]
      _ = (y ≫ (N.map τ).hom₁) ≫ (N.obj k).mor₁ := (Category.assoc _ _ _).symm
      _ = (z ≫ (φ k).hom₁) ≫ (N.obj k).mor₁ := by rw [hz]
      _ = z ≫ T₀.mor₁ ≫ (φ k).hom₂ := by rw [Category.assoc, (φ k).comm₁]
      _ = (z ≫ T₀.mor₁) ≫ (φ k).hom₂ := (Category.assoc _ _ _).symm
  have h5 : e = z ≫ T₀.mor₁ := by
    exact eq_of_comp_eq_of_split he₂ key
  rw [← sub_eq_zero, he, h5, Category.assoc, comp_distTriang_mor_zero₁₂ _ hT₀, comp_zero]

/-- **The index category `ℐ` of Tag 05R9** attached to a distinguished triangle `T'`: the
morphisms of triangles out of `T'` whose target is distinguished and whose three components lie
in `W`. -/
private def triangleIndex (W : MorphismProperty C) (T' : Triangle C) :
    ObjectProperty (Under T') :=
  fun A => A.right ∈ distTriang C ∧ W A.hom.hom₁ ∧ W A.hom.hom₂ ∧ W A.hom.hom₃

/-- The first component functor `ℐ ⥤ T'.obj₁/W` of Tag 05R9, `(s, s', s'') ↦ s`. -/
private noncomputable def triangleIndexπ₁ (W : MorphismProperty C) (T' : Triangle C) :
    (triangleIndex W T').FullSubcategory ⥤ W.Under ⊤ T'.obj₁ :=
  MorphismProperty.Comma.lift ((triangleIndex W T').ι ⋙ Under.post Triangle.π₁)
    (fun A => A.2.2.1) (fun _ => trivial) (fun _ => trivial)

/-- The second component functor `ℐ ⥤ T'.obj₂/W` of Tag 05R9, `(s, s', s'') ↦ s'`. -/
private noncomputable def triangleIndexπ₂ (W : MorphismProperty C) (T' : Triangle C) :
    (triangleIndex W T').FullSubcategory ⥤ W.Under ⊤ T'.obj₂ :=
  MorphismProperty.Comma.lift ((triangleIndex W T').ι ⋙ Under.post Triangle.π₂)
    (fun A => A.2.2.2.1) (fun _ => trivial) (fun _ => trivial)

/-- The third component functor `ℐ ⥤ T'.obj₃/W` of Tag 05R9, `(s, s', s'') ↦ s''`. -/
private noncomputable def triangleIndexπ₃ (W : MorphismProperty C) (T' : Triangle C) :
    (triangleIndex W T').FullSubcategory ⥤ W.Under ⊤ T'.obj₃ :=
  MorphismProperty.Comma.lift ((triangleIndex W T').ι ⋙ Under.post Triangle.π₃)
    (fun A => A.2.2.2.2) (fun _ => trivial) (fun _ => trivial)

/-- The diagram of distinguished triangles `ℐ ⥤ Triangle H`, `(s, s', s'') ↦ F(T'')`, over which
the source's five-lemma comparison runs. -/
private noncomputable def triangleIndexDiagram (F : C ⥤ H) [F.CommShift ℤ]
    (W : MorphismProperty C) (T' : Triangle C) :
    (triangleIndex W T').FullSubcategory ⥤ Triangle H :=
  (triangleIndex W T').ι ⋙ Under.forget T' ⋙ F.mapTriangle

/-- The base object of `ℐ`: the identity morphism of `T'`. -/
private def triangleIndexBase (W : MorphismProperty C) [W.ContainsIdentities] {T' : Triangle C}
    (hT' : T' ∈ distTriang C) : (triangleIndex W T').FullSubcategory :=
  ⟨Under.mk (𝟙 T'), hT', W.id_mem _, W.id_mem _, W.id_mem _⟩

/-- The base object of `ℐ` is initial: a morphism out of it is its target's structure morphism.
This is what makes the retractions `α`, `β`, `γ` of the source's proof retractions *at the base
index*, and the comparison morphisms `φ i` factor through `φ` at the base. -/
private lemma triangleIndex_hom_from_base {W : MorphismProperty C} [W.ContainsIdentities]
    {T' : Triangle C} (hT' : T' ∈ distTriang C) {k : (triangleIndex W T').FullSubcategory}
    (σ : triangleIndexBase W hT' ⟶ k) :
    ((triangleIndex W T').ι.map σ).right = k.1.hom :=
  (Category.id_comp _).symm.trans (Under.w ((triangleIndex W T').ι.map σ))

/-- The morphism of `ℐ` out of the base object with target `k`: the object `k` *is* a `W`-morphism
of distinguished triangles `T' ⟶ k.right`, and as such it is a morphism `𝟙 T' ⟶ k` under `T'`.
With `triangleIndex_hom_from_base`, which says that it is the only one, this is the initiality of
the base object. -/
private def triangleIndexFromBase (W : MorphismProperty C) [W.ContainsIdentities]
    {T' : Triangle C} (hT' : T' ∈ distTriang C) (k : (triangleIndex W T').FullSubcategory) :
    triangleIndexBase W hT' ⟶ k :=
  ObjectProperty.homMk (Under.homMk k.1.hom (Category.id_comp _))

/-- **The source's proof of Tag 05SC over the index category `ℐ`.** Let `T'` be a distinguished
triangle of `C`, let `(A, B, Z₀, u, b, a)` be a distinguished triangle of `H` and let
`φ₀ : (A, B, Z₀, u, b, a) ⟶ F(T')` be a morphism of triangles — the output of TR3 in the source's
proof. If the ind-object at `T'.obj₁` is essentially constant with value `A` and retraction
`φ₀.hom₁` at the identity index, and likewise at `T'.obj₂` with value `B` and retraction
`φ₀.hom₂`, then the ind-object at `T'.obj₃` is essentially constant with value `Z₀` and
retraction `φ₀.hom₃` at the identity index.

*Argument (the source's).* Over `ℐ` (Tag 05R9: filtered, and cofinal over each of the three
`T'.objₘ/W`) the base object is the identity of `T'`, so it is initial and the comparison
morphisms `φ i` are `φ₀` followed by the transition. The values at `T'.obj₁` and `T'.obj₂`
restrict to `ℐ` by cofinality (`isEssentiallyConstantWith_comp_final`), which is the surjectivity
of the comparison maps of Tag 05PY(4) at the first two vertices, and their retractions are the
splittings of `φ(i).hom₁` and `φ(i).hom₂`. The five lemma at the third vertex
(`exists_factorization_hom₃`, `eq_of_comp_hom₃`) then gives the bijectivity of the comparison map
at `Z₀`, Tag 05PY(4) in the form `exists_isEssentiallyConstantWith_of_hom_factorization` turns it
into essential constancy over `ℐ`, and cofinality of `ℐ ⟶ T'.obj₃/W`
(`isEssentiallyConstantWith_of_comp_final`) brings it back to `T'.obj₃/W`. -/
private theorem exists_isEssentiallyConstantWith_obj₃ (F : C ⥤ H) [F.CommShift ℤ]
    [F.IsTriangulated] (W : MorphismProperty C) (hW : W.IsSaturated) [W.ContainsIdentities]
    [W.IsCompatibleWithTriangulation] {T' : Triangle C} (hT' : T' ∈ distTriang C)
    {A B Z₀ : H} {u : A ⟶ B} {b : B ⟶ Z₀} {a : Z₀ ⟶ A⟦(1 : ℤ)⟧}
    (hZ : Triangle.mk u b a ∈ distTriang H)
    (φ₀ : Triangle.mk u b a ⟶ F.mapTriangle.obj T')
    {ιx : indDiagram F W T'.obj₁ ⟶ (Functor.const _).obj A}
    (hx : EssentiallyConstantInd.IsEssentiallyConstantWith (indDiagram F W T'.obj₁)
      (Cocone.mk A ιx) (idIndex W T'.obj₁) φ₀.hom₁)
    {ιy : indDiagram F W T'.obj₂ ⟶ (Functor.const _).obj B}
    (hy : EssentiallyConstantInd.IsEssentiallyConstantWith (indDiagram F W T'.obj₂)
      (Cocone.mk B ιy) (idIndex W T'.obj₂) φ₀.hom₂) :
    ∃ ι₃ : indDiagram F W T'.obj₃ ⟶ (Functor.const _).obj Z₀,
      EssentiallyConstantInd.IsEssentiallyConstantWith (indDiagram F W T'.obj₃)
        (Cocone.mk Z₀ ι₃) (idIndex W T'.obj₃) φ₀.hom₃ := by
  have := hW.isMultiplicative
  have := hW.hasLeftCalculusOfFractions
  obtain ⟨hfilt, hf₁, hf₂, hf₃⟩ := hW.isFiltered_and_final_component hT' (triangleIndex W T')
    (fun _ => Iff.rfl)
  have hfin₁ : (triangleIndexπ₁ W T').Final := hf₁
  have hfin₂ : (triangleIndexπ₂ W T').Final := hf₂
  have hfin₃ : (triangleIndexπ₃ W T').Final := hf₃
  have hfx : IsFiltered (W.Under ⊤ T'.obj₁) := W.isFiltered_under_of_hasLeftCalculusOfFractions _
  have hfy : IsFiltered (W.Under ⊤ T'.obj₂) := W.isFiltered_under_of_hasLeftCalculusOfFractions _
  -- the diagram of triangles and the comparison morphisms out of the base object
  have hNdist : ∀ i, (triangleIndexDiagram F W T').obj i ∈ distTriang H :=
    fun i => F.map_distinguished _ i.2.1
  have hφ : ∀ {i j : (triangleIndex W T').FullSubcategory} (τ : i ⟶ j),
      (φ₀ ≫ F.mapTriangle.map i.1.hom) ≫ (triangleIndexDiagram F W T').map τ =
        φ₀ ≫ F.mapTriangle.map j.1.hom := by
    intro i j τ
    have hw : i.1.hom ≫ ((triangleIndex W T').ι.map τ).right = j.1.hom :=
      Under.w ((triangleIndex W T').ι.map τ)
    show (φ₀ ≫ F.mapTriangle.map i.1.hom) ≫
        F.mapTriangle.map (((triangleIndex W T').ι.map τ).right) = _
    rw [Category.assoc, ← F.mapTriangle.map_comp, hw]
  -- the restriction of the two values to `ℐ`, and the comparison family out of the base object:
  -- it is the retraction of the value followed by the transition maps, by initiality of the base
  have hxI : EssentiallyConstantInd.IsEssentiallyConstantWith
      (triangleIndexπ₁ W T' ⋙ indDiagram F W T'.obj₁)
      ((Cocone.mk A ιx).whisker (triangleIndexπ₁ W T')) (triangleIndexBase W hT') φ₀.hom₁ :=
    isEssentiallyConstantWith_comp_final hx (triangleIndexπ₁ W T') (𝟙 _)
      ((congrArg (fun z => φ₀.hom₁ ≫ z) ((indDiagram F W T'.obj₁).map_id _)).trans
        (Category.comp_id _))
  have hyI : EssentiallyConstantInd.IsEssentiallyConstantWith
      (triangleIndexπ₂ W T' ⋙ indDiagram F W T'.obj₂)
      ((Cocone.mk B ιy).whisker (triangleIndexπ₂ W T')) (triangleIndexBase W hT') φ₀.hom₂ :=
    isEssentiallyConstantWith_comp_final hy (triangleIndexπ₂ W T') (𝟙 _)
      ((congrArg (fun z => φ₀.hom₂ ≫ z) ((indDiagram F W T'.obj₂).map_id _)).trans
        (Category.comp_id _))
  have hψ₁ : ∀ {k : (triangleIndex W T').FullSubcategory} (σ : triangleIndexBase W hT' ⟶ k),
      φ₀.hom₁ ≫ (triangleIndexπ₁ W T' ⋙ indDiagram F W T'.obj₁).map σ =
        (φ₀ ≫ F.mapTriangle.map k.1.hom).hom₁ := fun {k} σ =>
    congrArg (fun z : T' ⟶ k.1.right => φ₀.hom₁ ≫ F.map z.hom₁)
      (triangleIndex_hom_from_base hT' σ)
  have hψ₂ : ∀ {k : (triangleIndex W T').FullSubcategory} (σ : triangleIndexBase W hT' ⟶ k),
      φ₀.hom₂ ≫ (triangleIndexπ₂ W T' ⋙ indDiagram F W T'.obj₂).map σ =
        (φ₀ ≫ F.mapTriangle.map k.1.hom).hom₂ := fun {k} σ =>
    congrArg (fun z : T' ⟶ k.1.right => φ₀.hom₂ ≫ F.map z.hom₂)
      (triangleIndex_hom_from_base hT' σ)
  -- the factorization property and the splitting at the first two vertices
  have hsurj₁ : ∀ (V : H) (i : (triangleIndex W T').FullSubcategory)
      (g : V ⟶ ((triangleIndexDiagram F W T').obj i).obj₁),
      ∃ (k : (triangleIndex W T').FullSubcategory) (τ : i ⟶ k) (h : V ⟶ A),
        g ≫ ((triangleIndexDiagram F W T').map τ).hom₁ =
          h ≫ (φ₀ ≫ F.mapTriangle.map k.1.hom).hom₁ :=
    fun _ i g => exists_factorization_of_pinned hxI
      (fun k => (φ₀ ≫ F.mapTriangle.map k.1.hom).hom₁) hψ₁ i g
  have hsurj₂ : ∀ (V : H) (i : (triangleIndex W T').FullSubcategory)
      (g : V ⟶ ((triangleIndexDiagram F W T').obj i).obj₂),
      ∃ (k : (triangleIndex W T').FullSubcategory) (τ : i ⟶ k) (h : V ⟶ B),
        g ≫ ((triangleIndexDiagram F W T').map τ).hom₂ =
          h ≫ (φ₀ ≫ F.mapTriangle.map k.1.hom).hom₂ :=
    fun _ i g => exists_factorization_of_pinned hyI
      (fun k => (φ₀ ≫ F.mapTriangle.map k.1.hom).hom₂) hψ₂ i g
  have hsplit₁ : ∀ i : (triangleIndex W T').FullSubcategory,
      ∃ e : ((triangleIndexDiagram F W T').obj i).obj₁ ⟶ A,
        (φ₀ ≫ F.mapTriangle.map i.1.hom).hom₁ ≫ e = 𝟙 A := fun i =>
    ⟨ιx.app ((triangleIndexπ₁ W T').obj i), by
      rw [← hψ₁ (triangleIndexFromBase W hT' i)]
      exact comp_map_comp_ι_app hxI (triangleIndexFromBase W hT' i)⟩
  have hsplit₂ : ∀ i : (triangleIndex W T').FullSubcategory,
      ∃ e : ((triangleIndexDiagram F W T').obj i).obj₂ ⟶ B,
        (φ₀ ≫ F.mapTriangle.map i.1.hom).hom₂ ≫ e = 𝟙 B := fun i =>
    ⟨ιy.app ((triangleIndexπ₂ W T').obj i), by
      rw [← hψ₂ (triangleIndexFromBase W hT' i)]
      exact comp_map_comp_ι_app hyI (triangleIndexFromBase W hT' i)⟩
  -- the five lemma at the third vertex
  have hsurj₃ : ∀ (V : H) (i : (triangleIndex W T').FullSubcategory)
      (g : V ⟶ ((triangleIndexDiagram F W T').obj i).obj₃),
      ∃ (k : (triangleIndex W T').FullSubcategory) (τ : i ⟶ k) (h : V ⟶ Z₀),
        g ≫ ((triangleIndexDiagram F W T').map τ).hom₃ =
          h ≫ (φ₀ ≫ F.mapTriangle.map k.1.hom).hom₃ :=
    exists_factorization_hom₃ (triangleIndexDiagram F W T') hNdist hZ
      (fun i => φ₀ ≫ F.mapTriangle.map i.1.hom) hφ hsurj₁ hsurj₂ hsplit₂
  have hinj₃ : ∀ (V : H) (i : (triangleIndex W T').FullSubcategory) (h h' : V ⟶ Z₀),
      h ≫ (φ₀ ≫ F.mapTriangle.map i.1.hom).hom₃ =
          h' ≫ (φ₀ ≫ F.mapTriangle.map i.1.hom).hom₃ → h = h' :=
    fun V i h h' hh => eq_of_comp_hom₃ (triangleIndexDiagram F W T') hNdist hZ
      (fun i => φ₀ ≫ F.mapTriangle.map i.1.hom) hφ hsurj₁ hsplit₁ hsplit₂ (i := i) h h' hh
  -- Tag 05PY(4) over `ℐ`
  have hs : ∀ {k : (triangleIndex W T').FullSubcategory} (ψ : triangleIndexBase W hT' ⟶ k),
      (triangleIndexπ₃ W T' ⋙ indDiagram F W T'.obj₃).map ψ = F.map k.1.hom.hom₃ :=
    fun ψ => congrArg (fun z : T' ⟶ _ => F.map z.hom₃) (triangleIndex_hom_from_base hT' ψ)
  have hfac : ∀ (V : H) (j : (triangleIndex W T').FullSubcategory)
      (g : V ⟶ (triangleIndexπ₃ W T' ⋙ indDiagram F W T'.obj₃).obj j),
      ∃ (k : (triangleIndex W T').FullSubcategory) (σ : triangleIndexBase W hT' ⟶ k) (τ : j ⟶ k)
        (h : V ⟶ Z₀), g ≫ (triangleIndexπ₃ W T' ⋙ indDiagram F W T'.obj₃).map τ =
          h ≫ φ₀.hom₃ ≫ (triangleIndexπ₃ W T' ⋙ indDiagram F W T'.obj₃).map σ := by
    intro V j g
    obtain ⟨k, τ, h, hk⟩ := hsurj₃ V j g
    exact ⟨k, triangleIndexFromBase W hT' k, τ, h, hk⟩
  have hinj : ∀ (V : H) (h h' : V ⟶ Z₀) (k : (triangleIndex W T').FullSubcategory)
      (σ σ' : triangleIndexBase W hT' ⟶ k),
      h ≫ φ₀.hom₃ ≫ (triangleIndexπ₃ W T' ⋙ indDiagram F W T'.obj₃).map σ =
          h' ≫ φ₀.hom₃ ≫ (triangleIndexπ₃ W T' ⋙ indDiagram F W T'.obj₃).map σ' → h = h' := by
    intro V h h' k σ σ' hh
    refine hinj₃ V k h h' ?_
    rw [hs σ] at hh
    rw [hs σ'] at hh
    exact hh
  obtain ⟨ι, hι⟩ := exists_isEssentiallyConstantWith_of_hom_factorization
    (triangleIndexπ₃ W T' ⋙ indDiagram F W T'.obj₃) (i₀ := triangleIndexBase W hT')
    (X := Z₀) φ₀.hom₃ hfac hinj
  exact ⟨_, isEssentiallyConstantWith_of_comp_final (indDiagram F W T'.obj₃)
    (triangleIndexπ₃ W T') hι⟩

/-- **The claim in the source's proof of Tag 05SC**, from the chosen indices on. The data
`sx`, `sy`, `α`, `β`, `f'` is the output of `exists_compatible_retraction_square`: indices
`s : X ⟶ X'`, `t : Y ⟶ Y'` of `X/W` and `Y/W`, sections `α`, `β` of the coprojections there, and
a morphism `f' : X' ⟶ Y'` filling the square under `f` for which `α ≫ F(f') = u ≫ β` commutes.
Given it, `Z₀` is a value of `RF` at the third vertex, `b` and `a` being the morphisms `RF(g)`
and `RF(h)` of Tag 05SA for that value.

The source's argument from here: complete `(s, t)` to a morphism of distinguished triangles
`(s, t, s'') : T ⟶ T'` with `s'' ∈ W` by MS6, and `(α, β)` to a morphism of triangles
`(α, β, γ) : (A, B, Z₀, u, b, a) ⟶ F(T')` by TR3, `F(T')` being distinguished because `F` is
exact. Over the category `ℐ` of `W`-morphisms of distinguished triangles out of `T'` — filtered,
and cofinal over each of `X'/W`, `Y'/W`, `Z'/W` by Tag 05R9 — the comparison maps
`Mor(V, A) ⟶ colim Mor(V, F(X''))` and `Mor(V, B) ⟶ colim Mor(V, F(Y''))` and their shifts are
bijective, filtered colimits of the Hom-sequences of the triangles `F(T'')` are exact, and the
five lemma makes `Mor(V, Z₀) ⟶ colim Mor(V, F(Z''))` bijective; Tag 05PY(4), in the colimit-free
form `exists_isEssentiallyConstantWith_of_hom_factorization`, then exhibits `F(Z'')` as
essentially constant over `ℐ` with value `Z₀`, and cofinality of `ℐ ⟶ Z'/W` followed by Tag 05SB
along `s'' : Z ⟶ Z'` brings that back to `Z/W`. -/
private theorem isRightDerivedValueAt_obj₃_of_dist_aux (F : C ⥤ H) [F.CommShift ℤ]
    [F.IsTriangulated] (W : MorphismProperty C) (hW : W.IsSaturated)
    [W.IsCompatibleWithTriangulation] (T : Triangle C) (hT : T ∈ distTriang C)
    {c : Cocone (indDiagram F W T.obj₁)} (hc : F.IsRightDerivedValueAt W T.obj₁ c)
    {d : Cocone (indDiagram F W T.obj₂)} (hd : F.IsRightDerivedValueAt W T.obj₂ d)
    (u : c.pt ⟶ d.pt)
    {Z₀ : H} (b : d.pt ⟶ Z₀) (a : Z₀ ⟶ c.pt⟦(1 : ℤ)⟧)
    (hZ : Triangle.mk u b a ∈ distTriang H)
    (sx : W.Under ⊤ T.obj₁) (sy : W.Under ⊤ T.obj₂) (α : c.pt ⟶ F.obj sx.right)
    (β : d.pt ⟶ F.obj sy.right) (f' : sx.right ⟶ sy.right)
    (hα : α ≫ c.ι.app sx = 𝟙 c.pt) (hβ : β ≫ d.ι.app sy = 𝟙 d.pt)
    (hsq : T.mor₁ ≫ sy.hom = sx.hom ≫ f') (hcomm : α ≫ F.map f' = u ≫ β) :
    ∃ ι₃ : indDiagram F W T.obj₃ ⟶ (Functor.const (W.Under ⊤ T.obj₃)).obj Z₀,
      F.IsRightDerivedValueAt W T.obj₃ (Cocone.mk Z₀ ι₃) ∧
      (∀ (t : W.Under ⊤ T.obj₂) (r : W.Under ⊤ T.obj₃) (g' : t.right ⟶ r.right),
        T.mor₂ ≫ r.hom = t.hom ≫ g' → d.ι.app t ≫ b = F.map g' ≫ ι₃.app r) ∧
      ∀ (r : W.Under ⊤ T.obj₃) (s : W.Under ⊤ T.obj₁) (h' : r.right ⟶ s.right⟦(1 : ℤ)⟧),
        T.mor₃ ≫ s.hom⟦(1 : ℤ)⟧' = r.hom ≫ h' →
          ι₃.app r ≫ a = F.map h' ≫ (F.commShiftIso (1 : ℤ)).hom.app s.right ≫
            (c.ι.app s)⟦(1 : ℤ)⟧'
    := by
  have := hW.hasLeftCalculusOfFractions
  have := hW.isMultiplicative
  have := respectsIso_of_isSaturated hW
  -- MS6: complete the chosen square to a morphism of distinguished triangles `T ⟶ T'`
  obtain ⟨Z', g₃, h₃, hT'⟩ := distinguished_cocone_triangle f'
  obtain ⟨sz, hsz, hsz₂, hsz₃⟩ := MorphismProperty.compatible_with_triangulation (W := W)
    T (Triangle.mk f' g₃ h₃) hT hT' sx.hom sy.hom sx.prop sy.prop hsq
  -- TR3: complete `(α, β)` to a morphism of triangles into the distinguished triangle `F(T')`
  obtain ⟨γ, hγ₂, hγ₃⟩ := complete_distinguished_triangle_morphism (Triangle.mk u b a)
    (F.mapTriangle.obj (Triangle.mk f' g₃ h₃)) hZ (F.map_distinguished _ hT') α β hcomm.symm
  -- the values at `X'` and at `Y'`, with `α` and `β` as retractions at the identity indices
  obtain ⟨ιx, hx⟩ := exists_isEssentiallyConstantWith_at_index F W hc sx α hα
  obtain ⟨ιy, hy⟩ := exists_isEssentiallyConstantWith_at_index F W hd sy β hβ
  -- the source's argument over the index category of Tag 05R9: a value at `Z'`, retraction `γ`
  obtain ⟨ι', hι'⟩ := exists_isEssentiallyConstantWith_obj₃ F W hW hT' hZ
    ({ hom₁ := α, hom₂ := β, hom₃ := γ, comm₁ := hcomm.symm, comm₂ := hγ₂, comm₃ := hγ₃ } :
      Triangle.mk u b a ⟶ F.mapTriangle.obj (Triangle.mk f' g₃ h₃)) hx hy
  -- Tag 05SB along `sz : Z ⟶ Z'` brings that value back to `Z`
  obtain ⟨ι₃, hι₃, hι₃sq⟩ := exists_isRightDerivedValueAt_of_mem F W hsz
    (isRightDerivedValueAt_of_isEssentiallyConstantWith F W hι')
  -- `γ` splits the coprojection of the value at `Z` at the index `sz`
  have hγι : γ ≫ ι₃.app (MorphismProperty.Under.mk ⊤ sz hsz) = 𝟙 Z₀ :=
    (congrArg (fun z => γ ≫ z)
      ((hι₃sq (MorphismProperty.Under.mk ⊤ sz hsz) (idIndex W Z') (𝟙 Z') rfl).trans
        ((congrArg (fun z => z ≫ ι'.app (idIndex W Z')) (F.map_id Z')).trans
          (Category.id_comp _)))).trans hι'.retraction
  refine ⟨ι₃, hι₃, ?_, ?_⟩
  · -- `b` is the morphism `RF(g)` of Tag 05SA for this value
    obtain ⟨v, hv⟩ := exists_map_of_isRightDerivedValueAt F W T.mor₂ hd (Cocone.mk Z₀ ι₃)
    have hbv : b = v := eq_of_split_comp_eq hβ
      (hv sy (MorphismProperty.Under.mk ⊤ sz hsz) g₃ hsz₂) hγ₂ hγι
    intro t r g'' hsq'
    exact (congrArg (fun z => d.ι.app t ≫ z) hbv).trans (hv t r g'' hsq')
  · -- `a` is the morphism `RF(h)` of Tag 05SA for this value
    obtain ⟨c₁, hc₁⟩ := (exists_isRightDerivedValueAt_shift_iff F W T.obj₁ 1).mp ⟨c, hc⟩
    obtain ⟨e, he⟩ := exists_iso_shift_of_isRightDerivedValueAt F W T.obj₁ 1 hc hc₁
    obtain ⟨w, hw⟩ := exists_map_of_isRightDerivedValueAt F W T.mor₃ hι₃ c₁
    have key : ∀ (r : W.Under ⊤ T.obj₃) (s : W.Under ⊤ T.obj₁) (k : r.right ⟶ s.right⟦(1 : ℤ)⟧),
        T.mor₃ ≫ s.hom⟦(1 : ℤ)⟧' = r.hom ≫ k →
          ι₃.app r ≫ w ≫ e.inv = F.map k ≫ (F.commShiftIso (1 : ℤ)).hom.app s.right ≫
            (c.ι.app s)⟦(1 : ℤ)⟧' :=
      fun r s k hk => comp_comp_inv_eq (hw r ((underShift W T.obj₁ 1).obj s) k hk) (he s)
        e.hom_inv_id
    have haw : a = w ≫ e.inv := eq_of_split_comp_eq hγι
      ((key (MorphismProperty.Under.mk ⊤ sz hsz) sx h₃ hsz₃).trans (Category.assoc _ _ _).symm)
      hγ₃ (shift_comp_eq_id hα 1)
    intro r s k hsq'
    exact (congrArg (fun z => ι₃.app r ≫ z) haw).trans (key r s k hsq')

/-- **The claim in the source's proof of Tag 05SC.** Let `T = (X, Y, Z, f, g, h)` be a
distinguished triangle of `C`, let `c` be a value of `RF` at `X`, let `d` be a value of `RF` at
`Y`, let `u : c.pt ⟶ d.pt` be the morphism `RF(f)` of Tag 05SA and let `(c.pt, d.pt, Z₀, u, b, a)`
be a distinguished triangle of `H`. Then `Z₀` is a value of `RF` at `Z`, and `b` and `a` are the
morphisms `RF(g)` and `RF(h)` of Tag 05SA for that value.

This is `isRightDerivedValueAt_obj₃_of_dist_aux` preceded by the choice of indices and sections
of `exists_compatible_retraction_square`. -/
private theorem isRightDerivedValueAt_obj₃_of_dist (F : C ⥤ H) [F.CommShift ℤ]
    [F.IsTriangulated] (W : MorphismProperty C) (hW : W.IsSaturated)
    [W.IsCompatibleWithTriangulation] (T : Triangle C) (hT : T ∈ distTriang C)
    {c : Cocone (indDiagram F W T.obj₁)} (hc : F.IsRightDerivedValueAt W T.obj₁ c)
    {d : Cocone (indDiagram F W T.obj₂)} (hd : F.IsRightDerivedValueAt W T.obj₂ d)
    (u : c.pt ⟶ d.pt)
    (hu : ∀ (s : W.Under ⊤ T.obj₁) (t : W.Under ⊤ T.obj₂) (f' : s.right ⟶ t.right),
      T.mor₁ ≫ t.hom = s.hom ≫ f' → c.ι.app s ≫ u = F.map f' ≫ d.ι.app t)
    {Z₀ : H} (b : d.pt ⟶ Z₀) (a : Z₀ ⟶ c.pt⟦(1 : ℤ)⟧)
    (hZ : Triangle.mk u b a ∈ distTriang H) :
    ∃ ι₃ : indDiagram F W T.obj₃ ⟶ (Functor.const (W.Under ⊤ T.obj₃)).obj Z₀,
      F.IsRightDerivedValueAt W T.obj₃ (Cocone.mk Z₀ ι₃) ∧
      (∀ (t : W.Under ⊤ T.obj₂) (r : W.Under ⊤ T.obj₃) (g' : t.right ⟶ r.right),
        T.mor₂ ≫ r.hom = t.hom ≫ g' → d.ι.app t ≫ b = F.map g' ≫ ι₃.app r) ∧
      ∀ (r : W.Under ⊤ T.obj₃) (s : W.Under ⊤ T.obj₁) (h' : r.right ⟶ s.right⟦(1 : ℤ)⟧),
        T.mor₃ ≫ s.hom⟦(1 : ℤ)⟧' = r.hom ≫ h' →
          ι₃.app r ≫ a = F.map h' ≫ (F.commShiftIso (1 : ℤ)).hom.app s.right ≫
            (c.ι.app s)⟦(1 : ℤ)⟧' := by
  have := hW.hasLeftCalculusOfFractions
  obtain ⟨sx, sy, α, β, f', hα, hβ, hsq, hcomm⟩ :=
    exists_compatible_retraction_square F W T.mor₁ hc hd u hu
  exact isRightDerivedValueAt_obj₃_of_dist_aux F W hW T hT hc hd u b a hZ sx sy α β f'
    hα hβ hsq hcomm

/-- Tag 05SC, the primary case: if `RF` is defined at the first two vertices of a distinguished
triangle, it is defined at the third. -/
private theorem exists_isRightDerivedValueAt_obj₃ (F : C ⥤ H) [F.CommShift ℤ] [F.IsTriangulated]
    (W : MorphismProperty C) (hW : W.IsSaturated) [W.IsCompatibleWithTriangulation]
    (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : ∃ c, F.IsRightDerivedValueAt W T.obj₁ c)
    (h₂ : ∃ c, F.IsRightDerivedValueAt W T.obj₂ c) :
    ∃ c, F.IsRightDerivedValueAt W T.obj₃ c := by
  have := hW.hasLeftCalculusOfFractions
  obtain ⟨c, hc⟩ := h₁
  obtain ⟨d, hd⟩ := h₂
  obtain ⟨u, hu⟩ := exists_map_of_isRightDerivedValueAt F W T.mor₁ hc d
  obtain ⟨Z₀, b, a, hZ⟩ := distinguished_cocone_triangle u
  obtain ⟨ι₃, hι₃, -, -⟩ := isRightDerivedValueAt_obj₃_of_dist F W hW T hT hc hd u hu b a hZ
  exact ⟨_, hι₃⟩

theorem solution_right (F : C ⥤ H) [F.CommShift ℤ] [F.IsTriangulated]
    (W : MorphismProperty C) (hW : W.IsSaturated) [W.IsCompatibleWithTriangulation]
    (T : Triangle C) (hT : T ∈ distTriang C) :
    ((∃ c, F.IsRightDerivedValueAt W T.obj₁ c) → (∃ c, F.IsRightDerivedValueAt W T.obj₂ c) →
        ∃ c, F.IsRightDerivedValueAt W T.obj₃ c) ∧
      ((∃ c, F.IsRightDerivedValueAt W T.obj₂ c) → (∃ c, F.IsRightDerivedValueAt W T.obj₃ c) →
        ∃ c, F.IsRightDerivedValueAt W T.obj₁ c) ∧
      ((∃ c, F.IsRightDerivedValueAt W T.obj₃ c) → (∃ c, F.IsRightDerivedValueAt W T.obj₁ c) →
        ∃ c, F.IsRightDerivedValueAt W T.obj₂ c) ∧
      ∀ (cX : Cocone (MorphismProperty.Under.forget W ⊤ T.obj₁ ⋙ Under.forget T.obj₁ ⋙ F))
        (_ : F.IsRightDerivedValueAt W T.obj₁ cX)
        (cY : Cocone (MorphismProperty.Under.forget W ⊤ T.obj₂ ⋙ Under.forget T.obj₂ ⋙ F))
        (_ : F.IsRightDerivedValueAt W T.obj₂ cY)
        (cZ : Cocone (MorphismProperty.Under.forget W ⊤ T.obj₃ ⋙ Under.forget T.obj₃ ⋙ F))
        (_ : F.IsRightDerivedValueAt W T.obj₃ cZ),
        ∃ (u : cX.pt ⟶ cY.pt) (v : cY.pt ⟶ cZ.pt) (w : cZ.pt ⟶ cX.pt⟦(1 : ℤ)⟧),
          Triangle.mk u v w ∈ distTriang H ∧
          (∀ (s : W.Under ⊤ T.obj₁) (t : W.Under ⊤ T.obj₂) (f' : s.right ⟶ t.right),
            T.mor₁ ≫ t.hom = s.hom ≫ f' → cX.ι.app s ≫ u = F.map f' ≫ cY.ι.app t) ∧
          (∀ (t : W.Under ⊤ T.obj₂) (r : W.Under ⊤ T.obj₃) (g' : t.right ⟶ r.right),
            T.mor₂ ≫ r.hom = t.hom ≫ g' → cY.ι.app t ≫ v = F.map g' ≫ cZ.ι.app r) ∧
          ∀ (r : W.Under ⊤ T.obj₃) (s : W.Under ⊤ T.obj₁) (h' : r.right ⟶ s.right⟦(1 : ℤ)⟧),
            T.mor₃ ≫ s.hom⟦(1 : ℤ)⟧' = r.hom ≫ h' →
              cZ.ι.app r ≫ w =
                F.map h' ≫ (F.commShiftIso (1 : ℤ)).hom.app s.right ≫ (cX.ι.app s)⟦(1 : ℤ)⟧' := by
  have := hW.hasLeftCalculusOfFractions
  have := hW.isMultiplicative
  have := respectsIso_of_isSaturated hW
  refine ⟨fun h₁ h₂ => exists_isRightDerivedValueAt_obj₃ F W hW T hT h₁ h₂, fun h₂ h₃ => ?_,
    fun h₃ h₁ => ?_, ?_⟩
  · exact (exists_isRightDerivedValueAt_shift_iff F W T.obj₁ 1).mpr
      (exists_isRightDerivedValueAt_obj₃ F W hW T.rotate (rot_of_distTriang T hT) h₂ h₃)
  · exact (exists_isRightDerivedValueAt_shift_iff F W T.obj₂ 1).mpr
      (exists_isRightDerivedValueAt_obj₃ F W hW T.rotate.rotate
        (rot_of_distTriang _ (rot_of_distTriang T hT)) h₃
        ((exists_isRightDerivedValueAt_shift_iff F W T.obj₁ 1).mp h₁))
  · intro cX hcX cY hcY cZ hcZ
    obtain ⟨u, hu⟩ := exists_map_of_isRightDerivedValueAt F W T.mor₁ hcX cY
    obtain ⟨Z₀, b, a, hZ⟩ := distinguished_cocone_triangle u
    obtain ⟨ι₃, hι₃, hb, ha⟩ :=
      isRightDerivedValueAt_obj₃_of_dist F W hW T hT hcX hcY u hu b a hZ
    obtain ⟨e, he⟩ := exists_iso_of_isRightDerivedValueAt F W hι₃ hcZ
    have he' : ∀ r, ι₃.app r ≫ e.hom = cZ.ι.app r := he
    refine ⟨u, b ≫ e.hom, e.inv ≫ a, ?_, hu, ?_, ?_⟩
    · exact isomorphic_distinguished _ hZ _
        (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm (by simp) (by simp) (by simp))
    · intro t r g' hsq
      rw [← he' r]
      rw [← Category.assoc]
      exact (congrArg (fun φ => φ ≫ e.hom) (hb t r g' hsq)).trans (Category.assoc _ _ _)
    · intro r s h' hsq
      rw [← he r]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      exact ha r s h' hsq

end Triangulated

end DerivedFunctorValues

end

end
