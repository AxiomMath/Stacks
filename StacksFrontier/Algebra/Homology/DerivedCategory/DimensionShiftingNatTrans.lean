module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor

/-!
# Dimension shifting for a natural transformation of exact functors

Let `η : H₁ ⟶ H₂` be a natural transformation between two exact functors
`D(C) ⥤ D(D)` of derived categories, not assumed compatible with the shift. The proof of
[Stacks, Tag 0F1J] shows that such a map is invertible on a class `𝒞` of objects of `C` by
"dimension shifting, i.e. induction on `q`": every object of `𝒞` embeds into an object at which
`η` is known to be invertible, with cokernel again in `𝒞`, and both sides vanish in low
degrees. This file proves that argument
(`CategoryTheory.NatTrans.isIso_app_shift_singleFunctor_of_exists_shortExact`).

## The proof

For a distinguished triangle `T₁ → T₂ → T₃ → T₁⟦1⟧` the images under `H^q ∘ H₁` and
`H^q ∘ H₂` of `T₂ → T₃ → T₁⟦1⟧ → T₂⟦1⟧` are exact sequences, and `η` maps one to the other by
naturality alone: the connecting morphism is `T₃ → T₁⟦1⟧` itself, not its image under the
shift isomorphisms of the functors. The four lemma
(`CategoryTheory.Abelian.mono_of_epi_of_mono_of_mono'` and
`CategoryTheory.Abelian.epi_of_epi_of_epi_of_mono'`) then gives
`mono_homologyMap_app_obj₁_shift` and `epi_homologyMap_app_obj₁_shift`. Applied to the shifts
of the triangle of a short exact sequence `0 → M → I → Q → 0`, by induction on `q + s` these give
that `H^q(η)` at `M[0]⟦s⟧` is first a monomorphism and then an epimorphism.

## Main results

* `CategoryTheory.NatTrans.mono_homologyMap_app_obj₁_shift`,
  `CategoryTheory.NatTrans.epi_homologyMap_app_obj₁_shift` — the four lemma on a triangle.
* `CategoryTheory.NatTrans.isIso_app_shift_singleFunctor_of_exists_shortExact` — dimension
  shifting.

## References

* [Stacks Project, Tag 0F1J](https://stacks.math.columbia.edu/tag/0F1J)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Pretriangulated DerivedCategory

universe v u v' u'

namespace CategoryTheory.NatTrans

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory D]
  {H₁ H₂ : DerivedCategory C ⥤ DerivedCategory D}
  [H₁.CommShift ℤ] [H₂.CommShift ℤ] [H₁.IsTriangulated] [H₂.IsTriangulated]
  (η : H₁ ⟶ H₂)

section Exactness

/-- `-𝟙` as an isomorphism. -/
def negIdIso {A : Type*} [Category A] [Preadditive A] (X : A) : X ≅ X where
  hom := -𝟙 X
  inv := -𝟙 X
  hom_inv_id := by simp
  inv_hom_id := by simp

variable (H : DerivedCategory C ⥤ DerivedCategory D) [H.CommShift ℤ] [H.IsTriangulated]
  (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _) (q : ℤ)

/-- Exactness of `H^q(H T₂) ⟶ H^q(H T₃) ⟶ H^q(H(T₁⟦1⟧))` for a distinguished triangle `T`. -/
theorem exact_homologyFunctor_map_mor₃ :
    (ShortComplex.mk ((homologyFunctor D q).map (H.map T.mor₃))
      ((homologyFunctor D q).map (H.map (T.mor₁⟦(1 : ℤ)⟧')))
      (by rw [← Functor.map_comp, ← Functor.map_comp, comp_distTriang_mor_zero₃₁ _ hT,
        Functor.map_zero, Functor.map_zero])).Exact := by
  have h := (H ⋙ homologyFunctor D q).map_distinguished_exact _ (rot_of_distTriang _
    (rot_of_distTriang _ hT))
  refine (ShortComplex.exact_iff_of_iso ?_).1 h
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (negIdIso _) ?_ ?_
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · show 𝟙 _ ≫ _ = (homologyFunctor D q).map (H.map (-(T.mor₁⟦(1 : ℤ)⟧'))) ≫ (-𝟙 _)
    rw [H.map_neg, (homologyFunctor D q).map_neg, Preadditive.neg_comp_neg, Category.id_comp,
      Category.comp_id]

/-- Exactness of `H^q(H T₂) ⟶ H^q(H T₃) ⟶ H^q(H(T₁⟦1⟧))` at the middle, from `T.rotate`. -/
theorem exact_homologyFunctor_map_mor₂ :
    (ShortComplex.mk ((homologyFunctor D q).map (H.map T.mor₂))
      ((homologyFunctor D q).map (H.map T.mor₃))
      (by rw [← Functor.map_comp, ← Functor.map_comp, comp_distTriang_mor_zero₂₃ _ hT,
        Functor.map_zero, Functor.map_zero])).Exact :=
  (H ⋙ homologyFunctor D q).map_distinguished_exact _ (rot_of_distTriang _ hT)

/-- Exactness of `H^q(H(T₁⟦1⟧)) ⟶ H^q(H(T₂⟦1⟧)) ⟶ H^q(H(T₃⟦1⟧))`. -/
theorem exact_homologyFunctor_map_mor₁_shift :
    (ShortComplex.mk ((homologyFunctor D q).map (H.map (T.mor₁⟦(1 : ℤ)⟧')))
      ((homologyFunctor D q).map (H.map (T.mor₂⟦(1 : ℤ)⟧')))
      (by rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
        comp_distTriang_mor_zero₁₂ _ hT, Functor.map_zero, Functor.map_zero,
        Functor.map_zero])).Exact := by
  have h := (H ⋙ homologyFunctor D q).map_distinguished_exact _ (rot_of_distTriang _
    (rot_of_distTriang _ (rot_of_distTriang _ hT)))
  refine (ShortComplex.exact_iff_of_iso ?_).1 h
  refine ShortComplex.isoMk (negIdIso _) (Iso.refl _) (negIdIso _) ?_ ?_
  · show (-𝟙 _) ≫ _ = (homologyFunctor D q).map (H.map (-(T.mor₁⟦(1 : ℤ)⟧'))) ≫ 𝟙 _
    rw [H.map_neg, (homologyFunctor D q).map_neg, Preadditive.neg_comp, Category.id_comp,
      Category.comp_id]
  · show 𝟙 _ ≫ _ = (homologyFunctor D q).map (H.map (-(T.mor₂⟦(1 : ℤ)⟧'))) ≫ (-𝟙 _)
    rw [H.map_neg, (homologyFunctor D q).map_neg, Preadditive.neg_comp_neg, Category.id_comp,
      Category.comp_id]

end Exactness

/-- Naturality of `η` after applying `H^q`. -/
private theorem homologyMap_naturality {F₁ F₂ : DerivedCategory C ⥤ DerivedCategory D}
    (η : F₁ ⟶ F₂) (q : ℤ) {X Y : DerivedCategory C} (f : X ⟶ Y) :
    (homologyFunctor D q).map (F₁.map f) ≫ (homologyFunctor D q).map (η.app Y) =
      (homologyFunctor D q).map (η.app X) ≫ (homologyFunctor D q).map (F₂.map f) := by
  rw [← Functor.map_comp, η.naturality, Functor.map_comp]

/-- `H^q(η)` at isomorphic objects differ by conjugation with the isomorphism. -/
private theorem homologyMap_app_eq_of_iso {F₁ F₂ : DerivedCategory C ⥤ DerivedCategory D}
    (η : F₁ ⟶ F₂) (q : ℤ) {X X' : DerivedCategory C} (e : X ≅ X') :
    (homologyFunctor D q).map (η.app X') =
      inv ((homologyFunctor D q).map (F₁.map e.hom)) ≫ (homologyFunctor D q).map (η.app X) ≫
        (homologyFunctor D q).map (F₂.map e.hom) := by
  rw [← homologyMap_naturality η q e.hom, IsIso.inv_hom_id_assoc]

variable (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _) (q : ℤ)

include hT

/-- **The four lemma for `η` on a distinguished triangle, monomorphism form.** If `η` is an
epimorphism on `H^q` at `T₂`, and a monomorphism on `H^q` at `T₃` and at `T₂⟦1⟧`, it is a
monomorphism on `H^q` at `T₁⟦1⟧`. Only the naturality of `η` is used. -/
theorem mono_homologyMap_app_obj₁_shift
    (h₂ : Epi ((homologyFunctor D q).map (η.app T.obj₂)))
    (h₃ : Mono ((homologyFunctor D q).map (η.app T.obj₃)))
    (h₄ : Mono ((homologyFunctor D q).map (η.app (T.obj₂⟦(1 : ℤ)⟧)))) :
    Mono ((homologyFunctor D q).map (η.app (T.obj₁⟦(1 : ℤ)⟧))) := by
  let G := homologyFunctor D q
  let R₁ := ComposableArrows.mk₃ (G.map (H₁.map T.mor₂)) (G.map (H₁.map T.mor₃))
    (G.map (H₁.map (T.mor₁⟦(1 : ℤ)⟧')))
  let R₂ := ComposableArrows.mk₃ (G.map (H₂.map T.mor₂)) (G.map (H₂.map T.mor₃))
    (G.map (H₂.map (T.mor₁⟦(1 : ℤ)⟧')))
  let φ : R₁ ⟶ R₂ := ComposableArrows.homMk₃ (G.map (η.app T.obj₂)) (G.map (η.app T.obj₃))
    (G.map (η.app (T.obj₁⟦(1 : ℤ)⟧))) (G.map (η.app (T.obj₂⟦(1 : ℤ)⟧)))
    (homologyMap_naturality η q _)
    (homologyMap_naturality η q _)
    (homologyMap_naturality η q _)
  exact Abelian.mono_of_epi_of_mono_of_mono' φ
    (by
      show G.map (H₁.map T.mor₂) ≫ G.map (H₁.map T.mor₃) = 0
      rw [← G.map_comp, ← H₁.map_comp, comp_distTriang_mor_zero₂₃ _ hT, H₁.map_zero,
        G.map_zero])
    (exact_homologyFunctor_map_mor₃ H₁ T hT q).exact_toComposableArrows
    (exact_homologyFunctor_map_mor₂ H₂ T hT q).exact_toComposableArrows h₂ h₃ h₄

/-- **The four lemma for `η` on a distinguished triangle, epimorphism form.** If `η` is an
epimorphism on `H^q` at `T₃` and at `T₂⟦1⟧`, and a monomorphism on `H^q` at `T₃⟦1⟧`, it is an
epimorphism on `H^q` at `T₁⟦1⟧`. Only the naturality of `η` is used. -/
theorem epi_homologyMap_app_obj₁_shift
    (h₃ : Epi ((homologyFunctor D q).map (η.app T.obj₃)))
    (h₄ : Epi ((homologyFunctor D q).map (η.app (T.obj₂⟦(1 : ℤ)⟧))))
    (h₅ : Mono ((homologyFunctor D q).map (η.app (T.obj₃⟦(1 : ℤ)⟧)))) :
    Epi ((homologyFunctor D q).map (η.app (T.obj₁⟦(1 : ℤ)⟧))) := by
  let G := homologyFunctor D q
  let R₁ := ComposableArrows.mk₃ (G.map (H₁.map T.mor₃)) (G.map (H₁.map (T.mor₁⟦(1 : ℤ)⟧')))
    (G.map (H₁.map (T.mor₂⟦(1 : ℤ)⟧')))
  let R₂ := ComposableArrows.mk₃ (G.map (H₂.map T.mor₃)) (G.map (H₂.map (T.mor₁⟦(1 : ℤ)⟧')))
    (G.map (H₂.map (T.mor₂⟦(1 : ℤ)⟧')))
  let φ : R₁ ⟶ R₂ := ComposableArrows.homMk₃ (G.map (η.app T.obj₃))
    (G.map (η.app (T.obj₁⟦(1 : ℤ)⟧))) (G.map (η.app (T.obj₂⟦(1 : ℤ)⟧)))
    (G.map (η.app (T.obj₃⟦(1 : ℤ)⟧)))
    (homologyMap_naturality η q _)
    (homologyMap_naturality η q _)
    (homologyMap_naturality η q _)
  exact Abelian.epi_of_epi_of_epi_of_mono' φ
    (exact_homologyFunctor_map_mor₁_shift H₁ T hT q).exact_toComposableArrows
    (exact_homologyFunctor_map_mor₃ H₂ T hT q).exact_toComposableArrows
    (by
      show G.map (H₂.map (T.mor₁⟦(1 : ℤ)⟧')) ≫ G.map (H₂.map (T.mor₂⟦(1 : ℤ)⟧')) = 0
      rw [← G.map_comp, ← H₂.map_comp, ← Functor.map_comp, comp_distTriang_mor_zero₁₂ _ hT,
        Functor.map_zero, H₂.map_zero, G.map_zero])
    h₃ h₄ h₅

omit hT [H₁.CommShift ℤ] [H₂.CommShift ℤ] [H₁.IsTriangulated] [H₂.IsTriangulated] in
/-- Being a monomorphism on `H^q` is a property of the isomorphism class of the object. -/
theorem mono_homologyMap_app_of_iso {X X' : DerivedCategory C} (e : X ≅ X')
    (h : Mono ((homologyFunctor D q).map (η.app X))) :
    Mono ((homologyFunctor D q).map (η.app X')) := by
  rw [homologyMap_app_eq_of_iso η q e]
  infer_instance

omit hT [H₁.CommShift ℤ] [H₂.CommShift ℤ] [H₁.IsTriangulated] [H₂.IsTriangulated] in
/-- Being an epimorphism on `H^q` is a property of the isomorphism class of the object. -/
theorem epi_homologyMap_app_of_iso {X X' : DerivedCategory C} (e : X ≅ X')
    (h : Epi ((homologyFunctor D q).map (η.app X))) :
    Epi ((homologyFunctor D q).map (η.app X')) := by
  rw [homologyMap_app_eq_of_iso η q e]
  infer_instance

end CategoryTheory.NatTrans


namespace CategoryTheory.NatTrans

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory D]
  {H₁ H₂ : DerivedCategory C ⥤ DerivedCategory D}
  [H₁.CommShift ℤ] [H₂.CommShift ℤ] [H₁.IsTriangulated] [H₂.IsTriangulated]
  (η : H₁ ⟶ H₂)

/-- **Dimension shifting for a natural transformation of exact functors out of `D(C)`.** Let
`𝒞` be a class of objects of `C` and `b` an integer such that both functors carry every shift
`M[0]⟦s⟧` of an object `M` of `𝒞` into `D^{≥ b - s}`. Suppose every object of `𝒞` is the
kernel of an epimorphism `I ⟶ Q` with `Q` in `𝒞` and `η` invertible at every shift of `I[0]`.
Then `η` is invertible at every shift of `M[0]`, for every `M` in `𝒞`.

This is the "dimension shifting, i.e. induction on `q`" of the proof of [Stacks, Tag 0F1J]:
by induction on `q + s`, `η` is first a monomorphism on `H^q` at `M[0]⟦s⟧` for all `M` in `𝒞`,
by the four lemma on the triangle `M → I → Q → M[1]` and the invertibility at `Q` one step
down, and then an epimorphism, using in addition that it is a monomorphism at `Q` at the same
step. Below `b - s` both sides vanish. No compatibility of `η` with the shift is used. -/
theorem isIso_app_shift_singleFunctor_of_exists_shortExact (b : ℤ) (𝒞 : C → Prop)
    (hGE₁ : ∀ M, 𝒞 M → ∀ s : ℤ,
      DerivedCategory.IsGE (H₁.obj (((singleFunctor C 0).obj M)⟦s⟧)) (b - s))
    (hGE₂ : ∀ M, 𝒞 M → ∀ s : ℤ,
      DerivedCategory.IsGE (H₂.obj (((singleFunctor C 0).obj M)⟦s⟧)) (b - s))
    (hres : ∀ M, 𝒞 M → ∃ (S : ShortComplex C) (_ : S.ShortExact) (_ : S.X₁ ≅ M),
      𝒞 S.X₃ ∧ ∀ s : ℤ, IsIso (η.app (((singleFunctor C 0).obj S.X₂)⟦s⟧)))
    (M : C) (hM : 𝒞 M) (s : ℤ) : IsIso (η.app (((singleFunctor C 0).obj M)⟦s⟧)) := by
  let X : C → ℤ → DerivedCategory C := fun M s => ((singleFunctor C 0).obj M)⟦s⟧
  -- The statement at total degree `≤ N`.
  let P : ℤ → Prop := fun N => ∀ M, 𝒞 M → ∀ q s : ℤ, q + s ≤ N →
    IsIso ((homologyFunctor D q).map (η.app (X M s)))
  have base : P (b - 1) := by
    intro M hM q s hqs
    have := hGE₁ M hM s
    have := hGE₂ M hM s
    have z₁ := DerivedCategory.isZero_of_isGE (H₁.obj (X M s)) (b - s) q (by omega)
    have z₂ := DerivedCategory.isZero_of_isGE (H₂.obj (X M s)) (b - s) q (by omega)
    exact ⟨⟨0, z₁.eq_of_src _ _, z₂.eq_of_src _ _⟩⟩
  -- The shift identifications `M[0]⟦s - 1⟧⟦1⟧ ≅ M[0]⟦s⟧`.
  let sh : ∀ (M : C) (s : ℤ), (X M (s - 1))⟦(1 : ℤ)⟧ ≅ X M s := fun M s =>
    ((shiftFunctorAdd' (DerivedCategory C) (s - 1) 1 s (by omega)).app _).symm
  have step : ∀ N : ℤ, P N → P (N + 1) := by
    intro N hN
    -- monomorphism at total degree `N + 1`
    have hmono : ∀ M, 𝒞 M → ∀ q s : ℤ, q + s = N + 1 →
        Mono ((homologyFunctor D q).map (η.app (X M s))) := by
      intro M hM q s hqs
      obtain ⟨S, hS, e, hQ, hI⟩ := hres M hM
      let T := (CategoryTheory.shiftFunctor (Triangle (DerivedCategory C)) (s - 1)).obj
        hS.singleTriangle
      have hT : T ∈ distTriang _ := Triangle.shift_distinguished _ hS.singleTriangle_distinguished _
      have h₂ : Epi ((homologyFunctor D q).map (η.app T.obj₂)) := by
        have := hI (s - 1)
        show Epi ((homologyFunctor D q).map (η.app (X S.X₂ (s - 1))))
        infer_instance
      have h₃ : Mono ((homologyFunctor D q).map (η.app T.obj₃)) := by
        have := hN S.X₃ hQ q (s - 1) (by omega)
        show Mono ((homologyFunctor D q).map (η.app (X S.X₃ (s - 1))))
        infer_instance
      have h₄ : Mono ((homologyFunctor D q).map (η.app (T.obj₂⟦(1 : ℤ)⟧))) := by
        have := hI s
        exact mono_homologyMap_app_of_iso η q (sh S.X₂ s).symm inferInstance
      have h := mono_homologyMap_app_obj₁_shift η T hT q h₂ h₃ h₄
      exact mono_homologyMap_app_of_iso η q
        (sh S.X₁ s ≪≫ (shiftFunctor (DerivedCategory C) s).mapIso
          ((singleFunctor C 0).mapIso e)) h
    intro M hM q s hqs
    obtain hlt | heq := hqs.lt_or_eq
    · exact hN M hM q s (by omega)
    obtain ⟨S, hS, e, hQ, hI⟩ := hres M hM
    let T := (CategoryTheory.shiftFunctor (Triangle (DerivedCategory C)) (s - 1)).obj
      hS.singleTriangle
    have hT : T ∈ distTriang _ := Triangle.shift_distinguished _ hS.singleTriangle_distinguished _
    have h₃ : Epi ((homologyFunctor D q).map (η.app T.obj₃)) := by
      have := hN S.X₃ hQ q (s - 1) (by omega)
      show Epi ((homologyFunctor D q).map (η.app (X S.X₃ (s - 1))))
      infer_instance
    have h₄ : Epi ((homologyFunctor D q).map (η.app (T.obj₂⟦(1 : ℤ)⟧))) := by
      have := hI s
      exact epi_homologyMap_app_of_iso η q (sh S.X₂ s).symm inferInstance
    have h₅ : Mono ((homologyFunctor D q).map (η.app (T.obj₃⟦(1 : ℤ)⟧))) :=
      mono_homologyMap_app_of_iso η q (sh S.X₃ s).symm (hmono S.X₃ hQ q s heq)
    have hepi := epi_homologyMap_app_of_iso η q
      (sh S.X₁ s ≪≫ (shiftFunctor (DerivedCategory C) s).mapIso
        ((singleFunctor C 0).mapIso e)) (epi_homologyMap_app_obj₁_shift η T hT q h₃ h₄ h₅)
    have := hmono M hM q s heq
    exact isIso_of_mono_of_epi _
  have hall : ∀ N : ℤ, b - 1 ≤ N → P N := fun N hN =>
    Int.leInduction (motive := fun n _ => P n) base (fun n _ hn => step n hn) N hN
  rw [isIso_iff]
  intro q
  exact hall (max (q + s) (b - 1)) (le_max_right _ _) M hM q s (le_max_left _ _)

section Biproduct

variable {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
  [HasFiniteBiproducts A] [HasFiniteBiproducts B] {F₁ F₂ : A ⥤ B} [F₁.Additive] [F₂.Additive]
  (θ : F₁ ⟶ F₂)

omit [HasFiniteBiproducts B] in
/-- A natural transformation of additive functors is invertible at a finite biproduct as soon as
it is invertible at each summand. -/
theorem isIso_app_biproduct {n : ℕ} (f : Fin n → A) (h : ∀ k, IsIso (θ.app (f k))) :
    IsIso (θ.app (⨁ f)) := by
  have key : θ.app (⨁ f) = (F₁.mapBiproduct f).hom ≫
      biproduct.map (fun k => θ.app (f k)) ≫ (F₂.mapBiproduct f).inv := by
    rw [← Iso.inv_comp_eq]
    refine biproduct.hom_ext' _ _ fun k => ?_
    simp only [Functor.mapBiproduct_inv, biproduct.ι_desc_assoc, biproduct.ι_map_assoc,
      biproduct.ι_desc]
    exact θ.naturality _
  rw [key]
  exact (F₁.mapBiproduct f ≪≫ biproduct.mapIso (fun k => asIso (θ.app (f k))) ≪≫
    (F₂.mapBiproduct f).symm).isIso_hom

end Biproduct

end CategoryTheory.NatTrans


end
