module
public import StacksFrontier.Homology.KFlat.Bifunctor
public import StacksFrontier.Homology.KFlat.BifunctorLocalization
public import StacksFrontier.Homology.KFlat.BifunctorTransport
public import StacksFrontier.Homology.TotalComplexTransport

public import StacksFrontier.Homology.KFlat.BifunctorTransportRepresentatives
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryCompQh

/-!
# Composing transports of a derived bifunctor

Let `F`, `F'`, `F''` be bifunctors admitting K-flat descents, and let `(G₁, G₂, G₃)` carry `F` to
`F'` through `ε`, `(H₁, H₂, H₃)` carry `F'` to `F''` through `η`, and `(K₁, K₂, K₃)` carry `F` to
`F''` through `κ`, all along exact functors. Given isomorphisms `cᵢ : Gᵢ ⋙ Hᵢ ≅ Kᵢ` with which the
three comparisons are compatible (`hc`), the composite of the derived transports along `G` and
along `H` is the derived transport along `K`, once the derived functors of `Gᵢ ⋙ Hᵢ` and of `Kᵢ`
are identified by `Functor.mapDerivedCategoryCompIsoOfIso cᵢ`.

Taking `cᵢ = Iso.refl _` and `κ` the composite comparison gives the functoriality of
`derivedTransportIso` in the functors; taking `G = H = 𝟭` (or an arbitrary `cᵢ`) gives its
invariance under isomorphisms of exact functors.

## Main results

* `CochainComplex.KFlatBifunctor.transportComplexIso_comp`: on cochain complexes.
* `CochainComplex.KFlatBifunctor.homotopyTransportIso_comp`: on the homotopy categories.
* `CochainComplex.KFlatBifunctor.derivedTransportCompNatTrans_eq` and
  `derivedTransportIso_comp_app`: **on the derived categories**, as an equation of natural
  transformations of bifunctors and at a pair of objects.

## Implementation notes

The derived statement is reduced, by `Localization.natTrans₂_ext` along the two K-flat
localizations, to left K-flat and K-flat objects, where each transport is computed by
`derivedTransportIso_hom_app_app_Qh`; what remains is the homotopy-level statement, which is in
turn the class of the complex-level one. The arrow algebra at each level is a separate lemma in a
bare category (`derived_comp_chain`, `comp_chain_homotopy`, `ι_comp₄_f_eq`), applied by `exact`,
because the objects carry several definitionally equal spellings that a rewrite cannot cross.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.KFlatBifunctor

/-- Two composites of isomorphisms agree exactly when the composites of their inverses do. -/
theorem hom_comp₄_eq_iff_inv {C : Type*} [Category C] {X₀ X₁ X₂ X₃ X₄ Y : C}
    (a : X₀ ≅ X₁) (b : X₁ ≅ X₂) (c : X₂ ≅ X₃) (d : X₃ ≅ X₄) (e : X₀ ≅ Y) (f : Y ≅ X₄) :
    a.hom ≫ b.hom ≫ c.hom ≫ d.hom = e.hom ≫ f.hom ↔
      d.inv ≫ c.inv ≫ b.inv ≫ a.inv = f.inv ≫ e.inv := by
  have := Iso.inv_eq_inv (a ≪≫ b ≪≫ c ≪≫ d) (e ≪≫ f)
  simp only [Iso.trans_inv, Iso.trans_hom, Category.assoc] at this
  exact this.symm

/-- A chase on one summand of a complex, in a bare category of complexes: if a chain of four
morphisms and a chain of two morphisms are each computed on a family of summand inclusions by
explicit morphisms, and the two explicit composites agree, so do the two chains on that
summand. -/
theorem ι_comp₄_f_eq {C : Type*} [Category C] [Limits.HasZeroMorphisms C] {I : Type*}
    {c : ComplexShape I} {X₀ X₁ X₂ X₃ X₄ Y : HomologicalComplex C c}
    (d : X₀ ⟶ X₁) (c' : X₁ ⟶ X₂) (b : X₂ ⟶ X₃) (a : X₃ ⟶ X₄) (f : X₀ ⟶ Y) (e : Y ⟶ X₄)
    (n : I) {P P₁ P₂ P₃ P₄ P₅ : C}
    (ι₀ : P ⟶ X₀.X n) (ι₁ : P₁ ⟶ X₁.X n) (ι₂ : P₂ ⟶ X₂.X n) (ι₃ : P₃ ⟶ X₃.X n)
    (ι₄ : P₄ ⟶ X₄.X n) (ι₅ : P₅ ⟶ Y.X n)
    (x₁ : P ⟶ P₁) (x₂ : P₁ ⟶ P₂) (x₃ : P₂ ⟶ P₃) (x₄ : P₃ ⟶ P₄) (y₁ : P ⟶ P₅) (y₂ : P₅ ⟶ P₄)
    (h₁ : ι₀ ≫ d.f n = x₁ ≫ ι₁) (h₂ : ι₁ ≫ c'.f n = x₂ ≫ ι₂) (h₃ : ι₂ ≫ b.f n = x₃ ≫ ι₃)
    (h₄ : ι₃ ≫ a.f n = x₄ ≫ ι₄) (h₅ : ι₀ ≫ f.f n = y₁ ≫ ι₅) (h₆ : ι₅ ≫ e.f n = y₂ ≫ ι₄)
    (hx : x₁ ≫ x₂ ≫ x₃ ≫ x₄ = y₁ ≫ y₂) :
    ι₀ ≫ (d ≫ c' ≫ b ≫ a).f n = ι₀ ≫ (f ≫ e).f n := by
  simp only [HomologicalComplex.comp_f]
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, h₄, reassoc_of% h₅, h₆,
    ← Category.assoc y₁, ← hx]
  simp only [Category.assoc]

/-- A functor applied to a composite of three morphisms, in a bare category. -/
theorem map_comp₃ {C C' : Type*} [Category C] [Category C'] (H : C' ⥤ C) {X₀ X₁ X₂ X₃ : C'}
    (f₁ : X₀ ⟶ X₁) (f₂ : X₁ ⟶ X₂) (f₃ : X₂ ⟶ X₃) :
    H.map (f₁ ≫ f₂ ≫ f₃) = H.map f₁ ≫ H.map f₂ ≫ H.map f₃ := by
  simp

/-- A functor applied to an equation between a composite of four and a composite of two
morphisms, in a bare category. -/
theorem map_comp₄_eq {C C' : Type*} [Category C] [Category C'] (H : C' ⥤ C)
    {X₀ X₁ X₂ X₃ X₄ Y : C'} (f₁ : X₀ ⟶ X₁) (f₂ : X₁ ⟶ X₂) (f₃ : X₂ ⟶ X₃) (f₄ : X₃ ⟶ X₄)
    (g₁ : X₀ ⟶ Y) (g₂ : Y ⟶ X₄) (h : f₁ ≫ f₂ ≫ f₃ ≫ f₄ = g₁ ≫ g₂) :
    H.map f₁ ≫ H.map f₂ ≫ H.map f₃ ≫ H.map f₄ = H.map g₁ ≫ H.map g₂ := by
  simp only [← H.map_comp, h]

/-- A functor applied to a composite of a morphism and its inverse, in a bare category. -/
theorem map_inv_hom_id {C C' : Type*} [Category C] [Category C'] (H : C' ⥤ C) {X Y : C'}
    (e : X ≅ Y) : H.map e.inv ≫ H.map e.hom = 𝟙 _ := by
  simp [← H.map_comp]

/-- A bifunctor applied to three composable pairs of morphisms and to two composable pairs with
the same composites, in a bare category. -/
theorem bifunctor_map_chain {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
    (P : C₁ ⥤ C₂ ⥤ C₃) {a₀ a₁ a₂ a₃ a' : C₁} {b₀ b₁ b₂ b₃ b' : C₂}
    (f₁ : a₀ ⟶ a₁) (f₂ : a₁ ⟶ a₂) (f₃ : a₂ ⟶ a₃) (g₁ : b₀ ⟶ b₁) (g₂ : b₁ ⟶ b₂) (g₃ : b₂ ⟶ b₃)
    (e : a₀ ⟶ a') (p : a' ⟶ a₃) (e' : b₀ ⟶ b') (p' : b' ⟶ b₃)
    (hf : f₁ ≫ f₂ ≫ f₃ = e ≫ p) (hg : g₁ ≫ g₂ ≫ g₃ = e' ≫ p') :
    (P.map f₁).app b₀ ≫ (P.obj a₁).map g₁ ≫ (P.map f₂).app b₁ ≫ (P.obj a₂).map g₂ ≫
        (P.map f₃).app b₂ ≫ (P.obj a₃).map g₃ =
      (P.map e).app b₀ ≫ (P.obj a').map e' ≫ (P.map p).app b' ≫ (P.obj a₃).map p' := by
  have key : (P.map (f₁ ≫ f₂ ≫ f₃)).app b₀ ≫ (P.obj a₃).map (g₁ ≫ g₂ ≫ g₃) =
      (P.map (e ≫ p)).app b₀ ≫ (P.obj a₃).map (e' ≫ p') := by
    rw [hf, hg]
  simpa only [Functor.map_comp, NatTrans.comp_app, Category.assoc, NatTrans.naturality_assoc]
    using key

/-- Cancelling a factorization against its inverse, in a bare category. -/
theorem inv_comp_map_inv_comp_eq {C C' : Type*} [Category C] [Category C'] (H : C' ⥤ C)
    {S T : C'} {V W : C} (a : H.obj T ≅ V) (b : S ≅ T) (q : V ⟶ W) (c : H.obj S ⟶ W)
    (hc : c = H.map b.hom ≫ a.hom ≫ q) :
    a.inv ≫ H.map b.inv ≫ c = q := by
  subst hc
  simp [← H.map_comp_assoc]

/-- The arrow algebra behind `derivedTransportCompNatTrans_eq`, in a bare category. -/
theorem derived_comp_chain {Cc Dd : Type*} [Category Cc] [Category Dd] (Φ₀ : Cc ⥤ Dd)
    {Y₀ Y₁ Y₂ Y₃ Y₄ Y₅ Y₆ : Cc}
    {Z₁ Z₂ Z₃ W₀ W₀' U₁ V₁ V₂ V₂' V₂'' V₃ V₃' V₃'' V₄ V₅ X₀ X₁ R₁ : Dd}
    (τG : Y₀ ⟶ Y₆) (r₁ : Y₀ ⟶ Y₁) (r₂ : Y₁ ⟶ Y₂) (r₃ : Y₂ ⟶ Y₃) (r₄ : Y₃ ⟶ Y₄)
    (r₅ : Y₄ ⟶ Y₅) (r₆ : Y₅ ⟶ Y₆) (hτG : τG = r₁ ≫ r₂ ≫ r₃ ≫ r₄ ≫ r₅ ≫ r₆)
    (τH' : Φ₀.obj Y₆ ⟶ Z₁) (w₁ : Z₁ ⟶ Z₂) (w₂ : Z₂ ⟶ Z₃)
    (τH : Φ₀.obj Y₄ ⟶ W₀) (v₁ : W₀ ⟶ W₀') (v₂ : W₀' ⟶ Z₁)
    (hnat : Φ₀.map r₅ ≫ Φ₀.map r₆ ≫ τH' = τH ≫ v₁ ≫ v₂)
    (q₁ : Φ₀.obj Y₄ ⟶ Φ₀.obj Y₃) (q₂ : Φ₀.obj Y₃ ⟶ V₁) (q₃ : V₁ ⟶ V₂) (q₄ : V₂ ⟶ V₃)
    (q₅ : V₃ ⟶ V₄) (q₆ : V₄ ⟶ W₀) (hτH : τH = q₁ ≫ q₂ ≫ q₃ ≫ q₄ ≫ q₅ ≫ q₆)
    (hρ : Φ₀.map r₄ ≫ q₁ = 𝟙 _)
    (n₁ : Φ₀.obj Y₂ ⟶ U₁) (n₂ : U₁ ⟶ V₁) (h₃ : Φ₀.map r₃ ≫ q₂ = n₁ ≫ n₂)
    (f₁ : V₂ ⟶ V₂') (f₂ : V₂' ⟶ V₂'') (μ : U₁ ⟶ R₁) (p₃ : R₁ ⟶ V₂'')
    (hH : n₂ ≫ q₃ ≫ f₁ ≫ f₂ = μ ≫ p₃)
    (e₁ : V₃ ⟶ V₃') (e₂ : V₃' ⟶ V₃'') (q₄' : V₂' ⟶ V₃') (p₄ : V₂'' ⟶ V₃'')
    (hρ₁ : f₁ ≫ q₄' = q₄ ≫ e₁) (hρ₂ : f₂ ≫ p₄ = q₄' ≫ e₂)
    (p₅ : V₃'' ⟶ V₅) (p₆ : V₅ ⟶ Z₃)
    (hΦ : q₅ ≫ q₆ ≫ v₁ ≫ v₂ ≫ w₁ ≫ w₂ = e₁ ≫ e₂ ≫ p₅ ≫ p₆)
    (γ : Φ₀.obj Y₀ ⟶ X₀) (τK : X₀ ⟶ Z₃) (p₁ : X₀ ⟶ X₁) (p₂ : X₁ ⟶ R₁)
    (hτK : τK = p₁ ≫ p₂ ≫ p₃ ≫ p₄ ≫ p₅ ≫ p₆)
    (γ' : Φ₀.obj Y₁ ⟶ X₁) (hγ : Φ₀.map r₁ ≫ γ' = γ ≫ p₁)
    (k' : R₁ ⟶ X₁) (hγ' : γ' = Φ₀.map r₂ ≫ n₁ ≫ μ ≫ k') (hk : k' ≫ p₂ = 𝟙 _) :
    Φ₀.map τG ≫ τH' ≫ w₁ ≫ w₂ = γ ≫ τK := by
  rw [hτK, hτG]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hnat, hτH]
  simp only [Category.assoc]
  rw [reassoc_of% hρ, reassoc_of% h₃, hΦ, ← reassoc_of% hρ₁, ← reassoc_of% hρ₂,
    reassoc_of% hH, ← reassoc_of% hγ, hγ']
  simp only [Category.assoc]
  rw [reassoc_of% hk]

/-- The arrow algebra behind `homotopyTransportIso_comp`, in a bare category. -/
theorem comp_chain_homotopy {C : Type*} [Category C]
    {S₀ S₁ S₂ S₃ S₃' S₄ T₁ T₂ T₃ T₄ R₀ R₁ : C}
    (x : S₀ ⟶ T₁) (y : T₁ ⟶ T₂) (u₁ : T₂ ⟶ T₃) (u₂ : T₃ ⟶ T₄) (m : S₀ ⟶ R₀) (z : R₀ ⟶ T₄)
    (s : S₀ ⟶ S₁) (t₁ : S₁ ⟶ S₂) (i₁ : S₂ ⟶ T₁) (j₁ : T₁ ⟶ S₂) (t₂ : S₂ ⟶ S₃) (i₂ : S₃ ⟶ T₂)
    (a : S₃ ⟶ S₃') (i₂' : S₃' ⟶ T₃) (b : S₃' ⟶ S₄) (i₃ : S₄ ⟶ T₄)
    (k₁ : R₀ ⟶ R₁) (t₃ : R₁ ⟶ S₄) (m' : S₁ ⟶ R₁)
    (hx : x = s ≫ t₁ ≫ i₁) (hy : y = j₁ ≫ t₂ ≫ i₂) (hij : i₁ ≫ j₁ = 𝟙 _)
    (hu₁ : i₂ ≫ u₁ = a ≫ i₂') (hu₂ : i₂' ≫ u₂ = b ≫ i₃) (hz : z = k₁ ≫ t₃ ≫ i₃)
    (hm : s ≫ m' = m ≫ k₁) (hC : t₁ ≫ t₂ ≫ a ≫ b = m' ≫ t₃) :
    x ≫ y ≫ u₁ ≫ u₂ = m ≫ z := by
  rw [hx, hy, hz]
  simp only [Category.assoc]
  rw [reassoc_of% hij, reassoc_of% hu₁, hu₂, reassoc_of% hC, reassoc_of% hm]

variable {A B D A' B' D' A'' B'' D'' : Type*}
  [Category A] [Category B] [Category D] [Category A'] [Category B'] [Category D']
  [Category A''] [Category B''] [Category D'']
  [Abelian A] [Abelian B] [Abelian D] [Abelian A'] [Abelian B'] [Abelian D']
  [Abelian A''] [Abelian B''] [Abelian D'']
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : CochainComplex A ℤ) (K₂ : CochainComplex B ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)]
  (F' : A' ⥤ B' ⥤ D') [F'.Additive] [∀ X, (F'.obj X).Additive]
  [∀ (K₁ : CochainComplex A' ℤ) (K₂ : CochainComplex B' ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ F' (ComplexShape.up ℤ)]
  (F'' : A'' ⥤ B'' ⥤ D'') [F''.Additive] [∀ X, (F''.obj X).Additive]
  [∀ (K₁ : CochainComplex A'' ℤ) (K₂ : CochainComplex B'' ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ F'' (ComplexShape.up ℤ)]
  (G₁ : A ⥤ A') (G₂ : B ⥤ B') (G₃ : D ⥤ D') [G₁.Additive] [G₂.Additive] [G₃.Additive]
  (ε : ∀ (a : A) (b : B), G₃.obj ((F.obj a).obj b) ≅ (F'.obj (G₁.obj a)).obj (G₂.obj b))
  (hε₁ : ∀ {a a' : A} (f : a ⟶ a') (b : B),
    G₃.map ((F.map f).app b) ≫ (ε a' b).hom = (ε a b).hom ≫ (F'.map (G₁.map f)).app (G₂.obj b))
  (hε₂ : ∀ (a : A) {b b' : B} (g : b ⟶ b'),
    G₃.map ((F.obj a).map g) ≫ (ε a b').hom = (ε a b).hom ≫ (F'.obj (G₁.obj a)).map (G₂.map g))
  (H₁ : A' ⥤ A'') (H₂ : B' ⥤ B'') (H₃ : D' ⥤ D'') [H₁.Additive] [H₂.Additive] [H₃.Additive]
  (η : ∀ (a : A') (b : B'), H₃.obj ((F'.obj a).obj b) ≅ (F''.obj (H₁.obj a)).obj (H₂.obj b))
  (hη₁ : ∀ {a a' : A'} (f : a ⟶ a') (b : B'),
    H₃.map ((F'.map f).app b) ≫ (η a' b).hom = (η a b).hom ≫ (F''.map (H₁.map f)).app (H₂.obj b))
  (hη₂ : ∀ (a : A') {b b' : B'} (g : b ⟶ b'),
    H₃.map ((F'.obj a).map g) ≫ (η a b').hom = (η a b).hom ≫ (F''.obj (H₁.obj a)).map (H₂.map g))
  (K₁ : A ⥤ A'') (K₂ : B ⥤ B'') (K₃ : D ⥤ D'') [K₁.Additive] [K₂.Additive] [K₃.Additive]
  (κ : ∀ (a : A) (b : B), K₃.obj ((F.obj a).obj b) ≅ (F''.obj (K₁.obj a)).obj (K₂.obj b))
  (hκ₁ : ∀ {a a' : A} (f : a ⟶ a') (b : B),
    K₃.map ((F.map f).app b) ≫ (κ a' b).hom = (κ a b).hom ≫ (F''.map (K₁.map f)).app (K₂.obj b))
  (hκ₂ : ∀ (a : A) {b b' : B} (g : b ⟶ b'),
    K₃.map ((F.obj a).map g) ≫ (κ a b').hom = (κ a b).hom ≫ (F''.obj (K₁.obj a)).map (K₂.map g))
  (c₁ : G₁ ⋙ H₁ ≅ K₁) (c₂ : G₂ ⋙ H₂ ≅ K₂) (c₃ : G₃ ⋙ H₃ ≅ K₃)
  (hc : ∀ (a : A) (b : B),
    H₃.map (ε a b).hom ≫ (η (G₁.obj a) (G₂.obj b)).hom ≫
        (F''.map (c₁.hom.app a)).app (H₂.obj (G₂.obj b)) ≫
        (F''.obj (K₁.obj a)).map (c₂.hom.app b) =
      c₃.hom.app ((F.obj a).obj b) ≫ (κ a b).hom)
  [∀ n : ℤ, PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ⁻¹' {n})) G₃]
  [∀ n : ℤ, PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ⁻¹' {n})) H₃]
  [∀ n : ℤ, PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ⁻¹' {n})) K₃]
  [∀ (K : CochainComplex A ℤ) (L : CochainComplex B ℤ),
    HomologicalComplex₂.HasTotal (HomologicalComplex₂.mapBicomplex G₃
      (((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj L))
      (ComplexShape.up ℤ)]
  [∀ (K : CochainComplex A' ℤ) (L : CochainComplex B' ℤ),
    HomologicalComplex₂.HasTotal (HomologicalComplex₂.mapBicomplex H₃
      (((F'.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj L))
      (ComplexShape.up ℤ)]
  [∀ (K : CochainComplex A ℤ) (L : CochainComplex B ℤ),
    HomologicalComplex₂.HasTotal (HomologicalComplex₂.mapBicomplex K₃
      (((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj L))
      (ComplexShape.up ℤ)]

include hc in
/-- **Composing transports, on cochain complexes.** -/
theorem transportComplexIso_comp (K : CochainComplex A ℤ) (L : CochainComplex B ℤ) :
    (H₃.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (transportComplexIso F F' G₁ G₂ G₃ ε hε₁ hε₂ K L).hom ≫
      (transportComplexIso F' F'' H₁ H₂ H₃ η hη₁ hη₂ _ _).hom ≫
      ((F''.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso c₁ (ComplexShape.up ℤ)).hom.app K)).app _ ≫
      ((F''.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).obj ((K₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).map
        ((Functor.mapHomologicalComplexCompIso c₂ (ComplexShape.up ℤ)).hom.app L) =
    (Functor.mapHomologicalComplexCompIso c₃ (ComplexShape.up ℤ)).hom.app (totalComplex F K L) ≫
      (transportComplexIso F F'' K₁ K₂ K₃ κ hκ₁ hκ₂ K L).hom := by
  refine (hom_comp₄_eq_iff_inv ((H₃.mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
        (transportComplexIso F F' G₁ G₂ G₃ ε hε₁ hε₂ K L))
      (transportComplexIso F' F'' H₁ H₂ H₃ η hη₁ hη₂ _ _)
      (((F''.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).mapIso
        ((Functor.mapHomologicalComplexCompIso c₁ (ComplexShape.up ℤ)).app K)).app _)
      (((F''.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).obj ((K₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).mapIso
        ((Functor.mapHomologicalComplexCompIso c₂ (ComplexShape.up ℤ)).app L))
      ((Functor.mapHomologicalComplexCompIso c₃ (ComplexShape.up ℤ)).app (totalComplex F K L))
      (transportComplexIso F F'' K₁ K₂ K₃ κ hκ₁ hκ₂ K L)).2 ?_
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  have h₁ : ((K₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).ιMapBifunctor
        ((K₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) F'' (ComplexShape.up ℤ) p q n hpq ≫
      (HomologicalComplex.mapBifunctorMap (𝟙 ((K₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
        ((Functor.mapHomologicalComplexCompIso c₂ (ComplexShape.up ℤ)).inv.app L) F''
        (ComplexShape.up ℤ)).f n =
      (F''.obj (K₁.obj (K.X p))).map (c₂.inv.app (L.X q)) ≫
        ((K₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).ιMapBifunctor
          ((H₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((G₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)) F'' (ComplexShape.up ℤ)
          p q n hpq := by
    simp [HomologicalComplex.ι_mapBifunctorMap]
  have h₂ : ((K₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).ιMapBifunctor
        ((H₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((G₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)) F'' (ComplexShape.up ℤ)
        p q n hpq ≫
      (HomologicalComplex.mapBifunctorMap
        ((Functor.mapHomologicalComplexCompIso c₁ (ComplexShape.up ℤ)).inv.app K)
        (𝟙 ((H₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((G₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj L))) F''
        (ComplexShape.up ℤ)).f n =
      (F''.map (c₁.inv.app (K.X p))).app (H₂.obj (G₂.obj (L.X q))) ≫
        ((H₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((G₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).ιMapBifunctor
          ((H₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((G₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)) F'' (ComplexShape.up ℤ)
          p q n hpq := by
    simp [HomologicalComplex.ι_mapBifunctorMap]
  have h₃ := Functor.ι_mapBifunctorTotalIso_inv F' F'' H₁ H₂ H₃ η (ComplexShape.up ℤ)
    (ComplexShape.up ℤ) (c := ComplexShape.up ℤ) hη₁ hη₂
    ((G₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
    ((G₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) p q n hpq
  have h₄ : H₃.map (((G₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).ιMapBifunctor
        ((G₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) F' (ComplexShape.up ℤ) p q n hpq) ≫
      ((H₃.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (transportComplexIso F F' G₁ G₂ G₃ ε hε₁ hε₂ K L).inv).f n =
      H₃.map (ε (K.X p) (L.X q)).inv ≫
        H₃.map (G₃.map (HomologicalComplex.ιMapBifunctor K L F (ComplexShape.up ℤ) p q n hpq)) := by
    rw [Functor.mapHomologicalComplex_map_f, ← H₃.map_comp, ← H₃.map_comp]
    exact congrArg H₃.map (Functor.ι_mapBifunctorTotalIso_inv F F' G₁ G₂ G₃ ε
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (c := ComplexShape.up ℤ) hε₁ hε₂ K L p q n hpq)
  have h₅ := Functor.ι_mapBifunctorTotalIso_inv F F'' K₁ K₂ K₃ κ (ComplexShape.up ℤ)
    (ComplexShape.up ℤ) (c := ComplexShape.up ℤ) hκ₁ hκ₂ K L p q n hpq
  have h₆ : K₃.map (HomologicalComplex.ιMapBifunctor K L F (ComplexShape.up ℤ) p q n hpq) ≫
      ((Functor.mapHomologicalComplexCompIso c₃ (ComplexShape.up ℤ)).inv.app
        (totalComplex F K L)).f n =
      c₃.inv.app ((F.obj (K.X p)).obj (L.X q)) ≫
        H₃.map (G₃.map (HomologicalComplex.ιMapBifunctor K L F (ComplexShape.up ℤ) p q n hpq)) :=
    c₃.inv.naturality (HomologicalComplex.ιMapBifunctor K L F (ComplexShape.up ℤ) p q n hpq)
  have hx : (F''.obj (K₁.obj (K.X p))).map (c₂.inv.app (L.X q)) ≫
      (F''.map (c₁.inv.app (K.X p))).app (H₂.obj (G₂.obj (L.X q))) ≫
      (η (G₁.obj (K.X p)) (G₂.obj (L.X q))).inv ≫ H₃.map (ε (K.X p) (L.X q)).inv =
      (κ (K.X p) (L.X q)).inv ≫ c₃.inv.app ((F.obj (K.X p)).obj (L.X q)) :=
    (hom_comp₄_eq_iff_inv (H₃.mapIso (ε (K.X p) (L.X q)))
      (η (G₁.obj (K.X p)) (G₂.obj (L.X q)))
      ((F''.mapIso (c₁.app (K.X p))).app (H₂.obj (G₂.obj (L.X q))))
      ((F''.obj (K₁.obj (K.X p))).mapIso (c₂.app (L.X q)))
      (c₃.app ((F.obj (K.X p)).obj (L.X q))) (κ (K.X p) (L.X q))).1 (hc (K.X p) (L.X q))
  exact ι_comp₄_f_eq _ _ _ _ _ _ n _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆ hx

include hc in
/-- **Composing transports, on the homotopy categories.** -/
theorem homotopyTransportIso_comp (X : HomotopyCategory A (ComplexShape.up ℤ))
    (Y : HomotopyCategory B (ComplexShape.up ℤ)) :
    (H₃.mapHomotopyCategory (ComplexShape.up ℤ)).map
        (((homotopyTransportIso F F' G₁ G₂ G₃ ε hε₁ hε₂).hom.app X).app Y) ≫
      ((homotopyTransportIso F' F'' H₁ H₂ H₃ η hη₁ hη₂).hom.app
        ((G₁.mapHomotopyCategory (ComplexShape.up ℤ)).obj X)).app
        ((G₂.mapHomotopyCategory (ComplexShape.up ℤ)).obj Y) ≫
      ((homotopyBifunctor F'').map
          ((Functor.mapHomotopyCategoryCompIso c₁ (ComplexShape.up ℤ)).hom.app X)).app
        ((H₂.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((G₂.mapHomotopyCategory (ComplexShape.up ℤ)).obj Y)) ≫
      ((homotopyBifunctor F'').obj ((K₁.mapHomotopyCategory (ComplexShape.up ℤ)).obj X)).map
        ((Functor.mapHomotopyCategoryCompIso c₂ (ComplexShape.up ℤ)).hom.app Y) =
    (Functor.mapHomotopyCategoryCompIso c₃ (ComplexShape.up ℤ)).hom.app
        (((homotopyBifunctor F).obj X).obj Y) ≫
      ((homotopyTransportIso F F'' K₁ K₂ K₃ κ hκ₁ hκ₂).hom.app X).app Y := by
  obtain ⟨K⟩ := X
  obtain ⟨L⟩ := Y
  have hx := (congrArg (H₃.mapHomotopyCategory (ComplexShape.up ℤ)).map
    (homotopyTransportIso_hom_app_app_quotient' F F' G₁ G₂ G₃ ε hε₁ hε₂ K L)).trans
    (map_comp₃ (H₃.mapHomotopyCategory (ComplexShape.up ℤ)) _ _ _)
  have hy := homotopyTransportIso_hom_app_app_quotient' F' F'' H₁ H₂ H₃ η hη₁ hη₂
    ((G₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
    ((G₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)
  have hz := homotopyTransportIso_hom_app_app_quotient' F F'' K₁ K₂ K₃ κ hκ₁ hκ₂ K L
  have hij := map_inv_hom_id (H₃.mapHomotopyCategory (ComplexShape.up ℤ))
    (((homotopyBifunctorLiftingIso F').app
      ((G₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).app
      ((G₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj L))
  have hu₁ := NatTrans.congr_app ((homotopyBifunctorLiftingIso F'').inv.naturality
    ((Functor.mapHomologicalComplexCompIso c₁ (ComplexShape.up ℤ)).hom.app K))
    ((H₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((G₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj L))
  have hu₂ := ((homotopyBifunctorLiftingIso F'').inv.app
    ((K₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).naturality
    ((Functor.mapHomologicalComplexCompIso c₂ (ComplexShape.up ℤ)).hom.app L)
  have hm := (Functor.mapHomotopyCategoryCompIso c₃ (ComplexShape.up ℤ)).hom.naturality
    (((homotopyBifunctorLiftingIso F).hom.app K).app L)
  have hC := map_comp₄_eq (HomotopyCategory.quotient D'' (ComplexShape.up ℤ)) _ _ _ _ _ _
    (transportComplexIso_comp F F' F'' G₁ G₂ G₃ ε hε₁ hε₂ H₁ H₂ H₃ η hη₁ hη₂ K₁ K₂ K₃ κ hκ₁ hκ₂
      c₁ c₂ c₃ hc K L)
  simp only [NatTrans.comp_app] at hu₁ hu₂
  exact comp_chain_homotopy _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hx hy hij hu₁.symm hu₂.symm hz
    hm hC

section Derived

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]
  [HasDerivedCategory A'] [HasDerivedCategory B'] [HasDerivedCategory D']
  [HasDerivedCategory A''] [HasDerivedCategory B''] [HasDerivedCategory D'']
  [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
  [PreservesFiniteLimits G₃] [PreservesFiniteColimits G₃]
  [PreservesFiniteLimits H₁] [PreservesFiniteColimits H₁]
  [PreservesFiniteLimits H₂] [PreservesFiniteColimits H₂]
  [PreservesFiniteLimits H₃] [PreservesFiniteColimits H₃]
  [PreservesFiniteLimits K₁] [PreservesFiniteColimits K₁]
  [PreservesFiniteLimits K₂] [PreservesFiniteColimits K₂]
  [PreservesFiniteLimits K₃] [PreservesFiniteColimits K₃]
  [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)]
  [(kFlatQLeft F').IsLocalization (kFlatQuasiIsoLeft F')]
  [(kFlatQ F').IsLocalization (kFlatQuasiIso F')]
  [(kFlatQLeft F'').IsLocalization (kFlatQuasiIsoLeft F'')]
  [(kFlatQ F'').IsLocalization (kFlatQuasiIso F'')]
  (hG₁ : ∀ K : CochainComplex A ℤ, KFlatLeft F K →
    KFlatLeft F' ((G₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
  (hG₂ : ∀ L : CochainComplex B ℤ, KFlat F L →
    KFlat F' ((G₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj L))
  (hH₁ : ∀ K : CochainComplex A' ℤ, KFlatLeft F' K →
    KFlatLeft F'' ((H₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
  (hH₂ : ∀ L : CochainComplex B' ℤ, KFlat F' L →
    KFlat F'' ((H₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj L))
  (hK₁ : ∀ K : CochainComplex A ℤ, KFlatLeft F K →
    KFlatLeft F'' ((K₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
  (hK₂ : ∀ L : CochainComplex B ℤ, KFlat F L →
    KFlat F'' ((K₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj L))

/-- The composite of two transports, followed by the comparison of the composite functors with
`K₁` and `K₂`, as a natural transformation of bifunctors on the derived categories. -/
def derivedTransportCompNatTrans :
    derivedBifunctor F ⋙ (Functor.whiskeringRight _ _ _).obj
        (G₃.mapDerivedCategory ⋙ H₃.mapDerivedCategory) ⟶
      K₁.mapDerivedCategory ⋙ derivedBifunctor F'' ⋙
        (Functor.whiskeringLeft _ _ _).obj K₂.mapDerivedCategory :=
  Functor.whiskerRight (derivedTransportIso F F' G₁ G₂ G₃ ε hε₁ hε₂ hG₁ hG₂).hom
      ((Functor.whiskeringRight _ _ _).obj H₃.mapDerivedCategory) ≫
    Functor.whiskerLeft G₁.mapDerivedCategory
      (Functor.whiskerRight (derivedTransportIso F' F'' H₁ H₂ H₃ η hη₁ hη₂ hH₁ hH₂).hom
        ((Functor.whiskeringLeft _ _ _).obj G₂.mapDerivedCategory)) ≫
    Functor.whiskerRight (Functor.mapDerivedCategoryCompIsoOfIso c₁).inv
      (derivedBifunctor F'' ⋙ (Functor.whiskeringLeft _ _ _).obj
        (G₂.mapDerivedCategory ⋙ H₂.mapDerivedCategory)) ≫
    Functor.whiskerLeft (K₁.mapDerivedCategory ⋙ derivedBifunctor F'')
      ((Functor.whiskeringLeft _ _ _).map (Functor.mapDerivedCategoryCompIsoOfIso c₂).inv)

/-- The comparison of the composite functors with `K₃`, followed by the transport along the
`Kᵢ`, as a natural transformation of bifunctors on the derived categories. -/
def derivedTransportDirectNatTrans :
    derivedBifunctor F ⋙ (Functor.whiskeringRight _ _ _).obj
        (G₃.mapDerivedCategory ⋙ H₃.mapDerivedCategory) ⟶
      K₁.mapDerivedCategory ⋙ derivedBifunctor F'' ⋙
        (Functor.whiskeringLeft _ _ _).obj K₂.mapDerivedCategory :=
  Functor.whiskerLeft (derivedBifunctor F)
      ((Functor.whiskeringRight _ _ _).map (Functor.mapDerivedCategoryCompIsoOfIso c₃).inv) ≫
    (derivedTransportIso F F'' K₁ K₂ K₃ κ hκ₁ hκ₂ hK₁ hK₂).hom

include hc in
/-- **Composing transports of a derived bifunctor.** -/
theorem derivedTransportCompNatTrans_eq :
    derivedTransportCompNatTrans F F' F'' G₁ G₂ G₃ ε hε₁ hε₂ H₁ H₂ H₃ η hη₁ hη₂ K₁ K₂ c₁ c₂
        hG₁ hG₂ hH₁ hH₂ =
      derivedTransportDirectNatTrans F F'' G₃ H₃ K₁ K₂ K₃ κ hκ₁ hκ₂ c₃ hK₁ hK₂ := by
  refine Localization.natTrans₂_ext (kFlatQLeft F) (kFlatQ F) (kFlatQuasiIsoLeft F)
    (kFlatQuasiIso F) (fun X₁ X₂ => ?_)
  simp only [derivedTransportCompNatTrans, derivedTransportDirectNatTrans, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.whiskeringRight_obj_map,
    Functor.whiskeringLeft_obj_map, Functor.comp_obj, Functor.comp_map]
  have hτG := (derivedTransportIso_hom_app_app_Qh F F' G₁ G₂ G₃ ε hε₁ hε₂ hG₁ hG₂ X₁.obj X₂).trans
    (homotopyTransportAtIso_hom_app F F' G₁ G₂ G₃ ε hε₁ hε₂ hG₂ X₂ X₁.obj)
  have hτH := (derivedTransportIso_hom_app_app_Qh F' F'' H₁ H₂ H₃ η hη₁ hη₂ hH₁ hH₂
      ((G₁.mapHomotopyCategory (ComplexShape.up ℤ)).obj X₁.obj)
      ((kFlatMapRight F F' G₂ hG₂).obj X₂)).trans
    (homotopyTransportAtIso_hom_app F' F'' H₁ H₂ H₃ η hη₁ hη₂ hH₂
      ((kFlatMapRight F F' G₂ hG₂).obj X₂)
      ((G₁.mapHomotopyCategory (ComplexShape.up ℤ)).obj X₁.obj))
  have hτK := (derivedTransportIso_hom_app_app_Qh F F'' K₁ K₂ K₃ κ hκ₁ hκ₂ hK₁ hK₂ X₁.obj X₂).trans
    (homotopyTransportAtIso_hom_app F F'' K₁ K₂ K₃ κ hκ₁ hκ₂ hK₂ X₂ X₁.obj)
  have hnat := bifunctor_natTrans_naturality₂
    (derivedTransportIso F' F'' H₁ H₂ H₃ η hη₁ hη₂ hH₁ hH₂).hom
    (G₁.mapDerivedCategoryFactorsh.inv.app X₁.obj) (G₂.mapDerivedCategoryFactorsh.inv.app X₂.obj)
  have hρ := map_inv_hom_id H₃.mapDerivedCategory
    (((homotopyComparisonRightIso F').app
      ((G₁.mapHomotopyCategory (ComplexShape.up ℤ)).obj X₁.obj)).app
      ((kFlatMapRight F F' G₂ hG₂).obj X₂))
  have h₃ := H₃.mapDerivedCategoryFactorsh.hom.naturality
    (((homotopyTransportIso F F' G₁ G₂ G₃ ε hε₁ hε₂).hom.app X₁.obj).app X₂.obj)
  have hH := map_comp₄_eq DerivedCategory.Qh _ _ _ _ _ _
    (homotopyTransportIso_comp F F' F'' G₁ G₂ G₃ ε hε₁ hε₂ H₁ H₂ H₃ η hη₁ hη₂ K₁ K₂ K₃ κ hκ₁ hκ₂
      c₁ c₂ c₃ hc X₁.obj X₂.obj)
  have hρ₁ := NatTrans.congr_app ((homotopyComparisonRightIso F'').inv.naturality
    ((Functor.mapHomotopyCategoryCompIso c₁ (ComplexShape.up ℤ)).hom.app X₁.obj))
    ((kFlatMapRight F' F'' H₂ hH₂).obj ((kFlatMapRight F F' G₂ hG₂).obj X₂))
  have hρ₂ := ((homotopyComparisonRightIso F'').inv.app
    ((K₁.mapHomotopyCategory (ComplexShape.up ℤ)).obj X₁.obj)).naturality
    (ObjectProperty.homMk ((Functor.mapHomotopyCategoryCompIso c₂ (ComplexShape.up ℤ)).hom.app
        X₂.obj) :
      (kFlatMapRight F' F'' H₂ hH₂).obj ((kFlatMapRight F F' G₂ hG₂).obj X₂) ⟶
        (kFlatMapRight F F'' K₂ hK₂).obj X₂)
  simp only [NatTrans.comp_app] at hρ₁
  have hf := inv_comp_map_inv_comp_eq H₁.mapDerivedCategory
    (H₁.mapDerivedCategoryFactorsh.app ((G₁.mapHomotopyCategory (ComplexShape.up ℤ)).obj X₁.obj))
    (G₁.mapDerivedCategoryFactorsh.app X₁.obj) _ _
    (Functor.mapDerivedCategoryCompIsoOfIso_inv_app c₁ X₁.obj)
  have hg := inv_comp_map_inv_comp_eq H₂.mapDerivedCategory
    (H₂.mapDerivedCategoryFactorsh.app ((G₂.mapHomotopyCategory (ComplexShape.up ℤ)).obj X₂.obj))
    (G₂.mapDerivedCategoryFactorsh.app X₂.obj) _ _
    (Functor.mapDerivedCategoryCompIsoOfIso_inv_app c₂ X₂.obj)
  have hΦ := bifunctor_map_chain (derivedBifunctor F'') _ _ _ _ _ _ _ _ _ _ hf hg
  have hγ := (Functor.mapDerivedCategoryCompIsoOfIso c₃).inv.naturality
    (((homotopyComparisonRightIso F).hom.app X₁.obj).app X₂)
  have hγ' := Functor.mapDerivedCategoryCompIsoOfIso_inv_app c₃
    (((homotopyBifunctor F).obj X₁.obj).obj X₂.obj)
  have hk := Iso.inv_hom_id_app K₃.mapDerivedCategoryFactorsh
    (((homotopyBifunctor F).obj X₁.obj).obj X₂.obj)
  exact derived_comp_chain H₃.mapDerivedCategory _ _ _ _ _ _ _ hτG _ _ _ _ _ _ hnat
    _ _ _ _ _ _ hτH hρ _ _ h₃ _ _ _ _ hH _ _ _ _ hρ₁ hρ₂ _ _ hΦ _ _ _ _ hτK _ hγ _ hγ' hk

include hc in
/-- **Composing transports of a derived bifunctor, at a pair of objects.** -/
theorem derivedTransportIso_comp_app (M : DerivedCategory A) (N : DerivedCategory B) :
    H₃.mapDerivedCategory.map
        (((derivedTransportIso F F' G₁ G₂ G₃ ε hε₁ hε₂ hG₁ hG₂).hom.app M).app N) ≫
      ((derivedTransportIso F' F'' H₁ H₂ H₃ η hη₁ hη₂ hH₁ hH₂).hom.app
        (G₁.mapDerivedCategory.obj M)).app (G₂.mapDerivedCategory.obj N) ≫
      ((derivedBifunctor F'').map ((Functor.mapDerivedCategoryCompIsoOfIso c₁).inv.app M)).app
        (H₂.mapDerivedCategory.obj (G₂.mapDerivedCategory.obj N)) ≫
      ((derivedBifunctor F'').obj (K₁.mapDerivedCategory.obj M)).map
        ((Functor.mapDerivedCategoryCompIsoOfIso c₂).inv.app N) =
    (Functor.mapDerivedCategoryCompIsoOfIso c₃).inv.app (((derivedBifunctor F).obj M).obj N) ≫
      ((derivedTransportIso F F'' K₁ K₂ K₃ κ hκ₁ hκ₂ hK₁ hK₂).hom.app M).app N := by
  have h := NatTrans.congr_app (NatTrans.congr_app
    (derivedTransportCompNatTrans_eq F F' F'' G₁ G₂ G₃ ε hε₁ hε₂ H₁ H₂ H₃ η hη₁ hη₂ K₁ K₂ K₃ κ
      hκ₁ hκ₂ c₁ c₂ c₃ hc hG₁ hG₂ hH₁ hH₂ hK₁ hK₂) M) N
  simpa [derivedTransportCompNatTrans, derivedTransportDirectNatTrans] using h

end Derived

end CochainComplex.KFlatBifunctor

end
