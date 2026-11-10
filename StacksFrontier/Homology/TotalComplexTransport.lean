module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Transporting a total complex along a functor

Let `Φ : D ⥤ D'` be an additive functor and let `K` be a bicomplex in `D`. The total complex
`Tot(K)` is, in each degree, a coproduct of the terms of `K` along an antidiagonal, so there is
a canonical comparison morphism `Tot(Φ(K)) ⟶ Φ(Tot(K))` assembled from the `Φ(ι_{i₁, i₂})`, and
it is an isomorphism as soon as `Φ` preserves those antidiagonal coproducts. That is
`HomologicalComplex₂.totalIso`.

Combined with a comparison of *bifunctors*, this transports total complexes of bifunctors.
If `F : A ⥤ B ⥤ D` and `F' : A' ⥤ B' ⥤ D'` are bifunctors, if `Φ₁ : A ⥤ A'`, `Φ₂ : B ⥤ B'`
and `Φ : D ⥤ D'` are additive, and if `Φ` carries `F` to `F'`, i.e. there are isomorphisms
`Φ(F(a, b)) ≅ F'(Φ₁ a, Φ₂ b)` natural in `a` and in `b`, then

  `Φ(Tot(F(K, L))) ≅ Tot(F'(Φ₁ K, Φ₂ L))`

as complexes in `D'`. That is `Functor.mapBifunctorTotalIso`.

## Main definitions

* `HomologicalComplex₂.mapBicomplex`: an additive functor applied to each term of a bicomplex.
* `HomologicalComplex₂.totalMap`: the canonical comparison `Tot(Φ(K)) ⟶ Φ(Tot(K))`.
* `HomologicalComplex₂.totalIso`: that comparison, as an isomorphism, when `Φ` preserves the
  antidiagonal coproducts.
* `Functor.mapBifunctorBicomplexIso`: the bicomplex comparison
  `Φ(F(K, L)) ≅ F'(Φ₁ K, Φ₂ L)` built from a degreewise comparison of the bifunctors.
* `Functor.mapBifunctorTotalIso`: the resulting comparison of total complexes.

## Main results

* `HomologicalComplex₂.totalMap_naturality`: the comparison is natural in the bicomplex.
* `HomologicalComplex₂.ι_totalMapf`: the comparison is characterised on the summands.
* `Functor.mapBifunctorTotalIso_hom_naturality`: the comparison of total complexes of bifunctors
  is natural in both complexes.

## Implementation notes

The hypothesis on `Φ` is `PreservesColimitsOfShape (Discrete (ComplexShape.π c₁ c₂ c₁₂ ⁻¹' {n}))`
for each total degree `n`, that is, preservation of exactly the coproducts that occur, rather
than preservation of all colimits.

The comparison is built in the direction `Tot(Φ(K)) ⟶ Φ(Tot(K))` because that is the direction
in which it is *defined*: the source is a coproduct and so admits a map out of it given by its
universal property, while the target need not be one. Invertibility is a separate statement.

The bifunctor comparison is taken as a family of isomorphisms together with its two naturality
squares, rather than as a natural isomorphism of curried functors.
-/

@[expose] public section

open CategoryTheory Category Limits Preadditive

universe v v' u u'

namespace HomologicalComplex₂

variable {D : Type u} {D' : Type u'} [Category.{v} D] [Category.{v'} D']
  [Preadditive D] [Preadditive D']
  {I₁ I₂ I₁₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c₁₂ : ComplexShape I₁₂}
  [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]
  (Φ : D ⥤ D') [Φ.Additive] (K : HomologicalComplex₂ D c₁ c₂)

/-- `Φ(K)`, the bicomplex obtained by applying an additive functor `Φ` to each term of a
bicomplex `K`. -/
public abbrev mapBicomplex : HomologicalComplex₂ D' c₁ c₂ :=
  ((Φ.mapHomologicalComplex c₂).mapHomologicalComplex c₁).obj K

variable [K.HasTotal c₁₂] [(mapBicomplex Φ K).HasTotal c₁₂]

/-- The canonical morphism `Tot(Φ(K))^n ⟶ Φ(Tot(K)^n)`, induced out of the coproduct
`Tot(Φ(K))^n` by the family `Φ(ι_{i₁, i₂})`. -/
public noncomputable def totalMapf (n : I₁₂) :
    ((mapBicomplex Φ K).total c₁₂).X n ⟶ Φ.obj ((K.total c₁₂).X n) :=
  (mapBicomplex Φ K).totalDesc (fun i₁ i₂ h => Φ.map (K.ιTotal c₁₂ i₁ i₂ n h))

/-- On the summand indexed by `(i₁, i₂)`, `totalMapf` is `Φ(ι_{i₁, i₂})`. -/
@[reassoc]
public lemma ι_totalMapf (n : I₁₂) (i₁ : I₁) (i₂ : I₂)
    (h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = n) :
    (mapBicomplex Φ K).ιTotal c₁₂ i₁ i₂ n h ≫ totalMapf Φ K n =
      Φ.map (K.ιTotal c₁₂ i₁ i₂ n h) := by
  simp [totalMapf]

/-- The characterisation of `totalMapf` on summands, in the form that also covers the
summands whose degree does not match, where both sides are zero. -/
public lemma ιOrZero_totalMapf (n : I₁₂) (i₁ : I₁) (i₂ : I₂) :
    (mapBicomplex Φ K).ιTotalOrZero c₁₂ i₁ i₂ n ≫ totalMapf Φ K n =
      Φ.map (K.ιTotalOrZero c₁₂ i₁ i₂ n) := by
  by_cases h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = n
  · rw [HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ h,
      HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ h, ι_totalMapf]
  · rw [HomologicalComplex₂.ιTotalOrZero_eq_zero _ _ _ _ _ h,
      HomologicalComplex₂.ιTotalOrZero_eq_zero _ _ _ _ _ h, zero_comp, Φ.map_zero]

/-- A signed differential component followed by a summand inclusion is carried by `totalMapf`
to its image under `Φ`. -/
private theorem smul_comp_ιTotalOrZero_comp_totalMapf (u : ℤˣ) {X : D} {i₁ : I₁} {i₂ : I₂}
    (g : X ⟶ (K.X i₁).X i₂) (n : I₁₂) :
    (u • (Φ.map g ≫ (mapBicomplex Φ K).ιTotalOrZero c₁₂ i₁ i₂ n)) ≫ totalMapf Φ K n =
      Φ.map (u • (g ≫ K.ιTotalOrZero c₁₂ i₁ i₂ n)) := by
  rw [Units.smul_def, Units.smul_def, Φ.map_zsmul, Linear.smul_comp, Category.assoc,
    ιOrZero_totalMapf, Φ.map_comp]

/-- `totalMapf` is compatible with the horizontal differential of the total complex on each
summand. -/
public lemma d₁_totalMapf (i₁ : I₁) (i₂ : I₂) (n : I₁₂) :
    (mapBicomplex Φ K).d₁ c₁₂ i₁ i₂ n ≫ totalMapf Φ K n = Φ.map (K.d₁ c₁₂ i₁ i₂ n) := by
  by_cases h : c₁.Rel i₁ (c₁.next i₁)
  · rw [HomologicalComplex₂.d₁_eq' _ _ h, HomologicalComplex₂.d₁_eq' _ _ h]
    exact smul_comp_ιTotalOrZero_comp_totalMapf Φ K _ _ _
  · rw [HomologicalComplex₂.d₁_eq_zero _ _ _ _ _ h,
      HomologicalComplex₂.d₁_eq_zero _ _ _ _ _ h, zero_comp, Φ.map_zero]

/-- `totalMapf` is compatible with the vertical differential of the total complex on each
summand. -/
public lemma d₂_totalMapf (i₁ : I₁) (i₂ : I₂) (n : I₁₂) :
    (mapBicomplex Φ K).d₂ c₁₂ i₁ i₂ n ≫ totalMapf Φ K n = Φ.map (K.d₂ c₁₂ i₁ i₂ n) := by
  by_cases h : c₂.Rel i₂ (c₂.next i₂)
  · rw [HomologicalComplex₂.d₂_eq' _ _ _ h, HomologicalComplex₂.d₂_eq' _ _ _ h]
    exact smul_comp_ιTotalOrZero_comp_totalMapf Φ K _ _ _
  · rw [HomologicalComplex₂.d₂_eq_zero _ _ _ _ _ h,
      HomologicalComplex₂.d₂_eq_zero _ _ _ _ _ h, zero_comp, Φ.map_zero]

/-- The maps `Tot(Φ(K))^n ⟶ Φ(Tot(K)^n)` commute with the differentials. -/
public lemma d_totalMapf (n n' : I₁₂) :
    ((mapBicomplex Φ K).total c₁₂).d n n' ≫ totalMapf Φ K n' =
      totalMapf Φ K n ≫ Φ.map ((K.total c₁₂).d n n') := by
  refine HomologicalComplex₂.total.hom_ext c₁₂ (fun i₁ i₂ h => ?_)
  rw [← Category.assoc, ← Category.assoc, HomologicalComplex₂.total_d, Preadditive.comp_add,
    HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂, Preadditive.add_comp, d₁_totalMapf,
    d₂_totalMapf, ι_totalMapf, ← Φ.map_comp, HomologicalComplex₂.total_d, Preadditive.comp_add,
    HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂, Φ.map_add]

/-- The canonical morphism of complexes `Tot(Φ(K)) ⟶ Φ(Tot(K))`. -/
public noncomputable def totalMap :
    (mapBicomplex Φ K).total c₁₂ ⟶ (Φ.mapHomologicalComplex c₁₂).obj (K.total c₁₂) where
  f n := totalMapf Φ K n
  comm' n n' _ := by
    rw [Functor.mapHomologicalComplex_obj_d]
    exact (d_totalMapf Φ K n n').symm

/-- Preservation of the antidiagonal coproduct in one total degree makes the comparison
invertible in that degree. -/
public lemma isIso_totalMapf (n : I₁₂)
    [PreservesColimitsOfShape (Discrete ↥(ComplexShape.π c₁ c₂ c₁₂ ⁻¹' {n})) Φ] :
    IsIso (totalMapf (c₁₂ := c₁₂) Φ K n) := by
  let hc := Cofan.isColimitMapCoconeEquiv Φ _ _
    (isColimitOfPreserves Φ
      (K.toGradedObject.isColimitCofanMapObj (ComplexShape.π c₁ c₂ c₁₂) n))
  let ι' : ∀ i : ↥(ComplexShape.π c₁ c₂ c₁₂ ⁻¹' {n}),
      Φ.obj ((K.X i.1.1).X i.1.2) ⟶ ((mapBicomplex Φ K).total c₁₂).X n :=
    fun i => (mapBicomplex Φ K).ιTotal c₁₂ i.1.1 i.1.2 n i.2
  let ψ : Φ.obj ((K.total c₁₂).X n) ⟶ ((mapBicomplex Φ K).total c₁₂).X n :=
    Cofan.IsColimit.desc hc ι'
  have hψ : ∀ i : ↥(ComplexShape.π c₁ c₂ c₁₂ ⁻¹' {n}),
      Φ.map (K.ιTotal c₁₂ i.1.1 i.1.2 n i.2) ≫ ψ =
        (mapBicomplex Φ K).ιTotal c₁₂ i.1.1 i.1.2 n i.2 :=
    fun i => Cofan.IsColimit.fac hc _ i
  refine ⟨ψ, ?_, ?_⟩
  · refine HomologicalComplex₂.total.hom_ext c₁₂ (fun i₁ i₂ h => ?_)
    rw [Category.comp_id, ι_totalMapf_assoc]
    exact hψ ⟨(i₁, i₂), h⟩
  · refine Cofan.IsColimit.hom_ext hc _ _ (fun i => ?_)
    change Φ.map (K.ιTotal c₁₂ i.1.1 i.1.2 n i.2) ≫ ψ ≫ totalMapf Φ K n =
      Φ.map (K.ιTotal c₁₂ i.1.1 i.1.2 n i.2) ≫ 𝟙 _
    rw [← Category.assoc, hψ i, Category.comp_id]
    exact ι_totalMapf Φ K n _ _ i.2

/-- **An additive functor preserving the antidiagonal coproducts commutes with totalisation:**
`Tot(Φ(K)) ≅ Φ(Tot(K))`. -/
public noncomputable def totalIso
    [∀ n : I₁₂, PreservesColimitsOfShape (Discrete ↥(ComplexShape.π c₁ c₂ c₁₂ ⁻¹' {n})) Φ] :
    (mapBicomplex Φ K).total c₁₂ ≅ (Φ.mapHomologicalComplex c₁₂).obj (K.total c₁₂) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => @asIso _ _ _ _ (totalMapf (c₁₂ := c₁₂) Φ K n)
      (isIso_totalMapf (c₁₂ := c₁₂) Φ K n))
    (fun n n' _ => (totalMap Φ K).comm n n')

/-- The forward map of `totalIso` is `totalMap`. -/
public lemma totalIso_hom_eq_totalMap
    [∀ n : I₁₂, PreservesColimitsOfShape (Discrete ↥(ComplexShape.π c₁ c₂ c₁₂ ⁻¹' {n})) Φ] :
    (totalIso (c₁₂ := c₁₂) Φ K).hom = totalMap Φ K := rfl

/-- The comparison `Tot(Φ(-)) ⟶ Φ(Tot(-))` is natural in the bicomplex. -/
public theorem totalMap_naturality {L : HomologicalComplex₂ D c₁ c₂} [L.HasTotal c₁₂]
    [(mapBicomplex Φ L).HasTotal c₁₂] (f : K ⟶ L) :
    HomologicalComplex₂.total.map
        (((Φ.mapHomologicalComplex c₂).mapHomologicalComplex c₁).map f) c₁₂ ≫
      totalMap Φ L = totalMap Φ K ≫
        (Φ.mapHomologicalComplex c₁₂).map (HomologicalComplex₂.total.map f c₁₂) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex₂.total.hom_ext c₁₂
  intro i₁ i₂ h
  change (mapBicomplex Φ K).ιTotal c₁₂ i₁ i₂ n h ≫
      ((HomologicalComplex₂.total.map _ c₁₂).f n ≫ totalMapf Φ L n) =
    (mapBicomplex Φ K).ιTotal c₁₂ i₁ i₂ n h ≫
      (totalMapf Φ K n ≫ Φ.map ((HomologicalComplex₂.total.map f c₁₂).f n))
  rw [← Category.assoc, HomologicalComplex₂.ιTotal_map, Category.assoc, ι_totalMapf,
    ← Category.assoc, ι_totalMapf]
  change Φ.map ((f.f i₁).f i₂) ≫ Φ.map (L.ιTotal c₁₂ i₁ i₂ n h) =
    Φ.map (K.ιTotal c₁₂ i₁ i₂ n h) ≫ Φ.map ((HomologicalComplex₂.total.map f c₁₂).f n)
  rw [← Φ.map_comp, ← Φ.map_comp, HomologicalComplex₂.ιTotal_map]

end HomologicalComplex₂

namespace CategoryTheory.Functor

universe vA vB vA' vB' uA uB uA' uB'

variable {A : Type uA} {B : Type uB} {D : Type u} {A' : Type uA'} {B' : Type uB'} {D' : Type u'}
  [Category.{vA} A] [Category.{vB} B] [Category.{v} D]
  [Category.{vA'} A'] [Category.{vB'} B'] [Category.{v'} D']
  [Preadditive A] [Preadditive B] [Preadditive D]
  [Preadditive A'] [Preadditive B'] [Preadditive D']
  (F : A ⥤ B ⥤ D) (F' : A' ⥤ B' ⥤ D')
  [F.PreservesZeroMorphisms] [∀ X, (F.obj X).PreservesZeroMorphisms]
  [F'.PreservesZeroMorphisms] [∀ X, (F'.obj X).PreservesZeroMorphisms]
  (Φ₁ : A ⥤ A') (Φ₂ : B ⥤ B') (Φ : D ⥤ D') [Φ₁.Additive] [Φ₂.Additive] [Φ.Additive]
  (ε : ∀ (a : A) (b : B), Φ.obj ((F.obj a).obj b) ≅ (F'.obj (Φ₁.obj a)).obj (Φ₂.obj b))

variable {I₁ I₂ : Type*} (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂)

/-- The bicomplex comparison `Φ(F(K, L)) ≅ F'(Φ₁ K, Φ₂ L)`, built degreewise from a comparison
`ε` of the two bifunctors that is natural in each variable. -/
public noncomputable def mapBifunctorBicomplexIso
    (hε₁ : ∀ {a a' : A} (f : a ⟶ a') (b : B),
      Φ.map ((F.map f).app b) ≫ (ε a' b).hom =
        (ε a b).hom ≫ (F'.map (Φ₁.map f)).app (Φ₂.obj b))
    (hε₂ : ∀ (a : A) {b b' : B} (g : b ⟶ b'),
      Φ.map ((F.obj a).map g) ≫ (ε a b').hom =
        (ε a b).hom ≫ (F'.obj (Φ₁.obj a)).map (Φ₂.map g))
    (K : HomologicalComplex A c₁) (L : HomologicalComplex B c₂) :
    HomologicalComplex₂.mapBicomplex Φ
        (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K).obj L) ≅
      ((F'.mapBifunctorHomologicalComplex c₁ c₂).obj
          ((Φ₁.mapHomologicalComplex c₁).obj K)).obj ((Φ₂.mapHomologicalComplex c₂).obj L) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i₁ => HomologicalComplex.Hom.isoOfComponents
      (fun i₂ => ε (K.X i₁) (L.X i₂))
      (fun i₂ i₂' _ => (hε₂ (K.X i₁) (L.d i₂ i₂')).symm))
    (fun i₁ i₁' _ => by
      ext i₂
      exact (hε₁ (K.d i₁ i₁') (L.X i₂)).symm)

/-- **The total complex of a bifunctor transported along a functor.** If the additive functor
`Φ : D ⥤ D'` carries the bifunctor `F` to `F'` along `Φ₁` and `Φ₂`, and preserves the
antidiagonal coproducts occurring in the total complex, then

  `Φ(Tot(F(K, L))) ≅ Tot(F'(Φ₁ K, Φ₂ L))`. -/
public noncomputable def mapBifunctorTotalIso {I₁₂ : Type*} (c : ComplexShape I₁₂)
    [TotalComplexShape c₁ c₂ c] [DecidableEq I₁₂]
    (hε₁ : ∀ {a a' : A} (f : a ⟶ a') (b : B),
      Φ.map ((F.map f).app b) ≫ (ε a' b).hom =
        (ε a b).hom ≫ (F'.map (Φ₁.map f)).app (Φ₂.obj b))
    (hε₂ : ∀ (a : A) {b b' : B} (g : b ⟶ b'),
      Φ.map ((F.obj a).map g) ≫ (ε a b').hom =
        (ε a b).hom ≫ (F'.obj (Φ₁.obj a)).map (Φ₂.map g))
    (K : HomologicalComplex A c₁) (L : HomologicalComplex B c₂)
    [HomologicalComplex.HasMapBifunctor K L F c]
    [HomologicalComplex.HasMapBifunctor ((Φ₁.mapHomologicalComplex c₁).obj K)
      ((Φ₂.mapHomologicalComplex c₂).obj L) F' c]
    [HomologicalComplex₂.HasTotal (HomologicalComplex₂.mapBicomplex Φ
      (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K).obj L)) c]
    [∀ n : I₁₂, Limits.PreservesColimitsOfShape
      (Discrete ↥(ComplexShape.π c₁ c₂ c ⁻¹' {n})) Φ] :
    (Φ.mapHomologicalComplex c).obj (HomologicalComplex.mapBifunctor K L F c) ≅
      HomologicalComplex.mapBifunctor ((Φ₁.mapHomologicalComplex c₁).obj K)
        ((Φ₂.mapHomologicalComplex c₂).obj L) F' c :=
  (HomologicalComplex₂.totalIso Φ (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K).obj L)).symm
    ≪≫ HomologicalComplex₂.total.mapIso
      (mapBifunctorBicomplexIso F F' Φ₁ Φ₂ Φ ε c₁ c₂ hε₁ hε₂ K L) c

/-! ### The components of `mapBifunctorTotalIso`, and its naturality -/

section Components

variable {I₁₂ : Type*} {c : ComplexShape I₁₂} [TotalComplexShape c₁ c₂ c] [DecidableEq I₁₂]
  (hε₁ : ∀ {a a' : A} (f : a ⟶ a') (b : B),
    Φ.map ((F.map f).app b) ≫ (ε a' b).hom =
      (ε a b).hom ≫ (F'.map (Φ₁.map f)).app (Φ₂.obj b))
  (hε₂ : ∀ (a : A) {b b' : B} (g : b ⟶ b'),
    Φ.map ((F.obj a).map g) ≫ (ε a b').hom =
      (ε a b).hom ≫ (F'.obj (Φ₁.obj a)).map (Φ₂.map g))

omit [Preadditive A] [Preadditive A'] [Preadditive B] [Preadditive D] [Preadditive B']
  [Preadditive D'] [F.PreservesZeroMorphisms]
  [∀ X : A, (F.obj X).PreservesZeroMorphisms] [F'.PreservesZeroMorphisms]
  [∀ X : A', (F'.obj X).PreservesZeroMorphisms] [Φ₁.Additive] [Φ₂.Additive] [Φ.Additive] in
include hε₁ hε₂ in
/-- The two naturality squares of `ε`, combined into one and stated for the inverse of `ε`. -/
@[reassoc]
public lemma mapBifunctorComparison_inv_naturality
    {a a' : A} {b b' : B} (f : a ⟶ a') (g : b ⟶ b') :
    (F'.map (Φ₁.map f)).app (Φ₂.obj b) ≫
        ((F'.obj (Φ₁.obj a')).map (Φ₂.map g) ≫ (ε a' b').inv) =
      (ε a b).inv ≫ Φ.map ((F.map f).app b) ≫ Φ.map ((F.obj a').map g) := by
  have key : Φ.map ((F.map f).app b) ≫ Φ.map ((F.obj a').map g) ≫ (ε a' b').hom =
      (ε a b).hom ≫ (F'.map (Φ₁.map f)).app (Φ₂.obj b) ≫
        (F'.obj (Φ₁.obj a')).map (Φ₂.map g) := by
    rw [hε₂ a' g, ← Category.assoc, hε₁ f b, Category.assoc]
  rw [Iso.eq_inv_comp, ← Category.assoc, ← Category.assoc, Iso.comp_inv_eq, Category.assoc,
    Category.assoc]
  exact key.symm

section Pair

variable (K : HomologicalComplex A c₁) (L : HomologicalComplex B c₂)
  [HomologicalComplex.HasMapBifunctor K L F c]
  [HomologicalComplex.HasMapBifunctor ((Φ₁.mapHomologicalComplex c₁).obj K)
    ((Φ₂.mapHomologicalComplex c₂).obj L) F' c]
  [HomologicalComplex₂.HasTotal (HomologicalComplex₂.mapBicomplex Φ
    (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K).obj L)) c]
  [∀ n : I₁₂, Limits.PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π c₁ c₂ c ⁻¹' {n})) Φ]

/-- On the summand indexed by `(p, q)`, the comparison `mapBifunctorTotalIso` is the degreewise
comparison `ε`. -/
@[reassoc]
public lemma ι_mapBifunctorTotalIso_hom (p : I₁) (q : I₂) (n : I₁₂)
    (h : ComplexShape.π c₁ c₂ c (p, q) = n) :
    Φ.map (HomologicalComplex.ιMapBifunctor K L F c p q n h) ≫
        (mapBifunctorTotalIso F F' Φ₁ Φ₂ Φ ε c₁ c₂ c hε₁ hε₂ K L).hom.f n =
      (ε (K.X p) (L.X q)).hom ≫
        HomologicalComplex.ιMapBifunctor ((Φ₁.mapHomologicalComplex c₁).obj K)
          ((Φ₂.mapHomologicalComplex c₂).obj L) F' c p q n h := by
  have hid : HomologicalComplex₂.totalMapf (c₁₂ := c) Φ
        (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K).obj L) n ≫
      (HomologicalComplex₂.totalIso (c₁₂ := c) Φ
        (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K).obj L)).inv.f n = 𝟙 _ :=
    HomologicalComplex.congr_hom (HomologicalComplex₂.totalIso (c₁₂ := c) Φ
      (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K).obj L)).hom_inv_id n
  have hinv : Φ.map (HomologicalComplex.ιMapBifunctor K L F c p q n h) ≫
      (HomologicalComplex₂.totalIso (c₁₂ := c) Φ
        (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K).obj L)).inv.f n =
      (HomologicalComplex₂.mapBicomplex Φ
        (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K).obj L)).ιTotal c p q n h := by
    change Φ.map ((((F.mapBifunctorHomologicalComplex c₁ c₂).obj K).obj L).ιTotal c p q n h) ≫
      _ = _
    rw [← HomologicalComplex₂.ι_totalMapf Φ
      (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K).obj L) (c₁₂ := c) n p q h,
      Category.assoc, hid, Category.comp_id]
  have hmap : (HomologicalComplex₂.mapBicomplex Φ
        (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K).obj L)).ιTotal c p q n h ≫
      (HomologicalComplex₂.total.map
        (mapBifunctorBicomplexIso F F' Φ₁ Φ₂ Φ ε c₁ c₂ hε₁ hε₂ K L).hom c).f n =
      (ε (K.X p) (L.X q)).hom ≫
        HomologicalComplex.ιMapBifunctor ((Φ₁.mapHomologicalComplex c₁).obj K)
          ((Φ₂.mapHomologicalComplex c₂).obj L) F' c p q n h := by
    rw [HomologicalComplex₂.ιTotal_map]
    rfl
  calc Φ.map (HomologicalComplex.ιMapBifunctor K L F c p q n h) ≫
        (mapBifunctorTotalIso F F' Φ₁ Φ₂ Φ ε c₁ c₂ c hε₁ hε₂ K L).hom.f n
      = (Φ.map (HomologicalComplex.ιMapBifunctor K L F c p q n h) ≫
          (HomologicalComplex₂.totalIso (c₁₂ := c) Φ
            (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K).obj L)).inv.f n) ≫
        (HomologicalComplex₂.total.map
          (mapBifunctorBicomplexIso F F' Φ₁ Φ₂ Φ ε c₁ c₂ hε₁ hε₂ K L).hom c).f n := by
        rw [Category.assoc]; rfl
    _ = (ε (K.X p) (L.X q)).hom ≫
        HomologicalComplex.ιMapBifunctor ((Φ₁.mapHomologicalComplex c₁).obj K)
          ((Φ₂.mapHomologicalComplex c₂).obj L) F' c p q n h := by
        rw [hinv]; exact hmap

/-- On the summand indexed by `(p, q)`, the inverse of `mapBifunctorTotalIso` is the inverse of
the degreewise comparison `ε`. -/
@[reassoc]
public lemma ι_mapBifunctorTotalIso_inv (p : I₁) (q : I₂) (n : I₁₂)
    (h : ComplexShape.π c₁ c₂ c (p, q) = n) :
    HomologicalComplex.ιMapBifunctor ((Φ₁.mapHomologicalComplex c₁).obj K)
        ((Φ₂.mapHomologicalComplex c₂).obj L) F' c p q n h ≫
      (mapBifunctorTotalIso F F' Φ₁ Φ₂ Φ ε c₁ c₂ c hε₁ hε₂ K L).inv.f n =
      (ε (K.X p) (L.X q)).inv ≫
        Φ.map (HomologicalComplex.ιMapBifunctor K L F c p q n h) := by
  have hhom := ι_mapBifunctorTotalIso_hom F F' Φ₁ Φ₂ Φ ε c₁ c₂ hε₁ hε₂ K L p q n h
  have h1 : (ε (K.X p) (L.X q)).inv ≫
      Φ.map (HomologicalComplex.ιMapBifunctor K L F c p q n h) ≫
        (mapBifunctorTotalIso F F' Φ₁ Φ₂ Φ ε c₁ c₂ c hε₁ hε₂ K L).hom.f n =
      HomologicalComplex.ιMapBifunctor ((Φ₁.mapHomologicalComplex c₁).obj K)
        ((Φ₂.mapHomologicalComplex c₂).obj L) F' c p q n h := by
    rw [hhom, Iso.inv_hom_id_assoc]
  rw [← h1, Category.assoc, Category.assoc, ← HomologicalComplex.comp_f, Iso.hom_inv_id]
  simp

end Pair

section Naturality

variable (K K' : HomologicalComplex A c₁) (L L' : HomologicalComplex B c₂)
  [HomologicalComplex.HasMapBifunctor K L F c]
  [HomologicalComplex.HasMapBifunctor K' L' F c]
  [HomologicalComplex.HasMapBifunctor ((Φ₁.mapHomologicalComplex c₁).obj K)
    ((Φ₂.mapHomologicalComplex c₂).obj L) F' c]
  [HomologicalComplex.HasMapBifunctor ((Φ₁.mapHomologicalComplex c₁).obj K')
    ((Φ₂.mapHomologicalComplex c₂).obj L') F' c]
  [HomologicalComplex₂.HasTotal (HomologicalComplex₂.mapBicomplex Φ
    (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K).obj L)) c]
  [HomologicalComplex₂.HasTotal (HomologicalComplex₂.mapBicomplex Φ
    (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K').obj L')) c]
  [∀ n : I₁₂, Limits.PreservesColimitsOfShape
    (Discrete ↥(ComplexShape.π c₁ c₂ c ⁻¹' {n})) Φ]

/-- The inverse of the comparison of total complexes `mapBifunctorTotalIso` is natural in both
complexes. -/
public lemma mapBifunctorTotalIso_inv_naturality (u : K ⟶ K') (v : L ⟶ L') :
    HomologicalComplex.mapBifunctorMap ((Φ₁.mapHomologicalComplex c₁).map u)
        ((Φ₂.mapHomologicalComplex c₂).map v) F' c ≫
      (mapBifunctorTotalIso F F' Φ₁ Φ₂ Φ ε c₁ c₂ c hε₁ hε₂ K' L').inv =
    (mapBifunctorTotalIso F F' Φ₁ Φ₂ Φ ε c₁ c₂ c hε₁ hε₂ K L).inv ≫
      (Φ.mapHomologicalComplex c).map (HomologicalComplex.mapBifunctorMap u v F c) := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f]
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  dsimp only [Functor.mapHomologicalComplex_map_f, Functor.mapHomologicalComplex_obj_X]
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc,
    ι_mapBifunctorTotalIso_inv F F' Φ₁ Φ₂ Φ ε c₁ c₂ hε₁ hε₂ K' L' p q n hpq,
    ι_mapBifunctorTotalIso_inv_assoc F F' Φ₁ Φ₂ Φ ε c₁ c₂ hε₁ hε₂ K L p q n hpq,
    ← Functor.map_comp, HomologicalComplex.ι_mapBifunctorMap, Functor.map_comp, Functor.map_comp]
  dsimp only [Functor.mapHomologicalComplex_map_f, Functor.mapHomologicalComplex_obj_X]
  exact mapBifunctorComparison_inv_naturality_assoc F F' Φ₁ Φ₂ Φ ε hε₁ hε₂ (u.f p) (v.f q) _

/-- The comparison of total complexes `mapBifunctorTotalIso` is natural in both complexes. -/
public lemma mapBifunctorTotalIso_hom_naturality (u : K ⟶ K') (v : L ⟶ L') :
    (Φ.mapHomologicalComplex c).map (HomologicalComplex.mapBifunctorMap u v F c) ≫
        (mapBifunctorTotalIso F F' Φ₁ Φ₂ Φ ε c₁ c₂ c hε₁ hε₂ K' L').hom =
      (mapBifunctorTotalIso F F' Φ₁ Φ₂ Φ ε c₁ c₂ c hε₁ hε₂ K L).hom ≫
        HomologicalComplex.mapBifunctorMap ((Φ₁.mapHomologicalComplex c₁).map u)
          ((Φ₂.mapHomologicalComplex c₂).map v) F' c := by
  have h := mapBifunctorTotalIso_inv_naturality F F' Φ₁ Φ₂ Φ ε c₁ c₂ (c := c) hε₁ hε₂
    K K' L L' u v
  rw [Iso.comp_inv_eq] at h
  rw [h, Category.assoc, ← Category.assoc
    (mapBifunctorTotalIso F F' Φ₁ Φ₂ Φ ε c₁ c₂ c hε₁ hε₂ K L).hom,
    Iso.hom_inv_id, Category.id_comp]

end Naturality

end Components

end CategoryTheory.Functor

end
