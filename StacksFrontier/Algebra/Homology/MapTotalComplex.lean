module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.TotalComplex
public import StacksCore.Tactic.StacksAttribute

/-!
# An additive functor applied to the total complex of a bicomplex

Let `G : C ⥤ D` be an additive functor between preadditive categories and let `K` be a
bicomplex of `C` indexed by `(c₁, c₂)`, with a total complex for the total complex shape
`c₁₂`. Applying `G` termwise gives a bicomplex `G(K)` of `D`, and whenever that bicomplex too
has a total complex there is a canonical morphism of complexes

```
Tot(G(K)) ⟶ G(Tot(K))
```

(`HomologicalComplex₂.TotalMap.totalMap`), namely the one whose restriction to the summand of
bidegree `(i₁, i₂)` is `G` applied to the inclusion of that summand in `Tot(K)`. This module
constructs that morphism and gives two sufficient conditions for it to be an isomorphism.

The general criterion is `isIso_totalMapf_of_isColimit`: the comparison is invertible in total
degree `n` as soon as `G` carries the coproduct decomposition of `Tot(K)^n` to a coproduct
decomposition. In particular it is invertible in degree `n` when `G` preserves coproducts indexed
by `ComplexShape.π c₁ c₂ c₁₂ ⁻¹' {n}` (`isIso_totalMapf`), with no finiteness hypothesis on `K`, so
that `totalIso` applies to unbounded bicomplexes.

## Main definitions

* `HomologicalComplex₂.TotalMap.mapBicomplex`: the bicomplex `G(K)`.
* `HomologicalComplex₂.TotalMap.totalMapf`: the comparison morphism in one total degree.
* `HomologicalComplex₂.TotalMap.totalMap`: the comparison morphism of complexes.
* `HomologicalComplex₂.TotalMap.totalIsoOfIsIso`: the induced isomorphism, from degreewise
  invertibility.
* `HomologicalComplex₂.TotalMap.totalIso`: **an additive functor preserving coproducts
  commutes with the total complex**, `Tot(G(K)) ≅ G(Tot(K))`.

## Main results

* `HomologicalComplex₂.TotalMap.isIso_totalMapf_of_isColimit`: the general invertibility
  criterion.
* `HomologicalComplex₂.TotalMap.isIso_totalMapf`: invertibility under preservation of the
  relevant coproduct.
* `HomologicalComplex₂.TotalMap.totalMap_naturality`,
  `HomologicalComplex₂.TotalMap.totalIso_naturality`: naturality in the bicomplex.
* `HomologicalComplex₂.TotalMap.totalMap_naturality_functor`: naturality in the functor.

## Implementation notes

The hypothesis of `isIso_totalMapf_of_isColimit` is spelled as a colimit cofan on the family
of inclusions `G(ι_{i₁, i₂})`, which is the shape returned by
`CategoryTheory.Limits.Cofan.isColimitMapCoconeEquiv` composed with `isColimitOfPreserves`.

The coproduct hypothesis is taken per total degree,
`PreservesColimitsOfShape (Discrete ↥(ComplexShape.π c₁ c₂ c₁₂ ⁻¹' {n})) G`, rather than as
`PreservesColimitsOfSize`, because that is the weakest form and the stronger ones imply it by
instance resolution.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace HomologicalComplex₂.TotalMap

universe v v' u u' i₁ i₂ i₁₂

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Preadditive C] [Preadditive D]
  {I₁ : Type i₁} {I₂ : Type i₂} {I₁₂ : Type i₁₂}
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c₁₂ : ComplexShape I₁₂}
  [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]
  (G : C ⥤ D) [G.Additive] (K : HomologicalComplex₂ C c₁ c₂)

/-- `G(K)`, the bicomplex obtained by applying an additive functor `G` to each term of a
bicomplex `K`. -/
abbrev mapBicomplex : HomologicalComplex₂ D c₁ c₂ :=
  ((G.mapHomologicalComplex c₂).mapHomologicalComplex c₁).obj K

variable [K.HasTotal c₁₂]
  [HomologicalComplex₂.HasTotal
    (((G.mapHomologicalComplex c₂).mapHomologicalComplex c₁).obj K) c₁₂]

/-- The canonical morphism `Tot(G(K))^n ⟶ G(Tot(K)^n)`, induced by the `G(ι_{i₁, i₂})`. -/
def totalMapf (n : I₁₂) :
    ((mapBicomplex G K).total c₁₂).X n ⟶ G.obj ((K.total c₁₂).X n) :=
  (mapBicomplex G K).totalDesc (fun i₁ i₂ h => G.map (K.ιTotal c₁₂ i₁ i₂ n h))

/-- The comparison morphism `totalMapf` restricted to the summand of bidegree `(i₁, i₂)` is
`G` applied to the inclusion of that summand in `Tot(K)^n`. -/
@[reassoc]
lemma ι_totalMapf (n : I₁₂) (i₁ : I₁) (i₂ : I₂)
    (h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = n) :
    (mapBicomplex G K).ιTotal c₁₂ i₁ i₂ n h ≫ totalMapf G K n =
      G.map (K.ιTotal c₁₂ i₁ i₂ n h) := by
  simp [totalMapf]

/-- The variant of `ι_totalMapf` for `ιTotalOrZero`. -/
lemma ιOrZero_totalMapf (n : I₁₂) (i₁ : I₁) (i₂ : I₂) :
    (mapBicomplex G K).ιTotalOrZero c₁₂ i₁ i₂ n ≫ totalMapf G K n =
      G.map (K.ιTotalOrZero c₁₂ i₁ i₂ n) := by
  by_cases h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = n
  · rw [HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ h,
      HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ h, ι_totalMapf]
  · rw [HomologicalComplex₂.ιTotalOrZero_eq_zero _ _ _ _ _ h,
      HomologicalComplex₂.ιTotalOrZero_eq_zero _ _ _ _ _ h, zero_comp, G.map_zero]

/-- The comparison morphism is compatible with the first differential of the bicomplex. -/
lemma d₁_totalMapf (i₁ : I₁) (i₂ : I₂) (n : I₁₂) :
    (mapBicomplex G K).d₁ c₁₂ i₁ i₂ n ≫ totalMapf G K n = G.map (K.d₁ c₁₂ i₁ i₂ n) := by
  by_cases h : c₁.Rel i₁ (c₁.next i₁)
  · rw [HomologicalComplex₂.d₁_eq' _ _ h, HomologicalComplex₂.d₁_eq' _ _ h,
      Units.smul_def, Units.smul_def, G.map_zsmul, Linear.smul_comp]
    congr 1
    rw [Category.assoc, ιOrZero_totalMapf, G.map_comp]
    rfl
  · rw [HomologicalComplex₂.d₁_eq_zero _ _ _ _ _ h,
      HomologicalComplex₂.d₁_eq_zero _ _ _ _ _ h, zero_comp, G.map_zero]

/-- The comparison morphism is compatible with the second differential of the bicomplex. -/
lemma d₂_totalMapf (i₁ : I₁) (i₂ : I₂) (n : I₁₂) :
    (mapBicomplex G K).d₂ c₁₂ i₁ i₂ n ≫ totalMapf G K n = G.map (K.d₂ c₁₂ i₁ i₂ n) := by
  by_cases h : c₂.Rel i₂ (c₂.next i₂)
  · rw [HomologicalComplex₂.d₂_eq' _ _ _ h, HomologicalComplex₂.d₂_eq' _ _ _ h,
      Units.smul_def, Units.smul_def, G.map_zsmul, Linear.smul_comp]
    congr 1
    rw [Category.assoc, ιOrZero_totalMapf, G.map_comp]
    rfl
  · rw [HomologicalComplex₂.d₂_eq_zero _ _ _ _ _ h,
      HomologicalComplex₂.d₂_eq_zero _ _ _ _ _ h, zero_comp, G.map_zero]

/-- The maps `Tot(G(K))^n ⟶ G(Tot(K)^n)` commute with the differentials. -/
lemma d_totalMapf (n n' : I₁₂) :
    ((mapBicomplex G K).total c₁₂).d n n' ≫ totalMapf G K n' =
      totalMapf G K n ≫ G.map ((K.total c₁₂).d n n') := by
  refine HomologicalComplex₂.total.hom_ext c₁₂ (fun i₁ i₂ h => ?_)
  rw [← Category.assoc, ← Category.assoc, HomologicalComplex₂.total_d, Preadditive.comp_add,
    HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂, Preadditive.add_comp, d₁_totalMapf,
    d₂_totalMapf, ι_totalMapf, ← G.map_comp, HomologicalComplex₂.total_d, Preadditive.comp_add,
    HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂, G.map_add]

/-- The canonical morphism of complexes `Tot(G(K)) ⟶ G(Tot(K))`. -/
def totalMap :
    (mapBicomplex G K).total c₁₂ ⟶ (G.mapHomologicalComplex c₁₂).obj (K.total c₁₂) where
  f n := totalMapf G K n
  comm' n n' _ := by
    rw [Functor.mapHomologicalComplex_obj_d]
    exact (d_totalMapf G K n n').symm

/-- **The general invertibility criterion for the comparison `Tot(G(K))^n ⟶ G(Tot(K)^n)`**: it
is an isomorphism as soon as `G` carries the coproduct decomposition of `Tot(K)^n` into the
summands of total degree `n` to a coproduct decomposition of `G(Tot(K)^n)`. -/
lemma isIso_totalMapf_of_isColimit (n : I₁₂)
    (hc : IsColimit (Cofan.mk (G.obj ((K.total c₁₂).X n))
      (fun i : ↥(ComplexShape.π c₁ c₂ c₁₂ ⁻¹' {n}) =>
        G.map (K.ιTotal c₁₂ i.1.1 i.1.2 n i.2)))) :
    IsIso (totalMapf (c₁₂ := c₁₂) G K n) := by
  refine ⟨Cofan.IsColimit.desc hc fun i => (mapBicomplex G K).ιTotal c₁₂ i.1.1 i.1.2 n i.2,
    ?_, ?_⟩
  · refine HomologicalComplex₂.total.hom_ext c₁₂ (fun i₁ i₂ h => ?_)
    rw [Category.comp_id, ι_totalMapf_assoc]
    exact Cofan.IsColimit.fac hc _ ⟨(i₁, i₂), h⟩
  · refine Cofan.IsColimit.hom_ext hc _ _ (fun i => ?_)
    rw [Cofan.IsColimit.fac_assoc]
    exact (ι_totalMapf G K n _ _ i.2).trans (Category.comp_id _).symm

/-- **Preservation of the coproduct in one total degree makes the comparison invertible**
there. No finiteness hypothesis on `K` is needed. -/
lemma isIso_totalMapf (n : I₁₂)
    [PreservesColimitsOfShape (Discrete ↥(ComplexShape.π c₁ c₂ c₁₂ ⁻¹' {n})) G] :
    IsIso (totalMapf (c₁₂ := c₁₂) G K n) :=
  isIso_totalMapf_of_isColimit G K n
    (Cofan.isColimitMapCoconeEquiv G _ _
      (isColimitOfPreserves G
        (K.toGradedObject.isColimitCofanMapObj (ComplexShape.π c₁ c₂ c₁₂) n)))

/-- A degreewise invertible comparison assembles into an isomorphism of complexes
`Tot(G(K)) ≅ G(Tot(K))`. -/
def totalIsoOfIsIso (h : ∀ n, IsIso (totalMapf (c₁₂ := c₁₂) G K n)) :
    (mapBicomplex G K).total c₁₂ ≅ (G.mapHomologicalComplex c₁₂).obj (K.total c₁₂) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => @asIso _ _ _ _ (totalMapf (c₁₂ := c₁₂) G K n) (h n))
    (fun n n' _ => (totalMap G K).comm n n')

/-- **An additive functor preserving coproducts commutes with the total complex of a
bicomplex**: `Tot(G(K)) ≅ G(Tot(K))`. There is no finiteness hypothesis on `K`, so this
applies to unbounded bicomplexes. -/
def totalIso
    [∀ n : I₁₂, PreservesColimitsOfShape
      (Discrete ↥(ComplexShape.π c₁ c₂ c₁₂ ⁻¹' {n})) G] :
    (mapBicomplex G K).total c₁₂ ≅ (G.mapHomologicalComplex c₁₂).obj (K.total c₁₂) :=
  totalIsoOfIsIso G K (fun n => isIso_totalMapf G K n)

/-- The forward direction of `totalIsoOfIsIso` is `totalMap`. -/
theorem totalIsoOfIsIso_hom_eq_totalMap (h : ∀ n, IsIso (totalMapf (c₁₂ := c₁₂) G K n)) :
    (totalIsoOfIsIso (c₁₂ := c₁₂) G K h).hom = totalMap G K := rfl

/-- The forward direction of `totalIso` is `totalMap`. -/
theorem totalIso_hom_eq_totalMap
    [∀ n : I₁₂, PreservesColimitsOfShape
      (Discrete ↥(ComplexShape.π c₁ c₂ c₁₂ ⁻¹' {n})) G] :
    (totalIso (c₁₂ := c₁₂) G K).hom = totalMap G K := rfl

/-- A summand inclusion followed by the map induced by a morphism of bicomplexes
`φ : G(K) ⟶ G'(L)` and then by `totalMapf` is `φ` followed by `G'` applied to the inclusion. -/
private lemma ιTotal_total_map_totalMapf {G' : C ⥤ D} [G'.Additive]
    {K₁ L : HomologicalComplex₂ C c₁ c₂} [L.HasTotal c₁₂] [(mapBicomplex G K₁).HasTotal c₁₂]
    [(mapBicomplex G' L).HasTotal c₁₂]
    (φ : mapBicomplex G K₁ ⟶ mapBicomplex G' L) (n : I₁₂) (i₁ : I₁) (i₂ : I₂)
    (h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = n) :
    (mapBicomplex G K₁).ιTotal c₁₂ i₁ i₂ n h ≫
      (HomologicalComplex₂.total.map φ c₁₂).f n ≫ totalMapf G' L n =
    (φ.f i₁).f i₂ ≫ G'.map (L.ιTotal c₁₂ i₁ i₂ n h) := by
  rw [← Category.assoc, HomologicalComplex₂.ιTotal_map, Category.assoc, ι_totalMapf]

/-- The comparison morphism is natural in the bicomplex. -/
theorem totalMap_naturality
    {L : HomologicalComplex₂ C c₁ c₂} [L.HasTotal c₁₂]
    [HomologicalComplex₂.HasTotal
      (((G.mapHomologicalComplex c₂).mapHomologicalComplex c₁).obj L) c₁₂]
    (f : K ⟶ L) :
    HomologicalComplex₂.total.map
        (((G.mapHomologicalComplex c₂).mapHomologicalComplex c₁).map f) c₁₂ ≫
      totalMap G L = totalMap G K ≫
        (G.mapHomologicalComplex c₁₂).map (HomologicalComplex₂.total.map f c₁₂) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex₂.total.hom_ext c₁₂
  intro i₁ i₂ h
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  erw [ιTotal_total_map_totalMapf, ← Category.assoc, ι_totalMapf]
  simp only [Functor.mapHomologicalComplex_map_f, ← G.map_comp, HomologicalComplex₂.ιTotal_map]

/-- The totalization comparison isomorphism is natural in the bicomplex. -/
lemma totalIso_naturality
    [∀ n : I₁₂, PreservesColimitsOfShape
      (Discrete ↥(ComplexShape.π c₁ c₂ c₁₂ ⁻¹' {n})) G]
    {L : HomologicalComplex₂ C c₁ c₂} [L.HasTotal c₁₂]
    [(mapBicomplex G L).HasTotal c₁₂] (f : K ⟶ L) :
    (totalIso G K).hom ≫ (G.mapHomologicalComplex c₁₂).map
        (HomologicalComplex₂.total.map f c₁₂) =
      HomologicalComplex₂.total.map
        (((G.mapHomologicalComplex c₂).mapHomologicalComplex c₁).map f) c₁₂ ≫
          (totalIso G L).hom :=
  (totalMap_naturality G K f).symm

/-- **The comparison morphism is natural in the functor.** A natural transformation `α : G ⟶ G'`
induces a morphism of bicomplexes `G(K) ⟶ G'(K)`, and the square relating the two comparisons
`Tot(G(K)) ⟶ G(Tot(K))` and `Tot(G'(K)) ⟶ G'(Tot(K))` commutes. -/
theorem totalMap_naturality_functor {G' : C ⥤ D} [G'.Additive] (α : G ⟶ G')
    [(mapBicomplex G' K).HasTotal c₁₂] :
    HomologicalComplex₂.total.map
        ((NatTrans.mapHomologicalComplex (NatTrans.mapHomologicalComplex α c₂) c₁).app K) c₁₂ ≫
      totalMap G' K =
    totalMap G K ≫ (NatTrans.mapHomologicalComplex α c₁₂).app (K.total c₁₂) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex₂.total.hom_ext c₁₂
  intro i₁ i₂ h
  show (mapBicomplex G K).ιTotal c₁₂ i₁ i₂ n h ≫
      ((HomologicalComplex₂.total.map _ c₁₂).f n ≫ totalMapf G' K n) =
    (mapBicomplex G K).ιTotal c₁₂ i₁ i₂ n h ≫
      (totalMapf G K n ≫ α.app ((K.total c₁₂).X n))
  rw [ιTotal_total_map_totalMapf, ← Category.assoc, ι_totalMapf]
  exact (α.naturality (K.ιTotal c₁₂ i₁ i₂ n h)).symm

end HomologicalComplex₂.TotalMap
