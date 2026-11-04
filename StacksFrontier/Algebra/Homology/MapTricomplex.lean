module

public import StacksCore.Algebra.Homology.HomologicalTricomplex.Total12
public import StacksFrontier.Algebra.Homology.TotalComplexFiniteSupport

/-!
# An additive functor applied to a tricomplex

Let `G : C ⥤ D` be an additive functor between preadditive categories and let
`K : HomologicalComplex₃ C c₁ c₂ c₃` be a tricomplex of `C`. Applying `G` to each term gives a
tricomplex `G(K)` of `D` (`HomologicalComplex₃.mapTricomplex`), whose slices and whose third
differential are `G` applied to those of `K`. Integrating the first two indices against a total
complex shape `c₁₂` produces two bicomplexes of `HomologicalComplex₂ D c₁₂ c₃`, namely
`Tot₁₂(G(K))` and `G(Tot₁₂(K))`, together with a canonical morphism

```
Tot₁₂(G(K)) ⟶ G(Tot₁₂(K))
```

between them (`HomologicalComplex₃.int₁₂Map`): the one whose row `i₃` is the comparison
`Tot(G(K^{•,•,i₃})) ⟶ G(Tot(K^{•,•,i₃}))` of
`StacksFrontier.Algebra.Homology.MapTotalComplex` for the slice of `K` at `i₃`. It is an
isomorphism as soon as every slice has, in each total degree, only finitely many nonzero terms
(`HomologicalComplex₃.int₁₂Iso`); no preservation of coproducts by `G` is needed.

Also recorded are the two criteria which produce the hypotheses `HomologicalComplex₃.HasInt₁₂`
and `HomologicalComplex₃.HasTotal₁₂` from finiteness of the antidiagonals of `K`, so that a
tricomplex with finite support in each degree has both partial and total integrations as soon as
`C` has finite coproducts.

## Main definitions

* `HomologicalComplex₃.mapTricomplex`: the tricomplex `G(K)`.
* `HomologicalComplex₃.int₁₂Map`: the comparison morphism `Tot₁₂(G(K)) ⟶ G(Tot₁₂(K))`.
* `HomologicalComplex₃.int₁₂IsoOfIsIso`: the induced isomorphism, from invertibility in each
  bidegree.
* `HomologicalComplex₃.int₁₂Iso`: **an additive functor commutes with the integration of the
  first two indices of a tricomplex with finite support**, `Tot₁₂(G(K)) ≅ G(Tot₁₂(K))`.

## Main results

* `HomologicalComplex₃.hasInt₁₂_of_finite`, `HomologicalComplex₃.hasTotal₁₂_of_finite`: a
  tricomplex with finitely many nonzero terms on each antidiagonal can be integrated in the
  first two indices, and the resulting bicomplex has a total complex.
* `HomologicalComplex₃.isIso_int₁₂Map`: invertibility of the comparison in each bidegree makes
  it an isomorphism of bicomplexes.

## Implementation notes

`HomologicalComplex₃.int₁₂` is built termwise from the slices `K.X' i₃` rather than as a total
complex over the category of complexes, so the comparison is not an instance of
`HomologicalComplex₂.TotalMap.totalIso`; it is assembled from the slices instead. Its two
commutation squares are exactly the naturality of `HomologicalComplex₂.TotalMap.totalMap` in the
bicomplex, applied to the third differential of `K`, and its compatibility with the differential
of the total complex.

The slices of `G(K)` are *definitionally* `G` applied to the slices of `K`
(`HomologicalComplex₃.mapTricomplex_X'`), which is what lets the comparison for a slice be used
as a row of a morphism of bicomplexes; the instance `HomologicalComplex₃.hasTotal_mapBicomplex_X'`
transports the hypothesis `HasInt₁₂` for `G(K)` across that identification. It cannot loop with
the hypothesis it consumes: the two spellings of a slice have different heads once reducible
unfolding has been done, so neither matches the other's instance key.

## References

* [Stacks Project, Tag 08BI](https://stacks.math.columbia.edu/tag/08BI)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

namespace HomologicalComplex₃

variable {C : Type*} {D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  {I₁ I₂ I₃ I₁₂ J : Type*}
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c₃ : ComplexShape I₃}

/-- `G(K)`, the tricomplex obtained by applying an additive functor `G` to each term of a
tricomplex `K`. -/
abbrev mapTricomplex (G : C ⥤ D) [G.Additive] (K : HomologicalComplex₃ C c₁ c₂ c₃) :
    HomologicalComplex₃ D c₁ c₂ c₃ :=
  (((G.mapHomologicalComplex c₃).mapHomologicalComplex c₂).mapHomologicalComplex c₁).obj K

variable (G : C ⥤ D) [G.Additive] (K : HomologicalComplex₃ C c₁ c₂ c₃)

/-- The slice of `G(K)` at `i₃` is `G` applied to the slice of `K` at `i₃`. -/
lemma mapTricomplex_X' (i₃ : I₃) :
    (mapTricomplex G K).X' i₃ = HomologicalComplex₂.TotalMap.mapBicomplex G (K.X' i₃) :=
  rfl

/-- The third differential of `G(K)` is `G` applied to the third differential of `K`. -/
lemma mapTricomplex_d' (i₃ i₃' : I₃) :
    (mapTricomplex G K).d' i₃ i₃' =
      ((G.mapHomologicalComplex c₂).mapHomologicalComplex c₁).map (K.d' i₃ i₃') :=
  rfl

section

variable (c₁₂ : ComplexShape I₁₂) [TotalComplexShape c₁ c₂ c₁₂]

/-- A tricomplex with, in each total degree of the first two indices, only finitely many nonzero
terms can be integrated in those two indices: the coproducts defining the total complexes of its
slices are finite. -/
lemma hasInt₁₂_of_finite [HasFiniteCoproducts C]
    (h : ∀ (i₃ : I₃) (i₁₂ : I₁₂), {p : I₁ × I₂ | ComplexShape.π c₁ c₂ c₁₂ p = i₁₂ ∧
      ¬ IsZero (((K.X p.1).X p.2).X i₃)}.Finite) :
    K.HasInt₁₂ c₁₂ :=
  fun i₃ => HomologicalComplex₂.hasTotal_of_finite _ _ (h i₃)

section

variable [(mapTricomplex G K).HasInt₁₂ c₁₂]

/-- The slice of `G(K)` at `i₃` being `G` applied to the slice of `K` at `i₃`, the hypothesis
`HasInt₁₂` for `G(K)` is the existence of the coproducts defining `Tot(G(K^{•,•,i₃}))`, which is
what the comparison with `G(Tot(K^{•,•,i₃}))` needs. -/
instance hasTotal_mapBicomplex_X' (i₃ : I₃) :
    (HomologicalComplex₂.TotalMap.mapBicomplex G (K.X' i₃)).HasTotal c₁₂ :=
  inferInstanceAs (((mapTricomplex G K).X' i₃).HasTotal c₁₂)

end

variable [DecidableEq I₁₂] [K.HasInt₁₂ c₁₂]

/-- A tricomplex with finitely many nonzero terms on each antidiagonal of the target shape `c`
has a total complex formed by integrating the first two indices first: a term of `Tot₁₂(K)` all
of whose summands vanish is itself zero, so the coproducts defining the second total complex are
finite as well. -/
lemma hasTotal₁₂_of_finite [HasFiniteCoproducts C] (c : ComplexShape J)
    [TotalComplexShape c₁₂ c₃ c]
    (h : ∀ j : J, {t : I₁₂ × I₃ | ComplexShape.π c₁₂ c₃ c t = j ∧
      ∃ p : I₁ × I₂, ComplexShape.π c₁ c₂ c₁₂ p = t.1 ∧
        ¬ IsZero (((K.X p.1).X p.2).X t.2)}.Finite) :
    K.HasTotal₁₂ c₁₂ c := by
  refine HomologicalComplex₂.hasTotal_of_finite _ _ (fun j => (h j).subset ?_)
  rintro ⟨i₁₂, i₃⟩ ⟨hj, hz⟩
  refine ⟨hj, ?_⟩
  by_contra hcon
  exact hz (HomologicalComplex₂.isZero_total_X_of_isZero (K.X' i₃) c₁₂ i₁₂
    (fun i₁ i₂ hp => not_not.1 (fun hnz => hcon ⟨(i₁, i₂), hp, hnz⟩)))

variable [(mapTricomplex G K).HasInt₁₂ c₁₂]

/-- **The comparison morphism `Tot₁₂(G(K)) ⟶ G(Tot₁₂(K))`**, whose row `i₃` is the comparison
`HomologicalComplex₂.TotalMap.totalMap` for the slice of `K` at `i₃`. -/
def int₁₂Map : (mapTricomplex G K).int₁₂ c₁₂ ⟶
    HomologicalComplex₂.TotalMap.mapBicomplex G (K.int₁₂ c₁₂) where
  f i₁₂ :=
    { f := fun i₃ => HomologicalComplex₂.TotalMap.totalMapf (c₁₂ := c₁₂) G (K.X' i₃) i₁₂
      comm' := fun i₃ i₃' _ => (HomologicalComplex.congr_hom
        (HomologicalComplex₂.TotalMap.totalMap_naturality (c₁₂ := c₁₂) G (K.X' i₃)
          (K.d' i₃ i₃')) i₁₂).symm }
  comm' i₁₂ i₁₂' _ := HomologicalComplex.hom_ext _ _ (fun i₃ =>
    (HomologicalComplex₂.TotalMap.d_totalMapf (c₁₂ := c₁₂) G (K.X' i₃) i₁₂ i₁₂').symm)

/-- A comparison morphism invertible in each bidegree is an isomorphism of bicomplexes: a
morphism of bicomplexes is invertible as soon as all its components are. -/
lemma isIso_int₁₂Map
    (h : ∀ (i₁₂ : I₁₂) (i₃ : I₃), IsIso (((int₁₂Map G K c₁₂).f i₁₂).f i₃)) :
    IsIso (int₁₂Map G K c₁₂) := by
  have : ∀ i₁₂ : I₁₂, IsIso ((int₁₂Map G K c₁₂).f i₁₂) := by
    intro i₁₂
    have : ∀ i₃ : I₃, IsIso (((int₁₂Map G K c₁₂).f i₁₂).f i₃) := h i₁₂
    exact HomologicalComplex.Hom.isIso_of_components _
  exact HomologicalComplex.Hom.isIso_of_components _

/-- A comparison morphism invertible in each bidegree, as an isomorphism
`Tot₁₂(G(K)) ≅ G(Tot₁₂(K))`. -/
def int₁₂IsoOfIsIso (h : ∀ (i₁₂ : I₁₂) (i₃ : I₃), IsIso (((int₁₂Map G K c₁₂).f i₁₂).f i₃)) :
    (mapTricomplex G K).int₁₂ c₁₂ ≅
      HomologicalComplex₂.TotalMap.mapBicomplex G (K.int₁₂ c₁₂) :=
  @asIso _ _ _ _ (int₁₂Map G K c₁₂) (isIso_int₁₂Map G K c₁₂ h)

/-- **An additive functor commutes with the integration of the first two indices of a
tricomplex** whose slices have, in each total degree, only finitely many nonzero terms:
`Tot₁₂(G(K)) ≅ G(Tot₁₂(K))`. The finiteness makes each coproduct defining `Tot₁₂(K)` a finite
biproduct, which every additive functor preserves, so no preservation of coproducts by `G` is
assumed. -/
def int₁₂Iso
    (hfin : ∀ (i₃ : I₃) (i₁₂ : I₁₂), {p : I₁ × I₂ | ComplexShape.π c₁ c₂ c₁₂ p = i₁₂ ∧
      ¬ IsZero (((K.X p.1).X p.2).X i₃)}.Finite) :
    (mapTricomplex G K).int₁₂ c₁₂ ≅
      HomologicalComplex₂.TotalMap.mapBicomplex G (K.int₁₂ c₁₂) :=
  int₁₂IsoOfIsIso G K c₁₂ (fun i₁₂ i₃ =>
    HomologicalComplex₂.TotalMap.isIso_totalMapf_of_finite (c₁₂ := c₁₂) G (K.X' i₃) i₁₂
      (hfin i₃ i₁₂))

/-- The forward direction of `int₁₂IsoOfIsIso` is `int₁₂Map`. -/
theorem int₁₂IsoOfIsIso_hom_eq_int₁₂Map
    (h : ∀ (i₁₂ : I₁₂) (i₃ : I₃), IsIso (((int₁₂Map G K c₁₂).f i₁₂).f i₃)) :
    (int₁₂IsoOfIsIso G K c₁₂ h).hom = int₁₂Map G K c₁₂ :=
  rfl

end

end HomologicalComplex₃

end
