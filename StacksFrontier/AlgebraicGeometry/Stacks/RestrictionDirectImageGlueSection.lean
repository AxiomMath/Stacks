module

public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionDirectImageChartRefinement
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionDirectImageComparisonInjective

/-!
# Gluing a section of `f_*ℱ` from a compatible family over the chart diagrams

Fix an étale scheme chart `V` of `G` and a family of sections of `ℱ`, one over the object `u_F W`
of `𝒳` attached to each diagram of étale scheme charts over `V`, compatible in the sense of
`AlgebraicGeometry.Space.fMap_app_congr_of_comparisonChartHom_eq`: two morphisms of `𝒳` into two
of those objects which agree over `u_G V` restrict the two sections to the same section.

This file glues that family to a value at **every** pair `(Z, κ : f(Z) ⟶ u_G V)`, and that is
what produces a section of `f_*ℱ` over `u_G V`: by the dictionary between the objects of the
2-fibre product and the pairs (`AlgebraicGeometry.Space.twoFibreProductMk`,
`AlgebraicGeometry.Space.twoFibreProductArrow_comp`) the values at the pairs are the components
of a global section over the 2-fibre product of equation 075M, which is the sections of `f_*ℱ`
over `u_G V` by Stacks 06W6.

The gluing is the only place where the sheaf condition on `ℱ` is used. The sieve it is applied to
is the sieve of morphisms into `Z` along which the morphism into `u_G V` factors through the
image of an étale chart of `F`; it is covering because the objects coming from étale charts of `F`
cover the final object of the inherited étale site (Stacks 073M) and because of the factorization
lemma `AlgebraicGeometry.Space.exists_chartDiagram_comparisonChartHom_factor`.

## Main definitions

* `AlgebraicGeometry.Space.chartFactorSieve`: the sieve of morphisms into `Z` along which `κ`
  factors through the image of an étale scheme chart of `F`.
* `AlgebraicGeometry.Space.glueSection`: the glued value of the family at a pair `(Z, κ)`.

## Main results

* `AlgebraicGeometry.Space.chartFactorSieve_mem`: the sieve is covering.
* `AlgebraicGeometry.Space.glueSection_map`: the glued values are compatible with precomposition,
  which is what makes them the components of a global section over the 2-fibre product.
* `AlgebraicGeometry.Space.glueSection_chart`: at a pair coming from a chart diagram the glued
  value is the given section.

## References

* [Stacks Project, Tag 075M](https://stacks.math.columbia.edu/tag/075M)
* [Stacks Project, Tag 073M](https://stacks.math.columbia.edu/tag/073M)
* [Stacks Project, Tag 06W6](https://stacks.math.columbia.edu/tag/06W6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u v w v' w'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
  (eF : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (F ⋙ typeToCat)).p)
  (eG : StacksRepresentableCFG.EquivalenceOver q
    (presheafOfCategories (G ⋙ typeToCat)).p)
  (f : 𝒳 ⥤ 𝒴)
  (fSpace : (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩)
  (ha : schemeChartFunctor B S hS F p eF ⋙ f ≅
    CostructuredArrow.map fSpace.hom ⋙ schemeChartFunctor B S hS G q eG)
  (V : SmallEtale B S hS G)
  (ℱ : Sheaf (BigFppfOver.associatedTopology B S hS p .etale) (Type u))

/-! ### The sieve along which the family can be read -/

/-- The image under the 1-morphism of a composite, followed by a morphism of `𝒴`. -/
private theorem map_comp_assoc {A C D : 𝒳} {T : 𝒴} (g : A ⟶ C) (m : C ⟶ D)
    (κ : f.obj D ⟶ T) : f.map (g ≫ m) ≫ κ = f.map g ≫ (f.map m ≫ κ) := by
  rw [f.map_comp, Category.assoc]

/-- The sieve of morphisms `m` into an object `Z` of `𝒳` such that `f(m)` followed by a given
morphism `κ : f(Z) ⟶ u_G V` factors through the morphism `f(u_F W) ⟶ u_G V` of a diagram of
étale scheme charts over `V`.

This is a sieve because such a factorization of `f(m) ≫ κ` is one of `f(k ≫ m) ≫ κ` after
precomposition with `f(k)`. -/
def chartFactorSieve (Z : 𝒳) (κ : f.obj Z ⟶ (restrictionFunctor B S hS G q eG).obj V) :
    Sieve Z where
  arrows Z' m := ∃ (W : SmallEtale B S hS F)
    (ζ : (CostructuredArrow.map fSpace.hom).obj W.1 ⟶ V.1)
    (m' : Z' ⟶ (restrictionFunctor B S hS F p eF).obj W),
    f.map m' ≫ comparisonChartHom B S hS p q eF eG f fSpace ha
        (chartDiagramOfChartHom B S hS F G hF hG fSpace V W ζ) = f.map m ≫ κ
  downward_closed := by
    rintro Z' Z'' m ⟨W, ζ, m', hm'⟩ k
    refine ⟨W, ζ, k ≫ m', ?_⟩
    refine Eq.trans (congrArg (fun z ↦ z ≫ comparisonChartHom B S hS p q eF eG f fSpace ha
      (chartDiagramOfChartHom B S hS F G hF hG fSpace V W ζ)) (f.map_comp k m')) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (fun z ↦ f.map k ≫ z) hm') ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    exact congrArg (fun z ↦ z ≫ κ) (f.map_comp k m).symm

include hp hF in
/-- **The sieve is covering.** The objects of `𝒳` coming from étale scheme charts of `F` cover
the final object of the inherited étale site (Stacks 073M,
`AlgebraicGeometry.Space.restrictionFunctor_coversTop`), and over each member of that covering
sieve the morphism into `u_G V` does factor through the image of an étale chart, by the
factorization lemma
`AlgebraicGeometry.Space.exists_chartDiagram_comparisonChartHom_factor`. -/
theorem chartFactorSieve_mem (Z : 𝒳)
    (κ : f.obj Z ⟶ (restrictionFunctor B S hS G q eG).obj V) :
    chartFactorSieve B S hS F G p q hF hG eF eG f fSpace ha V Z κ ∈
      BigFppfOver.associatedTopology B S hS p .etale Z := by
  refine (BigFppfOver.associatedTopology B S hS p .etale).superset_covering ?_
    (restrictionFunctor_coversTop B S hS F p hF hp eF Z)
  rintro Z' m ⟨W₁, ⟨n⟩⟩
  obtain ⟨W₂, g, comm, m', hm'⟩ := exists_chartDiagram_comparisonChartHom_factor B S hS F G p q
    hF hG eF eG f fSpace ha V Z' W₁ n (f.map m ≫ κ)
  exact ⟨W₂, CostructuredArrow.homMk g comm.symm, m', hm'⟩

/-! ### The glued value of a compatible family -/

variable (yf : ∀ (W : SmallEtale B S hS F)
    (_ : (CostructuredArrow.map fSpace.hom).obj W.1 ⟶ V.1),
    ℱ.obj.obj (op ((restrictionFunctor B S hS F p eF).obj W)))
  (hyf : ∀ (W₁ W₂ : SmallEtale B S hS F)
    (ζ₁ : (CostructuredArrow.map fSpace.hom).obj W₁.1 ⟶ V.1)
    (ζ₂ : (CostructuredArrow.map fSpace.hom).obj W₂.1 ⟶ V.1)
    (Y : 𝒳) (n₁ : Y ⟶ (restrictionFunctor B S hS F p eF).obj W₁)
    (n₂ : Y ⟶ (restrictionFunctor B S hS F p eF).obj W₂),
    f.map n₁ ≫ comparisonChartHom B S hS p q eF eG f fSpace ha
          (chartDiagramOfChartHom B S hS F G hF hG fSpace V W₁ ζ₁) =
        f.map n₂ ≫ comparisonChartHom B S hS p q eF eG f fSpace ha
          (chartDiagramOfChartHom B S hS F G hF hG fSpace V W₂ ζ₂) →
    ℱ.obj.map n₁.op (yf W₁ ζ₁) = ℱ.obj.map n₂.op (yf W₂ ζ₂))

/-- The family of sections on the members of
`AlgebraicGeometry.Space.chartFactorSieve` attached to the given family: restrict the section of
a chart diagram along a chosen factorization. The compatibility hypothesis says the result does
not depend on the choice, which is
`AlgebraicGeometry.Space.chartFactorFamily_eq`. -/
noncomputable def chartFactorFamily (Z : 𝒳)
    (κ : f.obj Z ⟶ (restrictionFunctor B S hS G q eG).obj V) :
    Presieve.FamilyOfElements ℱ.obj
      (chartFactorSieve B S hS F G p q hF hG eF eG f fSpace ha V Z κ).arrows :=
  fun _ _ hm ↦ ℱ.obj.map hm.choose_spec.choose_spec.choose.op
    (yf hm.choose hm.choose_spec.choose)

/-- Restricting a restriction is restricting along the composite. -/
private theorem map_op_map_op {C : Type*} [Category C] (P : Cᵒᵖ ⥤ Type u) {X Y Z : C}
    (g : X ⟶ Y) (m : Y ⟶ Z) (x : P.obj (op Z)) :
    P.map g.op (P.map m.op x) = P.map (g ≫ m).op x :=
  (Functor.map_comp_apply P m.op g.op x).symm

include hyf in
/-- **The family does not depend on the chosen factorization.** This is the compatibility of the
given family, at the two factorizations. -/
theorem chartFactorFamily_eq (Z : 𝒳)
    (κ : f.obj Z ⟶ (restrictionFunctor B S hS G q eG).obj V) {Z' : 𝒳} (m : Z' ⟶ Z)
    (hm : (chartFactorSieve B S hS F G p q hF hG eF eG f fSpace ha V Z κ).arrows m)
    (W : SmallEtale B S hS F) (ζ : (CostructuredArrow.map fSpace.hom).obj W.1 ⟶ V.1)
    (m' : Z' ⟶ (restrictionFunctor B S hS F p eF).obj W)
    (hm' : f.map m' ≫ comparisonChartHom B S hS p q eF eG f fSpace ha
        (chartDiagramOfChartHom B S hS F G hF hG fSpace V W ζ) = f.map m ≫ κ) :
    chartFactorFamily B S hS F G p q hF hG eF eG f fSpace ha V ℱ yf Z κ m hm =
      ℱ.obj.map m'.op (yf W ζ) :=
  hyf hm.choose W hm.choose_spec.choose ζ Z' hm.choose_spec.choose_spec.choose m'
    (Eq.trans hm.choose_spec.choose_spec.choose_spec hm'.symm)

include hyf in
/-- The family of sections on the members of the sieve is compatible: the two restrictions are
restrictions of the sections of two chart diagrams along morphisms which agree over `u_G V`. -/
theorem chartFactorFamily_compatible (Z : 𝒳)
    (κ : f.obj Z ⟶ (restrictionFunctor B S hS G q eG).obj V) :
    (chartFactorFamily B S hS F G p q hF hG eF eG f fSpace ha V ℱ yf Z κ).Compatible := by
  intro Y₁ Y₂ Z' g₁ g₂ m₁ m₂ h₁ h₂ hcomm
  rw [chartFactorFamily_eq B S hS F G p q hF hG eF eG f fSpace ha V ℱ yf hyf Z κ m₁ h₁
      h₁.choose h₁.choose_spec.choose h₁.choose_spec.choose_spec.choose
      h₁.choose_spec.choose_spec.choose_spec,
    chartFactorFamily_eq B S hS F G p q hF hG eF eG f fSpace ha V ℱ yf hyf Z κ m₂ h₂
      h₂.choose h₂.choose_spec.choose h₂.choose_spec.choose_spec.choose
      h₂.choose_spec.choose_spec.choose_spec]
  rw [map_op_map_op, map_op_map_op]
  refine hyf _ _ _ _ Z' _ _ ?_
  refine Eq.trans (map_comp_assoc f g₁ _ _) ?_
  refine Eq.trans (congrArg (fun z ↦ f.map g₁ ≫ z)
    h₁.choose_spec.choose_spec.choose_spec) ?_
  refine Eq.trans (map_comp_assoc f g₁ m₁ κ).symm ?_
  refine Eq.trans (congrArg (fun z ↦ f.map z ≫ κ) hcomm) ?_
  refine Eq.trans (map_comp_assoc f g₂ m₂ κ) ?_
  refine Eq.trans (congrArg (fun z ↦ f.map g₂ ≫ z)
    h₂.choose_spec.choose_spec.choose_spec.symm) ?_
  exact (map_comp_assoc f g₂ _ _).symm

include hp hF hyf in
/-- **The glued value of the family at a pair** consisting of an object `Z` of `𝒳` and a morphism
`κ : f(Z) ⟶ u_G V` of `𝒴`: the amalgamation, for the sheaf `ℱ`, of the family of sections on the
members of `AlgebraicGeometry.Space.chartFactorSieve`. -/
noncomputable def glueSection (Z : 𝒳)
    (κ : f.obj Z ⟶ (restrictionFunctor B S hS G q eG).obj V) : ℱ.obj.obj (op Z) :=
  (((isSheaf_iff_isSheaf_of_type _ ℱ.obj).1 ℱ.2 _
      (chartFactorSieve_mem B S hS F G p q hp hF hG eF eG f fSpace ha V Z κ)).amalgamate
    (chartFactorFamily B S hS F G p q hF hG eF eG f fSpace ha V ℱ yf Z κ)
    (chartFactorFamily_compatible B S hS F G p q hF hG eF eG f fSpace ha V ℱ yf hyf Z κ))

include hp hF hyf in
/-- **The glued value restricts, along a member of the sieve, to the section of the chart diagram
the member factors through.** -/
theorem glueSection_restrict (Z : 𝒳)
    (κ : f.obj Z ⟶ (restrictionFunctor B S hS G q eG).obj V) {Z' : 𝒳} (m : Z' ⟶ Z)
    (W : SmallEtale B S hS F) (ζ : (CostructuredArrow.map fSpace.hom).obj W.1 ⟶ V.1)
    (m' : Z' ⟶ (restrictionFunctor B S hS F p eF).obj W)
    (hm' : f.map m' ≫ comparisonChartHom B S hS p q eF eG f fSpace ha
        (chartDiagramOfChartHom B S hS F G hF hG fSpace V W ζ) = f.map m ≫ κ) :
    ℱ.obj.map m.op (glueSection B S hS F G p q hp hF hG eF eG f fSpace ha V ℱ yf hyf Z κ) =
      ℱ.obj.map m'.op (yf W ζ) := by
  refine Eq.trans (((isSheaf_iff_isSheaf_of_type _ ℱ.obj).1 ℱ.2 _
    (chartFactorSieve_mem B S hS F G p q hp hF hG eF eG f fSpace ha V Z κ)).valid_glue
      (chartFactorFamily_compatible B S hS F G p q hF hG eF eG f fSpace ha V ℱ yf hyf Z κ) m
      ⟨W, ζ, m', hm'⟩) ?_
  exact chartFactorFamily_eq B S hS F G p q hF hG eF eG f fSpace ha V ℱ yf hyf Z κ m
    ⟨W, ζ, m', hm'⟩ W ζ m' hm'

include hp hF hyf in
/-- **The glued values are compatible with precomposition**, which is what makes them the
components of a global section over the 2-fibre product of equation 075M. -/
theorem glueSection_map (Z Z' : 𝒳) (n : Z' ⟶ Z)
    (κ : f.obj Z ⟶ (restrictionFunctor B S hS G q eG).obj V) :
    ℱ.obj.map n.op (glueSection B S hS F G p q hp hF hG eF eG f fSpace ha V ℱ yf hyf Z κ) =
      glueSection B S hS F G p q hp hF hG eF eG f fSpace ha V ℱ yf hyf Z' (f.map n ≫ κ) := by
  refine (((isSheaf_iff_isSheaf_of_type _ ℱ.obj).1 ℱ.2).isSeparated _
    (chartFactorSieve_mem B S hS F G p q hp hF hG eF eG f fSpace ha V Z' (f.map n ≫ κ))).ext ?_
  rintro Z'' k ⟨W, ζ, m', hm'⟩
  have hkn : f.map m' ≫ comparisonChartHom B S hS p q eF eG f fSpace ha
      (chartDiagramOfChartHom B S hS F G hF hG fSpace V W ζ) = f.map (k ≫ n) ≫ κ :=
    hm'.trans (map_comp_assoc f k n κ).symm
  rw [map_op_map_op, glueSection_restrict B S hS F G p q hp hF hG eF eG f fSpace ha V ℱ yf hyf Z κ
      (k ≫ n) W ζ m' hkn,
    glueSection_restrict B S hS F G p q hp hF hG eF eG f fSpace ha V ℱ yf hyf Z'
      (f.map n ≫ κ) k W ζ m' hm']

include hp hF hyf in
/-- **At a pair coming from a diagram of étale scheme charts the glued value is the given
section.** The identity is a member of the sieve there, factoring through that very diagram. -/
theorem glueSection_chart (W : SmallEtale B S hS F)
    (ζ : (CostructuredArrow.map fSpace.hom).obj W.1 ⟶ V.1) :
    glueSection B S hS F G p q hp hF hG eF eG f fSpace ha V ℱ yf hyf
        ((restrictionFunctor B S hS F p eF).obj W)
        (comparisonChartHom B S hS p q eF eG f fSpace ha
          (chartDiagramOfChartHom B S hS F G hF hG fSpace V W ζ)) =
      yf W ζ := by
  have h := glueSection_restrict B S hS F G p q hp hF hG eF eG f fSpace ha V ℱ yf hyf
    ((restrictionFunctor B S hS F p eF).obj W)
    (comparisonChartHom B S hS p q eF eG f fSpace ha
      (chartDiagramOfChartHom B S hS F G hF hG fSpace V W ζ))
    (𝟙 _) W ζ (𝟙 _) rfl
  rw [op_id, ℱ.obj.map_id] at h
  exact h

end AlgebraicGeometry.Space

end
