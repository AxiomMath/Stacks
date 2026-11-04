module

public import StacksFrontier.CategoryTheory.Monoidal.ExternalAdjunctionMate
public import StacksFrontier.CategoryTheory.Monoidal.FunctorCategoryConst
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.ExternalTensorProduct

/-!
# The product formula for colimits of external tensor products is the canonical comparison

Let `C₁` and `C₂` be small categories, `B` a commutative ring, and `F`, `G` diagrams of
`B`-modules on `C₁ᵒᵖ` and on `C₂ᵒᵖ`.  Restriction along the two projections of `C₁ × C₂` turns
them into one diagram `g₁^{-1}F ⊗ g₂^{-1}G` on `(C₁ × C₂)ᵒᵖ`, and
`Stacks.CategoryHomology.colimExternalTensorIso` exhibits an isomorphism

`π_!(g₁^{-1}F ⊗ g₂^{-1}G) ≅ π_{1,!}F ⊗_B π_{2,!}G`

between its colimit and the tensor product of the two colimits, `π_!` being the colimit over the
site as in Stacks 08PF.  That isomorphism is constructed from the universal property, so by
itself it says only that the two objects are isomorphic.  This file identifies it with the
*canonical* comparison morphism: the two-variable mate

`CategoryTheory.Adjunction.externalMate`

of the two identifications `π_i^{-1} ∘ (\text{point}) = \pi^{-1}` of the inverse images of the
point, taken for the adjunction `π_! ⊣ π^{-1}` between the colimit and the constant diagram and
for the monoidal structure of `π^{-1}` given by
`CategoryTheory.Functor.constMonoidal`.  In other words, the product formula holds for the
morphism that is determined by the colimit cocones, not merely for some isomorphism.

## Main definitions

* `Stacks.CategoryHomology.colimExternalTensorComparison`: the canonical comparison
  `π_!(g₁^{-1}F ⊗ g₂^{-1}G) ⟶ π_{1,!}F ⊗ π_{2,!}G`, as the two-variable mate.

## Main results

* `CategoryTheory.Limits.ι_comp_colimConstAdj_homEquiv_symm`: the adjunction between the colimit
  and the constant diagram sends a cocone to the morphism it induces on the colimit.
* `Stacks.CategoryHomology.ι_comp_colimExternalTensorComparison`: the canonical comparison sends
  the colimit cocone of the external tensor product at `(U, V)` to the tensor product of the
  colimit cocones at `U` and at `V`.
* `Stacks.CategoryHomology.colimExternalTensorComparison_eq_colimExternalTensorIso_hom`: it is
  the product-formula isomorphism, and
* `Stacks.CategoryHomology.isIso_colimExternalTensorComparison`: therefore invertible.

## Implementation notes

**What is proved.**  Everything in this file is unconditional: the comparison is defined for all
`F` and `G`, and its invertibility is proved outright.  The two natural transformations the
two-variable mate is built from are the identity, because restricting a constant diagram on
`C_iᵒᵖ` along a projection gives the constant diagram on `(C₁ × C₂)ᵒᵖ` on the nose; this is
`Stacks.CategoryHomology.const_comp_projFstInverseImage` and its companion for the second
projection, both of which hold by `rfl`.

**What is not proved.**  This is the *underived* statement.  Tag 08QB asserts the corresponding
identity for the total derived functors and the derived tensor products, and that is not proved
here or anywhere in this repository; the derived form needs the colimit over the product site to
be computed on an external tensor product of resolutions, which is where the proof in the source
appeals to the computation on free diagrams
(`Stacks.CategoryHomology.externalTensorFreeYonedaIso`) and then omits the verification.  No
`@[stacks 08QB]` attribute is therefore attached here: the two sites carrying that tag,
`Stacks.CategoryHomology.colimExternalTensorIso` and
`Stacks.CategoryHomology.externalTensorFreeYonedaIso`, already record the underived identity and
the computation on free diagrams, and the content added here is the identification of the first
with the canonical morphism rather than a new clause of the tag.

Beware that the canonical comparison of this file is *not* the oplax tensorator
`Functor.OplaxMonoidal.δ` of the colimit over the product site: the target of that tensorator is
`π_!(g₁^{-1}F) ⊗ π_!(g₂^{-1}G)`, built from the colimit over the *product* site, and it is not
invertible in general -- already for two discrete two-object categories the two sides have
different ranks.  The two differ by the comparisons `π_!(g_i^{-1}·) ⟶ π_{i,!}(·)` of Stacks 08QA
for the projections, as `CategoryTheory.Adjunction.externalMate_eq_δ_comp` records.

## References

* [Stacks Project, Tag 08QB](https://stacks.math.columbia.edu/tag/08QB)
* [Stacks Project, Tag 08QA](https://stacks.math.columbia.edu/tag/08QA)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory.Limits

universe v₁ u₁ v₂ u₂

/-- **The adjunction between the colimit and the constant diagram sends a cocone to the morphism
it induces on the colimit.**  Composing with the colimit cocone recovers the cocone. -/
@[reassoc]
lemma ι_comp_colimConstAdj_homEquiv_symm {J : Type u₁} [Category.{v₁} J] {D : Type u₂}
    [Category.{v₂} D] [HasColimitsOfShape J D] (X : J ⥤ D) (W : D)
    (φ : X ⟶ (Functor.const J).obj W) (Z : J) :
    colimit.ι X Z ≫ (colimConstAdj.homEquiv X W).symm φ = φ.app Z := by
  rw [Adjunction.homEquiv_counit, ← Category.assoc, colimit.ι_map]
  simp [colimConstAdj]

end CategoryTheory.Limits

namespace Stacks.CategoryHomology

universe u₁ u₂ w

variable {C₁ : Type u₁} {C₂ : Type u₂} [SmallCategory C₁] [SmallCategory C₂]
  {B : Type w} [CommRing B]

/-- **Restricting a constant diagram along the first projection gives a constant diagram.**  This
is the identity `g₁^{-1} ∘ π_1^{-1} = π^{-1}` between the inverse images of the point; it holds on
the nose. -/
lemma const_comp_projFstInverseImage :
    (Functor.const C₁ᵒᵖ : ModuleCat.{max u₁ u₂ w} B ⥤ _) ⋙ projFstInverseImage C₁ C₂ B =
      (Functor.const (C₁ × C₂)ᵒᵖ : ModuleCat.{max u₁ u₂ w} B ⥤ _) :=
  rfl

/-- **Restricting a constant diagram along the second projection gives a constant diagram.** -/
lemma const_comp_projSndInverseImage :
    (Functor.const C₂ᵒᵖ : ModuleCat.{max u₁ u₂ w} B ⥤ _) ⋙ projSndInverseImage C₁ C₂ B =
      (Functor.const (C₁ × C₂)ᵒᵖ : ModuleCat.{max u₁ u₂ w} B ⥤ _) :=
  rfl

/-- **The canonical comparison of the product formula**

`π_!(g₁^{-1}F ⊗ g₂^{-1}G) ⟶ π_{1,!}F ⊗_B π_{2,!}G`,

the two-variable mate `CategoryTheory.Adjunction.externalMate` of the two identities
`Stacks.CategoryHomology.const_comp_projFstInverseImage` and
`Stacks.CategoryHomology.const_comp_projSndInverseImage`, taken for the adjunction
`CategoryTheory.Limits.colimConstAdj` between the colimit over a site and the constant diagram
and for the monoidal structure `CategoryTheory.Functor.constMonoidal` of the latter.  Being a
mate, it is determined by the colimit cocones; it is not a choice. -/
def colimExternalTensorComparison (F : C₁ᵒᵖ ⥤ ModuleCat.{max u₁ u₂ w} B)
    (G : C₂ᵒᵖ ⥤ ModuleCat.{max u₁ u₂ w} B) :
    (colim : ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{max u₁ u₂ w} B) ⥤ _).obj (externalTensor F G) ⟶
      (colim : (C₁ᵒᵖ ⥤ ModuleCat.{max u₁ u₂ w} B) ⥤ _).obj F ⊗
        (colim : (C₂ᵒᵖ ⥤ ModuleCat.{max u₁ u₂ w} B) ⥤ _).obj G :=
  Adjunction.externalMate colimConstAdj colimConstAdj colimConstAdj
    (projFstInverseImage C₁ C₂ B) (projSndInverseImage C₁ C₂ B) (𝟙 _) (𝟙 _) F G

/-- **The canonical comparison sends the colimit cocone of the external tensor product at
`(U, V)` to the tensor product of the colimit cocones at `U` and at `V`.**  This is the defining
property of the mate, read through the universal property of the colimit. -/
@[reassoc]
lemma ι_comp_colimExternalTensorComparison (F : C₁ᵒᵖ ⥤ ModuleCat.{max u₁ u₂ w} B)
    (G : C₂ᵒᵖ ⥤ ModuleCat.{max u₁ u₂ w} B) (Z : (C₁ × C₂)ᵒᵖ) :
    colimit.ι (externalTensor F G) Z ≫ colimExternalTensorComparison F G =
      colimit.ι F (op Z.unop.1) ⊗ₘ colimit.ι G (op Z.unop.2) := by
  simp only [colimExternalTensorComparison, Adjunction.externalMate, externalTensor,
    ι_comp_colimConstAdj_homEquiv_symm]
  simp only [projFstInverseImage, projSndInverseImage, Functor.whiskeringLeft_obj_map,
    Functor.whiskerLeft_app, Monoidal.tensorHom_app, NatTrans.comp_app, NatTrans.id_app,
    Functor.constMonoidal_μ_app, Functor.op_obj, Prod.fst_obj, Prod.snd_obj]
  rfl

/-- **The product-formula isomorphism is the canonical comparison.**  Both are determined by
their composites with the colimit cocone, and those agree by
`Stacks.CategoryHomology.ι_comp_colimExternalTensorComparison` and
`Stacks.CategoryHomology.ι_comp_colimExternalTensorIso_hom`. -/
lemma colimExternalTensorComparison_eq_colimExternalTensorIso_hom
    (F : C₁ᵒᵖ ⥤ ModuleCat.{max u₁ u₂ w} B) (G : C₂ᵒᵖ ⥤ ModuleCat.{max u₁ u₂ w} B) :
    colimExternalTensorComparison F G = (colimExternalTensorIso F G).hom :=
  colimit.hom_ext fun Z ↦ by
    rw [ι_comp_colimExternalTensorComparison, ι_comp_colimExternalTensorIso_hom]

/-- **The canonical comparison of the product formula is an isomorphism**: the colimit of an
external tensor product of diagrams of modules is the tensor product of the two colimits, and the
isomorphism is the morphism determined by the colimit cocones. -/
instance isIso_colimExternalTensorComparison (F : C₁ᵒᵖ ⥤ ModuleCat.{max u₁ u₂ w} B)
    (G : C₂ᵒᵖ ⥤ ModuleCat.{max u₁ u₂ w} B) :
    IsIso (colimExternalTensorComparison F G) := by
  rw [colimExternalTensorComparison_eq_colimExternalTensorIso_hom]
  infer_instance

end Stacks.CategoryHomology

end
