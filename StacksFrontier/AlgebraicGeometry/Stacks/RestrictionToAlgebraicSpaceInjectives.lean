module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.Injective.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Equalizers
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Sites.Abelian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardRightExact
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionFunctorLimits
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionToAlgebraicSpace
public import StacksFrontier.CategoryTheory.Preadditive.Injective.Adjunction
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekExactness

/-!
# Restriction of abelian sheaves to the small étale site of a representing algebraic space

Let `𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids representable by an algebraic space
`F`, with a chosen equivalence over the site as in Tag 073M. Restriction of sheaves along the
induced functor `F_étale ⥤ 𝒳` is the inverse image `i_F^{-1}` of the morphism of topoi `i_F`,
equivalently the direct image `π_{F,*}`. On abelian sheaves it preserves injective objects, and
degreewise on cochain complexes it preserves K-injectivity.

## Main definitions

* `AlgebraicGeometry.Space.restrictionAbSheafFunctor`: the restriction `ℱ ↦ ℱ|_{F_étale}` of
  abelian sheaves, that is `Functor.sheafPushforwardContinuous` for the functor of Tag 073M.

## Main results

* `AlgebraicGeometry.Space.injective_restrictionAbSheafFunctor_obj`: **Stacks 075L**, part (1):
  the restriction of an injective abelian sheaf is injective.
* `AlgebraicGeometry.Space.isKInjective_restrictionAbSheafFunctor_obj`: **Stacks 075L**, part
  (2): the degreewise restriction of a K-injective complex of abelian sheaves is K-injective.

## Implementation notes

Both parts follow the source: restriction is right adjoint to the lower shriek functor
`π_F^{-1} = i_{F,!}` of the continuous functor `F_étale ⥤ 𝒳`, and that left adjoint is exact.
The exactness criterion used is `Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits`
together with `Stacks.Sites.LowerShriek.gShriek_preservesFiniteColimits` (Tag 04BH), whose
hypotheses are exactly the source's: the small étale site of `F` has fibre products and
equalizers and the functor `F_étale ⥤ 𝒳` preserves them. Injectives are then transferred by
`CategoryTheory.preservesInjectiveObjects_of_isExact` (Tag 015Z) and K-injectivity by
`CochainComplex.isKInjective_mapHomologicalComplex_of_exact` (Tag 08BJ).

Fibre products of étale charts are already available as
`AlgebraicGeometry.Space.SmallEtale.instHasPullbacks`, and binary products as
`AlgebraicGeometry.Space.SmallEtale.instHasBinaryProducts`; both hold because the fibre product
over `F` of two étale charts is representable, which is also what
`AlgebraicGeometry.Space.exists_chartProduct` below records, in the form exhibiting that fibre
product as a product among *all* scheme charts of `F`. Equalizers are obtained here from the
fibre products and the binary products. Note that the small étale site of an algebraic space
has in general
*no* terminal object — `F` itself need not be a scheme — so the finite limits used here cannot
be obtained from a terminal object together with fibre products.

The size conditions under which the lower shriek functor exists are carried as instance
hypotheses: sheafification of `Ab.{t}`-valued presheaves on the two sites, and pointwise left
Kan extensions along the functor. They are the `Ab.{t}`-valued analogue of the Kan-extension
condition for sheaves of sets, which needs no hypothesis — it is discharged outright by
`AlgebraicGeometry.Space.hasPointwiseRightKanExtension_restrictionFunctor_op`, which is why
`AlgebraicGeometry.Space.restrictionToposHom` is unconditional.

The source assumes `𝒳` is an *algebraic stack* representable by an *algebraic space* `F`.
Neither algebraicity enters the argument: all that is used is the functor `F_étale ⥤ 𝒳` of Tag
073M together with the representability data carried by an étale chart of `F`. So the
hypotheses below are that `p` be fibred in groupoids and that an equivalence over the site
with the category of elements of `F` be given, which is a generalization of the source's
statement and not a weakening of its conclusion.

The source adds that the same statements are *false* for sheaves of modules, referring to Tag
0758. That is `AlgebraicGeometry.Space.restriction_modules_not_preserves_injectives`, in
`StacksFrontier.AlgebraicGeometry.Stacks.RestrictionToAlgebraicSpaceModules`, which also states both
parts for abelian sheaves in the universe of the schemes with no size hypothesis
(`AlgebraicGeometry.Space.injective_restrictionAbSheafFunctor_obj_univ` and
`AlgebraicGeometry.Space.isKInjective_restrictionAbSheafFunctor_obj_univ`).

## References

* [Stacks Project, Tag 075L](https://stacks.math.columbia.edu/tag/075L)
* [Stacks Project, Tag 073M](https://stacks.math.columbia.edu/tag/073M)
* [Stacks Project, Tag 04BH](https://stacks.math.columbia.edu/tag/04BH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe t u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)

/-! ### Binary products and equalizers of étale charts -/

/-- The represented fibre product over `F` of two étale charts is their binary product among
all scheme charts of `F`, and it is again an étale chart. -/
theorem exists_chartProduct (X Y : SmallEtale B S hS F) :
    ∃ c : BinaryFan X.obj Y.obj, Nonempty (IsLimit c) ∧ IsEtaleChart B S hS F c.pt := by
  let h := X.property.rep
  let Z : CostructuredArrow yoneda F :=
    CostructuredArrow.mk (yoneda.map (h.snd Y.obj.hom) ≫ Y.obj.hom)
  let f : Z ⟶ X.obj := CostructuredArrow.homMk (h.fst' Y.obj.hom) (by
    dsimp [Z]
    rw [h.map_fst']
    exact h.w _)
  let g : Z ⟶ Y.obj := CostructuredArrow.homMk (h.snd Y.obj.hom) rfl
  refine ⟨BinaryFan.mk f g, ⟨BinaryFan.isLimitMk (fun s => ?_) ?_ ?_ ?_⟩, ?_⟩
  · exact CostructuredArrow.homMk
      (h.lift' s.fst.left s.snd.left (s.fst.w.trans s.snd.w.symm)) (by
        dsimp [Z]
        rw [← Category.assoc, ← yoneda.map_comp, h.lift'_snd]
        exact s.snd.w)
  · exact fun s => CostructuredArrow.hom_ext _ _ (h.lift'_fst _ _ _)
  · exact fun s => CostructuredArrow.hom_ext _ _ (h.lift'_snd _ _ _)
  · intro s m hm₁ hm₂
    refine CostructuredArrow.hom_ext _ _ (h.hom_ext' ?_ ?_)
    · exact (congrArg (fun z => z.left) hm₁).trans (h.lift'_fst _ _ _).symm
    · exact (congrArg (fun z => z.left) hm₂).trans (h.lift'_snd _ _ _).symm
  · exact etale_comp_of_scheme B S hS (h.snd Y.obj.hom) Y.obj.hom
      (X.property.property_snd Y.obj.hom) Y.property

/-- The inclusion of the étale charts into all scheme charts of `F` creates binary products. -/
@[instance_reducible]
noncomputable def smallEtaleCreatesBinaryProducts :
    CreatesLimitsOfShape (Discrete WalkingPair) (SmallEtale.inclusion B S hS F) where
  CreatesLimit {D} := by
    let h := exists_chartProduct B S hS F (D.obj ⟨.left⟩) (D.obj ⟨.right⟩)
    let E := diagramIsoPair (D ⋙ SmallEtale.inclusion B S hS F)
    exact createsLimitFullSubcategoryInclusion' D
      ((IsLimit.postcomposeInvEquiv E h.choose).symm h.choose_spec.1.some)
      h.choose_spec.2

/-- The scheme chart underlying a binary product of étale charts is the fibre product over `F`
of the underlying scheme charts. -/
theorem smallEtale_preservesBinaryProducts :
    PreservesLimitsOfShape (Discrete WalkingPair) (SmallEtale.inclusion B S hS F) where
  preservesLimit {D} := by
    let := smallEtaleCreatesBinaryProducts B S hS F
    obtain ⟨c, ⟨hc⟩, _⟩ := exists_chartProduct B S hS F (D.obj ⟨.left⟩) (D.obj ⟨.right⟩)
    let E := diagramIsoPair (D ⋙ SmallEtale.inclusion B S hS F)
    have : HasLimit (D ⋙ SmallEtale.inclusion B S hS F) :=
      ⟨_, (IsLimit.postcomposeInvEquiv E c).symm hc⟩
    infer_instance

/-- The small étale site of `F` has equalizers; they are computed from its fibre products and
its binary products. -/
theorem smallEtale_hasEqualizers : HasEqualizers (SmallEtale B S hS F) := by
  let := SmallEtale.instHasBinaryProducts B S hS F
  exact hasEqualizers_of_hasPullbacks_and_binary_products

/-! ### Restriction of abelian sheaves -/

/-- **Stacks 073M, equation 075K.** The restriction `ℱ|_{F_étale} = i_F^{-1}ℱ = π_{F,*}ℱ` of an
abelian sheaf on the inherited étale site of `𝒳` to the small étale site of the algebraic space
`F`. -/
noncomputable abbrev restrictionAbSheafFunctor (hp : p.IsFiberedInGroupoids)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    Sheaf (BigFppfOver.associatedTopology B S hS p .etale) Ab.{t} ⥤
      Sheaf (SmallEtale.topology B S hS F) Ab.{t} :=
  letI := restrictionFunctor_isContinuous B S hS F p hp e
  (restrictionFunctor B S hS F p e).sheafPushforwardContinuous Ab.{t}
    (SmallEtale.topology B S hS F) (BigFppfOver.associatedTopology B S hS p .etale)

/-- The restriction functor on abelian sheaves has an exact additive left adjoint, the lower
shriek functor. -/
private theorem exists_exact_leftAdjoint_restrictionAbSheafFunctor (hp : p.IsFiberedInGroupoids)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    [HasSheafify (BigFppfOver.associatedTopology B S hS p .etale) Ab.{t}]
    [HasSheafify (SmallEtale.topology B S hS F) Ab.{t}]
    [∀ G : (SmallEtale B S hS F)ᵒᵖ ⥤ Ab.{t},
      (restrictionFunctor B S hS F p e).op.HasPointwiseLeftKanExtension G] :
    ∃ L : Sheaf (SmallEtale.topology B S hS F) Ab.{t} ⥤
        Sheaf (BigFppfOver.associatedTopology B S hS p .etale) Ab.{t},
      Nonempty (L ⊣ restrictionAbSheafFunctor B S hS F p hp e) ∧ L.Additive ∧
        PreservesFiniteLimits L ∧ PreservesFiniteColimits L := by
  let := restrictionFunctor_isContinuous B S hS F p hp e
  let := SmallEtale.instHasBinaryProducts B S hS F
  let := smallEtale_hasEqualizers B S hS F
  let := restrictionFunctor_preservesBinaryProducts B S hS F p e
  let := restrictionFunctor_preservesEqualizers B S hS F p e
  let L := Functor.sheafPullbackConstruction.sheafPullback (restrictionFunctor B S hS F p e)
    Ab.{t} (SmallEtale.topology B S hS F) (BigFppfOver.associatedTopology B S hS p .etale)
  let : PreservesFiniteLimits L :=
    Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits.{t, u, w, u + 1, v} _ _ _
  let : PreservesFiniteColimits L :=
    Stacks.Sites.LowerShriek.gShriek_preservesFiniteColimits Ab.{t} _ _ _
  have : HasFiniteLimits (Sheaf (SmallEtale.topology B S hS F) Ab.{t}) :=
    Abelian.hasFiniteLimits
  have : HasBinaryProducts (Sheaf (SmallEtale.topology B S hS F) Ab.{t}) :=
    inferInstance
  exact ⟨L, ⟨Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _⟩,
    Functor.additive_of_preserves_binary_products L, inferInstance, inferInstance⟩

/-- **Stacks Project, Tag 075L, part (1).** Let `𝒳` be a category fibred in groupoids over the
big fppf site of `S` representable by the algebraic space `F`. If `I` is injective in
`Ab(𝒳_étale)`, then `I|_{F_étale}` is injective in `Ab(F_étale)`. -/
@[stacks 075L "part (1), injective abelian sheaves"]
theorem injective_restrictionAbSheafFunctor_obj (hp : p.IsFiberedInGroupoids)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    [HasSheafify (BigFppfOver.associatedTopology B S hS p .etale) Ab.{t}]
    [HasSheafify (SmallEtale.topology B S hS F) Ab.{t}]
    [∀ G : (SmallEtale B S hS F)ᵒᵖ ⥤ Ab.{t},
      (restrictionFunctor B S hS F p e).op.HasPointwiseLeftKanExtension G]
    (I : Sheaf (BigFppfOver.associatedTopology B S hS p .etale) Ab.{t}) [Injective I] :
    Injective ((restrictionAbSheafFunctor B S hS F p hp e).obj I) := by
  obtain ⟨L, ⟨adj⟩, _, _, _⟩ := exists_exact_leftAdjoint_restrictionAbSheafFunctor B S hS F p hp e
  let : (restrictionAbSheafFunctor B S hS F p hp e).PreservesInjectiveObjects :=
    preservesInjectiveObjects_of_isExact _ L adj ⟨inferInstance, inferInstance⟩
  exact Functor.injective_obj_of_injective _ inferInstance

/-- **Stacks Project, Tag 075L, part (2).** Let `𝒳` be a category fibred in groupoids over the
big fppf site of `S` representable by the algebraic space `F`. If `I` is a K-injective complex
in `Ab(𝒳_étale)`, then `I|_{F_étale}` is a K-injective complex in `Ab(F_étale)`. -/
@[stacks 075L "part (2), K-injective complexes"]
theorem isKInjective_restrictionAbSheafFunctor_obj (hp : p.IsFiberedInGroupoids)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    [HasSheafify (BigFppfOver.associatedTopology B S hS p .etale) Ab.{t}]
    [HasSheafify (SmallEtale.topology B S hS F) Ab.{t}]
    [∀ G : (SmallEtale B S hS F)ᵒᵖ ⥤ Ab.{t},
      (restrictionFunctor B S hS F p e).op.HasPointwiseLeftKanExtension G]
    (I : CochainComplex
      (Sheaf (BigFppfOver.associatedTopology B S hS p .etale) Ab.{t}) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((restrictionAbSheafFunctor B S hS F p hp e).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) := by
  obtain ⟨L, ⟨adj⟩, _, _, _⟩ := exists_exact_leftAdjoint_restrictionAbSheafFunctor B S hS F p hp e
  exact CochainComplex.isKInjective_mapHomologicalComplex_of_exact _ L adj I

end AlgebraicGeometry.Space

end
