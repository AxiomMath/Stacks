module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSitesLimits

/-!
# The image of an étale morphism from a scheme to an algebraic space (Stacks 06NF)

An étale morphism `f : yoneda.obj U ⟶ X` from a represented presheaf to an algebraic space over
`S` factors through the open subspace of `X` whose points are the image of the points of `U`.
The induced morphism is a surjective étale atlas of that open subspace, its kernel pair is the
same as the kernel pair of `f`, that kernel pair is an étale equivalence relation, and the open
subspace is the fppf sheaf quotient of `U` by it.

## Main definitions

* `AlgebraicGeometry.Space.factorThroughEtaleImage` is the induced morphism to the image open
  subspace.

## Main results

* `AlgebraicGeometry.Space.factorThroughEtaleImage_comp`: the factorization equation.
* `AlgebraicGeometry.Space.surjective_factor_through_etaleImage` and
  `AlgebraicGeometry.Space.etale_factor_through_etaleImage`: the induced morphism is a
  surjective étale atlas.
* `AlgebraicGeometry.Space.isEtaleEquivalenceRelation_etaleImage`: the kernel pair is an étale
  equivalence relation.
* `AlgebraicGeometry.Space.isCoequalizer_factor_through_etaleImage`: the open subspace is the
  quotient of `U` by that kernel pair.

## Implementation notes

The image open subspace is specified by its set of points, as in the correspondence of
Tag 03BZ, and the factorization comes from the pointwise criterion of Tag 03IE, so
`factorThroughEtaleImage` is a `Classical.choose` whose defining property is
`factorThroughEtaleImage_comp`; the three results about the induced morphism are therefore
stated for an arbitrary morphism satisfying the factorization equation.

Surjectivity is Tag 03H5 together with injectivity of the inclusion on points (Tag 06RV).
Étaleness, the kernel-pair invariance, and the quotient property all rest on the same general
fact, that a pullback square is unchanged when both its legs factor through a monomorphism:
`CategoryTheory.Limits.PullbackCone.isLimitOfFactors`. The equivalence relation and the
quotient are then Tag 0262, parts (1) and (3), applied to the induced atlas. Together these
make the data a presentation in the sense of `AlgebraicGeometry.Space.Presentation` (Tag 0263).

## References

* [Stacks Project, Tag 06NF](https://stacks.math.columbia.edu/tag/06NF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

add_to_stacks 06NF "kernel pair" CategoryTheory.Limits.PullbackCone.isLimitOfFactors

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
variable (hX : IsAlgebraicSpace B S hS X)
variable (U : BigFppfOver B S hS)
variable (f : yoneda.obj U ⟶ X)
variable (hf : (MorphismProperty.presheaf (MorphismProperty.inverseImage
  (@Etale.{u} : MorphismProperty Scheme.{u})
  (BigFppfOver.toScheme B S hS))) f)
variable (X' : Subfunctor X) (hX' : IsOpenSubspace B S hS X')
variable (hX'image : Set.range (pointsMap B S hS X'.toFunctor X'.ι) =
  Set.range (pointsMap B S hS (yoneda.obj U) f))

/-- A pullback square whose legs factor through a monomorphism is a pullback after factoring. -/
private theorem isPullback_of_factors_comp_mono {C : Type*} [Category C] {A P Q Y Z : C}
    (ι : Z ⟶ Y) [Mono ι] {f : P ⟶ Y} {g : Q ⟶ Y} {a : A ⟶ P} {b : A ⟶ Q}
    {f' : P ⟶ Z} {g' : Q ⟶ Z} (hf : f' ≫ ι = f) (hg : g' ≫ ι = g)
    (h : IsPullback a b f g) : IsPullback a b f' g' :=
  IsPullback.of_isLimit (PullbackCone.isLimitOfFactors f g ι f' g' hf hg
    (PullbackCone.mk a b h.w) h.isLimit)

include hX' hX'image

/-- The morphism from a scheme to the open subspace corresponding to the image
of its étale map. -/
@[stacks 06NF "induced morphism"]
noncomputable def factorThroughEtaleImage :
    yoneda.obj U ⟶ X'.toFunctor :=
  Classical.choose ((factorsThrough_openSubspace_iff_points B S hS
    hX (isAlgebraicSpace_yoneda B S hS U) X' hX' f).2 (by
      rw [hX'image]))

/-- The induced morphism composes with the inclusion to give the original
étale map. -/
@[stacks 06NF "factorization"]
theorem factorThroughEtaleImage_comp :
    factorThroughEtaleImage B S hS hX U f X' hX' hX'image ≫ X'.ι = f :=
  Classical.choose_spec ((factorsThrough_openSubspace_iff_points B S hS
    hX (isAlgebraicSpace_yoneda B S hS U) X' hX' f).2 (by
      rw [hX'image]))

/-- The induced map to the image open subspace is surjective. -/
@[stacks 06NF "surjective"]
theorem surjective_factor_through_etaleImage
    (f' : yoneda.obj U ⟶ X'.toFunctor) (hfactor : f' ≫ X'.ι = f) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f' := by
  apply (surjective_iff_surjective_pointsMap B S hS X'.toFunctor hX'.1 U f').2
  intro p'
  obtain ⟨p, hp⟩ : pointsMap B S hS X'.toFunctor X'.ι p' ∈
      Set.range (pointsMap B S hS (yoneda.obj U) f) := by
    rw [← hX'image]
    exact ⟨p', rfl⟩
  refine ⟨p, (pointsMap_injective_of_mono B S hS X'.ι) ?_⟩
  calc
    pointsMap B S hS X'.toFunctor X'.ι
        (pointsMap B S hS (yoneda.obj U) f' p) =
      pointsMap B S hS (yoneda.obj U) (f' ≫ X'.ι) p :=
        (congrFun (pointsMap_comp B S hS _ f' X'.ι) p).symm
    _ = pointsMap B S hS (yoneda.obj U) f p := by rw [hfactor]
    _ = pointsMap B S hS X'.toFunctor X'.ι p' := hp

omit hX'image
include hX' hf

/-- The induced map to the image open subspace is étale. -/
@[stacks 06NF "étale"]
theorem etale_factor_through_etaleImage
    (f' : yoneda.obj U ⟶ X'.toFunctor) (hfactor : f' ≫ X'.ι = f) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f' := by
  -- `hX'` is not needed for étaleness, but it is part of this statement's signature and the
  -- statements above this one pass it by name, so it is kept and discharged here.
  have _ := hX'
  let P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  have : MorphismProperty.RespectsIso (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : P.RespectsIso := MorphismProperty.RespectsIso.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  apply MorphismProperty.relative.of_exists (F := yoneda) (P := P)
  intro T g
  have hpb := hf.rep.isPullback (g ≫ X'.ι)
  exact ⟨hf.rep.pullback (g ≫ X'.ι), hf.rep.fst (g ≫ X'.ι),
    hf.rep.snd (g ≫ X'.ι), isPullback_of_factors_comp_mono X'.ι hfactor rfl hpb,
    hf.property (g ≫ X'.ι) (hf.rep.fst (g ≫ X'.ι))
      (hf.rep.snd (g ≫ X'.ι)) hpb⟩

omit hf hX'

include hf

/-- The kernel pair of an étale scheme morphism is an étale equivalence
relation on its source. -/
@[stacks 06NF "étale equivalence relation"]
theorem isEtaleEquivalenceRelation_etaleImage
    {R : BigFppfOver B S hS} (s t : R ⟶ U)
    (hR : IsPullback (yoneda.map s) (yoneda.map t) f f) :
    Stacks.Groupoids.IsEtaleEquivalenceRelation
      (prod.lift ((Over.post B.inclusion).map s)
        ((Over.post B.inclusion).map t)) where
  isEquivalenceRelation := by
    simpa only [Stacks.Groupoids.PreRelation.target, Stacks.Groupoids.PreRelation.source,
      prod.lift_fst, prod.lift_snd] using isEquivalenceRelation_of_isPullback B S hS f s t hR
  etale_source := by
    simp only [Stacks.Groupoids.PreRelation.source, prod.lift_snd]
    exact (hf.property f (yoneda.map s) t hR :
      AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map t))
  etale_target := by
    simp only [Stacks.Groupoids.PreRelation.target, prod.lift_fst]
    exact (hf.property f (yoneda.map t) s hR.flip :
      AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map s))

omit hf
include hX' hX'image hf

/-- The image open subspace is the fppf sheaf quotient of `U` by the kernel
pair of the original map. -/
@[stacks 06NF "presentation as a quotient"]
theorem isCoequalizer_factor_through_etaleImage
    {R : BigFppfOver B S hS} (s t : R ⟶ U)
    (hR : IsPullback (yoneda.map s) (yoneda.map t) f f)
    (f' : yoneda.obj U ⟶ X'.toFunctor) (hfactor : f' ≫ X'.ι = f) :
    let J := BigFppfOver.topology B S hS
    ∃ (hRsh : Presheaf.IsSheaf J (yoneda.obj R))
      (hUsh : Presheaf.IsSheaf J (yoneda.obj U)),
      let RF : Sheaf J (Type u) := ⟨yoneda.obj R, hRsh⟩
      let UF : Sheaf J (Type u) := ⟨yoneda.obj U, hUsh⟩
      let XF : Sheaf J (Type u) := ⟨X'.toFunctor, hX'.1.isSheaf⟩
      let sf : RF ⟶ UF := ⟨yoneda.map s⟩
      let tf : RF ⟶ UF := ⟨yoneda.map t⟩
      let ff : UF ⟶ XF := ⟨f'⟩
      let w : sf ≫ ff = tf ≫ ff := by
        apply Sheaf.hom_ext
        change yoneda.map s ≫ f' = yoneda.map t ≫ f'
        exact (isPullback_of_factors_comp_mono X'.ι hfactor hfactor hR).w
      Nonempty (IsColimit (Cofork.ofπ ff w)) := by
  have hR' := isPullback_of_factors_comp_mono X'.ι hfactor hfactor hR
  exact isCoequalizer_of_surjectiveEtale B S hS f' s t hR' hX'.1
    (surjective_factor_through_etaleImage B S hS U f X' hX' hX'image f' hfactor)
    (etale_factor_through_etaleImage B S hS U f hf X' hX' f' hfactor)

end AlgebraicGeometry.Space

end
