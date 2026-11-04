module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafKernelPair
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.ChartRelation
public import StacksFrontier.CategoryTheory.EquivalenceRelation.Transfer

/-!
# The quotient of an algebraic space by an étale equivalence relation

Stacks 02WW says that the quotient sheaf of an étale equivalence relation between two *objects
of the big fppf site* is an algebraic space. This file upgrades it to an equivalence relation
`j : R ⟶ U ×_Z U` between *algebraic spaces* over a presheaf `Z`, whose target and source maps
are representable and étale: the quotient sheaf `U/R` is again an algebraic space.

## Main definitions

* `CategoryTheory.Limits.coequalizerIsoOfIso` and
  `CategoryTheory.Limits.coequalizerIsoSwap`: the coequalizer of a parallel pair depends on the
  pair only up to isomorphism, and not on its order.
* `AlgebraicGeometry.Space.quotientPresheafIsoPoints`: the quotient presheaf of a relation
  between objects of the site, computed on restricted functors of points, agrees with the
  quotient presheaf of the relation of presheaves which it represents.

## Main results

* `Stacks.Groupoids.pointsIsoYoneda_naturality`: the identification of the restricted functor
  of points of `G.obj X` with the presheaf represented by `X` is natural in `X`.
* `AlgebraicGeometry.Space.isEtaleEquivalenceRelation_of_embedding`: a pair of étale morphisms
  of the site whose image under a fully faithful functor is an internal equivalence relation is
  an étale equivalence relation over `S`.
* `AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_of_isAlgebraicSpace`: the quotient
  sheaf of an equivalence relation of algebraic spaces with representable étale target and
  source maps is an algebraic space.

## Implementation notes

The two quotient-sheaf constructions order their parallel pair oppositely:
`AlgebraicGeometry.Space.quotientPresheaf` coequalizes the target before the source, while
`Stacks.Groupoids.quotientPresheaf` coequalizes the source before the target. The comparison
therefore passes through `CategoryTheory.Limits.coequalizerIsoSwap`.

## References

* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 043D](https://stacks.math.columbia.edu/tag/043D)
* [Stacks Project, Tag 046P](https://stacks.math.columbia.edu/tag/046P)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe v₂ u₂ v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

/-- An isomorphism of parallel pairs induces an isomorphism of their coequalizers. -/
def coequalizerIsoOfIso {A B A' B' : C} (f g : A ⟶ B) (f' g' : A' ⟶ B')
    [HasCoequalizer f g] [HasCoequalizer f' g'] (α : A ≅ A') (β : B ≅ B')
    (hf : f ≫ β.hom = α.hom ≫ f') (hg : g ≫ β.hom = α.hom ≫ g') :
    coequalizer f g ≅ coequalizer f' g' :=
  HasColimit.isoOfNatIso (parallelPair.ext α β hf hg)

/-- The coequalizer of a parallel pair does not depend on the order of the pair. -/
def coequalizerIsoSwap {A B : C} (f g : A ⟶ B) [HasCoequalizer f g] [HasCoequalizer g f] :
    coequalizer f g ≅ coequalizer g f where
  hom := coequalizer.desc (coequalizer.π g f) (coequalizer.condition g f).symm
  inv := coequalizer.desc (coequalizer.π f g) (coequalizer.condition f g).symm
  hom_inv_id := by apply coequalizer.hom_ext; simp
  inv_hom_id := by apply coequalizer.hom_ext; simp

end CategoryTheory.Limits

namespace Stacks.Groupoids

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]

/-- The identification of the restricted functor of points of `G.obj X` with the presheaf
represented by `X` is compatible with the maps induced by a morphism of `C`. -/
theorem pointsIsoYoneda_naturality (G : C ⥤ D) [G.Full] [G.Faithful] {R U : C} (f : R ⟶ U) :
    G.op.whiskerLeft (yoneda.map (G.map f)) ≫ (pointsIsoYoneda G U).hom =
      (pointsIsoYoneda G R).hom ≫ yoneda.map f := by
  ext T x
  apply G.map_injective
  simp [pointsIsoYoneda, Functor.FullyFaithful.homEquiv,
    Functor.FullyFaithful.ofFullyFaithful]

end Stacks.Groupoids

namespace AlgebraicGeometry.Space

open Stacks.Groupoids (sourceMap targetMap pointsIsoYoneda IsEtaleEquivalenceRelation)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### An étale equivalence relation recognised on represented presheaves -/

/-- The source of the relation of schemes determined by a pair of morphisms of the site is the
image of the source morphism. -/
private theorem relation_source_eq {R₀ U₀ : BigFppfOver B S hS} (s₀ t₀ : R₀ ⟶ U₀) :
    (relation B S hS s₀ t₀).source = (Over.post (X := B.obj hS) B.inclusion).map s₀ :=
  prod.lift_snd _ _

/-- The target of the relation of schemes determined by a pair of morphisms of the site is the
image of the target morphism. -/
private theorem relation_target_eq {R₀ U₀ : BigFppfOver B S hS} (s₀ t₀ : R₀ ⟶ U₀) :
    (relation B S hS s₀ t₀).target = (Over.post (X := B.obj hS) B.inclusion).map t₀ :=
  prod.lift_fst _ _

/-- A pair of étale morphisms of the big fppf site over `S` forming an internal equivalence
relation is an étale equivalence relation of schemes over `S`. -/
private theorem isEtaleEquivalenceRelation_of_isEquivalenceRelation {R₀ U₀ : BigFppfOver B S hS}
    (s₀ t₀ : R₀ ⟶ U₀) (hsite : IsEquivalenceRelation t₀ s₀)
    (ht : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) t₀)
    (hs : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) s₀) :
    IsEtaleEquivalenceRelation (relation B S hS s₀ t₀) := by
  have _ : HasFiniteLimits B.Schemes := hasFiniteLimits_of_hasTerminal_and_pullbacks
  have _ : PreservesFiniteLimits B.inclusion :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks B.inclusion
  have _ : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  refine { isEquivalenceRelation := ?_, etale_source := ?_, etale_target := ?_ }
  · rw [relation_target_eq, relation_source_eq]
    exact isEquivalenceRelation_map (Over.post (X := B.obj hS) B.inclusion) t₀ s₀ hsite
  · rwa [relation_source_eq]
  · rwa [relation_target_eq]

/-- A pair of étale morphisms of the big fppf site over `S` whose represented pair of
morphisms of presheaves is an internal equivalence relation — possibly only after an
isomorphism naming the relation presheaf — is an étale equivalence relation of schemes
over `S`. -/
theorem isEtaleEquivalenceRelation_of_yoneda {R₀ U₀ : BigFppfOver B S hS} (s₀ t₀ : R₀ ⟶ U₀)
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (i : A ≅ yoneda.obj R₀)
    (hrel : IsEquivalenceRelation (i.hom ≫ yoneda.map t₀) (i.hom ≫ yoneda.map s₀))
    (ht : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) t₀)
    (hs : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) s₀) :
    IsEtaleEquivalenceRelation (relation B S hS s₀ t₀) := by
  exact isEtaleEquivalenceRelation_of_isEquivalenceRelation B S hS s₀ t₀
    (isEquivalenceRelation_of_map_of_iso yoneda i t₀ s₀ hrel) ht hs

/-- A pair of étale morphisms of the big fppf site over `S` whose image under a fully faithful
functor is an internal equivalence relation — possibly only after an isomorphism naming the
relation object — is an étale equivalence relation of schemes over `S`. -/
theorem isEtaleEquivalenceRelation_of_embedding {R₀ U₀ : BigFppfOver B S hS} (s₀ t₀ : R₀ ⟶ U₀)
    {D : Type u₂} [Category.{v₂} D] (Φ : BigFppfOver B S hS ⥤ D) [Φ.Full] [Φ.Faithful]
    {A : D} (i : A ≅ Φ.obj R₀)
    (hrel : IsEquivalenceRelation (i.hom ≫ Φ.map t₀) (i.hom ≫ Φ.map s₀))
    (ht : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) t₀)
    (hs : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) s₀) :
    IsEtaleEquivalenceRelation (relation B S hS s₀ t₀) := by
  exact isEtaleEquivalenceRelation_of_isEquivalenceRelation B S hS s₀ t₀
    (isEquivalenceRelation_of_map_of_iso Φ i t₀ s₀ hrel) ht hs

/-! ### Comparing the two quotient presheaves -/

/-- The source map of the relation of schemes over `S` determined by a pair of morphisms of the
site is, on restricted functors of points, the map represented by the source morphism. -/
theorem sourceMap_relation_comp_pointsIsoYoneda {R₀ U₀ : BigFppfOver B S hS} (s₀ t₀ : R₀ ⟶ U₀) :
    sourceMap (Over.post (X := B.obj hS) B.inclusion) (relation B S hS s₀ t₀) ≫
        (pointsIsoYoneda (Over.post (X := B.obj hS) B.inclusion) U₀).hom =
      (pointsIsoYoneda (Over.post (X := B.obj hS) B.inclusion) R₀).hom ≫ yoneda.map s₀ := by
  change Functor.whiskerLeft (Over.post (X := B.obj hS) B.inclusion).op
    (yoneda.map (relation B S hS s₀ t₀).source) ≫ _ = _
  rw [relation_source_eq]
  exact Stacks.Groupoids.pointsIsoYoneda_naturality _ s₀

/-- The target map of the relation of schemes over `S` determined by a pair of morphisms of the
site is, on restricted functors of points, the map represented by the target morphism. -/
theorem targetMap_relation_comp_pointsIsoYoneda {R₀ U₀ : BigFppfOver B S hS} (s₀ t₀ : R₀ ⟶ U₀) :
    targetMap (Over.post (X := B.obj hS) B.inclusion) (relation B S hS s₀ t₀) ≫
        (pointsIsoYoneda (Over.post (X := B.obj hS) B.inclusion) U₀).hom =
      (pointsIsoYoneda (Over.post (X := B.obj hS) B.inclusion) R₀).hom ≫ yoneda.map t₀ := by
  change Functor.whiskerLeft (Over.post (X := B.obj hS) B.inclusion).op
    (yoneda.map (relation B S hS s₀ t₀).target) ≫ _ = _
  rw [relation_target_eq]
  exact Stacks.Groupoids.pointsIsoYoneda_naturality _ t₀

/-- The quotient presheaf of a relation between objects of the big fppf site, formed on the
restricted functors of points, is the quotient presheaf of the relation of presheaves over `Z`
which it represents. -/
def quotientPresheafIsoPoints {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {R : Over Z}
    {R₀ U₀ : BigFppfOver B S hS} {q : yoneda.obj U₀ ⟶ Z} (j : PreRelation R (Over.mk q))
    (s₀ t₀ : R₀ ⟶ U₀) (i : R.left ≅ yoneda.obj R₀)
    (htgt : j.target.left = i.hom ≫ yoneda.map t₀)
    (hsrc : j.source.left = i.hom ≫ yoneda.map s₀) :
    Stacks.Groupoids.quotientPresheaf (Over.post (X := B.obj hS) B.inclusion)
        (relation B S hS s₀ t₀) ≅ quotientPresheaf j :=
  coequalizerIsoOfIso _ _ (yoneda.map s₀) (yoneda.map t₀)
      (pointsIsoYoneda (Over.post (X := B.obj hS) B.inclusion) R₀)
      (pointsIsoYoneda (Over.post (X := B.obj hS) B.inclusion) U₀)
      (sourceMap_relation_comp_pointsIsoYoneda B S hS s₀ t₀)
      (targetMap_relation_comp_pointsIsoYoneda B S hS s₀ t₀) ≪≫
    coequalizerIsoSwap (yoneda.map s₀) (yoneda.map t₀) ≪≫
    coequalizerIsoOfIso (yoneda.map t₀) (yoneda.map s₀) j.target.left j.source.left
      i.symm (Iso.refl _) (by rw [htgt]; simp) (by rw [hsrc]; simp)

/-! ### The quotient of an algebraic space -/

/-- **Stacks 02WW for a relation of algebraic spaces.** The quotient sheaf of an equivalence
relation of algebraic spaces over a presheaf `Z`, whose target and source maps are
representable and étale, is an algebraic space over `S`. -/
theorem isAlgebraicSpace_quotientSheaf_of_isAlgebraicSpace
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {R U : Over Z} (j : PreRelation R U)
    [IsEquivalenceRelation j.target j.source] (hU : IsAlgebraicSpace B S hS U.left)
    (ht : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf j.target.left)
    (hs : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf j.source.left) :
    IsAlgebraicSpace B S hS (quotientSheaf j).obj := by
  have hj : IsPreEquivalenceRelation j :=
    ((isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation j).1 inferInstance).2
  obtain ⟨U₀, R₀, a, t₀, s₀, e, ht₀, hs₀, hetgt, hesrc, hqiso⟩ :=
    exists_etaleSiteRelation_of_isAlgebraicSpace j hj hU ht hs
  have hrestr : IsEquivalenceRelation
      (PreRelation.restrict j (chartInSliceMap U a)).target.left
      (PreRelation.restrict j (chartInSliceMap U a)).source.left :=
    isEquivalenceRelation_left _ _ inferInstance
  rw [hetgt, hesrc] at hrestr
  have _ : IsEtaleEquivalenceRelation (relation B S hS s₀ t₀) :=
    isEtaleEquivalenceRelation_of_embedding B S hS s₀ t₀ yoneda e hrestr ht₀ hs₀
  have halg : IsAlgebraicSpace B S hS
      (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS)
        (Over.post (X := B.obj hS) B.inclusion) (relation B S hS s₀ t₀)).obj :=
    isAlgebraicSpace_quotient_unconditional B S hS s₀ t₀
  have hpre := quotientPresheafIsoPoints B S hS
    (PreRelation.restrict j (chartInSliceMap U a)) s₀ t₀ e hetgt hesrc
  have hiso : (quotientSheaf (PreRelation.restrict j (chartInSliceMap U a))).obj ≅
      (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS)
        (Over.post (X := B.obj hS) B.inclusion) (relation B S hS s₀ t₀)).obj :=
    ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)).mapIso
      ((presheafToSheaf (BigFppfOver.topology B S hS) (Type u)).mapIso hpre)).symm
  have hrestrAlg : IsAlgebraicSpace B S hS
      (quotientSheaf (PreRelation.restrict j (chartInSliceMap U a))).obj :=
    AlgebraicGeometry.isAlgebraicSpace_of_iso B S hS hiso halg
  have hiso' : (quotientSheaf j).obj ≅
      (quotientSheaf (PreRelation.restrict j (chartInSliceMap U a))).obj :=
    ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)).mapIso
      (asIso (restrictQuotientSheafMap j (chartInSliceMap U a)))).symm
  exact AlgebraicGeometry.isAlgebraicSpace_of_iso B S hS hiso' hrestrAlg

end AlgebraicGeometry.Space

end
