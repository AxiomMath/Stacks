module

public import StacksFrontier.AlgebraicGeometry.Stacks.SubcategorySite
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteObjectwiseCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.VanishingAlongAFunctorEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.FullSubcategoryCoveringPullbacks

/-!
# Acyclicity on a slice of a full subsite of the site of an algebraic stack

Stacks 0GR0 compares the cohomology of an abelian sheaf on the étale (respectively fppf) site of
an algebraic stack with the cohomology of its inverse image on the lisse-étale (respectively
flat-fppf) site, over an object of the subsite. The four comparisons of
`StacksFrontier/AlgebraicGeometry/Stacks/SubsiteObjectwiseCohomology.lean` take one hypothesis,
`hacyclic`, which is **Stacks 0D6X** for the inclusion of the
subsite localized at the object: an injective abelian sheaf on the slice of the ambient site
restricts to a sheaf with no higher cohomology on the slice of the subsite. This file proves it.

## The covering pullbacks of the inclusion

Stacks 0D6X is available with the morphism universes of both sites free, as
`Stacks.CechSite.injective_sheaf_subsingleton_sheafH_of_functor`, and what it asks for beyond
continuity is the covering data of Stacks 00WV: a cofinal system of covering families admitting
the iterated fibre products of their arrows, preserved by the functor. That is the content of
`Stacks.Sites.PreservesCoveringPullbacks`, and it is *not* the statement that the subsite has
fibre products — it does not. A fibre product of two flat objects over a flat object need not be
flat; what is flat is the fibre product of a *covering* morphism of the flat-fppf site with an
arbitrary morphism, because such a covering morphism lies over a flat and locally finitely
presented morphism of schemes, and so does its base change.

That is exactly the closure condition of Stacks 07AK (1), which is what makes the inclusion
continuous and cocontinuous in the first place, and which holds for every algebraic stack. So the
covering-pullback condition is available with no hypothesis beyond the ones already discharged,
through `CategoryTheory.ObjectProperty.preservesCoveringPullbacks_over_ι`.

## Main results

* `AlgebraicGeometry.Stack.preservesCoveringPullbacks_over_ι_associatedTopology`: the
  covering-pullback condition of Stacks 00WV for the slice of the inclusion of a full subsite
  closed under the morphisms lying over a class `Q` of morphisms of schemes by which the ambient
  topology is refinable.
* `AlgebraicGeometry.Stack.FlatFppf.preservesCoveringPullbacks_over_inclusion` and
  `AlgebraicGeometry.Stack.LisseEtale.preservesCoveringPullbacks_over_inclusion`: that condition
  for the flat-fppf and the lisse-étale site of an algebraic stack, with no hypothesis.
* `AlgebraicGeometry.Stack.subsiteSliceCohomology_eq_zero`: **Stacks 0D6X** for the inclusion of a
  full subsite, localized at an object.
* `AlgebraicGeometry.Stack.FlatFppf.sliceAcyclic` and
  `AlgebraicGeometry.Stack.LisseEtale.sliceAcyclic`: the hypothesis `hacyclic` of the two
  abelian-sheaf clauses of Stacks 0GR0, discharged.
* `AlgebraicGeometry.Stack.FlatFppf.cohomologyOverObjectIso'` and
  `AlgebraicGeometry.Stack.LisseEtale.cohomologyOverObjectIso'`: **Stacks 0GR0** (2)(b) and (1)(b)
  with no hypothesis.

## References

* [Stacks Project, Tag 00WV](https://stacks.math.columbia.edu/tag/00WV)
* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK)
* [Stacks Project, Tag 0D6X](https://stacks.math.columbia.edu/tag/0D6X)
* [Stacks Project, Tag 0GR0](https://stacks.math.columbia.edu/tag/0GR0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Abelian

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS)

/-! ### The covering pullbacks of the inclusion of a full subsite -/

/-- A category fibred in groupoids over the big fppf category has pullbacks, since the fibre
products exist for strongly cartesian arrows. -/
private theorem hasPullbacks_of_isFiberedInGroupoids (hp : p.IsFiberedInGroupoids) :
    HasPullbacks X :=
  haveI := hp.isFibered
  @hasPullbacks_of_hasLimit_cospan _ _ fun {_ _ _} {f g} =>
    p.hasPullback_of_forall_isStronglyCartesian
      (fun f => hp.isStronglyCartesian_homLift (p.map f) f) f g

/-- **The covering-pullback condition of Stacks 00WV for a slice of the inclusion of a full
subsite.** Let `p : 𝒳 ⥤ (Sch/S)` be a category fibred in groupoids over the big fppf category of
a scheme `S` in `B`, endowed with the site of Stacks 06TP for a topology `τ` on the underlying
category of schemes of `B`, and let `P` cut out a full subcategory of `𝒳` closed under the
morphisms lying over `Q`-morphisms of schemes. If every `τ`-covering sieve is refined by a
covering family of `Q`-morphisms, then for every object `x` of `P` the slice functor
`Over.post P.ι` admits the covering pullbacks of Stacks 00WV on the slice at `x` of the topology
the subcategory inherits.

These are the hypotheses of `AlgebraicGeometry.Stack.isContinuous_ι_associatedTopology`: the
closure condition of Stacks 07AK (1) is all that is needed, over and above the fibre products of
the ambient fibred category, which exist by Stacks 06WY. -/
theorem preservesCoveringPullbacks_over_ι_associatedTopology (Q : MorphismProperty Scheme.{u})
    (hp : p.IsFiberedInGroupoids) (τ : GrothendieckTopology B.Schemes) (P : ObjectProperty X)
    [MorphismProperty.ContainsIdentities Q] [MorphismProperty.IsStableUnderComposition Q]
    [MorphismProperty.IsStableUnderBaseChange Q]
    (hτ : ∀ ⦃V : B.Schemes⦄ (T : Sieve V), T ∈ τ V →
      τ.IsRefinableBy (Q.inverseImage B.inclusion) T)
    (hclose : ∀ ⦃x y : X⦄ (f : x ⟶ y), Q (B.inclusion.map (p.map f).left) → P y → P x)
    (x : P.FullSubcategory) :
    Stacks.Sites.PreservesCoveringPullbacks ((subsiteTopology B S hS p τ P).over x)
      (Over.post (X := x) P.ι) := by
  have hcart : ∀ {a b : X} (f : a ⟶ b), p.IsStronglyCartesian (p.map f) f := fun f =>
    hp.isStronglyCartesian_homLift (p.map f) f
  have : p.IsFibered := hp.isFibered
  have := hasPullbacks_of_isFiberedInGroupoids B S hS p hp
  have := p.isStableUnderBaseChange_inverseImage hcart
    ((Q.inverseImage B.inclusion).inverseImage (BigFppfOver.forget B S hS))
  exact ObjectProperty.preservesCoveringPullbacks_over_ι
    (Q := ((Q.inverseImage B.inclusion).inverseImage
      (BigFppfOver.forget B S hS)).inverseImage p)
    (fun _ _ _ g f _ ↦ inferInstance)
    (fun _ _ f hf hy ↦ hclose f hf hy)
    (isRefinableBy_associatedTopology B S hS p Q hp τ hτ) x

/-- The covering-pullback condition of Stacks 00WV for a slice of the inclusion of a full subsite,
for an ambient topology generated by a chosen collection of covering families whose members lie
over `Q`-morphisms of schemes. -/
theorem preservesCoveringPullbacks_over_ι_associatedTopology_of_members
    (Q : MorphismProperty Scheme.{u}) (hp : p.IsFiberedInGroupoids)
    (K : Precoverage B.Schemes) (P : ObjectProperty X)
    [MorphismProperty.ContainsIdentities Q] [MorphismProperty.IsStableUnderComposition Q]
    [MorphismProperty.IsStableUnderBaseChange Q]
    (hK : ∀ ⦃V : B.Schemes⦄ (R : Presieve V), R ∈ K V →
      ∀ ⦃W : B.Schemes⦄ (g : W ⟶ V), R g → Q (B.inclusion.map g))
    (hclose : ∀ ⦃x y : X⦄ (f : x ⟶ y), Q (B.inclusion.map (p.map f).left) → P y → P x)
    (x : P.FullSubcategory) :
    Stacks.Sites.PreservesCoveringPullbacks
      ((subsiteTopology B S hS p K.toGrothendieck P).over x) (Over.post (X := x) P.ι) :=
  preservesCoveringPullbacks_over_ι_associatedTopology B S hS p Q hp _ P
    (isRefinableBy_toGrothendieck_of_members B Q K hK) hclose x

/-! ### Stacks 0D6X for a slice of the inclusion of a full subsite -/

/-- **Stacks 0D6X for a slice of the inclusion of a full subsite.** Let `P` cut out a full
subcategory of the objects of a category fibred in groupoids over the big fppf category of `S`,
let `x` be an object of `P`, and suppose the covering morphisms of the slice at `x` of the subsite
admit the fibre products of Stacks 00WV, preserved by the slice functor. Then the restriction
along that functor of an injective abelian sheaf on the slice of the ambient site at `x` has
vanishing cohomology in positive degrees.

Cohomology over `x` is the global cohomology of the slice at `x`, which is cohomology over the
terminal object `id : x ⟶ x` of that slice. The coefficient universe is the join of the two
universes of the site, which is where the sheaves on these slices live and which is what
`Stacks.CechSite.injective_sheaf_subsingleton_sheafH_of_functor` allows, neither site being
small. -/
@[stacks 0D6X "for the inclusion of a full subsite of the site of Stacks 06TP, localized at an \
object of the subsite"]
theorem subsiteSliceCohomology_eq_zero (hp : p.IsFiberedInGroupoids)
    (τ : GrothendieckTopology B.Schemes) (P : ObjectProperty X)
    [P.ι.IsContinuous (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)]
    (x : P.FullSubcategory)
    [Stacks.Sites.PreservesCoveringPullbacks ((subsiteTopology B S hS p τ P).over x)
      (Over.post (X := x) P.ι)]
    (I : Sheaf ((associatedTopology B S hS p τ).over (P.ι.obj x)) AddCommGrpCat.{max v w})
    [Injective I] (n : ℕ)
    (a : Sheaf.H ((subsiteSliceRestriction B S hS p τ P x).obj I) (n + 1)) : a = 0 := by
  have := hasPullbacks_of_isFiberedInGroupoids B S hS p hp
  have := Functor.isContinuous_overPost (subsiteTopology B S hS p τ P)
    (associatedTopology B S hS p τ) P.ι x
  set J := (subsiteTopology B S hS p τ P).over x with hJ
  set u := Over.post (X := x) P.ι with hu
  set Cov : ∀ U : Over x, Set { E : PreZeroHypercover.{max v w} U // E.sieve₀ ∈ J U } :=
    fun U => { E | (∀ (j : E.1.I₀) ⦃W : Over x⦄ (g : W ⟶ U), HasPullback (E.1.f j) g) ∧
      (∀ (j : E.1.I₀) ⦃W : Over x⦄ (g : W ⟶ U),
        PreservesLimit (cospan (E.1.f j) g) u) } with hCov
  have hProducts : ∀ {U : Over x}
      (E : { E : PreZeroHypercover.{max v w} U // E.sieve₀ ∈ J U }),
      E ∈ Cov U → ∀ (q : ℕ) (i : Fin (q + 1) → E.1.I₀),
        HasProduct (fun b ↦ Over.mk (E.1.f (i b))) :=
    fun E hE q i => Stacks.Sites.hasProduct_fibreProducts E.1 hE.1 q i
  have hImageProducts : ∀ {U : Over x}
      (E : { E : PreZeroHypercover.{max v w} U // E.sieve₀ ∈ J U }),
      E ∈ Cov U → ∀ (q : ℕ) (i : Fin (q + 1) → (E.1.map u).I₀),
        HasProduct (fun b ↦ Over.mk ((E.1.map u).f (i b))) :=
    fun E _ q i =>
      Stacks.Sites.hasProduct_fibreProducts (E.1.map u) (fun _ _ _ => inferInstance) q i
  have hsub := Stacks.CechSite.injective_sheaf_subsingleton_sheafH_of_functor.{max v w, v}
    J ((associatedTopology B S hS p τ).over (P.ι.obj x)) u Set.univ Cov hProducts hImageProducts
    (fun E _ => ⟨Set.mem_univ _, fun _ => Set.mem_univ _, fun _ _ => Set.mem_univ _⟩)
    (fun U _ R hR => by
      obtain ⟨E, hJE, hle, hpb, hpr⟩ := Stacks.Sites.exists_preZeroHypercover_le J u R hR
      exact ⟨⟨E, hJE⟩, ⟨hpb, hpr⟩, hle⟩)
    (fun E hE q i => by
      let := hProducts E hE
      let := hImageProducts E hE
      let := Stacks.Sites.preservesLimit_fibreProducts_overPost u E.1 hE.1 hE.2 q i
      exact Stacks.CechSite.isIso_cechProductMapOfFunctor u E.1 q i)
    I Over.mkIdTerminal (Set.mem_univ _) (n + 1) n.succ_pos
  exact hsub.elim a 0

/-! ### The two topologies of Stacks 07AK -/

/-- The covering-pullback condition of Stacks 00WV for a slice of the inclusion of a full subsite
of the fppf site of Stacks 06TP, closed under the morphisms lying over a flat and locally finitely
presented morphism of schemes. -/
theorem preservesCoveringPullbacks_over_ι_fppfTopology (hp : p.IsFiberedInGroupoids)
    (P : ObjectProperty X)
    (hclose : ∀ ⦃x y : X⦄ (f : x ⟶ y), Flat (B.inclusion.map (p.map f).left) →
      LocallyOfFinitePresentation (B.inclusion.map (p.map f).left) → P y → P x)
    (x : P.FullSubcategory) :
    Stacks.Sites.PreservesCoveringPullbacks
      ((subsiteTopology B S hS p B.topology P).over x) (Over.post (X := x) P.ι) := by
  have : MorphismProperty.ContainsIdentities
      ((@Flat : MorphismProperty Scheme.{u}) ⊓ @LocallyOfFinitePresentation) :=
    ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩⟩
  have : MorphismProperty.IsStableUnderComposition
      ((@Flat : MorphismProperty Scheme.{u}) ⊓ @LocallyOfFinitePresentation) :=
    MorphismProperty.IsStableUnderComposition.inf
  have : MorphismProperty.IsStableUnderBaseChange
      ((@Flat : MorphismProperty Scheme.{u}) ⊓ @LocallyOfFinitePresentation) :=
    MorphismProperty.IsStableUnderBaseChange.inf
  exact preservesCoveringPullbacks_over_ι_associatedTopology_of_members B S hS p
    ((@Flat : MorphismProperty Scheme.{u}) ⊓ @LocallyOfFinitePresentation) hp B.precoverage P
    (flat_and_locallyOfFinitePresentation_of_mem_precoverage B)
    (fun _ _ f hf ↦ hclose f hf.1 hf.2) x

/-- The covering-pullback condition of Stacks 00WV for a slice of the inclusion of a full subsite
of the étale site of Stacks 06TP — for any of the chosen étale precoverages of Stacks 03FF —
closed under the morphisms lying over a smooth morphism of schemes. -/
theorem preservesCoveringPullbacks_over_ι_etaleTopology (hp : p.IsFiberedInGroupoids)
    (K : Precoverage B.Schemes)
    (hK : ∀ ⦃V : B.Schemes⦄ (R : Presieve V), R ∈ K V →
      R.map B.inclusion ∈ Scheme.etalePrecoverage (B.inclusion.obj V))
    (P : ObjectProperty X)
    (hclose : ∀ ⦃x y : X⦄ (f : x ⟶ y), Smooth (B.inclusion.map (p.map f).left) → P y → P x)
    (x : P.FullSubcategory) :
    Stacks.Sites.PreservesCoveringPullbacks
      ((subsiteTopology B S hS p K.toGrothendieck P).over x) (Over.post (X := x) P.ι) :=
  preservesCoveringPullbacks_over_ι_associatedTopology_of_members B S hS p (@Smooth) hp K P
    (smooth_of_mem_of_map_mem_etalePrecoverage B K hK) hclose x

/-! ### The flat-fppf site -/

namespace FlatFppf

variable (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

/-- **The covering-pullback condition of Stacks 00WV for a slice of the inclusion of the flat-fppf
site.** No hypothesis: the closure condition of Stacks 07AK (1) holds for every algebraic stack,
by `AlgebraicGeometry.Stack.FlatFppf.closedUnderFlatMorphisms`. -/
theorem preservesCoveringPullbacks_over_inclusion
    (x : ObjectProperty.FullSubcategory (objectProperty B S hS 𝒳)) :
    Stacks.Sites.PreservesCoveringPullbacks ((inclusionTopology B S hS 𝒳).over x)
      (Over.post (X := x) (objectProperty B S hS 𝒳).ι) :=
  preservesCoveringPullbacks_over_ι_fppfTopology B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids _ (closedUnderFlatMorphisms B S hS 𝒳) x

/-- **Stacks 0D6X for the inclusion of the flat-fppf site, localized at a flat object.** The
restriction to the slice at `x` of the flat-fppf site of an injective abelian sheaf on the slice
at `x` of the fppf site of an algebraic stack has vanishing cohomology in positive degrees.

This is the hypothesis `hacyclic` of
`AlgebraicGeometry.Stack.FlatFppf.cohomologyOverObjectIso`, part (2)(b) of Stacks 0GR0. -/
@[stacks 0D6X "for the inclusion of the flat-fppf site of Stacks 0787, localized at a flat object"]
theorem sliceAcyclic (x : ObjectProperty.FullSubcategory (objectProperty B S hS 𝒳)) :
    haveI := isContinuous_inclusion B S hS 𝒳 (closedUnderFlatMorphisms B S hS 𝒳)
    ∀ I : Sheaf ((fppfTopology B S hS 𝒳).over ((objectProperty B S hS 𝒳).ι.obj x))
        AddCommGrpCat.{u + 1}, Injective I → ∀ (n : ℕ)
      (a : Sheaf.H ((subsiteSliceRestriction B S hS 𝒳.val.val.p B.topology
        (objectProperty B S hS 𝒳) x).obj I) (n + 1)), a = 0 := by
  have := isContinuous_inclusion B S hS 𝒳 (closedUnderFlatMorphisms B S hS 𝒳)
  have := preservesCoveringPullbacks_over_inclusion B S hS 𝒳 x
  intro I hI n a
  have := hI
  exact subsiteSliceCohomology_eq_zero B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    B.topology (objectProperty B S hS 𝒳) x I n a

/-- **Stacks 0GR0, part (2)(b).** For an algebraic stack `𝒳`, an abelian sheaf `F` on the fppf
site of `𝒳` and a flat object `x` of `𝒳`,

`H^q(x, F) = H^q(𝒳_{flat,fppf}/x, g⁻¹ F)`,

naturally in `F`, where `g⁻¹` is restriction to the flat-fppf site of Stacks 0787 and cohomology
over an object is the global cohomology on the slice site.

This is `AlgebraicGeometry.Stack.FlatFppf.cohomologyOverObjectIso` with its acyclicity hypothesis
discharged by `AlgebraicGeometry.Stack.FlatFppf.sliceAcyclic`. -/
@[stacks 0GR0 "part (2)(b), cohomology over a flat object"]
def cohomologyOverObjectIso'
    (x : ObjectProperty.FullSubcategory (objectProperty B S hS 𝒳)) (q : ℕ) :
    haveI := isContinuous_inclusion B S hS 𝒳 (closedUnderFlatMorphisms B S hS 𝒳)
    haveI := Functor.isContinuous_overPost (inclusionTopology B S hS 𝒳)
      (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι x
    (objectProperty B S hS 𝒳).ι.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳) ⋙
        (inclusionTopology B S hS 𝒳).overPullback AddCommGrpCat.{u + 1} x ⋙
          Sheaf.functorH ((inclusionTopology B S hS 𝒳).over x) q ≅
      (fppfTopology B S hS 𝒳).overPullback AddCommGrpCat.{u + 1}
            ((objectProperty B S hS 𝒳).ι.obj x) ⋙
        Sheaf.functorH ((fppfTopology B S hS 𝒳).over
          ((objectProperty B S hS 𝒳).ι.obj x)) q :=
  cohomologyOverObjectIso B S hS 𝒳 x (sliceAcyclic B S hS 𝒳 x) q

end FlatFppf

/-! ### The lisse-étale site -/

namespace LisseEtale

variable (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

/-- **The covering-pullback condition of Stacks 00WV for a slice of the inclusion of the
lisse-étale site.** No hypothesis: the closure condition of Stacks 07AK (1) for the smooth objects
holds for every algebraic stack, by
`AlgebraicGeometry.Stack.LisseEtale.closedUnderSmoothMorphisms`. -/
theorem preservesCoveringPullbacks_over_inclusion
    (x : ObjectProperty.FullSubcategory (smoothObject.{u, w} B S hS 𝒳)) :
    Stacks.Sites.PreservesCoveringPullbacks ((inclusionTopology.{u, w} B S hS 𝒳).over x)
      (Over.post (X := x) (smoothObject.{u, w} B S hS 𝒳).ι) :=
  preservesCoveringPullbacks_over_ι_etaleTopology B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids (etalePrecoverage B) (map_mem_etalePrecoverage B) _
    (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳) x

/-- **Stacks 0D6X for the inclusion of the lisse-étale site, localized at a smooth object.** The
restriction to the slice at `x` of the lisse-étale site of an injective abelian sheaf on the slice
at `x` of the étale site of an algebraic stack has vanishing cohomology in positive degrees.

This is the hypothesis `hacyclic` of
`AlgebraicGeometry.Stack.LisseEtale.cohomologyOverObjectIso`, part (1)(b) of Stacks 0GR0. -/
@[stacks 0D6X "for the inclusion of the lisse-étale site of Stacks 0787, localized at a smooth \
object"]
theorem sliceAcyclic (x : ObjectProperty.FullSubcategory (smoothObject.{u, w} B S hS 𝒳)) :
    haveI := isContinuous_inclusion B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
    ∀ I : Sheaf ((associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)).over
        ((smoothObject.{u, w} B S hS 𝒳).ι.obj x)) AddCommGrpCat.{u + 1},
        Injective I → ∀ (n : ℕ)
      (a : Sheaf.H ((subsiteSliceRestriction B S hS 𝒳.val.val.p (etaleTopology B)
        (smoothObject.{u, w} B S hS 𝒳) x).obj I) (n + 1)), a = 0 := by
  have := isContinuous_inclusion B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
  have := preservesCoveringPullbacks_over_inclusion B S hS 𝒳 x
  intro I hI n a
  have := hI
  exact subsiteSliceCohomology_eq_zero B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    (etaleTopology B) (smoothObject.{u, w} B S hS 𝒳) x I n a

/-- **Stacks 0GR0, part (1)(b).** For an algebraic stack `𝒳`, an abelian sheaf `F` on the étale
site of `𝒳` and a smooth object `x` of `𝒳`,

`H^q(x, F) = H^q(𝒳_{lisse,étale}/x, g⁻¹ F)`,

naturally in `F`, where `g⁻¹` is restriction to the lisse-étale site of Stacks 0787.

This is `AlgebraicGeometry.Stack.LisseEtale.cohomologyOverObjectIso` with its acyclicity
hypothesis discharged by `AlgebraicGeometry.Stack.LisseEtale.sliceAcyclic`. -/
@[stacks 0GR0 "part (1)(b), cohomology over a smooth object"]
def cohomologyOverObjectIso'
    (x : ObjectProperty.FullSubcategory (smoothObject.{u, w} B S hS 𝒳)) (q : ℕ) :
    haveI := isContinuous_inclusion B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
    haveI := Functor.isContinuous_overPost (inclusionTopology.{u, w} B S hS 𝒳)
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
      (smoothObject.{u, w} B S hS 𝒳).ι x
    (smoothObject.{u, w} B S hS 𝒳).ι.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (inclusionTopology.{u, w} B S hS 𝒳)
          (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) ⋙
        (inclusionTopology.{u, w} B S hS 𝒳).overPullback AddCommGrpCat.{u + 1} x ⋙
          Sheaf.functorH ((inclusionTopology.{u, w} B S hS 𝒳).over x) q ≅
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)).overPullback
            AddCommGrpCat.{u + 1} ((smoothObject.{u, w} B S hS 𝒳).ι.obj x) ⋙
        Sheaf.functorH ((associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)).over
          ((smoothObject.{u, w} B S hS 𝒳).ι.obj x)) q :=
  cohomologyOverObjectIso B S hS 𝒳 x (sliceAcyclic B S hS 𝒳 x) q

end LisseEtale

end AlgebraicGeometry.Stack

end
