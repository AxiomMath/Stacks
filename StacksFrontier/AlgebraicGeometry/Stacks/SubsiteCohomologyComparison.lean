module

public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteAcyclicity
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteGlobalCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.AbelianDerivedExistence

/-!
# Cohomology over an object of a full subsite, and the global comparison of Stacks 07AK

Stacks 07AK compares the cohomology of an abelian sheaf on the étale (respectively fppf) site of
an algebraic stack with that of its inverse image on a full subsite closed under the relevant
pullbacks and containing a surjective atlas:

`H^p(𝒳'_τ, g⁻¹ℱ) = H^p(𝒳_τ, ℱ)`.

The source proves this in two steps. The first is the comparison *over an object `x` of the
subsite*, which rests on the acyclicity statement of Stacks 0D6X for the inclusion. That step is
proved here unconditionally, on the subsite itself rather than on its slice. The second step
globalizes it along the atlas, and is where the two hypotheses of
`AlgebraicGeometry.Stack.subsiteCohomologyIso` come from; this file instantiates that reduction
for the flat-fppf and lisse-étale subsites.

## Cohomology over an object of a site

For an object `x` of a site `(𝒞, J)` the group `H^p(x, ℱ)` is `Ext^p` out of the free abelian
sheaf on the presheaf represented by `x` — `CategoryTheory.extensionByZeroUnitAb` — which is the
convention of Stacks 03YU and the one the universe-free form of Stacks 0D6X,
`Stacks.CechSite.injective_sheaf_subsingleton_ext_of_functor`, is stated with. It is *not* the
global cohomology of the slice `𝒞/x`: the two agree by the localization comparison of Stacks
03F3, which is available only on a small site, whereas the sites here are not small. The slice
form of the same statements is `StacksFrontier/AlgebraicGeometry/Stacks/SubsiteAcyclicity.lean`.

## Main results

* `CategoryTheory.ObjectProperty.preservesCoveringPullbacks_ι`: the covering-pullback condition
  of Stacks 00WV for the inclusion of a full subsite closed under a class `Q` of morphisms by
  which the ambient topology is refinable. Unlike
  `CategoryTheory.ObjectProperty.preservesCoveringPullbacks_over_ι` this is the condition on the
  inclusion itself, not on its slices.
* `AlgebraicGeometry.Stack.preservesCoveringPullbacks_ι_associatedTopology` and its two
  specializations: that condition for a full subsite of the site of Stacks 06TP.
* `AlgebraicGeometry.Stack.subsiteObjectCohomology_eq_zero`: **Stacks 0D6X** for the inclusion of
  a full subsite, over an object of the subsite.
* `AlgebraicGeometry.Stack.FlatFppf.objectAcyclic` and
  `AlgebraicGeometry.Stack.LisseEtale.objectAcyclic`: the same for the flat-fppf and the
  lisse-étale site of an algebraic stack, with no hypothesis.
* `AlgebraicGeometry.Stack.FlatFppf.cohomologyIso` and
  `AlgebraicGeometry.Stack.LisseEtale.cohomologyIso`: the global comparison of Stacks 07AK for the
  two subsites the source names, reduced to its own degree-zero case and to the global form of
  Stacks 0D6X. Both inputs are proved for every full subcategory satisfying the two conditions
  of Stacks 07AK in `StacksFrontier/AlgebraicGeometry/Stacks/SubsiteCohomologyAtlas.lean`, which
  carries the registration of the tag.

## The two data of the reduction

`AlgebraicGeometry.Stack.subsiteCohomologyIso` derives the comparison in every degree from two
data: the comparison of the constant sheaves `g_!ℤ_{𝒳'} ≅ ℤ_𝒳`, which by the adjunction
`g_! ⊣ g⁻¹` is exactly the comparison in degree zero, and the global form of Stacks 0D6X — the
vanishing of `H^{≥1}(𝒳'_τ, g⁻¹I)` for an injective abelian sheaf `I` on `𝒳_τ`. The library's form of
0D6X for *global* cohomology, `Stacks.CechSite.injective_sheaf_subsingleton_sheafH_of_functor`,
asks for a terminal object of the source site, which neither subsite has as soon as the stack has
a nontrivial automorphism, by
`CategoryTheory.Functor.IsFiberedInGroupoids.not_isTerminal_of_faithful_of_ne_id`. Both data are
instead obtained from the atlas of Stacks 07AK (2) in
`StacksFrontier/AlgebraicGeometry/Stacks/SubsiteCohomologyAtlas.lean`, by descent along the Čech
nerve of the atlas, through
`StacksFrontier/CategoryTheory/Sites/Cohomology/CoverDescent/Cohomology.lean`.

What the objectwise comparison below supplies is the comparison over an object `x` of the
subsite: cohomology over `x` is the same computed on `𝒳'_τ` and on `𝒳_τ`.

## References

* [Stacks Project, Tag 00WV](https://stacks.math.columbia.edu/tag/00WV)
* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
* [Stacks Project, Tag 079Z](https://stacks.math.columbia.edu/tag/079Z)
* [Stacks Project, Tag 07A0](https://stacks.math.columbia.edu/tag/07A0)
* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK)
* [Stacks Project, Tag 0D6X](https://stacks.math.columbia.edu/tag/0D6X)
* [Stacks Project, Tag 0GR0](https://stacks.math.columbia.edu/tag/0GR0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Abelian
open Stacks.Cohomology.DerivedLowerShriek

/-! ### Covering pullbacks of the inclusion of a full subsite -/

namespace CategoryTheory.ObjectProperty

universe v u

variable {C : Type u} [Category.{v} C] {P : ObjectProperty C} {J : GrothendieckTopology C}
  {Q : MorphismProperty C}

/-- **The covering-pullback condition of Stacks 00WV for the inclusion of a full subsite.** Let
`(𝒞, J)` be a site, let `Q` be a property of morphisms of `𝒞`, stable under base change and having
fibre products against arbitrary morphisms of the same target, by which every `J`-covering sieve
is refinable, and let `P` be a property of objects closed under `Q`. Then the inclusion of the
full subcategory cut out by `P` satisfies the covering-pullback clause of continuity for the
inherited topology.

This is `CategoryTheory.ObjectProperty.preservesCoveringPullbacks_over_ι` for the inclusion
itself rather than for its slices, and it is the form the objectwise acyclicity statement of
Stacks 0D6X consumes. The full subcategory is not assumed to have fibre products — it does not;
what the condition asks for is the fibre products of the arrows of a cofinal system of covering
families, which here are the families of `Q`-morphisms. -/
theorem preservesCoveringPullbacks_ι [Q.ContainsIdentities] [Q.IsStableUnderComposition]
    [Q.IsStableUnderBaseChange]
    (hQpb : ∀ ⦃X Y Z : C⦄ (g : Y ⟶ X) (f : Z ⟶ X), Q g → HasPullback g f)
    (hPQ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Q f → P Y → P X)
    (hJQ : ∀ ⦃X : C⦄ (S : Sieve X), S ∈ J X → J.IsRefinableBy Q S) :
    Stacks.Sites.PreservesCoveringPullbacks (P.ι.inheritedTopology J) P.ι where
  exists_cover U S hS := by
    obtain ⟨R, hRS, hRQ, hRJ⟩ := isRefinableBy_inheritedTopology hPQ hJQ S hS
    refine ⟨R, hRJ, hRS, fun _ f hf _ g ↦ ?_⟩
    obtain ⟨w, A, b, hup, hdown⟩ := exists_isPullback_ι hQpb hPQ f g (hRQ f hf)
    exact ⟨⟨⟨_, hup.isLimit⟩⟩, preservesLimit_of_preserves_limit_cone hup.isLimit
      ((isLimitMapConePullbackConeEquiv P.ι hup.w).symm hdown.isLimit)⟩

end CategoryTheory.ObjectProperty

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS)

/-! ### Covering pullbacks of the inclusion of a full subsite of the site of Stacks 06TP -/

/-- **The covering-pullback condition of Stacks 00WV for the inclusion of a full subsite of the
site of Stacks 06TP.** Let `p : 𝒳 ⥤ (Sch/S)` be a category fibred in groupoids over the big fppf
category of a scheme `S` in `B`, endowed with the site of Stacks 06TP for a topology `τ` on the
underlying category of schemes of `B`, and let `P` cut out a full subcategory of `𝒳` closed under
the morphisms lying over `Q`-morphisms of schemes. If every `τ`-covering sieve is refined by a
covering family of `Q`-morphisms, then the inclusion `P.ι` admits the covering pullbacks of
Stacks 00WV on the topology the subcategory inherits.

These are the hypotheses of `AlgebraicGeometry.Stack.isContinuous_ι_associatedTopology`: the
closure condition of Stacks 07AK (1) is all that is needed, over and above the fibre products of
the ambient fibred category, which exist by Stacks 06WY. -/
theorem preservesCoveringPullbacks_ι_associatedTopology (Q : MorphismProperty Scheme.{u})
    (hp : p.IsFiberedInGroupoids) (τ : GrothendieckTopology B.Schemes) (P : ObjectProperty X)
    [MorphismProperty.ContainsIdentities Q] [MorphismProperty.IsStableUnderComposition Q]
    [MorphismProperty.IsStableUnderBaseChange Q]
    (hτ : ∀ ⦃V : B.Schemes⦄ (T : Sieve V), T ∈ τ V →
      τ.IsRefinableBy (Q.inverseImage B.inclusion) T)
    (hclose : ∀ ⦃x y : X⦄ (f : x ⟶ y), Q (B.inclusion.map (p.map f).left) → P y → P x) :
    Stacks.Sites.PreservesCoveringPullbacks (subsiteTopology B S hS p τ P) P.ι := by
  have hcart : ∀ {a b : X} (f : a ⟶ b), p.IsStronglyCartesian (p.map f) f := fun f =>
    hp.isStronglyCartesian_homLift (p.map f) f
  have : p.IsFibered := hp.isFibered
  have := p.isStableUnderBaseChange_inverseImage hcart
    ((Q.inverseImage B.inclusion).inverseImage (BigFppfOver.forget B S hS))
  exact ObjectProperty.preservesCoveringPullbacks_ι
    (Q := ((Q.inverseImage B.inclusion).inverseImage
      (BigFppfOver.forget B S hS)).inverseImage p)
    (fun _ _ _ g f _ ↦ p.hasPullback_of_forall_isStronglyCartesian hcart g f)
    (fun _ _ f hf hy ↦ hclose f hf hy)
    (isRefinableBy_associatedTopology B S hS p Q hp τ hτ)

/-- The covering-pullback condition of Stacks 00WV for the inclusion of a full subsite, for an
ambient topology generated by a chosen collection of covering families whose members lie over
`Q`-morphisms of schemes. -/
theorem preservesCoveringPullbacks_ι_associatedTopology_of_members
    (Q : MorphismProperty Scheme.{u}) (hp : p.IsFiberedInGroupoids)
    (K : Precoverage B.Schemes) (P : ObjectProperty X)
    [MorphismProperty.ContainsIdentities Q] [MorphismProperty.IsStableUnderComposition Q]
    [MorphismProperty.IsStableUnderBaseChange Q]
    (hK : ∀ ⦃V : B.Schemes⦄ (R : Presieve V), R ∈ K V →
      ∀ ⦃W : B.Schemes⦄ (g : W ⟶ V), R g → Q (B.inclusion.map g))
    (hclose : ∀ ⦃x y : X⦄ (f : x ⟶ y), Q (B.inclusion.map (p.map f).left) → P y → P x) :
    Stacks.Sites.PreservesCoveringPullbacks
      (subsiteTopology B S hS p K.toGrothendieck P) P.ι :=
  preservesCoveringPullbacks_ι_associatedTopology B S hS p Q hp _ P
    (isRefinableBy_toGrothendieck_of_members B Q K hK) hclose

/-- The covering-pullback condition of Stacks 00WV for the inclusion of a full subsite of the
fppf site of Stacks 06TP, closed under the morphisms lying over a flat and locally finitely
presented morphism of schemes. -/
theorem preservesCoveringPullbacks_ι_fppfTopology (hp : p.IsFiberedInGroupoids)
    (P : ObjectProperty X)
    (hclose : ∀ ⦃x y : X⦄ (f : x ⟶ y), Flat (B.inclusion.map (p.map f).left) →
      LocallyOfFinitePresentation (B.inclusion.map (p.map f).left) → P y → P x) :
    Stacks.Sites.PreservesCoveringPullbacks (subsiteTopology B S hS p B.topology P) P.ι := by
  have : MorphismProperty.ContainsIdentities
      ((@Flat : MorphismProperty Scheme.{u}) ⊓ @LocallyOfFinitePresentation) :=
    ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩⟩
  have : MorphismProperty.IsStableUnderComposition
      ((@Flat : MorphismProperty Scheme.{u}) ⊓ @LocallyOfFinitePresentation) :=
    MorphismProperty.IsStableUnderComposition.inf
  have : MorphismProperty.IsStableUnderBaseChange
      ((@Flat : MorphismProperty Scheme.{u}) ⊓ @LocallyOfFinitePresentation) :=
    MorphismProperty.IsStableUnderBaseChange.inf
  exact preservesCoveringPullbacks_ι_associatedTopology_of_members B S hS p
    ((@Flat : MorphismProperty Scheme.{u}) ⊓ @LocallyOfFinitePresentation) hp B.precoverage P
    (flat_and_locallyOfFinitePresentation_of_mem_precoverage B)
    (fun _ _ f hf ↦ hclose f hf.1 hf.2)

/-- The covering-pullback condition of Stacks 00WV for the inclusion of a full subsite of the
étale site of Stacks 06TP — for any of the chosen étale precoverages of Stacks 03FF — closed
under the morphisms lying over a smooth morphism of schemes. -/
theorem preservesCoveringPullbacks_ι_etaleTopology (hp : p.IsFiberedInGroupoids)
    (K : Precoverage B.Schemes)
    (hK : ∀ ⦃V : B.Schemes⦄ (R : Presieve V), R ∈ K V →
      R.map B.inclusion ∈ Scheme.etalePrecoverage (B.inclusion.obj V))
    (P : ObjectProperty X)
    (hclose : ∀ ⦃x y : X⦄ (f : x ⟶ y), Smooth (B.inclusion.map (p.map f).left) → P y → P x) :
    Stacks.Sites.PreservesCoveringPullbacks
      (subsiteTopology B S hS p K.toGrothendieck P) P.ι :=
  preservesCoveringPullbacks_ι_associatedTopology_of_members B S hS p (@Smooth) hp K P
    (smooth_of_mem_of_map_mem_etalePrecoverage B K hK) hclose

/-! ### Stacks 0D6X over an object of a full subsite -/

/-- **Stacks 0D6X for the inclusion of a full subsite, over an object of the subsite.** Let `P`
cut out a full subcategory of the objects of a category fibred in groupoids over the big fppf
category of `S`, and suppose the covering morphisms of the subsite admit the fibre products of
Stacks 00WV, preserved by the inclusion. Then for every object `x` of the subsite the restriction
along the inclusion of an injective abelian sheaf on the ambient site has vanishing cohomology
over `x` in positive degrees.

Cohomology over `x` is `Ext` out of the free abelian sheaf on the representable presheaf of `x`,
lifted to the coefficient universe, which is `CategoryTheory.extensionByZeroUnitAb`. The
coefficient universe is the join of the two universes of the site, which is where the sheaves on
these sites live and which is what
`Stacks.CechSite.injective_sheaf_subsingleton_ext_of_functor` allows, neither site being
small. -/
@[stacks 0D6X "for the inclusion of a full subsite of the site of Stacks 06TP, over an object of \
the subsite"]
theorem subsiteObjectCohomology_eq_zero (hp : p.IsFiberedInGroupoids)
    (τ : GrothendieckTopology B.Schemes) (P : ObjectProperty X)
    [P.ι.IsContinuous (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)]
    [Stacks.Sites.PreservesCoveringPullbacks (subsiteTopology B S hS p τ P) P.ι]
    (I : Sheaf (associatedTopology B S hS p τ) AddCommGrpCat.{max v w}) [Injective I]
    (x : P.FullSubcategory) (n : ℕ)
    (a : Ext (extensionByZeroUnitAb.{max v w} (subsiteTopology B S hS p τ P) x)
      ((subsiteRestriction B S hS p τ P).obj I) (n + 1)) :
    a = 0 := by
  have hcart : ∀ {a b : X} (f : a ⟶ b), p.IsStronglyCartesian (p.map f) f := fun f =>
    hp.isStronglyCartesian_homLift (p.map f) f
  have : p.IsFibered := hp.isFibered
  have : HasPullbacks X :=
    @hasPullbacks_of_hasLimit_cospan _ _ fun {_ _ _} {f g} =>
      p.hasPullback_of_forall_isStronglyCartesian hcart f g
  set J := subsiteTopology B S hS p τ P with hJ
  set u := P.ι with hu
  set Cov : ∀ U : P.FullSubcategory,
      Set { E : PreZeroHypercover.{max v w} U // E.sieve₀ ∈ J U } :=
    fun U => { E | (∀ (j : E.1.I₀) ⦃W : P.FullSubcategory⦄ (g : W ⟶ U),
        HasPullback (E.1.f j) g) ∧
      (∀ (j : E.1.I₀) ⦃W : P.FullSubcategory⦄ (g : W ⟶ U),
        PreservesLimit (cospan (E.1.f j) g) u) } with hCov
  have hProducts : ∀ {U : P.FullSubcategory}
      (E : { E : PreZeroHypercover.{max v w} U // E.sieve₀ ∈ J U }),
      E ∈ Cov U → ∀ (q : ℕ) (i : Fin (q + 1) → E.1.I₀),
        HasProduct (fun b ↦ Over.mk (E.1.f (i b))) :=
    fun E hE q i => Stacks.Sites.hasProduct_fibreProducts E.1 hE.1 q i
  have hImageProducts : ∀ {U : P.FullSubcategory}
      (E : { E : PreZeroHypercover.{max v w} U // E.sieve₀ ∈ J U }),
      E ∈ Cov U → ∀ (q : ℕ) (i : Fin (q + 1) → (E.1.map u).I₀),
        HasProduct (fun b ↦ Over.mk ((E.1.map u).f (i b))) :=
    fun E _ q i =>
      Stacks.Sites.hasProduct_fibreProducts (E.1.map u) (fun _ _ _ => inferInstance) q i
  have hsub := Stacks.CechSite.injective_sheaf_subsingleton_ext_of_functor.{max v w, v}
    J (associatedTopology B S hS p τ) u Set.univ Cov hProducts hImageProducts
    (fun E _ => ⟨Set.mem_univ _, fun _ => Set.mem_univ _, fun _ _ => Set.mem_univ _⟩)
    (fun U _ R hR => by
      obtain ⟨E, hJE, hle, hpb, hpr⟩ := Stacks.Sites.exists_preZeroHypercover_le J u R hR
      exact ⟨⟨E, hJE⟩, ⟨hpb, hpr⟩, hle⟩)
    (fun E hE q i => by
      let := hProducts E hE
      let := hImageProducts E hE
      let := Stacks.Sites.preservesLimit_fibreProducts_overPost u E.1 hE.1 hE.2 q i
      exact Stacks.CechSite.isIso_cechProductMapOfFunctor u E.1 q i)
    I x (Set.mem_univ _) (n + 1) n.succ_pos
  exact hsub.elim a 0

/-! ### The flat-fppf site -/

namespace FlatFppf

variable (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

/-- **The covering-pullback condition of Stacks 00WV for the inclusion of the flat-fppf site.**
No hypothesis: the closure condition of Stacks 07AK (1) holds for every algebraic stack, by
`AlgebraicGeometry.Stack.FlatFppf.closedUnderFlatMorphisms`. -/
theorem preservesCoveringPullbacks_inclusion :
    Stacks.Sites.PreservesCoveringPullbacks (inclusionTopology B S hS 𝒳)
      (objectProperty B S hS 𝒳).ι :=
  preservesCoveringPullbacks_ι_fppfTopology B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids _ (closedUnderFlatMorphisms B S hS 𝒳)

/-- **Stacks 0D6X for the inclusion of the flat-fppf site, over a flat object.** The restriction
to the flat-fppf site of an injective abelian sheaf on the fppf site of an algebraic stack has
vanishing cohomology over every flat object in positive degrees. -/
@[stacks 0D6X "for the inclusion of the flat-fppf site of Stacks 0787, over a flat object"]
theorem objectAcyclic :
    haveI := isContinuous_inclusion B S hS 𝒳 (closedUnderFlatMorphisms B S hS 𝒳)
    ∀ I : Sheaf (fppfTopology B S hS 𝒳) AddCommGrpCat.{u + 1}, Injective I →
      ∀ (x : ObjectProperty.FullSubcategory (objectProperty B S hS 𝒳)) (n : ℕ)
      (a : Ext (extensionByZeroUnitAb.{u + 1} (inclusionTopology B S hS 𝒳) x)
        ((subsiteRestriction B S hS 𝒳.val.val.p B.topology
          (objectProperty B S hS 𝒳)).obj I) (n + 1)), a = 0 := by
  have := isContinuous_inclusion B S hS 𝒳 (closedUnderFlatMorphisms B S hS 𝒳)
  have := preservesCoveringPullbacks_inclusion B S hS 𝒳
  intro I hI x n a
  have := hI
  exact subsiteObjectCohomology_eq_zero B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    B.topology (objectProperty B S hS 𝒳) I x n a

/-- **The acyclicity statement of Stacks 07AC for the flat-fppf inclusion, discharged.** The
lower-shriek functor on abelian sheaves carries every bounded above acyclic complex whose terms
are direct sums of the extensions by zero `j_{U!} ℤ_U` to an acyclic complex.

This was the one open input of Stacks 07AS (3) for the flat-fppf site;
`AlgebraicGeometry.Stack.FlatFppf.abelianLowerShriekAcyclic_of_ext_vanishing` reduces it to the
object-level vanishing of Stacks 0D6X, which is
`AlgebraicGeometry.Stack.FlatFppf.objectAcyclic`. -/
theorem abelianLowerShriekAcyclic : AbelianLowerShriekAcyclic B S hS 𝒳 := by
  refine abelianLowerShriekAcyclic_of_ext_vanishing B S hS 𝒳 ?_
  intro U I hI n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact ⟨fun a b ↦ by
    rw [objectAcyclic B S hS 𝒳 I hI U m a, objectAcyclic B S hS 𝒳 I hI U m b]⟩

/-! #### The global comparison

The global clause of Stacks 07AK for the flat-fppf site, obtained from
`AlgebraicGeometry.Stack.subsiteCohomologyIso`: the comparison in every degree follows from the
comparison of the constant sheaves — equivalently, by the adjunction `g_! ⊣ g⁻¹`, from the
comparison in degree zero — together with the global form of Stacks 0D6X. See the module
docstring for why neither datum is available here. -/

section Global

attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'

/-- **The first sentence of Stacks 0789 for the flat-fppf site**: restriction of abelian sheaves
along the inclusion of the flat objects has a left adjoint `g_!`.

It is constructed as a left Kan extension followed by sheafification; the Kan extensions exist
because the flat-fppf site is essentially small in the universe of the schemes, which is
`AlgebraicGeometry.Stack.FlatFppf.hasLeftKanExtension_inclusion_ab`. -/
instance isRightAdjoint_subsiteRestriction :
    (subsiteRestriction B S hS 𝒳.val.val.p B.topology
      (objectProperty B S hS 𝒳)).IsRightAdjoint :=
  haveI := hasLeftKanExtension_inclusion_ab.{u, w, u + 1} B S hS 𝒳
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (objectProperty B S hS 𝒳).ι
    AddCommGrpCat.{u + 1} (inclusionTopology B S hS 𝒳)
    (fppfTopology B S hS 𝒳)).isRightAdjoint

/-- **Stacks 07AK, the cohomology comparison for the flat-fppf site.** For an algebraic stack
`𝒳`, every degree `q` and every abelian sheaf `ℱ` on the fppf site of `𝒳`,

`H^q(𝒳_{flat,fppf}, g⁻¹ℱ) ≅ H^q(𝒳_{fppf}, ℱ)`,

naturally in `ℱ`, where `g⁻¹` is restriction to the flat-fppf site of Stacks 0787.

The closure condition of Stacks 07AK (1) is discharged — it holds for every algebraic stack, by
`AlgebraicGeometry.Stack.FlatFppf.closedUnderFlatMorphisms` — so the inclusion is continuous and
cocontinuous with no hypothesis. Two data remain, and both are carried here as hypotheses.
`hunit` is the comparison `g_!ℤ_{𝒳'} ≅ ℤ_𝒳` of the constant sheaves, which by the adjunction
`g_! ⊣ g⁻¹` is the degree-zero case of the conclusion; it is what the source derives from the
atlas of Stacks 07AK (2), through the spectral sequence of Stacks 079Z, the localization
comparison of Stacks 07A0 and the fibre-power construction of Stacks 06X3. `hacyclic` is the
global form of Stacks 0D6X on the subsite; its object-level form is
`AlgebraicGeometry.Stack.FlatFppf.objectAcyclic`, which is unconditional, but the passage from
objects to global cohomology needs a terminal object of the subsite, which does not exist. See
the module docstring.

The form of this comparison with both data proved, for every full subcategory satisfying the
two conditions of Stacks 07AK, is `AlgebraicGeometry.Stack.subsiteCohomologyIsoOfAtlas`, and the
whole of Stacks 07AK is `AlgebraicGeometry.Stack.subsite_cohomology_comparison`, both in
`StacksFrontier/AlgebraicGeometry/Stacks/SubsiteCohomologyAtlas.lean`. -/
def cohomologyIso
    (hunit : (Stacks.Cohomology.lowerShriekAbelian (inclusionTopology B S hS 𝒳)
          (fppfTopology B S hS 𝒳) (objectProperty B S hS 𝒳).ι).obj
        ((constantSheaf (inclusionTopology B S hS 𝒳) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≅
      (constantSheaf (fppfTopology B S hS 𝒳) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    (hacyclic : ∀ I : Sheaf (fppfTopology B S hS 𝒳) AddCommGrpCat.{u + 1}, Injective I →
      ∀ (n : ℕ) (a : Sheaf.H ((subsiteRestriction B S hS 𝒳.val.val.p B.topology
        (objectProperty B S hS 𝒳)).obj I) (n + 1)), a = 0)
    (q : ℕ) :
    subsiteRestriction B S hS 𝒳.val.val.p B.topology (objectProperty B S hS 𝒳) ⋙
        Sheaf.functorH.{u + 1, u + 1, u, u + 1} (inclusionTopology B S hS 𝒳) q ≅
      Sheaf.functorH.{u + 1, u + 1, u, u + 1} (fppfTopology B S hS 𝒳) q :=
  subsiteCohomologyIso B S hS 𝒳.val.val.p B.topology (objectProperty B S hS 𝒳) hunit hacyclic q

end Global

end FlatFppf

/-! ### The lisse-étale site -/

namespace LisseEtale

variable (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

/-- **The covering-pullback condition of Stacks 00WV for the inclusion of the lisse-étale
site.** No hypothesis: the closure condition of Stacks 07AK (1) for the smooth objects holds for
every algebraic stack, by
`AlgebraicGeometry.Stack.LisseEtale.closedUnderSmoothMorphisms`. -/
theorem preservesCoveringPullbacks_inclusion :
    Stacks.Sites.PreservesCoveringPullbacks (inclusionTopology.{u, w} B S hS 𝒳)
      (smoothObject.{u, w} B S hS 𝒳).ι :=
  preservesCoveringPullbacks_ι_etaleTopology B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids (etalePrecoverage B) (map_mem_etalePrecoverage B) _
    (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)

/-- **Stacks 0D6X for the inclusion of the lisse-étale site, over a smooth object.** The
restriction to the lisse-étale site of an injective abelian sheaf on the étale site of an
algebraic stack has vanishing cohomology over every smooth object in positive degrees. -/
@[stacks 0D6X "for the inclusion of the lisse-étale site of Stacks 0787, over a smooth object"]
theorem objectAcyclic :
    haveI := isContinuous_inclusion B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
    ∀ I : Sheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        AddCommGrpCat.{u + 1}, Injective I →
      ∀ (x : ObjectProperty.FullSubcategory (smoothObject.{u, w} B S hS 𝒳)) (n : ℕ)
      (a : Ext (extensionByZeroUnitAb.{u + 1} (inclusionTopology.{u, w} B S hS 𝒳) x)
        ((subsiteRestriction B S hS 𝒳.val.val.p (etaleTopology B)
          (smoothObject.{u, w} B S hS 𝒳)).obj I) (n + 1)), a = 0 := by
  have := isContinuous_inclusion B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)
  have := preservesCoveringPullbacks_inclusion.{u, w} B S hS 𝒳
  intro I hI x n a
  have := hI
  exact subsiteObjectCohomology_eq_zero B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    (etaleTopology B) (smoothObject.{u, w} B S hS 𝒳) I x n a

/-! #### The global comparison

The global clause of Stacks 07AK for the lisse-étale site, obtained from
`AlgebraicGeometry.Stack.subsiteCohomologyIso` exactly as in the flat-fppf case. -/

section Global

/-- Continuity of the inclusion of the lisse-étale site, with the closure condition of Stacks
07AK (1) discharged, as a local instance. -/
local instance isContinuousInclusion :
    (smoothObject.{u, w} B S hS 𝒳).ι.IsContinuous (inclusionTopology.{u, w} B S hS 𝒳)
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) :=
  isContinuous_inclusion B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)

/-- Cocontinuity of the inclusion of the lisse-étale site, with the closure condition of Stacks
07AK (1) discharged, as a local instance. -/
local instance isCocontinuousInclusion :
    (smoothObject.{u, w} B S hS 𝒳).ι.IsCocontinuous (inclusionTopology.{u, w} B S hS 𝒳)
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) :=
  isCocontinuous_inclusion B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)

/-- The lisse-étale site of an algebraic stack is essentially small in the coefficient universe:
it is a full subcategory of the étale site of `𝒳`, which is essentially small in the universe of
the schemes and hence in any larger one. -/
theorem essentiallySmall_lisseEtale :
    EssentiallySmall.{u + 1} (ObjectProperty.FullSubcategory (smoothObject.{u, w} B S hS 𝒳)) :=
  haveI := FlatFppf.essentiallySmall_obj_coefficient.{u, w, u + 1} B S hS 𝒳
  essentiallySmall_of_fully_faithful.{u + 1} (smoothObject.{u, w} B S hS 𝒳).ι

/-- Restriction of abelian presheaves along the inclusion of the smooth objects admits a left Kan
extension: the comma categories indexing it are essentially small, so the required colimits exist
in abelian groups. -/
theorem hasLeftKanExtension_inclusion_ab :
    ∀ F : (ObjectProperty.FullSubcategory (smoothObject.{u, w} B S hS 𝒳))ᵒᵖ ⥤
      AddCommGrpCat.{u + 1}, (smoothObject.{u, w} B S hS 𝒳).ι.op.HasLeftKanExtension F :=
  fun F => by
  have := essentiallySmall_lisseEtale.{u, w} B S hS 𝒳
  have : (smoothObject.{u, w} B S hS 𝒳).ι.op.HasPointwiseLeftKanExtension F := fun Y => by
    have := hasColimitsOfShape_of_essentiallySmall.{u + 1}
      (CostructuredArrow (smoothObject.{u, w} B S hS 𝒳).ι.op Y) AddCommGrpCat.{u + 1}
    infer_instance
  infer_instance

/-- **The first sentence of Stacks 0789 for the lisse-étale site**: restriction of abelian
sheaves along the inclusion of the smooth objects has a left adjoint `g_!`. -/
instance isRightAdjoint_subsiteRestriction :
    (subsiteRestriction B S hS 𝒳.val.val.p (etaleTopology B)
      (smoothObject.{u, w} B S hS 𝒳)).IsRightAdjoint :=
  haveI := hasLeftKanExtension_inclusion_ab.{u, w} B S hS 𝒳
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (smoothObject.{u, w} B S hS 𝒳).ι AddCommGrpCat.{u + 1} (inclusionTopology.{u, w} B S hS 𝒳)
    (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))).isRightAdjoint

/-- **Stacks 07AK, the cohomology comparison for the lisse-étale site.** For an algebraic stack
`𝒳`, every degree `q` and every abelian sheaf `ℱ` on the étale site of `𝒳`,

`H^q(𝒳_{lisse,étale}, g⁻¹ℱ) ≅ H^q(𝒳_{étale}, ℱ)`,

naturally in `ℱ`, where `g⁻¹` is restriction to the lisse-étale site of Stacks 0787.

The closure condition of Stacks 07AK (1) is discharged — it holds for every algebraic stack, by
`AlgebraicGeometry.Stack.LisseEtale.closedUnderSmoothMorphisms` — and so is the existence of
`g_!`. The two remaining data are as in
`AlgebraicGeometry.Stack.FlatFppf.cohomologyIso`: the comparison `g_!ℤ_{𝒳'} ≅ ℤ_𝒳` of the
constant sheaves, which is the degree-zero case of the conclusion and is what the source derives
from the atlas of Stacks 07AK (2), and the global form of the acyclicity statement of Stacks
0D6X, whose object-level form is `AlgebraicGeometry.Stack.LisseEtale.objectAcyclic`. See the
module docstring.

The form of this comparison with both data proved, for every full subcategory satisfying the
two conditions of Stacks 07AK, is `AlgebraicGeometry.Stack.subsiteCohomologyIsoOfAtlas`, and the
whole of Stacks 07AK is `AlgebraicGeometry.Stack.subsite_cohomology_comparison`, both in
`StacksFrontier/AlgebraicGeometry/Stacks/SubsiteCohomologyAtlas.lean`. -/
def cohomologyIso
    (hunit : (Stacks.Cohomology.lowerShriekAbelian
          (inclusionTopology.{u, w} B S hS 𝒳)
          (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
          (smoothObject.{u, w} B S hS 𝒳).ι).obj
        ((constantSheaf (inclusionTopology.{u, w} B S hS 𝒳) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≅
      (constantSheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
          AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    (hacyclic : ∀ I : Sheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
        AddCommGrpCat.{u + 1}, Injective I →
      ∀ (n : ℕ) (a : Sheaf.H ((subsiteRestriction B S hS 𝒳.val.val.p (etaleTopology B)
        (smoothObject.{u, w} B S hS 𝒳)).obj I) (n + 1)), a = 0)
    (q : ℕ) :
    subsiteRestriction B S hS 𝒳.val.val.p (etaleTopology B) (smoothObject.{u, w} B S hS 𝒳) ⋙
        Sheaf.functorH.{u + 1, u + 1, u, u + 1} (inclusionTopology.{u, w} B S hS 𝒳) q ≅
      Sheaf.functorH.{u + 1, u + 1, u, u + 1}
        (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) q :=
  subsiteCohomologyIso B S hS 𝒳.val.val.p (etaleTopology B) (smoothObject.{u, w} B S hS 𝒳)
    hunit hacyclic q

end Global

end LisseEtale

end AlgebraicGeometry.Stack

end
