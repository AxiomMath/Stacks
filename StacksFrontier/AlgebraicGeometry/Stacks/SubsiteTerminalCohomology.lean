module

public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteCohomologyComparison

/-!
# The global comparison of Stacks 07AK on a full subsite with a terminal object

Let `P` cut out a full subsite of the site of Stacks 06TP which has a terminal object. The
restriction to the subsite of an injective abelian sheaf on the ambient site has vanishing global
cohomology in positive degrees (Stacks 0D6X), and if the image of the terminal object is terminal,
restriction to the subsite identifies the cohomology of the two sites (Stacks 07AK).

## Main definitions

* `AlgebraicGeometry.Stack.subsiteLowerShriekConstantSheafIso`: the comparison `g_!ℤ ≅ ℤ` of the
  constant sheaves.
* `AlgebraicGeometry.Stack.subsiteCohomologyIsoOfIsTerminal`: the comparison
  `H^q(P, g^{-1}F) ≅ H^q(𝒳, F)`.
* `AlgebraicGeometry.Stack.FlatFppf.cohomologyIsoOfIsTerminal`,
  `AlgebraicGeometry.Stack.LisseEtale.cohomologyIsoOfIsTerminal`: the comparison for the
  flat-fppf and the lisse-étale site of an algebraic stack.

## Main results

* `AlgebraicGeometry.Stack.subsiteGlobalCohomology_eq_zero`: the restriction of an injective
  abelian sheaf to a full subsite with a terminal object has vanishing global cohomology in
  positive degrees.

## References

* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK)
* [Stacks Project, Tag 0D6X](https://stacks.math.columbia.edu/tag/0D6X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Abelian

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS)

/-- **Vanishing of the global cohomology of a restricted injective sheaf.** Let `P` cut out a
full subcategory of the objects of a category fibred in groupoids over the big fppf category of
`S`, suppose the covering morphisms of the subsite admit the fibre products of Stacks 00WV,
preserved by the inclusion, and suppose the subsite has a terminal object. Then the restriction
along the inclusion of an injective abelian sheaf on the ambient site has vanishing global
cohomology `CategoryTheory.Sheaf.H` in positive degrees. -/
@[stacks 0D6X "for the inclusion of a full subsite of the site of Stacks 06TP, for the global \
cohomology of a subsite with a terminal object"]
theorem subsiteGlobalCohomology_eq_zero (hp : p.IsFiberedInGroupoids)
    (τ : GrothendieckTopology B.Schemes) (P : ObjectProperty X)
    [P.ι.IsContinuous (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)]
    [Stacks.Sites.PreservesCoveringPullbacks (subsiteTopology B S hS p τ P) P.ι]
    {e : P.FullSubcategory} (he : IsTerminal e)
    (I : Sheaf (associatedTopology B S hS p τ) AddCommGrpCat.{max v w}) [Injective I]
    (n : ℕ) (a : Sheaf.H ((subsiteRestriction B S hS p τ P).obj I) (n + 1)) :
    a = 0 := by
  have hcart : ∀ {a b : X} (f : a ⟶ b), p.IsStronglyCartesian (p.map f) f := fun f =>
    hp.isStronglyCartesian_homLift (p.map f) f
  have : p.IsFibered := hp.isFibered
  have : HasPullbacks X :=
    @hasPullbacks_of_hasLimit_cospan _ _ fun {_ _ _} {f g} =>
      p.hasPullback_of_forall_isStronglyCartesian hcart f g
  set J := subsiteTopology B S hS p τ P
  set u := P.ι
  set Cov : ∀ U : P.FullSubcategory,
      Set { E : PreZeroHypercover.{max v w} U // E.sieve₀ ∈ J U } :=
    fun U => { E | (∀ (j : E.1.I₀) ⦃W : P.FullSubcategory⦄ (g : W ⟶ U),
        HasPullback (E.1.f j) g) ∧
      (∀ (j : E.1.I₀) ⦃W : P.FullSubcategory⦄ (g : W ⟶ U),
        PreservesLimit (cospan (E.1.f j) g) u) }
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
  have hsub := Stacks.CechSite.injective_sheaf_subsingleton_sheafH_of_functor.{max v w, v}
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
    I he (Set.mem_univ _) (n + 1) n.succ_pos
  exact hsub.elim a 0

/-! ### The degree-zero comparison, and the global comparison of Stacks 07AK -/

variable (τ : GrothendieckTopology B.Schemes) (P : ObjectProperty X)
  [P.ι.IsContinuous (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)]

/-- **The comparison `g_!ℤ_{𝒳'} ≅ ℤ_𝒳` of the constant sheaves**, for a full subsite with a
terminal object whose image is terminal: the lower shriek along the inclusion of the constant
sheaf `ℤ` on the subsite is the constant sheaf `ℤ` on the ambient site. -/
def subsiteLowerShriekConstantSheafIso
    [(subsiteRestriction B S hS p τ P).IsRightAdjoint]
    {e : P.FullSubcategory} (he : IsTerminal e) (heX : IsTerminal (P.ι.obj e)) :
    (Stacks.Cohomology.lowerShriekAbelian (subsiteTopology B S hS p τ P)
          (associatedTopology B S hS p τ) P.ι).obj
        ((constantSheaf (subsiteTopology B S hS p τ P) AddCommGrpCat.{max v w}).obj
          (AddCommGrpCat.of (ULift.{max v w} ℤ))) ≅
      (constantSheaf (associatedTopology B S hS p τ) AddCommGrpCat.{max v w}).obj
        (AddCommGrpCat.of (ULift.{max v w} ℤ)) :=
  haveI := he.hasTerminal
  haveI := heX.hasTerminal
  (Stacks.Cohomology.BiggerSiteGlobal.lowerShriekConstantSheafIso
      (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ) P.ι he heX rfl).app
    (AddCommGrpCat.of (ULift.{max v w} ℤ))

/-- **Stacks 07AK, the global comparison, for a full subsite with a terminal object whose image
is terminal.** For every degree `q`

`H^q(P, g^{-1}F) ≅ H^q(𝒳, F)`

naturally in the abelian sheaf `F` on the ambient site, where `g` is the inclusion of the
subsite and the covering morphisms of the subsite admit the fibre products of Stacks 00WV. -/
def subsiteCohomologyIsoOfIsTerminal (hp : p.IsFiberedInGroupoids)
    [P.ι.IsCocontinuous (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)]
    [Stacks.Sites.PreservesCoveringPullbacks (subsiteTopology B S hS p τ P) P.ι]
    [(subsiteRestriction B S hS p τ P).IsRightAdjoint]
    {e : P.FullSubcategory} (he : IsTerminal e) (heX : IsTerminal (P.ι.obj e)) (q : ℕ) :
    subsiteRestriction B S hS p τ P ⋙
        Sheaf.functorH.{max v w, max v w, w, v} (subsiteTopology B S hS p τ P) q ≅
      Sheaf.functorH.{max v w, max v w, w, v} (associatedTopology B S hS p τ) q :=
  subsiteCohomologyIso B S hS p τ P
    (subsiteLowerShriekConstantSheafIso B S hS p τ P he heX)
    (fun I hI n a => by
      have := hI
      exact subsiteGlobalCohomology_eq_zero B S hS p hp τ P he I n a) q

/-! ### The two subsites of Stacks 0787 -/

namespace FlatFppf

variable (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

section

attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'

/-- **Stacks 07AK for the flat-fppf site.** If the flat-fppf site of an algebraic stack has a
terminal object whose image is terminal in the fppf site, then for every degree `q` restriction to
the flat-fppf site identifies the `q`-th cohomology of abelian sheaves on the fppf site with that
of their restrictions. -/
def cohomologyIsoOfIsTerminal
    {e : ObjectProperty.FullSubcategory (objectProperty B S hS 𝒳)} (he : IsTerminal e)
    (heX : IsTerminal ((objectProperty B S hS 𝒳).ι.obj e)) (q : ℕ) :
    subsiteRestriction B S hS 𝒳.val.val.p B.topology (objectProperty B S hS 𝒳) ⋙
        Sheaf.functorH.{u + 1, u + 1, u, u + 1} (inclusionTopology B S hS 𝒳) q ≅
      Sheaf.functorH.{u + 1, u + 1, u, u + 1} (fppfTopology B S hS 𝒳) q :=
  haveI := preservesCoveringPullbacks_inclusion B S hS 𝒳
  subsiteCohomologyIsoOfIsTerminal B S hS 𝒳.val.val.p B.topology (objectProperty B S hS 𝒳)
    𝒳.val.isFiberedInGroupoids he heX q

end

end FlatFppf

namespace LisseEtale

variable (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

section

/-- The inclusion of the lisse-étale site of `𝒳` into its étale site is continuous. -/
local instance isContinuousInclusionSubsiteTopology :
    (smoothObject.{u, w} B S hS 𝒳).ι.IsContinuous
      (subsiteTopology B S hS 𝒳.val.val.p (etaleTopology B) (smoothObject.{u, w} B S hS 𝒳))
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) :=
  isContinuous_inclusion B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)

/-- The inclusion of the lisse-étale site of `𝒳` into its étale site is cocontinuous. -/
local instance isCocontinuousInclusionSubsiteTopology :
    (smoothObject.{u, w} B S hS 𝒳).ι.IsCocontinuous
      (subsiteTopology B S hS 𝒳.val.val.p (etaleTopology B) (smoothObject.{u, w} B S hS 𝒳))
      (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) :=
  isCocontinuous_inclusion B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)

/-- **Stacks 07AK for the lisse-étale site.** If the lisse-étale site of an algebraic stack has a
terminal object whose image is terminal in the étale site, then for every degree `q` restriction
to the lisse-étale site identifies the `q`-th cohomology of abelian sheaves on the étale site with
that of their restrictions. -/
def cohomologyIsoOfIsTerminal
    {e : ObjectProperty.FullSubcategory (smoothObject.{u, w} B S hS 𝒳)} (he : IsTerminal e)
    (heX : IsTerminal ((smoothObject.{u, w} B S hS 𝒳).ι.obj e)) (q : ℕ) :
    subsiteRestriction B S hS 𝒳.val.val.p (etaleTopology B) (smoothObject.{u, w} B S hS 𝒳) ⋙
        Sheaf.functorH.{u + 1, u + 1, u, u + 1} (inclusionTopology.{u, w} B S hS 𝒳) q ≅
      Sheaf.functorH.{u + 1, u + 1, u, u + 1}
        (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) q :=
  haveI : Stacks.Sites.PreservesCoveringPullbacks
      (subsiteTopology B S hS 𝒳.val.val.p (etaleTopology B) (smoothObject.{u, w} B S hS 𝒳))
      (smoothObject.{u, w} B S hS 𝒳).ι :=
    preservesCoveringPullbacks_inclusion.{u, w} B S hS 𝒳
  subsiteCohomologyIsoOfIsTerminal B S hS 𝒳.val.val.p (etaleTopology B)
    (smoothObject.{u, w} B S hS 𝒳) 𝒳.val.isFiberedInGroupoids he heX q

end

end LisseEtale

end AlgebraicGeometry.Stack

end
