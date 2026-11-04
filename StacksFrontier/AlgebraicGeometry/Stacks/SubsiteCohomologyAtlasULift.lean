module

public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteCohomologyAtlas
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CoverDescent.ULift

/-!
# Stacks 07AK at coefficients in a larger universe

`AlgebraicGeometry.Stack.subsiteCohomologyIsoOfAtlas` is Stacks 07AK for abelian sheaves with
values in the universe `u + 1` of the site of an algebraic stack. A sheaf of modules over a sheaf
of rings in a larger universe `max (u + 1) t` has its underlying abelian sheaf in that universe,
so the module form of the comparison needs Stacks 07AK at those coefficients. This file proves
it, by the same descent along the atlas.

The descent of `StacksFrontier/CategoryTheory/Sites/Cohomology/CoverDescent/Cohomology.lean` has its
coefficient universe free; what is pinned to `u + 1` is the class
`AlgebraicGeometry.Stack.SmoothOverAtlas` of presheaves of sets it is run along. That class is
moved to the larger universe by `Stacks.Sites.CoverDescent.liftClass`, and
`Stacks.Sites.CoverDescent.IsClosedUnderRepresentableCovers.liftClass` shows that this preserves
closure under representable covers. The other input, Stacks 0D6X over an object of the subsite, is
`AlgebraicGeometry.Stack.subsiteObjectCohomology_eq_zero` with its coefficient universe freed,
which `Stacks.CechSite.injective_sheaf_subsingleton_ext_of_functor` allows.

## Main results

* `AlgebraicGeometry.Stack.subsiteObjectCohomology_eq_zero_of_le`: **Stacks 0D6X** over an object
  of a full subsite, at coefficients in any universe containing the site.
* `AlgebraicGeometry.Stack.subsiteCohomologyIsoOfAtlasOfLe`: **Stacks 07AK**, the cohomology
  comparison, at coefficients in any universe containing the site.

## References

* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK)
* [Stacks Project, Tag 0D6X](https://stacks.math.columbia.edu/tag/0D6X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Abelian
open Stacks.Sites.CoverDescent Stacks.Cohomology.DerivedLowerShriek

namespace AlgebraicGeometry.Stack

universe u v w t

section ObjectAcyclic

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS)

/-- **Stacks 0D6X for the inclusion of a full subsite, over an object of the subsite, at
coefficients in any universe containing the site.** This is
`AlgebraicGeometry.Stack.subsiteObjectCohomology_eq_zero` with the coefficients in `max v w t`
rather than `max v w`; the proof is the same, the library's form of Stacks 0D6X having its
coefficient universe free. -/
theorem subsiteObjectCohomology_eq_zero_of_le (hp : p.IsFiberedInGroupoids)
    (τ : GrothendieckTopology B.Schemes) (P : ObjectProperty X)
    [P.ι.IsContinuous (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)]
    [Stacks.Sites.PreservesCoveringPullbacks (subsiteTopology B S hS p τ P) P.ι]
    [HasSheafify (subsiteTopology B S hS p τ P) AddCommGrpCat.{max v w t}]
    [HasExt.{max v w t} (Sheaf (subsiteTopology B S hS p τ P) AddCommGrpCat.{max v w t})]
    (I : Sheaf (associatedTopology B S hS p τ) AddCommGrpCat.{max v w t}) [Injective I]
    (x : P.FullSubcategory) (n : ℕ)
    (a : Ext (extensionByZeroUnitAb.{max v w t} (subsiteTopology B S hS p τ P) x)
      ((P.ι.sheafPushforwardContinuous AddCommGrpCat.{max v w t}
        (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)).obj I) (n + 1)) :
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
  have hsub := Stacks.CechSite.injective_sheaf_subsingleton_ext_of_functor.{max v w t, max v t}
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

end ObjectAcyclic

section Atlas

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (𝒳 : AlgebraicStacks.{u, w} B S hS) (τ : SiteKind) (P : ObjectProperty 𝒳.val.val.obj)

/-- Restriction of abelian presheaves along the inclusion of a full subsite of an algebraic stack
admits a left Kan extension, at coefficients in any universe containing the site. This is
`AlgebraicGeometry.Stack.hasLeftKanExtension_subsite_ab` at a larger universe. -/
theorem hasLeftKanExtension_subsite_ab_of_le :
    ∀ F : P.FullSubcategoryᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) t},
      P.ι.op.HasLeftKanExtension F := fun F => by
  have := FlatFppf.essentiallySmall_obj_coefficient.{u, w, max (u + 1) t} B S hS 𝒳
  have : EssentiallySmall.{max (u + 1) t} P.FullSubcategory :=
    essentiallySmall_of_fully_faithful.{max (u + 1) t} P.ι
  have : P.ι.op.HasPointwiseLeftKanExtension F := fun Y => by
    have := hasColimitsOfShape_of_essentiallySmall.{max (u + 1) t}
      (CostructuredArrow P.ι.op Y) AddCommGrpCat.{max (u + 1) t}
    infer_instance
  infer_instance

/-- The final presheaf of `𝒳`, lifted to a larger universe, has one-point values. -/
abbrev uniqueULiftComponentPresheafId (y : 𝒳.val.val.objᵒᵖ) :
    Unique ((componentPresheaf (𝟭 𝒳.val.val.obj) ⋙ uliftFunctor.{t}).obj y) :=
  letI := componentPresheafIdUnique y
  { default := ULift.up default
    uniq := fun a => congrArg ULift.up (Unique.uniq _ a.down) }

variable {𝒳 τ P}

variable (hcl : IsClosedUnderSitePullback B S hS 𝒳.val.val.p P τ)
  (hatlas : ∃ x : 𝒳.val.val.obj, P x ∧
    AlgebraicStacks.IsSmooth B S hS (Bicategory.InducedBicategory.mkHom
        (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := x) rfl)) :
          schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x) ⟶ 𝒳) ∧
    IsSurjective B S hS (Bicategory.InducedBicategory.mkHom
        (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := x) rfl)) :
          schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x) ⟶ 𝒳))

include hatlas in
/-- **Stacks 07AK, the cohomology comparison, at coefficients in any universe containing the
site.** Let `𝒳'` be a full subcategory of an algebraic stack `𝒳` satisfying the two hypotheses of
Stacks 07AK for `τ` the étale or the fppf topology. For every degree `p`,

`H^p(𝒳'_τ, g⁻¹ℱ) ≅ H^p(𝒳_τ, ℱ)`,

naturally in the abelian sheaf `ℱ` on `𝒳_τ` with values in `AddCommGrpCat.{max (u + 1) t}`.

This is `AlgebraicGeometry.Stack.subsiteCohomologyIsoOfAtlas` at coefficients `max (u + 1) t`
rather than `u + 1`, by the same descent along the atlas, run along the class
`AlgebraicGeometry.Stack.SmoothOverAtlas` lifted to the larger universe. -/
def subsiteCohomologyIsoOfAtlasOfLe (q : ℕ) :
    haveI := isContinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
      𝒳.val.val.p P τ 𝒳.val.isFiberedInGroupoids hcl
    haveI : HasSheafify (subsiteTopology B S hS 𝒳.val.val.p (B.baseTopology τ) P)
        AddCommGrpCat.{max (u + 1) t} :=
      Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u + 1, u, t}
    haveI : HasSheafify (associatedTopology B S hS 𝒳.val.val.p (B.baseTopology τ))
        AddCommGrpCat.{max (u + 1) t} :=
      Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u + 1, u, t}
    haveI : HasExt.{max (u + 1) t} (Sheaf (subsiteTopology B S hS 𝒳.val.val.p
        (B.baseTopology τ) P) AddCommGrpCat.{max (u + 1) t}) :=
      Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{u + 1, u, t}
    haveI : HasExt.{max (u + 1) t} (Sheaf (associatedTopology B S hS 𝒳.val.val.p
        (B.baseTopology τ)) AddCommGrpCat.{max (u + 1) t}) :=
      Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{u + 1, u, t}
    P.ι.sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) t}
          (subsiteTopology B S hS 𝒳.val.val.p (B.baseTopology τ) P)
          (associatedTopology B S hS 𝒳.val.val.p (B.baseTopology τ)) ⋙
        Sheaf.functorH.{max (u + 1) t}
          (subsiteTopology B S hS 𝒳.val.val.p (B.baseTopology τ) P) q ≅
      Sheaf.functorH.{max (u + 1) t}
        (associatedTopology B S hS 𝒳.val.val.p (B.baseTopology τ)) q :=
  haveI := isContinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
    𝒳.val.val.p P τ 𝒳.val.isFiberedInGroupoids hcl
  haveI := isCocontinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
    𝒳.val.val.p P τ 𝒳.val.isFiberedInGroupoids hcl
  haveI : HasSheafify (subsiteTopology B S hS 𝒳.val.val.p (B.baseTopology τ) P)
      AddCommGrpCat.{max (u + 1) t} :=
    Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u + 1, u, t}
  haveI : HasSheafify (associatedTopology B S hS 𝒳.val.val.p (B.baseTopology τ))
      AddCommGrpCat.{max (u + 1) t} :=
    Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u + 1, u, t}
  haveI : HasExt.{max (u + 1) t} (Sheaf (subsiteTopology B S hS 𝒳.val.val.p
      (B.baseTopology τ) P) AddCommGrpCat.{max (u + 1) t}) :=
    Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{u + 1, u, t}
  haveI : HasExt.{max (u + 1) t} (Sheaf (associatedTopology B S hS 𝒳.val.val.p
      (B.baseTopology τ)) AddCommGrpCat.{max (u + 1) t}) :=
    Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{u + 1, u, t}
  haveI : EnoughInjectives (Sheaf (subsiteTopology B S hS 𝒳.val.val.p
      (B.baseTopology τ) P) AddCommGrpCat.{max (u + 1) t}) :=
    Stacks.Cohomology.SiteModules.site_enoughInjectives_addCommGrp.{u + 1, u, t}
  haveI : EnoughInjectives (Sheaf (associatedTopology B S hS 𝒳.val.val.p
      (B.baseTopology τ)) AddCommGrpCat.{max (u + 1) t}) :=
    Stacks.Cohomology.SiteModules.site_enoughInjectives_addCommGrp.{u + 1, u, t}
  haveI := hasLeftKanExtension_subsite_ab_of_le.{u, w, t} 𝒳 P
  haveI := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous P.ι
    AddCommGrpCat.{max (u + 1) t} (subsiteTopology B S hS 𝒳.val.val.p (B.baseTopology τ) P)
    (associatedTopology B S hS 𝒳.val.val.p (B.baseTopology τ))).isRightAdjoint
  haveI : PreservesFiniteColimits (P.ι.sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) t}
      (subsiteTopology B S hS 𝒳.val.val.p (B.baseTopology τ) P)
      (associatedTopology B S hS 𝒳.val.val.p (B.baseTopology τ))) :=
    haveI := (Functor.sheafAdjunctionCocontinuous P.ι AddCommGrpCat.{max (u + 1) t}
      (subsiteTopology B S hS 𝒳.val.val.p (B.baseTopology τ) P)
      (associatedTopology B S hS 𝒳.val.val.p
        (B.baseTopology τ))).leftAdjoint_preservesColimits.{0, 0}
    PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _
  haveI := preservesCoveringPullbacks_of_isClosedUnderSitePullback hcl
  let x := hatlas.choose
  let a : schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x) ⟶ 𝒳 :=
    Bicategory.InducedBicategory.mkHom
      (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := x) rfl))
  have h𝔎 : IsClosedUnderRepresentableCovers.{max (u + 1) t}
      (associatedTopology B S hS 𝒳.val.val.p (B.baseTopology τ))
      (subsiteTopology B S hS 𝒳.val.val.p (B.baseTopology τ) P) P.ι
      (liftClass.{t} (SmoothOverAtlas 𝒳 a)) :=
    (isClosedUnderRepresentableCovers_smoothOverAtlas a τ P hcl
      hatlas.choose_spec.2.1 hatlas.choose_spec.2.2
      (prop_objectMorphism_obj hcl hatlas.choose_spec.1)).liftClass
  let F₀ := componentPresheaf (𝟭 𝒳.val.val.obj) ⋙ uliftFunctor.{t}
  have hF₀ : liftClass.{t} (SmoothOverAtlas 𝒳 a) F₀ :=
    ⟨_, Or.inl rfl, ⟨Iso.refl _⟩⟩
  have _ := isIso_freeComparison.{max (u + 1) t, u, u + 1, u + 1}
    (associatedTopology B S hS 𝒳.val.val.p (B.baseTopology τ))
    (subsiteTopology B S hS 𝒳.val.val.p (B.baseTopology τ) P) P.ι F₀
    (fun F hF => restrictHom_bijective_of_mem.{max (u + 1) t, u, u + 1, u + 1} _ h𝔎 hF₀ F hF)
  let e₁ := freeAbelianSheafIsoConstantSheafOfUnique
    (subsiteTopology B S hS 𝒳.val.val.p (B.baseTopology τ) P) (P.ι.op ⋙ F₀)
    (fun y => uniqueULiftComponentPresheafId.{u, w, t} 𝒳 (P.ι.op.obj y))
  let e₂ := freeAbelianSheafIsoConstantSheafOfUnique
    (associatedTopology B S hS 𝒳.val.val.p (B.baseTopology τ)) F₀
    (uniqueULiftComponentPresheafId.{u, w, t} 𝒳)
  Stacks.Cohomology.BiggerSiteGlobal.sheafCohomologyIsoOfConstantSheafIsoOfAcyclic
    (subsiteTopology B S hS 𝒳.val.val.p (B.baseTopology τ) P)
    (associatedTopology B S hS 𝒳.val.val.p (B.baseTopology τ)) P.ι
    ((P.ι.sheafPullback AddCommGrpCat.{max (u + 1) t} _ _).mapIso e₁.symm ≪≫
      asIso (freeComparison.{max (u + 1) t, u, u + 1, u + 1}
        (associatedTopology B S hS 𝒳.val.val.p (B.baseTopology τ))
        (subsiteTopology B S hS 𝒳.val.val.p (B.baseTopology τ) P) P.ι F₀) ≪≫ e₂)
    (fun I _ n b => Stacks.Cohomology.ColimitsOfCohomology.ext_eq_zero_of_iso_first e₁.symm
      (n + 1) (fun c => ext_restriction_eq_zero_of_mem h𝔎
        (fun I _ d m c => subsiteObjectCohomology_eq_zero_of_le.{u, u + 1, u, t} B S hS
          𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (B.baseTopology τ) P I d m c) hF₀ I n c) b) q

end Atlas

end AlgebraicGeometry.Stack

end
