module

public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteAcyclicity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.ModuleCohomologyAbelianComparisonGlobal

/-!
# Cohomology of sheaves of modules over an object of the lisse-étale and the flat-fppf site

The module clauses of parts (1)(b) and (2)(b) of Stacks 0GR0 — "the same holds for sheaves of
modules" — over an object: for an algebraic stack `𝒳`, a smooth (respectively flat) object `x`
and a sheaf `ℱ` of `𝒪`-modules on `𝒳_étale/x` (respectively `𝒳_fppf/x`),

`H^p(x, ℱ) = H^p(𝒳_{lisse,étale}/x, g^*ℱ)` and `H^p(x, ℱ) = H^p(𝒳_{flat,fppf}/x, g^*ℱ)`,

where `H^p` of a sheaf of modules is `Ext^p` out of the structure sheaf.

`AlgebraicGeometry.Stack.FlatFppf.moduleCohomologyOverObjectIso` and
`AlgebraicGeometry.Stack.LisseEtale.moduleCohomologyOverObjectIso` state this conditionally on
the module form of the acyclicity statement of Stacks 0D6X. This file proves it with no
hypothesis.

## The proof

The cohomology of a sheaf of modules is the cohomology of its underlying abelian sheaf (Stacks
03FD, `Stacks.Cohomology.ModuleAbelianComparison.moduleFunctorHIso`), and restriction of sheaves
of modules forgets to restriction of abelian sheaves on the nose. So the module comparison is the
abelian comparison over `x`, which is Stacks 03YU from acyclicity,
`Stacks.Cohomology.BiggerSiteGlobal.sheafCohomologyIsoOfAcyclic`, for the slice functor
`Over.post P.ι` — whose two slices have the terminal objects `𝟙 x` — with the acyclicity supplied
by Stacks 0D6X on the slice.

The only point is the coefficient universe. A sheaf of modules over a ring in the universe
`max v w t` has its underlying abelian sheaf in that universe, so the abelian comparison and the
acyclicity statement of Stacks 0D6X are needed at coefficients `max v w t`, whereas
`AlgebraicGeometry.Stack.subsiteSliceCohomology_eq_zero` is stated at `max v w`. The library's form
of 0D6X, `Stacks.CechSite.injective_sheaf_subsingleton_sheafH_of_functor`, has its coefficient
universe free, so `AlgebraicGeometry.Stack.subsiteSliceCohomology_eq_zero_of_le` is the same
proof at the larger universe.

## Main results

* `AlgebraicGeometry.Stack.subsiteSliceCohomology_eq_zero_of_le`: **Stacks 0D6X** for the
  inclusion of a full subsite, localized at an object, at coefficients in any universe containing
  the site.
* `AlgebraicGeometry.Stack.subsiteSliceModuleCohomologyIso`: the module comparison over an object,
  for an arbitrary sheaf of rings.
* `AlgebraicGeometry.Stack.LisseEtale.sliceModuleCohomologyIso` and
  `AlgebraicGeometry.Stack.FlatFppf.sliceModuleCohomologyIso`: **Stacks 0GR0** (1)(b) and (2)(b)
  for sheaves of modules, with no hypothesis.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
* [Stacks Project, Tag 0D6X](https://stacks.math.columbia.edu/tag/0D6X)
* [Stacks Project, Tag 0GR0](https://stacks.math.columbia.edu/tag/0GR0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Abelian
open Stacks.Cohomology.BiggerSiteModules Stacks.Cohomology.DerivedLowerShriek

namespace AlgebraicGeometry.Stack

universe u v w t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS)
  (τ : GrothendieckTopology B.Schemes) (P : ObjectProperty X)

/-! ### Stacks 0D6X on a slice, at a larger universe -/

/-- **Stacks 0D6X for a slice of the inclusion of a full subsite, at coefficients in any universe
containing the site.** This is `AlgebraicGeometry.Stack.subsiteSliceCohomology_eq_zero` with the
coefficients in `max v w t` rather than `max v w`; the proof is the same, the library's form of
Stacks 0D6X having its coefficient universe free. -/
theorem subsiteSliceCohomology_eq_zero_of_le (hp : p.IsFiberedInGroupoids)
    [P.ι.IsContinuous (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)]
    (x : P.FullSubcategory)
    [HasSheafify ((subsiteTopology B S hS p τ P).over x) AddCommGrpCat.{max v w t}]
    [HasExt.{max v w t}
      (Sheaf ((subsiteTopology B S hS p τ P).over x) AddCommGrpCat.{max v w t})]
    [Stacks.Sites.PreservesCoveringPullbacks ((subsiteTopology B S hS p τ P).over x)
      (Over.post (X := x) P.ι)]
    (I : Sheaf ((associatedTopology B S hS p τ).over (P.ι.obj x)) AddCommGrpCat.{max v w t})
    [Injective I] (n : ℕ) :
    haveI := Functor.isContinuous_overPost (subsiteTopology B S hS p τ P)
      (associatedTopology B S hS p τ) P.ι x
    ∀ a : Sheaf.H (((Over.post (X := x) P.ι).sheafPushforwardContinuous
        AddCommGrpCat.{max v w t} ((subsiteTopology B S hS p τ P).over x)
        ((associatedTopology B S hS p τ).over (P.ι.obj x))).obj I) (n + 1), a = 0 := by
  have hcart : ∀ {a b : X} (f : a ⟶ b), p.IsStronglyCartesian (p.map f) f := fun f =>
    hp.isStronglyCartesian_homLift (p.map f) f
  have : p.IsFibered := hp.isFibered
  have : HasPullbacks X :=
    @hasPullbacks_of_hasLimit_cospan _ _ fun {_ _ _} {f g} =>
      p.hasPullback_of_forall_isStronglyCartesian hcart f g
  have := Functor.isContinuous_overPost (subsiteTopology B S hS p τ P)
    (associatedTopology B S hS p τ) P.ι x
  intro a
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
  have hsub := Stacks.CechSite.injective_sheaf_subsingleton_sheafH_of_functor.{max v w t, max v t}
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

/-! ### Cohomology of sheaves of modules over an object of a full subsite -/

/-- **Cohomology of sheaves of modules over an object of a full subsite.** Let `P` cut out a full
subcategory of the objects of a category fibred in groupoids over the big fppf category of `S`
whose inclusion is continuous and cocontinuous, let `x` be an object of `P` at which the slice of
the inclusion admits the covering pullbacks of Stacks 00WV, and let `O` be a sheaf of rings on
the slice of the ambient site at `x`. Then for every degree `q`

`H^q(P/x, g^*ℱ) ≅ H^q(𝒳/x, ℱ)`

naturally in the sheaf of `O`-modules `ℱ`, where `H^q` is `Ext^q` out of the structure sheaf.

This is `AlgebraicGeometry.Stack.subsiteModuleCohomologyOverObjectIso` with its acyclicity
hypothesis removed, and with no essential smallness of the slice. Both sides are the cohomology of
the underlying abelian sheaves, by Stacks 03FD
(`Stacks.Cohomology.ModuleAbelianComparison.moduleFunctorHIso`), and those agree by Stacks 03YU
from acyclicity (`Stacks.Cohomology.BiggerSiteGlobal.sheafCohomologyIsoOfAcyclic`) for the slice
functor, with the acyclicity supplied by Stacks 0D6X,
`AlgebraicGeometry.Stack.subsiteSliceCohomology_eq_zero_of_le`. -/
def subsiteSliceModuleCohomologyIso (hp : p.IsFiberedInGroupoids)
    [P.ι.IsContinuous (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)]
    [P.ι.IsCocontinuous (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)]
    (x : P.FullSubcategory)
    [Stacks.Sites.PreservesCoveringPullbacks ((subsiteTopology B S hS p τ P).over x)
      (Over.post (X := x) P.ι)]
    (O : Sheaf ((associatedTopology B S hS p τ).over (P.ι.obj x)) RingCat.{max v w t}) (q : ℕ) :
    subsiteSliceModuleRestriction.{u, v, w, t} B S hS p τ P x O ⋙
        moduleFunctorH.{t, w, max v w} ((subsiteTopology B S hS p τ P).over x)
          (subsiteSliceRing.{u, v, w, t} B S hS p τ P x O) q ≅
      moduleFunctorH.{t, w, max v w}
        ((associatedTopology B S hS p τ).over (P.ι.obj x)) O q :=
  haveI := Functor.isContinuous_overPost (subsiteTopology B S hS p τ P)
    (associatedTopology B S hS p τ) P.ι x
  haveI : HasSheafify ((subsiteTopology B S hS p τ P).over x) AddCommGrpCat.{max v w t} :=
    Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{max v w, w, t}
  haveI : HasSheafify ((associatedTopology B S hS p τ).over (P.ι.obj x))
      AddCommGrpCat.{max v w t} :=
    Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{max v w, w, t}
  haveI : EnoughInjectives
      (Sheaf ((subsiteTopology B S hS p τ P).over x) AddCommGrpCat.{max v w t}) :=
    Stacks.Cohomology.SiteModules.site_enoughInjectives_addCommGrp.{max v w, w, t}
  haveI : EnoughInjectives
      (Sheaf ((associatedTopology B S hS p τ).over (P.ι.obj x)) AddCommGrpCat.{max v w t}) :=
    Stacks.Cohomology.SiteModules.site_enoughInjectives_addCommGrp.{max v w, w, t}
  haveI : HasExt.{max v w t}
      (Sheaf ((subsiteTopology B S hS p τ P).over x) AddCommGrpCat.{max v w t}) :=
    Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{max v w, w, t}
  haveI : HasExt.{max v w t}
      (Sheaf ((associatedTopology B S hS p τ).over (P.ι.obj x)) AddCommGrpCat.{max v w t}) :=
    Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{max v w, w, t}
  haveI := (Functor.sheafAdjunctionCocontinuous (Over.post (X := x) P.ι)
    AddCommGrpCat.{max v w t} ((subsiteTopology B S hS p τ P).over x)
    ((associatedTopology B S hS p τ).over (P.ι.obj x))).isLeftAdjoint
  Functor.isoWhiskerLeft _
      (Stacks.Cohomology.ModuleAbelianComparison.moduleFunctorHIso.{t} _ _ q) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Iso.refl (SheafOfModules.toSheaf O ⋙
      (Over.post (X := x) P.ι).sheafPushforwardContinuous AddCommGrpCat.{max v w t}
        ((subsiteTopology B S hS p τ P).over x)
        ((associatedTopology B S hS p τ).over (P.ι.obj x)))) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Stacks.Cohomology.BiggerSiteGlobal.sheafCohomologyIsoOfAcyclic
        ((subsiteTopology B S hS p τ P).over x)
        ((associatedTopology B S hS p τ).over (P.ι.obj x)) (Over.post (X := x) P.ι)
        Over.mkIdTerminal Over.mkIdTerminal (by simp)
        (fun I _ n a =>
          subsiteSliceCohomology_eq_zero_of_le.{u, v, w, t} B S hS p τ P hp x I n a) q) ≪≫
    (Stacks.Cohomology.ModuleAbelianComparison.moduleFunctorHIso.{t} _ _ q).symm

/-! ### The flat-fppf site -/

namespace FlatFppf

variable (𝒴 : Stack.AlgebraicStacks.{u, w} B S hS)

/-- **Stacks 0GR0, part (2)(b), for sheaves of modules** — the source's "the same holds for
sheaves of modules". For an algebraic stack `𝒳`, a flat object `x` of `𝒳` and a sheaf `ℱ` of
`𝒪_𝒳`-modules on the fppf site of `𝒳` over `x`,

`H^q(x, ℱ) = H^q(𝒳_{flat,fppf}/x, g^*ℱ)`,

naturally in `ℱ`, where `g^*` is restriction of sheaves of modules to the flat-fppf site of
Stacks 0787, cohomology over an object is the global cohomology on the slice site, and `H^q` of a
sheaf of modules is `Ext^q` out of the structure sheaf.

This is `AlgebraicGeometry.Stack.FlatFppf.moduleCohomologyOverObjectIso` with its acyclicity
hypothesis removed: it is `AlgebraicGeometry.Stack.subsiteSliceModuleCohomologyIso` for the flat
objects, whose covering-pullback condition is
`AlgebraicGeometry.Stack.FlatFppf.preservesCoveringPullbacks_over_inclusion`. As there, the sheaf
of modules is quantified over the slice site at `x`, which is the generalization the comparison
naturally has: the source's `H^q(x, ℱ)` for `ℱ` on `𝒳` is the cohomology of the restriction of
`ℱ` to the slice. -/
@[stacks 0GR0 "part (2)(b), sheaves of modules"]
def sliceModuleCohomologyIso
    (x : ObjectProperty.FullSubcategory (objectProperty B S hS 𝒴)) (q : ℕ) :
    haveI := isContinuous_inclusion B S hS 𝒴 flatClosure
    haveI := isCocontinuous_inclusion B S hS 𝒴 flatClosure
    subsiteSliceModuleRestriction.{u, u + 1, u, t} B S hS 𝒴.val.val.p B.topology
          (objectProperty B S hS 𝒴) x (sliceStructureRing.{u, w, t} B S hS 𝒴 x) ⋙
        moduleFunctorH.{t, u, u + 1} ((inclusionTopology B S hS 𝒴).over x)
          (subsiteSliceRing.{u, u + 1, u, t} B S hS 𝒴.val.val.p B.topology
            (objectProperty B S hS 𝒴) x (sliceStructureRing.{u, w, t} B S hS 𝒴 x)) q ≅
      moduleFunctorH.{t, u, u + 1}
        ((fppfTopology B S hS 𝒴).over ((objectProperty B S hS 𝒴).ι.obj x))
        (sliceStructureRing.{u, w, t} B S hS 𝒴 x) q :=
  haveI := isContinuous_inclusion B S hS 𝒴 flatClosure
  haveI := isCocontinuous_inclusion B S hS 𝒴 flatClosure
  haveI := preservesCoveringPullbacks_over_inclusion B S hS 𝒴 x
  subsiteSliceModuleCohomologyIso.{u, u + 1, u, t} B S hS 𝒴.val.val.p B.topology
    (objectProperty B S hS 𝒴) 𝒴.val.isFiberedInGroupoids x
    (sliceStructureRing.{u, w, t} B S hS 𝒴 x) q

end FlatFppf

/-! ### The lisse-étale site -/

namespace LisseEtale

variable (𝒴 : Stack.AlgebraicStacks.{u, w} B S hS)

/-- **Stacks 0GR0, part (1)(b), for sheaves of modules** — the source's "the same holds for
sheaves of modules". For an algebraic stack `𝒳`, a smooth object `x` of `𝒳` and a sheaf `ℱ` of
`𝒪_𝒳`-modules on the étale site of `𝒳` over `x`,

`H^q(x, ℱ) = H^q(𝒳_{lisse,étale}/x, g^*ℱ)`,

naturally in `ℱ`, where `g^*` is restriction of sheaves of modules to the lisse-étale site of
Stacks 0787 and `H^q` of a sheaf of modules is `Ext^q` out of the structure sheaf.

This is `AlgebraicGeometry.Stack.LisseEtale.moduleCohomologyOverObjectIso` with its acyclicity
hypothesis removed: it is `AlgebraicGeometry.Stack.subsiteSliceModuleCohomologyIso` for the
smooth objects, whose covering-pullback condition is
`AlgebraicGeometry.Stack.LisseEtale.preservesCoveringPullbacks_over_inclusion`. The sheaf of
modules is quantified over the slice site at `x`; see
`AlgebraicGeometry.Stack.FlatFppf.sliceModuleCohomologyIso`. -/
@[stacks 0GR0 "part (1)(b), sheaves of modules"]
def sliceModuleCohomologyIso
    (x : ObjectProperty.FullSubcategory (smoothObject.{u, w} B S hS 𝒴)) (q : ℕ) :
    haveI := isContinuous_inclusion B S hS 𝒴 (closedUnderSmoothMorphisms B S hS 𝒴)
    haveI := isCocontinuous_inclusion B S hS 𝒴 (closedUnderSmoothMorphisms B S hS 𝒴)
    subsiteSliceModuleRestriction.{u, u + 1, u, t} B S hS 𝒴.val.val.p (etaleTopology B)
          (smoothObject.{u, w} B S hS 𝒴) x (sliceStructureRing.{u, w, t} B S hS 𝒴 x) ⋙
        moduleFunctorH.{t, u, u + 1} ((inclusionTopology.{u, w} B S hS 𝒴).over x)
          (subsiteSliceRing.{u, u + 1, u, t} B S hS 𝒴.val.val.p (etaleTopology B)
            (smoothObject.{u, w} B S hS 𝒴) x
            (sliceStructureRing.{u, w, t} B S hS 𝒴 x)) q ≅
      moduleFunctorH.{t, u, u + 1}
        ((associatedTopology B S hS 𝒴.val.val.p (etaleTopology B)).over
          ((smoothObject.{u, w} B S hS 𝒴).ι.obj x))
        (sliceStructureRing.{u, w, t} B S hS 𝒴 x) q :=
  haveI := isContinuous_inclusion B S hS 𝒴 (closedUnderSmoothMorphisms B S hS 𝒴)
  haveI := isCocontinuous_inclusion B S hS 𝒴 (closedUnderSmoothMorphisms B S hS 𝒴)
  haveI := preservesCoveringPullbacks_over_inclusion.{u, w} B S hS 𝒴 x
  subsiteSliceModuleCohomologyIso.{u, u + 1, u, t} B S hS 𝒴.val.val.p (etaleTopology B)
    (smoothObject.{u, w} B S hS 𝒴) 𝒴.val.isFiberedInGroupoids x
    (sliceStructureRing.{u, w, t} B S hS 𝒴 x) q

end LisseEtale

end AlgebraicGeometry.Stack

end
