module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.RepresentableQC.ChartCovers
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.RepresentableQC.LiftedSites
public import StacksFrontier.AlgebraicGeometry.Topologies.AffineSiteLiftedCartesian
public import StacksFrontier.AlgebraicGeometry.Topologies.EtaleSliceSubsite
public import StacksFrontier.Algebra.Category.Ring.PushoutTensorComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.SubsiteComparisonDescent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.SubsiteQuasiCoherentEquivalence
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteLocalization
public import StacksFrontier.CategoryTheory.Sites.Modules.UniverseLiftDenseSubsite
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSitesLimits

/-!
# Étale descent of the cartesian comparison maps on the lifted affine site

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be fibred in groupoids, representable by an algebraic space `F`
through an equivalence `e`, and let `X↑` be the lift of the étale affine ringed site
`(𝒳_{affine, étale}, 𝒪)` to a single universe (`AlgebraicGeometry.Stack.affineLiftedSite`). For an
object `x` of `X↑`, the objects of the slice `X↑/x` lying over an étale morphism of affine schemes
form the small étale site `X↑_{x, ét}` of `x`, a ringed site with the restricted structure sheaf
(`AlgebraicGeometry.Stack.affineLiftedEtaleSlice`), and the inclusion is a morphism of ringed
sites `X↑/x ⟶ X↑_{x, ét}` (`AlgebraicGeometry.Stack.affineLiftedEtaleSliceHom`).

On `X↑_{x, ét}` the restriction maps of the structure sheaf are flat and carry fibre products to
pushouts, cartesian presheaves of modules are sheaves and cartesian sheaves of modules are acyclic:
it is a flatly cofinal site of affine schemes. So the cartesian condition on `Rε_*L` descends along
a finite étale covering of `x` through `X↑_{x, ét}`
(`Stacks.Cohomology.SubsiteComparisonDescent.isIso_comparison_map_of_cover`).

Taking for the covering the finite étale covering of `x` by objects mapping to affine étale charts
of `F` (`AlgebraicGeometry.Stack.exists_finite_covering_liftedAffineEtaleHom`), this gives every
object of `X↑` a descent cover for the morphism of lifted ringed sites
`AlgebraicGeometry.Stack.liftedAffineEtaleHom` (`AlgebraicGeometry.Stack.nonempty_descentCover`),
which is the descent hypothesis of the restriction equivalence of the 0GZS subcategories along a
full subsite (`Stacks.Cohomology.SubsiteQuasiCoherentEquivalence.DescentCover`) used in the proof
of Stacks 0H0K.

## Main definitions

* `AlgebraicGeometry.Stack.affineLiftedToScheme`: the underlying affine scheme of an object of
  `X↑`.
* `AlgebraicGeometry.Stack.affineLiftedEtaleSlice`: the small étale site of an object of `X↑`,
  as a ringed site.
* `AlgebraicGeometry.Stack.affineLiftedEtaleSliceHom`: the morphism of ringed sites from the slice
  `X↑/x` to the small étale site of `x`.

## Main results

* `AlgebraicGeometry.Stack.isEtaleCofinal_affineLiftedSite`: every covering sieve of `X↑` contains
  a finite covering family lying over an étale covering of affine schemes.
* `AlgebraicGeometry.Stack.isIso_comparison_of_etaleCover`: the cartesian condition descends
  along a finite étale covering of an object of `X↑`.
* `AlgebraicGeometry.Stack.nonempty_descentCover`: every object of `X↑` has a descent cover for
  `AlgebraicGeometry.Stack.liftedAffineEtaleHom`.

## References

* [Stacks Project, Tag 0H0K](https://stacks.math.columbia.edu/tag/0H0K)
* [Stacks Project, Tag 0GZS](https://stacks.math.columbia.edu/tag/0GZS)
* [Stacks Project, Tag 00X6](https://stacks.math.columbia.edu/tag/00X6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.EtaleSlice Stacks.AffineSiteBaseChange
open Stacks.ModulesOnACategory.QuasiCoherentEquivalence
open Stacks.ModulesOnACategory.ChaoticComparison
open Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange (baseChangeDataOfComm)
open Stacks.Cohomology.SubsiteQuasiCoherentEquivalence

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

namespace AlgebraicGeometry.Stack

universe u v w t t'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-! ### The underlying affine schemes of the lifted affine site -/

/-- The underlying affine scheme of an object of the lifted affine site `X↑`. -/
abbrev affineLiftedToScheme : (affineLiftedSite.{u, v, w, t} B S hS p hp).C ⥤ Scheme.{u} :=
  AsSmall.down ⋙ AffineCategory.toScheme B S hS p

/-- The underlying schemes of the objects of the lifted affine site are affine. -/
instance isAffine_affineLiftedToScheme_obj (x : (affineLiftedSite.{u, v, w, t} B S hS p hp).C) :
    IsAffine ((affineLiftedToScheme.{u, v, w, t} B S hS p hp).obj x) :=
  AffineCategory.isAffine_toScheme_obj B S hS p _

/-- The lifted affine site has fibre products. -/
theorem hasPullbacks_affineLiftedSite :
    HasPullbacks (affineLiftedSite.{u, v, w, t} B S hS p hp).C :=
  have := AffineCategory.hasPullbacks B S hS p hp
  Adjunction.hasLimitsOfShape_of_equivalence (AsSmall.equiv (C := AffineCategory B S hS p)).inverse

/-- The underlying scheme functor of the lifted affine site preserves fibre products. -/
theorem preservesPullbacks_affineLiftedToScheme :
    PreservesLimitsOfShape WalkingCospan (affineLiftedToScheme.{u, v, w, t} B S hS p hp) :=
  have := AffineCategory.preservesPullbacks_toScheme B S hS p hp
  comp_preservesLimitsOfShape (AsSmall.equiv (C := AffineCategory B S hS p)).inverse _

/-- **The lifted affine site is étale cofinal**: every covering sieve of `X↑` contains a finite
covering family lying over an étale covering of affine schemes. This is
`AlgebraicGeometry.Stack.AffineCategory.exists_finite_etale_covering`, carried to the small model
`AsSmall`. -/
theorem isEtaleCofinal_affineLiftedSite :
    IsEtaleCofinal (affineLiftedToScheme.{u, v, w, t} B S hS p hp)
      (affineLiftedSite.{u, v, w, t} B S hS p hp).J := by
  intro y T hT
  have hd := RingedSite.lift_asSmallDown_isDenseSubsite.{t}
    (AffineCategory.siteKindRingedSite B S hS p hp .etale)
  obtain ⟨E, hfin, het, hcov, hle⟩ :=
    AffineCategory.exists_finite_etale_covering B S hS p hp _ (hd.functorPushforward_mem_iff.2 hT)
  let ε : Fin (Nat.card E.I₀) ≃ E.I₀ := (Finite.equivFin E.I₀).symm
  let E' := E.reindex ε
  have hs : E'.sieve₀ = E.sieve₀ := congrArg Sieve.generate (E.presieve₀_reindex ε)
  let E'' : PreZeroHypercover.{0} y :=
    ⟨Fin (Nat.card E.I₀), fun i => AsSmall.up.obj (E'.X i), fun i => AsSmall.up.map (E'.f i)⟩
  refine ⟨E'', inferInstanceAs (Finite (Fin _)), ?_, ?_, ?_⟩
  · have hpr : (E'.map (AffineCategory.toScheme B S hS p)).presieve₀ =
        (E.map (AffineCategory.toScheme B S hS p)).presieve₀ := by
      rw [PreZeroHypercover.presieve₀_map, PreZeroHypercover.presieve₀_map,
        E.presieve₀_reindex ε]
    exact hpr ▸ het
  · rw [PreZeroHypercover.sieve₀, Sieve.generate_le_iff]
    rintro _ _ ⟨i⟩
    obtain ⟨Z, g, h, hg, hfac⟩ := hle _ (Sieve.le_generate _ _ _ ⟨ε i⟩)
    rw [show E''.f i = AsSmall.up.map h ≫ g from congrArg AsSmall.up.map hfac]
    exact T.downward_closed hg _
  · refine hd.functorPushforward_mem_iff.1 ?_
    refine GrothendieckTopology.superset_covering _ ?_ (hs ▸ hcov)
    rintro Z g ⟨Y, a, b, ⟨i⟩, rfl⟩
    exact ⟨_, AsSmall.up.map (E'.f i), a, Sieve.le_generate _ _ _ ⟨i⟩, rfl⟩

/-! ### The small étale site of an object of the lifted affine site -/

section EtaleSlice

variable (x : (affineLiftedSite.{u, v, w, t} B S hS p hp).C)

/-- The inclusion of the small étale site into the slice is continuous. -/
instance affineLiftedEtaleSlice_isContinuous :
    (etaleOver (affineLiftedToScheme.{u, v, w, t} B S hS p hp) x).ι.IsContinuous
      (topology (affineLiftedToScheme.{u, v, w, t} B S hS p hp)
        (affineLiftedSite.{u, v, w, t} B S hS p hp).J x)
      ((affineLiftedSite.{u, v, w, t} B S hS p hp).over x).J :=
  haveI := hasPullbacks_affineLiftedSite.{u, v, w, t} B S hS p hp
  haveI := preservesPullbacks_affineLiftedToScheme.{u, v, w, t} B S hS p hp
  isContinuous_ι x (isEtaleCofinal_affineLiftedSite.{u, v, w, t} B S hS p hp)

/-- **The small étale site of an object `x` of the lifted affine site, as a ringed site**: the
full subcategory of the slice `X↑/x` on the objects lying over an étale morphism of affine schemes
(`Stacks.EtaleSlice.EtaleSlice`), with the topology inherited from the slice and the restriction
of the structure sheaf of the slice. -/
abbrev affineLiftedEtaleSlice : RingedSite.{max v w u t, max v w u t, max v w u t} where
  C := EtaleSlice (affineLiftedToScheme.{u, v, w, t} B S hS p hp) x
  J := topology (affineLiftedToScheme.{u, v, w, t} B S hS p hp)
    (affineLiftedSite.{u, v, w, t} B S hS p hp).J x
  O := ⟨(etaleOver (affineLiftedToScheme.{u, v, w, t} B S hS p hp) x).ι.op ⋙
      ((affineLiftedSite.{u, v, w, t} B S hS p hp).over x).O.obj,
    by
      have := affineLiftedEtaleSlice_isContinuous.{u, v, w, t} B S hS p hp x
      exact Functor.op_comp_isSheaf _
        (topology (affineLiftedToScheme.{u, v, w, t} B S hS p hp)
          (affineLiftedSite.{u, v, w, t} B S hS p hp).J x)
        ((affineLiftedSite.{u, v, w, t} B S hS p hp).over x).J
        ((affineLiftedSite.{u, v, w, t} B S hS p hp).over x).O⟩

/-- The inclusion of the small étale site into the slice is cocontinuous. -/
instance affineLiftedEtaleSlice_isCocontinuous :
    (etaleOver (affineLiftedToScheme.{u, v, w, t} B S hS p hp) x).ι.IsCocontinuous
      (affineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).J
      ((affineLiftedSite.{u, v, w, t} B S hS p hp).over x).J :=
  isCocontinuous_ι x (isEtaleCofinal_affineLiftedSite.{u, v, w, t} B S hS p hp)

/-- The small étale site of an object of the lifted affine site has fibre products. -/
instance affineLiftedEtaleSlice_hasPullbacks :
    HasPullbacks (affineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).C :=
  haveI := hasPullbacks_affineLiftedSite.{u, v, w, t} B S hS p hp
  haveI := preservesPullbacks_affineLiftedToScheme.{u, v, w, t} B S hS p hp
  Stacks.EtaleSlice.hasPullbacks _ x

/-- **The inclusion of the small étale site into the slice, as a morphism of ringed sites**
`X↑/x ⟶ X↑_{x, ét}`. It defines a morphism of sites by Stacks 00X6: the small étale site has fibre
products and the terminal object `id_x`, which the inclusion preserves. Its structure map is the
identity, the structure sheaf of the small étale site being the restriction of that of the
slice. -/
def affineLiftedEtaleSliceHom :
    RingedSite.Hom ((affineLiftedSite.{u, v, w, t} B S hS p hp).over x)
      (affineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x) where
  u := (etaleOver (affineLiftedToScheme.{u, v, w, t} B S hS p hp) x).ι
  isMorphismOfSites :=
    haveI := hasPullbacks_affineLiftedSite.{u, v, w, t} B S hS p hp
    haveI := preservesPullbacks_affineLiftedToScheme.{u, v, w, t} B S hS p hp
    haveI := affineLiftedEtaleSlice_isContinuous.{u, v, w, t} B S hS p hp x
    haveI := preservesPullbacks_ι (affineLiftedToScheme.{u, v, w, t} B S hS p hp) x
    Functor.isMorphismOfSites_of_isTerminal _ _ _ (isTerminal _ x) (isTerminal_ι_obj _ x)
  fsharp := 𝟙 _

/-- The functor of the morphism of ringed sites `X↑/x ⟶ X↑_{x, ét}` is the inclusion. -/
@[simp]
theorem affineLiftedEtaleSliceHom_u :
    (affineLiftedEtaleSliceHom.{u, v, w, t} B S hS p hp x).u =
      (etaleOver (affineLiftedToScheme.{u, v, w, t} B S hS p hp) x).ι :=
  rfl

/-- The structure map of the morphism of ringed sites `X↑/x ⟶ X↑_{x, ét}` is an isomorphism. -/
instance affineLiftedEtaleSliceHom_fsharp_isIso :
    IsIso (affineLiftedEtaleSliceHom.{u, v, w, t} B S hS p hp x).fsharp :=
  inferInstanceAs (IsIso (𝟙 _))

/-- The underlying scheme functor of the small étale site of an object of the lifted affine
site. -/
abbrev affineLiftedEtaleSliceToScheme :
    (affineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).C ⥤ Scheme.{u} :=
  Stacks.EtaleSlice.toScheme (affineLiftedToScheme.{u, v, w, t} B S hS p hp) x

/-- The ring transport from the global functions of the underlying affine schemes to the
structure sheaf of the small étale site: the latter is the former with its rings raised to the
universe of the site. -/
abbrev affineLiftedEtaleSliceRingTransport :
    Stacks.UniverseLift.RingTransport
      (CategoryTheory.Equivalence.refl : (affineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).C ≌ _)
      (rings (affineLiftedEtaleSliceToScheme.{u, v, w, t} B S hS p hp x) ⋙
        forget₂ CommRingCat RingCat)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (affineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).O).obj :=
  Stacks.UniverseLift.uliftRingTransport.{max v w t}
    (rings (affineLiftedEtaleSliceToScheme.{u, v, w, t} B S hS p hp x))

/-- The underlying schemes of the objects of the small étale site are affine. -/
private theorem isAffine_affineLiftedEtaleSliceToScheme_obj
    (Y : (affineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).C) :
    IsAffine ((affineLiftedEtaleSliceToScheme.{u, v, w, t} B S hS p hp x).obj Y) :=
  isAffine_affineLiftedToScheme_obj.{u, v, w, t} B S hS p hp _

/-- The topology of the small étale site is flatly cofinal for its underlying scheme
functor. -/
theorem isFlatCofinal_affineLiftedEtaleSlice :
    IsFlatCofinal (affineLiftedEtaleSliceToScheme.{u, v, w, t} B S hS p hp x)
      (affineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).J :=
  have := hasPullbacks_affineLiftedSite.{u, v, w, t} B S hS p hp
  have := preservesPullbacks_affineLiftedToScheme.{u, v, w, t} B S hS p hp
  Stacks.EtaleSlice.isFlatCofinal x (isEtaleCofinal_affineLiftedSite.{u, v, w, t} B S hS p hp)

/-- **The restriction maps of the structure sheaf of the small étale site are flat**: every
morphism of the small étale site lies over an étale, hence flat, morphism of affine schemes. -/
theorem flat_affineLiftedEtaleSlice_map
    ⦃U V : (affineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).C⦄ (f : U ⟶ V) :
    ((affineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).O.obj.map f.op).hom.Flat := by
  have := hasPullbacks_affineLiftedSite.{u, v, w, t} B S hS p hp
  have := preservesPullbacks_affineLiftedToScheme.{u, v, w, t} B S hS p hp
  have := isAffine_affineLiftedEtaleSliceToScheme_obj.{u, v, w, t} B S hS p hp x
  exact flat_ringSheaf_map_of_ringTransport.{u, max v w t}
    (affineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x)
    (affineLiftedEtaleSliceToScheme.{u, v, w, t} B S hS p hp x)
    (affineLiftedEtaleSliceRingTransport.{u, v, w, t} B S hS p hp x)
    (fun g => by
      have := etale_toScheme_map g
      infer_instance) f.op

/-- **The structure sheaf of the small étale site carries fibre products to pushouts**: the
underlying scheme functor preserves fibre products, the global functions of a fibre product of
affine schemes are the tensor product, and raising the universe of the rings preserves pushout
squares. -/
theorem isPushout_affineLiftedEtaleSlice_map
    ⦃A B' D : (affineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).C⦄ (f : A ⟶ D) (h : B' ⟶ D) :
    IsPushout ((affineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).O.obj.map f.op)
      ((affineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).O.obj.map h.op)
      ((affineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).O.obj.map (pullback.fst f h).op)
      ((affineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).O.obj.map (pullback.snd f h).op) := by
  have := hasPullbacks_affineLiftedSite.{u, v, w, t} B S hS p hp
  have := preservesPullbacks_affineLiftedToScheme.{u, v, w, t} B S hS p hp
  have := isAffine_affineLiftedEtaleSliceToScheme_obj.{u, v, w, t} B S hS p hp x
  have hpb := Functor.map_isPullback (affineLiftedEtaleSliceToScheme.{u, v, w, t} B S hS p hp x)
    (IsPullback.of_hasPullback f h)
  have h₂ := isPushout_appTop_of_isPullback hpb
  exact CommRingCat.isPushout_ulift.{u, max v w t} h₂

/-- Cartesian presheaves of modules on a slice of the small étale site are sheaves. -/
theorem isSheaf_of_isCartesianPresheaf_affineLiftedEtaleSlice_over
    (U : (affineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).C)
    (P : PresheafOfModules.{max v w u t} (Stacks.Sites.OverModules.overRingPresheaf
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (affineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).O).obj U))
    (hP : IsCartesianPresheaf P) :
    Presheaf.IsSheaf ((affineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).J.over U)
      P.presheaf := by
  have := hasPullbacks_affineLiftedSite.{u, v, w, t} B S hS p hp
  have := preservesPullbacks_affineLiftedToScheme.{u, v, w, t} B S hS p hp
  have : HasPullbacks (affineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).C :=
    affineLiftedEtaleSlice_hasPullbacks.{u, v, w, t} B S hS p hp x
  have : HasPullbacks ((affineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).over U).C :=
    (inferInstance : HasPullbacks (Over U))
  have : PreservesLimitsOfShape WalkingCospan
      (Over.forget U ⋙ affineLiftedEtaleSliceToScheme.{u, v, w, t} B S hS p hp x) :=
    comp_preservesLimitsOfShape _ _
  have : ∀ Y, IsAffine ((Over.forget U ⋙
      affineLiftedEtaleSliceToScheme.{u, v, w, t} B S hS p hp x).obj Y) :=
    fun Y => isAffine_affineLiftedEtaleSliceToScheme_obj.{u, v, w, t} B S hS p hp x Y.left
  exact isSheaf_of_isCartesianPresheaf_of_ringTransport.{u, max v w t}
    ((affineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).over U)
    (Over.forget U ⋙ affineLiftedEtaleSliceToScheme.{u, v, w, t} B S hS p hp x)
    ((isFlatCofinal_affineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).over U)
    (Stacks.UniverseLift.uliftRingTransport.{max v w t}
      (rings (Over.forget U ⋙ affineLiftedEtaleSliceToScheme.{u, v, w, t} B S hS p hp x))) P hP

end EtaleSlice

/-! ### Descent of the cartesian condition along a finite étale covering -/

section Descent

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance] AlgebraicGeometry.RingedSite.Hom.pushforwardTopos_additive
attribute [local instance 1500] HasDerivedCategory.standard
attribute [local instance 2000]
  Stacks.ModulesOnACategory.QuasiCoherentEquivalence.derivedPresheafCategory
attribute [local instance 2000]
  Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory

/-- **The cartesian condition descends along a finite étale covering of an object of the lifted
affine site.** Let `π i : x_i ⟶ x` be a finite family of morphisms of `X↑` lying over étale
morphisms of affine schemes and generating a covering sieve, and let `L` be an object of
`D(O_{X↑})` such that the comparison map of `Rε_*L` is invertible along every morphism whose
target maps to some `x_i`. Then the comparison map of `Rε_*L` along each `π i` is invertible.

The family `π i` is a covering of the terminal object `id_x` of the small étale site `X↑_{x, ét}`
of `x`; the comparison maps of `Rε_*L` along the arrows of `X↑/x` are those of `Rε_*(L|_x)`
(`Stacks.Cohomology.SubsiteQuasiCoherentEquivalence.isIso_comparison_restriction_iff`), and the
cartesian condition descends through the morphism of ringed sites `X↑/x ⟶ X↑_{x, ét}`
(`Stacks.Cohomology.SubsiteComparisonDescent.isIso_comparison_map_of_cover`), whose hypotheses on
`X↑_{x, ét}` hold because it is a flatly cofinal site of affine schemes. -/
theorem isIso_comparison_of_etaleCover (x : (affineLiftedSite.{u, v, w, t} B S hS p hp).C)
    {I : Type*} [Finite I] (obj : I → (affineLiftedSite.{u, v, w, t} B S hS p hp).C)
    (π : ∀ i, obj i ⟶ x)
    (hπ : Sieve.ofArrows obj π ∈ (affineLiftedSite.{u, v, w, t} B S hS p hp).J x)
    (het : ∀ i, Etale ((affineLiftedToScheme.{u, v, w, t} B S hS p hp).map (π i)))
    (L : DerivedCategory (SheafOfModules.{max v w u t}
      (Stacks.SheafOfModules.Tensor.ringSheaf (affineLiftedSite.{u, v, w, t} B S hS p hp).O))) :
    letI := Stacks.ModulesOnACategory.TildePullback.commSections_ringSheaf
      (affineLiftedSite.{u, v, w, t} B S hS p hp)
    ∀ (_ : ∀ ⦃z z' : (affineLiftedSite.{u, v, w, t} B S hS p hp).C⦄ (a : z ⟶ z') (i : I),
      Nonempty (z' ⟶ obj i) →
        IsIso (comparison.{max v w u t} (baseChangeDataOfComm.{max v w u t, max v w u t,
          max v w u t, max v w u t} (Stacks.SheafOfModules.Tensor.ringSheaf
            (affineLiftedSite.{u, v, w, t} B S hS p hp).O).obj
          Stacks.TerminalBaseChange.CommSections.mul_comm) a.op
          ((derivedEpsilonPushforward.{max v w u t}
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (affineLiftedSite.{u, v, w, t} B S hS p hp).O)).obj L)))
    (i : I),
    IsIso (comparison.{max v w u t} (baseChangeDataOfComm.{max v w u t, max v w u t,
      max v w u t, max v w u t} (Stacks.SheafOfModules.Tensor.ringSheaf
        (affineLiftedSite.{u, v, w, t} B S hS p hp).O).obj
      Stacks.TerminalBaseChange.CommSections.mul_comm) (π i).op
      ((derivedEpsilonPushforward.{max v w u t}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (affineLiftedSite.{u, v, w, t} B S hS p hp).O)).obj L)) := by
  intro hL i
  let X := affineLiftedSite.{u, v, w, t} B S hS p hp
  let Lx := affineLiftedToScheme.{u, v, w, t} B S hS p hp
  let Sm := affineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x
  let g := affineLiftedEtaleSliceHom.{u, v, w, t} B S hS p hp x
  have := hasPullbacks_affineLiftedSite.{u, v, w, t} B S hS p hp
  have := preservesPullbacks_affineLiftedToScheme.{u, v, w, t} B S hS p hp
  have := isAffine_affineLiftedEtaleSliceToScheme_obj.{u, v, w, t} B S hS p hp x
  have : HasPullbacks Sm.C := affineLiftedEtaleSlice_hasPullbacks.{u, v, w, t} B S hS p hp x
  have : g.u.IsCocontinuous Sm.J (X.over x).J :=
    affineLiftedEtaleSlice_isCocontinuous.{u, v, w, t} B S hS p hp x
  let ts : I → Sm.C := fun i => ⟨Over.mk (π i ≫ (Over.mk (𝟙 x)).hom), by
    show Etale (Lx.map (π i ≫ 𝟙 x))
    rw [Category.comp_id]
    exact het i⟩
  let q : ∀ i, ts i ⟶ terminal Lx x := fun i => ObjectProperty.homMk (Over.homMk (π i))
  have hcov : Sieve.ofArrows ts q ∈ Sm.J (terminal Lx x) := by
    refine ofArrows_mem_topology x (isEtaleCofinal_affineLiftedSite.{u, v, w, t} B S hS p hp)
      ts q ?_
    rw [GrothendieckTopology.mem_over_iff]
    refine X.J.superset_covering ?_ hπ
    rw [Sieve.generate_le_iff]
    rintro _ _ ⟨i⟩
    rw [Sieve.overEquiv_iff]
    exact Sieve.ofArrows_mk _ _ i
  exact (isIso_comparison_restriction_iff X x L (g.u.map (q i)).op).1
    (Stacks.Cohomology.SubsiteComparisonDescent.isIso_comparison_map_of_cover g
      (baseChangeDataOver X x) (isTerminal Lx x) ts q hcov
      (flat_affineLiftedEtaleSlice_map.{u, v, w, t} B S hS p hp x)
      (isPushout_affineLiftedEtaleSlice_map.{u, v, w, t} B S hS p hp x)
      (fun i => isSheaf_of_isCartesianPresheaf_affineLiftedEtaleSlice_over.{u, v, w, t}
        B S hS p hp x (ts i))
      (isZero_rightDerived_evaluation_of_ringTransport.{u, max v w t} Sm
        (affineLiftedEtaleSliceToScheme.{u, v, w, t} B S hS p hp x)
        (isFlatCofinal_affineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x)
        (affineLiftedEtaleSliceRingTransport.{u, v, w, t} B S hS p hp x))
      ((sheafRestriction.{max v w u t} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        x).mapDerivedCategory.obj L)
      (fun i A B b s => (isIso_comparison_restriction_iff X x L (g.u.map b).op).2
        (hL (g.u.map b).left i ⟨(g.u.map s).left⟩)) (q i))

variable (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
  (e : StacksRepresentableCFG.EquivalenceOver p (presheafOfCategories (F ⋙ typeToCat)).p)

/-- **Every object of the lifted affine site has a descent cover for the morphism of lifted
ringed sites of Stacks 0H0K.** For an object `x` of the lift `X↑` of `𝒳_{affine, étale}`, the
finite étale covering `x_i ⟶ x` by objects mapping to affine étale charts of `F`
(`AlgebraicGeometry.Stack.exists_finite_covering_liftedAffineEtaleHom`) is a descent cover for
`AlgebraicGeometry.Stack.liftedAffineEtaleHom` in the sense of
`Stacks.Cohomology.SubsiteQuasiCoherentEquivalence.DescentCover`: if `Rε_*L` has invertible
comparison maps along every arrow whose target maps to some `x_i`, then it has invertible
comparison maps along each `x_i ⟶ x` (`AlgebraicGeometry.Stack.isIso_comparison_of_etaleCover`). -/
theorem nonempty_descentCover (x : (affineLiftedSite.{u, v, w, t} B S hS p hp).C) :
    Nonempty (DescentCover.{t'} (liftedAffineEtaleHom.{u, v, w, t} B S hS p hp F hF e) x) := by
  obtain ⟨n, obj, π, hπ, hhom, het⟩ :=
    exists_finite_covering_liftedAffineEtaleHom.{u, v, w, t} B S hS p hp F hF e x
  have hπ' : Sieve.ofArrows (fun j : ULift.{t'} (Fin n) => obj j.down) (fun j => π j.down) ∈
      (affineLiftedSite.{u, v, w, t} B S hS p hp).J x := by
    refine GrothendieckTopology.superset_covering _ ?_ hπ
    rw [Sieve.generate_le_iff]
    rintro _ _ ⟨j⟩
    exact Sieve.ofArrows_mk (fun j : ULift.{t'} (Fin n) => obj j.down) (fun j => π j.down) ⟨j⟩
  have het' : ∀ j : ULift.{t'} (Fin n),
      Etale ((affineLiftedToScheme.{u, v, w, t} B S hS p hp).map (π j.down)) :=
    fun j => ((Scheme.presieve₀_mem_precoverage_iff _).1 het).2 j.down
  exact ⟨⟨ULift.{t'} (Fin n), fun j => obj j.down, fun j => π j.down, hπ', fun j => hhom j.down,
    fun L hL j => isIso_comparison_of_etaleCover.{u, v, w, t} B S hS p hp x
      (fun j : ULift.{t'} (Fin n) => obj j.down) (fun j : ULift.{t'} (Fin n) => π j.down) hπ'
      het' L hL j⟩⟩

end Descent

end AlgebraicGeometry.Stack
