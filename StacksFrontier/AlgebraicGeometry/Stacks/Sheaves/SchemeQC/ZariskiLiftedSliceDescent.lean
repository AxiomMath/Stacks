module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.RepresentableQC.LiftedEtaleSliceDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.SchemeQC.ZariskiLiftedSite
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ZariskiSiteAxioms
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.CoveringRefinesSieve

/-!
# Zariski descent of the cartesian comparison maps on the lifted Zariski affine site

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be fibred in groupoids and let `X↑` be the lift of its Zariski affine
ringed site `(𝒳_{affine, Zar}, 𝒪)` to a single universe
(`AlgebraicGeometry.Stack.zariskiAffineLiftedSite`).

A covering sieve of `𝒳_{affine, Zar}` contains a finite covering family lying over a Zariski
covering of affine schemes
(`AlgebraicGeometry.Stack.AffineCategory.exists_finite_zariski_covering`); open immersions are
étale, so the topology of `X↑` is étale cofinal for the underlying scheme functor
(`AlgebraicGeometry.Stack.isEtaleCofinal_zariskiAffineLiftedSite`). The small étale site of an
object `x` of `X↑`, with the topology inherited from `X↑`, is then a flatly cofinal site of affine
schemes, and the cartesian condition on `Rε_*L` descends along a finite covering of `x` lying over
étale morphisms through the morphism of ringed sites `X↑/x ⟶ X↑_{x, ét}`
(`AlgebraicGeometry.Stack.isIso_comparison_of_zariskiEtaleCover`).

This is the Zariski counterpart of `RepresentableQC/LiftedEtaleSliceDescent.lean`, whose
argument it follows; only the cofinality statement depends on the topology.

## Main results

* `AlgebraicGeometry.Stack.AffineCategory.exists_finite_zariski_covering`: a covering sieve of
  the associated affine Zariski site contains a finite covering family lying over a Zariski
  covering of affine schemes.
* `AlgebraicGeometry.Stack.isEtaleCofinal_zariskiAffineLiftedSite`: the lifted Zariski affine site
  is étale cofinal.
* `AlgebraicGeometry.Stack.isIso_comparison_of_zariskiEtaleCover`: the cartesian condition
  descends along a finite covering of an object of `X↑` lying over étale morphisms.

## References

* [Stacks Project, Tag 0H0J](https://stacks.math.columbia.edu/tag/0H0J)
* [Stacks Project, Tag 0GZS](https://stacks.math.columbia.edu/tag/0GZS)
* [Stacks Project, Tag 00X6](https://stacks.math.columbia.edu/tag/00X6)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.EtaleSlice Stacks.AffineSiteBaseChange
open Stacks.ModulesOnACategory.QuasiCoherentEquivalence
open Stacks.ModulesOnACategory.ChaoticComparison
open Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange (baseChangeDataOfComm)
open Stacks.Cohomology.SubsiteQuasiCoherentEquivalence


namespace AlgebraicGeometry.Stack

universe u v w t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

namespace AffineCategory

/-- **A covering sieve of the associated affine Zariski site contains a finite covering family
lying over a Zariski covering of affine schemes.** The image sieve downstairs is a covering sieve
of the big affine Zariski site, which contains a standard Zariski covering; its members are lifted
back to `𝒳_{affine}` along the structure functor, which is fibred in groupoids. -/
theorem exists_finite_zariski_covering (hp : p.IsFiberedInGroupoids)
    {x : AffineCategory B S hS p} (T : Sieve x)
    (hT : T ∈ associatedAffineTopology B S hS p
      (BigAffineZariski.topology B.toBigZariskiSite S hS) x) :
    ∃ E : PreZeroHypercover.{u + 1} x, Finite E.I₀ ∧
      (E.map (toScheme B S hS p)).presieve₀ ∈
        Scheme.precoverage @IsOpenImmersion ((toScheme B S hS p).obj x) ∧
      E.sieve₀ ∈ associatedAffineTopology B S hS p
        (BigAffineZariski.topology B.toBigZariskiSite S hS) x ∧
      E.sieve₀ ≤ T := by
  classical
  let q := toAffine B S hS p
  let L := BigAffineFppf.toScheme B S hS
  have hq := isFiberedInGroupoids_toAffine B S hS p hp
  have hT' := (Functor.mem_inheritedTopology_iff_functorPushforward q
    (BigAffineZariski.topology B.toBigZariskiSite S hS) hq T).1 hT
  obtain ⟨D₀, hD, hle⟩ := exists_covering_refining_sieve
    (BigAffineZariski.IsCovering B.toBigZariskiSite S hS)
    (BigAffineZariski.precoverage B.toBigZariskiSite S hS)
    (fun {_ _} hR => by obtain ⟨E, rfl, hE⟩ := hR; exact ⟨E, hE, rfl⟩)
    (BigAffineZariski.isSite B.toBigZariskiSite S hS) hT'
  let D : PreZeroHypercover.{u + 1} (q.obj x) := D₀
  have hcov : D.sieve₀ ∈ BigAffineZariski.topology B.toBigZariskiSite S hS (q.obj x) :=
    Precoverage.generate_mem_toGrothendieck ⟨D₀, rfl, hD⟩
  obtain ⟨hzar, hstd⟩ := hD.2
  have hzar' : (D.map L).presieve₀ ∈ Scheme.precoverage @IsOpenImmersion (L.obj (q.obj x)) :=
    hzar
  obtain ⟨hsurj, hopen⟩ := (Scheme.presieve₀_mem_precoverage_iff (D.map L)).mp hzar'
  have hmem : ∀ k : D.I₀, ∃ (y : AffineCategory B S hS p) (g : y ⟶ x) (h : D.X k ⟶ q.obj y),
      T g ∧ D.f k = h ≫ q.map g := fun k => hle _ _ (Presieve.ofArrows.mk k)
  choose y g h hg hfac using hmem
  have hlift : ∀ k, ∃ (z : AffineCategory B S hS p) (φ : z ⟶ y k), q.IsHomLift (h k) φ :=
    fun k => hq.exists_lift (h k) (y k) rfl
  choose z φ hφ using hlift
  have hmap : ∀ k, q.map (φ k ≫ g k) =
      eqToHom (IsHomLift.domain_eq q (h k) (φ k)) ≫ D.f k := by
    intro k
    have := hφ k
    rw [q.map_comp, IsHomLift.fac' q (h k) (φ k), hfac k]
    simp
  let E : PreZeroHypercover.{u + 1} x := ⟨D.I₀, z, fun k => φ k ≫ g k⟩
  refine ⟨E, hstd.1, ?_, ?_, ?_⟩
  · refine (Scheme.presieve₀_mem_precoverage_iff (E.map (toScheme B S hS p))).mpr ⟨?_, ?_⟩
    · intro a
      obtain ⟨k, b, rfl⟩ := hsurj a
      have := hφ k
      let c := L.map (eqToHom (IsHomLift.domain_eq q (h k) (φ k)))
      obtain ⟨d, rfl⟩ := (inferInstance : Surjective c).surj b
      refine ⟨k, d, ?_⟩
      show (L.map (q.map (φ k ≫ g k))) d = _
      rw [hmap k, L.map_comp, Scheme.Hom.comp_apply]
      rfl
    · intro k
      show IsOpenImmersion (L.map (q.map (φ k ≫ g k)))
      rw [hmap k, L.map_comp]
      have := hopen k
      change IsOpenImmersion (L.map (D.f k)) at this
      infer_instance
  · apply (Functor.mem_inheritedTopology_iff_functorPushforward q _ hq _).mpr
    refine GrothendieckTopology.superset_covering _ ?_ hcov
    rintro _ _ ⟨_, a, _, ⟨k⟩, rfl⟩
    have := hφ k
    refine ⟨z k, φ k ≫ g k, a ≫ eqToHom (IsHomLift.domain_eq q (h k) (φ k)).symm,
      Sieve.ofArrows_mk _ _ k, ?_⟩
    rw [hmap k]
    simp
  · rintro _ _ ⟨_, a, _, ⟨k⟩, rfl⟩
    rw [← Category.assoc]
    exact T.downward_closed (hg k) (a ≫ φ k)

end AffineCategory

/-! ### The underlying affine schemes of the lifted Zariski affine site -/

/-- The underlying affine scheme of an object of the lifted Zariski affine site `X↑`. -/
abbrev zariskiAffineLiftedToScheme :
    (zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp).C ⥤ Scheme.{u} :=
  AsSmall.down ⋙ AffineCategory.toScheme B S hS p

/-- The underlying schemes of the objects of the lifted Zariski affine site are affine. -/
instance isAffine_zariskiAffineLiftedToScheme_obj
    (x : (zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp).C) :
    IsAffine ((zariskiAffineLiftedToScheme.{u, v, w, t} B S hS p hp).obj x) :=
  AffineCategory.isAffine_toScheme_obj B S hS p _

/-- The lifted Zariski affine site has fibre products. -/
theorem hasPullbacks_zariskiAffineLiftedSite :
    HasPullbacks (zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp).C :=
  have := AffineCategory.hasPullbacks B S hS p hp
  Adjunction.hasLimitsOfShape_of_equivalence (AsSmall.equiv (C := AffineCategory B S hS p)).inverse

/-- The underlying scheme functor of the lifted Zariski affine site preserves fibre products. -/
theorem preservesPullbacks_zariskiAffineLiftedToScheme :
    PreservesLimitsOfShape WalkingCospan (zariskiAffineLiftedToScheme.{u, v, w, t} B S hS p hp) :=
  have := AffineCategory.preservesPullbacks_toScheme B S hS p hp
  comp_preservesLimitsOfShape (AsSmall.equiv (C := AffineCategory B S hS p)).inverse _

/-- **The lifted Zariski affine site is étale cofinal**: every covering sieve of `X↑` contains a
finite covering family lying over a Zariski, hence étale, covering of affine schemes. This is
`AlgebraicGeometry.Stack.AffineCategory.exists_finite_zariski_covering`, carried to the small
model `AsSmall`. -/
theorem isEtaleCofinal_zariskiAffineLiftedSite :
    IsEtaleCofinal (zariskiAffineLiftedToScheme.{u, v, w, t} B S hS p hp)
      (zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp).J := by
  intro y T hT
  have hd := RingedSite.lift_asSmallDown_isDenseSubsite.{t}
    (AffineCategory.siteKindRingedSite B S hS p hp .zariski)
  obtain ⟨E, hfin, hzar, hcov, hle⟩ :=
    AffineCategory.exists_finite_zariski_covering B S hS p hp _
      (hd.functorPushforward_mem_iff.2 hT)
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
    exact Scheme.precoverage_mono
      (fun _ _ f (_ : IsOpenImmersion f) => (inferInstance : Etale f)) _ (hpr ▸ hzar)
  · rw [PreZeroHypercover.sieve₀, Sieve.generate_le_iff]
    rintro _ _ ⟨i⟩
    obtain ⟨Z, g, h, hg, hfac⟩ := hle _ (Sieve.le_generate _ _ _ ⟨ε i⟩)
    rw [show E''.f i = AsSmall.up.map h ≫ g from congrArg AsSmall.up.map hfac]
    exact T.downward_closed hg _
  · refine hd.functorPushforward_mem_iff.1 ?_
    refine GrothendieckTopology.superset_covering _ ?_ (hs ▸ hcov)
    rintro Z g ⟨Y, a, b, ⟨i⟩, rfl⟩
    exact ⟨_, AsSmall.up.map (E'.f i), a, Sieve.le_generate _ _ _ ⟨i⟩, rfl⟩

/-! ### The small étale site of an object of the lifted Zariski affine site -/

section EtaleSlice

variable (x : (zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp).C)

/-- The inclusion of the small étale site into the slice is continuous. -/
instance zariskiAffineLiftedEtaleSlice_isContinuous :
    (etaleOver (zariskiAffineLiftedToScheme.{u, v, w, t} B S hS p hp) x).ι.IsContinuous
      (topology (zariskiAffineLiftedToScheme.{u, v, w, t} B S hS p hp)
        (zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp).J x)
      ((zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp).over x).J :=
  haveI := hasPullbacks_zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp
  haveI := preservesPullbacks_zariskiAffineLiftedToScheme.{u, v, w, t} B S hS p hp
  isContinuous_ι x (isEtaleCofinal_zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp)

/-- **The small étale site of an object `x` of the lifted Zariski affine site, as a ringed
site**: the full subcategory of the slice `X↑/x` on the objects lying over an étale morphism of
affine schemes, with the topology inherited from the slice and the restriction of the structure
sheaf of the slice. -/
abbrev zariskiAffineLiftedEtaleSlice : RingedSite.{max v w u t, max v w u t, max v w u t} where
  C := EtaleSlice (zariskiAffineLiftedToScheme.{u, v, w, t} B S hS p hp) x
  J := topology (zariskiAffineLiftedToScheme.{u, v, w, t} B S hS p hp)
    (zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp).J x
  O := ⟨(etaleOver (zariskiAffineLiftedToScheme.{u, v, w, t} B S hS p hp) x).ι.op ⋙
      ((zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp).over x).O.obj,
    by
      have := zariskiAffineLiftedEtaleSlice_isContinuous.{u, v, w, t} B S hS p hp x
      exact Functor.op_comp_isSheaf _
        (topology (zariskiAffineLiftedToScheme.{u, v, w, t} B S hS p hp)
          (zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp).J x)
        ((zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp).over x).J
        ((zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp).over x).O⟩

/-- The inclusion of the small étale site into the slice is cocontinuous. -/
instance zariskiAffineLiftedEtaleSlice_isCocontinuous :
    (etaleOver (zariskiAffineLiftedToScheme.{u, v, w, t} B S hS p hp) x).ι.IsCocontinuous
      (zariskiAffineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).J
      ((zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp).over x).J :=
  isCocontinuous_ι x (isEtaleCofinal_zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp)

/-- The small étale site of an object of the lifted Zariski affine site has fibre products. -/
instance zariskiAffineLiftedEtaleSlice_hasPullbacks :
    HasPullbacks (zariskiAffineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).C :=
  haveI := hasPullbacks_zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp
  haveI := preservesPullbacks_zariskiAffineLiftedToScheme.{u, v, w, t} B S hS p hp
  Stacks.EtaleSlice.hasPullbacks _ x

/-- **The inclusion of the small étale site into the slice, as a morphism of ringed sites**
`X↑/x ⟶ X↑_{x, ét}`, with identity structure map. -/
def zariskiAffineLiftedEtaleSliceHom :
    RingedSite.Hom ((zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp).over x)
      (zariskiAffineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x) where
  u := (etaleOver (zariskiAffineLiftedToScheme.{u, v, w, t} B S hS p hp) x).ι
  isMorphismOfSites :=
    haveI := hasPullbacks_zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp
    haveI := preservesPullbacks_zariskiAffineLiftedToScheme.{u, v, w, t} B S hS p hp
    haveI := zariskiAffineLiftedEtaleSlice_isContinuous.{u, v, w, t} B S hS p hp x
    haveI := preservesPullbacks_ι (zariskiAffineLiftedToScheme.{u, v, w, t} B S hS p hp) x
    Functor.isMorphismOfSites_of_isTerminal _ _ _ (isTerminal _ x) (isTerminal_ι_obj _ x)
  fsharp := 𝟙 _

/-- The structure map of the morphism of ringed sites `X↑/x ⟶ X↑_{x, ét}` is an isomorphism. -/
instance zariskiAffineLiftedEtaleSliceHom_fsharp_isIso :
    IsIso (zariskiAffineLiftedEtaleSliceHom.{u, v, w, t} B S hS p hp x).fsharp :=
  inferInstanceAs (IsIso (𝟙 _))

/-- The underlying scheme functor of the small étale site of an object of the lifted Zariski
affine site. -/
abbrev zariskiAffineLiftedEtaleSliceToScheme :
    (zariskiAffineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).C ⥤ Scheme.{u} :=
  Stacks.EtaleSlice.toScheme (zariskiAffineLiftedToScheme.{u, v, w, t} B S hS p hp) x

/-- The ring transport from the global functions of the underlying affine schemes to the
structure sheaf of the small étale site. -/
abbrev zariskiAffineLiftedEtaleSliceRingTransport :
    Stacks.UniverseLift.RingTransport
      (CategoryTheory.Equivalence.refl :
        (zariskiAffineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).C ≌ _)
      (rings (zariskiAffineLiftedEtaleSliceToScheme.{u, v, w, t} B S hS p hp x) ⋙
        forget₂ CommRingCat RingCat)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (zariskiAffineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).O).obj :=
  Stacks.UniverseLift.uliftRingTransport.{max v w t}
    (rings (zariskiAffineLiftedEtaleSliceToScheme.{u, v, w, t} B S hS p hp x))

private instance : HasPullbacks (zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp).C :=
  hasPullbacks_zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp

private instance : PreservesLimitsOfShape WalkingCospan
    (zariskiAffineLiftedToScheme.{u, v, w, t} B S hS p hp) :=
  preservesPullbacks_zariskiAffineLiftedToScheme.{u, v, w, t} B S hS p hp

private instance (Y : (zariskiAffineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).C) :
    IsAffine ((zariskiAffineLiftedEtaleSliceToScheme.{u, v, w, t} B S hS p hp x).obj Y) :=
  isAffine_zariskiAffineLiftedToScheme_obj.{u, v, w, t} B S hS p hp _

/-- The topology of the small étale site is flatly cofinal for its underlying scheme
functor. -/
theorem isFlatCofinal_zariskiAffineLiftedEtaleSlice :
    IsFlatCofinal (zariskiAffineLiftedEtaleSliceToScheme.{u, v, w, t} B S hS p hp x)
      (zariskiAffineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).J :=
  Stacks.EtaleSlice.isFlatCofinal x
    (isEtaleCofinal_zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp)

/-- The restriction maps of the structure sheaf of the small étale site are flat. -/
theorem flat_zariskiAffineLiftedEtaleSlice_map
    ⦃U V : (zariskiAffineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).C⦄ (f : U ⟶ V) :
    ((zariskiAffineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).O.obj.map f.op).hom.Flat := by
  exact flat_ringSheaf_map_of_ringTransport.{u, max v w t}
    (zariskiAffineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x)
    (zariskiAffineLiftedEtaleSliceToScheme.{u, v, w, t} B S hS p hp x)
    (zariskiAffineLiftedEtaleSliceRingTransport.{u, v, w, t} B S hS p hp x)
    (fun g => by have := etale_toScheme_map g; infer_instance) f.op

/-- The structure sheaf of the small étale site carries fibre products to pushouts. -/
theorem isPushout_zariskiAffineLiftedEtaleSlice_map
    ⦃A B' D : (zariskiAffineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).C⦄
    (f : A ⟶ D) (h : B' ⟶ D) :
    IsPushout ((zariskiAffineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).O.obj.map f.op)
      ((zariskiAffineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).O.obj.map h.op)
      ((zariskiAffineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).O.obj.map
        (pullback.fst f h).op)
      ((zariskiAffineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).O.obj.map
        (pullback.snd f h).op) := by
  have hpb := Functor.map_isPullback
    (zariskiAffineLiftedEtaleSliceToScheme.{u, v, w, t} B S hS p hp x)
    (IsPullback.of_hasPullback f h)
  have h₂ := isPushout_appTop_of_isPullback hpb
  exact CommRingCat.isPushout_ulift.{u, max v w t} h₂

end EtaleSlice

/-! ### Descent of the cartesian condition along a finite étale covering -/

section Descent

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance] AlgebraicGeometry.RingedSite.Hom.pushforwardTopos_additive

/-- A cartesian presheaf of modules on a slice of the small étale site of an object of the
lifted Zariski affine site is a sheaf. -/
theorem isSheaf_of_isCartesianPresheaf_zariskiAffineLiftedEtaleSlice
    (x : (zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp).C)
    (U : (zariskiAffineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).C)
    (P : PresheafOfModules.{max v w u t}
      (Stacks.Sites.OverModules.overRingPresheaf
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (zariskiAffineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).O).obj U))
    (hP : IsCartesianPresheaf P) :
    Presheaf.IsSheaf ((zariskiAffineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).J.over U)
      P.presheaf := by
  have : HasPullbacks ((zariskiAffineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).over U).C :=
    (inferInstance : HasPullbacks (Over U))
  have : PreservesLimitsOfShape WalkingCospan
      (Over.forget U ⋙ zariskiAffineLiftedEtaleSliceToScheme.{u, v, w, t} B S hS p hp x) :=
    comp_preservesLimitsOfShape _ _
  have : ∀ Y, IsAffine ((Over.forget U ⋙
      zariskiAffineLiftedEtaleSliceToScheme.{u, v, w, t} B S hS p hp x).obj Y) :=
    fun Y => isAffine_zariskiAffineLiftedToScheme_obj.{u, v, w, t} B S hS p hp _
  exact isSheaf_of_isCartesianPresheaf_of_ringTransport.{u, max v w t}
    ((zariskiAffineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).over U)
    (Over.forget U ⋙ zariskiAffineLiftedEtaleSliceToScheme.{u, v, w, t} B S hS p hp x)
    ((isFlatCofinal_zariskiAffineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).over U)
    (Stacks.UniverseLift.uliftRingTransport.{max v w t}
      (rings (Over.forget U ⋙ zariskiAffineLiftedEtaleSliceToScheme.{u, v, w, t} B S hS p hp x)))
    P hP

/-- The higher right derived functors of evaluation vanish on a cartesian sheaf of modules on the
small étale site of an object of the lifted Zariski affine site. -/
theorem isZero_rightDerived_evaluation_zariskiAffineLiftedEtaleSlice
    (x : (zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp).C)
    (G : SheafOfModules.{max v w u t} (Stacks.SheafOfModules.Tensor.ringSheaf
      (zariskiAffineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).O))
    (hG : IsCartesianPresheaf G.val)
    (U : (zariskiAffineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).C) (n : ℕ) (hn : 0 < n) :
    IsZero (((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf
      (zariskiAffineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x).O) (op U)).rightDerived n).obj
        G) := by
  exact isZero_rightDerived_evaluation_of_ringTransport.{u, max v w t}
    (zariskiAffineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x)
    (zariskiAffineLiftedEtaleSliceToScheme.{u, v, w, t} B S hS p hp x)
    (isFlatCofinal_zariskiAffineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x)
    (zariskiAffineLiftedEtaleSliceRingTransport.{u, v, w, t} B S hS p hp x) G hG U n hn

/-- **The cartesian condition descends along a finite covering of an object of the lifted
Zariski affine site lying over étale morphisms.** Let `π i : x_i ⟶ x` be a finite family of
morphisms of `X↑` lying over étale morphisms of affine schemes and generating a covering sieve,
and let `L` be an object of `D(O_{X↑})` such that the comparison map of `Rε_*L` is invertible
along every morphism whose target maps to some `x_i`. Then the comparison map of `Rε_*L` along
each `π i` is invertible. -/
theorem isIso_comparison_of_zariskiEtaleCover
    (x : (zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp).C)
    {I : Type*} [Finite I] (obj : I → (zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp).C)
    (π : ∀ i, obj i ⟶ x)
    (hπ : Sieve.ofArrows obj π ∈ (zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp).J x)
    (het : ∀ i, Etale ((zariskiAffineLiftedToScheme.{u, v, w, t} B S hS p hp).map (π i)))
    (L : DerivedCategory (SheafOfModules.{max v w u t}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp).O))) :
    letI := Stacks.ModulesOnACategory.TildePullback.commSections_ringSheaf
      (zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp)
    ∀ (_ : ∀ ⦃z z' : (zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp).C⦄ (a : z ⟶ z') (i : I),
      Nonempty (z' ⟶ obj i) →
        IsIso (comparison.{max v w u t} (baseChangeDataOfComm.{max v w u t, max v w u t,
          max v w u t, max v w u t} (Stacks.SheafOfModules.Tensor.ringSheaf
            (zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp).O).obj
          Stacks.TerminalBaseChange.CommSections.mul_comm) a.op
          ((derivedEpsilonPushforward.{max v w u t}
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp).O)).obj L)))
    (i : I),
    IsIso (comparison.{max v w u t} (baseChangeDataOfComm.{max v w u t, max v w u t,
      max v w u t, max v w u t} (Stacks.SheafOfModules.Tensor.ringSheaf
        (zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp).O).obj
      Stacks.TerminalBaseChange.CommSections.mul_comm) (π i).op
      ((derivedEpsilonPushforward.{max v w u t}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp).O)).obj L)) := by
  intro hL i
  let X := zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp
  let Lx := zariskiAffineLiftedToScheme.{u, v, w, t} B S hS p hp
  let Sm := zariskiAffineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x
  let g := zariskiAffineLiftedEtaleSliceHom.{u, v, w, t} B S hS p hp x
  have : HasPullbacks Sm.C :=
    zariskiAffineLiftedEtaleSlice_hasPullbacks.{u, v, w, t} B S hS p hp x
  have : g.u.IsCocontinuous Sm.J (X.over x).J :=
    zariskiAffineLiftedEtaleSlice_isCocontinuous.{u, v, w, t} B S hS p hp x
  let ts : I → Sm.C := fun i => ⟨Over.mk (π i ≫ (Over.mk (𝟙 x)).hom), by
    show Etale (Lx.map (π i ≫ 𝟙 x))
    rw [Category.comp_id]
    exact het i⟩
  let q : ∀ i, ts i ⟶ terminal Lx x := fun i => ObjectProperty.homMk (Over.homMk (π i))
  have hcov : Sieve.ofArrows ts q ∈ Sm.J (terminal Lx x) := by
    refine ofArrows_mem_topology x
      (isEtaleCofinal_zariskiAffineLiftedSite.{u, v, w, t} B S hS p hp) ts q ?_
    rw [GrothendieckTopology.mem_over_iff]
    refine X.J.superset_covering ?_ hπ
    rw [Sieve.generate_le_iff]
    rintro _ _ ⟨i⟩
    rw [Sieve.overEquiv_iff]
    exact Sieve.ofArrows_mk _ _ i
  have key := Stacks.Cohomology.SubsiteComparisonDescent.isIso_comparison_map_of_cover g
    (baseChangeDataOver X x) (isTerminal Lx x) ts q hcov
    (flat_zariskiAffineLiftedEtaleSlice_map.{u, v, w, t} B S hS p hp x)
    (isPushout_zariskiAffineLiftedEtaleSlice_map.{u, v, w, t} B S hS p hp x)
    (fun i => isSheaf_of_isCartesianPresheaf_zariskiAffineLiftedEtaleSlice.{u, v, w, t}
      B S hS p hp x (ts i))
    (isZero_rightDerived_evaluation_zariskiAffineLiftedEtaleSlice.{u, v, w, t} B S hS p hp x)
    ((sheafRestriction.{max v w u t} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      x).mapDerivedCategory.obj L)
    (fun i A B b s => (isIso_comparison_restriction_iff X x L (g.u.map b).op).2
      (hL (g.u.map b).left i ⟨(g.u.map s).left⟩)) (q i)
  exact (isIso_comparison_restriction_iff X x L (g.u.map (q i)).op).1 key

end Descent

end AlgebraicGeometry.Stack
