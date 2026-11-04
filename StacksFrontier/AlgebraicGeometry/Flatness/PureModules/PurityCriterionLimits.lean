module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.RelativeAssassinTwo.BaseChange
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.ProjectiveSectionsAlongFibre
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.LocallyProjectivePurity
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.PurityCriterion
public import StacksFrontier.AlgebraicGeometry.Flatness.RelativelyPure.ProperSupport
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeAssassin.ContainmentConstructible
public import StacksFrontier.AlgebraicGeometry.Morphisms.ConstructibleAssociatedPointsLocusSpreadOut
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Constructible
public import StacksFrontier.AlgebraicGeometry.Properties.AmpleAndExtension.LocallyProjectiveCover

/-!
# Openness of the purity locus

Let `f : X ⟶ S` be a morphism of finite presentation and let `ℱ` be a quasi-coherent
`𝒪_X`-module of finite presentation which is flat over `S`. The set of points `s ∈ S` at which
`ℱ` is pure along the fibre `X_s` is open.

## Main results

* `AlgebraicGeometry.isOpen_setOf_isPureAlong` is Tag 05MC.

## Implementation notes

The local constructibility of the fibrewise containment locus, Tag 05KR, is supplied by
`Stacks.RelativeAssassin.isLocallyConstructible_fibrewiseContainment`, which this library proves
outright; it is instantiated at the base change of `f` along the elementary étale
neighbourhood, at the pullback of `ℱ`, and at the quasi-compact open subscheme that is the image
of the pointed projective cover.

The argument of the source applies the purity criterion of Tag 05L4 twice: once over `S` at the
given point, through the elementary étale neighbourhood of Tag 05KW, and once over the
neighbourhood `S'` at each nearby point of `S'`. The second application uses the trivial
elementary étale neighbourhood of `(S', t)`, whose base change is compared with `X ×_S S'`
through the isomorphism `X ×_S S' ×_{S'} S' ≅ X ×_S S'`; purity is then carried back from `S'`
to `S` by the flat descent of Tag 05J9, and the image in `S` of an open subset of `S'` is open
because `S' ⟶ S` is étale.

## References

* [Stacks Project, Tag 05MC](https://stacks.math.columbia.edu/tag/05MC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- An isomorphism of schemes is injective on points. -/
private theorem injective_of_isIso_scheme {A B : Scheme.{u}} (h : A ⟶ B) [IsIso h] :
    Function.Injective ⇑h := by
  intro a b hab
  have h1 : (h ≫ inv h) a = (h ≫ inv h) b := by
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hab]
  simpa using h1

/-- The morphism to `X ×_S B` induced by a commutative square whose horizontal arrows `X' ⟶ X`
and `B ⟶ S` are étale is itself étale. -/
public theorem etale_pullback_lift_of_etale {X S X' B : Scheme.{u}} (f : X ⟶ S) (pi : B ⟶ S)
    [Etale pi] (g : X' ⟶ X) [Etale g] (p : X' ⟶ B) (hsq : g ≫ f = p ≫ pi) :
    Etale (pullback.lift g p hsq) := by
  have hc2 : 𝟙 X' ≫ g = pullback.lift g p hsq ≫ pullback.fst f pi := by
    rw [Category.id_comp, pullback.lift_fst]
  have hfst : pullback.lift (𝟙 X') (pullback.lift g p hsq) hc2 ≫
      pullback.fst g (pullback.fst f pi) = 𝟙 X' := pullback.lift_fst _ _ _
  have hsnd : pullback.lift (𝟙 X') (pullback.lift g p hsq) hc2 ≫
      pullback.snd g (pullback.fst f pi) = pullback.lift g p hsq := pullback.lift_snd _ _ _
  have hoi : IsOpenImmersion (pullback.lift (𝟙 X') (pullback.lift g p hsq) hc2) := by
    have he : Etale (pullback.lift (𝟙 X') (pullback.lift g p hsq) hc2 ≫
        pullback.fst g (pullback.fst f pi)) := by
      rw [hfst]
      infer_instance
    have : Etale (pullback.lift (𝟙 X') (pullback.lift g p hsq) hc2) :=
      Etale.of_comp _ (pullback.fst g (pullback.fst f pi))
    have : Mono (pullback.lift (𝟙 X') (pullback.lift g p hsq) hc2) := mono_of_mono_fac hfst
    exact IsOpenImmersion.of_flat_of_mono _
  rw [← hsnd]
  infer_instance

/-- The pullback of a finitely presented quasi-coherent module along a morphism of schemes is
again of finite type, quasi-coherent and finitely presented. -/
private theorem pullback_isFiniteType_isQuasicoherent_isFinitePresentation
    {A B : Scheme.{u}} (h : A ⟶ B) (G : B.Modules) [G.IsFiniteType] [G.IsQuasicoherent]
    [G.IsFinitePresentation] :
    ((Scheme.Modules.pullback h).obj G).IsFiniteType ∧
      ((Scheme.Modules.pullback h).obj G).IsQuasicoherent ∧
      ((Scheme.Modules.pullback h).obj G).IsFinitePresentation :=
  ⟨SheafOfModules.pullback_isFiniteType h.toLRSHom.toShHom G,
    Stacks.Modules.isQuasicoherent_pullback h G inferInstance,
    Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_pullback h G⟩

/-- The purity criterion for the trivial elementary étale neighbourhood: if `l : Y ⟶ Z` is étale
over `B`, the module `G` is flat over `B` everywhere, `l^*G` is pure along `Y_t`, and every point
of the relative assassin of `G` lying over a generalization of `t` is in the image of `l`, then
`G` is pure along `Z_t`. -/
private theorem isPureAlong_of_forall_specializes_mem_range
    {B Z Y : Scheme.{u}} (q : Z ⟶ B) [LocallyOfFiniteType q] [QuasiCompact q]
    (G : Z.Modules) [G.IsFiniteType] [G.IsQuasicoherent]
    (p : Y ⟶ B) [LocallyOfFiniteType p] [QuasiCompact p]
    (l : Y ⟶ Z) [Etale l] (hl : l ≫ q = p)
    (hflat : ∀ z : Z, IsFlatOverAt q.toLRSHom.toShHom G z)
    (t : B)
    (hpure : IsPureAlong ({ S := B, X := Y, f := p,
                            F := (Scheme.Modules.pullback l).obj G,
                            s := t } : PrePureSituation.{u}))
    (hsub : ∀ z : Z, z ∈ Stacks.Divisors.relativeAssassin q G → q z ⤳ t →
      z ∈ Set.range ⇑l) :
    IsPureAlong ({ S := B, X := Z, f := q, F := G, s := t } : PrePureSituation.{u}) := by
  classical
  let Nt : EtaleNeighborhood B t :=
    { scheme := B, point := t, toBase := 𝟙 B, map_point := by simp }
  have hNt : Nt.IsElementary := by
    rw [EtaleNeighborhood.isElementary_iff]
    show IsIso (Scheme.Hom.residueFieldMap (𝟙 B) t)
    rw [Scheme.residueFieldMap_id]
    exact IsIso.id _
  have hcomm : l ≫ q = p ≫ Nt.toBase := hl.trans (Category.comp_id p).symm
  have hiso : IsIso (pullback.fst q Nt.toBase) :=
    pullback_fst_iso_of_right_iso q (𝟙 B)
  have hLfst : pullback.lift l p hcomm ≫ pullback.fst q Nt.toBase = l := pullback.lift_fst _ _ _
  have hqx (x : (pullback q Nt.toBase : Scheme.{u})) :
      q (pullback.fst q Nt.toBase x) = pullback.snd q Nt.toBase x :=
    (congrArg (fun m : (pullback q Nt.toBase : Scheme.{u}) ⟶ B => m x)
      (pullback.condition : pullback.fst q Nt.toBase ≫ q = pullback.snd q Nt.toBase ≫ 𝟙 B) :)
  have key : ∀ x : (pullback q Nt.toBase : Scheme.{u}),
      x ∈ Stacks.Divisors.relativeAssassin (pullback.snd q Nt.toBase)
          ((Scheme.Modules.pullback (pullback.fst q Nt.toBase)).obj G) →
        pullback.snd q Nt.toBase x ⤳ t →
        x ∈ Set.range ⇑(pullback.lift l p hcomm) := by
    intro x hx hspec
    obtain ⟨y, hy⟩ := hsub _ (relativeAssassin_pullback_subset_preimage q Nt.toBase G hx)
      (by rwa [hqx x])
    refine ⟨y, injective_of_isIso_scheme (pullback.fst q Nt.toBase) ?_⟩
    rw [← Scheme.Hom.comp_apply, hLfst, hy]
  have hcov : ∀ z : (pullback.snd q Nt.toBase).fiber Nt.point,
      z ∈ Stacks.Divisors.associatedPoints
        ((Scheme.Modules.pullback ((pullback.snd q Nt.toBase).fiberι Nt.point)).obj
          ((Scheme.Modules.pullback (pullback.fst q Nt.toBase)).obj G)) →
      ∃ y : Y, pullback.lift l p hcomm y = (pullback.snd q Nt.toBase).fiberι Nt.point z := by
    intro z hz
    have hmem := (Stacks.Divisors.mem_associatedPoints_fiber_iff_mem_relativeAssassin
      (pullback.snd q Nt.toBase) _ Nt.point z).mp hz
    have hspec : (pullback.snd q Nt.toBase)
        ((pullback.snd q Nt.toBase).fiberι Nt.point z) ⤳ t := by
      rw [Scheme.Hom.apply_fiberι]
    exact key _ hmem hspec
  exact (isPureAlong_iff_relativeAssassin_specializing_mem_range q G t Nt hNt p l hcomm
    (fun x => hflat _) hpure hcov).mpr key

/-- **Stacks Project, Tag 05MC.** For a morphism `f : X ⟶ S` of finite presentation and a
quasi-coherent `𝒪_X`-module `ℱ` of finite presentation which is flat over `S`, the set of points
`s ∈ S` at which `ℱ` is pure along the fibre `X_s` is open in `S`.

The local constructibility of the fibrewise containment locus, Tag 05KR, which the argument
applies to the base change of `f`, is proved outright in this library. -/
@[stacks 05MC "using Stacks 05KR, proved outright in this library"]
public theorem isOpen_setOf_isPureAlong
    {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation] [F.IsFiniteType]
    (hflat : ∀ x : X, IsFlatOverAt f.toLRSHom.toShHom F x) :
    IsOpen {s : S | IsPureAlong ({ S := S, X := X, f := f, F := F,
                                   s := s } : PrePureSituation.{u})} := by
  classical
  have hconstructible : ∀ {Z B : Scheme.{u}} (r : Z ⟶ B), FinitePresentation r →
      ∀ (G : Z.Modules), G.IsQuasicoherent → G.IsFinitePresentation →
      ∀ V : Z.Opens, QuasiCompact (V.ι ≫ r) →
        IsLocallyConstructible {y : B | Stacks.Divisors.associatedPoints
          ((Scheme.Modules.pullback (r.fiberι y)).obj G) ⊆ r.fiberι y ⁻¹' (V : Set ↥Z)} := by
    intro Z B r hr G hGqc hGfp V hVqc
    exact Stacks.RelativeAssassin.isLocallyConstructible_fibrewiseContainment r hr G V
  have hID : ExistsElementaryEtaleNeighborhoodProjectiveSections.{u} := by
    intro X S f _ F _ _ x hfl
    exact exists_elementaryEtaleNeighborhood_projective_sections_of_isFlatOverAt f F x hfl
  rw [isOpen_iff_mem_nhds]
  intro s hs
  obtain ⟨N, hNelem, hNaff, X', hX'aff, p, g, hgEt, hcomm, hcover, hproj⟩ :=
    exists_elementary_pointed_projective_cover hID f F s
      ⟨inferInstance, inferInstance, inferInstance⟩ (fun x => hflat _)
  have hsq : g ≫ f = p ≫ N.toBase := hcomm.symm
  have hFqc : F.IsQuasicoherent := inferInstance
  have : Etale g := hgEt
  have : IsAffine N.scheme := hNaff
  have : IsAffine X' := hX'aff
  have : IsAffineHom p := isAffineHom_of_isAffine p
  have hlftc : LocallyOfFiniteType (p ≫ N.toBase) := by rw [hcomm]; infer_instance
  have : LocallyOfFiniteType p := locallyOfFiniteType_of_comp p N.toBase
  obtain ⟨hFgft, hFgqc, -⟩ := pullback_isFiniteType_isQuasicoherent_isFinitePresentation g F
  have hUPR : IsUniversallyPureRelative p ((Scheme.Modules.pullback g).obj F) := by
    refine isUniversallyPureRelative_of_pushforward_isLocallyProjective p _ ?_
    let : Module Γ(N.scheme, ⊤) Γ((Scheme.Modules.pullback g).obj F, ⊤) :=
      Module.compHom _ p.appTop.hom
    refine (isLocallyProjective_iff_exists_affineOpen_cover _).2
      ⟨PUnit.{u + 1}, fun _ => ⊤, IsOpenCover.mk (by simp), fun _ => isAffineOpen_top _,
        fun _ => ?_⟩
    exact hproj
  have hlEt : Etale (pullback.lift g p hsq) := etale_pullback_lift_of_etale f N.toBase g p hsq
  have hWopen : IsOpen (Set.range ⇑(pullback.lift g p hsq)) :=
    (pullback.lift g p hsq).isOpenMap.isOpen_range
  obtain ⟨hGft, hGqc, hGfp⟩ :=
    pullback_isFiniteType_isQuasicoherent_isFinitePresentation (pullback.fst f N.toBase) F
  have hflat' : ∀ z : (pullback f N.toBase : Scheme.{u}),
      IsFlatOverAt (pullback.snd f N.toBase).toLRSHom.toShHom
        ((Scheme.Modules.pullback (pullback.fst f N.toBase)).obj F) z :=
    fun z => @modulePullback_isFlatOverAt X S N.scheme (pullback f N.toBase) f N.toBase
      (pullback.fst f N.toBase) (pullback.snd f N.toBase)
      (IsPullback.of_hasPullback f N.toBase) F hFqc z (hflat _)
  have hliftfst : pullback.lift g p hsq ≫ pullback.fst f N.toBase = g := pullback.lift_fst _ _ _
  obtain ⟨hLft, hLqc, -⟩ := pullback_isFiniteType_isQuasicoherent_isFinitePresentation
    (pullback.lift g p hsq) ((Scheme.Modules.pullback (pullback.fst f N.toBase)).obj F)
  have hpureX' : ∀ t : N.scheme, IsPureAlong
      ({ S := N.scheme, X := X', f := p,
         F := (Scheme.Modules.pullback (pullback.lift g p hsq)).obj
           ((Scheme.Modules.pullback (pullback.fst f N.toBase)).obj F),
         s := t } : PrePureSituation.{u}) := by
    intro t
    have e : (Scheme.Modules.pullback (pullback.lift g p hsq)).obj
        ((Scheme.Modules.pullback (pullback.fst f N.toBase)).obj F) ≅
          (Scheme.Modules.pullback g).obj F :=
      ((Scheme.Modules.pullbackComp (pullback.lift g p hsq)
        (pullback.fst f N.toBase)).app F) ≪≫ eqToIso (by rw [hliftfst])
    have h2 := isUniversallyPureAlong_of_moduleIso p ((Scheme.Modules.pullback g).obj F)
      ((Scheme.Modules.pullback (pullback.lift g p hsq)).obj
        ((Scheme.Modules.pullback (pullback.fst f N.toBase)).obj F)) e.symm t (hUPR t)
    exact fun D _ _ => h2 D
  have hres : IsIso (N.toBase.residueFieldMap N.point) :=
    (EtaleNeighborhood.isElementary_iff N).mp hNelem
  have hbcf : IsIso (baseChangeFiberMap f N.toBase N.point) :=
    isIso_baseChangeFiberMap f N.toBase N.point
  have hcover' : ∀ x : f.fiber (N.toBase N.point), ∃ y : X',
      g y = f.fiberι (N.toBase N.point) x ∧ p y = N.point := by
    rw [N.map_point]; exact hcover
  have hcov0 : ∀ z : (pullback.snd f N.toBase).fiber N.point,
      z ∈ Stacks.Divisors.associatedPoints
        ((Scheme.Modules.pullback ((pullback.snd f N.toBase).fiberι N.point)).obj
          ((Scheme.Modules.pullback (pullback.fst f N.toBase)).obj F)) →
      ∃ y : X', pullback.lift g p hsq y =
        (pullback.snd f N.toBase).fiberι N.point z := by
    intro z _
    obtain ⟨y, hgy, hpy⟩ := hcover' (baseChangeFiberMap f N.toBase N.point z)
    refine ⟨y, ?_⟩
    have hqy : pullback.snd f N.toBase (pullback.lift g p hsq y) = N.point := by
      rw [← Scheme.Hom.comp_apply, pullback.lift_snd]; exact hpy
    have hmemy : pullback.lift g p hsq y ∈ (pullback.snd f N.toBase) ⁻¹' {N.point} := hqy
    have hzz : (pullback.snd f N.toBase).fiberι N.point
        (((pullback.snd f N.toBase).fiberHomeo N.point).symm ⟨_, hmemy⟩) =
          pullback.lift g p hsq y :=
      (pullback.snd f N.toBase).fiberι_fiberHomeo_symm _ _
    have hpr : pullback.fst f N.toBase (pullback.lift g p hsq y) = g y := by
      rw [← Scheme.Hom.comp_apply, hliftfst]
    have hz'img : f.fiberι (N.toBase N.point) (baseChangeFiberMap f N.toBase N.point
        (((pullback.snd f N.toBase).fiberHomeo N.point).symm ⟨_, hmemy⟩)) = g y := by
      rw [← Scheme.Hom.comp_apply, baseChangeFiberMap_comp_fiberι, Scheme.Hom.comp_apply,
        hzz, hpr]
    have heqbcf : baseChangeFiberMap f N.toBase N.point
        (((pullback.snd f N.toBase).fiberHomeo N.point).symm ⟨_, hmemy⟩) =
          baseChangeFiberMap f N.toBase N.point z :=
      (f.fiberι (N.toBase N.point)).isEmbedding.injective (hz'img.trans hgy)
    have hzeq : (((pullback.snd f N.toBase).fiberHomeo N.point).symm ⟨_, hmemy⟩) = z :=
      injective_of_isIso_scheme _ heqbcf
    rw [← hzz, hzeq]
  have hpureNg : IsPureAlong ({ S := N.scheme, X := X', f := p,
                                F := (Scheme.Modules.pullback g).obj F,
                                s := N.point } : PrePureSituation.{u}) :=
    fun D _ _ => hUPR N.point D
  have hrange := (isPureAlong_iff_relativeAssassin_specializing_mem_range f F s N hNelem p g hsq
    (fun x => hflat _) hpureNg hcov0).mp hs
  obtain ⟨W, hWdef⟩ : ∃ W : (pullback f N.toBase).Opens,
      (W : Set ↥(pullback f N.toBase)) = Set.range ⇑(pullback.lift g p hsq) :=
    ⟨⟨_, hWopen⟩, rfl⟩
  have hWcpt : IsCompact (W : Set ↥(pullback f N.toBase)) := by
    rw [hWdef]; exact isCompact_range (pullback.lift g p hsq).continuous
  have hqsp : QuasiSeparatedSpace (pullback f N.toBase : Scheme.{u}) :=
    (quasiSeparated_iff_quasiSeparatedSpace (pullback.snd f N.toBase)).mp inferInstance
  have hWqc : QuasiCompact W.ι := quasiCompact_opens_ι hWcpt
  have hE := hconstructible (pullback.snd f N.toBase)
    ⟨inferInstance, inferInstance, inferInstance⟩
    ((Scheme.Modules.pullback (pullback.fst f N.toBase)).obj F) hGqc hGfp W inferInstance
  have hsubE : {t : N.scheme | t ⤳ N.point} ⊆ {y : N.scheme |
      Stacks.Divisors.associatedPoints
        ((Scheme.Modules.pullback ((pullback.snd f N.toBase).fiberι y)).obj
          ((Scheme.Modules.pullback (pullback.fst f N.toBase)).obj F)) ⊆
        (pullback.snd f N.toBase).fiberι y ⁻¹' (W : Set ↥(pullback f N.toBase))} := by
    intro t ht z hz
    have hmem := (Stacks.Divisors.mem_associatedPoints_fiber_iff_mem_relativeAssassin
      (pullback.snd f N.toBase) _ t z).mp hz
    have hspec : (pullback.snd f N.toBase) ((pullback.snd f N.toBase).fiberι t z) ⤳ N.point := by
      rw [Scheme.Hom.apply_fiberι]; exact ht
    show (pullback.snd f N.toBase).fiberι t z ∈ (W : Set ↥(pullback f N.toBase))
    rw [hWdef]
    exact hrange _ hmem hspec
  have hEnhds := mem_nhds_of_isLocallyConstructible_of_specializes_subset hE hsubE
  obtain ⟨V, hVE, hVopen, hVmem⟩ := mem_nhds_iff.mp hEnhds
  refine mem_nhds_iff.mpr ⟨N.toBase '' V, ?_, N.toBase.isOpenMap V hVopen,
    ⟨N.point, hVmem, N.map_point⟩⟩
  rintro _ ⟨t, htV, rfl⟩
  have hpureZ : IsPureAlong ({ S := N.scheme, X := pullback f N.toBase,
                               f := pullback.snd f N.toBase,
                               F := (Scheme.Modules.pullback (pullback.fst f N.toBase)).obj F,
                               s := t } : PrePureSituation.{u}) := by
    refine isPureAlong_of_forall_specializes_mem_range (pullback.snd f N.toBase) _ p
      (pullback.lift g p hsq) (pullback.lift_snd _ _ _) hflat' t (hpureX' t) ?_
    intro z hzass hzspec
    have htz : (pullback.snd f N.toBase) z ∈ V := hzspec.mem_open hVopen htV
    obtain ⟨t₀, z₀, hz₀, hz₀eq⟩ :=
      (Stacks.Divisors.mem_relativeAssassin (pullback.snd f N.toBase) _ z).mp hzass
    have ht₀ : t₀ = (pullback.snd f N.toBase) z := by
      rw [← hz₀eq, Scheme.Hom.apply_fiberι]
    subst ht₀
    have hmemW : z ∈ (W : Set ↥(pullback f N.toBase)) := hz₀eq ▸ hVE htz hz₀
    rwa [hWdef] at hmemW
  have hflatpi : IsFlatAt N.toBase.toLRSHom.toShHom t := by
    show (N.toBase.stalkMap t).hom.Flat
    exact Flat.stalkMap N.toBase t
  exact isPureAlong_of_flatPointedBaseChange
    { X := X, S := S, f := f, F := F, s := N.toBase t, S' := N.scheme, s' := t,
      g := N.toBase, mapsTo := rfl, flatAt := hflatpi }
    ({ S := N.scheme, X := pullback f N.toBase, f := pullback.snd f N.toBase,
       F := (Scheme.Modules.pullback (pullback.fst f N.toBase)).obj F,
       s := t } : PrePureSituation.{u}) rfl rfl (by simp) HEq.rfl rfl hpureZ

/-- **Stacks Project, Tag 05MA.** Let `(S_i)` be an inverse system of affine schemes over a
directed index with limit `S`, let `s ∈ S` with images `s_i`, let `f : X ⟶ S` be of finite
presentation and let `ℱ` be a quasi-coherent `𝒪_X`-module of finite presentation which is pure
along `X_s` and flat over `S` at every point of `X_s`. Then the whole situation descends to a
finite stage: some `i` carries a finite-presentation morphism `X_i ⟶ S_i` and a finitely
presented quasi-coherent module `ℱ_i` which is pure along `(X_i)_{s_i}` and flat over `S_i` at
every point of that fibre, with `X = X_i ×_{S_i} S` and `ℱ` the pullback of `ℱ_i`.

The descent of the morphism, the module, the open flat locus and the flatness, which is Stacks
Limits 01ZM, 01ZR, 01ZS and 05LY, is the hypothesis `hdescend`; the passage of purity to a
finite stage, which is the second half of the proof of the source and uses Stacks 05KW, 05K6,
05L4, 05KR and Limits 05F4, is the hypothesis `hstage`. -/
@[stacks 05MA "assuming the limit descent as hdescend and the purity step as hstage"]
public theorem exists_stage_isPureAlong_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i : I, IsAffine (D.obj i)] (c : Cone D) (_hc : IsLimit c)
    {X : Scheme.{u}} (f : X ⟶ c.pt)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation] [F.IsFiniteType] (s : c.pt)
    (_hpure : IsPureAlong ({ S := c.pt, X := X, f := f, F := F,
                             s := s } : PrePureSituation.{u}))
    (_hflat : ∀ x : f.fiber s, IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s x))
    (hdescend : ∃ (i : I) (Xi : Scheme.{u}) (fi : Xi ⟶ D.obj i)
      (_ : LocallyOfFinitePresentation fi) (_ : QuasiCompact fi) (_ : QuasiSeparated fi)
      (Fi : Xi.Modules) (_ : Fi.IsFiniteType) (_ : Fi.IsQuasicoherent)
      (_ : Fi.IsFinitePresentation) (a : X ⟶ Xi),
      IsPullback a f fi (c.π.app i) ∧ Nonempty (F ≅ (Scheme.Modules.pullback a).obj Fi) ∧
        ∀ x : fi.fiber (c.π.app i s),
          IsFlatOverAt fi.toLRSHom.toShHom Fi (fi.fiberι (c.π.app i s) x))
    (hstage : ∀ (i : I) (Xi : Scheme.{u}) (fi : Xi ⟶ D.obj i)
      (_ : LocallyOfFinitePresentation fi) (_ : QuasiCompact fi) (_ : QuasiSeparated fi)
      (Fi : Xi.Modules) (_ : Fi.IsFiniteType) (_ : Fi.IsQuasicoherent)
      (_ : Fi.IsFinitePresentation) (a : X ⟶ Xi), IsPullback a f fi (c.π.app i) →
      Nonempty (F ≅ (Scheme.Modules.pullback a).obj Fi) →
      (∀ x : fi.fiber (c.π.app i s),
        IsFlatOverAt fi.toLRSHom.toShHom Fi (fi.fiberι (c.π.app i s) x)) →
      ∃ (j : I) (e : j ⟶ i) (_ : LocallyOfFiniteType (pullback.snd fi (D.map e)))
        (_ : QuasiCompact (pullback.snd fi (D.map e)))
        (_ : ((Scheme.Modules.pullback (pullback.fst fi (D.map e))).obj Fi).IsFiniteType)
        (_ : ((Scheme.Modules.pullback (pullback.fst fi (D.map e))).obj Fi).IsQuasicoherent),
        IsPureAlong ({ S := D.obj j, X := pullback fi (D.map e),
                       f := pullback.snd fi (D.map e),
                       F := (Scheme.Modules.pullback (pullback.fst fi (D.map e))).obj Fi,
                       s := c.π.app j s } : PrePureSituation.{u})) :
    ∃ (i : I) (Xi : Scheme.{u}) (fi : Xi ⟶ D.obj i) (_ : LocallyOfFinitePresentation fi)
      (_ : QuasiCompact fi) (_ : QuasiSeparated fi) (Fi : Xi.Modules) (_ : Fi.IsFiniteType)
      (_ : Fi.IsQuasicoherent) (_ : Fi.IsFinitePresentation) (a : X ⟶ Xi),
      IsPullback a f fi (c.π.app i) ∧ Nonempty (F ≅ (Scheme.Modules.pullback a).obj Fi) ∧
        (∀ x : fi.fiber (c.π.app i s),
          IsFlatOverAt fi.toLRSHom.toShHom Fi (fi.fiberι (c.π.app i s) x)) ∧
        IsPureAlong ({ S := D.obj i, X := Xi, f := fi, F := Fi,
                       s := c.π.app i s } : PrePureSituation.{u}) := by
  classical
  obtain ⟨i, Xi, fi, hlfpi, hqci, hqsi, Fi, hFift, hFiqc, hFifp, a, hpb, hFe, hflati⟩ :=
    hdescend
  obtain ⟨j, e, _, _, _, _, hpurej⟩ :=
    hstage i Xi fi hlfpi hqci hqsi Fi hFift hFiqc hFifp a hpb hFe hflati
  obtain ⟨eF⟩ := hFe
  have hcw : c.π.app j ≫ D.map e = c.π.app i := c.w e
  have hcomm : a ≫ fi = (f ≫ c.π.app j) ≫ D.map e := by
    rw [Category.assoc, hcw]
    exact hpb.w
  have ha : pullback.lift a (f ≫ c.π.app j) hcomm ≫ pullback.fst fi (D.map e) = a :=
    pullback.lift_fst _ _ _
  have hb : pullback.lift a (f ≫ c.π.app j) hcomm ≫ pullback.snd fi (D.map e) =
      f ≫ c.π.app j := pullback.lift_snd _ _ _
  have hpbj : IsPullback (pullback.lift a (f ≫ c.π.app j) hcomm) f
      (pullback.snd fi (D.map e)) (c.π.app j) := by
    refine IsPullback.of_right (h₁₂ := pullback.fst fi (D.map e)) ?_ hb
      (IsPullback.of_hasPullback fi (D.map e))
    rwa [ha, hcw]
  obtain ⟨hFjft, hFjqc, hFjfp⟩ :=
    pullback_isFiniteType_isQuasicoherent_isFinitePresentation (pullback.fst fi (D.map e)) Fi
  refine ⟨j, pullback fi (D.map e), pullback.snd fi (D.map e), inferInstance, inferInstance,
    inferInstance, (Scheme.Modules.pullback (pullback.fst fi (D.map e))).obj Fi, hFjft, hFjqc,
    hFjfp, pullback.lift a (f ≫ c.π.app j) hcomm, hpbj, ⟨?_⟩, ?_, hpurej⟩
  · refine eF ≪≫ ?_
    refine (eqToIso (by rw [ha]) : (Scheme.Modules.pullback a).obj Fi ≅
      (Scheme.Modules.pullback (pullback.lift a (f ≫ c.π.app j) hcomm ≫
        pullback.fst fi (D.map e))).obj Fi) ≪≫ ?_
    exact ((Scheme.Modules.pullbackComp (pullback.lift a (f ≫ c.π.app j) hcomm)
      (pullback.fst fi (D.map e))).app Fi).symm
  · intro x
    have hz : fi (pullback.fst fi (D.map e)
        ((pullback.snd fi (D.map e)).fiberι (c.π.app j s) x)) = c.π.app i s := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply,
        Scheme.Hom.apply_fiberι, ← Scheme.Hom.comp_apply, hcw]
    have hflatpt := hflati ((fi.fiberHomeo (c.π.app i s)).symm ⟨_, hz⟩)
    rw [fi.fiberι_fiberHomeo_symm] at hflatpt
    exact @modulePullback_isFlatOverAt Xi (D.obj i) (D.obj j) (pullback fi (D.map e)) fi
      (D.map e) (pullback.fst fi (D.map e)) (pullback.snd fi (D.map e))
      (IsPullback.of_hasPullback fi (D.map e)) Fi hFiqc _ hflatpt

end AlgebraicGeometry

end
