module

public import StacksFrontier.AlgebraicGeometry.Limits.NoetherianValuativeCriterion.GenericProperness
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.ChartValuativeExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.SchemeImageSite
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianValuativeProper
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.RefinedValuativeSeparatedness
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.Valuative.PushDownSolution

/-!
# A refined Noetherian valuative criterion for properness of algebraic spaces

Let `f : X ⟶ Y` and `h : U ⟶ X` be morphisms of algebraic spaces over `S` with `Y` locally
Noetherian, `f` and `h` of finite type and the image of `|h| : |U| → |X|` dense in `|X|`.

* If `f` is separated and every valuative diagram for `f` over a discrete valuation ring whose
  generic arrow factors through `h` has a dotted arrow, then `f` is proper (Stacks 0CMD).
* If `f` is quasi-separated and every such diagram has exactly one dotted arrow, then `f` is
  proper (Stacks 0CMF).

## Main results

* `AlgebraicGeometry.Space.isProper_of_denseRange_of_exists_discreteLift`: **Stacks 0CMD**.
* `AlgebraicGeometry.Space.isProper_of_denseRange_of_unique_discreteLift`: **Stacks 0CMF**.

## Implementation notes

The argument for Stacks 0CMD is the one of the source, with one change at the end. Only
universal closedness is at issue, and by Stacks 03IT it may be tested on a family of étale charts
`Spec A ⟶ Y` covering `Y`, with `A` Noetherian
(`AlgebraicGeometry.Space.exists_spec_isLocallyNoetherian_etale_covering_family`). Over such a
chart the base change `X_A ⟶ Spec A` of `f` is separated and of finite type, so the weak Chow lemma
(Stacks 089J, `AlgebraicGeometry.Space.exists_chowSchemeCover_over_spec`) gives a proper
surjective morphism `p : X' ⟶ X_A` from a scheme `X'` of the site. The base change of `h` to the
quasi-compact scheme `X'` has a quasi-compact étale atlas `T`, and `T ⟶ X'` is quasi-compact and
locally of finite type; let `Z ⊆ X'` be its scheme-theoretic image. Then `T ⟶ Z` is dominant, and
the composite `Z ⟶ X' ⟶ X_A` is proper with closed image containing the preimage of the image of
`|h|`, which is dense because `X_A ⟶ X` is étale, hence open on points (Stacks 03IR), and points
of a fibre product are pairs of points (Stacks 03H4). So `Z ⟶ X_A` is surjective, and by
Stacks 08AJ it suffices that the morphism of schemes `Z ⟶ Spec A` be universally closed.

The source concludes with the scheme case, Stacks 0CM3. Here `Z ⟶ Spec A` is shown to be proper
directly by condition (4) of Stacks 0208
(`AlgebraicGeometry.isProper_of_genericDiscreteValuativeCriterion`), which only quantifies over
discrete valuation subrings `A'` of residue fields `κ(η)` at generic points `η` of `Z` — rings
whose spectra lie in the site. Uniqueness of the dotted arrow is separatedness. For existence, `η`
is the image of a point `x` of `T` (Stacks 01RL), and `A'` is dominated by a discrete valuation
ring `R' ⊆ κ(x)` with fraction field `κ(x)` (Stacks 00PH). Over `R'` the generic arrow factors
through `h`, so the hypothesis gives a dotted arrow to `X`, hence to `X_A`, and the valuative
criterion for the proper morphism `Z ⟶ X_A` (Stacks 0A40) lifts it to `Z`. That dotted arrow over
the dominating extension `R'` of `A'` descends to `A'` because `Z ⟶ Spec A` is separated
(Stacks 0ARH, `AlgebraicGeometry.Space.exists_lift_of_dominatingExtension`).

Stacks 0CMF combines Stacks 0CME
(`AlgebraicGeometry.Space.isSeparated_of_denseRange_of_subsingleton_discreteLift`) and
Stacks 0CMD, as in the source.

As throughout the chapter, density of the image of `|h|` is `DenseRange` of
`AlgebraicGeometry.Space.pointsMap` for the topology `AlgebraicGeometry.Space.pointTopology` of
Stacks 03BX, and the valuative diagrams are the `AlgebraicGeometry.Space.ValuativeSquare`s, whose
valuation ring and fraction field have spectra in the chosen big site.

## References

* [Stacks Project, Tag 0CMD](https://stacks.math.columbia.edu/tag/0CMD)
* [Stacks Project, Tag 0CMF](https://stacks.math.columbia.edu/tag/0CMF)
* [Stacks Project, Tag 0208](https://stacks.math.columbia.edu/tag/0208)
* [Stacks Project, Tag 0ARH](https://stacks.math.columbia.edu/tag/0ARH)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X Y U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A discrete valuation subring `A'` of a field `K` with fraction field `K` is dominated by a
discrete valuation subring of any essentially finite type extension `L` of `K`, with fraction
field `L` (Stacks 00PH). -/
private theorem exists_isDiscreteValuationRing_dominating {K L : Type u} [Field K] [Field L]
    (j : K →+* L) (hj : j.EssFiniteType) (A' : Subring K) [IsDiscreteValuationRing A']
    [IsFractionRing A' K] :
    ∃ (R' : Subring L) (_ : IsDiscreteValuationRing R') (_ : IsFractionRing R' L)
      (φA : A' →+* R'), IsLocalHom φA ∧ (algebraMap R' L).comp φA = j.comp (algebraMap A' K) := by
  let := j.toAlgebra
  have : Algebra.EssFiniteType K L := hj
  let : Algebra A' L := (j.comp (algebraMap A' K)).toAlgebra
  have : IsScalarTower A' K L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨Bs, hBdvr, hBfrac, hBloc⟩ :=
    _root_.exists_isDiscreteValuationRing_isFractionRing_of_not_isField (R := A') K (L := L)
      (IsDiscreteValuationRing.not_isField A')
  exact ⟨Bs.toSubring, hBdvr, hBfrac, algebraMap A' Bs, hBloc,
    RingHom.ext fun a ↦ (IsScalarTower.algebraMap_apply A' Bs L a).symm⟩

/-- A dotted arrow in a valuative square of a representable morphism whose edges are
representable comes from a morphism of the site. -/
private theorem exists_hom_of_nonempty_lift {Z T : BigFppfOver B S hS} {χ : Z ⟶ T}
    (q : ValuativeSquare (yoneda.map χ))
    {uK : siteObject B S hS q.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base) ⟶ Z}
    {uA : siteObject B S hS q.ring_mem q.base ⟶ T}
    (hg : q.generic = yoneda.map uK) (hs : q.special = yoneda.map uA) (hq : Nonempty q.Lift) :
    ∃ l, specializationArrow q ≫ l = uK ∧ l ≫ χ = uA := by
  obtain ⟨L⟩ := hq
  refine ⟨yoneda.preimage L.map, yoneda.map_injective ?_, yoneda.map_injective ?_⟩
  · rw [yoneda.map_comp, yoneda.map_preimage, ← hg]
    exact L.generic_comm
  · rw [yoneda.map_comp, yoneda.map_preimage, ← hs]
    exact L.special_comm

/-- Let `p' : Z ⟶ X ×_Y T` be proper over the separated `Z ⟶ T`. A valuative square for
`Z ⟶ T` has a dotted arrow as soon as some dominating extension over a discrete valuation ring
has generic arrow, pushed to `X`, factoring through `h`: the hypothesis gives a dotted arrow to
`X`, the valuative criterion for `p'` lifts it to `Z`, and it descends (Stacks 0ARH). -/
private theorem nonempty_lift_of_dominatingExtension_of_isProper
    {Z T : BigFppfOver B S hS} (hZ : IsAlgebraicSpace B S hS (yoneda.obj Z))
    (hT : IsAlgebraicSpace B S hS (yoneda.obj T)) (f : X ⟶ Y) (h : U ⟶ X)
    (φ : yoneda.obj T ⟶ Y) (hXT : IsAlgebraicSpace B S hS (pullback φ f))
    (χ : Z ⟶ T) (hχ : IsSeparated B S hS (yoneda.map χ))
    (p' : yoneda.obj Z ⟶ pullback φ f) (hp' : IsProper B S hS p')
    (hp'χ : p' ≫ pullback.fst φ f = yoneda.map χ)
    (hvaluative : ∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R →
      ∀ g : yoneda.obj (siteObject B S hS q.field_mem
          (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)) ⟶ U,
        g ≫ h = q.generic → Nonempty q.Lift)
    (qZ : ValuativeSquare (yoneda.map χ)) (e : qZ.DominatingExtension)
    (hR : IsDiscreteValuationRing e.square.R)
    (w : yoneda.obj (siteObject B S hS e.square.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap e.square.R e.square.K)) ≫ e.square.base)) ⟶ U)
    (hw : w ≫ h = e.square.generic ≫ p' ≫ pullback.snd φ f) :
    Nonempty qZ.Lift := by
  let qf : ValuativeSquare f :=
    { R := e.square.R, K := e.square.K, ring_mem := e.square.ring_mem,
      field_mem := e.square.field_mem, base := e.square.base
      generic := e.square.generic ≫ p' ≫ pullback.snd φ f
      special := e.square.special ≫ φ
      comm := by
        calc (e.square.generic ≫ p' ≫ pullback.snd φ f) ≫ f
            = (e.square.generic ≫ p' ≫ pullback.fst φ f) ≫ φ := by
              simp only [Category.assoc, pullback.condition]
          _ = _ := by rw [hp'χ, e.square.comm, Category.assoc] }
  obtain ⟨L⟩ := hvaluative qf hR w hw
  let c := pullback.lift e.square.special L.map L.special_comm.symm
  let qp : ValuativeSquare p' :=
    { R := e.square.R, K := e.square.K, ring_mem := e.square.ring_mem,
      field_mem := e.square.field_mem, base := e.square.base
      generic := e.square.generic
      special := c
      comm := by
        apply pullback.hom_ext
        · rw [Category.assoc, hp'χ, e.square.comm, Category.assoc]
          exact (congrArg _ (pullback.lift_fst _ _ _)).symm
        · simp only [c, Category.assoc, pullback.lift_snd]
          exact L.generic_comm.symm }
  obtain ⟨M⟩ := ((isProper_iff_forall_unique_lift_of_isFiniteType_of_isQuasiSeparated hZ hXT
    p' hp'.2.1 (isQuasiSeparated_of_isSeparated B S hS hp'.1)).mp hp' qp).1
  exact exists_lift_of_dominatingExtension hZ hT hχ qZ e
    ⟨{ map := M.map
       generic_comm := M.generic_comm
       special_comm := by
         calc M.map ≫ yoneda.map χ = (M.map ≫ p') ≫ pullback.fst φ f := by
               rw [Category.assoc, hp'χ]
           _ = c ≫ pullback.fst φ f := by rw [M.special_comm]
           _ = _ := pullback.lift_fst _ _ _ }⟩

/-- The existence and uniqueness of dotted arrows at the generic points of the scheme-theoretic
image `Z` of `T' ⟶ X'`, that is, condition (4) of Stacks 0208 for `Z ⟶ Spec A`. -/
private theorem genericDiscreteValuativeCriterion_schemeImageObjι_comp
    (A : CommRingCat.{u}) (hA : B.Contains (Spec A)) (a : Spec A ⟶ S)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hU : IsAlgebraicSpace B S hS U) (f : X ⟶ Y) (h : U ⟶ X)
    (φ : yoneda.obj (siteObject B S hS hA a) ⟶ Y)
    {X' T' : BigFppfOver B S hS} (ψ : X' ⟶ siteObject B S hS hA a)
    (p : yoneda.obj X' ⟶ pullback φ f) (hp : IsProper B S hS p)
    (hpψ : p ≫ pullback.fst φ f = yoneda.map ψ)
    (t : yoneda.obj T' ⟶ pullback (p ≫ pullback.snd φ f) h) (τ₀ : T' ⟶ X')
    (hτ₀ : yoneda.map τ₀ = t ≫ pullback.fst (p ≫ pullback.snd φ f) h)
    (hvaluative : ∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R →
      ∀ g : yoneda.obj (siteObject B S hS q.field_mem
          (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)) ⟶ U,
        g ≫ h = q.generic → Nonempty q.Lift)
    [LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map τ₀)]
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map τ₀)]
    [_root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map ψ)] :
    GenericDiscreteValuativeCriterion
      ((BigFppfOver.toScheme B S hS).map (schemeImageObjι B S hS τ₀ ≫ ψ)) := by
  classical
  set G := BigFppfOver.toScheme B S hS
  let Tobj := siteObject B S hS hA a
  let g : yoneda.obj X' ⟶ X := p ≫ pullback.snd φ f
  have hT : IsAlgebraicSpace B S hS (yoneda.obj Tobj) := isAlgebraicSpace_yoneda B S hS _
  have hXT : IsAlgebraicSpace B S hS (pullback φ f) :=
    isAlgebraicSpace_pullback B S hS φ f hT hX hY
  have hX' : IsAlgebraicSpace B S hS (yoneda.obj X') := isAlgebraicSpace_yoneda B S hS X'
  let Zobj := schemeImageObj B S hS τ₀
  let ι : Zobj ⟶ X' := schemeImageObjι B S hS τ₀
  let τZ : T' ⟶ Zobj := toSchemeImageObj B S hS τ₀
  have hτZι : τZ ≫ ι = τ₀ := toSchemeImageObj_comp_schemeImageObjι B S hS τ₀
  have hιCI : _root_.AlgebraicGeometry.IsClosedImmersion (G.map ι) :=
    isClosedImmersion_schemeImageObjι B S hS τ₀
  have hZ : IsAlgebraicSpace B S hS (yoneda.obj Zobj) := isAlgebraicSpace_yoneda B S hS Zobj
  let p' : yoneda.obj Zobj ⟶ pullback φ f := yoneda.map ι ≫ p
  have hp'ψ : p' ≫ pullback.fst φ f = yoneda.map (ι ≫ ψ) := by
    simp only [p', Category.assoc, hpψ, yoneda.map_comp]
  have hp' : IsProper B S hS p' :=
    isProper_comp' B S hS (yoneda.map ι) p hX' hXT
      (isProper_yoneda_map B S hS ι inferInstance) hp
  have hτZdom : _root_.AlgebraicGeometry.IsDominant (G.map τZ) := by
    show _root_.AlgebraicGeometry.IsDominant (G.map τ₀).toImage
    infer_instance
  have hτZQC : QuasiCompact (G.map τZ) := by
    show QuasiCompact (G.map τ₀).toImage
    infer_instance
  have hτZLFT : LocallyOfFiniteType (G.map τZ) := by
    have : LocallyOfFiniteType (G.map τZ ≫ G.map ι) := by
      rw [← G.map_comp, hτZι]
      infer_instance
    exact locallyOfFiniteType_of_comp (G.map τZ) (G.map ι)
  have hχSep : _root_.AlgebraicGeometry.IsSeparated (G.map (ι ≫ ψ)) := by
    rw [G.map_comp]
    infer_instance
  intro η hη A' hA' hA'K i₂ sq
  refine ⟨?_, ?_⟩
  swap
  · -- uniqueness: `Z ⟶ Spec A` is separated
    exact _root_.AlgebraicGeometry.IsSeparated.valuativeCriterion (f := G.map (ι ≫ ψ))
      { R := A', K := (G.obj Zobj).residueField η, i₁ := (G.obj Zobj).fromSpecResidueField η,
        i₂ := i₂, commSq := sq }
  -- existence: `η` is the image of a point `x` of `T'`
  obtain ⟨x, hx⟩ := (isDominant_iff_genericPoints_subset_range (G.map τZ)).1 hτZdom hη
  have hT'hom : B.inclusion.map T'.hom = G.map (τZ ≫ ι ≫ ψ) ≫ B.inclusion.map Tobj.hom := by
    conv_lhs => rw [← Over.w (τZ ≫ ι ≫ ψ)]
    exact B.inclusion.map_comp _ _
  have hZhom : B.inclusion.map Zobj.hom = G.map (ι ≫ ψ) ≫ B.inclusion.map Tobj.hom := by
    conv_lhs => rw [← Over.w (ι ≫ ψ)]
    exact B.inclusion.map_comp _ _
  generalize hF : G.map τZ = F at hx hτZLFT
  subst hx
  have hFτ : (G.obj T').fromSpecResidueField x ≫ G.map τZ =
      Spec.map (F.residueFieldMap x) ≫ (G.obj Zobj).fromSpecResidueField (F x) := by
    rw [hF]
    exact (F.SpecMap_residueFieldMap_fromSpecResidueField x).symm
  -- a discrete valuation ring of `κ(x)` dominating `A'`
  obtain ⟨R', _, _, φA, hφA, hring⟩ := exists_isDiscreteValuationRing_dominating
    (F.residueFieldMap x).hom
    (RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap (f := F) x)) A'
  -- the spectra occurring lie in the site
  have hKη : B.Contains (Spec (.of ((G.obj Zobj).residueField (F x)))) :=
    B.residueField_spec_contains Zobj.left.property (F x)
  have hA'mem : B.Contains (Spec (.of (A' : Type u))) :=
    Scheme.size_Spec_lt_of_subring B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit A' hKη
  have hKx : B.Contains (Spec (.of ((G.obj T').residueField x))) :=
    B.residueField_spec_contains T'.left.property x
  have hR'mem : B.Contains (Spec (.of (R' : Type u))) :=
    Scheme.size_Spec_lt_of_subring B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit R' hKx
  -- the valuative square of `Z ⟶ Spec A` as one of algebraic spaces
  let base : Spec (.of (A' : Type u)) ⟶ S := i₂ ≫ B.inclusion.map Tobj.hom
  let uA : siteObject B S hS hA'mem base ⟶ Tobj :=
    Over.homMk (ObjectProperty.homMk i₂ : B.obj hA'mem ⟶ Tobj.left) (by
      apply ObjectProperty.hom_ext
      rfl)
  let uK : siteObject B S hS hKη
      (Spec.map (CommRingCat.ofHom (algebraMap A' ((G.obj Zobj).residueField (F x)))) ≫ base) ⟶
      Zobj :=
    Over.homMk (ObjectProperty.homMk ((G.obj Zobj).fromSpecResidueField (F x)) :
      B.obj hKη ⟶ Zobj.left) (by
      apply ObjectProperty.hom_ext
      show (G.obj Zobj).fromSpecResidueField (F x) ≫ B.inclusion.map Zobj.hom =
        Spec.map (CommRingCat.ofHom (algebraMap A' ((G.obj Zobj).residueField (F x)))) ≫
          i₂ ≫ B.inclusion.map Tobj.hom
      rw [hZhom, ← Category.assoc, sq.w, Category.assoc]
      rfl)
  let qZ : ValuativeSquare (yoneda.map (ι ≫ ψ)) :=
    { R := A', K := (G.obj Zobj).residueField (F x), ring_mem := hA'mem, field_mem := hKη,
      base := base, generic := yoneda.map uK, special := yoneda.map uA
      comm := by
        rw [← yoneda.map_comp, ← yoneda.map_comp]
        congr 1
        exact BigFppfOver.map_toScheme_injective B S hS sq.w }
  -- its dominating extension over `R' ⊆ κ(x)`
  let e := dominatingExtensionOfRingHom qZ (A := (R' : Type u)) (L := (G.obj T').residueField x)
    hR'mem hKx φA (F.residueFieldMap x).hom hφA hring
  have hspec : Spec.map (F.residueFieldMap x) ≫ Spec.map (CommRingCat.ofHom A'.subtype) =
      Spec.map (CommRingCat.ofHom (algebraMap R' ((G.obj T').residueField x))) ≫
        Spec.map (CommRingCat.ofHom φA) := by
    have hc : CommRingCat.ofHom A'.subtype ≫ F.residueFieldMap x =
        CommRingCat.ofHom φA ≫ CommRingCat.ofHom (algebraMap R' ((G.obj T').residueField x)) :=
      CommRingCat.hom_ext hring.symm
    have := congrArg Spec.map hc
    rw [Spec.map_comp, Spec.map_comp] at this
    exact this
  have hw : (G.obj T').fromSpecResidueField x ≫ G.map τZ ≫ G.map (ι ≫ ψ) =
      Spec.map (CommRingCat.ofHom (algebraMap R' ((G.obj T').residueField x))) ≫
        Spec.map (CommRingCat.ofHom φA) ≫ i₂ := by
    rw [← Category.assoc, hFτ, Category.assoc, sq.w, ← Category.assoc, hspec, Category.assoc]
  let uKx : siteObject B S hS e.square.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap e.square.R e.square.K)) ≫ e.square.base) ⟶ T' :=
    Over.homMk (ObjectProperty.homMk ((G.obj T').fromSpecResidueField x) :
      B.obj hKx ⟶ T'.left) (by
      apply ObjectProperty.hom_ext
      show (G.obj T').fromSpecResidueField x ≫ B.inclusion.map T'.hom =
        Spec.map (CommRingCat.ofHom (algebraMap R' ((G.obj T').residueField x))) ≫
          Spec.map (CommRingCat.ofHom φA) ≫ i₂ ≫ B.inclusion.map Tobj.hom
      rw [hT'hom, G.map_comp]
      simp only [Category.assoc]
      rw [reassoc_of% hw])
  have hgenE : e.square.generic = yoneda.map (uKx ≫ τZ) := by
    rw [e.generic_comm]
    show yoneda.map e.genericOver ≫ yoneda.map uK = _
    rw [← yoneda.map_comp]
    congr 1
    apply BigFppfOver.map_toScheme_injective B S hS
    show Spec.map (CommRingCat.ofHom (F.residueFieldMap x).hom) ≫
        (G.obj Zobj).fromSpecResidueField (F x) = (G.obj T').fromSpecResidueField x ≫ G.map τZ
    rw [hFτ]
    rfl
  -- the generic arrow over `R'` factors through `h`
  have key : (yoneda.map uKx ≫ t ≫ pullback.snd g h) ≫ h =
      e.square.generic ≫ p' ≫ pullback.snd φ f := by
    simp only [Category.assoc]
    rw [← pullback.condition, ← Category.assoc t (pullback.fst g h) g, ← hτ₀, ← hτZι, hgenE]
    simp only [p', g, yoneda.map_comp, Category.assoc]
  -- lift through the proper `Z ⟶ X_A`, then
  -- descent to `A'` (Stacks 0ARH)
  obtain ⟨lZ, h1, h2⟩ := exists_hom_of_nonempty_lift qZ (uK := uK) (uA := uA) rfl rfl
    (nonempty_lift_of_dominatingExtension_of_isProper hZ hT f h φ hXT (ι ≫ ψ)
      ((isSeparated_yoneda_map_iff B S hS (ι ≫ ψ)).2 hχSep) p' hp' hp'ψ hvaluative qZ e
      (inferInstanceAs (IsDiscreteValuationRing (R' : Type u))) _ key)
  refine ⟨⟨G.map lZ, ?_, ?_⟩⟩
  · have h1' := congrArg G.map h1
    rw [G.map_comp] at h1'
    exact h1'
  · have h2' := congrArg G.map h2
    rw [G.map_comp] at h2'
    exact h2'

/-- The proper morphism from the scheme-theoretic image `Z` of `T' ⟶ X'` to the base change
`X_A` of `X` is surjective: its image is closed and contains the dense set of points of `X_A`
lying over the image of `|h|`. -/
private theorem isSurjective_schemeImageObjι_comp
    (A : CommRingCat.{u}) (hA : B.Contains (Spec A)) (a : Spec A ⟶ S)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hU : IsAlgebraicSpace B S hS U) (f : X ⟶ Y) (h : U ⟶ X)
    (φ : yoneda.obj (siteObject B S hS hA a) ⟶ Y)
    {X' T' : BigFppfOver B S hS} (ψ : X' ⟶ siteObject B S hS hA a)
    (p : yoneda.obj X' ⟶ pullback φ f) (hp : IsProper B S hS p)
    (hpψ : p ≫ pullback.fst φ f = yoneda.map ψ)
    (t : yoneda.obj T' ⟶ pullback (p ≫ pullback.snd φ f) h) (τ₀ : T' ⟶ X')
    (hτ₀ : yoneda.map τ₀ = t ≫ pullback.fst (p ≫ pullback.snd φ f) h)
    (hφ : IsEtale B S hS φ) (hpsurj : IsSurjective B S hS p)
    (hdense : @DenseRange _ (pointTopology B S hS X) _ (pointsMap B S hS U h))
    (htSurj : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf t) :
    IsSurjective B S hS (yoneda.map (schemeImageObjι B S hS τ₀) ≫ p) := by
  classical
  set G := BigFppfOver.toScheme B S hS
  let Tobj := siteObject B S hS hA a
  let g : yoneda.obj X' ⟶ X := p ≫ pullback.snd φ f
  have hT : IsAlgebraicSpace B S hS (yoneda.obj Tobj) := isAlgebraicSpace_yoneda B S hS _
  have hXT : IsAlgebraicSpace B S hS (pullback φ f) :=
    isAlgebraicSpace_pullback B S hS φ f hT hX hY
  have hX' : IsAlgebraicSpace B S hS (yoneda.obj X') := isAlgebraicSpace_yoneda B S hS X'
  let Zobj := schemeImageObj B S hS τ₀
  let ι : Zobj ⟶ X' := schemeImageObjι B S hS τ₀
  let τZ : T' ⟶ Zobj := toSchemeImageObj B S hS τ₀
  have hτZι : τZ ≫ ι = τ₀ := toSchemeImageObj_comp_schemeImageObjι B S hS τ₀
  have hιCI : _root_.AlgebraicGeometry.IsClosedImmersion (G.map ι) :=
    isClosedImmersion_schemeImageObjι B S hS τ₀
  have hZ : IsAlgebraicSpace B S hS (yoneda.obj Zobj) := isAlgebraicSpace_yoneda B S hS Zobj
  let p' : yoneda.obj Zobj ⟶ pullback φ f := yoneda.map ι ≫ p
  have hp'ψ : p' ≫ pullback.fst φ f = yoneda.map (ι ≫ ψ) := by
    simp only [p', Category.assoc, hpψ, yoneda.map_comp]
  have hp' : IsProper B S hS p' :=
    isProper_comp' B S hS (yoneda.map ι) p hX' hXT
      (isProper_yoneda_map B S hS ι inferInstance) hp
  let _ : TopologicalSpace (points B S hS X) := pointTopology B S hS X
  have hPB : IsAlgebraicSpace B S hS (pullback g h) :=
    isAlgebraicSpace_pullback B S hS g h hX' hU hX
  let _ : TopologicalSpace (points B S hS (yoneda.obj Zobj)) :=
    pointTopology B S hS (yoneda.obj Zobj)
  let _ : TopologicalSpace (points B S hS (pullback φ f)) := pointTopology B S hS (pullback φ f)
  have hclosed : IsClosedMap (pointsMap B S hS (yoneda.obj Zobj) p') :=
    isClosedMap_pointsMap_of_pullback_fst_id B S hS p' (hp'.2.2 _ hXT (𝟙 _))
  have hD : Dense (pointsMap B S hS (pullback φ f) (pullback.snd φ f) ⁻¹'
      Set.range (pointsMap B S hS U h)) :=
    hdense.preimage (isOpenMap_pointsMap_of_isEtale B S hS _ hXT hX
      (isEtale_pullback_snd B S hS hX hY hT φ f hφ))
  have hsub : pointsMap B S hS (pullback φ f) (pullback.snd φ f) ⁻¹'
      Set.range (pointsMap B S hS U h) ⊆ Set.range (pointsMap B S hS (yoneda.obj Zobj) p') := by
    rintro z ⟨y, hy⟩
    obtain ⟨z', rfl⟩ := hpsurj z
    obtain ⟨w, hw, -⟩ := exists_points_of_isPullback B S hS (IsPullback.of_hasPullback g h) z' y
      (by rw [pointsMap_comp_apply]; exact hy.symm)
    obtain ⟨v, rfl⟩ :=
      (surjective_iff_surjective_pointsMap B S hS (pullback g h) hPB T' t).1 htSurj w
    refine ⟨pointsMap B S hS (yoneda.obj T') (yoneda.map τZ) v, ?_⟩
    rw [← hw, ← pointsMap_comp_apply, ← pointsMap_comp_apply, ← pointsMap_comp_apply]
    congr 1
    simp only [p', ← Category.assoc, ← yoneda.map_comp, hτZι, hτ₀]
    rfl
  intro z
  have hz : z ∈ closure (Set.range (pointsMap B S hS (yoneda.obj Zobj) p')) := hD.mono hsub z
  rwa [hclosed.isClosed_range.closure_eq] at hz

/-- The chart case of Stacks 0CMD: over an étale chart `Spec A ⟶ Y` with `A` Noetherian, the
base change of `f` is universally closed. See the module documentation for the argument. -/
private theorem universallyClosed_pullback_fst_of_denseRange
    (A : CommRingCat.{u}) (hA : B.Contains (Spec A)) (a : Spec A ⟶ S)
    [IsLocallyNoetherian (Spec A)]
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hU : IsAlgebraicSpace B S hS U) (f : X ⟶ Y) (h : U ⟶ X)
    (hsep : IsSeparated B S hS f) (hft : IsFiniteType B S hS f) (hh : IsFiniteType B S hS h)
    (hdense : @DenseRange _ (pointTopology B S hS X) _ (pointsMap B S hS U h))
    (hvaluative : ∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R →
      ∀ g : yoneda.obj (siteObject B S hS q.field_mem
          (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)) ⟶ U,
        g ≫ h = q.generic → Nonempty q.Lift)
    (φ : yoneda.obj (siteObject B S hS hA a) ⟶ Y) (hφ : IsEtale B S hS φ) :
    UniversallyClosed B S hS (pullback.fst φ f) := by
  classical
  let _ : TopologicalSpace (points B S hS X) := pointTopology B S hS X
  let G := BigFppfOver.toScheme B S hS
  let Tobj := siteObject B S hS hA a
  have : IsLocallyNoetherian (G.obj Tobj) := inferInstanceAs (IsLocallyNoetherian (Spec A))
  have hT : IsAlgebraicSpace B S hS (yoneda.obj Tobj) := isAlgebraicSpace_yoneda B S hS _
  have hXT : IsAlgebraicSpace B S hS (pullback φ f) :=
    isAlgebraicSpace_pullback B S hS φ f hT hX hY
  have hsepT : IsSeparated B S hS (pullback.fst φ f) :=
    isSeparated_pullback_fst_of_snd B S hS f φ (isSeparated_pullback B S hS f φ hsep)
  have hftT : IsFiniteType B S hS (pullback.fst φ f) :=
    IsFiniteType.of_isPullback B S hS (IsPullback.of_hasPullback φ f) hX hY hft
  -- the weak Chow lemma over the chart
  obtain ⟨X', ψ, p, hp, hpsurj, hpψ, hqp⟩ :=
    exists_chowSchemeCover_over_spec B S hS A hA a hXT (pullback.fst φ f) hsepT hftT
  have hX' : IsAlgebraicSpace B S hS (yoneda.obj X') := isAlgebraicSpace_yoneda B S hS X'
  have hψLFT : LocallyOfFiniteType (G.map ψ) := by
    refine (isLocallyOfFiniteType_yoneda_map_iff B S hS ψ).mp ?_
    rw [← hpψ]
    exact isLocallyOfFiniteType_comp B S hS hX' hXT hT p (pullback.fst φ f) hp.2.1.1 hftT.1
  have hψQC : QuasiCompact (G.map ψ) := quasiCompact_of_isHQuasiProjective hqp
  have hψSep : _root_.AlgebraicGeometry.IsSeparated (G.map ψ) := by
    refine (isSeparated_yoneda_map_iff B S hS ψ).mp ?_
    rw [← hpψ]
    exact isSeparated_comp B S hS p (pullback.fst φ f) hp.1 hsepT
  have : IsLocallyNoetherian (G.obj X') := LocallyOfFiniteType.isLocallyNoetherian (G.map ψ)
  have : CompactSpace (G.obj Tobj) := inferInstanceAs (CompactSpace (Spec A))
  have : CompactSpace (G.obj X') := QuasiCompact.compactSpace_of_compactSpace (G.map ψ)
  -- a quasi-compact étale atlas of the base change of `h` to `X'`
  let g : yoneda.obj X' ⟶ X := p ≫ pullback.snd φ f
  obtain ⟨T', t, hT'c, htSurj, htEt⟩ := hh.2 (yoneda.obj X') hX'
    (isQuasiCompact_yoneda_of_compact B S hS X' inferInstance) g
  have hPB : IsAlgebraicSpace B S hS (pullback g h) :=
    isAlgebraicSpace_pullback B S hS g h hX' hU hX
  have hT' : IsAlgebraicSpace B S hS (yoneda.obj T') := isAlgebraicSpace_yoneda B S hS T'
  let τ₀ : T' ⟶ X' := yoneda.preimage (t ≫ pullback.fst g h)
  have hτ₀ : yoneda.map τ₀ = t ≫ pullback.fst g h := yoneda.map_preimage _
  have hτ₀LFT : LocallyOfFiniteType (G.map τ₀) := by
    refine (isLocallyOfFiniteType_yoneda_map_iff B S hS τ₀).mp ?_
    rw [hτ₀]
    exact isLocallyOfFiniteType_comp B S hS hT' hPB hX' t (pullback.fst g h)
      (isLocallyOfFiniteType_of_isEtale B S hS hPB htEt)
      (IsLocallyOfFiniteType.of_isPullback B S hS (IsPullback.of_hasPullback g h) hU hX hh.1)
  have : CompactSpace (G.obj T') := hT'c
  have hτ₀QC : QuasiCompact (G.map τ₀) := quasiCompact_of_compactSpace _
  -- the scheme-theoretic image `Z` of `T' ⟶ X'`
  let Zobj := schemeImageObj B S hS τ₀
  let ι : Zobj ⟶ X' := schemeImageObjι B S hS τ₀
  have hιCI : _root_.AlgebraicGeometry.IsClosedImmersion (G.map ι) :=
    isClosedImmersion_schemeImageObjι B S hS τ₀
  have hZ : IsAlgebraicSpace B S hS (yoneda.obj Zobj) := isAlgebraicSpace_yoneda B S hS Zobj
  -- the morphism of schemes `Z ⟶ Spec A`
  have hχLFT : LocallyOfFiniteType (G.map (ι ≫ ψ)) := by
    rw [G.map_comp]
    infer_instance
  have hχQC : QuasiCompact (G.map (ι ≫ ψ)) := by
    rw [G.map_comp]
    infer_instance
  -- the proper morphism `Z ⟶ X_A`
  let p' : yoneda.obj Zobj ⟶ pullback φ f := yoneda.map ι ≫ p
  have hp'ψ : p' ≫ pullback.fst φ f = yoneda.map (ι ≫ ψ) := by
    simp only [p', Category.assoc, hpψ, yoneda.map_comp]
  have hχ : _root_.AlgebraicGeometry.IsProper (G.map (ι ≫ ψ)) :=
    isProper_of_genericDiscreteValuativeCriterion _
      (genericDiscreteValuativeCriterion_schemeImageObjι_comp A hA a hX hY hU f h φ ψ p hp hpψ t
        τ₀ hτ₀ hvaluative)
  -- surjectivity of `Z ⟶ X_A`
  refine universallyClosed_of_isSurjective_comp B S hS hZ hXT hT p' (pullback.fst φ f) ?_
    (isSurjective_schemeImageObjι_comp A hA a hX hY hU f h φ ψ p hp hpψ t τ₀ hτ₀ hφ hpsurj
      hdense htSurj)
  rw [hp'ψ]
  exact universallyClosed_yoneda_map B S hS _ inferInstance

/-- **Stacks 0CMD.** Let `f : X ⟶ Y` and `h : U ⟶ X` be morphisms of algebraic spaces over `S`
with `Y` locally Noetherian, `f` and `h` of finite type, `f` separated and the image of
`|h| : |U| → |X|` dense in `|X|`. If every commutative valuative diagram for `f` over a discrete
valuation ring `A` with fraction field `K` whose generic arrow `Spec K ⟶ X` factors through `h`
has a dotted arrow `Spec A ⟶ X`, then `f` is proper.

Universal closedness is tested on a family of étale charts `Spec A ⟶ Y` with `A` Noetherian
(Stacks 03IT); over each chart the argument is the one described in the module
documentation. -/
theorem isProper_of_denseRange_of_exists_discreteLift
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hU : IsAlgebraicSpace B S hS U) (f : X ⟶ Y) (h : U ⟶ X)
    (hnoeth : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hft : IsFiniteType B S hS f) (hh : IsFiniteType B S hS h) (hsep : IsSeparated B S hS f)
    (hdense : @DenseRange _ (pointTopology B S hS X) _ (pointsMap B S hS U h))
    (hvaluative : ∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R →
      ∀ g : yoneda.obj (siteObject B S hS q.field_mem
          (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)) ⟶ U,
        g ≫ h = q.generic → Nonempty q.Lift) :
    IsProper B S hS f := by
  refine ⟨hsep, hft, ?_⟩
  obtain ⟨I, A, hA, a, φ, -, hLocNoeth, hEtale, hCover⟩ :=
    exists_spec_isLocallyNoetherian_etale_covering_family B S hS hY hnoeth
  refine universallyClosed_of_etale_covering_family B S hS hY f
    (fun i ↦ siteObject B S hS (hA i) (a i)) φ hEtale hCover fun i ↦ ?_
  have := hLocNoeth i
  exact universallyClosed_pullback_fst_of_denseRange (A i) (hA i) (a i) hX hY hU f h hsep hft hh
    hdense hvaluative (φ i) (hEtale i)

/-- **Stacks 0CMF.** Let `f : X ⟶ Y` and `h : U ⟶ X` be morphisms of algebraic spaces over `S`
with `Y` locally Noetherian, `f` and `h` of finite type, `f` quasi-separated and the image of
`|h| : |U| → |X|` dense in `|X|`. If every commutative valuative diagram for `f` over a discrete
valuation ring `A` with fraction field `K` whose generic arrow `Spec K ⟶ X` factors through `h`
has exactly one dotted arrow `Spec A ⟶ X`, then `f` is proper.

As in the source this combines Stacks 0CME, which gives separatedness of `f` from the uniqueness
of the dotted arrows, with Stacks 0CMD, which gives properness from their existence. -/
@[stacks 0CMF]
theorem isProper_of_denseRange_of_unique_discreteLift
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hU : IsAlgebraicSpace B S hS U) (f : X ⟶ Y) (h : U ⟶ X)
    (hnoeth : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hft : IsFiniteType B S hS f) (hh : IsFiniteType B S hS h) (hqs : IsQuasiSeparated B S hS f)
    (hdense : @DenseRange _ (pointTopology B S hS X) _ (pointsMap B S hS U h))
    (hvaluative : ∀ q : ValuativeSquare f, IsDiscreteValuationRing q.R →
      ∀ g : yoneda.obj (siteObject B S hS q.field_mem
          (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)) ⟶ U,
        g ≫ h = q.generic → Nonempty q.Lift ∧ Subsingleton q.Lift) :
    IsProper B S hS f :=
  isProper_of_denseRange_of_exists_discreteLift hX hY hU f h hnoeth hft hh
    (isSeparated_of_denseRange_of_subsingleton_discreteLift hX hY hU f h hnoeth hft.1 hqs hh
      hdense fun q hq g hg => (hvaluative q hq g hg).2)
    hdense fun q hq g hg => (hvaluative q hq g hg).1

end AlgebraicGeometry.Space

end
