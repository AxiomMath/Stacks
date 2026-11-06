module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Smooth.StrongLifting
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurj

/-!
# Smooth morphisms satisfy the strong local lifting property (Stacks 0CHJ)

Let `S` be a scheme and consider a commutative square
```
X ←--- T
|      |
f      i
↓      ↓
Y ←--- T'
```
of algebraic spaces over `S` in which `f` is smooth and `i` is a thickening. Stacks 0CHJ asserts
that there is an étale covering `{T'ₖ ⟶ T'}` over each member of which the square can be filled
in: a morphism `T'ₖ ⟶ X` lying over `T'ₖ ⟶ T' ⟶ Y` and restricting on `T ×_{T'} T'ₖ` to the
given `T ⟶ X`.

## Main results

* `AlgebraicGeometry.Space.exists_chart_isClosedImmersion_of_isThickeningHom`: the restriction of
  a thickening of algebraic spaces to an étale chart of its target is a closed immersion of
  objects of the site which is surjective on points.
* `AlgebraicGeometry.Space.exists_siteObject_of_opens`: an open subscheme of an object of the big
  fppf category over `S` is again an object of that category.

## Implementation notes

The covering produced is by *affine schemes of the site*, which is stronger than the source's
conclusion and is what the proof naturally delivers.

## References

* [Stacks Project, Tag 0CHJ](https://stacks.math.columbia.edu/tag/0CHJ)
* [Stacks Project, Tag 039R](https://stacks.math.columbia.edu/tag/039R)
* [Stacks Project, Tag 07K4](https://stacks.math.columbia.edu/tag/07K4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_SmoothStrongLift :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_SmoothStrongLift
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
/-- Small discrete limits of presheaves on the big fppf site (instance search times out without
this shortcut). -/
local instance (priority := high) hasLimitsOfShape_discrete_presheaf_SmoothStrongLift
    (J : Type) : HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  inferInstance

/-- **An open subscheme of an object of the site is an object of the site.** Its size is bounded
by that of the ambient object, because an open immersion is a monomorphism locally of finite
presentation. -/
theorem exists_siteObject_of_opens (W : BigFppfOver B S hS)
    (A : ((BigFppfOver.toScheme B S hS).obj W).Opens) :
    ∃ (A' : BigFppfOver B S hS) (m : A' ⟶ W),
      _root_.AlgebraicGeometry.IsOpenImmersion
        ((BigFppfOver.toScheme B S hS).map m) ∧
      Set.range ((BigFppfOver.toScheme B S hS).map m).base = (A : Set _) ∧
      (IsAffineOpen A → IsAffine ((BigFppfOver.toScheme B S hS).obj A')) := by
  have hcontains : B.Contains A.toScheme :=
    Scheme.size_lt_of_isOpenImmersion A.ι W.left.property
  let cs : B.obj hcontains ⟶ W.left := B.inclusion.preimage
    (show B.inclusion.obj (B.obj hcontains) ⟶ B.inclusion.obj W.left from A.ι)
  have hm : (BigFppfOver.toScheme B S hS).map
      (Over.homMk cs : Over.mk (cs ≫ W.hom) ⟶ W) = A.ι :=
    B.inclusion.map_preimage _
  refine ⟨Over.mk (cs ≫ W.hom), Over.homMk cs, ?_, ?_, id⟩
  · rw [hm]
    infer_instance
  · rw [hm]
    exact A.range_ι

/-- Every point of an object `W` of the site lies in an affine open of `W` which is itself an
object of the site, mapping to `W` by an open immersion with that open as image. -/
private theorem exists_affine_siteObject_of_mem (W : BigFppfOver B S hS)
    (x : ((BigFppfOver.toScheme B S hS).obj W)) :
    ∃ (A : ((BigFppfOver.toScheme B S hS).obj W).Opens) (A' : BigFppfOver B S hS) (m : A' ⟶ W),
      x ∈ A ∧ _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map m) ∧
      Set.range ((BigFppfOver.toScheme B S hS).map m).base = (A : Set _) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj A') := by
  obtain ⟨_, ⟨A, hAaff, rfl⟩, hxA, -⟩ :=
    ((BigFppfOver.toScheme B S hS).obj W).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ x) isOpen_univ
  obtain ⟨A', m, hm, hrange, haff⟩ := exists_siteObject_of_opens B S hS W A
  exact ⟨A, A', m, hxA, hm, hrange, haff hAaff⟩

/-- **The restriction of a thickening of algebraic spaces to an étale chart of its target.** Let
`i : T ⟶ T'` be a thickening of algebraic spaces over `S` and let `ζ : yoneda.obj Z ⟶ T'` be any
morphism from a representable presheaf. Then the base change of `i` along `ζ` is represented by
an object `J` of the site, the projection `j : J ⟶ Z` is a closed immersion of schemes and is
surjective on points.

This is the general-thickening companion of
`AlgebraicGeometry.Space.exists_chart_isClosedImmersion_of_isFirstOrderThickening`; both
properties are read off the *same* represented pullback square, so that the closed immersion and
the surjection are the same morphism. -/
theorem exists_chart_isClosedImmersion_of_isThickeningHom
    {T T' : AlgebraicSpaces B S hS} {i : T ⟶ T'} (hi : IsThickeningHom B S hS i)
    (Z : BigFppfOver B S hS) (ζ : yoneda.obj Z ⟶ T'.obj) :
    ∃ (J : BigFppfOver B S hS) (j : J ⟶ Z) (η : yoneda.obj J ⟶ T.obj),
      IsPullback (yoneda.map j) η ζ i.hom ∧
      _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j) ∧
      Function.Surjective ((BigFppfOver.toScheme B S hS).map j).base := by
  have hrep := hi.isClosedImmersion.rep
  refine ⟨hrep.pullback ζ, hrep.snd ζ, hrep.fst ζ, (hrep.isPullback ζ).flip,
    hi.isClosedImmersion.property ζ (hrep.fst ζ) (hrep.snd ζ) (hrep.isPullback ζ),
    (hi.surjective.property ζ (hrep.fst ζ) (hrep.snd ζ) (hrep.isPullback ζ)).surj⟩

/-- The functor from the big fppf category over `S` to schemes is faithful, being the
composite of the forgetful functor of a slice with the inclusion of a full subcategory. -/
theorem toScheme_map_injective {W W' : BigFppfOver B S hS} {m₁ m₂ : W ⟶ W'}
    (h : (BigFppfOver.toScheme B S hS).map m₁ = (BigFppfOver.toScheme B S hS).map m₂) :
    m₁ = m₂ :=
  Over.OverMorphism.ext (B.inclusion.map_injective h)

/-- A morphism of the big fppf category over `S` commutes with the structure morphisms to the
base, read on underlying schemes. -/
theorem toScheme_map_comp_hom {W W' : BigFppfOver B S hS} (m : W ⟶ W') :
    (BigFppfOver.toScheme B S hS).map m ≫ B.inclusion.map W'.hom = B.inclusion.map W.hom := by
  rw [show (BigFppfOver.toScheme B S hS).map m = B.inclusion.map m.left from rfl,
    ← B.inclusion.map_comp, Over.w]

/-- The composite of the image under `yoneda` of a morphism of the site that is étale on
schemes with an étale morphism of presheaves is étale. -/
private theorem isEtale_yoneda_map_comp {W W' : BigFppfOver B S hS} (g : W ⟶ W')
    (hg : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map g))
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k : yoneda.obj W' ⟶ F) (hk : IsEtale B S hS k) :
    IsEtale B S hS (yoneda.map g ≫ k) :=
  isEtale_comp B S hS ((isEtale_iff_presheaf_of_yoneda B S hS _).2
    ((presheaf_yoneda_map_etale_iff B S hS g).2 hg)) hk

/-- **Stacks 0CHJ.** Let `S` be a scheme and consider a commutative square of algebraic spaces
over `S`
```
X ←--a-- T
|        |
f        i
↓        ↓
Y ←--b-- T'
```
in which `f` is smooth and `i` is a thickening. Then there is an étale covering of `T'` by
affine schemes `T'ₚ` of the site such that over each member the square can be filled in: there
is a `ψ : T'ₚ ⟶ X` with `ψ` over `Y` equal to `T'ₚ ⟶ T' ⟶ Y` and with the restriction of `ψ` to
`T ×_{T'} T'ₚ` equal to the restriction of `a`.

The covering is indexed by the points of `T'`, and the member at a point contains that point.

The proof follows the source, with the three reductions performed in one step for each member of
the covering rather than globally. Write `Z = X ×_Y T'`; it is smooth over `T'` because `f` is,
and the given data provide a section `σ : T ⟶ Z` of `Z ⟶ T'` over `T`. Given a point of `T'`,
choose an affine étale chart `P` of `T'` through it (Stacks 03FX, in the pointwise form
`AlgebraicGeometry.Space.exists_affine_etale_chart_at_point`) and let `J = T ×_{T'} P`, an affine
scheme and a thickening of `P`. Pulling an atlas of `Z` back along `J ⟶ Z` and intersecting with
the base change of `P` to that atlas produces an affine chart `U` of `Z` lying over `P` — so that
`U ⟶ P` is a *smooth morphism of affine schemes*, since smoothness of `Z ⟶ T'` is exactly the
condition on every square of étale charts — together with an étale `N ⟶ J` through the chosen
point and a morphism `N ⟶ U` over `Z`. Topological invariance of the étale site (Stacks 039R, in
the size-controlled cartesian form
`AlgebraicGeometry.Space.exists_etaleLift_isPullback_of_chart`) lifts `N ⟶ J` to an étale
`V ⟶ P` with `N = T ×_{T'} V`; shrinking `V` to an affine open through the point makes it affine,
and `Stacks.Smooth.exists_lift_of_isClosedImmersion_of_surjective` — the geometric form of
Algebra, Lemma 10.138.17 — then extends `T ×_{T'} V' ⟶ U` over the thickening to `V' ⟶ U`. The
member of the covering is `V'`, and `ψ` is `V' ⟶ U ⟶ Z ⟶ X`. -/
@[stacks 0CHJ]
theorem exists_isEtaleCovering_lift_of_isSmooth_of_isThickeningHom
    {X Y T T' : AlgebraicSpaces B S hS} {f : X ⟶ Y} (hf : IsSmooth B S hS f.hom)
    {i : T ⟶ T'} (hi : IsThickeningHom B S hS i) (a : T ⟶ X) (b : T' ⟶ Y)
    (hcomm : a ≫ f = i ≫ b) :
    ∃ (Z : points B S hS T'.obj → BigFppfOver B S hS)
      (q : ∀ p, yoneda.obj (Z p) ⟶ T'.obj),
      (∀ p, IsAffine ((BigFppfOver.toScheme B S hS).obj (Z p))) ∧
      IsEtaleCovering B S hS (fun p ↦ yoneda.obj (Z p)) q ∧
      ∀ p, ∃ ψ : yoneda.obj (Z p) ⟶ X.obj,
        ψ ≫ f.hom = q p ≫ b.hom ∧
        pullback.snd i.hom (q p) ≫ ψ = pullback.fst i.hom (q p) ≫ a.hom := by
  classical
  have hcomm' : a.hom ≫ f.hom = i.hom ≫ b.hom := by
    simpa using congrArg (fun m : T ⟶ Y ↦ m.hom) hcomm
  -- `Z = X ×_Y T'`, smooth over `T'`, with the section `σ` over `T`.
  set Zsp : AlgebraicSpaces B S hS := AlgebraicSpaces.fiberProduct B S hS f b with hZsp
  set pr₁ : Zsp.obj ⟶ X.obj := pullback.fst f.hom b.hom with hpr₁
  set pr₂ : Zsp.obj ⟶ T'.obj := pullback.snd f.hom b.hom with hpr₂
  have hsmZ : IsSmooth B S hS pr₂ :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := smoothMorphismProperty B S hS)
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f b) hf
  set σ : T.obj ⟶ Zsp.obj := pullback.lift a.hom i.hom hcomm' with hσ
  have hσ₁ : σ ≫ pr₁ = a.hom := pullback.lift_fst _ _ _
  have hσ₂ : σ ≫ pr₂ = i.hom := pullback.lift_snd _ _ _
  -- An atlas of `Z`.
  obtain ⟨U₀, c₀, hc₀s, hc₀e⟩ := Zsp.property.exists_atlas
  have hc₀et : IsEtale B S hS c₀ := (isEtale_iff_presheaf_of_yoneda B S hS c₀).2 hc₀e
  have key : ∀ p : points B S hS T'.obj,
      ∃ (Zp : BigFppfOver B S hS) (q : yoneda.obj Zp ⟶ T'.obj),
        IsAffine ((BigFppfOver.toScheme B S hS).obj Zp) ∧ IsEtale B S hS q ∧
        p ∈ Set.range (pointsMap B S hS (yoneda.obj Zp) q) ∧
        ∃ ψ : yoneda.obj Zp ⟶ X.obj, ψ ≫ f.hom = q ≫ b.hom ∧
          pullback.snd i.hom q ≫ ψ = pullback.fst i.hom q ≫ a.hom := by
    intro p
    -- An affine étale chart `P` of `T'` through `p`.
    obtain ⟨P, ζ, hPaff, hζpre, w, hw⟩ :=
      exists_affine_etale_chart_at_point B S hS T'.obj T'.property p
    have hζet : IsEtale B S hS ζ := (isEtale_iff_presheaf_of_yoneda B S hS ζ).2 hζpre
    -- `J = T ×_{T'} P`, a thickening of `P`.
    obtain ⟨J, j, η, hJpb, hjci, hjsurj⟩ :=
      exists_chart_isClosedImmersion_of_isThickeningHom B S hS hi P ζ
    have : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map j) := hjci
    -- The atlas of `Z` pulled back along `J ⟶ T ⟶ Z`.
    set τ : yoneda.obj J ⟶ Zsp.obj := η ≫ σ with hτ
    have hrepc₀ := hc₀s.rep
    set N₀ : BigFppfOver B S hS := hrepc₀.pullback τ with hN₀
    set nJ : N₀ ⟶ J := hrepc₀.snd τ with hnJ
    set nU₀' : yoneda.obj N₀ ⟶ yoneda.obj U₀ := hrepc₀.fst τ with hnU₀'
    have hN₀pb : IsPullback nU₀' (yoneda.map nJ) c₀ τ := hrepc₀.isPullback τ
    have hnJsurj : Function.Surjective ((BigFppfOver.toScheme B S hS).map nJ).base :=
      (hc₀s.property τ nU₀' nJ hN₀pb).surj
    have hnJet : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map nJ) :=
      hc₀e.property τ nU₀' nJ hN₀pb
    -- `M = U₀ ×_{T'} P`, étale over the atlas and lying over `P`.
    have hrepζ := hζpre.rep
    set M : BigFppfOver B S hS := hrepζ.pullback (c₀ ≫ pr₂) with hM
    set mU : M ⟶ U₀ := hrepζ.snd (c₀ ≫ pr₂) with hmU
    set mP' : yoneda.obj M ⟶ yoneda.obj P := hrepζ.fst (c₀ ≫ pr₂) with hmP'
    have hMpb : IsPullback mP' (yoneda.map mU) ζ (c₀ ≫ pr₂) := hrepζ.isPullback _
    have hmUet : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map mU) :=
      hζpre.property (c₀ ≫ pr₂) mP' mU hMpb
    set mP : M ⟶ P := yoneda.preimage mP' with hmPdef
    have hmPmap : yoneda.map mP = mP' := yoneda.map_preimage _
    -- The canonical morphism `N₀ ⟶ M`.
    have hdcompat : yoneda.map (nJ ≫ j) ≫ ζ = nU₀' ≫ (c₀ ≫ pr₂) := by
      have h1 := hN₀pb.w
      rw [hτ] at h1
      simp only [Functor.map_comp, Category.assoc]
      rw [hJpb.w, ← hσ₂, ← Category.assoc nU₀' c₀ pr₂, h1]
      simp only [Category.assoc]
    set dpres : yoneda.obj N₀ ⟶ yoneda.obj M :=
      hMpb.lift (yoneda.map (nJ ≫ j)) nU₀' hdcompat with hdpres
    have hd₁ : dpres ≫ mP' = yoneda.map (nJ ≫ j) := hMpb.lift_fst _ _ _
    have hd₂ : dpres ≫ yoneda.map mU = nU₀' := hMpb.lift_snd _ _ _
    set d : N₀ ⟶ M := yoneda.preimage dpres with hddef
    have hdmap : yoneda.map d = dpres := yoneda.map_preimage _
    have hdmP : d ≫ mP = nJ ≫ j :=
      yoneda.map_injective (by rw [yoneda.map_comp, hdmap, hmPmap, hd₁])
    -- The chosen points of `P`, `J`, `N₀` and `M`.
    obtain ⟨jS, hjS⟩ := hjsurj (pointsToScheme B S hS P w)
    obtain ⟨nJS, hnJS⟩ := hnJsurj jS
    set m₀ : (BigFppfOver.toScheme B S hS).obj M :=
      ((BigFppfOver.toScheme B S hS).map d).base nJS with hm₀
    -- An affine chart `U` of `Z` lying over `P`, through `m₀`.
    obtain ⟨A, U, uM, hm₀A, huMimm, huMrange, _⟩ := exists_affine_siteObject_of_mem B S hS M m₀
    have := huMimm
    -- The open part of `N₀` lying over `U`, étale over `J` and through the chosen point.
    obtain ⟨N, nN₀, hnN₀imm, hnN₀range, -⟩ := exists_siteObject_of_opens B S hS N₀
      ((BigFppfOver.toScheme B S hS).map d ⁻¹ᵁ A)
    have := hnN₀imm
    have hnJSmem : nJS ∈ Set.range ((BigFppfOver.toScheme B S hS).map nN₀).base := by
      rw [hnN₀range]
      exact hm₀A
    obtain ⟨nS, hnS⟩ := hnJSmem
    -- The morphism `N ⟶ U`.
    have hran : Set.range ((BigFppfOver.toScheme B S hS).map nN₀ ≫
        (BigFppfOver.toScheme B S hS).map d).base ⊆
        Set.range ((BigFppfOver.toScheme B S hS).map uM).base := by
      rintro y ⟨x, rfl⟩
      rw [huMrange]
      have hx : ((BigFppfOver.toScheme B S hS).map nN₀).base x ∈
          ((BigFppfOver.toScheme B S hS).map d ⁻¹ᵁ A : Set _) := by
        rw [← hnN₀range]
        exact Set.mem_range_self x
      simpa using hx
    set nUS := IsOpenImmersion.lift ((BigFppfOver.toScheme B S hS).map uM)
      ((BigFppfOver.toScheme B S hS).map nN₀ ≫ (BigFppfOver.toScheme B S hS).map d) hran
      with hnUS
    have hnUSfac : nUS ≫ (BigFppfOver.toScheme B S hS).map uM =
        (BigFppfOver.toScheme B S hS).map nN₀ ≫ (BigFppfOver.toScheme B S hS).map d :=
      IsOpenImmersion.lift_fac _ _ _
    obtain ⟨nU, hnUmap⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS
      (X := N) (Y := U) nUS (by
        rw [← toScheme_map_comp_hom B S hS uM, ← Category.assoc, hnUSfac, Category.assoc,
          toScheme_map_comp_hom B S hS d, toScheme_map_comp_hom B S hS nN₀])
    have hnUuM : (BigFppfOver.toScheme B S hS).map (nU ≫ uM) =
        (BigFppfOver.toScheme B S hS).map (nN₀ ≫ d) := by
      rw [Functor.map_comp, Functor.map_comp, hnUmap, hnUSfac]
    -- Topological invariance of the étale site lifts `N ⟶ J` to `V ⟶ P`.
    have hket : _root_.AlgebraicGeometry.Etale
        ((BigFppfOver.toScheme B S hS).map (nN₀ ≫ nJ)) := by
      rw [Functor.map_comp]
      have : _root_.AlgebraicGeometry.Etale
        ((BigFppfOver.toScheme B S hS).map nJ) := hnJet
      infer_instance
    obtain ⟨V, qV, pNV, hqVet, hqVspet, hsitepb, hprespb⟩ :=
      exists_etaleLift_isPullback_of_chart B S hS j hjsurj η ζ hζet hJpb (nN₀ ≫ nJ) hket
    -- An affine open `V'` of `V` through the chosen point.
    set v₀ : (BigFppfOver.toScheme B S hS).obj V :=
      ((BigFppfOver.toScheme B S hS).map pNV).base nS with hv₀
    obtain ⟨A', V', vV, hv₀A', hvVimm, hvVrange, _⟩ := exists_affine_siteObject_of_mem B S hS V v₀
    have := hvVimm
    set q' : V' ⟶ P := vV ≫ qV with hq'
    set qfin : yoneda.obj V' ⟶ T'.obj := yoneda.map q' ≫ ζ with hqfin
    have hqfinet : IsEtale B S hS qfin := by
      refine isEtale_yoneda_map_comp B S hS q' ?_ ζ hζet
      rw [hq', Functor.map_comp]
      have : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map qV) := hqVet
      infer_instance
    -- `J'' = T ×_{T'} V'`, a thickening of `V'`.
    obtain ⟨J'', j'', η'', hJ''pb, hj''ci, hj''surj⟩ :=
      exists_chart_isClosedImmersion_of_isThickeningHom B S hS hi V' qfin
    have : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map j'') := hj''ci
    -- The comparison `J'' ⟶ N`.
    have hlcompat : yoneda.map (j'' ≫ vV) ≫ (yoneda.map qV ≫ ζ) = η'' ≫ i.hom := by
      have h1 := hJ''pb.w
      rw [hqfin, hq'] at h1
      simpa only [Functor.map_comp, Category.assoc] using h1
    set l : yoneda.obj J'' ⟶ yoneda.obj N :=
      hprespb.lift (yoneda.map (j'' ≫ vV)) η'' hlcompat with hl
    have hl₁ : l ≫ yoneda.map pNV = yoneda.map (j'' ≫ vV) := hprespb.lift_fst _ _ _
    have hl₂ : l ≫ (yoneda.map (nN₀ ≫ nJ) ≫ η) = η'' := hprespb.lift_snd _ _ _
    set ls : J'' ⟶ N := yoneda.preimage l with hls
    have hlsmap : yoneda.map ls = l := yoneda.map_preimage _
    have hlspNV : ls ≫ pNV = j'' ≫ vV :=
      yoneda.map_injective (by rw [Functor.map_comp, hlsmap, hl₁, Functor.map_comp])
    -- The smooth morphism of affine schemes `U ⟶ P` and the lifting problem over it.
    set cU : yoneda.obj U ⟶ Zsp.obj := yoneda.map (uM ≫ mU) ≫ c₀ with hcU
    have hcUpre : (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf cU := by
      refine (isEtale_iff_presheaf_of_yoneda B S hS cU).1
        (isEtale_yoneda_map_comp B S hS (uM ≫ mU) ?_ c₀ hc₀et)
      rw [Functor.map_comp]
      have : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map mU) := hmUet
      infer_instance
    have hchartsq : yoneda.map (uM ≫ mP) ≫ ζ = cU ≫ pr₂ := by
      rw [Functor.map_comp, Category.assoc, hmPmap, hMpb.w, hcU, Functor.map_comp]
      simp only [Category.assoc]
    have hsmUP : _root_.AlgebraicGeometry.Smooth
        ((BigFppfOver.toScheme B S hS).map (uM ≫ mP)) :=
      hsmZ U P cU ζ (uM ≫ mP) hcUpre hζpre hchartsq
    have := hsmUP
    have hengcomm : (BigFppfOver.toScheme B S hS).map (ls ≫ nU) ≫
        (BigFppfOver.toScheme B S hS).map (uM ≫ mP) =
        (BigFppfOver.toScheme B S hS).map j'' ≫ (BigFppfOver.toScheme B S hS).map q' := by
      rw [← Functor.map_comp, ← Functor.map_comp]
      refine congrArg _ ?_
      calc (ls ≫ nU) ≫ uM ≫ mP = ls ≫ (nU ≫ uM) ≫ mP := by simp only [Category.assoc]
        _ = ls ≫ (nN₀ ≫ d) ≫ mP := by
              rw [toScheme_map_injective B S hS hnUuM]
        _ = ls ≫ nN₀ ≫ nJ ≫ j := by simp only [Category.assoc, hdmP]
        _ = ls ≫ (nN₀ ≫ nJ) ≫ j := by simp only [Category.assoc]
        _ = ls ≫ pNV ≫ qV := by rw [← hsitepb.w]
        _ = j'' ≫ q' := by rw [hq', ← Category.assoc, hlspNV, Category.assoc]
    obtain ⟨ψS, hψ₁, hψ₂⟩ := Stacks.Smooth.exists_lift_of_isClosedImmersion_of_surjective
      ((BigFppfOver.toScheme B S hS).map (uM ≫ mP)) hj''surj
      ((BigFppfOver.toScheme B S hS).map (ls ≫ nU))
      ((BigFppfOver.toScheme B S hS).map q') hengcomm
    obtain ⟨ψsite, hψsite⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS
      (X := V') (Y := U) ψS (by
        rw [← toScheme_map_comp_hom B S hS (uM ≫ mP), ← Category.assoc, hψ₁,
          toScheme_map_comp_hom B S hS q'])
    have hψsite₁ : ψsite ≫ (uM ≫ mP) = q' :=
      toScheme_map_injective B S hS (by rw [Functor.map_comp, hψsite, hψ₁])
    have hψsite₂ : j'' ≫ ψsite = ls ≫ nU :=
      toScheme_map_injective B S hS (by rw [Functor.map_comp, hψsite, hψ₂])
    -- The lift and its two compatibilities.
    refine ⟨V', qfin, inferInstance, hqfinet, ?_, yoneda.map ψsite ≫ cU ≫ pr₁, ?_, ?_⟩
    · -- the point `p` is hit
      obtain ⟨v', hv'⟩ : v₀ ∈ Set.range ((BigFppfOver.toScheme B S hS).map vV).base := by
        rw [hvVrange]
        exact hv₀A'
      refine ⟨(pointsEquivScheme B S hS V').symm v', ?_⟩
      have hptV' : pointsToScheme B S hS V' ((pointsEquivScheme B S hS V').symm v') = v' :=
        (pointsEquivScheme B S hS V').apply_symm_apply v'
      have hv₀' : (BigFppfOver.toScheme B S hS).map qV v₀
          = (BigFppfOver.toScheme B S hS).map j jS := by
        rw [hv₀]
        have h1 : (BigFppfOver.toScheme B S hS).map qV
            ((BigFppfOver.toScheme B S hS).map pNV nS)
            = (BigFppfOver.toScheme B S hS).map (pNV ≫ qV) nS := rfl
        rw [h1, hsitepb.w]
        change (BigFppfOver.toScheme B S hS).map j
          ((BigFppfOver.toScheme B S hS).map nJ
            ((BigFppfOver.toScheme B S hS).map nN₀ nS)) = _
        rw [hnS, hnJS]
      have hstep : pointsMap B S hS (yoneda.obj V') (yoneda.map q')
          ((pointsEquivScheme B S hS V').symm v') = w := by
        refine (bijective_pointsToScheme B S hS P).1 ?_
        rw [pointsToScheme_pointsMap_yoneda B S hS q', hptV']
        have h2 : (BigFppfOver.toScheme B S hS).map q' v'
            = (BigFppfOver.toScheme B S hS).map qV
              ((BigFppfOver.toScheme B S hS).map vV v') := by
          rw [hq']; rfl
        rw [h2, hv', hv₀', hjS]
      rw [hqfin, pointsMap_comp, Function.comp_apply, hstep, hw]
    · -- compatibility over `Y`
      have hcond : pr₁ ≫ f.hom = pr₂ ≫ b.hom := pullback.condition
      calc (yoneda.map ψsite ≫ cU ≫ pr₁) ≫ f.hom
          = yoneda.map ψsite ≫ cU ≫ pr₁ ≫ f.hom := by simp only [Category.assoc]
        _ = yoneda.map ψsite ≫ (cU ≫ pr₂) ≫ b.hom := by
              rw [hcond]
              simp only [Category.assoc]
        _ = yoneda.map ψsite ≫ (yoneda.map (uM ≫ mP) ≫ ζ) ≫ b.hom := by rw [hchartsq]
        _ = yoneda.map (ψsite ≫ (uM ≫ mP)) ≫ ζ ≫ b.hom := by
              simp only [Functor.map_comp, Category.assoc]
        _ = qfin ≫ b.hom := by rw [hψsite₁, hqfin, Category.assoc]
    · -- compatibility over `T`
      have h1 : hJ''pb.flip.isoPullback.hom ≫ pullback.fst i.hom qfin = η'' :=
        hJ''pb.flip.isoPullback_hom_fst
      have h2 : hJ''pb.flip.isoPullback.hom ≫ pullback.snd i.hom qfin = yoneda.map j'' :=
        hJ''pb.flip.isoPullback_hom_snd
      refine (cancel_epi hJ''pb.flip.isoPullback.hom).1 ?_
      rw [← Category.assoc hJ''pb.flip.isoPullback.hom (pullback.snd i.hom qfin),
        ← Category.assoc hJ''pb.flip.isoPullback.hom (pullback.fst i.hom qfin), h1, h2]
      calc yoneda.map j'' ≫ yoneda.map ψsite ≫ cU ≫ pr₁
          = yoneda.map (ls ≫ nU) ≫ cU ≫ pr₁ := by
            rw [← Category.assoc, ← Functor.map_comp, hψsite₂]
        _ = l ≫ yoneda.map nU ≫ cU ≫ pr₁ := by
            rw [Functor.map_comp, hlsmap, Category.assoc]
        _ = l ≫ (yoneda.map (nN₀ ≫ nJ) ≫ η) ≫ a.hom := by
            congr 1
            have hdmU : yoneda.map (d ≫ mU) = nU₀' := by
              rw [Functor.map_comp, hdmap, hd₂]
            have hw0 : nU₀' ≫ c₀ = yoneda.map nJ ≫ η ≫ σ := by
              have h0 := hN₀pb.w
              rwa [hτ] at h0
            calc yoneda.map nU ≫ cU ≫ pr₁
                = yoneda.map ((nU ≫ uM) ≫ mU) ≫ c₀ ≫ pr₁ := by
                  rw [hcU]
                  simp only [Functor.map_comp, Category.assoc]
              _ = yoneda.map (nN₀ ≫ d ≫ mU) ≫ c₀ ≫ pr₁ := by
                  rw [toScheme_map_injective B S hS hnUuM]
                  simp only [Category.assoc]
              _ = yoneda.map nN₀ ≫ (nU₀' ≫ c₀) ≫ pr₁ := by
                  rw [← hdmU]
                  simp only [Functor.map_comp, Category.assoc]
              _ = yoneda.map nN₀ ≫ (yoneda.map nJ ≫ η ≫ σ) ≫ pr₁ := by rw [hw0]
              _ = (yoneda.map (nN₀ ≫ nJ) ≫ η) ≫ a.hom := by
                  rw [← hσ₁]
                  simp only [Functor.map_comp, Category.assoc]
        _ = η'' ≫ a.hom := by rw [← Category.assoc, hl₂]
  choose Z q hZaff hZet hZmem hZlift using key
  refine ⟨Z, q, hZaff, ⟨T'.property, fun p ↦ isAlgebraicSpace_yoneda B S hS (Z p), hZet, ?_⟩,
    hZlift⟩
  exact Set.eq_univ_iff_forall.mpr fun p ↦ Set.mem_iUnion.mpr ⟨p, hZmem p⟩

end AlgebraicGeometry.Space

end
