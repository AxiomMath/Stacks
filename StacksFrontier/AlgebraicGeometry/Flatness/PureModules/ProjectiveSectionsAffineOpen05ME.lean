module

public import Mathlib.Algebra.Module.Projective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finite
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.RelativeWeakAssassin
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.WeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Divisors.RelativeAssassinTwo.BaseChange
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.ProjectiveSectionsAlongFibre
public import StacksFrontier.AlgebraicGeometry.Etale.FlatFiniteTypeModules
public import StacksFrontier.AlgebraicGeometry.Etale.FlatFiniteTypeNeighborhood
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleLocalization.EtalePullback
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.LocallyProjectivePurity
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.ProjectivePushforwardConverse
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.ProjectivePushforwardConverseAux
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.PurityCriterion
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.PurityCriterionLimits
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.PurityLimitStageBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.ConstructibleAssociatedPointsLocus
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.FibreComparison
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeAssassin.ContainmentConstructible
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeAssassin.FlatFibreSpecialization
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FlatLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.OpenLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.EtaleBase
public import StacksFrontier.AlgebraicGeometry.Properties.AmpleAndExtension.LocallyProjectiveCover
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationPullback

/-!
# Projective sections on an affine open after an elementary étale neighbourhood

Stacks Tag 05ME says: for `f : X ⟶ S` locally of finite presentation, `F` a quasi-coherent
`𝒪_X`-module of finite presentation and `x ∈ X` at which `F` is flat over `S`, there are an
affine elementary étale neighbourhood `(S', s') ⟶ (S, s)` and an affine open
`U' ⊆ X ×_S S'` containing `x' = (x, s')` with `Γ(U', F|_{U'})` a projective
`Γ(S', 𝒪_{S'})`-module. It is the improvement of Tag 05ID in which the chart carrying the
projective sections is an *open* of a base change rather than merely étale over `X`.

The source's proof has four inputs and one argument. The inputs are: openness of the flat locus
(Tag 0399), which shrinks `X` around `x` so that `F` is flat over `S`; finiteness of the
associated points of the fibre (Tag 05AF), which shrinks `X` further so that every point of
`Ass_{X_s}(F_s)` specializes to `x`; the affine chart of Tag 05KW, whose elementary étale
neighbourhood becomes the new base; and Tags 05MC and 05MD, which turn purity into projective
sections. The argument is the claim that for an affine open `U₀ ∋ x` inside the image of the
chart, `F|_{U₀}` is pure along `(U₀)_s`.

This file proves the argument and assembles it with Tag 05K6 and the four inputs into Tag 05ME.

## Main results

* `AlgebraicGeometry.isPureAlong_pullback_ι_of_isPureAlong_chart` is the source's claim: with
  `g : X' ⟶ X` étale over `S` such that `g^*F` is pure along `X'_s`, with `U₀ ⊆ X` an open
  neighbourhood of `x` inside the image of `g`, with `F` flat over `S` along `X_s ∩ g(X')` and
  with every point of `Ass_{X_s}(F_s) ∩ g(X')` specializing to `x`, the restriction `F|_{U₀}` is
  pure along `(U₀)_s`.
* `AlgebraicGeometry.exists_affineOpen_projective_sections_of_chart` is Tag 05ME: it produces the
  affine elementary étale neighbourhood `(S', s')` of `(S, s)`, the point `x' = (x, s')` of
  `X ×_S S'` and the affine open `U' ∋ x'` whose sections are projective over `Γ(S', 𝒪_{S'})`.
  The chart of Tag 05KW that its proof builds is what its name records.

## Implementation notes

The purity hypothesis and conclusion are `AlgebraicGeometry.IsPureAlong` applied to the
corresponding `AlgebraicGeometry.PrePureSituation`, and an impurity is unfolded directly: the
criterion of Tag 05L4 is not used, because the chart it needs is a chart of `U₀`, and its purity
input is the statement being proved.

The base `S` is shrunk to an affine open at the start, so that the chart of Tag 05KW exists and
so that Tags 05MC and 05MD apply; the neighbourhood that comes out is therefore an affine open of
an elementary étale neighbourhood of that affine open of `S`, which is again elementary étale
over `S`. The affine open of `X ×_S S'` is produced on the base change of the shrunken `X` and
transported along the resulting open immersion into `X ×_S S'`.

## References

* [Stacks Project, Tag 05ME](https://stacks.math.columbia.edu/tag/05ME)
* [Stacks Project, Tag 05KW](https://stacks.math.columbia.edu/tag/05KW)
* [Stacks Project, Tag 05L3](https://stacks.math.columbia.edu/tag/05L3)
* [Stacks Project, Tag 05K6](https://stacks.math.columbia.edu/tag/05K6)
* [Stacks Project, Tag 05KR](https://stacks.math.columbia.edu/tag/05KR)
* [Stacks Project, Tag 05MC](https://stacks.math.columbia.edu/tag/05MC)
* [Stacks Project, Tag 05MD](https://stacks.math.columbia.edu/tag/05MD)
* [Stacks Project, Tag 0399](https://stacks.math.columbia.edu/tag/0399)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 05AF](https://stacks.math.columbia.edu/tag/05AF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### The purity step -/

/-- An open subset contains every generalization of any of its points. -/
private theorem mem_of_specializes_mem_opens {X : Scheme.{u}} (U : X.Opens) {ζ x : X}
    (h : ζ ⤳ x) (hx : x ∈ U) : ζ ∈ (U : Set X) := by
  by_contra hζ
  have hsub : closure ({ζ} : Set X) ⊆ (U : Set X)ᶜ :=
    closure_minimal (Set.singleton_subset_iff.mpr hζ) U.isOpen.isClosed_compl
  exact hsub (specializes_iff_mem_closure.mp h) hx

/-- Evaluating a composite of morphisms of schemes at a point. -/
private theorem apply_eq_of_comp_eq {X Y Z : Scheme.{u}} {a : X ⟶ Y} {b : Y ⟶ Z} {e : X ⟶ Z}
    (h : a ≫ b = e) (x : X) : b (a x) = e x := by
  rw [← h]
  rfl

/-- A cartesian square whose base leg is composed with a monomorphism is again cartesian. -/
private theorem isPullback_comp_mono' {C : Type*} [Category C]
    {P X Y S T : C} {a : P ⟶ X} {b : P ⟶ Y} {q : X ⟶ S} {r : Y ⟶ S}
    (hpb : IsPullback a b q r) (i : S ⟶ T) [Mono i] :
    IsPullback a b (q ≫ i) (r ≫ i) := by
  refine IsPullback.mk' (by simpa only [Category.assoc] using congrArg (· ≫ i) hpb.w)
    (fun {_ _ _} h₁ h₂ => hpb.hom_ext h₁ h₂) ?_
  intro W c d hcd
  refine hpb.exists_lift c d ?_
  refine (cancel_mono i).mp ?_
  simpa only [Category.assoc] using hcd

/-- A base change of an open of `X` is the pullback of that open along the projection from the
base change of `X`, when the base legs are related by a monomorphism. -/
private theorem isPullback_pullback_lift' {Y X' X S' S T : Scheme.{u}} {a : Y ⟶ X'} {b : Y ⟶ T}
    {f' : X' ⟶ S'} {q : T ⟶ S'} (hpb : IsPullback a b f' q) (i : X' ⟶ X) (c : S' ⟶ S) [Mono c]
    (f : X ⟶ S) (r : T ⟶ S) (hc : f' ≫ c = i ≫ f) (hr : q ≫ c = r) (hw : (a ≫ i) ≫ f = b ≫ r) :
    IsPullback a (pullback.lift (a ≫ i) b hw) i (pullback.fst f r) := by
  subst hr
  refine IsPullback.of_bot (t := IsPullback.of_hasPullback f (q ≫ c)) ?_
    (pullback.lift_fst _ _ _).symm
  rw [pullback.lift_snd, ← hc]
  exact isPullback_comp_mono' hpb c

/-- **The purity step in the proof of Stacks Tag 05ME.** Let `f : X ⟶ S` be of finite type, let
`F` be a finite type quasi-coherent `𝒪_X`-module, let `x ∈ X` lie over `s ∈ S`, and let
`g : X' ⟶ X` be étale over `S` with `g^*F` pure along `X'_s`. Let `U₀ ⊆ X` be an open
neighbourhood of `x` contained in the image of `g`, assume `F` is flat over `S` at every point of
`X_s` lying in the image of `g`, and assume every associated point of the fibre `F_s` lying in
the image of `g` specializes to `x`. Then `F|_{U₀}` is pure along `(U₀)_s`.

Both the flatness and the specialization hypothesis are only used at points of the image of `g`,
which is where the proof finds the points it needs; in the source they hold on all of `X`, which
has been shrunk around `x` beforehand.

This is the paragraph of the source beginning "Let `U ⊆ g(X')` be an affine open neighbourhood of
`x`. We claim that `F|_U` is pure along `U_s`." An impurity of `F|_{U₀}` over an elementary étale
neighbourhood `(T, t)` of `(S, s)` is a point `ξ` of `Ass_{(U₀)_T/T}` lying over a point
specializing to `t` whose closure misses `(U₀)_t`. It is lifted to the base change `X' ×_S T` of
the chart, where purity of `g^*F` makes its closure meet the fibre, and Tag 05L3
(`Stacks.RelativeAssassin.exists_specializes_mem_associatedPoints_fibre`) upgrades the meeting
point to an associated point of the fibre of the pulled back module. Its image in `X` is then an
associated point of `F_s` by Tag 05KL
(`AlgebraicGeometry.relativeAssassin_pullback_subset_preimage`) together with the étale transfer
of the relative assassin, hence specializes to `x` by hypothesis, hence lies in `U₀`; so the
meeting point lies over `U₀` and the impurity was no impurity. -/
theorem isPureAlong_pullback_ι_of_isPureAlong_chart
    {X S X' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] (s : S) (x : X)
    (g : X' ⟶ X) [Etale g] (p : X' ⟶ S) [LocallyOfFiniteType p] [QuasiCompact p]
    (hgp : g ≫ f = p)
    (U₀ : X.Opens) [QuasiCompact (U₀.ι ≫ f)] (hxU₀ : x ∈ U₀)
    (hU₀g : (U₀ : Set X) ⊆ Set.range g.base)
    (hflat : ∀ ζ : f.fiber s, f.fiberι s ζ ∈ Set.range g.base →
      IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s ζ))
    (hpure : IsPureAlong
      ({ S := S
         X := X'
         f := p
         F := (Scheme.Modules.pullback g).obj F
         isFiniteType := SheafOfModules.pullback_isFiniteType g.toLRSHom.toShHom F
         isQuasicoherent := @SheafOfModules.modulePullback_isQuasicoherent X'.toRingedSpace
           X.toRingedSpace g.toLRSHom.toShHom F ‹F.IsQuasicoherent›
         s := s } : PrePureSituation.{u}))
    (hAss : ∀ ζ : X, ζ ∈ Stacks.Divisors.relativeAssassin f F → f ζ = s →
      ζ ∈ Set.range g.base → ζ ⤳ x) :
    IsPureAlong
      ({ S := S
         X := U₀.toScheme
         f := U₀.ι ≫ f
         F := (Scheme.Modules.pullback U₀.ι).obj F
         isFiniteType := SheafOfModules.pullback_isFiniteType U₀.ι.toLRSHom.toShHom F
         isQuasicoherent := @SheafOfModules.modulePullback_isQuasicoherent
           U₀.toScheme.toRingedSpace X.toRingedSpace U₀.ι.toLRSHom.toShHom F
           ‹F.IsQuasicoherent›
         s := s } : PrePureSituation.{u}) := by
  classical
  intro D hb helem hImp
  obtain ⟨hAssξ, hclosed⟩ := hImp
  have hFqc : F.IsQuasicoherent := inferInstance
  have : Etale D.g := hb
  have hsq : IsPullback D.toX D.toT (U₀.ι ≫ f) D.g := D.isPullback
  -- the comparison of `D.X_T` with the canonical base change `X ×_S T`
  have hjcomm : (D.toX ≫ U₀.ι) ≫ f = D.toT ≫ D.g := by
    rw [Category.assoc]; exact hsq.w
  let j : D.X_T ⟶ pullback f D.g := pullback.lift (D.toX ≫ U₀.ι) D.toT hjcomm
  have hjfst : j ≫ pullback.fst f D.g = D.toX ≫ U₀.ι := pullback.lift_fst _ _ _
  have hjsnd : j ≫ pullback.snd f D.g = D.toT := pullback.lift_snd _ _ _
  have hjpb : IsPullback D.toX j U₀.ι (pullback.fst f D.g) :=
    isPullback_pullback_lift' hsq U₀.ι (𝟙 S) f D.g (Category.comp_id _) (Category.comp_id _) hjcomm
  have : IsOpenImmersion j := MorphismProperty.of_isPullback hjpb inferInstance
  have : Etale j := inferInstance
  -- the base change of the chart
  let ZZ : Scheme.{u} := pullback g (pullback.fst f D.g)
  let π : ZZ ⟶ X' := pullback.fst g (pullback.fst f D.g)
  let m : ZZ ⟶ (pullback f D.g : Scheme.{u}) := pullback.snd g (pullback.fst f D.g)
  have hZZ : IsPullback π m g (pullback.fst f D.g) := IsPullback.of_hasPullback _ _
  have : Etale m := MorphismProperty.of_isPullback hZZ inferInstance
  have hσpb : IsPullback π (m ≫ pullback.snd f D.g) p D.g := by
    have h := IsPullback.paste_vert hZZ (IsPullback.of_hasPullback f D.g)
    rwa [hgp] at h
  -- the two modules in play on `X ×_S T` and on `ZZ`
  let FT := (Scheme.Modules.pullback (pullback.fst f D.g)).obj F
  have : FT.IsQuasicoherent :=
    @SheafOfModules.modulePullback_isQuasicoherent _ X.toRingedSpace
      (pullback.fst f D.g).toLRSHom.toShHom F hFqc
  let G := (Scheme.Modules.pullback g).obj F
  let M := (Scheme.Modules.pullback π).obj G
  have eFT : (Scheme.Modules.pullback j).obj FT ≅
      (Scheme.Modules.pullback D.toX).obj ((Scheme.Modules.pullback U₀.ι).obj F) :=
    (Scheme.Modules.pullbackComp j (pullback.fst f D.g)).app F ≪≫
      (Scheme.Modules.pullbackCongr hjfst).app F ≪≫
        ((Scheme.Modules.pullbackComp D.toX U₀.ι).app F).symm
  have eM : (Scheme.Modules.pullback m).obj FT ≅ M :=
    (Scheme.Modules.pullbackComp m (pullback.fst f D.g)).app F ≪≫
      (Scheme.Modules.pullbackCongr hZZ.w.symm).app F ≪≫
        ((Scheme.Modules.pullbackComp π g).app F).symm
  -- `ξ` seen inside `X ×_S T`
  have hξ₁ : j D.xi ∈ Stacks.Divisors.relativeAssassin (pullback.snd f D.g) FT := by
    rw [← mem_relativeAssassin_comp_iff_of_etale j (pullback.snd f D.g) FT D.xi, hjsnd,
      relativeAssassin_eq_of_moduleIso D.toT eFT]
    exact hAssξ
  -- `ξ` lifted to the base change of the chart
  have hfstξ : pullback.fst f D.g (j D.xi) = U₀.ι (D.toX D.xi) :=
    apply_eq_of_comp_eq hjfst D.xi
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : X', g x₀ = pullback.fst f D.g (j D.xi) := by
    rw [hfstξ]
    exact hU₀g (by rw [← U₀.range_ι]; exact Set.mem_range_self _)
  obtain ⟨ξ', hξ'π, hξ'm⟩ := Scheme.Pullback.exists_preimage_pullback (f := g)
    (g := pullback.fst f D.g) x₀ (j D.xi) hx₀
  have hξ'M : ξ' ∈ Stacks.Divisors.relativeAssassin (m ≫ pullback.snd f D.g) M := by
    rw [← relativeAssassin_eq_of_moduleIso (m ≫ pullback.snd f D.g) eM,
      mem_relativeAssassin_comp_iff_of_etale m (pullback.snd f D.g) FT ξ', hξ'm]
    exact hξ₁
  -- the lifted point lies over `t'`
  have hσξ' : (m ≫ pullback.snd f D.g) ξ' = D.t' := by
    change pullback.snd f D.g (m ξ') = D.t'
    rw [hξ'm, apply_eq_of_comp_eq hjsnd]
    exact D.xi_liesOver
  -- purity of the chart's module: the closure of the lifted point meets the fibre
  have hnotimp := hpure
    { T := D.T
      g := D.g
      t' := D.t'
      t := D.t
      specializes := D.specializes
      mapsToChosenPoint := D.mapsToChosenPoint
      X_T := ZZ
      toX := π
      toT := m ≫ pullback.snd f D.g
      isPullback := hσpb
      xi := ξ'
      xi_liesOver := hσξ' } hb helem
  have hmeetne : closure ({ξ'} : Set ZZ) ∩
      Set.range ((m ≫ pullback.snd f D.g).fiberι D.t) ≠ ∅ := fun h =>
    hnotimp ⟨hξ'M, h⟩
  obtain ⟨w, hwcl, hwr⟩ := Set.nonempty_iff_ne_empty.mpr hmeetne
  obtain ⟨w₁, hw₁⟩ := hwr
  -- Tag 05L3 upgrades it to an associated point of the fibre
  have : M.IsQuasicoherent := by
    have hGqc : G.IsQuasicoherent :=
      @SheafOfModules.modulePullback_isQuasicoherent X'.toRingedSpace X.toRingedSpace
        g.toLRSHom.toShHom F hFqc
    exact @SheafOfModules.modulePullback_isQuasicoherent _ X'.toRingedSpace
      π.toLRSHom.toShHom G hGqc
  have : M.IsFiniteType := by
    have hGft : G.IsFiniteType := SheafOfModules.pullback_isFiniteType g.toLRSHom.toShHom F
    exact @SheafOfModules.pullback_isFiniteType _ _ π.toLRSHom.toShHom G hGft
  have : LocallyOfFiniteType (m ≫ pullback.snd f D.g) := by
    have : LocallyOfFiniteType p := inferInstance
    exact MorphismProperty.of_isPullback hσpb inferInstance
  have hflatfib : ∀ y : (m ≫ pullback.snd f D.g).fiber D.t,
      IsFlatOverAt (m ≫ pullback.snd f D.g).toLRSHom.toShHom M
        ((m ≫ pullback.snd f D.g).fiberι D.t y) := by
    intro y
    have hz : (m ≫ pullback.snd f D.g) ((m ≫ pullback.snd f D.g).fiberι D.t y) = D.t :=
      (m ≫ pullback.snd f D.g).apply_fiberι D.t y
    have hfg : f (g (π ((m ≫ pullback.snd f D.g).fiberι D.t y))) = s := by
      have hc := apply_eq_of_comp_eq hσpb.w ((m ≫ pullback.snd f D.g).fiberι D.t y)
      rw [← hgp] at hc
      exact hc.trans ((congrArg D.g hz).trans D.mapsToChosenPoint)
    have hflatX : IsFlatOverAt f.toLRSHom.toShHom F
        (g (π ((m ≫ pullback.snd f D.g).fiberι D.t y))) := by
      have h := hflat ((f.fiberHomeo s).symm ⟨_, hfg⟩)
        (by rw [f.fiberι_fiberHomeo_symm s ⟨_, hfg⟩]; exact Set.mem_range_self _)
      rwa [f.fiberι_fiberHomeo_symm s ⟨_, hfg⟩] at h
    have hGz : IsFlatOverAt p.toLRSHom.toShHom G
        (π ((m ≫ pullback.snd f D.g).fiberι D.t y)) := by
      have h := (isFlatOverAt_pullback_iff_of_isFlatAt g f F
        (π ((m ≫ pullback.snd f D.g).fiberι D.t y))
        (Flat.stalkMap g (π ((m ≫ pullback.snd f D.g).fiberι D.t y)))).mp hflatX
      rwa [hgp] at h
    let G₀ : SheafOfModules.{u} (structureSheafRing X'.toRingedSpace) := G
    have : G₀.IsQuasicoherent := show G.IsQuasicoherent from inferInstance
    exact modulePullback_isFlatOverAt hσpb G₀ _ hGz
  obtain ⟨w₀, hw₀spec, hw₀Ass⟩ :=
    Stacks.RelativeAssassin.exists_specializes_mem_associatedPoints_fibre
      (m ≫ pullback.snd f D.g) M D.t hflatfib hξ'M
      ⟨w₁, by rw [hw₁]; exact specializes_iff_mem_closure.mpr hwcl⟩
  -- its image in `X` is an associated point of `F_s`, hence specializes to `x`
  have hwM : (m ≫ pullback.snd f D.g).fiberι D.t w₀ ∈
      Stacks.Divisors.relativeAssassin (m ≫ pullback.snd f D.g) M :=
    (Stacks.Divisors.mem_associatedPoints_fiber_iff_mem_relativeAssassin _ M D.t w₀).mp hw₀Ass
  have hwFT : m ((m ≫ pullback.snd f D.g).fiberι D.t w₀) ∈
      Stacks.Divisors.relativeAssassin (pullback.snd f D.g) FT := by
    refine (mem_relativeAssassin_comp_iff_of_etale m (pullback.snd f D.g) FT _).mp ?_
    rw [relativeAssassin_eq_of_moduleIso (m ≫ pullback.snd f D.g) eM]
    exact hwM
  have hζ : pullback.fst f D.g (m ((m ≫ pullback.snd f D.g).fiberι D.t w₀)) ∈
      Stacks.Divisors.relativeAssassin f F :=
    relativeAssassin_pullback_subset_preimage f D.g F hwFT
  have hsndw : pullback.snd f D.g (m ((m ≫ pullback.snd f D.g).fiberι D.t w₀)) = D.t :=
    (m ≫ pullback.snd f D.g).apply_fiberι D.t w₀
  have hfζ : f (pullback.fst f D.g (m ((m ≫ pullback.snd f D.g).fiberι D.t w₀))) = s := by
    exact (apply_eq_of_comp_eq (pullback.condition (f := f) (g := D.g)) _).trans
      ((congrArg D.g hsndw).trans D.mapsToChosenPoint)
  have hζg : pullback.fst f D.g (m ((m ≫ pullback.snd f D.g).fiberι D.t w₀)) ∈
      Set.range g.base := by
    exact ⟨π ((m ≫ pullback.snd f D.g).fiberι D.t w₀), apply_eq_of_comp_eq hZZ.w _⟩
  have hζU₀ : pullback.fst f D.g (m ((m ≫ pullback.snd f D.g).fiberι D.t w₀)) ∈ (U₀ : Set X) :=
    mem_of_specializes_mem_opens U₀ (hAss _ hζ hfζ hζg) hxU₀
  -- so the meeting point comes from a point of `D.X_T`
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : U₀.toScheme,
      U₀.ι u₀ = pullback.fst f D.g (m ((m ≫ pullback.snd f D.g).fiberι D.t w₀)) := by
    rw [← U₀.range_ι] at hζU₀
    exact hζU₀
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := U₀.ι)
    (g := pullback.fst f D.g) u₀ (m ((m ≫ pullback.snd f D.g).fiberι D.t w₀)) hu₀
  have hcomp : hjpb.isoPullback.inv ≫ j = pullback.snd U₀.ι (pullback.fst f D.g) :=
    hjpb.isoPullback_inv_snd
  have hjy : j (hjpb.isoPullback.inv z) =
      m ((m ≫ pullback.snd f D.g).fiberι D.t w₀) :=
    (apply_eq_of_comp_eq hcomp z).trans hz₂
  -- that point lies in the fibre over `t` and in the closure of `ξ`, a contradiction
  have hToTy : D.toT (hjpb.isoPullback.inv z) = D.t := by
    rw [← apply_eq_of_comp_eq hjsnd, hjy, hsndw]
  have hspecj : j D.xi ⤳ j (hjpb.isoPullback.inv z) := by
    rw [hjy, ← hξ'm]
    exact hw₀spec.map m.continuous
  have hspec : D.xi ⤳ hjpb.isoPullback.inv z :=
    j.isOpenEmbedding.isInducing.specializes_iff.mp hspecj
  have hfin : hjpb.isoPullback.inv z ∈ closure ({D.xi} : Set D.X_T) ∩
      Set.range (D.toT.fiberι D.t) := by
    refine ⟨specializes_iff_mem_closure.mp hspec, ?_⟩
    rw [D.toT.range_fiberι D.t]
    exact hToTy
  rw [hclosed] at hfin
  exact hfin

/-! ### The inputs of the source's proof -/

/-- **Tag 0399 in the form the source uses it.** The points at which `F` is flat over `S` form an
open set, so flatness at `x` gives an open neighbourhood of `x` on which `F` is flat over `S`. -/
private theorem exists_opens_isFlatOverAt {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (F : X.Modules) [F.IsQuasicoherent]
    [F.IsFinitePresentation] (x : X) (hflat : IsFlatOverAt f.toLRSHom.toShHom F x) :
    ∃ V : X.Opens, x ∈ V ∧ ∀ y : X, y ∈ V → IsFlatOverAt f.toLRSHom.toShHom F y :=
  ⟨⟨_, isOpen_setOf_flatOverAt f F⟩, hflat, fun _ hy => hy⟩

/-- An open neighbourhood of `x` avoiding a finite set of points none of which generalizes `x`:
the closures of the points to be avoided are finitely many closed sets missing `x`. -/
private theorem exists_opens_mem_avoiding_finite {Z : Type u} [TopologicalSpace Z] (x : Z)
    (E : Set Z) (hE : E.Finite) (hbad : ∀ y ∈ E, ¬ y ⤳ x) :
    ∃ U : TopologicalSpace.Opens Z, x ∈ U ∧ ∀ y ∈ E, y ∉ U := by
  classical
  refine Set.Finite.induction_on
    (motive := fun E _ => (∀ y ∈ E, ¬ y ⤳ x) →
      ∃ U : TopologicalSpace.Opens Z, x ∈ U ∧ ∀ y ∈ E, y ∉ U)
    E hE ?_ ?_ hbad
  · intro _
    exact ⟨⊤, by simp, by simp⟩
  · intro a t ha ht ih hbadt
    obtain ⟨U, hxU, havoid⟩ := ih (by
      intro y hy
      exact hbadt y (by simp [hy]))
    let V : TopologicalSpace.Opens Z :=
      ⟨{z | z ∉ closure ({a} : Set Z)}, isOpen_compl_iff.mpr isClosed_closure⟩
    have hxV : x ∈ V := by
      change x ∉ closure ({a} : Set Z)
      intro hxcl
      exact hbadt a (by simp) (specializes_iff_mem_closure.mpr hxcl)
    refine ⟨U ⊓ V, ⟨hxU, hxV⟩, ?_⟩
    intro y hy
    simp only [Set.mem_insert_iff] at hy
    rcases hy with hya | hy
    · subst y
      change ¬ (a ∈ U ∧ a ∈ V)
      intro hmem
      exact hmem.2 (subset_closure (Set.mem_singleton a))
    · exact fun hmem => havoid y hy hmem.1

/-- Associated points transfer along an étale morphism of locally Noetherian schemes: on such a
scheme the associated points are the weakly associated points, and those transfer by Tag 05FP. -/
private theorem mem_associatedPoints_pullback_iff_of_etale' {A B : Scheme.{u}} (q : A ⟶ B)
    [Etale q] [IsLocallyNoetherian A] [IsLocallyNoetherian B] (G : B.Modules)
    [G.IsQuasicoherent] (y : A) :
    y ∈ Stacks.Divisors.associatedPoints ((Scheme.Modules.pullback q).obj G) ↔
      q y ∈ Stacks.Divisors.associatedPoints G := by
  rw [associatedPoints_eq_weaklyAssociatedPoints A, associatedPoints_eq_weaklyAssociatedPoints B,
    Stacks.Divisors.mem_weaklyAssociatedPoints_iff,
    Stacks.Divisors.mem_weaklyAssociatedPoints_iff]
  exact isWeaklyAssociatedPoint_pullback_iff_of_etale q G y

/-- The module on the fibre of the base change along an elementary étale neighbourhood, read on
the fibre of `f` itself through
`AlgebraicGeometry.ConnectedComponentSection.elementaryFiberIso`. -/
private def elementaryFiberModuleIso' {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) {s : S}
    (N : EtaleNeighborhood S s) [IsIso N.residueFieldMap] :
    (Scheme.Modules.pullback ((pullback.snd f N.toBase).fiberι N.point)).obj
        ((Scheme.Modules.pullback (pullback.fst f N.toBase)).obj F) ≅
      (Scheme.Modules.pullback (ConnectedComponentSection.elementaryFiberIso f N).hom).obj
        ((Scheme.Modules.pullback (f.fiberι s)).obj F) :=
  (Scheme.Modules.pullbackComp ((pullback.snd f N.toBase).fiberι N.point)
      (pullback.fst f N.toBase)).app F ≪≫
    (Scheme.Modules.pullbackCongr
        (ConnectedComponentSection.elementaryFiberIso_hom_fiberι f N).symm).app F ≪≫
      ((Scheme.Modules.pullbackComp
        (ConnectedComponentSection.elementaryFiberIso f N).hom (f.fiberι s)).app F).symm

/-- A point of the fibre over the distinguished point of an elementary étale neighbourhood which
is associated to the pulled back module has an associated image in the fibre of `f` over `s`. -/
private theorem mem_associatedPoints_of_elementaryFiber {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsQuasicoherent] {s : S}
    (N : EtaleNeighborhood S s) (hN : N.IsElementary)
    (z : (pullback.snd f N.toBase).fiber N.point)
    (hz : z ∈ Stacks.Divisors.associatedPoints
      ((Scheme.Modules.pullback ((pullback.snd f N.toBase).fiberι N.point)).obj
        ((Scheme.Modules.pullback (pullback.fst f N.toBase)).obj F))) :
    (ConnectedComponentSection.elementaryFiberIso f N).hom z ∈
      Stacks.Divisors.associatedPoints ((Scheme.Modules.pullback (f.fiberι s)).obj F) := by
  let : IsIso N.residueFieldMap := hN
  have hFqc : F.IsQuasicoherent := inferInstance
  have hsnd : LocallyOfFiniteType (pullback.snd f N.toBase) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback f N.toBase) inferInstance
  let : LocallyOfFiniteType (pullback.snd f N.toBase) := hsnd
  let : IsLocallyNoetherian ((pullback.snd f N.toBase).fiber N.point) :=
    isLocallyNoetherian_fiber_of_locallyOfFiniteType (pullback.snd f N.toBase) N.point
  let : IsLocallyNoetherian (f.fiber s) := isLocallyNoetherian_fiber_of_locallyOfFiniteType f s
  let : ((Scheme.Modules.pullback (f.fiberι s)).obj F).IsQuasicoherent :=
    @SheafOfModules.modulePullback_isQuasicoherent (f.fiber s).toRingedSpace X.toRingedSpace
      (f.fiberι s).toLRSHom.toShHom F hFqc
  have hzweak : Stacks.Divisors.IsWeaklyAssociatedPoint
      ((Scheme.Modules.pullback (ConnectedComponentSection.elementaryFiberIso f N).hom).obj
        ((Scheme.Modules.pullback (f.fiberι s)).obj F)) z := by
    refine (isWeaklyAssociatedPoint_iff_of_iso (elementaryFiberModuleIso' f F N) z).mp ?_
    rw [← Stacks.Divisors.mem_weaklyAssociatedPoints_iff,
      ← associatedPoints_eq_weaklyAssociatedPoints]
    exact hz
  rw [associatedPoints_eq_weaklyAssociatedPoints (f.fiber s),
    Stacks.Divisors.mem_weaklyAssociatedPoints_iff]
  exact (isWeaklyAssociatedPoint_pullback_iff_of_etale
    (ConnectedComponentSection.elementaryFiberIso f N).hom
    ((Scheme.Modules.pullback (f.fiberι s)).obj F) z).mp hzweak

/-- An affine open neighbourhood of `q x` inside the image of an étale `q`. -/
private theorem exists_affineOpen_mem_range_of_etale' {A B : Scheme.{u}} (q : A ⟶ B) [Etale q]
    (y : A) :
    ∃ W : B.Opens, IsAffineOpen W ∧ q y ∈ W ∧
      W ≤ ⟨Set.range q.base, q.isOpenMap.isOpen_range⟩ :=
  exists_isAffineOpen_mem_and_subset
    (U := (⟨Set.range q.base, q.isOpenMap.isOpen_range⟩ : B.Opens)) (x := q y) ⟨y, rfl⟩

/-- Restricting an elementary étale neighbourhood to an open subscheme of its scheme containing
its distinguished point leaves it elementary. -/
private theorem isElementary_restrictOpen' {S : Scheme.{u}} {s : S} (N : EtaleNeighborhood S s)
    (hN : N.IsElementary) (V : N.scheme.Opens) (hV : N.point ∈ V) :
    ({ scheme := V.toScheme
       point := ⟨N.point, hV⟩
       toBase := V.ι ≫ N.toBase
       map_point := N.map_point } : EtaleNeighborhood S s).IsElementary := by
  refine (EtaleNeighborhood.isElementary_iff _).mpr ?_
  rw [Scheme.residueFieldMap_comp]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _
    ((EtaleNeighborhood.isElementary_iff N).mp hN)
    (Scheme.instIsIsoCommRingCatResidueFieldMapOfIsOpenImmersion V.ι _)

/-- Composing the structure morphism of an elementary étale neighbourhood with an open immersion
of the base gives an elementary étale neighbourhood of the larger base. -/
private theorem isElementary_comp_isOpenImmersion' {S T : Scheme.{u}} (c : S ⟶ T)
    [IsOpenImmersion c] {s : S} (N : EtaleNeighborhood S s) (hN : N.IsElementary) (t : T)
    (ht : (N.toBase ≫ c) N.point = t) :
    ({ scheme := N.scheme
       point := N.point
       toBase := N.toBase ≫ c
       map_point := ht } : EtaleNeighborhood T t).IsElementary := by
  refine (EtaleNeighborhood.isElementary_iff _).mpr ?_
  rw [Scheme.residueFieldMap_comp]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _
    (Scheme.instIsIsoCommRingCatResidueFieldMapOfIsOpenImmersion c _)
    ((EtaleNeighborhood.isElementary_iff N).mp hN)

/-- **Tag 05MD in the form the source uses it.** On an affine base, an affine morphism of finite
presentation whose finitely presented quasi-coherent module is flat over the base and pure
relative to it has projective global sections. -/
private theorem projective_sections_of_isPureRelative {X S : Scheme.{u}} (q : X ⟶ S) [IsAffine S]
    [IsAffineHom q] [LocallyOfFinitePresentation q] [QuasiCompact q] [QuasiSeparated q]
    (G : X.Modules) [G.IsQuasicoherent] [G.IsFinitePresentation] (hft : G.IsFiniteType)
    (hflat : IsFlatOver q.toLRSHom.toShHom G)
    (hpure : letI : G.IsFiniteType := hft; IsPureRelative q G) :
    Module.Projective Γ(S, ⊤) Γ((Scheme.Modules.pushforward q).obj G, ⊤) := by
  let : G.IsFiniteType := hft
  exact ((isLocallyProjective_pushforward_iff_isPureRelative q G hflat).2 hpure) ⊤
    (isAffineOpen_top S)

/-- Purity along a fibre is inherited by the base change along an open immersion of the base: an
impurity over the smaller base is an impurity over the larger one, elementariness included. -/
private theorem isPureAlong_baseChange_of_isOpenImmersion (P Q : PrePureSituation.{u})
    (q : Q.S ⟶ P.S) [IsOpenImmersion q] (a : Q.X ⟶ P.X) (hpb : IsPullback a Q.f P.f q)
    (e : Q.F ≅ (Scheme.Modules.pullback a).obj P.F)
    (hp : IsPureAlong (P.atPoint (q Q.s))) : IsPureAlong Q := by
  intro D hD hElem hImp
  let : Etale D.g := hD
  let N : EtaleNeighborhood Q.S Q.s := ⟨D.T, D.t, D.g, D.mapsToChosenPoint⟩
  let : IsIso (D.g.residueFieldMap D.t) := (EtaleNeighborhood.isElementary_iff N).mp hElem
  have hq : (D.g ≫ q) D.t = q Q.s := congrArg q D.mapsToChosenPoint
  let E : ImpurityDiagram (P.atPoint (q Q.s)) :=
    { T := D.T
      g := D.g ≫ q
      t' := D.t'
      t := D.t
      specializes := D.specializes
      mapsToChosenPoint := hq
      X_T := D.X_T
      toX := D.toX ≫ a
      toT := D.toT
      isPullback := D.isPullback.paste_horiz hpb
      xi := D.xi
      xi_liesOver := D.xi_liesOver }
  apply hp E inferInstance
  · exact isElementary_comp_isOpenImmersion' q N hElem _ hq
  · refine ⟨?_, hImp.2⟩
    rw [← relativeAssassin_eq_of_moduleIso D.toT ((Scheme.Modules.pullback D.toX).mapIso e ≪≫
      (Scheme.Modules.pullbackComp D.toX a).app P.F)]
    exact hImp.1

/-- Projective global sections on the source of an open immersion are projective sections on the
image of the open immersion: the two modules of sections agree, linearly over the base. -/
private theorem projective_sections_image_of_isOpenImmersion {Y X S : Scheme.{u}} (i : Y ⟶ X)
    [IsOpenImmersion i] (q : X ⟶ S) (F : X.Modules)
    (hproj : letI : Module Γ(S, ⊤) Γ((Scheme.Modules.pullback i).obj F, ⊤) :=
      Module.compHom _ (i ≫ q).appTop.hom
      Module.Projective Γ(S, ⊤) Γ((Scheme.Modules.pullback i).obj F, ⊤)) :
    letI : Module Γ(S, ⊤) Γ(F, i ''ᵁ ⊤) :=
      Module.compHom _ (q.appLE ⊤ (i ''ᵁ ⊤) (by simp)).hom
    Module.Projective Γ(S, ⊤) Γ(F, i ''ᵁ ⊤) := by
  let R := Γ(S, ⊤)
  let G := (Scheme.Modules.pullback i).obj F
  let : Module R Γ(F, i ''ᵁ ⊤) := Module.compHom _ (q.appLE ⊤ (i ''ᵁ ⊤) (by simp)).hom
  let : Module R Γ(G, ⊤) := Module.compHom _ (i ≫ q).appTop.hom
  let E := (Scheme.Modules.restrictFunctorIsoPullback i).app F
  let e₁ := F.restrictAppIso i ⊤
  let e₂ : Γ(F.restrict i, ⊤) ≅ Γ(G, ⊤) := asIso (E.hom.app ⊤)
  let e : Γ(F, i ''ᵁ ⊤) ≃ₗ[R] Γ(G, ⊤) :=
    { (e₁.symm ≪≫ e₂).addCommGroupIsoToAddEquiv with
      map_smul' := by
        intro r m
        change (E.hom.app ⊤) (e₁.inv ((q.appLE ⊤ (i ''ᵁ ⊤) (by simp)).hom r • m)) =
          (i ≫ q).appTop.hom r • (E.hom.app ⊤) (e₁.inv m)
        rw [Scheme.Modules.smul_restrictAppIso_inv_apply, Scheme.Modules.Hom.app_smul]
        congr 1
        have hc := Scheme.Hom.appLE_comp_appLE i q ⊤ (i ''ᵁ ⊤) ⊤
          (by simp) (i.preimage_image_eq ⊤).ge
        rw [Scheme.Hom.appIso_hom']
        change ((q.appLE ⊤ (i ''ᵁ ⊤) (by simp)) ≫
          i.appLE (i ''ᵁ ⊤) ⊤ (i.preimage_image_eq ⊤).ge).hom r = _
        rw [hc]
        exact congrArg (fun α : Γ(S, ⊤) ⟶ Γ(Y, ⊤) => α.hom r)
          (Scheme.Hom.appLE_eq_app (i ≫ q) (U := ⊤)) }
  let : Module.Projective R Γ(G, ⊤) := hproj
  exact Module.Projective.of_equiv' e.symm

/-- Projectivity of the global sections over an external base transports along an isomorphism of
modules on the source. -/
private theorem projective_sections_of_moduleIso {W T : Scheme.{u}} (r : W ⟶ T)
    {M M' : W.Modules} (e : M ≅ M')
    (hM : letI : Module Γ(T, ⊤) Γ(M, ⊤) := Module.compHom _ r.appTop.hom
      Module.Projective Γ(T, ⊤) Γ(M, ⊤)) :
    letI : Module Γ(T, ⊤) Γ(M', ⊤) := Module.compHom _ r.appTop.hom
    Module.Projective Γ(T, ⊤) Γ(M', ⊤) := by
  let : Module Γ(T, ⊤) Γ(M, ⊤) := Module.compHom _ r.appTop.hom
  let : Module Γ(T, ⊤) Γ(M', ⊤) := Module.compHom _ r.appTop.hom
  let : Module.Projective Γ(T, ⊤) Γ(M, ⊤) := hM
  exact Module.Projective.of_equiv'
    ({ (asIso (e.hom.app ⊤)).addCommGroupIsoToAddEquiv with
        map_smul' := fun c m => Scheme.Modules.Hom.app_smul e.hom (r.appTop.hom c) m } :
      Γ(M, ⊤) ≃ₗ[Γ(T, ⊤)] Γ(M', ⊤))

/-! ### Tags 05MC and 05MD: from purity along one fibre to projective sections -/

/-- **Tags 05MC and 05MD.** For an affine morphism of finite presentation between affine schemes
whose finitely presented quasi-coherent module is flat over the base and pure along the fibre over
`t`, there is an affine open `V ∋ t` of the base over which the sections of the base change are
projective.

Purity along the fibre over `t` spreads to an open neighbourhood of `t` by Tag 05MC
(`AlgebraicGeometry.isOpen_setOf_isPureAlong`, whose local constructibility input is Tag 05KR,
`Stacks.RelativeAssassin.isLocallyConstructible_fibrewiseContainment`); over an affine open `V`
inside that neighbourhood the base change is pure relative to `V`, and Tag 05MD
(`AlgebraicGeometry.isLocallyProjective_pushforward_iff_isPureRelative`) makes its sections
projective. -/
private theorem exists_affineOpen_projective_sections_of_isPureAlong {U B : Scheme.{u}}
    (q : U ⟶ B) [IsAffine U] [IsAffine B] [LocallyOfFinitePresentation q]
    (G : U.Modules) [G.IsQuasicoherent] [G.IsFinitePresentation] [G.IsFiniteType] (t : B)
    (hflat : IsFlatOver q.toLRSHom.toShHom G)
    (hpure : IsPureAlong ({ S := B, X := U, f := q, F := G, s := t } : PrePureSituation.{u})) :
    ∃ (V : B.Opens) (_ : IsAffineOpen V) (_ : t ∈ V),
      letI : Module Γ(V.toScheme, ⊤)
          Γ((Scheme.Modules.pullback (pullback.fst q V.ι)).obj G, ⊤) :=
        Module.compHom _ (pullback.snd q V.ι).appTop.hom
      Module.Projective Γ(V.toScheme, ⊤)
        Γ((Scheme.Modules.pullback (pullback.fst q V.ι)).obj G, ⊤) := by
  classical
  have hGqc : G.IsQuasicoherent := inferInstance
  let P0 : PrePureSituation.{u} := { S := B, X := U, f := q, F := G, s := t }
  let L : B.Opens :=
    ⟨{r | IsPureAlong (P0.atPoint r)}, isOpen_setOf_isPureAlong q G hflat⟩
  obtain ⟨V, hVaff, htV, hVL⟩ :=
    exists_isAffineOpen_mem_and_subset (U := L) (x := t) (show t ∈ L from hpure)
  let : IsAffine V.toScheme := hVaff
  refine ⟨V, hVaff, htV, ?_⟩
  let a2 : (pullback q V.ι : Scheme.{u}) ⟶ U := pullback.fst q V.ι
  let q2 : (pullback q V.ι : Scheme.{u}) ⟶ V.toScheme := pullback.snd q V.ι
  let G3 := (Scheme.Modules.pullback a2).obj G
  have : G3.IsQuasicoherent := isQuasicoherent_pullback_obj a2 G
  let : G3.IsFiniteType := SheafOfModules.pullback_isFiniteType a2.toLRSHom.toShHom G
  have hflat3 : IsFlatOver q2.toLRSHom.toShHom G3 :=
    @modulePullback_isFlatOver U B V.toScheme (pullback q V.ι : Scheme.{u}) q V.ι a2 q2
      (IsPullback.of_hasPullback q V.ι) G hGqc hflat
  have hpure3 : IsPureRelative q2 G3 := fun r =>
    isPureAlong_baseChange_of_isOpenImmersion P0
      ({ S := V.toScheme, X := (pullback q V.ι : Scheme.{u}), f := q2, F := G3, s := r } :
        PrePureSituation.{u}) V.ι a2 (IsPullback.of_hasPullback q V.ι) (Iso.refl _) (hVL r.2)
  exact projective_sections_of_isPureRelative q2 G3 inferInstance hflat3 hpure3

/-! ### Tag 05ME over an affine base -/

/-- **Stacks Project, Tag 05ME** for an affine morphism between affine schemes whose module is
flat over the base everywhere and all of whose associated points in the fibre over `s1`
generalize `x1`. It produces the affine elementary étale neighbourhood `(N, N.point)` of
`(S1, s1)` together with an affine scheme `W`, an open immersion `κ` of `W` into the base change
`X1 ×_{S1} N`, and a point `w` of `W` over `(x1, N.point)`, such that the global sections of the
pullback of the module to `W` are projective over `Γ(N, 𝒪_N)`.

The chart of Tag 05KW (`AlgebraicGeometry.exists_elementary_pointed_projective_cover`) is pulled
back to `X1 ×_{S1} A` along the neighbourhood `A` it produces; Tag 05K6
(`AlgebraicGeometry.isUniversallyPureRelative_of_pushforward_isLocallyProjective`) makes its
module universally pure, the claim
`AlgebraicGeometry.isPureAlong_pullback_ι_of_isPureAlong_chart` carries purity to an affine open
`U1` of the base change containing the lifted point, and Tags 05MC and 05MD finish through
`AlgebraicGeometry.exists_affineOpen_projective_sections_of_isPureAlong`. -/
private theorem exists_openImmersion_projective_sections_of_affine {X1 S1 : Scheme.{u}}
    (f1 : X1 ⟶ S1) [IsAffine X1] [IsAffine S1] [LocallyOfFinitePresentation f1]
    (G1 : X1.Modules) [G1.IsQuasicoherent] [G1.IsFinitePresentation] (x1 : X1) (s1 : S1)
    (hx1 : f1 x1 = s1) (hflat1 : IsFlatOver f1.toLRSHom.toShHom G1)
    (hgen : ∀ z : f1.fiber s1, z ∈ Stacks.Divisors.associatedPoints
      ((Scheme.Modules.pullback (f1.fiberι s1)).obj G1) → f1.fiberι s1 z ⤳ x1) :
    ∃ (N : EtaleNeighborhood S1 s1) (_ : N.IsElementary) (_ : IsAffine N.scheme)
      (W : Scheme.{u}) (_ : IsAffine W) (κ : W ⟶ (pullback f1 N.toBase : Scheme.{u}))
      (_ : IsOpenImmersion κ) (w : W),
      pullback.fst f1 N.toBase (κ w) = x1 ∧ pullback.snd f1 N.toBase (κ w) = N.point ∧
      letI : Module Γ(N.scheme, ⊤)
          Γ((Scheme.Modules.pullback (κ ≫ pullback.fst f1 N.toBase)).obj G1, ⊤) :=
        Module.compHom _ (κ ≫ pullback.snd f1 N.toBase).appTop.hom
      Module.Projective Γ(N.scheme, ⊤)
        Γ((Scheme.Modules.pullback (κ ≫ pullback.fst f1 N.toBase)).obj G1, ⊤) := by
  classical
  have hG1qc : G1.IsQuasicoherent := inferInstance
  have hG1fp : G1.IsFinitePresentation := inferInstance
  let : G1.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation G1
  let : IsAffineHom f1 := inferInstance
  -- Tag 05KW: the pointed affine chart over an affine elementary étale neighbourhood of `s1`
  have hfp1 : FinitePresentation f1 := ⟨inferInstance, inferInstance, inferInstance⟩
  have hID : ExistsElementaryEtaleNeighborhoodProjectiveSections.{u} := by
    intro X' S' f' _ F' _ _ y hfl
    exact exists_elementaryEtaleNeighborhood_projective_sections_of_isFlatOverAt f' F' y hfl
  obtain ⟨A, hAe, hAa, Y, hYa, hp, g, hgE, hcomm, hpointed, hproj⟩ :=
    exists_elementary_pointed_projective_cover hID f1 G1 s1 hfp1
      (fun z => hflat1 (f1.fiberι s1 z))
  let : IsAffine A.scheme := hAa
  let : IsAffine Y := hYa
  let : Etale g := hgE
  let : IsIso A.residueFieldMap := hAe
  let x1Fiber : f1.fiber s1 := (f1.fiberHomeo s1).symm ⟨x1, hx1⟩
  obtain ⟨y0, hy0g, hy0h⟩ := hpointed x1Fiber
  have hy0 : g y0 = x1 := by
    rw [hy0g]
    exact f1.fiberι_fiberHomeo_symm s1 ⟨x1, hx1⟩
  -- the base change along the neighbourhood, and the chart lifted into it
  let P1 : Scheme.{u} := pullback f1 A.toBase
  let fst1 : P1 ⟶ X1 := pullback.fst f1 A.toBase
  let snd1 : P1 ⟶ A.scheme := pullback.snd f1 A.toBase
  have hpb1 : IsPullback fst1 snd1 f1 A.toBase := IsPullback.of_hasPullback f1 A.toBase
  let : IsAffineHom fst1 := inferInstance
  let : IsAffine P1 := isAffine_of_isAffineHom fst1
  let FB1 : P1.Modules := (Scheme.Modules.pullback fst1).obj G1
  have : FB1.IsQuasicoherent := isQuasicoherent_pullback_obj fst1 G1
  let : FB1.IsFiniteType := SheafOfModules.pullback_isFiniteType fst1.toLRSHom.toShHom G1
  let : LocallyOfFiniteType snd1 := MorphismProperty.of_isPullback hpb1 inferInstance
  let : QuasiCompact snd1 := MorphismProperty.of_isPullback hpb1 inferInstance
  let j : Y ⟶ P1 := pullback.lift g hp hcomm.symm
  have hjfst : j ≫ fst1 = g := pullback.lift_fst _ _ _
  have hjsnd : j ≫ snd1 = hp := pullback.lift_snd _ _ _
  let : Etale j := etale_pullback_lift_of_etale f1 A.toBase g hp hcomm.symm
  let xLift : P1 := j y0
  have hxLiftFst : fst1 xLift = x1 := (apply_eq_of_comp_eq hjfst y0).trans hy0
  have hxLiftSnd : snd1 xLift = A.point := (apply_eq_of_comp_eq hjsnd y0).trans hy0h
  have hflatP1 : ∀ z : P1, IsFlatOverAt snd1.toLRSHom.toShHom FB1 z := fun z =>
    @modulePullback_isFlatOverAt X1 S1 A.scheme P1 f1 A.toBase fst1 snd1 hpb1 G1 hG1qc z
      (hflat1 (fst1 z))
  -- the associated points of the fibre of `FB1` over the distinguished point generalize `xLift`
  let eFiber := ConnectedComponentSection.elementaryFiberIso f1 A
  let xLiftFiber : snd1.fiber A.point := (snd1.fiberHomeo A.point).symm ⟨xLift, hxLiftSnd⟩
  have heFiberLift : eFiber.hom xLiftFiber = x1Fiber := by
    apply (f1.fiberι s1).isEmbedding.injective
    calc
      f1.fiberι s1 (eFiber.hom xLiftFiber) = fst1 (snd1.fiberι A.point xLiftFiber) :=
        apply_eq_of_comp_eq (ConnectedComponentSection.elementaryFiberIso_hom_fiberι f1 A) _
      _ = fst1 xLift := by rw [Scheme.Hom.fiberι_fiberHomeo_symm]
      _ = x1 := hxLiftFst
      _ = f1.fiberι s1 x1Fiber := by rw [Scheme.Hom.fiberι_fiberHomeo_symm]
  have hAssrel : ∀ ζ : P1, ζ ∈ Stacks.Divisors.relativeAssassin snd1 FB1 → snd1 ζ = A.point →
      ζ ∈ Set.range j.base → ζ ⤳ xLift := by
    intro ζ hζ hfζ _
    have hι : snd1.fiberι A.point ((snd1.fiberHomeo A.point).symm ⟨ζ, hfζ⟩) = ζ :=
      snd1.fiberι_fiberHomeo_symm A.point ⟨ζ, hfζ⟩
    have hz : (snd1.fiberHomeo A.point).symm ⟨ζ, hfζ⟩ ∈ Stacks.Divisors.associatedPoints
        ((Scheme.Modules.pullback (snd1.fiberι A.point)).obj FB1) :=
      (Stacks.Divisors.mem_associatedPoints_fiber_iff_mem_relativeAssassin snd1 FB1 A.point
        _).mpr (by rw [hι]; exact hζ)
    have hzorig := mem_associatedPoints_of_elementaryFiber f1 G1 A hAe _ hz
    have hspecY : eFiber.hom ((snd1.fiberHomeo A.point).symm ⟨ζ, hfζ⟩) ⤳ x1Fiber := by
      refine (f1.fiberι s1).isEmbedding.isInducing.specializes_iff.mp ?_
      simpa only [x1Fiber, Scheme.Hom.fiberι_fiberHomeo_symm] using hgen _ hzorig
    have hspecZ : (snd1.fiberHomeo A.point).symm ⟨ζ, hfζ⟩ ⤳ xLiftFiber := by
      refine eFiber.hom.isEmbedding.isInducing.specializes_iff.mp ?_
      simpa only [heFiberLift] using hspecY
    have hfin := hspecZ.map (snd1.fiberι A.point).continuous
    rwa [hι, show snd1.fiberι A.point xLiftFiber = xLift from
      snd1.fiberι_fiberHomeo_symm A.point ⟨xLift, hxLiftSnd⟩] at hfin
  -- Tag 05K6: the chart's projective sections make the chart's module universally pure
  let Fchart : Y.Modules := (Scheme.Modules.pullback g).obj G1
  have : Fchart.IsQuasicoherent := isQuasicoherent_pullback_obj g G1
  let : Fchart.IsFiniteType := SheafOfModules.pullback_isFiniteType g.toLRSHom.toShHom G1
  let : IsAffineHom hp := inferInstance
  have hhLFT : LocallyOfFiniteType (hp ≫ A.toBase) := by rw [hcomm]; infer_instance
  let : LocallyOfFiniteType hp := locallyOfFiniteType_of_comp hp A.toBase
  have hUnivPure : IsUniversallyPureRelative hp Fchart :=
    isUniversallyPureRelative_of_pushforward_isLocallyProjective hp Fchart
      (isLocallyProjective_pushforward_of_projective_sections hp Fchart (by exact hproj))
  let eJ : (Scheme.Modules.pullback j).obj FB1 ≅ Fchart :=
    (Scheme.Modules.pullbackComp j fst1).app G1 ≪≫ (Scheme.Modules.pullbackCongr hjfst).app G1
  -- the claim: purity on an affine open neighbourhood of the lifted point
  obtain ⟨U1, hU1aff, hxU1, hU1sub⟩ := exists_affineOpen_mem_range_of_etale' j y0
  let : IsAffine U1.toScheme := hU1aff
  have hU1pure := isPureAlong_pullback_ι_of_isPureAlong_chart snd1 FB1 A.point xLift j hp hjsnd
    U1 hxU1 (by exact hU1sub) (fun ζ _ => hflatP1 _)
    (by
      intro D hD hElem hImp
      refine hUnivPure A.point
        ({ T := D.T
           g := D.g
           t' := D.t'
           t := D.t
           specializes := D.specializes
           mapsToChosenPoint := D.mapsToChosenPoint
           X_T := D.X_T
           toX := D.toX
           toT := D.toT
           isPullback := D.isPullback
           xi := D.xi
           xi_liesOver := D.xi_liesOver } : ImpurityDiagram
             ({ S := A.scheme, X := Y, f := hp, F := Fchart, s := A.point } :
               PrePureSituation.{u})) ⟨?_, hImp.2⟩
      rw [← relativeAssassin_eq_of_moduleIso D.toT ((Scheme.Modules.pullback D.toX).mapIso eJ)]
      exact hImp.1)
    hAssrel
  -- Tags 05MC and 05MD
  let f2 := U1.ι ≫ snd1
  let G2 := (Scheme.Modules.pullback U1.ι).obj FB1
  have : G2.IsQuasicoherent := isQuasicoherent_pullback_obj U1.ι FB1
  let : G2.IsFiniteType := SheafOfModules.pullback_isFiniteType U1.ι.toLRSHom.toShHom FB1
  have hflat2 : IsFlatOver f2.toLRSHom.toShHom G2 := fun y =>
    (isFlatOverAt_pullback_ι_iff snd1 U1 FB1 y).mpr (hflatP1 (U1.ι y))
  obtain ⟨V, hVaff, htV, hproj3⟩ :=
    exists_affineOpen_projective_sections_of_isPureAlong f2 G2 A.point hflat2 hU1pure
  let : IsAffine V.toScheme := hVaff
  -- the neighbourhood is shrunk to `V`, and the base change of `U1` is the required open
  let N : EtaleNeighborhood S1 s1 :=
    ⟨V.toScheme, ⟨A.point, htV⟩, V.ι ≫ A.toBase, A.map_point⟩
  have hN : N.IsElementary := isElementary_restrictOpen' A hAe V htV
  let a2 : (pullback f2 V.ι : Scheme.{u}) ⟶ U1.toScheme := pullback.fst f2 V.ι
  let q2 : (pullback f2 V.ι : Scheme.{u}) ⟶ V.toScheme := pullback.snd f2 V.ι
  let : IsAffineHom f2 := inferInstance
  let : IsAffineHom q2 := inferInstance
  let : IsAffine (pullback f2 V.ι : Scheme.{u}) := isAffine_of_isAffineHom q2
  let k1 : (pullback f2 V.ι : Scheme.{u}) ⟶ (pullback snd1 V.ι : Scheme.{u}) :=
    pullback.lift (a2 ≫ U1.ι) q2
      (by simpa only [Category.assoc] using (IsPullback.of_hasPullback f2 V.ι).w)
  have hk1a : k1 ≫ pullback.fst snd1 V.ι = a2 ≫ U1.ι := pullback.lift_fst _ _ _
  have hk1b : k1 ≫ pullback.snd snd1 V.ι = q2 := pullback.lift_snd _ _ _
  have hk1pb : IsPullback a2 k1 U1.ι (pullback.fst snd1 V.ι) :=
    isPullback_pullback_lift' (IsPullback.of_hasPullback f2 V.ι) U1.ι (𝟙 A.scheme) snd1 V.ι
      (Category.comp_id _) (Category.comp_id _) _
  let : IsOpenImmersion k1 := MorphismProperty.of_isPullback hk1pb inferInstance
  let eZ : (pullback snd1 V.ι : Scheme.{u}) ≅ (pullback f1 N.toBase : Scheme.{u}) :=
    pullbackLeftPullbackSndIso f1 A.toBase V.ι
  let κ : (pullback f2 V.ι : Scheme.{u}) ⟶ (pullback f1 N.toBase : Scheme.{u}) := k1 ≫ eZ.hom
  have hZf : eZ.hom ≫ pullback.fst f1 N.toBase = pullback.fst snd1 V.ι ≫ fst1 :=
    pullbackLeftPullbackSndIso_hom_fst f1 A.toBase V.ι
  have hZs : eZ.hom ≫ pullback.snd f1 N.toBase = pullback.snd snd1 V.ι :=
    pullbackLeftPullbackSndIso_hom_snd f1 A.toBase V.ι
  have hκfst : κ ≫ pullback.fst f1 N.toBase = (a2 ≫ U1.ι) ≫ fst1 := by
    simp only [show κ = k1 ≫ eZ.hom from rfl, Category.assoc, hZf, reassoc_of% hk1a]
  have hκsnd : κ ≫ pullback.snd f1 N.toBase = q2 := by
    simp only [show κ = k1 ≫ eZ.hom from rfl, Category.assoc, hZs, hk1b]
  obtain ⟨w, hwa, hwq⟩ := Scheme.Pullback.exists_preimage_pullback (f := f2) (g := V.ι)
    (⟨xLift, hxU1⟩ : U1.toScheme) (⟨A.point, htV⟩ : V.toScheme) hxLiftSnd
  refine ⟨N, hN, inferInstance, (pullback f2 V.ι : Scheme.{u}), inferInstance, κ,
    inferInstance, w, ?_, ?_, ?_⟩
  · change (κ ≫ pullback.fst f1 N.toBase) w = x1
    rw [hκfst]
    change fst1 (U1.ι (a2 w)) = x1
    rw [hwa]
    exact hxLiftFst
  · change (κ ≫ pullback.snd f1 N.toBase) w = N.point
    rw [hκsnd]
    exact hwq
  · rw [hκsnd]
    refine projective_sections_of_moduleIso q2 ?_ hproj3
    refine (Scheme.Modules.pullbackComp a2 U1.ι).app
      ((Scheme.Modules.pullback fst1).obj G1) ≪≫ ?_
    refine (Scheme.Modules.pullbackComp (a2 ≫ U1.ι) fst1).app G1 ≪≫ ?_
    exact (Scheme.Modules.pullbackCongr hκfst.symm).app G1

/-! ### Tag 05ME -/

/-- **Stacks Project, Tag 05ME.** Let `f : X ⟶ S` be locally of finite presentation, let `F` be a
quasi-coherent `𝒪_X`-module of finite presentation, and let `x ∈ X` lie over `s ∈ S` with `F` flat
over `S` at `x`. Then there are an affine elementary étale neighbourhood `(S', s') ⟶ (S, s)` and
an affine open `U' ⊆ X ×_S S'` containing `x' = (x, s')` such that `Γ(U', F|_{U'})` is a
projective `Γ(S', 𝒪_{S'})`-module.

The chart whose name this declaration carries is the one of Tag 05KW, built inside
`AlgebraicGeometry.exists_openImmersion_projective_sections_of_affine` after `X` has been shrunk
twice: by openness of the flat locus, Tag 0399 (`AlgebraicGeometry.isOpen_setOf_flatOverAt`), and
by finiteness of the associated points of the fibre, Tag 05AF
(`AlgebraicGeometry.associatedPoints_inter_finite`), which removes the ones not generalizing `x`.
The affine open produced over the shrunken `X` is transported to `X ×_S S'` along the resulting
open immersion. -/
@[stacks 05ME]
theorem exists_affineOpen_projective_sections_of_chart
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation]
    (s : S) (x : X) (hxs : f x = s) (hflat : IsFlatOverAt f.toLRSHom.toShHom F x) :
    ∃ (N : EtaleNeighborhood S s) (_ : N.IsElementary) (_ : IsAffine N.scheme)
      (x' : (pullback f N.toBase : Scheme.{u}))
      (_ : pullback.fst f N.toBase x' = x)
      (_ : pullback.snd f N.toBase x' = N.point)
      (U' : (pullback f N.toBase : Scheme.{u}).Opens)
      (_ : IsAffineOpen U') (_ : x' ∈ U'),
      let G := (Scheme.Modules.pullback (pullback.fst f N.toBase)).obj F
      letI : Module Γ(N.scheme, ⊤) Γ(G, U') :=
        Module.compHom Γ(G, U') ((pullback.snd f N.toBase).appLE ⊤ U' (by simp)).hom
      Module.Projective Γ(N.scheme, ⊤) Γ(G, U') := by
  subst hxs
  classical
  have hFqc : F.IsQuasicoherent := inferInstance
  -- Tag 0399 shrinks `X` to an open on which `F` is flat over `S`; `S` is shrunk to an affine
  -- open and `X` to an affine open over it.
  obtain ⟨Vflat, hxflat, hflatOn⟩ := exists_opens_isFlatOverAt f F x hflat
  obtain ⟨Sopen, hSaff, hsS, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := S) (x := f x) (U := ⊤) (by simp)
  have hxCand : x ∈ Vflat ⊓ f ⁻¹ᵁ Sopen := ⟨hxflat, by simpa using hsS⟩
  obtain ⟨Xopen, hXaff, hxXopen, hXsub⟩ := exists_isAffineOpen_mem_and_subset hxCand
  have hXsub' : Xopen ≤ f ⁻¹ᵁ Sopen := fun y hy => (hXsub hy).2
  let : IsAffine Xopen.toScheme := hXaff
  let : IsAffine Sopen.toScheme := hSaff
  let f0 := f.resLE Sopen Xopen hXsub'
  let G0 := (Scheme.Modules.pullback Xopen.ι).obj F
  let x0 : Xopen.toScheme := ⟨x, hxXopen⟩
  let s0 : Sopen.toScheme := f0 x0
  have hG0qc : G0.IsQuasicoherent :=
    @SheafOfModules.modulePullback_isQuasicoherent Xopen.toScheme.toRingedSpace X.toRingedSpace
      Xopen.ι.toLRSHom.toShHom F hFqc
  let : G0.IsQuasicoherent := hG0qc
  let : LocallyOfFinitePresentation f0 := by dsimp only [f0]; infer_instance
  let : IsAffineHom f0 := inferInstance
  let : QuasiCompact f0 := inferInstance
  let : QuasiSeparated f0 := inferInstance
  let : LocallyOfFiniteType f0 := inferInstance
  have hf0ι : f0 ≫ Sopen.ι = Xopen.ι ≫ f := by
    simp [f0]
  have hflat0 : ∀ y : Xopen.toScheme, IsFlatOverAt f0.toLRSHom.toShHom G0 y := by
    intro y
    refine (isFlatOverAt_comp_iff_of_etale f0 Sopen.ι G0 y).mp ?_
    rw [hf0ι]
    exact (isFlatOverAt_pullback_ι_iff f Xopen F y).mpr (hflatOn (Xopen.ι y) (hXsub y.2).1)
  -- Tag 05AF: the associated points of the fibre are finitely many, so `X` can be shrunk again
  -- so that all of them generalize `x`.
  let Gs := (Scheme.Modules.pullback (f0.fiberι s0)).obj G0
  have : Gs.IsQuasicoherent :=
    @SheafOfModules.modulePullback_isQuasicoherent (f0.fiber s0).toRingedSpace
      Xopen.toScheme.toRingedSpace (f0.fiberι s0).toLRSHom.toShHom G0 hG0qc
  let : Gs.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation Gs
  let : IsLocallyNoetherian (f0.fiber s0) :=
    isLocallyNoetherian_fiber_of_locallyOfFiniteType f0 s0
  let : Gs.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isQuasicoherent_isFiniteType Gs
  have hAssFin : (Stacks.Divisors.associatedPoints Gs).Finite := by
    simpa using associatedPoints_inter_finite Gs ⊤ isCompact_univ
  obtain ⟨Otop, hxO, hOavoid⟩ :=
    exists_opens_mem_avoiding_finite x0
      (f0.fiberι s0 '' {z | z ∈ Stacks.Divisors.associatedPoints Gs ∧ ¬ f0.fiberι s0 z ⤳ x0})
      ((hAssFin.subset fun z hz => hz.1).image _) (by rintro y ⟨z, hz, rfl⟩; exact hz.2)
  let O : Xopen.toScheme.Opens := ⟨Otop, Otop.2⟩
  obtain ⟨X1, hX1aff, hxX1, hX1sub⟩ :=
    exists_isAffineOpen_mem_and_subset (U := O) (x := x0) hxO
  let i : X1.toScheme ⟶ Xopen.toScheme := X1.ι
  let f1 : X1.toScheme ⟶ Sopen.toScheme := i ≫ f0
  let G1 : X1.toScheme.Modules := (Scheme.Modules.pullback i).obj G0
  let x1 : X1.toScheme := ⟨x0, hxX1⟩
  have hG1qc : G1.IsQuasicoherent :=
    @SheafOfModules.modulePullback_isQuasicoherent X1.toScheme.toRingedSpace
      Xopen.toScheme.toRingedSpace i.toLRSHom.toShHom G0 hG0qc
  let : IsAffine X1.toScheme := hX1aff
  let : G1.IsQuasicoherent := hG1qc
  let : LocallyOfFinitePresentation f1 := inferInstance
  let : LocallyOfFiniteType f1 := inferInstance
  have hflat1 : IsFlatOver f1.toLRSHom.toShHom G1 := fun y =>
    (isFlatOverAt_pullback_ι_iff f0 X1 G0 y).mpr (hflat0 (X1.ι y))
  -- every associated point of the fibre of `G1` generalizes `x1`
  let : IsLocallyNoetherian (f1.fiber s0) :=
    isLocallyNoetherian_fiber_of_locallyOfFiniteType f1 s0
  have hix : i x1 = x0 := rfl
  have hgen : ∀ z : f1.fiber s0, z ∈ Stacks.Divisors.associatedPoints
      ((Scheme.Modules.pullback (f1.fiberι s0)).obj G1) → f1.fiberι s0 z ⤳ x1 := by
    intro z hz
    let : Etale (fiberMapOfSource i f0 s0) :=
      MorphismProperty.of_isPullback (fiberMapOfSource_isPullback i f0 s0).flip inferInstance
    have hz' : z ∈ Stacks.Divisors.associatedPoints
        ((Scheme.Modules.pullback (fiberMapOfSource i f0 s0)).obj Gs) := by
      rw [Stacks.Divisors.associatedPoints_congr (fiberModuleIsoOfSource i f0 G0 s0)]
      exact hz
    have hm : fiberMapOfSource i f0 s0 z ∈ Stacks.Divisors.associatedPoints Gs :=
      (mem_associatedPoints_pullback_iff_of_etale' (fiberMapOfSource i f0 s0) Gs z).mp hz'
    have hmPoint : f0.fiberι s0 (fiberMapOfSource i f0 s0 z) = i (f1.fiberι s0 z) :=
      apply_eq_of_comp_eq (fiberMapOfSource_fiberι i f0 s0) z
    have hInO : f0.fiberι s0 (fiberMapOfSource i f0 s0 z) ∈ O := by
      rw [hmPoint]
      exact hX1sub (f1.fiberι s0 z).2
    have hspec0 : f0.fiberι s0 (fiberMapOfSource i f0 s0 z) ⤳ x0 := by
      by_contra hns
      exact hOavoid _ ⟨fiberMapOfSource i f0 s0 z, ⟨hm, hns⟩, rfl⟩ hInO
    have hspecMap : i (f1.fiberι s0 z) ⤳ i x1 := by
      rw [← hmPoint, hix]
      exact hspec0
    exact i.isOpenEmbedding.isInducing.specializes_iff.mp hspecMap
  -- Tag 05ME over the affine base
  obtain ⟨N0, hN0, hN0aff, W, hWaff, κ, hκ, w, hκx, hκt, hκproj⟩ :=
    exists_openImmersion_projective_sections_of_affine f1 G1 x1 s0 rfl hflat1 hgen
  let : IsAffine N0.scheme := hN0aff
  let : IsAffine W := hWaff
  let : IsOpenImmersion κ := hκ
  -- the neighbourhood of `(S, f x)` and the open immersion into `X ×_S S'`
  let j0 : X1.toScheme ⟶ X := i ≫ Xopen.ι
  have hj0 : f1 ≫ Sopen.ι = j0 ≫ f := by
    dsimp only [f1, j0]
    rw [Category.assoc, hf0ι]
    simp only [Category.assoc]
  have hn : (N0.toBase ≫ Sopen.ι) N0.point = f x := by
    change Sopen.ι (N0.toBase N0.point) = f x
    rw [N0.map_point]
    change (f1 ≫ Sopen.ι) x1 = f x
    rw [hj0]
    rfl
  let N : EtaleNeighborhood S (f x) :=
    ⟨N0.scheme, N0.point, N0.toBase ≫ Sopen.ι, hn⟩
  have hN : N.IsElementary :=
    isElementary_comp_isOpenImmersion' Sopen.ι N0 hN0 (f x) hn
  let az : (pullback f1 N0.toBase : Scheme.{u}) ⟶ X1.toScheme := pullback.fst f1 N0.toBase
  let bz : (pullback f1 N0.toBase : Scheme.{u}) ⟶ N0.scheme := pullback.snd f1 N0.toBase
  have hwz : (az ≫ j0) ≫ f = bz ≫ (N0.toBase ≫ Sopen.ι) := by
    have hc : az ≫ f1 = bz ≫ N0.toBase := pullback.condition
    simp only [Category.assoc, ← hj0, reassoc_of% hc]
  let kz : (pullback f1 N0.toBase : Scheme.{u}) ⟶ (pullback f N.toBase : Scheme.{u}) :=
    pullback.lift (az ≫ j0) bz hwz
  let : IsOpenImmersion kz :=
    MorphismProperty.of_isPullback
      (isPullback_pullback_lift' (IsPullback.of_hasPullback f1 N0.toBase) j0 Sopen.ι f N.toBase
        hj0 rfl hwz) inferInstance
  have hkzf : kz ≫ pullback.fst f N.toBase = az ≫ j0 := pullback.lift_fst _ _ _
  have hkzs : kz ≫ pullback.snd f N.toBase = bz := pullback.lift_snd _ _ _
  let k : W ⟶ (pullback f N.toBase : Scheme.{u}) := κ ≫ kz
  have hkfst : (κ ≫ az) ≫ j0 = k ≫ pullback.fst f N.toBase := by
    simp only [show k = κ ≫ kz from rfl, Category.assoc, hkzf]
  have hksnd : k ≫ pullback.snd f N.toBase = κ ≫ bz := by
    simp only [show k = κ ≫ kz from rfl, Category.assoc, hkzs]
  have hkx : pullback.fst f N.toBase (k w) = x := by
    change (k ≫ pullback.fst f N.toBase) w = x
    rw [← hkfst]
    change Xopen.ι (i (az (κ w))) = x
    rw [hκx]
    rfl
  have hkt : pullback.snd f N.toBase (k w) = N.point := by
    change (k ≫ pullback.snd f N.toBase) w = N.point
    rw [hksnd]
    exact hκt
  refine ⟨N, hN, inferInstance, k w, hkx, hkt, k ''ᵁ (⊤ : W.Opens),
    (isAffineOpen_top W).image_of_isOpenImmersion k, ⟨w, by simp, rfl⟩, ?_⟩
  refine projective_sections_image_of_isOpenImmersion k (pullback.snd f N.toBase)
    ((Scheme.Modules.pullback (pullback.fst f N.toBase)).obj F) ?_
  rw [hksnd]
  refine projective_sections_of_moduleIso (κ ≫ bz) ?_ hκproj
  refine (Scheme.Modules.pullback (κ ≫ az)).mapIso
    ((Scheme.Modules.pullbackComp i Xopen.ι).app F) ≪≫ ?_
  refine (Scheme.Modules.pullbackComp (κ ≫ az) j0).app F ≪≫ ?_
  refine (Scheme.Modules.pullbackCongr hkfst).app F ≪≫ ?_
  exact ((Scheme.Modules.pullbackComp k (pullback.fst f N.toBase)).app F).symm

end AlgebraicGeometry

end
