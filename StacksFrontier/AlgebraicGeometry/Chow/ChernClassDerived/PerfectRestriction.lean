module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedChernSetup
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.EnvelopeChern
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TwistByInvertible
public import StacksFrontier.AlgebraicGeometry.FiberRank.ConstantRank
public import StacksFrontier.AlgebraicGeometry.Perfect.GenericFreeCohomology

/-!
# Restriction of the Chern classes of a perfect object, and vanishing above the rank

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `E` be an object
of `D(𝒪_X)` whose Chern classes are defined (Stacks 0F9E). This file records two properties of
the total Chern class `c(E)` of Stacks 0GUD used for the localized Chern classes of Stacks 0F9H:

* for a morphism `h : Z ⟶ X` locally of finite type, `c(E)|_Z = c(Lh^*E)`, the Chern classes of
  `Lh^*E` being defined by Stacks 0GUE (5);
* if `E` is isomorphic to a finite locally free module of rank `< p` placed in degree `0`, then
  `c_p(E) = 0`.

## Main definitions

* `Stacks.Chow.EnvelopePresentation.basePullback` — an envelope presentation of `E` pulled back
  to a presentation of `Lh^*E`.

## Main results

* `Stacks.Chow.res_perfectChernClass_derivedPullback` — `c(E)|_Z = c(Lh^*E)`.
* `Stacks.Chow.perfectChernClass_apply_eq_zero_of_iso_single` — `c_p(E) = 0` if `E` is a finite
  locally free module of rank `< p` in degree `0`.
* `Stacks.Chow.TotalChowClass.apply_eq_zero_of_res_apply_eq_zero` and
  `Stacks.Chow.TotalChowClass.apply_eq_zero_of_res_apply_eq_zero_of_isEnvelope` — a component of
  a total class vanishing on the pieces of a decomposition, or on an envelope, vanishes.

## References

* [Stacks Project, Tag 0GUD](https://stacks.math.columbia.edu/tag/0GUD)
* [Stacks Project, Tag 0GUE](https://stacks.math.columbia.edu/tag/0GUE)
* [Stacks Project, Tag 0F9E](https://stacks.math.columbia.edu/tag/0F9E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ZeroObject

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The components of a total class -/

namespace TotalChowClass

variable {C : ChowSituation.{u}} {Y Y' : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]

/-- The total class obtained by replacing one component by `0`. -/
def eraseComponent (c : TotalChowClass C sY) (p : ℕ) : TotalChowClass C sY :=
  fun q ↦ if q = p then 0 else c q

/-- The `p`-th component of `eraseComponent c p` is `0`. -/
theorem eraseComponent_apply_self (c : TotalChowClass C sY) (p : ℕ) :
    eraseComponent c p p = 0 := by
  simp [eraseComponent]

/-- For `q ≠ p`, the `q`-th component of `eraseComponent c p` is the `q`-th component of `c`. -/
theorem eraseComponent_apply_of_ne (c : TotalChowClass C sY) {p q : ℕ} (h : q ≠ p) :
    eraseComponent c p q = c q := by
  simp [eraseComponent, h]

/-- If the restriction of the `p`-th component of `c` along `h` vanishes, erasing that component
does not change the restriction. -/
theorem res_eraseComponent (h : Y' ⟶ Y) [LocallyOfFiniteType h] (c : TotalChowClass C sY)
    (p : ℕ) (hp : res h rfl c p = 0) : res h rfl (eraseComponent c p) = res h rfl c := by
  refine ext fun q ↦ ?_
  rw [res_rfl_apply, res_rfl_apply]
  by_cases hq : q = p
  · subst hq
    rw [eraseComponent_apply_self, map_zero, ← res_rfl_apply, hp]
  · rw [eraseComponent_apply_of_ne c hq]

/-- A component vanishes if erasing it does not change the class. -/
private theorem apply_eq_zero_of_eraseComponent_eq (c : TotalChowClass C sY) {p : ℕ}
    (hc : eraseComponent c p = c) : c p = 0 := by
  rw [← hc, eraseComponent_apply_self]

/-- **A component vanishing on the pieces of a decomposition vanishes.** -/
theorem apply_eq_zero_of_res_apply_eq_zero {I : Type u} {U : I → Y.Opens}
    (hU : IsClopenDecomposition U) (c : TotalChowClass C sY) (p : ℕ)
    (h : ∀ i, res (U i).ι rfl c p = 0) : c p = 0 := by
  exact apply_eq_zero_of_eraseComponent_eq c
    (eq_of_res_eq hU fun i ↦ res_eraseComponent (U i).ι c p (h i))

/-- **A component vanishing after restriction along an envelope vanishes.** -/
theorem apply_eq_zero_of_res_apply_eq_zero_of_isEnvelope (f : Y' ⟶ Y) [LocallyOfFiniteType f]
    (hf : IsEnvelope f) (c : TotalChowClass C sY) (p : ℕ) (h : res f rfl c p = 0) : c p = 0 := by
  exact apply_eq_zero_of_eraseComponent_eq c
    (res_injective_of_isEnvelope f hf rfl (res_eraseComponent f c p h))

end TotalChowClass

/-! ### Restriction of the Chern classes of a perfect object -/

section Pullback

variable {X Z : Scheme.{u}} {E : DerivedCategory X.Modules}

/-- The termwise pullback of a presenting complex along the base change of the envelope
represents the derived pullback of the object. -/
theorem EnvelopePresentation.basePullback_representation (H : EnvelopePresentation E)
    (h : Z ⟶ X) :
    Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (pullback.snd H.f h).toLRSHom.toShHom).obj
        ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback h.toLRSHom.toShHom).obj E) ≅
      DerivedCategory.Q.obj (pullbackComplex (pullback.fst H.f h) H.P)) := by
  obtain ⟨j⟩ := H.representation
  let p := pullback.fst H.f h
  let q := pullback.snd H.f h
  have hsq : q.toLRSHom.toShHom ≫ h.toLRSHom.toShHom =
      p.toLRSHom.toShHom ≫ H.f.toLRSHom.toShHom :=
    congrArg (fun f => f.toLRSHom.toShHom) (pullback.condition (f := H.f) (g := h)).symm
  exact ⟨(Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
        q.toLRSHom.toShHom h.toLRSHom.toShHom).app E ≪≫
      (eqToIso (Cohomology.DerivedPullbackAlongIso.derivedPullback_eq_of_eq hsq)).app E ≪≫
      ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
        p.toLRSHom.toShHom H.f.toLRSHom.toShHom).app E).symm ≪≫
      (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        p.toLRSHom.toShHom).mapIso j ≪≫
      Cohomology.derivedPullbackIsoPullbackOfKFlat p.toLRSHom.toShHom H.P
        (Stacks.BlowUpComplexes.kFlatComplex_of_isLocallyBoundedFiniteLocallyFree H.P
          H.locallyBounded)⟩

/-- **The pullback of an envelope presentation along a morphism to the base.** If `(f, 𝓔^•)`
presents `E`, then the base change of `f` along `h : Z ⟶ X`, with the termwise pullback of `𝓔^•`,
presents `Lh^*E`. -/
def EnvelopePresentation.basePullback (H : EnvelopePresentation E) (h : Z ⟶ X) :
    EnvelopePresentation
      ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback h.toLRSHom.toShHom).obj E) where
  Y := pullback H.f h
  f := pullback.snd H.f h
  envelope := isEnvelope_isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback H.f h) H.envelope
  P := pullbackComplex (pullback.fst H.f h) H.P
  locallyBounded :=
    Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback _ H.P H.locallyBounded
  representation := H.basePullback_representation h

variable (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **The Chern classes of a perfect object commute with restriction**: for `h : Z ⟶ X` locally
of finite type, the restriction of `c(E)` to `Z` is `c(Lh^*E)`. Both restrict on the envelope
`Y ×_X Z ⟶ Z` to the total Chern class of the pulled back presenting complex. -/
theorem res_perfectChernClass_derivedPullback (h : Z ⟶ X) [LocallyOfFiniteType h]
    (hE : HasDefinedChernClasses E)
    (hE' : HasDefinedChernClasses
      ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback h.toLRSHom.toShHom).obj E)) :
    TotalChowClass.res h rfl (perfectChernClass C sX hE) = perfectChernClass C (h ≫ sX) hE' := by
  set H := hE.some
  have hs' : pullback.fst H.f h ≫ H.f ≫ sX = pullback.snd H.f h ≫ h ≫ sX := by
    rw [← Category.assoc, pullback.condition, Category.assoc]
  refine eq_perfectChernClass C (h ≫ sX) hE' (H.basePullback h) ?_
  change TotalChowClass.res (pullback.snd H.f h) rfl
      (TotalChowClass.res h rfl (perfectChernClass C sX hE)) =
    complexChern C (pullback.snd H.f h ≫ h ≫ sX)
      (Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback _ H.P H.locallyBounded)
  rw [TotalChowClass.res_res, TotalChowClass.res_congr pullback.condition.symm _
      (by rw [Category.assoc, hs']),
    ← TotalChowClass.res_res H.f rfl (pullback.fst H.f h) hs',
    res_perfectChernClass C sX hE H, res_complexChern]

end Pullback

/-! ### The Chern classes of a finite locally free module of small rank -/

section SmallRank

variable (C : ChowSituation.{u}) {Z : Scheme.{u}}

/-- On an open on which it is finite locally free of rank `r`, a module has fibre rank `r`. -/
theorem fiberRank_eq_of_isFiniteLocallyFreeOfRank_restrictModules (M : Z.Modules) (U : Z.Opens)
    (r : ℕ) (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((RingedSpace.restrictModules Z.toRingedSpace U).obj M) r) {x : Z} (hx : x ∈ U) :
    Scheme.Modules.fiberRank M x = r := by
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.restrictFunctor U.ι).obj M) r :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      ((Stacks.AlgebraicGeometry.PerfectCohomology.restrictModulesIsoRestrict Z U).app M) h
  exact (Stacks.FiniteLocallyFree.Reduced.fiberRank_restrict U.ι M ⟨x, hx⟩).symm.trans
    (Scheme.Modules.fiberRank_eq_of_isFiniteLocallyFreeOfRank _ r _)

/-- A finite locally free module of rank `< p` has fibre rank `< p` at every point. -/
theorem fiberRank_lt_of_isFiniteLocallyFreeOfRankLT (M : Z.Modules) {p : ℕ}
    (hM : IsFiniteLocallyFreeOfRankLT M p) (x : Z) : Scheme.Modules.fiberRank M x < p := by
  obtain ⟨U, hxU, r, hr, h⟩ := hM.2 x
  exact (fiberRank_eq_of_isFiniteLocallyFreeOfRank_restrictModules M U r h hxU).trans_lt hr

/-- A zero module is finite locally free. -/
private theorem isFiniteLocallyFree_of_isZero {M : Z.Modules} (h : IsZero M) :
    SheafOfModules.IsFiniteLocallyFree (R := StrictlyPerfect.structureSheafOfRings
        Z.toRingedSpace) M :=
  SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree (r := 0)
    (hM := isFiniteLocallyFreeOfRank_zero_of_isZero h) _

/-- The complex `M[0]` of a finite locally free module is a locally bounded complex of finite
locally free modules. -/
theorem isLocallyBoundedFiniteLocallyFree_singleZero (M : Z.Modules)
    (hfl : SheafOfModules.IsFiniteLocallyFree (R := StrictlyPerfect.structureSheafOfRings
        Z.toRingedSpace) M) :
    IsLocallyBoundedFiniteLocallyFree (singleZero M) := by
  refine ⟨fun n ↦ ?_, fun x ↦ ⟨⊤, trivial, 0, 0, fun n hn ↦ Functor.map_isZero _
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M n (by omega))⟩⟩
  by_cases hn : n = 0
  · subst hn
    exact hfl
  · exact isFiniteLocallyFree_of_isZero
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M n hn)

/-- **The Chern classes of `M[0]` vanish above the rank**: if `M` is finite locally free of rank
`< p`, the degree `p` component of the total Chern class of the complex `M[0]` is zero. On each
rank locus the complex is `M` of some constant rank `r < p` in degree `0`, whose total Chern class
`c(M)` has no component above `r`. -/
theorem complexChern_singleZero_apply_eq_zero (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
    (M : Z.Modules) {p : ℕ} (hrank : ∀ x, Scheme.Modules.fiberRank M x < p)
    (hP : IsLocallyBoundedFiniteLocallyFree (singleZero M)) :
    complexChern C sZ hP p = 0 := by
  refine TotalChowClass.apply_eq_zero_of_res_apply_eq_zero
    (isClopenDecomposition_complexRankLoci hP) _ p fun ρ ↦ ?_
  rw [res_complexChern_complexRankLocus]
  rcases isEmpty_or_nonempty (complexRankLocus hP ρ.down) with hρ | ⟨⟨x, hx⟩⟩
  · have := TotalChowClass.subsingleton_of_isEmpty ((complexRankLocus hP ρ.down).ι ≫ sZ)
    rw [Subsingleton.elim (complexChernBounded C _ _ _ _) 0, TotalChowClass.zero_apply]
  · have hxρ : complexRank hP x = ρ.down := (mem_complexRankLocus hP).mp hx
    have hrank' : ∀ n, ρ.down n = Scheme.Modules.fiberRank ((singleZero M).X n) x := fun n ↦ by
      rw [← hxρ, complexRank_apply]
    have hzero : ∀ n ∉ ({0} : Finset ℤ), ρ.down n = 0 := fun n hn ↦ by
      rw [hrank' n]
      exact fiberRank_eq_zero_of_isZero_restrictModules _ ⊤ (Functor.map_isZero _
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M n
          (by simpa using hn))) trivial
    have := isFiniteLocallyFreeOfRank_complexRankLocus hP ρ.down 0
    rw [complexChernBounded_eq_prod C _ _ ρ.down _ {0} hzero]
    simp only [complexChernProd, Finset.sort_singleton, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, complexChernFactor, Int.negOnePow_zero,
      Units.val_one, zpow_one, val_totalChernUnit]
    exact totalChern_apply_of_lt C _ _ _ ((hrank' 0).trans_lt (hrank x))

/-- **The rank consideration**: if `E` is isomorphic to a finite locally free module whose fibre
ranks are `< p`, sitting in degree `0`, and its Chern classes are defined, then `c_p(E) = 0`. -/
theorem perfectChernClass_apply_eq_zero_of_iso_single_of_fiberRank_lt (sZ : Z ⟶ C.S)
    [LocallyOfFiniteType sZ] {E : DerivedCategory Z.Modules} (hE : HasDefinedChernClasses E)
    (M : Z.Modules) (hfl : SheafOfModules.IsFiniteLocallyFree (R :=
        StrictlyPerfect.structureSheafOfRings Z.toRingedSpace) M) {p : ℕ} (hrank : ∀ x,
        Scheme.Modules.fiberRank M x < p)
    (e : E ≅ (DerivedCategory.singleFunctor Z.Modules 0).obj M) :
    perfectChernClass C sZ hE p = 0 := by
  have hP := isLocallyBoundedFiniteLocallyFree_singleZero M hfl
  let H₀ : EnvelopePresentation E :=
    ⟨Z, 𝟙 Z, ⟨inferInstance, isCompletelyDecomposed_id Z⟩, singleZero M, hP,
      ⟨(Cohomology.DerivedPullbackAlongIso.derivedPullbackIdIso Z.toRingedSpace).app E ≪≫ e ≪≫
        (DerivedCategory.singleFunctorIsoCompQ Z.Modules 0).app M⟩⟩
  refine TotalChowClass.apply_eq_zero_of_res_apply_eq_zero_of_isEnvelope (𝟙 Z) H₀.envelope _ p ?_
  rw [res_perfectChernClass C sZ hE H₀]
  exact complexChern_singleZero_apply_eq_zero C _ M hrank hP

/-- **Stacks 0F9H, the rank consideration**: if `E` is isomorphic to a finite locally free module
of rank `< p` sitting in degree `0` and its Chern classes are defined, then `c_p(E) = 0`. -/
theorem perfectChernClass_apply_eq_zero_of_iso_single (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
    {E : DerivedCategory Z.Modules} (hE : HasDefinedChernClasses E) (M : Z.Modules) {p : ℕ}
    (hM : IsFiniteLocallyFreeOfRankLT M p)
    (e : E ≅ (DerivedCategory.singleFunctor Z.Modules 0).obj M) :
    perfectChernClass C sZ hE p = 0 :=
  perfectChernClass_apply_eq_zero_of_iso_single_of_fiberRank_lt C sZ hE M hM.1
    (fiberRank_lt_of_isFiniteLocallyFreeOfRankLT M hM) e

/-- **The Chern classes of a zero object**: if `E` is zero, its Chern classes of positive degree
vanish. -/
theorem perfectChernClass_apply_eq_zero_of_isZero (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
    {E : DerivedCategory Z.Modules} (hE : HasDefinedChernClasses E) (hzero : IsZero E) {p : ℕ}
    (hp : 0 < p) : perfectChernClass C sZ hE p = 0 := by
  have := isFiniteLocallyFreeOfRank_zero_of_isZero (isZero_zero Z.Modules)
  exact perfectChernClass_apply_eq_zero_of_iso_single_of_fiberRank_lt C sZ hE 0
    (isFiniteLocallyFree_of_isZero (isZero_zero _))
    (fun x ↦ (Scheme.Modules.fiberRank_eq_of_isFiniteLocallyFreeOfRank (0 : Z.Modules) 0 x).trans_lt
      hp) (hzero.iso (Functor.map_isZero _ (isZero_zero _)))

end SmallRank

end Stacks.Chow

end
