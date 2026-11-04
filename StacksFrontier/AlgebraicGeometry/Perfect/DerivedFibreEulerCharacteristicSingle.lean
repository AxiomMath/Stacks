module

public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreEulerCharacteristicRank
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentFrom.Affine
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedChernSetup
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.RankZero
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.IntegralPerfectComplex
public import StacksFrontier.AlgebraicGeometry.Perfect.GenericFreeCohomology

/-!
# The Euler characteristic of a finite locally free module in degree zero

Let `W` be a scheme and `M` a finite locally free `𝒪_W`-module, of a rank allowed to vary from
point to point. The derived-fibre Euler characteristic of `M` placed in degree `0` takes at a
point `w` the value of the rank of `M` near `w`. Consequently an object of `D(𝒪_W)` isomorphic to
such an `M[0]` whose derived-fibre Euler characteristic vanishes everywhere is zero: the rank of
`M` is `0` near every point, so `M` is zero.

This is the step "the assumption on rank implies that `E₂|_{X₁ ∩ X₂}` is zero" in the proof of
[Stacks, Tag 0FAN].

## Main results

* `Stacks.Chow.isZero_of_isFiniteLocallyFreeOfRankLT_one`: a finite locally free module of rank
  `< 1` everywhere is zero.
* `AlgebraicGeometry.DerivedFibreBetti.chiDerivedFibre_singleFunctor_eq_of_restrict`: the
  derived-fibre Euler characteristic of `M[0]` at a point of an open on which `M` has rank `r`
  is `r`.
* `AlgebraicGeometry.DerivedFibreBetti.isZero_of_iso_singleFunctor_of_chiDerivedFibre_eq_zero`:
  an object of `D(𝒪_W)` isomorphic to a finite locally free module in degree `0` with vanishing
  derived-fibre Euler characteristic is zero.
* `AlgebraicGeometry.DerivedFibreBetti.isZero_derivedPullback_of_chiDerivedFibre_eq_zero`: the
  same for the derived pullback of a perfect object of Euler characteristic `0`.

## Implementation notes

The rank hypothesis is `Stacks.Chow.IsFiniteLocallyFreeOfRankLT`, which states the rank near a
point on the ringed-space restriction `W.toRingedSpace.restrict U.isOpenEmbedding`; this is
definitionally the open subscheme `U`, which is where the rank computation for bounded complexes
of finite locally free modules,
`AlgebraicGeometry.DerivedFibreBetti.chiDerivedFibre_eq_of_bounded_finiteLocallyFreeOfRank`, is
applied, after base change along the open immersion `U ⟶ W`.

## References

* [Stacks Project, Tag 0FAN](https://stacks.math.columbia.edu/tag/0FAN)
* [Stacks Project, Tag 0BDJ](https://stacks.math.columbia.edu/tag/0BDJ)
* [Stacks Project, Tag 0BDI](https://stacks.math.columbia.edu/tag/0BDI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-- **A finite locally free module of rank everywhere `< 1` is zero.** Near each point it is
finite locally free of rank `0`, hence zero there, and vanishing is local. -/
theorem isZero_of_isFiniteLocallyFreeOfRankLT_one {W : Scheme.{u}} {M : W.Modules}
    (hM : IsFiniteLocallyFreeOfRankLT (X := W.toRingedSpace) M 1) : IsZero M := by
  choose U hU r hr hrank using hM.2
  refine RingedSpace.isZero_of_restrictModules W.toRingedSpace M U (fun x => ⟨x, hU x⟩)
    fun x => ?_
  have hx := hrank x
  rw [Nat.lt_one_iff.mp (hr x)] at hx
  exact @isZero_of_isFiniteLocallyFreeOfRank_zero (Scheme.Opens.toScheme (X := W) (U x)) _ hx

end Stacks.Chow

namespace AlgebraicGeometry.DerivedFibreBetti

attribute [local instance] HasDerivedCategory.standard

/-- **The derived-fibre Euler characteristic of a finite locally free module in degree `0` is its
rank.** If the restriction of the `𝒪_W`-module `M` to an open `U` is finite locally free of rank
`r`, the derived-fibre Euler characteristic of `M[0]` is `r` at every point of `U`.

Base change along the open immersion `U ⟶ W` (Tag 0BDI) reduces to `U`, where `M[0]` restricts to
the one-term complex `M|_U[0]`, whose terms are finite locally free of ranks `r` in degree `0` and
`0` elsewhere. -/
theorem chiDerivedFibre_singleFunctor_eq_of_restrict (W : Scheme.{u}) (M : W.Modules)
    (hpc : RingedSpace.IsPseudoCoherent (X := W.toRingedSpace)
      ((DerivedCategory.singleFunctor _ 0).obj M))
    (U : W.Opens) (r : ℕ)
    (hr : SheafOfModules.IsFiniteLocallyFreeOfRank
        (R := StrictlyPerfect.structureSheafOfRings (W.toRingedSpace.restrict U.isOpenEmbedding))
        ((RingedSpace.PseudoCoherence.restrictModules W.toRingedSpace U).obj M) r)
    (w : W) (hw : w ∈ U) :
    chiDerivedFibre W ((DerivedCategory.singleFunctor _ 0).obj M) hpc w = r := by
  classical
  let P : CochainComplex W.Modules ℤ :=
    (HomologicalComplex.single W.Modules (ComplexShape.up ℤ) 0).obj M
  let eQ : (DerivedCategory.singleFunctor _ 0).obj M ≅ DerivedCategory.Q.obj P :=
    (DerivedCategory.singleFunctorIsoCompQ _ 0).app M
  have hpcP : RingedSpace.IsPseudoCoherent (X := W.toRingedSpace) (DerivedCategory.Q.obj P) :=
    hpc.of_iso eQ
  let PU := RingedSpace.restrictComplex P U
  let eModel : (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      U.ι.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj PU :=
    derivedPullbackOpenQIso (X := W.toRingedSpace) U P
  have hpcU : RingedSpace.IsPseudoCoherent (X := U.toScheme.toRingedSpace)
      (DerivedCategory.Q.obj PU) :=
    (isPseudoCoherent_derivedPullback U.ι (DerivedCategory.Q.obj P) hpcP).of_iso eModel
  have hzero (i : ℤ) (hi : i ≠ 0) : IsZero (PU.X i) :=
    Functor.map_isZero (RingedSpace.restrictModules W.toRingedSpace U)
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M i hi)
  have hbounded : {i : ℤ | ¬ IsZero (PU.X i)}.Finite :=
    (Set.finite_singleton (0 : ℤ)).subset fun i hi =>
      Classical.byContradiction fun h => hi (hzero i h)
  let rk : ℤ → ℕ := fun i => if i = 0 then r else 0
  have hrank (i : ℤ) : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (PU.X i) (rk i) := by
    by_cases hi : i = 0
    · subst hi
      simp only [rk, ite_true]
      exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
        ((RingedSpace.restrictModules W.toRingedSpace U).mapIso
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M)).symm hr
    · simp only [rk, ite_eq_right hi]
      exact isFiniteLocallyFreeOfRank_zero_of_isZero (Y := U.toScheme) (M := PU.X i) (hzero i hi)
  calc chiDerivedFibre W ((DerivedCategory.singleFunctor _ 0).obj M) hpc w
      = chiDerivedFibre W (DerivedCategory.Q.obj P) hpcP w :=
        congrFun (chiDerivedFibre_congr W hpc hpcP eQ) w
    _ = chiDerivedFibre U.toScheme
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            U.ι.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P))
          (isPseudoCoherent_derivedPullback U.ι _ hpcP) ⟨w, hw⟩ :=
        (congrFun (chiDerivedFibre_derivedPullback U.ι (DerivedCategory.Q.obj P) hpcP)
          ⟨w, hw⟩).symm
    _ = chiDerivedFibre U.toScheme _ hpcU ⟨w, hw⟩ :=
        congrFun (chiDerivedFibre_congr U.toScheme _ hpcU eModel) ⟨w, hw⟩
    _ = ∑ᶠ i : ℤ, (i.negOnePow : ℤ) * (rk i : ℤ) :=
        chiDerivedFibre_eq_of_bounded_finiteLocallyFreeOfRank U.toScheme PU hbounded rk hrank
          hpcU ⟨w, hw⟩
    _ = r := by
        rw [finsum_eq_single _ (0 : ℤ) fun i hi => by simp [rk, hi]]
        simp [rk]

/-- **An object isomorphic to a finite locally free module in degree `0` with Euler
characteristic `0` is zero.** Let `E` be a pseudo-coherent object of `D(𝒪_W)` isomorphic to `M[0]`
for a finite locally free `𝒪_W`-module `M` (of rank `< p` near every point), and suppose the
derived-fibre Euler characteristic of `E` vanishes everywhere. Then `E` is zero.

Near each point the Euler characteristic of `E` is the local rank of `M`, which is therefore `0`;
so `M` is zero, and so is `E ≅ M[0]`. -/
theorem isZero_of_iso_singleFunctor_of_chiDerivedFibre_eq_zero (W : Scheme.{u})
    {E : DerivedCategory W.Modules} (hE : RingedSpace.IsPseudoCoherent (X := W.toRingedSpace) E)
    {M : W.Modules} {p : ℕ}
    (hM : Stacks.Chow.IsFiniteLocallyFreeOfRankLT (X := W.toRingedSpace) M p)
    (e : E ≅ (DerivedCategory.singleFunctor _ 0).obj M)
    (hchi : ∀ w : W, chiDerivedFibre W E hE w = 0) :
    IsZero E := by
  have hpc : RingedSpace.IsPseudoCoherent (X := W.toRingedSpace)
      ((DerivedCategory.singleFunctor _ 0).obj M) :=
    hE.of_iso e
  have hM₁ : Stacks.Chow.IsFiniteLocallyFreeOfRankLT (X := W.toRingedSpace) M 1 := by
    refine ⟨hM.1, fun w => ?_⟩
    obtain ⟨U, hw, r, -, hr⟩ := hM.2 w
    refine ⟨U, hw, r, ?_, hr⟩
    have h : (0 : ℤ) = r :=
      (hchi w).symm.trans ((congrFun (chiDerivedFibre_congr W hE hpc e) w).trans
        (chiDerivedFibre_singleFunctor_eq_of_restrict W M hpc U r hr w hw))
    omega
  exact (Functor.map_isZero _ (Stacks.Chow.isZero_of_isFiniteLocallyFreeOfRankLT_one hM₁)).of_iso e

/-- **A derived pullback of rank `0` which is a finite locally free module in degree `0` is zero.**
Let `E` be a perfect object of `D(𝒪_Y)` whose derived-fibre Euler characteristic vanishes
everywhere and `z : W ⟶ Y` a morphism such that `Lz^* E` is isomorphic to a finite locally free
module of rank `< p` placed in degree `0`. Then `Lz^* E` is zero.

The Euler characteristic of `Lz^* E` is that of `E` composed with `z` (Tag 0BDI), hence `0`. -/
theorem isZero_derivedPullback_of_chiDerivedFibre_eq_zero {W Y : Scheme.{u}} (z : W ⟶ Y)
    (E : DerivedCategory Y.Modules) (hE : RingedSpace.IsPerfect.{u, u + 1} E)
    (hchi : ∀ y : Y, chiDerivedFibre Y E (isPseudoCoherent_of_isPerfect E hE) y = 0) {p : ℕ}
    (h : ∃ M : W.Modules, Stacks.Chow.IsFiniteLocallyFreeOfRankLT M p ∧
      Nonempty ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        z.toLRSHom.toShHom).obj E ≅ (DerivedCategory.singleFunctor _ 0).obj M)) :
    IsZero ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      z.toLRSHom.toShHom).obj E) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := h
  refine isZero_of_iso_singleFunctor_of_chiDerivedFibre_eq_zero W
    (isPseudoCoherent_derivedPullback z E (isPseudoCoherent_of_isPerfect E hE)) hM e fun w => ?_
  rw [chiDerivedFibre_derivedPullback]
  exact hchi (z.base w)

end AlgebraicGeometry.DerivedFibreBetti

end
