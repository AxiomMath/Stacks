module

public import StacksFrontier.AlgebraicGeometry.DerivedTildePerfect
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Rank
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreBettiSemicontinuity
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentStandardModel
public import StacksFrontier.AlgebraicGeometry.Perfect.SingleDegreeRankOpenBetti
public import StacksFrontier.Homology.Perfect.SingleDegreeFibre
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback

/-!
# From concentrated derived-fibre Betti numbers to the single-degree rank locus

Let `X` be a scheme, `E` a perfect object of the derived category of sheaves of modules on `X`,
`i` an integer and `r` a natural number, and let `U = singleDegreeRankOpen E i r` be the largest
open subscheme of `X` on which `E` is a finite locally free module of rank `r` placed in degree
`i`. This file proves the converse of the pointwise description of `U` through the derived-fibre
Betti numbers of [stacks 0BDI]: a point at which

`β_j(x) = 0` for `j ≠ i`, and `β_i(x) = r`

lies in `U`. Together with the forward half of
`StacksFrontier/AlgebraicGeometry/Perfect/SingleDegreeRankOpenBetti.lean` this pins the points of
`U`.

This is the half of the pointwise description which uses perfectness of `E`, and it is the step
the proof of [stacks 0BDK] takes when it quotes the local structure theorem for perfect complexes
over a local ring ([stacks 0BCD], More on Algebra, Lemma 15.77.7).

## Main results

* `AlgebraicGeometry.tildeULiftFreeIso`: the derived sheafification of a finite free module of
  rank `n`, in the `ULift (Fin n → S)` spelling the local structure theorem produces, is the free
  sheaf on `ULift (Fin n)`.
* `AlgebraicGeometry.isFiniteLocallyFreeOfRank_tilde_uliftFree`: that sheaf is finite locally free
  of rank `n`.
* `Scheme.Modules.exists_away_derivedPullback_iso_singleFunctor_of_derivedFiberBetti`:
  on an affine scheme `Spec R`, a prime at which the derived-fibre Betti numbers of a perfect `E`
  are concentrated in degree `i` with value `r` has a principal open neighbourhood on which the
  derived pullback of `E` is a finite locally free module of rank `r` placed in degree `i`.
* `AlgebraicGeometry.Scheme.Modules.mem_singleDegreeRankOpen_of_derivedFiberBetti`: the converse
  half of the pointwise description of `U`, on an arbitrary scheme.

## Implementation notes

*The route.* The assertion is local on `X`, so the point is taken inside an affine open entered
through `AlgebraicGeometry.IsAffineOpen.fromSpec`, exactly as part (2) of [stacks 0BDI] is reduced
to the affine case in
`StacksFrontier/AlgebraicGeometry/Perfect/DerivedFibreBettiSemicontinuity.lean`. Three
statements then move the hypothesis to the module side and the conclusion back:

* perfectness and pseudo-coherence survive the derived pullback to the chart
  (`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback`, [stacks 09UA],
  and `AlgebraicGeometry.DerivedFibreBetti.isPseudoCoherent_derivedPullback`, [stacks 0BDI]
  part (1)), and the Betti numbers are unchanged
  (`AlgebraicGeometry.DerivedFibreBetti.derivedFiberBetti_derivedPullback`);
* on `Spec R` a pseudo-coherent object is a derived sheafification
  (`AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory`, the standard-model half of
  [stacks 06Z0], fed by [stacks 08E5]), perfectness crosses to the module side by [stacks 08EB]
  (`AlgebraicGeometry.isPerfect_tilde_iff`) and the Betti numbers become the module-theoretic ones
  by `AlgebraicGeometry.DerivedFibreBetti.derivedFiberBetti_eq_fibreBetti`;
* the local structure theorem
  `StacksDraft.Perfect.exists_away_iso_singleFunctor_free_of_fibre_concentrated` produces an
  `f ∉ p` and an identification over `R_f`, and [stacks 08DW] part (2) in the standard model
  (`AlgebraicGeometry.StandardModel.affinePullbackComparison`) carries it to the derived pullback
  along `Spec R_f ⟶ Spec R`.

*Why the free module needs its own isomorphism.* The local structure theorem states its conclusion
with the module `ULift (Fin n → R_f)`, which is free of rank `n` but is not the `Finsupp` that
Mathlib's `AlgebraicGeometry.tildeFinsupp` compares with the free sheaf. `tildeULiftFreeIso`
interposes the linear equivalence, after which
`AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_free_of_equiv` gives the rank.

*The rank.* The rank in the conclusion of the local structure theorem is the fibre dimension
`β_i(p)` rather than the prescribed `r`. Rather than rewrite inside a type, the free module is
kept at that dimension and the hypothesis `β_i(p) = r` is used only to rewrite the `Prop`
`IsFiniteLocallyFreeOfRank _ _`, where `r` occurs as an ordinary argument.

*The model of the derived categories.* Everything is at
`CategoryTheory.HasDerivedCategory.standard`, seated at priority `10000`: the global instance
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` is of the same class and wins at the default
priority, which silently puts the objects at the locally small model. That is the warning
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineDerivedEquivalenceStandard.lean` records.

These results carry no Stacks attribute: they are steps of the proof of [stacks 0BDK], not clauses
of its statement.

## References

* [The Stacks Project, Lemma 36.31.3 (0BDK)](https://stacks.math.columbia.edu/tag/0BDK)
* [The Stacks Project, Lemma 36.31.1 (0BDI)](https://stacks.math.columbia.edu/tag/0BDI)
* [The Stacks Project, Lemma 15.77.7 (0BCD)](https://stacks.math.columbia.edu/tag/0BCD)
* [The Stacks Project, Lemma 36.10.7 (08EB)](https://stacks.math.columbia.edu/tag/08EB)
* [The Stacks Project, Lemma 36.5.3 (08DW)](https://stacks.math.columbia.edu/tag/08DW)
* [The Stacks Project, Lemma 36.3.5 (06Z0)](https://stacks.math.columbia.edu/tag/06Z0)
* [The Stacks Project, Lemma 36.21.1 (09UA)](https://stacks.math.columbia.edu/tag/09UA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars)

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The derived sheafification of a finite free module -/

/-- The `S`-module `ULift (Fin n → S)` is the finitely supported functions on `ULift (Fin n)`. -/
def uliftFunLinearEquivFinsupp (S : CommRingCat.{u}) (n : ℕ) :
    ULift.{u} (Fin n → (S : Type u)) ≃ₗ[(S : Type u)]
      (ULift.{u} (Fin n) →₀ (S : Type u)) :=
  ULift.moduleEquiv.trans
    ((Finsupp.linearEquivFunOnFinite (S : Type u) (S : Type u) (Fin n)).symm.trans
      (Finsupp.domLCongr Equiv.ulift.symm))

/-- **The derived sheafification of a finite free module of rank `n` is the free sheaf.** The
module is written `ULift (Fin n → S)`, the spelling the local structure theorem for perfect
complexes produces; `AlgebraicGeometry.tildeFinsupp` compares the `Finsupp` spelling with the free
sheaf, and `uliftFunLinearEquivFinsupp` is the linear equivalence between the two. -/
def tildeULiftFreeIso (S : CommRingCat.{u}) (n : ℕ) :
    (tilde.functor S).obj (ModuleCat.of (S : Type u) (ULift.{u} (Fin n → (S : Type u)))) ≅
      SheafOfModules.free.{u} (ULift.{u} (Fin n)) :=
  (tilde.functor S).mapIso (uliftFunLinearEquivFinsupp S n).toModuleIso ≪≫
    tildeFinsupp (R := S) (ULift.{u} (Fin n))

/-- **The derived sheafification of a finite free module of rank `n` is finite locally free of
rank `n`.** -/
theorem isFiniteLocallyFreeOfRank_tilde_uliftFree (S : CommRingCat.{u}) (n : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((tilde.functor S).obj
        (ModuleCat.of (S : Type u) (ULift.{u} (Fin n → (S : Type u))))) n :=
  Scheme.Modules.isFiniteLocallyFreeOfRankSheaf_of_iso (tildeULiftFreeIso S n).symm
    (SheafOfModules.isFiniteLocallyFreeOfRank_free_of_equiv (X := Spec S)
      (ULift.{u} (Fin n)) n Equiv.ulift)

/-! ### Transporting a single-degree identification over `R_g` to the derived pullback -/

/-- **[Stacks 08DW] part (2) applied to a single-degree identification over a localization.** If
derived extension of scalars along `R ⟶ R_g` carries `M` to a module `L` placed in degree `i`, then
derived pullback along `Spec R_g ⟶ Spec R` carries `M̃` to `L̃` placed in degree `i`.

The first step is the affine comparison square
`AlgebraicGeometry.StandardModel.affinePullbackComparison`, the second transports the given
identification along derived sheafification, and the third is Mathlib's
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor` for the exact functor
`AlgebraicGeometry.tilde.functor`. -/
def derivedPullbackAwayTildeSingleIso (R : CommRingCat.{u})
    (M : DerivedCategory (ModuleCat.{u} R)) (g : (R : Type u)) (i : ℤ)
    (L : ModuleCat.{u} (CommRingCat.of (Localization.Away g)))
    (eg : (totalDerivedExtensionScalars.{u, u, u}
          (algebraMap (R : Type u) (Localization.Away g))).functor.obj M ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} (Localization.Away g)) i).obj L) :
    (derivedPullback (Spec.map (CommRingCat.ofHom
          (algebraMap (R : Type u) (Localization.Away g)))).toLRSHom.toShHom).obj
        ((tilde.functor R).mapDerivedCategory.obj M) ≅
      (DerivedCategory.singleFunctor
          (Spec (CommRingCat.of (Localization.Away g))).Modules i).obj
        ((tilde.functor (CommRingCat.of (Localization.Away g))).obj L) :=
  (StandardModel.affinePullbackComparison R (CommRingCat.of (Localization.Away g))
      (CommRingCat.ofHom (algebraMap (R : Type u) (Localization.Away g)))).app M ≪≫
    (tilde.functor (CommRingCat.of (Localization.Away g))).mapDerivedCategory.mapIso eg ≪≫
      ((tilde.functor (CommRingCat.of (Localization.Away g))).mapDerivedCategorySingleFunctor
        i).app L

/-! ### A perfect object on an affine scheme is a derived sheafification of a perfect module -/

/-- **A perfect object of `D(𝒪_{Spec R})` is the derived sheafification of a perfect object of
`D(R)`.** Pseudo-coherence makes the cohomology sheaves quasi-coherent ([stacks 08E5]), which on an
affine scheme is exactly being a derived sheafification ([stacks 06Z0]), and perfectness crosses to
the module side by [stacks 08EB]. -/
theorem exists_isPerfect_iso_mapDerivedCategory_tilde (R : CommRingCat.{u})
    (E : DerivedCategory (Spec R).Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec R).toRingedSpace) E)
    (hPC : RingedSpace.IsPseudoCoherent.{u, u + 1} (X := (Spec R).toRingedSpace) E) :
    ∃ M : DerivedCategory (ModuleCat.{u} R),
      StacksDraft.Perfect.IsPerfect M ∧
        Nonempty ((tilde.functor R).mapDerivedCategory.obj M ≅ E) := by
  obtain ⟨M, ⟨e⟩⟩ := StandardModel.exists_iso_mapDerivedCategory R E
    (isQuasicoherentDerived_of_isPseudoCoherent (Spec R) E hPC)
  refine ⟨M, (isPerfect_tilde_iff M).1 ?_, ⟨e⟩⟩
  exact Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso.{u, u + 1} e.symm hE

/-- **The derived-fibre Betti function of an object presented as a derived sheafification is the
module-theoretic one.** This is
`AlgebraicGeometry.DerivedFibreBetti.derivedFiberBetti_eq_fibreBetti` read at a point. -/
theorem derivedFiberBetti_eq_fibreBetti_of_iso (R : CommRingCat.{u})
    (M : DerivedCategory (ModuleCat.{u} R)) (E : DerivedCategory (Spec R).Modules)
    (hPC : RingedSpace.IsPseudoCoherent.{u, u + 1} (X := (Spec R).toRingedSpace) E)
    (e : (tilde.functor R).mapDerivedCategory.obj M ≅ E) (j : ℤ) (q : Spec R) :
    DerivedFibreBetti.derivedFiberBetti (Spec R) E hPC j q =
      StacksDraft.Perfect.fibreBetti.{u, u} M j q :=
  congrFun (DerivedFibreBetti.derivedFiberBetti_eq_fibreBetti R E hPC j M e) q

namespace Scheme.Modules

/-! ### The affine step -/

/-- **On an affine scheme, concentrated derived-fibre Betti numbers give a principal neighbourhood
on which `E` is a finite locally free module of rank `r` in degree `i`.** Let `R` be a commutative
ring, `E` a perfect object of `D(𝒪_{Spec R})`, `i` an integer, `r` a natural number and `p` a point
of `Spec R` at which the derived-fibre Betti numbers of `E` vanish outside degree `i` and take the
value `r` in degree `i`. Then there is an `g ∈ R` outside `p` such that the derived pullback of `E`
along `Spec R_g ⟶ Spec R` is isomorphic to a finite locally free module of rank `r` placed in
degree `i`.

Pseudo-coherence of `E` makes it a derived sheafification `M̃` on the affine scheme, perfectness
crosses to `M` by [stacks 08EB] and the Betti numbers become the module-theoretic ones; the local
structure theorem [stacks 0BCD] then supplies `g` and an identification of `M ⊗ᴸ_R R_g` with a
finite free module placed in degree `i`, which [stacks 08DW] part (2) carries to the derived
pullback. -/
theorem exists_away_derivedPullback_iso_singleFunctor_of_derivedFiberBetti
    (R : CommRingCat.{u}) (E : DerivedCategory (Spec R).Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := (Spec R).toRingedSpace) E)
    (hPC : RingedSpace.IsPseudoCoherent.{u, u + 1} (X := (Spec R).toRingedSpace) E)
    (i : ℤ) (r : ℕ) (p : Spec R)
    (hvanish : ∀ j : ℤ, j ≠ i → DerivedFibreBetti.derivedFiberBetti (Spec R) E hPC j p = 0)
    (hrank : DerivedFibreBetti.derivedFiberBetti (Spec R) E hPC i p = r) :
    ∃ g : (R : Type u),
      g ∉ p.asIdeal ∧
        ∃ N : (Spec (CommRingCat.of (Localization.Away g))).Modules,
          AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N r ∧
            Nonempty ((derivedPullback
                (Spec.map (CommRingCat.ofHom
                  (algebraMap (R : Type u) (Localization.Away g)))).toLRSHom.toShHom).obj E ≅
              (DerivedCategory.singleFunctor
                (Spec (CommRingCat.of (Localization.Away g))).Modules i).obj N) := by
  have : p.asIdeal.IsPrime := p.isPrime
  obtain ⟨M, hMperf, ⟨e⟩⟩ := exists_isPerfect_iso_mapDerivedCategory_tilde R E hE hPC
  have hbetti : ∀ j : ℤ,
      DerivedFibreBetti.derivedFiberBetti (Spec R) E hPC j p =
        StacksDraft.Perfect.fibreBetti.{u, u} M j p := fun j =>
    derivedFiberBetti_eq_fibreBetti_of_iso R M E hPC e j p
  have hvan' : ∀ j : ℤ, j ≠ i →
      Module.finrank p.asIdeal.ResidueField
        (StacksDraft.Perfect.derivedFibreHomology.{u, u} p.asIdeal M j) = 0 := by
    intro j hj
    exact (hbetti j).symm.trans (hvanish j hj)
  have hrank' : Module.finrank p.asIdeal.ResidueField
      (StacksDraft.Perfect.derivedFibreHomology.{u, u} p.asIdeal M i) = r :=
    (hbetti i).symm.trans hrank
  obtain ⟨g, hg, ⟨eg⟩⟩ :=
    StacksDraft.Perfect.exists_away_iso_singleFunctor_free_of_fibre_concentrated.{u, u}
      p.asIdeal M hMperf i hvan'
  rw [hrank'] at eg
  refine ⟨g, hg, (tilde.functor (CommRingCat.of (Localization.Away g))).obj
      (ModuleCat.of (Localization.Away g) (ULift.{u} (Fin r → Localization.Away g))),
    isFiniteLocallyFreeOfRank_tilde_uliftFree (CommRingCat.of (Localization.Away g)) r, ⟨?_⟩⟩
  exact (derivedPullback (Spec.map (CommRingCat.ofHom
      (algebraMap (R : Type u) (Localization.Away g)))).toLRSHom.toShHom).mapIso e.symm ≪≫
    derivedPullbackAwayTildeSingleIso R M g i _ eg

/-- **Restriction along a composite of open immersions, from an iterated derived pullback.** If
the derived pullback of `E` along `b : Z ⟶ X` and then along `a : Y ⟶ Z` is isomorphic to `N`
placed in degree `i`, then so is the restriction of `E` along `a ≫ b`.

Restriction along an open immersion is the derived pullback along it
(`derivedRestrictIsoDerivedPullback`) and the two derived pullbacks compose by the unconditional
formula of [stacks 0D5S]; the equality of the two underlying morphisms of ringed spaces is
transported by `eqToIso`, as in
`exists_isFiniteLocallyFreeOfRank_derivedPullback_of_factorsThrough`. -/
def derivedRestrictCompIsoOfDerivedPullback {X Y Z : Scheme.{u}}
    (E : DerivedCategory X.Modules) (i : ℤ) (a : Y ⟶ Z) [IsOpenImmersion a] (b : Z ⟶ X)
    [IsOpenImmersion b] (N : Y.Modules)
    (eN : (derivedPullback a.toLRSHom.toShHom).obj
          ((derivedPullback b.toLRSHom.toShHom).obj E) ≅
        (DerivedCategory.singleFunctor Y.Modules i).obj N) :
    (restrictFunctor (a ≫ b)).mapDerivedCategory.obj E ≅
      (DerivedCategory.singleFunctor Y.Modules i).obj N :=
  have hs : a.toLRSHom.toShHom ≫ b.toLRSHom.toShHom = (a ≫ b).toLRSHom.toShHom := by
    simp only [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom]
  (derivedRestrictIsoDerivedPullback (a ≫ b)).app E ≪≫
    eqToIso (congrArg (fun k => (derivedPullback.{u, u + 1, u + 1} k).obj E) hs).symm ≪≫
      ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
        a.toLRSHom.toShHom b.toLRSHom.toShHom).app E).symm ≪≫ eN

/-! ### The converse half of the pointwise description -/

/-- **A point whose derived-fibre Betti numbers are concentrated in degree `i` with value `r` lies
in the open subscheme of [stacks 0BDK].** Let `X` be a scheme, `E` a perfect object of `D(𝒪_X)`,
`i` an integer and `r` a natural number, and let `x` be a point of `X` at which the derived-fibre
Betti numbers of `E` vanish outside degree `i` and take the value `r` in degree `i`. Then `x` lies
in `singleDegreeRankOpen E i r`.

This is the converse of
`AlgebraicGeometry.Scheme.Modules.derivedFiberBetti_eq_zero_of_mem_singleDegreeRankOpen` together
with `…derivedFiberBetti_eq_rank_of_mem_singleDegreeRankOpen`, and the half which uses perfectness
of `E`.

The point is taken inside an affine open; the derived pullback of `E` to the chart is perfect by
[stacks 09UA] and has the same Betti numbers by [stacks 0BDI] part (1), so the affine step applies
and gives a principal open of the chart on which `E` is a finite locally free module of rank `r`
placed in degree `i`. That principal open maps to `X` by an open immersion whose range contains
`x`, so `mem_singleDegreeRankOpen_of_isOpenImmersion` puts `x` in the open subscheme. -/
theorem mem_singleDegreeRankOpen_of_derivedFiberBetti {X : Scheme.{u}}
    (E : DerivedCategory X.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
    (hPC : RingedSpace.IsPseudoCoherent.{u, u + 1} (X := X.toRingedSpace) E)
    (i : ℤ) (r : ℕ) {x : X}
    (hvanish : ∀ j : ℤ, j ≠ i → DerivedFibreBetti.derivedFiberBetti X E hPC j x = 0)
    (hrank : DerivedFibreBetti.derivedFiberBetti X E hPC i x = r) :
    x ∈ singleDegreeRankOpen E i r := by
  obtain ⟨V, hxV⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_affineOpens_eq_top X).ge (Set.mem_univ x))
  obtain ⟨y, hy⟩ : x ∈ Set.range (V.2.fromSpec).base := by
    rw [V.2.range_fromSpec]; exact hxV
  have hchartPerf := AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
    (V.2.fromSpec).toLRSHom.toShHom E hE
  have hchartPC := DerivedFibreBetti.isPseudoCoherent_derivedPullback V.2.fromSpec E hPC
  have hbc : ∀ j : ℤ, DerivedFibreBetti.derivedFiberBetti (Spec Γ(X, V.1))
      ((derivedPullback (V.2.fromSpec).toLRSHom.toShHom).obj E) hchartPC j y =
      DerivedFibreBetti.derivedFiberBetti X E hPC j x := by
    intro j
    refine (congrFun
      (DerivedFibreBetti.derivedFiberBetti_derivedPullback V.2.fromSpec E hPC j) y).trans ?_
    exact congrArg (DerivedFibreBetti.derivedFiberBetti X E hPC j) hy
  obtain ⟨g, hg, N, hN, ⟨eN⟩⟩ :=
    exists_away_derivedPullback_iso_singleFunctor_of_derivedFiberBetti Γ(X, V.1) _ hchartPerf
      hchartPC i r y (fun j hj => (hbc j).trans (hvanish j hj)) ((hbc i).trans hrank)
  obtain ⟨z, hz⟩ : y ∈ Set.range (Spec.map (CommRingCat.ofHom
      (algebraMap (Γ(X, V.1) : Type u) (Localization.Away g)))).base := by
    have hb : y ∈ PrimeSpectrum.basicOpen g := hg
    rwa [← Scheme.Hom.opensRange_localizationAway (R := Γ(X, V.1)) g] at hb
  have : IsOpenImmersion (V.2.fromSpec) := V.2.isOpenImmersion_fromSpec
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (Γ(X, V.1) : Type u) (Localization.Away g)))) :=
    Scheme.isOpenImmersion_SpecMap_localizationAway g
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (Γ(X, V.1) : Type u) (Localization.Away g))) ≫ V.2.fromSpec) :=
    IsOpenImmersion.comp _ _
  refine mem_singleDegreeRankOpen_of_isOpenImmersion E i r
    (Spec.map (CommRingCat.ofHom
      (algebraMap (Γ(X, V.1) : Type u) (Localization.Away g))) ≫ V.2.fromSpec)
    ⟨N, hN, ⟨derivedRestrictCompIsoOfDerivedPullback E i _ _ N eN⟩⟩ ⟨z, ?_⟩
  have hz' : (Spec.map (CommRingCat.ofHom
      (algebraMap (Γ(X, V.1) : Type u) (Localization.Away g)))) z = y := hz
  simpa only [Scheme.Hom.comp_apply, hz'] using hy

end Scheme.Modules

end AlgebraicGeometry

end
