module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Sheaf
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.RestrictHomology
public import StacksFrontier.AlgebraicGeometry.Perfect.SingleDegreeOpen
public import StacksFrontier.AlgebraicGeometry.Perfect.SingleDegreeRankOpen
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictPseudoCoherentPullback
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictTarget
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Defs

/-!
# The ranks of the cohomology of a perfect complex vanish outside a bounded range

Let `E` be a perfect object of `D(𝒪_X)` on a scheme `X`, and let `U ⊆ X` be a nonempty open on
which every cohomology module `Hⁱ(E|_U)` is finite locally free of a constant rank `rᵢ`. Then
`rᵢ = 0` for all but finitely many `i`: near a point of `U` the object `E` is represented by a
bounded complex of finite locally free modules, so its cohomology modules vanish there outside a
bounded range of degrees, and a zero module which is finite locally free of rank `r` on a
nonempty scheme has `r = 0`.

## Main results

* `AlgebraicGeometry.homologyDerivedPullbackIsoRestrict`: the `i`-th cohomology module of the
  derived pullback of `E` along the inclusion of an open subscheme is the restriction of the
  `i`-th cohomology module of `E`.
* `AlgebraicGeometry.rank_eq_zero_of_isZero_of_isFiniteLocallyFreeOfRank`: a zero module which
  is finite locally free of rank `r` on a nonempty scheme has `r = 0`.
* `AlgebraicGeometry.exists_rank_eq_zero_of_isPerfect`: the ranks of the cohomology of a perfect
  object on a nonempty open vanish outside a bounded range of degrees.

## Implementation notes

**The two vocabularies of derived restriction.**
`AlgebraicGeometry.Scheme.Modules.derivedRestrictModulesIsoDerivedPullback` identifies
`AlgebraicGeometry.RingedSpace.derivedRestrictModules` with
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback` along `U.ι`, and
`AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoRestrictFunctor` identifies it with
`CategoryTheory.Functor.mapDerivedCategory` of `AlgebraicGeometry.Scheme.Modules.restrictFunctor`.
Composing the two with
`AlgebraicGeometry.Scheme.Modules.homologyFunctor_mapDerivedCategory_restrictFunctor_iso` — the
exactness of restriction — gives `AlgebraicGeometry.homologyDerivedPullbackIsoRestrict`, which is
what lets the `derivedPullback` spelling of `Hⁱ(E|_U)` be computed from the cohomology modules of
`E` themselves.

## References

* [Stacks Project, Tag 0ESQ](https://stacks.math.columbia.edu/tag/0ESQ)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StrictlyPerfect TopologicalSpace Opposite
open Stacks.Cohomology.PerfectComplexes
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry

/-- **The cohomology of a derived pullback along the inclusion of an open subscheme.** The `i`-th
cohomology module of `L(U.ι)^*E` is the restriction to `U` of the `i`-th cohomology module of
`E`.

Derived restriction to `U` is both the derived pullback along `U.ι`
(`AlgebraicGeometry.Scheme.Modules.derivedRestrictModulesIsoDerivedPullback`) and the functor
induced on derived categories by Mathlib's restriction
(`AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoRestrictFunctor`); restriction is exact,
so it commutes with the cohomology modules. -/
def homologyDerivedPullbackIsoRestrict (X : Scheme.{u}) (U : X.Opens) (i : ℤ)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :
    (DerivedCategory.homologyFunctor (OXMod.{u, u} U.toScheme.toRingedSpace) i).obj
        ((derivedPullback U.ι.toLRSHom.toShHom).obj E) ≅
      (Scheme.Modules.restrictFunctor U.ι).obj
        ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) i).obj E) :=
  (DerivedCategory.homologyFunctor (OXMod.{u, u} U.toScheme.toRingedSpace) i).mapIso
      ((Scheme.Modules.derivedRestrictModulesIsoDerivedPullback X U).app E).symm ≪≫
    (DerivedCategory.homologyFunctor (OXMod.{u, u} U.toScheme.toRingedSpace) i).mapIso
      ((RingedSpace.derivedRestrictModulesIsoRestrictFunctor X U).app E) ≪≫
    (Scheme.Modules.homologyFunctor_mapDerivedCategory_restrictFunctor_iso U.ι i).app E

/-- **A zero module which is finite locally free of rank `r` on a nonempty scheme has `r = 0`.**
Near a point the module is the free module on `r` generators; if `r > 0` the structure sheaf is a
retract of that free module, hence a zero object, and then the ring of global sections of a
nonempty scheme would be trivial. -/
theorem rank_eq_zero_of_isZero_of_isFiniteLocallyFreeOfRank {Y : Scheme.{u}} [Nonempty Y]
    {M : Y.Modules} (hM : IsZero M) {r : ℕ}
    (h : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r) : r = 0 := by
  obtain ⟨y⟩ := ‹Nonempty Y›
  obtain ⟨V, hyV, ⟨e⟩⟩ := (Scheme.Modules.isFiniteLocallyFreeOfRank_iff M r).2 h y
  by_contra hr
  let R := (V : Scheme.{u}).ringCatSheaf
  let I := ULift.{u} (Fin r)
  let i₀ : I := ⟨⟨0, Nat.pos_of_ne_zero hr⟩⟩
  have hfree : IsZero (SheafOfModules.free.{u} (R := R) I) :=
    (Functor.map_isZero (Scheme.Modules.restrictFunctor V.ι) hM).of_iso e.symm
  let s := (SheafOfModules.unit R).unitHomEquiv (𝟙 _)
  let π : SheafOfModules.free.{u} (R := R) I ⟶ SheafOfModules.unit R :=
    ((SheafOfModules.unit R).freeHomEquiv).symm fun _ => s
  have hπ : SheafOfModules.ιFree i₀ ≫ π = 𝟙 _ := by
    apply (SheafOfModules.unit R).unitHomEquiv.injective
    exact congrFun (((SheafOfModules.unit R).freeHomEquiv).apply_symm_apply fun _ => s) i₀
  have hunit : IsZero (SheafOfModules.unit R) := by
    rw [IsZero.iff_id_eq_zero, ← hπ, hfree.eq_of_src π 0, comp_zero]
  have : Nonempty (⊤ : (V : Scheme.{u}).Opens) := ⟨⟨⟨y, hyV⟩, trivial⟩⟩
  have key : ∀ c : (SheafOfModules.unit R).val.obj (op ⊤), c = 0 := fun c => by
    have h : (𝟙 (SheafOfModules.unit R) : SheafOfModules.unit R ⟶ _).val.app (op ⊤) c =
        (0 : SheafOfModules.unit R ⟶ SheafOfModules.unit R).val.app (op ⊤) c := by
      rw [hunit.eq_of_src (𝟙 _) 0]
    have h0 : (0 : SheafOfModules.unit R ⟶ SheafOfModules.unit R).val.app (op ⊤) c = 0 := by
      change (0 : (SheafOfModules.unit R).val ⟶ (SheafOfModules.unit R).val).app (op ⊤) c = 0
      simp
    simpa [h0] using h
  have : Subsingleton Γ((V : Scheme.{u}), ⊤) := ⟨fun a b => (key a).trans (key b).symm⟩
  exact false_of_nontrivial_of_subsingleton Γ((V : Scheme.{u}), ⊤)

/-- **The ranks of the cohomology of a perfect object vanish outside a bounded range.** Let `E` be
a perfect object of `D(𝒪_X)` and let `U ⊆ X` be a nonempty open on which every `Hⁱ(E|_U)` is finite
locally free of rank `rᵢ`. Then there are `a ≤ b` such that `rᵢ = 0` for `i < a` and for `b < i`.

Near a point `x` of `U` the object `E` is represented by a bounded strictly perfect complex `P`, by
the definition of perfectness ([Stacks, Tag 08CM]). In a degree where `P` vanishes the cohomology
of `E` restricts to zero near `x`
(`Stacks.AlgebraicGeometry.PerfectCohomology.derivedHomologyRestrictIso`), so the finite locally
free module `Hⁱ(E|_U)` restricts to zero on a nonempty open of `U`, and its rank is `0` by
`AlgebraicGeometry.rank_eq_zero_of_isZero_of_isFiniteLocallyFreeOfRank`. -/
theorem exists_rank_eq_zero_of_isPerfect {X : Scheme.{u}}
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) (hE : IsPerfect.{u, u, u + 1} E)
    (U : X.Opens) (hU : (U : Set X).Nonempty) (r : ℤ → ℕ)
    (hrank : ∀ i : ℤ, SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} U.toScheme.toRingedSpace) i).obj
        ((derivedPullback U.ι.toLRSHom.toShHom).obj E)) (r i)) :
    ∃ a b : ℤ, ∀ i : ℤ, (i < a ∨ b < i) → r i = 0 := by
  classical
  obtain ⟨x, hxU⟩ := hU
  obtain ⟨E', hEC, ⟨eEK⟩⟩ := hE
  obtain ⟨I, W, hW, hmodels⟩ := hEC
  obtain ⟨j, hxj⟩ := Opens.mem_iSup.mp (hW ▸ Opens.mem_top x)
  obtain ⟨P, hP, ⟨q, hq⟩⟩ := hmodels j
  have hzero : ∀ n : ℤ, IsZero (P.X n) → r n = 0 := by
    intro n hn
    let H := (DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) n).obj E
    let Wj : X.Opens := W j
    have hPH : IsZero (P.homology n) := by
      simpa [HomologicalComplex.homology] using
        ShortComplex.isZero_homology_of_isZero_X₂ (P.sc n) hn
    have hW' : IsZero ((Scheme.Modules.restrictFunctor Wj.ι).obj H) :=
      (hPH.of_iso (Stacks.AlgebraicGeometry.PerfectCohomology.derivedHomologyRestrictIso
        X Wj eEK q hq n).symm).of_iso
        ((Stacks.AlgebraicGeometry.PerfectCohomology.restrictModulesIsoRestrict X Wj).app H).symm
    let V : X.Opens := U ⊓ Wj
    have hVW : V ≤ Wj := inf_le_right
    have hVU : V ≤ U := inf_le_left
    have hV : IsZero ((Scheme.Modules.restrictFunctor V.ι).obj H) :=
      Scheme.Modules.isZero_of_isZero_restrict_isIso (Scheme.Opens.isoOfLE hVW).hom
        ((Functor.map_isZero (Scheme.Modules.restrictFunctor (Wj.ι ⁻¹ᵁ V).ι) hW').of_iso
          (Scheme.Modules.restrictPreimageIso hVW H).symm)
    have hN : IsZero ((Scheme.Modules.restrictFunctor (U.ι ⁻¹ᵁ V).ι).obj
        ((Scheme.Modules.restrictFunctor U.ι).obj H)) :=
      (Functor.map_isZero (Scheme.Modules.restrictFunctor (Scheme.Opens.isoOfLE hVU).hom)
        hV).of_iso (Scheme.Modules.restrictPreimageIso hVU H)
    have hp : Scheme.Modules.IsFiniteLocallyFreeOfRank
        ((Scheme.Modules.restrictFunctor U.ι).obj H) (r n) :=
      ((Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ _).2 (hrank n)).of_iso
        (homologyDerivedPullbackIsoRestrict X U n E)
    have : Nonempty (U.ι ⁻¹ᵁ V : Scheme.{u}) := ⟨⟨⟨x, hxU⟩, by simpa [V] using ⟨hxU, hxj⟩⟩⟩
    exact rank_eq_zero_of_isZero_of_isFiniteLocallyFreeOfRank hN
      ((Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ _).1 (hp.restrict (U.ι ⁻¹ᵁ V).ι))
  obtain ⟨a, ha⟩ := hP.bounded.bddBelow
  obtain ⟨b, hb⟩ := hP.bounded.bddAbove
  refine ⟨a, b, fun i hi => hzero i ?_⟩
  by_contra hne
  rcases hi with hi | hi
  exacts [absurd (ha hne) (not_le.mpr hi), absurd (hb hne) (not_le.mpr hi)]

end AlgebraicGeometry

end
