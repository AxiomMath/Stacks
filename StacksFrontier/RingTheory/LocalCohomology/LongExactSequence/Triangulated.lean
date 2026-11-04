module

public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree.ExactSequence
public import StacksFrontier.RingTheory.LocalCohomology.LongExactSequence

/-!
# The long exact sequence of local cohomology, with its maps

Let `I` be a finitely generated ideal of a commutative ring `A`, let `Y = V(I)` and let
`0 → M₁ → M₂ → M₃ → 0` be a short exact sequence of `A`-modules. This file provides the map
`H^i_Y(M) ⟶ H^i_Y(N)` induced by a map of modules, the exactness of

`H^i_Y(M₁) → H^i_Y(M₂) → H^i_Y(M₃)`

at the middle term, and the two surjectivity criteria that exactness one step further out gives:
`H^i_Y(M₁) → H^i_Y(M₂)` is surjective as soon as `H^i_Y(M₃) = 0`, and `H^i_Y(M₂) → H^i_Y(M₃)` is
surjective as soon as `H^{i+1}_Y(M₁) = 0`.

The route is the triangulated one. `RΓ_Y` is the right adjoint of the inclusion of the derived
objects with `I`-power-torsion cohomology (Stacks 0A6R), that subcategory is triangulated, and a
right adjoint of a triangulated functor between triangulated categories is triangulated; so the
distinguished triangle attached to a short exact sequence of complexes is carried to a
distinguished triangle, and Mathlib's homology sequence of a distinguished triangle
(`CategoryTheory.DerivedCategory.HomologySequence`) gives both exactness statements, the second
through the connecting map `δ`.

## Main definitions

* `Stacks.LocalCohomology.localCohomologyModuleMap` — the map `H^i_Y(M) ⟶ H^i_Y(N)` induced by
  `M ⟶ N`.

## Main results

* `Stacks.LocalCohomology.derivedPowerTorsionProperty_isTriangulated` and
  `Stacks.LocalCohomology.localCohomologyFunctor_isTriangulated` — the triangulated structure
  that makes the sequence available with its maps.
* `Stacks.LocalCohomology.exact_localCohomologyModuleMap` — exactness at the middle term.
* `Stacks.LocalCohomology.surjective_localCohomologyModuleMap_of_isZero_X₃` — surjectivity of
  `H^i_Y(M₁) → H^i_Y(M₂)` from the vanishing of `H^i_Y(M₃)`.
* `Stacks.LocalCohomology.surjective_localCohomologyModuleMap_of_isZero_X₁_succ` —
  surjectivity of `H^i_Y(M₂) → H^i_Y(M₃)` from the vanishing of `H^{i+1}_Y(M₁)`.

## Implementation notes

`StacksFrontier.RingTheory.LocalCohomology.LongExactSequence` provides the same long exact sequence
in map-free form, from the Čech model. That route needs no triangulated structure and it is what
the descending induction of Stacks 0DX7 consumes, so it is still the one to use for the statements
it proves; this file is the complement, giving the maps.

The map on local cohomology modules, the two `ObjectProperty` instances and the middle exactness
below are the single copies in the library.
`StacksFrontier.RingTheory.LocalCohomology.ArtinianOverLocalRing` once carried private duplicates of
all four; it imports this file and uses these instead.

**What this gives for Stacks 0EB3, and what is still missing.** Tag 0EB3 says that for a
Noetherian ring `A` of dimension `d`, an element `f` outside every minimal prime `p` with
`dim A/p = d` acts surjectively on `H^d_Y(M)` for every finite module `M`. The source's argument
is exactly the two criteria below, applied to

* `0 → fM → M → M/fM → 0`, whose third term has `dim Supp(M/fM) < d`, and
* `0 → ker(M ↠ fM) → M → fM → 0`, whose first term has `dim Supp ≤ dim A = d < d + 1`,

composed along `M ↠ fM ↪ M`, which is multiplication by `f`. The dimension drop in the first
bullet is proved, as `Module.supportDim_quotSMulTop_lt_of_avoidsTopMinimalPrimes` in
`StacksFrontier.RingTheory.KrullDimension.AvoidTopMinimalPrimes`. The *vanishing* of local
cohomology above the dimension of the support is Stacks 0DXC, and that is the single input 0EB3
is still waiting on. It is not available: the reductions in
`StacksFrontier.RingTheory.LocalCohomology.DimensionVanishing.SupportReduction` carry the bound
`cd(B, J) ≤ dim B` as a hypothesis, and that bound's own missing inputs are recorded there —
clause (3) ⟹ (1) of Stacks 0DX7 and clause (1) of Stacks 0A3G. With 0DXC in hand, 0EB3 is a
short argument from the two criteria below.

## References

* [Stacks Project, Tag 0DX7](https://stacks.math.columbia.edu/tag/0DX7)
* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
* [Stacks Project, Tag 0EB3](https://stacks.math.columbia.edu/tag/0EB3)
* [Stacks Project, Tag 0DXC](https://stacks.math.columbia.edu/tag/0DXC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

attribute [local instance] HasDerivedCategory.standard

universe w u

namespace Stacks.LocalCohomology

/-- The map on local cohomology modules induced by a map of modules. -/
def localCohomologyModuleMap
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (M N : ModuleCat.{w} A) (f : M ⟶ N) (i : ℤ) :
    localCohomologyModule A I hI M i ⟶ localCohomologyModule A I hI N i :=
  (DerivedCategory.homologyFunctor (ModuleCat.{w} A) i).map
    ((Dualizing.derivedPowerTorsionProperty A I hI).ι.map
      ((Dualizing.localCohomologyFunctor A I hI).map
        ((DerivedCategory.singleFunctor (ModuleCat.{w} A) 0).map f)))

/-- Having `I`-power-torsion cohomology is invariant under isomorphism in the derived category. -/
theorem derivedPowerTorsionProperty_isClosedUnderIsomorphisms
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    (Dualizing.derivedPowerTorsionProperty.{u, w} A I hI).IsClosedUnderIsomorphisms where
  of_iso e h i := (Dualizing.powerTorsionModuleProperty A I hI).prop_of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso e) (h i)

attribute [local instance] derivedPowerTorsionProperty_isClosedUnderIsomorphisms

/-- **The objects with `I`-power-torsion cohomology form a triangulated subcategory of `D(A)`.**
It contains zero, is stable under the shift because the shift permutes the homology functors, and
is closed under the middle object of a distinguished triangle because `I`-power torsion is a
Serre class. -/
theorem derivedPowerTorsionProperty_isTriangulated
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    (Dualizing.derivedPowerTorsionProperty.{u, w} A I hI).IsTriangulated := by
  let P := Dualizing.derivedPowerTorsionProperty.{u, w} A I hI
  let S := Dualizing.powerTorsionModuleProperty.{u, w} A I hI
  have : P.ContainsZero := ⟨⟨0, isZero_zero _, fun i =>
    S.prop_of_isZero ((DerivedCategory.homologyFunctor _ i).map_isZero (isZero_zero _))⟩⟩
  have : P.IsStableUnderShift ℤ := ⟨fun n => ⟨fun X h i =>
    S.prop_of_iso (((DerivedCategory.homologyFunctor (ModuleCat.{w} A) 0).shiftIso
      n i (n + i) rfl).app X).symm (h (n + i))⟩⟩
  have : P.IsTriangulatedClosed₂ := .mk' (fun T hT h₁ h₃ i =>
    S.prop_X₂_of_exact (DerivedCategory.HomologySequence.exact₂ T hT i) (h₁ i) (h₃ i))
  exact {}

attribute [local instance] derivedPowerTorsionProperty_isTriangulated

/-- **The shift-compatibility of `RΓ_{V(I)}`.** The inclusion of the derived objects with
`I`-power-torsion cohomology commutes with the shift, because the subcategory is stable under it,
and the shift-compatibility of a right adjoint is determined by that of its left adjoint. This is
*data*, not a proposition, and `Functor.IsTriangulated` cannot even be stated without it. -/
@[instance_reducible]
def localCohomologyFunctorCommShift
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    (Dualizing.localCohomologyFunctor.{u, w} A I hI).CommShift ℤ :=
  (Dualizing.localCohomologyRightAdjoint.{u, w} A I hI).2.rightAdjointCommShift ℤ

/-- **`RΓ_{V(I)}` is a triangulated functor.** It is the right adjoint of the inclusion of a
triangulated subcategory, and a right adjoint of a triangulated functor is triangulated.

The shift-compatibility the statement quantifies over is `localCohomologyFunctorCommShift`, bound
by the `letI` of the statement: it is the one the conclusion is about, and no other is in scope. -/
theorem localCohomologyFunctor_isTriangulated
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    letI := localCohomologyFunctorCommShift.{w, u} A I hI
    (Dualizing.localCohomologyFunctor.{u, w} A I hI).IsTriangulated := by
  -- `Dualizing.localCohomologyFunctor` is a `def` for `(localCohomologyRightAdjoint …).1`, so an
  -- instance search at the first spelling does not find one seated at the second.  Both are
  -- ascribed to the *same* datum here, which is what makes the final `exact` check by
  -- definitional equality instead of searching.
  let : (Dualizing.localCohomologyFunctor.{u, w} A I hI).CommShift ℤ :=
    localCohomologyFunctorCommShift.{w, u} A I hI
  let : (Dualizing.localCohomologyRightAdjoint.{u, w} A I hI).1.CommShift ℤ :=
    localCohomologyFunctorCommShift.{w, u} A I hI
  let : (Dualizing.localCohomologyRightAdjoint.{u, w} A I hI).2.CommShift ℤ :=
    (Dualizing.localCohomologyRightAdjoint.{u, w} A I hI).2.commShift_of_leftAdjoint ℤ
  exact (Dualizing.localCohomologyRightAdjoint.{u, w} A I hI).2.isTriangulated_rightAdjoint

section Sequence

variable (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
  (S : ShortComplex (ModuleCat.{w} A)) (i : ℤ)

/-- The distinguished triangle of `D(A)` obtained by applying `RΓ_Y`, followed by the inclusion of
the objects with `I`-power-torsion cohomology, to the triangle of a short exact sequence. -/
def idealLocalCohomologyTriangle (hS : S.ShortExact) :
    Triangle (DerivedCategory (ModuleCat.{w} A)) :=
  let s := CochainComplex.singleFunctor (ModuleCat.{w} A) 0
  have : PreservesFiniteLimits s := inferInstanceAs
    (PreservesFiniteLimits (HomologicalComplex.single _ (.up ℤ) 0))
  have : PreservesFiniteColimits s := inferInstanceAs
    (PreservesFiniteColimits (HomologicalComplex.single _ (.up ℤ) 0))
  let P := Dualizing.derivedPowerTorsionProperty.{u, w} A I hI
  let G := (Dualizing.localCohomologyRightAdjoint.{u, w} A I hI).1
  let adj : P.ι ⊣ G := (Dualizing.localCohomologyRightAdjoint.{u, w} A I hI).2
  let : G.CommShift ℤ := adj.rightAdjointCommShift ℤ
  P.ι.mapTriangle.obj (G.mapTriangle.obj (DerivedCategory.triangleOfSES (hS.map_of_exact s)))

/-- The triangle `idealLocalCohomologyTriangle` is distinguished. -/
theorem idealLocalCohomologyTriangle_distinguished (hS : S.ShortExact) :
    idealLocalCohomologyTriangle A I hI S hS ∈ distTriang _ := by
  let s := HomologicalComplex.single (ModuleCat.{w} A) (.up ℤ) 0
  let P := Dualizing.derivedPowerTorsionProperty.{u, w} A I hI
  let G := (Dualizing.localCohomologyRightAdjoint.{u, w} A I hI).1
  let adj : P.ι ⊣ G := (Dualizing.localCohomologyRightAdjoint.{u, w} A I hI).2
  let : G.CommShift ℤ := adj.rightAdjointCommShift ℤ
  have : G.IsTriangulated := localCohomologyFunctor_isTriangulated.{w, u} A I hI
  exact P.ι.map_distinguished _ (G.map_distinguished _
    (DerivedCategory.triangleOfSES_distinguished (hS.map_of_exact s)))

/-- **Exactness of `H^i_Y(M₁) → H^i_Y(M₂) → H^i_Y(M₃)` at the middle term.** -/
theorem exact_localCohomologyModuleMap (hS : S.ShortExact) :
    Function.Exact (localCohomologyModuleMap A I hI S.X₁ S.X₂ S.f i)
      (localCohomologyModuleMap A I hI S.X₂ S.X₃ S.g i) := by
  have hT := idealLocalCohomologyTriangle_distinguished A I hI S hS
  let H := DerivedCategory.homologyFunctor (ModuleCat.{w} A) i
  let R := ShortComplex.mk (H.map (idealLocalCohomologyTriangle A I hI S hS).mor₁)
    (H.map (idealLocalCohomologyTriangle A I hI S hS).mor₂) (by
      rw [← Functor.map_comp, comp_distTriang_mor_zero₁₂ _ hT, Functor.map_zero])
  have hR : R.Exact := DerivedCategory.HomologySequence.exact₂ _ hT i
  exact LinearMap.exact_iff.2 ((ShortComplex.moduleCat_exact_iff_range_eq_ker R).mp hR).symm

/-- **Surjectivity of `H^i_Y(M₁) → H^i_Y(M₂)` from the vanishing of `H^i_Y(M₃)`.** Exactness at
the middle term identifies the image with the kernel of the next map, and that kernel is
everything when its target vanishes. -/
theorem surjective_localCohomologyModuleMap_of_isZero_X₃ (hS : S.ShortExact)
    (h₃ : IsZero (localCohomologyModule A I hI S.X₃ i)) :
    Function.Surjective (localCohomologyModuleMap A I hI S.X₁ S.X₂ S.f i).hom := by
  have := ModuleCat.isZero_iff_subsingleton.mp h₃
  exact fun y => Set.mem_range.mp
    ((exact_localCohomologyModuleMap A I hI S i hS y).mp (Subsingleton.elim _ _))

/-- **Surjectivity of `H^i_Y(M₂) → H^i_Y(M₃)` from the vanishing of `H^{i+1}_Y(M₁)`.** The next
map out of `H^i_Y(M₃)` in the long exact sequence is the connecting map to `H^{i+1}_Y(M₁)`, which
is zero when its target vanishes; exactness there then makes the map an epimorphism. -/
theorem surjective_localCohomologyModuleMap_of_isZero_X₁_succ (hS : S.ShortExact)
    (h₁ : IsZero (localCohomologyModule A I hI S.X₁ (i + 1))) :
    Function.Surjective (localCohomologyModuleMap A I hI S.X₂ S.X₃ S.g i).hom := by
  let T := idealLocalCohomologyTriangle A I hI S hS
  have hT := idealLocalCohomologyTriangle_distinguished A I hI S hS
  let R := ShortComplex.mk ((DerivedCategory.homologyFunctor (ModuleCat.{w} A) i).map T.mor₂)
    (DerivedCategory.HomologySequence.δ T i (i + 1) rfl)
    (DerivedCategory.HomologySequence.comp_δ T hT i (i + 1) rfl)
  have hR : R.Exact := DerivedCategory.HomologySequence.exact₃ T hT i (i + 1) rfl
  have hobj : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{w} A) (i + 1)).obj T.obj₁) := by
    have heq : (DerivedCategory.homologyFunctor (ModuleCat.{w} A) (i + 1)).obj T.obj₁ =
        localCohomologyModule A I hI S.X₁ (i + 1) := by
      dsimp [T, idealLocalCohomologyTriangle, localCohomologyModule,
        Dualizing.localCohomologyFunctor, DerivedCategory.triangleOfSES]
      rfl
    rwa [heq]
  exact (ModuleCat.epi_iff_surjective R.f).mp (hR.epi_f_iff.mpr (hobj.eq_of_tgt R.g 0))

end Sequence

end Stacks.LocalCohomology

