module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.RegularImmersionClassCases
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleClassBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBaseChangeExcess
public import StacksFrontier.AlgebraicGeometry.Conormal.SquareFlatIso
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.FiberRankIsomorphismInvariant
public import StacksFrontier.AlgebraicGeometry.Duality.KoszulRegularNormalRank
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedVirtualNormalImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedVirtualNormalClassDualIso

/-!
# The normal sheaf of a regular immersion under smooth base change

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `i : X ⟶ P` be a
regular immersion of schemes locally of finite type over `S` and let `p : P' ⟶ P` be a smooth
morphism, with base change `j : X ×_P P' ⟶ P'`. The base change (Stacks 0FBJ) of the normal sheaf
`𝒞_{X/P}^∨` of `i` along the cartesian square is a virtual normal sheaf for `j` whose surjection
onto `𝒞_{X ×_P P'/P'}` is an isomorphism: it is the pullback of the reflexivity isomorphism of
`𝒞_{X/P}` followed by the canonical map `g^*𝒞_{X/P} ⟶ 𝒞_{X ×_P P'/P'}` of Stacks 0473, an
isomorphism because `p` is flat. When `j` is a regular immersion this identifies it with the
normal sheaf `𝒞_{X ×_P P'/P'}^∨` of `j`, compatibly with the surjections, and so the classes of
Stacks 0FBK and 0FBQ (3) of the two virtual normal sheaves agree.

## Main results

* `Stacks.Chow.VirtualNormalBundle.isIso_baseChange_surjection_of_flat` — the base change of a
  virtual normal sheaf with invertible surjection along a flat morphism has invertible surjection.
* `Stacks.Chow.VirtualNormalBundle.dualIsoOfIsIsoSurjection` — two virtual normal sheaves of the
  same immersion with invertible surjections have isomorphic duals, compatibly with the
  surjections.
* `Stacks.Chow.completedVirtualNormalGysinClass_eq_of_dualIso`,
  `Stacks.Chow.completedVirtualNormalGysinClassOfOpen_eq_of_dualIso`,
  `Stacks.Chow.completedVirtualNormalGysinClassOfImmersion_eq_of_dualIso` — the classes of
  Stacks 0FBK and Stacks 0FBQ (3) at arbitrary rank depend on the virtual normal sheaf only up to
  an isomorphism of duals compatible with the surjections.
* `Stacks.Chow.completedVirtualNormalGysinClassOfImmersion_baseChange_ofIsRegularImmersion` — for
  a regular immersion `i` and a flat `p` with regular base change `j`, the class of the base change
  of `𝒞_{X/P}^∨` is the class of `𝒞_{X ×_P P'/P'}^∨`.
* `Stacks.Chow.regularImmersionSmoothBaseChangeCase` — the base-change clause of Stacks 0FBK in
  the form used by Stacks 0FF2.

## References

* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBQ](https://stacks.math.columbia.edu/tag/0FBQ)
* [Stacks Project, Tag 0FBJ](https://stacks.math.columbia.edu/tag/0FBJ)
* [Stacks Project, Tag 0473](https://stacks.math.columbia.edu/tag/0473)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RegularIdealSheaf Stacks.AlgebraicGeometry.ReflexiveModules
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Chow

/-! ### Virtual normal sheaves with invertible surjection -/

section Iso

variable {Z X : Scheme.{u}} {i : Z ⟶ X} [IsImmersion i]

/-- **Two virtual normal sheaves with invertible surjections have isomorphic duals**: both
duals are identified with the conormal sheaf by their surjections. -/
def VirtualNormalBundle.dualIsoOfIsIsoSurjection (𝒩 𝒩' : VirtualNormalBundle i)
    [IsIso 𝒩.surjection] [IsIso 𝒩'.surjection] :
    dualSheaf 𝒩'.bundle ≅ dualSheaf 𝒩.bundle :=
  asIso 𝒩'.surjection ≪≫ (asIso 𝒩.surjection).symm

/-- The identification of the duals is compatible with the surjections. -/
theorem VirtualNormalBundle.dualIsoOfIsIsoSurjection_hom_comp_surjection
    (𝒩 𝒩' : VirtualNormalBundle i) [IsIso 𝒩.surjection] [IsIso 𝒩'.surjection] :
    (𝒩.dualIsoOfIsIsoSurjection 𝒩').hom ≫ 𝒩.surjection = 𝒩'.surjection :=
  (Category.assoc _ _ _).trans ((congrArg (𝒩'.surjection ≫ ·)
    (asIso 𝒩.surjection).inv_hom_id).trans (Category.comp_id _))

/-- **Flat base change of a virtual normal sheaf with invertible surjection.** For a cartesian
square `Z' = Z ×_X X'` of immersions with `X' ⟶ X` flat, the base change of a virtual normal sheaf
whose surjection is an isomorphism again has invertible surjection: it is the inverse of the dual
base-change isomorphism, the pullback of the surjection, and the canonical map
`g^*𝒞_{Z/X} ⟶ 𝒞_{Z'/X'}` of Stacks 0473, invertible by flatness. -/
theorem VirtualNormalBundle.isIso_baseChange_surjection_of_flat {Z' X' : Scheme.{u}}
    {i' : Z' ⟶ X'} [IsImmersion i'] (g : Z' ⟶ Z) (f : X' ⟶ X) [Flat f]
    (sq : IsPullback i' g f i) (𝒩 : VirtualNormalBundle i) [h𝒩 : IsIso 𝒩.surjection] :
    IsIso (𝒩.baseChange i i' g f sq).surjection := by
  rw [VirtualNormalBundle.baseChange_surjection]
  have : IsIso (C := SheafOfModules (structureSheafRing Z.toSheafedSpace)) 𝒩.surjection := h𝒩
  exact IsIso.comp_isIso' (Iso.isIso_inv _) (IsIso.comp_isIso'
    (Functor.map_isIso (modulePullback g.toLRSHom.toShHom) (f := 𝒩.surjection))
    (Stacks.Immersion.isIso_immersionConormalSheafMap_of_flat i' i g f sq))


end Iso

section Immersion

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsImmersion i] (hi : i ≫ sX = sZ)
  (𝒩 𝒩' : VirtualNormalBundle i) (ψ : dualSheaf 𝒩'.bundle ≅ dualSheaf 𝒩.bundle)
  (hψ : ψ.hom ≫ 𝒩.surjection = 𝒩'.surjection)

include hψ in
/-- **The counterpart for immersions (Stacks 0FBQ (3))**: the class `c(Z ⟶ X, 𝒩)` built from an
open `U` depends on `𝒩` only up to an isomorphism of duals compatible with the surjections. -/
theorem completedVirtualNormalGysinClassOfOpen_eq_of_dualIso (U : X.Opens)
    (i' : Z ⟶ U.toScheme) [IsClosedImmersion i'] (hU : i' ≫ U.ι = i) :
    completedVirtualNormalGysinClassOfOpen C sZ sX i hi U i' hU 𝒩 =
      completedVirtualNormalGysinClassOfOpen C sZ sX i hi U i' hU 𝒩' := by
  unfold completedVirtualNormalGysinClassOfOpen
  rw [completedVirtualNormalGysinClass_eq_of_dualIso C sZ (U.ι ≫ sX) i'
    (openFactor_comp_structureMorphism C sZ sX i hi hU) (𝒩.toOpenFactor hU) (𝒩'.toOpenFactor hU)
    ψ ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ (immersionConormalSheafFactorIso U i' hU).hom) hψ))]

include hψ in
/-- The class `c(Z ⟶ X, 𝒩)` of Stacks 0FBQ (3) at the canonical open depends on `𝒩` only up to an
isomorphism of duals compatible with the surjections. -/
theorem completedVirtualNormalGysinClassOfImmersion_eq_of_dualIso :
    completedVirtualNormalGysinClassOfImmersion C sZ sX i hi 𝒩 =
      completedVirtualNormalGysinClassOfImmersion C sZ sX i hi 𝒩' :=
  completedVirtualNormalGysinClassOfOpen_eq_of_dualIso C sZ sX i hi 𝒩 𝒩' ψ hψ _ _ _

end Immersion

/-! ### The normal sheaf of a regular immersion under flat base change -/

section RegularBaseChange

variable (C : ChowSituation.{u}) {X P P' : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (i : X ⟶ P) [IsImmersion i] (hi : i ≫ sP = sX)
  (p : P' ⟶ P) [LocallyOfFiniteType p] [Flat p] [IsLocallyNoetherian X]
  [IsLocallyNoetherian (pullback i p)] (hr : IsRegularImmersion i)
  (hr' : IsRegularImmersion (pullback.snd i p))

/-- **The base change of the normal sheaf of a regular immersion along a flat morphism has
invertible surjection**: the surjection of `𝒞_{X/P}^∨` is the reflexivity isomorphism, and the
canonical map of Stacks 0473 is an isomorphism for a flat base change. -/
instance VirtualNormalBundle.isIso_baseChange_ofIsRegularImmersion_surjection :
    IsIso ((VirtualNormalBundle.ofIsRegularImmersion i hr).baseChange i (pullback.snd i p)
      (pullback.fst i p) p (isPullback_pullbackSnd i p)).surjection :=
  VirtualNormalBundle.isIso_baseChange_surjection_of_flat (pullback.fst i p) p
    (isPullback_pullbackSnd i p) _

/-- **The normal sheaf of a regular immersion under flat base change.** For a regular immersion
`i : X ⟶ P` and a flat `p : P' ⟶ P` such that the base change `j : X ×_P P' ⟶ P'` is a regular
immersion, the class of Stacks 0FBQ (3) of the base change of `𝒞_{X/P}^∨` along the cartesian
square is the class of the normal sheaf `𝒞_{X ×_P P'/P'}^∨` of `j`: both surjections onto
`𝒞_{X ×_P P'/P'}` are isomorphisms, so the two duals are identified compatibly with them. -/
theorem completedVirtualNormalGysinClassOfImmersion_baseChange_ofIsRegularImmersion :
    completedVirtualNormalGysinClassOfImmersion C (pullback.fst i p ≫ sX) (p ≫ sP)
        (pullback.snd i p) (pullbackSnd_comp_structureMorphism_eq C sX sP i hi p)
        ((VirtualNormalBundle.ofIsRegularImmersion i hr).baseChange i (pullback.snd i p)
          (pullback.fst i p) p (isPullback_pullbackSnd i p)) =
      completedVirtualNormalGysinClassOfImmersion C (pullback.fst i p ≫ sX) (p ≫ sP)
        (pullback.snd i p) (pullbackSnd_comp_structureMorphism_eq C sX sP i hi p)
        (VirtualNormalBundle.ofIsRegularImmersion (pullback.snd i p) hr') :=
  completedVirtualNormalGysinClassOfImmersion_eq_of_dualIso C _ _ _ _ _ _
    (VirtualNormalBundle.dualIsoOfIsIsoSurjection _ _)
    (VirtualNormalBundle.dualIsoOfIsIsoSurjection_hom_comp_surjection _ _)

end RegularBaseChange

/-- **Stacks 0FBK, the base-change clause, in the form used by Stacks 0FF2**
(`Stacks.Chow.RegularImmersionSmoothBaseChangeCase`): for a regular immersion `i : X ⟶ P` and a
smooth `p : P' ⟶ P` with base change `j : X ×_P P' ⟶ P'` a regular immersion, the restriction of
`i^!` along `p` is `j^!`. The restriction of the class of `𝒞_{X/P}^∨` is the class of its base
change (`Stacks.Chow.completedBivariantRestriction_completedVirtualNormalGysinClassOfImmersion`),
which is the class of `𝒞_{X ×_P P'/P'}^∨` because `p` is flat
(`Stacks.Chow.completedVirtualNormalGysinClassOfImmersion_baseChange_ofIsRegularImmersion`). -/
theorem regularImmersionSmoothBaseChangeCase (C : ChowSituation.{u}) :
    RegularImmersionSmoothBaseChangeCase C := by
  intro X P P' sX _ sP _ i _ hi p _ hr hr'
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian sP
  have : IsLocallyNoetherian P' := LocallyOfFiniteType.isLocallyNoetherian (p ≫ sP)
  have : IsLocallyNoetherian (pullback i p) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst i p ≫ sX)
  exact (completedBivariantRestriction_completedVirtualNormalGysinClassOfImmersion C sX sP i hi p
    (VirtualNormalBundle.ofIsRegularImmersion i hr)).trans
    (completedVirtualNormalGysinClassOfImmersion_baseChange_ofIsRegularImmersion C sX sP i hi p hr
      hr')

end Stacks.Chow

end
