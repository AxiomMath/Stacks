module

public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.FiniteStalkAtPuncture
public import StacksFrontier.AlgebraicGeometry.DerivedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.InvertibleTrivialInCodimensionOne

/-!
# A module trivial off a point with free stalk at it is trivial

Let `X` be a normal locally Noetherian scheme, `w ∈ X` a point whose local ring has dimension
at least two, and `U ⊆ X` an open containing every point other than `w`. A quasi-coherent
`𝒪_X`-module `M` with `M|_U ≅ 𝒪_U` and `M_w ≅ 𝒪_{X,w}` is isomorphic to `𝒪_X`.

Indeed `M` is coherent (`Stacks.AlgebraicGeometry.FiniteStalkAtPuncture.isCoherent`), its stalk
at `w` has depth `depth 𝒪_{X,w} ≥ 2` (Serre's `S₂` for the normal local ring `𝒪_{X,w}`), so the
Hartogs extension property (`AlgebraicGeometry.isIso_unit_restrict_pushforward_of_depth_ge_two`)
gives `M ≅ j_* j^* M ≅ j_* 𝒪_U ≅ 𝒪_X` for `j : U → X`, exactly as for `𝒪_X` itself.

## Main results

* `AlgebraicGeometry.nonempty_iso_unit_of_pullback_iso_of_stalk`: the statement above.
-/

@[expose] public section

universe u

open CategoryTheory Stacks.ModuleStalkSpecialization

namespace AlgebraicGeometry

/-- **A quasi-coherent module trivial off a point, with free stalk of rank one at the point, is
trivial**, on a normal locally Noetherian scheme whose local ring at the point has dimension at
least two. -/
theorem nonempty_iso_unit_of_pullback_iso_of_stalk {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] (M : X.Modules) [M.IsQuasicoherent] (U : X.Opens) (w : X)
    (hw : ∀ x, x ∉ U → x = w) (hdim : (2 : ℕ∞) ≤ ringKrullDim (X.presheaf.stalk w))
    (e : (Scheme.Modules.pullback U.ι).obj M ≅
      (Scheme.Modules.pullback U.ι).obj (SheafOfModules.unit X.ringCatSheaf))
    (ew : letI := stalkModule M w
      Nonempty (M.presheaf.stalk w ≃ₗ[X.presheaf.stalk w] X.presheaf.stalk w)) :
    Nonempty (M ≅ SheafOfModules.unit X.ringCatSheaf) := by
  let := stalkModule M w
  obtain ⟨ew⟩ := ew
  have hU : (M.restrict U.ι).IsFiniteType := by
    have : ((Scheme.Modules.pullback U.ι).obj
        (SheafOfModules.unit X.ringCatSheaf)).IsFiniteType :=
      SheafOfModules.pullback_isFiniteType U.ι.toLRSHom.toShHom _
    exact Stacks.AlgebraicGeometry.DerivedPushforward.isFiniteType_of_iso
      (e.symm ≪≫ ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).symm)
  have hfin : Module.Finite (X.presheaf.stalk w) (M.presheaf.stalk w) :=
    Module.Finite.equiv ew.symm
  have : M.IsCoherent :=
    Stacks.AlgebraicGeometry.FiniteStalkAtPuncture.isCoherent M U hU w hw hfin
  have : (SheafOfModules.unit X.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  have : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (SheafOfModules.unit X.ringCatSheaf) :=
    Stacks.AlgebraicGeometry.Tag09NY.isInvertible_unit X
  have hM := isIso_unit_restrict_pushforward_of_depth_ge_two X M U fun x hx => by
    obtain rfl := hw x hx
    have key := VectorBundleCodimensionOne.two_le_depth_stalk_of_isNormal x hdim
    rw [← Module.depth_eq_depth_of_linearEquiv _ ew] at key
    exact key
  have hO := isIso_unit_restrict_pushforward_of_depth_ge_two
    X (SheafOfModules.unit X.ringCatSheaf) U fun x hx => by
      obtain rfl := hw x hx
      exact two_le_depth_stalk_of_isInvertible _ x hdim
  exact ⟨asIso ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app M) ≪≫
    (Scheme.Modules.pushforward U.ι).mapIso e ≪≫
    (asIso ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app _)).symm⟩

end AlgebraicGeometry
