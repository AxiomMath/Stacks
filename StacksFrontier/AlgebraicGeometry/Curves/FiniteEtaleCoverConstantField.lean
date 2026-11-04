module

public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.SmoothProperConnectedComponent
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleFibreSupportDimension
public import StacksFrontier.Topology.Dimension.LocalKrullDim
public import StacksFrontier.Topology.Dimension.SpecializingSurjection
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProper
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Picard.FrobeniusFixedTorsion

/-!
# A connected finite étale cover of a smooth proper curve is a curve over its constant field

Let `X` be a smooth proper curve over a field `k` and `Y ⟶ X` a finite étale morphism with `Y`
connected. Then `Y` is smooth and proper over `k` of dimension one (an étale morphism preserves
local dimensions, and a surjective closed map does not lower the dimension), so by Stacks 0GK5
(4)–(5) its field of global functions `k_Y` is a finite separable extension of `k` over which `Y`
is smooth, proper and geometrically irreducible; it is again a curve over `k_Y`.

This is the cover `Y_V` over its constant field in the proof of the geometric input of Weil II
1.3.4 (Tag 03VH): the Frobenius-invariant characters of the geometric fundamental group become
Frobenius eigenvectors in the Picard group of `Y_V ⊗ k̄`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- **An étale morphism does not raise the dimension.** -/
theorem topologicalKrullDim_le_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] :
    topologicalKrullDim X ≤ topologicalKrullDim Y := by
  rw [← IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph,
    TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
  refine iSup_le fun x => ?_
  rw [← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim]
  calc topologicalKrullDimAt (↥(Set.univ : Set X)) x
      = topologicalKrullDimAt (↥(f ⁻¹' (Set.univ : Set Y))) ⟨x.1, trivial⟩ := rfl
    _ = _ := topologicalKrullDimAt_preimage_eq_of_etale f Set.univ isClosed_univ ⟨x.1, trivial⟩
    _ ≤ topologicalKrullDim (↥(Set.univ : Set Y)) := topologicalKrullDimAt_le_topologicalKrullDim _
    _ = topologicalKrullDim Y :=
      IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ Y).isHomeomorph

/-- **A surjective closed morphism does not lower the dimension.** -/
theorem topologicalKrullDim_le_of_surjective_of_isClosedMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hsurj : Function.Surjective f) (hclosed : IsClosedMap f) :
    topologicalKrullDim Y ≤ topologicalKrullDim X :=
  Topology.topologicalKrullDim_le_of_surjective_of_specializingMap_or_generalizingMap f f.continuous
    hsurj (Or.inl hclosed.specializingMap)

/-- A finite étale morphism with nonempty source onto a connected scheme is surjective: its
image is open and closed. -/
theorem surjective_of_finiteEtale {X : Scheme.{u}} [ConnectedSpace X] (Y : FiniteEtaleOver X)
    [Nonempty Y.left] : Function.Surjective Y.hom := by
  have : IsFinite Y.hom := Y.prop.1
  have : Etale Y.hom := Y.prop.2
  have : PreconnectedSpace ((Functor.fromPUnit X).obj Y.right) :=
    inferInstanceAs (PreconnectedSpace X)
  have : Nonempty ((𝟭 Scheme).obj Y.left) := inferInstanceAs (Nonempty Y.left)
  rw [← Set.range_eq_univ]
  exact IsClopen.eq_univ ⟨Y.hom.isClosedMap.isClosed_range, Y.hom.isOpenMap.isOpen_range⟩
    (Set.range_nonempty _)

/-- **A connected finite étale cover of a smooth proper curve is a smooth proper geometrically
irreducible curve over its constant field** `k_Y = Γ(Y, 𝒪_Y)`, a finite extension of `k`. -/
theorem exists_constantField_of_finiteEtale (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [Smooth f] [IsCurve k f] [ConnectedSpace X]
    (Y : FiniteEtaleOver X) [ConnectedSpace Y.left] :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (_ : Module.Finite k K)
      (r : Y.left ⟶ Spec (.of K)),
      r ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) = Y.hom ≫ f ∧ IsProper r ∧ Smooth r ∧
        GeometricallyIrreducible r ∧ IsCurve K r := by
  have : IsFinite Y.hom := Y.prop.1
  have : Etale Y.hom := Y.prop.2
  have : Nonempty Y.left := ConnectedSpace.toNonempty
  have hdimX : topologicalKrullDim X = 1 := IsCurve.topologicalKrullDim_eq_one f
  have hle : topologicalKrullDim Y.left ≤ 1 := hdimX ▸ topologicalKrullDim_le_of_etale Y.hom
  have hge : 1 ≤ topologicalKrullDim Y.left := hdimX ▸
    topologicalKrullDim_le_of_surjective_of_isClosedMap Y.hom (surjective_of_finiteEtale Y)
      Y.hom.isClosedMap
  let q : Y.left ⟶ Spec (.of k) := Y.hom ≫ f
  have : IsProper q := inferInstanceAs (IsProper (Y.hom ≫ f))
  have : Smooth q := inferInstanceAs (Smooth (Y.hom ≫ f))
  obtain ⟨K, _, _, _, _, r, hr, hsm, hproj, hgi, -⟩ :=
    exists_isSeparable_smooth_isProjectiveMorphism_geometricallyIrreducible k q hle
  have : IsProper r := isProper_of_isProjectiveMorphism r hproj
  have : GeometricallyReduced r := geometricallyReduced_of_smooth r
  have : GeometricallyIntegral r :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible r
  have : IsIntegral Y.left := GeometricallyIntegral.isIntegral_of_subsingleton r
  refine ⟨K, inferInstance, inferInstance, inferInstance, r, hr, inferInstance, hsm, hgi,
    { topologicalKrullDim_eq_one := le_antisymm hle hge }⟩

end AlgebraicGeometry
