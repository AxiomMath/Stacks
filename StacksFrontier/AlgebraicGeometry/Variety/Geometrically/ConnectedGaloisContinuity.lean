module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedGaloisAction
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.QuasiCompactOpen
public import StacksFrontier.Topology.Noetherian.LocallyConnected
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Continuity of the Galois action on geometric connected components

For a quasi-compact scheme over a field, open geometric connected components form a finite
set, and the absolute Galois group acts continuously on that set. A scheme of finite type
satisfies both hypotheses.

## Main results

* `AlgebraicGeometry.finite_geometricConnectedComponents_of_isOpen`: finiteness of geometric
  connected components.
* `AlgebraicGeometry.continuous_galoisActionOnGeometricConnectedComponents`: continuity of the
  Galois action.
* `AlgebraicGeometry.isOpen_geometricConnectedComponent_of_finiteType`: the geometric connected
  components of a scheme of finite type are open.

## Implementation notes

The separable algebraic closure is an abstract field extension with an `IsSepClosure` instance.
The action is the canonical action of Tag 038D; its group is written as an opposite group to
account for the contravariance of `Spec`. Continuity uses the Krull topology on that group and
the quotient topology on connected components. Quasi-compactness of a scheme is expressed by
`CompactSpace` on its underlying space, while finite type is expressed by the locally
finite-type and quasi-compact properties of its structure morphism. The finite-type implication
for quasi-compactness uses the more general existing result for a quasi-compact morphism over a
quasi-compact base; the spectrum of a field is quasi-compact.

## References

* [Stacks Project, Tag 038E](https://stacks.math.columbia.edu/tag/038E)
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

add_to_stacks 038E "finite type implies assumption (1)"
  AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace
add_to_sga "3 VIB 10.1" "Y is quasi-compact"
  AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace
add_to_sga "4 VI 1.14" "(i), special case"
  AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace
add_to_sga "4 VIII 5.1" "partial" AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace

variable (k ksep : Type u) [Field k] [Field ksep] [Algebra k ksep]
  [IsSepClosure k ksep] (X : Over (Spec (.of k)))

omit [IsSepClosure k ksep] in
/-- The geometric base change of a quasi-compact scheme is quasi-compact. -/
public theorem compactSpace_galoisActionOnBaseChange [CompactSpace X.left] :
    CompactSpace (galoisActionOnBaseChange k ksep X).V := by
  show CompactSpace (SchemeOver.baseChange k ksep X)
  exact QuasiCompact.compactSpace_of_compactSpace (pullback.fst X.hom (spectrumMap k ksep))

omit [IsSepClosure k ksep] in
/-- The Galois action on the base change is the endomorphism determined by its two
projections. -/
public theorem galoisActionOnBaseChange_ρ_eq_of_fst_snd (g : MulOpposite (ksep ≃ₐ[k] ksep))
    (a : pullback X.hom (spectrumMap k ksep) ⟶ pullback X.hom (spectrumMap k ksep))
    (hfst : a ≫ pullback.fst X.hom (spectrumMap k ksep) = pullback.fst X.hom (spectrumMap k ksep))
    (hsnd : a ≫ pullback.snd X.hom (spectrumMap k ksep) =
      pullback.snd X.hom (spectrumMap k ksep) ≫
        Spec.map (CommRingCat.ofHom g.unop.toRingEquiv.toRingHom)) :
    ((galoisActionOnBaseChange k ksep X).ρ g).asHom = a := by
  apply pullback.hom_ext
  · show
      (pullback.lift
        (pullback.fst X.hom (spectrumMap k ksep) ≫ 𝟙 X.left)
        (pullback.snd X.hom (spectrumMap k ksep) ≫ specMapAlgAut k ksep g.unop) _) ≫
          pullback.fst X.hom (spectrumMap k ksep) = _
    simp only [Category.comp_id, pullback.lift_fst]
    exact hfst.symm
  · show
      (pullback.lift
        (pullback.fst X.hom (spectrumMap k ksep) ≫ 𝟙 X.left)
        (pullback.snd X.hom (spectrumMap k ksep) ≫ specMapAlgAut k ksep g.unop) _) ≫
          pullback.snd X.hom (spectrumMap k ksep) = _
    simp only [Category.comp_id, pullback.lift_snd]
    show pullback.snd X.hom (spectrumMap k ksep) ≫
        Spec.map (CommRingCat.ofHom g.unop.toRingEquiv.toRingHom) = _
    exact hsnd.symm

omit [IsSepClosure k ksep] in
/-- Open connected components of the geometric base change of a quasi-compact scheme are
finite in number. -/
@[stacks 038E "part (a)"]
public theorem finite_geometricConnectedComponents_of_isOpen
    [CompactSpace X.left]
    (hopen : ∀ x : (galoisActionOnBaseChange k ksep X).V,
      IsOpen (connectedComponent x)) :
    Finite (ConnectedComponents (galoisActionOnBaseChange k ksep X).V) := by
  have := compactSpace_galoisActionOnBaseChange k ksep X
  have : DiscreteTopology (ConnectedComponents (galoisActionOnBaseChange k ksep X).V) :=
    ConnectedComponents.discreteTopology_iff.mpr hopen
  exact Finite.of_finite_univ isCompact_univ.finite_of_discrete

/-- The absolute Galois action on open geometric connected components of a quasi-compact
scheme is continuous for the Krull topology. -/
@[stacks 038E "part (b)"]
public theorem continuous_galoisActionOnGeometricConnectedComponents
    [CompactSpace X.left]
    (hopen : ∀ x : (galoisActionOnBaseChange k ksep X).V,
      IsOpen (connectedComponent x)) :
    let : TopologicalSpace (galoisActionOnGeometricConnectedComponents k ksep X).V :=
      (inferInstance : TopologicalSpace
        (ConnectedComponents (galoisActionOnBaseChange k ksep X).V))
    Continuous (fun p : MulOpposite (ksep ≃ₐ[k] ksep) ×
        ConnectedComponents (galoisActionOnBaseChange k ksep X).V =>
      ConcreteCategory.hom
        ((galoisActionOnGeometricConnectedComponents k ksep X).ρ p.1).asHom p.2) := by
  let A := galoisActionOnGeometricConnectedComponents k ksep X
  let G := MulOpposite (ksep ≃ₐ[k] ksep)
  let : TopologicalSpace A.V :=
    (inferInstance : TopologicalSpace
      (ConnectedComponents (galoisActionOnBaseChange k ksep X).V))
  let : MulAction G A.V := Action.instMulAction A
  have : DiscreteTopology A.V := ConnectedComponents.discreteTopology_iff.mpr hopen
  show Continuous (fun p : G × A.V => p.1 • p.2)
  have := compactSpace_galoisActionOnBaseChange k ksep X
  have hcont : ContinuousSMul G A.V := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro T
    obtain ⟨x, rfl⟩ :
        ∃ x : (galoisActionOnBaseChange k ksep X).V,
          ConnectedComponents.mk x = T := ConnectedComponents.surjective_coe T
    let V : (pullback (C := Scheme) X.hom (spectrumMap k ksep)).Opens :=
      ⟨connectedComponent x, hopen x⟩
    obtain ⟨H, hHopen, hfix⟩ := exists_open_subgroup_fixing_isCompact_open X.left X.hom V
      isClosed_connectedComponent.isCompact
    let C : (galoisActionOnGeometricConnectedComponents k ksep X).V :=
      ConnectedComponents.mk x
    refine Subgroup.isOpen_mono (H₁ := H.op) (H₂ := MulAction.stabilizer G C) (fun g hg => ?_)
      (hHopen.preimage MulOpposite.continuous_unop)
    obtain ⟨a, hfst, hsnd, hVeq⟩ := hfix (MulOpposite.unop g) hg
    let q := ((galoisActionOnBaseChange k ksep X).ρ g).asHom
    have hqa : q = a.hom := galoisActionOnBaseChange_ρ_eq_of_fst_snd k ksep X g a.hom hfst hsnd
    have hVq : V = q ⁻¹ᵁ V := by simpa [hqa] using hVeq
    have hqxV : x ∈ (q ⁻¹ᵁ V).1 := by
      rw [← hVq]
      exact mem_connectedComponent
    have hact :
        ConcreteCategory.hom (A.ρ g).asHom C = ConnectedComponents.mk (q.base x) := by
      show ConcreteCategory.hom
        ((galoisActionOnGeometricConnectedComponents k ksep X).ρ g).asHom
          (ConnectedComponents.mk x) = ConnectedComponents.mk (q.base x)
      rw [galoisActionOnGeometricConnectedComponents_ρ_apply_mk]
      rfl
    show ConcreteCategory.hom (A.ρ g).asHom C = C
    exact hact.trans (ConnectedComponents.coe_eq_coe'.2 hqxV)
  exact hcont.continuous_smul

omit [IsSepClosure k ksep] in
/-- The geometric connected components of a scheme of finite type over a field are open. -/
@[stacks 038E "finite type implies assumption (2)"]
public theorem isOpen_geometricConnectedComponent_of_finiteType
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (x : (galoisActionOnBaseChange k ksep X).V) :
    IsOpen (connectedComponent x) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap k ksep))
  let Z : Over (Spec (.of ksep)) := (Over.pullback g).obj X
  let Y := Z.left
  have : LocallyOfFiniteType Z.hom := inferInstanceAs (LocallyOfFiniteType (pullback.snd X.hom g))
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have : QuasiCompact Z.hom := inferInstanceAs (QuasiCompact (pullback.snd X.hom g))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace Z.hom
  have : IsNoetherian Y := { }
  have : Finite (ConnectedComponents (galoisActionOnBaseChange k ksep X).V) := by
    show Finite (ConnectedComponents (↥Y))
    exact TopologicalSpace.NoetherianSpace.finite_connectedComponents (↥Y)
  show IsOpen (connectedComponent (x : ↥Y))
  exact (TopologicalSpace.isClopen_connectedComponent_of_finite_connectedComponents (x : ↥Y)).2

end AlgebraicGeometry
