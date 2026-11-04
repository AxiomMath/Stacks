module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.BaseChangeComposition
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ReducedProduct
public import StacksFrontier.RingTheory.GeometricallyReduced.TensorProduct
public import StacksFrontier.FieldTheory.Separable.TFAE

/-!
# placeholder
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

open scoped TensorProduct

namespace Stacks.Chow

/-- The spectrum of a separable field extension is geometrically reduced over the base field:
after any further extension `L/k` the ring of the base change is `K ⊗_k L`, which is reduced by
Stacks 030U, `L` being a reduced `k`-algebra. -/
theorem geometricallyReduced_specMap_algebraMap_of_isSeparableExtension (k K : Type u) [Field k]
    [Field K] [Algebra k K] [Algebra.IsSeparableExtension k K] :
    GeometricallyReduced (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  rw [geometricallyReduced_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro L _ _
  have hred : _root_.IsReduced (K ⊗[k] L) :=
    Algebra.isReduced_tensorProduct_of_isSeparableExtension_or_isSeparablyGenerated
      (Or.inl ‹Algebra.IsSeparableExtension k K›)
  exact ObjectProperty.prop_of_iso IsReduced (pullbackSpecIso k K L).symm
    ((affine_isReduced_iff _).2 hred)

/-- A reduced closed subscheme occurs with multiplicity one along each of its irreducible
components: the stalk at a generic point is a field, and it is a simple module over the stalk of
the ambient scheme because the stalk map of a closed immersion is surjective. -/
theorem componentMultiplicity_eq_one_of_isReduced {Y Z : Scheme.{u}} (i : Z ⟶ Y)
    [IsClosedImmersion i] [IsReduced Z] (ξ : genericPoints Z) :
    componentMultiplicity i ξ = 1 := by
  classical
  let A : Type u := Y.presheaf.stalk (i ξ.1)
  let B : Type u := Z.presheaf.stalk ξ.1
  let _ : Module A B := Module.compHom B (i.stalkMap ξ.1).hom
  have hfield : IsField B := isField_stalk_of_closure_mem_irreducibleComponents (X := Z) ξ.1 ξ.2
  let _ : Field B := hfield.toField
  have hsimple : IsSimpleModule A B := by
    rw [isSimpleModule_iff_toSpanSingleton_surjective]
    refine ⟨inferInstance, ?_⟩
    intro b hb c
    obtain ⟨a, ha⟩ := i.stalkMap_surjective ξ.1 (c / b)
    refine ⟨a, ?_⟩
    show (i.stalkMap ξ.1).hom a * b = c
    calc
      (i.stalkMap ξ.1).hom a * b = (c / b) * b := by rw [ha]
      _ = c := div_mul_cancel₀ c hb
  simp [componentMultiplicity, A, B]

/-- In a cartesian square whose lower edge is the spectrum of a separable extension of fields,
the base change of a reduced closed subscheme is reduced: the base change of the subscheme is
the fibre product of the subscheme with the spectrum of the larger field over the smaller, and
that spectrum is geometrically reduced. -/
theorem isReduced_comap_of_isPullback_of_geometricallyReduced
    {k : Type u} [Field k] {W Y Y' : Scheme.{u}} {q : Y ⟶ Spec (.of k)} {φ : W ⟶ Spec (.of k)}
    {q' : Y' ⟶ W} {p : Y' ⟶ Y} (hPB : IsPullback p q' q φ) (hφ : GeometricallyReduced φ)
    (I : Y.IdealSheafData) (hI : IsReduced I.subscheme) :
    IsReduced (I.comap p).subscheme := by
  have := hφ
  have := hI
  have hsq := (IsPullback.of_hasPullback p I.subschemeι).paste_horiz hPB.flip
  have hred : IsReduced (pullback φ (I.subschemeι ≫ q)) := isReduced_pullback _ _
  exact ObjectProperty.prop_of_iso IsReduced
    ((I.comapIso p).trans hsq.isoPullback).symm hred

/-- A nonzero coefficient of the cycle of a reduced closed subscheme is one. -/
theorem closedSubschemeCycleCoeff_eq_one_of_isReduced (C : ChowSituation.{u})
    {Y Z : Scheme.{u}} (q : Y ⟶ C.S) [LocallyOfFiniteType q] (i : Z ⟶ Y)
    [IsClosedImmersion i] [IsReduced Z] (k : ℤ) (y : Y)
    (hy : closedSubschemeCycleCoeff C q i k y ≠ 0) :
    closedSubschemeCycleCoeff C q i k y = 1 := by
  classical
  unfold closedSubschemeCycleCoeff at hy ⊢
  split at hy
  · rename_i h
    rw [dite_eq_left h]
    exact componentMultiplicity_eq_one_of_isReduced i _
  · exact absurd rfl hy

variable {X S S' : Scheme.{u}}

/-- **Multiplicity one at a separable point.** If the residue field extension `κ(t)/κ(g t)` is
separable then every nonzero base-change multiplicity on the fibre of `X ×_S S'` over `t` is
one: the reduced closure of the image point stays reduced after the base change, and a reduced
closed subscheme occurs with multiplicity one. -/
theorem flatPullbackWeight_eq_one_of_isSeparableExtension (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (t : S')
    (hsep : letI : Algebra ↥(S.residueField (g t)) ↥(S'.residueField t) :=
        (g.residueFieldMap t).hom.toAlgebra
      Algebra.IsSeparableExtension ↥(S.residueField (g t)) ↥(S'.residueField t))
    (j : ℤ) (y : (pullback.snd f g).fiber t)
    (hne : flatPullbackWeight (fieldChowSituation ↥(S'.residueField t))
        ((pullback.snd f g).fiberToSpecResidueField t)
        (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t)
        j y ≠ 0) :
    flatPullbackWeight (fieldChowSituation ↥(S'.residueField t))
        ((pullback.snd f g).fiberToSpecResidueField t)
        (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t)
        j y = 1 := by
  have hgr : GeometricallyReduced (residueFieldBaseChangeSituation g t).g :=
    @geometricallyReduced_specMap_algebraMap_of_isSeparableExtension
      ↥(S.residueField (g t)) ↥(S'.residueField t) _ _ (g.residueFieldMap t).hom.toAlgebra hsep
  have := isReduced_comap_of_isPullback_of_geometricallyReduced
    (isPullback_restrictedFiberMap_baseChange f g t) hgr
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
      ({restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t y} :
        Set (f.fiber (g t)))))
    (Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _)
  exact closedSubschemeCycleCoeff_eq_one_of_isReduced _ _ _ j y hne

end Stacks.Chow

end
