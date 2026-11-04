module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.FieldTheory.IsSepClosed
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.GaloisInvariantClosed
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleGaloisAction
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleSeparableClosure

/-!
# Descent of fixed geometric irreducible components

An irreducible component after extension to a separable closure is fixed by the Galois action
exactly when it is the base change of a geometrically irreducible component over the ground
field.  Invariance of the underlying closed subset lets it descend, and the descended component
is geometrically irreducible because its own base change is the irreducible component one
started from.

## Main results

* `AlgebraicGeometry.fixed_geometricComponent_iff_exists_geometricallyIrreducible_component`
  characterizes the fixed geometric components by descent to geometrically irreducible
  components.

## Implementation notes

An irreducible component is a member of `irreducibleComponents`.  Its canonical reduced closed
subscheme is defined by its vanishing ideal.  Geometric irreducibility is imposed on the
structure morphism of that subscheme, and the equality of components is the equality of their
underlying closed subsets after base change.

## References

* [Stacks Project, Tag 038J](https://stacks.math.columbia.edu/tag/038J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- A closed set whose preimage under a continuous, surjective, generalizing map is an
irreducible component is itself an irreducible component. -/
theorem mem_irreducibleComponents_of_preimage_eq {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [QuasiSober X] [QuasiSober Y] {p : Y → X} (hp : Continuous p)
    (hsurj : Function.Surjective p) (hgen : GeneralizingMap p) {S : Set Y}
    (hS : S ∈ irreducibleComponents Y) {T : Set X} (hT : IsClosed T) (hpre : p ⁻¹' T = S) :
    T ∈ irreducibleComponents X := by
  have hTirr : IsIrreducible T := by
    rw [← Set.image_preimage_eq T hsurj, hpre]
    exact hS.1.image p hp.continuousOn
  obtain ⟨T', hT', hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible T hTirr
  obtain ⟨η, hη⟩ : ∃ η, closure ({η} : Set Y) = S :=
    ⟨_, hS.1.closure_genericPoint (isClosed_of_mem_irreducibleComponents S hS)⟩
  obtain ⟨η', hη'⟩ : ∃ η', closure ({η'} : Set X) = T' :=
    ⟨_, hT'.1.closure_genericPoint (isClosed_of_mem_irreducibleComponents T' hT')⟩
  have hηT : p η ∈ T := by
    rw [← Set.mem_preimage, hpre, ← hη]
    exact subset_closure rfl
  have hspec : η' ⤳ p η := by
    rw [specializes_iff_mem_closure, hη']
    exact hsub hηT
  obtain ⟨z, hz, hpz⟩ := hgen hspec
  have hSz : S ⊆ closure ({z} : Set Y) := by
    rw [← hη]
    exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hz))
      isClosed_closure
  have hzS : z ∈ S := hS.2 isIrreducible_singleton.closure hSz (subset_closure rfl)
  have hT'T : T' ⊆ T := by
    rw [← hη']
    refine closure_minimal (Set.singleton_subset_iff.mpr ?_) hT
    rw [← hpz, ← Set.mem_preimage, hpre]
    exact hzS
  rwa [Set.Subset.antisymm hsub hT'T]

/-- A closed subset whose preimage in the base change to a separable closure is irreducible
has a geometrically irreducible reduced closed subscheme. -/
theorem geometricallyIrreducible_vanishingIdeal_subschemeι_comp
    (k ksep : Type u) [Field k] [Field ksep] [Algebra k ksep] [IsSepClosure k ksep]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (T : TopologicalSpace.Closeds X)
    {S : Set (pullback (C := Scheme) f
      (Spec.map (CommRingCat.ofHom (algebraMap k ksep))))}
    (hS : IsIrreducible S)
    (hpre : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k ksep)))).base ⁻¹'
      (T : Set X) = S) :
    GeometricallyIrreducible ((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫ f) := by
  let p := pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k ksep)))
  let I : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal T
  have hIsupport : (I.support : Set X) = T :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal T
  let J := I.comap p
  have hJrange : Set.range J.subschemeι = S := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap]
    simpa only [TopologicalSpace.Closeds.coe_preimage, hIsupport] using hpre
  have hJirr : IrreducibleSpace J.subscheme := by
    let e := J.subschemeι.isClosedEmbedding.isEmbedding.homeomorphImage Set.univ
    have hImageIrr : IrreducibleSpace ↥(J.subschemeι '' Set.univ) := by
      rw [Set.image_univ, hJrange]
      exact Subtype.irreducibleSpace hS
    have hUnivIrr : IrreducibleSpace ↥Set.univ := e.irreducibleSpace_iff.mpr hImageIrr
    exact (Homeomorph.Set.univ J.subscheme).irreducibleSpace_iff.mp hUnivIrr
  let q := I.subschemeι ≫ f
  let eComap : J.subscheme ≅ pullback I.subschemeι p :=
    I.comapIso p ≪≫ pullbackSymmetry p I.subschemeι
  let e : pullback q (Spec.map (CommRingCat.ofHom (algebraMap k ksep))) ≅ J.subscheme :=
    (pullbackRightPullbackFstIso f _ I.subschemeι).symm ≪≫ eComap.symm
  exact ((geometricallyIrreducible_tfae_of_isSepClosure k I.subscheme q ksep).out 1 3).mpr
    (e.schemeIsoToHomeo.irreducibleSpace_iff.mpr hJirr)

/-- A geometric irreducible component is fixed by the Galois action exactly when it descends
to a geometrically irreducible component of the original scheme. -/
@[stacks 038J "fixed_component_descent"]
theorem fixed_geometricComponent_iff_exists_geometricallyIrreducible_component
    (k ksep : Type u) [Field k] [Field ksep] [Algebra k ksep]
    [IsSepClosure k ksep]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    (Tbar : (galoisActionOnGeometricIrreducibleComponents k ksep (Over.mk f)).V) :
    (∀ σ : MulOpposite (ksep ≃ₐ[k] ksep),
      ConcreteCategory.hom
        ((galoisActionOnGeometricIrreducibleComponents k ksep (Over.mk f)).ρ σ) Tbar =
        Tbar) ↔
      ∃ T : irreducibleComponents X,
        GeometricallyIrreducible
          ((Scheme.IdealSheafData.vanishingIdeal
              ⟨(T : Set X), isClosed_of_mem_irreducibleComponents T.1 T.2⟩).subschemeι ≫ f) ∧
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k ksep)))).base ⁻¹'
          (T : Set X) = Tbar.1 := by
  let p := pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k ksep)))
  constructor
  · intro hfixed
    have hstable : ∀ σ : ksep ≃ₐ[k] ksep,
        (galoisBaseChangeMap k ksep X f σ) ⁻¹' Tbar.1 = Tbar.1 := by
      intro σ
      let g : pullback f (Spec.map (CommRingCat.ofHom (algebraMap k ksep))) ⟶
          pullback f (Spec.map (CommRingCat.ofHom (algebraMap k ksep))) :=
        galoisBaseChangeMap k ksep X f σ
      have himage : g '' Tbar.1 = Tbar.1 := congrArg Subtype.val (hfixed (MulOpposite.op σ))
      have hbij : Function.Bijective g.base :=
        (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso
          ((galoisActionOnBaseChange k ksep (Over.mk f)).ρAut (MulOpposite.op σ)))).bijective
      exact (Set.preimage_eq_iff_eq_image hbij).mpr himage.symm
    obtain ⟨T, hTclosed, hpre⟩ :=
      exists_closed_subset_with_preimage_eq_of_galois_invariant
        k ksep X f Tbar.1 (isClosed_of_mem_irreducibleComponents Tbar.1 Tbar.2) hstable
    have hT : T ∈ irreducibleComponents X :=
      mem_irreducibleComponents_of_preimage_eq p.continuous p.surjective
        (Flat.generalizingMap p) Tbar.2 hTclosed hpre
    exact ⟨⟨T, hT⟩, geometricallyIrreducible_vanishingIdeal_subschemeι_comp k ksep f
      ⟨T, hTclosed⟩ Tbar.2.1 hpre, hpre⟩
  · rintro ⟨T, -, hpre⟩ σ
    let a := (galoisActionOnBaseChange k ksep (Over.mk f)).ρ σ
    have hcommute : a ≫ p = p := by
      dsimp [a, p, galoisActionOnBaseChange, pullback.map]
      rw [pullback.lift_fst]
      simp
    let e := Scheme.homeoOfIso
      ((galoisActionOnBaseChange k ksep (Over.mk f)).ρAut σ)
    have hbar : e ⁻¹' Tbar.1 = Tbar.1 := by
      rw [← hpre]
      ext x
      have hx := congrArg (fun q : _ ⟶ X => q.base x) hcommute
      change (TopCat.Hom.hom p.base) ((TopCat.Hom.hom a.base) x) = p x at hx
      show (TopCat.Hom.hom p.base) ((TopCat.Hom.hom a.base) x) ∈ (T : Set X) ↔
        p x ∈ (T : Set X)
      rw [hx]
    apply Subtype.ext
    rw [galoisActionOnGeometricIrreducibleComponents_ρ_apply_coe]
    show e '' Tbar.1 = Tbar.1
    exact ((Set.preimage_eq_iff_eq_image e.bijective).mp hbar).symm

end AlgebraicGeometry

end
