module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectOverField
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectTriangulatedCanonical
public import StacksFrontier.AlgebraicGeometry.DerivedTildePerfect
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.NoetherianCoherent
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic

/-!
# Relative perfectness over a field is not perfectness on the fibres

Let `k` be a field and let `X` be a scheme of finite presentation over `k`. By Stacks 0DI1,
`AlgebraicGeometry.isPerfectRelativeTo_canonical_iff_boundedCoherent`, the `Spec k`-perfect
objects of `D(𝒪_X)` are exactly the objects of `D^b_Coh(𝒪_X)`. The base being a point, the only
fibre of `X ⟶ Spec k` is `X` itself, so the closing sentence of that example — relative
perfectness does **not** mean perfectness on the fibres — says that some bounded complex with
coherent cohomology on such an `X` is not a perfect object of `D(𝒪_X)`.

This file exhibits one. Take `X = Spec k[ε]`, the dual numbers, which is of finite presentation
over `k`, and take the sheaf associated with the residue field `k[ε]/(ε)`, placed in degree zero.
It is coherent, hence `Spec k`-perfect; and it is not perfect, because by Stacks 08EB
perfectness of `M̃` on an affine scheme is perfectness of `M` over the ring, and the residue
field of the dual numbers is not a perfect module — a perfect finite module over a Noetherian
local ring would force the ring to be regular, hence a domain, and `ε² = 0`.

## Main definitions

* `AlgebraicGeometry.dualNumberStructureMap`: the structure morphism `Spec k[ε] ⟶ Spec k`.
* `AlgebraicGeometry.dualNumberResidueComplex`: the residue field of `k[ε]`, sheafified and
  placed in cohomological degree zero.

## Main results

* `AlgebraicGeometry.derivedCategoryBBounded_singleFunctor_obj`: a coherent module on a scheme,
  placed in degree zero, lies in `D^b_Coh(𝒪_X)`.
* `AlgebraicGeometry.isPerfectRelativeTo_dualNumberResidueComplex_and_not_isPerfect`: the
  witness, in one statement — the residue complex of `Spec k[ε]` is `Spec k`-perfect and is not
  perfect.
* `AlgebraicGeometry.not_isZero_dualNumberResidueComplex`: the witness is not a zero object.
* `AlgebraicGeometry.exists_not_isZero_isPerfectRelativeTo_dualNumber`: the subcategory of Stacks
  0DI3 is not the zero subcategory — at `Spec k[ε] ⟶ Spec k`, which is flat and locally of finite
  presentation, it contains a nonzero object.

## References

* [Stacks Project, Example 36.35.2 (Tag 0DI1)](https://stacks.math.columbia.edu/tag/0DI1)
* [Stacks Project, Lemma 36.10.7 (Tag 08EB)](https://stacks.math.columbia.edu/tag/08EB)
* [Stacks Project, Lemma 36.35.4 (Tag 0DI3)](https://stacks.math.columbia.edu/tag/0DI3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

universe u

namespace AlgebraicGeometry

section SingleObject

attribute [local instance] HasDerivedCategory.standard

/-- **A coherent module placed in cohomological degree zero lies in `D^b_Coh(𝒪_X)`.** Its
cohomology is the module itself in degree zero and zero in every other degree, so it is bounded
on both sides, and the zero module is coherent. -/
public theorem derivedCategoryBBounded_singleFunctor_obj (X : Scheme.{u})
    (F : OXMod.{u, u} X.toRingedSpace) (hF : F.IsCoherent) :
    DerivedCategoryB.derivedCategoryBBounded
      (fun M : OXMod.{u, u} X.toRingedSpace => M.IsCoherent)
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj F) := by
  have e : ∀ i : ℤ, (DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) i).obj
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj F) ≅
      ((CochainComplex.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj F).homology i :=
    fun i => (DerivedCategory.homologyFunctorFactors (OXMod.{u, u} X.toRingedSpace) i).app _
  have hzero : ∀ i : ℤ, i ≠ 0 → IsZero
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) i).obj
        ((DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj F)) :=
    fun i hi => (HomologicalComplex.isZero_single_obj_homology _ _ _ _ hi).of_iso (e i)
  refine ⟨⟨⟨0, fun n hn => hzero n (by omega)⟩, ⟨0, fun n hn => hzero n (by omega)⟩⟩, fun n => ?_⟩
  by_cases hn : n = 0
  · subst hn
    exact ObjectProperty.prop_of_iso
      (P := fun M : OXMod.{u, u} X.toRingedSpace => M.IsCoherent)
      (e 0 ≪≫ HomologicalComplex.singleObjHomologySelfIso _ _ _).symm hF
  · exact ObjectProperty.prop_of_isZero
      (P := fun M : OXMod.{u, u} X.toRingedSpace => M.IsCoherent) (hzero n hn)

end SingleObject

/-! ### The dual numbers -/

/-- The structure morphism `Spec k[ε] ⟶ Spec k` of the dual numbers over a field. -/
public def dualNumberStructureMap (k : Type u) [Field k] :
    Spec (CommRingCat.of (DualNumber k)) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))

/-- `Spec k[ε] ⟶ Spec k` is locally of finite presentation: the dual numbers are a finitely
presented `k`-algebra, by `AlgebraicGeometry.finitePresentation_dualNumber`. -/
public instance locallyOfFinitePresentation_dualNumberStructureMap (k : Type u) [Field k] :
    LocallyOfFinitePresentation (dualNumberStructureMap k) := by
  rw [dualNumberStructureMap, LocallyOfFinitePresentation.SpecMap_iff]
  exact RingHom.finitePresentation_algebraMap.2 (finitePresentation_dualNumber k)

section Witness

attribute [local instance] HasDerivedCategory.standard

/-- **The residue field of the dual numbers, sheafified and placed in degree zero.** This is the
object of `D(𝒪_{Spec k[ε]})` which is `Spec k`-perfect without being perfect. -/
public def dualNumberResidueComplex (k : Type u) [Field k] :
    DerivedCategory (OXMod.{u, u} (Spec (CommRingCat.of (DualNumber k))).toRingedSpace) :=
  (tilde.functor (CommRingCat.of (DualNumber k))).mapDerivedCategory.obj
    ((DerivedCategory.singleFunctor (ModuleCat.{u} (CommRingCat.of (DualNumber k))) 0).obj
      (ModuleCat.of _ (IsLocalRing.ResidueField (DualNumber k))))

/-- The residue complex of `Spec k[ε]` lies in `D^b_Coh`: it is the sheaf associated with a
finite module over a Noetherian ring, placed in a single degree. -/
public theorem derivedCategoryBBounded_dualNumberResidueComplex (k : Type u) [Field k] :
    DerivedCategoryB.derivedCategoryBBounded
      (fun M : OXMod.{u, u} (Spec (CommRingCat.of (DualNumber k))).toRingedSpace =>
        M.IsCoherent)
      (dualNumberResidueComplex k) := by
  obtain ⟨hb, hc⟩ := derivedCategoryBBounded_singleFunctor_obj
    (Spec (CommRingCat.of (DualNumber k)))
    ((tilde.functor (CommRingCat.of (DualNumber k))).obj
      (ModuleCat.of _ (IsLocalRing.ResidueField (DualNumber k))))
    (CoherentAbelian.isCoherent_of_stacksIsCoherent
      (Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_tilde _))
  have e := (((tilde.functor (CommRingCat.of (DualNumber k))).mapDerivedCategorySingleFunctor
    0).app (ModuleCat.of _ (IsLocalRing.ResidueField (DualNumber k)))).symm
  refine ⟨DerivedCategoryB.isBounded_of_iso e hb, fun i => ?_⟩
  exact ObjectProperty.prop_of_iso
    (P := fun M : OXMod.{u, u} (Spec (CommRingCat.of (DualNumber k))).toRingedSpace =>
      M.IsCoherent)
    ((DerivedCategory.homologyFunctor
      (OXMod.{u, u} (Spec (CommRingCat.of (DualNumber k))).toRingedSpace) i).mapIso e) (hc i)

/-- **Stacks 0DI1, the closing warning.** Over a field, relative perfectness is not perfectness
on the fibres: the residue field of the dual numbers, sheafified and placed in degree zero, is
`Spec k`-perfect on the scheme `Spec k[ε]` — which is of finite presentation over `k`, and whose
only fibre over `Spec k` is itself — and it is not a perfect object of `D(𝒪_{Spec k[ε]})`.

The first half is Stacks 0DI1 itself,
`AlgebraicGeometry.isPerfectRelativeTo_canonical_iff_boundedCoherent`, applied to a coherent
module in degree zero. The second is Stacks 08EB,
`AlgebraicGeometry.isPerfect_tilde_iff`, against
`AlgebraicGeometry.not_isPerfectModule_residueField_dualNumber`. -/
@[stacks 0DI1 "relative perfectness over a field is not perfectness on the fibres"]
public theorem isPerfectRelativeTo_dualNumberResidueComplex_and_not_isPerfect (k : Type u)
    [Field k] :
    (dualNumberStructureMap k).IsPerfectRelativeTo
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
          (RingedSpace.inverseImage (Spec (CommRingCat.of k)).toRingedSpace
            (dualNumberStructureMap k).base))
        (dualNumberResidueComplex k) ∧
      ¬ Stacks.Cohomology.PerfectComplexes.IsPerfect
          (X := (Spec (CommRingCat.of (DualNumber k))).toRingedSpace)
          (dualNumberResidueComplex k) := by
  refine ⟨(isPerfectRelativeTo_canonical_iff_boundedCoherent k (dualNumberStructureMap k)
    (dualNumberResidueComplex k)).2 (derivedCategoryBBounded_dualNumberResidueComplex k),
    fun h => not_isPerfectModule_residueField_dualNumber k ?_⟩
  exact (isPerfect_tilde_iff _).1 h

/-- **The residue complex of `Spec k[ε]` is not a zero object.** A zero object of `D(𝒪_X)` is
perfect, and this one is not.

The witness of `AlgebraicGeometry.isPerfectRelativeTo_dualNumberResidueComplex_and_not_isPerfect`
is a genuine one: the closing warning of Stacks 0DI1 is not satisfied by the zero complex, for
which the two conditions it separates coincide. -/
public theorem not_isZero_dualNumberResidueComplex (k : Type u) [Field k] :
    ¬ IsZero (dualNumberResidueComplex k) := fun h =>
  (isPerfectRelativeTo_dualNumberResidueComplex_and_not_isPerfect k).2
    (RingedSpace.isPerfect_of_isZero.{u, u + 1}
      (X := (Spec (CommRingCat.of (DualNumber k))).toRingedSpace) h)

/-- **The subcategory of Stacks 0DI3 is not the zero subcategory.** The structure morphism
`Spec k[ε] ⟶ Spec k` is flat and locally of finite presentation, and the `Spec k`-perfect objects
of `D(𝒪_{Spec k[ε]})` — the object property that
`AlgebraicGeometry.Scheme.Hom.isClosedUnderIsomorphisms_isPerfectRelativeTo`,
`AlgebraicGeometry.Scheme.Hom.isSaturated_isPerfectRelativeTo` and
`AlgebraicGeometry.Scheme.Hom.isTriangulated_isPerfectRelativeTo_canonical` prove to be a strictly
full saturated triangulated subcategory — contain a nonzero object.

A triangulated subcategory contains the zero object by definition, so this is what says that the
three closure properties are not being asserted of the zero subcategory. The nonzero object is
the residue complex of the dual numbers, which is moreover not perfect; a reader wanting the two
facts together should use
`AlgebraicGeometry.isPerfectRelativeTo_dualNumberResidueComplex_and_not_isPerfect`.

This is not a clause of Stacks 0DI3 and carries no attribute. -/
public theorem exists_not_isZero_isPerfectRelativeTo_dualNumber (k : Type u) [Field k] :
    ∃ E : DerivedCategory
        (OXMod.{u, u} (Spec (CommRingCat.of (DualNumber k))).toRingedSpace),
      ¬ IsZero E ∧
        Scheme.Hom.isPerfectRelativeTo (dualNumberStructureMap k)
          (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
            (RingedSpace.inverseImage (Spec (CommRingCat.of k)).toRingedSpace
              (dualNumberStructureMap k).base)) E :=
  ⟨dualNumberResidueComplex k, not_isZero_dualNumberResidueComplex k,
    (isPerfectRelativeTo_dualNumberResidueComplex_and_not_isPerfect k).1⟩

end Witness

end AlgebraicGeometry

end
