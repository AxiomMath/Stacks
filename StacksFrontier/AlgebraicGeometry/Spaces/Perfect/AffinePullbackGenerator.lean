module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentWeakSerreSchemeUniverse
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageSystemProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPushforwardAffineConservative
public import StacksFrontier.CategoryTheory.Triangulated.Generators
public import StacksFrontier.CategoryTheory.Triangulated.LocallySmallCompactEnvelope
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentWeakSerre

/-!
# Pulling back a compact generator of `D_QCoh` along an affine morphism

Let `g : X ⟶ X₀` be an affine morphism of algebraic spaces and `G` a compact object of
`D_QCoh(𝒪_{X₀})` which is a weak generator. Then `Lg^*G` is a compact weak generator of
`D_QCoh(𝒪_X)`: it is compact because `Rg_*` commutes with direct sums on `D_QCoh`, and it is a
weak generator because `Hom(Lg^*G[n], K) = Hom(G[n], Rg_*K)` and `Rg_*` is conservative on
`D_QCoh` for affine `g`.

## Main results

* `AlgebraicGeometry.Space.isWeakTriangulatedGenerator_quasicoherentDerivedModulePullback`: the
  weak generation statement above.

## References

* [Stacks Project, Tag 09IY](https://stacks.math.columbia.edu/tag/09IY)
* [Stacks Project, Tag 01S7](https://stacks.math.columbia.edu/tag/01S7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {B S hS}

/-- **The derived pullback of a compact weak generator of `D_QCoh` along an affine morphism is
a compact weak generator.** -/
theorem isCompactObject_and_isWeakTriangulatedGenerator_quasicoherentDerivedModulePullback
    {X X₀ : AlgebraicSpaces B S hS} (g : X ⟶ X₀) (hg : IsAffineHom B S hS g.hom)
    (G : QuasicoherentDerivedCategory.{u, u} B S hS X₀.1 X₀.2) (hGc : IsCompactObject.{u} G)
    (hG : (ObjectProperty.singleton G).IsWeakTriangulatedGenerator) :
    IsCompactObject.{u} ((quasicoherentDerivedModulePullback g).obj G) ∧
      (ObjectProperty.singleton
        ((quasicoherentDerivedModulePullback g).obj G)).IsWeakTriangulatedGenerator := by
  have hqc := isQuasiCompact_of_isAffineHom' B S hS g.hom X.2 X₀.2 hg
  have hqs := isQuasiSeparated_of_isAffineHom B S hS g.hom X.2 X₀.2 hg
  refine ⟨isCompactObject_quasicoherentDerivedModulePullback g hqc hqs G hGc, ?_⟩
  rw [ObjectProperty.isWeakTriangulatedGenerator_iff]
  intro K hK
  let R := quasicoherentDerivedPushforward B S hS g hqc hqs
  let adj := quasicoherentDerivedModuleAdjunction B S hS g hqc hqs
  have hRK : ¬ IsZero (R.obj K) := fun h =>
    hK (ObjectProperty.isZero_fullSubcategory_of_isZero_obj
      (isZero_of_isZero_derivedModulePushforward_of_isAffineHom B S hS g hg K.obj K.property
        ((ObjectProperty.ι _).map_isZero h |>.of_iso
          ((quasicoherentDerivedPushforwardCompιIso B S hS g hqc hqs).app K).symm)))
  obtain ⟨E, hE, n, f, hf⟩ := (ObjectProperty.isWeakTriangulatedGenerator_iff _).1 hG _ hRK
  obtain rfl := (ObjectProperty.singleton_iff _ _).1 hE
  refine ⟨_, (ObjectProperty.singleton_iff _ _).2 rfl, n,
    adj.homEquiv _ _ |>.symm (f ≫ (R.commShiftIso n).inv.app K), fun h0 => hf ?_⟩
  have := congrArg (adj.homEquiv _ _) h0
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_apply, Functor.map_zero, comp_zero] at this
  rw [← cancel_mono ((R.commShiftIso n).inv.app K), this, zero_comp]

/-- **Compact objects of `D_QCoh` lie in the triangulated envelope of a compact weak generator.**
A property of objects of `D_QCoh(𝒪_X)` which is triangulated, stable under retracts and holds
for a compact weak generator holds for every compact object (Stacks 09SR). -/
theorem prop_of_isCompactObject_of_isWeakTriangulatedGenerator {X : AlgebraicSpaces B S hS}
    (G : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) (hGc : IsCompactObject.{u} G)
    (hG : (ObjectProperty.singleton G).IsWeakTriangulatedGenerator)
    (Φ : ObjectProperty (QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2))
    [Φ.IsTriangulated] [Φ.IsStableUnderRetracts] (hΦG : Φ G)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) (hE : IsCompactObject.{u} E) :
    Φ E := by
  have := isGrothendieckAbelian_modules_ringUniverse B S hS X.1 X.2
  have := enoughInjectives_modules_ringUniverse B S hS X.1 X.2
  have := hasCoproducts_quasicoherentDerivedCategory_ringUniverse B S hS X.1 X.2
  have hle : (ObjectProperty.singleton G).triangEnvelope ≤ Φ := by
    rwa [ObjectProperty.triangEnvelope_le_iff, ObjectProperty.singleton_le_iff]
  exact hle _
    (CategoryTheory.Pretriangulated.triangEnvelope_eq_isCompactObject_of_locallySmall G hGc hG ▸ hE)

end AlgebraicGeometry.Space

end
