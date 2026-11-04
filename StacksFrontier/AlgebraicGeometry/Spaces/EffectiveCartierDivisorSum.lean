module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPresentations
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.AlgebraicGeometry.Groupoids.InvariantSubobject
public import StacksFrontier.AlgebraicGeometry.Scheme.IdealSheafComapMul
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleCharts

/-!
# The sum of two effective Cartier divisors on an algebraic space

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let
`D₁, D₂ ⊆ X` be closed subspaces. Following Stacks 083U their *sum* is the closed subspace cut
out by the product `𝓘_{D₁} 𝓘_{D₂}` of their defining ideals. On a surjective étale scheme chart
`φ : U ⟶ X` the base change of `Dᵢ` is a closed immersion of schemes with ideal sheaf
`AlgebraicGeometry.Space.chartKer`; the closed subscheme cut out by the product of the two ideal
sheaves is invariant under the relation `R = U ×_X U`, and its descent is the sum.

## Main definitions

* `AlgebraicGeometry.Space.chartKer`: the ideal sheaf of the base change of a closed subspace
  along a scheme chart.
* `AlgebraicGeometry.Space.sumOfChart`: the sum formed on a given surjective étale chart.
* `AlgebraicGeometry.Space.sumClosedSubspaces`: the sum `D₁ + D₂` of Stacks 083U, formed on the
  chart supplied by the algebraic-space hypothesis.
* `AlgebraicGeometry.Space.definingIdealTensorMul`: the multiplication
  `𝓘_{D₁} ⊗_{𝒪_X} 𝓘_{D₂} ⟶ 𝒪_X` of two defining ideal sheaves on the small étale site of `X`.

## Main results

* `AlgebraicGeometry.Space.comap_chartKer`: the chart ideal sheaves of a closed subspace are
  compatible with change of chart.
* `AlgebraicGeometry.Space.isInvariantSubscheme_mul_chartKer`: the closed subscheme cut out by
  the product of two chart ideal sheaves is invariant under the relation of the chart.
* `AlgebraicGeometry.Space.definingIdealAt_sumOfChart` and
  `AlgebraicGeometry.Space.definingIdealAt_sumClosedSubspaces`: over an étale chart lying over the
  chart used to form the sum, the defining ideal of the sum is the ideal of regular functions
  killed by the closed subscheme that the product of the chart ideal sheaves cuts out there.
* `AlgebraicGeometry.Space.definingIdealAt_sumClosedSubspaces_of_isAffine`: on an affine étale
  chart the defining ideal of the sum is the product of the defining ideals of the summands.
* `AlgebraicGeometry.Space.eq_sumOfChart_of_definingIdealAt`: that formula on the affine charts
  determines the sum among all closed subspaces of `X`.
* `CategoryTheory.Equivalence.mono_functor_map`: an equivalence of categories carries
  monomorphisms to monomorphisms.
* `AlgebraicGeometry.Space.tensorRightFunctor_map_ι`: the first factor of
  `definingIdealTensorMul` is the image of the inclusion `𝓘_{D₁} ⟶ 𝒪_X` under the functor
  "tensor on the right by `𝓘_{D₂}`".

## Implementation notes

The sum is formed for arbitrary closed subspaces rather than only for effective Cartier
divisors: neither the product of the ideal sheaves nor the descent of the closed subscheme it cuts
out uses invertibility.

`AlgebraicGeometry.Space.sumClosedSubspaces` is formed on the surjective étale chart supplied by
`AlgebraicGeometry.IsAlgebraicSpace.exists_atlas`, and the product is taken in
`AlgebraicGeometry.Scheme.IdealSheafData` on that chart. By
`AlgebraicGeometry.Space.eq_sumOfChart_of_definingIdealAt` the result does not depend on the
chart.

## References

* [Stacks Project, Tag 083U](https://stacks.math.columbia.edu/tag/083U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.Equivalence

/-- An equivalence of categories carries monomorphisms to monomorphisms. -/
theorem mono_functor_map {C D : Type*} [Category C] [Category D] (e : C ≌ D)
    {A Y : C} (f : A ⟶ Y) [Mono f] : Mono (e.functor.map f) :=
  inferInstance

end CategoryTheory.Equivalence

namespace AlgebraicGeometry

/-- The closed subscheme cut out by the kernel of a closed immersion presents the same
subobject as the closed immersion itself. -/
theorem Scheme.subobject_mk_ker_subschemeι {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    [IsClosedImmersion f] :
    Subobject.mk f.ker.subschemeι = Subobject.mk f := by
  have h : f.ker.subschemeι.ker = f.ker := Scheme.IdealSheafData.ker_subschemeι _
  have := IsClosedImmersion.isIso_lift f.ker.subschemeι f h
  exact (Subobject.mk_eq_mk_of_comm f f.ker.subschemeι
    (asIso (IsClosedImmersion.lift f.ker.subschemeι f h.le))
    (IsClosedImmersion.lift_fac _ _ _)).symm

/-- The ideal sheaf of a product of ideals of the global sections is the product of their
ideal sheaves. -/
theorem Scheme.IdealSheafData.ofIdealTop_mul {X : Scheme.{u}} (I J : Ideal Γ(X, ⊤)) :
    ofIdealTop I * ofIdealTop J = ofIdealTop (I * J) := by
  ext U : 2
  simp [Ideal.map_mul]

/-- On an affine scheme the closed subscheme cut out by an ideal of the global sections kills
exactly that ideal. -/
theorem Scheme.IdealSheafData.ker_appTop_subschemeι_ofIdealTop {X : Scheme.{u}} [IsAffine X]
    (I : Ideal Γ(X, ⊤)) :
    RingHom.ker ((ofIdealTop I).subschemeι.appTop).hom = I := by
  have h : RingHom.ker ((ofIdealTop I).subschemeι.appTop).hom =
      (ofIdealTop I).ideal ⟨⊤, isAffineOpen_top X⟩ :=
    ker_subschemeι_app _ ⟨⊤, isAffineOpen_top X⟩
  rw [h]
  simp

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS)

/-! ### The ideal sheaf of a closed subspace on a scheme chart -/

/-- The ideal sheaf on a scheme chart of `X` cutting out the base change of a closed subspace
of `X`. -/
noncomputable def chartKer {U : BigFppfOver B S hS} (D : ClosedSubspaces B S hS X.1)
    (φ : yoneda.obj U ⟶ X.1) :
    ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData :=
  ((BigFppfOver.toScheme B S hS).map (D.2.2.rep.snd φ)).ker

/-- The chart ideal sheaf is the kernel of pullback of regular functions along the base change
of the inclusion of the closed subspace. -/
theorem chartKer_eq {U : BigFppfOver B S hS} (D : ClosedSubspaces B S hS X.1)
    (φ : yoneda.obj U ⟶ X.1) :
    chartKer B S hS X D φ = ((BigFppfOver.toScheme B S hS).map (D.2.2.rep.snd φ)).ker :=
  rfl

/-- The base change of a closed subspace along a chart is a closed immersion of schemes. -/
instance isClosedImmersion_rep_snd {U : BigFppfOver B S hS}
    (D : ClosedSubspaces B S hS X.1) (φ : yoneda.obj U ⟶ X.1) :
    _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (D.2.2.rep.snd φ)) :=
  D.2.2.property_snd φ

/-- The subobject presented by the chart ideal sheaf of a closed subspace is the one presented
by the base change of its inclusion. -/
theorem subobject_mk_chartKer {U : BigFppfOver B S hS} (D : ClosedSubspaces B S hS X.1)
    (φ : yoneda.obj U ⟶ X.1) :
    Subobject.mk (chartKer B S hS X D φ).subschemeι =
      Subobject.mk ((BigFppfOver.toScheme B S hS).map (D.2.2.rep.snd φ)) :=
  Scheme.subobject_mk_ker_subschemeι _

/-- Along a morphism of charts the inverse image of the chart ideal sheaf at the target is the
chart ideal sheaf at the source. -/
theorem comap_chartKer {U V : BigFppfOver B S hS} (D : ClosedSubspaces B S hS X.1)
    (φ : yoneda.obj U ⟶ X.1) (r : V ⟶ U) (ψ : yoneda.obj V ⟶ X.1)
    (hψ : yoneda.map r ≫ φ = ψ) :
    (chartKer B S hS X D φ).comap ((BigFppfOver.toScheme B S hS).map r) =
      chartKer B S hS X D ψ := by
  rw [← Scheme.IdealSheafData.subobject_mk_subschemeι_inj,
    ← Scheme.IdealSheafData.subobject_pullback_mk_subschemeι, subobject_mk_chartKer,
    subobject_mk_chartKer]
  exact pullback_obj_mk_snd B S hS φ D.2.2.rep r ψ hψ

/-! ### The sum formed on a chart -/

section Chart

variable {U : BigFppfOver B S hS} {φ : yoneda.obj U ⟶ X.1}
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)

include hs in
/-- The closed subscheme cut out by the product of the chart ideal sheaves of two closed
subspaces is invariant under the relation of the chart. -/
theorem isInvariantSubscheme_mul_chartKer (D₁ D₂ : ClosedSubspaces B S hS X.1) :
    IsInvariantSubscheme B S hS hs
      (Subobject.mk (chartKer B S hS X D₁ φ * chartKer B S hS X D₂ φ).subschemeι) := by
  show (Subobject.pullback ((BigFppfOver.toScheme B S hS).map
      (atlasRelationTarget B S hS hs))).obj
        (Subobject.mk (chartKer B S hS X D₁ φ * chartKer B S hS X D₂ φ).subschemeι) =
      (Subobject.pullback ((BigFppfOver.toScheme B S hS).map
        (atlasRelationSource B S hS hs))).obj
        (Subobject.mk (chartKer B S hS X D₁ φ * chartKer B S hS X D₂ φ).subschemeι)
  rw [Scheme.IdealSheafData.subobject_pullback_mk_subschemeι,
    Scheme.IdealSheafData.subobject_pullback_mk_subschemeι,
    Scheme.IdealSheafData.subobject_mk_subschemeι_inj,
    Stacks.IdealSheaf.comap_mul, Stacks.IdealSheaf.comap_mul,
    comap_chartKer B S hS X D₁ φ _ _ rfl, comap_chartKer B S hS X D₂ φ _ _ rfl,
    comap_chartKer B S hS X D₁ φ _ _ (yoneda_map_atlasRelationSource_comp B S hS hs),
    comap_chartKer B S hS X D₂ φ _ _ (yoneda_map_atlasRelationSource_comp B S hS hs)]

include hs he in
/-- The sum of two closed subspaces formed on a chart: the closed subspace of `X` descended from
the closed subscheme that the product of the chart ideal sheaves of `D₁` and `D₂` cuts out on a
surjective étale scheme chart `φ : U ⟶ X`. -/
noncomputable def sumOfChart (D₁ D₂ : ClosedSubspaces B S hS X.1) :
    ClosedSubspaces B S hS X.1 :=
  ⟨invariantSubspace B S hS φ
    (Subobject.mk (chartKer B S hS X D₁ φ * chartKer B S hS X D₂ φ).subschemeι),
    isClosedSubspace_invariantSubspace_subschemeι B S hS X hs he _
      (isInvariantSubscheme_mul_chartKer B S hS X hs D₁ D₂)⟩

include hs he in
/-- Over an étale chart `A` of `X` lying over the chart used to form the sum, the defining ideal of
the sum is the ideal of regular functions on `A` killed by the closed subscheme that the product of
the chart ideal sheaves of `D₁` and `D₂` at `A` cuts out. -/
theorem definingIdealAt_sumOfChart (D₁ D₂ : ClosedSubspaces B S hS X.1)
    (A : SmallEtale B S hS X.1)
    (m : A ⟶ (⟨CostructuredArrow.mk φ, he⟩ : SmallEtale B S hS X.1)) :
    definingIdealAt B S hS X (sumOfChart B S hS X hs he D₁ D₂) (op A) =
      RingHom.ker ((chartKer B S hS X D₁ A.1.hom *
        chartKer B S hS X D₂ A.1.hom).subschemeι.appTop).hom := by
  have hw : yoneda.map ((SmallEtale.toOver B S hS X.1).map m) ≫ φ = A.1.hom :=
    CostructuredArrow.w m.1
  rw [show sumOfChart B S hS X hs he D₁ D₂ =
      ⟨invariantSubspace B S hS φ
        (Subobject.mk (chartKer B S hS X D₁ φ * chartKer B S hS X D₂ φ).subschemeι),
        isClosedSubspace_invariantSubspace_subschemeι B S hS X hs he _
          (isInvariantSubscheme_mul_chartKer B S hS X hs D₁ D₂)⟩ from rfl,
    definingIdealAt_invariantSubspace_subschemeι B S hS X hs he _
      (isInvariantSubscheme_mul_chartKer B S hS X hs D₁ D₂) _ A m,
    Stacks.IdealSheaf.comap_mul, comap_chartKer B S hS X D₁ φ _ _ hw,
    comap_chartKer B S hS X D₂ φ _ _ hw]

include hs he in
/-- A closed subspace of `X` whose defining ideal over every affine étale chart lying over the
chart is the ideal cut out there by the product of the chart ideal sheaves of `D₁` and `D₂` is
the sum of `D₁` and `D₂`. -/
theorem eq_sumOfChart_of_definingIdealAt (D₁ D₂ Z : ClosedSubspaces B S hS X.1)
    (h : ∀ A : SmallEtale B S hS X.1,
      IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj A)) →
      ∀ _ : A ⟶ (⟨CostructuredArrow.mk φ, he⟩ : SmallEtale B S hS X.1),
      definingIdealAt B S hS X Z (op A) =
        RingHom.ker ((chartKer B S hS X D₁ A.1.hom *
          chartKer B S hS X D₂ A.1.hom).subschemeι.appTop).hom) :
    Z = sumOfChart B S hS X hs he D₁ D₂ :=
  definingIdealSheaf_injective B S hS X <| structureSubmodule_ext_of_forall_isAffine_hom B S hS X
    (⟨CostructuredArrow.mk φ, he⟩ : SmallEtale B S hS X.1)
    ((presheafSurjective_iff_isSurjective_yoneda B S hS X.1 X.2 U φ).1 hs) _ _
    fun A hA m => (h A hA m).trans (definingIdealAt_sumOfChart B S hS X hs he D₁ D₂ A m).symm

end Chart

/-! ### The sum of two closed subspaces -/

/-- The scheme chart of an algebraic space supplied by its defining hypothesis. -/
noncomputable def atlasObj : BigFppfOver B S hS := X.2.exists_atlas.choose

/-- The structure morphism of the chart `AlgebraicGeometry.Space.atlasObj`. -/
noncomputable def atlasHom : yoneda.obj (atlasObj B S hS X) ⟶ X.1 :=
  X.2.exists_atlas.choose_spec.choose

/-- The chart of an algebraic space is surjective after every representable base change. -/
theorem atlasHom_surjective :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (atlasHom B S hS X) :=
  X.2.exists_atlas.choose_spec.choose_spec.1

/-- The chart of an algebraic space is étale after every representable base change. -/
theorem atlasHom_etale :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (atlasHom B S hS X) :=
  X.2.exists_atlas.choose_spec.choose_spec.2

/-- The *sum* `D₁ + D₂` of two closed subspaces of an algebraic space `X`: the
closed subspace cut out by the product `𝓘_{D₁} 𝓘_{D₂}` of their defining ideals, formed on a
surjective étale scheme chart of `X` and descended. -/
@[stacks 083U "the sum of two effective Cartier divisors, for arbitrary closed subspaces"]
noncomputable def sumClosedSubspaces (D₁ D₂ : ClosedSubspaces B S hS X.1) :
    ClosedSubspaces B S hS X.1 :=
  sumOfChart B S hS X (atlasHom_surjective B S hS X) (atlasHom_etale B S hS X) D₁ D₂

/-- The sum is cut out by the product of the ideal sheaves of the summands: over an étale chart of
`X` lying over the chart on which it is formed, the defining ideal of `D₁ + D₂` is the ideal of
regular functions killed by the closed subscheme that the product of the chart ideal sheaves of
`D₁` and `D₂` cuts out there. -/
@[stacks 083U "the sum of two effective Cartier divisors, for arbitrary closed subspaces"]
theorem definingIdealAt_sumClosedSubspaces (D₁ D₂ : ClosedSubspaces B S hS X.1)
    (A : SmallEtale B S hS X.1)
    (m : A ⟶ (⟨CostructuredArrow.mk (atlasHom B S hS X), atlasHom_etale B S hS X⟩ :
      SmallEtale B S hS X.1)) :
    definingIdealAt B S hS X (sumClosedSubspaces B S hS X D₁ D₂) (op A) =
      RingHom.ker ((chartKer B S hS X D₁ A.1.hom *
        chartKer B S hS X D₂ A.1.hom).subschemeι.appTop).hom :=
  definingIdealAt_sumOfChart B S hS X (atlasHom_surjective B S hS X)
    (atlasHom_etale B S hS X) D₁ D₂ A m

/-- On an affine étale chart the defining ideal of the sum is the product of
the defining ideals of the summands. -/
@[stacks 083U "the sum of two effective Cartier divisors, for arbitrary closed subspaces"]
theorem definingIdealAt_sumClosedSubspaces_of_isAffine (D₁ D₂ : ClosedSubspaces B S hS X.1)
    (A : SmallEtale B S hS X.1)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj A.1.left)]
    (m : A ⟶ (⟨CostructuredArrow.mk (atlasHom B S hS X), atlasHom_etale B S hS X⟩ :
      SmallEtale B S hS X.1)) :
    definingIdealAt B S hS X (sumClosedSubspaces B S hS X D₁ D₂) (op A) =
      definingIdealAt B S hS X D₁ (op A) * definingIdealAt B S hS X D₂ (op A) := by
  have h : ∀ D : ClosedSubspaces B S hS X.1, chartKer B S hS X D A.1.hom =
      Scheme.IdealSheafData.ofIdealTop (definingIdealAt B S hS X D (op A)) :=
    fun D => ker_rep_snd_eq_ofIdealTop_definingIdealAt B S hS X D A
  have h₃ : chartKer B S hS X D₁ A.1.hom * chartKer B S hS X D₂ A.1.hom =
      Scheme.IdealSheafData.ofIdealTop (definingIdealAt B S hS X D₁ (op A) *
        definingIdealAt B S hS X D₂ (op A)) := by
    rw [h D₁, h D₂]
    exact Scheme.IdealSheafData.ofIdealTop_mul _ _
  rw [definingIdealAt_sumClosedSubspaces B S hS X D₁ D₂ A m, h₃]
  exact Scheme.IdealSheafData.ker_appTop_subschemeι_ofIdealTop _

/-! ### The multiplication of two defining ideal sheaves -/

section Multiplication

open Stacks.SheafOfModules.Invertible
open Stacks.SheafOfModules.TensorSheafification

/-- The multiplication `𝓘_{D₁} ⊗_{𝒪_X} 𝓘_{D₂} ⟶ 𝒪_X` of the defining ideal sheaves of two
closed subspaces: tensor the inclusion of `𝓘_{D₁}` with `𝓘_{D₂}`, undo the unit, and include
`𝓘_{D₂}`. -/
noncomputable def definingIdealTensorMul (D₁ D₂ : ClosedSubspaces B S hS X.1) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
          ((structureCommRings B S hS X)) (forget₂ CommRingCat RingCat)
          ((structureRingSheaf B S hS X).property)⟩
      ).obj ((idealSheafOfModules B S hS X D₁))).obj ((idealSheafOfModules B S hS X D₂))) ⟶
      SheafOfModules.unit (structureRingSheaf B S hS X) :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
        (structureCommRings B S hS X) (forget₂ CommRingCat RingCat)
        (structureRingSheaf B S hS X).property⟩
    ).map (definingIdealSheaf B S hS X D₁).ι).app (idealSheafOfModules B S hS X D₂)) ≫
    (tensorProductLeftUnitor (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property (idealSheafOfModules B S hS X D₂)).hom ≫
    (definingIdealSheaf B S hS X D₂).ι

/-- Tensoring the inclusion of `𝓘_{D₁}` with `𝓘_{D₂}` is the value on that inclusion of the
functor "tensor on the right by `𝓘_{D₂}`". -/
theorem tensorRightFunctor_map_ι (D₁ D₂ : ClosedSubspaces B S hS X.1) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
          (structureCommRings B S hS X) (forget₂ CommRingCat RingCat)
          (structureRingSheaf B S hS X).property⟩
      ).flip.obj
        (idealSheafOfModules B S hS X D₂)).map (definingIdealSheaf B S hS X D₁).ι =
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          ⟨(structureCommRings B S hS X), Presheaf.isSheaf_of_isSheaf_comp _
            (structureCommRings B S hS X) (forget₂ CommRingCat RingCat)
            (structureRingSheaf B S hS X).property⟩
        ).map (definingIdealSheaf B S hS X D₁).ι).app (idealSheafOfModules B S hS X D₂)) :=
  rfl

end Multiplication

end Space

end AlgebraicGeometry

end
