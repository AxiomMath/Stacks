module

public import StacksFrontier.CategoryTheory.Monoidal.MonObjImagePoint
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineProjectionFormulaStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.DualEvaluationEpiSmallEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeModuleTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeSurjectiveUnitMono
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyFiniteLocallyFreeDualTwist

/-!
# Stacks 0GUV, with the dual twist discharged

Let `f : X ⟶ Y` be a surjective finite locally free morphism of algebraic spaces over a scheme
`S`.  If `X` has the resolution property, so does `Y`.  This file closes the last step of the
source's proof, which
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyFiniteLocallyFree` isolates as
`AlgebraicGeometry.Space.DirectImageDualDescent` and
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyFiniteLocallyFreeDualTwist`
carries as the hypothesis `hdual`: the projection formula together with the twist by the dual of
`f_*𝒪_X`.  With that step proved here, 0GUV is unconditional and the tag moves onto the
unconditional statement below.

Write `ℬ = f_*𝒪_X` and `ℬ^∨ = 𝓗om_{𝒪_Y}(ℬ, 𝒪_Y)`.  Given a finite type quasi-coherent
`𝒪_Y`-module `𝒢`, a finite locally free `ℳ` and an epimorphism `φ : ℳ ⟶ f_*f^*𝒢`, the twisted map
is the composite

`ℬ^∨ ⊗ ℳ ⟶ ℬ^∨ ⊗ (ℬ ⊗ 𝒢) ≅ (ℬ^∨ ⊗ ℬ) ⊗ 𝒢 ⟶ 𝒪_Y ⊗ 𝒢 ≅ 𝒢`

of `ℬ^∨` whiskered with `φ` followed by the projection formula, the inverse associator, the trace
of `ℬ` whiskered with `𝒢`, and the left unitor.  Its source is finite locally free and it is an
epimorphism, because tensoring preserves epimorphisms in a monoidal closed category and the trace
is an epimorphism.

## Main results

* `AlgebraicGeometry.Space.epi_dualTwistComp`: the twisted composite is an epimorphism as soon as
  the trace is.
* `AlgebraicGeometry.Space.epi_dualEvaluationDesc_pushforwardStructureModule`: **the trace
  `(f_*𝒪_X)^∨ ⊗ f_*𝒪_X ⟶ 𝒪_Y` of a surjective finite locally free morphism is an
  epimorphism.**  This is where the surjectivity of `f` is spent.
* `AlgebraicGeometry.Space.directImageDualDescent`:
  `AlgebraicGeometry.Space.DirectImageDualDescent` holds for every morphism of algebraic spaces,
  so the hypothesis `hdual` of
  `AlgebraicGeometry.Space.hasResolutionProperty_of_isSurjective_isFiniteLocallyFree_of_dualTwist`
  can be discharged.
* `AlgebraicGeometry.Space.hasResolutionProperty_of_isSurjective_isFiniteLocallyFree_unconditional`
  is **Stacks 0GUV with no further input.**

## Implementation notes

**No coevaluation, and no left dual.**  The implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyFiniteLocallyFreeDualTwist`
record
the coevaluation `𝒪_Y ⟶ ℬ ⊗ ℬ^∨` of Stacks 0FNY — equivalently, the left-dual property of `ℬ^∨` —
as the obstruction to the dual twist, on the ground that without it the transposed map cannot be
formed.  That is not so: the composite displayed above *is* the transposed map, and writing it
down needs only the evaluation, the projection formula and the associativity and unit constraints
of the tensor product.  A duality would be used only to recognise the composite as a transpose,
which no step of the source's proof needs.  What the step does need is that the evaluation is an
epimorphism, which fails for a module of rank zero and is exactly where the surjectivity of `f`
enters; that is
`AlgebraicGeometry.Space.epi_dualEvaluationDesc_pushforwardStructureModule`, proved from
`AlgebraicGeometry.Space.epi_dualEvaluationDesc` and
`AlgebraicGeometry.Space.exists_mono_unit_pushforwardStructureModule`.

**No hypothesis is carried.**  `AlgebraicGeometry.Space.directImageDualDescent` is proved for an
arbitrary morphism `f` of algebraic spaces: the surjectivity and the finite local freeness it
consumes are the two premises of `AlgebraicGeometry.Space.DirectImageDualDescent` itself, which
are the two hypotheses of Stacks 0GUV.

**The two spellings of the tensor product.**  The projection formula
`AlgebraicGeometry.Space.modulePushforwardPullbackIsoSheafTensor` is stated for the tensor product
sheaf of Stacks 01CA and the twist is formed in
`AlgebraicGeometry.Space.modulesMonoidalCategory`; `AlgebraicGeometry.Space.modulesTensorObjIso`
is the comparison, and it is composed into the isomorphism `f_*f^*𝒢 ≅ ℬ ⊗ 𝒢` used below.

**The module universe** is the universe `u` of the schemes throughout, as it is for
`AlgebraicGeometry.Space.DirectImageDualDescent`; the reason is recorded there.

**Where `@[stacks 0GUV]` sits.**  On
`AlgebraicGeometry.Space.hasResolutionProperty_of_isSurjective_isFiniteLocallyFree_unconditional`
below, whose hypotheses are exactly the tag's — `f` surjective, `f` finite locally free, and `X`
having the resolution property.  The statement
`AlgebraicGeometry.Space.hasResolutionProperty_of_isSurjective_isFiniteLocallyFree_of_dualTwist`
is untagged, and isolates which step of the source's proof uses which input.

## References

* [Stacks Project, Tag 0GUV](https://stacks.math.columbia.edu/tag/0GUV)
* [Stacks Project, Tag 0FNY](https://stacks.math.columbia.edu/tag/0FNY)
* [Stacks Project, Tag 03ZV](https://stacks.math.columbia.edu/tag/03ZV)
* [Stacks Project, Tag 03ME](https://stacks.math.columbia.edu/tag/03ME)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory modulesBraidedCategory modulesMonoidalClosed

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- The forward map of an isomorphism is an epimorphism. -/
private theorem epi_hom_of_iso {C : Type*} [Category C] {A B : C} (e : A ≅ B) : Epi e.hom :=
  inferInstance

/-- **The dual twist of an epimorphism is an epimorphism**, granted that the trace is one.  For
`𝒪_F`-modules `𝒟`, `𝒞`, `ℳ`, `𝒢` on an algebraic space, a morphism `T : 𝒟 ⊗ 𝒞 ⟶ 𝒪_F` and an
epimorphism `ψ : ℳ ⟶ 𝒞 ⊗ 𝒢`, the composite

`𝒟 ⊗ ℳ ⟶ 𝒟 ⊗ (𝒞 ⊗ 𝒢) ≅ (𝒟 ⊗ 𝒞) ⊗ 𝒢 ⟶ 𝒪_F ⊗ 𝒢 ≅ 𝒢`

is an epimorphism as soon as `T` is.  Tensoring preserves epimorphisms on either side because the
`𝒪_F`-modules are monoidal closed and braided, `AlgebraicGeometry.Space.modulesMonoidalClosed`. -/
theorem epi_dualTwistComp (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    {D C M G : Modules.{u, u} B S hS F hF}
    (T : D ⊗ C ⟶ 𝟙_ (Modules.{u, u} B S hS F hF)) (hT : Epi T)
    (ψ : M ⟶ C ⊗ G) (hψ : Epi ψ) :
    Epi ((D ◁ ψ) ≫ (α_ D C G).inv ≫ (T ▷ G) ≫ (λ_ G).hom) := by
  have e1 : Epi (D ◁ ψ) := have := hψ; Mon.epi_whiskerLeft D ψ
  have e3 : Epi (T ▷ G) := have := hT; Mon.epi_whiskerRight G T
  exact @epi_comp _ _ _ _ _ _ e1 _ (@epi_comp _ _ _ _ _ _ (epi_hom_of_iso (α_ D C G).symm) _
    (@epi_comp _ _ _ _ _ _ e3 _ (epi_hom_of_iso (λ_ G))))

/-- **The trace `(f_*𝒪_X)^∨ ⊗ f_*𝒪_X ⟶ 𝒪_Y` of a surjective finite locally free morphism of
algebraic spaces is an epimorphism.**

This is the step of the proof of Stacks 0GUV that consumes the surjectivity of `f`: `f_*𝒪_X` is
finite locally free by Stacks 03ZV, and surjectivity enters as the monomorphism
`𝒪_Y ⟶ f_*𝒪_X` of `AlgebraicGeometry.Space.exists_mono_unit_pushforwardStructureModule`, which is
the form in which this development has the positive rank the source asks for. -/
theorem epi_dualEvaluationDesc_pushforwardStructureModule (f : X ⟶ Y)
    (hsurj : IsSurjective B S hS f.hom) (hflf : IsFiniteLocallyFree B S hS f) :
    Epi (dualEvaluationDesc B S hS Y.1 Y.2 (pushforwardStructureModule B S hS f)) := by
  obtain ⟨m, hm⟩ := exists_mono_unit_pushforwardStructureModule B S hS f hsurj hflf
  exact epi_dualEvaluationDesc B S hS Y.1 Y.2 _ hflf.2 m hm

/-- **The projection formula and the dual twist, the last two steps of the proof of
Stacks 0GUV**: `AlgebraicGeometry.Space.DirectImageDualDescent` holds for every morphism `f` of
algebraic spaces.

Given the two premises of that statement — `f` surjective and finite locally free — a finite type
quasi-coherent `𝒢` and an epimorphism `φ : ℳ ⟶ f_*f^*𝒢` with `ℳ` finite locally free, the module
`(f_*𝒪_X)^∨ ⊗ ℳ` is finite locally free
(`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_dual_pushforwardStructureModule` and
`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_tensorObj`) and the dual twist of `φ` along the
projection formula is an epimorphism onto `𝒢`
(`AlgebraicGeometry.Space.epi_dualTwistComp` and
`AlgebraicGeometry.Space.epi_dualEvaluationDesc_pushforwardStructureModule`).

This discharges the hypothesis `hdual` of
`AlgebraicGeometry.Space.hasResolutionProperty_of_isSurjective_isFiniteLocallyFree_of_dualTwist`.
-/
theorem directImageDualDescent (f : X ⟶ Y) : DirectImageDualDescent B S hS f := by
  intro hsurj hflf G hG _ M hM φ hφ
  have hD := isFiniteLocallyFreeOnSite_dual_pushforwardStructureModule B S hS f hflf
  refine ⟨_, isFiniteLocallyFreeOnSite_tensorObj B S hS Y.1 Y.2 _ M hD hM,
    (smallEtaleInternalHomSmall B S hS Y.1 Y.2 (pushforwardStructureModule B S hS f)
        (𝟙_ (Modules.{u, u} B S hS Y.1 Y.2)) ◁
      (φ ≫ (modulePushforwardPullbackIsoSheafTensor B S hS f hflf.1 G hG ≪≫
        (modulesTensorObjIso B S hS Y.1 Y.2
          (pushforwardStructureModule B S hS f) G).symm).hom)) ≫
      (α_ _ _ _).inv ≫
      (dualEvaluationDesc B S hS Y.1 Y.2 (pushforwardStructureModule B S hS f) ▷ G) ≫
      (λ_ G).hom, ?_⟩
  exact epi_dualTwistComp B S hS Y.1 Y.2 _
    (epi_dualEvaluationDesc_pushforwardStructureModule B S hS f hsurj hflf) _
    (@epi_comp _ _ _ _ _ _ hφ _ (epi_hom_of_iso _))

/-- **Stacks 0GUV, with no further input.**  For `f : X ⟶ Y` a surjective finite locally free
morphism of algebraic spaces over a scheme `S`, if `X` has the resolution property then so does
`Y`.

This is
`AlgebraicGeometry.Space.hasResolutionProperty_of_isSurjective_isFiniteLocallyFree_of_dualTwist`
with its hypothesis `hdual` discharged by `AlgebraicGeometry.Space.directImageDualDescent`, which
is proved outright for every morphism of algebraic spaces.  Its hypotheses are therefore exactly
the tag's: `f` surjective, `f` finite locally free, and `X` having the resolution property. -/
@[stacks 0GUV]
theorem hasResolutionProperty_of_isSurjective_isFiniteLocallyFree_unconditional (f : X ⟶ Y)
    (hsurj : IsSurjective B S hS f.hom) (hflf : IsFiniteLocallyFree B S hS f)
    (hX : HasResolutionProperty.{u, u} B S hS X.1 X.2) :
    HasResolutionProperty.{u, u} B S hS Y.1 Y.2 :=
  hasResolutionProperty_of_isSurjective_isFiniteLocallyFree_of_dualTwist B S hS f hsurj hflf
    (directImageDualDescent B S hS f) hX

end AlgebraicGeometry.Space

end
