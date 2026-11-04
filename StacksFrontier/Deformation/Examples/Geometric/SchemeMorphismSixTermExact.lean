module

public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismConjugationArrowLinear
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismDerivationTangentLinearMap
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismObstructionKeyFinal
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismObstructionPull
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismObstructionPushClass
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismProductInvariants
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismSixTermExactObstruction
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismsRimSchlessingerUnconditional
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismEndpointsSupplied

/-!
# The exact sequence of Stacks 0E3V

Let `f : X → Y` be a morphism of schemes over a field `k`, in the setting of Example 0DY7.
[Stacks Project, Tag 0E3V] states that there is a canonical exact sequence of `k`-vector spaces

`0 → Inf(Def_{X → Y}) → Inf(Def_X × Def_Y) → Der_k(𝒪_Y, f_*𝒪_X) → T Def_{X → Y}`
`  → T(Def_X × Def_Y) → Ext¹_{𝒪_X}(Lf^*NL_{Y/k}, 𝒪_X)`.

This file names the five canonical `k`-linear arrows between the source's six terms, at data
depending on nothing but `f`, and proves that the sequence they form is exact.

## The terms

* `Inf(Def_{X → Y})`, `Inf(Def_X)`, `Inf(Def_Y)` are the tangent spaces at the identity of the
  automorphism functors of the base points (Tags 06JT, 06JV), at the fixed choices of
  pushforwards `Deformation.Examples.schemeMorphismTrivialPushforwards`,
  `Deformation.Examples.schemeMorphismSourcePushforwards` and
  `Deformation.Examples.schemeMorphismTargetPushforwards` — the last two being the endpoint
  images of the first — and `Inf(Def_X × Def_Y)` is read as `Inf(Def_X) × Inf(Def_Y)`.
* `Der_k(𝒪_Y, f_*𝒪_X)` is `Deformation.Examples.schemeMorphismDerivations f pY` with its
  `k`-structure `Deformation.Examples.schemeMorphismDerivationsModule`.
* `T Def_{X → Y}` and `T(Def_X × Def_Y) = T Def_X × T Def_Y` are the tangent modules at the
  rank-one coordinate module, i.e. over `k[ε]`.
* `Ext¹_{𝒪_X}(Lf^*NL_{Y/k}, 𝒪_X)` is `Deformation.Examples.schemeMorphismObstructionExt f pY`
  with its `k`-structure `Deformation.Examples.schemeMorphismObstructionExtModule`.

The products are the source's `Def_X × Def_Y`: for the 2-fibre product
`Deformation.Examples.schemeEndpointsProduct` over `𝒞_Λ`, the projections induce `k`-linear
equivalences `Deformation.Examples.schemeEndpointsProductInfEquiv` and
`Deformation.Examples.schemeEndpointsProductTangentEquiv`.

## The arrows

* `a = Deformation.Examples.schemeMorphismInfinitesimalPair'`, induced on infinitesimal
  automorphisms by the two endpoint-forgetting morphisms;
* `b = Deformation.Examples.schemeMorphismSixTermConjugationArrow`: a pair `(α, β)` goes to the
  derivation by which `β⁻¹ ∘ f' ∘ α` differs from the trivial lift `f' = f × id : X' → Y'`;
* `c = Deformation.Examples.schemeMorphismDerivationTangentLinearMap`: a derivation `D` goes to
  the class of the translate `D ⬝ f'`;
* `d = Deformation.Examples.schemeMorphismTangentPair'`, induced on tangent modules by the two
  endpoint-forgetting morphisms;
* `e = Deformation.Examples.schemeMorphismObstructionLinearMap`: a pair `(X', Y')` of
  first-order deformations goes to the obstruction `Push(Y') − Pull(X')` to deforming `f` along
  it (Tag 08U8).

## Main results

* `Deformation.Examples.schemeMorphismDeformation_sixTermExact`: Tag 0E3V — `a` is injective and
  the sequence `a, b, c, d, e` is exact at its four interior terms.
* `Deformation.Examples.schemeMorphismDeformation_exact_inf_der_tangent`: the part up to
  `T(Def_X × Def_Y)`.
* `Deformation.Examples.exact_schemeMorphismTangentPair'_schemeMorphismObstructionLinearMap`:
  exactness at `T(Def_X × Def_Y)`.

## References

* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (pX : X ⟶ baseSpec (residueFieldBase Λ k)) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))
  (hf : f ≫ pY = pX)

/-- **The arrow `b : Inf(Def_X × Def_Y) → Der_k(𝒪_Y, f_*𝒪_X)` of Tag 0E3V at the canonical
data**: `Deformation.Examples.schemeMorphismConjugationArrowLinear` at the fixed pushforwards and
the trivial lift. -/
abbrev schemeMorphismSixTermConjugationArrow :
    letI := naturalLocalizedTangentAddCommGroup (schemeMorphismTrivialPushforwards f pX pY
        hf)
      (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf).satisfiesRS
    letI := naturalLocalizedTangentModule (schemeMorphismTrivialPushforwards f pX pY
        hf)
      (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf).satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup (schemeMorphismSourcePushforwards f pX pY
        hf) (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)).satisfiesRS
    letI := naturalLocalizedTangentModule (schemeMorphismSourcePushforwards f pX pY
        hf) (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)).satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup (schemeMorphismTargetPushforwards f pX pY
        hf) (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)).satisfiesRS
    letI := naturalLocalizedTangentModule (schemeMorphismTargetPushforwards f pX pY
        hf) (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)).satisfiesRS
    letI := schemeMorphismDerivationsModule f pY
      (SheafOfModules.unit (structureSheafRing X.toRingedSpace))
    (localizedAutomorphismFunctorTangent (schemeMorphismSourcePushforwards f pX pY hf) ×
        localizedAutomorphismFunctorTangent (schemeMorphismTargetPushforwards f pX pY hf)) →ₗ[k]
      schemeMorphismDerivations f pY :=
  schemeMorphismConjugationArrowLinear f pX pY hf (schemeMorphismSourcePushforwards f pX pY
      hf) (schemeMorphismTargetPushforwards f pX pY hf)
          (schemeDeformationCategoryProjection_isPredeformationCategory (Λ := Λ) (k := k) (Over.mk
          pX)) (schemeDeformationCategoryProjection_isPredeformationCategory (Λ := Λ) (k := k)
          (Over.mk pY)) (firstOrderPushforwardCrossConormalIsoUnit (schemeMorphismSourcePushforwards
          f pX pY hf)) (firstOrderPushforwardCross_maximalIdeal_pow_two
          (schemeMorphismSourcePushforwards f pX pY hf)) (schemeMorphismTrivialLift f pX pY hf)
          (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)).satisfiesRS
          (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)).satisfiesRS

/-- **Stacks 0E3V, the sequence up to `T(Def_X × Def_Y)`.** The canonical arrow
`Inf(Def_{X → Y}) → Inf(Def_X × Def_Y)` is injective, and the sequence

`Inf(Def_{X → Y}) → Inf(Def_X × Def_Y) → Der_k(𝒪_Y, f_*𝒪_X) → T Def_{X → Y} → T(Def_X × Def_Y)`

of `k`-linear maps is exact at its three interior terms. -/
theorem schemeMorphismDeformation_exact_inf_der_tangent :
    letI := naturalLocalizedTangentAddCommGroup (schemeMorphismTrivialPushforwards f pX pY
        hf)
      (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf).satisfiesRS
    letI := naturalLocalizedTangentModule (schemeMorphismTrivialPushforwards f pX pY
        hf)
      (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf).satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup (schemeMorphismSourcePushforwards f pX pY
        hf) (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)).satisfiesRS
    letI := naturalLocalizedTangentModule (schemeMorphismSourcePushforwards f pX pY
        hf) (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)).satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup (schemeMorphismTargetPushforwards f pX pY
        hf) (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)).satisfiesRS
    letI := naturalLocalizedTangentModule (schemeMorphismTargetPushforwards f pX pY
        hf) (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)).satisfiesRS
    letI := schemeMorphismDerivationsModule f pY
      (SheafOfModules.unit (structureSheafRing X.toRingedSpace))
    Function.Injective (schemeMorphismInfinitesimalPair' f pX pY hf
        (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY
        hf).satisfiesRS (schemeMorphismTrivialPushforwards f pX pY hf)
            (schemeMorphismSourcePushforwards f pX pY hf) (schemeMorphismTargetPushforwards f pX pY
            hf)) ∧
      Function.Exact (schemeMorphismInfinitesimalPair' f pX pY hf
          (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY
          hf).satisfiesRS (schemeMorphismTrivialPushforwards f pX pY hf)
              (schemeMorphismSourcePushforwards f pX pY hf) (schemeMorphismTargetPushforwards f pX
              pY hf)) (schemeMorphismSixTermConjugationArrow f pX pY hf) ∧
      Function.Exact (schemeMorphismSixTermConjugationArrow f pX pY hf)
        (schemeMorphismDerivationTangentLinearMap f pX pY hf) ∧
      Function.Exact (schemeMorphismDerivationTangentLinearMap f pX pY hf)
        (schemeMorphismTangentPair' f pX pY hf
            (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY
            hf) (FGModuleCat.of k (ULift.{u} k))) := by
  obtain ⟨h3, h4⟩ := exact_schemeMorphismSixTerm_thirdFourthSpot_canonical f pX pY hf
  exact ⟨injective_schemeMorphismInfinitesimalPair' f pX pY hf _ _ _ _,
    exact_schemeMorphismInfinitesimalPair'_conjDerivationCross f pX pY hf, h3, h4⟩


/-- **The sixth arrow `e : T(Def_X × Def_Y) → Ext¹_{𝒪_X}(Lf^*NL_{Y/k}, 𝒪_X)` of Tag 0E3V**: a
pair `(X', Y')` of first-order deformations of `X` and `Y` over `k[ε]` goes to
`Push(Y') − Pull(X')`, the obstruction to deforming `f` to a morphism `X' → Y'` (Tag 08U8),
untwisted from `Ext¹_{𝒪_X}(Lf^*NL_{Y/k}, 𝒪_X ⊗_k k)`. -/
def schemeMorphismObstructionLinearMap :
    letI := schemeMorphismObstructionExtModule f pY
    ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
        (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)))
        (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))
        (FGModuleCat.of k (ULift.{u} k))) ×
      ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
        (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)))
        (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))
        (FGModuleCat.of k (ULift.{u} k))) →ₗ[k]
      schemeMorphismObstructionExt f pY :=
  schemeMorphismObstructionLinearMapOfClasses f pX pY (schemeMorphismObstructionPull f pX pY hf)
    (schemeMorphismObstructionPull_isIsomorphic f pX pY hf)
    (fun g x y a ha => schemeMorphismObstructionPull_naturality f pX pY hf g x y a ha)
    (schemeMorphismObstructionPush f pY) (schemeMorphismObstructionPush_isIsomorphic f pY)
    (fun g x y a ha => schemeMorphismObstructionPush_naturality f pY g x y a ha)

/-- **Stacks 0E3V, exactness at `T(Def_X × Def_Y)`**: the kernel of the sixth arrow `e` is the
image of `d : T Def_{X → Y} → T(Def_X × Def_Y)`. -/
theorem exact_schemeMorphismTangentPair'_schemeMorphismObstructionLinearMap :
    letI := schemeMorphismObstructionExtModule f pY
    Function.Exact (schemeMorphismTangentPair' f pX pY hf
        (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf)
        (FGModuleCat.of k (ULift.{u} k)))
      (schemeMorphismObstructionLinearMap f pX pY hf) :=
  exact_schemeMorphismTangentPair'_obstructionLinearMapOfClasses f pX pY hf
    (schemeMorphismObstructionPull f pX pY hf)
    (schemeMorphismObstructionPull_isIsomorphic f pX pY hf)
    (fun g x y a ha => schemeMorphismObstructionPull_naturality f pX pY hf g x y a ha)
    (schemeMorphismObstructionPush f pY) (schemeMorphismObstructionPush_isIsomorphic f pY)
    (fun g x y a ha => schemeMorphismObstructionPush_naturality f pY g x y a ha)
    (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf)
    (schemeMorphismObstruction_key f pX pY hf)

/-- Let `f : X → Y` be a morphism of schemes over `k` (Example 0DY7). There is a canonical exact
sequence of `k`-vector spaces

`0 → Inf(Def_{X → Y}) → Inf(Def_X × Def_Y) → Der_k(𝒪_Y, f_*𝒪_X) → T Def_{X → Y}`
`  → T(Def_X × Def_Y) → Ext¹_{𝒪_X}(Lf^*NL_{Y/k}, 𝒪_X)`.

The six terms are `localizedAutomorphismFunctorTangent` of the fixed pushforwards
`schemeMorphismTrivialPushforwards f pX pY hf` (`Inf(Def_{X → Y})`), the product of those of
`schemeMorphismSourcePushforwards f pX pY hf` and `schemeMorphismTargetPushforwards f pX pY hf`
(`Inf(Def_X × Def_Y)`), `schemeMorphismDerivations f pY` (`Der_k(𝒪_Y, f_*𝒪_X)`), the tangent
module of `Def_{X → Y}` over `k[ε]` (`T Def_{X → Y}`), the product of the tangent modules of
`Def_X` and `Def_Y` over `k[ε]` (`T(Def_X × Def_Y)`), and `schemeMorphismObstructionExt f pY`
(`Ext¹_{𝒪_X}(Lf^*NL_{Y/k}, 𝒪_X)`), each with its `k`-vector space structure. The products are
the source's `Def_X × Def_Y`: for the 2-fibre product `schemeEndpointsProduct pX pY` over `𝒞_Λ`
(a deformation category, `isDeformationCategory_schemeEndpointsProduct`), the projections induce
`k`-linear equivalences `schemeEndpointsProductInfEquiv` (`Inf(Def_X × Def_Y) ≃ Inf(Def_X) ×
Inf(Def_Y)`) and `schemeEndpointsProductTangentEquiv` (`T(Def_X × Def_Y) ≃ T Def_X × T Def_Y`),
and the arrows `a` and `d` below are the maps induced by `Def_{X → Y} → Def_X × Def_Y`
(`schemeMorphismEndpointsBased`) followed by these equivalences
(`schemeMorphismInfinitesimalPair'_canonical_eq`, `schemeMorphismTangentPair'_eq`).

The five arrows are `a = schemeMorphismInfinitesimalPair'` and `d = schemeMorphismTangentPair'`,
induced by the endpoint-forgetting morphisms; `b = schemeMorphismSixTermConjugationArrow`,
`(α, β) ↦` the derivation by which `β⁻¹ ∘ f' ∘ α` differs from the trivial lift
`f' = f × id`; `c = schemeMorphismDerivationTangentLinearMap`, `D ↦` the class of `D ⬝ f'`; and
`e = schemeMorphismObstructionLinearMap`, `(X', Y') ↦ Push(Y') − Pull(X')`, the obstruction of
Tag 08U8. The statement: `a` is injective (exactness at `Inf(Def_{X → Y})`) and the sequence is
exact at `Inf(Def_X × Def_Y)`, `Der_k(𝒪_Y, f_*𝒪_X)`, `T Def_{X → Y}` and `T(Def_X × Def_Y)`. -/
@[stacks 0E3V "the canonical exact sequence of k-vector spaces 0 -> Inf(Def_{X -> Y}) -> \
Inf(Def_X x Def_Y) -> Der_k(O_Y, f_*O_X) -> T Def_{X -> Y} -> T(Def_X x Def_Y) -> \
Ext^1_{O_X}(Lf^* NL_{Y/k}, O_X) for a morphism of schemes f : X -> Y over k: its five k-linear \
maps and exactness at all five spots"]
theorem schemeMorphismDeformation_sixTermExact :
    letI := naturalLocalizedTangentAddCommGroup (schemeMorphismTrivialPushforwards f pX pY hf)
      (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf).satisfiesRS
    letI := naturalLocalizedTangentModule (schemeMorphismTrivialPushforwards f pX pY hf)
      (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf).satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup (schemeMorphismSourcePushforwards f pX pY
        hf) (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)).satisfiesRS
    letI := naturalLocalizedTangentModule (schemeMorphismSourcePushforwards f pX pY
        hf) (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)).satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup (schemeMorphismTargetPushforwards f pX pY
        hf) (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)).satisfiesRS
    letI := naturalLocalizedTangentModule (schemeMorphismTargetPushforwards f pX pY
        hf) (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)).satisfiesRS
    letI := schemeMorphismDerivationsModule f pY
      (SheafOfModules.unit (structureSheafRing X.toRingedSpace))
    letI := schemeMorphismObstructionExtModule f pY
    Function.Injective (schemeMorphismInfinitesimalPair' f pX pY hf
        (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY
        hf).satisfiesRS (schemeMorphismTrivialPushforwards f pX pY hf)
            (schemeMorphismSourcePushforwards f pX pY hf) (schemeMorphismTargetPushforwards f pX pY
            hf)) ∧
      Function.Exact (schemeMorphismInfinitesimalPair' f pX pY hf
          (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY
          hf).satisfiesRS (schemeMorphismTrivialPushforwards f pX pY hf)
              (schemeMorphismSourcePushforwards f pX pY hf) (schemeMorphismTargetPushforwards f pX
              pY hf)) (schemeMorphismSixTermConjugationArrow f pX pY hf) ∧
      Function.Exact (schemeMorphismSixTermConjugationArrow f pX pY hf)
        (schemeMorphismDerivationTangentLinearMap f pX pY hf) ∧
      Function.Exact (schemeMorphismDerivationTangentLinearMap f pX pY hf)
        (schemeMorphismTangentPair' f pX pY hf
            (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY
            hf) (FGModuleCat.of k (ULift.{u} k))) ∧
      Function.Exact (schemeMorphismTangentPair' f pX pY hf
            (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY
            hf) (FGModuleCat.of k (ULift.{u} k)))
        (schemeMorphismObstructionLinearMap f pX pY hf) := by
  obtain ⟨h1, h2, h3, h4⟩ := schemeMorphismDeformation_exact_inf_der_tangent f pX pY hf
  exact ⟨h1, h2, h3, h4,
    exact_schemeMorphismTangentPair'_schemeMorphismObstructionLinearMap f pX pY hf⟩

end Deformation.Examples
