module

public import StacksFrontier.Deformation.Examples.Geometric.SchemesDeformationCategory
public import StacksFrontier.Deformation.Examples.Geometric.SchemesInfinitesimalAutomorphismsDerivations
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The infinitesimal automorphisms of a scheme, at the trivial deformation

Let `k` be a field and `X` a scheme over `k`. The first display of [Stacks Project, Tag 0DY9] is

`Inf(𝓓_X) = Ext⁰_{𝒪_X}(NL_{X/k}, 𝒪_X) = Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X) = Der_k(𝒪_X, 𝒪_X)`,

where, as the source's proof recalls, `Inf(𝓓_X)` is the group of automorphisms of the trivial
deformation `X' = X ×_{Spec k} Spec k[ε]` of `X` that are the identity modulo `ε`. This file
states and proves it at exactly that group
(`Deformation.Examples.infinitesimalAutomorphismGroupTrivialDeformationChain`).

The library's `Inf(𝓕)` of a predeformation category, `Deformation.infinitesimalAutomorphismGroup`
([Stacks Project, Tag 06JS]), is formed from a point `x₀` over `k`, a pushforward `x₀ → x'₀` of it
along `k → k[ε]`, and the pair `k → k[ε] → k`. Here all of these are the canonical ones:

* the pair is the constant inclusion `Deformation.dualNumbersInclusion` of the residue-field object
  into the dual-number object `Deformation.artinianDualNumbers` of `𝒞_Λ`, followed by the residue
  map `Deformation.residueMorphism`; it is a dual-number pair in the sense of
  `Deformation.IsCanonicalDualNumberPair` by
  `Deformation.isCanonicalDualNumberPair_dualNumbersInclusion`;
* `x₀` is `X` itself, `Deformation.Examples.residueTrivialFiberObj`;
* `x'₀` is the trivial deformation `X ×_{Spec k} Spec k[ε]`, the base change of `x₀` along the
  constant inclusion (`Deformation.Examples.dualNumbersTrivialDeformation`), and `x₀ → x'₀` is the
  projection of the fibre product (`Deformation.Examples.dualNumbersTrivialDeformationHom`);
* the predeformation-category structure is the one of [Stacks Project, Tag 0DY8],
  `Deformation.Examples.isDeformationCategory_schemeDeformationCategoryProjection`.

Any other choice of these data gives a uniquely isomorphic group, by
`Deformation.infinitesimalAutomorphismGroup_uniqueEquiv` ([Stacks Project, Tag 06JS]).

## Main definitions

* `Deformation.isCanonicalDualNumberPair_dualNumbersInclusion`: `k → k[ε] → k` is a dual-number
  pair.
* `Deformation.Examples.dualNumbersTrivialDeformation`: the trivial deformation
  `X ×_{Spec k} Spec k[ε]`.
* `Deformation.Examples.infinitesimalAutomorphismGroupTrivialDeformationChain`: **the first
  display of [Stacks Project, Tag 0DY9]**.

## References

* [Stacks Project, Tag 0DY9](https://stacks.math.columbia.edu/tag/0DY9)
* [Stacks Project, Tag 0DY8](https://stacks.math.columbia.edu/tag/0DY8)
* [Stacks Project, Tag 06JS](https://stacks.math.columbia.edu/tag/06JS)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Deformation

universe u v w

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- **The constant inclusion `k → k[ε]` and the projection `k[ε] → k` form a dual-number pair**,
in the coordinates `Deformation.residueFieldCoordinates` on the residue-field object and
`Deformation.dualNumbersEquiv` on the dual-number object of `𝒞_Λ`. -/
theorem isCanonicalDualNumberPair_dualNumbersInclusion :
    IsCanonicalDualNumberPair (dualNumbersInclusion.{u, v, w} (Λ := Λ) (k := k))
      (residueMorphism.{u, v, w} (artinianDualNumbers.{u, w, v} Λ k)) := by
  refine ⟨residueFieldCoordinates.{u, v, w}, dualNumbersEquiv.{u, v, w}, ?_, ?_, ?_⟩
  · ext c
    · exact dualNumbersEquiv_fst.{u, v, w} _
    · show TrivSqZeroExt.snd (dualNumbersEquiv.{u, v, w} (Λ := Λ)
        (dualNumbersUp.{u, v, w} (Λ := Λ) (TrivSqZeroExt.inl (ULift.down c)))) = 0
      rw [show dualNumbersEquiv.{u, v, w} (Λ := Λ)
          (dualNumbersUp.{u, v, w} (Λ := Λ) (TrivSqZeroExt.inl (ULift.down c))) =
            TrivSqZeroExt.inl (ULift.down c) from
        (AlgEquiv.ofBijective _ dualNumbersUp_bijective.{u, v, w}).symm_apply_apply _]
      rfl
  · ext z
    show aug.{u, v, w} _ z = TrivSqZeroExt.fst (dualNumbersEquiv.{u, v, w} z)
    rw [aug_dualNumbers, dualNumbersEquiv_fst]
  · exact (eq_residueMorphism _).trans (eq_residueMorphism _).symm

end Deformation

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-- **The trivial deformation `X' = X ×_{Spec k} Spec k[ε]` of `X` to the dual numbers**: the
base change of `X`, read as a deformation over the residue-field object, along the constant
inclusion of `k` into the dual-number object of `𝒞_Λ`. Its total space is the fibre product of
`X → Spec k` and `Spec k[ε] → Spec k`. -/
@[sga "3 VIIA 1.2.0" "special case", sga "7 VI 2.6(c)" "special case"]
def dualNumbersTrivialDeformation (X : Over (Spec (CommRingCat.of k))) :
    SchemeDeformationCategory (Λ := Λ) (k := k) X :=
  baseChangeDeformation (residueTrivialDeformation X) dualNumbersInclusion.{u, u, u}

/-- The trivial deformation as a point of the fibre over the dual-number object. -/
abbrev dualNumbersTrivialFiberObj (X : Over (Spec (CommRingCat.of k))) :
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber
      (artinianDualNumbers.{u, u, u} Λ k) :=
  ⟨dualNumbersTrivialDeformation X, rfl⟩

/-- **The pushforward `x₀ → x'₀` of `X` along `k → k[ε]`**: the arrow of `X` onto its base change
to the dual numbers, whose component on total spaces is the projection
`X ×_{Spec k} Spec k[ε] → X`. -/
def dualNumbersTrivialDeformationHom (X : Over (Spec (CommRingCat.of k))) :
    (residueTrivialFiberObj (Λ := Λ) X).1 ⟶ (dualNumbersTrivialFiberObj X).1 :=
  baseChangeDeformationHom (residueTrivialDeformation X) dualNumbersInclusion.{u, u, u}

/-- The pushforward `x₀ → x'₀` lies over the constant inclusion `k → k[ε]`. -/
theorem dualNumbersTrivialDeformationHom_isHomLift (X : Over (Spec (CommRingCat.of k))) :
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).IsHomLift
      dualNumbersInclusion.{u, u, u} (dualNumbersTrivialDeformationHom X) :=
  Functor.IsHomLift.map (dualNumbersTrivialDeformationHom X)

/-- **The first display of [Stacks Project, Tag 0DY9].** For a scheme `X` over the field `k`,

`Inf(𝓓_X) = Ext⁰_{𝒪_X}(NL_{X/k}, 𝒪_X) = Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X) = Der_k(𝒪_X, 𝒪_X)`,

given as the three identifications of those four groups.

`Inf(𝓓_X)` is the library's infinitesimal automorphism group
`Deformation.infinitesimalAutomorphismGroup` of the deformation category of `X`, which is a
predeformation category by [Stacks Project, Tag 0DY8], formed at its canonical data: the point
`X` over `k`, its pushforward the trivial deformation `X ×_{Spec k} Spec k[ε]`, and the pair
`k → k[ε] → k`. That is, the automorphisms of the trivial deformation that are the identity
modulo `ε`.

* The first identification is an isomorphism of **groups**: composition of such automorphisms
  corresponds to addition of derivations
  (`Deformation.Examples.infinitesimalAutomorphismGroupMulEquivDerivations`, at the coordinate
  `Deformation.Examples.artinianDualNumbersCoordinate` of the dual-number object).
* The second is `AlgebraicGeometry.Scheme.naiveCotangentExtZeroAddEquiv`: `Ext⁰` out of the naive
  cotangent complex `NL_{X/k}` of the structure morphism of `X` is the `Hom` out of its degree `0`
  cohomology sheaf, which is `Ω_{X/k}` by [Stacks Project, Tag 0D0J].
* The third is `k`-linear: `Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X)` carries the `k`-structure of sheaves of
  modules on a scheme over `k` (`AlgebraicGeometry.modulesLinear`), and the derivations of `𝒪_X`
  over `k` with values in `𝒪_X` the one of
  `Deformation.Examples.schemeMorphismDerivationsModule`; it is corepresentability of relative
  derivations (`Deformation.Examples.schemeMorphismDerivationsLinearEquiv`) read through the
  comparison `AlgebraicGeometry.Scheme.Hom.cotangentSheafIso` of the two constructions of the
  sheaf of relative differentials.

`Der_k(𝒪_X, 𝒪_X)` is written `schemeMorphismDerivations (𝟙 X.left) X.hom`, the derivations of
`𝒪_X` over `k` with values in the pushforward of `𝒪_X` along the identity of `X`, which is `𝒪_X`
itself (`Deformation.Examples.schemeMorphismPushforwardStructureSheaf_id`, by `rfl`). -/
@[stacks 0DY9 "first display: for a scheme X over the field k, Inf(Def_X) = Ext^0(NL_{X/k}, \
O_X) = Hom(Omega_{X/k}, O_X) = Der_k(O_X, O_X), as three identifications: Inf(Def_X) is the \
library's infinitesimal automorphism group of the deformation category of X at the trivial \
deformation X x_k Spec k[eps], and is isomorphic as a group to Der_k(O_X, O_X); Ext^0 out of the \
naive cotangent complex is additively Hom(Omega_{X/k}, O_X); and Hom(Omega_{X/k}, O_X) is \
k-linearly Der_k(O_X, O_X). The second display, T Def_X = Ext^1(NL_{X/k}, O_X), is registered \
separately",
  sga "1 III 6.1" "special case",
  sga "3 VIIA 2.5" "first component",
  sga "3 VIIA 6.4.3" "special case",
  sga "7 VI 4.16" "special case"]
def infinitesimalAutomorphismGroupTrivialDeformationChain (X : Over (Spec (CommRingCat.of k))) :
    (infinitesimalAutomorphismGroup
        (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) X).predeformation
        (x₀ := residueTrivialFiberObj X) (xε := dualNumbersTrivialFiberObj X)
        dualNumbersInclusion.{u, u, u}
        (residueMorphism.{u, u, u} (artinianDualNumbers.{u, u, u} Λ k))
        isCanonicalDualNumberPair_dualNumbersInclusion.{u, u, u}
        (dualNumbersTrivialDeformationHom X) (dualNumbersTrivialDeformationHom_isHomLift X)
        ≃* Multiplicative (schemeMorphismDerivations (Λ := Λ) (k := k) (𝟙 X.left) X.hom))
      × (Scheme.naiveCotangentExt X.hom (structureSheafModules X.left) 0
          ≃+ (Scheme.Hom.relativeDifferentials X.hom ⟶ structureSheafModules X.left))
      × (letI : Module k (Scheme.Hom.relativeDifferentials X.hom ⟶ structureSheafModules X.left) :=
            (modulesLinear k (Over.mk X.hom)).homModule _ _;
          letI := schemeMorphismDerivationsModule (Λ := Λ) (k := k) (𝟙 X.left) X.hom
            (structureSheafModules X.left);
          ((Scheme.Hom.relativeDifferentials X.hom ⟶ structureSheafModules X.left) ≃ₗ[k]
            schemeMorphismDerivations (Λ := Λ) (k := k) (𝟙 X.left) X.hom)) :=
  letI : Linear k X.left.Modules := modulesLinear k (Over.mk X.hom)
  letI := schemeMorphismDerivationsModule (Λ := Λ) (k := k) (𝟙 X.left) X.hom
    (structureSheafModules X.left)
  ⟨infinitesimalAutomorphismGroupMulEquivDerivations
      (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) X).predeformation
      (x₀ := residueTrivialFiberObj X) (xε := dualNumbersTrivialFiberObj X)
      dualNumbersInclusion.{u, u, u}
      (residueMorphism.{u, u, u} (artinianDualNumbers.{u, u, u} Λ k))
      isCanonicalDualNumberPair_dualNumbersInclusion.{u, u, u}
      artinianDualNumbersCoordinate
      (dualNumbersTrivialDeformationHom X) (dualNumbersTrivialDeformationHom_isHomLift X),
    Scheme.naiveCotangentExtZeroAddEquiv X.hom _,
    (Linear.homCongr k (Scheme.Hom.cotangentSheafIso X.hom) (Iso.refl _)).trans
      (schemeMorphismDerivationsLinearEquiv (Λ := Λ) (k := k) (𝟙 X.left) X.hom
        (structureSheafModules X.left)).symm⟩

end Deformation.Examples

end
