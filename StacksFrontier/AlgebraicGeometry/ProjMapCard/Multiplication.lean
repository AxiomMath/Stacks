module

public import StacksFrontier.AlgebraicGeometry.ProjMapCard.RestrictionComparison
public import StacksFrontier.AlgebraicGeometry.ProjTwistTheta.Multiplication

/-!
# Tag 01MY: the comparison maps on twists are compatible with the multiplication maps

Let `ψ : 𝒜 →+*ᵍ ℬ` be a homomorphism of nonnegatively graded rings, `U(ψ) ⊆ Proj ℬ` its domain
of definition, `r_ψ : U(ψ) ⟶ Proj 𝒜` the induced morphism and `θ n` the comparison map on the
`n`-th twist. The twists of `Proj 𝒜` carry multiplication maps
`𝒪(n) ⊗ 𝒪(m) → 𝒪(n + m)` (Tag 01MU) making `⨁_n 𝒪(n)` a graded algebra, and Tag 01MY asserts
that the family `θ` is a map of graded algebras. This file proves the multiplicativity clause:

`r_ψ^*𝒪(n) ⊗ r_ψ^*𝒪(m) ⟶ r_ψ^*𝒪(n + m) ⟶ ι^*𝒪(n + m)` equals
`r_ψ^*𝒪(n) ⊗ r_ψ^*𝒪(m) ⟶ ι^*𝒪(n) ⊗ ι^*𝒪(m) ⟶ ι^*𝒪(n + m)`,

where both pulled-back multiplications are formed with the Tag 01CD comparison between the
pullback of a tensor product and the tensor product of the pullbacks.

## Main results

* `Stacks.AlgebraicGeometry.ProjMapCard.twistPushforwardMap_twistMultiplicationMap`: the
  mathematical content, as an equality of *sections*. The adjoint form of `θ (n + m)`, applied
  to the product of two honest sections, is the product of the images of those sections.
* `Stacks.AlgebraicGeometry.ProjMapCard.twistMap_comp_pullbackTwistMultiplication`: **Tag 01MY,
  graded-algebra multiplication.** The clause itself.
* `Stacks.AlgebraicGeometry.ProjMapCard.projMapData_preserves_products`: the same statement
  written on the canonical bundle
  `Stacks.AlgebraicGeometry.ProjTwistCompare.projMapData`, which is the spelling of the tagged
  statement.

## The route

The source of both sides is a tensor product of two pullbacks, and nothing can be said about
its sections directly. Composing with the Tag 01CD comparison, which is invertible, replaces
that source by the pullback `r_ψ^*(𝒪(n) ⊗ 𝒪(m))`, and
`Stacks.AlgebraicGeometry.ProjTwistTheta.comparison_comp_pullbackTwistMultiplication` collapses
the left-hand side to `r_ψ^*` of the multiplication map followed by `θ (n + m)`. A morphism out
of a pullback of a tensor product is determined by its adjoint transpose on the
sheafification-unit images of pure tensors (`pullbackTensor_hom_ext`), so the clause reduces to
an identity between sections over an open of `Proj 𝒜`, and there every term is concrete:

* `θ` on a pullback-unit image is the adjoint form of `θ` followed by the identification of
  restriction with pullback (`Stacks.AlgebraicGeometry.ProjTwistTheta.unit_comp_map_twistMap`);
* the Tag 01CD comparison on a pullback-unit image of a pure tensor is the pure tensor of the
  pullback-unit images (`Stacks.RingedSpace.comparison_homEquiv_unit_tmul`);
* its *inverse* on a pure tensor of sections read through the restriction functor is the
  companion file's `restrictFunctorIsoPullback_tensorSheafUnit_eq`, which is the step no
  earlier round could take;
* and what is left is multiplicativity on sections, which is
  `Stacks.AlgebraicGeometry.ProjTwistTheta.twistPushforwardMap_mul_val` — the fibre comparison
  is a ring homomorphism.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a `def`, so every transport of an equality of morphisms
onto an element is `congrArg` of a function that evaluates a morphism, and the computation is a
chain of `Eq.trans`; a rewrite fails its motive check even where both sides print identically.
The one `rw` in the file is the cancellation of the comparison isomorphism, which happens before
any element is in sight.

Each of the identities above is used in the spelling
`CategoryTheory.PresheafOfModules.Hom.app _ (.op U)`; the twist files use
`(_.val.app (.op U)).hom'` and `Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection`,
  and all three agree by
`rfl`.

## What is not done

The unit law in the spelling of the tagged statement and uniqueness of the family of comparison maps are not
proved here; neither is the statement that `θ` is an isomorphism.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry HomogeneousLocalization TopologicalSpace CategoryTheory Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.RingedSpace PresheafOfModules RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare Stacks.AlgebraicGeometry.ProjTwistTheta
open Stacks.AlgebraicGeometry.TwistTensor Stacks.AlgebraicGeometry.ProjInvertibleLocus
open scoped TensorProduct

namespace Stacks.AlgebraicGeometry.ProjMapCard

universe u w w'

/-! ### Morphisms out of the pullback of a tensor product -/

section Generic

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  (P Q : SheafOfModules.{u} (structureRingSheaf Y))

/-- The adjoint transpose of a morphism out of a pullback, evaluated on a section, is the
morphism evaluated on the pullback-unit image of that section. -/
public theorem homEquiv_app_pullbackUnit {R : SheafOfModules.{u} (structureRingSheaf X)}
    (α : (pullbackFunctor f).obj P ⟶ R) (U : (Opens Y.carrier)ᵒᵖ) (t : P.val.obj U) :
    Hom.app ((pullbackAdjunction f).homEquiv P R α).val U t =
      Hom.app α.val ((opensMap f).op.obj U) (pullbackUnit f P U t) := by
  rw [Adjunction.homEquiv_unit]
  rfl

/-- **Two morphisms out of `f^*(P ⊗ Q)` are equal as soon as their adjoint transposes agree on
the sheafification-unit images of pure tensors of sections.** This is the extensionality
principle the multiplicativity clause is proved with: the source of the clause has no usable
sections, and this is what replaces them. -/
public theorem pullbackTensor_hom_ext {R : SheafOfModules.{u} (structureRingSheaf X)}
    (α β : (pullbackFunctor f).obj (((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨((Y)).presheaf, ((Y)).IsSheaf⟩))).obj (P, Q)) ⟶ R)
    (h : ∀ (U : Opens Y.carrier) (x : P.val.obj (op U)) (y : Q.val.obj (op U)),
      Hom.app α.val (op ((opensMap f).obj U))
          (pullbackUnit f (((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨((Y)).presheaf, ((Y)).IsSheaf⟩))).obj (P, Q)) (op U)
            (Hom.app ((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.RingedSpace.structureRingSheaf (Y))
              (𝟙 (Stacks.RingedSpace.structureRingSheaf (Y)).obj)).unit.app
              (PresheafOfModules.tensorObj (O := (Y).presheaf) (P).val (Q).val)) (op U) (x ⊗ₜ y))) =
        Hom.app β.val (op ((opensMap f).obj U))
          (pullbackUnit f (((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨((Y)).presheaf, ((Y)).IsSheaf⟩))).obj (P, Q)) (op U)
            (Hom.app ((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.RingedSpace.structureRingSheaf (Y))
              (𝟙 (Stacks.RingedSpace.structureRingSheaf (Y)).obj)).unit.app
              (PresheafOfModules.tensorObj (O := (Y).presheaf) (P).val (Q).val)) (op U)
              (x ⊗ₜ y)))) :
    α = β := by
  refine ((pullbackAdjunction f).homEquiv _ _).injective ?_
  refine PresheafOfModules.sheafification_hom_ext
    (PresheafOfModules.tensorObj_hom_ext fun U x y ↦ ?_)
  exact (homEquiv_app_pullbackUnit f _ α U _).trans
    ((h U.unop x y).trans (homEquiv_app_pullbackUnit f _ β U _).symm)

/-- The Tag 01CD comparison on the pullback-unit image of the sheafification-unit image of a
pure tensor: the pure tensor of the two pullback-unit images. -/
public theorem comparison_pullbackUnit_tensorSheafUnit (U : Opens Y.carrier)
    (x : P.val.obj (op U)) (y : Q.val.obj (op U)) :
    Hom.app ((Stacks.PullbackTensorIso.pullbackTensorIso f).hom.app (P, Q)).val
        (op ((opensMap f).obj U))
        (pullbackUnit f (((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨((Y)).presheaf, ((Y)).IsSheaf⟩))).obj (P, Q)) (op U)
          (Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.RingedSpace.structureRingSheaf (Y))
            (𝟙 (Stacks.RingedSpace.structureRingSheaf (Y)).obj)).unit.app
            (PresheafOfModules.tensorObj (O := (Y).presheaf) (P).val (Q).val)) (op U) (x ⊗ₜ y))) =
      Hom.app ((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.RingedSpace.structureRingSheaf (X))
        (𝟙 (Stacks.RingedSpace.structureRingSheaf (X)).obj)).unit.app
        (PresheafOfModules.tensorObj (O := (X).presheaf) (((pullbackFunctor f).obj P)).val
        (((pullbackFunctor f).obj Q)).val))
        (op ((opensMap f).obj U))
        (pullbackUnit f P (op U) x ⊗ₜ pullbackUnit f Q (op U) y) :=
  (Stacks.PullbackTensorIso.comparison_val_app_pullbackUnit f P Q U _).trans
    (comparison_homEquiv_unit_tmul f P Q (op U) x y)

end Generic

/-- The restriction functor on a morphism, read on a section: it is the morphism on sections
over the image open. Stated at the morphism level and transported, because the direct
element-level `rfl` exhausts the kernel budget. -/
public theorem restrictFunctor_map_app_apply {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsOpenImmersion g] {M N : Y.Modules} (φ : M ⟶ N) (V : X.Opens)
    (z : ((Scheme.Modules.restrictFunctor g).obj M).val.obj (op V)) :
    Hom.app ((Scheme.Modules.restrictFunctor g).map φ).val (op V) z =
      Hom.app φ.val (op (g ''ᵁ V)) z :=
  congrArg (fun k => (ConcreteCategory.hom k) z)
    (show ((Scheme.Modules.restrictFunctor g).map φ).app V = φ.app (g ''ᵁ V) from rfl)

/-- Naturality of the identification of restriction with pullback, read on a section: the image
under `restrictFunctorIsoPullback` of the value of a morphism is the value of the pullback of
that morphism on the image. -/
public theorem restrictFunctorIsoPullback_hom_app_naturality {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsOpenImmersion g] {M N : Y.Modules} (φ : M ⟶ N) (V : X.Opens)
    (z : ((Scheme.Modules.restrictFunctor g).obj M).val.obj (op V)) :
    Hom.app ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app N).val (op V)
        (Hom.app φ.val (op (g ''ᵁ V)) z) =
      Hom.app ((Scheme.Modules.pullback g).map φ).val (op V)
        (Hom.app ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app M).val (op V) z) := by
  refine Eq.trans (congrArg (Hom.app
    ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app N).val (op V))
    (restrictFunctor_map_app_apply g φ V z).symm) ?_
  exact congrArg (fun ρ => Hom.app (SheafOfModules.Hom.val ρ) (op V) z)
    ((Scheme.Modules.restrictFunctorIsoPullback g).hom.naturality φ)

/-! ### Tag 01MY, the multiplication clause -/

section Proj

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
  TopCat.Presheaf.IsSheaf
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top

/-- The comparison map on the `n`-th twist, evaluated on a pullback-unit image: it is the
adjoint form of the comparison followed by the identification of restriction with pullback.

This is `Stacks.AlgebraicGeometry.ProjTwistTheta.unit_comp_map_twistMap` read on a section. -/
public theorem twistMap_pullbackUnit (ψ : 𝒜 →+*ᵍ ℬ) (n : ℤ)
    (U : (AlgebraicGeometry.Proj 𝒜).Opens) (w : (twistingSheaf 𝒜 n).val.obj (op U)) :
    Hom.app (twistMap 𝒜 ℬ ψ n).val (op (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U))
        (pullbackUnit (mapHom 𝒜 ℬ ψ).toLRSHom.toShHom (twistingSheaf 𝒜 n) (op U) w) =
      Hom.app ((Scheme.Modules.restrictFunctorIsoPullback (mapDomain 𝒜 ℬ ψ).ι).hom.app
          (twistingSheaf ℬ n)).val (op (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U))
        (Hom.app (twistPushforwardMap 𝒜 ℬ ψ n).val (op U) w) :=
  congrArg (fun φ => Hom.app (SheafOfModules.Hom.val φ) (op U) w)
    (unit_comp_map_twistMap 𝒜 ℬ ψ n)

/-- **Multiplicativity of the comparison on sections, as an equality of sections.** The adjoint
form of the comparison on the `(n + m)`-th twist carries the product of two honest sections of
`𝒪(n)` and `𝒪(m)` over an open `U` to the product of their images over the image of
`r_ψ ⁻¹ᵁ U`.

This is the mathematical content of the clause:
`Stacks.AlgebraicGeometry.ProjTwistTheta.twistPushforwardMap_mul_val` computes both sides
pointwise, and the two values agree because the fibre comparison is a ring homomorphism. -/
public theorem twistPushforwardMap_twistMultiplicationMap (ψ : 𝒜 →+*ᵍ ℬ) (n m : ℤ)
    (U : (AlgebraicGeometry.Proj 𝒜).Opens)
    (s : (twistingSheaf 𝒜 n).val.obj (op U)) (t : (twistingSheaf 𝒜 m).val.obj (op U)) :
    Hom.app (twistPushforwardMap 𝒜 ℬ ψ (n + m)).val (op U)
        (Hom.app (twistMultiplicationMap 𝒜 n m).val (op U)
          (Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.RingedSpace.structureRingSheaf ((AlgebraicGeometry.Proj 𝒜).toRingedSpace))
            (𝟙 (Stacks.RingedSpace.structureRingSheaf
            ((AlgebraicGeometry.Proj 𝒜).toRingedSpace)).obj)).unit.app
            (PresheafOfModules.tensorObj (O := ((AlgebraicGeometry.Proj 𝒜).toRingedSpace).presheaf)
            ((twistingSheaf 𝒜 n)).val ((twistingSheaf 𝒜 m)).val)) (op U) (s ⊗ₜ t))) =
      Hom.app (twistMultiplicationMap ℬ n m).val
          (op ((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U)))
        (Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.RingedSpace.structureRingSheaf ((AlgebraicGeometry.Proj ℬ).toRingedSpace))
          (𝟙 (Stacks.RingedSpace.structureRingSheaf
          ((AlgebraicGeometry.Proj ℬ).toRingedSpace)).obj)).unit.app
          (PresheafOfModules.tensorObj (O := ((AlgebraicGeometry.Proj ℬ).toRingedSpace).presheaf)
          ((twistingSheaf ℬ n)).val ((twistingSheaf ℬ m)).val))
          (op ((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U)))
          (Hom.app (twistPushforwardMap 𝒜 ℬ ψ n).val (op U) s ⊗ₜ
            Hom.app (twistPushforwardMap 𝒜 ℬ ψ m).val (op U) t)) :=
  Subtype.ext (funext fun z =>
    (twistPushforwardMap_mul_val 𝒜 ℬ ψ n m U s t z).trans
      (twistMultiplicationMap_tmul ℬ n m ((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U))
        (((twistPushforwardMap 𝒜 ℬ ψ n).val.app (op U)).hom' s)
        (((twistPushforwardMap 𝒜 ℬ ψ m).val.app (op U)).hom' t) z).symm)

/-- **Tag 01MY, graded-algebra multiplication.** The comparison maps `θ` on the twists are
compatible with the multiplication maps `𝒪(n) ⊗ 𝒪(m) → 𝒪(n + m)` of the twisting algebras, both
pulled back with the Tag 01CD comparison. -/
public theorem twistMap_comp_pullbackTwistMultiplication (ψ : 𝒜 →+*ᵍ ℬ) (n m : ℤ) :
    pullbackTwistMultiplication 𝒜 (mapHom 𝒜 ℬ ψ) n m ≫ twistMap 𝒜 ℬ ψ (n + m) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(((mapDomain 𝒜 ℬ ψ).toScheme.toRingedSpace)).presheaf,
        (((mapDomain 𝒜 ℬ ψ).toScheme.toRingedSpace)).IsSheaf⟩)).map
        (X := ((Scheme.Modules.pullback (mapHom 𝒜 ℬ ψ)).obj (twistingSheaf 𝒜 n),
        (Scheme.Modules.pullback (mapHom 𝒜 ℬ ψ)).obj (twistingSheaf 𝒜 m)))
        (Y := ((Scheme.Modules.pullback (mapDomain 𝒜 ℬ ψ).ι).obj (twistingSheaf ℬ n),
        (Scheme.Modules.pullback (mapDomain 𝒜 ℬ ψ).ι).obj (twistingSheaf ℬ m)))
        (((twistMap 𝒜 ℬ ψ n), (twistMap 𝒜 ℬ ψ m)) : (_, _) ⟶ (_, _))) ≫
        pullbackTwistMultiplication ℬ (mapDomain 𝒜 ℬ ψ).ι n m := by
  have tensorMapUnit := tensorSheaf_map_unit_tmul (mapDomain 𝒜 ℬ ψ).toScheme.toRingedSpace
    (twistMap 𝒜 ℬ ψ n) (twistMap 𝒜 ℬ ψ m)
  generalize tensorMapEq : (Functor.uncurry.obj
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(mapDomain 𝒜 ℬ ψ).toScheme.toRingedSpace.presheaf,
        (mapDomain 𝒜 ℬ ψ).toScheme.toRingedSpace.IsSheaf⟩)).map
      (X := ((Scheme.Modules.pullback (mapHom 𝒜 ℬ ψ)).obj (twistingSheaf 𝒜 n),
        (Scheme.Modules.pullback (mapHom 𝒜 ℬ ψ)).obj (twistingSheaf 𝒜 m)))
      (Y := ((Scheme.Modules.pullback (mapDomain 𝒜 ℬ ψ).ι).obj (twistingSheaf ℬ n),
        (Scheme.Modules.pullback (mapDomain 𝒜 ℬ ψ).ι).obj (twistingSheaf ℬ m)))
      ((twistMap 𝒜 ℬ ψ n, twistMap 𝒜 ℬ ψ m) : (_, _) ⟶ (_, _)) = tensorMap
  refine (cancel_epi ((Stacks.PullbackTensorIso.pullbackTensorIso
    (mapHom 𝒜 ℬ ψ).toLRSHom.toShHom).hom.app
      (twistingSheaf 𝒜 n, twistingSheaf 𝒜 m))).mp ?_
  refine Eq.trans (Eq.trans (Category.assoc _ _ _).symm
    (congrArg (fun k => k ≫ twistMap 𝒜 ℬ ψ (n + m))
      (comparison_comp_pullbackTwistMultiplication 𝒜 (mapHom 𝒜 ℬ ψ) n m))) ?_
  refine pullbackTensor_hom_ext (mapHom 𝒜 ℬ ψ).toLRSHom.toShHom
    (twistingSheaf 𝒜 n) (twistingSheaf 𝒜 m) _ _ fun U s t => ?_
  -- the left-hand side: push the unit through the multiplication map, then use `θ`'s
  -- adjoint description
  refine Eq.trans (congrArg (Hom.app (twistMap 𝒜 ℬ ψ (n + m)).val
      (op (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U)))
    (pullbackUnit_naturality (mapHom 𝒜 ℬ ψ).toLRSHom.toShHom (twistMultiplicationMap 𝒜 n m)
      (op U) (Hom.app ((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.RingedSpace.structureRingSheaf ((AlgebraicGeometry.Proj 𝒜).toRingedSpace))
        (𝟙 (Stacks.RingedSpace.structureRingSheaf
        ((AlgebraicGeometry.Proj 𝒜).toRingedSpace)).obj)).unit.app
        (PresheafOfModules.tensorObj (O := ((AlgebraicGeometry.Proj 𝒜).toRingedSpace).presheaf)
        ((twistingSheaf 𝒜 n)).val ((twistingSheaf 𝒜 m)).val)) (op U) (s ⊗ₜ t)))) ?_
  refine Eq.trans (twistMap_pullbackUnit 𝒜 ℬ ψ (n + m) U _) ?_
  -- the mathematical content
  refine Eq.trans (congrArg (Hom.app
    ((Scheme.Modules.restrictFunctorIsoPullback (mapDomain 𝒜 ℬ ψ).ι).hom.app
      (twistingSheaf ℬ (n + m))).val (op (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U)))
    (twistPushforwardMap_twistMultiplicationMap 𝒜 ℬ ψ n m U s t)) ?_
  -- the right-hand side, read backwards
  refine Eq.trans (restrictFunctorIsoPullback_hom_app_naturality (mapDomain 𝒜 ℬ ψ).ι
    (twistMultiplicationMap ℬ n m) (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U) _) ?_
  refine congrArg (Hom.app ((Scheme.Modules.pullback (mapDomain 𝒜 ℬ ψ).ι).map
    (twistMultiplicationMap ℬ n m)).val (op (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U))) ?_
  refine Eq.trans (restrictFunctorIsoPullback_tensorSheafUnit_eq (mapDomain 𝒜 ℬ ψ).ι
    (twistingSheaf ℬ n) (twistingSheaf ℬ m) (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U)
    (Hom.app (twistPushforwardMap 𝒜 ℬ ψ n).val (op U) s)
    (Hom.app (twistPushforwardMap 𝒜 ℬ ψ m).val (op U) t)).symm ?_
  refine congrArg (Hom.app ((Stacks.PullbackTensorIso.pullbackTensorIso
    (mapDomain 𝒜 ℬ ψ).ι.toLRSHom.toShHom).inv.app
      (twistingSheaf ℬ n, twistingSheaf ℬ m)).val (op (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U))) ?_
  refine Eq.trans (congrArg₂ (fun a b => Hom.app
    ((PresheafOfModules.sheafificationAdjunction
    (R := Stacks.RingedSpace.structureRingSheaf ((mapDomain 𝒜 ℬ ψ).toScheme.toRingedSpace))
    (𝟙 (Stacks.RingedSpace.structureRingSheaf ((mapDomain 𝒜 ℬ
    ψ).toScheme.toRingedSpace)).obj)).unit.app
    (PresheafOfModules.tensorObj (O := ((mapDomain 𝒜 ℬ ψ).toScheme.toRingedSpace).presheaf)
    (((Scheme.Modules.pullback (mapDomain 𝒜 ℬ ψ).ι).obj (twistingSheaf ℬ n))).val
    (((Scheme.Modules.pullback (mapDomain 𝒜 ℬ ψ).ι).obj (twistingSheaf ℬ m))).val))
        (op (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U)) (a ⊗ₜ b))
    (twistMap_pullbackUnit 𝒜 ℬ ψ n U s).symm
    (twistMap_pullbackUnit 𝒜 ℬ ψ m U t).symm) ?_
  refine Eq.trans (tensorMapUnit (op (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U)) _ _).symm ?_
  refine Eq.trans (PresheafOfModules.hom_congr_apply'
    (congrArg (fun morphism => SheafOfModules.Hom.val morphism) tensorMapEq)
    (op (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U)) _) ?_
  exact congrArg (Hom.app tensorMap.val (op (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U)))
    (comparison_pullbackUnit_tensorSheafUnit (mapHom 𝒜 ℬ ψ).toLRSHom.toShHom
      (twistingSheaf 𝒜 n) (twistingSheaf 𝒜 m) U s t).symm

/-- **Tag 01MY, graded-algebra multiplication, on the canonical bundle.** The tagged
statement's spelling of `twistMap_comp_pullbackTwistMultiplication`: the morphism and the twist maps are the
fields of `Stacks.AlgebraicGeometry.ProjTwistCompare.projMapData`. -/
@[stacks 01MY "graded-algebra multiplication"]
public theorem projMapData_preserves_products (ψ : 𝒜 →+*ᵍ ℬ)
    (n m : ℤ) :
    pullbackTwistMultiplication 𝒜 (projMapData 𝒜 ℬ ψ).hom n m ≫
      (projMapData 𝒜 ℬ ψ).twistMap (n + m) =
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(((mapDomain 𝒜 ℬ ψ).toScheme.toRingedSpace)).presheaf,
      (((mapDomain 𝒜 ℬ ψ).toScheme.toRingedSpace)).IsSheaf⟩)).map
      ((((projMapData 𝒜 ℬ ψ).twistMap n), ((projMapData 𝒜 ℬ ψ).twistMap m)) : (_, _) ⟶ (_, _))) ≫
      pullbackTwistMultiplication ℬ (mapDomain 𝒜 ℬ ψ).ι n m :=
  twistMap_comp_pullbackTwistMultiplication 𝒜 ℬ ψ n m

end Proj

end Stacks.AlgebraicGeometry.ProjMapCard

end
