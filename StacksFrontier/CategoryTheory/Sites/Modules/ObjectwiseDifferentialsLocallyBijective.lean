module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PrincipalPartsUniversal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import StacksCore.Tactic.StacksAttribute

/-!
# Objectwise differentials map locally bijectively to the sheaf of differentials

Let `(C, J)` be a site and `φ : O₁ ⟶ O₂` a morphism of sheaves of commutative rings. Let `Q` be
the presheaf of `O₂`-modules `U ↦ Ω[O₂(U)⁄O₁(U)]` of objectwise Kähler differentials, and let
`Ω_{O₂/O₁}` be the sheaf of relative differentials of Stacks 04BN, with universal derivation
`d`. Sending `d b` to `d b` defines a morphism of presheaves of modules `Q ⟶ Ω_{O₂/O₁}`, and
this file proves that it is locally injective and locally surjective. Equivalently,
`Ω_{O₂/O₁}` is the sheaf associated to `Q` (Stacks 08TP, for sheaves of rings).

## Main definitions

* `AlgebraicGeometry.SheafOfModules.objectwiseDifferentials`: the presheaf of modules
  `U ↦ Ω[O₂(U)⁄O₁(U)]`, with values lifted to the coefficient-module universe.
* `AlgebraicGeometry.SheafOfModules.objectwiseDifferentialsToSheaf`: the comparison morphism
  `Q ⟶ Ω_{O₂/O₁}`.
* `AlgebraicGeometry.SheafOfModules.objectwiseDifferentialsSheafificationHom`: the morphism of
  sheaves of modules from the sheafification of `Q` to `Ω_{O₂/O₁}` adjunct to the comparison.

## Main results

* `AlgebraicGeometry.SheafOfModules.objectwiseDifferentialsToSheaf_d`: the comparison sends
  `d b` to `d b`.
* `AlgebraicGeometry.SheafOfModules.isIso_objectwiseDifferentialsSheafificationHom`: the
  sheafification of `Q` is isomorphic to `Ω_{O₂/O₁}` through the comparison.
* `AlgebraicGeometry.SheafOfModules.isLocallyInjective_objectwiseDifferentialsToSheaf` and
  `AlgebraicGeometry.SheafOfModules.isLocallySurjective_objectwiseDifferentialsToSheaf`: the
  comparison is locally injective and locally surjective.

## Implementation notes

The sheafification of `Q` carries the relative derivation `η ∘ d`, where `η` is the unit of
sheafification; it factors through the universal derivation of `Ω_{O₂/O₁}` by a morphism `χ`
(`existsUnique_descDerivation`). The adjunct `μ'` of the comparison and `χ` are mutually
inverse: `χ ≫ μ' = 𝟙` by the uniqueness in `existsUnique_descDerivation`, and `μ' ≫ χ = 𝟙`
because morphisms out of a sheafification are determined by their composite with `η` and
morphisms out of `Q` by their values on the differentials `d b` (`liftedDiffUniversal`). The
comparison is then the composite of the locally bijective unit `η` with an isomorphism.

The site is `C : Type u₁` with `Category.{v₁} C`, the rings are `CommRingCat.{u}`-valued and
the modules live in the universe `max u u₁ v₁ v` of `liftPresheaf`, which is also the
universe of `moduleOfDifferentialsOfSite.{v₁, u₁, u, v}`. On the small étale site of an
algebraic space this is the module universe `u + 1`. Sheafification of abelian presheaves at
that universe is assumed through `HasWeakSheafify` and `WEqualsLocallyBijective`; it is used
only in the proofs.

## References

* [Stacks Project, Tag 08TP](https://stacks.math.columbia.edu/tag/08TP)
* [Stacks Project, Tag 04BN](https://stacks.math.columbia.edu/tag/04BN)
-/

@[expose] public noncomputable section

open CategoryTheory

universe v v₁ u u₁

namespace AlgebraicGeometry.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (O₁ O₂ : Sheaf J CommRingCat.{u}) (φ : O₁ ⟶ O₂)

/-- The presheaf of `O₂`-modules `U ↦ Ω[O₂(U)⁄O₁(U)]` of objectwise Kähler differentials, with
its values lifted to the coefficient-module universe `max u u₁ v₁ v`. -/
abbrev objectwiseDifferentials :
    PresheafOfModules.{max u u₁ v₁ v} (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj :=
  liftPresheaf.{v, v₁, u, u₁}
    (PresheafOfModules.DifferentialsConstruction.relativeDifferentials' φ.hom)

/-- The comparison morphism from the objectwise Kähler differentials to the sheaf of relative
differentials `Ω_{O₂/O₁}`: it sends `d b` to the universal derivation of `Ω_{O₂/O₁}` at `b`. -/
def objectwiseDifferentialsToSheaf :
    objectwiseDifferentials.{v} O₁ O₂ φ ⟶
      (moduleOfDifferentialsOfSite.{v₁, u₁, u, v} O₁ O₂ φ).val :=
  (liftedDiffUniversal.{max u u₁ v₁ v, v₁, u, u₁} φ.hom).desc
    (universalDerivationOfSite.{v₁, u₁, u, v} O₁ O₂ φ)

/-- The comparison composed with the objectwise universal derivation is the universal
derivation of `Ω_{O₂/O₁}`. -/
theorem objectwiseDifferentialsToSheaf_postcomp :
    (liftedDiffDerivation.{v₁, u, u₁, v} φ.hom).postcomp
        (objectwiseDifferentialsToSheaf.{v} O₁ O₂ φ) =
      universalDerivationOfSite.{v₁, u₁, u, v} O₁ O₂ φ :=
  (liftedDiffUniversal.{max u u₁ v₁ v, v₁, u, u₁} φ.hom).fac _

/-- The comparison sends the objectwise differential `d b` to the universal derivation of
`Ω_{O₂/O₁}` evaluated at `b`. -/
theorem objectwiseDifferentialsToSheaf_d (X : Cᵒᵖ) (b : O₂.obj.obj X) :
    ((objectwiseDifferentialsToSheaf.{v} O₁ O₂ φ).app X).hom
        ((liftedDiffDerivation.{v₁, u, u₁, v} φ.hom).d b) =
      (universalDerivationOfSite.{v₁, u₁, u, v} O₁ O₂ φ).d b :=
  PresheafOfModules.Derivation.congr_d (objectwiseDifferentialsToSheaf_postcomp O₁ O₂ φ) b

section Sheafification

variable [HasWeakSheafify J AddCommGrpCat.{max u u₁ v₁ v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u u₁ v₁ v}]

/-- The morphism from the sheafification of the objectwise Kähler differentials to the sheaf of
relative differentials `Ω_{O₂/O₁}` adjunct to `objectwiseDifferentialsToSheaf`. -/
def objectwiseDifferentialsSheafificationHom :
    (PresheafOfModules.sheafification.{max u u₁ v₁ v}
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)).obj
        (objectwiseDifferentials.{v} O₁ O₂ φ) ⟶
      moduleOfDifferentialsOfSite.{v₁, u₁, u, v} O₁ O₂ φ :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)).homEquiv _ _).symm
    (objectwiseDifferentialsToSheaf.{v} O₁ O₂ φ)

/-- The unit of sheafification followed by `objectwiseDifferentialsSheafificationHom` is the
comparison `objectwiseDifferentialsToSheaf`. -/
theorem objectwiseDifferentialsSheafificationHom_fac :
    (PresheafOfModules.sheafificationAdjunction
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)).unit.app
        (objectwiseDifferentials.{v} O₁ O₂ φ) ≫
      (objectwiseDifferentialsSheafificationHom.{v} O₁ O₂ φ).val =
      objectwiseDifferentialsToSheaf.{v} O₁ O₂ φ :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)).homEquiv_unit _ _ _).symm.trans
    (((PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)).homEquiv _ _).apply_symm_apply _)

/-- The sheafification of the objectwise Kähler differentials is the sheaf of relative
differentials: `objectwiseDifferentialsSheafificationHom` is an isomorphism. -/
@[stacks 08TP "for sheaves of rings, as an isomorphism out of the sheafification"]
theorem isIso_objectwiseDifferentialsSheafificationHom :
    IsIso (objectwiseDifferentialsSheafificationHom.{v} O₁ O₂ φ) := by
  let R := Stacks.SheafOfModules.Tensor.ringSheaf O₂
  let Q := objectwiseDifferentials.{v} O₁ O₂ φ
  let sh := (PresheafOfModules.sheafification.{max u u₁ v₁ v} (𝟙 R.obj)).obj Q
  let Ω := moduleOfDifferentialsOfSite.{v₁, u₁, u, v} O₁ O₂ φ
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app Q
  let dQ : Q.Derivation' φ.hom := liftedDiffDerivation.{v₁, u, u₁, v} φ.hom
  let eQ := liftedDiffUniversal.{max u u₁ v₁ v, v₁, u, u₁} φ.hom
  let dΩ := universalDerivationOfSite.{v₁, u₁, u, v} O₁ O₂ φ
  let μ : Q ⟶ Ω.val := objectwiseDifferentialsToSheaf.{v} O₁ O₂ φ
  let μ' : sh ⟶ Ω := objectwiseDifferentialsSheafificationHom.{v} O₁ O₂ φ
  have hμ : η ≫ μ'.val = μ := objectwiseDifferentialsSheafificationHom_fac.{v} O₁ O₂ φ
  have hdμ : dQ.postcomp μ = dΩ := objectwiseDifferentialsToSheaf_postcomp.{v} O₁ O₂ φ
  let D : sh.val.Derivation' φ.hom := dQ.postcomp η
  obtain ⟨χ, hχ, -⟩ := existsUnique_descDerivation.{v₁, u₁, u, v} O₁ O₂ φ sh D
  have hdμ' : D.postcomp μ'.val = dΩ := by
    rw [← hdμ, ← hμ]
    ext X x; rfl
  refine ⟨χ, ?_, ?_⟩
  · apply (PresheafOfModules.sheafificationHomEquiv (R := R) (𝟙 R.obj)).injective
    change η ≫ (μ' ≫ χ).val = η ≫ 𝟙 sh.val
    apply eQ.postcomp_injective
    trans (D.postcomp μ'.val).postcomp χ.val
    · ext X x; rfl
    · rw [hdμ', hχ]
      ext X x; rfl
  · apply (existsUnique_descDerivation.{v₁, u₁, u, v} O₁ O₂ φ Ω dΩ).unique
    · trans (dΩ.postcomp χ.val).postcomp μ'.val
      · ext X x; rfl
      · rw [hχ, hdμ']
    · ext X x; rfl

/-- The comparison `objectwiseDifferentialsToSheaf` is the unit of sheafification followed by
an isomorphism, on underlying presheaves of abelian groups. -/
theorem toPresheaf_map_objectwiseDifferentialsToSheaf :
    CategoryTheory.toSheafify J (objectwiseDifferentials.{v} O₁ O₂ φ).presheaf ≫
        (PresheafOfModules.toPresheaf _).map
          (objectwiseDifferentialsSheafificationHom.{v} O₁ O₂ φ).val =
      (PresheafOfModules.toPresheaf _).map (objectwiseDifferentialsToSheaf.{v} O₁ O₂ φ) :=
  ((PresheafOfModules.toPresheaf _).map_comp _ _).symm.trans
    (congrArg (PresheafOfModules.toPresheaf _).map
      (objectwiseDifferentialsSheafificationHom_fac.{v} O₁ O₂ φ))

/-- The underlying morphism of abelian presheaves of
`objectwiseDifferentialsSheafificationHom` is an isomorphism. -/
instance isIso_toPresheaf_map_objectwiseDifferentialsSheafificationHom :
    IsIso ((PresheafOfModules.toPresheaf _).map
      (objectwiseDifferentialsSheafificationHom.{v} O₁ O₂ φ).val) := by
  have := isIso_objectwiseDifferentialsSheafificationHom.{v} O₁ O₂ φ
  have : IsIso (objectwiseDifferentialsSheafificationHom.{v} O₁ O₂ φ).val :=
    inferInstanceAs (IsIso ((_root_.SheafOfModules.forget _).map
      (objectwiseDifferentialsSheafificationHom.{v} O₁ O₂ φ)))
  infer_instance

/-- **Stacks 08TP**, injectivity half: the comparison from the objectwise Kähler differentials
to the sheaf of relative differentials is locally injective. -/
@[stacks 08TP "for sheaves of rings, local injectivity"]
theorem isLocallyInjective_objectwiseDifferentialsToSheaf :
    PresheafOfModules.IsLocallyInjective J (objectwiseDifferentialsToSheaf.{v} O₁ O₂ φ) := by
  have := isIso_toPresheaf_map_objectwiseDifferentialsSheafificationHom.{v} O₁ O₂ φ
  have hψ := Presheaf.instIsLocallyInjectiveOfIsIsoFunctorOpposite (J := J)
    (φ := (PresheafOfModules.toPresheaf _).map
      (objectwiseDifferentialsSheafificationHom.{v} O₁ O₂ φ).val)
  have hη := (J.W_toSheafify (objectwiseDifferentials.{v} O₁ O₂ φ).presheaf).isLocallyInjective
  exact (congrArg (Presheaf.IsLocallyInjective J)
    (toPresheaf_map_objectwiseDifferentialsToSheaf.{v} O₁ O₂ φ)).mp
    (@Presheaf.isLocallyInjective_comp _ _ _ _ _ _ _ _ J _ _ _ _ _ hη hψ)

/-- **Stacks 08TP**, surjectivity half: the comparison from the objectwise Kähler differentials
to the sheaf of relative differentials is locally surjective. -/
@[stacks 08TP "for sheaves of rings, local surjectivity"]
theorem isLocallySurjective_objectwiseDifferentialsToSheaf :
    PresheafOfModules.IsLocallySurjective J (objectwiseDifferentialsToSheaf.{v} O₁ O₂ φ) := by
  have := isIso_toPresheaf_map_objectwiseDifferentialsSheafificationHom.{v} O₁ O₂ φ
  exact (Presheaf.isLocallySurjective_iff_of_fac J
    (toPresheaf_map_objectwiseDifferentialsToSheaf.{v} O₁ O₂ φ)).2
    (Presheaf.isLocallySurjective_of_iso J
      ((PresheafOfModules.toPresheaf _).map
        (objectwiseDifferentialsSheafificationHom.{v} O₁ O₂ φ).val))

end Sheafification

end AlgebraicGeometry.SheafOfModules

end
