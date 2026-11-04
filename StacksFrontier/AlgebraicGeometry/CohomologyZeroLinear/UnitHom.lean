module

public import StacksFrontier.AlgebraicGeometry.CohomologyZeroLinear.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverFieldDualityLinear
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Morphisms out of the structure sheaf are degree-zero cohomology, `k`-linearly

For a scheme `X` over a field `k` and a sheaf of `𝒪_X`-modules `ℱ`,

  `Hom_{𝒪_X}(𝒪_X, ℱ) = Γ(ℱ, ⊤) = H⁰(X, ℱ)`,

and this composite is an isomorphism of `k`-vector spaces. The `k`-action on
`Hom_{𝒪_X}(𝒪_X, ℱ)` is the one `AlgebraicGeometry.Scheme.Modules.linearOverBase` puts on the
category of modules, where a scalar acts by multiplication by its image in `Γ(X, 𝒪_X)`, and
`H⁰(X, ℱ)` is a `k`-vector space by the restriction of scalars
`AlgebraicGeometry.restrictScalarsOverBase`.

## Main definitions

* `AlgebraicGeometry.unitHomLinearEquivSections` — `Hom_{𝒪_X}(𝒪_X, ℱ) ≃ₗ[k] Γ(ℱ, ⊤)`.
* `AlgebraicGeometry.unitHomLinearEquivCohomologyOverFieldZero` —
  `Hom_{𝒪_X}(𝒪_X, ℱ) ≃ₗ[k] H⁰(X, ℱ)`.

## Implementation notes

The structure sheaf is named `Stacks.Ample.unitModule X`, which is `SheafOfModules.unit
X.ringCatSheaf` at the type `AlgebraicGeometry.Scheme.Modules`: the `k`-module structure on a
morphism group of `X.Modules` is not found when the source is spelled at the type
`SheafOfModules X.ringCatSheaf`, which is the same type but not that `def`.

The unit section is introduced by a `let` with a `change` rather than written as the numeral `1`
in the module `Γ(unitModule X, ⊤)`: that module is an abelian group as far as instance search is
concerned, and the `OfNat` instance lives on `Γ(X, ⊤)` only.

Compatibility of a family of sections is handled by `PresheafOfModules.map_comp_apply` and
`PresheafOfModules.congr_map_apply` in term mode rather than by `rw`: the topology carried by
`(⊤ : X.Opens)` and the one carried by the site of `X.ringCatSheaf` are definitionally but not
reducibly equal, so a `rewrite` leaves the goal ill-typed at the transparency it uses.

## References

* [Stacks Project, Tag 01AD](https://stacks.math.columbia.edu/tag/01AD)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The isomorphism `Hom_{𝒪_X}(𝒪_X, ℱ) ≃ₗ[k] Γ(ℱ, ⊤)` of `k`-vector spaces on a scheme over `k`,
sending a morphism out of the structure sheaf to the global section it sends the unit section
to. -/
@[ega "II 1.7.13" "Hom_{O_S}(O_S"]
def unitHomLinearEquivSections (M : X.Modules) :
    letI := Scheme.Modules.linearOverBase f
    (Stacks.Ample.unitModule X ⟶ M) ≃ₗ[k]
      (restrictScalarsOverBase k f).obj
        ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj M) := by
  letI := Scheme.Modules.linearOverBase f
  let one : (Stacks.Ample.unitModule X).val.obj (op (⊤ : X.Opens)) := by
    change X.ringCatSheaf.obj.obj (op (⊤ : X.Opens))
    exact 1
  refine LinearEquiv.ofBijective
    ({ toFun := fun g => (M.unitHomEquiv g).val (op (⊤ : X.Opens))
       map_add' := fun _ _ => rfl
       map_smul' := fun a g =>
         Scheme.smul_val_app_top X k (Stacks.LocalCohomology.baseScalars k f) a g one } :
      (Stacks.Ample.unitModule X ⟶ M) →ₗ[k]
        (restrictScalarsOverBase k f).obj
          ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj M)) ⟨?_, ?_⟩
  · intro g h hgh
    apply M.unitHomEquiv.injective
    apply Subtype.ext
    funext V
    have hg := (M.unitHomEquiv g).property (Limits.isTerminalTop.from V.unop).op
    have hh := (M.unitHomEquiv h).property (Limits.isTerminalTop.from V.unop).op
    exact hg.symm.trans ((congrArg _ hgh).trans hh)
  · intro s
    refine ⟨M.unitHomEquiv.symm (PresheafOfModules.sectionsMk
      (fun V => M.val.map (Limits.isTerminalTop.from V.unop).op s) ?_), ?_⟩
    · intro V W g
      exact (PresheafOfModules.map_comp_apply M.val
          (Limits.isTerminalTop.from V.unop).op g s).symm.trans
        (PresheafOfModules.congr_map_apply M.val
          (Quiver.Hom.unop_inj (Limits.isTerminalTop.hom_ext _ _)) s)
    · refine Eq.trans (congrArg (fun z => (z : M.sections).val (op (⊤ : X.Opens)))
        (Equiv.apply_symm_apply M.unitHomEquiv _)) ?_
      exact (PresheafOfModules.congr_map_apply M.val
          (congrArg Quiver.Hom.op (Limits.isTerminalTop.hom_ext _ (𝟙 _))) s).trans
        (congrFun (congrArg (fun z => (ConcreteCategory.hom z).toFun) (M.val.map_id _)) s)

/-- The isomorphism `Hom_{𝒪_X}(𝒪_X, ℱ) ≃ₗ[k] H⁰(X, ℱ)` of `k`-vector spaces on a scheme over `k`:
`AlgebraicGeometry.unitHomLinearEquivSections` followed by the identification
`AlgebraicGeometry.cohomologyOverFieldZeroLinearIso` of degree-zero cohomology with global
sections. -/
def unitHomLinearEquivCohomologyOverFieldZero (M : X.Modules) :
    letI := Scheme.Modules.linearOverBase f
    (Stacks.Ample.unitModule X ⟶ M) ≃ₗ[k] cohomologyOverField k f M 0 :=
  letI := Scheme.Modules.linearOverBase f
  (unitHomLinearEquivSections f M).trans
    (cohomologyOverFieldZeroLinearIso k f M).symm.toLinearEquiv

end AlgebraicGeometry

end
