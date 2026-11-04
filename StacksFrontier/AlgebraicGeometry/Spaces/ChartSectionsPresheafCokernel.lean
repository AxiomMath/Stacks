module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSections
public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.PresheafCokernel

/-!
# The base change comparison of a presheaf quotient of modules on an algebraic space

Let `F` be an algebraic space, let `a : K ⟶ P` be a morphism of `𝒪_F`-modules on the small étale
site of `F` and let `π : P.val ⟶ C` exhibit a presheaf of modules `C` as the cokernel of `a`
computed object by object.  This file proves that the base change comparison of
`AlgebraicGeometry.Space.sectionsBaseChange` for `C` over a morphism `f : V ⟶ U` of étale charts
is bijective as soon as it is bijective for `K` and for `P`.

This is right exactness of the tensor product, read on the sections of a presheaf quotient, and it
is the step which makes the degree-zero descent of Stacks 023M available for a quotient of
cartesian modules: a *sheaf* quotient has no such property, its sections over a chart not being the
quotient of the sections, whereas the presheaf quotient has it for free.

## Main results

* `AlgebraicGeometry.Space.exists_baseChangeEquiv_sections_of_isPresheafCokernel`: **the sections
  of a presheaf quotient of `𝒪_F`-modules over a smaller chart are the base change of its sections
  over the larger chart**, as soon as that holds for the two terms of the quotient.  The
  equivalence carries `1 ⊗ₜ n` to the restriction of `n`.
* `AlgebraicGeometry.Space.chartPresheafSectionsModule` and
  `AlgebraicGeometry.Space.chartPresheafRestrictLinear`: the restriction of scalars and the
  restriction of sections of a presheaf of modules along a chart morphism, the presheaf-level
  counterparts of `AlgebraicGeometry.Space.chartSectionsModule` and
  `AlgebraicGeometry.Space.chartRestrictLinear`.

## Implementation notes

No affineness enters: affineness of the two charts is what makes the two hypotheses available
through `AlgebraicGeometry.Space.IsCartesianOnAffineCharts`, and plays no part in the argument.

The conclusion is an existential over a linear equivalence whose value on `1 ⊗ₜ n` is prescribed,
rather than bijectivity of a named map, because the `𝒪_F(U)`-module structure on the sections of
`C` over `V` is a local definition — `Module.compHom` along
`AlgebraicGeometry.Space.chartRestrict` — and a statement about a map linear for it would have to
carry that definition in its own statement.  The prescribed value determines the equivalence,
`𝒪_F(V)`-linearity giving `e (b ⊗ₜ n) = b • C.map f.op n`.

The arithmetic is `Module.BaseChange.baseChangeEquivOfPresentation`, whose four exactness
conditions on the sections are not hypotheses here: they are what
`PresheafOfModules.IsPresheafCokernel` says.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u m

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- The `𝒪_F(U)`-module structure on the sections over a smaller chart of a *presheaf* of modules,
given by restriction of scalars along `f : V ⟶ U`.  Not an instance: it depends on `f`.

This is `AlgebraicGeometry.Space.chartSectionsModule` for a presheaf of modules rather than a
sheaf of modules. -/
@[instance_reducible]
noncomputable def chartPresheafSectionsModule
    (C : PresheafOfModules.{m}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj)
    {U V : SmallEtale B S hS F} (f : V ⟶ U) :
    Module (chartRing B S hS F hF U) (C.obj (op V)) :=
  Module.compHom _ (chartRestrict f)

/-- Restriction of sections of a presheaf of modules along a chart morphism, as an
`𝒪_F(U)`-linear map.  This is `AlgebraicGeometry.Space.chartRestrictLinear` for a presheaf of
modules. -/
noncomputable def chartPresheafRestrictLinear
    (C : PresheafOfModules.{m}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj)
    {U V : SmallEtale B S hS F} (f : V ⟶ U) :
    letI := chartPresheafSectionsModule C f
    (C.obj (op U) : Type m) →ₗ[chartRing B S hS F hF U] (C.obj (op V) : Type m) :=
  let := chartPresheafSectionsModule C f
  { toFun := fun n => C.map f.op n
    map_add' := map_add (C.map f.op).hom
    map_smul' := fun c n => (C.map_smul f.op c n).symm ▸ rfl }

/-- `chartPresheafRestrictLinear C f` sends a section `n` over `U` to its restriction
`C.map f.op n` over `V`. -/
theorem chartPresheafRestrictLinear_apply
    (C : PresheafOfModules.{m}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj)
    {U V : SmallEtale B S hS F} (f : V ⟶ U) (n : C.obj (op U)) :
    chartPresheafRestrictLinear C f n = C.map f.op n := rfl

/-- **The sections of a presheaf quotient of `𝒪_F`-modules over a smaller chart are the base
change of its sections over the larger chart**, as soon as that holds for the two terms of the
quotient.

Let `a : K ⟶ P` be a morphism of `𝒪_F`-modules and let `π : P.val ⟶ C` exhibit `C` as the
cokernel of `a` computed object by object.  If the base change comparisons of `K` and of `P` over
`f : V ⟶ U` are bijective, then there is an `𝒪_F(V)`-linear equivalence
`𝒪_F(V) ⊗_{𝒪_F(U)} C(U) ≃ C(V)` carrying `1 ⊗ₜ n` to the restriction of `n`.

There is no flatness hypothesis and no affineness hypothesis: surjectivity of `π` on the sections
over both charts, which is part of being a presheaf cokernel, makes right exactness of the tensor
product sufficient. -/
theorem exists_baseChangeEquiv_sections_of_isPresheafCokernel
    {K P : Modules.{u, m} B S hS F hF}
    {C : PresheafOfModules.{m}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj}
    (a : K ⟶ P) (π : P.val ⟶ C) (hπ : PresheafOfModules.IsPresheafCokernel a.val π)
    {U V : SmallEtale B S hS F} (f : V ⟶ U)
    (hK : Function.Bijective (sectionsBaseChange K f))
    (hP : Function.Bijective (sectionsBaseChange P f)) :
    letI := chartAlgebra (hF := hF) f
    ∃ e : TensorProduct (chartRing B S hS F hF U) (chartRing B S hS F hF V)
          (C.obj (op U)) ≃ₗ[chartRing B S hS F hF V] (C.obj (op V) : Type m),
      ∀ n, e (TensorProduct.tmul _ (1 : chartRing B S hS F hF V) n) = C.map f.op n := by
  let _ := chartAlgebra (hF := hF) f
  let _ := chartSectionsModule K f
  let _ := chartSectionsModule P f
  let _ := chartPresheafSectionsModule C f
  have _ := chartSections_isScalarTower K f
  have _ := chartSections_isScalarTower P f
  have _ : IsScalarTower (chartRing B S hS F hF U) (chartRing B S hS F hF V)
      (C.obj (op V)) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  refine ⟨Module.BaseChange.baseChangeEquivOfPresentation
    (a.val.app (op U)).hom (π.app (op U)).hom (a.val.app (op V)).hom (π.app (op V)).hom
    (chartRestrictLinear K f) (chartRestrictLinear P f) (chartPresheafRestrictLinear C f)
    (fun x => (PresheafOfModules.naturality_apply a.val f.op x).symm)
    (fun x => (PresheafOfModules.naturality_apply π f.op x).symm)
    hK hP (hπ.surjective (op U)) (hπ.surjective (op V))
    (fun x => hπ.app_app_eq_zero (op U) x)
    (fun x hx => (hπ.exact (op V) x).mp hx), fun n => ?_⟩
  exact Module.BaseChange.baseChangeEquivOfPresentation_one_tmul _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n

end AlgebraicGeometry.Space

end
