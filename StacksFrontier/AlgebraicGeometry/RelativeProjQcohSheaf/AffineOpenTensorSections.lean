module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineTensorGeneral
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaRestrictionSections

/-!
# Sections of a tensor product over an affine open

Let `S` be a scheme, `V ⊆ S` an affine open and `F`, `G` quasi-coherent `𝒪_S`-modules. This file
proves that the canonical map

$$\Gamma(V, F) \otimes_{\Gamma(S, V)} \Gamma(V, G) \longrightarrow \Gamma(V, F \otimes G)$$

is an isomorphism of `Γ(S, V)`-modules. This is Tag 01I8 read over an arbitrary affine open of
an arbitrary scheme, rather than over the whole of a spectrum.

Two weaker forms were already available. `AlgebraicGeometry.TildeTensor.gammaTensorEquiv` is the
isomorphism, but only for `V = ⊤` on `Spec R`; and
`Stacks.AlgebraicGeometry.AffineTensorGeneral.span_gammaTmul_eq_top` is the statement over an
arbitrary affine scheme, but only as a *spanning* statement — the pure tensors generate, which
is surjectivity and says nothing about injectivity. What is proved here is the bijection, over
an arbitrary affine open.

## The canonical map is the sheafification unit

The tensor product of two sheaves of modules is the sheafification of the presheaf
`U ↦ F(U) ⊗_{𝒪(U)} G(U)`, and the comparison map of the statement is nothing but the
sheafification unit read over `V`. So no map has to be built: `gammaTensorMap` below is
`PresheafOfModules.tensorSheafUnit` retyped, it is `Γ(S, V)`-linear by construction, and it
carries a pure tensor to `Stacks.PullbackTensorCoherence.tmul` definitionally. Only bijectivity
is at issue.

## The proof

Write `j := hV.fromSpec : Spec Γ(S, V) ⟶ S`, which is an open immersion with image `V`. The
bijection is exhibited as a composite of four bijections,

$$\Gamma(V,F) \otimes \Gamma(V,G) \to \Gamma(j^{-1}F, \top) \otimes \Gamma(j^{-1}G, \top) \to
\Gamma(j^{-1}F \otimes j^{-1}G, \top) \to \Gamma(j^{-1}(F \otimes G), \top) \to
\Gamma(F \otimes G, V),$$

namely `AlgebraicGeometry.affineSectionsLinearEquiv` on each factor, Tag 01I8 on the spectrum
`Spec Γ(S, V)`, the inverse of the comparison
`Stacks.AlgebraicGeometry.RestrictionSections.restrictTensorIso` of a restriction of a tensor
product with the tensor product of the restrictions, and `affineSectionsLinearEquiv` again. The
middle map is used only as a *bijection* and never as a linear map, which is what lets the
composite be assembled without transporting any scalar action across the comparison.

That composite is then identified with `gammaTensorMap` by induction on the tensor: both are
additive, so it is enough to check a pure tensor, and there the computation is
`restrictTensorIso_hom_unit_tmul` followed by
`Stacks.AlgebraicGeometry.RestrictionSections.tensorSheafUnit_val_map`, which moves the
sheafification unit along the equality of opens `j(⊤) = V` that `affineSectionsLinearEquiv` is
the transport for.

## Main definitions

* `Stacks.AlgebraicGeometry.AffineOpenTensorSections.gammaTensorMap`: the canonical map
  `Γ(V, F) ⊗_{Γ(S, V)} Γ(V, G) → Γ(V, F ⊗ G)`, over an arbitrary open.
* `Stacks.AlgebraicGeometry.AffineOpenTensorSections.gammaTensorEquiv`: **the affine
  tensor-sections isomorphism**, the same map over an affine open, packaged as a linear
  equivalence.

## Main results

* `Stacks.AlgebraicGeometry.AffineOpenTensorSections.bijective_gammaTensorMap`: **the canonical
  map is bijective over an affine open**, for `F` and `G` quasi-coherent.
* `Stacks.AlgebraicGeometry.AffineOpenTensorSections.span_gammaTmul_eq_top`: the pure tensors of
  sections over an affine open span the sections of the tensor product. This is the surjective
  half, in the shape `AffineTensorGeneral` states it at `⊤`.
* `Stacks.AlgebraicGeometry.AffineOpenTensorSections.exists_gammaTmul_notMem`: **a proper
  submodule of the sections of `F ⊗ G` over an affine open is escaped by a pure tensor.** This
  is the form in which the spanning statement is consumed by an argument about a point of a
  relative homogeneous spectrum, whose homogeneous pieces are proper submodules.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry MonoidalCategory PresheafOfModules
open scoped AlgebraicGeometry TensorProduct

universe u

namespace Stacks.AlgebraicGeometry.AffineOpenTensorSections

open Stacks.RingedSpace (structureRingSheaf)
open Stacks.AlgebraicGeometry.RestrictionSections
open Stacks.AlgebraicGeometry

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

attribute [local instance] Stacks.Algebraization.sectionsModuleΓ
  Stacks.Algebraization.sectionsModuleΓSheaf Stacks.Algebraization.sectionsSMulCommClassΓ
  Stacks.Algebraization.sectionsModuleΓPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafVal

variable {S : Scheme.{u}}

/-- A sheaf of modules on a scheme, retyped over the `Stacks.RingedSpace.structureRingSheaf`
spelling of the structure sheaf, which is the spelling the monoidal product of Tag 01CA is
indexed by. The crossing of the `rfl`-equality of the two spellings is done here, once. -/
abbrev ofScheme (F : S.Modules) : SheafOfModules.{u} (structureRingSheaf S.toRingedSpace) := F

/-- The monoidal product of two sheaves of modules on `S`. -/
abbrev tensorSheafMod (F G : S.Modules) :
    SheafOfModules.{u} (structureRingSheaf S.toRingedSpace) := ofScheme F ⊗ ofScheme G

/-- The monoidal product of two sheaves of modules on `S`, retyped as an object of
`AlgebraicGeometry.Scheme.Modules`. -/
abbrev tensorMod (F G : S.Modules) : S.Modules := tensorSheafMod F G

/-- The section of `F ⊗ G` over `V` attached to a pair of sections of `F` and `G` over `V`: the
image of their pure tensor under the unit of the sheafification that forms the tensor product.
The type is ascribed at the `Γ(·, ·)` spelling, which is what carries the `Γ(S, V)`-module
structure that instance search finds. -/
def gammaTmul (F G : S.Modules) (V : S.Opens) (s : Γ(F, V)) (t : Γ(G, V)) :
    Γ(tensorMod F G, V) :=
  Stacks.PullbackTensorCoherence.tmul S.toRingedSpace (ofScheme F) (ofScheme G) (op V) s t

/-- **The canonical map `Γ(V, F) ⊗_{Γ(S, V)} Γ(V, G) → Γ(V, F ⊗ G)`**, over an arbitrary open
`V`: the sheafification unit of the tensor product, read over `V` and retyped as a `Γ(S, V)`-
linear map. It is linear by construction, no hypothesis on `F`, `G` or `V` being needed to name
it; `bijective_gammaTensorMap` is where `V` affine and `F`, `G` quasi-coherent enter. -/
def gammaTensorMap (F G : S.Modules) (V : S.Opens) :
    Γ(F, V) ⊗[Γ(S, V)] Γ(G, V) →ₗ[Γ(S, V)] Γ(tensorMod F G, V) :=
  ModuleCat.Hom.hom ((PresheafOfModules.tensorSheafUnit (ofScheme F) (ofScheme G)).app (op V))

/-- The canonical map carries a pure tensor to the pure tensor of local sections of
`Stacks.PullbackTensorCoherence.tmul`. The two are the same term. -/
@[simp] theorem gammaTensorMap_tmul (F G : S.Modules) (V : S.Opens)
    (a : Γ(F, V)) (b : Γ(G, V)) :
    gammaTensorMap F G V (a ⊗ₜ[Γ(S, V)] b) = gammaTmul F G V a b :=
  rfl

/-- The canonical map is the sheafification unit, in the `Stacks.RingedSpace.tensorSheafUnit`
spelling that the comparison lemmas of
`Stacks.AlgebraicGeometry.RestrictionSections` are stated in. -/
theorem gammaTensorMap_tmul_eq_unit (F G : S.Modules) (V : S.Opens)
    (a : Γ(F, V)) (b : Γ(G, V)) :
    gammaTensorMap F G V (a ⊗ₜ[Γ(S, V)] b) =
      Hom.app ((PresheafOfModules.sheafificationAdjunction.{u}
          (R := Stacks.RingedSpace.structureRingSheaf (S.toRingedSpace))
          (𝟙 (Stacks.RingedSpace.structureRingSheaf (S.toRingedSpace)).obj)).unit.app
          (PresheafOfModules.tensorObj (O := (S.toRingedSpace).presheaf)
            ((ofScheme F)).val ((ofScheme G)).val))
        (op V) (a ⊗ₜ b) :=
  rfl

variable {V : S.Opens}

/-- The restriction of a sheaf of modules on `S` to the spectrum of the ring of functions on an
affine open `V`, along `AlgebraicGeometry.IsAffineOpen.fromSpec`. Its sections over an open `W`
are the sections of the original over the image of `W`; in particular its global sections are
`Γ(F, V)`, which is what `AlgebraicGeometry.affineSectionsLinearEquiv` expresses. -/
abbrev resMod (hV : IsAffineOpen V) (F : S.Modules) : (Spec Γ(S, V)).Modules :=
  F.restrict hV.fromSpec

/-- The image of `⊤` under `AlgebraicGeometry.IsAffineOpen.fromSpec` is the affine open itself:
that morphism is an open immersion with range `V`. -/
theorem image_top_fromSpec (hV : IsAffineOpen V) :
    hV.fromSpec ''ᵁ (⊤ : (Spec Γ(S, V)).Opens) = V := by
  rw [Scheme.Hom.image_top_eq_opensRange, hV.opensRange_fromSpec]

/-- **The inverse of the comparison of a restriction of a tensor product with the tensor product
of the restrictions**, read on global sections over `Spec Γ(S, V)`.

This is used only as a bijection — never as a linear map — which is why no scalar action has to
be transported across it. -/
def chartComparisonInv (hV : IsAffineOpen V) (F G : S.Modules) :
    Γ(AffineTensorRecovery.tensorMod (resMod hV F) (resMod hV G), ⊤) →
      Γ(resMod hV (tensorMod F G), ⊤) :=
  fun z => Hom.app (restrictTensorIso hV.fromSpec F G).inv.val (op ⊤) z

/-- `chartComparisonInv` is bijective: it is an isomorphism of sheaves of modules read on
sections over an open. -/
theorem chartComparisonInv_bijective (hV : IsAffineOpen V) (F G : S.Modules) :
    Function.Bijective (chartComparisonInv hV F G) :=
  Function.bijective_iff_has_inverse.2
    ⟨fun z => Hom.app (restrictTensorIso hV.fromSpec F G).hom.val (op ⊤) z,
      fun a => Stacks.SheafOfModules.hom_val_app_inv_val_app
        (restrictTensorIso hV.fromSpec F G) (op ⊤) a,
      fun z => Stacks.SheafOfModules.inv_val_app_hom_val_app
        (restrictTensorIso hV.fromSpec F G) (op ⊤) z⟩

/-- `chartComparisonInv` is additive. -/
theorem chartComparisonInv_add (hV : IsAffineOpen V) (F G : S.Modules)
    (y z : Γ(AffineTensorRecovery.tensorMod (resMod hV F) (resMod hV G), ⊤)) :
    chartComparisonInv hV F G (y + z) =
      chartComparisonInv hV F G y + chartComparisonInv hV F G z :=
  map_add _ _ _

/-- `chartComparisonInv` carries the zero section to the zero section. -/
theorem chartComparisonInv_zero (hV : IsAffineOpen V) (F G : S.Modules) :
    chartComparisonInv hV F G 0 = 0 :=
  map_zero _

/-- `chartComparisonInv` undoes the comparison on the sheafification-unit image of a pure
tensor: it carries the pure tensor of two global sections upstairs to the pure tensor of the
same two sections, read over the image `j(⊤)` of `⊤`. -/
theorem chartComparisonInv_unit_tmul (hV : IsAffineOpen V) (F G : S.Modules)
    (a : Γ(resMod hV F, ⊤)) (b : Γ(resMod hV G, ⊤)) :
    chartComparisonInv hV F G
        (Hom.app ((PresheafOfModules.sheafificationAdjunction.{u}
            (R := Stacks.RingedSpace.structureRingSheaf ((Spec Γ(S, V)).toRingedSpace))
            (𝟙 (Stacks.RingedSpace.structureRingSheaf
              ((Spec Γ(S, V)).toRingedSpace)).obj)).unit.app
            (PresheafOfModules.tensorObj (O := ((Spec Γ(S, V)).toRingedSpace).presheaf)
              ((resMod hV F)).val ((resMod hV G)).val)) (op ⊤) (a ⊗ₜ b)) =
      Hom.app ((PresheafOfModules.sheafificationAdjunction.{u}
          (R := Stacks.RingedSpace.structureRingSheaf (S.toRingedSpace))
          (𝟙 (Stacks.RingedSpace.structureRingSheaf (S.toRingedSpace)).obj)).unit.app
          (PresheafOfModules.tensorObj (O := (S.toRingedSpace).presheaf)
            ((ofScheme F)).val ((ofScheme G)).val))
        (op (hV.fromSpec ''ᵁ (⊤ : (Spec Γ(S, V)).Opens))) (a ⊗ₜ b) := by
  refine Eq.trans (congrArg (chartComparisonInv hV F G)
    (restrictTensorIso_hom_unit_tmul hV.fromSpec F G ⊤ a b).symm) ?_
  exact Stacks.SheafOfModules.inv_val_app_hom_val_app (restrictTensorIso hV.fromSpec F G)
    (op ⊤) _

/-- **The composite bijection**: the four-step chain of the module docstring, as a plain
function. It is identified with `gammaTensorMap` in `gammaTensorInv_eq`. -/
def gammaTensorInv (hV : IsAffineOpen V) (F G : S.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] :
    Γ(F, V) ⊗[Γ(S, V)] Γ(G, V) → Γ(tensorMod F G, V) :=
  fun z =>
    affineSectionsLinearEquiv (tensorMod F G) hV
      (chartComparisonInv hV F G
        (AffineTensorRecovery.gammaTensorEquiv (resMod hV F) (resMod hV G)
          (TensorProduct.congr (affineSectionsLinearEquiv F hV).symm
            (affineSectionsLinearEquiv G hV).symm z)))

/-- The composite is bijective, being a composite of four bijections. -/
theorem gammaTensorInv_bijective (hV : IsAffineOpen V) (F G : S.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] :
    Function.Bijective (gammaTensorInv hV F G) :=
  ((affineSectionsLinearEquiv (tensorMod F G) hV).bijective.comp
    ((chartComparisonInv_bijective hV F G).comp
      ((AffineTensorRecovery.gammaTensorEquiv (resMod hV F) (resMod hV G)).bijective.comp
        (TensorProduct.congr (affineSectionsLinearEquiv F hV).symm
          (affineSectionsLinearEquiv G hV).symm).bijective)))

/-- The affine comparison of sections is the restriction map along the equality of opens
`j(⊤) = V`, applied to a section. This is
`AlgebraicGeometry.affineSectionsLinearEquiv_eq_map` at the equality `image_top_fromSpec`. -/
theorem affineSectionsLinearEquiv_eq (hV : IsAffineOpen V) (M : S.Modules)
    (t : Γ(resMod hV M, ⊤)) :
    affineSectionsLinearEquiv M hV t =
      M.val.map (eqToHom (image_top_fromSpec hV).symm).op t :=
  affineSectionsLinearEquiv_eq_map M hV (image_top_fromSpec hV) t

/-- **The composite agrees with the canonical map.** Both are additive, so it is enough to
check a pure tensor, and there the computation is the comparison on the unit image followed by
the naturality of the unit along the equality of opens `j(⊤) = V`. -/
theorem gammaTensorInv_eq (hV : IsAffineOpen V) (F G : S.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] (z : Γ(F, V) ⊗[Γ(S, V)] Γ(G, V)) :
    gammaTensorInv hV F G z = gammaTensorMap F G V z := by
  dsimp only [gammaTensorInv]
  induction z using TensorProduct.induction_on with
  | zero =>
      rw [map_zero, map_zero, chartComparisonInv_zero, map_zero, map_zero]
  | tmul a b =>
      rw [TensorProduct.congr_tmul, AffineTensorRecovery.gammaTensorEquiv_tmul]
      refine Eq.trans (congrArg (affineSectionsLinearEquiv (tensorMod F G) hV)
        (chartComparisonInv_unit_tmul hV F G _ _)) ?_
      refine Eq.trans (affineSectionsLinearEquiv_eq hV (tensorMod F G) _) ?_
      refine Eq.trans (tensorSheafUnit_val_map (ofScheme F) (ofScheme G)
        (eqToHom (image_top_fromSpec hV).symm).op _ _) ?_
      exact congrArg₂ (fun p q => Hom.app ((PresheafOfModules.sheafificationAdjunction.{u}
          (R := Stacks.RingedSpace.structureRingSheaf (S.toRingedSpace))
          (𝟙 (Stacks.RingedSpace.structureRingSheaf (S.toRingedSpace)).obj)).unit.app
          (PresheafOfModules.tensorObj (O := (S.toRingedSpace).presheaf)
            ((ofScheme F)).val ((ofScheme G)).val)) (op V) (p ⊗ₜ q))
        (((affineSectionsLinearEquiv_eq hV F _).symm).trans
          ((affineSectionsLinearEquiv F hV).apply_symm_apply a))
        (((affineSectionsLinearEquiv_eq hV G _).symm).trans
          ((affineSectionsLinearEquiv G hV).apply_symm_apply b))
  | add x y hx hy =>
      rw [map_add, map_add, chartComparisonInv_add, map_add]
      exact (congrArg₂ (· + ·) hx hy).trans (map_add (gammaTensorMap F G V) x y).symm

/-- **The affine tensor-sections isomorphism, as a bijectivity statement.** For `V` an affine
open of a scheme `S` and `F`, `G` quasi-coherent `𝒪_S`-modules, the canonical map

`Γ(V, F) ⊗_{Γ(S, V)} Γ(V, G) → Γ(V, F ⊗ G)`

is bijective. This is Tag 01I8 over an arbitrary affine open, strengthening the spanning
statement `Stacks.AlgebraicGeometry.AffineTensorGeneral.span_gammaTmul_eq_top` — which is the
surjective half at `V = ⊤` — to a bijection at an arbitrary affine open. -/
theorem bijective_gammaTensorMap (hV : IsAffineOpen V) (F G : S.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] :
    Function.Bijective (gammaTensorMap F G V) := by
  refine ⟨fun a b hab => (gammaTensorInv_bijective hV F G).injective ?_, fun y => ?_⟩
  · rw [gammaTensorInv_eq, gammaTensorInv_eq]
    exact hab
  · obtain ⟨z, hz⟩ := (gammaTensorInv_bijective hV F G).surjective y
    exact ⟨z, (gammaTensorInv_eq hV F G z).symm.trans hz⟩

/-- **The affine tensor-sections isomorphism.** For `V` an affine open of a scheme `S` and `F`,
`G` quasi-coherent `𝒪_S`-modules,

`Γ(V, F) ⊗_{Γ(S, V)} Γ(V, G) ≃ Γ(V, F ⊗ G)`

as `Γ(S, V)`-modules, via the canonical map. This is Tag 01I8 over an arbitrary affine open of
an arbitrary scheme; `AlgebraicGeometry.TildeTensor.gammaTensorEquiv` is the case `V = ⊤` on a
spectrum. -/
def gammaTensorEquiv (hV : IsAffineOpen V) (F G : S.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] :
    (Γ(F, V) ⊗[Γ(S, V)] Γ(G, V)) ≃ₗ[Γ(S, V)] Γ(tensorMod F G, V) :=
  LinearEquiv.ofBijective _ (bijective_gammaTensorMap hV F G)

/-- The isomorphism carries a pure tensor of sections to the pure tensor local section. -/
@[simp] theorem gammaTensorEquiv_tmul (hV : IsAffineOpen V) (F G : S.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] (a : Γ(F, V)) (b : Γ(G, V)) :
    gammaTensorEquiv hV F G (a ⊗ₜ[Γ(S, V)] b) = gammaTmul F G V a b :=
  rfl

/-- **The pure tensors of sections over an affine open span the sections of the tensor
product.** This is the surjective half of `bijective_gammaTensorMap`, in the shape
`Stacks.AlgebraicGeometry.AffineTensorGeneral.span_gammaTmul_eq_top` states it at `⊤`. -/
theorem span_gammaTmul_eq_top (hV : IsAffineOpen V) (F G : S.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] :
    Submodule.span Γ(S, V)
        (Set.range fun p : Γ(F, V) × Γ(G, V) => gammaTmul F G V p.1 p.2) = ⊤ := by
  have key : ∀ z : Γ(F, V) ⊗[Γ(S, V)] Γ(G, V), gammaTensorMap F G V z ∈
      Submodule.span Γ(S, V)
        (Set.range fun p : Γ(F, V) × Γ(G, V) => gammaTmul F G V p.1 p.2) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simpa only [map_zero] using Submodule.zero_mem _
    | tmul a b => exact Submodule.subset_span ⟨(a, b), rfl⟩
    | add z w hz hw => simpa only [map_add] using Submodule.add_mem _ hz hw
  refine le_antisymm le_top fun x _ => ?_
  obtain ⟨z, rfl⟩ := (bijective_gammaTensorMap hV F G).surjective x
  exact key z

/-- **A submodule of the sections of `F ⊗ G` over an affine open containing every pure tensor is
everything.** The pure tensors span, by `span_gammaTmul_eq_top`. -/
theorem eq_top_of_forall_gammaTmul_mem (hV : IsAffineOpen V) (F G : S.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent]
    (I : Submodule Γ(S, V) Γ(tensorMod F G, V))
    (h : ∀ (a : Γ(F, V)) (b : Γ(G, V)), gammaTmul F G V a b ∈ I) :
    I = ⊤ := by
  refine eq_top_iff.2 ?_
  rw [← span_gammaTmul_eq_top hV F G]
  exact Submodule.span_le.2 (by rintro y ⟨p, rfl⟩; exact h p.1 p.2)

/-- **A proper submodule of the sections of `F ⊗ G` over an affine open is escaped by a pure
tensor.** The contrapositive of `eq_top_of_forall_gammaTmul_mem`.

This is the step with which an argument about a point of a relative homogeneous spectrum — a
homogeneous prime of the section ring, whose homogeneous pieces are proper submodules — reduces
to an argument about a pure tensor `a ⊗ b`, and so to the two factors separately. -/
theorem exists_gammaTmul_notMem (hV : IsAffineOpen V) (F G : S.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent]
    (I : Submodule Γ(S, V) Γ(tensorMod F G, V)) (hI : I ≠ ⊤) :
    ∃ (a : Γ(F, V)) (b : Γ(G, V)), gammaTmul F G V a b ∉ I := by
  by_contra hcon
  refine hI (eq_top_of_forall_gammaTmul_mem hV F G I fun a b => ?_)
  by_contra hab
  exact hcon ⟨a, b, hab⟩

end Stacks.AlgebraicGeometry.AffineOpenTensorSections

end
