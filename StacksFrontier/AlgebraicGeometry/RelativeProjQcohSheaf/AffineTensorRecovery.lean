module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineHomRecovery
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCoherence
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.TildeTensorSections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Global sections of a tensor product, at the spelling a twisting is stated in

A twisting of a quadruple of Section 01NS is a homomorphism of sheaves of graded algebras, and
its multiplicativity is an equality of morphisms out of a tensor product of two pieces of the
graded algebra, pulled back along the structure morphism of the test scheme. Reducing such an
equality to a computation on global sections over an affine base needs two facts about the
tensor product of Tag 01CA at the spelling
`Stacks.SheafOfModules.Strict.monoidalCategory`, in which the tensor product is the tensor
product sheaf on the nose:

* the tensor product of two quasi-coherent modules is quasi-coherent (Tag 01CE), so that the
  mapping property of a quasi-coherent module over an affine base applies to it;
* over an affine base the global sections of the tensor product are the tensor product of the
  global sections (Tag 01I8), so that a linear map out of them is determined by its values on
  pure tensors.

Both are already proved in this repository, the first for a ringed space and the second on
`Spec R`, but at the `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf` spelling of the
tensor product. This file restates them with the monoidal `⊗`, which is the same object on the
nose, and records the consequence for a morphism out of a pullback.

## Main results

* `Stacks.AlgebraicGeometry.AffineTensorRecovery.isQuasicoherent_tensorObj`: **Tag 01CE at the
  monoidal spelling** — `A ⊗ B` is quasi-coherent when `A` and `B` are.
* `Stacks.AlgebraicGeometry.AffineTensorRecovery.gammaTensorEquiv`: **Tag 01I8 on global
  sections at the monoidal spelling** — `Γ(F) ⊗_R Γ(G) ≃ Γ(F ⊗ G)` on `Spec R`.
* `Stacks.AlgebraicGeometry.AffineTensorRecovery.span_gammaTmul_eq_top` and
  `Stacks.AlgebraicGeometry.AffineTensorRecovery.span_gammaTmul_eq_top'`: the pure tensors span
  the global sections of `F ⊗ G` on `Spec R`, over `R` and over `Γ(Spec R, 𝒪)`.
* `Stacks.AlgebraicGeometry.AffineTensorRecovery.pullback_hom_ext`: **two morphisms out of
  `g^*(F ⊗ G)` that agree on the pure tensors of global sections are equal**, for `g` a morphism
  of schemes with target `Spec R` and `F`, `G` quasi-coherent. Nothing is asked of the target.

## Implementation notes

The monoidal structure in play is the one a twisting is stated with,
`Stacks.PullbackGradedAlgebra.monoidalCategory`, whose tensor product on objects is
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf` by definition and hence Tag 01CB's
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf` by `rfl`
(`Stacks.TensorSheafSpellingIso.tensorSheaf_eq`). No comparison isomorphism is therefore
inserted anywhere below: each statement is its counterpart retyped, and the crossing happens at
the `:=`.

## References

* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry MonoidalCategory
open scoped AlgebraicGeometry TensorProduct

universe u

namespace Stacks.AlgebraicGeometry.AffineTensorRecovery

open Stacks.RingedSpace (structureRingSheaf pullbackFunctor pushforwardFunctor pullbackAdjunction)

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

attribute [local instance] Stacks.Algebraization.sectionsModuleΓ
  Stacks.Algebraization.sectionsModuleΓSheaf Stacks.Algebraization.sectionsSMulCommClassΓ
  Stacks.Algebraization.sectionsModuleΓPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafVal

/-- **Stacks Project, Tag 01CE, at the monoidal spelling.** The tensor product of two
quasi-coherent sheaves of modules on a ringed space is quasi-coherent, for the monoidal product
of Tag 01CA whose tensor product is the tensor product sheaf on the nose. -/
instance isQuasicoherent_tensorObj (X : RingedSpace.{u, u})
    (A B : SheafOfModules.{u} (structureRingSheaf X))
    [A.IsQuasicoherent] [B.IsQuasicoherent] :
    (A ⊗ B).IsQuasicoherent :=
  @AlgebraicGeometry.tensorSheaf_isQuasicoherent X A B ‹_› ‹_›

variable {R : CommRingCat.{u}}

/-- A sheaf of modules on `Spec R`, retyped over the `Stacks.RingedSpace.structureRingSheaf`
spelling of the structure sheaf of rings, which is the spelling the monoidal product of Tag 01CA
is indexed by. The crossing of the `rfl`-equality of the two spellings is done here, once. -/
abbrev ofSpec (F : (Spec R).Modules) :
    SheafOfModules.{u} (structureRingSheaf (Spec R).toRingedSpace) := F

/-- The monoidal product of two sheaves of modules on `Spec R`. -/
abbrev tensorSheafMod (F G : (Spec R).Modules) :
    SheafOfModules.{u} (structureRingSheaf (Spec R).toRingedSpace) := ofSpec F ⊗ ofSpec G

/-- The monoidal product of two sheaves of modules on `Spec R`, retyped as an object of
`(Spec R).Modules`. -/
abbrev tensorMod (F G : (Spec R).Modules) : (Spec R).Modules := tensorSheafMod F G

/-- The global section of `F ⊗ G` attached to a pair of global sections of `F` and `G`: the
image of the pure tensor under the unit of the sheafification that forms the tensor product. -/
@[sga "3 VIIA 3.1.2" "special case"]
def gammaTmul (F G : (Spec R).Modules) (s : Γ(F, ⊤)) (t : Γ(G, ⊤)) :
    Γ(tensorMod F G, ⊤) :=
  AlgebraicGeometry.TildeTensor.gammaTmulG F G s t

/-- **Stacks Project, Tag 01I8 on global sections, at the monoidal spelling.** For
quasi-coherent `F` and `G` on `Spec R` the canonical map
`Γ(Spec R, F) ⊗_R Γ(Spec R, G) ⟶ Γ(Spec R, F ⊗ G)` is an isomorphism of `R`-modules. -/
def gammaTensorEquiv (F G : (Spec R).Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] :
    (Γ(F, ⊤) ⊗[R] Γ(G, ⊤)) ≃ₗ[R] Γ(tensorMod F G, ⊤) :=
  AlgebraicGeometry.TildeTensor.gammaTensorEquiv F G

/-- `gammaTensorEquiv` sends a pure tensor `s ⊗ₜ t` to `gammaTmul F G s t`. -/
@[simp] lemma gammaTensorEquiv_tmul (F G : (Spec R).Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] (s : Γ(F, ⊤)) (t : Γ(G, ⊤)) :
    gammaTensorEquiv F G (s ⊗ₜ[R] t) = gammaTmul F G s t :=
  rfl

/-- **The pure tensors of global sections span the global sections of `F ⊗ G`** over `Spec R`,
for `F` and `G` quasi-coherent: the canonical map of Tag 01I8 is surjective and a tensor product
is spanned by its pure tensors. -/
theorem span_gammaTmul_eq_top (F G : (Spec R).Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] :
    Submodule.span R
        (Set.range fun p : Γ(F, ⊤) × Γ(G, ⊤) => gammaTmul F G p.1 p.2) = ⊤ := by
  have key : ∀ y : Γ(F, ⊤) ⊗[R] Γ(G, ⊤), gammaTensorEquiv F G y ∈
      Submodule.span R (Set.range fun p : Γ(F, ⊤) × Γ(G, ⊤) => gammaTmul F G p.1 p.2) := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul s t => exact Submodule.subset_span ⟨(s, t), rfl⟩
    | add a b ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
  refine le_antisymm le_top fun x _ => ?_
  obtain ⟨y, rfl⟩ := (gammaTensorEquiv F G).surjective x
  exact key y

/-- Tag 01CE for the monoidal product of two quasi-coherent modules on `Spec R`, at the
`AlgebraicGeometry.Scheme.Modules` spelling of the category, which is the spelling the mapping
property of a quasi-coherent module over an affine base is stated in. -/
instance isQuasicoherent_tensorMod (F G : (Spec R).Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] : (tensorMod F G).IsQuasicoherent :=
  @isQuasicoherent_tensorObj (Spec R).toRingedSpace (ofSpec F) (ofSpec G) ‹_› ‹_›

/-- **The pure tensors of global sections span the global sections of `F ⊗ G` over the ring of
functions**, for `F` and `G` quasi-coherent on `Spec R`. This is `span_gammaTmul_eq_top` with the
scalars enlarged from `R` to `Γ(Spec R, 𝒪)`, which act through `R → Γ(Spec R, 𝒪)`; it is the form
a `Γ(Spec R, 𝒪)`-linear map out of the global sections is tested against. -/
theorem span_gammaTmul_eq_top' (F G : (Spec R).Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] :
    Submodule.span Γ(Spec R, ⊤)
        (Set.range fun p : Γ(F, ⊤) × Γ(G, ⊤) => gammaTmul F G p.1 p.2) = ⊤ := by
  have key : ∀ x : Γ(tensorMod F G, ⊤),
      x ∈ Submodule.span R (Set.range fun p : Γ(F, ⊤) × Γ(G, ⊤) => gammaTmul F G p.1 p.2) →
      x ∈ Submodule.span Γ(Spec R, ⊤)
        (Set.range fun p : Γ(F, ⊤) × Γ(G, ⊤) => gammaTmul F G p.1 p.2) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact Submodule.zero_mem _
    | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
    | smul r a _ ha =>
        rw [Scheme.Modules.smul_Spec_def]
        exact Submodule.smul_mem _ _ ha
  refine le_antisymm le_top fun x _ => key x ?_
  rw [span_gammaTmul_eq_top F G]
  exact Submodule.mem_top

/-- **Two morphisms out of the pullback of a tensor product of quasi-coherent modules on
`Spec R` that agree on the pure tensors of global sections are equal.**

Let `g : T ⟶ Spec R` be a morphism of schemes, `F` and `G` quasi-coherent `𝒪_{Spec R}`-modules
and `N` an arbitrary `𝒪_T`-module. A morphism `g^*(F ⊗ G) ⟶ N` is determined by the global
sections it assigns to the pure tensors `s ⊗ t` of global sections of `F` and `G`: the mapping
property of a quasi-coherent module over an affine base reduces the equality to an equality of
linear maps on `Γ(Spec R, F ⊗ G)`, which Tag 01I8 exhibits as spanned by those pure tensors.

Nothing is asked of `N`, so no quasi-compactness or quasi-separatedness of `g` enters. -/
theorem pullback_hom_ext {T : Scheme.{u}} (g : T ⟶ Spec R)
    (F G : (Spec R).Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    (N : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    {h h' : (pullbackFunctor g.toLRSHom.toShHom).obj (tensorMod F G) ⟶ N}
    (hyp : ∀ (s : Γ(F, ⊤)) (t : Γ(G, ⊤)),
      AffineHomRecovery.sectionsMap g (tensorMod F G) N h (gammaTmul F G s t) =
        AffineHomRecovery.sectionsMap g (tensorMod F G) N h' (gammaTmul F G s t)) :
    h = h' := by
  refine AffineHomRecovery.hom_ext g (tensorMod F G) N ?_
  have heq : AffineHomRecovery.sectionsMap g (tensorMod F G) N h =
      AffineHomRecovery.sectionsMap g (tensorMod F G) N h' :=
    LinearMap.ext_on (span_gammaTmul_eq_top' F G) (by rintro y ⟨p, rfl⟩; exact hyp p.1 p.2)
  exact fun x => DFunLike.congr_fun heq x

end Stacks.AlgebraicGeometry.AffineTensorRecovery

end
