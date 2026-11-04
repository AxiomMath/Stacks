module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.ExternalTensor.Duality
public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Modules.UnitStalk
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleKGroup

/-!
# Morphisms out of a finite locally free module as global sections of a tensor product

Let `W` be a scheme, let `P` be a finite locally free `𝒪_W`-module and let `ℱ` be an arbitrary
`𝒪_W`-module.  Then

`Hom_{𝒪_W}(P, ℱ) ≃ Γ(W, ℱ ⊗ P^∨)`,

the right-hand side being the morphisms out of the structure sheaf.  This is the hom-set form of
the left-duality of `P`: it is `CategoryTheory.tensorRightHomEquiv` for the exact pairing between
`P` and `P^∨`, read at the unit object.

The use this is written for is the nonvanishing half of step 1 of the proof of
[Stacks, Tag 0G0E].  There a nonzero morphism `ℰ ⊠ 𝒢 ⟶ H^i(K)` out of an external tensor product
of finite locally free modules has to be turned into a nonzero global section of
`H^i(K) ⊗ (ℰ^∨ ⊠ 𝒢^∨)`, which is the degree-`i` cohomology sheaf of `K ⊗^𝐋 (ℰ^∨ ⊠ 𝒢^∨)[0]`, the
object the source's display computes.  So the external tensor product case is stated too,
with the dual of the box replaced by the box of the duals.

## Main definitions

* `AlgebraicGeometry.dualTensorHomEquiv` — `Hom(P, ℱ) ≃ Γ(W, ℱ ⊗ P^∨)` for finite locally free
  `P`.
* `AlgebraicGeometry.externalTensorDualTensorHomEquiv` —
  `Hom(ℰ ⊠ 𝒢, ℱ) ≃ Γ(X ×_S Y, ℱ ⊗ (ℰ^∨ ⊠ 𝒢^∨))` for finite locally free `ℰ` and `𝒢`.

## Main results

* `AlgebraicGeometry.eq_zero_of_forall_hom_unit_tensor_dual_eq_zero` and
  `AlgebraicGeometry.eq_zero_of_forall_hom_unit_tensor_externalTensorProduct_dual_eq_zero` — the
  two bijections read as vanishing statements: if the tensor product has no nonzero global
  section then there is no nonzero morphism out of `P`, resp. out of `ℰ ⊠ 𝒢`.

## Implementation notes

*Why the vanishing corollaries are stated separately.*  The bijections are bijections of hom-sets,
not of additive groups: `CategoryTheory.tensorRightHomEquiv` is an `Equiv`, and Mathlib records no
additivity for it.  A vanishing hypothesis is therefore not transported by applying the bijection
to `0`; it is transported by applying it to the morphism in question *and* to `0`, both images
being zero by hypothesis, and then using injectivity.  That is what the corollaries do, and it is
the only form in which they are used.

*The monoidal structure.*  `AlgebraicGeometry.onSpaceModulesMonoidal` is activated as a local
instance, as in `StacksFrontier/AlgebraicGeometry/DerivedVarieties/ExternalTensor/Duality.lean`: its
tensor product on objects is the tensor product sheaf of [Stacks, Tag 01CB] and its unit is the
structure sheaf, both by `rfl`, so the statements below are given in the instance-free spellings
`AlgebraicGeometry.Scheme.Modules.tensorObjRingedSpace` and `Stacks.UnitStalk.unitModule` while
the proofs are written with the monoidal notation.  Those two are used rather than
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf` and `SheafOfModules.unit` for the
reason `Stacks.UnitStalk.unitModule`'s own docstring records: `AlgebraicGeometry.Scheme.Modules`
is a `def`, so instance search re-infers the ambient category from the *term*, and the zero
morphism of a hom-group written at the `SheafOfModules` spelling is not found.

*The two spellings of finite local freeness.*  The hypotheses are taken at
`Stacks.FiniteLocallyFree.IsFiniteLocallyFree`, which is what
`AlgebraicGeometry.VectorBundleKZero.dualSheafExactPairing` and
`AlgebraicGeometry.externalTensorProductDualIso` consume, and converted to
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree` by
`Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry` where
`Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFree_dualSheaf` of [Stacks, Tag 0FA7]
needs it.

## References

* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
* [Stacks Project, Tag 0FA7](https://stacks.math.columbia.edu/tag/0FA7)
* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
* [Stacks Project, Tag 0G0E](https://stacks.math.columbia.edu/tag/0G0E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open Stacks.FiniteLocallyFree Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace AlgebraicGeometry

open Stacks.AlgebraicGeometry.ReflexiveModules AlgebraicGeometry.VectorBundleKZero

attribute [local instance] onSpaceModulesMonoidal

/-- An equivalence out of a type `α` into a type all of whose elements are zero forces `α`'s
elements to be zero. -/
private theorem eq_zero_of_equiv_of_forall_eq_zero {α β : Type*} [Zero α] [Zero β] (e : α ≃ β)
    (h : ∀ s : β, s = 0) (q : α) : q = 0 :=
  e.injective ((h _).trans (h (e 0)).symm)

/-- **`Hom(P, ℱ) ≃ Γ(W, ℱ ⊗ P^∨)` for a finite locally free `P`.**  The left-duality of `P`,
read on hom-sets out of the unit object: `Hom(𝒪_W ⊗ P, ℱ) ≃ Hom(𝒪_W, ℱ ⊗ P^∨)` is
`CategoryTheory.tensorRightHomEquiv` for the pairing
`AlgebraicGeometry.VectorBundleKZero.dualSheafExactPairing`, and the left unitor identifies
`𝒪_W ⊗ P` with `P`. -/
def dualTensorHomEquiv (W : Scheme.{u}) (P F : W.Modules)
    (hP : IsFiniteLocallyFree.{u, u, u} (R := W.ringCatSheaf) P) :
    (P ⟶ F) ≃ (Stacks.UnitStalk.unitModule W ⟶
      Scheme.Modules.tensorObjRingedSpace W F (dualSheaf P)) :=
  (Iso.homFromEquiv (λ_ P)).symm.trans
    (@tensorRightHomEquiv W.Modules _ (onSpaceModulesMonoidal W) (𝟙_ W.Modules) P (dualSheaf P) F
      (dualSheafExactPairing W P hP))

/-- **A module with no nonzero morphism out of `P` after dualising receives none from `P`.**  If
`ℱ ⊗ P^∨` has no nonzero global section, then there is no nonzero morphism `P ⟶ ℱ`.

This is `AlgebraicGeometry.dualTensorHomEquiv` read through its injectivity: the images of the
given morphism and of `0` are both zero by hypothesis, hence equal. -/
theorem eq_zero_of_forall_hom_unit_tensor_dual_eq_zero (W : Scheme.{u}) (P F : W.Modules)
    (hP : IsFiniteLocallyFree.{u, u, u} (R := W.ringCatSheaf) P)
    (hvan : ∀ s : Stacks.UnitStalk.unitModule W ⟶
      Scheme.Modules.tensorObjRingedSpace W F (dualSheaf P), s = 0)
    (q : P ⟶ F) : q = 0 :=
  eq_zero_of_equiv_of_forall_eq_zero (dualTensorHomEquiv W P F hP) hvan q

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- **`Hom(ℰ ⊠ 𝒢, ℱ) ≃ Γ(X ×_S Y, ℱ ⊗ (ℰ^∨ ⊠ 𝒢^∨))`** for finite locally free `ℰ` and `𝒢`.

It is `AlgebraicGeometry.dualTensorHomEquiv` at `P = ℰ ⊠ 𝒢`, which is finite locally free by
`AlgebraicGeometry.isFiniteLocallyFree_externalTensorProduct`, followed by the identification
`(ℰ ⊠ 𝒢)^∨ ≅ ℰ^∨ ⊠ 𝒢^∨` of `AlgebraicGeometry.externalTensorProductDualIso`. -/
def externalTensorDualTensorHomEquiv (E : X.Modules) (G : Y.Modules)
    (F : (Limits.pullback f g).Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (hG : IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) G) :
    (externalTensorProduct f g E G ⟶ F) ≃
      (Stacks.UnitStalk.unitModule (Limits.pullback f g) ⟶
        Scheme.Modules.tensorObjRingedSpace (Limits.pullback f g) F
          (externalTensorProduct f g (dualSheaf E) (dualSheaf G))) :=
  (dualTensorHomEquiv (Limits.pullback f g) (externalTensorProduct f g E G) F
      (isFiniteLocallyFree_externalTensorProduct f g E G hE hG)).trans
    (Iso.homToEquiv
      ((MonoidalCategory.whiskerLeftIso F (externalTensorProductDualIso f g E G hE hG))))

/-- **A module with no nonzero morphism out of `ℰ ⊠ 𝒢` after dualising receives none from
`ℰ ⊠ 𝒢`.**  If `ℱ ⊗ (ℰ^∨ ⊠ 𝒢^∨)` has no nonzero global section, then there is no nonzero
morphism `ℰ ⊠ 𝒢 ⟶ ℱ`.

This is the hypothesis `hF` of
`AlgebraicGeometry.isZero_of_forall_externalTensorProduct_hom_eq_zero`, [Stacks, Tag 0FZ0] read
contrapositively, reduced to a statement about global sections -- which is what the display of
[Stacks, Tag 0G0E] computes.  The duals `ℰ^∨` and `𝒢^∨` are again finite locally free by
[Stacks, Tag 0FA7], so the quantification over all finite locally free `ℰ`, `𝒢` is not
narrowed by passing to them. -/
theorem eq_zero_of_forall_hom_unit_tensor_externalTensorProduct_dual_eq_zero
    (E : X.Modules) (G : Y.Modules) (F : (Limits.pullback f g).Modules)
    (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (hG : IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) G)
    (hvan : ∀ s : Stacks.UnitStalk.unitModule (Limits.pullback f g) ⟶
      Scheme.Modules.tensorObjRingedSpace (Limits.pullback f g) F
        (externalTensorProduct f g (dualSheaf E) (dualSheaf G)), s = 0)
    (q : externalTensorProduct f g E G ⟶ F) : q = 0 :=
  eq_zero_of_equiv_of_forall_eq_zero (externalTensorDualTensorHomEquiv f g E G F hE hG) hvan q

/-- **The dual of a finite locally free module is finite locally free**, at the spelling of
finite local freeness that `AlgebraicGeometry.externalTensorProductDualIso` and the display of
[Stacks, Tag 0G0E] consume.  This is [Stacks, Tag 0FA7],
`Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFree_dualSheaf`, read through
`Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry`.

It is what makes the passage to duals in
`AlgebraicGeometry.eq_zero_of_forall_hom_unit_tensor_externalTensorProduct_dual_eq_zero`
harmless: the box of the two duals is again a box of two finite locally free modules, so the
display of [Stacks, Tag 0G0E] applies to it. -/
theorem isFiniteLocallyFree_dualSheaf' {W : Scheme.{u}} (P : W.Modules)
    (hP : IsFiniteLocallyFree.{u, u, u} (R := W.ringCatSheaf) P) :
    IsFiniteLocallyFree.{u, u, u} (R := W.ringCatSheaf) (dualSheaf P) :=
  (isFiniteLocallyFree_iff_algebraicGeometry (dualSheaf P)).2
    (Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFree_dualSheaf P
      ((isFiniteLocallyFree_iff_algebraicGeometry P).1 hP))

end AlgebraicGeometry

end
