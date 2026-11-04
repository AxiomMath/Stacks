module

public import StacksFrontier.Deformation.RingedSpaceThickening.DeformationSolutionIsomorphism
import StacksCore.Tactic.StacksAttribute

/-!
# Isomorphism classes of solutions of (08U7) as a fibre of `Ext¹` groups (Stacks 0GQ3)

This is **Stacks 0GQ3** for the solutions of (08U7) in the form
`AlgebraicGeometry.RingedSpaceThickening.DeformationSolution` of **Stacks 08U7** — first order
thickenings `i : X ⟶ X'` with a morphism of thickenings `(f, f')` to `t : S ⟶ S'`, an
identification `Ker(i^♯) ≅ 𝒢` and the compatibility with the prescribed `c` — up to the
isomorphism `AlgebraicGeometry.RingedSpaceThickening.Isomorphic` of **Stacks 08UC**.

As in the source's proof: by **Stacks 0GPZ** applied to `X ⟶ S'`, classes `ζ` in
`Ext¹_{𝒪_X}(𝖭𝖫_{X/S'}, 𝒢)` parametrize the extensions `0 ⟶ 𝒢 ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` of
`f⁻¹𝒪_{S'}`-algebras (`SquareZeroAlgebraExtension.isomorphismClassesEquivExt`); by
**Stacks 0GQ1** applied to `X ⟶ S ⟶ S'` and `c`, such an extension admits an `S'`-morphism
`X' ⟶ S'` compatible with `c` and `f` exactly when `ζ` maps to the image of `ξ`
(`nonempty_compatibleMorphism_iff_pullbackExtClass_eq`); and this is the same thing as saying that
`𝒪_{X'}` is a solution of (08U7): `firstOrderIdealMap_comp_eq_iff_leftSquare` (the compatibility
equation is the left square of (08U7)), `ExtensionSolution.toDeformationSolution` and
`DeformationSolution.toExtensionSolution` (the two forms of a solution), and
`isomorphic_iff_nonempty_iso` (isomorphism of solutions is isomorphism of the extensions).

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.DeformationSolution.isomorphismClassesEquivExtFibre`:
  **Stacks 0GQ3**, with its value `DeformationSolution.isomorphismClassesEquivExtFibre_mk`.

## References

* [Stacks Project, Tag 0GQ3](https://stacks.math.columbia.edu/tag/0GQ3)
* [Stacks Project, Tag 08U7](https://stacks.math.columbia.edu/tag/08U7)
* [Stacks Project, Tag 0GPZ](https://stacks.math.columbia.edu/tag/0GPZ)
* [Stacks Project, Tag 0GQ1](https://stacks.math.columbia.edu/tag/0GQ1)
* [Stacks Project, Tag 08UC](https://stacks.math.columbia.edu/tag/08UC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X S S' : RingedSpace.{u, u}} {t : S ⟶ S'} (ht : IsFirstOrderThickening t) (f : X ⟶ S)
  (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf))
  (c' : (modulePullback f).obj ((modulePullback t).obj
    (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶
      (show SheafOfModules.{u} (structureSheafRing X) from G))

/-- Isomorphism of solutions of **Stacks 08U7**,
`AlgebraicGeometry.RingedSpaceThickening.Isomorphic`, as a setoid: it is an equivalence relation
because it is isomorphism of the underlying extensions (`isomorphic_iff_nonempty_iso`). -/
def DeformationSolution.isomorphicSetoid : Setoid (DeformationSolution t ht f G c') where
  r := Isomorphic
  iseqv := by
    refine ⟨fun Q => isomorphic_refl Q, fun {Q₁ Q₂} h => ?_, fun {Q₁ Q₂ Q₃} h h' => ?_⟩
    · obtain ⟨ψ⟩ := (isomorphic_iff_nonempty_iso Q₁ Q₂).1 h
      exact (isomorphic_iff_nonempty_iso Q₂ Q₁).2 ⟨ψ.symm⟩
    · obtain ⟨ψ⟩ := (isomorphic_iff_nonempty_iso Q₁ Q₂).1 h
      obtain ⟨ψ'⟩ := (isomorphic_iff_nonempty_iso Q₂ Q₃).1 h'
      exact (isomorphic_iff_nonempty_iso Q₁ Q₃).2 ⟨ψ ≪≫ ψ'⟩

/-- The `f`-map `prescribedFMap c'`, transposed: `f^*𝒥 ≅ f^*t^*Ker(t^♯) ⟶ 𝒢`. -/
theorem homEquiv_symm_prescribedFMap :
    ((modulePullbackPushforwardAdjunction f).homEquiv _ _).symm (prescribedFMap ht f _ c') =
      (modulePullback f).map (baseIdealIsoPullback ht).hom ≫ c' :=
  ((modulePullbackPushforwardAdjunction f).homEquiv_naturality_left_symm _ _).trans
    (congrArg _ (Equiv.symm_apply_apply _ _))

/-- Let `t : (S, 𝒪_S) ⟶ (S', 𝒪_{S'})` be a first order thickening, `𝒥 = Ker(t^♯)`
(`baseIdealModule`), `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)`, `𝒢` an `𝒪_X`-module and `c : 𝒥 ⟶ 𝒢` as in (08U7):
here `c` is given, as in `DeformationSolution`, by `c' : f^*t^*Ker(t^♯) ⟶ 𝒢`, and is
`f^*𝒥 ≅ f^*t^*Ker(t^♯) ⟶ 𝒢` (`baseIdealIsoPullback`). Let `ξ ∈ Ext¹_{𝒪_S}(𝖭𝖫_{S/S'}, 𝒥)` be the
element corresponding to the extension `𝒪_{S'}` of `𝒪_S` by `𝒥` via **Stacks 0GPZ** (`baseClass`).
The set of isomorphism classes of solutions of (08U7) (first order thickenings `X ⟶ X'` with a
morphism of thickenings to `S ⟶ S'`, `Ker ≅ 𝒢` and inducing `c`, up to the isomorphism `Isomorphic`
of **Stacks 08UC**) is canonically bijective to the fibre of

`Ext¹_{𝒪_X}(𝖭𝖫_{X/S'}, 𝒢) ⟶ Ext¹_{𝒪_X}(Lf^*𝖭𝖫_{S/S'}, 𝒢)`

over the image of `ξ`: the map is precomposition with the canonical comparison
`Lf^*𝖭𝖫_{S/S'} ⟶ 𝖭𝖫_{X/S'}` (through the derived pullback `Lf^*` of **Stacks 06YJ**), and the
image of `ξ` is `Lf^*ξ` pushed along `Lf^*𝒥 ⟶ f^*𝒥 ⟶ 𝒢` (`pullbackExtClass`). The bijection sends
a solution `X'` to the class, under **Stacks 0GPZ** for `X ⟶ S'`, of `𝒪_{X'}` read as an extension
of `f⁻¹𝒪_{S'}`-algebras (`DeformationSolution.isomorphismClassesEquivExtFibre_mk`). -/
@[stacks 0GQ3]
def DeformationSolution.isomorphismClassesEquivExtFibre :
    Quotient (DeformationSolution.isomorphicSetoid ht f G c') ≃
      {z : extOneNaiveCotangent (f ≫ t) G //
        restrictDerivedExtClass (derivedPullbackNaiveCotangentMap f t) z =
          pullbackExtClass f t ((modulePullback f).map (baseIdealIsoPullback ht).hom ≫ c')
            (baseClass ht)} :=
  (Quotient.congr (Equiv.refl _) fun Q₁ Q₂ => isomorphic_iff_nonempty_iso Q₁ Q₂).trans
    ((DeformationSolution.classesEquivExtensionClasses t ht f G c').trans
      ((_root_.AlgebraicGeometry.RingedSpaceThickening.isomorphismClassesEquivExtFibre ht f G
        (prescribedFMap ht f _ c')).trans
        (Equiv.subtypeEquivRight fun z => by rw [homEquiv_symm_prescribedFMap])))

/-- **The bijection of Stacks 0GQ3 is canonical**: it sends the class of a solution `X'` to the
image under the bijection of **Stacks 0GPZ** for `X ⟶ S'` of the class of `𝒪_{X'}`, read on `X`
as an extension of `f⁻¹𝒪_{S'}`-algebras. -/
theorem DeformationSolution.isomorphismClassesEquivExtFibre_mk
    (Q : DeformationSolution t ht f G c') :
    (DeformationSolution.isomorphismClassesEquivExtFibre ht f G c' (Quotient.mk _ Q)).1 =
      SquareZeroAlgebraExtension.isomorphismClassesEquivExt (f ≫ t) G
        (Quotient.mk _ (Q.toExtensionSolution).extension) :=
  rfl

end AlgebraicGeometry.RingedSpaceThickening

end
