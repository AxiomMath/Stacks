module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkMate

/-!
# The stalk formula for a pullback, computed on a unital tensor

`Stacks.ModuleSkyscraper.pullbackStalkIso` of Tag 0098,

`𝒪_{X,x} ⊗_{𝒪_{Y,f x}} N_{f x} ≅ (f^*N)_x`,

is produced by conjugating a comparison of skyscraper right adjoints, so no description of it on
an element comes with it. `Stacks.ModuleSkyscraper.pushStalkMap_germ` computes its *mate*, which
is enough for a statement about the counit; what a consumer chasing an element through the
isomorphism itself needs is the value on `1 ⊗ germ_{f x} t`, and that is what this file supplies:
it is the germ at `x` of the section of `f^*N` that the unit of `f^* ⊣ f_*` attaches to `t`.

Those elements generate: `𝒪_{X,x} ⊗_{𝒪_{Y,f x}} N_{f x}` is generated over `𝒪_{X,x}` by the
`1 ⊗ germ_{f x} t`, so the equation determines the isomorphism. Formally no generation argument is
needed — the equation is read off the unit of the composite adjunction, which is where
`CategoryTheory.unit_conjugateEquiv` evaluates the conjugate.

## Main results

* `Stacks.ModuleSkyscraper.conjugateEquiv_pullbackStalkIso_hom`: the conjugate of the stalk
  formula across the two composite adjunctions is `Stacks.ModuleSkyscraper.pushSkyIso`, which is
  how the formula is defined; stated so that `CategoryTheory.unit_conjugateEquiv` can use it.
* `Stacks.ModuleSkyscraper.pullbackStalkIso_hom_app_one_tmul_germ`: **Tag 0098 on a unital
  tensor.** The stalk formula carries `1 ⊗ germ_{f x} t` to the germ at `x` of the section of
  `f^*N` attached to `t` by the unit of `f^* ⊣ f_*`.

## Implementation notes

Both sides of `CategoryTheory.unit_conjugateEquiv` are morphisms of sheaves of modules on `Y`,
and the equation is read at one open `V`, one section `t` and the unique proof that `f x` lies in
`V`; after that evaluation each side is the asserted germ by `rfl`, the reindexing
`x ∈ f⁻¹V ↔ f x ∈ V` and the sections of a skyscraper being reductions. This is the same shape as
the proof of `Stacks.ModuleSkyscraper.pushStalkMap_germ`, and for the same reason: transposing
across the skyscraper adjunction first removes the definitional slack that blocks `rw`.

No tag attribute is placed here. Tag 0098 is the stalk formula, which
`Stacks.ModuleSkyscraper.pullbackStalkIso` carries; this is a computation of it.

## References

* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open scoped ChangeOfRings

universe u

namespace Stacks.ModuleSkyscraper

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)

/-- **The conjugate of the stalk formula is `pushSkyIso`.** `pullbackStalkIso` is *defined* as the
conjugate of `pushSkyIso` across the two composite adjunctions, so applying the conjugation
bijection returns `pushSkyIso`. -/
public theorem conjugateEquiv_pullbackStalkIso_hom :
    conjugateEquiv
        ((Scheme.Modules.pullbackPushforwardAdjunction f).comp (modulesStalkSkyAdjunction X x))
        ((modulesStalkSkyAdjunction Y (f x)).comp
          (ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom))
        (pullbackStalkIso f x).hom =
      (pushSkyIso f x).hom := by
  rw [pullbackStalkIso_hom_eq_conjugateEquiv_symm]
  exact Equiv.apply_symm_apply _ _

/-- **Tag 0098 on a unital tensor.** For a section `t` of `N` over an open `V` containing `f x`,
the stalk formula carries `1 ⊗ germ_{f x} t` to the germ at `x` of the section of `f^*N` over
`f⁻¹V` that the unit of `f^* ⊣ f_*` attaches to `t`.

This is `CategoryTheory.unit_conjugateEquiv` at the conjugation that defines the stalk formula,
evaluated at `V`, at `t` and at the unique proof that `f x` lies in `V`. -/
public theorem pullbackStalkIso_hom_app_one_tmul_germ (N : Y.Modules) (V : Y.Opens)
    (hx : f.base x ∈ V) (t : Γ(N, V)) :
    ((pullbackStalkIso f x).hom.app N).hom
        ((1 : ToType (X.presheaf.stalk x)) ⊗ₜ[ToType (Y.presheaf.stalk (f x)),
          (f.stalkMap x).hom] ((N.presheaf.germ V (f x) hx).hom t)) =
      (((Scheme.Modules.pullback f).obj N).presheaf.germ (f ⁻¹ᵁ V) x hx).hom
        ((((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).val.app (op V)).hom t) := by
  have h := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp (modulesStalkSkyAdjunction X x))
    ((modulesStalkSkyAdjunction Y (f x)).comp
      (ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom))
    (pullbackStalkIso f x).hom N
  rw [conjugateEquiv_pullbackStalkIso_hom] at h
  exact (congrArg (fun u => (u.val.app (op V)).hom t ⟨hx⟩) h).symm

end Stacks.ModuleSkyscraper

end
