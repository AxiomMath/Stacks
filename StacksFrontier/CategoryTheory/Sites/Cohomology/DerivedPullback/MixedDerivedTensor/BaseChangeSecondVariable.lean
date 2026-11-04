module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatChangeOfRings

/-!
# Cancellation of a base change is natural in the second tensor factor

Let `f : O₁ ⟶ O₂` be a morphism of sheaves of commutative rings on a site `(C, J)`.  The
sectionwise cancellation of a base change

`(H ⊗_{O₂} (O₂ ⊗_{O₁} G))|_{O₁} ≅ H|_{O₁} ⊗_{O₁} G`

of `Stacks.FlatChangeOfRings.baseChange` is an isomorphism of presheaves of `O₁`-modules which
is natural in `H`, and that is the naturality
`Stacks.FlatChangeOfRings.baseChange_naturality` records.  It is natural in `G` as well, and
this file proves that: on a pure tensor `a ⊗ (s ⊗ x)` both composites return
`(s • a) ⊗ γ(x)`, so the two agree by the same extensionality principle for maps out of a
double tensor product that the naturality in `H` uses.

Naturality in both variables is what makes the cancellation bifunctorial, and bifunctoriality
is what the identity `F ⊗_O f^*G = F ⊗_{f⁻¹O'} f⁻¹G` of Stacks 08I6 asserts.

## Main results

* `Stacks.Cohomology.MixedDerivedTensor.baseChange_naturality_snd`: the cancellation of a base
  change is natural in the second tensor factor, at a fixed first factor.
* `Stacks.Cohomology.MixedDerivedTensor.baseChangeNatIso_naturality_snd`: the same, as the
  naturality in `G` of the isomorphism of functors
  `Stacks.FlatChangeOfRings.baseChangeNatIso`.

## Implementation notes

The proof is the one of `Stacks.FlatChangeOfRings.baseChange_naturality`, with the morphism
moved to the other tensor factor: the two sides are additive maps out of
`H(X) ⊗_{O₂(X)} (O₂(X) ⊗_{O₁(X)} G(X))`, and
`Stacks.FlatChangeOfRings.tensorBaseChange_hom_ext` reduces their equality to the pure tensors.
The scalar towers are reinstated by the same sequence of `let`s, because the sectionwise
statement is about honest modules over honest rings while the ambient statement is about
presheaves of modules; the morphism
`Stacks.PresheafOfModules.ChangeOfRings.changeOfRings f.hom` acts on a pure tensor by
`s ⊗ x ↦ s ⊗ γ(x)`, which is where the two sides meet.

**Universes.**  The site is `C : Type u` with `Category.{v} C` and the structure sheaves and
modules live in universe `w`, as in `Stacks.FlatChangeOfRings`.

**No tag is placed in this file.**  The statement is the naturality of a construction tagged
where it is built; Stacks 05V4 needs only the naturality in the first variable, and Stacks 08I6
asserts an isomorphism in the derived category, which nothing here concludes.

## References

* [The Stacks Project, Tag 05V4](https://stacks.math.columbia.edu/tag/05V4)
* [The Stacks Project, Tag 08I6](https://stacks.math.columbia.edu/tag/08I6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe v u w

namespace Stacks.Cohomology.MixedDerivedTensor

open Stacks Stacks.FlatChangeOfRings

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {O₁ O₂ : Sheaf J CommRingCat.{w}} (f : O₁ ⟶ O₂)

/-- **The cancellation of a base change is natural in the second tensor factor.**  For a
morphism `γ : G ⟶ G'` of presheaves of `O₁`-modules and a presheaf `H` of `O₂`-modules, the
isomorphism `(H ⊗_{O₂} (O₂ ⊗_{O₁} G))|_{O₁} ≅ H|_{O₁} ⊗_{O₁} G` commutes with the maps induced
by `γ` on the two sides. -/
lemma baseChange_naturality_snd {G G' : PresheafOfModules.{w} (ringPresheaf O₁.obj)}
    (γ : G ⟶ G') (H : PresheafOfModules.{w} (ringPresheaf O₂.obj)) :
    (PresheafOfModules.restrictScalars (ringPresheafMap f)).map
        (tensorMapRight H
          ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings f.hom).map γ)) ≫
      (baseChange f G' H).hom =
    (baseChange f G H).hom ≫ tensorMapRight
      ((PresheafOfModules.restrictScalars (ringPresheafMap f)).obj H) γ := by
  apply PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  let _ : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := (f.hom.app X).hom.toAlgebra
  let _ : Module (O₂.obj.obj X) (H.obj X) := (H.obj X).isModule
  let _ : Module (O₁.obj.obj X) (G.obj X) := (G.obj X).isModule
  let _ : Module (O₁.obj.obj X) (G'.obj X) := (G'.obj X).isModule
  let _ : Module (O₁.obj.obj X) (H.obj X) := Module.compHom _ (f.hom.app X).hom
  let _ : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (H.obj X) :=
    IsScalarTower.of_algebraMap_smul (by intro r x; rfl)
  let L : (H.obj X ⊗[O₂.obj.obj X] (O₂.obj.obj X ⊗[O₁.obj.obj X] G.obj X)) →+
      (H.obj X ⊗[O₁.obj.obj X] G'.obj X) :=
    (((PresheafOfModules.restrictScalars (ringPresheafMap f)).map
        (tensorMapRight H
          ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings f.hom).map γ)) ≫
      (baseChange f G' H).hom).app X).hom.toAddMonoidHom
  let R : (H.obj X ⊗[O₂.obj.obj X] (O₂.obj.obj X ⊗[O₁.obj.obj X] G.obj X)) →+
      (H.obj X ⊗[O₁.obj.obj X] G'.obj X) :=
    (((baseChange f G H).hom ≫ tensorMapRight
        ((PresheafOfModules.restrictScalars (ringPresheafMap f)).obj H)
          γ).app X).hom.toAddMonoidHom
  refine tensorBaseChange_hom_ext L R ?_
  intro a s x
  show tensorBaseChange
      (a ⊗ₜ[O₂.obj.obj X] (s ⊗ₜ[O₁.obj.obj X] (show G'.obj X from (γ.app X).hom x))) =
    (show H.obj X from s • a) ⊗ₜ[O₁.obj.obj X] (show G'.obj X from (γ.app X).hom x)
  rw [tensorBaseChange_tmul]

/-- **`Stacks.FlatChangeOfRings.baseChangeNatIso` is natural in `G`.**  Together with its own
naturality in `H`, which is how it is built, this makes the cancellation of a base change
bifunctorial. -/
lemma baseChangeNatIso_naturality_snd {G G' : PresheafOfModules.{w} (ringPresheaf O₁.obj)}
    (γ : G ⟶ G') :
    Functor.whiskerRight
          (tensorRightNatTrans
            ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings f.hom).map γ))
          (PresheafOfModules.restrictScalars (ringPresheafMap f)) ≫
        (baseChangeNatIso f G').hom
      = (baseChangeNatIso f G).hom ≫
          Functor.whiskerLeft (PresheafOfModules.restrictScalars (ringPresheafMap f))
            (tensorRightNatTrans γ) :=
  NatTrans.ext (funext (baseChange_naturality_snd f γ))

end Stacks.Cohomology.MixedDerivedTensor

end
