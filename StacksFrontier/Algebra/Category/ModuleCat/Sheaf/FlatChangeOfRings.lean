module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafFlatCover
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ChangeOfRingsAdjunction
import StacksCore.Tactic.StacksAttribute

/-!
# Flatness under change of rings

Let `f : O₁ ⟶ O₂` be a morphism of sheaves of commutative rings on a site `(C, J)` and let
`G` be a sheaf of `O₁`-modules.  Stacks 05V4 asserts that if `G` is flat then the sheaf of
`O₂`-modules `G ⊗_{O₁} O₂` obtained by extension of scalars is flat.

The proof is the one in the source.  Flatness of a sheaf of modules is exactness of the
endofunctor `- ⊗ G` (Stacks 03ER, `Stacks.SheafOfModules.IsFlat`), and the identity
`H ⊗_{O₂} (O₂ ⊗_{O₁} G) = H ⊗_{O₁} G` "as sheaves of abelian groups" of the source is
realised here as the natural isomorphism `Stacks.FlatChangeOfRings.baseChangeNatIso`,
sectionwise `TensorProduct.AlgebraTensorModule.cancelBaseChange`.  Right exactness of a
tensor functor `(Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj G` is automatic
(`Stacks.preservesFiniteColimits_sheafTensorRight`), so only left
exactness has to be transported, and it is transported along the forgetful functor to sheaves
of abelian groups, which preserves and reflects finite limits.

## Main definitions

* `Stacks.FlatChangeOfRings.ringSheafMap`, `ringPresheafMap`: the morphism of sheaves,
  respectively presheaves, of rings underlying `f`.
* `Stacks.FlatChangeOfRings.presheafExtendScalars`: the sectionwise tensor product
  `H ↦ (X ↦ O₂(X) ⊗_{O₁(X)} H(X))` of Stacks 03CU, retyped at the spelling used here.
* `Stacks.FlatChangeOfRings.extendScalars`: extension of scalars for sheaves of modules
  along `f`, namely the sectionwise tensor product followed by sheafification.
* `Stacks.FlatChangeOfRings.tensorBaseChange`: the sectionwise interchange
  `H ⊗_S (S ⊗_R G) ≃ₗ[S] H ⊗_R G`.
* `Stacks.FlatChangeOfRings.baseChangeApp`, `baseChange`, `baseChangeNatIso`: that
  interchange as an isomorphism of presheaves of `O₁`-modules, natural in `H`.

## Main results

* `Stacks.FlatChangeOfRings.tensorBaseChange_hom_ext`: two additive maps out of
  `H ⊗_S (S ⊗_R G)` agreeing on the pure tensors `a ⊗ (s ⊗ x)` are equal.  This is the form
  in which the double tensor product is used; stating it once avoids an induction at a
  spelling of the tensor product that is definitionally but not syntactically the one the
  change-of-rings functor produces.
* `Stacks.FlatChangeOfRings.extendScalarsAdjunction`: extension of scalars along `f` is left
  adjoint to restriction of scalars, so the functor defined here is the expected one.
* `Stacks.FlatChangeOfRings.isFlat_extendScalars`: **Stacks 05V4.**

## Implementation notes

**Universes.**  The site is `C : Type u` with `Category.{v} C`, and the structure sheaves and
the modules both live in universe `w`.  The module universe is *not* independent of the ring
universe here, and that is forced by the input rather than chosen: the transport used for
`tensorRightExtendScalarsIso` is `Stacks.isIso_sheafification_map_tensorMapRight`, whose
module universe is pinned to the ring universe because `Stacks.BilinearMap` — the extension
theorem for bilinear maps along a local bijection that it rests on — is stated with a single
universe for both.  Every other statement about flatness of sheaves of modules on this branch
(`Stacks.isFlat_flatCover`, `Stacks.sheafTensorRight_shortExact_of_flat`, and both directions
of Stacks 08FC) lives at the same single universe, so this is the generality in which the
result is consumed.  Extension of scalars itself has no such constraint: for a module
universe `t` the sectionwise tensor product `O₂(X) ⊗_{O₁(X)} H(X)` lands in `max w t`, so the
statement is universe-uniform exactly when `w ≤ t`.

**Spellings.**  Three definitionally equal presheaves of rings occur in this area: the
`ringPresheaf O.obj` of `Stacks`, the `Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf O.obj`
of Stacks 03CU (the same abbreviation) and `(Stacks.SheafOfModules.Tensor.ringSheaf O).obj`, the
presheaf of rings of the canonical ring sheaf, which is the first one only after unfolding that
definition.  The presheaf-level material below is written entirely at the `ringPresheaf`
spelling, which is the one `Stacks.tensorObj` and
`Stacks.PresheafOfModules.ChangeOfRings.changeOfRings` use; the crossing to the
`Stacks.SheafOfModules.Tensor.ringSheaf` spelling happens once, in `presheafExtendScalars` and
in `baseChangeNatIsoOf`, each a definition whose declared result type pins the target spelling.
Writing the presheaf-level lemmas across the two spellings instead makes the naturality proofs
fail with "the target expression is not type-correct under the `implicit` transparency level".

## References

* [Stacks Project, Tag 05V4](https://stacks.math.columbia.edu/tag/05V4)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe v u w

namespace Stacks.FlatChangeOfRings

open Stacks

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {O₁ O₂ : Sheaf J CommRingCat.{w}} (f : O₁ ⟶ O₂)

/-- The morphism of sheaves of rings underlying a morphism of sheaves of commutative
rings. -/
noncomputable abbrev ringSheafMap :
    Stacks.SheafOfModules.Tensor.ringSheaf O₁ ⟶ Stacks.SheafOfModules.Tensor.ringSheaf O₂ :=
  (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map f

/-- The morphism of presheaves of rings underlying a morphism of sheaves of commutative
rings, at the `Stacks.ringPresheaf` spelling. -/
noncomputable def ringPresheafMap : ringPresheaf O₁.obj ⟶ ringPresheaf O₂.obj :=
  (ringSheafMap f).hom

/-! ## The sectionwise interchange -/

section Algebraic

variable {R S : Type w} [CommRing R] [CommRing S] [Algebra R S]
  {G H : Type w} [AddCommGroup G] [Module R G] [AddCommGroup H] [Module S H]

/-- The sectionwise interchange `H ⊗_S (S ⊗_R G) ≃ H ⊗_R G` underlying change of rings for
tensor products. -/
noncomputable def tensorBaseChange [Module R H] [IsScalarTower R S H] :
    H ⊗[S] (S ⊗[R] G) ≃ₗ[S] H ⊗[R] G :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange R S S H G

/-- The interchange `tensorBaseChange` sends `a ⊗ (s ⊗ x)` to `(s • a) ⊗ x`. -/
@[simp]
lemma tensorBaseChange_tmul [Module R H] [IsScalarTower R S H] (a : H) (s : S) (x : G) :
    tensorBaseChange (a ⊗ₜ[S] (s ⊗ₜ[R] x)) = (s • a) ⊗ₜ[R] x :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul R S S a x s

/-- Two additive maps out of `H ⊗_S (S ⊗_R G)` which agree on the pure tensors
`a ⊗ (s ⊗ x)` are equal. -/
lemma tensorBaseChange_hom_ext {P : Type w} [AddCommGroup P]
    (φ ψ : (H ⊗[S] (S ⊗[R] G)) →+ P)
    (hpure : ∀ (a : H) (s : S) (x : G),
      φ (a ⊗ₜ[S] (s ⊗ₜ[R] x)) = ψ (a ⊗ₜ[S] (s ⊗ₜ[R] x))) (t : H ⊗[S] (S ⊗[R] G)) :
    φ t = ψ t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb
  | tmul a q =>
    induction q using TensorProduct.induction_on with
    | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero]
    | add c d hc hd =>
      rw [TensorProduct.tmul_add, map_add, map_add]
      exact congrArg₂ (· + ·) hc hd
    | tmul s x => exact hpure a s x

end Algebraic

/-! ## Base change for presheaves of modules -/

section Presheaf

variable (G : PresheafOfModules.{w} (ringPresheaf O₁.obj))

/-- The component at `X` of the base-change isomorphism. -/
noncomputable def baseChangeApp
    (H : PresheafOfModules.{w} (ringPresheaf O₂.obj)) (X : Cᵒᵖ) :
    ((PresheafOfModules.restrictScalars (ringPresheafMap f)).obj
        (tensorObj H ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings f.hom).obj G))).obj X ≅
      (tensorObj ((PresheafOfModules.restrictScalars (ringPresheafMap f)).obj H) G).obj X := by
  letI : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := (f.hom.app X).hom.toAlgebra
  letI : Module (O₂.obj.obj X) (H.obj X) := (H.obj X).isModule
  letI : Module (O₁.obj.obj X) (G.obj X) := (G.obj X).isModule
  letI : Module (O₁.obj.obj X) (H.obj X) := Module.compHom _ (f.hom.app X).hom
  letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (H.obj X) :=
    IsScalarTower.of_algebraMap_smul (by intro r x; rfl)
  exact LinearEquiv.toModuleIso
    ((tensorBaseChange (R := O₁.obj.obj X) (S := O₂.obj.obj X)
      (G := G.obj X) (H := H.obj X)).restrictScalars (O₁.obj.obj X))

/-- **Base change for presheaves of modules**:
`(H ⊗_{O₂} (O₂ ⊗_{O₁} G))_{O₁} ≅ H_{O₁} ⊗_{O₁} G`. -/
noncomputable def baseChange (H : PresheafOfModules.{w} (ringPresheaf O₂.obj)) :
    (PresheafOfModules.restrictScalars (ringPresheafMap f)).obj
        (tensorObj H ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings f.hom).obj G)) ≅
      tensorObj ((PresheafOfModules.restrictScalars (ringPresheafMap f)).obj H) G := by
  refine PresheafOfModules.isoMk (baseChangeApp f G H) ?_
  intro X Y g
  let _ : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := (f.hom.app X).hom.toAlgebra
  let _ : Algebra (O₁.obj.obj Y) (O₂.obj.obj Y) := (f.hom.app Y).hom.toAlgebra
  let _ : Module (O₂.obj.obj X) (H.obj X) := (H.obj X).isModule
  let _ : Module (O₂.obj.obj Y) (H.obj Y) := (H.obj Y).isModule
  let _ : Module (O₁.obj.obj X) (G.obj X) := (G.obj X).isModule
  let _ : Module (O₁.obj.obj Y) (G.obj Y) := (G.obj Y).isModule
  let _ : Module (O₁.obj.obj X) (H.obj X) := Module.compHom _ (f.hom.app X).hom
  let _ : Module (O₁.obj.obj Y) (H.obj Y) := Module.compHom _ (f.hom.app Y).hom
  let _ : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (H.obj X) :=
    IsScalarTower.of_algebraMap_smul (by intro r x; rfl)
  let _ : IsScalarTower (O₁.obj.obj Y) (O₂.obj.obj Y) (H.obj Y) :=
    IsScalarTower.of_algebraMap_smul (by intro r x; rfl)
  let L : (H.obj X ⊗[O₂.obj.obj X] (O₂.obj.obj X ⊗[O₁.obj.obj X] G.obj X)) →+
      (H.obj Y ⊗[O₁.obj.obj Y] G.obj Y) :=
    (baseChangeApp f G H Y).hom.hom.toAddMonoidHom.comp
      (((PresheafOfModules.restrictScalars (ringPresheafMap f)).obj
        (tensorObj H ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings f.hom).obj G))).map
          g).hom.toAddMonoidHom
  let R : (H.obj X ⊗[O₂.obj.obj X] (O₂.obj.obj X ⊗[O₁.obj.obj X] G.obj X)) →+
      (H.obj Y ⊗[O₁.obj.obj Y] G.obj Y) :=
    ((tensorObj ((PresheafOfModules.restrictScalars (ringPresheafMap f)).obj H)
        G).map g).hom.toAddMonoidHom.comp
      (baseChangeApp f G H X).hom.hom.toAddMonoidHom
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  refine tensorBaseChange_hom_ext L R ?_
  intro a s x
  change tensorBaseChange
      ((show H.obj Y from H.map g a) ⊗ₜ[O₂.obj.obj Y]
        ((O₂.obj.map g s) ⊗ₜ[O₁.obj.obj Y] (show G.obj Y from G.map g x))) =
    (show H.obj Y from H.map g (s • a)) ⊗ₜ[O₁.obj.obj Y] (show G.obj Y from G.map g x)
  rw [tensorBaseChange_tmul, H.map_smul]
  rfl

/-- The base-change isomorphism is natural in the first tensor factor. -/
lemma baseChange_naturality {H H' : PresheafOfModules.{w} (ringPresheaf O₂.obj)} (φ : H ⟶ H') :
    (PresheafOfModules.restrictScalars (ringPresheafMap f)).map
        ((tensorRight ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings f.hom).obj G)).map φ) ≫
      (baseChange f G H').hom =
    (baseChange f G H).hom ≫ (tensorRight G).map
      ((PresheafOfModules.restrictScalars (ringPresheafMap f)).map φ) := by
  apply PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  let _ : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := (f.hom.app X).hom.toAlgebra
  let _ : Module (O₂.obj.obj X) (H.obj X) := (H.obj X).isModule
  let _ : Module (O₂.obj.obj X) (H'.obj X) := (H'.obj X).isModule
  let _ : Module (O₁.obj.obj X) (G.obj X) := (G.obj X).isModule
  let _ : Module (O₁.obj.obj X) (H.obj X) := Module.compHom _ (f.hom.app X).hom
  let _ : Module (O₁.obj.obj X) (H'.obj X) := Module.compHom _ (f.hom.app X).hom
  let _ : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (H'.obj X) :=
    IsScalarTower.of_algebraMap_smul (by intro r x; rfl)
  let L : (H.obj X ⊗[O₂.obj.obj X] (O₂.obj.obj X ⊗[O₁.obj.obj X] G.obj X)) →+
      (H'.obj X ⊗[O₁.obj.obj X] G.obj X) :=
    (((PresheafOfModules.restrictScalars (ringPresheafMap f)).map
        ((tensorRight ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings f.hom).obj G)).map φ) ≫
      (baseChange f G H').hom).app X).hom.toAddMonoidHom
  let R : (H.obj X ⊗[O₂.obj.obj X] (O₂.obj.obj X ⊗[O₁.obj.obj X] G.obj X)) →+
      (H'.obj X ⊗[O₁.obj.obj X] G.obj X) :=
    (((baseChange f G H).hom ≫ (tensorRight G).map
        ((PresheafOfModules.restrictScalars (ringPresheafMap f)).map φ)).app X).hom.toAddMonoidHom
  refine tensorBaseChange_hom_ext L R ?_
  intro a s x
  show tensorBaseChange
      ((show H'.obj X from φ.app X a) ⊗ₜ[O₂.obj.obj X] (s ⊗ₜ[O₁.obj.obj X] x)) =
    (show H'.obj X from φ.app X (s • a)) ⊗ₜ[O₁.obj.obj X] x
  rw [tensorBaseChange_tmul, (φ.app X).hom.map_smul]

/-- The base-change isomorphism, as an isomorphism of functors. -/
noncomputable def baseChangeNatIso :
    tensorRight ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings f.hom).obj G) ⋙
        PresheafOfModules.restrictScalars (ringPresheafMap f) ≅
      PresheafOfModules.restrictScalars (ringPresheafMap f) ⋙ tensorRight G :=
  NatIso.ofComponents (fun H ↦ baseChange f G H) (fun φ ↦ baseChange_naturality f G φ)

end Presheaf


/-! ## Extension of scalars for sheaves of modules -/

section Sheaf

variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The sectionwise extension of scalars of Stacks 03CU, retyped at the spelling of the
sheaf-level statements. -/
noncomputable def presheafExtendScalars :
    PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₁).obj ⥤
      PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj :=
  Stacks.PresheafOfModules.ChangeOfRings.changeOfRings f.hom

/-- **Extension of scalars for sheaves of modules** along a morphism of sheaves of
commutative rings: the sectionwise tensor product `O₂ ⊗_{O₁} -`, sheafified. -/
noncomputable def extendScalars :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₁) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂) :=
  SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O₁) ⋙ presheafExtendScalars f ⋙
    moduleSheafification O₂

/-- Extension of scalars is left adjoint to restriction of scalars (Stacks 03CZ), so the
functor defined here is the expected one.

It is built from `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction`, the
presheaf-level adjunction supplied as data rather than as an inhabitant of a `Nonempty` type.
That matters for the unit: an adjunction between a fixed pair of functors is not unique as
data, so nothing can be computed about the unit of one obtained by `Classical.choice`, whereas
the unit here is `x ↦ 1 ⊗ x` (`…changeOfRingsAdjunction_unit_app_apply`) followed by the unit
of sheafification. -/
noncomputable def extendScalarsAdjunction :
    extendScalars f ⊣ SheafOfModules.restrictScalars.{w} (ringSheafMap f) :=
  Adjunction.restrictFullyFaithful
    ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction f.hom).comp
      (PresheafOfModules.sheafificationAdjunction (R := Stacks.SheafOfModules.Tensor.ringSheaf O₂)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)))
    (SheafOfModules.fullyFaithfulForget (Stacks.SheafOfModules.Tensor.ringSheaf O₁))
    (Functor.FullyFaithful.id _)
    (eqToIso (Functor.comp_id (extendScalars f)).symm) (eqToIso (Functor.id_comp _))

variable (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₁))

/-- The unit of sheafification at the sectionwise extension of scalars: a locally bijective
morphism from `O₂ ⊗_{p,O₁} G` to the underlying presheaf of `O₂ ⊗_{O₁} G`. -/
noncomputable abbrev toExtendScalarsVal :
    (presheafExtendScalars f).obj G.val ⟶ ((extendScalars f).obj G).val :=
  (PresheafOfModules.sheafificationAdjunction (R := Stacks.SheafOfModules.Tensor.ringSheaf O₂)
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)).unit.app _

/-- The unit `toExtendScalarsVal f G` is locally injective on underlying presheaves. -/
instance : Presheaf.IsLocallyInjective J
    ((PresheafOfModules.toPresheaf (ringPresheaf O₂.obj)).map (toExtendScalarsVal f G)) := by
  change Presheaf.IsLocallyInjective J
    (CategoryTheory.toSheafify J ((presheafExtendScalars f).obj G.val).presheaf)
  infer_instance

/-- The unit `toExtendScalarsVal f G` is locally surjective on underlying presheaves. -/
instance : Presheaf.IsLocallySurjective J
    ((PresheafOfModules.toPresheaf (ringPresheaf O₂.obj)).map (toExtendScalarsVal f G)) := by
  change Presheaf.IsLocallySurjective J
    (CategoryTheory.toSheafify J ((presheafExtendScalars f).obj G.val).presheaf)
  infer_instance

/-- Tensoring and then sheafifying does not distinguish the sectionwise extension of scalars
from its sheafification, because the unit of sheafification is locally bijective and
`Stacks.isIso_sheafification_map_tensorMapRight` says the second tensor variable does not see
a local bijection. -/
noncomputable def tensorRightExtendScalarsIso :
    tensorRightOf O₂ ((presheafExtendScalars f).obj G.val) ⋙ moduleSheafification O₂ ≅
      tensorRightOf O₂ ((extendScalars f).obj G).val ⋙ moduleSheafification O₂ := by
  haveI : ∀ M, IsIso ((Functor.whiskerRight
      (tensorRightNatTrans (O := O₂.obj) (toExtendScalarsVal f G))
      (moduleSheafification O₂)).app M) := fun M ↦
    isIso_sheafification_map_tensorMapRight (O := O₂.obj)
      (R := Stacks.SheafOfModules.Tensor.ringSheaf O₂) (M := M) (ringSheafCompare O₂)
      (toExtendScalarsVal f G)
  haveI := NatIso.isIso_of_isIso_app (Functor.whiskerRight
    (tensorRightNatTrans (O := O₂.obj) (toExtendScalarsVal f G)) (moduleSheafification O₂))
  have e := asIso (Functor.whiskerRight
    (tensorRightNatTrans (O := O₂.obj) (toExtendScalarsVal f G)) (moduleSheafification O₂))
  exact e

/-- The base-change isomorphism of `baseChangeNatIso`, retyped at the spelling of the
sheaf-level statements. -/
noncomputable def baseChangeNatIsoOf :
    tensorRightOf O₂ ((presheafExtendScalars f).obj G.val) ⋙
        PresheafOfModules.restrictScalars (ringSheafMap f).hom ≅
      PresheafOfModules.restrictScalars (ringSheafMap f).hom ⋙ tensorRightOf O₁ G.val :=
  baseChangeNatIso f G.val

/-- **The identity `H ⊗_{O₂} (O₂ ⊗_{O₁} G) = H ⊗_{O₁} G` of sheaves of abelian groups.**
This is the step the source performs "as sheaves of abelian groups for example": the two
tensor products have the same underlying sheaf of abelian groups, naturally in `H`. -/
noncomputable def tensorBaseChangeSheafIso :
    SheafOfModules.restrictScalars.{w} (ringSheafMap f) ⋙
        (Stacks.SheafOfModules.Tensor.sheafTensor O₁).flip.obj G ⋙
        SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O₁) ≅
      SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O₂) ⋙
        tensorRightOf O₂ ((presheafExtendScalars f).obj G.val) ⋙
          moduleSheafification O₂ ⋙
            SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O₂) :=
  Functor.isoWhiskerLeft (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O₂))
    (Functor.isoWhiskerRight (baseChangeNatIsoOf f G).symm
      (PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf O₁).obj ⋙
        presheafToSheaf J AddCommGrpCat.{w}))

/-- A functor into sheaves of modules preserves finite limits if it does so after forgetting to
sheaves of abelian groups. -/
private theorem preservesFiniteLimits_of_comp_toSheaf {C' : Type u} [Category.{v} C']
    {J' : GrothendieckTopology C'} {R : Sheaf J' RingCat.{w}} {A : Type*} [Category A]
    (F : A ⥤ SheafOfModules.{w} R) [PreservesFiniteLimits (F ⋙ SheafOfModules.toSheaf R)] :
    PreservesFiniteLimits F :=
  preservesFiniteLimits_of_reflects_of_preserves F (SheafOfModules.toSheaf R)

/-- **Stacks Project, Tag 05V4.** Extension of scalars along a morphism of sheaves of
commutative rings takes a flat sheaf of modules to a flat sheaf of modules. -/
@[stacks 05V4]
theorem isFlat_extendScalars (hG : SheafOfModules.IsFlat G) :
    SheafOfModules.IsFlat ((extendScalars f).obj G) := by
  refine (exactFunctor_iff _).2 ⟨?_, inferInstance⟩
  have hVt : SheafOfModules.restrictScalars.{w} (ringSheafMap f) ⋙
      SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O₁) =
        SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O₂) := rfl
  have hV : PreservesFiniteLimits (SheafOfModules.restrictScalars.{w} (ringSheafMap f)) := by
    have h : PreservesFiniteLimits (SheafOfModules.restrictScalars.{w} (ringSheafMap f) ⋙
        SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O₁)) := by
      rw [hVt]; infer_instance
    exact preservesFiniteLimits_of_comp_toSheaf _
  have hT₁ := ((exactFunctor_iff _).1 hG).1
  have h₁ : PreservesFiniteLimits ((Stacks.SheafOfModules.Tensor.sheafTensor O₁).flip.obj G ⋙
      SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O₁)) :=
    comp_preservesFiniteLimits _ _
  have h₂ : PreservesFiniteLimits (SheafOfModules.restrictScalars.{w} (ringSheafMap f) ⋙
      (Stacks.SheafOfModules.Tensor.sheafTensor O₁).flip.obj G ⋙
        SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O₁)) :=
    comp_preservesFiniteLimits _ _
  have h₃ := preservesFiniteLimits_of_natIso (tensorBaseChangeSheafIso f G)
  have h₃' : PreservesFiniteLimits
      ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O₂) ⋙
          tensorRightOf O₂ ((presheafExtendScalars f).obj G.val) ⋙
            moduleSheafification O₂) ⋙
        SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O₂)) := h₃
  have h₄ := preservesFiniteLimits_of_natIso (Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O₂))
      (tensorRightExtendScalarsIso f G))
    (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O₂)))
  have h₄' : PreservesFiniteLimits
      ((Stacks.SheafOfModules.Tensor.sheafTensor O₂).flip.obj ((extendScalars f).obj G) ⋙
      SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O₂)) := h₄
  exact preservesFiniteLimits_of_comp_toSheaf _

end Sheaf

end Stacks.FlatChangeOfRings
