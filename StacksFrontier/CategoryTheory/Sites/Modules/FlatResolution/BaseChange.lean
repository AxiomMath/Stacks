module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatResolution.ExtensionOfScalars
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatColimits

/-!
# The universal property of extension of scalars for sheaves of modules

Let `f : O ⟶ O₀` be a morphism of sheaves of commutative rings on a site. A sheaf of
`O₀`-modules `M₀` together with a morphism `M ⟶ M₀|_O` *is* the extension of scalars of a sheaf
of `O`-modules `M` when that morphism is universal among morphisms from `M` into the
restriction of a sheaf of `O₀`-modules. This file records that property, shows that extension
of scalars has it, and collects the consequences the lifting construction of Stacks 0DIT uses:
the universal morphism descends maps and epimorphisms, it is itself an epimorphism when `f` is
locally surjective, it carries zero modules to zero modules, and it is compatible with binary
direct sums.

## Main definitions

* `Stacks.SheafOfModules.ComplexLifting.IsExtensionOfScalars`: the universal property.

## Main results

* `Stacks.SheafOfModules.ComplexLifting.extensionOfScalarsUnit_isExtension`: extension of
  scalars has the universal property.
* `Stacks.SheafOfModules.ComplexLifting.extensionRestrictionAdjunction_unit_app`: the universal
  morphism is the unit of the adjunction of Stacks 03CZ, by `rfl`.
* `Stacks.SheafOfModules.ComplexLifting.IsExtensionOfScalars.epi_unit`: the universal morphism
  is an epimorphism when `f` is locally surjective.
* `Stacks.SheafOfModules.ComplexLifting.IsExtensionOfScalars.pair`: the universal property is
  stable under binary direct sums.

## Implementation notes

Recording extension of scalars by its universal property, rather than by a particular model,
is what keeps the lifting construction independent of the chosen sheafification: the terms it
builds are only ever known to satisfy the universal property. The model used to prove that the
property is attained is `Stacks.Sheaves.ChangeOfRings.extensionOfScalars`, the sectionwise
tensor product of Stacks 03CU followed by sheafification, and the hom-bijection is the
composite of that sheafification bijection with the objectwise change-of-rings bijection
`Stacks.PresheafOfModules.ChangeOfRings.homEquivCore` and the fully faithful inclusion of sheaves
of modules into presheaves of modules.  Assembling the bijection from `homEquivCore` rather
than reading it off `Stacks.Sheaves.ChangeOfRings.extensionRestrictionAdjunction` was forced
while Tag 03CU was available only in its `Nonempty` form, whose unit is opaque; it is no longer,
and `extensionRestrictionAdjunction_unit_app` identifies the two.

The epimorphism statement is the only place where the model is used in an essential way: the
unit `M ⟶ (O₀ ⊗_O M)|_O` is locally surjective because a pure tensor `a ⊗ m` over a member of
a covering on which `a` lifts to a section `r` of `O` equals `1 ⊗ (r · m)`, so the presheaf-level
unit is locally surjective, and sheafification preserves that.

Binary direct sums are formed as a coproduct indexed by `ULift Bool` rather than as a biproduct,
so that the flatness of a direct sum (Stacks 05NG) applies to them verbatim.

## References

* [Stacks Project, Tag 0DIT](https://stacks.math.columbia.edu/tag/0DIT)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open TensorProduct

universe v u w z

namespace Stacks.SheafOfModules.ComplexLifting

open AlgebraicGeometry.SheafOfModules (ringPresheaf)
open Stacks.Sheaves.ChangeOfRings (ringSheafMap extensionOfScalars
  extensionRestrictionAdjunction)

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- The universal-property formulation of `M₀ ≅ M ⊗_O O₀`: every morphism from `M` into the
restriction of scalars of a sheaf of `O₀`-modules factors uniquely through `unit`. -/
def IsExtensionOfScalars {O O₀ : Sheaf J CommRingCat.{w}} (f : O ⟶ O₀)
    (M : _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (M₀ : _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
    (unit : M ⟶ (_root_.SheafOfModules.restrictScalars (ringSheafMap f)).obj M₀) : Prop :=
  ∀ N : _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O₀),
    Function.Bijective (fun a : M₀ ⟶ N ↦
      unit ≫ (_root_.SheafOfModules.restrictScalars (ringSheafMap f)).map a)

/-- Restriction of scalars does not identify distinct morphisms of sheaves of modules. -/
lemma restrictScalars_faithful {O O₀ : Sheaf J CommRingCat.{w}} (f : O ⟶ O₀) :
    (_root_.SheafOfModules.restrictScalars.{z} (ringSheafMap f)).Faithful := by
  constructor
  intro M N a b hab
  ext U x
  exact congrArg (fun k => (k.val.app U) x) hab

/-- Extension of scalars carries a zero module to a zero module. -/
lemma isZero_of_isExtensionOfScalars {O O₀ : Sheaf J CommRingCat.{w}} (f : O ⟶ O₀)
    {M : _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    {M₀ : _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)}
    {unit : M ⟶ (_root_.SheafOfModules.restrictScalars (ringSheafMap f)).obj M₀}
    (h : IsExtensionOfScalars f M M₀ unit) (hM : IsZero M) : IsZero M₀ := by
  rw [IsZero.iff_id_eq_zero]
  apply (h M₀).injective
  simp [hM.eq_of_src unit 0]

/-- A morphism out of an extension of scalars, recovered from its restriction along the
universal morphism. -/
noncomputable def IsExtensionOfScalars.desc {O O₀ : Sheaf J CommRingCat.{w}} (f : O ⟶ O₀)
    {M : _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    {M₀ : _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)}
    {unit : M ⟶ (_root_.SheafOfModules.restrictScalars (ringSheafMap f)).obj M₀}
    (h : IsExtensionOfScalars f M M₀ unit)
    {N : _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)}
    (k : M ⟶ (_root_.SheafOfModules.restrictScalars (ringSheafMap f)).obj N) : M₀ ⟶ N :=
  Classical.choose ((h N).surjective k)

/-- The defining property of `IsExtensionOfScalars.desc`. -/
lemma IsExtensionOfScalars.desc_spec {O O₀ : Sheaf J CommRingCat.{w}} (f : O ⟶ O₀)
    {M : _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    {M₀ : _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)}
    {unit : M ⟶ (_root_.SheafOfModules.restrictScalars (ringSheafMap f)).obj M₀}
    (h : IsExtensionOfScalars f M M₀ unit)
    {N : _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)}
    (k : M ⟶ (_root_.SheafOfModules.restrictScalars (ringSheafMap f)).obj N) :
    unit ≫ (_root_.SheafOfModules.restrictScalars (ringSheafMap f)).map
      (IsExtensionOfScalars.desc f h k) = k :=
  Classical.choose_spec ((h N).surjective k)

/-- An epimorphism factoring through the universal morphism descends to an epimorphism. -/
lemma IsExtensionOfScalars.epi_desc {O O₀ : Sheaf J CommRingCat.{w}} (f : O ⟶ O₀)
    {M : _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    {M₀ : _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)}
    {unit : M ⟶ (_root_.SheafOfModules.restrictScalars (ringSheafMap f)).obj M₀}
    (h : IsExtensionOfScalars f M M₀ unit)
    {N : _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)}
    (k : M ⟶ (_root_.SheafOfModules.restrictScalars (ringSheafMap f)).obj N) [Epi k] :
    Epi (IsExtensionOfScalars.desc f h k) := by
  have : (_root_.SheafOfModules.restrictScalars.{z} (ringSheafMap f)).Faithful :=
    restrictScalars_faithful f
  have : Epi ((_root_.SheafOfModules.restrictScalars (ringSheafMap f)).map
      (IsExtensionOfScalars.desc f h k)) :=
    epi_of_epi_fac (IsExtensionOfScalars.desc_spec f h k)
  exact (_root_.SheafOfModules.restrictScalars (ringSheafMap f)).epi_of_epi_map inferInstance

section Model

variable [J.WEqualsLocallyBijective AddCommGrpCat.{max w z}]
  [HasSheafify J AddCommGrpCat.{max w z}]
  {O O₀ : Sheaf J CommRingCat.{w}}

/-- The hom-bijection exhibiting `Stacks.Sheaves.ChangeOfRings.extensionOfScalars` as left
adjoint to restriction of scalars, in the objectwise form the universal property asks for. -/
noncomputable def extensionOfScalarsHomEquiv (f : O ⟶ O₀)
    (M : _root_.SheafOfModules.{max w z} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (N : _root_.SheafOfModules.{max w z} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) :
    ((extensionOfScalars.{z} f).obj M ⟶ N) ≃
      (M ⟶ (_root_.SheafOfModules.restrictScalars (ringSheafMap f)).obj N) :=
  (_root_.PresheafOfModules.sheafificationHomEquiv
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₀).obj)).trans
    ((Stacks.PresheafOfModules.ChangeOfRings.homEquivCore f.hom M.val N.val).trans
      ((_root_.SheafOfModules.fullyFaithfulForget
          (Stacks.SheafOfModules.Tensor.ringSheaf O)).homEquiv (X := M)
        (Y := (_root_.SheafOfModules.restrictScalars (ringSheafMap f)).obj N)).symm)

/-- The universal morphism into the extension of scalars of `M`. -/
noncomputable def extensionOfScalarsUnit (f : O ⟶ O₀)
    (M : _root_.SheafOfModules.{max w z} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    M ⟶ (_root_.SheafOfModules.restrictScalars (ringSheafMap f)).obj
      ((extensionOfScalars.{z} f).obj M) := extensionOfScalarsHomEquiv f M _ (𝟙 _)

/-- The hom-bijection of `extensionOfScalarsHomEquiv` is composition with
`extensionOfScalarsUnit`. -/
lemma extensionOfScalarsHomEquiv_eq (f : O ⟶ O₀)
    (M : _root_.SheafOfModules.{max w z} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (N : _root_.SheafOfModules.{max w z} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
    (a : (extensionOfScalars.{z} f).obj M ⟶ N) :
    extensionOfScalarsHomEquiv f M N a = extensionOfScalarsUnit f M ≫
      (_root_.SheafOfModules.restrictScalars (ringSheafMap f)).map a := by
  ext U x
  let _inst := (f.hom.app U).hom.toAlgebra
  exact Stacks.PresheafOfModules.ChangeOfRings.unitApp_apply f.hom
    (_root_.PresheafOfModules.sheafificationHomEquiv
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₀).obj) a) U x

/-- Extension of scalars has the universal property. -/
lemma extensionOfScalarsUnit_isExtension (f : O ⟶ O₀)
    (M : _root_.SheafOfModules.{max w z} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    IsExtensionOfScalars f M ((extensionOfScalars.{z} f).obj M) (extensionOfScalarsUnit f M) := by
  intro N
  simpa only [← extensionOfScalarsHomEquiv_eq] using (extensionOfScalarsHomEquiv f M N).bijective

/-- **The unit of `Stacks.Sheaves.ChangeOfRings.extensionRestrictionAdjunction` is the universal
morphism `extensionOfScalarsUnit`**, by `rfl`.

The adjunction of Stacks 03CZ is assembled from
  `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction`, the *data*
form of Tag 03CU, and `extensionOfScalarsUnit` is built from
  `Stacks.PresheafOfModules.ChangeOfRings.homEquivCore`, the
bijection that same `def` packages; so the two are the same term.  Consequently everything
proved here about `extensionOfScalarsUnit` — the universal property, local surjectivity, and
being an epimorphism when `f` is locally surjective — is a statement about the adjunction's own
unit.

With the `Nonempty`-wrapped form of Tag 03CU in place of the `def`, the adjunction's unit is an
inhabitant chosen by `Classical.choice` and this equation is not provable at all: an adjunction
between a fixed pair of functors is not unique as data, so nothing records which one was taken.
That is why the hom-bijection above is assembled from `homEquivCore` directly rather than read
off the adjunction. -/
theorem extensionRestrictionAdjunction_unit_app (f : O ⟶ O₀)
    (M : _root_.SheafOfModules.{max w z} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (extensionRestrictionAdjunction.{z} f).unit.app M = extensionOfScalarsUnit f M :=
  rfl

/-- The hom-bijection of the adjunction of Stacks 03CZ is `extensionOfScalarsHomEquiv`.

Unlike `extensionRestrictionAdjunction_unit_app` this is not `rfl`: `Adjunction.homEquiv` of an
adjunction produced by `Adjunction.restrictFullyFaithful` carries the two `eqToIso` conjugations
of that construction.  It follows from the unit equation all the same. -/
theorem extensionRestrictionAdjunction_homEquiv (f : O ⟶ O₀)
    (M : _root_.SheafOfModules.{max w z} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (N : _root_.SheafOfModules.{max w z} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) :
    (extensionRestrictionAdjunction.{z} f).homEquiv M N = extensionOfScalarsHomEquiv f M N := by
  ext a
  rw [Adjunction.homEquiv_unit, extensionRestrictionAdjunction_unit_app,
    extensionOfScalarsHomEquiv_eq]

/-- The unit of the adjunction of Stacks 03CZ exhibits extension of scalars by its universal
property. -/
lemma extensionRestrictionAdjunction_unit_isExtension (f : O ⟶ O₀)
    (M : _root_.SheafOfModules.{max w z} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    IsExtensionOfScalars f M ((extensionOfScalars.{z} f).obj M)
      ((extensionRestrictionAdjunction.{z} f).unit.app M) :=
  extensionOfScalarsUnit_isExtension f M

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasSheafify J AddCommGrpCat.{max w z}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w z}] in
/-- The presheaf-level unit `M ⟶ O₀ ⊗_O M` is locally surjective when `f` is: a pure tensor
`a ⊗ m` is `1 ⊗ (r · m)` on any member of a covering on which `a` lifts to a section `r`
of `O`. -/
lemma presheafUnit_isLocallySurjective (f : O ⟶ O₀) (hf : Sheaf.IsLocallySurjective f)
    (M : _root_.PresheafOfModules.{max w z} (ringPresheaf O.obj)) :
    Presheaf.IsLocallySurjective J
      ((_root_.PresheafOfModules.toPresheaf _).map
        (Stacks.PresheafOfModules.ChangeOfRings.unitHom f.hom (𝟙
          ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings f.hom).obj M)))) := by
  let η : M.presheaf ⟶
      ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings f.hom).obj M).presheaf :=
    (_root_.PresheafOfModules.toPresheaf _).map
      (Stacks.PresheafOfModules.ChangeOfRings.unitHom f.hom (𝟙
        ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings f.hom).obj M)))
  constructor
  intro U s
  let _inst := (f.hom.app (Opposite.op U)).hom.toAlgebra
  change Presheaf.imageSieve η s ∈ J U
  change (O₀.obj.obj (Opposite.op U) ⊗[O.obj.obj (Opposite.op U)]
    M.obj (Opposite.op U)) at s
  induction s using TensorProduct.inductionOn with
  | add x y hx hy =>
    apply J.superset_covering (S := Presheaf.imageSieve η x ⊓ Presheaf.imageSieve η y)
      _ (J.intersection_covering hx hy)
    rintro V i ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨a + b, ?_⟩
    change (η.app _).hom (a + b) =
      (((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings f.hom).obj M).presheaf.map i.op).hom
        (x + y)
    change (η.app _).hom a =
      (((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings f.hom).obj M).presheaf.map i.op).hom x
        at ha
    change (η.app _).hom b =
      (((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings f.hom).obj M).presheaf.map i.op).hom y
        at hb
    exact (map_add (η.app _).hom a b).trans
      ((congrArg₂ (· + ·) ha hb).trans (map_add _ x y).symm)
  | tmul a m =>
    apply J.superset_covering (S := Presheaf.imageSieve f.hom a) _ (hf.imageSieve_mem a)
    rintro V i ⟨r, hr⟩
    let _instV := (f.hom.app (Opposite.op V)).hom.toAlgebra
    refine ⟨r • (show M.obj (Opposite.op V) from M.map i.op m), ?_⟩
    change (Stacks.PresheafOfModules.ChangeOfRings.unitApp f.hom (𝟙 _) _).hom _ =
      (Stacks.PresheafOfModules.ChangeOfRings.cofMap f.hom M i.op).hom (a ⊗ₜ m)
    rw [Stacks.PresheafOfModules.ChangeOfRings.unitApp_apply,
      Stacks.PresheafOfModules.ChangeOfRings.cofMap_tmul, ← TensorProduct.smul_tmul]
    simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_one, hr]
    rfl

/-- The universal morphism into the extension of scalars is an epimorphism when `f` is
locally surjective. -/
lemma extensionOfScalarsUnit_epi (f : O ⟶ O₀) (hf : Sheaf.IsLocallySurjective f)
    (M : _root_.SheafOfModules.{max w z} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    Epi (extensionOfScalarsUnit f M) := by
  let T := (Stacks.PresheafOfModules.ChangeOfRings.changeOfRings f.hom).obj M.val
  let η : M.val.presheaf ⟶ T.presheaf :=
    (_root_.PresheafOfModules.toPresheaf _).map (Stacks.PresheafOfModules.ChangeOfRings.unitHom
      f.hom (𝟙 T))
  have hη : Presheaf.IsLocallySurjective J η :=
    presheafUnit_isLocallySurjective f hf M.val
  have heq : ((_root_.SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O)).map
      (extensionOfScalarsUnit f M)).hom = η ≫ CategoryTheory.toSheafify J T.presheaf := by
    ext U x
    let _inst := (f.hom.app U).hom.toAlgebra
    exact Stacks.PresheafOfModules.ChangeOfRings.unitApp_apply f.hom
      (_root_.PresheafOfModules.sheafificationHomEquiv
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₀).obj) (𝟙 _)) U x
  have h : Sheaf.IsLocallySurjective
      ((_root_.SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O)).map
        (extensionOfScalarsUnit f M)) := by
    change Presheaf.IsLocallySurjective J _
    rw [heq]
    exact Presheaf.isLocallySurjective_comp J η (CategoryTheory.toSheafify J T.presheaf)
  exact (_root_.SheafOfModules.toSheaf.{max w z}
    (Stacks.SheafOfModules.Tensor.ringSheaf O)).epi_of_epi_map inferInstance

/-- Any morphism with the universal property of extension of scalars is an epimorphism when
`f` is locally surjective: it agrees with `extensionOfScalarsUnit` up to an isomorphism. -/
lemma IsExtensionOfScalars.epi_unit (f : O ⟶ O₀) (hf : Sheaf.IsLocallySurjective f)
    {M : _root_.SheafOfModules.{max w z} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    {M₀ : _root_.SheafOfModules.{max w z} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)}
    {uM : M ⟶ (_root_.SheafOfModules.restrictScalars (ringSheafMap f)).obj M₀}
    (h : IsExtensionOfScalars f M M₀ uM) : Epi uM := by
  let R := _root_.SheafOfModules.restrictScalars (ringSheafMap f)
  have h' := extensionOfScalarsUnit_isExtension f M
  let a := IsExtensionOfScalars.desc f h' uM
  let b := IsExtensionOfScalars.desc f h (extensionOfScalarsUnit f M)
  have ha : extensionOfScalarsUnit f M ≫ R.map a = uM := IsExtensionOfScalars.desc_spec f h' uM
  have hb : uM ≫ R.map b = extensionOfScalarsUnit f M := IsExtensionOfScalars.desc_spec f h _
  have hba : b ≫ a = 𝟙 _ := by
    apply (h _).injective
    change uM ≫ R.map (b ≫ a) = uM ≫ R.map (𝟙 _)
    rw [R.map_comp, ← Category.assoc, hb, ha, R.map_id, Category.comp_id]
  have : Epi (R.map a) := epi_of_epi_fac (by rw [← R.map_comp, hba, R.map_id])
  have : Epi (extensionOfScalarsUnit f M) := extensionOfScalarsUnit_epi f hf M
  rw [← ha]
  exact epi_comp _ _

end Model

section Coproduct

variable [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
  [HasSheafify J AddCommGrpCat.{z}] {O : Sheaf J CommRingCat.{w}}

/- Instance search for these coproducts times out under Lean v4.35.0: supply them. -/
local instance : HasColimitsOfShape (Discrete (ULift.{z} Bool))
    (PresheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj) :=
  PresheafOfModules.hasColimitsOfShape _ _

set_option synthInstance.maxHeartbeats 400000 in
-- the `inferInstance` search for colimits of sheaves of modules over `ringSheaf O` is deep
local instance (priority := high) : HasColimitsOfShape (Discrete (ULift.{z} Bool))
    (_root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
  inferInstance

/-- The two-element family whose coproduct is the direct sum of `M` and `N`. -/
abbrev pairFamily (M N : _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (i : ULift.{z} Bool) := if i.down then N else M

/-- The direct sum of two sheaves of modules, formed as a coproduct over `ULift Bool`. -/
noncomputable abbrev pairObj
    (M N : _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O)) := ∐ pairFamily M N

/-- The first inclusion into `pairObj`. -/
noncomputable abbrev pairInl
    (M N : _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    M ⟶ pairObj M N := Sigma.ι (pairFamily M N) ⟨false⟩

/-- The second inclusion into `pairObj`. -/
noncomputable abbrev pairInr
    (M N : _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    N ⟶ pairObj M N := Sigma.ι (pairFamily M N) ⟨true⟩

/-- The morphism out of `pairObj` determined by a morphism out of each summand. -/
noncomputable abbrev pairDesc
    {M N P : _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (a : M ⟶ P) (b : N ⟶ P) : pairObj M N ⟶ P :=
  Sigma.desc (fun i => match i with | ⟨false⟩ => a | ⟨true⟩ => b)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- `pairDesc` restricts to the first summand as prescribed. -/
lemma pairInl_desc {M N P : _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (a : M ⟶ P) (b : N ⟶ P) : pairInl M N ≫ pairDesc a b = a := Sigma.ι_comp_desc _ _

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- `pairDesc` restricts to the second summand as prescribed. -/
lemma pairInr_desc {M N P : _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (a : M ⟶ P) (b : N ⟶ P) : pairInr M N ≫ pairDesc a b = b := Sigma.ι_comp_desc _ _

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- A morphism out of `pairObj` is determined by its restrictions to the two summands. -/
lemma pair_hom_ext {M N P : _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    {a b : pairObj M N ⟶ P}
    (h₁ : pairInl M N ≫ a = pairInl M N ≫ b)
    (h₂ : pairInr M N ≫ a = pairInr M N ≫ b) : a = b := by
  apply Sigma.hom_ext
  rintro ⟨_ | _⟩ <;> assumption

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- A direct sum of two flat sheaves of modules is flat. -/
lemma pair_isFlat {M N : _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat M)
    (hN : AlgebraicGeometry.SheafOfModules.IsFlat N) :
    AlgebraicGeometry.SheafOfModules.IsFlat (pairObj M N) := by
  apply Stacks.SheafOfModules.FlatColimits.isFlat_coproduct
  rintro ⟨_ | _⟩ <;> assumption

/-- The universal property of extension of scalars is stable under binary direct sums. -/
lemma IsExtensionOfScalars.pair {O₀ : Sheaf J CommRingCat.{w}} (f : O ⟶ O₀)
    {M N : _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    {M₀ N₀ : _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)}
    {uM : M ⟶ (_root_.SheafOfModules.restrictScalars (ringSheafMap f)).obj M₀}
    {uN : N ⟶ (_root_.SheafOfModules.restrictScalars (ringSheafMap f)).obj N₀}
    (hM : IsExtensionOfScalars f M M₀ uM) (hN : IsExtensionOfScalars f N N₀ uN) :
    IsExtensionOfScalars f (pairObj M N) (pairObj M₀ N₀)
      (pairDesc
        (uM ≫ (_root_.SheafOfModules.restrictScalars (ringSheafMap f)).map (pairInl M₀ N₀))
        (uN ≫ (_root_.SheafOfModules.restrictScalars (ringSheafMap f)).map
          (pairInr M₀ N₀))) := by
  intro T
  constructor
  · intro a b hab
    have h₁ := congrArg (pairInl M N ≫ ·) hab
    have h₂ := congrArg (pairInr M N ≫ ·) hab
    simp only [← Category.assoc, pairInl_desc, pairInr_desc] at h₁ h₂
    exact pair_hom_ext ((hM T).injective h₁) ((hN T).injective h₂)
  · intro k
    obtain ⟨a, ha⟩ := (hM T).surjective (pairInl M N ≫ k)
    obtain ⟨b, hb⟩ := (hN T).surjective (pairInr M N ≫ k)
    refine ⟨pairDesc a b, pair_hom_ext ?_ ?_⟩ <;>
      (simp only [← Category.assoc, pairInl_desc, pairInr_desc]; simp only [Category.assoc,
        ← Functor.map_comp, pairInl_desc, pairInr_desc]; assumption)

end Coproduct

end Stacks.SheafOfModules.ComplexLifting

end
