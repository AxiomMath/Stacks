module

public import StacksFrontier.AlgebraicGeometry.ProjTrivialization.Basic
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAssociatorSections

/-!
# Multiplication by `f ^ n` is bijective on the sections over an open inside `D₊(f)`

Let `S = ⨁_{d ≥ 0} 𝒮 d` be a graded ring, `X = Proj 𝒮`, let `f ∈ 𝒮 d` be homogeneous, and let
`ℱ` be an **arbitrary** sheaf of `𝒪_X`-modules. For an open `W ⊆ D₊(f)` and a section `t` of `ℱ`
over `W`, the local pure tensor `t ⊗ f ^ n` is a section of the twist
`ℱ(nd) = ℱ ⊗_{𝒪_X} 𝒪_X(nd)` over `W`, and this file proves that

`Γ(W, ℱ) → Γ(W, ℱ(nd))`, `t ↦ t ⊗ f ^ n`

is a **bijection**. For `ℱ = 𝒪_X` this is Tag 01MS,
`Stacks.AlgebraicGeometry.ProjTrivialization.bijective_trivializingHom`; what is new is that `ℱ`
is arbitrary, which is the input that the comparison map of Tag 0B5I and the recovery statement
of Tag 03GM (2) are waiting on.

## The two steps, and where each comes from

The obstruction recorded against this statement in four places —
`Constructions/ProjectiveSpaceQuasicoherentModule.lean`,
`Constructions/ProjTwistSectionComparison.lean`,
`AlgebraicGeometry/TwistedSectionModule/Localization.lean` and
`AlgebraicGeometry/SectionProduct/Stalk.lean` — is the absence of a compatibility of the
sheafified tensor product with restriction to an open: nothing identified `(ℱ ⊗ 𝒪(nd))|_W` with
`ℱ|_W ⊗ 𝒪(nd)|_W`, so the trivialization of the second factor could not be tensored with the
identity of `ℱ`.

**That compatibility is in the library and the note is stale.**
`Stacks.SheafOfModules.TensorProduct.tensorSheafOverIso`
(`AlgebraicGeometry/Stacks/Quasicoherent/Descent/QuasicoherentTensor.lean`) is exactly it, for an
arbitrary site and in the `Stacks.SheafOfModules.TensorSheafification.tensorSheaf` spelling that
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistSheafOfModules` is defined in; it is the
localization case of Tag 03EL, proved from
`PresheafOfModules.sheafificationOverIso` (restriction commutes with sheafification) and the
pointwise `overRestrictionTensorPresheafIso`. `tensorOverIso` below is that isomorphism at the
site of `Proj 𝒮`, and the only work it needs is to see that the five sheafification hypotheses
of the localized site are satisfied there.

With it the statement is a two-line composite of isomorphisms, and **no surjectivity of the
sheafification unit is used anywhere**:

* `tensorOverIso`: `(ℱ ⊗ 𝒪(nd))|_{D₊(f)} ≅ ℱ|_{D₊(f)} ⊗ 𝒪(nd)|_{D₊(f)}`;
* `divTrivIso`: tensoring with the trivialization `𝒪(nd)|_{D₊(f)} ≅ 𝒪|_{D₊(f)}` of Tag 01MS
  (`twistingSheafOverBasicOpenIsoUnit`) and then the right unit constraint of the tensor product
  sheaf, so `ℱ|_{D₊(f)} ⊗ 𝒪(nd)|_{D₊(f)} ≅ ℱ|_{D₊(f)}`.

That the composite is multiplication by `f ^ n` on sections, rather than merely *some*
isomorphism, is the second half of the file, and it is where the section formulas of the tensor
product sheaf are used: `Stacks.SheafOfModules.sheafify_map_toSheafify_app` for the trivialization
step and `Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso_hom_app` — the right unit constraint
on a local pure tensor, `t ⊗ r ↦ r • t` — for the unitor step.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTwistRestriction.tensorOverIso`: the compatibility of the
  sheafified tensor product with restriction to an open of `Proj 𝒮`.
* `Stacks.AlgebraicGeometry.ProjTwistRestriction.tensorSection`: the image of a pure tensor of
  local sections under the sheafification unit, on the localized site.
* `Stacks.AlgebraicGeometry.ProjTwistRestriction.trivSection` and `trivCoord`: the trivializing
  section `f ^ n` of `𝒪(nd)` over an open of `D₊(f)`, and the coordinate of a section of
  `𝒪(nd)` in that trivialization.
* `Stacks.AlgebraicGeometry.ProjTwistRestriction.divTrivIso` and `twistRestrictIso`: division by
  the trivializing section, and the resulting `ℱ(nd)|_{D₊(f)} ≅ ℱ|_{D₊(f)}`.
* `Stacks.AlgebraicGeometry.ProjTwistRestriction.mulTrivSection`: multiplication of a section of
  `ℱ` over `W ⊆ D₊(f)` by `f ^ n`, as a section of `ℱ(nd)` over `W`.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistRestriction.sheafificationOverIso_inv_val_app`:
  **restriction to an open commutes with the sheafification unit**, on sections. This is the
  defining property of `PresheafOfModules.sheafificationOverIso`, which that definition does not
  record; it is what identifies the composite above with multiplication by `f ^ n` rather than
  leaving it an unnamed isomorphism.
* `Stacks.AlgebraicGeometry.ProjTwistRestriction.divTrivIso_hom_app_tensorSection`: dividing a
  local pure tensor `t ⊗ s` by the trivializing section gives the scalar multiple of `t` by the
  coordinate of `s`; `divTrivIso_hom_app_tensorSection_trivSection` is the case `s = f ^ n`,
  where the coordinate is `1` and the value is `t`.
* `Stacks.AlgebraicGeometry.ProjTwistRestriction.trivSection_eq`: the section of coordinate `1`
  is `Stacks.AlgebraicGeometry.ProjTrivialization.trivializingSection`, i.e. `f ^ n`.
* `Stacks.AlgebraicGeometry.ProjTwistRestriction.bijective_mulTrivSection`: **`Γ(W, ℱ) → Γ(W,
  ℱ(nd))`, `t ↦ t ⊗ f ^ n`, is bijective for every open `W ⊆ D₊(f)` and every sheaf of modules
  `ℱ`.** This is the statement the four notes ask for.
* `Stacks.AlgebraicGeometry.ProjTwistRestriction.bijective_twistRestrictIso_app`: the same
  bijection read off the isomorphism of sheaves, without the formula.

## Implementation notes

**Why the spellings are so long.** Four descriptions of the same sheaf of rings on the localized
site are in play: `(projRingSheaf 𝒮).over V`, `Sheaf.toRingCat` of
`(ProjectiveSpectrum.Proj.structureSheaf 𝒮).over V`,
`Stacks.SheafOfModules.TensorSheafification.structureSheaf` of its sections, and
`CategoryTheory.Sheaf.toRingCat` of it. All four are definitionally equal, but the *module* and
*scalar action* instances are keyed on the syntactic form, and instance search does not unfold a
structure projection to find them: writing `r • t` with `r` spelled through one and `t` through
another fails with a missing `HSMul`. `ringOver` and `restrictModule` fix one spelling —
`TensorSheafification.structureSheaf`, the one the section formulas of the tensor product sheaf
are stated in — and every statement below is phrased through them.

**The right unit constraint is used, not the monoidal structure.** `divTrivIso` is built from
`Stacks.SheafOfModules.TensorPower.tensorSheafMapIso` and
`Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso`, whose sources and targets are literally
`TensorSheafification.tensorSheaf`. Going through the monoidal structure
`Stacks.SheafOfModules.Strict.monoidalCategory` instead also works, but its `whiskerLeft` has no
section formula of its own; and going through `Stacks.SheafOfModules.tensorLeftFunctor` makes the
elaborator unify `(tensorLeftFunctor O hO A).obj B` with `tensorSheaf O hO A B` across an
`Iso.trans`, which exhausts the heartbeat budget at `whnf`.

**`0 < d` is not needed** and is not assumed, exactly as in
`StacksFrontier/AlgebraicGeometry/ProjTrivialization/Basic.lean`: the trivialization of `𝒪(nd)` on
`D₊(f)` holds for every `n : ℤ` and every homogeneous `f`, and so does everything below.
Instantiating at `0 < d` and `n = k` gives the form the consumers want.

## References

* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 0B5I](https://stacks.math.columbia.edu/tag/0B5I)

## What is not done

**No `@[stacks]` attribute is attached.** Nothing here is an assertion of a tag: Tag 01MS's two
clauses are the triviality and the invertibility of `𝒪(nd)` on `D₊(f)` and both are tagged in
`ProjTrivialization/Basic.lean`; Tag 03EL is tagged on
`Stacks.SheafOfModules.pullbackTensorIso`. The statement proved here is an input to Tag 0B5I's
comparison map and to Tag 03GM clause (2), and neither of those is proved here.

**The compatibility as `n` varies is not proved here.** What a comparison map needs beyond the
bijections below is that multiplying by `f ^ n` and then by `f ^ m` is multiplying by
`f ^ (n + m)`, so that `m / f ^ n` has a well-defined image; that is
`Stacks.AlgebraicGeometry.ProjTwistRestriction.twistSheafScalarMap_mulTrivSection_pow`, proved in
`ProjTwistScalarTriviality.lean` for multiplication by a homogeneous scalar, and the local
comparison for the ℕ-graded module of Tag 03GM is built from it in
`ProjTwistLocalComparison.lean`. Tag 0B5I's comparison, whose module is the ℤ-graded
`⨁_{n ∈ ℤ} Γ(X, ℱ(n))`, is still not built: the `θ`/`hθ` hypotheses of
`Stacks.AlgebraicGeometry.ProjTwistComparison.comparison` are **not** discharged.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.SheafOfModules.TensorSheafification
open scoped TensorProduct

namespace Stacks.AlgebraicGeometry.ProjTwistRestriction

universe u w v₁ u₁

/-! ### Sections of an isomorphism of sheaves of modules -/

/-- An isomorphism of sheaves of modules is injective on the sections over any object. -/
theorem injective_hom_val_app {C : Type u₁} [Category.{v₁} C] {JJ : GrothendieckTopology C}
    {Rg : Sheaf JJ RingCat.{u}} {A B : SheafOfModules.{u} Rg} (e : A ≅ B) (W : Cᵒᵖ) :
    Function.Injective fun x : A.val.obj W ↦ e.hom.val.app W x := by
  intro a b hab
  exact (Stacks.SheafOfModules.inv_val_app_hom_val_app e W a).symm.trans
    ((congrArg (fun z ↦ e.inv.val.app W z) hab).trans
      (Stacks.SheafOfModules.inv_val_app_hom_val_app e W b))

/-- An isomorphism of sheaves of modules is bijective on the sections over any object. -/
theorem bijective_hom_val_app {C : Type u₁} [Category.{v₁} C] {JJ : GrothendieckTopology C}
    {Rg : Sheaf JJ RingCat.{u}} {A B : SheafOfModules.{u} Rg} (e : A ≅ B) (W : Cᵒᵖ) :
    Function.Bijective fun x : A.val.obj W ↦ e.hom.val.app W x :=
  Function.bijective_iff_has_inverse.mpr
    ⟨fun y ↦ e.inv.val.app W y, Stacks.SheafOfModules.inv_val_app_hom_val_app e W,
      Stacks.SheafOfModules.hom_val_app_inv_val_app e W⟩

/-- A map on sections which an isomorphism of sheaves of modules undoes is bijective: it is the
inverse of a bijection. This is how an explicit formula for a map is upgraded to bijectivity,
with the isomorphism supplying the inverse. -/
theorem bijective_of_hom_val_app_comp {C : Type u₁} [Category.{v₁} C]
    {JJ : GrothendieckTopology C} {Rg : Sheaf JJ RingCat.{u}} {A B : SheafOfModules.{u} Rg}
    (e : A ≅ B) (W : Cᵒᵖ) (m : B.val.obj W → A.val.obj W)
    (hm : ∀ y, e.hom.val.app W (m y) = y) : Function.Bijective m :=
  Function.bijective_iff_has_inverse.mpr
    ⟨fun x ↦ e.hom.val.app W x, hm,
      fun y ↦ injective_hom_val_app e W (hm (e.hom.val.app W y))⟩

/-- The unit of an adjunction followed by the right adjoint's action on the descent of a
morphism is that morphism: one half of the `Equiv` of the adjunction, written as an equation
between morphisms so that it can be evaluated on a section. -/
theorem unit_comp_map_homEquiv_symm {C : Type u₁} [Category.{v₁} C] {D : Type*} [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (X : C) (Y : D) (g : X ⟶ R.obj Y) :
    adj.unit.app X ≫ R.map ((adj.homEquiv X Y).symm g) = g :=
  (adj.homEquiv_unit X Y ((adj.homEquiv X Y).symm g)).symm.trans
    ((adj.homEquiv X Y).apply_symm_apply g)

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules

/-! ### The site of `Proj 𝒮` and its localizations -/

/-- The structure sheaf of `Proj 𝒮` is a sheaf of rings. -/
theorem isSheaf_proj : Presheaf.IsSheaf
    (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj) :=
  Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf
    (ProjectiveSpectrum.Proj.structureSheaf 𝒮)

/-- The structure presheaf of the open subspace `V` of `Proj 𝒮`. -/
abbrev projOverO (V : Opens (ProjectiveSpectrum.top 𝒮)) : (Over V)ᵒᵖ ⥤ CommRingCat.{u} :=
  ((ProjectiveSpectrum.Proj.structureSheaf 𝒮).over V).obj

/-- The structure sheaf of the open subspace `V` of `Proj 𝒮` is a sheaf of rings on the
localized site. -/
theorem isSheaf_projOver (V : Opens (ProjectiveSpectrum.top 𝒮)) :
    Presheaf.IsSheaf ((Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮)).over V)
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf (projOverO 𝒮 V)) :=
  Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf
    ((ProjectiveSpectrum.Proj.structureSheaf 𝒮).over V)

/-- The sheaf of rings of the open subspace `V` of `Proj 𝒮`, in the spelling in which the
section formulas of the tensor product sheaf are stated. -/
abbrev ringOver (V : Opens (ProjectiveSpectrum.top 𝒮)) :
    Sheaf ((Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮)).over V) RingCat.{u} :=
  Stacks.SheafOfModules.TensorSheafification.structureSheaf (projOverO 𝒮 V) (isSheaf_projOver 𝒮 V)

/-- The restriction of a sheaf of modules on `Proj 𝒮` to an open `V`, at the spelling of
`ringOver`. -/
abbrev restrictModule
    (F : SheafOfModules.{u} (Stacks.AlgebraicGeometry.ProjTrivialization.projRingSheaf 𝒮))
    (V : Opens (ProjectiveSpectrum.top 𝒮)) : SheafOfModules.{u} (ringOver 𝒮 V) :=
  F.over V

/-! ### Restriction to an open commutes with the sheafification unit -/

section SheafificationOver

/-- The sheaf of rings of `Proj 𝒮`, written as `CategoryTheory.Sheaf.toRingCat` asks for it. -/
abbrev projRing : Sheaf (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮)) RingCat.{u} :=
  CategoryTheory.Sheaf.toRingCat (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
    (ProjectiveSpectrum.Proj.structureSheaf 𝒮)

/-- `PresheafOfModules.sheafificationOverIso` is the descent, along the sheafification
adjunction of the localized site, of the restriction of the sheafification unit. This is its
definition, recorded so that its value on a section can be computed. -/
theorem sheafificationOverIso_inv_eq (V : Opens (ProjectiveSpectrum.top 𝒮))
    (P : PresheafOfModules.{u} (projRing 𝒮).obj) :
    (PresheafOfModules.sheafificationOverIso
        (Osharp := ProjectiveSpectrum.Proj.structureSheaf 𝒮) V P).inv =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 ((projRing 𝒮).over V).obj)).homEquiv
          ((PresheafOfModules.overRestriction
            (Osharp := ProjectiveSpectrum.Proj.structureSheaf 𝒮) V).obj P)
          (((PresheafOfModules.sheafification (𝟙 (projRing 𝒮).obj)).obj P).over V)).symm
        ((PresheafOfModules.overRestriction
            (Osharp := ProjectiveSpectrum.Proj.structureSheaf 𝒮) V).map
          ((PresheafOfModules.sheafificationAdjunction (𝟙 (projRing 𝒮).obj)).unit.app P)) :=
  rfl

/-- `sheafificationOverIso_inv_val_app` for an arbitrary sheaf of commutative rings `O`. -/
private theorem sheafificationOverIso_inv_val_app_of_sheaf {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] (O : Sheaf J CommRingCat.{u}) (V : C)
    [HasWeakSheafify (J.over V) AddCommGrpCat.{u}]
    [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (P : PresheafOfModules.{u} (CategoryTheory.Sheaf.toRingCat J O).obj) (W : (Over V)ᵒᵖ)
    (z : ((PresheafOfModules.overRestriction (Osharp := O) V).obj P).obj W) :
    (PresheafOfModules.sheafificationOverIso (Osharp := O) V P).inv.val.app W
        (((PresheafOfModules.sheafificationAdjunction
            (𝟙 ((CategoryTheory.Sheaf.toRingCat J O).over V).obj)).unit.app
          ((PresheafOfModules.overRestriction (Osharp := O) V).obj P)).app W z) =
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (CategoryTheory.Sheaf.toRingCat J O).obj)).unit.app P).app (op W.unop.left) z :=
  congrArg (fun φ ↦ φ.app W z)
    (unit_comp_map_homEquiv_symm
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 ((CategoryTheory.Sheaf.toRingCat J O).over V).obj)) _
      (((PresheafOfModules.sheafification (𝟙 (CategoryTheory.Sheaf.toRingCat J O).obj)).obj P).over
        V)
      ((PresheafOfModules.overRestriction (Osharp := O) V).map
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (CategoryTheory.Sheaf.toRingCat J O).obj)).unit.app P)))

/-- **Restriction to an open commutes with the sheafification unit.** The inverse of
`PresheafOfModules.sheafificationOverIso` carries the image of a section under the sheafification
unit of the localized site to the image of that section under the sheafification unit of
`Proj 𝒮`. This is the triangle identity of the sheafification adjunction, read on a section. -/
theorem sheafificationOverIso_inv_val_app (V : Opens (ProjectiveSpectrum.top 𝒮))
    (P : PresheafOfModules.{u} (projRing 𝒮).obj) (W : (Over V)ᵒᵖ)
    (z : ((PresheafOfModules.overRestriction
      (Osharp := ProjectiveSpectrum.Proj.structureSheaf 𝒮) V).obj P).obj W) :
    (PresheafOfModules.sheafificationOverIso
          (Osharp := ProjectiveSpectrum.Proj.structureSheaf 𝒮) V P).inv.val.app W
        (((PresheafOfModules.sheafificationAdjunction
            (𝟙 ((projRing 𝒮).over V).obj)).unit.app
          ((PresheafOfModules.overRestriction
            (Osharp := ProjectiveSpectrum.Proj.structureSheaf 𝒮) V).obj P)).app W z) =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (projRing 𝒮).obj)).unit.app P).app
        (op W.unop.left) z :=
  sheafificationOverIso_inv_val_app_of_sheaf _ V P W z

end SheafificationOver

/-! ### The tensor product and restriction to an open -/

/-- The restriction of `ℱ ⊗ 𝒢` to an open `V` of `Proj 𝒮` is the tensor product, formed on the
localized site, of the restrictions. This is the localization case of Tag 03EL at the site of
`Proj 𝒮`. -/
def tensorOverIso (F G : SheafOfModules.{u}
      (Stacks.AlgebraicGeometry.ProjTrivialization.projRingSheaf 𝒮))
    (V : Opens (ProjectiveSpectrum.top 𝒮)) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj,
        Presheaf.isSheaf_of_isSheaf_comp _ ((ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj)
          (forget₂ CommRingCat RingCat) ((isSheaf_proj 𝒮))⟩).obj (F)).obj (G))).over V ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(projOverO 𝒮 V), Presheaf.isSheaf_of_isSheaf_comp _ ((projOverO 𝒮 V))
          (forget₂ CommRingCat RingCat) ((isSheaf_projOver 𝒮 V))⟩).obj
        ((restrictModule 𝒮 F V))).obj ((restrictModule 𝒮 G V))) :=
  Stacks.SheafOfModules.TensorProduct.tensorSheafOverIso
    (ProjectiveSpectrum.Proj.structureSheaf 𝒮) V F G

/-- The image under the sheafification unit of the pure tensor `t ⊗ s` of two local sections:
a section of the tensor product sheaf on the localized site. -/
def tensorSection {V : Opens (ProjectiveSpectrum.top 𝒮)}
    (A B : SheafOfModules.{u} (ringOver 𝒮 V)) (W : (Over V)ᵒᵖ)
    (t : A.val.obj W) (s : B.val.obj W) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(projOverO 𝒮 V), Presheaf.isSheaf_of_isSheaf_comp _ ((projOverO 𝒮 V))
        (forget₂ CommRingCat RingCat) ((isSheaf_projOver 𝒮 V))⟩).obj (A)).obj (B))).val.obj W :=
  (Stacks.SheafOfModules.TensorSheafification.toSheafify (projOverO 𝒮 V) (isSheaf_projOver 𝒮 V)
      (A.val ⊗ B.val)).app W (t ⊗ₜ[(projOverO 𝒮 V).obj W] s)

variable {f : S} {d : ℕ}

/-! ### Dividing by the trivializing section -/

/-- The trivialization of `𝒪(nd)` on `D₊(f)`, spelled with `SheafOfModules.unit`. -/
def trivIso (hf : f ∈ 𝒮 d) (n : ℤ) :
    restrictModule 𝒮 (twistingSheaf 𝒮 (n * d)) (ProjectiveSpectrum.basicOpen 𝒮 f) ≅
      SheafOfModules.unit (ringOver 𝒮 (ProjectiveSpectrum.basicOpen 𝒮 f)) :=
  Stacks.AlgebraicGeometry.ProjTrivialization.twistingSheafOverBasicOpenIsoUnit 𝒮 hf n

/-- The coordinate of a local section of `𝒪(nd)` over `W ⊆ D₊(f)` in the trivialization by the
section `f ^ n`: the unique section of the structure sheaf whose product with `f ^ n` is the
given section. -/
def trivCoord (hf : f ∈ 𝒮 d) (n : ℤ)
    (W : (Over (ProjectiveSpectrum.basicOpen 𝒮 f))ᵒᵖ)
    (s : (restrictModule 𝒮 (twistingSheaf 𝒮 (n * d))
      (ProjectiveSpectrum.basicOpen 𝒮 f)).val.obj W) :
    (ringOver 𝒮 (ProjectiveSpectrum.basicOpen 𝒮 f)).obj.obj W :=
  (trivIso 𝒮 hf n).hom.val.app W s

/-- The trivializing section of `𝒪(nd)` over an open `W ⊆ D₊(f)`: the section of coordinate `1`,
which `trivSection_eq` identifies with `f ^ n`. -/
def trivSection (hf : f ∈ 𝒮 d) (n : ℤ)
    (W : (Over (ProjectiveSpectrum.basicOpen 𝒮 f))ᵒᵖ) :
    (restrictModule 𝒮 (twistingSheaf 𝒮 (n * d))
      (ProjectiveSpectrum.basicOpen 𝒮 f)).val.obj W :=
  (trivIso 𝒮 hf n).inv.val.app W
    (1 : (ringOver 𝒮 (ProjectiveSpectrum.basicOpen 𝒮 f)).obj.obj W)

/-- The trivializing section has coordinate `1`. -/
theorem trivCoord_trivSection (hf : f ∈ 𝒮 d) (n : ℤ)
    (W : (Over (ProjectiveSpectrum.basicOpen 𝒮 f))ᵒᵖ) :
    trivCoord 𝒮 hf n W (trivSection 𝒮 hf n W) = 1 :=
  Stacks.SheafOfModules.hom_val_app_inv_val_app (trivIso 𝒮 hf n) W
    (1 : (ringOver 𝒮 (ProjectiveSpectrum.basicOpen 𝒮 f)).obj.obj W)

/-- The trivializing section is `f ^ n`: the inverse trivialization is multiplication by
`Stacks.AlgebraicGeometry.ProjTrivialization.trivializingSection`, so its value at `1` is that
section. -/
theorem trivSection_eq (hf : f ∈ 𝒮 d) (n : ℤ)
    (W : (Over (ProjectiveSpectrum.basicOpen 𝒮 f))ᵒᵖ) :
    trivSection 𝒮 hf n W =
      Stacks.AlgebraicGeometry.ProjTrivialization.trivializingSection 𝒮 hf n
        (leOfHom W.unop.hom) :=
  one_smul ((ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op W.unop.left))
    (Stacks.AlgebraicGeometry.ProjTrivialization.trivializingSection 𝒮 hf n
      (leOfHom W.unop.hom))

/-- **Division by the trivializing section**, on the localized site: the tensor product of `ℱ`
with the trivialized `𝒪(nd)`, read through the right unit constraint, is `ℱ`. -/
def divTrivIso (hf : f ∈ 𝒮 d) (n : ℤ)
    (F : SheafOfModules.{u} (Stacks.AlgebraicGeometry.ProjTrivialization.projRingSheaf 𝒮)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(projOverO 𝒮 (ProjectiveSpectrum.basicOpen 𝒮 f)),
        Presheaf.isSheaf_of_isSheaf_comp _ ((projOverO 𝒮 (ProjectiveSpectrum.basicOpen 𝒮 f)))
          (forget₂ CommRingCat RingCat)
          ((isSheaf_projOver 𝒮 (ProjectiveSpectrum.basicOpen 𝒮 f)))⟩).obj
        ((restrictModule 𝒮 F (ProjectiveSpectrum.basicOpen 𝒮 f)))).obj
        ((restrictModule 𝒮 (twistingSheaf 𝒮 (n * d)) (ProjectiveSpectrum.basicOpen 𝒮 f)))) ≅
      restrictModule 𝒮 F (ProjectiveSpectrum.basicOpen 𝒮 f) :=
  Stacks.SheafOfModules.TensorPower.tensorSheafMapIso
      (projOverO 𝒮 (ProjectiveSpectrum.basicOpen 𝒮 f))
      (isSheaf_projOver 𝒮 (ProjectiveSpectrum.basicOpen 𝒮 f))
      (Iso.refl (restrictModule 𝒮 F (ProjectiveSpectrum.basicOpen 𝒮 f))) (trivIso 𝒮 hf n) ≪≫
    Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso
      (projOverO 𝒮 (ProjectiveSpectrum.basicOpen 𝒮 f))
      (isSheaf_projOver 𝒮 (ProjectiveSpectrum.basicOpen 𝒮 f))
      (restrictModule 𝒮 F (ProjectiveSpectrum.basicOpen 𝒮 f))

/-- **The restriction to `D₊(f)` of the twist `ℱ(nd)` is the restriction of `ℱ`**, for an
arbitrary sheaf of modules `ℱ` on `Proj 𝒮`. -/
def twistRestrictIso (hf : f ∈ 𝒮 d) (n : ℤ)
    (F : SheafOfModules.{u} (Stacks.AlgebraicGeometry.ProjTrivialization.projRingSheaf 𝒮)) :
    (twistSheafOfModules 𝒮 F (n * d)).over (ProjectiveSpectrum.basicOpen 𝒮 f) ≅
      restrictModule 𝒮 F (ProjectiveSpectrum.basicOpen 𝒮 f) :=
  tensorOverIso 𝒮 F (twistingSheaf 𝒮 (n * d)) (ProjectiveSpectrum.basicOpen 𝒮 f) ≪≫
    divTrivIso 𝒮 hf n F

/-- Dividing by the trivializing section: the composite of the trivialization with the right
unit constraint sends the local pure tensor `t ⊗ s` to the scalar multiple of `t` by the
coordinate of `s`. -/
theorem divTrivIso_hom_app_tensorSection (hf : f ∈ 𝒮 d) (n : ℤ)
    (F : SheafOfModules.{u} (Stacks.AlgebraicGeometry.ProjTrivialization.projRingSheaf 𝒮))
    (W : (Over (ProjectiveSpectrum.basicOpen 𝒮 f))ᵒᵖ)
    (t : (restrictModule 𝒮 F (ProjectiveSpectrum.basicOpen 𝒮 f)).val.obj W)
    (s : (restrictModule 𝒮 (twistingSheaf 𝒮 (n * d))
      (ProjectiveSpectrum.basicOpen 𝒮 f)).val.obj W) :
    (divTrivIso 𝒮 hf n F).hom.val.app W
        (tensorSection 𝒮 (restrictModule 𝒮 F (ProjectiveSpectrum.basicOpen 𝒮 f))
          (restrictModule 𝒮 (twistingSheaf 𝒮 (n * d))
            (ProjectiveSpectrum.basicOpen 𝒮 f)) W t s) =
      trivCoord 𝒮 hf n W s • t := by
  refine Eq.trans (congrArg (fun z ↦ (Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso
        (projOverO 𝒮 (ProjectiveSpectrum.basicOpen 𝒮 f))
        (isSheaf_projOver 𝒮 (ProjectiveSpectrum.basicOpen 𝒮 f))
        (restrictModule 𝒮 F (ProjectiveSpectrum.basicOpen 𝒮 f))).hom.val.app W z)
      (Stacks.SheafOfModules.sheafify_map_toSheafify_app
        (projOverO 𝒮 (ProjectiveSpectrum.basicOpen 𝒮 f))
        (isSheaf_projOver 𝒮 (ProjectiveSpectrum.basicOpen 𝒮 f))
        ((SheafOfModules.forget _).map
            (Iso.refl (restrictModule 𝒮 F (ProjectiveSpectrum.basicOpen 𝒮 f))).hom ⊗ₘ
          (SheafOfModules.forget _).map (trivIso 𝒮 hf n).hom) W
        (t ⊗ₜ[(projOverO 𝒮 (ProjectiveSpectrum.basicOpen 𝒮 f)).obj W] s))) ?_
  exact Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso_hom_app
    (projOverO 𝒮 (ProjectiveSpectrum.basicOpen 𝒮 f))
    (isSheaf_projOver 𝒮 (ProjectiveSpectrum.basicOpen 𝒮 f))
    (restrictModule 𝒮 F (ProjectiveSpectrum.basicOpen 𝒮 f)) W t _

/-- **Dividing `t ⊗ f ^ n` by the trivializing section gives `t` back.** This is the formula
with the coordinate of the trivializing section evaluated, and it is the only place where the
scalar action on sections is manipulated; every use below instantiates it. -/
theorem divTrivIso_hom_app_tensorSection_trivSection (hf : f ∈ 𝒮 d) (n : ℤ)
    (F : SheafOfModules.{u} (Stacks.AlgebraicGeometry.ProjTrivialization.projRingSheaf 𝒮))
    (W : (Over (ProjectiveSpectrum.basicOpen 𝒮 f))ᵒᵖ)
    (t : (restrictModule 𝒮 F (ProjectiveSpectrum.basicOpen 𝒮 f)).val.obj W) :
    (divTrivIso 𝒮 hf n F).hom.val.app W
        (tensorSection 𝒮 (restrictModule 𝒮 F (ProjectiveSpectrum.basicOpen 𝒮 f))
          (restrictModule 𝒮 (twistingSheaf 𝒮 (n * d))
            (ProjectiveSpectrum.basicOpen 𝒮 f)) W t (trivSection 𝒮 hf n W)) = t :=
  (divTrivIso_hom_app_tensorSection 𝒮 hf n F W t (trivSection 𝒮 hf n W)).trans
    ((congrArg (fun r ↦ r • t) (trivCoord_trivSection 𝒮 hf n W)).trans (one_smul _ t))

/-- **Multiplication by the trivializing section is bijective on the sections over every open
inside `D₊(f)`**, on the localized site. -/
theorem bijective_tensorSection_trivSection (hf : f ∈ 𝒮 d) (n : ℤ)
    (F : SheafOfModules.{u} (Stacks.AlgebraicGeometry.ProjTrivialization.projRingSheaf 𝒮))
    (W : (Over (ProjectiveSpectrum.basicOpen 𝒮 f))ᵒᵖ) :
    Function.Bijective fun t : (restrictModule 𝒮 F (ProjectiveSpectrum.basicOpen 𝒮 f)).val.obj W ↦
      tensorSection 𝒮 (restrictModule 𝒮 F (ProjectiveSpectrum.basicOpen 𝒮 f))
        (restrictModule 𝒮 (twistingSheaf 𝒮 (n * d)) (ProjectiveSpectrum.basicOpen 𝒮 f)) W t
        (trivSection 𝒮 hf n W) :=
  bijective_of_hom_val_app_comp (divTrivIso 𝒮 hf n F) W _
    (divTrivIso_hom_app_tensorSection_trivSection 𝒮 hf n F W)

/-- **The sections of `ℱ(nd)` over an open `W ⊆ D₊(f)` are the sections of `ℱ` over `W`**, for
an arbitrary sheaf of modules `ℱ` on `Proj 𝒮`. -/
theorem bijective_twistRestrictIso_app (hf : f ∈ 𝒮 d) (n : ℤ)
    (F : SheafOfModules.{u} (Stacks.AlgebraicGeometry.ProjTrivialization.projRingSheaf 𝒮))
    {W : Opens (ProjectiveSpectrum.top 𝒮)} (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f) :
    Function.Bijective fun x : (twistSheafOfModules 𝒮 F (n * d)).val.obj (op W) ↦
      ((twistRestrictIso 𝒮 hf n F).hom.val.app (op (Over.mk (homOfLE hW))) x :
        F.val.obj (op W)) :=
  bijective_hom_val_app (twistRestrictIso 𝒮 hf n F) (op (Over.mk (homOfLE hW)))

/-! ### Multiplication by `f ^ n` on the sections over an open inside `D₊(f)` -/

/-- **Multiplication by `f ^ n`** on the sections over an open `W ⊆ D₊(f)`: the local pure
tensor `t ⊗ f ^ n`, a section of the twist `ℱ(nd)` over `W`. -/
def mulTrivSection (hf : f ∈ 𝒮 d) (n : ℤ)
    (F : SheafOfModules.{u} (Stacks.AlgebraicGeometry.ProjTrivialization.projRingSheaf 𝒮))
    {W : Opens (ProjectiveSpectrum.top 𝒮)} (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (t : F.val.obj (op W)) : (twistSheafOfModules 𝒮 F (n * d)).val.obj (op W) :=
  (Stacks.SheafOfModules.TensorSheafification.toSheafify
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj (isSheaf_proj 𝒮)
      (F.val ⊗ (twistingSheaf 𝒮 (n * d)).val)).app (op W)
    (t ⊗ₜ[(ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op W)]
      Stacks.AlgebraicGeometry.ProjTrivialization.trivializingSection 𝒮 hf n hW)

/-- Multiplication by `f ^ n` on `Proj 𝒮` and on the localized site at `D₊(f)` agree under
`tensorOverIso`: restriction to an open commutes with the sheafification unit, and the pointwise
comparison of the two tensor presheaves is the identity. -/
theorem tensorOverIso_inv_val_app_tensorSection (hf : f ∈ 𝒮 d) (n : ℤ)
    (F : SheafOfModules.{u} (Stacks.AlgebraicGeometry.ProjTrivialization.projRingSheaf 𝒮))
    {W : Opens (ProjectiveSpectrum.top 𝒮)} (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (t : F.val.obj (op W)) :
    (tensorOverIso 𝒮 F (twistingSheaf 𝒮 (n * d))
          (ProjectiveSpectrum.basicOpen 𝒮 f)).inv.val.app (op (Over.mk (homOfLE hW)))
        (tensorSection 𝒮 (restrictModule 𝒮 F (ProjectiveSpectrum.basicOpen 𝒮 f))
          (restrictModule 𝒮 (twistingSheaf 𝒮 (n * d)) (ProjectiveSpectrum.basicOpen 𝒮 f))
          (op (Over.mk (homOfLE hW))) t
          (trivSection 𝒮 hf n (op (Over.mk (homOfLE hW))))) =
      mulTrivSection 𝒮 hf n F hW t := by
  have generic : ∀ {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
      [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
      [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
      [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
      [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
      [∀ X : C, (J.over X).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
      (O : CategoryTheory.Sheaf J CommRingCat.{u}) (V : C)
      (F G : SheafOfModules.{u} (structureSheaf O.obj
        (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf O)))
      (W' : (Over V)ᵒᵖ)
      (x : (PresheafOfModules.tensorObj (O := (O.over V).obj) (F.over V).val
        (G.over V).val).obj W'),
      (Stacks.SheafOfModules.TensorProduct.tensorSheafOverIso O V F G).inv.val.app W'
          ((toSheafify (O.over V).obj
            (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf (O.over V))
            (MonoidalCategoryStruct.tensorObj
              (self := (Stacks.SheafOfModules.monoidalCategoryPresheafOfModules (O.over V).obj
                (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf
                  (O.over V))).toMonoidalCategoryStruct)
              (F.over V).val (G.over V).val)).app W' x) =
        ((PresheafOfModules.sheafificationAdjunction
            (𝟙 (CategoryTheory.Sheaf.toRingCat J O).obj)).unit.app
          (PresheafOfModules.tensorObj (O := O.obj) F.val G.val)).app (op W'.unop.left) x := by
    intro C _ J _ _ _ _ _ _ O V F G W' x
    have h1 : (Stacks.SheafOfModules.TensorProduct.tensorSheafOverIso O V F G).inv =
        (PresheafOfModules.sheafification
            (𝟙 ((CategoryTheory.Sheaf.toRingCat J O).over V).obj)).map
            (Stacks.SheafOfModules.TensorProduct.overRestrictionTensorPresheafIso O V F.val
              G.val).inv ≫
          (PresheafOfModules.sheafificationOverIso (Osharp := O) V
            (PresheafOfModules.tensorObj (O := O.obj) F.val G.val)).inv := rfl
    rw [h1]
    refine (Stacks.SheafOfModules.comp_val_app_apply _ _ _ _).trans ?_
    have hnat := congrArg (fun φ ↦ φ.app W' x)
      ((PresheafOfModules.sheafificationAdjunction
          (𝟙 ((CategoryTheory.Sheaf.toRingCat J O).over V).obj)).unit.naturality
        (Stacks.SheafOfModules.TensorProduct.overRestrictionTensorPresheafIso O V F.val
          G.val).inv)
    simp only [PresheafOfModules.comp_app] at hnat
    refine (congrArg (fun z ↦ (PresheafOfModules.sheafificationOverIso (Osharp := O) V
      (PresheafOfModules.tensorObj (O := O.obj) F.val G.val)).inv.val.app W' z)
      hnat.symm).trans ?_
    exact sheafificationOverIso_inv_val_app_of_sheaf O V _ W' _
  refine (generic (ProjectiveSpectrum.Proj.structureSheaf 𝒮) (ProjectiveSpectrum.basicOpen 𝒮 f)
    F (twistingSheaf 𝒮 (n * d)) (op (Over.mk (homOfLE hW)))
    (t ⊗ₜ[(projOverO 𝒮 (ProjectiveSpectrum.basicOpen 𝒮 f)).obj (op (Over.mk (homOfLE hW)))]
      trivSection 𝒮 hf n (op (Over.mk (homOfLE hW))))).trans ?_
  exact congrArg (fun y ↦
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (projRing 𝒮).obj)).unit.app
      (PresheafOfModules.tensorObj (O := (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj)
        F.val (twistingSheaf 𝒮 (n * d)).val)).app (op W)
      (t ⊗ₜ[(ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op W)] y))
    (trivSection_eq 𝒮 hf n (op (Over.mk (homOfLE hW))))

/-- **Dividing `t ⊗ f ^ n` by the trivializing section gives `t` back**, on `Proj 𝒮`: the
isomorphism `ℱ(nd)|_{D₊(f)} ≅ ℱ|_{D₊(f)}` undoes multiplication by `f ^ n` on the sections over
an open `W ⊆ D₊(f)`. -/
theorem twistRestrictIso_hom_val_app_mulTrivSection (hf : f ∈ 𝒮 d) (n : ℤ)
    (F : SheafOfModules.{u} (Stacks.AlgebraicGeometry.ProjTrivialization.projRingSheaf 𝒮))
    {W : Opens (ProjectiveSpectrum.top 𝒮)} (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (t : F.val.obj (op W)) :
    (twistRestrictIso 𝒮 hf n F).hom.val.app (op (Over.mk (homOfLE hW)))
        (mulTrivSection 𝒮 hf n F hW t) = t := by
  refine Eq.trans (congrArg (fun z ↦ (divTrivIso 𝒮 hf n F).hom.val.app
      (op (Over.mk (homOfLE hW)))
      ((tensorOverIso 𝒮 F (twistingSheaf 𝒮 (n * d))
        (ProjectiveSpectrum.basicOpen 𝒮 f)).hom.val.app (op (Over.mk (homOfLE hW))) z))
    (tensorOverIso_inv_val_app_tensorSection 𝒮 hf n F hW t).symm) ?_
  refine Eq.trans (congrArg (fun z ↦ (divTrivIso 𝒮 hf n F).hom.val.app
      (op (Over.mk (homOfLE hW))) z)
    (Stacks.SheafOfModules.hom_val_app_inv_val_app
      (tensorOverIso 𝒮 F (twistingSheaf 𝒮 (n * d)) (ProjectiveSpectrum.basicOpen 𝒮 f))
      (op (Over.mk (homOfLE hW))) _)) ?_
  exact divTrivIso_hom_app_tensorSection_trivSection 𝒮 hf n F (op (Over.mk (homOfLE hW))) t

/-- **Multiplication by `f ^ n` is a bijection `Γ(W, ℱ) → Γ(W, ℱ(nd))` for every open
`W ⊆ D₊(f)` and every sheaf of `𝒪_{Proj 𝒮}`-modules `ℱ`.**

For `ℱ = 𝒪_{Proj 𝒮}` this is
`Stacks.AlgebraicGeometry.ProjTrivialization.bijective_trivializingHom`, Tag 01MS; the content
here is that `ℱ` is arbitrary. The inverse is the map Tag 0B5I's local comparison calls
"division by `f ^ n`". -/
theorem bijective_mulTrivSection (hf : f ∈ 𝒮 d) (n : ℤ)
    (F : SheafOfModules.{u} (Stacks.AlgebraicGeometry.ProjTrivialization.projRingSheaf 𝒮))
    {W : Opens (ProjectiveSpectrum.top 𝒮)} (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f) :
    Function.Bijective (mulTrivSection 𝒮 hf n F hW) :=
  bijective_of_hom_val_app_comp (twistRestrictIso 𝒮 hf n F) (op (Over.mk (homOfLE hW)))
    (mulTrivSection 𝒮 hf n F hW)
    (twistRestrictIso_hom_val_app_mulTrivSection 𝒮 hf n F hW)

end Stacks.AlgebraicGeometry.ProjTwistRestriction

end
