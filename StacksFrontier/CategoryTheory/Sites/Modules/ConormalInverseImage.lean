module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageRestrictScalars
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KernelIdealSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposInverseImageExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackLocalGeneration
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalIdealRestriction
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoiRing

/-!
# The inverse image of a conormal sheaf

Let `f : Sh(C) ⟶ Sh(D)` be a morphism of topoi and `φ : 𝒜 ⟶ ℬ` a locally surjective
homomorphism of sheaves of commutative rings on `D`, with kernel `ℐ`. The inverse image of the
conormal sheaf `ℐ/ℐ²` of `φ` is the conormal sheaf of the inverse-image homomorphism
`f⁻¹φ : f⁻¹𝒜 ⟶ f⁻¹ℬ`. This is the degree `-1` term of the identification
`f⁻¹ NL_{ℬ/𝒜} = NL_{f⁻¹ℬ/f⁻¹𝒜}` of [Stacks 08TZ].

## Main definitions

* `Stacks.Sites.Conormal.conormalHomEquiv`: morphisms of sheaves of `ℬ`-modules out of `ℐ/ℐ²`
  are morphisms of sheaves of `𝒜`-modules out of `ℐ` with scalars restricted along `φ`.
* `Stacks.Sites.Conormal.conormalModule`: the conormal sheaf, read as a sheaf of modules over
  the sheaf of rings underlying `ℬ`.
* `Stacks.Sheaves.RingedToposModules.inverseImageIdealIso`: the inverse image of the kernel
  ideal is the kernel ideal of the inverse image, `f⁻¹ℐ ≅ ℐ'`.
* `Stacks.Sheaves.RingedToposModules.inverseImageConormalHomEquiv`: the inverse image of
  `ℐ/ℐ²` and the conormal sheaf of `f⁻¹φ` have the same morphisms into every sheaf of
  `f⁻¹ℬ`-modules.
* `Stacks.Sheaves.RingedToposModules.inverseImageConormalIso`: the resulting identification
  `f⁻¹(ℐ/ℐ²) ≅ ℐ'/(ℐ')²`.

## Main results

* `Stacks.Sheaves.RingedToposModules.naturalHomEquiv_inverseImageConormalHomEquiv`: that
  bijection is natural in the sheaf of `f⁻¹ℬ`-modules, which is what turns it into an
  isomorphism by `Stacks.Sheaves.RingedToposModules.isoOfNaturalHomEquiv`.
* `Stacks.Sites.Conormal.conormalModuleHomEquivOf_app_conormalClass`: the universal property of
  the conormal sheaf, read on sections, at an arbitrary spelling of the ring map underlying the
  presentation.
* `Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_inverseImageIdealAdjunctionEquiv`
  and `Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_inverseImageIdealIso_inv_comp`:
  the two steps of the bijection that involve the inverse image, read on underlying sheaves of
  sets, where they are the hom-set bijection of `f⁻¹ ⊣ f_*` and the identity.

## Implementation notes

The argument is by universal properties throughout; a general topos has no points, so no
stalkwise reasoning is available. Morphisms out of the inverse image are read through the
adjunction of [Stacks 03D3], where the universal property of the conormal sheaf applies, and
the two restrictions of scalars are exchanged with the direct image by
`Stacks.Sheaves.RingedToposModules.directImageModulesRestrictScalarsIso`.

Each step of the bijection, and each initial segment of the steps, is a separate declaration
stated at the spelling of the lemma it instantiates. Two reasons. The conormal sheaf is
a sheaf of modules over the sheaf of rings underlying `ℬ`, which has two definitionally equal
spellings, so the conormal sheaf is pinned to one of them by
`Stacks.Sites.Conormal.conormalModule`, a semireducible definition, and every statement below
uses that spelling; composing the steps across the two spellings re-checks the defeq at every
intermediate type. And the identification is taken along an arbitrary morphism of sheaves of
rings equal to the one underlying `φ` (`Stacks.Sites.Conormal.conormalHomEquivOf`), so that no
`eqToHom` bridging the two spellings of `f⁻¹φ` appears in any composition.

Naturality of the whole bijection is stated as
`Stacks.Sheaves.RingedToposModules.NaturalHomEquiv` applied to the bijection rather than as the
equation it unfolds to, because elaborating that equation applies the outermost
`Equiv.trans` to a morphism, and exposing its underlying function forces the transport inside
`Stacks.Sites.Conormal.conormalHomEquivOf` to be unfolded.

## References

* [Stacks Project, Tag 08TZ](https://stacks.math.columbia.edu/tag/08TZ)
* [Stacks Project, Tag 08TW](https://stacks.math.columbia.edu/tag/08TW), the naive cotangent
  complex.
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3), the adjunction for
  sheaves of modules along a morphism of topoi.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.Sites.Conormal

universe t v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A B : Sheaf J CommRingCat.{max u v t}} (φ : A ⟶ B)

/-- The morphism of sheaves of rings underlying a homomorphism of sheaves of commutative
rings. -/
noncomputable abbrev presentationRingHom :
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v t} (J := J)) A ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v t} (J := J)) B :=
  (Stacks.forgetCommRingSheaf.{v, u, max u v t} J).map φ

section Ideal

variable (α : (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v t} (J := J)) A ⟶
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v t} (J := J)) B)

/-- A morphism `α : 𝒜 ⟶ ℬ` of sheaves of rings, read as a morphism of sheaves of `𝒜`-modules
into `ℬ` with its scalars restricted along `α`. -/
noncomputable abbrev presentationModuleHom :
    SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v t} (J := J)) A) ⟶
      (SheafOfModules.restrictScalars α).obj
        (SheafOfModules.unit
          ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v t} (J := J)) B)) :=
  SheafOfModules.unitToRestrictScalarsObjUnit α

/-- The kernel `ℐ = Ker α` of a morphism of sheaves of rings, as a sheaf of `𝒜`-modules. Its
sections over an object of the site are the kernel ideal of `α` there. -/
noncomputable abbrev idealSheaf :
    SheafOfModules.{max u v t}
      ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v t} (J := J)) A) :=
  SheafOfModules.kerObj (presentationModuleHom.{t, v, u} J α)

section Underlying

variable [J.HasSheafCompose (forget AddCommGrpCat.{max u v t})]

/-- On underlying sheaves of sets, a morphism of sheaves of rings read as a morphism of sheaves
of modules is that morphism. -/
lemma moduleSheafFunctor_map_presentationModuleHom :
    (Sheaf.moduleSheafFunctor
          ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v t} (J := J)) A)).map
        (presentationModuleHom.{t, v, u} J α) =
      (sheafCompose J (forget RingCat.{max u v t})).map α :=
  rfl

end Underlying

end Ideal

/-! ## Maps out of the conormal sheaf -/

section Canonical

/-- A local section of `𝒜` lies in the kernel sheaf of the presentation exactly when it lies in
the kernel ideal. -/
lemma mem_idealSheaf_iff (U : Cᵒᵖ) (a : A.obj.obj U) :
    a ∈ (SheafOfModules.kerSubmodule
        (presentationModuleHom.{t, v, u} J (presentationRingHom.{t, v, u} J φ))).obj U ↔
      a ∈ kernelIdeal φ.hom U :=
  Iff.rfl

/-- A local section of the kernel ideal, read as a local section of the kernel sheaf. -/
def idealSection (U : Cᵒᵖ) (g : ↥(kernelIdeal φ.hom U)) :
    ↥((idealSheaf.{t, v, u} J (presentationRingHom.{t, v, u} J φ)).val.obj U) :=
  ⟨g.1, (mem_idealSheaf_iff.{t, v, u} J φ U g.1).mpr g.2⟩

/-- A local section of the kernel sheaf, read as a local section of the kernel ideal. -/
def sectionOfIdealSheaf (U : Cᵒᵖ)
    (g : ↥((idealSheaf.{t, v, u} J (presentationRingHom.{t, v, u} J φ)).val.obj U)) :
    ↥(kernelIdeal φ.hom U) :=
  ⟨g.1, (mem_idealSheaf_iff.{t, v, u} J φ U g.1).mp g.2⟩

variable [Presheaf.IsLocallySurjective J φ.hom]
  (G : SheafOfModules.{max u v t}
    ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v t} (J := J)) B))

/-- A morphism of sheaves of `𝒜`-modules out of the kernel sheaf, read as a restriction datum
for the presentation. -/
noncomputable def idealRestrictionOfHom
    (β : idealSheaf.{t, v, u} J (presentationRingHom.{t, v, u} J φ) ⟶
      (SheafOfModules.restrictScalars (presentationRingHom.{t, v, u} J φ)).obj G) :
    IdealRestriction.{v, u, max u v t, t} φ G where
  app U := AddMonoidHom.mk' (fun g ↦ β.val.app U (idealSection.{t, v, u} J φ U g))
    (fun _ _ ↦ map_add (β.val.app U).hom _ _)
  app_smul U r g := (β.val.app U).hom.map_smul r (idealSection.{t, v, u} J φ U g)
  app_map {U _} f g := PresheafOfModules.naturality_apply β.val f
    (idealSection.{t, v, u} J φ U g)

/-- A restriction datum for the presentation, read as a morphism of sheaves of `𝒜`-modules out
of the kernel sheaf. -/
noncomputable def homOfIdealRestriction (ρ : IdealRestriction.{v, u, max u v t, t} φ G) :
    idealSheaf.{t, v, u} J (presentationRingHom.{t, v, u} J φ) ⟶
      (SheafOfModules.restrictScalars (presentationRingHom.{t, v, u} J φ)).obj G where
  val.app U := ModuleCat.ofHom
    (X := (idealSheaf.{t, v, u} J (presentationRingHom.{t, v, u} J φ)).val.obj U)
    (Y := ((SheafOfModules.restrictScalars
      (presentationRingHom.{t, v, u} J φ)).obj G).val.obj U)
    { toFun := fun g ↦ ρ.app U (sectionOfIdealSheaf.{t, v, u} J φ U g)
      map_add' := fun g h ↦ (ρ.app U).map_add (sectionOfIdealSheaf.{t, v, u} J φ U g)
        (sectionOfIdealSheaf.{t, v, u} J φ U h)
      map_smul' := fun r g ↦ ρ.app_smul U r (sectionOfIdealSheaf.{t, v, u} J φ U g) }
  val.naturality {U _} f := ModuleCat.hom_ext (LinearMap.ext fun g ↦
    ρ.app_map f (sectionOfIdealSheaf.{t, v, u} J φ U g))

/-- A morphism out of the conormal sheaf, read as a restriction datum for the presentation:
its value on the conormal class of a local section of the kernel ideal. -/
noncomputable def conormalRestriction (α : conormalSheaf.{v, u, max u v t, t} J A B φ ⟶ G) :
    IdealRestriction.{v, u, max u v t, t} φ G where
  app U := AddMonoidHom.mk'
    (fun g ↦ α.val.app U (toAssociatedModule.{v, u, max u v t, t} J A B φ
      (conormalPresheaf φ.hom) U ((kernelIdeal φ.hom U).toCotangent g)))
    (fun g h ↦ (congrArg (fun y ↦ α.val.app U y)
        (toAssociatedModule_add.{v, u, max u v t, t} J A B φ (conormalPresheaf φ.hom) U
          ((kernelIdeal φ.hom U).toCotangent g)
          ((kernelIdeal φ.hom U).toCotangent h))).trans
      (map_add (α.val.app U).hom _ _))
  app_smul U r g := (congrArg (fun y ↦ α.val.app U y)
      (toAssociatedModule_smul.{v, u, max u v t, t} J A B φ (conormalPresheaf φ.hom) U
        (Ideal.Quotient.mk _ r) ((kernelIdeal φ.hom U).toCotangent g))).trans
    ((α.val.app U).hom.map_smul _ _)
  app_map {U _} f g := (congrArg (fun y ↦ α.val.app _ y)
      (toAssociatedModule_map.{v, u, max u v t, t} J A B φ (conormalPresheaf φ.hom) f
        ((kernelIdeal φ.hom U).toCotangent g))).trans
    (PresheafOfModules.naturality_apply α.val f _)

/-- **Maps out of the conormal sheaf are maps out of the kernel ideal.** A morphism of sheaves
of `ℬ`-modules `ℐ/ℐ² ⟶ 𝒢` is the same thing as a morphism of sheaves of `𝒜`-modules from `ℐ`
to `𝒢` with its scalars restricted along the presentation: a local section of `ℐ` acts as zero
on `𝒢`, so an `𝒜`-linear map out of `ℐ` annihilates `ℐ²`. -/
noncomputable def conormalHomEquiv :
    (conormalSheaf.{v, u, max u v t, t} J A B φ ⟶ G) ≃
      (idealSheaf.{t, v, u} J (presentationRingHom.{t, v, u} J φ) ⟶
        (SheafOfModules.restrictScalars (presentationRingHom.{t, v, u} J φ)).obj G) where
  toFun α := homOfIdealRestriction.{t, v, u} J φ G (conormalRestriction.{t, v, u} J φ G α)
  invFun β := conormalDesc.{v, u, max u v t, t} φ G (idealRestrictionOfHom.{t, v, u} J φ G β)
  left_inv _ := conormal_hom_ext.{v, u, max u v t, t} φ G fun U x ↦
    conormalDesc_toAssociatedModule.{v, u, max u v t, t} φ G _ U x
  right_inv _ := SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U ↦
    ModuleCat.hom_ext (LinearMap.ext fun g ↦
      conormalDesc_toAssociatedModule.{v, u, max u v t, t} φ G _ U
        (sectionOfIdealSheaf.{t, v, u} J φ U g)))

end Canonical

/-! ## The identification at an arbitrary spelling of the ring map -/

section Transport

variable [Presheaf.IsLocallySurjective J φ.hom]

/-- The conormal sheaf `ℐ/ℐ²` of the presentation, read as a sheaf of modules over the sheaf of
rings underlying `ℬ`. -/
noncomputable def conormalModule :
    SheafOfModules.{max u v t}
      ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v t} (J := J)) B) :=
  conormalSheaf.{v, u, max u v t, t} J A B φ

variable (α : (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v t} (J := J)) A ⟶
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v t} (J := J)) B)
  (hα : α = presentationRingHom.{t, v, u} J φ)

/-- `Stacks.Sites.Conormal.conormalHomEquiv` at a morphism of sheaves of rings presented as an
arbitrary term equal to the one underlying the presentation. -/
noncomputable def conormalHomEquivOf
    (G : SheafOfModules.{max u v t}
      ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v t} (J := J)) B)) :
    (conormalSheaf.{v, u, max u v t, t} J A B φ ⟶ G) ≃
      (idealSheaf.{t, v, u} J α ⟶ (SheafOfModules.restrictScalars α).obj G) := by
  subst hα
  exact conormalHomEquiv.{t, v, u} J φ G

/-- The identification of maps out of the conormal sheaf with maps out of the kernel ideal is
natural in the sheaf of `ℬ`-modules. -/
lemma conormalHomEquivOf_comp
    (G G' : SheafOfModules.{max u v t}
      ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v t} (J := J)) B))
    (a : conormalSheaf.{v, u, max u v t, t} J A B φ ⟶ G) (γ : G ⟶ G') :
    conormalHomEquivOf.{t, v, u} J φ α hα G' (a ≫ γ) =
      conormalHomEquivOf.{t, v, u} J φ α hα G a ≫
        (SheafOfModules.restrictScalars α).map γ := by
  subst hα
  exact SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun _ ↦
    ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl))

/-- The inverse identification, of maps out of the kernel ideal with maps out of the conormal
sheaf, is natural in the sheaf of `ℬ`-modules. -/
lemma conormalHomEquivOf_symm_comp
    (G G' : SheafOfModules.{max u v t}
      ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v t} (J := J)) B))
    (b : idealSheaf.{t, v, u} J α ⟶ (SheafOfModules.restrictScalars α).obj G) (γ : G ⟶ G') :
    (conormalHomEquivOf.{t, v, u} J φ α hα G').symm
        (b ≫ (SheafOfModules.restrictScalars α).map γ) =
      (conormalHomEquivOf.{t, v, u} J φ α hα G).symm b ≫ γ := by
  refine (Equiv.symm_apply_eq _).mpr ?_
  rw [conormalHomEquivOf_comp.{t, v, u} J φ α hα G G' _ γ, Equiv.apply_symm_apply]

/-- `Stacks.Sites.Conormal.conormalHomEquivOf` with the conormal sheaf read as a sheaf of
modules over the sheaf of rings underlying `ℬ`. This is the spelling in which the conormal
sheaf and the direct image of a sheaf of modules are modules over the very same sheaf of
rings. -/
noncomputable def conormalModuleHomEquivOf
    (G : SheafOfModules.{max u v t}
      ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v t} (J := J)) B)) :
    (conormalModule.{t, v, u} J φ ⟶ G) ≃
      (idealSheaf.{t, v, u} J α ⟶ (SheafOfModules.restrictScalars α).obj G) :=
  conormalHomEquivOf.{t, v, u} J φ α hα G

/-- The identification of maps out of the conormal sheaf with maps out of the kernel ideal is
natural in the sheaf of `ℬ`-modules. -/
lemma conormalModuleHomEquivOf_comp
    (G G' : SheafOfModules.{max u v t}
      ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v t} (J := J)) B))
    (a : conormalModule.{t, v, u} J φ ⟶ G) (γ : G ⟶ G') :
    conormalModuleHomEquivOf.{t, v, u} J φ α hα G' (a ≫ γ) =
      conormalModuleHomEquivOf.{t, v, u} J φ α hα G a ≫
        (SheafOfModules.restrictScalars α).map γ :=
  conormalHomEquivOf_comp.{t, v, u} J φ α hα G G' a γ

/-- The inverse identification, of maps out of the kernel ideal with maps out of the conormal
sheaf, is natural in the sheaf of `ℬ`-modules. -/
lemma conormalModuleHomEquivOf_symm_comp
    (G G' : SheafOfModules.{max u v t}
      ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v t} (J := J)) B))
    (b : idealSheaf.{t, v, u} J α ⟶ (SheafOfModules.restrictScalars α).obj G) (γ : G ⟶ G') :
    (conormalModuleHomEquivOf.{t, v, u} J φ α hα G').symm
        (b ≫ (SheafOfModules.restrictScalars α).map γ) =
      (conormalModuleHomEquivOf.{t, v, u} J φ α hα G).symm b ≫ γ :=
  conormalHomEquivOf_symm_comp.{t, v, u} J φ α hα G G' b γ

omit [Presheaf.IsLocallySurjective J φ.hom] in
include hα in
/-- A local section of the kernel sheaf of an arbitrary spelling of the ring map underlying
the presentation lies in the kernel ideal of the presentation. -/
lemma coe_mem_kernelIdeal (U : Cᵒᵖ) (g : ↥((idealSheaf.{t, v, u} J α).val.obj U)) :
    (g.1 : A.obj.obj U) ∈ kernelIdeal φ.hom U := by
  subst hα
  exact g.2

/-- **The universal property of the conormal sheaf, read on sections, at an arbitrary spelling
of the ring map underlying the presentation.** The restriction to the kernel sheaf of a
morphism out of the conormal sheaf is its value on conormal classes. This is
`Stacks.Sites.Conormal.conormalHomEquiv` of Stacks 08TS evaluated at a local section, with the
local section of the kernel sheaf and the local section of the kernel ideal presented
independently, so that neither has to be rewritten along the equality of the two spellings. -/
lemma conormalModuleHomEquivOf_app_conormalClass
    (R : Sheaf J CommRingCat.{max u v t}) (c : R ⟶ A)
    (G : SheafOfModules.{max u v t} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v t} B))
    (x : conormalModule.{t, v, u} J φ ⟶ G) (U : Cᵒᵖ)
    (g : ↥((idealSheaf.{t, v, u} J α).val.obj U)) (y : ↥(kernelIdeal φ.hom U))
    (hgy : g.1 = y.1) :
    (conormalModuleHomEquivOf.{t, v, u} J φ α hα G x).val.app U g =
      x.val.app U (conormalClass.{v, u, max u v t, t} J R A B c φ U y) := by
  subst hα
  obtain rfl : g = idealSection.{t, v, u} J φ U y := Subtype.ext hgy
  rfl

end Transport

end Stacks.Sites.Conormal

/-! ## The inverse image of the kernel ideal -/

namespace Stacks.Sheaves.RingedToposModules

open CategoryTheory.Limits Stacks.Sites.Conormal
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

section Reflect

universe v₁ u₁

/-- Post-composition with an isomorphism, as a bijection of the morphisms out of a fixed
object. -/
def homCompIsoEquiv {E : Type u₁} [Category.{v₁} E] {X Y Z : E} (e : Y ≅ Z) :
    (X ⟶ Y) ≃ (X ⟶ Z) where
  toFun a := a ≫ e.hom
  invFun b := b ≫ e.inv
  left_inv a := show (a ≫ e.hom) ≫ e.inv = a by
    rw [Category.assoc, e.hom_inv_id, Category.comp_id]
  right_inv b := show (b ≫ e.inv) ≫ e.hom = b by
    rw [Category.assoc, e.inv_hom_id, Category.comp_id]

/-- Pre-composition with an isomorphism, as a bijection of the morphisms into a fixed
object. -/
def isoCompHomEquiv {E : Type u₁} [Category.{v₁} E] {X Y Z : E} (e : X ≅ Y) :
    (Y ⟶ Z) ≃ (X ⟶ Z) where
  toFun a := e.hom ≫ a
  invFun b := e.inv ≫ b
  left_inv a := show e.inv ≫ e.hom ≫ a = a by
    rw [← Category.assoc, e.inv_hom_id, Category.id_comp]
  right_inv b := show e.hom ≫ e.inv ≫ b = b by
    rw [← Category.assoc, e.hom_inv_id, Category.id_comp]

/-- Naturality in the target of a family of bijections between the morphisms out of two
objects: the bijection commutes with post-composition. -/
def NaturalHomEquiv {E : Type u₁} [Category.{v₁} E] {X Y : E}
    (e : ∀ Z : E, (X ⟶ Z) ≃ (Y ⟶ Z)) : Prop :=
  ∀ (Z Z' : E) (a : X ⟶ Z) (γ : Z ⟶ Z'), e Z' (a ≫ γ) = e Z a ≫ γ

/-- Two objects between which the maps out are identified naturally in the target are
isomorphic: the Yoneda argument. -/
noncomputable def isoOfNaturalHomEquiv {E : Type u₁} [Category.{v₁} E] {X Y : E}
    (e : ∀ Z : E, (X ⟶ Z) ≃ (Y ⟶ Z)) (he : NaturalHomEquiv e) :
    X ≅ Y where
  hom := (e Y).symm (𝟙 Y)
  inv := e X (𝟙 X)
  hom_inv_id := by
    refine (e X).injective ?_
    rw [he Y X ((e Y).symm (𝟙 Y)) (e X (𝟙 X)), Equiv.apply_symm_apply, Category.id_comp]
  inv_hom_id := by
    have h := he X Y (𝟙 X) ((e Y).symm (𝟙 Y))
    rw [Category.id_comp, Equiv.apply_symm_apply] at h
    exact h.symm

end Reflect

section PullbackInv

universe ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget RingCat.{ww'})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]

/-- The inverse of the comparison of the inverse image with restriction of scalars is the
identity on underlying sheaves of sets. -/
lemma moduleSheafFunctor_map_pullbackModuleObjRestrictScalarsIso_inv
    (J : GrothendieckTopology C) [J.HasSheafCompose (forget RingCat.{ww})]
    [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
    (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
    {S S' : Sheaf K RingCat.{ww'}} (α : S' ⟶ S) (G : SheafOfModules.{ww'} S) :
    (Sheaf.moduleSheafFunctor (pullbackRingSheaf J Φ S')).map
        (pullbackModuleObjRestrictScalarsIso J Φ α G).inv = 𝟙 _ :=
  moduleSheafFunctor_map_pullbackModuleObjRestrictScalarsInv J Φ α G

end PullbackInv

section InverseImage

universe w w' v u v' u'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{max u' v' w'})]
  (f : MorphismOfTopoi (Sheaf J (Type (max u v w))) (Sheaf K (Type (max u' v' w'))))

/-- The inverse image of sheaves of modules over the sheaf of rings underlying a sheaf of
commutative rings on the target. -/
noncomputable abbrev inverseImageCommModules (A : Sheaf K CommRingCat.{max u' v' w'}) :
    SheafOfModules.{max u' v' w'}
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) A) ⥤
      SheafOfModules.{max u v w}
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (J := J))
          (f.inverseImageRing.obj A)) :=
  inverseImageModules f ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) A)

/-- The inverse image of `𝒜` read as a sheaf of modules over itself is `f⁻¹𝒜` read as a sheaf
of modules over itself: the two have the same underlying sheaf of sets and the same scalar
action. -/
noncomputable def inverseImageUnitIso (A : Sheaf K CommRingCat.{max u' v' w'}) :
    (inverseImageCommModules.{w, w', v, u, v', u'} f A).obj
        (SheafOfModules.unit
          ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) A)) ≅
      SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (J := J))
          (f.inverseImageRing.obj A)) :=
  Iso.refl _

/-- The inverse image of sheaves of modules is a left adjoint, by Stacks 03D3. -/
noncomputable instance isLeftAdjoint_inverseImageCommModules
    (A : Sheaf K CommRingCat.{max u' v' w'}) :
    (inverseImageCommModules.{w, w', v, u, v', u'} f A).IsLeftAdjoint :=
  inverseImageModules_isLeftAdjoint f
    ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) A)

/-- The inverse image of sheaves of modules along a morphism of topoi is left exact. -/
noncomputable instance preservesFiniteLimits_inverseImageCommModules
    (A : Sheaf K CommRingCat.{max u' v' w'}) :
    Limits.PreservesFiniteLimits (inverseImageCommModules.{w, w', v, u, v', u'} f A) :=
  inverseImageModules_preservesFiniteLimits f
    ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) A)

/-- The direct image of sheaves of modules over the inverse image of the sheaf of rings
underlying a sheaf of commutative rings on the target, read as a sheaf of modules over that
sheaf of rings by restriction of scalars along the unit. -/
noncomputable abbrev directImageCommModules (A : Sheaf K CommRingCat.{max u' v' w'}) :
    SheafOfModules.{max u v w}
          ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (J := J))
            (f.inverseImageRing.obj A)) ⥤
      SheafOfModules.{max u' v' w'}
        ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) A) :=
  directImageModules f ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) A)

/-- **Stacks 03D3** over the sheaf of rings underlying a sheaf of commutative rings: the
inverse image of sheaves of modules along a morphism of topoi is left adjoint to the direct
image. -/
noncomputable def commModulesAdjunction (A : Sheaf K CommRingCat.{max u' v' w'}) :
    inverseImageCommModules.{w, w', v, u, v', u'} f A ⊣
      directImageCommModules.{w, w', v, u, v', u'} f A :=
  inverseImageAdjDirectImageModules f
    ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) A)

variable {A B : Sheaf K CommRingCat.{max u' v' w'}} (φ : A ⟶ B)

omit [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{max u' v' w'})] in
/-- The ring map underlying the inverse image of a homomorphism of sheaves of commutative rings
is the inverse image of the ring map underlying it. -/
lemma inverseImageRingMap_presentationRingHom :
    inverseImageRingMap f (presentationRingHom.{w', v', u'} K φ) =
      presentationRingHom.{w, v, u} J (f.inverseImageRing.map φ) :=
  (forgetCommRingSheaf_map_pullbackCommRingSheafMap J f.inverseImage φ).symm

/-- The ring map `f⁻¹𝒜 ⟶ f⁻¹ℬ`, spelled as the inverse image of the ring map underlying `φ`.
This is the spelling in which the comparisons below are stated; it is the ring map underlying
`f⁻¹φ` by `inverseImageRingMap_presentationRingHom`. -/
noncomputable abbrev inverseImagePresentationRingHom :
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (J := J)) (f.inverseImageRing.obj A) ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (J := J))
        (f.inverseImageRing.obj B) :=
  inverseImageRingMap f (presentationRingHom.{w', v', u'} K φ)

/-- The inverse image of `ℬ` read as a sheaf of `𝒜`-modules is `f⁻¹ℬ` read as a sheaf of
`f⁻¹𝒜`-modules: the inverse image commutes with restriction of scalars, and the inverse image
of the unit module is the unit module of the inverse-image sheaf of rings. -/
noncomputable def inverseImageRestrictUnitIso :
    (inverseImageCommModules.{w, w', v, u, v', u'} f A).obj
        ((SheafOfModules.restrictScalars (presentationRingHom.{w', v', u'} K φ)).obj
          (SheafOfModules.unit
            ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) B))) ≅
      (SheafOfModules.restrictScalars
          (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).obj
        (SheafOfModules.unit
          ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (J := J))
            (f.inverseImageRing.obj B))) :=
  (pullbackModuleObjRestrictScalarsIso J f.inverseImage (presentationRingHom.{w', v', u'} K φ)
    (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} (J := K)) B))).symm

/-- **The inverse image of the presentation is the presentation of the inverse image**, as
morphisms of sheaves of modules over the inverse-image sheaf of rings. -/
lemma inverseImageCommModules_map_presentationModuleHom :
    (inverseImageCommModules.{w, w', v, u, v', u'} f A).map
          (presentationModuleHom.{w', v', u'} K (presentationRingHom.{w', v', u'} K φ)) ≫
        (inverseImageRestrictUnitIso.{w, w', v, u, v', u'} f φ).hom =
      (inverseImageUnitIso.{w, w', v, u, v', u'} f A).hom ≫
        presentationModuleHom.{w, v, u} J
          (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ) := by
  refine hom_ext_moduleSheafFunctor (Sheaf.hom_ext_sections fun _ _ ↦ ?_)
  rfl

/-- The inverse image of the presentation, read through the two comparisons. -/
lemma inverseImageCommModules_map_presentationModuleHom' :
    (inverseImageCommModules.{w, w', v, u, v', u'} f A).map
        (presentationModuleHom.{w', v', u'} K (presentationRingHom.{w', v', u'} K φ)) =
      (inverseImageUnitIso.{w, w', v, u, v', u'} f A).hom ≫
        presentationModuleHom.{w, v, u} J
            (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ) ≫
          (inverseImageRestrictUnitIso.{w, w', v, u, v', u'} f φ).inv := by
  rw [← Category.assoc,
    ← inverseImageCommModules_map_presentationModuleHom.{w, w', v, u, v', u'} f φ,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The inverse image of the kernel inclusion is annihilated by the presentation of the
inverse image. -/
lemma inverseImageKerIota_comp :
    ((inverseImageCommModules.{w, w', v, u, v', u'} f A).map
          (SheafOfModules.kerIota (presentationModuleHom.{w', v', u'} K
            (presentationRingHom.{w', v', u'} K φ))) ≫
        (inverseImageUnitIso.{w, w', v, u, v', u'} f A).hom) ≫
      presentationModuleHom.{w, v, u} J
        (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ) = 0 := by
  rw [Category.assoc,
    ← inverseImageCommModules_map_presentationModuleHom.{w, w', v, u, v', u'} f φ,
    ← Category.assoc, ← Functor.map_comp, SheafOfModules.kerIota_comp, Functor.map_zero,
    zero_comp]

/-- The kernel inclusion of the presentation of the inverse image is annihilated by the inverse
image of the presentation. -/
lemma kerIota_comp_inverseImageCommModules_map :
    (SheafOfModules.kerIota (presentationModuleHom.{w, v, u} J
          (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)) ≫
        (inverseImageUnitIso.{w, w', v, u, v', u'} f A).inv) ≫
      (inverseImageCommModules.{w, w', v, u, v', u'} f A).map
        (presentationModuleHom.{w', v', u'} K
          (presentationRingHom.{w', v', u'} K φ)) = 0 := by
  rw [Category.assoc,
    inverseImageCommModules_map_presentationModuleHom'.{w, w', v, u, v', u'} f φ,
    Iso.inv_hom_id_assoc, ← Category.assoc, SheafOfModules.kerIota_comp, zero_comp]

/-- The inverse image of the kernel inclusion is annihilated by the inverse image of the
presentation. -/
lemma inverseImage_kerIota_comp_map :
    (inverseImageCommModules.{w, w', v, u, v', u'} f A).map
          (SheafOfModules.kerIota (presentationModuleHom.{w', v', u'} K
            (presentationRingHom.{w', v', u'} K φ))) ≫
        (inverseImageCommModules.{w, w', v, u, v', u'} f A).map
          (presentationModuleHom.{w', v', u'} K
            (presentationRingHom.{w', v', u'} K φ)) = 0 := by
  rw [← Functor.map_comp, SheafOfModules.kerIota_comp, Functor.map_zero]

/-- The inverse image of the kernel sequence of the presentation is a kernel sequence: `f⁻¹` is
left exact, being the inverse image of a morphism of topoi. -/
noncomputable def isLimitInverseImageKernelFork :
    IsLimit (KernelFork.ofι _
      (inverseImage_kerIota_comp_map.{w, w', v, u, v', u'} f φ)) :=
  isLimitForkMapOfIsLimit'
    (inverseImageCommModules.{w, w', v, u, v', u'} f A)
    (SheafOfModules.kerIota_comp (presentationModuleHom.{w', v', u'} K
      (presentationRingHom.{w', v', u'} K φ)))
    (SheafOfModules.kerIsLimit _)

/-- The comparison `f⁻¹ℐ ⟶ ℐ'`: the inverse image of the kernel inclusion factors through the
kernel of the presentation of the inverse image. -/
noncomputable def inverseImageIdealHom :
    (inverseImageCommModules.{w, w', v, u, v', u'} f A).obj
        (idealSheaf.{w', v', u'} K (presentationRingHom.{w', v', u'} K φ)) ⟶
      idealSheaf.{w, v, u} J (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ) :=
  SheafOfModules.kerLift _ (inverseImageKerIota_comp.{w, w', v, u, v', u'} f φ)

/-- The comparison `f⁻¹ℐ ⟶ ℐ'` factors the inverse image of the kernel inclusion. -/
lemma inverseImageIdealHom_comp :
    inverseImageIdealHom.{w, w', v, u, v', u'} f φ ≫
        SheafOfModules.kerIota (presentationModuleHom.{w, v, u} J
          (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)) =
      (inverseImageCommModules.{w, w', v, u, v', u'} f A).map
          (SheafOfModules.kerIota (presentationModuleHom.{w', v', u'} K
            (presentationRingHom.{w', v', u'} K φ))) ≫
        (inverseImageUnitIso.{w, w', v, u, v', u'} f A).hom :=
  SheafOfModules.kerLift_comp _ _

/-- The comparison `ℐ' ⟶ f⁻¹ℐ`: the kernel inclusion of the presentation of the inverse image
factors through the inverse image of the kernel, because the latter is a kernel. -/
noncomputable def inverseImageIdealInv :
    idealSheaf.{w, v, u} J (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ) ⟶
      (inverseImageCommModules.{w, w', v, u, v', u'} f A).obj
        (idealSheaf.{w', v', u'} K (presentationRingHom.{w', v', u'} K φ)) :=
  (KernelFork.IsLimit.lift' (isLimitInverseImageKernelFork.{w, w', v, u, v', u'} f φ) _
    (kerIota_comp_inverseImageCommModules_map.{w, w', v, u, v', u'} f φ)).1

/-- The comparison `ℐ' ⟶ f⁻¹ℐ` factors the kernel inclusion of the presentation of the inverse
image. -/
lemma inverseImageIdealInv_comp :
    inverseImageIdealInv.{w, w', v, u, v', u'} f φ ≫
        (inverseImageCommModules.{w, w', v, u, v', u'} f A).map
          (SheafOfModules.kerIota (presentationModuleHom.{w', v', u'} K
            (presentationRingHom.{w', v', u'} K φ))) =
      SheafOfModules.kerIota (presentationModuleHom.{w, v, u} J
          (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)) ≫
        (inverseImageUnitIso.{w, w', v, u, v', u'} f A).inv :=
  (KernelFork.IsLimit.lift' (isLimitInverseImageKernelFork.{w, w', v, u, v', u'} f φ) _
    (kerIota_comp_inverseImageCommModules_map.{w, w', v, u, v', u'} f φ)).2

/-- **The inverse image of the kernel ideal is the kernel ideal of the inverse image**:
`f⁻¹ℐ ≅ ℐ'`, where `ℐ = Ker(𝒜 ⟶ ℬ)` and `ℐ' = Ker(f⁻¹𝒜 ⟶ f⁻¹ℬ)`. This is left exactness of
the inverse image of a morphism of topoi applied to the kernel sequence of the
presentation. -/
noncomputable def inverseImageIdealIso :
    (inverseImageCommModules.{w, w', v, u, v', u'} f A).obj
        (idealSheaf.{w', v', u'} K (presentationRingHom.{w', v', u'} K φ)) ≅
      idealSheaf.{w, v, u} J (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ) where
  hom := inverseImageIdealHom.{w, w', v, u, v', u'} f φ
  inv := inverseImageIdealInv.{w, w', v, u, v', u'} f φ
  hom_inv_id := by
    refine Fork.IsLimit.hom_ext (isLimitInverseImageKernelFork.{w, w', v, u, v', u'} f φ) ?_
    have h : (inverseImageIdealHom.{w, w', v, u, v', u'} f φ ≫
          inverseImageIdealInv.{w, w', v, u, v', u'} f φ) ≫
            (inverseImageCommModules.{w, w', v, u, v', u'} f A).map
              (SheafOfModules.kerIota (presentationModuleHom.{w', v', u'} K
                (presentationRingHom.{w', v', u'} K φ))) =
        𝟙 _ ≫ (inverseImageCommModules.{w, w', v, u, v', u'} f A).map
          (SheafOfModules.kerIota (presentationModuleHom.{w', v', u'} K
            (presentationRingHom.{w', v', u'} K φ))) := by
      rw [Category.assoc, inverseImageIdealInv_comp.{w, w', v, u, v', u'} f φ, ← Category.assoc,
        inverseImageIdealHom_comp.{w, w', v, u, v', u'} f φ, Category.assoc, Iso.hom_inv_id,
        Category.comp_id, Category.id_comp]
    exact h
  inv_hom_id := by
    rw [← cancel_mono (SheafOfModules.kerIota (presentationModuleHom.{w, v, u} J
        (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ))), Category.assoc,
      inverseImageIdealHom_comp.{w, w', v, u, v', u'} f φ, ← Category.assoc,
      inverseImageIdealInv_comp.{w, w', v, u, v', u'} f φ, Category.assoc, Iso.inv_hom_id,
      Category.comp_id, Category.id_comp]

/-- **The inverse image of a locally surjective homomorphism of sheaves of commutative rings is
locally surjective.** The inverse image of a morphism of topoi is a left adjoint, and a left
adjoint between categories of sheaves of sets preserves local surjectivity. -/
instance isLocallySurjective_inverseImageRing_map
    [Presheaf.IsLocallySurjective K φ.hom] :
    Presheaf.IsLocallySurjective J (f.inverseImageRing.map φ).hom := by
  have hK : Sheaf.IsLocallySurjective
      ((sheafCompose K (forget CommRingCat.{max u' v' w'})).map φ) :=
    (Presheaf.isLocallySurjective_iff_whisker_forget K φ.hom).mp inferInstance
  have hJ : Sheaf.IsLocallySurjective
      ((sheafCompose J (forget CommRingCat.{max u v w})).map (f.inverseImageRing.map φ)) := by
    rw [MorphismOfTopoi.inverseImageRing_map_forget]
    exact Stacks.Sheaves.LocalGeneration.map_locallySurjective_of_adjunction f.adj _
  exact (Presheaf.isLocallySurjective_iff_whisker_forget J
    (f.inverseImageRing.map φ).hom).mpr hJ

/-! ## The inverse image of the conormal sheaf -/

variable [Presheaf.IsLocallySurjective K φ.hom]
  (M M' : SheafOfModules.{max u v w}
    ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (J := J))
      (f.inverseImageRing.obj B)))

omit [Presheaf.IsLocallySurjective K φ.hom] in
/-- The comparison of the direct image with restriction of scalars along the presentation: the
direct image of a sheaf of `f⁻¹ℬ`-modules, read as a sheaf of `𝒜`-modules, is the direct image
over `f⁻¹𝒜` of its restriction of scalars along `f⁻¹φ`. -/
noncomputable def directImageRestrictScalarsIso :
    (SheafOfModules.restrictScalars (presentationRingHom.{w', v', u'} K φ)).obj
        ((directImageCommModules.{w, w', v, u, v', u'} f B).obj M) ≅
      (directImageCommModules.{w, w', v, u, v', u'} f A).obj
        ((SheafOfModules.restrictScalars
          (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).obj M) :=
  directImageModulesRestrictScalarsIso f (presentationRingHom.{w', v', u'} K φ) M

omit [Presheaf.IsLocallySurjective K φ.hom] in
/-- The comparison of the direct image with restriction of scalars along the presentation is
natural in the sheaf of `f⁻¹ℬ`-modules. -/
lemma directImageRestrictScalarsIso_naturality (γ : M ⟶ M') :
    (SheafOfModules.restrictScalars (presentationRingHom.{w', v', u'} K φ)).map
          ((directImageCommModules.{w, w', v, u, v', u'} f B).map γ) ≫
        (directImageRestrictScalarsIso f φ M').hom =
      (directImageRestrictScalarsIso f φ M).hom ≫
        (directImageCommModules.{w, w', v, u, v', u'} f A).map
          ((SheafOfModules.restrictScalars
            (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).map γ) :=
  (directImageModulesCompRestrictScalarsIso f
    (presentationRingHom.{w', v', u'} K φ)).hom.naturality γ

/-- Morphisms out of the inverse image of the conormal sheaf are morphisms of the conormal
sheaf into the direct image, by the adjunction of Stacks 03D3. -/
noncomputable def conormalInverseImageAdjunctionEquiv :
    ((inverseImageCommModules.{w, w', v, u, v', u'} f B).obj
        (conormalModule.{w', v', u'} K φ) ⟶ M) ≃
      (conormalModule.{w', v', u'} K φ ⟶
        (directImageCommModules.{w, w', v, u, v', u'} f B).obj M) :=
  (commModulesAdjunction.{w, w', v, u, v', u'} f B).homEquiv
    (conormalModule.{w', v', u'} K φ) M

/-- Morphisms of the conormal sheaf into the direct image are morphisms out of the kernel ideal
with scalars restricted along the presentation. -/
noncomputable def conormalDirectImageIdealEquiv :
    (conormalModule.{w', v', u'} K φ ⟶
        (directImageCommModules.{w, w', v, u, v', u'} f B).obj M) ≃
      (idealSheaf.{w', v', u'} K (presentationRingHom.{w', v', u'} K φ) ⟶
        (SheafOfModules.restrictScalars (presentationRingHom.{w', v', u'} K φ)).obj
          ((directImageCommModules.{w, w', v, u, v', u'} f B).obj M)) :=
  conormalModuleHomEquivOf.{w', v', u'} K φ (presentationRingHom.{w', v', u'} K φ) rfl
    ((directImageCommModules.{w, w', v, u, v', u'} f B).obj M)

/-- Exchanging the restriction of scalars with the direct image, on morphisms out of the
kernel ideal. -/
noncomputable def conormalIdealDirectImageRestrictEquiv :
    (idealSheaf.{w', v', u'} K (presentationRingHom.{w', v', u'} K φ) ⟶
        (SheafOfModules.restrictScalars (presentationRingHom.{w', v', u'} K φ)).obj
          ((directImageCommModules.{w, w', v, u, v', u'} f B).obj M)) ≃
      (idealSheaf.{w', v', u'} K (presentationRingHom.{w', v', u'} K φ) ⟶
        (directImageCommModules.{w, w', v, u, v', u'} f A).obj
          ((SheafOfModules.restrictScalars
            (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).obj M)) :=
  homCompIsoEquiv (directImageRestrictScalarsIso f φ M)

omit [Presheaf.IsLocallySurjective K φ.hom] in
/-- Post-composition with the comparison of the direct image and restriction of scalars. -/
lemma conormalIdealDirectImageRestrictEquiv_apply
    (a : idealSheaf.{w', v', u'} K (presentationRingHom.{w', v', u'} K φ) ⟶
      (SheafOfModules.restrictScalars (presentationRingHom.{w', v', u'} K φ)).obj
        ((directImageCommModules.{w, w', v, u, v', u'} f B).obj M)) :
    conormalIdealDirectImageRestrictEquiv f φ M a =
      a ≫ (directImageRestrictScalarsIso f φ M).hom :=
  rfl

/-- Morphisms out of the kernel ideal into a direct image are morphisms out of the inverse
image of the kernel ideal, by the adjunction of Stacks 03D3. -/
noncomputable def inverseImageIdealAdjunctionEquiv :
    (idealSheaf.{w', v', u'} K (presentationRingHom.{w', v', u'} K φ) ⟶
        (directImageCommModules.{w, w', v, u, v', u'} f A).obj
          ((SheafOfModules.restrictScalars
            (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).obj M)) ≃
      ((inverseImageCommModules.{w, w', v, u, v', u'} f A).obj
          (idealSheaf.{w', v', u'} K (presentationRingHom.{w', v', u'} K φ)) ⟶
        (SheafOfModules.restrictScalars
          (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).obj M) :=
  ((commModulesAdjunction.{w, w', v, u, v', u'} f A).homEquiv
    (idealSheaf.{w', v', u'} K (presentationRingHom.{w', v', u'} K φ))
    ((SheafOfModules.restrictScalars
      (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).obj M)).symm

/-- Transporting along `f⁻¹ℐ ≅ ℐ'`, the identification of the inverse image of the kernel ideal
with the kernel ideal of the inverse image. -/
noncomputable def inverseImageIdealTransportEquiv :
    ((inverseImageCommModules.{w, w', v, u, v', u'} f A).obj
          (idealSheaf.{w', v', u'} K (presentationRingHom.{w', v', u'} K φ)) ⟶
        (SheafOfModules.restrictScalars
          (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).obj M) ≃
      (idealSheaf.{w, v, u} J (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ) ⟶
        (SheafOfModules.restrictScalars
          (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).obj M) :=
  isoCompHomEquiv (inverseImageIdealIso.{w, w', v, u, v', u'} f φ).symm

omit [Presheaf.IsLocallySurjective K φ.hom] in
/-- Pre-composition with the identification of the kernel ideal of the inverse image with the
inverse image of the kernel ideal. -/
lemma inverseImageIdealTransportEquiv_apply
    (a : (inverseImageCommModules.{w, w', v, u, v', u'} f A).obj
        (idealSheaf.{w', v', u'} K (presentationRingHom.{w', v', u'} K φ)) ⟶
      (SheafOfModules.restrictScalars
        (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).obj M) :
    inverseImageIdealTransportEquiv f φ M a =
      (inverseImageIdealIso.{w, w', v, u, v', u'} f φ).inv ≫ a :=
  rfl

/-- Morphisms out of the kernel ideal of the inverse image are morphisms out of the conormal
sheaf of the inverse image. -/
noncomputable def inverseImageConormalDescEquiv :
    (idealSheaf.{w, v, u} J (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ) ⟶
        (SheafOfModules.restrictScalars
          (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).obj M) ≃
      (conormalModule.{w, v, u} J (f.inverseImageRing.map φ) ⟶ M) :=
  (conormalModuleHomEquivOf.{w, v, u} J (f.inverseImageRing.map φ)
    (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)
    (inverseImageRingMap_presentationRingHom.{w, w', v, u, v', u'} f φ) M).symm

/-- Morphisms out of the inverse image of the conormal sheaf are morphisms out of the kernel
ideal into the direct image with scalars restricted along the presentation. -/
noncomputable def conormalInverseImageIdealEquiv :
    ((inverseImageCommModules.{w, w', v, u, v', u'} f B).obj
        (conormalModule.{w', v', u'} K φ) ⟶ M) ≃
      (idealSheaf.{w', v', u'} K (presentationRingHom.{w', v', u'} K φ) ⟶
        (SheafOfModules.restrictScalars (presentationRingHom.{w', v', u'} K φ)).obj
          ((directImageCommModules.{w, w', v, u, v', u'} f B).obj M)) :=
  (conormalInverseImageAdjunctionEquiv f φ M).trans (conormalDirectImageIdealEquiv f φ M)

/-- The same, with the restriction of scalars exchanged with the direct image. -/
noncomputable def conormalInverseImageIdealDirectImageEquiv :
    ((inverseImageCommModules.{w, w', v, u, v', u'} f B).obj
        (conormalModule.{w', v', u'} K φ) ⟶ M) ≃
      (idealSheaf.{w', v', u'} K (presentationRingHom.{w', v', u'} K φ) ⟶
        (directImageCommModules.{w, w', v, u, v', u'} f A).obj
          ((SheafOfModules.restrictScalars
            (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).obj M)) :=
  (conormalInverseImageIdealEquiv f φ M).trans
    (conormalIdealDirectImageRestrictEquiv f φ M)

/-- The same, transposed across the adjunction into morphisms out of the inverse image of the
kernel ideal. -/
noncomputable def conormalInverseImageIdealPullbackEquiv :
    ((inverseImageCommModules.{w, w', v, u, v', u'} f B).obj
        (conormalModule.{w', v', u'} K φ) ⟶ M) ≃
      ((inverseImageCommModules.{w, w', v, u, v', u'} f A).obj
          (idealSheaf.{w', v', u'} K (presentationRingHom.{w', v', u'} K φ)) ⟶
        (SheafOfModules.restrictScalars
          (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).obj M) :=
  (conormalInverseImageIdealDirectImageEquiv f φ M).trans
    (inverseImageIdealAdjunctionEquiv f φ M)

/-- The same, transported onto the kernel ideal of the inverse image. -/
noncomputable def conormalInverseImageIdealSheafEquiv :
    ((inverseImageCommModules.{w, w', v, u, v', u'} f B).obj
        (conormalModule.{w', v', u'} K φ) ⟶ M) ≃
      (idealSheaf.{w, v, u} J (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ) ⟶
        (SheafOfModules.restrictScalars
          (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).obj M) :=
  (conormalInverseImageIdealPullbackEquiv f φ M).trans
    (inverseImageIdealTransportEquiv f φ M)

/-- **The inverse image of the conormal sheaf and the conormal sheaf of the inverse image have
the same morphisms into every sheaf of `f⁻¹ℬ`-modules.** The bijection is the composite of the
adjunction of Stacks 03D3, the universal property of the conormal sheaf, the exchange of the
direct image with restriction of scalars, the adjunction again, the identification
`f⁻¹ℐ ≅ ℐ'`, and the universal property of the conormal sheaf of the inverse image. -/
noncomputable def inverseImageConormalHomEquiv :
    ((inverseImageCommModules.{w, w', v, u, v', u'} f B).obj
        (conormalModule.{w', v', u'} K φ) ⟶ M) ≃
      (conormalModule.{w, v, u} J (f.inverseImageRing.map φ) ⟶ M) :=
  (conormalInverseImageIdealSheafEquiv f φ M).trans (inverseImageConormalDescEquiv f φ M)

/-! ### Naturality of the identification in the sheaf of modules -/

/-- Transposition across the adjunction of Stacks 03D3 is natural in the target. -/
lemma conormalInverseImageAdjunctionEquiv_comp
    (a : (inverseImageCommModules.{w, w', v, u, v', u'} f B).obj
      (conormalModule.{w', v', u'} K φ) ⟶ M) (γ : M ⟶ M') :
    conormalInverseImageAdjunctionEquiv f φ M' (a ≫ γ) =
      conormalInverseImageAdjunctionEquiv f φ M a ≫
        (directImageCommModules.{w, w', v, u, v', u'} f B).map γ :=
  (commModulesAdjunction.{w, w', v, u, v', u'} f B).homEquiv_naturality_right a γ

omit [K.HasSheafCompose (forget AddCommGrpCat.{max u' v' w'})] in
/-- The universal property of the conormal sheaf is natural in the sheaf of `ℬ`-modules. -/
lemma conormalDirectImageIdealEquiv_comp
    (a : conormalModule.{w', v', u'} K φ ⟶
      (directImageCommModules.{w, w', v, u, v', u'} f B).obj M) (γ : M ⟶ M') :
    conormalDirectImageIdealEquiv f φ M'
        (a ≫ (directImageCommModules.{w, w', v, u, v', u'} f B).map γ) =
      conormalDirectImageIdealEquiv f φ M a ≫
        (SheafOfModules.restrictScalars (presentationRingHom.{w', v', u'} K φ)).map
          ((directImageCommModules.{w, w', v, u, v', u'} f B).map γ) :=
  conormalModuleHomEquivOf_comp.{w', v', u'} K φ (presentationRingHom.{w', v', u'} K φ) rfl
    ((directImageCommModules.{w, w', v, u, v', u'} f B).obj M)
    ((directImageCommModules.{w, w', v, u, v', u'} f B).obj M') a _

omit [Presheaf.IsLocallySurjective K φ.hom] in
/-- The exchange of restriction of scalars with the direct image is natural in the sheaf of
`f⁻¹ℬ`-modules. -/
lemma conormalIdealDirectImageRestrictEquiv_comp
    (a : idealSheaf.{w', v', u'} K (presentationRingHom.{w', v', u'} K φ) ⟶
      (SheafOfModules.restrictScalars (presentationRingHom.{w', v', u'} K φ)).obj
        ((directImageCommModules.{w, w', v, u, v', u'} f B).obj M)) (γ : M ⟶ M') :
    conormalIdealDirectImageRestrictEquiv f φ M'
        (a ≫ (SheafOfModules.restrictScalars (presentationRingHom.{w', v', u'} K φ)).map
          ((directImageCommModules.{w, w', v, u, v', u'} f B).map γ)) =
      conormalIdealDirectImageRestrictEquiv f φ M a ≫
        (directImageCommModules.{w, w', v, u, v', u'} f A).map
          ((SheafOfModules.restrictScalars
            (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).map γ) := by
  rw [conormalIdealDirectImageRestrictEquiv_apply, conormalIdealDirectImageRestrictEquiv_apply,
    Category.assoc, Category.assoc, directImageRestrictScalarsIso_naturality]

omit [Presheaf.IsLocallySurjective K φ.hom] in
/-- Transposition across the adjunction of Stacks 03D3 is natural in the source. -/
lemma inverseImageIdealAdjunctionEquiv_comp
    (a : idealSheaf.{w', v', u'} K (presentationRingHom.{w', v', u'} K φ) ⟶
      (directImageCommModules.{w, w', v, u, v', u'} f A).obj
        ((SheafOfModules.restrictScalars
          (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).obj M)) (γ : M ⟶ M') :
    inverseImageIdealAdjunctionEquiv f φ M'
        (a ≫ (directImageCommModules.{w, w', v, u, v', u'} f A).map
          ((SheafOfModules.restrictScalars
            (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).map γ)) =
      inverseImageIdealAdjunctionEquiv f φ M a ≫
        (SheafOfModules.restrictScalars
          (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).map γ :=
  (commModulesAdjunction.{w, w', v, u, v', u'} f A).homEquiv_naturality_right_symm a _

omit [Presheaf.IsLocallySurjective K φ.hom] in
/-- Transporting along `f⁻¹ℐ ≅ ℐ'` is natural in the sheaf of `f⁻¹ℬ`-modules. -/
lemma inverseImageIdealTransportEquiv_comp
    (a : (inverseImageCommModules.{w, w', v, u, v', u'} f A).obj
        (idealSheaf.{w', v', u'} K (presentationRingHom.{w', v', u'} K φ)) ⟶
      (SheafOfModules.restrictScalars
        (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).obj M) (γ : M ⟶ M') :
    inverseImageIdealTransportEquiv f φ M'
        (a ≫ (SheafOfModules.restrictScalars
          (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).map γ) =
      inverseImageIdealTransportEquiv f φ M a ≫
        (SheafOfModules.restrictScalars
          (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).map γ := by
  rw [inverseImageIdealTransportEquiv_apply, inverseImageIdealTransportEquiv_apply,
    Category.assoc]

omit [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{max u' v' w'})] in
/-- The universal property of the conormal sheaf of the inverse image is natural in the sheaf
of `f⁻¹ℬ`-modules. -/
lemma inverseImageConormalDescEquiv_comp
    (a : idealSheaf.{w, v, u} J (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ) ⟶
      (SheafOfModules.restrictScalars
        (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).obj M) (γ : M ⟶ M') :
    inverseImageConormalDescEquiv f φ M'
        (a ≫ (SheafOfModules.restrictScalars
          (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).map γ) =
      inverseImageConormalDescEquiv f φ M a ≫ γ :=
  conormalModuleHomEquivOf_symm_comp.{w, v, u} J (f.inverseImageRing.map φ)
    (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)
    (inverseImageRingMap_presentationRingHom.{w, w', v, u, v', u'} f φ) M M' a γ

/-- The first two steps of the identification are natural in the sheaf of `f⁻¹ℬ`-modules. -/
lemma conormalInverseImageIdealEquiv_comp
    (a : (inverseImageCommModules.{w, w', v, u, v', u'} f B).obj
      (conormalModule.{w', v', u'} K φ) ⟶ M) (γ : M ⟶ M') :
    conormalInverseImageIdealEquiv f φ M' (a ≫ γ) =
      conormalInverseImageIdealEquiv f φ M a ≫
        (SheafOfModules.restrictScalars (presentationRingHom.{w', v', u'} K φ)).map
          ((directImageCommModules.{w, w', v, u, v', u'} f B).map γ) := by
  simp only [conormalInverseImageIdealEquiv, Equiv.trans_apply]
  rw [conormalInverseImageAdjunctionEquiv_comp, conormalDirectImageIdealEquiv_comp]

/-- The first three steps of the identification are natural in the sheaf of
`f⁻¹ℬ`-modules. -/
lemma conormalInverseImageIdealDirectImageEquiv_comp
    (a : (inverseImageCommModules.{w, w', v, u, v', u'} f B).obj
      (conormalModule.{w', v', u'} K φ) ⟶ M) (γ : M ⟶ M') :
    conormalInverseImageIdealDirectImageEquiv f φ M' (a ≫ γ) =
      conormalInverseImageIdealDirectImageEquiv f φ M a ≫
        (directImageCommModules.{w, w', v, u, v', u'} f A).map
          ((SheafOfModules.restrictScalars
            (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).map γ) := by
  simp only [conormalInverseImageIdealDirectImageEquiv, Equiv.trans_apply]
  rw [conormalInverseImageIdealEquiv_comp, conormalIdealDirectImageRestrictEquiv_comp]

/-- The first four steps of the identification are natural in the sheaf of `f⁻¹ℬ`-modules. -/
lemma conormalInverseImageIdealPullbackEquiv_comp
    (a : (inverseImageCommModules.{w, w', v, u, v', u'} f B).obj
      (conormalModule.{w', v', u'} K φ) ⟶ M) (γ : M ⟶ M') :
    conormalInverseImageIdealPullbackEquiv f φ M' (a ≫ γ) =
      conormalInverseImageIdealPullbackEquiv f φ M a ≫
        (SheafOfModules.restrictScalars
          (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).map γ := by
  simp only [conormalInverseImageIdealPullbackEquiv, Equiv.trans_apply]
  rw [conormalInverseImageIdealDirectImageEquiv_comp, inverseImageIdealAdjunctionEquiv_comp]

/-- The first five steps of the identification are natural in the sheaf of `f⁻¹ℬ`-modules. -/
lemma conormalInverseImageIdealSheafEquiv_comp
    (a : (inverseImageCommModules.{w, w', v, u, v', u'} f B).obj
      (conormalModule.{w', v', u'} K φ) ⟶ M) (γ : M ⟶ M') :
    conormalInverseImageIdealSheafEquiv f φ M' (a ≫ γ) =
      conormalInverseImageIdealSheafEquiv f φ M a ≫
        (SheafOfModules.restrictScalars
          (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).map γ := by
  simp only [conormalInverseImageIdealSheafEquiv, Equiv.trans_apply]
  rw [conormalInverseImageIdealPullbackEquiv_comp, inverseImageIdealTransportEquiv_comp]

/-- **The identification of the morphisms out of the two conormal sheaves is natural in the
sheaf of `f⁻¹ℬ`-modules.** Each of the six steps is natural, the restriction of scalars and the
direct image cancelling against one another at the two ends. -/
lemma naturalHomEquiv_inverseImageConormalHomEquiv :
    NaturalHomEquiv (inverseImageConormalHomEquiv f φ) := fun N N' b c ↦ by
  simp only [inverseImageConormalHomEquiv, Equiv.trans_apply]
  rw [conormalInverseImageIdealSheafEquiv_comp, inverseImageConormalDescEquiv_comp]

/-- **The inverse image of the conormal sheaf is the conormal sheaf of the inverse image**:
`f⁻¹(ℐ/ℐ²) ≅ ℐ'/(ℐ')²`, where `ℐ = Ker φ` and `ℐ' = Ker(f⁻¹φ)`. This is the degree `-1` term
of the identification `f⁻¹ NL_{ℬ/𝒜} = NL_{f⁻¹ℬ/f⁻¹𝒜}` of Stacks 08TZ. -/
@[stacks 08TZ "the degree -1 term, for an arbitrary locally surjective homomorphism of sheaves \
of rings, of which the conormal term of the tag is the instance at the canonical polynomial \
presentation. The instantiation is \
`Stacks.SheafOfModules.inverseImageNaiveCotangentNegOneIso` and the isomorphism of complexes is \
`Stacks.SheafOfModules.inverseImageNaiveCotangentComplexIso`"]
noncomputable def inverseImageConormalIso :
    (inverseImageCommModules.{w, w', v, u, v', u'} f B).obj
        (conormalModule.{w', v', u'} K φ) ≅
      conormalModule.{w, v, u} J (f.inverseImageRing.map φ) :=
  isoOfNaturalHomEquiv (inverseImageConormalHomEquiv f φ)
    (naturalHomEquiv_inverseImageConormalHomEquiv f φ)

end InverseImage

/-! ## The identification on underlying sheaves of sets -/

section InverseImageUnderlying

universe w w' v u v' u'

open CategoryTheory.Functor CategoryTheory.Sheaf
open Stacks.Sites.Conormal

attribute [local implicit_reducible] CategoryTheory.sheafCompose

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{max u' v' w'})]
  (f : MorphismOfTopoi (Sheaf J (Type (max u v w))) (Sheaf K (Type (max u' v' w'))))
  (A : Sheaf K CommRingCat.{max u' v' w'})

/-- The underlying morphism of sheaves of sets of the inverse image of a morphism of sheaves of
modules over the sheaf of rings underlying a sheaf of commutative rings. -/
lemma moduleSheafFunctor_map_inverseImageCommModules_map
    {G G' : SheafOfModules.{max u' v' w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} A)}
    (k : G ⟶ G') :
    (Sheaf.moduleSheafFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj A))).map
        ((inverseImageCommModules.{w, w', v, u, v', u'} f A).map k) =
      f.inverseImage.map
        ((Sheaf.moduleSheafFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} A)).map k) :=
  moduleSheafFunctor_map_inverseImageModules_map f _ k

/-- The underlying morphism of sheaves of sets of the transpose of a morphism into a direct
image is the transpose of its underlying morphism of sheaves of sets. -/
lemma moduleSheafFunctor_map_commModulesAdjunction_homEquiv_symm
    (G : SheafOfModules.{max u' v' w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} A))
    (F : SheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj A)))
    (q : G ⟶ (directImageCommModules.{w, w', v, u, v', u'} f A).obj F) :
    (Sheaf.moduleSheafFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj A))).map
        (((commModulesAdjunction.{w, w', v, u, v', u'} f A).homEquiv G F).symm q) =
      (f.adj.homEquiv
          ((Sheaf.moduleSheafFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} A)).obj G)
          ((Sheaf.moduleSheafFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w}
              (f.inverseImageRing.obj A))).obj F)).symm
        ((Sheaf.moduleSheafFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} A)).map q) := by
  rw [show (commModulesAdjunction.{w, w', v, u, v', u'} f A).homEquiv =
      toposModulesHomEquiv f (Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} A) from
    Adjunction.mkOfHomEquiv_homEquiv _]
  exact moduleSheafFunctor_map_toposModulesHomEquiv_symm f _ q

/-- The comparison of the inverse image of the unit module with the unit module of the
inverse-image sheaf of rings is the identity on underlying sheaves of sets. -/
lemma moduleSheafFunctor_map_inverseImageUnitIso_inv :
    (Sheaf.moduleSheafFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj A))).map
        (inverseImageUnitIso.{w, w', v, u, v', u'} f A).inv =
      𝟙 _ :=
  (Sheaf.moduleSheafFunctor
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj A))).map_id _

variable {B : Sheaf K CommRingCat.{max u' v' w'}} (φ : A ⟶ B)
  [Presheaf.IsLocallySurjective K φ.hom]
  (M : SheafOfModules.{max u v w}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj B)))

omit [Presheaf.IsLocallySurjective K φ.hom] in
/-- The transposition of a morphism out of the kernel ideal across the adjunction of
Stacks 03D3 is the transposition of its underlying morphism of sheaves of sets. -/
lemma moduleSheafFunctor_map_inverseImageIdealAdjunctionEquiv
    (q : idealSheaf.{max u' v' w', v', u'} K (presentationRingHom.{max u' v' w', v', u'} K φ) ⟶
      (directImageCommModules.{w, w', v, u, v', u'} f A).obj
        ((SheafOfModules.restrictScalars
          (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).obj M)) :
    (Sheaf.moduleSheafFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj A))).map
        (inverseImageIdealAdjunctionEquiv f φ M q) =
      (f.adj.homEquiv
          ((Sheaf.moduleSheafFunctor
              (Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} A)).obj
            (idealSheaf.{max u' v' w', v', u'} K
              (presentationRingHom.{max u' v' w', v', u'} K φ)))
          ((Sheaf.moduleSheafFunctor
              (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w}
                (f.inverseImageRing.obj A))).obj
            ((SheafOfModules.restrictScalars
              (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ)).obj M))).symm
        ((Sheaf.moduleSheafFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} A)).map q) :=
  moduleSheafFunctor_map_commModulesAdjunction_homEquiv_symm f A _ _ q

omit [Presheaf.IsLocallySurjective K φ.hom] in
/-- The identification `f⁻¹ℐ ≅ ℐ'` carries the kernel inclusion of the inverse image to the
inverse image of the kernel inclusion, on underlying sheaves of sets. -/
lemma moduleSheafFunctor_map_inverseImageIdealIso_inv_comp :
    (Sheaf.moduleSheafFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w}
              (f.inverseImageRing.obj A))).map
          (inverseImageIdealIso.{w, w', v, u, v', u'} f φ).inv ≫
        f.inverseImage.map ((Sheaf.moduleSheafFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', max u' v' w'} A)).map
            (SheafOfModules.kerIota (presentationModuleHom.{max u' v' w', v', u'} K
              (presentationRingHom.{max u' v' w', v', u'} K φ)))) =
      (Sheaf.moduleSheafFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w}
              (f.inverseImageRing.obj A))).map
        (SheafOfModules.kerIota (presentationModuleHom.{max u v w, v, u} J
          (inverseImagePresentationRingHom.{w, w', v, u, v', u'} f φ))) := by
  have key := congrArg (Sheaf.moduleSheafFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj A))).map
    (inverseImageIdealInv_comp.{w, w', v, u, v', u'} f φ)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    moduleSheafFunctor_map_inverseImageUnitIso_inv] at key
  exact Eq.trans (congrArg (fun m ↦ (Sheaf.moduleSheafFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (f.inverseImageRing.obj A))).map
          (inverseImageIdealIso.{w, w', v, u, v', u'} f φ).inv ≫ m)
      (moduleSheafFunctor_map_inverseImageCommModules_map f A
        (SheafOfModules.kerIota (presentationModuleHom.{max u' v' w', v', u'} K
          (presentationRingHom.{max u' v' w', v', u'} K φ)))).symm)
    (Eq.trans key (Category.comp_id _))

end InverseImageUnderlying

end Stacks.Sheaves.RingedToposModules

end
