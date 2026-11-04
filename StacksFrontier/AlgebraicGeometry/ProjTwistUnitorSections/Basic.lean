module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OnSpaceMonoidal
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistSectionModuleGraded

/-!
# The global sections of a twist of the structure sheaf, with the unit tensor removed

On `Proj 𝒮` the `n`-th twist of a module `ℱ` is `ℱ ⊗ 𝒪(n)`, so the twist of the *structure
sheaf* is `𝒪 ⊗ 𝒪(n)` and not `𝒪(n)` on the nose. Every statement proved by twisting a module —
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistSheafOfModules` and its graded scalar action —
therefore speaks about `Γ(Proj 𝒮, 𝒪 ⊗ 𝒪(n))`, while every statement about the canonical section
of a homogeneous element speaks about `Γ(Proj 𝒮, 𝒪(n))`. The two groups are *not* the same type.

The left unitor of the sheafified tensor product, read on the sections over `⊤`, identifies them,
and the identification carries the graded scalar action of [Stacks, Tag 03GK] on the first group
to the action by the morphisms of twisting sheaves on the second.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTwistUnitorSections.unitTwistSectionsEquiv`:
  `Γ(Proj 𝒮, 𝒪 ⊗ 𝒪(n)) ≃+ Γ(Proj 𝒮, 𝒪(n))`, the left unitor over `⊤`.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistUnitorSections.leftUnitor_hom_tensorSheafMap_id`:
  naturality of the left unitor of [Stacks, Tag 01CA] in the `tensorSheafMap` spelling of the
  tensor product of two morphisms, on an arbitrary ringed space.
* `Stacks.AlgebraicGeometry.ProjTwistUnitorSections.unitTwistSectionsEquiv_tensorObjTmul` and
  `unitTwistSectionsEquiv_symm_apply`: the identification and its inverse on sections —
  `r ⊗ u ↦ r · u` one way, `u ↦ 1 ⊗ u` the other.
* `Stacks.AlgebraicGeometry.ProjTwistUnitorSections.unitTwistSectionsEquiv_homogeneousScalar`:
  **the identification intertwines the two scalar actions.** The graded action of a homogeneous
  `a` of degree `i` on `Γ(Proj 𝒮, 𝒪 ⊗ 𝒪(n))` becomes the action on `Γ(Proj 𝒮, 𝒪(n))` of
  `Stacks.AlgebraicGeometry.ProjTwistedSections.twistScalarSheafMap`, the morphism
  `𝒪(n) ⟶ 𝒪(i + n)` of twisting sheaves that `a` induces.

## Implementation notes

`Stacks.AlgebraicGeometry.ProjTwistedSections.twistSheafScalarMap` is by definition
`tensorSheafMap _ (𝟙 ℱ) (twistScalarSheafMap …)`, so at `ℱ = 𝒪` the scalar action is the
identity of the monoidal unit tensored with a morphism of twisting sheaves. Naturality of the left
unitor is stated in that `tensorSheafMap` spelling rather than taken from
`MonoidalCategory.leftUnitor_naturality`: the monoidal structure of
`Stacks.SheafOfModules.OnSpace.monoidal` is transported along an equivalence, so `𝟙 ◁ g` is not
syntactically `tensorSheafMap`.

The monoidal structure is registered locally at the spelling
`SheafOfModules ((sheafCompose …).obj (ProjectiveSpectrum.Proj.structureSheaf 𝒮))` in which
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf` states its own type: instance search
does not cross between that and `Stacks.RingedSpace.structureSheafRing (Proj 𝒮).toRingedSpace`,
although the two are definitionally equal.

Every equality of morphisms is transported onto a section by `congrArg` of a function that
evaluates a morphism, never by `rw`: the goals here mix the two spellings of the category of
modules and `rw` reports them as not type-correct at `implicit` transparency.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 03GK](https://stacks.math.columbia.edu/tag/03GK)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite TopologicalSpace
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf twistSheafOfModules)
open Stacks.SheafOfModules.TensorStalkRingedSpace (toTensorSheafSection
  tensorSheafMap_app_toTensorSheafSection)
open Stacks.SheafOfModules.OnSpace (tensorObjTmul unitSection)
open Stacks.AlgebraicGeometry.ProjTwistedSections (twistedSectionsComponent
  homogeneousScalarTwistedSections twistScalarSheafMap twistSheafScalarMap)
open scoped TensorProduct

universe u w

namespace Stacks.AlgebraicGeometry.ProjTwistUnitorSections

attribute [local instance] Stacks.SheafOfModules.OnSpace.monoidal

/-! ### Naturality of the left unitor, in the `tensorSheafMap` spelling -/

section Space

variable (Z : RingedSpace.{u, u})

/-- **The left unitor of [Stacks, Tag 01CA] is natural**, with the tensor product of the
identity of the unit with a morphism written as
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMap`. -/
public theorem leftUnitor_hom_tensorSheafMap_id
    {B B' : SheafOfModules.{u} (structureSheafRing Z)} (g : B ⟶ B') :
    ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Z)).presheaf, ((Z)).IsSheaf⟩)).map
        (((𝟙 (𝟙_ (SheafOfModules.{u} (structureSheafRing Z)))), g) : (_, _) ⟶ (_, _))) ≫
        (λ_ B').hom =
      (λ_ B).hom ≫ g := by
  refine Stacks.SheafOfModules.OnSpace.tensor_hom_ext Z fun U r b => ?_
  refine Eq.trans ?_ (congrArg (g.val.app U).hom
    (Stacks.SheafOfModules.OnSpace.leftUnitor_tmul Z B U r b)).symm
  refine Eq.trans ((congrArg ((λ_ B').hom.val.app U).hom
      (tensorSheafMap_app_toTensorSheafSection Z
        (𝟙_ (SheafOfModules.{u} (structureSheafRing Z))) B
        (𝟙_ (SheafOfModules.{u} (structureSheafRing Z))) B'
        (𝟙 (𝟙_ (SheafOfModules.{u} (structureSheafRing Z)))) g U.unop r b)).trans
    (Stacks.SheafOfModules.OnSpace.leftUnitor_tmul Z B' U r ((g.val.app U).hom b))) ?_
  exact (map_smul (g.val.app U).hom _ b).symm

end Space

/-! ### The identification on `Proj 𝒮` -/

section Proj

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- The monoidal structure of [Stacks, Tag 01CA] on the modules over `Proj 𝒮`, registered at the
spelling of the ring sheaf in which `twistingSheaf` states its own type. -/
local instance projGradedMonoidal :
    MonoidalCategory (SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮))) :=
  Stacks.SheafOfModules.OnSpace.monoidal (AlgebraicGeometry.Proj 𝒮).toRingedSpace

/-- **The `n`-th twist of the structure sheaf is the monoidal unit tensor the `n`-th twisting
sheaf.** Here `twistSheafOfModules` is the sheafified tensor product in the
`Stacks.SheafOfModules.TensorSheafification` spelling and `⊗` is the monoidal product in the
`Stacks.SheafOfModules.TensorStalkRingedSpace` spelling. -/
public theorem twistSheafOfModules_unit_eq (n : ℤ) :
    twistSheafOfModules 𝒮 (SheafOfModules.unit (AlgebraicGeometry.Proj 𝒮).ringCatSheaf) n =
      𝟙_ (SheafOfModules.{u}
        ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
          (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (ProjectiveSpectrum.Proj.structureSheaf 𝒮))) ⊗ twistingSheaf 𝒮 n := rfl

/-- **`Γ(Proj 𝒮, 𝒪 ⊗ 𝒪(n)) ≃+ Γ(Proj 𝒮, 𝒪(n))`**: the left unitor of [Stacks, Tag 01CA], read on
the sections over `⊤`. -/
public def unitTwistSectionsEquiv (n : ℤ) :
    twistedSectionsComponent 𝒮
        (SheafOfModules.unit (AlgebraicGeometry.Proj 𝒮).ringCatSheaf) n ≃+
      (twistingSheaf 𝒮 n).val.obj (op ⊤) where
  toFun s := ((λ_ (twistingSheaf 𝒮 n)).hom.val.app (op ⊤)).hom s
  invFun u := ((λ_ (twistingSheaf 𝒮 n)).inv.val.app (op ⊤)).hom u
  left_inv s :=
    congrArg (fun α : twistSheafOfModules 𝒮
          (SheafOfModules.unit (AlgebraicGeometry.Proj 𝒮).ringCatSheaf) n ⟶
        twistSheafOfModules 𝒮
          (SheafOfModules.unit (AlgebraicGeometry.Proj 𝒮).ringCatSheaf) n =>
      (α.val.app (op ⊤)).hom s) (λ_ (twistingSheaf 𝒮 n)).hom_inv_id
  right_inv u :=
    congrArg (fun α : twistingSheaf 𝒮 n ⟶ twistingSheaf 𝒮 n => (α.val.app (op ⊤)).hom u)
      (λ_ (twistingSheaf 𝒮 n)).inv_hom_id
  map_add' s t := map_add ((λ_ (twistingSheaf 𝒮 n)).hom.val.app (op ⊤)).hom s t

/-- The `n`-th twisting sheaf, as a sheaf of modules over
`Stacks.RingedSpace.structureSheafRing (Proj 𝒮).toRingedSpace`. -/
public abbrev twistObj (n : ℤ) :
    SheafOfModules.{u} (structureSheafRing (AlgebraicGeometry.Proj 𝒮).toRingedSpace) :=
  twistingSheaf 𝒮 n

/-- **The identification on a pure tensor of global sections**: `r ⊗ u ↦ r · u`. -/
public theorem unitTwistSectionsEquiv_tensorObjTmul (n : ℤ)
    (r : (AlgebraicGeometry.Proj 𝒮).toRingedSpace.presheaf.obj (op ⊤))
    (u : (twistObj 𝒮 n).val.obj (op ⊤)) :
    unitTwistSectionsEquiv 𝒮 n
        (tensorObjTmul (AlgebraicGeometry.Proj 𝒮).toRingedSpace
          (𝟙_ (SheafOfModules.{u}
            (structureSheafRing (AlgebraicGeometry.Proj 𝒮).toRingedSpace)))
          (twistObj 𝒮 n) (op ⊤)
          (unitSection (AlgebraicGeometry.Proj 𝒮).toRingedSpace (op ⊤) r) u)
      = r • u :=
  Stacks.SheafOfModules.OnSpace.leftUnitor_tmul
    (AlgebraicGeometry.Proj 𝒮).toRingedSpace (twistObj 𝒮 n) (op ⊤) r u

/-- **The inverse identification on a global section**: `u ↦ 1 ⊗ u`. -/
public theorem unitTwistSectionsEquiv_symm_apply (n : ℤ)
    (u : (twistingSheaf 𝒮 n).val.obj (op ⊤)) :
    (unitTwistSectionsEquiv 𝒮 n).symm u =
      tensorObjTmul (AlgebraicGeometry.Proj 𝒮).toRingedSpace
        (𝟙_ (SheafOfModules.{u}
          ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
            (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (ProjectiveSpectrum.Proj.structureSheaf 𝒮))))
        (twistingSheaf 𝒮 n) (op ⊤)
        (unitSection (AlgebraicGeometry.Proj 𝒮).toRingedSpace (op ⊤) 1) u :=
  Stacks.SheafOfModules.OnSpace.leftUnitor_inv_apply
    (AlgebraicGeometry.Proj 𝒮).toRingedSpace (twistingSheaf 𝒮 n) (op ⊤) u

/-- **The identification intertwines the two scalar actions.** For a homogeneous `a` of degree
`i`, the graded action of [Stacks, Tag 03GK] on `Γ(Proj 𝒮, 𝒪 ⊗ 𝒪(n))` becomes the action on
`Γ(Proj 𝒮, 𝒪(n))` of the morphism `𝒪(n) ⟶ 𝒪(i + n)` of twisting sheaves that `a` induces. -/
public theorem unitTwistSectionsEquiv_homogeneousScalar (i : ℕ) (n : ℤ) (a : 𝒮 i)
    (s : twistedSectionsComponent 𝒮
      (SheafOfModules.unit (AlgebraicGeometry.Proj 𝒮).ringCatSheaf) n) :
    unitTwistSectionsEquiv 𝒮 ((i : ℤ) + n)
        (homogeneousScalarTwistedSections 𝒮
          (SheafOfModules.unit (AlgebraicGeometry.Proj 𝒮).ringCatSheaf) i n a s)
      = ((twistScalarSheafMap 𝒮 i n ((i : ℤ) + n) rfl a).val.app (op ⊤)).hom
          (unitTwistSectionsEquiv 𝒮 n s) :=
  congrArg
    (fun α : twistSheafOfModules 𝒮
          (SheafOfModules.unit (AlgebraicGeometry.Proj 𝒮).ringCatSheaf) n ⟶
        twistingSheaf 𝒮 ((i : ℤ) + n) =>
      (α.val.app (op ⊤)).hom s)
    (leftUnitor_hom_tensorSheafMap_id (AlgebraicGeometry.Proj 𝒮).toRingedSpace
      (twistScalarSheafMap 𝒮 i n ((i : ℤ) + n) rfl a))

end Proj

end Stacks.AlgebraicGeometry.ProjTwistUnitorSections

end
