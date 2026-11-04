module

public import StacksFrontier.AlgebraicGeometry.SheafifyStalk.StalkMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkColimit
public import StacksFrontier.Topology.Sheaves.Modules.Differentials.InverseImage
public import StacksFrontier.Topology.Sheaves.Skyscraper.Modules

/-!
# The stalks of the inverse image of a sheaf of modules

Let `f : Y ⟶ X` be a continuous map, let `O` be a sheaf of commutative rings on `X` and let `M`
be a sheaf of `O`-modules. The stalk at a point `y` of `Y` of the inverse image `f⁻¹M` is the
stalk of `M` at `f y`, semilinearly over the isomorphism `O_{f y} ≅ (f⁻¹O)_y` of the stalks of
the rings; the identification carries the germ at `f y` of a section `s` of `M` to the germ at
`y` of the inverse-image section of `s`.

## Main definitions

* `Stacks.InverseImageStalk.skyscraperObj`, `Stacks.InverseImageStalk.skyscraperFunctor`: the
  skyscraper sheaf of `O`-modules at a point, for a sheaf of commutative rings on a space.
* `Stacks.InverseImageStalk.stalkFunctor`: the stalk at a point of a sheaf of `O`-modules, as a
  module over the stalk of `O`.
* `Stacks.InverseImageStalk.ringStalkEquiv`: the isomorphism `O_{f y} ≅ (f⁻¹O)_y`, as a ring
  equivalence.
* `Stacks.InverseImageStalk.pushforwardSkyscraperIso`: the direct image along `f` of the
  skyscraper at `y` is the skyscraper at `f y`, its value read over `O_{f y}` along
  `ringStalkEquiv`.
* `Stacks.InverseImageStalk.inverseImageStalkIso`: the identification
  `(f⁻¹M)_y ≅ M_{f y}`, as a natural isomorphism of functors.
* `Stacks.InverseImageStalk.inverseImageModuleStalkIso` and
  `Stacks.InverseImageStalk.inverseImageModuleStalkEquiv`: the same identification at a single
  sheaf of modules, as an isomorphism of `(f⁻¹O)_y`-modules and as a semilinear equivalence
  over `ringStalkEquiv`.
* `Stacks.InverseImageStalk.semilinearEquivOfRestrictScalarsIso`: an isomorphism of modules
  over a ring whose source has its scalars transported along the inverse of a ring
  isomorphism, read as a semilinear equivalence over that isomorphism.

## Main results

* `Stacks.InverseImageStalk.stalkSkyscraperAdjunction`: the stalk functor on sheaves of
  `O`-modules is left adjoint to the skyscraper functor.
* `Stacks.InverseImageStalk.ringStalkEquiv_germ`: the ring isomorphism carries the germ at
  `f y` of a section of `O` to the germ at `y` of its inverse-image section.
* `Stacks.InverseImageStalk.inverseImageStalkIso_hom_germ` and
  `Stacks.InverseImageStalk.inverseImageModuleStalkEquiv_germ`: the identification carries the
  germ at `y` of the inverse-image section of `s` to the germ of `s` at `f y`, and back. This
  pins the identification down.
* `Stacks.InverseImageStalk.inverseImageStalkIso_hom_naturality`: naturality in the sheaf of
  modules, that is, compatibility with the maps induced on stalks by a morphism.

## Route and why

`SheafOfModules.pullback` is a chosen left adjoint, so it has no description of its sections
and offers no formula for its stalks. The identification here is therefore obtained by
comparing right adjoints, exactly as in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkColimit`: both

`f⁻¹(-) ⋙ stalk_y`  and  `stalk_{f y} ⋙ restrictScalars (ringStalkEquiv)⁻¹`

are left adjoints, the first by the inverse-image/direct-image adjunction composed with the
stalk–skyscraper adjunction and the second by the stalk–skyscraper adjunction composed with
the equivalence a ring isomorphism induces on modules; and their right adjoints are isomorphic
because the direct image of a skyscraper is a skyscraper. No filtered colimit interchange and
no tensor product occurs: since the map on ring stalks is an isomorphism, the base change that
appears for a general morphism of ringed spaces is trivial here.

The germ formula comes from the same comparison rather than from a separate computation. The
identification is `CategoryTheory.Adjunction.leftAdjointUniq` of the two adjunctions, so
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` equates the two units; the unit of the
first is the inverse-image unit followed by a germ and the unit of the second is a germ, so
evaluating that equation at a section is the germ formula.

That the map on ring stalks is an isomorphism is not reproved: `ringStalkEquiv` is
`Stacks.SheafifyStalk.stalkSheafPullbackIso` for the sheaf of rings, and its germ formula is
`Stacks.SheafifyStalk.stalkSheafPullbackIso_inv_eq`, which writes the inverse of that
comparison as the stalk of the unit followed by `TopCat.Presheaf.stalkPushforward`.

## Implementation notes

The stalk of a sheaf of modules is taken over the `CommRingCat`-valued stalk of `O`, as in
`Stacks.ModuleSkyscraper`, rather than over the `RingCat`-valued stalk of the underlying sheaf
of rings used by `AlgebraicGeometry.SheafOfModules.stalkObj`. The two stalks have the same
underlying abelian group, but only the first is a commutative ring, which is what the
base-change machinery for modules is stated over, and the ring comparison that this file needs
exists only for sheaves of commutative rings. The underlying bijection of
`Stacks.InverseImageStalk.inverseImageModuleStalkEquiv` is a bijection between the stalks of
the underlying presheaves of abelian groups, so it is the same map whichever of the two stalks
of a sheaf of modules it is read through; only its semilinearity refers to the
`CommRingCat`-valued stalk.

The stalk–skyscraper adjunction for a sheaf of commutative rings on a space is
`Stacks.Modules.stalkSkyscraperAdjunction`. `Stacks.InverseImageStalk.skyscraperObj`,
`skyscraperFunctor`, `stalkFunctor` and `stalkSkyscraperAdjunction` are that development named
at the spelling `AlgebraicGeometry.SheafOfModules.underlyingRingSheaf O` of the underlying
sheaf of rings, which is a reducible abbreviation of the `sheafCompose` application the
adjunction is stated over.

The two comparison maps of skyscrapers are reindexings of sections along `y ∈ f⁻¹V ↔ f y ∈ V`,
written as `g ↦ fun p ↦ g ⟨p.down⟩` rather than as the identity, because the two index types
are definitionally and not syntactically equal; their composites are then the identity by
`rfl`. The semilinearity of each is the germ formula for `ringStalkEquiv`: a section of `O`
over `V` acts on the left through the inverse-image unit followed by the germ at `y`, and on
the right through the germ at `f y` followed by the ring isomorphism.

A semilinear equivalence needs `RingHomInvPair` for the two directions of the ring
equivalence, which Mathlib provides as lemmas rather than instances; they are made local
instances for the section that states it.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 08TM](https://stacks.math.columbia.edu/tag/08TM)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry Stacks.ModuleSkyscraper

universe u

noncomputable section

namespace Stacks.InverseImageStalk

/-! ### The stalk–skyscraper adjunction for a sheaf of commutative rings on a space -/

section Adjunction

variable {X : TopCat.{u}} (O : TopCat.Sheaf CommRingCat.{u} X) (x : X)

/-- The skyscraper sheaf of `O`-modules at `x` with value an `O_x`-module `A`: its sections over
an open `U` are `A` when `x ∈ U` and zero otherwise.

This is `Stacks.Modules.skyscraper`, named here at the spelling of the underlying sheaf of
rings that the rest of this file uses. -/
def skyscraperObj (A : ModuleCat.{u} ↑(O.presheaf.stalk x)) :
    SheafOfModules.{u} (SheafOfModules.underlyingRingSheaf O) :=
  Stacks.Modules.skyscraper O x A

/-- The skyscraper at `x`, as a functor from `O_x`-modules to sheaves of `O`-modules. -/
def skyscraperFunctor :
    ModuleCat.{u} ↑(O.presheaf.stalk x) ⥤
      SheafOfModules.{u} (SheafOfModules.underlyingRingSheaf O) :=
  Stacks.Modules.skyscraperFunctor O x

/-- The stalk at `x`, as a functor from sheaves of `O`-modules to modules over the stalk of
`O` at `x`. -/
def stalkFunctor :
    SheafOfModules.{u} (SheafOfModules.underlyingRingSheaf O) ⥤
      ModuleCat.{u} ↑(O.presheaf.stalk x) :=
  Stacks.Modules.stalkSheafFunctor O x

/-- **The stalk functor on sheaves of `O`-modules is left adjoint to the skyscraper functor.**
This is `Stacks.Modules.stalkSkyscraperAdjunction`, whose hom bijection is
`Stacks.Modules.skyscraperHomEquiv`. -/
def stalkSkyscraperAdjunction : stalkFunctor O x ⊣ skyscraperFunctor O x :=
  Stacks.Modules.stalkSkyscraperAdjunction O x


end Adjunction

/-! ### The stalks of the inverse image of the sheaf of rings -/

section Rings

variable {X Y : TopCat.{u}} (f : Y ⟶ X) (O : TopCat.Sheaf CommRingCat.{u} X) (y : Y)

/-- **The stalk of the inverse image of a sheaf of commutative rings**, `(f⁻¹O)_y ≅ O_{f y}`,
as a ring equivalence in the direction `O_{f y} ≅ (f⁻¹O)_y`. -/
def ringStalkEquiv : ↑(O.presheaf.stalk (f y)) ≃+*
    ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f).obj O).presheaf.stalk y) :=
  (Stacks.SheafifyStalk.stalkSheafPullbackIso
    CommRingCat.{u} f O y).symm.commRingCatIsoToRingEquiv

/-- The isomorphism of ring stalks as a ring homomorphism `O_{f y} →+* (f⁻¹O)_y`, in the
spelling that the semilinear hypotheses and `ModuleCat.restrictScalars` consume. -/
abbrev ringStalkHom : ↑(O.presheaf.stalk (f y)) →+*
    ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f).obj O).presheaf.stalk y) :=
  ringStalkEquiv f O y

/-- The inverse isomorphism of ring stalks as a ring homomorphism `(f⁻¹O)_y →+* O_{f y}`. -/
abbrev ringStalkInvHom :
    ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f).obj O).presheaf.stalk y) →+*
      ↑(O.presheaf.stalk (f y)) :=
  (ringStalkEquiv f O y).symm

section
attribute [local implicit_reducible] TopCat.Presheaf.stalk

/-- **The ring isomorphism on stalks carries a germ to the germ of the inverse-image section.**
The germ at `f y` of a section `r` of `O` over `U` is sent to the germ at `y` of the image of
`r` under the unit `O ⟶ f_* f⁻¹O`. -/
theorem ringStalkEquiv_germ (U : Opens X) (hU : f y ∈ U) (r : O.obj.obj (op U)) :
    ringStalkEquiv f O y ((O.presheaf.germ U (f y) hU).hom r) =
      (((TopCat.Sheaf.pullback CommRingCat.{u} f).obj O).presheaf.germ
          ((Opens.map f).obj U) y hU).hom
        (AlgebraicGeometry.SheafOfModules.inverseImageRingUnitApp f O (op U) r) := by
  refine Eq.trans (congrArg
    (fun m : O.presheaf.stalk (f y) ⟶
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj O).presheaf.stalk y =>
      m.hom ((O.presheaf.germ U (f y) hU).hom r))
    (Stacks.SheafifyStalk.stalkSheafPullbackIso_inv_eq CommRingCat.{u} f O y)) ?_
  refine (ConcreteCategory.comp_apply _ _ _).trans ?_
  refine Eq.trans (congrArg
    (TopCat.Presheaf.stalkPushforward CommRingCat.{u} f
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj O).presheaf y).hom
    (TopCat.Presheaf.stalkFunctor_map_germ_apply U (f y) hU _ r)) ?_
  exact TopCat.Presheaf.stalkPushforward_germ_apply CommRingCat.{u} f _ U y hU _

end

end Rings

/-! ### The direct image of a skyscraper -/

section Skyscraper

variable {X Y : TopCat.{u}} (f : Y ⟶ X) (O : TopCat.Sheaf CommRingCat.{u} X) (y : Y)
  (A : ModuleCat.{u} ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f).obj O).presheaf.stalk y))

/-- The comparison `f_*(sky_y A) ⟶ sky_{f y} A`, a reindexing of sections along
`y ∈ f⁻¹V ↔ f y ∈ V`. -/
def pushforwardSkyscraperHom :
    (SheafOfModules.pushforward
        (AlgebraicGeometry.SheafOfModules.inverseImageRingHom f O)).obj
      (skyscraperObj ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj O) y A) ⟶
    skyscraperObj O (f y) ((ModuleCat.restrictScalars (ringStalkHom f O y)).obj A) :=
  ⟨PresheafOfModules.homMk
    { app := fun _V => AddCommGrpCat.ofHom
        { toFun := fun g p => g ⟨p.down⟩
          map_zero' := rfl
          map_add' := fun _ _ => rfl } }
    (fun V r g => funext fun p => by
      change (((TopCat.Sheaf.pullback CommRingCat.{u} f).obj O).presheaf.germ
            ((Opens.map f).obj V.unop) y p.down).hom
          (AlgebraicGeometry.SheafOfModules.inverseImageRingUnitApp f O V r) • g ⟨p.down⟩
        = ringStalkEquiv f O y ((O.presheaf.germ V.unop (f y) p.down).hom r) • g ⟨p.down⟩
      rw [ringStalkEquiv_germ f O y V.unop p.down r])⟩

/-- The reindexing of `Stacks.InverseImageStalk.pushforwardSkyscraperHom` in the other
direction. -/
def pushforwardSkyscraperInv :
    skyscraperObj O (f y)
        ((ModuleCat.restrictScalars (ringStalkHom f O y)).obj A) ⟶
    (SheafOfModules.pushforward
        (AlgebraicGeometry.SheafOfModules.inverseImageRingHom f O)).obj
      (skyscraperObj ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj O) y A) :=
  ⟨PresheafOfModules.homMk
    { app := fun _V => AddCommGrpCat.ofHom
        { toFun := fun g p => g ⟨p.down⟩
          map_zero' := rfl
          map_add' := fun _ _ => rfl } }
    (fun V r g => funext fun p => by
      change ringStalkEquiv f O y ((O.presheaf.germ V.unop (f y) p.down).hom r) • g ⟨p.down⟩
        = (((TopCat.Sheaf.pullback CommRingCat.{u} f).obj O).presheaf.germ
            ((Opens.map f).obj V.unop) y p.down).hom
          (AlgebraicGeometry.SheafOfModules.inverseImageRingUnitApp f O V r) • g ⟨p.down⟩
      rw [ringStalkEquiv_germ f O y V.unop p.down r])⟩

/-- **The direct image of a skyscraper at `y` is the skyscraper at `f y`**, with its value read
as a module over `O_{f y}` along the isomorphism of ring stalks. -/
def pushforwardSkyscraperObjIso :
    (SheafOfModules.pushforward
        (AlgebraicGeometry.SheafOfModules.inverseImageRingHom f O)).obj
      (skyscraperObj ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj O) y A) ≅
    skyscraperObj O (f y) ((ModuleCat.restrictScalars (ringStalkHom f O y)).obj A) where
  hom := pushforwardSkyscraperHom f O y A
  inv := pushforwardSkyscraperInv f O y A
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- `Stacks.InverseImageStalk.pushforwardSkyscraperObjIso`, naturally in the value: the two
right adjoints of the stalk formula for an inverse image are isomorphic. -/
def pushforwardSkyscraperIso :
    skyscraperFunctor ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj O) y ⋙
        SheafOfModules.pushforward
          (AlgebraicGeometry.SheafOfModules.inverseImageRingHom f O) ≅
      ModuleCat.restrictScalars (ringStalkHom f O y) ⋙ skyscraperFunctor O (f y) :=
  NatIso.ofComponents (pushforwardSkyscraperObjIso f O y) (fun _ => rfl)

end Skyscraper

/-! ### The stalks of the inverse image of a sheaf of modules -/

section Modules

variable {X Y : TopCat.{u}} (f : Y ⟶ X) (O : TopCat.Sheaf CommRingCat.{u} X) (y : Y)

/-- Taking the inverse image and then the stalk at `y` is a left adjoint, with right adjoint
the skyscraper at `y` followed by the direct image. -/
def pullbackStalkAdjunction :
    (SheafOfModules.pullback
          (AlgebraicGeometry.SheafOfModules.inverseImageRingHom f O) ⋙
        stalkFunctor ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj O) y) ⊣
      (ModuleCat.restrictScalars (ringStalkHom f O y) ⋙
        skyscraperFunctor O (f y)) :=
  ((SheafOfModules.pullbackPushforwardAdjunction
    (AlgebraicGeometry.SheafOfModules.inverseImageRingHom f O)).comp
      (stalkSkyscraperAdjunction ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj O) y)).ofNatIsoRight
    (pushforwardSkyscraperIso f O y)

/-- Taking the stalk at `f y` and then transporting the scalars along the inverse of the
isomorphism of ring stalks is a left adjoint, with the same right adjoint as
`Stacks.InverseImageStalk.pullbackStalkAdjunction`. -/
def stalkRestrictScalarsAdjunction :
    (stalkFunctor O (f y) ⋙
        ModuleCat.restrictScalars (ringStalkInvHom f O y)) ⊣
      (ModuleCat.restrictScalars (ringStalkHom f O y) ⋙
        skyscraperFunctor O (f y)) :=
  (stalkSkyscraperAdjunction O (f y)).comp
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (ringStalkEquiv f O y)).symm.toAdjunction

/-- **The stalk of the inverse image of a sheaf of modules is the stalk at the image point**:
`(f⁻¹M)_y ≅ M_{f y}`, as modules over `(f⁻¹O)_y` through the isomorphism of ring stalks, and
naturally in `M`.

Both sides are left adjoints and
`Stacks.InverseImageStalk.pushforwardSkyscraperIso` identifies their right adjoints, so
`CategoryTheory.Adjunction.leftAdjointUniq` identifies them. No description of the sections of
the inverse image is used. -/
def inverseImageStalkIso :
    (SheafOfModules.pullback
          (AlgebraicGeometry.SheafOfModules.inverseImageRingHom f O) ⋙
        stalkFunctor ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj O) y) ≅
      (stalkFunctor O (f y) ⋙
        ModuleCat.restrictScalars (ringStalkInvHom f O y)) :=
  Adjunction.leftAdjointUniq (pullbackStalkAdjunction f O y)
    (stalkRestrictScalarsAdjunction f O y)

variable (M : SheafOfModules.{u} (SheafOfModules.underlyingRingSheaf O))

/-- **The stalk of the inverse image of a sheaf of modules**, at a single sheaf of modules:
`(f⁻¹M)_y ≅ M_{f y}`, as an isomorphism of `(f⁻¹O)_y`-modules, the right-hand side read over
`(f⁻¹O)_y` along the inverse of the isomorphism of ring stalks. -/
def inverseImageModuleStalkIso :
    stalkObj (AlgebraicGeometry.SheafOfModules.inverseImageModule f O M).val y ≅
      (ModuleCat.restrictScalars (ringStalkInvHom f O y)).obj
        (stalkObj M.val (f y)) :=
  (inverseImageStalkIso f O y).app M

section
attribute [local implicit_reducible] TopCat.Presheaf.stalk

variable (U : Opens X) (hU : f y ∈ U) (s : M.val.obj (op U))

/-- **The identification of stalks carries the germ of an inverse-image section to a germ.**
The germ at `y` of the image of a section `s` of `M` over `U` under the unit
`M ⟶ f_* f⁻¹M` is sent to the germ of `s` at `f y`. This pins the identification down, since
every element of the stalk is such a germ. -/
theorem inverseImageStalkIso_hom_germ :
    ((inverseImageStalkIso f O y).hom.app M).hom
        ((TopCat.Presheaf.germ
            (AlgebraicGeometry.SheafOfModules.inverseImageModule f O M).val.presheaf
            ((Opens.map f).obj U) y hU).hom
          (((AlgebraicGeometry.SheafOfModules.inverseImageModuleUnit f O M).val.app
            (op U)).hom s))
      = (TopCat.Presheaf.germ M.val.presheaf U (f y) hU).hom s :=
  congrFun (ConcreteCategory.congr_hom
    (congrArg (fun m : M ⟶ (ModuleCat.restrictScalars (ringStalkHom f O y) ⋙
        skyscraperFunctor O (f y)).obj ((stalkFunctor O (f y) ⋙
          ModuleCat.restrictScalars (ringStalkInvHom f O y)).obj M) =>
      m.val.app (op U))
      (Adjunction.unit_leftAdjointUniq_hom_app (pullbackStalkAdjunction f O y)
        (stalkRestrictScalarsAdjunction f O y) M)) s) ⟨hU⟩

/-- `Stacks.InverseImageStalk.inverseImageStalkIso_hom_germ` read on the inverse: the germ of
`s` at `f y` is carried to the germ at `y` of the inverse-image section of `s`. -/
theorem inverseImageStalkIso_inv_germ :
    ((inverseImageStalkIso f O y).inv.app M).hom
        ((TopCat.Presheaf.germ M.val.presheaf U (f y) hU).hom s)
      = (TopCat.Presheaf.germ
          (AlgebraicGeometry.SheafOfModules.inverseImageModule f O M).val.presheaf
          ((Opens.map f).obj U) y hU).hom
        (((AlgebraicGeometry.SheafOfModules.inverseImageModuleUnit f O M).val.app
          (op U)).hom s) :=
  (congrArg ((inverseImageStalkIso f O y).inv.app M).hom
      (inverseImageStalkIso_hom_germ f O y M U hU s)).symm.trans
    (ConcreteCategory.congr_hom ((inverseImageStalkIso f O y).app M).hom_inv_id _)

end

/-- **Naturality in the sheaf of modules.** For a morphism `g : M ⟶ N` the square relating the
maps induced on stalks by `f⁻¹g` and by `g` commutes. -/
theorem inverseImageStalkIso_hom_naturality
    {M N : SheafOfModules.{u} (SheafOfModules.underlyingRingSheaf O)} (g : M ⟶ N) :
    (stalkFunctor ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj O) y).map
          ((SheafOfModules.pullback
            (AlgebraicGeometry.SheafOfModules.inverseImageRingHom f O)).map g) ≫
        (inverseImageStalkIso f O y).hom.app N =
      (inverseImageStalkIso f O y).hom.app M ≫
        (ModuleCat.restrictScalars (ringStalkInvHom f O y)).map
          ((stalkFunctor O (f y)).map g) :=
  (inverseImageStalkIso f O y).hom.naturality g

end Modules

/-! ### The identification as a semilinear equivalence -/

section Semilinear

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- A ring isomorphism `e : R ≃+* S` turns an isomorphism of `S`-modules whose source is an
`R`-module with its scalars transported along `e⁻¹` into an `e`-semilinear equivalence. -/
def semilinearEquivOfRestrictScalarsIso {R S : Type u} [Ring R] [Ring S] (e : R ≃+* S)
    {A : ModuleCat.{u} R} {B : ModuleCat.{u} S}
    (i : (ModuleCat.restrictScalars (e.symm : S →+* R)).obj A ≅ B) :
    A ≃ₛₗ[(e : R →+* S)] B where
  toFun := i.hom.hom
  map_add' a b := map_add i.hom.hom a b
  map_smul' r a :=
    (congrArg i.hom.hom (congrArg (fun z => z • a) (e.symm_apply_apply r).symm)).trans
      (i.hom.hom.map_smul (e r) a)
  invFun := i.inv.hom
  left_inv a := ConcreteCategory.congr_hom i.hom_inv_id a
  right_inv b := ConcreteCategory.congr_hom i.inv_hom_id b

variable {X Y : TopCat.{u}} (f : Y ⟶ X) (O : TopCat.Sheaf CommRingCat.{u} X) (y : Y)
  (M : SheafOfModules.{u} (SheafOfModules.underlyingRingSheaf O))

/-- **The stalk of the inverse image of a sheaf of modules is the stalk at the image point**,
as a bijection semilinear over the isomorphism `O_{f y} ≅ (f⁻¹O)_y` of ring stalks:
`M_{f y} ≃ (f⁻¹M)_y`.

The type is left to be inferred, as for
`Stacks.ModuleSkyscraper.pullbackStalkLinearEquiv`: the two stalks are modules over the stalks
of the sheaves of rings through the module structure that `Stacks.ModuleSkyscraper.stalkObj`
installs, which is not available as a global instance at the spelling of the ring that the
underlying sheaf of rings of `O` produces. -/
def inverseImageModuleStalkEquiv :=
  semilinearEquivOfRestrictScalarsIso (ringStalkEquiv f O y)
    (inverseImageModuleStalkIso f O y M).symm

section
attribute [local implicit_reducible] TopCat.Presheaf.stalk

/-- The semilinear equivalence carries the germ of a section `s` of `M` at `f y` to the germ at
`y` of the inverse-image section of `s`. -/
theorem inverseImageModuleStalkEquiv_germ (U : Opens X) (hU : f y ∈ U)
    (s : M.val.obj (op U)) :
    inverseImageModuleStalkEquiv f O y M
        ((TopCat.Presheaf.germ M.val.presheaf U (f y) hU).hom s)
      = (TopCat.Presheaf.germ
          (AlgebraicGeometry.SheafOfModules.inverseImageModule f O M).val.presheaf
          ((Opens.map f).obj U) y hU).hom
        (((AlgebraicGeometry.SheafOfModules.inverseImageModuleUnit f O M).val.app
          (op U)).hom s) :=
  inverseImageStalkIso_inv_germ f O y M U hU s

end

end Semilinear

end Stacks.InverseImageStalk

end

end
