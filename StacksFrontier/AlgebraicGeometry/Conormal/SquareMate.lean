module

public import StacksFrontier.AlgebraicGeometry.Conormal.IsoSquareUnit

/-!
# The mate of a commuting square, and the conormal quotient map across it

Let
```
Z₁ --j₁--→ X₁
|          |
a          b
↓          ↓
Z₂ --j₂--→ X₂
```
be a commuting square of ringed spaces. Pulling back and pushing forward sheaves of modules along
the two ways around it gives two comparison isomorphisms,

* `RingedSpaceModuleAdjunction.modulePullbackSquareIso`, `b^* ⋙ (j₁)^* ≅ (j₂)^* ⋙ a^*`,
* `RingedSpaceModuleAdjunction.modulePushforwardSquareIso`, `(j₁)_* ⋙ b_* ≅ a_* ⋙ (j₂)_*`,

and the first is the **mate** of the second
(`RingedSpaceModuleAdjunction.conjugateEquiv_modulePullbackSquareIso_hom`). Reading that
mate correspondence on units gives `RingedSpaceModuleAdjunction.unit_modulePullbackSquareIso`.

For a morphism `j`, the *conormal quotient map* `ℐ_j ⟶ j_* 𝒞_j` of [Stacks Project, Tag 01R3]
part (1) is the unit of `j^* ⊣ j_*` at the ideal sheaf. Across an isomorphism square, the
transport of the conormal sheaf carries the conormal quotient map of `j₁` to that of `j₂`; this is
`Stacks.ClosedImmersion.ambientPushforwardConormalIsoOfSquare_comp_unit`.

## Main definitions

* `RingedSpaceModuleAdjunction.modulePullbackSquareIso` and
  `RingedSpaceModuleAdjunction.modulePushforwardSquareIso` are the two comparisons above,
  for an **arbitrary** commuting square of morphisms of ringed spaces.
  `Stacks.ClosedImmersion.modulePullbackIsoOfSquare` is the first of them in the special case
  where the two vertical morphisms are isomorphisms, which
  `Stacks.ClosedImmersion.modulePullbackIsoOfSquare_eq` records.

## Main results

* `RingedSpaceModuleAdjunction.conjugateEquiv_modulePullbackSquareIso_hom`: the pullback
  comparison and the pushforward comparison correspond under the mate bijection
  `CategoryTheory.conjugateEquiv`.
* `RingedSpaceModuleAdjunction.unit_modulePullbackSquareIso`: that correspondence read on
  units. Going around the square one way, the unit of `b^* ⊣ b_*` followed by `b_*` of the unit of
  `(j₁)^* ⊣ (j₁)_*` and by the two comparisons is, the other way, the unit of `(j₂)^* ⊣ (j₂)_*`
  followed by `(j₂)_*` of the unit of `a^* ⊣ a_*`.
* `Stacks.ClosedImmersion.ambientPushforwardConormalIsoOfSquare_comp_unit`: the transport of the
  conormal sheaf across an isomorphism square is compatible with the conormal quotient maps.
* `RingedSpaceModuleAdjunction.conjugateEquiv_modulePullbackComp_inv` and
  `RingedSpaceModuleAdjunction.conjugateEquiv_modulePullbackCongr`: the mates of the inverse
  composition law and of the transport along an equality of morphisms.
* `RingedSpaceModuleAdjunction.modulePullbackSquareIso_inv` and
  `RingedSpaceModuleAdjunction.modulePushforwardSquareIso_hom_app` write the two
  comparisons out.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction 
open AlgebraicGeometry AlgebraicGeometry.RingedSpace

universe u

namespace RingedSpaceModuleAdjunction

/-! ### Two mate computations -/

variable {X Y Z : RingedSpace.{u, u}}

/-- **The inverse of `RingedSpaceModuleAdjunction.modulePullbackComp` has the inverse of
`RingedSpaceModuleAdjunction.modulePushforwardComp` as its mate.** -/
theorem conjugateEquiv_modulePullbackComp_inv (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv (modulePullbackPushforwardAdjunction (f ≫ g))
        ((modulePullbackPushforwardAdjunction g).comp
          (modulePullbackPushforwardAdjunction f)) (modulePullbackComp f g).inv =
      (modulePushforwardComp f g).inv :=
  (Iso.hom_comp_eq_id (modulePushforwardComp f g)).mp
    (((congrArg (fun z => z ≫ conjugateEquiv _ _ (modulePullbackComp f g).inv)
        (conjugateEquiv_modulePullbackComp_hom f g)).symm).trans
      (conjugateEquiv_comm _ _ (modulePullbackComp f g).inv_hom_id))

/-- **The mate of the transport of a pullback along an equality of morphisms of ringed spaces is
the transport of the pushforward.** -/
theorem conjugateEquiv_modulePullbackCongr {p q : X ⟶ Y} (h : p = q) :
    conjugateEquiv (modulePullbackPushforwardAdjunction q)
        (modulePullbackPushforwardAdjunction p) (modulePullbackCongr h).hom =
      (eqToIso (congrArg modulePushforward h)).inv := by
  subst h
  rw [modulePullbackCongr, eqToIso_refl, Iso.refl_hom, eqToIso_refl, Iso.refl_inv,
    conjugateEquiv_id]

/-- The components of the transport of a pushforward along an equality of morphisms of ringed
spaces are the transports of the objects. -/
theorem modulePushforwardCongr_hom_app {p q : X ⟶ Y} (h : p = q)
    (N : SheafOfModules.{u} (structureSheafRing X)) :
    (eqToIso (congrArg modulePushforward h)).hom.app N =
      eqToHom (congrArg (fun r : X ⟶ Y => (modulePushforward r).obj N) h) := by
  subst h
  rfl

/-! ### The two comparisons attached to a commuting square -/

section Square

variable {Z₁ Z₂ X₁ X₂ : RingedSpace.{u, u}} (a : Z₁ ⟶ Z₂) (b : X₁ ⟶ X₂) (j₁ : Z₁ ⟶ X₁)
  (j₂ : Z₂ ⟶ X₂)

/-- **`b^* ⋙ (j₁)^* ≅ (j₂)^* ⋙ a^*`: the two ways around a commuting square of ringed spaces
agree on pullbacks.** It is the composition law
`RingedSpaceModuleAdjunction.modulePullbackComp` on each side, joined by the transport
along the equality of the two composites. -/
def modulePullbackSquareIso (comm : j₁ ≫ b = a ≫ j₂) :
    modulePullback b ⋙ modulePullback j₁ ≅ modulePullback j₂ ⋙ modulePullback a :=
  (modulePullbackComp j₁ b).symm ≪≫ modulePullbackCongr comm ≪≫ modulePullbackComp a j₂

/-- **`(j₁)_* ⋙ b_* ≅ a_* ⋙ (j₂)_*`: the two ways around a commuting square of ringed spaces
agree on pushforwards.** It is the composition law
`RingedSpaceModuleAdjunction.modulePushforwardComp` on each side, joined by the transport along
the equality of the two composites. -/
def modulePushforwardSquareIso (comm : j₁ ≫ b = a ≫ j₂) :
    modulePushforward j₁ ⋙ modulePushforward b ≅ modulePushforward a ⋙ modulePushforward j₂ :=
  modulePushforwardComp j₁ b ≪≫ eqToIso (congrArg modulePushforward comm) ≪≫
    (modulePushforwardComp a j₂).symm

/-- **`RingedSpaceModuleAdjunction.modulePullbackSquareIso` written out backwards.** Its
inverse is the inverse of the composition law at `(a, j₂)`, the transport along the square's
commutativity read backwards, and the composition law at `(j₁, b)`. -/
theorem modulePullbackSquareIso_inv (comm : j₁ ≫ b = a ≫ j₂) :
    (modulePullbackSquareIso a b j₁ j₂ comm).inv =
      ((modulePullbackComp a j₂).inv ≫ (modulePullbackCongr comm.symm).hom) ≫
        (modulePullbackComp j₁ b).hom :=
  rfl

/-- The components of `RingedSpaceModuleAdjunction.modulePushforwardSquareIso`: the two
pushforward composition isomorphisms and the transport along the square's commutativity. -/
theorem modulePushforwardSquareIso_hom_app (comm : j₁ ≫ b = a ≫ j₂)
    (N : SheafOfModules.{u} (structureSheafRing Z₁)) :
    (modulePushforwardSquareIso a b j₁ j₂ comm).hom.app N =
      ((modulePushforwardComp j₁ b).app N).hom ≫
        eqToHom (congrArg (fun r : Z₁ ⟶ X₂ => (modulePushforward r).obj N) comm) ≫
          ((modulePushforwardComp a j₂).app N).inv := by
  rw [modulePushforwardSquareIso, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    NatTrans.comp_app, modulePushforwardCongr_hom_app comm, Iso.app_hom, Iso.app_inv]

/-- **The pullback comparison of a commuting square is the mate of the pushforward comparison.**
Under the mate bijection `CategoryTheory.conjugateEquiv` between natural transformations of left
adjoints and natural transformations of the corresponding right adjoints,
`RingedSpaceModuleAdjunction.modulePullbackSquareIso` corresponds to the inverse of
`RingedSpaceModuleAdjunction.modulePushforwardSquareIso`. -/
theorem conjugateEquiv_modulePullbackSquareIso_hom (comm : j₁ ≫ b = a ≫ j₂) :
    conjugateEquiv ((modulePullbackPushforwardAdjunction j₂).comp
          (modulePullbackPushforwardAdjunction a))
        ((modulePullbackPushforwardAdjunction b).comp
          (modulePullbackPushforwardAdjunction j₁))
        (modulePullbackSquareIso a b j₁ j₂ comm).hom =
      (modulePushforwardSquareIso a b j₁ j₂ comm).inv := by
  rw [modulePullbackSquareIso, modulePushforwardSquareIso, Iso.trans_hom, Iso.trans_hom,
    Iso.symm_hom, Iso.trans_inv, Iso.trans_inv, Iso.symm_inv,
    ← conjugateEquiv_modulePullbackComp_hom a j₂,
    ← conjugateEquiv_modulePullbackCongr comm,
    ← conjugateEquiv_modulePullbackComp_inv j₁ b,
    conjugateEquiv_comp, conjugateEquiv_comp]

/-- **The comparisons of a commuting square carry the units of the two adjunctions into each
other.** For an `𝒪_{X₂}`-module `M`, the unit of `b^* ⊣ b_*` followed by `b_*` of the unit of
`(j₁)^* ⊣ (j₁)_*`, by `(j₁)_* b_*` of
`RingedSpaceModuleAdjunction.modulePullbackSquareIso` and by
`RingedSpaceModuleAdjunction.modulePushforwardSquareIso` is the unit of `(j₂)^* ⊣ (j₂)_*`
followed by `(j₂)_*` of the unit of `a^* ⊣ a_*`. -/
theorem unit_modulePullbackSquareIso (comm : j₁ ≫ b = a ≫ j₂)
    (M : SheafOfModules.{u} (structureSheafRing X₂)) :
    ((modulePullbackPushforwardAdjunction b).unit.app M ≫
        (modulePushforward b).map
          ((modulePullbackPushforwardAdjunction j₁).unit.app
            ((modulePullback b).obj M))) ≫
      (modulePushforward j₁ ⋙ modulePushforward b).map
          ((modulePullbackSquareIso a b j₁ j₂ comm).hom.app M) ≫
        (modulePushforwardSquareIso a b j₁ j₂ comm).hom.app
          ((modulePullback a).obj ((modulePullback j₂).obj M)) =
    (modulePullbackPushforwardAdjunction j₂).unit.app M ≫
      (modulePushforward j₂).map
        ((modulePullbackPushforwardAdjunction a).unit.app ((modulePullback j₂).obj M)) := by
  have h := CategoryTheory.unit_conjugateEquiv
    ((modulePullbackPushforwardAdjunction j₂).comp (modulePullbackPushforwardAdjunction a))
    ((modulePullbackPushforwardAdjunction b).comp (modulePullbackPushforwardAdjunction j₁))
    (modulePullbackSquareIso a b j₁ j₂ comm).hom M
  rw [conjugateEquiv_modulePullbackSquareIso_hom, Adjunction.comp_unit_app,
    Adjunction.comp_unit_app] at h
  simp only [Functor.comp_obj] at h
  rw [← Category.assoc, ← h, Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _

end Square

end RingedSpaceModuleAdjunction

namespace Stacks.ClosedImmersion

variable {Z₁ Z₂ X₁ X₂ : RingedSpace.{u, u}} (a : Z₁ ≅ Z₂) (b : X₁ ≅ X₂) (j₁ : Z₁ ⟶ X₁)
  (j₂ : Z₂ ⟶ X₂)

/-- `Stacks.ClosedImmersion.modulePullbackIsoOfSquare` is
`RingedSpaceModuleAdjunction.modulePullbackSquareIso` of the same square. -/
theorem modulePullbackIsoOfSquare_eq (comm : j₁ ≫ b.hom = a.hom ≫ j₂) :
    modulePullbackIsoOfSquare a b j₁ j₂ comm =
      modulePullbackSquareIso a.hom b.hom j₁ j₂ comm :=
  rfl

/-- **The conormal-sheaf transport across an isomorphism square carries the conormal quotient map
of `j₁` to that of `j₂`.** Precisely: `b_*` of the unit of `(j₁)^* ⊣ (j₁)_*` at `ℐ_{j₁}`, followed
by `Stacks.ClosedImmersion.ambientPushforwardConormalIsoOfSquare`, is
`Stacks.ClosedImmersion.pushforwardIdealSheafIsoOfSquare` followed by the unit of
`(j₂)^* ⊣ (j₂)_*` at `ℐ_{j₂}`. -/
theorem ambientPushforwardConormalIsoOfSquare_comp_unit (comm : j₁ ≫ b.hom = a.hom ≫ j₂) :
    (modulePushforward b.hom).map
          ((modulePullbackPushforwardAdjunction j₁).unit.app (idealSheaf j₁)) ≫
        (ambientPushforwardConormalIsoOfSquare a b j₁ j₂ comm).hom =
      (pushforwardIdealSheafIsoOfSquare a b j₁ j₂ comm).hom ≫
        (modulePullbackPushforwardAdjunction j₂).unit.app (idealSheaf j₂) := by
  refine (Iso.cancel_iso_hom_right _ _ ((modulePushforward j₂).mapIso
    (modulePullbackPushforwardUnitIsoOfIso a (conormalSheaf j₂)))).mp ?_
  have hW : ((modulePushforward j₂).mapIso
      (modulePullbackPushforwardUnitIsoOfIso a (conormalSheaf j₂))).hom =
      (modulePushforward j₂).map
        ((modulePullbackPushforwardAdjunction a.hom).unit.app (conormalSheaf j₂)) := rfl
  have hXi : (ambientPushforwardConormalIsoOfSquare a b j₁ j₂ comm).hom =
      (modulePushforwardSquareIso a.hom b.hom j₁ j₂ comm).hom.app (conormalSheaf j₁) ≫
        (modulePushforward j₂).map
          (pushforwardConormalSheafIsoOfSquare a b j₁ j₂ comm).hom := by
    rw [modulePushforwardSquareIso_hom_app, Category.assoc, Category.assoc]
    exact (Iso.inv_comp_eq _).mp (ambientPushforwardConormalIsoOfSquare_hom a b j₁ j₂ comm)
  have hS : (conormalSheafIsoOfSquare a b j₁ j₂ comm).hom =
      (modulePullback j₁).map (idealSheafIsoOfSquare a b j₁ j₂ comm).hom ≫
        (modulePullbackSquareIso a.hom b.hom j₁ j₂ comm).hom.app (idealSheaf j₂) := by
    rw [conormalSheafIsoOfSquare, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
      modulePullbackIsoOfSquare_eq]
  have hnatsq := (modulePushforwardSquareIso a.hom b.hom j₁ j₂ comm).hom.naturality
    (conormalSheafIsoOfSquare a b j₁ j₂ comm).hom
  have hL : ((modulePushforward b.hom).map
        ((modulePullbackPushforwardAdjunction j₁).unit.app (idealSheaf j₁)) ≫
      (ambientPushforwardConormalIsoOfSquare a b j₁ j₂ comm).hom) ≫
      ((modulePushforward j₂).mapIso
        (modulePullbackPushforwardUnitIsoOfIso a (conormalSheaf j₂))).hom =
      (modulePushforward b.hom).map
          ((modulePullbackPushforwardAdjunction j₁).unit.app (idealSheaf j₁)) ≫
        (modulePushforward j₁ ⋙ modulePushforward b.hom).map
            (conormalSheafIsoOfSquare a b j₁ j₂ comm).hom ≫
          (modulePushforwardSquareIso a.hom b.hom j₁ j₂ comm).hom.app
            ((modulePullback a.hom).obj (conormalSheaf j₂)) := by
    rw [hW, hXi, Category.assoc, Category.assoc, ← CategoryTheory.Functor.map_comp,
      pushforwardConormalSheafIsoOfSquare_hom_comp_unit, ← Functor.comp_map, ← hnatsq]
  have hu : (modulePullbackPushforwardAdjunction j₁).unit.app (idealSheaf j₁) ≫
      (modulePushforward j₁).map ((modulePullback j₁).map
        (idealSheafIsoOfSquare a b j₁ j₂ comm).hom) =
      (idealSheafIsoOfSquare a b j₁ j₂ comm).hom ≫
        (modulePullbackPushforwardAdjunction j₁).unit.app
          ((modulePullback b.hom).obj (idealSheaf j₂)) := by
    have h := (modulePullbackPushforwardAdjunction j₁).unit.naturality
      (idealSheafIsoOfSquare a b j₁ j₂ comm).hom
    simpa only [Functor.id_map, Functor.comp_map] using h.symm
  have hhead : (pushforwardIdealSheafIsoOfSquare a b j₁ j₂ comm).hom ≫
      (modulePullbackPushforwardAdjunction b.hom).unit.app (idealSheaf j₂) ≫
      (modulePushforward b.hom).map ((modulePullbackPushforwardAdjunction j₁).unit.app
        ((modulePullback b.hom).obj (idealSheaf j₂))) =
      (modulePushforward b.hom).map
          ((modulePullbackPushforwardAdjunction j₁).unit.app (idealSheaf j₁)) ≫
        (modulePushforward j₁ ⋙ modulePushforward b.hom).map
          ((modulePullback j₁).map (idealSheafIsoOfSquare a b j₁ j₂ comm).hom) := by
    rw [← Category.assoc, pushforwardIdealSheafIsoOfSquare_hom_comp_unit, Functor.comp_map,
      ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, hu]
  refine hL.trans ?_
  rw [hW, Category.assoc,
    ← unit_modulePullbackSquareIso a.hom b.hom j₁ j₂ comm (idealSheaf j₂), hS,
    CategoryTheory.Functor.map_comp]
  simp only [← Category.assoc]
  simp only [← Category.assoc] at hhead
  rw [hhead]

end Stacks.ClosedImmersion

end
