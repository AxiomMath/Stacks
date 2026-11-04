module

public import StacksFrontier.Topology.Sheaves.Modules.InverseImageStalk
import StacksCore.Tactic.StacksAttribute

/-!
# Inverse image commutes with restriction of scalars

Let `f : Y ⟶ X` be a continuous map of topological spaces and let `φ : 𝒜 ⟶ ℬ` be a homomorphism
of sheaves of commutative rings on `X`. A sheaf of `ℬ`-modules `M` can be read as a sheaf of
`𝒜`-modules along `φ` and then pulled back to `Y`, or pulled back first and then read along
`f⁻¹φ`. This file identifies the two:

`f⁻¹(M|_𝒜) = (f⁻¹M)|_{f⁻¹𝒜}`.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.underlyingRingMap`: the morphism of sheaves of rings
  underlying a homomorphism of sheaves of commutative rings.
* `AlgebraicGeometry.SheafOfModules.pushforwardRestrictScalarsIso`: restriction of scalars
  along `φ` of `f_*N` is `f_*` of the restriction of scalars along `f⁻¹φ`.
* `AlgebraicGeometry.SheafOfModules.inverseImageRestrictScalarsHom`: the canonical comparison
  morphism, the transpose of the inverse-image unit read through that identification.
* `AlgebraicGeometry.SheafOfModules.inverseImageStalkHom`: the map on stalks
  `M_{f y} ⟶ (f⁻¹M)_y` carrying a germ to the germ of the inverse-image section.
* `AlgebraicGeometry.SheafOfModules.inverseImageRestrictScalarsIso`: **the identification
  `f⁻¹(M|_𝒜) ≅ (f⁻¹M)|_{f⁻¹𝒜}`.**

## Main results

* `AlgebraicGeometry.SheafOfModules.inverseImageStalkHom_bijective`: the map on stalks is
  bijective, since it is the identification of `Stacks.InverseImageStalk`.
* `AlgebraicGeometry.SheafOfModules.inverseImageRestrictScalarsHom_unit_apply`: the comparison
  carries the inverse-image section of a local section, taken over `𝒜`, to the inverse-image
  section taken over `ℬ`.
* `AlgebraicGeometry.SheafOfModules.isIso_inverseImageRestrictScalarsHom`: **the comparison is
  an isomorphism.**

## Implementation notes

The comparison is not formal: it is the mate of the isomorphism `(f_*N)|_𝒜 ≅ f_*(N|_{f⁻¹𝒜})`,
and a mate is an isomorphism only for a reason. The reason here is that inverse image along the
unit `𝒜 ⟶ f_*f⁻¹𝒜` involves no tensoring, because the map `𝒜_{f y} ⟶ (f⁻¹𝒜)_y` it induces on
stalks is an isomorphism. That is the content of
`Stacks.InverseImageStalk.inverseImageStalkIso`, and the proof below is the reduction to it:
restriction of scalars does not change the underlying sheaf of abelian groups, so both sides
have the stalk of `M` at `f y` as their stalk at `y`, and the comparison is the identity through
those identifications because both identifications are given by the same formula on germs.

`inverseImageStalkHom` is the map on stalks of the inverse-image unit, written out as a
morphism of `AddCommGrpCat`-valued stalks rather than taken from
`Stacks.InverseImageStalk.inverseImageModuleStalkEquiv`, whose type mentions the stalk of the
sheaf of rings and is therefore not the type a morphism of sheaves of abelian groups induces.
The two agree, by `inverseImageStalkHom_bijective`'s proof, because germs exhaust a stalk.

The two restrictions of scalars in `pushforwardRestrictScalarsIso` differ by the square
`inverseImageRingHom_naturality_apply`, so the component over an open is an instance of
`ModuleCat.restrictScalarsComp'App` and `ModuleCat.restrictScalarsCongr`; the restriction maps
agree on the nose, which is why the naturality field is `rfl` after a `change`.

## References

* [Stacks Project, Tag 08RR](https://stacks.math.columbia.edu/tag/08RR)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.SheafOfModules

/-- The morphism of sheaves of rings underlying a homomorphism of sheaves of commutative
rings. -/
noncomputable abbrev underlyingRingMap {Z : TopCat.{u}} {A B : TopCat.Sheaf CommRingCat.{u} Z}
    (φ : A ⟶ B) : underlyingRingSheaf A ⟶ underlyingRingSheaf B :=
  (sheafCompose (Opens.grothendieckTopology Z) (forget₂ CommRingCat.{u} RingCat.{u})).map φ

variable {X Y : TopCat.{u}} (f : Y ⟶ X) {A B : TopCat.Sheaf CommRingCat.{u} X} (φ : A ⟶ B)

/-! ### Restriction of scalars and the direct image -/

/-- The square of the inverse-image unit, on sections: restricting scalars along `φ` and then
along the unit of `ℬ` is restricting scalars along the unit of `𝒜` and then along `f⁻¹φ`. -/
theorem inverseImageRingHom_comp_app (U : (Opens X)ᵒᵖ) :
    ((inverseImageRingHom f B).hom.app U).hom.comp ((underlyingRingMap φ).hom.app U).hom =
      ((underlyingRingMap ((TopCat.Sheaf.pullback CommRingCat.{u} f).map φ)).hom.app
          ((opensMap f).op.obj U)).hom.comp ((inverseImageRingHom f A).hom.app U).hom := by
  ext x
  exact inverseImageRingHom_naturality_apply f φ U x

/-- **Restriction of scalars commutes with the direct image.** Reading `f_*N` as a sheaf of
`𝒜`-modules along `φ` is reading `N` as a sheaf of `f⁻¹𝒜`-modules along `f⁻¹φ` and then taking
the direct image. Restriction of scalars does not change the sections, so this is the square of
the inverse-image unit, read on each open. -/
noncomputable def pushforwardRestrictScalarsIso
    (N : _root_.SheafOfModules.{u}
      (underlyingRingSheaf ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B))) :
    (_root_.SheafOfModules.restrictScalars (underlyingRingMap φ)).obj
        ((_root_.SheafOfModules.pushforward (inverseImageRingHom f B)).obj N) ≅
      (_root_.SheafOfModules.pushforward (inverseImageRingHom f A)).obj
        ((_root_.SheafOfModules.restrictScalars
          (underlyingRingMap ((TopCat.Sheaf.pullback CommRingCat.{u} f).map φ))).obj N) := by
  refine (_root_.SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U => ?_) ?_)
  · exact (ModuleCat.restrictScalarsComp'App ((underlyingRingMap φ).hom.app U).hom
        ((inverseImageRingHom f B).hom.app U).hom
        (((inverseImageRingHom f B).hom.app U).hom.comp
          ((underlyingRingMap φ).hom.app U).hom) rfl
        (N.val.obj ((opensMap f).op.obj U))).symm ≪≫
      (ModuleCat.restrictScalarsCongr (inverseImageRingHom_comp_app f φ U)).app
        (N.val.obj ((opensMap f).op.obj U)) ≪≫
      ModuleCat.restrictScalarsComp'App ((inverseImageRingHom f A).hom.app U).hom
        ((underlyingRingMap ((TopCat.Sheaf.pullback CommRingCat.{u} f).map φ)).hom.app
          ((opensMap f).op.obj U)).hom
        (((underlyingRingMap ((TopCat.Sheaf.pullback CommRingCat.{u} f).map φ)).hom.app
          ((opensMap f).op.obj U)).hom.comp ((inverseImageRingHom f A).hom.app U).hom) rfl
        (N.val.obj ((opensMap f).op.obj U))
  · intro U V g
    ext x
    change N.val.map ((opensMap f).op.map g) x = N.val.map ((opensMap f).op.map g) x
    rfl

/-! ### The comparison morphism -/

variable (M : _root_.SheafOfModules.{u} (underlyingRingSheaf B))

/-- The canonical comparison `f⁻¹(M|_𝒜) ⟶ (f⁻¹M)|_{f⁻¹𝒜}`: the transpose, along the
inverse-image/direct-image adjunction over `𝒜`, of the inverse-image unit of `M` read through
`AlgebraicGeometry.SheafOfModules.pushforwardRestrictScalarsIso`. -/
noncomputable def inverseImageRestrictScalarsHom :
    inverseImageModule f A
        ((_root_.SheafOfModules.restrictScalars (underlyingRingMap φ)).obj M) ⟶
      (_root_.SheafOfModules.restrictScalars
          (underlyingRingMap ((TopCat.Sheaf.pullback CommRingCat.{u} f).map φ))).obj
        (inverseImageModule f B M) :=
  ((inverseImageAdjunction f A).homEquiv _ _).symm
    ((_root_.SheafOfModules.restrictScalars (underlyingRingMap φ)).map
        (inverseImageModuleUnit f B M) ≫
      (pushforwardRestrictScalarsIso f φ (inverseImageModule f B M)).hom)

/-- The unit of the inverse-image/direct-image adjunction over `𝒜` at `M|_𝒜`, followed by the
direct image of the comparison, is the restriction of scalars of the inverse-image unit of `M`
followed by `AlgebraicGeometry.SheafOfModules.pushforwardRestrictScalarsIso`. -/
theorem inverseImageRestrictScalarsHom_unit :
    (inverseImageAdjunction f A).unit.app
          ((_root_.SheafOfModules.restrictScalars (underlyingRingMap φ)).obj M) ≫
        (_root_.SheafOfModules.pushforward (inverseImageRingHom f A)).map
          (inverseImageRestrictScalarsHom f φ M) =
      (_root_.SheafOfModules.restrictScalars (underlyingRingMap φ)).map
          (inverseImageModuleUnit f B M) ≫
        (pushforwardRestrictScalarsIso f φ (inverseImageModule f B M)).hom := by
  refine Eq.trans
    ((inverseImageAdjunction f A).homEquiv_unit
      (f := inverseImageRestrictScalarsHom f φ M)).symm ?_
  exact Equiv.apply_symm_apply ((inverseImageAdjunction f A).homEquiv _ _) _

/-- **The comparison carries an inverse-image section to the inverse-image section.** The
inverse-image section of a local section `m` of `M`, taken over `𝒜`, goes to the inverse-image
section of `m` taken over `ℬ`. -/
theorem inverseImageRestrictScalarsHom_unit_apply (U : (Opens X)ᵒᵖ) (m : M.val.obj U) :
    (inverseImageRestrictScalarsHom f φ M).val.app ((opensMap f).op.obj U)
        ((inverseImageModuleUnit f A
          ((_root_.SheafOfModules.restrictScalars (underlyingRingMap φ)).obj M)).val.app U m) =
      (inverseImageModuleUnit f B M).val.app U m :=
  congrArg (fun k => k.val.app U m) (inverseImageRestrictScalarsHom_unit f φ M)

/-! ### The comparison on stalks -/

/-- The map on stalks `M_{f y} ⟶ (f⁻¹M)_y` induced by the inverse-image unit: the stalk of the
unit at `f y`, followed by the comparison of the stalk of a direct image with the stalk at the
image point. -/
noncomputable def inverseImageStalkHom (O : TopCat.Sheaf CommRingCat.{u} X)
    (N : _root_.SheafOfModules.{u} (underlyingRingSheaf O)) (y : Y) :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.val.presheaf (f y) ⟶
      TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (inverseImageModule f O N).val.presheaf y :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f y)).map
      ((PresheafOfModules.toPresheaf _).map (inverseImageModuleUnit f O N).val) ≫
    TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f
      (inverseImageModule f O N).val.presheaf y

section
attribute [local implicit_reducible] TopCat.Presheaf.stalk

/-- The map on stalks `M_{f y} ⟶ (f⁻¹M)_y` carries the germ at `f y` of a section `m` of `M`
over `U` to the germ at `y` of the inverse-image section of `m` over `f⁻¹U`. -/
theorem inverseImageStalkHom_germ (O : TopCat.Sheaf CommRingCat.{u} X)
    (N : _root_.SheafOfModules.{u} (underlyingRingSheaf O)) (y : Y)
    (U : Opens X) (hy : f y ∈ U) (m : N.val.obj (op U)) :
    inverseImageStalkHom f O N y
        ((TopCat.Presheaf.germ N.val.presheaf U (f y) hy).hom m) =
      (TopCat.Presheaf.germ (inverseImageModule f O N).val.presheaf
          ((Opens.map f).obj U) y hy).hom
        (((inverseImageModuleUnit f O N).val.app (op U)).hom m) := by
  refine (ConcreteCategory.comp_apply _ _ _).trans ?_
  refine Eq.trans (congrArg (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f
      (inverseImageModule f O N).val.presheaf y).hom
    (TopCat.Presheaf.stalkFunctor_map_germ_apply U (f y) hy
      ((PresheafOfModules.toPresheaf _).map (inverseImageModuleUnit f O N).val) m)) ?_
  exact TopCat.Presheaf.stalkPushforward_germ_apply AddCommGrpCat.{u} f
    (inverseImageModule f O N).val.presheaf U y hy _

end

/-- **The map on stalks of the inverse-image unit is bijective.** It agrees on germs with
`Stacks.InverseImageStalk.inverseImageModuleStalkEquiv`, which is a bijection, and germs
exhaust a stalk. -/
theorem inverseImageStalkHom_bijective (O : TopCat.Sheaf CommRingCat.{u} X)
    (N : _root_.SheafOfModules.{u} (underlyingRingSheaf O)) (y : Y) :
    Function.Bijective (inverseImageStalkHom f O N y) := by
  have h : ∀ m, inverseImageStalkHom f O N y m =
      Stacks.InverseImageStalk.inverseImageModuleStalkEquiv f O y N m := by
    intro m
    obtain ⟨U, hy, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq N.val.presheaf m
    exact (inverseImageStalkHom_germ f O N y U hy s).trans
      (Stacks.InverseImageStalk.inverseImageModuleStalkEquiv_germ f O y N U hy s).symm
  have hb : Function.Bijective
      (Stacks.InverseImageStalk.inverseImageModuleStalkEquiv f O y N) :=
    (Stacks.InverseImageStalk.inverseImageModuleStalkEquiv f O y N).bijective
  constructor
  · exact fun a b hab => hb.injective ((h a).symm.trans (hab.trans (h b)))
  · intro c
    obtain ⟨a, ha⟩ := hb.surjective c
    exact ⟨a, (h a).trans ha⟩

/-! ### The identification -/

/-- **Inverse image commutes with restriction of scalars.** The comparison is an isomorphism:
both stalks are the stalk of `M` at the image point, through the identification of
`Stacks.InverseImageStalk`, and the comparison is the identity there because the two
identifications are given by the same formula on germs. -/
theorem isIso_inverseImageRestrictScalarsHom :
    IsIso (inverseImageRestrictScalarsHom f φ M) := by
  let R := underlyingRingSheaf ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj A)
  let ρM := (_root_.SheafOfModules.restrictScalars (underlyingRingMap φ)).obj M
  let k := inverseImageRestrictScalarsHom f φ M
  suffices h : IsIso ((_root_.SheafOfModules.toSheaf R).map k) from
    isIso_of_reflects_iso k (_root_.SheafOfModules.toSheaf R)
  apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso _).mpr
  intro y
  let t := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
    ((PresheafOfModules.toPresheaf R.obj).map k.val)
  have hcomm : ∀ m, t (inverseImageStalkHom f A ρM y m) = inverseImageStalkHom f B M y m := by
    have h : inverseImageStalkHom f A ρM y ≫ t = inverseImageStalkHom f B M y := by
      apply TopCat.Presheaf.stalk_hom_ext
      intro U hy
      apply AddCommGrpCat.hom_ext
      ext m
      show t (inverseImageStalkHom f A ρM y
          ((TopCat.Presheaf.germ ρM.val.presheaf U (f y) hy).hom m)) =
        inverseImageStalkHom f B M y
          ((TopCat.Presheaf.germ M.val.presheaf U (f y) hy).hom m)
      rw [inverseImageStalkHom_germ f A ρM y U hy m, inverseImageStalkHom_germ f B M y U hy m]
      refine (TopCat.Presheaf.stalkFunctor_map_germ_apply ((Opens.map f).obj U) y hy
        ((PresheafOfModules.toPresheaf R.obj).map k.val) _).trans ?_
      exact congrArg (TopCat.Presheaf.germ (inverseImageModule f B M).val.presheaf
          ((Opens.map f).obj U) y hy)
        (inverseImageRestrictScalarsHom_unit_apply f φ M (op U) m)
    exact fun m => ConcreteCategory.congr_hom h m
  have hA := inverseImageStalkHom_bijective f A ρM y
  have hB := inverseImageStalkHom_bijective f B M y
  refine (ConcreteCategory.isIso_iff_bijective t).mpr ⟨?_, ?_⟩
  · intro a b hab
    obtain ⟨a', rfl⟩ := hA.surjective a
    obtain ⟨b', rfl⟩ := hA.surjective b
    exact congrArg (inverseImageStalkHom f A ρM y)
      (hB.injective ((hcomm a').symm.trans (hab.trans (hcomm b'))))
  · intro c
    obtain ⟨a, ha⟩ := hB.surjective c
    exact ⟨inverseImageStalkHom f A ρM y a, (hcomm a).trans ha⟩

/-- **The identification `f⁻¹(M|_𝒜) ≅ (f⁻¹M)|_{f⁻¹𝒜}`**: taking the inverse image of a sheaf of
`ℬ`-modules read as a sheaf of `𝒜`-modules is reading the inverse image as a sheaf of
`f⁻¹𝒜`-modules. -/
noncomputable def inverseImageRestrictScalarsIso :
    inverseImageModule f A
        ((_root_.SheafOfModules.restrictScalars (underlyingRingMap φ)).obj M) ≅
      (_root_.SheafOfModules.restrictScalars
          (underlyingRingMap ((TopCat.Sheaf.pullback CommRingCat.{u} f).map φ))).obj
        (inverseImageModule f B M) :=
  haveI := isIso_inverseImageRestrictScalarsHom f φ M
  asIso (inverseImageRestrictScalarsHom f φ M)

/-- The identification carries an inverse-image section over `𝒜` to the inverse-image section
over `ℬ`. -/
theorem inverseImageRestrictScalarsIso_unit_apply (U : (Opens X)ᵒᵖ) (m : M.val.obj U) :
    (inverseImageRestrictScalarsIso f φ M).hom.val.app ((opensMap f).op.obj U)
        ((inverseImageModuleUnit f A
          ((_root_.SheafOfModules.restrictScalars (underlyingRingMap φ)).obj M)).val.app U m) =
      (inverseImageModuleUnit f B M).val.app U m :=
  inverseImageRestrictScalarsHom_unit_apply f φ M U m

end AlgebraicGeometry.SheafOfModules

end
