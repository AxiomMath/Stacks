module

public import StacksFrontier.Topology.Sheaves.RingedSpace.StalkModulePullback
public import StacksFrontier.Topology.Sheaves.Modules.Colimits

/-!
# The stalk of a pushforward on the image

Let `(i, i^♯) : (Z, 𝒪_Z) ⟶ (X, 𝒪_X)` be a morphism of ringed spaces whose underlying
continuous map is inducing — a closed embedding, for instance — and let `z : Z`. For a sheaf
of `𝒪_Z`-modules `M` the canonical map on stalks of the underlying presheaves of abelian
groups, `TopCat.Presheaf.stalkPushforward`, is an isomorphism, and this file records that it
is `𝒪_{X,i(z)}`-linear for the module structure obtained from `M_z` by restricting scalars
along the germ map `𝒪_{X,i(z)} ⟶ 𝒪_{Z,z}`:

`(i_* M)_{i(z)} ≅ (𝒪_{X,i(z)} ⟶ 𝒪_{Z,z})^* (M_z)`,

naturally in `M`. Together with the vanishing of `(i_* M)_x` off the image of `i`
(`Stacks.ClosedImmersion.isZero_stalk_modulePushforward_of_notMemRange`) this computes every
stalk of `i_* M` for a closed embedding `i`.

## Main definitions

* `Stacks.ClosedImmersion.stalkPushforwardModuleMap`: the comparison map, `stalkPushforward`
  with its `𝒪_{X,i(z)}`-linearity supplied.
* `Stacks.ClosedImmersion.stalkPushforwardModuleIso`: the comparison map as an isomorphism of
  `𝒪_{X,i(z)}`-modules.
* `Stacks.ClosedImmersion.stalkPushforwardModuleFunctorIso`: the same isomorphism read as an
  isomorphism of functors `i_* ⋙ (-)_{i(z)} ≅ (-)_z ⋙ restrictScalars`.

## Main results

* `Stacks.ClosedImmersion.stalkPushforwardModuleMap_germ`: the comparison map on a germ.
* `Stacks.ClosedImmersion.isIso_stalkPushforwardModuleMap`: the comparison map is invertible
  whenever the underlying continuous map is inducing.

## Implementation notes

The two underlying objects are *equal*, not merely isomorphic: the underlying presheaf of
abelian groups of `i_* M` is literally the topological pushforward of the underlying presheaf
of `M` (Mathlib's `PresheafOfModules.pushforwardCompToPresheaf` is `Iso.refl`), so
`TopCat.Presheaf.stalk ((i_* M).val.presheaf) (i z)` and
`TopCat.Presheaf.stalk (i.base _* M.val.presheaf) (i z)` are definitionally equal and no
transport on carriers is needed. The whole content is therefore the `map_smul'` field, a germ
computation: a scalar `r` and a germ `s` are represented over a common open `U ∋ i(z)`, the
scalar action on sections of `i_* M` over `U` is the action of `𝒪_Z(i^{-1}U)` through
`i^♯` (true by `rfl`, since `SheafOfModules.pushforward` is
`pushforward₀ ⋙ restrictScalars`), and the germ of that action is computed twice by
`AlgebraicGeometry.SheafOfModules.germ_hom_smul` — once on `X`, once on `Z` — the two being
matched by `Stacks.RingedSpace.stalkRingMap_germ`.

Invertibility is Mathlib's `TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing`
transported across `CategoryTheory.ConcreteCategory.isIso_iff_bijective`: both `AddCommGrpCat`
and `ModuleCat` have a forgetful functor that reflects isomorphisms, and the two underlying
functions are the same function.

Nothing here is tagged. Stacks 0E23's single clause asserts that a base-change comparison map
is an isomorphism; this is one of its inputs, and the statement itself is Stacks 00AE read on
the image rather than off it, which is not a clause of 00AE.

## References

* [Stacks Project, Tag 00AE](https://stacks.math.columbia.edu/tag/00AE)
* [Stacks Project, Tag 0E23](https://stacks.math.columbia.edu/tag/0E23)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

noncomputable section

namespace Stacks.ClosedImmersion

universe u

variable {Z X : RingedSpace.{u, u}} (i : Z ⟶ X) (z : Z.carrier)

/-- **The stalk of `i_* M` on the image, as a map of `𝒪_{X,i(z)}`-modules.** The canonical map
`(i_* M)_{i(z)} ⟶ M_z` on stalks of the underlying presheaves of abelian groups is linear over
the germ map `Stacks.RingedSpace.stalkRingMap i z : 𝒪_{X,i(z)} ⟶ 𝒪_{Z,z}`.

No hypothesis on `i` is needed for the map; `isIso_stalkPushforwardModuleMap` shows it is
invertible as soon as the underlying continuous map is inducing. -/
def stalkPushforwardModuleMap (M : SheafOfModules.{u} (structureSheafRing Z)) :
    AlgebraicGeometry.SheafOfModules.stalkObj (structureSheafRing X) (i.hom.base z)
        ((modulePushforward i).obj M) ⟶
      (ModuleCat.restrictScalars.{u, u, u} (Stacks.RingedSpace.stalkRingMap i z).hom).obj
        (AlgebraicGeometry.SheafOfModules.stalkObj (structureSheafRing Z) z M) :=
  ConcreteCategory.ofHom (C := ModuleCat _)
    { toFun := fun s => (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u}
        i.hom.base M.val.presheaf z).hom s
      map_add' := by intro a b; exact map_add _ _ _
      map_smul' := by
        intro r s
        obtain ⟨V, hV, a, ha⟩ := TopCat.Presheaf.exists_germ_eq (structureSheafRing X).obj r
        obtain ⟨W, hW, m, hm⟩ :=
          TopCat.Presheaf.exists_germ_eq ((modulePushforward i).obj M).val.presheaf s
        let U : Opens X.carrier := V ⊓ W
        have hU : i.hom.base z ∈ U := ⟨hV, hW⟩
        let a' : (structureSheafRing X).obj.obj (op U) :=
          ((structureSheafRing X).obj.map (homOfLE (inf_le_left : U ≤ V)).op).hom a
        let m' : ((modulePushforward i).obj M).val.obj (op U) :=
          (((modulePushforward i).obj M).val.presheaf.map
            (homOfLE (inf_le_right : U ≤ W)).op).hom m
        have hga : (TopCat.Presheaf.germ (C := RingCat.{u}) (X := X.carrier)
            (structureSheafRing X).obj U (i.hom.base z) hU).hom a' = r := by
          rw [show a' = ((structureSheafRing X).obj.map
              (homOfLE (inf_le_left : U ≤ V)).op).hom a from rfl,
            TopCat.Presheaf.germ_res_apply]
          exact ha
        have hgm : (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X.carrier)
            ((modulePushforward i).obj M).val.presheaf U (i.hom.base z) hU).hom m' = s := by
          rw [show m' = (((modulePushforward i).obj M).val.presheaf.map
              (homOfLE (inf_le_right : U ≤ W)).op).hom m from rfl,
            TopCat.Presheaf.germ_res_apply]
          exact hm
        -- the comparison map on a germ over `U`
        have key : ∀ t : ((modulePushforward i).obj M).val.obj (op U),
            (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u}
                i.hom.base M.val.presheaf z).hom
              ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X.carrier)
                ((modulePushforward i).obj M).val.presheaf U (i.hom.base z) hU).hom t) =
              (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := Z.carrier)
                M.val.presheaf ((opensMap i).obj U) z hU).hom t := fun t =>
          TopCat.Presheaf.stalkPushforward_germ_apply AddCommGrpCat.{u} i.hom.base
            M.val.presheaf U z hU t
        -- the scalar action on `X`, then on `Z`, then matched by `stalkRingMap_germ`
        have eX := AlgebraicGeometry.SheafOfModules.germ_hom_smul (structureSheafRing X)
          (i.hom.base z) ((modulePushforward i).obj M).val U hU a' m'
        have eZ := AlgebraicGeometry.SheafOfModules.germ_hom_smul (structureSheafRing Z) z M.val
          ((opensMap i).obj U) hU ((structureSheafHom i).hom.app (op U) a') m'
        have eR := Stacks.RingedSpace.stalkRingMap_germ i z U hU a'
        have e1 : r • s = (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X.carrier)
            ((modulePushforward i).obj M).val.presheaf U (i.hom.base z) hU).hom (a' • m') := by
          rw [← hga, ← hgm]
          exact eX.symm
        change (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u}
              i.hom.base M.val.presheaf z).hom (r • s) =
          (Stacks.RingedSpace.stalkRingMap i z).hom r •
            (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u}
              i.hom.base M.val.presheaf z).hom s
        calc (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u}
              i.hom.base M.val.presheaf z).hom (r • s)
            = (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u}
                i.hom.base M.val.presheaf z).hom
              ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X.carrier)
                ((modulePushforward i).obj M).val.presheaf U (i.hom.base z) hU).hom
                  (a' • m')) := by rw [e1]
          _ = (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := Z.carrier)
                M.val.presheaf ((opensMap i).obj U) z hU).hom (a' • m') := key _
          _ = (TopCat.Presheaf.germ (C := RingCat.{u}) (X := Z.carrier)
                (structureSheafRing Z).obj ((opensMap i).obj U) z hU).hom
                  ((structureSheafHom i).hom.app (op U) a') •
              (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := Z.carrier)
                M.val.presheaf ((opensMap i).obj U) z hU).hom m' := eZ
          _ = (Stacks.RingedSpace.stalkRingMap i z).hom
                ((TopCat.Presheaf.germ (C := RingCat.{u}) (X := X.carrier)
                  (structureSheafRing X).obj U (i.hom.base z) hU).hom a') •
              (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := Z.carrier)
                M.val.presheaf ((opensMap i).obj U) z hU).hom m' := by rw [eR]
          _ = (Stacks.RingedSpace.stalkRingMap i z).hom r •
              (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u}
                i.hom.base M.val.presheaf z).hom s := by
                rw [hga, ← key m', hgm] }

/-- The comparison map `(i_* M)_{i(z)} ⟶ M_z` sends the germ at `i(z)` of a section of `i_* M`
over `U` to the germ at `z` of the same section, read over `i^{-1}U`. -/
theorem stalkPushforwardModuleMap_germ (M : SheafOfModules.{u} (structureSheafRing Z))
    (U : Opens X.carrier) (hU : i.hom.base z ∈ U)
    (t : ((modulePushforward i).obj M).val.obj (op U)) :
    (stalkPushforwardModuleMap i z M).hom
        ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X.carrier)
          ((modulePushforward i).obj M).val.presheaf U (i.hom.base z) hU).hom t) =
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := Z.carrier)
        M.val.presheaf ((opensMap i).obj U) z hU).hom t :=
  TopCat.Presheaf.stalkPushforward_germ_apply AddCommGrpCat.{u} i.hom.base
    M.val.presheaf U z hU t

/-- **The comparison map is natural in `M`.** Both sides send the germ at `i(z)` of a section
`t` of `i_* M` over `U` to the germ at `z` of `f(t)`, read over `i^{-1}U`; that `i_* f` and `f`
act by the same map on sections over `U` is `rfl`, since `PresheafOfModules.pushforward` acts on
morphisms by reindexing. -/
theorem stalkPushforwardModuleMap_naturality {M N : SheafOfModules.{u} (structureSheafRing Z)}
    (f : M ⟶ N) :
    AlgebraicGeometry.SheafOfModules.stalkMap (structureSheafRing X) (i.hom.base z)
        ((modulePushforward i).map f) ≫ stalkPushforwardModuleMap i z N =
      stalkPushforwardModuleMap i z M ≫
        (ModuleCat.restrictScalars.{u, u, u} (Stacks.RingedSpace.stalkRingMap i z).hom).map
          (AlgebraicGeometry.SheafOfModules.stalkMap (structureSheafRing Z) z f) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun s => ?_)
  obtain ⟨U, hU, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    ((modulePushforward i).obj M).val.presheaf s
  have hL : (AlgebraicGeometry.SheafOfModules.stalkMap (structureSheafRing X) (i.hom.base z)
        ((modulePushforward i).map f)).hom
        ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X.carrier)
          ((modulePushforward i).obj M).val.presheaf U (i.hom.base z) hU).hom t) =
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X.carrier)
        ((modulePushforward i).obj N).val.presheaf U (i.hom.base z) hU).hom
          (((modulePushforward i).map f).val.app (op U) t) :=
    TopCat.Presheaf.stalkFunctor_map_germ_apply U (i.hom.base z) hU
      ((PresheafOfModules.toPresheaf (structureSheafRing X).obj).map
        ((modulePushforward i).map f).val) t
  have hR : ((ModuleCat.restrictScalars.{u, u, u} (Stacks.RingedSpace.stalkRingMap i z).hom).map
        (AlgebraicGeometry.SheafOfModules.stalkMap (structureSheafRing Z) z f)).hom
        ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := Z.carrier)
          M.val.presheaf ((opensMap i).obj U) z hU).hom t) =
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := Z.carrier)
        N.val.presheaf ((opensMap i).obj U) z hU).hom
          (f.val.app (op ((opensMap i).obj U)) t) :=
    TopCat.Presheaf.stalkFunctor_map_germ_apply ((opensMap i).obj U) z hU
      ((PresheafOfModules.toPresheaf (structureSheafRing Z).obj).map f.val) t
  show (stalkPushforwardModuleMap i z N).hom
      ((AlgebraicGeometry.SheafOfModules.stalkMap (structureSheafRing X) (i.hom.base z)
        ((modulePushforward i).map f)).hom
          ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X.carrier)
            ((modulePushforward i).obj M).val.presheaf U (i.hom.base z) hU).hom t)) =
    ((ModuleCat.restrictScalars.{u, u, u} (Stacks.RingedSpace.stalkRingMap i z).hom).map
      (AlgebraicGeometry.SheafOfModules.stalkMap (structureSheafRing Z) z f)).hom
        ((stalkPushforwardModuleMap i z M).hom
          ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X.carrier)
            ((modulePushforward i).obj M).val.presheaf U (i.hom.base z) hU).hom t))
  rw [stalkPushforwardModuleMap_germ i z M U hU t, hR, hL, stalkPushforwardModuleMap_germ]
  rfl

/-- **The comparison map is invertible when the base is inducing.** The underlying map of
abelian groups is `TopCat.Presheaf.stalkPushforward`, an isomorphism by
`TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing`, and both `ModuleCat` and
`AddCommGrpCat` have a forgetful functor reflecting isomorphisms. -/
theorem isIso_stalkPushforwardModuleMap
    (hi : Topology.IsInducing (ConcreteCategory.hom i.hom.base))
    (M : SheafOfModules.{u} (structureSheafRing Z)) :
    IsIso (stalkPushforwardModuleMap i z M) := by
  have h : IsIso (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u}
      i.hom.base M.val.presheaf z) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing AddCommGrpCat.{u} hi
      M.val.presheaf z
  have hb := ConcreteCategory.bijective_of_isIso
    (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} i.hom.base M.val.presheaf z)
  exact (ConcreteCategory.isIso_iff_bijective _).mpr hb

/-- **The stalk of `i_* M` on the image.** For a morphism of ringed spaces with inducing
underlying map and `z : Z`, the stalk of `i_* M` at `i(z)` is the stalk of `M` at `z` with
scalars restricted along the germ map `𝒪_{X,i(z)} ⟶ 𝒪_{Z,z}`. -/
def stalkPushforwardModuleIso (hi : Topology.IsInducing (ConcreteCategory.hom i.hom.base))
    (M : SheafOfModules.{u} (structureSheafRing Z)) :
    AlgebraicGeometry.SheafOfModules.stalkObj (structureSheafRing X) (i.hom.base z)
        ((modulePushforward i).obj M) ≅
      (ModuleCat.restrictScalars.{u, u, u} (Stacks.RingedSpace.stalkRingMap i z).hom).obj
        (AlgebraicGeometry.SheafOfModules.stalkObj (structureSheafRing Z) z M) :=
  have := isIso_stalkPushforwardModuleMap i z hi M
  asIso (stalkPushforwardModuleMap i z M)

/-- `stalkPushforwardModuleIso` as an isomorphism of functors
`i_* ⋙ (-)_{i(z)} ≅ (-)_z ⋙ restrictScalars`. -/
def stalkPushforwardModuleFunctorIso
    (hi : Topology.IsInducing (ConcreteCategory.hom i.hom.base)) :
    modulePushforward i ⋙
        AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing X) (i.hom.base z) ≅
      AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Z) z ⋙
        ModuleCat.restrictScalars.{u, u, u} (Stacks.RingedSpace.stalkRingMap i z).hom :=
  NatIso.ofComponents (fun M => stalkPushforwardModuleIso i z hi M)
    (fun f => stalkPushforwardModuleMap_naturality i z f)

end Stacks.ClosedImmersion

end
