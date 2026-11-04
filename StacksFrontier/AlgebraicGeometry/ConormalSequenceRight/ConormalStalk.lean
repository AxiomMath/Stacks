module

public import StacksFrontier.AlgebraicGeometry.AmpleWire.UnitStalk
public import StacksFrontier.AlgebraicGeometry.ConormalSheaf.Basic
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.ImmersionStalk
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction
public import StacksFrontier.Topology.Sheaves.Sheafify.ModuleStalkTensor

/-!
# The stalks of the conormal sheaf of an immersion

Let `i : Z ⟶ X` be an immersion of schemes, factored as the closed immersion
`j = i.liftCoborder` into the open subscheme `W = i.coborderRange` followed by the inclusion of
`W`. The conormal sheaf `𝒞_{Z/X}` is the pullback along `j` of the defining ideal sheaf `ℐ` of
`j`. This file computes its stalks: at a point `z` of `Z` the stalk is `J/J²`, where `J` is the
kernel of the map of local rings `𝒪_{W, j z} ⟶ 𝒪_{Z, z}`.

## Main definitions

* `Stacks.ConormalSequenceRight.stalkIdealMap` and
  `Stacks.ConormalSequenceRight.stalkIdealEquiv`: the stalk of an ideal subsheaf of the
  structure sheaf, identified with its ideal of germs inside the stalk of the structure sheaf.
* `Stacks.ConormalSequenceRight.definingIdealStalkEquiv`: the stalk of the defining ideal sheaf
  of an immersion at `j z`, identified with `RingHom.ker (j.stalkMap z)`.
* `Stacks.ConormalSequenceRight.tensorKerEquivCotangent`: for a surjective algebra map `A ⟶ C`
  with kernel `J`, the base change `C ⊗_A J` is the conormal module `J/J²`.

## Main results

* `Stacks.ConormalSequenceRight.stalkIdealEquiv_germ`,
  `Stacks.ConormalSequenceRight.definingIdealStalkEquiv_coe` and
  `Stacks.ConormalSequenceRight.tensorKerEquivCotangent_tmul_one`: the three identifications on
  generators. Each is pinned on germs, respectively on the generator `1 ⊗ a`, so that none of
  them can be altered by an automorphism of its target.
* `Stacks.ConormalSequenceRight.exists_conormalSheafStalkCotangentEquiv`: **the stalk of the
  conormal sheaf of an immersion at `z` is `J/J²` for `J = ker (𝒪_{W, j z} ⟶ 𝒪_{Z, z})`**, by an
  isomorphism carrying the conormal class of a local section `f` of the defining ideal sheaf to
  the class of the germ of `f`.

## Route

Three identifications, composed.

1. The stalk of an ideal subsheaf `ℐ ⊆ 𝒪_X` is its ideal of germs. The map into the stalk of
   `𝒪_X` is the stalk of the inclusion, read through the comparison of the abelian-group stalk
   of `𝒪_X` with its ring stalk (`Stacks.Ample.unitStalkIso`). It is injective because two
   sections of `ℐ` with the same germ in `𝒪_X` already agree on a smaller open, hence have the
   same germ in `ℐ`; its image is the germ ideal by definition.
2. For the defining ideal sheaf of an immersion, that germ ideal is the kernel of the map of
   local rings: this is
   `Stacks.AlgebraicGeometry.RegularIdealSheaf.stalkIdeal_definingIdealOfHom_eq_ker`.
3. The stalk of the pullback is the base change of the stalk
   (`RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv`), and the base change of
   an ideal to the quotient by it is the conormal module, by `Ideal.quotTensorEquivCotangent`
   transported along `Ideal.quotientKerAlgEquivOfSurjective`.

The conclusion is stated as an existence statement with the germ formula attached, as
`RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv` is: the comparison it
provides is not canonical on the nose, and the formula is what pins the composite down.

## Implementation notes

The equivalence is stated additively. Its three factors are linear over three different rings —
`𝒪_{Z, z}` for the pullback comparison, `𝒪_{W, j z}` for the other two — and no common ring acts
on all five objects without a change of scalars that would have to be carried through every
statement. Nothing downstream needs more: exactness of a sequence of sheaves is checked on
stalks as a statement about the underlying additive maps.

A presheaf of modules whose ring presheaf is written out as `𝒪_X ⋙ forget₂ CommRingCat RingCat`
is used throughout (`idealPresheaf`, `conormalRetyped`). The module structure on a stalk is found
by instance search only at that spelling, and neither `AlgebraicGeometry.Scheme.ringCatSheaf` nor
`structureSheafRing` is unfolded by the search.

The kernel is that of the map of local rings of the *closed factor* `j`, not of `i` itself. The
two agree under the isomorphism of local rings `𝒪_{X, i z} ≅ 𝒪_{W, j z}` induced by the open
immersion `W ⟶ X`; that transport is not performed here.

## References

* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.RegularIdealSheaf
open scoped TensorProduct

universe u

namespace Stacks.ConormalSequenceRight

section IdealStalk

variable {X : Scheme.{u}}
  (J : (Stacks.RingedSpace.structureSheafModule X.toLocallyRingedSpace.toRingedSpace).Submodule)
  (x : X)

/-- The underlying presheaf of modules of an ideal subsheaf, with its ring presheaf written out
so that its stalk is found to be a module over the stalk of the structure sheaf. -/
noncomputable abbrev idealPresheaf :
    PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
  J.toSheafOfModules.val

/-- The structure sheaf as a module over itself, with its ring presheaf written out. -/
noncomputable abbrev unitPresheaf :
    PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
  (Stacks.RingedSpace.structureSheafModule X.toLocallyRingedSpace.toRingedSpace).val

/-- **The stalk of an ideal subsheaf, mapped into the stalk of the structure sheaf.** It is the
stalk of the inclusion, read through the comparison of the abelian-group stalk of `𝒪_X` with its
ring stalk. -/
noncomputable def stalkIdealMap :
    TopCat.Presheaf.stalk (C := Ab.{u}) (idealPresheaf J).presheaf x →ₗ[X.presheaf.stalk x]
      X.presheaf.stalk x where
  toFun m := Stacks.Ample.unitStalkFun X x
    (Stacks.Sheafify.ModuleStalkTensor.stalkLinearMapOfHom X.presheaf x
      (M := idealPresheaf J) (N := unitPresheaf) J.ι.val m)
  map_add' a b := by
    rw [map_add]
    exact Stacks.Ample.unitStalkFun_add X x _ _
  map_smul' r m := by
    rw [map_smul]
    exact Stacks.Ample.unitStalkFun_smul X x r _

/-- The map of `stalkIdealMap` sends the germ of a section of the ideal subsheaf to the germ of
that section in the structure sheaf. -/
theorem stalkIdealMap_germ (U : Opens X) (hx : x ∈ U) (a : (idealPresheaf J).obj (op U)) :
    stalkIdealMap J x
        (TopCat.Presheaf.germ (C := Ab.{u}) (idealPresheaf J).presheaf U x hx a) =
      X.presheaf.germ U x hx a.1 := by
  refine Eq.trans (congrArg (Stacks.Ample.unitStalkFun X x)
    (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
      ((PresheafOfModules.toPresheaf (X.presheaf ⋙ forget₂ CommRingCat RingCat)).map J.ι.val)
      a)) ?_
  exact Stacks.Ample.unitStalkFun_germ X x U hx _

/-- The germ of a section of the subsheaf lies in its ideal of germs. -/
private theorem germ_mem_stalkIdeal (U : Opens X) (hx : x ∈ U) (a : (idealPresheaf J).obj (op U)) :
    X.presheaf.germ U x hx a.1 ∈ Stacks.RingedSpace.stalkIdeal (X := X.toLocallyRingedSpace) J x :=
  (Stacks.RingedSpace.mem_stalkIdeal_iff J).mpr ⟨U, hx, a.1, a.2, rfl⟩

/-- The image of `stalkIdealMap` lies in the ideal of germs of sections of the subsheaf. -/
theorem stalkIdealMap_mem (m : TopCat.Presheaf.stalk (C := Ab.{u}) (idealPresheaf J).presheaf x) :
    stalkIdealMap J x m ∈ Stacks.RingedSpace.stalkIdeal (X := X.toLocallyRingedSpace) J x := by
  obtain ⟨U, hx, a, rfl⟩ :=
    TopCat.Presheaf.exists_germ_eq (C := Ab.{u}) (idealPresheaf J).presheaf m
  rw [stalkIdealMap_germ J x U hx a]
  exact germ_mem_stalkIdeal J x U hx a

/-- `stalkIdealMap` is injective: two sections of the subsheaf with the same germ in the
structure sheaf already agree on a smaller open, hence have the same germ in the subsheaf. -/
theorem stalkIdealMap_injective : Function.Injective (stalkIdealMap J x) := by
  refine (injective_iff_map_eq_zero _).mpr ?_
  intro m hm
  obtain ⟨U, hx, a, rfl⟩ :=
    TopCat.Presheaf.exists_germ_eq (C := Ab.{u}) (idealPresheaf J).presheaf m
  rw [stalkIdealMap_germ J x U hx a] at hm
  have h0 : X.presheaf.germ U x hx a.1 =
      X.presheaf.germ ⊤ x (by trivial) (0 : X.presheaf.obj (op ⊤)) := by simpa using hm
  obtain ⟨V, hxV, iVU, iVtop, hV⟩ :=
    X.presheaf.germ_eq x hx (by trivial) a.1 (0 : X.presheaf.obj (op ⊤)) h0
  have hres : (idealPresheaf J).map iVU.op a = 0 := by
    apply Subtype.ext
    refine Eq.trans ?_ (hV.trans (map_zero _))
    rfl
  refine Eq.trans (TopCat.Presheaf.germ_res_apply (C := Ab.{u}) (idealPresheaf J).presheaf
    iVU x hxV a).symm ?_
  rw [show (idealPresheaf J).presheaf.map iVU.op a = 0 from hres]
  exact map_zero _

/-- Every germ of a section of the subsheaf is in the image of `stalkIdealMap`. -/
theorem stalkIdealMap_surjective_onto (y : X.presheaf.stalk x)
    (hy : y ∈ Stacks.RingedSpace.stalkIdeal (X := X.toLocallyRingedSpace) J x) :
    ∃ m, stalkIdealMap J x m = y := by
  obtain ⟨U, hx, s, hs, rfl⟩ := (Stacks.RingedSpace.mem_stalkIdeal_iff J).mp hy
  exact ⟨TopCat.Presheaf.germ (C := Ab.{u}) (idealPresheaf J).presheaf U x hx ⟨s, hs⟩,
    stalkIdealMap_germ J x U hx ⟨s, hs⟩⟩

/-- **The stalk of an ideal subsheaf is its ideal of germs** inside the stalk of the structure
sheaf. -/
noncomputable def stalkIdealEquiv :
    TopCat.Presheaf.stalk (C := Ab.{u}) (idealPresheaf J).presheaf x ≃ₗ[X.presheaf.stalk x]
      ↥(Stacks.RingedSpace.stalkIdeal (X := X.toLocallyRingedSpace) J x) :=
  LinearEquiv.ofBijective
    ((stalkIdealMap J x).codRestrict _ (stalkIdealMap_mem J x))
    ⟨fun a b hab => stalkIdealMap_injective J x (congrArg Subtype.val hab),
      fun y => by
        obtain ⟨m, hm⟩ := stalkIdealMap_surjective_onto J x y.1 y.2
        exact ⟨m, Subtype.ext hm⟩⟩

/-- The identification of the stalk of an ideal subsheaf with its ideal of germs sends the germ
of a section to that germ. -/
theorem stalkIdealEquiv_germ (U : Opens X) (hx : x ∈ U) (a : (idealPresheaf J).obj (op U)) :
    (stalkIdealEquiv J x
        (TopCat.Presheaf.germ (C := Ab.{u}) (idealPresheaf J).presheaf U x hx a) : _) =
      X.presheaf.germ U x hx a.1 :=
  stalkIdealMap_germ J x U hx a

variable {Z : Scheme.{u}}

/-- **The stalk of the defining ideal sheaf of an immersion is the kernel of the map of local
rings.** -/
noncomputable def definingIdealStalkEquiv (j : Z ⟶ X) [IsImmersion j] (z : Z) :
    TopCat.Presheaf.stalk (C := Ab.{u})
        (idealPresheaf (definingIdealOfHom j)).presheaf (j.base z) ≃ₗ[X.presheaf.stalk (j.base z)]
      ↥(RingHom.ker (j.stalkMap z).hom) :=
  (stalkIdealEquiv (definingIdealOfHom j) (j.base z)).trans
    (LinearEquiv.ofEq _ _ (stalkIdeal_definingIdealOfHom_eq_ker j z))

/-- That identification sends the germ of a section of the defining ideal sheaf to its germ. -/
theorem definingIdealStalkEquiv_coe (j : Z ⟶ X) [IsImmersion j] (z : Z)
    (V : Opens X) (hz : j.base z ∈ V)
    (a : (idealPresheaf (definingIdealOfHom j)).obj (op V)) :
    (definingIdealStalkEquiv j z
        (TopCat.Presheaf.germ (C := Ab.{u})
          (idealPresheaf (definingIdealOfHom j)).presheaf V (j.base z) hz a) : _) =
      X.presheaf.germ V (j.base z) hz a.1 :=
  stalkIdealMap_germ (definingIdealOfHom j) (j.base z) V hz a

/-- The germ of a section of the defining ideal sheaf dies in the local ring of the source. -/
theorem germ_mem_ker_stalkMap (j : Z ⟶ X) [IsImmersion j] (z : Z)
    (V : Opens X) (hz : j.base z ∈ V)
    (a : (idealPresheaf (definingIdealOfHom j)).obj (op V)) :
    X.presheaf.germ V (j.base z) hz a.1 ∈ RingHom.ker (j.stalkMap z).hom := by
  rw [← stalkIdeal_definingIdealOfHom_eq_ker j z]
  exact germ_mem_stalkIdeal _ _ V hz a

end IdealStalk

section Algebra

/-- **The base change of an ideal to the quotient by it is the conormal module.** For a
surjective algebra map `A ⟶ C` with kernel `J`, the `A`-module `C ⊗_A J` is `J/J²`. -/
noncomputable def tensorKerEquivCotangent {A C : Type u} [CommRing A] [CommRing C]
    [Algebra A C] (hsurj : Function.Surjective (algebraMap A C)) :
    (C ⊗[A] ↥(RingHom.ker (algebraMap A C))) ≃ₗ[A]
      (RingHom.ker (algebraMap A C)).Cotangent :=
  letI e : (A ⧸ RingHom.ker (algebraMap A C)) ≃ₐ[A] C :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A C) hsurj
  (TensorProduct.congr e.symm.toLinearEquiv
      (LinearEquiv.refl A ↥(RingHom.ker (algebraMap A C)))).trans
    ((Ideal.quotTensorEquivCotangent (RingHom.ker (algebraMap A C))).restrictScalars A)

/-- The normalisation of `tensorKerEquivCotangent`: it carries the generator `1 ⊗ a` to the
class of `a` modulo `J²`. -/
theorem tensorKerEquivCotangent_tmul_one {A C : Type u} [CommRing A] [CommRing C]
    [Algebra A C] (hsurj : Function.Surjective (algebraMap A C))
    (a : ↥(RingHom.ker (algebraMap A C))) :
    tensorKerEquivCotangent hsurj ((1 : C) ⊗ₜ[A] a) =
      (RingHom.ker (algebraMap A C)).toCotangent a := by
  rw [tensorKerEquivCotangent]
  simp only [LinearEquiv.trans_apply, TensorProduct.congr_tmul, LinearEquiv.restrictScalars_apply,
    LinearEquiv.refl_apply, AlgEquiv.toLinearEquiv_apply, map_one]
  exact Ideal.quotTensorEquivCotangent_one_tmul _ a

end Algebra

section Conormal

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (z : Z)

/-- The underlying presheaf of modules of the conormal sheaf, with its ring presheaf written out
so that its stalk is found to be a module over the stalk of the structure sheaf. -/
noncomputable abbrev conormalRetyped :
    PresheafOfModules.{u} (Z.presheaf ⋙ forget₂ CommRingCat RingCat) :=
  ((modulePullback i.liftCoborder.toLRSHom.toShHom).obj
    ((definingIdeal i).toSheafOfModules)).val

/-- **The stalk of the conormal sheaf of an immersion is the conormal module of the kernel on
local rings.** At a point `z` of `Z`, the stalk of `𝒞_{Z/X}` is `J/J²` for `J` the kernel of
`𝒪_{W, j z} ⟶ 𝒪_{Z, z}`, by an isomorphism carrying the conormal class of a local section `f`
of the defining ideal sheaf to the class of the germ of `f`. -/
theorem exists_conormalSheafStalkCotangentEquiv :
    letI := (i.liftCoborder.stalkMap z).hom.toAlgebra
    ∃ e : ToType (TopCat.Presheaf.stalk (C := Ab.{u}) (conormalRetyped i).presheaf z) ≃+
        (RingHom.ker (i.liftCoborder.stalkMap z).hom).Cotangent,
      ∀ (V : Opens i.coborderRange.toScheme) (hz : i.liftCoborder.base z ∈ V)
        (s : (idealPresheaf (definingIdealOfHom i.liftCoborder)).obj (op V)),
        e (TopCat.Presheaf.germ (C := Ab.{u}) (conormalRetyped i).presheaf
            (i.liftCoborder ⁻¹ᵁ V) z hz
            (((modulePullbackPushforwardAdjunction
                i.liftCoborder.toLRSHom.toShHom).unit.app
              ((definingIdeal i).toSheafOfModules)).val.app (op V) s)) =
          (RingHom.ker (i.liftCoborder.stalkMap z).hom).toCotangent
            ⟨(i.coborderRange.toScheme).presheaf.germ V (i.liftCoborder.base z) hz s.1,
              germ_mem_ker_stalkMap i.liftCoborder z V hz s⟩ := by
  let := (i.liftCoborder.stalkMap z).hom.toAlgebra
  obtain ⟨e₀, he₀⟩ :
      ∃ e : ToType (TopCat.Presheaf.stalk (C := Ab.{u}) (conormalRetyped i).presheaf z)
          ≃ₗ[ToType (Z.presheaf.stalk z)]
          (ToType (Z.presheaf.stalk z) ⊗[ToType ((i.coborderRange.toScheme).presheaf.stalk
              (i.liftCoborder.base z))]
            ToType (TopCat.Presheaf.stalk (C := Ab.{u})
              (idealPresheaf (definingIdealOfHom i.liftCoborder)).presheaf
              (i.liftCoborder.base z))),
        ∀ (V : Opens i.coborderRange.toScheme) (hz : i.liftCoborder.base z ∈ V)
          (s : (idealPresheaf (definingIdealOfHom i.liftCoborder)).obj (op V)),
          e (TopCat.Presheaf.germ (C := Ab.{u}) (conormalRetyped i).presheaf
              (i.liftCoborder ⁻¹ᵁ V) z hz
              (((modulePullbackPushforwardAdjunction
                  i.liftCoborder.toLRSHom.toShHom).unit.app
                ((definingIdeal i).toSheafOfModules)).val.app (op V) s)) =
            (1 : ToType (Z.presheaf.stalk z)) ⊗ₜ
              TopCat.Presheaf.germ (C := Ab.{u})
                (idealPresheaf (definingIdealOfHom i.liftCoborder)).presheaf V
                (i.liftCoborder.base z) hz s :=
    RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
      i.liftCoborder.toLRSHom.toShHom ((definingIdeal i).toSheafOfModules) z
  refine ⟨e₀.toAddEquiv.trans ((TensorProduct.congr (LinearEquiv.refl _ _)
      (definingIdealStalkEquiv i.liftCoborder z)).toAddEquiv.trans
    (tensorKerEquivCotangent (i.liftCoborder.stalkMap_surjective z)).toAddEquiv), ?_⟩
  intro V hz s
  refine Eq.trans (congrArg (fun y =>
    (tensorKerEquivCotangent (i.liftCoborder.stalkMap_surjective z))
      ((TensorProduct.congr (LinearEquiv.refl _ _)
        (definingIdealStalkEquiv i.liftCoborder z)) y)) (he₀ V hz s)) ?_
  rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply, tensorKerEquivCotangent_tmul_one]
  congr 1
  exact Subtype.ext (definingIdealStalkEquiv_coe i.liftCoborder z V hz s)

end Conormal

end Stacks.ConormalSequenceRight

end
