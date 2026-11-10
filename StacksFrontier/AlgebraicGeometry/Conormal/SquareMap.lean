module

public import StacksFrontier.AlgebraicGeometry.Conormal.Charts
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.AffineIdentification
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.Functoriality
public import StacksFrontier.AlgebraicGeometry.Thickenings.UniversalConormalGenerators
public import StacksFrontier.Topology.Sheaves.Basis.ModuleHomOnBasis
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The canonical map of conormal sheaves attached to a commutative square of immersions

Let
```
Z --i--→ X
|        |
f        g
↓        ↓
Z' -i'-→ X'
```
be a commutative square of schemes with `i` and `i'` immersions. [Stacks Project, Tag 01R4]
asserts that there is a canonical map of `𝒪_Z`-modules `f^* 𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}`, and
characterises it affine-locally: for every pair of affine opens `U ⊆ X` and `V ⊆ X'` with
`g(U) ⊆ V`, whose scheme-theoretic intersections with `Z` and `Z'` are `Spec (Γ(X, U) ⧸ I)` and
`Spec (Γ(X', V) ⧸ J)`, the induced map `J/J² ⟶ I/I²` is the one coming from `g^♯ J ⊆ I`.

The map itself is `Stacks.Immersion.immersionConormalSheafMap` and its affine characterisation is
`Stacks.Immersion.isInducedConormalSheafMap_immersionConormalSheafMap`, both already available
from `StacksFrontier.AlgebraicGeometry.Thickenings.UniversalConormalGenerators`; this file records
them as the corresponding parts of the tag with `add_to_stacks` and does not restate them. What it
proves are the two remaining assertions of the source: the containment `g^♯ J ⊆ I` that makes the
affine characterisation meaningful — without it the characterisation would have nothing to say
about a class whose representative has no image in `I` — and the fact that the affine
characterisation determines the map.

Uniqueness is then used to prove the **composition law** for the canonical map: for two squares of
immersions stacked vertically, the map of the composite square is the composite of the two maps,
read through the pullback composition isomorphism. That law is [Stacks Project, Tag 04G2] part
(3), stated there for algebraic spaces; it is proved here for schemes, which by parts (1) and (2)
of the same tag is the case the schemes conormal sheaf of [Stacks Project, Tag 01R2] and the
schemes map of [Stacks Project, Tag 01R4] describe. Its instance at a restriction square is what
carries the third condition of [Stacks Project, Tag 04FH] from an open of the ambient scheme to a
smaller open.

## Main results

* `Stacks.Immersion.immersionConormalSheafMap_ideal_mem`: the ambient ring map
  `g^♯ : Γ(X', V) ⟶ Γ(X, U)` carries `J` into `I`, so the affine characterisation's target class
  exists.
* `Stacks.Immersion.immersionConormalSheafMap_unique`: the affine characterisation is satisfied by
  at most one morphism, so it determines the canonical map.
* `Stacks.Immersion.immersionConormalSheafMap_comp`: the composition law, that is
  [Stacks Project, Tag 04G2] part (3) for schemes.
* `Stacks.Immersion.immersionConormalSheafMap_morphismRestrict`: that law at a restriction square,
  which is restriction naturality of the canonical map.
* `RingedSpaceModuleAdjunction.homEquiv_modulePullbackComp_comp`: the adjunction fact the
  composition law rests on — the transpose of a morphism out of `(f ≫ g)^*` splits into the
  transposes along `g^* ⊣ g_*` and `f^* ⊣ f_*`.
* `Stacks.ClosedImmersion.idealSheafMap_restrictHom_comp_ofRestrict` and
  `Stacks.ClosedImmersion.conormalSheafMap_restrictHom_comp_ofRestrict`: at the level of ringed
  spaces, the maps of ideal and of conormal sheaves induced by a restriction square are the
  restriction isomorphisms `ℐ_i|_U ≅ ℐ_{i|_U}` and `𝒞_i|_{i⁻¹U} ≅ 𝒞_{i|_U}`.

## Implementation notes

The containment is proved on rings rather than on sheaves. By
`Stacks.Conormal.ker_appLE_eq_of_affineModel` each of the two presented ideals is the kernel of
the map on sections of its immersion over the affine open, and the square says that
`g^♯` followed by `i^♯` is `(i')^♯` followed by `f^♯`; so a section killed by `(i')^♯` has its
`g^♯`-image killed by `i^♯`. The replacement of `i ≫ g` by `f ≫ i'` cannot be done by `rw`,
because the containment argument of `AlgebraicGeometry.Scheme.Hom.appLE` depends on the morphism;
it is done by generalising the morphism and substituting.

Uniqueness is local in two stages. Two morphisms agreeing on the affine charts of
[Stacks Project, Tag 01R4] agree on the sections over `i ⁻¹ᵁ U` for every affine `U` inside
`i.coborderRange ⊓ g ⁻¹ᵁ V`, by `Stacks.Conormal.affineConormalIsoCotangent` and surjectivity of
`Ideal.toCotangent`; those opens cover `f ⁻¹ᵁ (i' ⁻¹ᵁ V)`, which glues them to an equality of
sections over that open; and the opens `i' ⁻¹ᵁ V` for affine `V ≤ i'.coborderRange` form a basis
of `Z'`, so the two transposes agree. The affine model over such an open comes from
`AlgebraicGeometry.IsClosedImmersion.Spec_iff`, whose hypothesis is available because an open
inside the coborder of the range is one over which the immersion restricts to a closed immersion.

The composition law is proved by uniqueness rather than by unfolding the comparison isomorphisms.
The only obstacle is that a pair of affine opens `U ⊆ X₁` and `P ⊆ X₃` for the composite square
need not factor through an affine open of `X₂`; so the affine characterisation is verified on the
affine opens `U₀ ⊆ U` that do factor, and transported back by
`Stacks.Tag01R3PartTwo.affineConormalIsoCotangent_restrict`. Those opens cover `i₁⁻¹U`,
because the upper square carries a point of it into the coborder of the range of `i₂`, where the
middle immersion has an affine model.

Both statements are phrased through the ringed-space pullback
`RingedSpaceModuleAdjunction.modulePullback` and the adjunction
`RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction`, which is the vocabulary
the conormal sheaf and the canonical map are built in.

## References

* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 0473](https://stacks.math.columbia.edu/tag/0473)
* [Stacks Project, Tag 04FH](https://stacks.math.columbia.edu/tag/04FH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction 
open AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Stacks.ClosedImmersion Stacks.ClosedImmersion.AffineConormal
open Stacks.ClosedImmersion.IdealSheafAffine

universe u

namespace RingedSpaceModuleAdjunction

/-! ### Two coherences of the pullback composition isomorphism -/

/-- **Pushforward along a composite is the composite of the pushforwards, on morphisms.** The two
functors are definitionally equal, the components of
`RingedSpaceModuleAdjunction.modulePushforwardComp` being identities, so this holds by
`rfl`; it is stated because the two spellings are not syntactically equal. -/
theorem modulePushforward_comp_map {Zr Wr Vr : RingedSpace.{u, u}} (f : Zr ⟶ Wr) (g : Wr ⟶ Vr)
    {M N : SheafOfModules.{u} (structureSheafRing Zr)} (ψ : M ⟶ N) :
    (modulePushforward (f ≫ g)).map ψ =
      (modulePushforward g).map ((modulePushforward f).map ψ) := rfl

/-- **The transpose of a morphism out of `(f ≫ g)^*` splits along the two adjunctions.** For
`φ₂ : g^* M ⟶ N_W` and `φ₁ : f^* N_W ⟶ N_Z`, the transpose along `(f ≫ g)^* ⊣ (f ≫ g)_*` of the
composite of `RingedSpaceModuleAdjunction.modulePullbackComp` with `f^* φ₂` and `φ₁` is the
transpose of `φ₂` followed by `g_*` of the transpose of `φ₁`.

This is `RingedSpaceModuleAdjunction.unit_modulePullbackComp` — the only description of the
composition isomorphism a consumer needs — combined with naturality of the unit of `f^* ⊣ f_*`. -/
theorem homEquiv_modulePullbackComp_comp {Zr Wr Vr : RingedSpace.{u, u}} (f : Zr ⟶ Wr)
    (g : Wr ⟶ Vr) (M : SheafOfModules.{u} (structureSheafRing Vr))
    (Nw : SheafOfModules.{u} (structureSheafRing Wr))
    (Nz : SheafOfModules.{u} (structureSheafRing Zr))
    (φ₂ : (modulePullback g).obj M ⟶ Nw) (φ₁ : (modulePullback f).obj Nw ⟶ Nz) :
    (modulePullbackPushforwardAdjunction (f ≫ g)).homEquiv M Nz
        ((modulePullbackComp f g).hom.app M ≫ (modulePullback f).map φ₂ ≫ φ₁) =
      (modulePullbackPushforwardAdjunction g).homEquiv M Nw φ₂ ≫
        (modulePushforward g).map
          ((modulePullbackPushforwardAdjunction f).homEquiv Nw Nz φ₁) := by
  have hn := (modulePullbackPushforwardAdjunction f).unit.naturality φ₂
  simp only [Functor.comp_map, Functor.id_map] at hn
  have hf : (modulePullbackPushforwardAdjunction f).unit.app ((modulePullback g).obj M) ≫
        (modulePushforward f).map ((modulePullback f).map φ₂ ≫ φ₁) =
      φ₂ ≫ (modulePullbackPushforwardAdjunction f).unit.app Nw ≫
        (modulePushforward f).map φ₁ := by
    rw [Functor.map_comp, ← Category.assoc, ← hn, Category.assoc]
  have hmid := ((modulePushforward g).map_comp
      ((modulePullbackPushforwardAdjunction f).unit.app ((modulePullback g).obj M))
      ((modulePushforward f).map ((modulePullback f).map φ₂ ≫ φ₁))).symm.trans
    (congrArg (modulePushforward g).map hf)
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Functor.map_comp, ← Category.assoc, ← unit_modulePullbackComp,
    modulePushforward_comp_map]
  exact (Category.assoc _ _ _).trans
    (congrArg (fun z => (modulePullbackPushforwardAdjunction g).unit.app M ≫ z)
      (hmid.trans ((modulePushforward g).map_comp _ _)))

end RingedSpaceModuleAdjunction

namespace Stacks.Immersion

variable {Z X Z' X' : Scheme.{u}}

/-! ### The affine ideal containment -/

/-- **[Stacks Project, Tag 01R4]: the ambient ring map carries the target ideal into the source
ideal.** On a pair of affine opens `U ⊆ X` and `V ⊆ X'` with `g(U) ⊆ V` presenting the
scheme-theoretic intersections as `Spec (Γ(X, U) ⧸ I)` and `Spec (Γ(X', V) ⧸ J)`, the map
`g^♯ : Γ(X', V) ⟶ Γ(X, U)` sends `J` into `I`.

This is what lets the affine characterisation speak of the class in `I/I²` of the image of a
class in `J/J²`. -/
@[stacks 01R4 "affine ideal containment"]
theorem immersionConormalSheafMap_ideal_mem (i : Z ⟶ X) (i' : Z' ⟶ X')
    [IsImmersion i] [IsImmersion i'] (f : Z ⟶ Z') (g : X ⟶ X') (comm : i ≫ g = f ≫ i')
    (U : X.Opens) (hU : IsAffineOpen U) (V : X'.Opens) (hV : IsAffineOpen V)
    (hUV : U ≤ g ⁻¹ᵁ V) (I : Ideal Γ(X, U)) (J : Ideal Γ(X', V))
    (eZ : pullback i U.ι ≅ Spec (quotRing I))
    (heZ : pullback.snd i U.ι ≫ hU.isoSpec.hom = eZ.hom ≫ quotImmersion Γ(X, U) I)
    (eZ' : pullback i' V.ι ≅ Spec (quotRing J))
    (heZ' : pullback.snd i' V.ι ≫ hV.isoSpec.hom = eZ'.hom ≫ quotImmersion Γ(X', V) J)
    (a : J) : (g.appLE V U hUV).hom (a : Γ(X', V)) ∈ I := by
  have hFU : i ⁻¹ᵁ U ≤ f ⁻¹ᵁ (i' ⁻¹ᵁ V) := preimage_le_preimage_of_square comm U V hUV
  have hI : RingHom.ker (i.appLE U (i ⁻¹ᵁ U) le_rfl).hom = I :=
    Stacks.Conormal.ker_appLE_eq_of_affineModel i U hU I eZ heZ
  have hJ : RingHom.ker (i'.appLE V (i' ⁻¹ᵁ V) le_rfl).hom = J :=
    Stacks.Conormal.ker_appLE_eq_of_affineModel i' V hV J eZ' heZ'
  have ha0 : (i'.appLE V (i' ⁻¹ᵁ V) le_rfl).hom (a : Γ(X', V)) = 0 :=
    RingHom.mem_ker.mp (hJ.ge a.2)
  have key : ∀ (p : Z ⟶ X') (hp : i ⁻¹ᵁ U ≤ p ⁻¹ᵁ V), p = f ≫ i' →
      (p.appLE V (i ⁻¹ᵁ U) hp).hom (a : Γ(X', V)) = 0 := by
    rintro p hp rfl
    have hsplit : i'.appLE V (i' ⁻¹ᵁ V) le_rfl ≫ f.appLE (i' ⁻¹ᵁ V) (i ⁻¹ᵁ U) hFU =
        (f ≫ i').appLE V (i ⁻¹ᵁ U) hp :=
      Scheme.Hom.appLE_comp_appLE f i' V (i' ⁻¹ᵁ V) (i ⁻¹ᵁ U) le_rfl hFU
    rw [← hsplit, CommRingCat.comp_apply, ha0, map_zero]
  rw [← hI]
  refine RingHom.mem_ker.mpr ?_
  rw [← CommRingCat.comp_apply,
    Scheme.Hom.appLE_comp_appLE i g V U (i ⁻¹ᵁ U) hUV le_rfl]
  exact key (i ≫ g) _ comm

/-! ### Uniqueness -/

/-- An immersion has an affine model over any affine open contained in the coborder of its range. -/
private theorem exists_affineModel_of_le_coborderRange (i : Z ⟶ X) [IsImmersion i]
    (U : X.Opens) (hU : IsAffineOpen U) (hUc : U ≤ i.coborderRange) :
    ∃ (I : Ideal Γ(X, U)) (e : pullback i U.ι ≅ Spec (quotRing I)),
      pullback.snd i U.ι ≫ hU.isoSpec.hom = e.hom ≫ quotImmersion Γ(X, U) I := by
  have h := isClosedImmersion_resLE_of_le_coborderRange i U hUc
  rw [Scheme.Hom.resLE_eq_morphismRestrict] at h
  exact Conormal.exists_affineModel_of_isClosedImmersion_restrict i U hU h

/-- An isomorphism of modules carries an equation about its forward map to one about its
inverse. -/
private theorem eq_inv_apply {R : Type u} [Ring R] {M N : ModuleCat.{u} R} (A : M ≅ N)
    (x : M) (y : N) (h : A.hom.hom x = y) : x = A.inv.hom y :=
  h ▸ ((ModuleCat.hom_comp_apply A.hom A.inv x).symm.trans
    (ModuleCat.hom_apply_congr A.hom_inv_id x)).symm

/-- Two morphisms satisfying the affine characterisation have the same transpose on the conormal
sections over `i' ⁻¹ᵁ V`, restricted to `i ⁻¹ᵁ U`, for a compatible pair of affine opens carrying
affine models.

Every conormal section over `i' ⁻¹ᵁ V` is the class of an element of `J` by surjectivity of
`Ideal.toCotangent` and `Stacks.Conormal.affineConormalIsoCotangent`, and
`Stacks.Immersion.immersionConormalSheafMap_ideal_mem` provides the element of `I` that the
characterisation needs on the other side. -/
private theorem transpose_eq_of_affineModel (i : Z ⟶ X) (i' : Z' ⟶ X')
    [IsImmersion i] [IsImmersion i'] (f : Z ⟶ Z') (g : X ⟶ X') (comm : i ≫ g = f ≫ i')
    (φ ψ : (modulePullback f.toLRSHom.toShHom).obj
        (conormalSheaf i'.liftCoborder.toLRSHom.toShHom) ⟶
      conormalSheaf i.liftCoborder.toLRSHom.toShHom)
    (hφ : IsInducedConormalSheafMap i i' f g comm φ)
    (hψ : IsInducedConormalSheafMap i i' f g comm ψ)
    (U : X.Opens) (hU : IsAffineOpen U) (V : X'.Opens) (hV : IsAffineOpen V)
    (hUV : U ≤ g ⁻¹ᵁ V) (I : Ideal Γ(X, U)) (J : Ideal Γ(X', V))
    (eZ : pullback i U.ι ≅ Spec (quotRing I))
    (heZ : pullback.snd i U.ι ≫ hU.isoSpec.hom = eZ.hom ≫ quotImmersion Γ(X, U) I)
    (eZ' : pullback i' V.ι ≅ Spec (quotRing J))
    (heZ' : pullback.snd i' V.ι ≫ hV.isoSpec.hom = eZ'.hom ≫ quotImmersion Γ(X', V) J)
    (s : (conormalSheaf i'.liftCoborder.toLRSHom.toShHom).val.obj (op (i' ⁻¹ᵁ V))) :
    (conormalSheaf i.liftCoborder.toLRSHom.toShHom).val.map
        (homOfLE (preimage_le_preimage_of_square comm U V hUV)).op
        (((modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).homEquiv _ _ φ).val.app
          (op (i' ⁻¹ᵁ V)) s) =
      (conormalSheaf i.liftCoborder.toLRSHom.toShHom).val.map
        (homOfLE (preimage_le_preimage_of_square comm U V hUV)).op
        (((modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).homEquiv _ _ ψ).val.app
          (op (i' ⁻¹ᵁ V)) s) := by
  obtain ⟨a, ha⟩ := J.toCotangent_surjective
    ((Stacks.Conormal.affineConormalIsoCotangent i' V hV J eZ' heZ').hom.hom s)
  have hs := eq_inv_apply
    (Stacks.Conormal.affineConormalIsoCotangent i' V hV J eZ' heZ') _ _ ha.symm
  subst hs
  exact (hφ U hU V hV hUV I J eZ heZ eZ' heZ' a
      ⟨(g.appLE V U hUV).hom (a : Γ(X', V)), immersionConormalSheafMap_ideal_mem i i' f g comm
        U hU V hV hUV I J eZ heZ eZ' heZ' a⟩ rfl).trans
    (hψ U hU V hV hUV I J eZ heZ eZ' heZ' a
      ⟨(g.appLE V U hUV).hom (a : Γ(X', V)), immersionConormalSheafMap_ideal_mem i i' f g comm
        U hU V hV hUV I J eZ heZ eZ' heZ' a⟩ rfl).symm

/-- Two morphisms satisfying the affine characterisation have the same transpose on the conormal
sections over `i' ⁻¹ᵁ V`, for an affine open `V ⊆ X'` inside `i'.coborderRange`.

The affine opens `U ⊆ X` inside `i.coborderRange ⊓ g ⁻¹ᵁ V` have preimages covering
`f ⁻¹ᵁ (i' ⁻¹ᵁ V)`, since the square carries a point of that open into `g ⁻¹ᵁ V` and every point
of `Z` has its image in the coborder of the range; on each of them the two sections agree by
`Stacks.Immersion.transpose_eq_of_affineModel`, so the sheaf condition identifies them. -/
private theorem transpose_eq_of_coborder_affine (i : Z ⟶ X) (i' : Z' ⟶ X')
    [IsImmersion i] [IsImmersion i'] (f : Z ⟶ Z') (g : X ⟶ X') (comm : i ≫ g = f ≫ i')
    (φ ψ : (modulePullback f.toLRSHom.toShHom).obj
        (conormalSheaf i'.liftCoborder.toLRSHom.toShHom) ⟶
      conormalSheaf i.liftCoborder.toLRSHom.toShHom)
    (hφ : IsInducedConormalSheafMap i i' f g comm φ)
    (hψ : IsInducedConormalSheafMap i i' f g comm ψ)
    (V : X'.Opens) (hV : IsAffineOpen V) (hVc : V ≤ i'.coborderRange)
    (s : (conormalSheaf i'.liftCoborder.toLRSHom.toShHom).val.obj (op (i' ⁻¹ᵁ V))) :
    ((modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).homEquiv _ _ φ).val.app
        (op (i' ⁻¹ᵁ V)) s =
      ((modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).homEquiv _ _ ψ).val.app
        (op (i' ⁻¹ᵁ V)) s := by
  let C := conormalSheaf i.liftCoborder.toLRSHom.toShHom
  let T : Z.Opens := f ⁻¹ᵁ (i' ⁻¹ᵁ V)
  let A := {U : X.affineOpens // U.1 ≤ i.coborderRange ⊓ g ⁻¹ᵁ V}
  let B : A → Z.Opens := fun j => i ⁻¹ᵁ j.1.1
  have hBT (j : A) : B j ≤ T :=
    preimage_le_preimage_of_square comm j.1.1 V (le_inf_iff.mp j.2).2
  have hcover : T ≤ ⨆ j : A, B j := by
    intro z hz
    have hzV : i z ∈ g ⁻¹ᵁ V := by
      change (i ≫ g) z ∈ V
      rw [comm]
      exact hz
    obtain ⟨_, ⟨U, hU, rfl⟩, hzU, hUle⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open
        (show i z ∈ i.coborderRange ⊓ g ⁻¹ᵁ V from ⟨subset_coborder ⟨z, rfl⟩, hzV⟩)
        (i.coborderRange ⊓ g ⁻¹ᵁ V).2
    exact (Opens.mem_iSup).2 ⟨⟨⟨U, hU⟩, hUle⟩, hzU⟩
  obtain ⟨J, eJ, heJ⟩ := exists_affineModel_of_le_coborderRange i' V hV hVc
  refine (show TopCat.Sheaf _ Z.carrier from ⟨C.val.presheaf, C.isSheaf⟩).eq_of_locally_eq'
    (U := B) T (fun j => homOfLE (hBT j)) hcover _ _ (fun j => ?_)
  obtain ⟨I, eI, heI⟩ := exists_affineModel_of_le_coborderRange i j.1.1 j.1.2 (le_inf_iff.mp j.2).1
  exact transpose_eq_of_affineModel i i' f g comm φ ψ hφ hψ j.1.1 j.1.2 V hV
    (le_inf_iff.mp j.2).2 I J eI heI eJ heJ s

/-- **[Stacks Project, Tag 01R4]: the affine formula determines the map.** A morphism
`f^* 𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}` satisfying the affine characterisation is
`Stacks.Immersion.immersionConormalSheafMap`.

Transposing along `f^* ⊣ f_*` and testing on the basis of `Z'` given by the opens `i' ⁻¹ᵁ V` for
affine `V ⊆ X'` inside `i'.coborderRange` reduces this to
`Stacks.Immersion.transpose_eq_of_coborder_affine`. -/
@[stacks 01R4 "uniqueness"]
theorem immersionConormalSheafMap_unique (i : Z ⟶ X) (i' : Z' ⟶ X')
    [IsImmersion i] [IsImmersion i'] (f : Z ⟶ Z') (g : X ⟶ X') (comm : i ≫ g = f ≫ i')
    (φ : (modulePullback f.toLRSHom.toShHom).obj
        (conormalSheaf i'.liftCoborder.toLRSHom.toShHom) ⟶
      conormalSheaf i.liftCoborder.toLRSHom.toShHom)
    (hφ : IsInducedConormalSheafMap i i' f g comm φ) :
    φ = immersionConormalSheafMap i i' f g (toShHom_square comm) := by
  let A := Stacks.Conormal.ConormalChart i'
  let B : A → Z'.Opens := (Stacks.Conormal.conormalChartFunctor i').obj
  have hBasis : Opens.IsBasis (Set.range B) := Stacks.Conormal.conormalChart_isBasis i'
  refine ((modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).homEquiv _ _).injective ?_
  refine Stacks.BasisRestriction.moduleSheafHom_ext_onBasis _ _ B hBasis _ _ (fun j => ?_)
  ext s
  exact transpose_eq_of_coborder_affine i i' f g comm φ _ hφ
    (isInducedConormalSheafMap_immersionConormalSheafMap i i' f g comm) j.1.1 j.1.2 j.2 s

/-! ### The composition law -/

/-- **Two commutative squares stacked vertically compose to a commutative square.** -/
theorem square_comp {Z₁ Z₂ Z₃ X₁ X₂ X₃ : Scheme.{u}} {i₁ : Z₁ ⟶ X₁} {i₂ : Z₂ ⟶ X₂}
    {i₃ : Z₃ ⟶ X₃} {f₁ : Z₁ ⟶ Z₂} {g₁ : X₁ ⟶ X₂} {f₂ : Z₂ ⟶ Z₃} {g₂ : X₂ ⟶ X₃}
    (comm₁ : i₁ ≫ g₁ = f₁ ≫ i₂) (comm₂ : i₂ ≫ g₂ = f₂ ≫ i₃) :
    i₁ ≫ g₁ ≫ g₂ = (f₁ ≫ f₂) ≫ i₃ := by
  rw [← Category.assoc, comm₁, Category.assoc, comm₂, Category.assoc]

/-- **The composite of the two induced maps satisfies the affine characterisation of the composite
square on a triple of affine opens.** The characterisation of [Stacks Project, Tag 01R4] for the
stacked square reads over a pair of affine opens `U₀ ⊆ X₁` and `P ⊆ X₃`; this is that equation in
the presence of an affine open `V₀ ⊆ X₂` through which the pair factors, which is what lets the
two characterisations be chained.

The transpose of the composite splits by
`RingedSpaceModuleAdjunction.homEquiv_modulePullbackComp_comp`, and the two halves are
joined by naturality of the transpose of the upper square's map. -/
private theorem transpose_comp_eq_of_affineModel {Z₁ Z₂ Z₃ X₁ X₂ X₃ : Scheme.{u}}
    (i₁ : Z₁ ⟶ X₁) (i₂ : Z₂ ⟶ X₂) (i₃ : Z₃ ⟶ X₃)
    [IsImmersion i₁] [IsImmersion i₂] [IsImmersion i₃]
    (f₁ : Z₁ ⟶ Z₂) (g₁ : X₁ ⟶ X₂) (comm₁ : i₁ ≫ g₁ = f₁ ≫ i₂)
    (f₂ : Z₂ ⟶ Z₃) (g₂ : X₂ ⟶ X₃) (comm₂ : i₂ ≫ g₂ = f₂ ≫ i₃)
    (U₀ : X₁.Opens) (hU₀ : IsAffineOpen U₀) (V₀ : X₂.Opens) (hV₀ : IsAffineOpen V₀)
    (P : X₃.Opens) (hP : IsAffineOpen P)
    (hU₀V₀ : U₀ ≤ g₁ ⁻¹ᵁ V₀) (hV₀P : V₀ ≤ g₂ ⁻¹ᵁ P) (hU₀P : U₀ ≤ (g₁ ≫ g₂) ⁻¹ᵁ P)
    (I₀ : Ideal Γ(X₁, U₀)) (J₀ : Ideal Γ(X₂, V₀)) (K : Ideal Γ(X₃, P))
    (e₁ : pullback i₁ U₀.ι ≅ Spec (quotRing I₀))
    (he₁ : pullback.snd i₁ U₀.ι ≫ hU₀.isoSpec.hom = e₁.hom ≫ quotImmersion Γ(X₁, U₀) I₀)
    (e₂ : pullback i₂ V₀.ι ≅ Spec (quotRing J₀))
    (he₂ : pullback.snd i₂ V₀.ι ≫ hV₀.isoSpec.hom = e₂.hom ≫ quotImmersion Γ(X₂, V₀) J₀)
    (e₃ : pullback i₃ P.ι ≅ Spec (quotRing K))
    (he₃ : pullback.snd i₃ P.ι ≫ hP.isoSpec.hom = e₃.hom ≫ quotImmersion Γ(X₃, P) K)
    (a : K) (c₀ : I₀)
    (hc₀ : (c₀ : Γ(X₁, U₀)) = ((g₁ ≫ g₂).appLE P U₀ hU₀P).hom (a : Γ(X₃, P))) :
    (conormalSheaf i₁.liftCoborder.toLRSHom.toShHom).val.map
        (homOfLE (preimage_le_preimage_of_square (square_comp comm₁ comm₂) U₀ P hU₀P)).op
        (((modulePullbackPushforwardAdjunction (f₁ ≫ f₂).toLRSHom.toShHom).homEquiv _ _
              ((modulePullbackComp f₁.toLRSHom.toShHom f₂.toLRSHom.toShHom).hom.app
                  (conormalSheaf i₃.liftCoborder.toLRSHom.toShHom) ≫
                (modulePullback f₁.toLRSHom.toShHom).map
                  (immersionConormalSheafMap i₂ i₃ f₂ g₂ (toShHom_square comm₂)) ≫
                immersionConormalSheafMap i₁ i₂ f₁ g₁ (toShHom_square comm₁))).val.app
          (op (i₃ ⁻¹ᵁ P)) ((Stacks.Conormal.affineConormalIsoCotangent i₃ P hP K e₃ he₃).inv.hom
            (K.toCotangent a))) =
      (Stacks.Conormal.affineConormalIsoCotangent i₁ U₀ hU₀ I₀ e₁ he₁).inv.hom
        (I₀.toCotangent c₀) := by
  have hT := homEquiv_modulePullbackComp_comp f₁.toLRSHom.toShHom f₂.toLRSHom.toShHom
    (conormalSheaf i₃.liftCoborder.toLRSHom.toShHom)
    (conormalSheaf i₂.liftCoborder.toLRSHom.toShHom)
    (conormalSheaf i₁.liftCoborder.toLRSHom.toShHom)
    (immersionConormalSheafMap i₂ i₃ f₂ g₂ (toShHom_square comm₂))
    (immersionConormalSheafMap i₁ i₂ f₁ g₁ (toShHom_square comm₁))
  obtain ⟨b, hb⟩ : ∃ b : J₀, (b : Γ(X₂, V₀)) = (g₂.appLE P V₀ hV₀P).hom (a : Γ(X₃, P)) :=
    ⟨⟨_, immersionConormalSheafMap_ideal_mem i₂ i₃ f₂ g₂ comm₂ V₀ hV₀ P hP hV₀P J₀ K
      e₂ he₂ e₃ he₃ a⟩, rfl⟩
  have hα := isInducedConormalSheafMap_immersionConormalSheafMap i₂ i₃ f₂ g₂ comm₂
    V₀ hV₀ P hP hV₀P J₀ K e₂ he₂ e₃ he₃ a b hb
  have hc₀' : (c₀ : Γ(X₁, U₀)) = (g₁.appLE V₀ U₀ hU₀V₀).hom (b : Γ(X₂, V₀)) := by
    rw [hb, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, hc₀]
  have hβ := isInducedConormalSheafMap_immersionConormalSheafMap i₁ i₂ f₁ g₁ comm₁
    U₀ hU₀ V₀ hV₀ hU₀V₀ I₀ J₀ e₁ he₁ e₂ he₂ b c₀ hc₀'
  have hnat := val_app_naturality
    ((modulePullbackPushforwardAdjunction f₁.toLRSHom.toShHom).homEquiv _ _
      (immersionConormalSheafMap i₁ i₂ f₁ g₁ (toShHom_square comm₁)))
    (homOfLE (preimage_le_preimage_of_square comm₂ V₀ P hV₀P))
    (((modulePullbackPushforwardAdjunction f₂.toLRSHom.toShHom).homEquiv _ _
        (immersionConormalSheafMap i₂ i₃ f₂ g₂ (toShHom_square comm₂))).val.app
      (op (i₃ ⁻¹ᵁ P)) ((Stacks.Conormal.affineConormalIsoCotangent i₃ P hP K e₃ he₃).inv.hom
        (K.toCotangent a)))
  have hpf := modulePushforward_obj_val_map f₁.toLRSHom.toShHom
    (conormalSheaf i₁.liftCoborder.toLRSHom.toShHom)
    (homOfLE (preimage_le_preimage_of_square comm₂ V₀ P hV₀P))
    (((modulePullbackPushforwardAdjunction f₁.toLRSHom.toShHom).homEquiv _ _
        (immersionConormalSheafMap i₁ i₂ f₁ g₁ (toShHom_square comm₁))).val.app
      (op (f₂ ⁻¹ᵁ (i₃ ⁻¹ᵁ P)))
      (((modulePullbackPushforwardAdjunction f₂.toLRSHom.toShHom).homEquiv _ _
          (immersionConormalSheafMap i₂ i₃ f₂ g₂ (toShHom_square comm₂))).val.app
        (op (i₃ ⁻¹ᵁ P)) ((Stacks.Conormal.affineConormalIsoCotangent i₃ P hP K e₃ he₃).inv.hom
          (K.toCotangent a))))
  have hsplit := val_map_unique (conormalSheaf i₁.liftCoborder.toLRSHom.toShHom)
    ((Opens.map f₁.toLRSHom.toShHom.hom.base).map
      (homOfLE (preimage_le_preimage_of_square comm₂ V₀ P hV₀P)))
    (homOfLE (preimage_le_preimage_of_square comm₁ U₀ V₀ hU₀V₀))
    (homOfLE (preimage_le_preimage_of_square (square_comp comm₁ comm₂) U₀ P hU₀P))
    (((modulePullbackPushforwardAdjunction f₁.toLRSHom.toShHom).homEquiv _ _
        (immersionConormalSheafMap i₁ i₂ f₁ g₁ (toShHom_square comm₁))).val.app
      (op (f₂ ⁻¹ᵁ (i₃ ⁻¹ᵁ P)))
      (((modulePullbackPushforwardAdjunction f₂.toLRSHom.toShHom).homEquiv _ _
          (immersionConormalSheafMap i₂ i₃ f₂ g₂ (toShHom_square comm₂))).val.app
        (op (i₃ ⁻¹ᵁ P)) ((Stacks.Conormal.affineConormalIsoCotangent i₃ P hP K e₃ he₃).inv.hom
          (K.toCotangent a))))
  refine Eq.trans (val_map_congr _ (congrArg
    (fun ψ => ψ.val.app (op (i₃ ⁻¹ᵁ P))
      ((Stacks.Conormal.affineConormalIsoCotangent i₃ P hP K e₃ he₃).inv.hom
        (K.toCotangent a))) hT)) ?_
  refine Eq.trans hsplit.symm ?_
  refine Eq.trans (val_map_congr _ hpf.symm) ?_
  refine Eq.trans (val_map_congr _ hnat.symm) ?_
  exact Eq.trans (val_map_congr _ (congrArg _ hα)) hβ

/-- **[Stacks Project, Tag 01R4] is functorial for stacked squares.** For two commutative squares
of immersions stacked vertically, the induced map of conormal sheaves of the composite square is
the composite of the two induced maps, read through the pullback composition isomorphism
`RingedSpaceModuleAdjunction.modulePullbackComp`.

The source states no such law; it is what makes the map of the tag a map of *pseudofunctors*, and
it is what transports the map along a restriction of the ambient scheme.

The proof is `Stacks.Immersion.immersionConormalSheafMap_unique`: the composite is shown to
satisfy the affine characterisation of the composite square. A pair of affine opens `U ⊆ X₁` and
`P ⊆ X₃` need not factor through an affine open of `X₂`, so the characterisation is verified after
restricting to the affine opens `U₀ ⊆ U` that do, by
`Stacks.Immersion.transpose_comp_eq_of_affineModel` and
`Stacks.Tag01R3PartTwo.affineConormalIsoCotangent_restrict`; those cover `i₁⁻¹U`, since the
square carries a point of it into the coborder of the range of `i₂`. -/
@[stacks 04G2 "part (3) for schemes"]
theorem immersionConormalSheafMap_comp {Z₁ Z₂ Z₃ X₁ X₂ X₃ : Scheme.{u}}
    (i₁ : Z₁ ⟶ X₁) (i₂ : Z₂ ⟶ X₂) (i₃ : Z₃ ⟶ X₃)
    [IsImmersion i₁] [IsImmersion i₂] [IsImmersion i₃]
    (f₁ : Z₁ ⟶ Z₂) (g₁ : X₁ ⟶ X₂) (comm₁ : i₁ ≫ g₁ = f₁ ≫ i₂)
    (f₂ : Z₂ ⟶ Z₃) (g₂ : X₂ ⟶ X₃) (comm₂ : i₂ ≫ g₂ = f₂ ≫ i₃) :
    immersionConormalSheafMap i₁ i₃ (f₁ ≫ f₂) (g₁ ≫ g₂)
        (toShHom_square (square_comp comm₁ comm₂)) =
      (modulePullbackComp f₁.toLRSHom.toShHom f₂.toLRSHom.toShHom).hom.app
          (conormalSheaf i₃.liftCoborder.toLRSHom.toShHom) ≫
        (modulePullback f₁.toLRSHom.toShHom).map
          (immersionConormalSheafMap i₂ i₃ f₂ g₂ (toShHom_square comm₂)) ≫
        immersionConormalSheafMap i₁ i₂ f₁ g₁ (toShHom_square comm₁) := by
  refine (immersionConormalSheafMap_unique i₁ i₃ (f₁ ≫ f₂) (g₁ ≫ g₂)
    (square_comp comm₁ comm₂) _ ?_).symm
  intro U hU P hP hUP I K eZ heZ eV heV a c hac
  let A := {p : X₁.affineOpens × X₂.affineOpens //
    p.1.1 ≤ U ⊓ i₁.coborderRange ⊓ g₁ ⁻¹ᵁ p.2.1 ∧ p.2.1 ≤ g₂ ⁻¹ᵁ P ⊓ i₂.coborderRange}
  let B : A → Z₁.Opens := fun p => i₁ ⁻¹ᵁ p.1.1.1
  have hBT (p : A) : B p ≤ i₁ ⁻¹ᵁ U :=
    i₁.preimage_mono ((le_inf_iff.mp (le_inf_iff.mp p.2.1).1).1)
  have hcover : i₁ ⁻¹ᵁ U ≤ ⨆ p : A, B p := by
    intro z hz
    have hzc : g₁ (i₁ z) ∈ i₂.coborderRange := by
      change (i₁ ≫ g₁) z ∈ i₂.coborderRange
      rw [comm₁]
      exact subset_coborder ⟨f₁ z, rfl⟩
    obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hzV₀, hV₀le⟩ :=
      X₂.isBasis_affineOpens.exists_subset_of_mem_open
        (show g₁ (i₁ z) ∈ g₂ ⁻¹ᵁ P ⊓ i₂.coborderRange from ⟨hUP hz, hzc⟩)
        (g₂ ⁻¹ᵁ P ⊓ i₂.coborderRange).2
    obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hzU₀, hU₀le⟩ :=
      X₁.isBasis_affineOpens.exists_subset_of_mem_open
        (show i₁ z ∈ U ⊓ i₁.coborderRange ⊓ g₁ ⁻¹ᵁ V₀ from
          ⟨⟨hz, subset_coborder ⟨z, rfl⟩⟩, hzV₀⟩)
        (U ⊓ i₁.coborderRange ⊓ g₁ ⁻¹ᵁ V₀).2
    exact (Opens.mem_iSup).2 ⟨⟨(⟨U₀, hU₀⟩, ⟨V₀, hV₀⟩), hU₀le, hV₀le⟩, hzU₀⟩
  refine (show TopCat.Sheaf _ Z₁.carrier from
      ⟨(conormalSheaf i₁.liftCoborder.toLRSHom.toShHom).val.presheaf,
        (conormalSheaf i₁.liftCoborder.toLRSHom.toShHom).isSheaf⟩).eq_of_locally_eq'
    (U := B) (i₁ ⁻¹ᵁ U) (fun p => homOfLE (hBT p)) hcover _ _ (fun p => ?_)
  obtain ⟨I₀, e₁, he₁⟩ := exists_affineModel_of_le_coborderRange i₁ p.1.1.1 p.1.1.2
    (le_inf_iff.mp (le_inf_iff.mp p.2.1).1).2
  obtain ⟨J₀, e₂, he₂⟩ := exists_affineModel_of_le_coborderRange i₂ p.1.2.1 p.1.2.2
    (le_inf_iff.mp p.2.2).2
  have hU₀U : p.1.1.1 ≤ U := (le_inf_iff.mp (le_inf_iff.mp p.2.1).1).1
  have hU₀V₀ : p.1.1.1 ≤ g₁ ⁻¹ᵁ p.1.2.1 := (le_inf_iff.mp p.2.1).2
  have hV₀P : p.1.2.1 ≤ g₂ ⁻¹ᵁ P := (le_inf_iff.mp p.2.2).1
  have hU₀P : p.1.1.1 ≤ (g₁ ≫ g₂) ⁻¹ᵁ P :=
    hU₀V₀.trans ((Opens.map g₁.base).map (homOfLE hV₀P)).le
  have hcres : (X₁.presheaf.map (homOfLE hU₀U).op).hom (c : Γ(X₁, U)) =
      ((g₁ ≫ g₂).appLE P p.1.1.1 hU₀P).hom (a : Γ(X₃, P)) := by
    rw [hac, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  obtain ⟨c₀, hc₀, hc₀'⟩ : ∃ c₀ : I₀, (c₀ : Γ(X₁, p.1.1.1)) =
      ((g₁ ≫ g₂).appLE P p.1.1.1 hU₀P).hom (a : Γ(X₃, P)) ∧
      (X₁.presheaf.map (homOfLE hU₀U).op).hom (c : Γ(X₁, U)) = (c₀ : Γ(X₁, p.1.1.1)) :=
    ⟨⟨_, immersionConormalSheafMap_ideal_mem i₁ i₃ (f₁ ≫ f₂) (g₁ ≫ g₂)
        (square_comp comm₁ comm₂) p.1.1.1 p.1.1.2 P hP hU₀P I₀ K e₁ he₁ eV heV a⟩,
      rfl, hcres⟩
  have hres := Stacks.Tag01R3PartTwo.affineConormalIsoCotangent_restrict i₁ U p.1.1.1 hU₀U hU
    p.1.1.2 I I₀ eZ heZ e₁ he₁ c (hc₀' ▸ c₀.2)
  have hresinv : ((modulePushforward i₁.toLRSHom.toShHom).obj
        (conormalSheaf i₁.liftCoborder.toLRSHom.toShHom)).val.map (homOfLE hU₀U).op
        ((Stacks.Conormal.affineConormalIsoCotangent i₁ U hU I eZ heZ).inv.hom
          (I.toCotangent c)) =
      (Stacks.Conormal.affineConormalIsoCotangent i₁ p.1.1.1 p.1.1.2 I₀ e₁ he₁).inv.hom
        (I₀.toCotangent c₀) :=
    eq_inv_apply (Stacks.Conormal.affineConormalIsoCotangent i₁ p.1.1.1 p.1.1.2 I₀ e₁ he₁) _ _
      (hres.trans (congrArg I₀.toCotangent (Subtype.ext hc₀')))
  refine Eq.trans (val_map_unique (conormalSheaf i₁.liftCoborder.toLRSHom.toShHom)
    (homOfLE (preimage_le_preimage_of_square (square_comp comm₁ comm₂) U P hUP))
    (homOfLE (hBT p))
    (homOfLE (preimage_le_preimage_of_square (square_comp comm₁ comm₂) p.1.1.1 P hU₀P)) _) ?_
  refine Eq.trans (transpose_comp_eq_of_affineModel i₁ i₂ i₃ f₁ g₁ comm₁ f₂ g₂ comm₂
    p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2 P hP hU₀V₀ hV₀P hU₀P I₀ J₀ K e₁ he₁ e₂ he₂ eV heV
    a c₀ hc₀) ?_
  refine Eq.trans hresinv.symm ?_
  exact val_map_eq_of_subsingleton (conormalSheaf i₁.liftCoborder.toLRSHom.toShHom)
    ((Opens.map i₁.toLRSHom.toShHom.hom.base).map (homOfLE hU₀U)) (homOfLE (hBT p)) _

/-- **Restriction naturality of the induced map of conormal sheaves.** Let `i : Z ⟶ X` be an
immersion, let `V ⊆ X` be open and let `(i ∣_ V) ≫ k = g ≫ j` be a commutative square with `j`
an immersion. Over a smaller open `V₀ ≤ V` the induced map of the restricted square is the induced
map of the square over `V`, pulled back along the restriction of `i⁻¹V` to `i⁻¹V₀` and composed
with the induced map of the restriction square itself.

This is `Stacks.Immersion.immersionConormalSheafMap_comp` stacked on
`AlgebraicGeometry.morphismRestrict_homOfLE`. It is the form in which the third condition of
[Stacks Project, Tag 04FH] — an equation between maps of conormal sheaves attached to a lift over
an open of `X` — is carried from `V` to `V₀`. -/
theorem immersionConormalSheafMap_morphismRestrict {Z X W W' : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] {j : W ⟶ W'} [IsImmersion j] {V V₀ : X.Opens} (hV : V₀ ≤ V)
    (g : (i ⁻¹ᵁ V).toScheme ⟶ W) (k : V.toScheme ⟶ W') (comm : i ∣_ V ≫ k = g ≫ j) :
    immersionConormalSheafMap (i ∣_ V₀) j (Z.homOfLE (i.preimage_mono hV) ≫ g)
        (X.homOfLE hV ≫ k)
        (toShHom_square (square_comp (morphismRestrict_homOfLE i V₀ V hV) comm)) =
      (modulePullbackComp (Z.homOfLE (i.preimage_mono hV)).toLRSHom.toShHom
            g.toLRSHom.toShHom).hom.app (conormalSheaf j.liftCoborder.toLRSHom.toShHom) ≫
        (modulePullback (Z.homOfLE (i.preimage_mono hV)).toLRSHom.toShHom).map
          (immersionConormalSheafMap (i ∣_ V) j g k (toShHom_square comm)) ≫
        immersionConormalSheafMap (i ∣_ V₀) (i ∣_ V) (Z.homOfLE (i.preimage_mono hV))
          (X.homOfLE hV) (toShHom_square (morphismRestrict_homOfLE i V₀ V hV)) :=
  immersionConormalSheafMap_comp (i ∣_ V₀) (i ∣_ V) j (Z.homOfLE (i.preimage_mono hV))
    (X.homOfLE hV) (morphismRestrict_homOfLE i V₀ V hV) g k comm

end Stacks.Immersion

namespace Stacks.ClosedImmersion

/-! ### The square map of a restriction square -/

variable {Zr Xr : RingedSpace.{u, u}}

/-- **The ideal-sheaf transport of a restriction is the ideal-sheaf map of the restriction
square.** For a morphism of ringed spaces `i : Zr ⟶ Xr` and an open `U ⊆ Xr`, the isomorphism
`ℐ_i|_U ≅ ℐ_{i|_U}` of `Stacks.ClosedImmersion.restrictIdealSheafIso`, read through the
identification of a restriction with a pullback along the open immersion, is the map of ideal
sheaves that the square `restrictHom i U ≫ ι_U = ι_{i⁻¹U} ≫ i` induces.

Both sides are pinned by their composites with the inclusion of `ℐ_{i|_U}` into the structure
sheaf, which is a monomorphism; the two composites agree by naturality of
`AlgebraicGeometry.RingedSpace.modulePullbackRestrictIso` and by
`AlgebraicGeometry.RingedSpace.modulePullbackUnitToUnit_ofRestrict`, which identifies that
isomorphism at the structure sheaf with the transpose of the structure-sheaf map. -/
theorem idealSheafMap_restrictHom_comp_ofRestrict (i : Zr ⟶ Xr) (U : Opens Xr.carrier) :
    (modulePullbackRestrictIso Xr U).hom.app (idealSheaf i) ≫ (restrictIdealSheafIso i U).hom =
      idealSheafMap (restrictHom_comp_ofRestrict i U) := by
  have := mono_idealSheafι (restrictHom i U)
  refine (cancel_mono (idealSheafι (restrictHom i U))).1 ?_
  rw [Category.assoc, restrictIdealSheafIso_hom_comp_ι, idealSheafMap_comp_ι]
  exact ((modulePullbackRestrictIso Xr U).hom.naturality (idealSheafι i)).symm.trans
    (congrArg
      (fun z => (modulePullback (Xr.ofRestrict U.isOpenEmbedding)).map (idealSheafι i) ≫ z)
      (modulePullbackUnitToUnit_ofRestrict Xr U).symm)

/-- **The conormal-sheaf map of a restriction square is the restriction isomorphism of the
conormal sheaf.** For a morphism of ringed spaces `i : Zr ⟶ Xr` and an open `U ⊆ Xr`, the map
`ι_{i⁻¹U}^* 𝒞_i ⟶ 𝒞_{i|_U}` of `Stacks.ClosedImmersion.conormalSheafMap` induced by the square
`restrictHom i U ≫ ι_U = ι_{i⁻¹U} ≫ i` is the isomorphism `𝒞_i|_{i⁻¹U} ≅ 𝒞_{i|_U}` of
`Stacks.ClosedImmersion.restrictConormalSheafIso`, read through the identification of a
restriction with a pullback along the open immersion.

In particular the induced map of a restriction square is an isomorphism, as
[Stacks Project, Tag 0473] predicts for a flat base change; this statement is sharper, since it
says *which* isomorphism it is.

Both maps are the pullback along `i|_U` of their ideal-sheaf counterparts twisted by the square
comparison: for the right-hand side that is
`Stacks.ClosedImmersion.squareIso_hom_comp_restrictConormal`, for the left-hand side it is the
definition of `Stacks.ClosedImmersion.conormalSheafMap`; so the statement follows from
`Stacks.ClosedImmersion.idealSheafMap_restrictHom_comp_ofRestrict` once the two square
comparisons are seen to be inverse, which is
`Stacks.ClosedImmersion.pullbackCompIso_inv`. -/
@[sga "3 I 6.8.5" "special case"]
theorem conormalSheafMap_restrictHom_comp_ofRestrict (i : Zr ⟶ Xr) (U : Opens Xr.carrier) :
    conormalSheafMap (restrictHom_comp_ofRestrict i U) =
      (modulePullbackRestrictIso Zr ((Opens.map i.hom.base).obj U)).hom.app (conormalSheaf i) ≫
        (restrictConormalSheafIso i U).hom := by
  rw [conormalSheafMap, ← idealSheafMap_restrictHom_comp_ofRestrict i U,
    ← squareIso_hom_comp_restrictConormal i U, ← pullbackCompIso_inv, Iso.hom_inv_id_assoc]

end Stacks.ClosedImmersion

/-! ### The parts of the tag the library already carries -/

add_to_stacks 01R4 "canonical map" Stacks.Immersion.immersionConormalSheafMap

add_to_stacks 01R4 "affine formula"
  Stacks.Immersion.isInducedConormalSheafMap_immersionConormalSheafMap

end
