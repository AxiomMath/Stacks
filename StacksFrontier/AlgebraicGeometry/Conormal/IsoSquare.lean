module

public import StacksFrontier.AlgebraicGeometry.Conormal.OpenFactorization
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackUnit

/-!
# The ideal sheaf and the conormal sheaf are invariant under isomorphisms

Let
```
Z₁ --j₁--→ X₁
|          |
a          b
↓          ↓
Z₂ --j₂--→ X₂
```
be a commuting square of ringed spaces in which `a` and `b` are **isomorphisms**. This file
transports the ideal sheaf and the conormal sheaf across such a square:

* `Stacks.ClosedImmersion.idealSheafIsoOfSquare` is `ℐ_{j₁} ≅ b^* ℐ_{j₂}`,
* `Stacks.ClosedImmersion.conormalSheafIsoOfSquare` is `𝒞_{j₁} ≅ a^* 𝒞_{j₂}`,
* `Stacks.ClosedImmersion.ambientPushforwardConormalIsoOfSquare` is
  `b_* ((j₁)_* 𝒞_{j₁}) ≅ (j₂)_* 𝒞_{j₂}`,

the last being the form in which the sections of a pushforward conormal sheaf over an open of
`X₁` become sections over the corresponding open of `X₂`.

This is the **second** of the two comparisons that the module docstring of
`StacksFrontier.AlgebraicGeometry.Conormal.AffineModel` names as missing between the affine model of
[Stacks Project, Tag 01R3] part (2) and that tag's statement: "transport of the whole computation
along the isomorphisms `V ≅ Spec Γ(X, V)` and `j ⁻¹ᵁ V ≅ Spec (Γ(X, V) ⧸ I)`". It is proved here
for ringed spaces, which is where `Stacks.ClosedImmersion.idealSheaf` and
`Stacks.ClosedImmersion.conormalSheaf` live. **Nothing here carries a `01R3` attribute**: a
transport statement is not that tag's statement, and the scheme-level glue that would turn this
into Tag 01R3 part (2) — identifying `V.toScheme` with `Spec Γ(X, V)` as *ringed spaces* and the
sections of a restriction with sections over an open — is not in this file.

## Main definitions

* `RingedSpaceModuleAdjunction.modulePushforwardEquivalenceOfIso`: pushforward along an
  isomorphism of ringed spaces is an equivalence on sheaves of modules.
* `RingedSpaceModuleAdjunction.modulePullbackIsoPushforwardInv`: `b^* ≅ (b⁻¹)_*` for an
  isomorphism `b`.
* `RingedSpaceModuleAdjunction.modulePullbackPushforwardUnitIsoOfIso` and
  `RingedSpaceModuleAdjunction.modulePullbackPushforwardCounitIsoOfIso`: the unit and
  counit of `b^* ⊣ b_*` as isomorphisms.
* `Stacks.ClosedImmersion.pullbackIdealSheafCompIso` is `b^* ℐ_{j ≫ b} ≅ ℐ_j`, for `b` an
  isomorphism.
* `Stacks.ClosedImmersion.idealSheafCompIsoOfIso` is `ℐ_{a ≫ j} ≅ ℐ_j`, for `a` an isomorphism.
* `Stacks.ClosedImmersion.modulePullbackIsoOfSquare` is `b^* ⋙ (j₁)^* ≅ (j₂)^* ⋙ a^*`, the
  identification of the two ways around the square.
* `Stacks.ClosedImmersion.idealSheafIsoOfSquare`,
  `Stacks.ClosedImmersion.conormalSheafIsoOfSquare`,
  `Stacks.ClosedImmersion.pushforwardIdealSheafIsoOfSquare`,
  `Stacks.ClosedImmersion.pushforwardConormalSheafIsoOfSquare` and
  `Stacks.ClosedImmersion.ambientPushforwardConormalIsoOfSquare` are the transports listed above.

## Main results

* `RingedSpaceModuleAdjunction.modulePullback_map_structureSheafModuleHom_comp_counit`:
  the structure-sheaf map of `j ≫ b`, pulled back along `b`, is the structure-sheaf map of `j`.
  This is `Stacks.ClosedImmersion.modulePullback_structureSheafModuleHom_comp_counit` with the
  open immersion `ι_U` replaced by an arbitrary morphism of ringed spaces; the proof of that
  statement never used the open immersion, so the generalisation is free.
* `RingedSpaceModuleAdjunction.isIso_structureSheafModuleHom_of_iso`: the structure-sheaf
  map of an isomorphism of ringed spaces is an isomorphism.
* Every bundled isomorphism below is pinned: `pullbackIdealSheafCompIso_hom_comp_ι`,
  `idealSheafCompIsoOfIso_hom_comp_ι`, `idealSheafIsoOfSquare_hom_comp_pullback_ι`,
  `pushforwardIdealSheafIsoOfSquare_hom_comp_ι`,
  `conormalSheafIsoOfSquare_hom_comp_pullback_ι`,
  `pushforwardConormalSheafIsoOfSquare_hom_comp_unit` and
  `ambientPushforwardConormalIsoOfSquare_hom`. A bundled isomorphism whose type does not mention
  its characterisation asserts nothing by itself.

## Implementation notes

The whole file rests on two observations.

The first is that for sheaves of modules on ringed spaces **pushforward is multiplicative on the
nose**: `RingedSpaceModuleAdjunction.modulePushforwardComp` and
`RingedSpaceModuleAdjunction.modulePushforwardId` have identity components, and
`RingedSpaceModuleAdjunction.structureSheafModuleHom_comp` is `rfl`. So pushforward along
an isomorphism is visibly an equivalence, and a pullback along an isomorphism is therefore a
pushforward along its inverse, hence exact, with invertible unit and counit. None of this needs a
description of the sections of a pullback.

The second is that the conjugation identity the open-immersion case turns on
(`Stacks.ClosedImmersion.modulePullback_structureSheafModuleHom_comp_counit`) holds for every
morphism of ringed spaces: both sides are transposes under `b^* ⊣ b_*` of the structure-sheaf map
of `j ≫ b`. Combined with
`RingedSpaceModuleAdjunction.isIso_modulePullbackUnitToUnit` — which is also already
available for every morphism — it identifies the two ideal sheaves as the kernels of one
morphism read in two vocabularies.

The ambient leg of the square is handled by that conjugation; the source leg is handled by
`CategoryTheory.Limits.kernelCompMono`, since `structureSheafModuleHom (a ≫ j₂)` is by `rfl`
`structureSheafModuleHom j₂` followed by the pushforward of the invertible
`structureSheafModuleHom a`.

Instance search cannot find `IsIso` of the counit of `b^* ⊣ b_*` on its own — an adjunction is
not a class, so `CategoryTheory.Adjunction.counit_isIso_of_R_fully_faithful` is unreachable from
the goal. The unit and counit are therefore packaged as named isomorphisms, exactly as
`AlgebraicGeometry.RingedSpace.modulePullbackPushforwardCounitOfRestrictIso` does for the
open-immersion case.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 01C2](https://stacks.math.columbia.edu/tag/01C2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open AlgebraicGeometry AlgebraicGeometry.RingedSpace

universe u

namespace RingedSpaceModuleAdjunction

variable {X Y : RingedSpace.{u, u}}

/-! ### Pushforward and pullback along an isomorphism -/

/-- Pushforward of sheaves of modules preserves zero morphisms: it does not change the underlying
maps on sections, only the opens they are indexed by. This is
`RingedSpaceModuleAdjunction.modulePushforward_map_zero` as an instance. -/
instance modulePushforward_preservesZeroMorphisms (f : X ⟶ Y) :
    (modulePushforward f).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- **Pushforward along an isomorphism of ringed spaces is an equivalence** on sheaves of
modules, with inverse the pushforward along the inverse isomorphism.

Nothing is needed beyond multiplicativity of pushforward: the two composites are the
pushforwards along `b ≫ b⁻¹` and `b⁻¹ ≫ b`, and
`RingedSpaceModuleAdjunction.modulePushforwardComp` and
`RingedSpaceModuleAdjunction.modulePushforwardId` have identity components, so the two
unit and counit isomorphisms are assembled from `CategoryTheory.eqToIso` alone. -/
def modulePushforwardEquivalenceOfIso (b : X ≅ Y) :
    SheafOfModules.{u} (structureSheafRing X) ≌ SheafOfModules.{u} (structureSheafRing Y) :=
  .mk (modulePushforward b.hom) (modulePushforward b.inv)
    ((modulePushforwardId X).symm ≪≫ eqToIso (congrArg modulePushforward b.hom_inv_id.symm) ≪≫
      (modulePushforwardComp b.hom b.inv).symm)
    (modulePushforwardComp b.inv b.hom ≪≫
      eqToIso (congrArg modulePushforward b.inv_hom_id) ≪≫ modulePushforwardId Y)

/-- The functor of `RingedSpaceModuleAdjunction.modulePushforwardEquivalenceOfIso` is the
pushforward along `b`. -/
@[simp]
theorem modulePushforwardEquivalenceOfIso_functor (b : X ≅ Y) :
    (modulePushforwardEquivalenceOfIso b).functor = modulePushforward b.hom :=
  rfl

/-- The inverse of `RingedSpaceModuleAdjunction.modulePushforwardEquivalenceOfIso` is the
pushforward along `b⁻¹`. -/
@[simp]
theorem modulePushforwardEquivalenceOfIso_inverse (b : X ≅ Y) :
    (modulePushforwardEquivalenceOfIso b).inverse = modulePushforward b.inv :=
  rfl

/-- Pushforward along an isomorphism of ringed spaces is an equivalence, as an instance. -/
instance isEquivalence_modulePushforward_hom (b : X ≅ Y) :
    (modulePushforward b.hom).IsEquivalence :=
  (modulePushforwardEquivalenceOfIso b).isEquivalence_functor

/-- Pushforward along the inverse of an isomorphism of ringed spaces is an equivalence, as an
instance. -/
instance isEquivalence_modulePushforward_inv (b : X ≅ Y) :
    (modulePushforward b.inv).IsEquivalence :=
  (modulePushforwardEquivalenceOfIso b).isEquivalence_inverse

/-- **Pullback along an isomorphism is pushforward along its inverse**, `b^* ≅ (b⁻¹)_*`.

Both are left adjoint to `b_*`: the first by
`RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction`, the second because
`RingedSpaceModuleAdjunction.modulePushforwardEquivalenceOfIso` exhibits `b_*` and
`(b⁻¹)_*` as inverse equivalences. Pinned by
`RingedSpaceModuleAdjunction.unit_modulePullbackIsoPushforwardInv_hom_app`. -/
def modulePullbackIsoPushforwardInv (b : X ≅ Y) :
    modulePullback b.hom ≅ modulePushforward b.inv :=
  (modulePullbackPushforwardAdjunction b.hom).leftAdjointUniq
    (modulePushforwardEquivalenceOfIso b).symm.toAdjunction

/-- **The characterisation of
`RingedSpaceModuleAdjunction.modulePullbackIsoPushforwardInv`.** Composed with the unit
of `b^* ⊣ b_*` it is the unit of `(b⁻¹)_* ⊣ b_*`; since a unit determines its left adjoint up to
unique isomorphism, this fixes the isomorphism completely. -/
theorem unit_modulePullbackIsoPushforwardInv_hom_app (b : X ≅ Y)
    (M : SheafOfModules.{u} (structureSheafRing Y)) :
    (modulePullbackPushforwardAdjunction b.hom).unit.app M ≫
        (modulePushforward b.hom).map ((modulePullbackIsoPushforwardInv b).hom.app M) =
      (modulePushforwardEquivalenceOfIso b).symm.toAdjunction.unit.app M :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ M

/-- **Pullback along an isomorphism of ringed spaces is an equivalence**, being isomorphic to the
pushforward along the inverse isomorphism. This is what makes it exact. -/
instance isEquivalence_modulePullback_of_iso (b : X ≅ Y) :
    (modulePullback b.hom).IsEquivalence :=
  Functor.isEquivalence_of_iso (modulePullbackIsoPushforwardInv b).symm

/-- Pullback along an isomorphism of ringed spaces preserves zero morphisms, being isomorphic to
a pushforward. -/
instance modulePullback_preservesZeroMorphisms_of_iso (b : X ≅ Y) :
    (modulePullback b.hom).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_iso (modulePullbackIsoPushforwardInv b).symm

/-- **`b^* (b_* N) ≅ N`** for an isomorphism `b` of ringed spaces: the counit of `b^* ⊣ b_*` is
an isomorphism, because its right adjoint `b_*` is an equivalence and therefore fully faithful.

The isomorphism is packaged rather than left to instance search, which cannot reach
`CategoryTheory.Adjunction.counit_isIso_of_R_fully_faithful` from the goal `IsIso (ε.app N)`
because an adjunction is not a class. -/
def modulePullbackPushforwardCounitIsoOfIso (b : X ≅ Y)
    (N : SheafOfModules.{u} (structureSheafRing X)) :
    (modulePullback b.hom).obj ((modulePushforward b.hom).obj N) ≅ N :=
  haveI : IsIso (modulePullbackPushforwardAdjunction b.hom).counit :=
    Adjunction.counit_isIso_of_R_fully_faithful _
  asIso ((modulePullbackPushforwardAdjunction b.hom).counit.app N)

/-- `RingedSpaceModuleAdjunction.modulePullbackPushforwardCounitIsoOfIso` is the counit of
`b^* ⊣ b_*`. -/
@[simp]
theorem modulePullbackPushforwardCounitIsoOfIso_hom (b : X ≅ Y)
    (N : SheafOfModules.{u} (structureSheafRing X)) :
    (modulePullbackPushforwardCounitIsoOfIso b N).hom =
      (modulePullbackPushforwardAdjunction b.hom).counit.app N :=
  rfl

/-- **`N ≅ b_* (b^* N)`** for an isomorphism `b` of ringed spaces: the unit of `b^* ⊣ b_*` is an
isomorphism, because its left adjoint `b^*` is an equivalence and therefore fully faithful. -/
def modulePullbackPushforwardUnitIsoOfIso (b : X ≅ Y)
    (N : SheafOfModules.{u} (structureSheafRing Y)) :
    N ≅ (modulePushforward b.hom).obj ((modulePullback b.hom).obj N) :=
  haveI : IsIso (modulePullbackPushforwardAdjunction b.hom).unit :=
    Adjunction.unit_isIso_of_L_fully_faithful _
  asIso ((modulePullbackPushforwardAdjunction b.hom).unit.app N)

/-- `RingedSpaceModuleAdjunction.modulePullbackPushforwardUnitIsoOfIso` is the unit of
`b^* ⊣ b_*`. -/
@[simp]
theorem modulePullbackPushforwardUnitIsoOfIso_hom (b : X ≅ Y)
    (N : SheafOfModules.{u} (structureSheafRing Y)) :
    (modulePullbackPushforwardUnitIsoOfIso b N).hom =
      (modulePullbackPushforwardAdjunction b.hom).unit.app N :=
  rfl

/-! ### The structure-sheaf map of an isomorphism -/

/-- **The structure-sheaf map is the unit followed by the pushforward of its own transpose.**
This is `RingedSpaceModuleAdjunction.homEquiv_modulePullbackUnitToUnit` written out
through `CategoryTheory.Adjunction.homEquiv_unit`. -/
theorem structureSheafModuleHom_eq_unit_comp (f : X ⟶ Y) :
    structureSheafModuleHom f =
      (modulePullbackPushforwardAdjunction f).unit.app
          (SheafOfModules.unit (structureSheafRing Y)) ≫
        (modulePushforward f).map (modulePullbackUnitToUnit f) :=
  (homEquiv_modulePullbackUnitToUnit f).symm.trans (Adjunction.homEquiv_unit ..)

/-- **The structure-sheaf map of an isomorphism of ringed spaces is an isomorphism.** By
`RingedSpaceModuleAdjunction.structureSheafModuleHom_eq_unit_comp` it is the unit of
`b^* ⊣ b_*` at `𝒪_Y` followed by the pushforward of `b^* 𝒪_Y ⟶ 𝒪_X`; the latter is an
isomorphism for every morphism by
`RingedSpaceModuleAdjunction.isIso_modulePullbackUnitToUnit`, and the former because
`b^*` is an equivalence. -/
instance isIso_structureSheafModuleHom_of_iso (b : X ≅ Y) :
    IsIso (structureSheafModuleHom b.hom) := by
  rw [structureSheafModuleHom_eq_unit_comp]
  infer_instance

/-! ### The conjugation identity for an arbitrary ambient morphism -/

/-- **The structure-sheaf map of `j ≫ b`, pulled back along `b`, is the structure-sheaf map of
`j`** — conjugated by `b^* 𝒪_Y ⟶ 𝒪_X` and by the counit of `b^* ⊣ b_*` at `j_* 𝒪_Z`.

Both sides are transposes under `b^* ⊣ b_*` of the structure-sheaf map of `j ≫ b`: the left-hand
side by the formula for the inverse hom-set bijection, the right-hand side by
`RingedSpaceModuleAdjunction.homEquiv_modulePullbackUnitToUnit` and naturality of
transposition in the target.

This is `Stacks.ClosedImmersion.modulePullback_structureSheafModuleHom_comp_counit` with the open
immersion `ι_U` replaced by an arbitrary morphism of ringed spaces `b`. That proof used nothing
about open immersions, so the generalisation costs nothing; what it buys is the case of `b` an
isomorphism, where the counit is again invertible. -/
theorem modulePullback_map_structureSheafModuleHom_comp_counit {Z : RingedSpace.{u, u}}
    (b : X ⟶ Y) (j : Z ⟶ X) :
    (modulePullback b).map (structureSheafModuleHom (j ≫ b)) ≫
        (modulePullbackPushforwardAdjunction b).counit.app
          ((modulePushforward j).obj (SheafOfModules.unit (structureSheafRing Z))) =
      modulePullbackUnitToUnit b ≫ structureSheafModuleHom j := by
  refine ((modulePullbackPushforwardAdjunction b).homEquiv _ _).injective ?_
  rw [Adjunction.homEquiv_naturality_right, homEquiv_modulePullbackUnitToUnit]
  exact (congrArg ((modulePullbackPushforwardAdjunction b).homEquiv _ _)
      (Adjunction.homEquiv_counit _ _ _ _).symm).trans (Equiv.apply_symm_apply _ _)

end RingedSpaceModuleAdjunction

namespace Stacks.ClosedImmersion

open RingedSpaceModuleAdjunction

variable {Z₁ Z₂ X₁ X₂ : RingedSpace.{u, u}}

/-! ### The two legs of the square -/

/-- **`b^* ℐ_{j ≫ b} ≅ ℐ_j` for an isomorphism `b`.** The ideal sheaf of `j ≫ b` pulls back along
`b` to the ideal sheaf of `j`.

Pullback along an isomorphism is left exact, so the left-hand side is the kernel of the
pulled-back structure-sheaf map, and that morphism is the structure-sheaf map of `j` conjugated
by two isomorphisms, by
`RingedSpaceModuleAdjunction.modulePullback_map_structureSheafModuleHom_comp_counit`.
Pinned by `Stacks.ClosedImmersion.pullbackIdealSheafCompIso_hom_comp_ι`.

This is `Stacks.ClosedImmersion.idealSheafOfRestrictIso` with the open immersion `ι_U` replaced by
an isomorphism; the two statements have no common instance, since an open immersion `ι_U` is an
isomorphism only for `U = ⊤`. -/
def pullbackIdealSheafCompIso (b : X₁ ≅ X₂) (j : Z₁ ⟶ X₁) :
    (modulePullback b.hom).obj (idealSheaf (j ≫ b.hom)) ≅ idealSheaf j :=
  PreservesKernel.iso (modulePullback b.hom) (structureSheafModuleHom (j ≫ b.hom)) ≪≫
    kernel.mapIso _ (structureSheafModuleHom j) (asIso (modulePullbackUnitToUnit b.hom))
      (modulePullbackPushforwardCounitIsoOfIso b
        ((modulePushforward j).obj (SheafOfModules.unit (structureSheafRing Z₁))))
      (modulePullback_map_structureSheafModuleHom_comp_counit b.hom j)

/-- **The characterising property of `Stacks.ClosedImmersion.pullbackIdealSheafCompIso`.**
Followed by the inclusion of `ℐ_j` into `𝒪_{X₁}` it is the pullback along `b` of the inclusion of
`ℐ_{j ≫ b}` into `𝒪_{X₂}`, read in `𝒪_{X₁}` through
`RingedSpaceModuleAdjunction.modulePullbackUnitToUnit`. Since the inclusion of an ideal
sheaf is a monomorphism, this determines the isomorphism. -/
theorem pullbackIdealSheafCompIso_hom_comp_ι (b : X₁ ≅ X₂) (j : Z₁ ⟶ X₁) :
    (pullbackIdealSheafCompIso b j).hom ≫ idealSheafι j =
      (modulePullback b.hom).map (idealSheafι (j ≫ b.hom)) ≫
        modulePullbackUnitToUnit b.hom := by
  have h1 : (kernel.mapIso ((modulePullback b.hom).map (structureSheafModuleHom (j ≫ b.hom)))
        (structureSheafModuleHom j) (asIso (modulePullbackUnitToUnit b.hom))
        (modulePullbackPushforwardCounitIsoOfIso b
          ((modulePushforward j).obj (SheafOfModules.unit (structureSheafRing Z₁))))
        (modulePullback_map_structureSheafModuleHom_comp_counit b.hom j)).hom ≫
      idealSheafι j =
      kernel.ι ((modulePullback b.hom).map (structureSheafModuleHom (j ≫ b.hom))) ≫
        modulePullbackUnitToUnit b.hom :=
    kernel.lift_ι _ _ _
  have h2 : (PreservesKernel.iso (modulePullback b.hom)
        (structureSheafModuleHom (j ≫ b.hom))).hom ≫
      kernel.ι ((modulePullback b.hom).map (structureSheafModuleHom (j ≫ b.hom))) =
      (modulePullback b.hom).map (idealSheafι (j ≫ b.hom)) := by
    rw [← PreservesKernel.iso_inv_ι, Iso.hom_inv_id_assoc]
    rfl
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => (PreservesKernel.iso (modulePullback b.hom)
        (structureSheafModuleHom (j ≫ b.hom))).hom ≫ z) h1).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun z => z ≫ modulePullbackUnitToUnit b.hom) h2)))

/-- **`ℐ_{a ≫ j} ≅ ℐ_j` for an isomorphism `a` of the source.** Precomposing with an isomorphism
does not change the defining ideal.

By `RingedSpaceModuleAdjunction.structureSheafModuleHom_comp` the structure-sheaf map of
`a ≫ j` is, on the nose, that of `j` followed by `j_*` of the structure-sheaf map of `a`; the
latter is an isomorphism by
`RingedSpaceModuleAdjunction.isIso_structureSheafModuleHom_of_iso`, hence a monomorphism,
so the two kernels agree by `CategoryTheory.Limits.kernelCompMono`. Pinned by
`Stacks.ClosedImmersion.idealSheafCompIsoOfIso_hom_comp_ι`. -/
def idealSheafCompIsoOfIso (a : Z₁ ≅ Z₂) (j : Z₂ ⟶ X₂) :
    idealSheaf (a.hom ≫ j) ≅ idealSheaf j :=
  kernelCompMono (structureSheafModuleHom j)
    ((modulePushforward j).map (structureSheafModuleHom a.hom))

/-- **The characterising property of `Stacks.ClosedImmersion.idealSheafCompIsoOfIso`.** It
commutes with the two inclusions into `𝒪_{X₂}`, which are the same morphism; since they are
monomorphisms this determines the isomorphism. -/
theorem idealSheafCompIsoOfIso_hom_comp_ι (a : Z₁ ≅ Z₂) (j : Z₂ ⟶ X₂) :
    (idealSheafCompIsoOfIso a j).hom ≫ idealSheafι j = idealSheafι (a.hom ≫ j) :=
  kernel.lift_ι _ _ _

/-- Transporting the inclusion of an ideal sheaf along an equality of morphisms of ringed spaces
does nothing. -/
theorem eqToHom_comp_idealSheafι {p q : Z₁ ⟶ X₂} (h : p = q) :
    eqToHom (congrArg idealSheaf h) ≫ idealSheafι q = idealSheafι p := by
  subst h
  exact Category.id_comp _

/-- **A morphism that factors through an isomorphism of the source has the same ideal sheaf, by an
isomorphism compatible with the two inclusions into `𝒪_{X₂}`.** For `p = a.hom ≫ j` with `a` an
isomorphism, `ℐ_j ≅ ℐ_p`, and the isomorphism carries `idealSheafι p` to `idealSheafι j`. Since
those inclusions are monomorphisms this determines the isomorphism, so the `∃` names a unique
object.

The witness is `Stacks.ClosedImmersion.idealSheafCompIsoOfIso` followed by the transport along
`h`, and the proof is `Stacks.ClosedImmersion.idealSheafCompIsoOfIso_hom_comp_ι` and
`Stacks.ClosedImmersion.eqToHom_comp_idealSheafι`.

**The existential is load-bearing and is not a weakening.** Stated as an equation about the
explicit composite, this is a `(kernel) deterministic timeout` at any concrete pair of affine
schemes — for instance at `Stacks.ClosedImmersion.AffineConormal.idealSheafQuotIso`, where both legs
check in seconds individually but the composite does not. The cost is in the kernel's comparison
of the *statement's* composite against the proof term's type, and binding the isomorphism
existentially removes that composite from every type the kernel has to compare while keeping the
compatibility. This is what lets
`Stacks.ClosedImmersion.AffineConormal.surjIdealSheafIso` be defined together with its
normalisation; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.AffineZeroSection`. -/
theorem exists_idealSheafIso_hom_comp_ι (a : Z₁ ≅ Z₂) (j : Z₂ ⟶ X₂) (p : Z₁ ⟶ X₂)
    (h : p = a.hom ≫ j) :
    ∃ Φ : idealSheaf j ≅ idealSheaf p, Φ.hom ≫ idealSheafι p = idealSheafι j := by
  refine ⟨(idealSheafCompIsoOfIso a j).symm ≪≫ (eqToIso (congrArg idealSheaf h)).symm, ?_⟩
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun z => (idealSheafCompIsoOfIso a j).inv ≫ z)
    (eqToHom_comp_idealSheafι h.symm)) ?_
  exact (Iso.inv_comp_eq _).mpr (idealSheafCompIsoOfIso_hom_comp_ι a j).symm

/-! ### The ideal sheaf across an isomorphism square -/

/-- Pushing forward an isomorphism `M ≅ b^* N` and then inverting the unit at `N` is compatible
with the unit of `b^* ⊣ b_*`. -/
private theorem pushforward_mapIso_trans_unitIso_symm_hom_comp_unit (b : X₁ ≅ X₂)
    {M : SheafOfModules.{u} (structureSheafRing X₁)}
    {N : SheafOfModules.{u} (structureSheafRing X₂)}
    (φ : M ≅ (modulePullback b.hom).obj N) :
    ((modulePushforward b.hom).mapIso φ ≪≫ (modulePullbackPushforwardUnitIsoOfIso b N).symm).hom ≫
        (modulePullbackPushforwardAdjunction b.hom).unit.app N =
      (modulePushforward b.hom).map φ.hom := by
  rw [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
    ← modulePullbackPushforwardUnitIsoOfIso_hom b N, Iso.inv_hom_id, Category.comp_id]

variable (a : Z₁ ≅ Z₂) (b : X₁ ≅ X₂) (j₁ : Z₁ ⟶ X₁) (j₂ : Z₂ ⟶ X₂)

/-- **`ℐ_{j₁} ≅ b^* ℐ_{j₂}`: the ideal sheaf is invariant under an isomorphism square.** For
`j₁ ≫ b = a ≫ j₂` with `a` and `b` isomorphisms, the ideal sheaf of `j₁` is the pullback along
`b` of the ideal sheaf of `j₂`.

The two legs are `Stacks.ClosedImmersion.pullbackIdealSheafCompIso` and
`Stacks.ClosedImmersion.idealSheafCompIsoOfIso`, joined by the equality of the two composites.
Pinned by `Stacks.ClosedImmersion.idealSheafIsoOfSquare_hom_comp_pullback_ι`. -/
def idealSheafIsoOfSquare (comm : j₁ ≫ b.hom = a.hom ≫ j₂) :
    idealSheaf j₁ ≅ (modulePullback b.hom).obj (idealSheaf j₂) :=
  (pullbackIdealSheafCompIso b j₁).symm ≪≫
    (modulePullback b.hom).mapIso
      (eqToIso (congrArg idealSheaf comm) ≪≫ idealSheafCompIsoOfIso a j₂)

/-- **The characterising property of `Stacks.ClosedImmersion.idealSheafIsoOfSquare`.** Followed by
the pullback along `b` of the inclusion `ℐ_{j₂} ⟶ 𝒪_{X₂}` and by
`RingedSpaceModuleAdjunction.modulePullbackUnitToUnit`, it is the inclusion
`ℐ_{j₁} ⟶ 𝒪_{X₁}`. Since that inclusion is a monomorphism and the two comparison morphisms are
monomorphisms as well, this determines the isomorphism. -/
theorem idealSheafIsoOfSquare_hom_comp_pullback_ι (comm : j₁ ≫ b.hom = a.hom ≫ j₂) :
    (idealSheafIsoOfSquare a b j₁ j₂ comm).hom ≫
        (modulePullback b.hom).map (idealSheafι j₂) ≫ modulePullbackUnitToUnit b.hom =
      idealSheafι j₁ := by
  have key : (eqToIso (congrArg idealSheaf comm) ≪≫ idealSheafCompIsoOfIso a j₂).hom ≫
      idealSheafι j₂ = idealSheafι (j₁ ≫ b.hom) := by
    rw [Iso.trans_hom, eqToIso.hom, Category.assoc, idealSheafCompIsoOfIso_hom_comp_ι]
    exact eqToHom_comp_idealSheafι comm
  rw [idealSheafIsoOfSquare, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    ← Category.assoc ((modulePullback b.hom).map
      (eqToIso (congrArg idealSheaf comm) ≪≫ idealSheafCompIsoOfIso a j₂).hom),
    ← CategoryTheory.Functor.map_comp, key, ← pullbackIdealSheafCompIso_hom_comp_ι b j₁,
    Iso.inv_hom_id_assoc]

/-- **`b_* ℐ_{j₁} ≅ ℐ_{j₂}`**, the pushforward form of
`Stacks.ClosedImmersion.idealSheafIsoOfSquare`: the ideal sheaf of `j₁`, read on `X₂` through the
isomorphism `b`, is the ideal sheaf of `j₂`.

Pinned by `Stacks.ClosedImmersion.pushforwardIdealSheafIsoOfSquare_hom_comp_ι`. -/
def pushforwardIdealSheafIsoOfSquare (comm : j₁ ≫ b.hom = a.hom ≫ j₂) :
    (modulePushforward b.hom).obj (idealSheaf j₁) ≅ idealSheaf j₂ :=
  (modulePushforward b.hom).mapIso (idealSheafIsoOfSquare a b j₁ j₂ comm) ≪≫
    (modulePullbackPushforwardUnitIsoOfIso b (idealSheaf j₂)).symm

/-- **The characterising property of
`Stacks.ClosedImmersion.pushforwardIdealSheafIsoOfSquare`.** Followed by the unit of `b^* ⊣ b_*`
at `ℐ_{j₂}` it is `b_*` of `Stacks.ClosedImmersion.idealSheafIsoOfSquare`.

The unit is an isomorphism because `b` is, so this determines the isomorphism from the pinned
`Stacks.ClosedImmersion.idealSheafIsoOfSquare`. -/
theorem pushforwardIdealSheafIsoOfSquare_hom_comp_unit (comm : j₁ ≫ b.hom = a.hom ≫ j₂) :
    (pushforwardIdealSheafIsoOfSquare a b j₁ j₂ comm).hom ≫
        (modulePullbackPushforwardAdjunction b.hom).unit.app (idealSheaf j₂) =
      (modulePushforward b.hom).map (idealSheafIsoOfSquare a b j₁ j₂ comm).hom := by
  exact pushforward_mapIso_trans_unitIso_symm_hom_comp_unit b _

/-- **`Stacks.ClosedImmersion.pushforwardIdealSheafIsoOfSquare` is compatible with the inclusions
into the structure sheaves.** Followed by the inclusion `ℐ_{j₂} ⟶ 𝒪_{X₂}` and by the
structure-sheaf map of `b`, it is the pushforward along `b` of the inclusion
`ℐ_{j₁} ⟶ 𝒪_{X₁}`.

Since the structure-sheaf map of `b` is an isomorphism
(`RingedSpaceModuleAdjunction.isIso_structureSheafModuleHom_of_iso`) and the inclusion of
an ideal sheaf is a monomorphism, this is a second, independent determination of the
isomorphism. -/
theorem pushforwardIdealSheafIsoOfSquare_hom_comp_ι (comm : j₁ ≫ b.hom = a.hom ≫ j₂) :
    (pushforwardIdealSheafIsoOfSquare a b j₁ j₂ comm).hom ≫
        idealSheafι j₂ ≫ structureSheafModuleHom b.hom =
      (modulePushforward b.hom).map (idealSheafι j₁) := by
  have hunit := (modulePullbackPushforwardAdjunction b.hom).unit.naturality (idealSheafι j₂)
  simp only [Functor.id_map, Functor.comp_map] at hunit
  have hnat : idealSheafι j₂ ≫ structureSheafModuleHom b.hom =
      (modulePullbackPushforwardAdjunction b.hom).unit.app (idealSheaf j₂) ≫
        (modulePushforward b.hom).map ((modulePullback b.hom).map (idealSheafι j₂)) ≫
          (modulePushforward b.hom).map (modulePullbackUnitToUnit b.hom) := by
    rw [structureSheafModuleHom_eq_unit_comp, ← Category.assoc, hunit, Category.assoc]
  have key := congrArg (modulePushforward b.hom).map
    (idealSheafIsoOfSquare_hom_comp_pullback_ι a b j₁ j₂ comm)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at key
  refine Eq.trans ?_ key
  rw [hnat, ← Category.assoc, pushforwardIdealSheafIsoOfSquare_hom_comp_unit]

/-! ### The conormal sheaf across an isomorphism square -/

/-- **`b^* ⋙ (j₁)^* ≅ (j₂)^* ⋙ a^*`: the two ways around the square agree.** This is the
composition law `RingedSpaceModuleAdjunction.modulePullbackComp` on each side, joined by
the equality of the two composites.

It is the functorial form of `Stacks.ClosedImmersion.pullbackCompIso`, and stating it as a
natural isomorphism rather than object by object is what makes
`Stacks.ClosedImmersion.conormalSheafIsoOfSquare_hom_comp_pullback_ι` a single naturality
step. -/
def modulePullbackIsoOfSquare (comm : j₁ ≫ b.hom = a.hom ≫ j₂) :
    modulePullback b.hom ⋙ modulePullback j₁ ≅ modulePullback j₂ ⋙ modulePullback a.hom :=
  (modulePullbackComp j₁ b.hom).symm ≪≫ modulePullbackCongr comm ≪≫ modulePullbackComp a.hom j₂

/-- **`𝒞_{j₁} ≅ a^* 𝒞_{j₂}`: the conormal sheaf is invariant under an isomorphism square.** For
`j₁ ≫ b = a ≫ j₂` with `a` and `b` isomorphisms, the conormal sheaf of `j₁` is the pullback along
`a` of the conormal sheaf of `j₂`.

It is `(j₁)^*` of `Stacks.ClosedImmersion.idealSheafIsoOfSquare` followed by
`Stacks.ClosedImmersion.modulePullbackIsoOfSquare` at the ideal sheaf of `j₂`. Pinned by
`Stacks.ClosedImmersion.conormalSheafIsoOfSquare_hom_comp_pullback_ι`. -/
def conormalSheafIsoOfSquare (comm : j₁ ≫ b.hom = a.hom ≫ j₂) :
    conormalSheaf j₁ ≅ (modulePullback a.hom).obj (conormalSheaf j₂) :=
  (modulePullback j₁).mapIso (idealSheafIsoOfSquare a b j₁ j₂ comm) ≪≫
    (modulePullbackIsoOfSquare a b j₁ j₂ comm).app (idealSheaf j₂)

/-- **The characterising property of `Stacks.ClosedImmersion.conormalSheafIsoOfSquare`.** Read
inside `a^* (j₂)^* 𝒪_{X₂}` — that is, after mapping both conormal sheaves along the pullback of
the relevant ideal-sheaf inclusion — the isomorphism is `(j₁)^*` of the pinned
`Stacks.ClosedImmersion.idealSheafIsoOfSquare` followed by
`Stacks.ClosedImmersion.modulePullbackIsoOfSquare` at the structure sheaf.

The proof is one naturality square for
`Stacks.ClosedImmersion.modulePullbackIsoOfSquare`. Since
`RingedSpaceModuleAdjunction.modulePullbackComp` is itself characterised by
`RingedSpaceModuleAdjunction.conjugateEquiv_modulePullbackComp_hom`, and
`Stacks.ClosedImmersion.idealSheafIsoOfSquare` is determined by
`Stacks.ClosedImmersion.idealSheafIsoOfSquare_hom_comp_pullback_ι`, this fixes the isomorphism
rather than leaving it an arbitrary witness of its type. -/
theorem conormalSheafIsoOfSquare_hom_comp_pullback_ι (comm : j₁ ≫ b.hom = a.hom ≫ j₂) :
    (conormalSheafIsoOfSquare a b j₁ j₂ comm).hom ≫
        (modulePullback a.hom).map ((modulePullback j₂).map (idealSheafι j₂)) =
      (modulePullback j₁).map ((idealSheafIsoOfSquare a b j₁ j₂ comm).hom ≫
          (modulePullback b.hom).map (idealSheafι j₂)) ≫
        (modulePullbackIsoOfSquare a b j₁ j₂ comm).hom.app
          (SheafOfModules.unit (structureSheafRing X₂)) := by
  rw [conormalSheafIsoOfSquare, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc,
    CategoryTheory.Functor.map_comp, Category.assoc]
  exact congrArg
    (fun z => (modulePullback j₁).map (idealSheafIsoOfSquare a b j₁ j₂ comm).hom ≫ z)
    ((modulePullbackIsoOfSquare a b j₁ j₂ comm).hom.naturality (idealSheafι j₂)).symm

/-- **`a_* 𝒞_{j₁} ≅ 𝒞_{j₂}`**, the pushforward form of
`Stacks.ClosedImmersion.conormalSheafIsoOfSquare`.

Pinned by `Stacks.ClosedImmersion.pushforwardConormalSheafIsoOfSquare_hom_comp_unit`: composed
with the invertible unit of `a^* ⊣ a_*` it is `a_*` of
`Stacks.ClosedImmersion.conormalSheafIsoOfSquare`, which determines it because that unit is an
isomorphism. -/
def pushforwardConormalSheafIsoOfSquare (comm : j₁ ≫ b.hom = a.hom ≫ j₂) :
    (modulePushforward a.hom).obj (conormalSheaf j₁) ≅ conormalSheaf j₂ :=
  (modulePushforward a.hom).mapIso (conormalSheafIsoOfSquare a b j₁ j₂ comm) ≪≫
    (modulePullbackPushforwardUnitIsoOfIso a (conormalSheaf j₂)).symm

/-- **The characterising property of
`Stacks.ClosedImmersion.pushforwardConormalSheafIsoOfSquare`.** Followed by the unit of
`a^* ⊣ a_*` at `𝒞_{j₂}` it is `a_*` of `Stacks.ClosedImmersion.conormalSheafIsoOfSquare`.

The unit is an isomorphism because `a` is, so this determines the isomorphism from the pinned
`Stacks.ClosedImmersion.conormalSheafIsoOfSquare`. -/
theorem pushforwardConormalSheafIsoOfSquare_hom_comp_unit (comm : j₁ ≫ b.hom = a.hom ≫ j₂) :
    (pushforwardConormalSheafIsoOfSquare a b j₁ j₂ comm).hom ≫
        (modulePullbackPushforwardAdjunction a.hom).unit.app (conormalSheaf j₂) =
      (modulePushforward a.hom).map (conormalSheafIsoOfSquare a b j₁ j₂ comm).hom := by
  exact pushforward_mapIso_trans_unitIso_symm_hom_comp_unit a _

/-- **`b_* ((j₁)_* 𝒞_{j₁}) ≅ (j₂)_* 𝒞_{j₂}`.** The pushforward of the conormal sheaf of `j₁` to
`X₁`, read on `X₂` through `b`, is the pushforward of the conormal sheaf of `j₂`.

This is the form in which the computation transports to *sections*: over an open `A` of `X₂` the
left-hand side has the sections of `(j₁)_* 𝒞_{j₁}` over `b⁻¹ A`. Pinned by
`Stacks.ClosedImmersion.ambientPushforwardConormalIsoOfSquare_hom`, which identifies it with
`(j₂)_*` of the pinned `Stacks.ClosedImmersion.pushforwardConormalSheafIsoOfSquare`. -/
def ambientPushforwardConormalIsoOfSquare (comm : j₁ ≫ b.hom = a.hom ≫ j₂) :
    (modulePushforward b.hom).obj ((modulePushforward j₁).obj (conormalSheaf j₁)) ≅
      (modulePushforward j₂).obj (conormalSheaf j₂) :=
  (modulePushforwardComp j₁ b.hom).app (conormalSheaf j₁) ≪≫
    eqToIso (congrArg (fun p : Z₁ ⟶ X₂ => (modulePushforward p).obj (conormalSheaf j₁)) comm) ≪≫
    ((modulePushforwardComp a.hom j₂).app (conormalSheaf j₁)).symm ≪≫
    (modulePushforward j₂).mapIso (pushforwardConormalSheafIsoOfSquare a b j₁ j₂ comm)

/-- **The characterising property of
`Stacks.ClosedImmersion.ambientPushforwardConormalIsoOfSquare`**: the two pushforward composition
isomorphisms it is built from contribute nothing, so it is the transport of
`Stacks.ClosedImmersion.pushforwardConormalSheafIsoOfSquare` along the equality of the two
composites of the square.

This is where multiplicativity of pushforward being an equality rather than an isomorphism pays
off: `RingedSpaceModuleAdjunction.modulePushforwardComp` has identity components, so the
only comparison left is the `CategoryTheory.eqToHom` of `comm`. -/
theorem ambientPushforwardConormalIsoOfSquare_hom (comm : j₁ ≫ b.hom = a.hom ≫ j₂) :
    ((modulePushforwardComp j₁ b.hom).app (conormalSheaf j₁)).inv ≫
        (ambientPushforwardConormalIsoOfSquare a b j₁ j₂ comm).hom =
      eqToHom (congrArg (fun p : Z₁ ⟶ X₂ =>
            (modulePushforward p).obj (conormalSheaf j₁)) comm) ≫
        ((modulePushforwardComp a.hom j₂).app (conormalSheaf j₁)).inv ≫
          (modulePushforward j₂).map
            (pushforwardConormalSheafIsoOfSquare a b j₁ j₂ comm).hom := by
  rw [ambientPushforwardConormalIsoOfSquare, Iso.trans_hom, Iso.inv_hom_id_assoc, Iso.trans_hom,
    Iso.trans_hom, eqToIso.hom, Iso.symm_hom, Functor.mapIso_hom]

end Stacks.ClosedImmersion

end
