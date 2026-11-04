module

public import StacksFrontier.CategoryTheory.Sites.Modules.SquareZeroPushout
public import StacksFrontier.Topology.Sheaves.RingedSpace.Thickening

/-!
# The first order thickening of ringed spaces presented by a square-zero pushout

A sheaf of commutative rings `O'` on the space of a ringed space `X`, together with a locally
surjective morphism `p : O' ⟶ 𝒪_X` whose kernel has square zero on sections, is the same thing
as a first order thickening `i : X ⟶ X'` of ringed spaces with `X'` carried by the space of `X`.
This file makes the ringed space `X'` and the morphism `i`, and proves
`AlgebraicGeometry.RingedSpaceThickening.IsFirstOrderThickening i`.

It is then applied to the square-zero pushout `(R ⋉ 𝒢)/J` of
`StacksFrontier.CategoryTheory.Sites.Modules.SquareZeroPushout`, taken on the site of opens of `X`
with `ℬ = 𝒪_X`: that pushout, with its projection onto `𝒪_X`, presents a first order thickening
of `X`. This is the deformed space `X'_ξ` of the construction of [Stacks 08UC].

## Main definitions

* `Stacks.Deformation.SqZeroThickening.thickenedSpace`: the ringed space with the space of `X`
  and structure sheaf `O'`.
* `Stacks.Deformation.SqZeroThickening.thickening`: the morphism `X ⟶ X'`, the identity on the
  underlying space and `p` on structure sheaves.
* `Stacks.Deformation.SqZeroThickening.pushoutThickenedSpace` and
  `Stacks.Deformation.SqZeroThickening.pushoutThickening`: the two of them for the square-zero
  pushout and its projection onto `𝒪_X`.

## Main results

* `Stacks.Deformation.SqZeroThickening.isThickening_thickening` and
  `Stacks.Deformation.SqZeroThickening.isFirstOrderThickening_thickening`: `i` is a thickening,
  and a first order one, as soon as `p` is locally surjective and the product of two sections
  killed by `p` vanishes.
* `Stacks.Deformation.SqZeroThickening.isFirstOrderThickening_pushoutThickening`: **the
  square-zero pushout presents a first order thickening of `X`.** Its two hypotheses are
  discharged by `Stacks.Sites.SqZeroPushout.isLocallySurjective_pushoutProj` and by the exactness
  statements `Stacks.Sites.SqZeroPushout.pushoutProj_app_eq_zero_iff` and
  `Stacks.Sites.SqZeroPushout.pushoutInr_mul_pushoutInr`: a section killed by the projection is
  `[(0, n)]`, and two such multiply to zero.

## Implementation notes

The underlying spaces of `X` and `X'` are *equal*, and the morphism `i` is the identity on them;
this is the source's own reduction, and it is what makes the comorphism of `i` literally `p`, so
that `AlgebraicGeometry.RingedSpaceModuleAdjunction.structureSheafHom i` is `p` composed with the
forgetful functor to `RingCat` on the nose. All three clauses of `IsThickening` then come out of
hypotheses about `p` alone: the underlying map is an isomorphism because it is the identity; the
structure-sheaf map is an epimorphism of sheaves of modules because it is locally surjective and
the forgetful functor to sheaves of abelian groups reflects epimorphisms; and the kernel is
locally nilpotent with no shrinking of the open at all, since a section it contains already
squares to zero over the same open.

The hypothesis is stated as "the product of two sections killed by `p` is zero" rather than as
`Ker(p)² = ⊥`, because that is the form the pushout supplies — there a section killed by the
projection is exhibited as `[(0, n)]` and two such multiply to zero — and because
`IsFirstOrderThickening` asks for `Ker² = ⊥` over every open, which is exactly this statement
quantified over pairs.

Everything is in one universe and the site is the small site of opens of `X`, which is what the
square-zero pushout and `RingedSpace.{u, u}` both require.

## References

* [Stacks Project, Tag 08UC](https://stacks.math.columbia.edu/tag/08UC)
* [Stacks Project, Tag 08KZ](https://stacks.math.columbia.edu/tag/08KZ)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace PresheafOfModules
open RingedSpaceModuleAdjunction
open AlgebraicGeometry.RingedSpaceThickening

universe u

namespace Stacks.Deformation.SqZeroThickening

section General

variable (X : RingedSpace.{u, u})

variable (O' : Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u})
  (p : O' ⟶ (X.sheaf : Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}))

/-- The ringed space with the same underlying topological space as `X` and structure sheaf
`O'`. -/
noncomputable def thickenedSpace : RingedSpace.{u, u} where
  carrier := X.carrier
  presheaf := O'.obj
  IsSheaf := O'.property

/-- The morphism of ringed spaces `X ⟶ X'` which is the identity on the underlying space and
`p : O' ⟶ 𝒪_X` on structure sheaves. -/
noncomputable def thickening : X ⟶ thickenedSpace X O' :=
  ⟨{ base := 𝟙 X.carrier, c := p.hom }⟩

/-- The underlying map of `i : X ⟶ X'` is the identity. -/
theorem thickening_base : (thickening X O' p).hom.base = 𝟙 X.carrier := rfl

/-- The comorphism of `i : X ⟶ X'`, read on sections, is `p`. -/
theorem structureSheafHom_thickening_app (U : (Opens X.carrier)ᵒᵖ) (a : O'.obj.obj U) :
    (structureSheafHom (thickening X O' p)).hom.app U a = p.hom.app U a :=
  rfl

/-- **`i : X ⟶ X'` is a thickening** as soon as `p` is locally surjective and the product of two
local sections killed by `p` vanishes: the underlying map is the identity, local surjectivity
gives the epimorphism of sheaves of modules, and a section of the kernel squares to zero over the
open it is given on, so the kernel is locally nilpotent. -/
theorem isThickening_thickening
    (hp : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier) p.hom)
    (hsq : ∀ (U : (Opens X.carrier)ᵒᵖ) (a b : O'.obj.obj U),
      p.hom.app U a = 0 → p.hom.app U b = 0 → a * b = 0) :
    IsThickening (thickening X O' p) := by
  refine ⟨?_, ?_, ?_⟩
  · change IsIso (𝟙 X.carrier)
    infer_instance
  · have h : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
        ((PresheafOfModules.toPresheaf _).map
          (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom (thickening X O' p))).val) :=
      ⟨fun s => hp.imageSieve_mem s⟩
    have : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf _).map
        (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom (thickening X O' p)))) := h
    exact (SheafOfModules.toSheaf _).epi_of_epi_map inferInstance
  · intro U a ha x hx
    refine ⟨U, le_rfl, hx, 2, ?_⟩
    have hid : ((structureSheafRing (thickenedSpace X O')).obj.map
        (homOfLE (le_rfl (a := U))).op) a = a := by
      rw [show (homOfLE (le_rfl (a := U))).op = 𝟙 (op U) from rfl,
        CategoryTheory.Functor.map_id]
      rfl
    rw [hid, pow_two]
    exact hsq (op U) a a ha ha

/-- **`i : X ⟶ X'` is a first order thickening** under the same hypotheses: the square of the
kernel ideal over an open is generated by products of two sections killed by `p`, all of which
vanish. -/
theorem isFirstOrderThickening_thickening
    (hp : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier) p.hom)
    (hsq : ∀ (U : (Opens X.carrier)ᵒᵖ) (a b : O'.obj.obj U),
      p.hom.app U a = 0 → p.hom.app U b = 0 → a * b = 0) :
    IsFirstOrderThickening (thickening X O' p) := by
  refine ⟨isThickening_thickening X O' p hp hsq, fun U => ?_⟩
  rw [show (2 : ℕ) = 1 + 1 from rfl, Submodule.pow_succ, Submodule.pow_one]
  refine le_antisymm (Ideal.mul_le.2 ?_) bot_le
  intro r hr s hs
  rw [Ideal.mem_bot]
  exact hsq (op U) r s hr hs

end General

section Pushout

open Stacks.Sites.SqZeroPushout

variable (X : RingedSpace.{u, u})
  (R : Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u})
  (π : R ⟶ (X.sheaf : Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}))
  (N : SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology X.carrier)
    (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
  (ψ : PushoutData.{u} π N)

/-- The deformed ringed space `X'_ξ`: the space of `X` with the square-zero pushout
`(R ⋉ 𝒢)/J` as its structure sheaf. -/
noncomputable abbrev pushoutThickenedSpace : RingedSpace.{u, u} :=
  thickenedSpace X (pushoutSheaf.{u} π N ψ)

/-- The thickening `X ⟶ X'_ξ` presented by the square-zero pushout and its projection onto
`𝒪_X`. -/
noncomputable abbrev pushoutThickening : X ⟶ pushoutThickenedSpace X R π N ψ :=
  thickening X (pushoutSheaf.{u} π N ψ) (pushoutProj.{u} π N ψ)

/-- **The square-zero pushout presents a first order thickening of `X`.** Local surjectivity of
the projection is `Stacks.Sites.SqZeroPushout.isLocallySurjective_pushoutProj`, and the
square-zero condition is the exactness of the pushout: a local section killed by the projection
is `[(0, n)]` for a local section `n` of `𝒢` by
`Stacks.Sites.SqZeroPushout.pushoutProj_app_eq_zero_iff`, and two such multiply to zero by
`Stacks.Sites.SqZeroPushout.pushoutInr_mul_pushoutInr`. -/
theorem isFirstOrderThickening_pushoutThickening
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier) π.hom] :
    IsFirstOrderThickening (pushoutThickening X R π N ψ) := by
  refine isFirstOrderThickening_thickening X (pushoutSheaf.{u} π N ψ) (pushoutProj.{u} π N ψ)
    (isLocallySurjective_pushoutProj.{u} π N ψ) ?_
  intro U a b ha hb
  obtain ⟨n, rfl⟩ := (pushoutProj_app_eq_zero_iff π N ψ U a).1 ha
  obtain ⟨m, rfl⟩ := (pushoutProj_app_eq_zero_iff π N ψ U b).1 hb
  exact pushoutInr_mul_pushoutInr π N ψ U n m

end Pushout

end Stacks.Deformation.SqZeroThickening

end
