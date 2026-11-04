module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceSection

/-!
# The two comorphisms agree on the functions read from the base, in inverse-image form

Let `Z ⊂ X` be a thickening of algebraic spaces over a scheme `S`, let `W₀ ⊆ W` be a closed
subspace of a second algebraic space, let `p : W ⟶ T` be a morphism to an **arbitrary** third
space and let `c, c' : X ⟶ W` be two morphisms with `c ≫ p = c' ≫ p` — when `T = X` and `p` is
a projection, two sections of `p` — whose restrictions to the thickening are one and the same
morphism `e₀ ≫ j`.

`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/LiftDifferenceSection.lean` proves that their
comorphisms read through the thickening agree after the **direct-image** form
`p^♯ : 𝒪_X ⟶ p_*𝒪_W` of the comorphism of `p`.  This file reads that agreement in the two
**inverse-image** forms the descent of
`StacksFrontier/AlgebraicGeometry/Spaces/LiftDifferenceDescent.lean` consumes:

* after `p^♯ : p^{-1}𝒪_X ⟶ 𝒪_W`, on the small étale site of `W`;
* after `j^{-1}(p^♯)`, on the small étale site of `W₀`, for the two transported comorphisms of
  `StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/LiftDifferenceRestrictedTarget.lean`.

Both readings are the same statement transposed along a ring-level adjunction `f^{-1} ⊣ f_*`,
which is a bijection; no full faithfulness and no comparison of iterated inverse images is used.
The second reading is what says that the descended difference of the two comorphisms kills the
functions read from the base, which is what makes it a derivation *over the base* and hence a
map out of the relative differentials.

## Main results

* `Stacks.Sheaves.ToposPushforward.comp_eq_of_ringUnit_comp_map_eq`: two morphisms out of an
  inverse image of a sheaf of rings agree as soon as their direct images agree after the unit.
* `AlgebraicGeometry.Space.structureSharp_comp_map_structureSharpThroughThickeningAt'` and
  `AlgebraicGeometry.Space.structureSharp_comp_map_structureSharpThroughThickeningAt_eq'`: the
  two direct-image statements of
  `StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/LiftDifferenceSection.lean` **at an
  arbitrary target `T` for `p`**, which that file states only for `T = X`.
* `structureSharpRingInverseImage_comp_structureSharpThroughThickeningAt_eq'`:
  **the two comorphisms agree after `p^♯ : p^{-1}𝒪_T ⟶ 𝒪_W`.**
* `inverseImage_structureSharpRingInverseImage_comp_restrictedSharpThroughThickening_eq'`:
  **the two transported comorphisms agree after `j^{-1}(p^♯)`.**
* `AlgebraicGeometry.Space.structureSharpRingInverseImage_comp_structureSharpThroughThickeningAt_eq`
  and
  `inverseImage_structureSharpRingInverseImage_comp_restrictedSharpThroughThickening_eq`:
  those two statements at `T = X`, where the target of `p` is the source of `c` and `c'`.

## Implementation notes

`LiftDifferenceSection.lean` states its two direct-image lemmas in the configuration of a
groupoid, where the target of `p` is the source `X` of `c` and `c'`.  Descending the difference
of two lifts of a morphism *over a base* needs them where the target is a third space, so the
primed variants above restate them there.  Nothing in either proof depends on the
identification: both rest on `AlgebraicGeometry.Space.structureSharpThroughThickening_comp`,
which `LiftDifferenceSection.lean` already proves for `f : X ⟶ W` and `g : W ⟶ V` with `V`
arbitrary.  When that file's `Section` namespace is itself generalized the primed names should
be removed in favour of the plain ones.

The two inverse-image statements are carried twice for the same reason, and the unprimed pair is
the one to keep byte-identical: it is the pair this file has always exported at `T = X`, and the
primed pair generalizes it.  Consumers that descend a lift over a base want the primed names;
the unprimed ones remain for the groupoid configuration.

## References

* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 0CKE](https://stacks.math.columbia.edu/tag/0CKE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace Stacks.Sheaves.ToposPushforward

universe ww vv uu vv' uu'

/-- **Two morphisms out of an inverse image of a sheaf of rings agree as soon as their direct
images agree after the unit of `f^{-1} ⊣ f_*`.**  The transpose along the ring-level adjunction
of a morphism out of `f^{-1}O` is the unit followed by the direct image, and transposition is a
bijection. -/
theorem comp_eq_of_ringUnit_comp_map_eq {Cc : Type uu} [Category.{vv} Cc]
    {Dd : Type uu'} [Category.{vv'} Dd]
    {Jc : GrothendieckTopology Cc} {Kc : GrothendieckTopology Dd}
    [Jc.HasSheafCompose (CategoryTheory.forget RingCat.{ww})]
    [Kc.HasSheafCompose (CategoryTheory.forget RingCat.{ww})]
    (f : MorphismOfTopoi (Sheaf Jc (Type ww)) (Sheaf Kc (Type ww)))
    (O : Sheaf Kc RingCat.{ww}) {T : Sheaf Jc RingCat.{ww}}
    {φ₁ φ₂ : inverseImageRingSheaf f O ⟶ T}
    (h : ringUnit f O ≫ (pushforwardRingFunctor f).map φ₁ =
      ringUnit f O ≫ (pushforwardRingFunctor f).map φ₂) :
    φ₁ = φ₂ :=
  ((ringImageAdjunction f).homEquiv O T).injective
    ((ringImageAdjunction_homEquiv_apply f O T φ₁).trans
      (h.trans (ringImageAdjunction_homEquiv_apply f O T φ₂).symm))

end Stacks.Sheaves.ToposPushforward

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X W : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)

-- The target of `p` in the primed, generalized statements of this file.  It is declared on its
-- own line so that the section's own variable block stays exactly as the unprimed statements --
-- the ones the base carries -- were written against.
variable {T : AlgebraicSpaces B S hS}

/-- Two members of a family of morphisms at equal indices agree after transport.  The same
helper is `private` in
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/LiftDifferenceSection.lean`, hence
inaccessible here. -/
private theorem family_congr_target {Cc : Type*} [Category Cc] {io : Type*} {A : Cc}
    (R : io → Cc) (F : ∀ k, A ⟶ R k) {k k' : io} (e : k = k') {D : Cc} (q : R k = D)
    (q' : R k' = D) : F k ≫ eqToHom q = F k' ≫ eqToHom q' := by
  cases e; rfl

/-- **The comorphism of `c : X ⟶ W`, read through the thickening and then along a morphism
`p : W ⟶ T` to an arbitrary target, is the comorphism of the composite `c ≫ p`.**

This is `AlgebraicGeometry.Space.structureSharp_comp_map_structureSharpThroughThickeningAt` with
the target of `p` freed from the source `X` of `c`: there the target of `p` is forced to be `X`,
which is the configuration of a groupoid, while the descent of a lift over a base needs a third
space.  The proof is word for word the same one, because the functoriality
`AlgebraicGeometry.Space.structureSharpThroughThickening_comp` it rests on is already stated at
an arbitrary target. -/
theorem structureSharp_comp_map_structureSharpThroughThickeningAt' (c : X ⟶ W) (p : W ⟶ T)
    (κ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = κ) :
    (structureSharp B S hS p ≫
        (pushforwardRingFunctor (smallToposMorphismTypeU B S hS p)).map
          (structureSharpThroughThickeningAt B S hS Z c κ h)) ≫
        pushforwardRingSheafCompHom B S hS κ p
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)) =
      structureSharpThroughThickeningAt B S hS Z (c ≫ p) (κ ≫ p)
        ((Category.assoc _ _ _).symm.trans (congrArg (fun m => m ≫ p) h)) := by
  cases h
  have e1 : structureSharpThroughThickeningAt B S hS Z c
        (subspaceInclusion B S hS X Z ≫ c) rfl =
      structureSharpThroughThickening B S hS Z c := Category.comp_id _
  have e2 : structureSharpThroughThickeningAt B S hS Z (c ≫ p)
        ((subspaceInclusion B S hS X Z ≫ c) ≫ p)
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun m => m ≫ p) (rfl : subspaceInclusion B S hS X Z ≫ c =
            subspaceInclusion B S hS X Z ≫ c))) =
      structureSharpThroughThickening B S hS Z (c ≫ p) := Category.comp_id _
  rw [e1]
  exact (Category.assoc _ _ _).trans
    ((structureSharpThroughThickening_comp B S hS Z c p).trans e2.symm)

/-- **Two morphisms agreeing on the thickening and agreeing after a morphism `p : W ⟶ T` to an
arbitrary target have the same comorphism read through the thickening**, after the comorphism of
`p`.

This is `AlgebraicGeometry.Space.structureSharp_comp_map_structureSharpThroughThickeningAt_eq`
with the target of `p` freed from the source `X` of `c` and `c'`.  Both sides, composed with the
invertible comparison of iterated direct images, are the comorphism of `c ≫ p` resp. `c' ≫ p`
read through the thickening, and those two indices are equal by `hcc`. -/
theorem structureSharp_comp_map_structureSharpThroughThickeningAt_eq' (c c' : X ⟶ W)
    (p : W ⟶ T) (κ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = κ)
    (h' : subspaceInclusion B S hS X Z ≫ c' = κ) (hcc : c ≫ p = c' ≫ p) :
    structureSharp B S hS p ≫
        (pushforwardRingFunctor (smallToposMorphismTypeU B S hS p)).map
          (structureSharpThroughThickeningAt B S hS Z c κ h) =
      structureSharp B S hS p ≫
        (pushforwardRingFunctor (smallToposMorphismTypeU B S hS p)).map
          (structureSharpThroughThickeningAt B S hS Z c' κ h') := by
  have hK := pushforwardRingSheafCompHom_comp_inv B S hS κ p
    (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))
  have hfam := family_congr_target
    (fun k : X ⟶ T => pullbackRingSheaf.{u, u, u, u + 1, u, u + 1}
      (SmallEtale.topology B S hS T.1)
      (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z ≫ k)).pushforward
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))
    (fun k => structureSharpThroughThickening B S hS Z k) hcc
    (congrArg (fun n : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ T =>
      pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS T.1)
        (smallToposMorphismTypeU B S hS n).pushforward
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))
      ((Category.assoc _ _ _).symm.trans (congrArg (fun m => m ≫ p) h)))
    (congrArg (fun n : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ T =>
      pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS T.1)
        (smallToposMorphismTypeU B S hS n).pushforward
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))
      ((Category.assoc _ _ _).symm.trans (congrArg (fun m => m ≫ p) h')))
  have hstep : (structureSharp B S hS p ≫
      (pushforwardRingFunctor (smallToposMorphismTypeU B S hS p)).map
        (structureSharpThroughThickeningAt B S hS Z c κ h)) ≫
      pushforwardRingSheafCompHom B S hS κ p
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)) =
    (structureSharp B S hS p ≫
      (pushforwardRingFunctor (smallToposMorphismTypeU B S hS p)).map
        (structureSharpThroughThickeningAt B S hS Z c' κ h')) ≫
      pushforwardRingSheafCompHom B S hS κ p
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)) := by
    rw [structureSharp_comp_map_structureSharpThroughThickeningAt',
      structureSharp_comp_map_structureSharpThroughThickeningAt']
    exact hfam
  exact cancel_right_of_comp_id _ _ _ _ hK hstep

/-- **The two comorphisms of two morphisms agreeing on the thickening and over `p` agree after
the inverse-image form `p^♯ : p^{-1}𝒪_T ⟶ 𝒪_W` of the comorphism of `p`.**

`AlgebraicGeometry.Space.structureSharp_comp_map_structureSharpThroughThickeningAt_eq'` is the
same equation after the direct-image form `p^♯ : 𝒪_T ⟶ p_*𝒪_W`, and the two forms are adjunct
by `AlgebraicGeometry.Space.ringUnit_comp_map_structureSharpRingInverseImage`; the transposition
along `p^{-1} ⊣ p_*` is a bijection, so the two readings are equivalent.

The target `T` of `p` is arbitrary — in particular it need not be the source `X` of `c` and
`c'`.  `structureSharpRingInverseImage_comp_structureSharpThroughThickeningAt_eq`
is the same statement at `T = X`. -/
theorem structureSharpRingInverseImage_comp_structureSharpThroughThickeningAt_eq'
    (c c' : X ⟶ W) (p : W ⟶ T)
    (κ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = κ)
    (h' : subspaceInclusion B S hS X Z ≫ c' = κ) (hcc : c ≫ p = c' ≫ p) :
    structureSharpRingInverseImage B S hS p ≫
        structureSharpThroughThickeningAt B S hS Z c κ h =
      structureSharpRingInverseImage B S hS p ≫
        structureSharpThroughThickeningAt B S hS Z c' κ h' := by
  have key : ∀ (d : X ⟶ W) (hd : subspaceInclusion B S hS X Z ≫ d = κ),
      ringUnit (smallToposMorphismTypeU B S hS p) (structureRingSheaf B S hS T) ≫
          (pushforwardRingFunctor (smallToposMorphismTypeU B S hS p)).map
            (structureSharpRingInverseImage B S hS p ≫
              structureSharpThroughThickeningAt B S hS Z d κ hd) =
        structureSharp B S hS p ≫
          (pushforwardRingFunctor (smallToposMorphismTypeU B S hS p)).map
            (structureSharpThroughThickeningAt B S hS Z d κ hd) := by
    intro d hd
    rw [(pushforwardRingFunctor (smallToposMorphismTypeU B S hS p)).map_comp
      (structureSharpRingInverseImage B S hS p)
      (structureSharpThroughThickeningAt B S hS Z d κ hd)]
    exact Eq.trans (Category.assoc _ _ _).symm
      (congrArg (fun m => m ≫ (pushforwardRingFunctor (smallToposMorphismTypeU B S hS p)).map
          (structureSharpThroughThickeningAt B S hS Z d κ hd))
        (ringUnit_comp_map_structureSharpRingInverseImage B S hS p))
  refine comp_eq_of_ringUnit_comp_map_eq (smallToposMorphismTypeU B S hS p)
    (structureRingSheaf B S hS T) ?_
  exact (key c h).trans
    ((structureSharp_comp_map_structureSharpThroughThickeningAt_eq' B S hS Z c c' p κ h h'
      hcc).trans (key c' h').symm)

/-- **The two comorphisms of two morphisms agreeing on the thickening and over `p` agree after
the inverse-image form `p^♯ : p^{-1}𝒪_X ⟶ 𝒪_W` of the comorphism of `p`.**

`AlgebraicGeometry.Space.structureSharp_comp_map_structureSharpThroughThickeningAt_eq` is the
same equation after the direct-image form `p^♯ : 𝒪_X ⟶ p_*𝒪_W`, and the two forms are adjunct
by `AlgebraicGeometry.Space.ringUnit_comp_map_structureSharpRingInverseImage`; the transposition
along `p^{-1} ⊣ p_*` is a bijection, so the two readings are equivalent. -/
theorem structureSharpRingInverseImage_comp_structureSharpThroughThickeningAt_eq
    (c c' : X ⟶ W) (p : W ⟶ X)
    (κ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = κ)
    (h' : subspaceInclusion B S hS X Z ≫ c' = κ) (hcc : c ≫ p = c' ≫ p) :
    structureSharpRingInverseImage B S hS p ≫
        structureSharpThroughThickeningAt B S hS Z c κ h =
      structureSharpRingInverseImage B S hS p ≫
        structureSharpThroughThickeningAt B S hS Z c' κ h' := by
  exact structureSharpRingInverseImage_comp_structureSharpThroughThickeningAt_eq' B S hS Z c c' p
    κ h h' hcc

variable (W₀ : ClosedSubspaces B S hS W.1)

/-- **The two transported comorphisms on the small étale site of `W₀` agree after
`j^{-1}(p^♯)`.**  The direct image of either side after the unit of `j^{-1} ⊣ j_*` is, by the
naturality of the unit and the defining adjunction identity
`AlgebraicGeometry.Space.ringUnit_comp_map_restrictedSharpThroughThickening`, the comorphism
read through the thickening precomposed with `p^♯ : p^{-1}𝒪_T ⟶ 𝒪_W`; those agree by
`AlgebraicGeometry.Space.structureSharpRingInverseImage_comp_structureSharpThroughThickeningAt_eq'`,
and transposition is a bijection.

This is what says that the descended difference of the two comorphisms kills the functions read
from the base `T` along `p`; `T` is arbitrary.
`inverseImage_structureSharpRingInverseImage_comp_restrictedSharpThroughThickening_eq`
is the same statement at `T = X`. -/
theorem inverseImage_structureSharpRingInverseImage_comp_restrictedSharpThroughThickening_eq'
    (c c' : X ⟶ W) (p : W ⟶ T)
    (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
    (h : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
    (h' : subspaceInclusion B S hS X Z ≫ c' = e₀ ≫ subspaceInclusion B S hS W W₀)
    (hcc : c ≫ p = c' ≫ p) :
    (inverseImageRingFunctor (smallToposMorphismTypeU B S hS
          (subspaceInclusion B S hS W W₀))).map
          (structureSharpRingInverseImage B S hS p) ≫
        restrictedSharpThroughThickening B S hS Z W₀ c e₀ h =
      (inverseImageRingFunctor (smallToposMorphismTypeU B S hS
          (subspaceInclusion B S hS W W₀))).map
          (structureSharpRingInverseImage B S hS p) ≫
        restrictedSharpThroughThickening B S hS Z W₀ c' e₀ h' := by
  have hnat : ringUnit (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀))
          (structureRingSheafInverseImage B S hS p) ≫
        (pushforwardRingFunctor (smallToposMorphismTypeU B S hS
          (subspaceInclusion B S hS W W₀))).map
          ((inverseImageRingFunctor (smallToposMorphismTypeU B S hS
            (subspaceInclusion B S hS W W₀))).map
            (structureSharpRingInverseImage B S hS p)) =
      structureSharpRingInverseImage B S hS p ≫
        ringUnit (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀))
          (structureRingSheaf B S hS W) :=
    ((ringUnitNatTrans (smallToposMorphismTypeU B S hS
      (subspaceInclusion B S hS W W₀))).naturality
      (structureSharpRingInverseImage B S hS p)).symm
  have key : ∀ (d : X ⟶ W)
      (hd : subspaceInclusion B S hS X Z ≫ d = e₀ ≫ subspaceInclusion B S hS W W₀),
      ringUnit (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀))
            (structureRingSheafInverseImage B S hS p) ≫
          (pushforwardRingFunctor (smallToposMorphismTypeU B S hS
            (subspaceInclusion B S hS W W₀))).map
            ((inverseImageRingFunctor (smallToposMorphismTypeU B S hS
                (subspaceInclusion B S hS W W₀))).map
                (structureSharpRingInverseImage B S hS p) ≫
              restrictedSharpThroughThickening B S hS Z W₀ d e₀ hd) =
        (structureSharpRingInverseImage B S hS p ≫
            structureSharpThroughThickeningAt B S hS Z d
              (e₀ ≫ subspaceInclusion B S hS W W₀) hd) ≫
          pushforwardRingSheafCompInv B S hS e₀ (subspaceInclusion B S hS W W₀)
            (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)) := by
    intro d hd
    refine Eq.trans (congrArg (fun m => ringUnit (smallToposMorphismTypeU B S hS
          (subspaceInclusion B S hS W W₀))
          (structureRingSheafInverseImage B S hS p) ≫ m)
      ((pushforwardRingFunctor (smallToposMorphismTypeU B S hS
        (subspaceInclusion B S hS W W₀))).map_comp _ _)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun m => m ≫
      (pushforwardRingFunctor (smallToposMorphismTypeU B S hS
        (subspaceInclusion B S hS W W₀))).map
        (restrictedSharpThroughThickening B S hS Z W₀ d e₀ hd)) hnat) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (fun m => structureSharpRingInverseImage B S hS p ≫ m)
      (ringUnit_comp_map_restrictedSharpThroughThickening B S hS Z W₀ d e₀ hd)) ?_
    exact (Category.assoc _ _ _).symm
  refine comp_eq_of_ringUnit_comp_map_eq (smallToposMorphismTypeU B S hS
    (subspaceInclusion B S hS W W₀)) (structureRingSheafInverseImage B S hS p) ?_
  refine (key c h).trans (Eq.trans ?_ (key c' h').symm)
  exact congrArg (fun m => m ≫ pushforwardRingSheafCompInv B S hS e₀
      (subspaceInclusion B S hS W W₀)
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))
    (structureSharpRingInverseImage_comp_structureSharpThroughThickeningAt_eq' B S hS Z c c' p
      (e₀ ≫ subspaceInclusion B S hS W W₀) h h' hcc)

/-- **The two transported comorphisms on the small étale site of `W₀` agree after
`j^{-1}(p^♯)`.**  The direct image of either side after the unit of `j^{-1} ⊣ j_*` is, by the
naturality of the unit and the defining adjunction identity
`AlgebraicGeometry.Space.ringUnit_comp_map_restrictedSharpThroughThickening`, the comorphism
read through the thickening precomposed with `p^♯ : p^{-1}𝒪_X ⟶ 𝒪_W`; those agree by
`AlgebraicGeometry.Space.structureSharpRingInverseImage_comp_structureSharpThroughThickeningAt_eq`,
and transposition is a bijection.

This is what says that the descended difference of the two comorphisms kills the functions read
from `X` along `p`. -/
theorem inverseImage_structureSharpRingInverseImage_comp_restrictedSharpThroughThickening_eq
    (c c' : X ⟶ W) (p : W ⟶ X)
    (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
    (h : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
    (h' : subspaceInclusion B S hS X Z ≫ c' = e₀ ≫ subspaceInclusion B S hS W W₀)
    (hcc : c ≫ p = c' ≫ p) :
    (inverseImageRingFunctor (smallToposMorphismTypeU B S hS
          (subspaceInclusion B S hS W W₀))).map
          (structureSharpRingInverseImage B S hS p) ≫
        restrictedSharpThroughThickening B S hS Z W₀ c e₀ h =
      (inverseImageRingFunctor (smallToposMorphismTypeU B S hS
          (subspaceInclusion B S hS W W₀))).map
          (structureSharpRingInverseImage B S hS p) ≫
        restrictedSharpThroughThickening B S hS Z W₀ c' e₀ h' := by
  exact inverseImage_structureSharpRingInverseImage_comp_restrictedSharpThroughThickening_eq'
    B S hS Z W₀ c c' p e₀ h h' hcc

end AlgebraicGeometry.Space

end
