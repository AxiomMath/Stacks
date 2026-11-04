module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SharpCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardAssoc
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceRestrictedData

/-!
# The comorphism of a section of a morphism, read through a thickening

Let `Z ⊂ X` be a thickening of algebraic spaces over a scheme `S`, with inclusion `i : Z ⟶ X`,
and let `c : X ⟶ W` be a morphism.
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/LiftDifferenceCommonTarget.lean` reads the
comorphism of `c` as a morphism of sheaves of rings

`𝒪_W ⟶ (i ≫ c)_*(i^{-1}𝒪_X)`

on the small étale site of `W`.  This file proves that that reading is **functorial**: composing
it with the comorphism of a further morphism `g : W ⟶ V`, and with the comparison of iterated
direct images, gives the same reading of the comorphism of the composite `c ≫ g`.

The consequence this file is written for is the case `g = p` with `c ≫ p = 𝟙_X`, that is `c` a
*section* of `p`: the composite then no longer depends on `c`, so **two sections of one and the
same morphism `p : W ⟶ X` whose restrictions to the thickening agree have the same comorphism
read through the thickening**, after the comorphism of `p`.  That is the geometric input of
[Stacks Project, Tag 0CKE]: there `p` is the source of a groupoid in algebraic spaces and the
two sections are two elements of `Γ₀`, and what it says on sections is that the two comorphisms
agree on the functions pulled back along the source — which are the generators of the defining
ideal of `R₀ = s^{-1}(U₀)` in `R`.

The file also records the derivation laws of the sectionwise difference of the two transported
comorphisms of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/LiftDifferenceRestrictedData.lean`, which hold
with no hypothesis on the kernel of `j^♯`.

## Main definitions

* `AlgebraicGeometry.Space.pushforwardRingSheafCompHom`: the comparison
  `g_*(f_*O) ⟶ (f ≫ g)_*O` of iterated direct images of a sheaf of rings, the inverse of
  `AlgebraicGeometry.Space.pushforwardRingSheafCompInv`.

## Main results

* `AlgebraicGeometry.Space.pushforwardRingSheafCompHom_comp_inv` and
  `AlgebraicGeometry.Space.pushforwardRingSheafCompInv_comp_hom`: the two comparisons of
  iterated direct images are mutually inverse.
* `AlgebraicGeometry.Space.structureSharpThroughThickening_comp`: **the comorphism read through
  a thickening is functorial.**  Its set-level form is
  `AlgebraicGeometry.Space.structureSharpThroughThickening_comp_set`, which is where the
  associativity cocycle law of [Stacks Project, Tag 03G2], part (3)
  (`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp_assoc`) and the composition law of
  [Stacks Project, Tag 03G8] on sheaves of sets
  (`AlgebraicGeometry.Space.structureSharpSet_comp`) are spent.
* `AlgebraicGeometry.Space.structureSharp_comp_map_structureSharpThroughThickeningAt`: the same,
  with the restriction to the thickening named, so that the two morphisms being compared below
  have one and the same target.
* `AlgebraicGeometry.Space.structureSharp_comp_map_structureSharpThroughThickeningAt_eq`:
  **two sections of one morphism which agree on the thickening have the same comorphism read
  through the thickening**, after the comorphism of the morphism they are sections of.
* `AlgebraicGeometry.Space.restrictedSharpDiff_add`,
  `AlgebraicGeometry.Space.restrictedSharpDiff_map`,
  `AlgebraicGeometry.Space.restrictedSharpDiff_mul` and
  `AlgebraicGeometry.Space.restrictedSharpDiff_eq_zero_iff`: the sectionwise difference of the
  two transported comorphisms is additive, commutes with restriction, obeys the Leibniz rule for
  the action through `j^♯`, and vanishes exactly where the two comorphisms agree.  These are
  `Stacks.Sites.diff_add_of_ι_diff` and its companions at the geometric data; they need no
  hypothesis on the kernel of `j^♯`, so they are available before hypothesis (2) of
  [Stacks Project, Tag 0618] is discharged.

## Implementation notes

**The functoriality is proved on underlying sheaves of sets.**  Both comparisons of iterated
direct images are the identity on underlying sheaves of sets in one factor and a component of
the comparison of transporting functors in the other, so the whole statement becomes an
equation between morphisms of sheaves of sets, which
`CategoryTheory.sheafCompose _ (CategoryTheory.forget RingCat)` reflects.  The set-level
equation is then a naturality chase, which is carried out at an **abstract site** — as
`comp_chase` — because the terms over the small étale ringed site exhaust the elaboration
budget as soon as a comparison is restated; the same precaution is taken for the three
`eqToHom` manipulations.

**Why `AlgebraicGeometry.Space.structureSharpThroughThickening_comp` is stated without an
`eqToHom`.**  Its two sides have `((i ≫ f) ≫ g)_*` and `(i ≫ (f ≫ g))_*` for their targets,
which are the same object; stating it that way keeps the proof free of transport, and the
`eqToHom` is introduced once, in
`AlgebraicGeometry.Space.structureSharp_comp_map_structureSharpThroughThickeningAt`, where the
restriction to the thickening is named.

**The `𝒪_{W₀}`-action on the sections of the ideal of values is seated by a `letI` naming the
canonical module structure `CategoryTheory.ModuleCat.isModule`**, rather than left to instance
search, in the statement of `AlgebraicGeometry.Space.restrictedSharpDiff_mul` — the only
statement here that spells a scalar action.  The sheaf of rings indexing the module is
`Stacks.SheafOfModules.Tensor.ringSheaf`, a plain `def`, so the `Semiring` and `AddCommMonoid`
arguments that search assembles for the goal at this spelling agree with the ones the section
module's own structure carries only after that `def` is unfolded, which instance search —
working at `instances` transparency — will not do, and the canonical candidate is rejected
during unification.  The bound value is term-identical to the canonical instance, so no second
module structure exists, and `letI` zeta-reduces, so the statement is the same one.  The same
`letI` is carried for the same reason by
`AlgebraicGeometry.Space.restrictedSquareZeroValues_ι_smul` of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/LiftDifferenceRestrictedData.lean`, whose
Leibniz hypothesis this statement consumes.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map and
  its compatibility with composition.
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2), part (3), the morphism
  of small étale topoi and the associativity of its composition isomorphism.
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618), the difference of two
  lifts.
* [Stacks Project, Tag 0CKE](https://stacks.math.columbia.edu/tag/0CKE), the tag this geometric
  input belongs to.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The comparison of iterated direct images is invertible -/

section PushforwardComp

variable {V₁ V₂ V₃ : AlgebraicSpaces B S hS}

/-- Cancelling a composite against the composite of the two inverses. -/
private theorem comp_four_cancel {Cc : Type*} [Category Cc] {A Bb Dd : Cc} (a : A ⟶ Bb)
    (b : Bb ⟶ Dd) (b' : Dd ⟶ Bb) (a' : Bb ⟶ A) (hb : b ≫ b' = 𝟙 Bb) (ha : a ≫ a' = 𝟙 A) :
    (a ≫ b) ≫ b' ≫ a' = 𝟙 A := by
  rw [Category.assoc, ← Category.assoc b, hb, Category.id_comp, ha]

/-- **The comparison of iterated direct images of a sheaf of rings**, in the direction
`g_*(f_*O) ⟶ (f ≫ g)_*O`: the inverse of
`AlgebraicGeometry.Space.pushforwardRingSheafCompInv`. -/
noncomputable def pushforwardRingSheafCompHom (f : V₁ ⟶ V₂) (g : V₂ ⟶ V₃)
    (O : Sheaf (SmallEtale.topology B S hS V₁.1) RingCat.{u}) :
    pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS V₃.1)
        (smallToposMorphismTypeU B S hS g).pushforward
        (pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS V₂.1)
          (smallToposMorphismTypeU B S hS f).pushforward O) ⟶
      pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS V₃.1)
        (smallToposMorphismTypeU B S hS (f ≫ g)).pushforward O :=
  (pullbackRingSheafComp (SmallEtale.topology B S hS V₂.1)
      (SmallEtale.topology B S hS V₃.1) (smallToposMorphismTypeU B S hS f).pushforward
      (smallToposMorphismTypeU B S hS g).pushforward O).hom ≫
    pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS V₃.1) O
      (smallToposMorphismTypeU_comp B S hS f g).hom

/-- The two comparisons of iterated direct images are mutually inverse. -/
theorem pushforwardRingSheafCompHom_comp_inv (f : V₁ ⟶ V₂) (g : V₂ ⟶ V₃)
    (O : Sheaf (SmallEtale.topology B S hS V₁.1) RingCat.{u}) :
    pushforwardRingSheafCompHom B S hS f g O ≫ pushforwardRingSheafCompInv B S hS f g O =
      𝟙 _ :=
  comp_four_cancel _ _ _ _
    (pullbackRingSheafMapOfNatTrans_hom_inv_id (SmallEtale.topology B S hS V₃.1) O
      (smallToposMorphismTypeU_comp B S hS f g))
    (pullbackRingSheafComp (SmallEtale.topology B S hS V₂.1)
      (SmallEtale.topology B S hS V₃.1) (smallToposMorphismTypeU B S hS f).pushforward
      (smallToposMorphismTypeU B S hS g).pushforward O).hom_inv_id

/-- The two comparisons of iterated direct images are mutually inverse. -/
theorem pushforwardRingSheafCompInv_comp_hom (f : V₁ ⟶ V₂) (g : V₂ ⟶ V₃)
    (O : Sheaf (SmallEtale.topology B S hS V₁.1) RingCat.{u}) :
    pushforwardRingSheafCompInv B S hS f g O ≫ pushforwardRingSheafCompHom B S hS f g O =
      𝟙 _ :=
  comp_four_cancel _ _ _ _
    (pullbackRingSheafComp (SmallEtale.topology B S hS V₂.1)
      (SmallEtale.topology B S hS V₃.1) (smallToposMorphismTypeU B S hS f).pushforward
      (smallToposMorphismTypeU B S hS g).pushforward O).inv_hom_id
    (pullbackRingSheafMapOfNatTrans_hom_inv_id (SmallEtale.topology B S hS V₃.1) O
      (smallToposMorphismTypeU_comp B S hS f g).symm)

end PushforwardComp

/-! ### Functoriality of the comorphism read through a thickening -/

section Functorial

variable {X W V : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)

/-- The sheaf of sets underlying `i^{-1}𝒪_X`. -/
abbrev thickeningInverseImageSetSheaf : Sheaf (SmallEtale.topology B S hS
    (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1) (Type u) :=
  (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).inverseImage.obj
    (structureSetSheaf B S hS X)

/-- The comorphism read through the thickening, on underlying sheaves of sets. -/
theorem sheafCompose_map_structureSharpThroughThickening (f : X ⟶ W) :
    (sheafCompose (SmallEtale.topology B S hS W.1)
          (CategoryTheory.forget RingCat.{u})).map
        (structureSharpThroughThickening B S hS Z f) =
      structureSharpSet B S hS f ≫
        (smallToposMorphismTypeU B S hS f).pushforward.map
          ((smallToposMorphismTypeU B S hS
            (subspaceInclusion B S hS X Z)).adj.unit.app
            (structureSetSheaf B S hS X)) ≫
        (smallToposMorphismTypeU_comp B S hS
            (subspaceInclusion B S hS X Z) f).hom.app
          (thickeningInverseImageSetSheaf B S hS Z) :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

/-- The naturality chase behind
`AlgebraicGeometry.Space.structureSharpThroughThickening_comp`, at an abstract site. -/
private theorem comp_chase {Zc Xc Wc Vc : Type*} [Category Zc] [Category Xc] [Category Wc]
    [Category Vc] (Pi : Zc ⥤ Xc) (Pf : Xc ⥤ Wc) (Pg : Wc ⥤ Vc) (Pk : Zc ⥤ Wc)
    (Pfg : Xc ⥤ Vc) (Pl : Zc ⥤ Vc) (Nif : Pi ⋙ Pf ⟶ Pk) (Nkg : Pk ⋙ Pg ⟶ Pl)
    (Nfg : Pf ⋙ Pg ⟶ Pfg) (Nifg : Pi ⋙ Pfg ⟶ Pl) {OX : Xc} {OW : Wc} {OV : Vc} {L : Zc}
    (sf : OW ⟶ Pf.obj OX) (sg : OV ⟶ Pg.obj OW) (sfg : OV ⟶ Pfg.obj OX)
    (u : OX ⟶ Pi.obj L)
    (hassoc : Pg.map (Nif.app L) ≫ Nkg.app L = Nfg.app (Pi.obj L) ≫ Nifg.app L)
    (hcomp : sg ≫ Pg.map sf ≫ Nfg.app OX = sfg) :
    sg ≫ Pg.map (sf ≫ Pf.map u ≫ Nif.app L) ≫ Nkg.app L =
      sfg ≫ Pfg.map u ≫ Nifg.app L := by
  have hnat : Pg.map (Pf.map u) ≫ Nfg.app (Pi.obj L) = Nfg.app OX ≫ Pfg.map u :=
    Nfg.naturality u
  rw [← hcomp, Pg.map_comp, Pg.map_comp]
  simp only [Category.assoc]
  rw [hassoc, ← Category.assoc (Pg.map (Pf.map u)), hnat]
  simp only [Category.assoc]

/-- **Functoriality of the comorphism read through a thickening**, on underlying sheaves of
sets. -/
theorem structureSharpThroughThickening_comp_set (f : X ⟶ W) (g : W ⟶ V) :
    structureSharpSet B S hS g ≫
        (smallToposMorphismTypeU B S hS g).pushforward.map
          ((sheafCompose (SmallEtale.topology B S hS W.1)
            (CategoryTheory.forget RingCat.{u})).map
            (structureSharpThroughThickening B S hS Z f)) ≫
        (smallToposMorphismTypeU_comp B S hS
            (subspaceInclusion B S hS X Z ≫ f) g).hom.app
          (thickeningInverseImageSetSheaf B S hS Z) =
      (sheafCompose (SmallEtale.topology B S hS V.1)
          (CategoryTheory.forget RingCat.{u})).map
        (structureSharpThroughThickening B S hS Z (f ≫ g)) := by
  rw [sheafCompose_map_structureSharpThroughThickening,
    sheafCompose_map_structureSharpThroughThickening]
  exact comp_chase _ _ _ _ _ _
    (smallToposMorphismTypeU_comp B S hS (subspaceInclusion B S hS X Z) f).hom
    (smallToposMorphismTypeU_comp B S hS (subspaceInclusion B S hS X Z ≫ f) g).hom
    (smallToposMorphismTypeU_comp B S hS f g).hom
    (smallToposMorphismTypeU_comp B S hS (subspaceInclusion B S hS X Z) (f ≫ g)).hom
    (structureSharpSet B S hS f) (structureSharpSet B S hS g)
    (structureSharpSet B S hS (f ≫ g))
    ((smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).adj.unit.app
      (structureSetSheaf B S hS X))
    (smallToposMorphismTypeU_comp_assoc B S hS (subspaceInclusion B S hS X Z) f g
      (thickeningInverseImageSetSheaf B S hS Z))
    (structureSharpSet_comp B S hS f g)

/-- **Functoriality of the comorphism read through a thickening.** -/
theorem structureSharpThroughThickening_comp (f : X ⟶ W) (g : W ⟶ V) :
    structureSharp B S hS g ≫
        (pushforwardRingFunctor (smallToposMorphismTypeU B S hS g)).map
          (structureSharpThroughThickening B S hS Z f) ≫
        pushforwardRingSheafCompHom B S hS (subspaceInclusion B S hS X Z ≫ f) g
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)) =
      structureSharpThroughThickening B S hS Z (f ≫ g) := by
  refine (sheafCompose (SmallEtale.topology B S hS V.1)
    (CategoryTheory.forget RingCat.{u})).map_injective ?_
  simp only [pushforwardRingSheafCompHom, Functor.map_comp, pullbackRingSheafFunctor_map]
  exact structureSharpThroughThickening_comp_set B S hS Z f g

/-- **Functoriality of the comorphism read through a thickening**, with the restriction to the
thickening named. -/
theorem structureSharpThroughThickening_comp_at (f : X ⟶ W) (g : W ⟶ V) :
    structureSharp B S hS g ≫
        (pushforwardRingFunctor (smallToposMorphismTypeU B S hS g)).map
          (structureSharpThroughThickening B S hS Z f) ≫
        pushforwardRingSheafCompHom B S hS (subspaceInclusion B S hS X Z ≫ f) g
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)) =
      structureSharpThroughThickeningAt B S hS Z (f ≫ g)
        ((subspaceInclusion B S hS X Z ≫ f) ≫ g) (Category.assoc _ _ _).symm :=
  (structureSharpThroughThickening_comp B S hS Z f g).trans (Category.comp_id _).symm

end Functorial

/-! ### Two sections of one morphism -/

section Section

variable {X W : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)

/-- Sliding an `eqToHom` out of a direct image and across the comparison. -/
private theorem slide_eqToHom (Cc Dd : Type*) [Category Cc] [Category Dd] (F : Cc ⥤ Dd)
    (io : Type*) (Q : io → Cc) (Qp : io → Dd) (K : ∀ k, F.obj (Q k) ⟶ Qp k)
    {A : Cc} {m k : io} (t : A ⟶ Q m) (e : m = k) :
    F.map (t ≫ eqToHom (congrArg Q e)) ≫ K k =
      F.map t ≫ K m ≫ eqToHom (congrArg Qp e) := by
  cases e; simp

/-- Two `eqToHom`s compose to one. -/
private theorem comp_eqToHom_eqToHom {Cc : Type*} [Category Cc] {io : Type*} (Q : io → Cc)
    {A : Cc} {a b d : io} (t : A ⟶ Q a) (e : a = b) (e' : b = d) :
    (t ≫ eqToHom (congrArg Q e)) ≫ eqToHom (congrArg Q e') =
      t ≫ eqToHom (congrArg Q (e.trans e')) := by
  cases e; cases e'; simp

/-- Two members of a family of morphisms at equal indices agree after transport. -/
private theorem family_congr {Cc : Type*} [Category Cc] {io : Type*} {A : Cc} (R : io → Cc)
    (T : ∀ k, A ⟶ R k) {k k' : io} (e : k = k') {D : Cc} (p : R k = D) (p' : R k' = D) :
    T k ≫ eqToHom p = T k' ≫ eqToHom p' := by
  cases e; rfl

/-- **The comorphism of a morphism `c : X ⟶ W`, read through the thickening and then along a
morphism `p : W ⟶ X`, is the comorphism of the composite `c ≫ p`.** -/
theorem structureSharp_comp_map_structureSharpThroughThickeningAt (c : X ⟶ W) (p : W ⟶ X)
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
  rw [e1]
  exact (Category.assoc _ _ _).trans (structureSharpThroughThickening_comp_at B S hS Z c p)

/-- **Two sections of one morphism which agree on the thickening have the same comorphism read
through the thickening**, after the comorphism of the morphism they are sections of. -/
theorem structureSharp_comp_map_structureSharpThroughThickeningAt_eq (c c' : X ⟶ W)
    (p : W ⟶ X) (κ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = κ)
    (h' : subspaceInclusion B S hS X Z ≫ c' = κ) (hcc : c ≫ p = c' ≫ p) :
    structureSharp B S hS p ≫
        (pushforwardRingFunctor (smallToposMorphismTypeU B S hS p)).map
          (structureSharpThroughThickeningAt B S hS Z c κ h) =
      structureSharp B S hS p ≫
        (pushforwardRingFunctor (smallToposMorphismTypeU B S hS p)).map
          (structureSharpThroughThickeningAt B S hS Z c' κ h') := by
  refine cancel_right_of_comp_id _ _ _ _
    (pushforwardRingSheafCompHom_comp_inv B S hS κ p
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))) ?_
  rw [structureSharp_comp_map_structureSharpThroughThickeningAt,
    structureSharp_comp_map_structureSharpThroughThickeningAt]
  let F := fun n : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ X =>
    pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS X.1)
      (smallToposMorphismTypeU B S hS n).pushforward
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))
  exact family_congr (fun k : X ⟶ X => F (subspaceInclusion B S hS X Z ≫ k))
    (fun k => structureSharpThroughThickening B S hS Z k) hcc
    (congrArg F ((Category.assoc _ _ _).symm.trans (congrArg (fun m => m ≫ p) h)))
    (congrArg F ((Category.assoc _ _ _).symm.trans (congrArg (fun m => m ≫ p) h')))

end Section

/-! ### The sectionwise difference of the two transported comorphisms is a derivation -/

section Derivation

variable {X W : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (W₀ : ClosedSubspaces B S hS W.1)
  (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
  (hZ : IsFirstOrderThickening B S hS X Z.1) (c c' : X ⟶ W)
  (h : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
  (h' : subspaceInclusion B S hS X Z ≫ c' = e₀ ≫ subspaceInclusion B S hS W W₀)

include hZ

/-- **The sectionwise difference of the two transported comorphisms is additive.** -/
theorem restrictedSharpDiff_add
    {V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ}
    (x y : (structureRingSheafInverseImage B S hS
      (subspaceInclusion B S hS W W₀)).obj.obj V) :
    restrictedSharpDiff B S hS Z W₀ e₀ hZ c c' h h' (x + y) =
      restrictedSharpDiff B S hS Z W₀ e₀ hZ c c' h h' x +
        restrictedSharpDiff B S hS Z W₀ e₀ hZ c c' h h' y :=
  Stacks.Sites.diff_add_of_ι_diff (restrictedSquareZeroValues B S hS Z W₀ e₀ hZ)
    (restrictedSharpThroughThickening B S hS Z W₀ c e₀ h)
    (restrictedSharpThroughThickening B S hS Z W₀ c' e₀ h')
    (fun {_V} y => restrictedSharpDiff B S hS Z W₀ e₀ hZ c c' h h' y)
    (fun {_V} y =>
      restrictedSquareZeroValues_ι_restrictedSharpDiff B S hS Z W₀ e₀ hZ c c' h h' y) x y

/-- **The sectionwise difference of the two transported comorphisms commutes with
restriction.** -/
theorem restrictedSharpDiff_map
    {V W' : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ}
    (k : V ⟶ W')
    (x : (structureRingSheafInverseImage B S hS
      (subspaceInclusion B S hS W W₀)).obj.obj V) :
    restrictedSharpDiff B S hS Z W₀ e₀ hZ c c' h h'
        ((structureRingSheafInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).obj.map k x) =
      ((modulePushforward B S hS e₀).obj (conormalModule B S hS X Z)).val.map k
        (restrictedSharpDiff B S hS Z W₀ e₀ hZ c c' h h' x) :=
  Stacks.Sites.diff_map_of_ι_diff (restrictedSquareZeroValues B S hS Z W₀ e₀ hZ)
    (restrictedSharpThroughThickening B S hS Z W₀ c e₀ h)
    (restrictedSharpThroughThickening B S hS Z W₀ c' e₀ h')
    (fun {_V} y => restrictedSharpDiff B S hS Z W₀ e₀ hZ c c' h h' y)
    (fun {_V} y =>
      restrictedSquareZeroValues_ι_restrictedSharpDiff B S hS Z W₀ e₀ hZ c c' h h' y) k x

/-- **The Leibniz rule for the sectionwise difference of the two transported comorphisms**, for
the `𝒪_{W₀}`-action through `j^♯` and the transported comorphism of `c`.  This is where the
square-zero property of the ideal of values is spent. -/
theorem restrictedSharpDiff_mul
    {V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ}
    (x y : (structureRingSheafInverseImage B S hS
      (subspaceInclusion B S hS W W₀)).obj.obj V) :
    letI : Module ((structureRingSheaf B S hS
          (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS)).obj.obj V)
        (((modulePushforward B S hS e₀).obj (conormalModule B S hS X Z)).val.obj V) :=
      (((modulePushforward B S hS e₀).obj (conormalModule B S hS X Z)).val.obj V).isModule
    restrictedSharpDiff B S hS Z W₀ e₀ hZ c c' h h' (x * y) =
      (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).hom.app V x •
          restrictedSharpDiff B S hS Z W₀ e₀ hZ c c' h h' y +
        (structureSharpRingInverseImage B S hS
            (subspaceInclusion B S hS W W₀)).hom.app V y •
          restrictedSharpDiff B S hS Z W₀ e₀ hZ c c' h h' x :=
  Stacks.Sites.diff_mul_of_ι_diff (restrictedSquareZeroValues B S hS Z W₀ e₀ hZ)
    (restrictedSharpThroughThickening B S hS Z W₀ c e₀ h)
    (restrictedSharpThroughThickening B S hS Z W₀ c' e₀ h')
    (fun {_V} y => restrictedSharpDiff B S hS Z W₀ e₀ hZ c c' h h' y)
    (fun {_V} y =>
      restrictedSquareZeroValues_ι_restrictedSharpDiff B S hS Z W₀ e₀ hZ c c' h h' y)
    (fun {_V} y m => restrictedSquareZeroValues_ι_smul B S hS Z W₀ e₀ hZ c h y m) x y

/-- **The sectionwise difference vanishes exactly where the two transported comorphisms
agree.** -/
theorem restrictedSharpDiff_eq_zero_iff
    {V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ}
    (x : (structureRingSheafInverseImage B S hS
      (subspaceInclusion B S hS W W₀)).obj.obj V) :
    restrictedSharpDiff B S hS Z W₀ e₀ hZ c c' h h' x = 0 ↔
      (restrictedSharpThroughThickening B S hS Z W₀ c e₀ h).hom.app V x =
        (restrictedSharpThroughThickening B S hS Z W₀ c' e₀ h').hom.app V x :=
  Stacks.Sites.diff_eq_zero_iff_of_ι_diff (restrictedSquareZeroValues B S hS Z W₀ e₀ hZ)
    (restrictedSharpThroughThickening B S hS Z W₀ c e₀ h)
    (restrictedSharpThroughThickening B S hS Z W₀ c' e₀ h')
    (fun {_V} y => restrictedSharpDiff B S hS Z W₀ e₀ hZ c c' h h' y)
    (fun {_V} y =>
      restrictedSquareZeroValues_ι_restrictedSharpDiff B S hS Z W₀ e₀ hZ c c' h h' y) x

end Derivation

end AlgebraicGeometry.Space

end
