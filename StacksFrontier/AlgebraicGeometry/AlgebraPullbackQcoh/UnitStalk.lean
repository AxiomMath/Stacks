module

public import StacksFrontier.AlgebraicGeometry.PullbackTensorIso.StalkRingComparison
public import StacksFrontier.AlgebraicGeometry.RelativeSpecFinish.AlgebraStalk

/-!
# The stalk of the underlying module of an algebra sheaf

Let `A` be a sheaf of commutative `𝒪_X`-algebras on a scheme `X` and `t : X`.  Three stalks of
`A` at `t` are in play, each a colimit in a different category: the stalk in `CommRingCat`,
which is what `Stacks.AffineAlgebraEquivalence.stalkAlgebraPullbackIso` computes; the stalk in
`RingCat`, which is the ring `Mathlib`'s `AlgebraicGeometry.SheafOfModules.stalkFunctor` works
over; and the stalk of the underlying presheaf of abelian groups, which is the carrier of the
stalk of `Stacks.RelativeSpec.AlgebraSheaf.underlyingModule A`.

**This file identifies the first and the third, as `𝒪_{X,t}`-modules**: the stalk in
`CommRingCat`, viewed as a module over the `CommRingCat` stalk of the structure sheaf through
the stalk of the structure morphism of `A`, is the stalk of the underlying module with the
module structure of [Stacks, Tag 01CB].  The identification carries a germ to the germ of the
same section.

This is the comparison that `StacksFrontier/AlgebraicGeometry/AlgebraPullbackQcoh/Comparison.lean`
records as missing for the `algebraPullback_isQuasicoherent` clause of [Stacks, Tag 01SA], at
the generality the clause needs — an arbitrary algebra sheaf rather than a structure sheaf.

## Main definitions

* `Stacks.AlgebraPullbackQcoh.unitAbStalkIso`: for a presheaf of rings `R` on a space, the
  stalk of `R` in `RingCat` and the stalk of the underlying presheaf of abelian groups of
  `CategoryTheory.PresheafOfModules.unit R` are the same abelian group.
* `Stacks.AlgebraPullbackQcoh.algebraRingedSpace`: the ringed space whose space is `X` and
  whose structure sheaf is `A`.
* `Stacks.AlgebraPullbackQcoh.algebraStalkIso`, `algebraStalkAddEquiv`: **the comparison.**
* `Stacks.AlgebraPullbackQcoh.algebraStalkAlgebra`: the `𝒪_{X,t}`-algebra structure on the
  stalk of `A` in `CommRingCat`, given by the stalk of the structure morphism.
* `Stacks.AlgebraPullbackQcoh.algebraStalkLinearEquiv`: the comparison as an
  `𝒪_{X,t}`-linear equivalence.

## Main results

* `Stacks.AlgebraPullbackQcoh.unitAbStalkIso_hom_germ` and
  `Stacks.AlgebraPullbackQcoh.algebraStalkAddEquiv_germ`: the comparisons carry a germ to the
  germ of the same section.
* `Stacks.AlgebraPullbackQcoh.algebraStalkAddEquiv_smul`: **the two scalar actions agree.**
  Multiplication by the image of `r : 𝒪_{X,t}` under the stalk of the structure morphism
  corresponds to the action of [Stacks, Tag 01CB] of `r` on the stalk of the underlying
  module.

## Route

The whole of `StacksFrontier/AlgebraicGeometry/PullbackTensorIso/StalkRingComparison.lean`
applies here with **no generalisation**, because an algebra sheaf on `X` *is* the structure
sheaf of a ringed space: `algebraRingedSpace A` is `X` with `A` as its structure sheaf, and
`structureSheafRing (algebraRingedSpace A)` is
`Stacks.RelativeSpec.AlgebraSheaf.ringSheaf A` by `rfl`.  So
`Stacks.PullbackTensorIso.stalkRingIso` at that ringed space is the `CommRingCat`-versus-
`RingCat` comparison at `A`.

What is genuinely new is the second step, from `RingCat` to abelian groups.  It is
`CategoryTheory.Limits.preservesColimitIso` for `forget₂ RingCat AddCommGrpCat`, which
preserves filtered colimits; the underlying presheaf of abelian groups of
`CategoryTheory.PresheafOfModules.unit R` is the composite of `R` with that functor, so no
bridge is needed between the two diagrams.  `LocallyFreeRank.unitStalkLEquiv` is the same
comparison packaged as a linear equivalence;
it is not reused because its germ formula is internal to its proof.

The scalar agreement is the germ characterisation on both sides: the action of
[Stacks, Tag 01CB] is pinned by `germ (r • m) = germ r • germ m`, and `r • m` in the sections
of the underlying module of `A` is multiplication by the image of `r` under the structure
morphism, so both sides are the germ of `A.hom(r) * m`.

## What is not done

**No clause of [Stacks, Tag 01SA] is proved here, and no project tag attribute is attached.**
Tag 01SA is a single unqualified tag on a nine-field structure.  This file is one input
to the `algebraPullback_isQuasicoherent` clause, which is discharged in the sibling
`StacksFrontier/AlgebraicGeometry/AlgebraPullbackQcoh/Invertible.lean`; the remaining two
clauses of the tag, its base-change isomorphism and the identification of that isomorphism,
are open there and are not touched here.

Nothing here is specific to a quasi-coherent algebra: no quasi-coherence, affineness,
Noetherian, finiteness or flatness hypothesis occurs in this file.

## Transparency gotchas

* `Stacks.RelativeSpec.AlgebraSheaf.underlyingModule A` is a sheaf of modules over
  `AlgebraicGeometry.Scheme.ringCatSheaf`, and the module structure of [Stacks, Tag 01CB] on a
  stalk is stated over `structureSheafRing`.  The two
    sheaves of rings are equal
  by `rfl` but not at reducible transparency, so instance search does not find the module
  structure; `underlyingModuleSheaf` re-types the module over the second spelling, which is
  the remedy `StacksFrontier/AlgebraicGeometry/PullbackTensorIso/Basic.lean` uses for the same
  reason.
* The germ formula cannot be proved by rewriting with
  `Stacks.PullbackTensorIso.stalkRingIso_hom_germ`: the two germ spellings
  `(algebraRingedSpace A).presheaf.germ` and `A.right.obj.germ` are definitionally equal but
  the rewrite motive is not type-correct at implicit transparency.  The proof is a
  `congrArg`/`Eq.trans` chain instead.
* In the scalar lemma the image of a germ under the stalk of the structure morphism is written
  through the named accessor `algebraStalkMap`, whose declared type fixes the codomain to be
  `algebraStalk A t`.  Written as `(TopCat.Presheaf.stalkFunctor CommRingCat t).map A.hom.hom`
  directly, the codomain is a second spelling of the same object and the multiplication in the
  statement has no `HMul` instance.

## References

* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat

universe u

namespace Stacks.AlgebraPullbackQcoh

section Unit

variable {X : TopCat.{u}} (R : TopCat.Presheaf RingCat.{u} X) (x : X)

/-- **The stalk of a presheaf of rings, in `RingCat` and as an abelian group.**  The
forgetful functor `RingCat ⥤ AddCommGrpCat` preserves filtered colimits and a stalk is a
filtered colimit, so the stalk of `R` in `RingCat` is the stalk of the underlying presheaf of
abelian groups of `CategoryTheory.PresheafOfModules.unit R`, the presheaf of rings `R` viewed
as a module over itself. -/
def unitAbStalkIso : (forget₂ RingCat.{u} AddCommGrpCat.{u}).obj (R.stalk x) ≅
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (PresheafOfModules.unit R).presheaf x :=
  preservesColimitIso (forget₂ RingCat.{u} AddCommGrpCat.{u}) ((OpenNhds.inclusion x).op ⋙ R)

/-- `Stacks.AlgebraPullbackQcoh.unitAbStalkIso` carries a germ to the germ of the same
section.  This is `CategoryTheory.Limits.ι_preservesColimitIso_hom`, the germ maps being the
colimit inclusions. -/
lemma unitAbStalkIso_hom_germ (U : Opens X) (h : x ∈ U) (r : R.obj (op U)) :
    (unitAbStalkIso R x).hom.hom (TopCat.Presheaf.germ (C := RingCat.{u}) R U x h r) =
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (PresheafOfModules.unit R).presheaf U x h r :=
  ConcreteCategory.congr_hom
    (ι_preservesColimitIso_hom (forget₂ RingCat.{u} AddCommGrpCat.{u})
      ((OpenNhds.inclusion x).op ⋙ R) (op ⟨U, h⟩)) r

end Unit

section AlgebraSheaf

open Stacks.RelativeSpec

variable {X : Scheme.{u}} (A : AlgebraSheaf X) (t : X)

/-- **The scheme `X` with `A` as its structure sheaf**, as a ringed space.  An algebra sheaf is
a sheaf of commutative rings on a space, which is exactly the datum of a ringed space; this is
what makes the comparisons of
`StacksFrontier/AlgebraicGeometry/PullbackTensorIso/StalkRingComparison.lean` available at an
arbitrary algebra sheaf with no generalisation. -/
def algebraRingedSpace : RingedSpace.{u, u} :=
  { carrier := X.toTopCat, presheaf := A.right.obj, IsSheaf := A.right.property }

/-- The stalk at `t` of an algebra sheaf, taken in `CommRingCat`.  This is the spelling
`Stacks.AffineAlgebraEquivalence.stalkAlgebraPullbackIso` is stated over. -/
abbrev algebraStalk : CommRingCat.{u} :=
  (Stacks.AffineAlgebraEquivalence.stalkOnSheaf (T := X) t).obj A.right

/-- The stalk at `t` of the structure morphism `𝒪_X ⟶ A`, a ring homomorphism
`𝒪_{X,t} ⟶ A_t` between stalks taken in `CommRingCat`.  It is given a named accessor so that
its codomain is the spelling `algebraStalk A t`; see the transparency notes. -/
abbrev algebraStalkMap : Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X.toRingedSpace t ⟶
  algebraStalk A t :=
  (TopCat.Presheaf.stalkFunctor CommRingCat.{u} t).map A.hom.hom

/-- The underlying `𝒪_X`-module of an algebra sheaf, re-typed over the spelling
`structureSheafRing` of the structure sheaf of `X` as
  a sheaf of rings.  The two
spellings are the same sheaf of rings, but only this one lets instance search find the module
structure on a stalk. -/
abbrev underlyingModuleSheaf :
    SheafOfModules.{u} (structureSheafRing
      X.toRingedSpace) :=
  AlgebraSheaf.underlyingModule A

/-- The stalk at `t` of the underlying module of an algebra sheaf, as an abelian group: the
genuine Mathlib stalk of the underlying presheaf of abelian groups. -/
abbrev moduleAbStalk : AddCommGrpCat.{u} :=
  Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk X.toRingedSpace (underlyingModuleSheaf
    A).val t

/-- **The stalk of an algebra sheaf in `CommRingCat` is the stalk of its underlying module.**
The two forgetful functors `CommRingCat ⥤ RingCat` and `RingCat ⥤ AddCommGrpCat` both preserve
filtered colimits, so this is `Stacks.PullbackTensorIso.stalkRingIso` at the ringed space
`algebraRingedSpace A` followed by `unitAbStalkIso`. -/
def algebraStalkIso : (forget₂ RingCat.{u} AddCommGrpCat.{u}).obj
      ((forget₂ CommRingCat.{u} RingCat.{u}).obj (algebraStalk A t)) ≅ moduleAbStalk A t :=
  (forget₂ RingCat.{u} AddCommGrpCat.{u}).mapIso
      (Stacks.PullbackTensorIso.stalkRingIso (algebraRingedSpace A) t) ≪≫
    unitAbStalkIso (AlgebraSheaf.ringSheaf A).obj t

/-- `Stacks.AlgebraPullbackQcoh.algebraStalkIso` as an isomorphism of additive groups. -/
def algebraStalkAddEquiv : algebraStalk A t ≃+ moduleAbStalk A t :=
  (algebraStalkIso A t).addCommGroupIsoToAddEquiv

/-- **The comparison on germs.**  It carries the germ in `CommRingCat` of a section of `A` to
the germ of the same section in the underlying module. -/
lemma algebraStalkAddEquiv_germ (U : X.Opens) (h : t ∈ U) (a : A.right.obj.obj (op U)) :
    algebraStalkAddEquiv A t (TopCat.Presheaf.germ A.right.obj U t h a) =
      TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (underlyingModuleSheaf A).val.presheaf U t h a :=
  (congrArg (AddCommGrpCat.Hom.hom (unitAbStalkIso (AlgebraSheaf.ringSheaf A).obj t).hom)
      (Stacks.PullbackTensorIso.stalkRingIso_hom_germ (algebraRingedSpace A) t U h a)).trans
    (unitAbStalkIso_hom_germ (AlgebraSheaf.ringSheaf A).obj t U h a)

/-- **The two scalar actions agree.**  Multiplication in `A_t` by the image of `r : 𝒪_{X,t}`
under the stalk of the structure morphism corresponds, under the comparison, to the action of
[Stacks, Tag 01CB] of `r` on the stalk of the underlying module.

Both are pinned by their effect on germs: refining two germs to a common open neighbourhood,
the left side is the germ of `A.hom(r) * m` because the germ map is a ring homomorphism, and
the right side is the same because `r • m` in the sections of the underlying module *is*
`A.hom(r) * m`. -/
lemma algebraStalkAddEquiv_smul (r : Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk
  X.toRingedSpace t)
    (m : algebraStalk A t) :
    algebraStalkAddEquiv A t
        ((algebraStalkMap A t).hom r * m) =
      r • algebraStalkAddEquiv A t m := by
  obtain ⟨U, hU, r₀, hr⟩ := TopCat.Presheaf.exists_germ_eq X.toRingedSpace.presheaf r
  obtain ⟨V, hV, m₀, hm⟩ := TopCat.Presheaf.exists_germ_eq A.right.obj m
  have hW : t ∈ U ⊓ V := ⟨hU, hV⟩
  set r₁ := X.toRingedSpace.presheaf.map (homOfLE (inf_le_left (a := U) (b := V))).op r₀ with hr₁
  set m₁ := A.right.obj.map (homOfLE (inf_le_right (a := U) (b := V))).op m₀ with hm₁
  have hrW : TopCat.Presheaf.germ X.toRingedSpace.presheaf (U ⊓ V) t hW r₁ = r :=
    (TopCat.Presheaf.germ_res_apply X.toRingedSpace.presheaf (homOfLE inf_le_left) t hW r₀).trans hr
  have hmW : TopCat.Presheaf.germ A.right.obj (U ⊓ V) t hW m₁ = m :=
    (TopCat.Presheaf.germ_res_apply A.right.obj (homOfLE inf_le_right) t hW m₀).trans hm
  have key : (algebraStalkMap A t).hom
        (TopCat.Presheaf.germ X.toRingedSpace.presheaf (U ⊓ V) t hW r₁) =
      TopCat.Presheaf.germ A.right.obj (U ⊓ V) t hW (A.hom.hom.app (op (U ⊓ V)) r₁) :=
    TopCat.Presheaf.stalkFunctor_map_germ_apply (U ⊓ V) t hW A.hom.hom r₁
  have hmul : TopCat.Presheaf.germ A.right.obj (U ⊓ V) t hW
        (A.hom.hom.app (op (U ⊓ V)) r₁ * m₁) =
      TopCat.Presheaf.germ A.right.obj (U ⊓ V) t hW (A.hom.hom.app (op (U ⊓ V)) r₁) *
        TopCat.Presheaf.germ A.right.obj (U ⊓ V) t hW m₁ :=
    map_mul (TopCat.Presheaf.germ A.right.obj (U ⊓ V) t hW).hom _ _
  rw [← hrW, ← hmW, key]
  exact (congrArg (algebraStalkAddEquiv A t) hmul.symm).trans
    ((algebraStalkAddEquiv_germ A t (U ⊓ V) hW
          (A.hom.hom.app (op (U ⊓ V)) r₁ * m₁)).trans
      ((Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule_germ_smul X.toRingedSpace
        (underlyingModuleSheaf A).val t
            (U ⊓ V) hW r₁ m₁).trans
        (congrArg
          (fun y : moduleAbStalk A t =>
            TopCat.Presheaf.germ X.toRingedSpace.presheaf (U ⊓ V) t hW r₁ • y)
          (algebraStalkAddEquiv_germ A t (U ⊓ V) hW m₁).symm)))

/-- The `𝒪_{X,t}`-algebra structure on the stalk of `A` in `CommRingCat`, given by the stalk
of the structure morphism of `A`. -/
abbrev algebraStalkAlgebra : Algebra (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk
  X.toRingedSpace t)
    (algebraStalk A t) :=
  (algebraStalkMap A t).hom.toAlgebra

attribute [local instance] algebraStalkAlgebra

/-- **The comparison as an `𝒪_{X,t}`-linear equivalence**, by
`Stacks.AlgebraPullbackQcoh.algebraStalkAddEquiv_smul`. -/
def algebraStalkLinearEquiv :
    algebraStalk A t ≃ₗ[Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X.toRingedSpace t]
      moduleAbStalk A t :=
  AddEquiv.toLinearEquiv (algebraStalkAddEquiv A t) fun r m => algebraStalkAddEquiv_smul A t r m

/-- The underlying map of `algebraStalkLinearEquiv` is `algebraStalkAddEquiv`. -/
@[simp]
lemma algebraStalkLinearEquiv_apply (m : algebraStalk A t) :
    algebraStalkLinearEquiv A t m = algebraStalkAddEquiv A t m := rfl

/-- The inverse of the comparison carries the germ of a section in the underlying module to
its germ in `CommRingCat`. -/
lemma algebraStalkLinearEquiv_symm_germ (U : X.Opens) (h : t ∈ U)
    (a : A.right.obj.obj (op U)) :
    (algebraStalkLinearEquiv A t).symm
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (underlyingModuleSheaf A).val.presheaf U t h a) =
      TopCat.Presheaf.germ A.right.obj U t h a :=
  (algebraStalkLinearEquiv A t).symm_apply_eq.2 (algebraStalkAddEquiv_germ A t U h a).symm

end AlgebraSheaf

end Stacks.AlgebraPullbackQcoh

end
