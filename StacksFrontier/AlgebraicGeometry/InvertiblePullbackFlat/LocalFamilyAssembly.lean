module

public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.ChartSaturation
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.PullbackMeromorphicFamily

/-!
# The family of Tag 0BD7 built on arbitrary opens, assembled onto preimages

`Stacks.InvertiblePullback.IsPullMeromorphicFamily` asks that the regular section `t i`
representing `φ^*(g_i) s` be defined on the whole preimage `φ^{-1}(A i)`. The penultimate
paragraph of [Stacks, Tag 0BD7] cannot produce that directly: a preimage contains whole fibres,
and that `φ^*(g) s` is regular along a whole fibre is the *conclusion* of the last paragraph's
saturation argument, not an input to it. What the local argument at a point `x` of `X` gives is
a section on some open `V ∋ x` of `X` contained in `φ^{-1}(A)`, and nothing more.

This file closes that gap. `Stacks.InvertiblePullback.IsPullMeromorphicFamilyOn` is the family
with each `t i` on an arbitrary open `V i ≤ φ^{-1}(A i)`, and
`Stacks.InvertiblePullback.exists_isPullMeromorphicFamily_of_isPullMeromorphicFamilyOn` turns
such a family, with the saturation inputs of
`StacksFrontier/AlgebraicGeometry/InvertiblePullbackFlat/ChartSaturation.lean`, into a genuine
family on preimages together with its generating property. The chart of that file is what makes
this possible: `φ^{-1}(chart y)` *is* the generating locus of one member, so it already sits
inside that member's open `V i`, and restricting the member to it lands on a preimage.

## Main definitions

* `Stacks.InvertiblePullback.IsPullMeromorphicFamilyOn`: `φ^*(g_i) s = t i` on an open `V i` of
  `φ^{-1}(A i)`, rather than on `φ^{-1}(A i)` itself.
* `Stacks.InvertiblePullback.IsMaximalPullMeromorphicFamilyOn`: `V i` is the largest open of
  `φ^{-1}(A i)` on which `φ^*(g_i) s` is regular.

## Main results

* `Stacks.InvertiblePullback.isPullMeromorphicFamilyOn_preimage`: on the preimages themselves
  the new predicate is `Stacks.InvertiblePullback.IsPullMeromorphicFamily`, so it is a
  generalisation and not a second encoding of the same notion.
* `Stacks.InvertiblePullback.exists_isPullMeromorphicFamily_of_isPullMeromorphicFamilyOn`: the
  assembly. Both conjuncts owed by the hypothesis `hfam` of
  `Stacks.InvertiblePullback`'s
  `exists_isInvertible_pullback_iso_of_isTrivial_genericFiber_of_named_section` come out of it,
  with the family re-indexed by the points of the base.

## Implementation notes

The tag is **withheld**. The hypotheses here are the family on arbitrary opens together with
`hex` and `hagree`, none of which Tag 0BD7 states. The family is produced in
`StacksFrontier/AlgebraicGeometry/InvertiblePullbackFlat/LocalFamilyCover.lean` and `hagree` is
discharged, from the maximality clause below, in
`StacksFrontier/AlgebraicGeometry/InvertiblePullbackFlat/LocalFamilyAgreement.lean`.

Whatever produces it must **choose** the generator `m` of the generic stalk, not receive it.
`hfam` of
`Stacks.InvertiblePullback`'s
`exists_isInvertible_pullback_iso_of_isTrivial_genericFiber_of_named_section` has `∃ m, …` as
its hypothesis and rebinds `m` in its conclusion, and that is not a slip: the local statement
with `m` universally quantified is false. Take `Y = Spec k[y]`, `X = Spec k[y, z]`, `φ` the
projection, `ℒ = 𝒪_X`, and `m` the germ of `z` at the generic point. Every hypothesis of the
tag holds and `K(X)` is a field, so `m` generates; but at the origin `x` a meromorphic `q = a/b`
on the base with `φ^*(q) s` regular and generating at `x` would give `a z = b t` in the
factorial local ring `𝒪_{X, x}` with `a, b ∈ k[y]` and `t` a unit there, and `z` is prime and
does not divide `b`, so `z ∣ t`. The generator the source does produce is the one
`AlgebraicGeometry.eq_smul_grpGerm_genericFiberTrivGenerator` names, which depends on the
trivialization of the generic fibre and on no affine chart; a local statement about it has to
read `∃ m, Submodule.span _ {m} = ⊤ ∧ ∀ x, …`.

The re-indexed family is indexed by `Y`, not by the original `ι`: the chart is a function of a
point of the base, and the member of the original family that it comes from is chosen by
`exists_chart_coe_preimage_eq_generatingLocus`. Its generating property is read off at
`y = φ(z)`, where `z` lies in `φ^{-1}(chart (φ z))` because `φ z ∈ chart (φ z)`.

That `chart y ≤ A (idx y)` is not part of the chart's conclusion and is recovered from
surjectivity of `φ`, which hypothesis (3) of the tag supplies through
`AlgebraicGeometry.Surjective.of_nonempty_fiber`: a point of `chart y` is the image of a point
of `φ^{-1}(chart y)`, which lies in `V (idx y)` and hence in `φ^{-1}(A (idx y))`.

`PresheafOfModules.naturality_apply` is given its morphism explicitly in the last step. Left to
unification it fails: the expected type spells the restriction with
`PresheafOfModules.restrictₛₗ` while the lemma spells it with `PresheafOfModules.map`, and with
the morphism a metavariable there is nothing to drive the unfolding.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Meromorphic Stacks.SheafOfModules

universe u

namespace Stacks.InvertiblePullback

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (L : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (s : MeromorphicSection X.sheaf L)
    {ι : Type*} {A : ι → Y.Opens} {V : ι → Opens X.toRingedSpace.carrier}
    (hVA : ∀ i, (V i : X.Opens) ≤ (f ⁻¹ᵁ A i : X.Opens))
    (g : ∀ i, (totalQuotientSheafAsModule Y).val.obj (op (A i)))
    (t : ∀ i, L.val.obj (op (V i)))

/-- **The family `φ^*(g_i) s` of [Stacks, Tag 0BD7] on arbitrary opens.** As
`Stacks.InvertiblePullback.IsPullMeromorphicFamily`, except that `t i` is a regular section of
`ℒ` on an open `V i` of `φ^{-1}(A i)` and the equation is the restricted one. -/
def IsPullMeromorphicFamilyOn : Prop :=
  ∀ i, (meromorphicSectionSheafAsModule X L).val.restrictₛₗ (homOfLE (hVA i)).op
        ((pullbackMeromorphicMul f L s).val.app (op (A i)) (g i))
    = (toMeromorphicSectionSheafAsModule X L).val.app (op (V i)) (t i)

/-- **The opens of the family are as large as they can be.** Every open of `φ^{-1}(A i)` on which
`φ^*(g_i) s` is a regular section is contained in `V i`, with that section the restriction of
`t i`. This is the clause that makes the agreement hypothesis `hagree` of
`Stacks.InvertiblePullback.exists_isPullMeromorphicFamily_of_isPullMeromorphicFamilyOn`
derivable: without it `V i` can be any open on which the product happens to be regular, and then
`hagree` is false.

The containment `hVA` of `Stacks.InvertiblePullback.IsPullMeromorphicFamilyOn` is not an argument
here: it is a consequence, since `V i` is one of the opens the clause quantifies over. -/
def IsMaximalPullMeromorphicFamilyOn : Prop :=
  ∀ (i : ι) (W : Opens X.toRingedSpace.carrier)
      (hWA : W ≤ ((f ⁻¹ᵁ A i : X.Opens) : Opens X.toRingedSpace.carrier))
      (v : L.val.obj (op W)),
    (meromorphicSectionSheafAsModule X L).val.restrictₛₗ (homOfLE hWA).op
        ((pullbackMeromorphicMul f L s).val.app (op (A i)) (g i))
      = (toMeromorphicSectionSheafAsModule X L).val.app (op W) v →
    ∃ hWV : W ≤ V i, L.val.restrictₛₗ (homOfLE hWV).op (t i) = v

/-- **On the preimages themselves the two family predicates agree.** So
`Stacks.InvertiblePullback.IsPullMeromorphicFamilyOn` generalises
`Stacks.InvertiblePullback.IsPullMeromorphicFamily` rather than re-encoding it. -/
theorem isPullMeromorphicFamilyOn_preimage
    (t' : ∀ i, L.val.obj (op ((f ⁻¹ᵁ A i : X.Opens) : Opens X.toRingedSpace.carrier))) :
    IsPullMeromorphicFamilyOn (V := fun i => ((f ⁻¹ᵁ A i : X.Opens) :
        Opens X.toRingedSpace.carrier)) f L s (fun _ => le_rfl) g t'
      ↔ IsPullMeromorphicFamily f L s g t' := by
  refine forall_congr' fun i => ?_
  have hid : (meromorphicSectionSheafAsModule X L).val.restrictₛₗ
        (homOfLE (le_refl ((f ⁻¹ᵁ A i : X.Opens) : Opens X.toRingedSpace.carrier))).op
        ((pullbackMeromorphicMul f L s).val.app (op (A i)) (g i))
      = (pullbackMeromorphicMul f L s).val.app (op (A i)) (g i) := by
    show (meromorphicSectionSheafAsModule X L).val.presheaf.map
      (𝟙 (op ((f ⁻¹ᵁ A i : X.Opens) : Opens X.toRingedSpace.carrier))) _ = _
    rw [CategoryTheory.Functor.map_id]
    rfl
  rw [hid]
  exact Iff.rfl

include hVA in
/-- **The family on arbitrary opens is assembled into a family on preimages.** With the
saturation inputs of `ChartSaturation.lean`, each member restricted to the chart of
[Stacks, Tag 0BD7] is a regular section on a preimage, and the resulting family, indexed by the
base, satisfies both the family equation and the generating property. -/
theorem exists_isPullMeromorphicFamily_of_isPullMeromorphicFamilyOn
    [IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L]
    [IsLocallyNoetherian Y]
    (ht : IsPullMeromorphicFamilyOn f L s hVA g t)
    (hex : ∀ z : X.toRingedSpace.carrier, ∃ i, z ∈ generatingLocus L (t i))
    (hirr : ∀ y : Y, IsIrreducible (f.base ⁻¹' {y}))
    (hagree : ∀ (i j : ι) (x : X.toRingedSpace.carrier),
      x ∈ generatingLocus L (t i) → x ∈ generatingLocus L (t j) →
      ∀ z : X.toRingedSpace.carrier, f.base z = f.base x →
        (z ∈ generatingLocus L (t i) ↔ z ∈ generatingLocus L (t j)))
    (hfiber : ∀ y : Y, Nonempty (f.fiber y))
    (hfinite : QuasiCompact f ∨ LocallyOfFiniteType f) :
    ∃ (A' : Y → Y.Opens) (g' : ∀ y, (totalQuotientSheafAsModule Y).val.obj (op (A' y)))
      (t' : ∀ y, L.val.obj (op ((f ⁻¹ᵁ A' y : X.Opens) : Opens X.toRingedSpace.carrier))),
      IsPullMeromorphicFamily f L s g' t' ∧
        ∀ z : X.toRingedSpace.carrier, ∃ y, z ∈ generatingLocus L (t' y) := by
  classical
  obtain ⟨chart, hmem, hpre⟩ :=
    exists_chart_coe_preimage_eq_generatingLocus f L t hex hirr hagree hfiber hfinite
  choose idx hidx using hpre
  have hsurj : Function.Surjective f.base := (Surjective.of_nonempty_fiber f hfiber).surj
  have hcV : ∀ y, ((f ⁻¹ᵁ chart y : X.Opens) : Opens X.toRingedSpace.carrier) ≤ V (idx y) := by
    intro y z hz
    exact generatingLocus_le L (t (idx y)) ((hidx y) ▸ hz)
  have hcA : ∀ y, chart y ≤ A (idx y) := by
    intro y y' hy'
    obtain ⟨z, hz⟩ := hsurj y'
    have hzc : z ∈ ((f ⁻¹ᵁ chart y : X.Opens) : Opens X.toRingedSpace.carrier) := by
      show f.base z ∈ chart y
      rw [hz]; exact hy'
    have hzA := hVA (idx y) (hcV y hzc)
    show y' ∈ A (idx y)
    rw [← hz]; exact hzA
  refine ⟨chart,
    fun y => (totalQuotientSheafAsModule Y).val.restrictₛₗ (homOfLE (hcA y)).op (g (idx y)),
    fun y => L.val.restrictₛₗ (homOfLE (hcV y)).op (t (idx y)), fun y => ?_, fun z => ?_⟩
  · have h1 : (pullbackMeromorphicMul f L s).val.app (op (chart y))
          ((totalQuotientSheafAsModule Y).val.restrictₛₗ (homOfLE (hcA y)).op (g (idx y)))
        = ((_root_.SheafOfModules.pushforward f.toRingCatSheafHom).obj
            (meromorphicSectionSheafAsModule X L)).val.restrictₛₗ (homOfLE (hcA y)).op
            ((pullbackMeromorphicMul f L s).val.app (op (A (idx y))) (g (idx y))) :=
      PresheafOfModules.naturality_apply _ _ _
    have h2 : ((_root_.SheafOfModules.pushforward f.toRingCatSheafHom).obj
            (meromorphicSectionSheafAsModule X L)).val.restrictₛₗ (homOfLE (hcA y)).op
            ((pullbackMeromorphicMul f L s).val.app (op (A (idx y))) (g (idx y)))
        = (meromorphicSectionSheafAsModule X L).val.restrictₛₗ (homOfLE (hcV y)).op
            ((meromorphicSectionSheafAsModule X L).val.restrictₛₗ (homOfLE (hVA (idx y))).op
              ((pullbackMeromorphicMul f L s).val.app (op (A (idx y))) (g (idx y)))) :=
      (meromorphicSectionSheafAsModule X L).val.map_comp_apply
        (homOfLE (hVA (idx y))).op (homOfLE (hcV y)).op _
    have h3 : (meromorphicSectionSheafAsModule X L).val.restrictₛₗ (homOfLE (hcV y)).op
            ((toMeromorphicSectionSheafAsModule X L).val.app (op (V (idx y))) (t (idx y)))
        = (toMeromorphicSectionSheafAsModule X L).val.app
            (op ((f ⁻¹ᵁ chart y : X.Opens) : Opens X.toRingedSpace.carrier))
            (L.val.restrictₛₗ (homOfLE (hcV y)).op (t (idx y))) :=
      (PresheafOfModules.naturality_apply (toMeromorphicSectionSheafAsModule X L).val
        (homOfLE (hcV y)).op (t (idx y))).symm
    exact ((h1.trans h2).trans
      (congrArg (fun x => (meromorphicSectionSheafAsModule X L).val.restrictₛₗ
        (homOfLE (hcV y)).op x) (ht (idx y)))).trans h3
  · refine ⟨f.base z, ?_⟩
    have hz : z ∈ ((f ⁻¹ᵁ chart (f.base z) : X.Opens) : Opens X.toRingedSpace.carrier) :=
      hmem (f.base z)
    rw [generatingLocus_restrictₛₗ]
    exact ⟨(hidx (f.base z)) ▸ hz, hz⟩

end Stacks.InvertiblePullback

end
