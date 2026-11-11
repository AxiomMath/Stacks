module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ColimitOfConstructibles
public import StacksCore.Tactic.StacksAttribute

/-!
# Pointwise torsion étale sheaves as filtered colimits of constructible ones, over a presentation

Let `X` be a quasi-compact and quasi-separated scheme. Every *torsion* abelian sheaf on the small
étale site of `X` is a filtered colimit of constructible abelian sheaves (Stacks 03SA, part (2)).
This module carries the source's proof of that part over one input taken as a binder, the
abelian spelling of Stacks 093C described below, and at the pointwise torsion condition
`AlgebraicGeometry.IsTorsionAbelianSheaf`.

Stacks 03SA (2) itself is
`AlgebraicGeometry.exists_isFilteredColimit_isConstructibleAbelianSheaf_of_qcqs` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.LocalTorsionColimitOfConstructibles`,
with no binder beyond the tag's and at the local torsion condition of Stacks 0DD7,
`Stacks.Torsion.torsionSheafProperty`, which the pointwise condition implies
(`AlgebraicGeometry.torsionSheafProperty_of_isTorsionAbelianSheaf`). Parts (1) and (3) are
`AlgebraicGeometry.exists_isFilteredColimit_isConstructibleSetSheaf_of_qcqs` and
`AlgebraicGeometry.exists_isFilteredColimit_isConstructibleModuleSheaf_of_qcqs`.

The source proves part (2) from part (3): a torsion abelian sheaf `F` is the union of its
`n`-torsion subsheaves `F[n]`, each `F[n]` is a sheaf of `ℤ/nℤ`-modules, and `ℤ/nℤ` is
Noetherian, so part (3) presents `F[n]` as a filtered colimit of cokernels of maps
`⨁_j j_{V_j!}(ℤ/nℤ) ⟶ ⨁_i j_{U_i!}(ℤ/nℤ)`. Those cokernels are exactly the sheaves displayed by
Stacks 09YT, and their constructibility is already in the library, as
`AlgebraicGeometry.isConstructibleAbelianSheaf_of_hasFiniteZModShriekPresentation`. So the one
input that this file takes as a binder is the *presentation*: that a torsion abelian sheaf is a
filtered colimit of sheaves of that displayed shape. That is the abelian spelling of Stacks 093C.

## Binders

* **Stacks 093C for torsion abelian sheaves**, as
  `AlgebraicGeometry.TorsionAbelianSheavesAreFilteredColimitsOfZModPresentations`: every torsion
  abelian sheaf on `X_étale` is a filtered colimit of sheaves carrying a
  `AlgebraicGeometry.HasFiniteZModShriekPresentation` at quasi-compact quasi-separated étale
  objects. As the source organises the argument, this bundles three steps: the decomposition of
  a torsion sheaf into its `n`-torsion subsheaves; Stacks 093C at `Λ = ℤ/nℤ`; and the
  identification of the `n`-torsion abelian sheaves with the sheaves of `ℤ/nℤ`-modules. Only a
  presentation is assumed, never constructibility of anything: that is what is proved here.
  The unconditional proof of part (2) in `LocalTorsionColimitOfConstructibles` does not go
  through this presentation: it divides the part (3) presentation over `ULift ℤ` by `n` instead.
* **Stacks 03S8 (2) at the finite groups `ℤ/nℤ`**, as
  `AlgebraicGeometry.AbelianShriekZModIsConstructible`, which is a theorem of the library,
  `AlgebraicGeometry.abelianShriekZModIsConstructible`.

## Main definitions

* `AlgebraicGeometry.IsTorsionAbelianSheaf` — torsion for an abelian sheaf on the small étale
  site: every section over every étale object is annihilated by a positive integer.
* `AlgebraicGeometry.TorsionAbelianSheavesAreFilteredColimitsOfZModPresentations` — Stacks 093C
  for torsion abelian sheaves, carried as a hypothesis.

## Main results

* `AlgebraicGeometry.exists_isFilteredColimit_isConstructibleAbelianSheaf` — the source's proof
  of Stacks 03SA (2), at pointwise torsion and over the binders `h093C` and `h03S8`.

The conclusion is not satisfied trivially: `CategoryTheory.IsFiltered.nonempty` forbids an empty
index category, and `AlgebraicGeometry.Space.isZero_of_isColimit_of_forall_isZero` says a colimit
of a diagram of zero sheaves is zero, so no presentation of a nonzero sheaf has all its terms
zero.

## Implementation notes

Torsion is stated here pointwise, on sections over the objects of the small étale site (compare
the hypothesis `hF` of `Stacks.EtaleCohomology.torsionEtaleModule`, which is annihilation by a
*fixed* integer in the same spelling). It is *not* stated with a single integer annihilating all
of `F`: that is strictly stronger, and the source's `F` is only locally bounded. The source's
torsion is weaker still than the pointwise condition: it is the local condition of Stacks 0DD7,
`Stacks.Torsion.torsionSheafProperty`, at which Stacks 03SA (2) is registered.

The coefficient universe is `AddCommGrpCat.{u + 1}`, as in the abelian half of
`ColimitOfConstructibles`, because `AlgebraicGeometry.abelianShriekZMod` — and hence the
displayed shape of Stacks 09YT — is stated there.

The conclusion quantifies over a diagram, a cocone whose point is literally the given sheaf, and
`Nonempty (IsColimit _)`, matching parts (1) and (3).

Neither the quasi-compactness nor the quasi-separatedness of `X` is used by the proof beyond
feeding Stacks 09YT, which needs both; they are therefore binders of the theorem and not of the
presentation `h093C`.

## References

* [Stacks Project, Tag 03SA](https://stacks.math.columbia.edu/tag/03SA)
* [Stacks Project, Tag 09YT](https://stacks.math.columbia.edu/tag/09YT)
* [Stacks Project, Tag 093C](https://stacks.math.columbia.edu/tag/093C)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
* [Stacks Project, Tag 0F0M](https://stacks.math.columbia.edu/tag/0F0M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

/-- An abelian sheaf on the small étale site of `X` is **torsion** when every section of it over
every étale object is annihilated by some positive integer. This is the *pointwise* form of
torsion. It implies the local form of Stacks 0DD7, `Stacks.Torsion.torsionSheafProperty`, which
is the hypothesis of Stacks 03SA (2) and the condition under which the source's `F = ⋃ F[n]`
exhausts `F` in the category of sheaves.

Like `AlgebraicGeometry.IsConstructibleAbelianSheaf` this is a transparent abbreviation, so its
defining witnesses can be applied directly. -/
public abbrev IsTorsionAbelianSheaf
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) : Prop :=
  ∀ (U : SmallEtale B X.obj X.property) (s : F.obj.obj (op U)), ∃ n : ℕ, 0 < n ∧ n • s = 0

/-- A sheaf isomorphic to a torsion abelian sheaf is torsion: an isomorphism of sheaves is an
isomorphism of abelian groups on sections, and the inverse image of a section annihilated by `n`
is annihilated by `n`. -/
public theorem isTorsionAbelianSheaf_congr
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}} (e : F ≅ G)
    (hF : IsTorsionAbelianSheaf B X F) : IsTorsionAbelianSheaf B X G := by
  intro U s
  set c := (((sheafToPresheaf (SmallEtale.topology B X.obj X.property)
    AddCommGrpCat.{u + 1}).mapIso e).app (op U))
  obtain ⟨n, hn, hns⟩ := hF U (c.inv s)
  refine ⟨n, hn, ?_⟩
  have h : c.hom (c.inv s) = s := by simp
  calc n • s = n • c.hom (c.inv s) := by rw [h]
    _ = c.hom (n • c.inv s) := by rw [map_nsmul]
    _ = 0 := by rw [hns, map_zero]

/-- **Stacks 093C for torsion abelian sheaves as a hypothesis**, in the spelling of
`AlgebraicGeometry.HasFiniteZModShriekPresentation`: every torsion abelian sheaf on the small
étale site of `X` is a filtered colimit of cokernels of maps
`⨁_j j_{V_j!}(ℤ/m_jℤ) ⟶ ⨁_i j_{U_i!}(ℤ/n_iℤ)` between finite direct sums of extensions by zero
of constant sheaves with finite cyclic value, at quasi-compact quasi-separated étale objects.

This is the abelian analogue of the inputs
`AlgebraicGeometry.SetSheavesAreFilteredColimitsOfPresentations` and
`AlgebraicGeometry.ModuleSheavesAreFilteredColimitsOfPresentations` of the proofs of parts (1)
and (3) of Stacks 03SA, each in the spelling of its own presentations. In the organisation of
the source's proof of part (2) it bundles three steps, described in the module documentation:
the decomposition of a torsion sheaf into its `n`-torsion parts, Stacks 093C at `Λ = ℤ/nℤ`, and
the identification of `n`-torsion abelian sheaves with sheaves of `ℤ/nℤ`-modules. It asserts a
presentation only, and no constructibility. -/
public def TorsionAbelianSheavesAreFilteredColimitsOfZModPresentations : Prop :=
  ∀ F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1},
    IsTorsionAbelianSheaf B X F →
    ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
      (ι : D ⟶ (Functor.const I).obj F), Nonempty (IsColimit (Cocone.mk F ι)) ∧
        ∀ i, HasFiniteZModShriekPresentation B X (IsQCQSEtaleObject B X) (D.obj i)

/-- A presentation by affine étale objects is one by quasi-compact quasi-separated étale objects,
so the hypothesis also follows from its affine form — the source's "in fact, we can even
assume `U_i` and `V_j` affine". -/
public theorem torsionAbelianSheavesAreFilteredColimitsOfZModPresentations_of_affine
    (h : ∀ F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1},
      IsTorsionAbelianSheaf B X F →
      ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
        (D : I ⥤ Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
        (ι : D ⟶ (Functor.const I).obj F), Nonempty (IsColimit (Cocone.mk F ι)) ∧
          ∀ i, HasFiniteZModShriekPresentation B X
            (SmallEtale.IsAffine B X.obj X.property) (D.obj i)) :
    TorsionAbelianSheavesAreFilteredColimitsOfZModPresentations B X := fun F hF => by
  obtain ⟨I, hI, hfilt, D, ι, hcolim, hD⟩ := h F hF
  exact ⟨I, hI, hfilt, D, ι, hcolim,
    fun i => hasFiniteZModShriekPresentation_qcqs_of_affine B X (hD i)⟩

/-- **The proof of Stacks 03SA (2), at pointwise torsion and over its inputs.** Let `X` be a
quasi-compact and quasi-separated scheme and let `F` be a pointwise torsion abelian sheaf on
`X_étale`. Then `F` is a filtered colimit of constructible abelian
sheaves.

This is the source's own proof, organised as for parts (1) and (3): the presentation `h093C`
writes `F` as a filtered colimit of the cokernels displayed by Stacks 09YT, and those cokernels
are constructible by the library's Stacks 09YT,
`AlgebraicGeometry.isConstructibleAbelianSheaf_of_hasFiniteZModShriekPresentation`, which in turn
rests on Stacks 03RZ for abelian sheaves
(`AlgebraicGeometry.Constructible.constructibleAbelianSheaf_isWeakSerreClass`, an unconditional
instance of this library). Of the inputs the source cites, Stacks 03RZ (2) is discharged from the
library; the binders are Stacks 093C for torsion abelian sheaves, which subsumes the source's
reduction to part (3), and Stacks 03S8 (2) at the finite groups `ℤ/nℤ`.

Stacks 03SA (2) with no binder beyond the tag's, and at the weaker local torsion hypothesis of
Stacks 0DD7, is `AlgebraicGeometry.exists_isFilteredColimit_isConstructibleAbelianSheaf_of_qcqs`.
-/
public theorem exists_isFilteredColimit_isConstructibleAbelianSheaf
    (h093C : TorsionAbelianSheavesAreFilteredColimitsOfZModPresentations B X)
    (h03S8 : AbelianShriekZModIsConstructible B) (hXc : CompactSpace X.obj)
    (hXq : QuasiSeparatedSpace X.obj)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : IsTorsionAbelianSheaf B X F) :
    ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
      (ι : D ⟶ (Functor.const I).obj F), Nonempty (IsColimit (Cocone.mk F ι)) ∧
        ∀ i, IsConstructibleAbelianSheaf B X (D.obj i) := by
  obtain ⟨I, hI, hfilt, D, ι, hcolim, hD⟩ := h093C F hF
  exact ⟨I, hI, hfilt, D, ι, hcolim,
    fun i => isConstructibleAbelianSheaf_of_hasFiniteZModShriekPresentation B X h03S8 hXc hXq
      (hD i)⟩

end AlgebraicGeometry

end
