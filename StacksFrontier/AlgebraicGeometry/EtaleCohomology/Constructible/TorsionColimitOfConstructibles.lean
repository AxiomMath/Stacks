module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ColimitOfConstructibles
public import StacksCore.Tactic.StacksAttribute

/-!
# Torsion étale sheaves as filtered colimits of constructible ones

Let `X` be a quasi-compact and quasi-separated scheme. Every *torsion* abelian sheaf on the small
étale site of `X` is a filtered colimit of constructible abelian sheaves (Stacks 03SA, part (2)).
This is the part of that tag which
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ColimitOfConstructibles` does not
carry: that module has part (1), for sheaves of sets
(`AlgebraicGeometry.exists_isFilteredColimit_isConstructibleSetSheaf`), and part (3), for sheaves
of modules over a Noetherian ring
(`AlgebraicGeometry.exists_isFilteredColimit_isConstructibleModuleSheaf`).

The source proves part (2) from part (3): a torsion abelian sheaf `F` is the union of its
`n`-torsion subsheaves `F[n]`, each `F[n]` is a sheaf of `ℤ/nℤ`-modules, and `ℤ/nℤ` is
Noetherian, so part (3) presents `F[n]` as a filtered colimit of cokernels of maps
`⨁_j j_{V_j!}(ℤ/nℤ) ⟶ ⨁_i j_{U_i!}(ℤ/nℤ)`. Those cokernels are exactly the sheaves displayed by
Stacks 09YT, and their constructibility is already in the library, as
`AlgebraicGeometry.isConstructibleAbelianSheaf_of_hasFiniteZModShriekPresentation`. So the one
input that this file grants rather than proves is the *presentation*: that a torsion abelian
sheaf is a filtered colimit of sheaves of that displayed shape. That is the abelian spelling of
Stacks 093C, and it is the same input parts (1) and (3) grant, in the spelling their own
presentations use.

## Hypotheses that are granted rather than proved

* **Stacks 093C for torsion abelian sheaves**, as
  `AlgebraicGeometry.TorsionAbelianSheavesAreFilteredColimitsOfZModPresentations`: every torsion
  abelian sheaf on `X_étale` is a filtered colimit of sheaves carrying a
  `AlgebraicGeometry.HasFiniteZModShriekPresentation` at quasi-compact quasi-separated étale
  objects. As the source organises the argument, this bundles three steps, none of which this
  library has: the decomposition of a torsion sheaf into its `n`-torsion subsheaves; Stacks 093C
  at `Λ = ℤ/nℤ`, whose module form is granted in
  `ColimitOfConstructibles` as `AlgebraicGeometry.ModuleSheavesAreFilteredColimitsOfPresentations`
  for the same reason; and the identification of the `n`-torsion abelian sheaves with the sheaves
  of `ℤ/nℤ`-modules, whose absence `ColimitOfConstructibles` already records in the docstring of
  `AlgebraicGeometry.isConstructibleAbelianSheaf_of_hasFiniteZModShriekPresentation`. Only a
  presentation is granted, never constructibility of anything: that is what is proved here.
* **Stacks 03S8 (2) at the finite groups `ℤ/nℤ`**, as
  `AlgebraicGeometry.AbelianShriekZModIsConstructible`, which is the hypothesis the library's
  Stacks 09YT already carries.

## Main definitions

* `AlgebraicGeometry.IsTorsionAbelianSheaf` — torsion for an abelian sheaf on the small étale
  site: every section over every étale object is annihilated by a positive integer.
* `AlgebraicGeometry.TorsionAbelianSheavesAreFilteredColimitsOfZModPresentations` — Stacks 093C
  for torsion abelian sheaves, carried as a hypothesis.

## Main results

* `AlgebraicGeometry.exists_isFilteredColimit_isConstructibleAbelianSheaf` — **Stacks 03SA (2)**.

The conclusion is not satisfied trivially: `CategoryTheory.IsFiltered.nonempty` forbids an empty
index category, and `AlgebraicGeometry.Space.isZero_of_isColimit_of_forall_isZero` says a colimit
of a diagram of zero sheaves is zero, so no presentation of a nonzero sheaf has all its terms
zero.

## Implementation notes

Torsion is stated on sections over the objects of the small étale site, which is the condition
the source's `F = ⋃ F[n]` encodes and the condition the library's other torsion statements use
(see the hypothesis `hF` of `Stacks.EtaleCohomology.torsionEtaleModule`, which is annihilation by
a *fixed* integer in the same spelling). It is *not* stated with a single integer annihilating
all of `F`: that is strictly stronger, and the source's `F` is only locally bounded.

The coefficient universe is `AddCommGrpCat.{u + 1}`, as in the abelian half of
`ColimitOfConstructibles`, because `AlgebraicGeometry.abelianShriekZMod` — and hence the
displayed shape of Stacks 09YT — is stated there, and because that is the universe at which
`AlgebraicGeometry.exists_isFilteredColimit_isConstructibleAbelianSheaf_support_notMem`, the one
consumer of this tag in the library, needs it.

The conclusion quantifies over a diagram, a cocone whose point is literally the given sheaf, and
`Nonempty (IsColimit _)`, matching parts (1) and (3) and matching the hypothesis `h03SA` of
`AlgebraicGeometry.exists_isFilteredColimit_isConstructibleAbelianSheaf_support_notMem`, which
this theorem discharges.

Neither the quasi-compactness nor the quasi-separatedness of `X` is used by the proof beyond
feeding Stacks 09YT, which needs both; they are therefore binders of the theorem and not of the
granted hypothesis.

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
every étale object is annihilated by some positive integer. This is the hypothesis of
Stacks 03SA (2), and the condition under which the source's `F = ⋃ F[n]` exhausts `F`.

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

This is the input parts (1) and (3) of Stacks 03SA also grant, each in the spelling of its own
presentations, namely `AlgebraicGeometry.SetSheavesAreFilteredColimitsOfPresentations` and
`AlgebraicGeometry.ModuleSheavesAreFilteredColimitsOfPresentations`. In the organisation of the
source's proof of part (2) it bundles three unavailable steps, described in the module
documentation: the decomposition of a torsion sheaf into its `n`-torsion parts, Stacks 093C at
`Λ = ℤ/nℤ`, and the identification of `n`-torsion abelian sheaves with sheaves of
`ℤ/nℤ`-modules. It grants a presentation only, and no constructibility. -/
public def TorsionAbelianSheavesAreFilteredColimitsOfZModPresentations : Prop :=
  ∀ F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1},
    IsTorsionAbelianSheaf B X F →
    ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
      (ι : D ⟶ (Functor.const I).obj F), Nonempty (IsColimit (Cocone.mk F ι)) ∧
        ∀ i, HasFiniteZModShriekPresentation B X (IsQCQSEtaleObject B X) (D.obj i)

/-- A presentation by affine étale objects is one by quasi-compact quasi-separated étale objects,
so the granted hypothesis also follows from its affine form — the source's "in fact, we can even
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

/-- **Stacks 03SA (2).** Let `X` be a quasi-compact and quasi-separated scheme and let `F` be a
torsion abelian sheaf on `X_étale`. Then `F` is a filtered colimit of constructible abelian
sheaves.

This is the source's own proof, organised as for parts (1) and (3): the granted presentation
writes `F` as a filtered colimit of the cokernels displayed by Stacks 09YT, and those cokernels
are constructible by the library's Stacks 09YT,
`AlgebraicGeometry.isConstructibleAbelianSheaf_of_hasFiniteZModShriekPresentation`, which in turn
rests on Stacks 03RZ for abelian sheaves
(`AlgebraicGeometry.Constructible.constructibleAbelianSheaf_isWeakSerreClass`, an unconditional
instance of this library). Of the inputs the source cites, Stacks 03RZ (2) is discharged from the
library; what remains granted is Stacks 093C for torsion abelian sheaves, which subsumes the
source's reduction to part (3), and Stacks 03S8 (2) at the finite groups `ℤ/nℤ`. -/
@[stacks 03SA "part (2), torsion abelian sheaves, granted Stacks 093C for torsion abelian \
  sheaves in the Z/nZ-shriek spelling as the hypothesis h093C, which subsumes the source's \
  reduction to part (3), and Stacks 03S8 (2) at the finite groups Z/nZ as the hypothesis \
  h03S8; Stacks 03RZ (2) and Stacks 09YT are discharged from the library"]
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
