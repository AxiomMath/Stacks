module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.IntegerShriekPresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleSurjectiveDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.TorsionOfConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerreAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CompactConstructibleAbelian
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.TorsionLocalAnnihilation
import StacksCore.Tactic.StacksAttribute

/-!
# Constructibility of an abelian étale sheaf descends along a surjective morphism

Let `f : X ⟶ Y` be a surjective morphism of quasi-compact and quasi-separated schemes and let `ℱ`
be an *arbitrary* abelian sheaf on `Y_étale`. Then `ℱ` is constructible as soon as `f⁻¹ℱ` is;
with Stacks 095G, which is the converse and needs neither surjectivity nor quasi-compactness,
this is part (2) of Stacks 095Q, proved unconditionally below.

## The route taken

An abelian group is a `ℤ`-module and `ℤ` is Noetherian, so the statement to be proved is a
special case of the sheaves-of-modules statement of Stacks 095Q — which the library already has
without hypotheses, as `AlgebraicGeometry.isConstructibleModuleSheaf_pullback_iff_of_surjective`.
The whole content of the proof below is therefore the passage between abelian sheaves and sheaves
of `ℤ`-modules, in both directions.

Going out costs nothing. Constructibility of a sheaf of `ℤ`-modules asks the local values on the
strata to be *finitely generated*, constructibility of an abelian sheaf asks them to be *finite*,
and a finite abelian group is a finitely generated `ℤ`-module; this is
`AlgebraicGeometry.isConstructibleModuleSheaf_moduleCatIntEquivalence`. The module development is
pinned to a coefficient ring in `Type (u + 1)`, so the descent itself is run at the Noetherian
ring `ULift.{u + 1} ℤ`, reached and left by restriction of scalars along `ULift.ringEquiv`
(`AlgebraicGeometry.isConstructibleModuleSheaf_uliftIntRestrictScalars` and its converse
`AlgebraicGeometry.isConstructibleModuleSheaf_int_of_uliftIntRestrictScalars` below).

Coming back is the step with content, and is
`AlgebraicGeometry.isConstructibleAbelianSheaf_of_isConstructibleModuleSheaf_int`: finitely
generated has to be improved to finite, and what does it is torsion. A finitely generated abelian
group annihilated by a positive integer is finite, so on a stratum where `ℱ` is locally constant
with finitely generated values it is enough to annihilate the whole restriction by one positive
integer, which is `Stacks.ConstantSheaf.isLocallyAnnihilated_of_torsionSheafProperty`. Torsion of
`ℱ` is **not** assumed: it is read off the stalks of `f⁻¹ℱ`, by the unconditional
`AlgebraicGeometry.torsionSheafProperty_of_isConstructibleAbelianSheaf_pullback`, and it survives
the restriction to a stratum by
`AlgebraicGeometry.torsionSheafProperty_smallEtaleAbelianPullback` below.

Nothing of the source's Stacks 093C for *torsion abelian* sheaves is needed: the form of
Stacks 093C the descent consumes is the one for sheaves of modules, which the library proves as
`AlgebraicGeometry.moduleSheavesAreFilteredColimitsOfPresentations`.

## The source's own route

The source argues inside the category of abelian sheaves instead: torsion makes Stacks 03SA (2)
available, which writes `ℱ = colim_i ℱ_i` as a filtered colimit of constructible sheaves; inverse
image is a left adjoint, so `f⁻¹ℱ = colim_i f⁻¹ℱ_i`, and `f⁻¹ℱ` is a compact object because it is
constructible (Stacks 09Z4), so the identity of `f⁻¹ℱ` factors through some `f⁻¹ℱ_i`; that makes
`f⁻¹(ℱ_i ⟶ ℱ)` a split epimorphism, and surjectivity of `f` carries the epimorphism back to `Y` by
`AlgebraicGeometry.epi_of_epi_smallEtalePullback_abelian`. So `ℱ` is a quotient of a constructible
sheaf — and this is the one step of that argument which uses `f` at all. Applying it twice
finishes: for `p : 𝒢 ⟶ ℱ` such a quotient, the kernel of `p` has constructible inverse image,
since inverse image is left exact and the constructible abelian sheaves are a weak Serre
subcategory (Stacks 03RZ (2)); so the kernel is itself a quotient of a constructible `ℋ`, and `ℱ`
is the cokernel of the composite `ℋ ⟶ ker p ⟶ 𝒢`.

That argument is kept below, in the section `ColimitRoute`, because it is the source's and
because its steps are of independent interest. It quantifies over three statements of the source,
and they stand on different footings. Two are theorems of the library, so a caller can always
supply them: Stacks 03S8 (2) at the finite groups `ℤ/nℤ`, as `h03S8` in the spelling
`AlgebraicGeometry.AbelianShriekZModIsConstructible`, is
`AlgebraicGeometry.abelianShriekZModIsConstructible`, and Stacks 095N for `ℤ`-modules at `X`, as
`h095N`, is `AlgebraicGeometry.hasFiniteShriekPresentation_of_isConstructibleModuleSheaf_int`.
The third is not: Stacks 093C for torsion abelian sheaves at `Y`, as `h093C` in the spelling
`AlgebraicGeometry.LocallyTorsionAbelianSheavesAreFilteredColimitsOfZModPresentations`, has no
proof in the library. The route above avoids it altogether, so the section is superseded by the
unconditional equivalence and carries no tag.

## Stacks 03SA (2) at the local torsion notion, over a presentation

Stacks 03SA (2) is about a *torsion* abelian sheaf, and the source's torsion for a sheaf on a
site is the **local** condition of Stacks 0DD7: every section is annihilated by a positive
integer after restriction along the arrows of a covering sieve, the integer being allowed to vary
over the sieve. That is `Stacks.Torsion.torsionSheafProperty`.

`AlgebraicGeometry.exists_isFilteredColimit_isConstructibleAbelianSheaf` of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Constructible/TorsionColimitOfConstructibles.lean`
states Stacks 03SA (2) at `AlgebraicGeometry.IsTorsionAbelianSheaf` instead, the **pointwise**
condition that every section over every étale object is annihilated by a positive integer. That
is strictly stronger: pointwise torsion implies local torsion by the maximal sieve
(`AlgebraicGeometry.torsionSheafProperty_of_isTorsionAbelianSheaf`), while the converse would
need a common multiple of the integers occurring over a covering, hence quasi-compactness of the
object, which the objects of `X_étale` need not have. So that theorem assumes strictly more than
its tag, and constructibility — which produces the local condition and only the local condition —
cannot reach its hypothesis.

`AlgebraicGeometry.exists_isFilteredColimit_isConstructibleAbelianSheaf_of_torsionSheafProperty`
below is therefore the same statement re-indexed at `Stacks.Torsion.torsionSheafProperty`. The
proof is unchanged: in the pointwise version the torsion hypothesis is consumed *only* by the
hypothesis `h093C`, so re-indexing that hypothesis is the whole edit. It is the input of the
source's route below.

Stacks 03SA (2) itself, at `Stacks.Torsion.torsionSheafProperty` and with no binder beyond the
tag's, is `AlgebraicGeometry.exists_isFilteredColimit_isConstructibleAbelianSheaf_of_qcqs` of
`Constructible/LocalTorsionColimitOfConstructibles.lean`, which reduces it to part (3) without
going through `h093C`.

## Main results

* `AlgebraicGeometry.isConstructibleAbelianSheaf_pullback_iff_of_surjective` — **Stacks 095Q
  (2)**, with no hypotheses beyond the surjectivity of `f` and the quasi-compactness and
  quasi-separatedness of `X` and `Y` that the source's statement assumes.
* `AlgebraicGeometry.isConstructibleAbelianSheaf_of_isConstructibleModuleSheaf_int` — a torsion
  abelian sheaf whose attached sheaf of `ℤ`-modules is constructible is constructible.
* `AlgebraicGeometry.torsionSheafProperty_smallEtaleAbelianPullback` — torsion of an abelian
  étale sheaf passes to inverse images.
* `AlgebraicGeometry.isConstructibleModuleSheaf_int_of_uliftIntRestrictScalars` — the transport of
  constructibility from `ULift ℤ`-modules back to `ℤ`-modules.
* `AlgebraicGeometry.exists_isFilteredColimit_isConstructibleAbelianSheaf_of_torsionSheafProperty`
  — the source's proof of Stacks 03SA (2) at the local torsion notion, over the presentation
  `AlgebraicGeometry.LocallyTorsionAbelianSheavesAreFilteredColimitsOfZModPresentations`.
* `AlgebraicGeometry.epi_of_epi_smallEtalePullback_abelian` — inverse image along a surjective
  morphism reflects epimorphisms of abelian sheaves.
* `AlgebraicGeometry.exists_epi_of_isColimit_of_surjective_abelian` — the descent step of the
  source's route, with no hypothesis beyond compactness of `f⁻¹ℱ`.
* `AlgebraicGeometry.exists_epi_isConstructibleAbelianSheaf_of_pullback` and
  `AlgebraicGeometry.isConstructibleAbelianSheaf_of_isConstructibleAbelianSheaf_pullback` — the
  source's route to the converse implication, quantifying over the three statements of the source
  listed above.

## Implementation notes

The coefficient universe is `AddCommGrpCat.{u + 1}`, as in the rest of the constructibility
development, `u` being the universe of the schemes. The `ModuleCat.{u + 1} ℤ` sheafification
instances are what the passage to sheaves of `ℤ`-modules asks for; the corresponding instances at
`ModuleCat.{u + 1} (ULift.{u + 1} ℤ)` need not be assumed, the ring being in `Type (u + 1)`, where
`AlgebraicGeometry.SmallEtale.isRightAdjointPushforward_moduleCatSelf` and
`AlgebraicGeometry.SmallEtale.hasWeakSheafifyOver_moduleCatSelf` apply.

The three statements of
`Stacks.ConstantSheaf.isLocallyAnnihilated_of_torsionSheafProperty`,
`Stacks.ConstantSheaf.isFiniteLocallyConstant_of_isFiniteTypeLocallyConstantModuleSheaf` and
`Stacks.ConstantSheaf.intSheaf` are read at the universes `u` for the morphisms of the small étale
site, `u + 1` for its objects and `0` for the slack in the coefficient universe, which makes their
`max` of the three equal to `u + 1`.

Torsion enters only through `Stacks.Torsion.torsionSheafProperty`, and the only producer used is
the unconditional `AlgebraicGeometry.torsionSheafProperty_of_isConstructibleAbelianSheaf_pullback`
of `Constructible/TorsionOfConstructible.lean`; that lemma also witnesses that the condition is
satisfied by non-trivial sheaves, every constructible abelian sheaf satisfying it.

## References

* [Stacks Project, Tag 095Q](https://stacks.math.columbia.edu/tag/095Q)
* [Stacks Project, Tag 095G](https://stacks.math.columbia.edu/tag/095G)
* [Stacks Project, Tag 03SA](https://stacks.math.columbia.edu/tag/03SA)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
* [Stacks Project, Tag 093C](https://stacks.math.columbia.edu/tag/093C)
* [Stacks Project, Tag 095N](https://stacks.math.columbia.edu/tag/095N)
* [Stacks Project, Tag 09Z4](https://stacks.math.columbia.edu/tag/09Z4)
* [Stacks Project, Tag 0DD7](https://stacks.math.columbia.edu/tag/0DD7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Torsion Stacks.ConstantSheaf

universe u r

namespace AlgebraicGeometry

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts
attribute [local instance] Cardinal.fact_isRegular_aleph0

variable (B : BigEtaleSite.{u})

/-! ### Stacks 03SA (2) at the local torsion notion, over a presentation -/

section Torsion

variable (X : B.Scheme)

/-- **Stacks 093C for torsion abelian sheaves as a hypothesis**, at the faithful local torsion
notion: every abelian sheaf on `X_étale` satisfying `Stacks.Torsion.torsionSheafProperty` is a
filtered colimit of cokernels of maps
`⨁_j j_{V_j!}(ℤ/m_jℤ) ⟶ ⨁_i j_{U_i!}(ℤ/n_iℤ)` at quasi-compact quasi-separated étale objects.

This is `AlgebraicGeometry.TorsionAbelianSheavesAreFilteredColimitsOfZModPresentations` with its
hypothesis replaced by the local condition of Stacks 0DD7, which is the condition the source's
"torsion abelian sheaf" names. As a hypothesis it is therefore strictly stronger: it covers more
sheaves, the pointwise condition implying the local one. The module documentation explains why
the pointwise condition cannot be reached from constructibility, and
`TorsionColimitOfConstructibles.lean` explains which steps of the source's proof this bundles. -/
public def LocallyTorsionAbelianSheavesAreFilteredColimitsOfZModPresentations : Prop :=
  ∀ F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1},
    torsionSheafProperty (SmallEtale.topology B X.obj X.property) F →
    ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
      (ι : D ⟶ (Functor.const I).obj F), Nonempty (IsColimit (Cocone.mk F ι)) ∧
        ∀ i, HasFiniteZModShriekPresentation B X (IsQCQSEtaleObject B X) (D.obj i)

/-- The assumption in its local form implies the pointwise form that
`AlgebraicGeometry.exists_isFilteredColimit_isConstructibleAbelianSheaf` carries: a pointwise
torsion abelian sheaf is torsion. -/
public theorem torsionAbelianSheavesAreFilteredColimitsOfZModPresentations_of_locally
    (h : LocallyTorsionAbelianSheavesAreFilteredColimitsOfZModPresentations B X) :
    TorsionAbelianSheavesAreFilteredColimitsOfZModPresentations B X := fun F hF =>
  h F (torsionSheafProperty_of_isTorsionAbelianSheaf B X F hF)

section Coefficients

variable
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) AddCommGrpCat.{u + 1}]

/-- **The proof of Stacks 03SA (2) at local torsion, over its inputs.** Let `X` be a quasi-compact
and quasi-separated scheme and let `F` be a torsion abelian sheaf on `X_étale`. Then `F` is a
filtered colimit of constructible abelian sheaves.

This is the faithful restatement of
`AlgebraicGeometry.exists_isFilteredColimit_isConstructibleAbelianSheaf`
(`Constructible/TorsionColimitOfConstructibles.lean`), whose torsion hypothesis is
`AlgebraicGeometry.IsTorsionAbelianSheaf`, the *pointwise* annihilation of every section over
every étale object. That condition strengthens the hypothesis of the tag, whose "torsion abelian
sheaf" is the *local* condition of Stacks 0DD7, here `Stacks.Torsion.torsionSheafProperty`; the
two are not equivalent, the objects of `X_étale` not being quasi-compact.

The proof is the source's, and is the same as the pointwise version's: the presentation supplied
by `h093C` writes `F` as a filtered colimit of the cokernels displayed by Stacks 09YT, and those
cokernels are constructible by the library's Stacks 09YT,
`AlgebraicGeometry.isConstructibleAbelianSheaf_of_hasFiniteZModShriekPresentation`, which rests on
Stacks 03RZ (2).

Two statements of the source are binders of this theorem rather than inputs it derives.
Stacks 03S8 (2) at the finite groups `ℤ/nℤ`, as `h03S8`, is a theorem of the library —
`AlgebraicGeometry.abelianShriekZModIsConstructible` of
`Constructible/AbelianShriekConstructible.lean` proves
`AlgebraicGeometry.AbelianShriekZModIsConstructible` outright. Stacks 093C for torsion abelian
sheaves at the local torsion notion, as `h093C` in the spelling
`AlgebraicGeometry.LocallyTorsionAbelianSheavesAreFilteredColimitsOfZModPresentations`, is not
proved in that spelling.

The conclusion with neither binder is
`AlgebraicGeometry.exists_isFilteredColimit_isConstructibleAbelianSheaf_of_qcqs`, where
Stacks 03SA (2) is registered. -/
public theorem exists_isFilteredColimit_isConstructibleAbelianSheaf_of_torsionSheafProperty
    (h093C : LocallyTorsionAbelianSheavesAreFilteredColimitsOfZModPresentations B X)
    (h03S8 : AbelianShriekZModIsConstructible B) (hXc : CompactSpace X.obj)
    (hXq : QuasiSeparatedSpace X.obj)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : torsionSheafProperty (SmallEtale.topology B X.obj X.property) F) :
    ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
      (ι : D ⟶ (Functor.const I).obj F), Nonempty (IsColimit (Cocone.mk F ι)) ∧
        ∀ i, IsConstructibleAbelianSheaf B X (D.obj i) := by
  obtain ⟨I, hI, hfilt, D, ι, hcolim, hD⟩ := h093C F hF
  exact ⟨I, hI, hfilt, D, ι, hcolim,
    fun i => isConstructibleAbelianSheaf_of_hasFiniteZModShriekPresentation B X h03S8 hXc hXq
      (hD i)⟩

end Coefficients

end Torsion

/-! ### Descent of constructibility -/

variable {X Y : B.Scheme} (f : X ⟶ Y)

/-- **Inverse image along a surjective morphism reflects epimorphisms of abelian sheaves.** For
`f : X ⟶ Y` surjective, a map `α` of abelian sheaves on `Y_étale` with `f⁻¹α` an epimorphism is
itself an epimorphism. Together with the preservation of epimorphisms by the left adjoint `f⁻¹`,
this says that `f⁻¹` creates epimorphisms.

An epimorphism of abelian sheaves is locally surjective, local surjectivity descends along a
surjective morphism by
`AlgebraicGeometry.isLocallySurjective_of_isLocallySurjective_smallEtalePullback_abelian`, and a
locally surjective map of sheaves is an epimorphism. -/
public theorem epi_of_epi_smallEtalePullback_abelian
    (hf : Function.Surjective (B.inclusion.map f).base)
    {F G : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1}} (α : F ⟶ G)
    (hα : Epi ((smallEtaleAbelianPullbackFunctor B f).map α)) : Epi α := by
  have h₁ : Presheaf.IsLocallySurjective (SmallEtale.topology B X.obj X.property)
      ((smallEtaleAbelianPullbackFunctor B f).map α).hom :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u + 1}
      ((smallEtaleAbelianPullbackFunctor B f).map α)).2 hα
  have := isLocallySurjective_of_isLocallySurjective_smallEtalePullback_abelian B f hf α h₁
  infer_instance

/-- **The descent step of Stacks 095Q (2).** Let `f : X ⟶ Y` be a surjective morphism of the big
étale site and let `ℱ` be the colimit of a filtered diagram of abelian sheaves on `Y_étale`. If
the inverse image `f⁻¹ℱ` is a compact object of the category of abelian sheaves on `X_étale`,
then some coprojection `ℱ_i ⟶ ℱ` is an epimorphism.

Nothing is assumed here: inverse image preserves the colimit, being a left adjoint, so
compactness of `f⁻¹ℱ` factors its identity through some `f⁻¹ℱ_i`, which makes `f⁻¹(ℱ_i ⟶ ℱ)` a
split epimorphism, and surjectivity of `f` carries that back to `Y`. This is the one step of the
proof of Stacks 095Q at which `f` is used. -/
public theorem exists_epi_of_isColimit_of_surjective_abelian
    (hf : Function.Surjective (B.inclusion.map f).base)
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1})
    (t : Cocone D) (ht : IsColimit t)
    (hcompact : IsFinitelyPresentable.{u + 1}
      ((smallEtaleAbelianPullbackFunctor B f).obj t.pt)) :
    ∃ i : I, Epi (t.ι.app i) := by
  have hadj := (smallEtaleBaseChange B f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property)
  have := hadj.leftAdjoint_preservesColimits
  have : IsCardinalPresentable
      ((smallEtaleAbelianPullbackFunctor B f).mapCocone t).pt Cardinal.aleph0.{u + 1} :=
    hcompact
  have : IsCardinalFiltered I Cardinal.aleph0.{u + 1} :=
    (isCardinalFiltered_aleph0_iff I).2 ‹IsFiltered I›
  obtain ⟨i, r, hr⟩ := IsCardinalPresentable.exists_hom_of_isColimit
    (κ := Cardinal.aleph0.{u + 1})
    (isColimitOfPreserves (smallEtaleAbelianPullbackFunctor B f) ht) (𝟙 _)
  have hsplit : IsSplitEpi ((smallEtaleAbelianPullbackFunctor B f).map (t.ι.app i)) :=
    ⟨⟨r, hr⟩⟩
  exact ⟨i, epi_of_epi_smallEtalePullback_abelian B f hf (t.ι.app i) hsplit.epi⟩

/-! ### From constructibility of the attached sheaf of `ℤ`-modules back to abelian sheaves -/

section ModuleBridge

/-- Constructibility of a sheaf of `Λ`-modules on the small étale site is invariant under
isomorphism: the same constructible stratification works, and a trivialization of the restriction
to a stratum is carried along the restriction of the given isomorphism. -/
private theorem isConstructibleModuleSheaf_of_iso (Z : B.Scheme) (Λ : Type r) [CommRing Λ]
    [IsNoetherianRing Λ]
    [∀ (S T : B.Scheme) (g : T ⟶ S),
      ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{u + 1} Λ)
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{u + 1} Λ)]
    {G G' : Sheaf (SmallEtale.topology B Z.obj Z.property) (ModuleCat.{u + 1} Λ)} (e : G ≅ G')
    (hG : IsConstructibleModuleSheaf B Z Λ G) :
    IsConstructibleModuleSheaf B Z Λ G' := by
  intro U
  obtain ⟨s, hs⟩ := hG U
  exact ⟨s, fun i => ObjectProperty.IsClosedUnderIsomorphisms.of_iso
    (((smallEtaleBaseChange B (s.inclusion i)).sheafPullback (ModuleCat.{u + 1} Λ)
      (SmallEtale.topology B Z.obj Z.property)
      (SmallEtale.topology B (s.piece i).obj (s.piece i).property)).mapIso e) (hs i)⟩

section Abelian

variable
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]

/-- **Torsion of an abelian étale sheaf passes to inverse images.** For an arbitrary morphism
`g : Z ⟶ W` of the big étale site, the inverse image along `g` of an abelian sheaf on `W_étale`
satisfying the local torsion condition of Stacks 0DD7 satisfies it again on `Z_étale`.

Torsion of an abelian étale sheaf is detected on the stalks at geometric points, by
`AlgebraicGeometry.SmallEtale.torsionSheafProperty_of_forall_etaleStalk` and
`AlgebraicGeometry.SmallEtale.exists_nsmul_eq_zero_etaleStalk`, and the stalk of `g⁻¹ℱ` at a
geometric point of `Z` is the stalk of `ℱ` at its image point. -/
public theorem torsionSheafProperty_smallEtaleAbelianPullback {Z W : B.Scheme} (g : Z ⟶ W)
    (F : Sheaf (SmallEtale.topology B W.obj W.property) AddCommGrpCat.{u + 1})
    (hF : torsionSheafProperty (SmallEtale.topology B W.obj W.property) F) :
    torsionSheafProperty (SmallEtale.topology B Z.obj Z.property)
      ((smallEtaleAbelianPullbackFunctor B g).obj F) :=
  SmallEtale.torsionSheafProperty_of_forall_etaleStalk.{u, u + 1} B Z.obj Z.property _
    fun t a => exists_nsmul_eq_zero_of_iso
      (etaleStalkSmallEtalePullObjIso B g t AddCommGrpCat.{u + 1} F).symm
      (fun y => SmallEtale.exists_nsmul_eq_zero_etaleStalk.{u, u + 1} B W.obj W.property
        (t.map (B.inclusion.map g)) F hF y) a

end Abelian

section IntModules

variable
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{u + 1} ℤ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{u + 1} ℤ)]

/-- **A constructible sheaf of `ULift ℤ`-modules descends to a constructible sheaf of
`ℤ`-modules.** This is the converse transport of
`AlgebraicGeometry.isConstructibleModuleSheaf_uliftIntRestrictScalars`: if restriction of scalars
along `ULift.ringEquiv` carries a sheaf `G` of `ℤ`-modules on `Z_étale` to a constructible sheaf
of `ULift ℤ`-modules, then `G` itself is constructible.

The same constructible stratification works. On a stratum the inverse equivalence carries a
trivialization by finitely generated `ULift ℤ`-modules to one by finitely generated `ℤ`-modules,
restriction of scalars along a ring isomorphism preserving module-finiteness; this is
`Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_of_coefficientEquivalence` at that inverse. -/
public theorem isConstructibleModuleSheaf_int_of_uliftIntRestrictScalars (Z : B.Scheme)
    (G : Sheaf (SmallEtale.topology B Z.obj Z.property) (ModuleCat.{u + 1} ℤ))
    (hG : IsConstructibleModuleSheaf B Z (ULift.{u + 1} ℤ)
      ((Sheaf.coefficientEquivalence (SmallEtale.topology B Z.obj Z.property)
        ModuleCat.restrictScalarsUliftIntEquivalence.{u + 1, u + 1}).functor.obj G)) :
    IsConstructibleModuleSheaf B Z ℤ G := by
  intro U
  obtain ⟨s, hs⟩ := hG U
  refine ⟨s, fun i => ?_⟩
  refine isFiniteTypeLocallyConstant_of_coefficientEquivalence _
    ModuleCat.restrictScalarsUliftIntEquivalence.{u + 1, u + 1}.symm
    (fun M => ModuleCat.isFG (ULift.{u + 1} ℤ) M) (fun M hM => ?_) _ (hs i) _ ?_
  · have := (ModuleCat.isFG_iff M).1 hM
    exact (ModuleCat.isFG_iff _).2
      (ModuleCat.moduleFinite_restrictScalars_of_ringEquiv (ULift.ringEquiv (R := ℤ)).symm M)
  · refine (sheafCompose _
      ModuleCat.restrictScalarsUliftIntEquivalence.{u + 1, u + 1}.inverse).mapIso
        ((Sheaf.sheafPullbackCoefficientIso (smallEtaleBaseChange B (s.inclusion i))
          (SmallEtale.topology B Z.obj Z.property)
          (SmallEtale.topology B (s.piece i).obj (s.piece i).property)
          ModuleCat.restrictScalarsUliftIntEquivalence.{u + 1, u + 1}).app G).symm ≪≫ ?_
    exact ((Sheaf.coefficientEquivalence _
      ModuleCat.restrictScalarsUliftIntEquivalence.{u + 1, u + 1}).unitIso.app _).symm

end IntModules

end ModuleBridge

section Descent

variable
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) AddCommGrpCat.{u + 1}]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{u + 1} ℤ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{u + 1} ℤ)]

/-- The constructible abelian sheaves on the small étale site of a scheme of `B`, as a property of
objects of the category of abelian sheaves, at the coefficient universe of this file. -/
private abbrev constructibleAbelianSheavesOn (Z : B.Scheme) :
    ObjectProperty (Sheaf (SmallEtale.topology B Z.obj Z.property) AddCommGrpCat.{u + 1}) :=
  fun F => IsConstructibleAbelianSheaf B Z F


/-- **A torsion abelian étale sheaf whose attached sheaf of `ℤ`-modules is constructible is
itself constructible.** Let `ℱ` be an abelian sheaf on `Z_étale` satisfying the local torsion
condition of Stacks 0DD7. If the sheaf of `ℤ`-modules attached to `ℱ` by the equivalence
`AddCommGrpCat ≌ ModuleCat ℤ` is constructible, then `ℱ` is constructible as an abelian sheaf.

The two notions of constructibility differ only in the condition imposed on the local values of
the strata: a constructible sheaf of `ℤ`-modules is locally constant with *finitely generated*
values, a constructible abelian sheaf is locally constant with *finite* values. Torsion closes the
gap. Torsion survives the restriction to a stratum by
`AlgebraicGeometry.torsionSheafProperty_smallEtaleAbelianPullback`, a torsion abelian sheaf with
finitely generated local values is locally annihilated by a single positive integer by
`Stacks.ConstantSheaf.isLocallyAnnihilated_of_torsionSheafProperty`, and a finitely generated
abelian group killed by a positive integer is finite, which is
`Stacks.ConstantSheaf.isFiniteLocallyConstant_of_isFiniteTypeLocallyConstantModuleSheaf`. -/
public theorem isConstructibleAbelianSheaf_of_isConstructibleModuleSheaf_int (Z : B.Scheme)
    (F : Sheaf (SmallEtale.topology B Z.obj Z.property) AddCommGrpCat.{u + 1})
    (hF : IsConstructibleModuleSheaf B Z ℤ
      ((Sheaf.coefficientEquivalence (SmallEtale.topology B Z.obj Z.property)
        AddCommGrpCat.moduleCatIntEquivalence.{u + 1}).functor.obj F))
    (hTor : torsionSheafProperty (SmallEtale.topology B Z.obj Z.property) F) :
    IsConstructibleAbelianSheaf B Z F := by
  intro U
  obtain ⟨s, hs⟩ := hF U
  refine ⟨s, fun i => ?_⟩
  have hfin : IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0}
      (SmallEtale.topology B (s.piece i).obj (s.piece i).property) ℤ
      ((intSheaf.{u, u + 1, 0}
        (SmallEtale.topology B (s.piece i).obj (s.piece i).property)).obj
        ((smallEtaleAbelianPullbackFunctor B (s.inclusion i)).obj F)) := by
    refine ObjectProperty.IsClosedUnderIsomorphisms.of_iso ?_ (hs i)
    exact ((Sheaf.sheafPullbackCoefficientIso (smallEtaleBaseChange B (s.inclusion i))
      (SmallEtale.topology B Z.obj Z.property)
      (SmallEtale.topology B (s.piece i).obj (s.piece i).property)
      AddCommGrpCat.moduleCatIntEquivalence.{u + 1}).app F).symm
  exact isFiniteLocallyConstant_of_isFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0} _ _ hfin
    (isLocallyAnnihilated_of_torsionSheafProperty.{u, u + 1, 0} _ _
      (torsionSheafProperty_smallEtaleAbelianPullback B (s.inclusion i) F hTor) hfin)

variable (hXc : CompactSpace X.obj) (hXq : QuasiSeparatedSpace X.obj)
  (hYc : CompactSpace Y.obj) (hYq : QuasiSeparatedSpace Y.obj)
  (h093C : LocallyTorsionAbelianSheavesAreFilteredColimitsOfZModPresentations B Y)
  (h03S8 : AbelianShriekZModIsConstructible B)
  (h095N : ∀ G : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} ℤ),
    IsConstructibleModuleSheaf B X ℤ G →
      HasFiniteShriekPresentation.{u, 0, u + 1} B X ℤ (IsQCQSEtaleObject B X) G)

include hXc hXq hYc hYq

/-! ### The source's own route, through Stacks 03SA (2) -/

section ColimitRoute

include h093C h03S8 h095N

/-- **An abelian sheaf with constructible inverse image is a quotient of a constructible sheaf.**
Let `f : X ⟶ Y` be a surjective morphism of quasi-compact quasi-separated schemes and `ℱ` an
abelian sheaf on `Y_étale` whose inverse image along `f` is constructible. Then there is a
constructible abelian sheaf on `Y_étale` and an epimorphism from it onto `ℱ`.

No torsion hypothesis is imposed on `ℱ`: constructibility of `f⁻¹ℱ` makes `ℱ` torsion, by the
stalk criterion of
`AlgebraicGeometry.torsionSheafProperty_of_isConstructibleAbelianSheaf_pullback`. Stacks 03SA (2)
then writes `ℱ` as a filtered colimit of constructible sheaves, Stacks 09Z4 makes `f⁻¹ℱ` a
compact object, and `AlgebraicGeometry.exists_epi_of_isColimit_of_surjective_abelian` produces
the epimorphism.

Stacks 09Z4 is applied through its library form
`AlgebraicGeometry.isFinitelyPresentable_of_isConstructibleAbelianSheaf`, which takes Stacks 095N
for `ℤ`-modules as an input; here that input is the hypothesis `h095N`, and
`AlgebraicGeometry.hasFiniteShriekPresentation_of_isConstructibleModuleSheaf_int` of
`Constructible/IntegerShriekPresentation.lean` is a proof of it. Likewise `h03S8` is proved by
`AlgebraicGeometry.abelianShriekZModIsConstructible`. The hypothesis the library cannot supply is
`h093C`, `AlgebraicGeometry.LocallyTorsionAbelianSheavesAreFilteredColimitsOfZModPresentations`,
which it does not prove. -/
public theorem exists_epi_isConstructibleAbelianSheaf_of_pullback
    (hf : Function.Surjective (B.inclusion.map f).base)
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf B X ((smallEtaleAbelianPullbackFunctor B f).obj F)) :
    ∃ (G : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1}) (p : G ⟶ F),
      IsConstructibleAbelianSheaf B Y G ∧ Epi p := by
  have hxc : CompactSpace X.obj := hXc
  have hxq : QuasiSeparatedSpace X.obj := hXq
  have htors : torsionSheafProperty (SmallEtale.topology B Y.obj Y.property) F :=
    torsionSheafProperty_of_isConstructibleAbelianSheaf_pullback B f hf F hF
  obtain ⟨I, hI, hfilt, D, ι, ⟨hcolim⟩, hD⟩ :=
    exists_isFilteredColimit_isConstructibleAbelianSheaf_of_torsionSheafProperty B Y h093C h03S8
      hYc hYq F htors
  have hcompact : IsFinitelyPresentable.{u + 1}
      ((smallEtaleAbelianPullbackFunctor B f).obj F) :=
    isFinitelyPresentable_of_isConstructibleAbelianSheaf B X h095N _ hF
  obtain ⟨i, hi⟩ := exists_epi_of_isColimit_of_surjective_abelian B f hf D (Cocone.mk F ι)
    hcolim hcompact
  exact ⟨D.obj i, ι.app i, hD i, hi⟩

/-- **Stacks 095Q (2), the converse implication.** Let `f : X ⟶ Y` be a surjective morphism of
quasi-compact quasi-separated schemes and `ℱ` an abelian sheaf on `Y_étale` whose inverse image
`f⁻¹ℱ` is constructible. Then `ℱ` is constructible.

`AlgebraicGeometry.exists_epi_isConstructibleAbelianSheaf_of_pullback` applied to `ℱ` gives a
constructible `𝒢` with an epimorphism `p : 𝒢 ⟶ ℱ`; applied to the kernel of `p`, whose inverse
image is the kernel of a map between constructible sheaves, it gives a constructible `ℋ`
surjecting onto that kernel. Then `ℱ` is the cokernel of `ℋ ⟶ ker p ⟶ 𝒢` and so is constructible
by Stacks 03RZ (2).

This is the source's own argument, and it quantifies over `h093C`, `h03S8` and `h095N`. Of those,
`h03S8` and `h095N` are theorems of the library,
`AlgebraicGeometry.abelianShriekZModIsConstructible` and
`AlgebraicGeometry.hasFiniteShriekPresentation_of_isConstructibleModuleSheaf_int`; `h093C`,
`AlgebraicGeometry.LocallyTorsionAbelianSheavesAreFilteredColimitsOfZModPresentations`, is not,
and the library does not prove it. The same conclusion with none of the three is the backward
direction of `AlgebraicGeometry.isConstructibleAbelianSheaf_pullback_iff_of_surjective`, which
reaches it through the sheaves of `ℤ`-modules instead; that is where the tag 095Q (2) is
registered. -/
public theorem isConstructibleAbelianSheaf_of_isConstructibleAbelianSheaf_pullback
    (hf : Function.Surjective (B.inclusion.map f).base)
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf B X ((smallEtaleAbelianPullbackFunctor B f).obj F)) :
    IsConstructibleAbelianSheaf B Y F := by
  obtain ⟨G, p, hG, hp⟩ := exists_epi_isConstructibleAbelianSheaf_of_pullback B f hXc hXq hYc hYq
    h093C h03S8 h095N hf F hF
  have := hp
  have hGpull : IsConstructibleAbelianSheaf B X
      ((smallEtaleAbelianPullbackFunctor B f).obj G) :=
    isConstructibleFiniteSheaf_pullback B f G hG
  have hKpull : IsConstructibleAbelianSheaf B X
      ((smallEtaleAbelianPullbackFunctor B f).obj (kernel p)) :=
    (constructibleAbelianSheavesOn B X).prop_of_iso
      (PreservesKernel.iso (smallEtaleAbelianPullbackFunctor B f) p).symm
      ((constructibleAbelianSheavesOn B X).prop_kernel
        ((smallEtaleAbelianPullbackFunctor B f).map p) hGpull hF)
  obtain ⟨H, q, hH, hq⟩ := exists_epi_isConstructibleAbelianSheaf_of_pullback B f hXc hXq hYc hYq
    h093C h03S8 h095N hf (kernel p) hKpull
  have := hq
  have hcoker : IsColimit (CokernelCofork.ofπ (f := q ≫ kernel.ι p) p
      (by rw [Category.assoc, kernel.condition, comp_zero])) :=
    isCokernelEpiComp (c := CokernelCofork.ofπ p (kernel.condition p))
      (Abelian.epiIsCokernelOfKernel _ (limit.isLimit _)) q rfl
  exact (constructibleAbelianSheavesOn B Y).prop_of_iso
    ((colimit.isColimit _).coconePointUniqueUpToIso hcoker)
    ((constructibleAbelianSheavesOn B Y).prop_cokernel (q ≫ kernel.ι p) hH hG)

end ColimitRoute

/-! ### Stacks 095Q (2) -/

/-- **Stacks 095Q, part (2).** Let `f : X ⟶ Y` be a surjective morphism of quasi-compact and
quasi-separated schemes and let `ℱ` be an abelian sheaf on `Y_étale` — arbitrary, with no torsion
assumption. Then `ℱ` is constructible if and only if `f⁻¹ℱ` is constructible.

The forward implication is Stacks 095G, `AlgebraicGeometry.isConstructibleFiniteSheaf_pullback`,
and needs neither surjectivity of `f` nor quasi-compactness. The converse is carried out in the
category of sheaves of `ℤ`-modules, where Stacks 095Q is already unconditional:
`AlgebraicGeometry.isConstructibleModuleSheaf_pullback_iff_of_surjective`. Only the
quasi-compactness and quasi-separatedness of `X` and `Y`, which the source's statement assumes,
are hypotheses.

The passage between the two categories is the one place with content. Going out is immediate,
`AlgebraicGeometry.isConstructibleModuleSheaf_moduleCatIntEquivalence`, a finite abelian group
being a finitely generated `ℤ`-module; the module development is pinned to a Noetherian ring in
`Type (u + 1)`, so the descent happens at `ULift ℤ` and is transported back by
`AlgebraicGeometry.isConstructibleModuleSheaf_int_of_uliftIntRestrictScalars`. Coming back is
`AlgebraicGeometry.isConstructibleAbelianSheaf_of_isConstructibleModuleSheaf_int`, which needs
`ℱ` to be torsion — and that is exactly what the constructibility of `f⁻¹ℱ` supplies, through the
stalk criterion `AlgebraicGeometry.torsionSheafProperty_of_isConstructibleAbelianSheaf_pullback`.
Stacks 093C for torsion abelian sheaves is not used: the module form of Stacks 093C, which the
library proves, is what the descent above consumes. -/
@[stacks 095Q "part (2), abelian sheaves"]
public theorem isConstructibleAbelianSheaf_pullback_iff_of_surjective
    (hf : Function.Surjective (B.inclusion.map f).base)
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1}) :
    IsConstructibleAbelianSheaf B Y F ↔
      IsConstructibleAbelianSheaf B X ((smallEtaleAbelianPullbackFunctor B f).obj F) := by
  refine ⟨fun hF => isConstructibleFiniteSheaf_pullback B f F hF, fun hF => ?_⟩
  have hxc : CompactSpace X.obj := hXc
  have hxq : QuasiSeparatedSpace X.obj := hXq
  have hyc : CompactSpace Y.obj := hYc
  have hyq : QuasiSeparatedSpace Y.obj := hYq
  have hint : IsConstructibleModuleSheaf B X ℤ
      (((smallEtaleBaseChange B f).sheafPullback (ModuleCat.{u + 1} ℤ)
        (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B X.obj X.property)).obj
        ((Sheaf.coefficientEquivalence (SmallEtale.topology B Y.obj Y.property)
          AddCommGrpCat.moduleCatIntEquivalence.{u + 1}).functor.obj F)) :=
    isConstructibleModuleSheaf_of_iso B X ℤ
      ((Sheaf.sheafPullbackCoefficientIso (smallEtaleBaseChange B f)
        (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property)
        AddCommGrpCat.moduleCatIntEquivalence.{u + 1}).app F)
      (isConstructibleModuleSheaf_moduleCatIntEquivalence B X _ hF)
  have hulift : IsConstructibleModuleSheaf B X (ULift.{u + 1} ℤ)
      ((smallEtaleModulePullbackFunctor B (ULift.{u + 1} ℤ) f).obj
        ((Sheaf.coefficientEquivalence (SmallEtale.topology B Y.obj Y.property)
          ModuleCat.restrictScalarsUliftIntEquivalence.{u + 1, u + 1}).functor.obj
          ((Sheaf.coefficientEquivalence (SmallEtale.topology B Y.obj Y.property)
            AddCommGrpCat.moduleCatIntEquivalence.{u + 1}).functor.obj F))) :=
    isConstructibleModuleSheaf_of_iso B X (ULift.{u + 1} ℤ)
      ((Sheaf.sheafPullbackCoefficientIso (smallEtaleBaseChange B f)
        (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property)
        ModuleCat.restrictScalarsUliftIntEquivalence.{u + 1, u + 1}).app _)
      (isConstructibleModuleSheaf_uliftIntRestrictScalars B X _ hint)
  exact isConstructibleAbelianSheaf_of_isConstructibleModuleSheaf_int B Y F
    (isConstructibleModuleSheaf_int_of_uliftIntRestrictScalars B Y _
      (isConstructibleModuleSheaf_of_isConstructibleModuleSheaf_pullback B (ULift.{u + 1} ℤ) f
        hyc hyq hxc hxq hf _ hulift))
    (torsionSheafProperty_of_isConstructibleAbelianSheaf_pullback B f hf F hF)

end Descent

end AlgebraicGeometry

end
