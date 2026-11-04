module

public import StacksFrontier.AlgebraicGeometry.Flatness.RaynaudGrusonFlattening0815
public import StacksFrontier.AlgebraicGeometry.Modules.FinitePresentationPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.QuasicoherentCriteria

/-!
# The `U = ⊤` case of Raynaud–Gruson flattening

`StacksFrontier/AlgebraicGeometry/Flatness/RaynaudGrusonFlattening0815.lean` states Stacks tag 0815
as `AlgebraicGeometry.FinitePresentationHasModuleFlatteningBlowup` and proves the *flatness half*
of its conclusion in the region where the input module is already flat over the whole base. This
file completes that region to the full conclusion of tag 0815 — finite presentation of the strict
transform as well as flatness — and deduces the case `U = ⊤` of the tag.

## What this closes, and what it does not

`Stacks.Blowup.eq_top_of_disjoint_univ_support` says that the unit ideal sheaf is the *only*
`⊤`-admissible centre. So the result proved here,
`AlgebraicGeometry.hasModuleFlatteningBlowup_top`, is not a sub-region of the `U = ⊤` case of tag
0815: it **is** that case, in full, and
`AlgebraicGeometry.finitePresentationHasModuleFlatteningBlowup_of_ne_top` records that by
reducing `AlgebraicGeometry.FinitePresentationHasModuleFlatteningBlowup` to the range `U ≠ ⊤`,
with the `U = ⊤` branch of its proof discharged outright.

It is *not* tag 0815. Being a case split, the residual hypothesis `U ≠ ⊤` is logically equivalent
to the full statement, and **the case closed is the degenerate one** — but it does genuinely
narrow the class of instances rather than restate the conclusion. A separating instance that
`U = ⊤` excludes: let `k` be a field, `S = Spec k[t², t³]`,
`X = Spec k[t]`, `f` the normalization of the cuspidal curve and `ℱ = 𝒪_X`. Then `f` is finite
and surjective, so tag 0815 applies to it with `U = ∅`, while `k[t², t³] → k[t]` is finite
birational and not flat, so `ℱ` is flat over no open neighbourhood of the cusp and the hypothesis
`U = ⊤` excludes this `f` outright. All the content of tag 0815 lives in the range `U < ⊤`, where
the centre may be any finitely presented closed subscheme of the complement of `U`; nothing here
touches that range. The inputs of that range are listed under "The inputs" in
`RaynaudGrusonFlattening0815.lean`, corrected as described below.

## Main results

* `Stacks.Blowup.isFinitePresentation_strictTransformSheaf_top`: the strict transform of a module
  of finite presentation along the blowup with empty centre is of finite presentation as an
  `𝒪_{X ×_S S'}`-module — the conjunct tag 0815 actually states — and
  `Stacks.Blowup.isFinitePresentation_strictTransformModule_top`: the same after the further
  pullback to the strict transform `X'`, which is the weaker form
  `AlgebraicGeometry.HasModuleFlatteningBlowup` asks for.
* `AlgebraicGeometry.HasModuleFlatteningBlowup.of_isFlatOver`: the **full** conclusion of tag
  0815 — both conjuncts — for a module that is already of finite presentation and flat over the
  whole base. This upgrades `AlgebraicGeometry.HasModuleFlatteningBlowupFlat.of_isFlatOver`,
  which gives only the flatness conjunct.
* `AlgebraicGeometry.isFlatOver_resLE_top_iff` and
  `AlgebraicGeometry.isFinitePresentation_restrict_preimage_top_iff`: flatness over the base and
  finite presentation are unchanged by restricting to `f ⁻¹ᵁ ⊤`, which is what converts the
  hypotheses of tag 0815 at `U = ⊤` into hypotheses on `ℱ` itself.
* `AlgebraicGeometry.hasModuleFlatteningBlowup_top`: the case `U = ⊤` of tag 0815, and
  `AlgebraicGeometry.finitePresentationHasModuleFlatteningBlowup_of_ne_top`, which records it by
  reducing the tag to the range `U ≠ ⊤`.
* `AlgebraicGeometry.flat_resLE_top_iff`, `AlgebraicGeometry.hasFlatteningBlowup_top` and
  `AlgebraicGeometry.finitePresentationHasFlatteningBlowup_of_ne_top`: the same at the structure
  sheaf, i.e. for the morphism form of the tag.

## Implementation notes

**A recorded gap of `RaynaudGrusonFlattening0815.lean` is refuted here.** That file's "What
remains" section says that the repo "has tag 01B6 for finite TYPE of a module pullback … but
nothing for finite presentation", and gives that as the reason only the flatness half of the
empty-centre region is proved. Tag 01BQ — finite presentation of a module pullback along a
morphism of *ringed spaces* — is proved as
`Stacks.SheafOfModules.modulePullback_isFinitePresentation`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FinitePresentationPullback.lean:367`), and its
specialisation to schemes is `Stacks.Modules.isFinitePresentation_pullback`. That is the whole of
the first recorded gap.
The second one, `Stacks.Blowup.isIso_blowUpToBase_top`, is still open and is still only needed to
turn the `U = ⊤` case into an `iff`.

Flatness over the base is transported across `f ⁻¹ᵁ ⊤` by
`AlgebraicGeometry.isFlatOver_tfae` (tag 01U4): its third clause is flatness after `resLE` along
*some* open cover of the base together with *some* open cover of each preimage, and the
one-element covers `fun _ : PUnit ↦ ⊤` and `fun _ : PUnit ↦ f ⁻¹ᵁ ⊤` turn that clause into
exactly the hypothesis of tag 0815 at `U = ⊤`. Note that `List.TFAE.out` is 1-indexed on this
pin, so the clause is `.out 3 1`. The reverse implication is
`AlgebraicGeometry.isFlatOver_resLE`, so the two are recorded here as an `iff` and no consumer
can be weakened in either direction.

Finite presentation is transported the other way round, by reflecting it along the isomorphism
`(f ⁻¹ᵁ ⊤).ι`; that is `Stacks.Modules.isFinitePresentation_of_restrict_eq_top`.

## References

* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
* [Stacks Project, Tag 01BQ](https://stacks.math.columbia.edu/tag/01BQ)
* [Stacks Project, Tag 01U4](https://stacks.math.columbia.edu/tag/01U4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Blowup

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- A module isomorphic to the pullback of a module of finite presentation is of finite
presentation. -/
private theorem isFinitePresentation_of_iso_pullback {X Y : Scheme.{u}} (g : Y ⟶ X)
    {𝒢 : Y.Modules} (ℱ : X.Modules) [ℱ.IsFinitePresentation]
    (e : 𝒢 ≅ (Scheme.Modules.pullback g).obj ℱ) : 𝒢.IsFinitePresentation :=
  (SheafOfModules.isFinitePresentation Y.ringCatSheaf).prop_of_iso e.symm inferInstance

/-- **The empty-blowup region of Stacks 0815, finite-presentation half, in the tag's own
spelling.** Tag 0815 asserts that the strict transform `ℱ'` is of finite presentation *as an
`𝒪_{X ×_S S'}`-module*, that is, for `Stacks.Blowup.strictTransformSheaf`. Along the blowup in
the unit ideal sheaf that holds whenever `ℱ` is of finite presentation: the exceptional divisor
is empty, so nothing is divided out and the strict transform is the plain pullback of `ℱ`
(`Stacks.Blowup.strictTransformSheafTopIso`), and pullback preserves finite presentation by tag
01BQ.

This is the conjunct the tag page states.
`Stacks.Blowup.isFinitePresentation_strictTransformModule_top` below is its further pullback to
the closed subscheme `X' ⊆ X ×_S S'`, which is the weaker form that
`AlgebraicGeometry.HasModuleFlatteningBlowup` happens to ask for. -/
theorem isFinitePresentation_strictTransformSheaf_top (ℱ : X.Modules)
    [ℱ.IsFinitePresentation] :
    (strictTransformSheaf f (⊤ : S.IdealSheafData) ℱ).IsFinitePresentation :=
  isFinitePresentation_of_iso_pullback
    (blowUpPullbackToSource f (⊤ : S.IdealSheafData)) ℱ (strictTransformSheafTopIso f ℱ)

/-- **The empty-blowup region of Stacks 0815, finite-presentation half.** The strict transform
of a module of finite presentation along the blowup in the unit ideal sheaf is again of finite
presentation.

The strict transform there is a pullback twice over: the exceptional divisor is empty, so nothing
is divided out and the strict transform on `X ×_S S'` is the plain pullback of `ℱ`
(`Stacks.Blowup.isFinitePresentation_strictTransformSheaf_top`); and the strict transform of `X`
is the whole of `X ×_S S'`, so passing to it is another pullback. Both steps preserve finite
presentation by tag 01BQ. -/
theorem isFinitePresentation_strictTransformModule_top (ℱ : X.Modules)
    [ℱ.IsFinitePresentation] :
    (strictTransformModule f (⊤ : S.IdealSheafData) ℱ).IsFinitePresentation :=
  Stacks.Modules.isFinitePresentation_pullback
    (strictTransformι f (⊤ : S.IdealSheafData)) _
    (isFinitePresentation_strictTransformSheaf_top f ℱ)

end Stacks.Blowup

namespace AlgebraicGeometry

open Stacks.Blowup

variable {X S : Scheme.{u}}

/-- The inclusion of the preimage of the whole base is an isomorphism. -/
private theorem isIso_ι_preimage_top (f : X ⟶ S) : IsIso (f ⁻¹ᵁ (⊤ : S.Opens)).ι :=
  Stacks.Modules.isIso_ι_of_eq_top (by simp)

/-- **The region of Stacks 0815 where no blowup is needed, in full.** If the module `ℱ` is of
finite presentation and already flat over all of `S` then the blowup in the unit ideal sheaf
witnesses tag 0815's conclusion: its centre is empty, so it is `U`-admissible for every `U`, and
the strict transform along it is `ℱ` pulled back to `X ×_S S'`, which is both of finite
presentation and flat over `S'`.

This is the upgrade of `AlgebraicGeometry.HasModuleFlatteningBlowupFlat.of_isFlatOver` from the
flatness conjunct to both conjuncts; see the implementation notes above for the gap that made the
upgrade possible. -/
theorem HasModuleFlatteningBlowup.of_isFlatOver (f : X ⟶ S) (U : S.Opens) (ℱ : X.Modules)
    [ℱ.IsFinitePresentation] (hℱ : IsFlatOver f.toLRSHom.toShHom ℱ) :
    HasModuleFlatteningBlowup f U ℱ :=
  have _ : ℱ.IsQuasicoherent := Stacks.Modules.isQuasicoherent_of_isFinitePresentation ℱ
  ⟨⊤, finitePresentation_subschemeι_top, by simp,
    isFinitePresentation_strictTransformModule_top f ℱ,
    isFlatOver_strictTransformModule_top f ℱ hℱ⟩

/-- Flatness of a module over the base is unchanged by restricting to the preimage of the whole
base: the one-element covers `fun _ ↦ ⊤` of `S` and `fun _ ↦ f ⁻¹ᵁ ⊤` of that preimage turn the
third clause of `AlgebraicGeometry.isFlatOver_tfae` into the right-hand side. -/
theorem isFlatOver_resLE_top_iff (f : X ⟶ S) (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    IsFlatOver (f.resLE (⊤ : S.Opens) (f ⁻¹ᵁ (⊤ : S.Opens)) le_rfl).toLRSHom.toShHom
        (ℱ.restrict (f ⁻¹ᵁ (⊤ : S.Opens)).ι) ↔
      IsFlatOver f.toLRSHom.toShHom ℱ := by
  refine ⟨fun h ↦ ((isFlatOver_tfae f ℱ).out 3 1).mp ?_, fun h ↦ isFlatOver_resLE ℱ h _ _ le_rfl⟩
  refine ⟨PUnit.{u + 1}, fun _ ↦ (⊤ : S.Opens), ?_, fun _ ↦ ?_⟩
  · simp [IsOpenCover]
  · exact ⟨PUnit.{u + 1}, fun _ ↦ f ⁻¹ᵁ (⊤ : S.Opens), by simp, fun _ ↦ h⟩

/-- Finite presentation of a module is unchanged by restricting to the preimage of the whole
base, because `f ⁻¹ᵁ ⊤` is the whole source. -/
theorem isFinitePresentation_restrict_preimage_top_iff (f : X ⟶ S) (ℱ : X.Modules) :
    (ℱ.restrict (f ⁻¹ᵁ (⊤ : S.Opens)).ι).IsFinitePresentation ↔ ℱ.IsFinitePresentation := by
  have htop : f ⁻¹ᵁ (⊤ : S.Opens) = (⊤ : X.Opens) := by simp
  refine ⟨Stacks.Modules.isFinitePresentation_of_restrict_eq_top htop ℱ, fun h ↦ ?_⟩
  exact isFinitePresentation_of_iso_pullback _ ℱ
    ((Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ (⊤ : S.Opens)).ι).app ℱ)

/-- **The case `U = ⊤` of Stacks 0815.** When the open over which the module is already flat and
of finite presentation is the whole base, tag 0815 holds, and with no hypothesis at all on `f`,
on `X` or on `S` beyond those two.

By `Stacks.Blowup.eq_top_of_disjoint_univ_support` the unit ideal sheaf is the only
`⊤`-admissible centre, so this is the whole of the `U = ⊤` case and not a region inside it. -/
theorem hasModuleFlatteningBlowup_top (f : X ⟶ S) (ℱ : X.Modules)
    (hfp : (ℱ.restrict (f ⁻¹ᵁ (⊤ : S.Opens)).ι).IsFinitePresentation)
    (hflat : IsFlatOver (f.resLE (⊤ : S.Opens) (f ⁻¹ᵁ (⊤ : S.Opens)) le_rfl).toLRSHom.toShHom
      (ℱ.restrict (f ⁻¹ᵁ (⊤ : S.Opens)).ι)) :
    HasModuleFlatteningBlowup f (⊤ : S.Opens) ℱ := by
  have _ : ℱ.IsFinitePresentation :=
    (isFinitePresentation_restrict_preimage_top_iff f ℱ).mp hfp
  have _ : ℱ.IsQuasicoherent := Stacks.Modules.isQuasicoherent_of_isFinitePresentation ℱ
  exact HasModuleFlatteningBlowup.of_isFlatOver f ⊤ ℱ
    ((isFlatOver_resLE_top_iff f ℱ).mp hflat)

/-- **The statement of Stacks 0815 reduces to the range `U ≠ ⊤`.** Granted the tag for every
open other than the whole base, the tag holds; the case `U = ⊤` is discharged by
`AlgebraicGeometry.hasModuleFlatteningBlowup_top`.

The hypothesis differs from `AlgebraicGeometry.FinitePresentationHasModuleFlatteningBlowup` by
the single added conjunct `U ≠ ⊤` and nothing else, which is what makes this a record of the
`U = ⊤` case being closed rather than a restatement. **It is nevertheless logically equivalent to
that statement** — any case split is, once one case is proved — and the case closed is the
degenerate one: at `U = ⊤` the module is already flat and of finite presentation over all of `S`,
no blowup is available at all
(`Stacks.Blowup.eq_top_of_disjoint_univ_support`), and every instance of the tag with a
non-flat `ℱ` falls in the remaining range. See the module documentation for the cuspidal-curve
instance that the hypothesis `U = ⊤` excludes. -/
theorem finitePresentationHasModuleFlatteningBlowup_of_ne_top
    (H : ∀ {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) (ℱ : X.Modules) [CompactSpace X]
      [CompactSpace S] [QuasiSeparatedSpace S] [LocallyOfFinitePresentation f]
      [ℱ.IsQuasicoherent] [ℱ.IsFiniteType], U ≠ ⊤ → IsCompact (U : Set S) →
      (ℱ.restrict (f ⁻¹ᵁ U).ι).IsFinitePresentation →
      IsFlatOver (f.resLE U (f ⁻¹ᵁ U) le_rfl).toLRSHom.toShHom (ℱ.restrict (f ⁻¹ᵁ U).ι) →
      HasModuleFlatteningBlowup f U ℱ) :
    FinitePresentationHasModuleFlatteningBlowup.{u} := by
  intro X S f U ℱ hX hS hqsS hlfp hqc hft hcpt hfp hflat
  rcases eq_or_ne U ⊤ with rfl | hUtop
  · exact hasModuleFlatteningBlowup_top f ℱ hfp hflat
  · exact @H X S f U ℱ hX hS hqsS hlfp hqc hft hUtop hcpt hfp hflat

/-- Flatness of a morphism is unchanged by restricting to the whole base and its preimage: the
restriction is conjugate to `f` by the two isomorphisms `Scheme.topIso`. -/
theorem flat_resLE_top_iff (f : X ⟶ S) :
    Flat (f.resLE (⊤ : S.Opens) (f ⁻¹ᵁ (⊤ : S.Opens)) le_rfl) ↔ Flat f := by
  have _ := isIso_ι_preimage_top f
  have _ : IsIso (⊤ : S.Opens).ι := Stacks.Modules.isIso_ι_of_eq_top rfl
  have hcomp : (f ⁻¹ᵁ (⊤ : S.Opens)).ι ≫ f =
      f.resLE (⊤ : S.Opens) (f ⁻¹ᵁ (⊤ : S.Opens)) le_rfl ≫ (⊤ : S.Opens).ι :=
    (Scheme.Hom.resLE_comp_ι f le_rfl).symm
  have _ : MorphismProperty.RespectsIso (@Flat) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  constructor
  · intro h
    have h2 : Flat ((f ⁻¹ᵁ (⊤ : S.Opens)).ι ≫ f) := hcomp ▸ inferInstance
    exact (MorphismProperty.cancel_left_of_respectsIso (@Flat) _ _).mp h2
  · intro h
    have h2 : Flat (f.resLE (⊤ : S.Opens) (f ⁻¹ᵁ (⊤ : S.Opens)) le_rfl ≫ (⊤ : S.Opens).ι) :=
      hcomp ▸ inferInstance
    exact (MorphismProperty.cancel_right_of_respectsIso (@Flat) _ _).mp h2

/-- **The case `U = ⊤` of the morphism form of Stacks 0815.** A morphism that is already flat
over the whole base needs no blowup, and the unit ideal sheaf is the only `⊤`-admissible
centre. -/
theorem hasFlatteningBlowup_top (f : X ⟶ S)
    (hflat : Flat (f.resLE (⊤ : S.Opens) (f ⁻¹ᵁ (⊤ : S.Opens)) le_rfl)) :
    HasFlatteningBlowup f (⊤ : S.Opens) :=
  have _ : Flat f := (flat_resLE_top_iff f).mp hflat
  HasFlatteningBlowup.of_flat f ⊤

/-- **The morphism form of Stacks 0815 reduces to the range `U ≠ ⊤`**, by
`AlgebraicGeometry.hasFlatteningBlowup_top`. The same assessment as for
`AlgebraicGeometry.finitePresentationHasModuleFlatteningBlowup_of_ne_top` applies: the hypothesis
is logically equivalent to the conclusion and the case closed is the degenerate one. -/
theorem finitePresentationHasFlatteningBlowup_of_ne_top
    (H : ∀ {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) [CompactSpace X] [CompactSpace S]
      [QuasiSeparatedSpace S] [LocallyOfFinitePresentation f], U ≠ ⊤ → IsCompact (U : Set S) →
      Flat (f.resLE U (f ⁻¹ᵁ U) le_rfl) → HasFlatteningBlowup f U) :
    FinitePresentationHasFlatteningBlowup.{u} := by
  intro X S f U hX hS hqsS hlfp hcpt hflat
  rcases eq_or_ne U ⊤ with rfl | hUtop
  · exact hasFlatteningBlowup_top f hflat
  · exact @H X S f U hX hS hqsS hlfp hUtop hcpt hflat

end AlgebraicGeometry

end
