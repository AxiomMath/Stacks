module

public import StacksFrontier.AlgebraicGeometry.Locality.Diagonal

/-!
# `hy` at the diagonal: the last sheaf-side hypothesis of [Stacks, Tag 08S2]

`StacksDraft.AlgebraicGeometry.F3.LeibnizDerivation.Affine` reduces
[Stacks, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2) to one statement,
`IsIso (Stacks.LeibnizDerivation.kaehlerToConormal f V U hUV)` for `U` and `V` affine, and
`StacksFrontier.AlgebraicGeometry.Locality.Diagonal` narrows what that needs to two statements:
`hy` at the diagonal, and the module-structure step. Its "What is not done" section says of the
first that it reduces to

> `Stacks.LeibnizDerivation.deltaAt f U b` being the comorphism of `i.coborderRange.ι` applied to
> `p₂^♯ b − p₁^♯ b`, which is `AlgebraicGeometry.Scheme.Hom.appLE_comp` bookkeeping on the two
> projections.

**That is correct, and this file carries it out.** `hy` is discharged here for an *arbitrary*
immersion from the one ambient identity, and that identity is proved at the diagonal.

## Main results

* `Stacks.Tag08S2DiagonalHy.appLE_coborderRange_delta`: **the bookkeeping identity.** The
  comorphism of `(pullback.diagonal f).coborderRange.ι` from the ambient chart to
  `Stacks.LeibnizDerivation.chart f U` carries `p₂^♯ b - p₁^♯ b` to
  `Stacks.LeibnizDerivation.deltaAt f U b`. It is two applications of
  `AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE`, one per projection.
* `Stacks.Tag08S2DiagonalHy.hy_of_appLE_image`: **`hy` for a named section, at an arbitrary
  immersion.** The hypothesis
  `Stacks.Tag08S2Locality.conormalAffineSectionsIsoCotangent_apply_of_image` still carries follows
  from the single identity above. Nothing is affine, Noetherian, finite or quasi-compact, and no
  presentation data enters: the containment `V ≤ i.coborderRange` appears only inside
  `AlgebraicGeometry.Scheme.Opens.isoOfLE`, which is proof-irrelevant in it, so this applies to the
  `Stacks.Conormal.AffineCotangent.le_coborderRange_of_isoSpecQuotient` proof the engine uses.
* `Stacks.Tag08S2DiagonalHy.delta_mem_ker_diagAppLE`: **the ring-level membership.**
  `p₂^♯ b - p₁^♯ b` lies in `RingHom.ker (Stacks.DiagonalChart.diagAppLE f U).hom`, the ideal of
  the diagonal in the chart — immediate from `Stacks.DiagonalChart.fst_appLE_comp_diagAppLE` and
  `snd_appLE_comp_diagAppLE`, both of which are the identity. This names the element of the
  presentation ideal the generator formula is read at.
* `Stacks.Tag08S2DiagonalHy.image_restrictIdealSheafIso'_top`,
  `topIso_inv_comp_isoOfLE_appTop`, `appLE_top_top`, `opens_ι_appLE_top`: the four transport
  lemmas the reduction of `hy` to that identity goes through.

## Route

`hy` compares two elements of `Γ((i.coborderRange.ι ⁻¹ᵁ V).toScheme, ⊤)`. Both are
`AlgebraicGeometry.Scheme.Opens.topIso` images of ambient sections:

* the left by `image_restrictIdealSheafIso'_top`, which is
  `Stacks.Conormal.Tag01R3Generators.image_restrictIdealSectionTop` read at the `⊤` spelling that
  `hy` produces rather than through `zSec` at `i.coborderRange.ι ⁻¹ᵁ V` — the two differ by an
  `eqToHom`, and `Stacks.Conormal.Locality.restrictIdealSheafIso'_app_ι` is stated at an arbitrary
  open, so it is cheaper to redo than to transport;
* the right by `image_restrictIdealSectionTop` itself, followed by
  `topIso_inv_comp_isoOfLE_appTop`, which identifies the comorphism of
  `AlgebraicGeometry.Scheme.Opens.isoOfLE` on global sections with the `appLE` of the larger
  open's inclusion.

So the whole content of `hy` is the ambient identity, which at the diagonal is
`appLE_coborderRange_delta`.

## What is not done

* **No clause of [Stacks, Tag 08S2] or of [Stacks, Tag 01R3] is discharged, and no `stacks`
  attribute is attached.** Nothing here is an assertion of either tag.
* **The assembly is owed, and the obstruction is the INSTANTIATION, not the mathematics.** Feeding
  `hy_of_appLE_image` and `delta_mem_ker_diagAppLE` into
  `Stacks.Tag08S2Locality.conormalAffineSectionsIsoCotangent_apply_of_image` at the diagonal — with
  the presentation data of `Stacks.DiagonalPresentation.exists_diagonalPresentation_ker` and the
  section of `Stacks.Tag08S2Locality.exists_diagonalIdealSection_ambient` — is a single `refine`,
  and its *proof* goes through; what fails is elaborating the **statement**, which times out at
  `whnf` against the 200000-heartbeat default. Three spellings all time out
  identically: the presentation data existentially quantified, taken as parameters, and the
  isomorphism bound under an `∃` with only its module type written out.

  **The cause is not the statement's size.** The same generator formula stated
  at a *generic* immersion `i : Z ⟶ X` and a generic affine open `V : X.Opens` elaborates with no
  compiler option at all. What is expensive is substituting `i := pullback.diagonal f` and
  `V := Stacks.LeibnizDerivation.ambientChart f U`: the chart is an intersection of two pullback
  preimages and the diagonal is a limit cone, so typing the quotient generator as an element of the
  pushforward sections over the chart drives `whnf` through `getLimitCone`. **So the fix is to keep
  the generic statement and instantiate it only in an application, where the expected type guides
  unification** — not to golf the diagonal spelling, and not to raise the budget.

* **The module-structure step is untouched.** `conormalAffineSectionsIsoCotangent` is
  `Γ(X ×_S X, ambientChart f U)`-linear while `Stacks.LeibnizDerivation.kaehlerToConormal` lives in
  `ModuleCat Γ(X, U)`; `Stacks.LeibnizDerivation.surjective_diagRes_appTop` is the bridge and is
  proved.

## Overlap to be deduplicated

`hy` was derived independently and concurrently in an untracked scratch file of the
[Stacks, Tag 01R3] part (2) effort, as `Stacks.Tag01R3PartTwo.hy_of_names`, together with
counterparts of three of the four transport lemmas below. The two `hy` lemmas are not equivalent:
`hy_of_appLE_image` here takes only `V ≤ i.coborderRange` and **no presentation data**, so it holds
with no affineness hypothesis anywhere, while that one carries `hV`, `I`, `e` and `he`. Whichever
survives, the weaker hypotheses are the ones to keep.

## Two restated lemmas

`Stacks.Smooth.opens_ι_appLE_top`
(`StacksFrontier/AlgebraicGeometry/Smooth/LiftTorsor.lean:128`) and
`Stacks.AffineAlgebraEquivalence2.appLE_top_top`
(`StacksFrontier/AlgebraicGeometry/AffineAlgebraEquivalence2/AffineOpenHom.lean:58`) are both
sorry-free and `public`, and **neither is reachable from the conormal development's import
level** — `Unknown identifier` on both. They are restated here with their own proofs rather than
re-derived; moving them up the import graph would delete these two declarations.

## Universe situation

A single universe `u`, as in the tagged statements.

## Vocabulary

No declaration of the tagged statements is restated; everything is stated over the
repository's own names.

## References

* [Stacks Project, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Tag08S2DiagonalHy

variable {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens)

/-- The comorphism of the coborder inclusion carries the ambient difference to `deltaAt`. -/
theorem appLE_coborderRange_delta (b : Γ(X, U)) :
    ((pullback.diagonal f).coborderRange.ι.appLE
        (Stacks.LeibnizDerivation.ambientChart f U)
        (Stacks.LeibnizDerivation.chart f U)
        (Stacks.LeibnizDerivation.coborderRange_ι_preimage_ambientChart f U).ge).hom
      (((pullback.snd f f).appLE U (Stacks.LeibnizDerivation.ambientChart f U)
          (Stacks.LeibnizDerivation.ambientChart_le_snd_preimage f U)).hom b -
        ((pullback.fst f f).appLE U (Stacks.LeibnizDerivation.ambientChart f U)
          (Stacks.LeibnizDerivation.ambientChart_le_fst_preimage f U)).hom b) =
      Stacks.LeibnizDerivation.deltaAt f U b := by
  rw [map_sub, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  rfl

/-- **The image in the structure sheaf of the `⊤`-shaped transport of a section of an ideal
sheaf.** This is `Stacks.Conormal.Tag01R3Generators.image_restrictIdealSectionTop` read at the
spelling `hy` produces: the section is carried by restriction to `O.ι ''ᵁ ⊤` and then by
`restrictIdealSheafIso'` at `⊤`, rather than through `zSec` at `O.ι ⁻¹ᵁ O`. -/
theorem image_restrictIdealSheafIso'_top {A B : Scheme.{u}} (g : A ⟶ B) (O : B.Opens)
    (y : (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom).val.obj (.op O)) :
    ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom (g ∣_ O).toLRSHom.toShHom))).val.app (.op ⊤)).hom
        (((Stacks.Conormal.Restriction.restrictIdealSheafIso' g O).hom.val.app (.op ⊤)).hom
          (((Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom).val.map
            (homOfLE (Scheme.Opens.ι_image_top O).le).op).hom y)) =
      O.topIso.inv.hom ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom g.toLRSHom.toShHom))).val.app (.op O) y) := by
  refine Eq.trans (Stacks.Conormal.Locality.restrictIdealSheafIso'_app_ι g O ⊤ _) ?_
  refine Eq.trans (congrArg (O.ι.appIso ⊤).hom
    (PresheafOfModules.naturality_apply
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom g.toLRSHom.toShHom))).val
      (homOfLE (Scheme.Opens.ι_image_top O).le).op y)) ?_
  refine Eq.trans (congrArg (O.ι.appIso ⊤).hom
    (Stacks.Conormal.Locality.unitModule_val_map
      (Scheme.Opens.ι_image_top O).le _)) ?_
  rw [Scheme.Opens.ι_appIso]
  rfl

/-- **The global sections of a morphism, in the form `appLE ⊤ ⊤`.** The residual restriction map
is a map between two copies of `⊤`, and the homs of a poset category are a subsingleton, so it is
the identity. -/
theorem appLE_top_top {A B : Scheme.{u}} (t : A ⟶ B) (e : (⊤ : A.Opens) ≤ t ⁻¹ᵁ ⊤) :
    t.appLE ⊤ ⊤ e = t.appTop :=
  have h : A.presheaf.map (homOfLE e).op = 𝟙 Γ(A, ⊤) :=
    Eq.trans (congrArg A.presheaf.map
      (Subsingleton.elim (homOfLE e).op (𝟙 (Opposite.op (⊤ : A.Opens)))))
      (A.presheaf.map_id _)
  Eq.trans (congrArg (fun k ↦ t.appTop ≫ k) h) (Category.comp_id t.appTop)

/-- **`AlgebraicGeometry.Scheme.Opens.topIso` is the `appLE` of the open immersion.** This is
`Stacks.Smooth.opens_ι_appLE_top` (`StacksFrontier/AlgebraicGeometry/Smooth/LiftTorsor.lean:128`),
which has this very proof but sits at an import level the conormal development does
not reach; it is restated here rather than re-derived. -/
theorem opens_ι_appLE_top {Y : Scheme.{u}} (W : Y.Opens) :
    W.ι.appLE W ⊤ (le_of_eq W.ι_preimage_self.symm) = W.topIso.inv := by
  simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
  congr 1

/-- **The comorphism of `AlgebraicGeometry.Scheme.Opens.isoOfLE` on global sections is the
`appLE` of the larger open's inclusion.** Both sides are the `appLE` from the ambient open `W`
to the top open of `(C.ι ⁻¹ᵁ W).toScheme`, read along the two sides of
`AlgebraicGeometry.Scheme.Opens.isoOfLE_hom_ι`; `appLE` carries a containment proof mentioning
the morphism, so the transport is `Stacks.DiagonalConormal.appLE_congr` and not `rw`. -/
theorem topIso_inv_comp_isoOfLE_appTop {Y : Scheme.{u}} {W C : Y.Opens} (h : W ≤ C) :
    W.topIso.inv ≫ (Scheme.Opens.isoOfLE h).hom.appTop =
      C.ι.appLE W (C.ι ⁻¹ᵁ W) le_rfl ≫ (C.ι ⁻¹ᵁ W).topIso.inv := by
  rw [← opens_ι_appLE_top W, ← opens_ι_appLE_top (C.ι ⁻¹ᵁ W),
    ← appLE_top_top (Scheme.Opens.isoOfLE h).hom le_top]
  refine Eq.trans (Scheme.Hom.appLE_comp_appLE _ W.ι W ⊤ ⊤ W.ι_preimage_self.ge le_top) ?_
  refine Eq.trans
    (Stacks.DiagonalConormal.appLE_congr (Scheme.Opens.isoOfLE_hom_ι h) W ⊤ _
      (C.ι ⁻¹ᵁ W).ι_preimage_self.ge) ?_
  exact (Scheme.Hom.appLE_comp_appLE (C.ι ⁻¹ᵁ W).ι C.ι W (C.ι ⁻¹ᵁ W) ⊤ le_rfl
    (C.ι ⁻¹ᵁ W).ι_preimage_self.ge).symm

/-- **The engine's hypothesis `hy`, for two sections named through the structure sheaf.** For an
immersion `i : Z ⟶ Y` and an open `V` of `Y` inside the coborder neighbourhood, the comparison
`Stacks.Tag08S2Locality.conormalAffineSectionsIsoCotangent_apply_of_image` asks for is implied by
the single ambient identity: the comorphism of `i.coborderRange.ι` carries the image of `x₀` in
the structure sheaf to the image of `y₀`.

Both sides reduce to `AlgebraicGeometry.Scheme.Opens.topIso` of an ambient section —
the left by `image_restrictIdealSheafIso'_top`, the right by
`Stacks.Conormal.Tag01R3Generators.image_restrictIdealSectionTop` followed by
`topIso_inv_comp_isoOfLE_appTop` — so the whole content is `hxy`. Nothing is affine, Noetherian
or quasi-compact, and no presentation data is used: the containment proof enters only through
`AlgebraicGeometry.Scheme.Opens.isoOfLE`, which is proof-irrelevant in it. -/
theorem hy_of_appLE_image {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsImmersion i] (V : Y.Opens)
    (hVC : V ≤ i.coborderRange)
    (y₀ : (Stacks.ClosedImmersion.idealSheaf i.liftCoborder.toLRSHom.toShHom).val.obj
      (.op (i.coborderRange.ι ⁻¹ᵁ V)))
    (x₀ : (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom).val.obj (.op V))
    (hxy : (i.coborderRange.ι.appLE V (i.coborderRange.ι ⁻¹ᵁ V) le_rfl).hom
        (((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom i.toLRSHom.toShHom))).val.app (.op V)).hom x₀) =
      ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom i.liftCoborder.toLRSHom.toShHom))).val.app
          (.op (i.coborderRange.ι ⁻¹ᵁ V))).hom y₀) :
    ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom
            (i.liftCoborder ∣_ (i.coborderRange.ι ⁻¹ᵁ V)).toLRSHom.toShHom))).val.app
            (.op ⊤)).hom
          (((Stacks.Conormal.Restriction.restrictIdealSheafIso' i.liftCoborder
              (i.coborderRange.ι ⁻¹ᵁ V)).hom.val.app (.op ⊤)).hom
            (((Stacks.ClosedImmersion.idealSheaf
              i.liftCoborder.toLRSHom.toShHom).val.map
              (homOfLE (Scheme.Opens.ι_image_top
                (i.coborderRange.ι ⁻¹ᵁ V)).le).op).hom y₀)) =
        ((SheafOfModules.unitToPushforwardObjUnit (structureSheafHom
            (Scheme.Opens.isoOfLE hVC).hom.toLRSHom.toShHom)).val.app
            (.op ⊤)).hom
          (((kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom
            (i ∣_ V).toLRSHom.toShHom))).val.app (.op ⊤)).hom
            (Stacks.Conormal.Tag01R3Generators.restrictIdealSectionTop i V x₀)) := by
  refine Eq.trans (image_restrictIdealSheafIso'_top i.liftCoborder
    (i.coborderRange.ι ⁻¹ᵁ V) y₀) ?_
  refine Eq.trans (congrArg (i.coborderRange.ι ⁻¹ᵁ V).topIso.inv.hom hxy.symm) ?_
  have key := topIso_inv_comp_isoOfLE_appTop hVC
  have hz : ∀ z : Γ(Y, V),
      ((Scheme.Opens.isoOfLE hVC).hom.appTop).hom (V.topIso.inv.hom z) =
        (i.coborderRange.ι ⁻¹ᵁ V).topIso.inv.hom
          ((i.coborderRange.ι.appLE V (i.coborderRange.ι ⁻¹ᵁ V) le_rfl).hom z) := fun z =>
    ((CommRingCat.comp_apply _ _ z).symm.trans (congr($key z))).trans
      (CommRingCat.comp_apply _ _ z)
  rw [Stacks.Conormal.Tag01R3Generators.image_restrictIdealSectionTop i V x₀]
  exact (hz _).symm

/-- **`p₂^♯ b - p₁^♯ b` lies in the ideal of the diagonal in the ambient chart.** Both projections
retract the diagonal, so `Stacks.DiagonalChart.diagAppLE` sends each lift of `b` back to `b` and
the difference to zero. This names the element of the presentation ideal that the generator
formula of [Stacks, Tag 08S2] is read at. -/
theorem delta_mem_ker_diagAppLE (b : Γ(X, U)) :
    ((pullback.snd f f).appLE U (Stacks.LeibnizDerivation.ambientChart f U)
        (Stacks.LeibnizDerivation.ambientChart_le_snd_preimage f U)).hom b -
      ((pullback.fst f f).appLE U (Stacks.LeibnizDerivation.ambientChart f U)
        (Stacks.LeibnizDerivation.ambientChart_le_fst_preimage f U)).hom b ∈
      RingHom.ker (Stacks.DiagonalChart.diagAppLE f U).hom := by
  rw [RingHom.mem_ker, map_sub, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    Stacks.DiagonalChart.snd_appLE_comp_diagAppLE,
    Stacks.DiagonalChart.fst_appLE_comp_diagAppLE, sub_self]

end Stacks.Tag08S2DiagonalHy

end
