module

public import StacksFrontier.AlgebraicGeometry.AffineStageDescent.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.ProperImageSystemModels
public import StacksFrontier.AlgebraicGeometry.ProperLimitStage.AffineModel
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A separated model of a morphism over the Noetherian approximation of an affine base

`StacksFrontier/AlgebraicGeometry/AffineStageDescent/Basic.lean` writes a scheme of finite
presentation over `Spec R` as the base change of a scheme of finite presentation over `Spec ℤ[i]`
for some finite subset `i` of `R`, by [Stacks, Tag 01ZM] part (1).
`StacksFrontier/AlgebraicGeometry/ProperLimitStage/AffineModel.lean` turns such a model into a
*proper* model over a later stage, by [Stacks, Tag 081F] with Chow's lemma discharged over the
Noetherian stage, but it asks for the model to be **separated** and does not produce one.

This file produces one. [Stacks, Tag 01ZQ] says that a morphism over a stage which is separated
after base change to the limit is separated after base change to some later stage, so it suffices
to replace the model of Tag 01ZM part (1) by its base change to the stage that Tag 01ZQ supplies:
the base change is again of finite presentation, and the limit is unchanged.

The two descents are stated at different spellings — Tag 01ZQ speaks of a *morphism* of schemes
over a stage and asks for properties of its left component, while Tag 01ZM part (1) delivers an
*object* of a category of schemes over a stage — and the translation between them is the one
already recorded for the image system of a good diagram
(`AlgebraicGeometry.overPullback_map_terminal_iff`,
`AlgebraicGeometry.prop_of_overIso`, `AlgebraicGeometry.overPullbackObj_shiftIso`), applied here
at the morphism `Xᵢ ⟶ Over.mk (𝟙 (Spec ℤ[i]))` to the terminal object. Nothing new is needed for
it.

## Main results

* `AlgebraicGeometry.finitePresentation_overPullbackObj`: the structure morphism of a base change
  of an object of finite presentation over the base is of finite presentation.
* `AlgebraicGeometry.exists_isSeparated_overPullback_of_isLimit`: Tag 01ZQ for the structure
  morphism of an object over a stage, rather than for a morphism of such objects.
* `AlgebraicGeometry.exists_isProper_overPullbackObj_of_isLimit_of_isNoetherian`: the same
  translation for [Stacks, Tag 081F] over a Noetherian stage.
* `AlgebraicGeometry.exists_isProper_finitePresentation_model_of_isLimit`: **a proper morphism of
  finite presentation over a cofiltered limit of Noetherian schemes is the base change of a proper
  morphism of finite presentation over a stage**, isomorphism included.
* `AlgebraicGeometry.exists_isSeparated_finitePresentation_baseChange_specAdjoinFinsetDiagram`: a
  separated scheme of finite presentation over `Spec R` is the base change of a *separated* scheme
  of finite presentation over `Spec ℤ[i]` for some finite `i ⊆ R`.
* `AlgebraicGeometry.exists_isProper_model_baseChange_specAdjoinFinsetDiagram`: the model theorem
  at the Noetherian approximation of `Spec R`.
* `AlgebraicGeometry.exists_isProper_finitePresentation_baseChange_of_isAffine`: **the same over
  an arbitrary affine base**, which is the first move of the limit-descent paragraph of
  [Stacks, Tag 0E7D] — it reduces that paragraph to an affine *Noetherian* base.

## Implementation notes

No Stacks attribute is attached to any of these. Tag 01ZQ is already carried by
`AlgebraicGeometry.exists_isSeparated_baseChange_of_isLimit`, whose statement is the tag's own; the
first two results below are that theorem at a different spelling and at one particular system, and
a second attribute would put one tag on two unidentified constants. Tag 081F is withheld for the
reason `StacksFrontier/AlgebraicGeometry/ProperLimitStage/NoetherianChow.lean` records: Chow's
lemma is available only over a Noetherian base, [Stacks, Tag 0200], and not over the
quasi-compact quasi-separated base of [Stacks, Tag 0202].

**A model theorem that drops the isomorphism cannot be used, and this file used to drop it.**
`AlgebraicGeometry.exists_isProper_model_of_finitePresentation_specAdjoinFinsetDiagram` takes the
isomorphism `X ≅ Xᵢ ×_{Spec ℤ[i]} Spec R` of Tag 01ZM part (1) as a hypothesis, consumes it to
move properness, and does not return it; the earlier form of
`AlgebraicGeometry.exists_isProper_model_baseChange_specAdjoinFinsetDiagram` inherited that and so
produced a proper scheme over a stage with nothing relating it to `X`. Every consumer of the
limit-descent argument computes on `X` *through* the model, so the isomorphism is the part that
makes the statement usable, and it is now in the conclusion of all three model theorems. The
weaker statement is recoverable from the stronger one at the identity transition, so nothing was
lost by the change.

**No system of base changes has to be constructed.** Separatedness at a finite stage is an
eventual statement, and the absolute form of that statement, [Stacks, Tag 086Q], would need the
base changes of the model along the transitions to be exhibited as an inverse system with limit
the source over `Spec R`. Tag 01ZQ is that statement for a morphism over a varying stage and
needs none of it; it is applied here to the morphism from the model to the terminal object, whose
left component is the model's own structure morphism.

`AlgebraicGeometry.exists_isSeparated_overPullback_of_isLimit` places no smallness hypothesis on
the index category, because its morphisms are required to live in the universe of its objects and
`CategoryTheory.EssentiallySmall` is then found by instance search. That is the shape in which Tag
01ZQ is stated, and it is the shape the system of the finitely generated subalgebras of a ring
has.

The separatedness hypothesis of the last two results is the one place where a morphism property of
the *limit* is used, and it is free in the application: a proper morphism is separated, so the
composite below asks only that the morphism over `Spec R` be proper and of finite presentation —
which is exactly what [Stacks, Tag 09ZR] delivers.

## References

* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 01ZQ](https://stacks.math.columbia.edu/tag/01ZQ)
* [Stacks Project, Tag 01TS](https://stacks.math.columbia.edu/tag/01TS)
* [Stacks Project, Tag 081F](https://stacks.math.columbia.edu/tag/081F)
* [Stacks Project, Tag 0E7D](https://stacks.math.columbia.edu/tag/0E7D)
* [Stacks Project, Tag 0EX4](https://stacks.math.columbia.edu/tag/0EX4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

universe v u

/-- **Finite presentation of a base change, in the object spelling.** If the structure morphism of
`Z : CategoryTheory.Over S` is of finite presentation, so is the structure morphism of its base
change along `b : T ⟶ S`. -/
lemma finitePresentation_overPullbackObj {S T : Scheme.{u}} (b : T ⟶ S) (Z : Over S)
    (hZ : FinitePresentation Z.hom) : FinitePresentation ((Over.pullback b).obj Z).hom :=
  FinitePresentation.of_isPullback (IsPullback.of_hasPullback Z.hom b) hZ

/-- **Separatedness descends to a finite stage, for the structure morphism of an object over a
stage.** Let `D` be a cofiltered inverse system of quasi-compact quasi-separated schemes with
affine transition morphisms and limit cone `c`, and let `Z` be a quasi-compact quasi-separated
scheme over the stage `D.obj i₀`. If the base change of `Z` to the limit is separated over the
limit, then the base change of `Z` to `D.obj i` is separated over `D.obj i` for some later stage
`i`.

This is [Stacks, Tag 01ZQ], `AlgebraicGeometry.exists_isSeparated_baseChange_of_isLimit`, applied
to the morphism from `Z` to the terminal object `Over.mk (𝟙 (D.obj i₀))`, whose left component is
the structure morphism of `Z`. -/
theorem exists_isSeparated_overPullback_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (Z : Over (D.obj i₀))
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [CompactSpace (D.obj i₀)] [QuasiSeparatedSpace (D.obj i₀)]
    [CompactSpace Z.left] [QuasiSeparatedSpace Z.left]
    [IsSeparated ((Over.pullback (c.π.app i₀)).obj Z).hom] :
    ∃ (i : I) (g : i ⟶ i₀), IsSeparated ((Over.pullback (D.map g)).obj Z).hom := by
  let t : Z ⟶ Over.mk (𝟙 (D.obj i₀)) := Over.homMk Z.hom
  let _ : CompactSpace (Over.mk (𝟙 (D.obj i₀))).left :=
    inferInstanceAs (CompactSpace (D.obj i₀))
  let _ : QuasiSeparatedSpace (Over.mk (𝟙 (D.obj i₀))).left :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj i₀))
  let _ : IsSeparated ((Over.pullback (c.π.app i₀)).map t).left :=
    (overPullback_map_terminal_iff (@IsSeparated) _ Z).mpr ‹_›
  obtain ⟨i, g, hsep⟩ :=
    exists_isSeparated_baseChange_of_isLimit D c i₀ Z (Over.mk (𝟙 (D.obj i₀))) t hc
  exact ⟨i, g, (overPullback_map_terminal_iff (@IsSeparated) _ Z).mp hsep⟩

/-- **Properness descends to a finite stage, for the structure morphism of an object over a
stage.** Let `D` be a cofiltered inverse system with affine transition morphisms and limit cone
`c`, let the stage `D.obj i₀` be Noetherian and quasi-separated, and let `Xᵢ` be separated and of
finite presentation over it. If the base change of `Xᵢ` to the limit is proper over the limit,
then the base change of `Xᵢ` to `D.obj i` is proper over `D.obj i` for some later stage `i`.

This is [Stacks, Tag 081F] with Chow's lemma discharged over the Noetherian stage,
`AlgebraicGeometry.exists_isProper_baseChange_of_isLimit_of_isNoetherian`, applied to the morphism
from `Xᵢ` to the terminal object `Over.mk (𝟙 (D.obj i₀))` and read through
`AlgebraicGeometry.overPullback_map_terminal_iff` — the same object-versus-morphism translation
that `AlgebraicGeometry.exists_isSeparated_overPullback_of_isLimit` performs for Tag 01ZQ. The two
compactness hypotheses that theorem places on the source are supplied by finite presentation over
a quasi-compact quasi-separated stage.

`CompactSpace (D.obj i₀)` is deliberately absent: it is implied by `IsNoetherian (D.obj i₀)`, and
stating both makes `CategoryTheory.linter.overlappingInstances` fire. -/
theorem exists_isProper_overPullbackObj_of_isLimit_of_isNoetherian
    {I : Type v} [Category.{v} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (Xᵢ : Over (D.obj i₀)) (hXᵢ : FinitePresentation Xᵢ.hom) [IsSeparated Xᵢ.hom]
    [QuasiSeparatedSpace (D.obj i₀)] [IsNoetherian (D.obj i₀)]
    [IsProper ((Over.pullback (c.π.app i₀)).obj Xᵢ).hom] :
    ∃ (i : I) (hi : i ⟶ i₀), IsProper ((Over.pullback (D.map hi)).obj Xᵢ).hom := by
  have hlfp : LocallyOfFinitePresentation Xᵢ.hom := hXᵢ.1
  have hqc : QuasiCompact Xᵢ.hom := hXᵢ.2.1
  have hqs : QuasiSeparated Xᵢ.hom := hXᵢ.2.2
  have hcs : CompactSpace Xᵢ.left := QuasiCompact.compactSpace_of_compactSpace Xᵢ.hom
  have hqss : QuasiSeparatedSpace Xᵢ.left := quasiSeparatedSpace_of_quasiSeparated Xᵢ.hom
  have hqsY : QuasiSeparatedSpace (Over.mk (𝟙 (D.obj i₀))).left :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj i₀))
  have hnY : IsNoetherian (Over.mk (𝟙 (D.obj i₀))).left :=
    inferInstanceAs (IsNoetherian (D.obj i₀))
  let t : Xᵢ ⟶ Over.mk (𝟙 (D.obj i₀)) := Over.homMk Xᵢ.hom
  have hlft : LocallyOfFiniteType t.left := inferInstanceAs (LocallyOfFiniteType Xᵢ.hom)
  have hsepf : IsSeparated t.left := inferInstanceAs (IsSeparated Xᵢ.hom)
  have hmap : IsProper ((Over.pullback (c.π.app i₀)).map t).left :=
    (overPullback_map_terminal_iff (@IsProper) _ Xᵢ).mpr ‹_›
  obtain ⟨i, hi, hprop⟩ :=
    exists_isProper_baseChange_of_isLimit_of_isNoetherian D c hc i₀ Xᵢ
      (Over.mk (𝟙 (D.obj i₀))) t
  exact ⟨i, hi, (overPullback_map_terminal_iff (@IsProper) _ Xᵢ).mp hprop⟩

/-- **A proper morphism of finite presentation over a cofiltered limit of Noetherian schemes has a
proper model of finite presentation over a stage, and the source is its base change.** Let `D` be
a cofiltered inverse system of Noetherian quasi-separated schemes with affine transition
morphisms and limit cone `c`, and let `X` be proper and of finite presentation over `c.pt`. Then
there are a stage `j` and a scheme `Xⱼ` over `D.obj j` which is proper and of finite presentation
over that stage, together with an isomorphism `X ≅ (Over.pullback (c.π.app j)).obj Xⱼ` over
`c.pt`.

This is the composite the limit-descent paragraph of [Stacks, Tag 0E7D] opens with. [Stacks, Tag
01ZM] part (1) produces a model of finite presentation; [Stacks, Tag 01ZQ] in the form
`AlgebraicGeometry.exists_isSeparated_overPullback_of_isLimit` makes it separated at a later
stage; [Stacks, Tag 081F] in the form
`AlgebraicGeometry.exists_isProper_overPullbackObj_of_isLimit_of_isNoetherian` then makes it
proper at a later stage still. Each replacement of the model by its base change along a transition
keeps finite presentation, by `AlgebraicGeometry.finitePresentation_overPullbackObj`, and keeps
the isomorphism with `X`, by `AlgebraicGeometry.overPullbackObj_shiftIso`.

**The isomorphism is part of the conclusion, and that is the point of this statement.** A
consumer of the limit-descent argument needs to compute on `X` through the model, so a theorem
that produces a proper model and forgets how `X` sits over it cannot be used at all; see the
implementation notes. -/
@[ega "IV 8.1.1" "special case", sga "3 VIB 10.0" "(ii), special case"]
theorem exists_isProper_finitePresentation_model_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)] [∀ i : I, IsNoetherian (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    (X : Over c.pt) [IsProper X.hom] (hX : FinitePresentation X.hom) :
    ∃ (j : I) (Xⱼ : Over (D.obj j)), FinitePresentation Xⱼ.hom ∧ IsProper Xⱼ.hom ∧
      Nonempty (X ≅ (Over.pullback (c.π.app j)).obj Xⱼ) := by
  obtain ⟨i, Xᵢ, hXᵢ, ⟨e⟩⟩ :=
    LimitDescent.exists_model_of_finitePresentation_of_essentiallySmall D c hc X hX
  have hlfp : LocallyOfFinitePresentation Xᵢ.hom := hXᵢ.1
  have hqc : QuasiCompact Xᵢ.hom := hXᵢ.2.1
  have hqs : QuasiSeparated Xᵢ.hom := hXᵢ.2.2
  have hcs : CompactSpace Xᵢ.left := QuasiCompact.compactSpace_of_compactSpace Xᵢ.hom
  have hqss : QuasiSeparatedSpace Xᵢ.left := quasiSeparatedSpace_of_quasiSeparated Xᵢ.hom
  have hsep₀ : IsSeparated ((Over.pullback (c.π.app i)).obj Xᵢ).hom :=
    prop_of_overIso (@IsSeparated) e inferInstance
  obtain ⟨j₁, a, hsep₁⟩ := exists_isSeparated_overPullback_of_isLimit D c hc i Xᵢ
  have hfp₁ : FinitePresentation ((Over.pullback (D.map a)).obj Xᵢ).hom :=
    finitePresentation_overPullbackObj _ Xᵢ hXᵢ
  have e₁ : X ≅ (Over.pullback (c.π.app j₁)).obj ((Over.pullback (D.map a)).obj Xᵢ) :=
    e ≪≫ overPullbackObj_shiftIso D c a Xᵢ
  have hprop₁ : IsProper ((Over.pullback (c.π.app j₁)).obj
      ((Over.pullback (D.map a)).obj Xᵢ)).hom := isProper_hom_of_overIso e₁
  obtain ⟨j₂, b, hprop₂⟩ := exists_isProper_overPullbackObj_of_isLimit_of_isNoetherian
    D c hc j₁ ((Over.pullback (D.map a)).obj Xᵢ) hfp₁
  exact ⟨j₂, (Over.pullback (D.map b)).obj ((Over.pullback (D.map a)).obj Xᵢ),
    finitePresentation_overPullbackObj _ _ hfp₁, hprop₂,
    ⟨e₁ ≪≫ overPullbackObj_shiftIso D c b ((Over.pullback (D.map a)).obj Xᵢ)⟩⟩

variable (R : Type u) [CommRing R]

/-- **A separated scheme of finite presentation over `Spec R` has a separated model over a
Noetherian stage.** Let `X` be separated and of finite presentation over `Spec R`. Then there are
a finite subset `i` of `R` and a scheme `Xᵢ` over `Spec ℤ[i]` which is separated and of finite
presentation and whose base change to `Spec R` is `X`.

The model is produced by [Stacks, Tag 01ZM] part (1),
`AlgebraicGeometry.exists_finitePresentation_baseChange_specAdjoinFinsetDiagram`, and made
separated by [Stacks, Tag 01ZQ] in the form
`AlgebraicGeometry.exists_isSeparated_overPullback_of_isLimit`; replacing the model by its base
change to the later stage keeps finite presentation, by
`AlgebraicGeometry.finitePresentation_overPullbackObj`, and keeps the base change to `Spec R`,
by `AlgebraicGeometry.overPullbackObj_shiftIso`.

This is exactly the hypothesis of
`AlgebraicGeometry.exists_isProper_model_of_finitePresentation_specAdjoinFinsetDiagram`. -/
theorem exists_isSeparated_finitePresentation_baseChange_specAdjoinFinsetDiagram
    (X : Over (specAdjoinFinsetCone R).pt) (hX : FinitePresentation X.hom) [IsSeparated X.hom] :
    ∃ (i : (Finset R)ᵒᵖ) (Xᵢ : Over ((specAdjoinFinsetDiagram R).obj i)),
      FinitePresentation Xᵢ.hom ∧ IsSeparated Xᵢ.hom ∧
        Nonempty (X ≅ (Over.pullback ((specAdjoinFinsetCone R).π.app i)).obj Xᵢ) := by
  obtain ⟨i, Z, hZ, ⟨e⟩⟩ := exists_finitePresentation_baseChange_specAdjoinFinsetDiagram R X hX
  let _ : LocallyOfFinitePresentation Z.hom := hZ.1
  let _ : QuasiCompact Z.hom := hZ.2.1
  let _ : QuasiSeparated Z.hom := hZ.2.2
  let _ : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  let _ : QuasiSeparatedSpace Z.left := quasiSeparatedSpace_of_quasiSeparated Z.hom
  let _ : IsSeparated ((Over.pullback ((specAdjoinFinsetCone R).π.app i)).obj Z).hom :=
    prop_of_overIso (@IsSeparated) e ‹_›
  obtain ⟨j, a, hsep⟩ :=
    exists_isSeparated_overPullback_of_isLimit (specAdjoinFinsetDiagram R)
      (specAdjoinFinsetCone R) (isLimit_specAdjoinFinsetCone R) i Z
  exact ⟨j, (Over.pullback ((specAdjoinFinsetDiagram R).map a)).obj Z,
    finitePresentation_overPullbackObj _ Z hZ, hsep,
    ⟨e ≪≫ overPullbackObj_shiftIso (specAdjoinFinsetDiagram R) (specAdjoinFinsetCone R) a Z⟩⟩

/-- **A proper scheme of finite presentation over `Spec R` is the base change of a proper scheme
of finite presentation over a Noetherian stage.** Let `X` be proper and of finite presentation
over `Spec R`. Then there are a finite subset `j` of `R` and a scheme `Xⱼ` over `Spec ℤ[j]`,
proper and of finite presentation over it, with an isomorphism `X ≅ Xⱼ ×_{Spec ℤ[j]} Spec R` over
`Spec R`.

This is `AlgebraicGeometry.exists_isProper_finitePresentation_model_of_isLimit` at
`AlgebraicGeometry.specAdjoinFinsetCone`. Every hypothesis that theorem places on the system is
discharged by the construction of the system: `(Finset R)ᵒᵖ` is cofiltered, the transition
morphisms are affine, and the stages are Noetherian hence quasi-compact and quasi-separated. -/
theorem exists_isProper_model_baseChange_specAdjoinFinsetDiagram
    (X : Over (specAdjoinFinsetCone R).pt) [IsProper X.hom] (hX : FinitePresentation X.hom) :
    ∃ (j : (Finset R)ᵒᵖ) (Xⱼ : Over ((specAdjoinFinsetDiagram R).obj j)),
      FinitePresentation Xⱼ.hom ∧ IsProper Xⱼ.hom ∧
        Nonempty (X ≅ (Over.pullback ((specAdjoinFinsetCone R).π.app j)).obj Xⱼ) :=
  exists_isProper_finitePresentation_model_of_isLimit (specAdjoinFinsetDiagram R)
    (specAdjoinFinsetCone R) (isLimit_specAdjoinFinsetCone R) X hX

/-- **A proper scheme of finite presentation over an affine scheme is the base change of a proper
scheme of finite presentation over an affine Noetherian scheme of finite type over the
integers.** Let `S` be affine and let `X` be proper and of finite presentation over `S`. Then
there are an affine Noetherian scheme `T` of finite type over `ℤ`, a morphism `q : S ⟶ T`, and a
scheme `XT` over `T` which is proper and of finite presentation over it, with an isomorphism
`X ≅ XT ×_T S` over `S`.

This is the first move of the limit-descent paragraph of [Stacks, Tag 0E7D]: it reduces a
statement about a proper morphism of finite presentation over an arbitrary affine base to the same
statement over an affine *Noetherian* base, which is where [Stacks, Tag 02V7] lives. It is
`AlgebraicGeometry.exists_isProper_finitePresentation_model_of_isLimit` at
`AlgebraicGeometry.affineStageCone`, and is the properness-carrying companion of
`AlgebraicGeometry.exists_finitePresentation_baseChange_of_isAffine`.

The properness of `X` is passed to the generic theorem as an explicit instance argument. As an
instance *binder* it is not found at the spelling `(affineStageCone S).pt`, although that is
`S` by `rfl`; at an argument position the elaborator checks against the expected type and the two
spellings are identified. -/
theorem exists_isProper_finitePresentation_baseChange_of_isAffine
    (S : Scheme.{u}) [IsAffine S] (X : Over S) [IsProper X.hom]
    (hX : FinitePresentation X.hom) :
    ∃ (T : Scheme.{u}) (q : S ⟶ T) (XT : Over T),
      IsAffine T ∧ IsNoetherian T ∧ LocallyOfFiniteType (terminal.from T) ∧
        FinitePresentation XT.hom ∧ IsProper XT.hom ∧
        Nonempty (X ≅ (Over.pullback q).obj XT) := by
  obtain ⟨j, XT, hfp, hprop, hiso⟩ :=
    @exists_isProper_finitePresentation_model_of_isLimit _ _ _
      (specAdjoinFinsetDiagram Γ(S, ⊤)) _ _ _
      (affineStageCone S) (isLimit_affineStageCone S) X ‹IsProper X.hom› hX
  exact ⟨(specAdjoinFinsetDiagram Γ(S, ⊤)).obj j, (affineStageCone S).π.app j, XT,
    isAffine_specAdjoinFinsetDiagram_obj _ j, isNoetherian_specAdjoinFinsetDiagram_obj _ j,
    locallyOfFiniteType_terminalFrom_specAdjoinFinsetDiagram_obj _ j, hfp, hprop, hiso⟩

end AlgebraicGeometry

end
