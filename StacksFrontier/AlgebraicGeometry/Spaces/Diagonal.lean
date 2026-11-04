module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.DiagonalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.QuasiCompactLocal

/-!
# The absolute diagonal of an algebraic space

Let `F` be an algebraic space over a scheme `S`. The absolute diagonal `Δ : F ⟶ F ⨯ F` is
representable by definition, and this file proves that every represented base change of it is
locally of finite type, a monomorphism, separated and locally quasi-finite.

## Main definitions

* `AlgebraicGeometry.Space.atlasProd` is the chart of `F ⨯ F` attached to a chart
  `q : h_U ⟶ F` of `F`, and `AlgebraicGeometry.Space.kernelPairToProd` is the morphism
  `R ⟶ U ⨯ U` of the site induced by the kernel pair of `q`.
* `AlgebraicGeometry.Space.PresheafImpliesHoldsOnEveryEtaleChart` is the implication from the
  represented-base-change form of a property of morphisms of algebraic spaces to its
  étale-chart form; it is an ingredient of Stacks 03MJ, and it is carried as an explicit
  hypothesis where it is needed because the module that proves it,
  `StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBridge`, imports this one.

## Main results

* `AlgebraicGeometry.Space.monomorphisms_diag_of_representable` and
  `AlgebraicGeometry.Space.isSeparated_diag_of_representable` are parts (2) and (3) for an
  arbitrary presheaf with representable diagonal, algebraicity not being needed for them;
  `AlgebraicGeometry.Space.mono_toScheme_map_of_isPullback_diag` is the content of both,
  before packaging.
* `AlgebraicGeometry.Space.presheaf_diag_of_kernelPair` is the reduction parts (1) and (4)
  rest on: a property of scheme morphisms which is stable under base change and fppf local on
  the target holds for every represented base change of `Δ` as soon as it holds for the kernel
  pair `R ⟶ U ×_S U` of a surjective étale atlas `U ⟶ F`.
* `AlgebraicGeometry.Space.presheaf_of_etale_cover` is the descent step that reduction uses, in
  place of Stacks 02WZ, and `Stacks.Descent.locallyOfFiniteType_isLocalAtTarget_fppf` is the
  entry of Stacks 02WH it needs.
* `CategoryTheory.IsPullback.of_isoBotLeft`,
  `CategoryTheory.Limits.isPullback_diag_prodLift` and
  `CategoryTheory.Limits.isPullback_diag_of_isPullback` are the general categorical facts
  about a kernel pair and the diagonal which exhibit the kernel pair of an atlas as a base
  change of `Δ`.
* `AlgebraicGeometry.Space.isPullback_kernelPairToProd` is that cartesian square in the site,
  `AlgebraicGeometry.Space.presheaf_atlasProd` carries a relative property of a chart over to
  `AlgebraicGeometry.Space.atlasProd`, and
  `AlgebraicGeometry.Space.locallyOfFiniteType_and_mono_toScheme_kernelPairToProd` states the
  two scheme-level facts about `R ⟶ U ⨯ U` that the reduction rests on.
* `AlgebraicGeometry.Space.locallyOfFiniteType_presheaf_mapDesc` and
  `AlgebraicGeometry.Space.locallyQuasiFinite_presheaf_mapDesc` carry the two finite-type
  clauses over to the comparison of fibre products of Stacks 03KN, and
  `AlgebraicGeometry.Space.isLocallyOfFiniteType_mapDesc` and
  `AlgebraicGeometry.Space.isLocallyQuasiFinite_mapDesc` state them in the étale-chart form of
  Stacks 03XF and 03XJ, modulo the hypothesis named above.

## Implementation notes

Parts (2) and (3) need no presentation of `F` at all, and no algebraicity: the diagonal is a
split monomorphism in any category with binary products, monomorphisms are stable under base
change, and `yoneda` reflects them while `AlgebraicGeometry.BigFppfOver.toScheme` preserves
them, so every represented base change of `Δ` is a monomorphism of schemes. A monomorphism of
schemes is separated, which gives part (3), and is universally injective, which combines with
part (1) to give part (4).

Parts (1) and (4) are the argument of the source, with the presentation `F = U/R` replaced by
the atlas and its kernel pair. Two forms of the cartesian square
```
R  ⟶  F
↓      ↓ Δ
U ⨯ U ⟶ F ⨯ F
```
are available. `CategoryTheory.Limits.isPullback_diag_prodLift` is the statement for the
canonical kernel pair, transported along an isomorphism of the bottom-left corner by
`CategoryTheory.IsPullback.of_isoBotLeft`; this is how
`AlgebraicGeometry.Space.isPullback_kernelPairToProd` is obtained from
`AlgebraicGeometry.Space.atlasProd`, the chart of `F ⨯ F` attached to a chart of `F`.
`CategoryTheory.Limits.isPullback_diag_of_isPullback` is the statement for a kernel pair
`s, t` of `q : V ⟶ F` and an arbitrary jointly monic pair `π₁, π₂ : W ⟶ V`: any `j : R ⟶ W`
with components `s` and `t` is a base change of `diag F` along `prod.lift (π₁ ≫ q) (π₂ ≫ q)`.
Applied with `W` the Yoneda image of `U ×_S U` and `π₁, π₂` the images of the two projections
— jointly monic because Yoneda preserves binary products — it exhibits `R ⟶ U ×_S U` as the
base change of `Δ` along the chart of `F ⨯ F`, and it is the form
`AlgebraicGeometry.Space.presheaf_diag_of_kernelPair` uses.

The second general fact the reduction needs is
`AlgebraicGeometry.Space.presheaf_of_etale_cover`, the special case of Stacks 02WZ which the
argument needs: a property of scheme morphisms which is fppf local on the target holds for
every represented base change of a representable morphism of presheaves as soon as each such
base change has it after one further surjective étale base change. Being fppf local on the
target is Stacks 02WH, available for the properties used here through
`Stacks.Descent.locallyOfFiniteType_isLocalAtTarget_fpqc` and
`AlgebraicGeometry.Scheme.fppfPrecoverage_le_fpqcPrecoverage`; the surjective étale base
change is an fppf covering family of one member by
`AlgebraicGeometry.Scheme.Hom.singleton_mem_fppfPrecoverage`. The required cover of a
represented base change of `Δ` along `g : h_T ⟶ F ⨯ F` is obtained by pulling the atlas back
along the two components of `g` in turn; the resulting chart maps `g` through the chart of
`F ⨯ F`, which is where the cartesian square applies.

On the morphism `j : R ⟶ U ⨯ U` of the site the two properties needed are immediate: `j` is a
monomorphism, because the two projections of a kernel pair are jointly monomorphic, and
locally of finite type, because its composite with the first projection is the étale morphism
`R ⟶ U`. The source deduces that `j` is a monomorphism from `R` being an equivalence relation;
that is not needed, since the universal property of `R = U ×_F U` alone gives it through
`CategoryTheory.Functor.relativelyRepresentable.hom_ext'`.

Two assertions of part (1) of Stacks 03KN, that the comparison of fibre products is locally
of finite type and locally quasi-finite, are stated here in both available forms. The
represented-base-change form is proved; the étale-chart form of
`AlgebraicGeometry.Space.IsLocallyOfFiniteType` and
`AlgebraicGeometry.Space.IsLocallyQuasiFinite` is not implied by it *in this module*, because
those properties are tested on étale charts rather than on represented base changes, and the
implication is part of Stacks 03MJ. It is therefore carried as the explicit hypothesis
`AlgebraicGeometry.Space.PresheafImpliesHoldsOnEveryEtaleChart`. That hypothesis **is** proved
in the development, as
`AlgebraicGeometry.Space.presheafImpliesHoldsOnEveryEtaleChart_of_etale_precomp`, carrying
`@[stacks 03MJ "condition (1) from the represented base changes"]`, and the two statements
below are restated there with it discharged, as
`AlgebraicGeometry.Space.isLocallyOfFiniteType_mapDesc'` and
`AlgebraicGeometry.Space.isLocallyQuasiFinite_mapDesc'`, carrying `@[stacks 03KN]`. It cannot
be discharged here: that module imports this one.

## References

* [Stacks Project, Tag 02X4](https://stacks.math.columbia.edu/tag/02X4)
* [Stacks Project, Tag 021U](https://stacks.math.columbia.edu/tag/021U)
* [Stacks Project, Tag 02WH](https://stacks.math.columbia.edu/tag/02WH)
* [Stacks Project, Tag 02WZ](https://stacks.math.columbia.edu/tag/02WZ)
* [Stacks Project, Tag 03KN](https://stacks.math.columbia.edu/tag/03KN)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- A cartesian square may be transported along an isomorphism of its bottom-left corner. -/
theorem IsPullback.of_isoBotLeft {P X Y Y' Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}
    {g : Y ⟶ Z} (h : IsPullback fst snd f g) (e : Y' ≅ Y) :
    IsPullback fst (snd ≫ e.inv) f (e.hom ≫ g) := by
  have hw : fst ≫ f = (snd ≫ e.inv) ≫ e.hom ≫ g := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h.w
  refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk hw
    (fun c ↦ h.lift c.fst (c.snd ≫ e.hom) (by simpa using c.condition)) ?_ ?_ ?_⟩⟩
  · intro c
    simp
  · intro c
    simp
  · intro c m hm₁ hm₂
    refine h.hom_ext (by rw [hm₁, h.lift_fst]) ?_
    rw [h.lift_snd, ← hm₂]
    simp

namespace Limits

/-- If `a, b : R ⟶ A` is a kernel pair of `q : A ⟶ F`, then `R` is the fibre product of the
absolute diagonal of `F` and the map `A ⨯ A ⟶ F ⨯ F` induced by `q`. This is the cartesian
square used to prove properties of the diagonal of an algebraic space from a presentation. -/
@[ega "I 5.3.5" "special case"]
theorem isPullback_diag_prodLift {R A F : C} {a b : R ⟶ A} {q : A ⟶ F}
    (h : IsPullback a b q q) [HasBinaryProduct A A] [HasBinaryProduct F F] :
    IsPullback (a ≫ q) (prod.lift a b) (diag F) (prod.map q q) := by
  have hdf : diag F ≫ prod.fst = 𝟙 F := prod.lift_fst _ _
  have hds : diag F ≫ prod.snd = 𝟙 F := prod.lift_snd _ _
  have hw : (a ≫ q) ≫ diag F = prod.lift a b ≫ prod.map q q := by
    refine prod.hom_ext ?_ ?_
    · rw [Category.assoc, hdf, Category.comp_id, Category.assoc, prod.map_fst,
        ← Category.assoc, prod.lift_fst]
    · rw [Category.assoc, hds, Category.comp_id, Category.assoc, prod.map_snd,
        ← Category.assoc, prod.lift_snd, h.w]
  have key : ∀ c : PullbackCone (diag F) (prod.map q q),
      (c.snd ≫ prod.fst) ≫ q = c.fst ∧ (c.snd ≫ prod.snd) ≫ q = c.fst := fun c ↦
    ⟨by rw [Category.assoc, ← prod.map_fst q q, ← Category.assoc, ← c.condition,
        Category.assoc, hdf, Category.comp_id],
     by rw [Category.assoc, ← prod.map_snd q q, ← Category.assoc, ← c.condition,
        Category.assoc, hds, Category.comp_id]⟩
  refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk hw
    (fun c ↦ h.lift (c.snd ≫ prod.fst) (c.snd ≫ prod.snd) ((key c).1.trans (key c).2.symm))
      ?_ ?_ ?_⟩⟩
  · intro c
    rw [← Category.assoc, h.lift_fst]
    exact (key c).1
  · intro c
    refine prod.hom_ext ?_ ?_ <;> simp
  · intro c m hm₁ hm₂
    refine h.hom_ext ?_ ?_ <;> simp [← hm₂]

/-- A kernel pair `s, t : R ⟶ V` of `q : V ⟶ F` is a base change of the diagonal of `F`: if
`π₁, π₂ : W ⟶ V` is a jointly monic pair and `j : R ⟶ W` has components `s` and `t`, then `j`
is the base change of `diag F` along `prod.lift (π₁ ≫ q) (π₂ ≫ q)`. -/
theorem isPullback_diag_of_isPullback {F V R W : C} [HasBinaryProduct F F] [HasBinaryProduct V V]
    (q : V ⟶ F) {s t : R ⟶ V} (hst : IsPullback s t q q)
    {π₁ π₂ : W ⟶ V} (hW : Mono (prod.lift π₁ π₂))
    {j : R ⟶ W} (h₁ : j ≫ π₁ = s) (h₂ : j ≫ π₂ = t) :
    IsPullback (s ≫ q) j (diag F) (prod.lift (π₁ ≫ q) (π₂ ≫ q)) := by
  have hj₁ : j ≫ π₁ ≫ q = s ≫ q := by rw [← Category.assoc, h₁]
  have hj₂ : j ≫ π₂ ≫ q = t ≫ q := by rw [← Category.assoc, h₂]
  have hcomm : CommSq (s ≫ q) j (diag F) (prod.lift (π₁ ≫ q) (π₂ ≫ q)) :=
    ⟨prod.hom_ext (by simp [hj₁]) (by simp [hj₂, hst.w])⟩
  have e₁ (c : PullbackCone (diag F) (prod.lift (π₁ ≫ q) (π₂ ≫ q))) :
      c.fst = c.snd ≫ π₁ ≫ q := by
    simpa using congrArg (fun k => k ≫ (prod.fst : F ⨯ F ⟶ F)) c.condition
  have e₂ (c : PullbackCone (diag F) (prod.lift (π₁ ≫ q) (π₂ ≫ q))) :
      c.fst = c.snd ≫ π₂ ≫ q := by
    simpa using congrArg (fun k => k ≫ (prod.snd : F ⨯ F ⟶ F)) c.condition
  refine IsPullback.of_isLimit' hcomm (PullbackCone.IsLimit.mk hcomm.w
    (fun c => hst.lift (c.snd ≫ π₁) (c.snd ≫ π₂) ?_) ?_ ?_ ?_)
  · simp only [Category.assoc]
    rw [← e₁ c, ← e₂ c]
  · intro c
    rw [← Category.assoc, hst.lift_fst]
    simp [e₁ c]
  · intro c
    rw [← cancel_mono (prod.lift π₁ π₂)]
    exact prod.hom_ext (by simp [h₁, hst.lift_fst]) (by simp [h₂, hst.lift_snd])
  · intro c m _ hm₂
    refine hst.hom_ext ?_ ?_
    · rw [hst.lift_fst, ← h₁, ← Category.assoc, hm₂]
    · rw [hst.lift_snd, ← h₂, ← Category.assoc, hm₂]

end Limits

end CategoryTheory

namespace Stacks.Descent

/-- **Stacks 02WH.** Being locally of finite type is fppf local on the base. -/
@[stacks 02WH "locally_finite_type"]
instance locallyOfFiniteType_isLocalAtTarget_fppf :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.LocallyOfFiniteType : MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fppfPrecoverage :=
  isLocalAtTarget_fppfPrecoverage _

end Stacks.Descent

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Two general steps -/

/-- Two objects of the big fppf category over `S` representing the base change of the same
morphism of presheaves along the same morphism have the same properties as schemes over the
base. -/
theorem property_of_isPullback_of_isPullback {Q : MorphismProperty Scheme.{u}} [Q.RespectsIso]
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {a : BigFppfOver B S hS}
    {g : yoneda.obj a ⟶ Y} {b₁ b₂ : BigFppfOver B S hS} {u₁ : b₁ ⟶ a} {u₂ : b₂ ⟶ a}
    {α₁ : yoneda.obj b₁ ⟶ X} {α₂ : yoneda.obj b₂ ⟶ X}
    (h₁ : IsPullback α₁ (yoneda.map u₁) f g) (h₂ : IsPullback α₂ (yoneda.map u₂) f g)
    (hu : Q ((BigFppfOver.toScheme B S hS).map u₂)) :
    Q ((BigFppfOver.toScheme B S hS).map u₁) := by
  have he : (h₁.isoIsPullback _ _ h₂).hom ≫ yoneda.map u₂ = yoneda.map u₁ :=
    h₁.isoIsPullback_hom_snd _ _ h₂
  have he' : (yoneda.preimageIso (h₁.isoIsPullback _ _ h₂)).hom ≫ u₂ = u₁ :=
    yoneda.map_injective (by simp [he])
  refine (Q.arrow_mk_iso_iff (Arrow.isoMk
    ((BigFppfOver.toScheme B S hS).mapIso (yoneda.preimageIso (h₁.isoIsPullback _ _ h₂)))
      (Iso.refl _) ?_)).2 hu
  simpa [← Functor.map_comp] using congrArg (BigFppfOver.toScheme B S hS).map he'

/-- **Stacks 02WZ** in the case needed here. A property `Q` of scheme morphisms which is fppf
local on the target holds for every represented base change of a representable morphism of
presheaves as soon as every such base change has `Q` after one further surjective étale base
change.

This is not Stacks 02WZ itself, which asserts an equivalence for one surjective étale chart of
the target, and it is not tagged as such; it is the implication that argument supplies, in the
form in which the proof of Stacks 02X4 uses it. -/
theorem presheaf_of_etale_cover (Q : MorphismProperty Scheme.{u})
    [MorphismProperty.IsLocalAtTarget Q Scheme.fppfPrecoverage]
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f)
    (h : ∀ (a : BigFppfOver B S hS) (g : yoneda.obj a ⟶ Y),
      ∃ (b : BigFppfOver B S hS) (c : b ⟶ a),
        Surjective ((BigFppfOver.toScheme B S hS).map c) ∧
        Etale ((BigFppfOver.toScheme B S hS).map c) ∧
        Q ((BigFppfOver.toScheme B S hS).map (hf.snd (yoneda.map c ≫ g)))) :
    (MorphismProperty.presheaf (Q.inverseImage (BigFppfOver.toScheme B S hS))) f := by
  have : (Q.inverseImage (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  refine MorphismProperty.relative_of_snd hf fun a g => ?_
  obtain ⟨b, c, hsurj, hetale, hQ⟩ := h a g
  have hD : IsPullback (Limits.pullback.fst (hf.snd g) c) (Limits.pullback.snd (hf.snd g) c)
      (hf.snd g) c := IsPullback.of_hasPullback _ _
  have hsnd : Q ((BigFppfOver.toScheme B S hS).map (Limits.pullback.snd (hf.snd g) c)) :=
    property_of_isPullback_of_isPullback B S hS
      ((yoneda.map_isPullback hD).paste_horiz (hf.isPullback g))
      (hf.isPullback (yoneda.map c ≫ g)) hQ
  have : Etale ((BigFppfOver.toScheme B S hS).map c) := hetale
  have : Surjective ((BigFppfOver.toScheme B S hS).map c) := hsurj
  show Q ((BigFppfOver.toScheme B S hS).map (hf.snd g))
  refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
    (K := Scheme.fppfPrecoverage)
    (Scheme.Hom.singleton_mem_fppfPrecoverage ((BigFppfOver.toScheme B S hS).map c)) ?_
  intro V gg _ hgg
  cases hgg
  have hDS := (BigFppfOver.toScheme B S hS).map_isPullback hD
  rw [← hDS.isoPullback_inv_snd, Q.cancel_left_of_respectsIso]
  exact hsnd

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### The monomorphism and separatedness assertions -/

/-- Every represented base change of the diagonal of a presheaf on the big fppf site of `S` is a
monomorphism of schemes. No algebraicity is used: the diagonal is a split monomorphism, and
monomorphisms are stable under base change, reflected by `yoneda` and preserved by
`AlgebraicGeometry.BigFppfOver.toScheme`. -/
theorem mono_toScheme_map_of_isPullback_diag {a b : BigFppfOver B S hS}
    (g : yoneda.obj a ⟶ F ⨯ F) (fst : yoneda.obj b ⟶ F) (snd : b ⟶ a)
    (sq : IsPullback fst (yoneda.map snd) (diag F) g) :
    Mono ((BigFppfOver.toScheme B S hS).map snd) := by
  have hdiag : (MorphismProperty.monomorphisms ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) (diag F) :=
    inferInstanceAs (Mono (diag F))
  have : Mono (yoneda.map snd) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq hdiag
  have : Mono snd := yoneda.mono_of_mono_map ‹Mono (yoneda.map snd)›
  exact preserves_mono_of_preservesLimit _ snd

/-- The diagonal of a presheaf on the big fppf category over `S` with representable diagonal is
a monomorphism: each of its represented base changes is a monomorphism of schemes. Algebraicity
of the presheaf is not needed. -/
theorem monomorphisms_diag_of_representable
    (hdiag : yoneda.relativelyRepresentable (diag F)) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (MorphismProperty.monomorphisms Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (diag F) :=
  ⟨hdiag, fun _ _ g fst snd sq ↦ mono_toScheme_map_of_isPullback_diag B S hS g fst snd sq⟩

/-- The diagonal of a presheaf on the big fppf category over `S` with representable diagonal is
separated: each of its represented base changes is a separated morphism of schemes. Algebraicity
of the presheaf is not needed. -/
theorem isSeparated_diag_of_representable
    (hdiag : yoneda.relativelyRepresentable (diag F)) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsSeparated.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (diag F) :=
  ⟨hdiag, fun _ _ g fst snd sq ↦
    have := mono_toScheme_map_of_isPullback_diag B S hS g fst snd sq
    _root_.AlgebraicGeometry.IsSeparated.isSeparated_of_mono _⟩

/-! ### The chart `U ⨯ U ⟶ F ⨯ F` attached to a chart of `F` -/

/-- The Yoneda embedding of the big fppf site over `S` carries binary products to binary
products. -/
def yonedaProdIso (U V : BigFppfOver B S hS) :
    yoneda.obj (U ⨯ V) ≅ yoneda.obj U ⨯ yoneda.obj V :=
  preservesLimitIso yoneda (pair U V) ≪≫ HasLimit.isoOfNatIso (pairComp U V yoneda)

/-- The isomorphism `yonedaProdIso` followed by the first projection is the image under the Yoneda
embedding of the first projection `U ⨯ V ⟶ U`. -/
@[reassoc (attr := simp)]
theorem yonedaProdIso_hom_fst (U V : BigFppfOver B S hS) :
    (yonedaProdIso B S hS U V).hom ≫ prod.fst = yoneda.map prod.fst := by
  show (preservesLimitIso yoneda (pair U V)).hom ≫
    (HasLimit.isoOfNatIso (pairComp U V yoneda)).hom ≫
      limit.π (pair (yoneda.obj U) (yoneda.obj V)) ⟨WalkingPair.left⟩ = _
  simp only [← Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc,
    preservesLimitIso_hom_π]
  simp [pairComp]

/-- The isomorphism `yonedaProdIso` followed by the second projection is the image under the
Yoneda embedding of the second projection `U ⨯ V ⟶ V`. -/
@[reassoc (attr := simp)]
theorem yonedaProdIso_hom_snd (U V : BigFppfOver B S hS) :
    (yonedaProdIso B S hS U V).hom ≫ prod.snd = yoneda.map prod.snd := by
  show (preservesLimitIso yoneda (pair U V)).hom ≫
    (HasLimit.isoOfNatIso (pairComp U V yoneda)).hom ≫
      limit.π (pair (yoneda.obj U) (yoneda.obj V)) ⟨WalkingPair.right⟩ = _
  simp only [← Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc,
    preservesLimitIso_hom_π]
  simp [pairComp]

/-- The chart of `F ⨯ F` attached to a chart `q : yoneda.obj U ⟶ F` of `F`. -/
def atlasProd {U : BigFppfOver B S hS} (q : yoneda.obj U ⟶ F) : yoneda.obj (U ⨯ U) ⟶ F ⨯ F :=
  prod.lift (yoneda.map prod.fst ≫ q) (yoneda.map prod.snd ≫ q)

/-- The chart `atlasProd q` is the composite of `yonedaProdIso` with the product map `q ⨯ q`. -/
theorem atlasProd_eq {U : BigFppfOver B S hS} (q : yoneda.obj U ⟶ F) :
    atlasProd B S hS q = (yonedaProdIso B S hS U U).hom ≫ prod.map q q := by
  refine prod.hom_ext ?_ ?_ <;> simp [atlasProd]

/-- The chart of `F ⨯ F` attached to a chart of `F` inherits every relative property of the
chart whose tested property of morphisms of schemes is stable under composition. No base-change
hypothesis is needed: the relative property attached to *any* property of morphisms of schemes
is stable under base change. -/
theorem presheaf_atlasProd (Q : MorphismProperty Scheme.{u})
    [Q.IsStableUnderComposition] {U : BigFppfOver B S hS} (q : yoneda.obj U ⟶ F)
    (hq : (MorphismProperty.presheaf
      (Q.inverseImage (BigFppfOver.toScheme B S hS))) q) :
    (MorphismProperty.presheaf (Q.inverseImage (BigFppfOver.toScheme B S hS)))
      (atlasProd B S hS q) := by
  let P : MorphismProperty (BigFppfOver B S hS) :=
    Q.inverseImage (BigFppfOver.toScheme B S hS)
  have : P.IsStableUnderComposition := MorphismProperty.IsStableUnderComposition.inverseImage _
  have hbc := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) P
  have h₁ : P.presheaf (prod.map q (𝟙 (yoneda.obj U))) :=
    hbc.of_isPullback (IsPullback.of_prod_fst_with_id q (yoneda.obj U)) hq
  have h₂' : P.presheaf (prod.map q (𝟙 F)) :=
    hbc.of_isPullback (IsPullback.of_prod_fst_with_id q F) hq
  have h₂ : P.presheaf (prod.map (𝟙 F) q) := by
    have heq : prod.map (𝟙 F) q =
        ((prod.braiding F (yoneda.obj U)).hom ≫ prod.map q (𝟙 F)) ≫
          (prod.braiding F F).hom := by
      refine prod.hom_ext ?_ ?_ <;> simp
    rw [heq]
    exact MorphismProperty.RespectsIso.postcomp P.presheaf _ _
      (MorphismProperty.RespectsIso.precomp P.presheaf _ _ h₂')
  have hprod : P.presheaf (prod.map q q) := by
    have heq : prod.map q q = prod.map q (𝟙 (yoneda.obj U)) ≫ prod.map (𝟙 F) q := by
      refine prod.hom_ext ?_ ?_ <;> simp
    rw [heq]
    exact MorphismProperty.comp_mem _ _ _ h₁ h₂
  rw [atlasProd_eq]
  exact MorphismProperty.RespectsIso.precomp P.presheaf _ _ hprod

/-! ### The kernel pair of a chart -/

/-- The morphism `R ⟶ U ⨯ U` of the site induced by the kernel pair of a chart
`q : yoneda.obj U ⟶ F`. -/
def kernelPairToProd {U : BigFppfOver B S hS} {q : yoneda.obj U ⟶ F}
    (hq : yoneda.relativelyRepresentable q) : hq.pullback q ⟶ U ⨯ U :=
  prod.lift (hq.fst' q) (hq.snd q)

/-- The cartesian square of the source's proof, in the site: the kernel pair of a chart of `F`
is the fibre product of the diagonal of `F` and the induced chart of `F ⨯ F`. -/
theorem isPullback_kernelPairToProd {U : BigFppfOver B S hS} {q : yoneda.obj U ⟶ F}
    (hq : yoneda.relativelyRepresentable q) :
    IsPullback (yoneda.map (hq.fst' q) ≫ q) (yoneda.map (kernelPairToProd B S hS hq))
      (diag F) (atlasProd B S hS q) := by
  have hmap : yoneda.map (kernelPairToProd B S hS hq) =
      prod.lift (yoneda.map (hq.fst' q)) (yoneda.map (hq.snd q)) ≫
        (yonedaProdIso B S hS U U).inv := by
    rw [Iso.eq_comp_inv]
    refine prod.hom_ext ?_ ?_ <;> simp [kernelPairToProd, ← Functor.map_comp]
  rw [hmap, atlasProd_eq]
  exact (isPullback_diag_prodLift (hq.isPullback' q)).of_isoBotLeft _

/-- The morphism `R ⟶ U ⨯ U` induced by the kernel pair of a chart is a monomorphism: the two
projections of a kernel pair are jointly monomorphic. -/
theorem mono_kernelPairToProd {U : BigFppfOver B S hS} {q : yoneda.obj U ⟶ F}
    (hq : yoneda.relativelyRepresentable q) : Mono (kernelPairToProd B S hS hq) where
  right_cancellation x y hxy := by
    refine hq.hom_ext' ?_ ?_
    · simpa [kernelPairToProd] using congrArg (fun k ↦ k ≫ prod.fst) hxy
    · simpa [kernelPairToProd] using congrArg (fun k ↦ k ≫ prod.snd) hxy

/-- The morphism of schemes underlying the morphism `R ⟶ U ⨯ U` induced by the kernel pair of a
surjective étale chart is a monomorphism which is locally of finite type, hence also locally
quasi-finite. -/
theorem locallyOfFiniteType_and_mono_toScheme_kernelPairToProd {U : BigFppfOver B S hS}
    (q : yoneda.obj U ⟶ F)
    (hqEtale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) q) :
    LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map
        (kernelPairToProd B S hS hqEtale.rep)) ∧
      Mono ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS hqEtale.rep)) := by
  set T := BigFppfOver.toScheme B S hS with hT
  set j := kernelPairToProd B S hS hqEtale.rep with hj
  have hfst : j ≫ prod.fst = hqEtale.rep.fst' q := prod.lift_fst _ _
  have : Etale (T.map (hqEtale.rep.fst' q)) :=
    hqEtale.property q (yoneda.map (hqEtale.rep.snd q)) (hqEtale.rep.fst' q)
      (hqEtale.rep.isPullback' q).flip
  have hcomp : LocallyOfFiniteType (T.map j ≫ T.map (prod.fst (X := U) (Y := U))) := by
    rw [← T.map_comp, hfst]
    infer_instance
  have : Mono j := mono_kernelPairToProd B S hS hqEtale.rep
  exact ⟨locallyOfFiniteType_of_comp (T.map j) (T.map prod.fst),
    preserves_mono_of_preservesLimit _ j⟩

/-! ### The reduction to the kernel pair of an atlas -/

/-- The reduction behind Stacks 02X4. Let `F` be a presheaf on the big fppf category over `S`
with representable diagonal and a surjective étale atlas `q : h_U ⟶ F`, and let `s, t : R ⟶ U`
be the kernel pair of `q`. A property `Q` of scheme morphisms which is stable under base change
and fppf local on the target holds for every represented base change of `diag F` as soon as it
holds for `R ⟶ U ×_S U`. -/
theorem presheaf_diag_of_kernelPair (Q : MorphismProperty Scheme.{u})
    [Q.IsStableUnderBaseChange] [MorphismProperty.IsLocalAtTarget Q Scheme.fppfPrecoverage]
    (hdiag : yoneda.relativelyRepresentable (diag F))
    {U R : BigFppfOver B S hS} {q : yoneda.obj U ⟶ F} {s t : R ⟶ U}
    (hst : IsPullback (yoneda.map s) (yoneda.map t) q q)
    (hqSurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) q)
    (hqEtale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) q)
    (hQ : Q ((BigFppfOver.toScheme B S hS).map (prod.lift s t))) :
    (MorphismProperty.presheaf (Q.inverseImage (BigFppfOver.toScheme B S hS))) (diag F) := by
  have hq : yoneda.relativelyRepresentable q := hdiag.of_diag q
  have hmono : Mono (prod.lift (yoneda.map (prod.fst : U ⨯ U ⟶ U)) (yoneda.map prod.snd)) :=
    inferInstanceAs (Mono (prodComparison yoneda U U))
  have hjSq : IsPullback (yoneda.map s ≫ q) (yoneda.map (prod.lift s t)) (diag F)
      (prod.lift (yoneda.map (prod.fst : U ⨯ U ⟶ U) ≫ q) (yoneda.map prod.snd ≫ q)) :=
    isPullback_diag_of_isPullback q hst hmono
      (by rw [← Functor.map_comp, prod.lift_fst]) (by rw [← Functor.map_comp, prod.lift_snd])
  refine presheaf_of_etale_cover B S hS Q hdiag fun a g => ?_
  obtain ⟨b₁, c₁, α₁, hsq₁⟩ := hq (g ≫ (prod.fst : F ⨯ F ⟶ F))
  obtain ⟨b₂, c₂, α₂, hsq₂⟩ := hq (yoneda.map c₁ ≫ g ≫ (prod.snd : F ⨯ F ⟶ F))
  rw [← yoneda.map_preimage α₁] at hsq₁
  rw [← yoneda.map_preimage α₂] at hsq₂
  refine ⟨b₂, c₂ ≫ c₁, ?_, ?_, ?_⟩
  · have : Surjective _ := hqSurj.property _ _ c₁ hsq₁
    have : Surjective _ := hqSurj.property _ _ c₂ hsq₂
    rw [Functor.map_comp]
    infer_instance
  · have : Etale _ := hqEtale.property _ _ c₁ hsq₁
    have : Etale _ := hqEtale.property _ _ c₂ hsq₂
    rw [Functor.map_comp]
    infer_instance
  · have key₁ : yoneda.map (c₂ ≫ yoneda.preimage α₁) ≫ q =
        yoneda.map (c₂ ≫ c₁) ≫ g ≫ (prod.fst : F ⨯ F ⟶ F) := by
      rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hsq₁.w]
    have key₂ : yoneda.map (yoneda.preimage α₂) ≫ q =
        yoneda.map (c₂ ≫ c₁) ≫ g ≫ (prod.snd : F ⨯ F ⟶ F) := by
      rw [hsq₂.w, Functor.map_comp, Category.assoc]
    have hfac : yoneda.map (c₂ ≫ c₁) ≫ g =
        yoneda.map (prod.lift (c₂ ≫ yoneda.preimage α₁) (yoneda.preimage α₂)) ≫
          prod.lift (yoneda.map (prod.fst : U ⨯ U ⟶ U) ≫ q) (yoneda.map prod.snd ≫ q) := by
      refine prod.hom_ext ?_ ?_
      · conv_rhs => rw [Category.assoc, prod.lift_fst, ← Category.assoc, ← Functor.map_comp,
          prod.lift_fst]
        rw [Category.assoc, key₁]
      · conv_rhs => rw [Category.assoc, prod.lift_snd, ← Category.assoc, ← Functor.map_comp,
          prod.lift_snd]
        rw [Category.assoc, key₂]
    have hpb : IsPullback
        (Limits.pullback.fst (prod.lift s t)
          (prod.lift (c₂ ≫ yoneda.preimage α₁) (yoneda.preimage α₂)))
        (Limits.pullback.snd (prod.lift s t)
          (prod.lift (c₂ ≫ yoneda.preimage α₁) (yoneda.preimage α₂)))
        (prod.lift s t) (prod.lift (c₂ ≫ yoneda.preimage α₁) (yoneda.preimage α₂)) :=
      IsPullback.of_hasPullback _ _
    have hbig := (yoneda.map_isPullback hpb).paste_horiz hjSq
    rw [← hfac] at hbig
    refine property_of_isPullback_of_isPullback B S hS
      (hdiag.isPullback (yoneda.map (c₂ ≫ c₁) ≫ g)) hbig ?_
    exact Q.of_isPullback ((BigFppfOver.toScheme B S hS).map_isPullback hpb) hQ

/-! ### The local finiteness assertions -/


/-! ### The remaining half of Stacks 03MJ -/

/-- **Stacks 03MJ, condition (1) from the represented base changes.** The property of a
property `P` of scheme morphisms that whenever it holds for every represented base change of a
morphism of algebraic spaces over `S`, it also holds on every one of that morphism's étale
charts.

This is the half of Stacks 03MJ needed to pass from the represented-base-change form of local
finite type and local quasi-finiteness to the étale-chart form in which
`AlgebraicGeometry.Space.IsLocallyOfFiniteType` and
`AlgebraicGeometry.Space.IsLocallyQuasiFinite` are stated. It **is** proved in the development,
as `AlgebraicGeometry.Space.presheafImpliesHoldsOnEveryEtaleChart_of_etale_precomp` in
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleChartBridge.lean`; it is nevertheless carried as an
explicit hypothesis by the two statements below, because that module imports this one and so
cannot be used from here. The same file restates both of them with the hypothesis
discharged. -/
abbrev PresheafImpliesHoldsOnEveryEtaleChart (P : MorphismProperty Scheme.{u}) : Prop :=
  ∀ {G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (φ : G ⟶ H),
    (MorphismProperty.presheaf (P.inverseImage (BigFppfOver.toScheme B S hS))) φ →
    HoldsOnEveryEtaleChart B S hS P φ

/-! ### The comparison of two fibre products -/

variable {X Y Z T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 03KN, part (1).** The comparison `X ×[Z] Y ⟶ X ×[T] Y` is locally of finite type:
each of its represented base changes is a morphism of schemes which is locally of finite
type. -/
theorem locallyOfFiniteType_presheaf_mapDesc (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T)
    (hZ : IsAlgebraicSpace B S hS Z) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (pullback.mapDesc f g h) :=
  presheaf_of_isPullback B S hS (isPullback_mapDesc B S hS f g h)
    (presheaf_of_isPullback B S hS (isPullback_pullbackDiagonal_diag B S hS h)
      (presheaf_locallyOfFiniteType_diag B S hS Z hZ))

/-- **Stacks 03KN, part (1).** The comparison `X ×[Z] Y ⟶ X ×[T] Y` is locally quasi-finite:
each of its represented base changes is a morphism of schemes which is locally of finite type
and locally quasi-finite. -/
theorem locallyQuasiFinite_presheaf_mapDesc (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T)
    (hZ : IsAlgebraicSpace B S hS Z) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      ((@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
      (BigFppfOver.toScheme B S hS))) (pullback.mapDesc f g h) :=
  presheaf_of_isPullback B S hS (isPullback_mapDesc B S hS f g h)
    (presheaf_of_isPullback B S hS (isPullback_pullbackDiagonal_diag B S hS h)
      (presheaf_locallyQuasiFinite_diag B S hS Z hZ))

/-- **Stacks 03KN, part (1).** The comparison `X ×[Z] Y ⟶ X ×[T] Y` is locally of finite type in
the sense of Stacks 03XF, granted the half of Stacks 03MJ named by
`AlgebraicGeometry.Space.PresheafImpliesHoldsOnEveryEtaleChart`. -/
theorem isLocallyOfFiniteType_mapDesc
    (hbridge : PresheafImpliesHoldsOnEveryEtaleChart B S hS
      (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}))
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) (hZ : IsAlgebraicSpace B S hS Z) :
    IsLocallyOfFiniteType B S hS (pullback.mapDesc f g h) :=
  hbridge _ (locallyOfFiniteType_presheaf_mapDesc B S hS f g h hZ)

/-- **Stacks 03KN, part (1).** The comparison `X ×[Z] Y ⟶ X ×[T] Y` is locally quasi-finite in
the sense of Stacks 03XJ, granted the half of Stacks 03MJ named by
`AlgebraicGeometry.Space.PresheafImpliesHoldsOnEveryEtaleChart`. -/
theorem isLocallyQuasiFinite_mapDesc
    (hbridge : PresheafImpliesHoldsOnEveryEtaleChart B S hS
      ((@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u})))
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) (hZ : IsAlgebraicSpace B S hS Z) :
    IsLocallyQuasiFinite B S hS (pullback.mapDesc f g h) :=
  hbridge _ (locallyQuasiFinite_presheaf_mapDesc B S hS f g h hZ)

end AlgebraicGeometry.Space

end
