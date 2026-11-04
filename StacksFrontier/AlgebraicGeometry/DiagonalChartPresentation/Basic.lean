module

public import StacksFrontier.AlgebraicGeometry.LeibnizDerivation.Chart
public import StacksFrontier.AlgebraicGeometry.DiagonalConormal.Retraction
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Algebra.Category.Ring.Constructions

/-!
# The affine model of the diagonal over an affine chart

For `f : X ⟶ S`, an affine open `V` of `S` and an affine open `U ≤ f ⁻¹ᵁ V` of `X`, the open

  `Stacks.LeibnizDerivation.ambientChart f U = pullback.fst f f ⁻¹ᵁ U ⊓ pullback.snd f f ⁻¹ᵁ U`

is an affine open of `X ×_S X` containing the part of the diagonal over `U`. This file computes
its ring of sections: writing `R = Γ(S, V)` and `A = Γ(X, U)`,

  `Γ(X ×_S X, ambientChart f U) ≅ A ⊗_R A`   (`tensorIsoChart`),

and identifies the three structure maps across it — the two projections become the two
inclusions (`includeLeft_tensorIsoChart`, `includeRight_tensorIsoChart`), and the comorphism of
the diagonal becomes the multiplication map `A ⊗_R A ⟶ A`
(`tensorIsoChart_comp_diagAppLE`). Consequently:

* the ideal of the diagonal in the chart is the Kähler ideal
  (`kaehlerIdeal_eq_comap_ker_diagAppLE`); and
* the section `p₂^♯ b - p₁^♯ b` of [Stacks, Tag 08S2] is the element `1 ⊗ b - b ⊗ 1`
  (`tensorIsoChart_one_tmul_sub_tmul_one`), whose class modulo the square of the ideal is `d b`
  by `Stacks.DiagonalConormal.toCotangent_one_tmul_sub_tmul_one`.

## Main definitions

* `Stacks.DiagonalChart.chartPushoutSection`: the comparison
  `pushout (f.appLE V U hUV) (f.appLE V U hUV) ⟶ Γ(X ×_S X, ambientChart f U)`, specialized to
  the square exhibiting `X ×_S X` as the fibre product of `f` with itself.
* `Stacks.DiagonalChart.diagAppLE`: the comorphism of the diagonal from the ambient chart down
  to `U`.
* `Stacks.DiagonalChart.tensorIsoPushout`: the tensor square of a morphism of `CommRingCat`
  compared with the categorical pushout of that morphism with itself.
* `Stacks.DiagonalChart.tensorIsoChart`: **the affine model**, `Γ(X ×_S X, ambientChart f U) ≅`
  `A ⊗_R A`.

## Main results

* `Stacks.DiagonalChart.isIso_chartPushoutSection`: the pushout comparison for the ambient chart
  is invertible for `U` and `V` affine.
* `Stacks.DiagonalChart.fst_appLE_comp_diagAppLE` and
  `Stacks.DiagonalChart.snd_appLE_comp_diagAppLE`: each projection is retracted by the diagonal
  on sections over the chart — true for an arbitrary open `U`.
* `Stacks.DiagonalChart.chartPushoutSection_comp_diagAppLE`: the diagonal's comorphism, read on
  the pushout, is `pushout.desc (𝟙) (𝟙)` — also for an arbitrary `U`.
* `Stacks.DiagonalChart.includeLeft_tensorIsoChart`,
  `Stacks.DiagonalChart.includeRight_tensorIsoChart`,
  `Stacks.DiagonalChart.tensorIsoChart_comp_diagAppLE`: the three structure maps across the
  affine model.
* `Stacks.DiagonalChart.kaehlerIdeal_eq_comap_ker_diagAppLE`: **the ideal of the diagonal in
  the chart is the Kähler ideal.**
* `Stacks.DiagonalChart.tensorIsoChart_one_tmul_sub_tmul_one`: **the generator formula in the
  chart.**

## Implementation notes

The invertibility of the pushout comparison is
`AlgebraicGeometry.isIso_pushoutSection_of_isAffineOpen`, applied to
`CategoryTheory.IsPullback.of_hasPullback f f` with both legs the same morphism and both opens
the same `U`; the hypothesis `UY = g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT` of that lemma is satisfied by `rfl`
because that intersection *is* the definition of `ambientChart`.

The pushout of a morphism of `CommRingCat` with itself is the tensor square by
`CommRingCat.isPushout_tensorProduct`, which is stated for `CommRingCat.ofHom (algebraMap R A)`;
the hypothesis `halg : CommRingCat.ofHom (algebraMap R A) = φ` transports it to an arbitrary
`φ : R ⟶ A` carrying the algebra structure, and holds for the instance `φ.hom.toAlgebra`, with
which `CommRingCat.KaehlerDifferential φ` is defined.

That each projection is retracted by the diagonal on sections is
`AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE` followed by
`AlgebraicGeometry.pullback.diagonal_fst` (resp. `diagonal_snd`); the identification of the
Kähler ideal is `RingHom.comap_ker` together with `Stacks.DiagonalConormal.ker_lmulHom`, which
holds by `rfl` because `KaehlerDifferential.ideal` *is* the kernel of the multiplication map.

`inf_le_left` at `ambientChart f U` carries the `CompleteLattice` path to `LE` rather than
`TopologicalSpace.Opens.instPartialOrder`'s, and `AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE`
then fails to rewrite on a goal that visibly contains its pattern. The named containments
`Stacks.LeibnizDerivation.ambientChart_le_fst_preimage` and `…_le_snd_preimage`, whose declared
types fix the instance, are used at every `appLE` below for this reason.

`CommRingCat.of ↑Γ(X, U)` and `Γ(X, U)` are definitionally equal but not syntactically, so
`simp`'s identity lemmas do not fire on `𝟙 Γ(X, U)` when the goal was produced at the
`CommRingCat.of` spelling. `includeLeft_comp_lmulHom` and `includeRight_comp_lmulHom` are
therefore stated separately, for an arbitrary object `A` of `CommRingCat`, and applied by
`exact`, which elaborates at default transparency, where the two spellings unify.

`CategoryTheory.asIso` is applied positionally, `@asIso _ _ _ _ _ h`: `isIso_chartPushoutSection`
takes affineness as an argument and so is not an instance.

Nothing is Noetherian, finite, quasi-compact or separated. `f` is an arbitrary morphism of
schemes, and affineness of `U` and `V` is used only for `isIso_chartPushoutSection` and the
declarations depending on it; the three `appLE` statements and
`chartPushoutSection_comp_diagAppLE` hold for an arbitrary open `U`.

## References

* [Stacks Project, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 01UT](https://stacks.math.columbia.edu/tag/01UT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct

universe u

noncomputable section

namespace Stacks.DiagonalChart

/-! ### The multiplication map of a tensor square -/

section Lmul

variable {R A : CommRingCat.{u}} [Algebra R A]

/-- The multiplication map undoes the left inclusion. -/
theorem includeLeft_comp_lmulHom :
    CommRingCat.ofHom (S := CommRingCat.of (A ⊗[R] A))
        Algebra.TensorProduct.includeLeftRingHom ≫
      Stacks.DiagonalConormal.lmulHom R A = 𝟙 _ := by
  ext a; simp

/-- The multiplication map undoes the right inclusion. -/
theorem includeRight_comp_lmulHom :
    CommRingCat.ofHom (S := CommRingCat.of (A ⊗[R] A))
        Algebra.TensorProduct.includeRight.toRingHom ≫
      Stacks.DiagonalConormal.lmulHom R A = 𝟙 _ := by
  ext a; simp

end Lmul

/-! ### The pushout of a ring map with itself is the tensor product -/

section Tensor

variable {R A : CommRingCat.{u}} (φ : R ⟶ A) [Algebra R A]
  (halg : CommRingCat.ofHom (algebraMap R A) = φ)

include halg

/-- The tensor square of `φ` is a pushout square of `φ` with itself. -/
theorem isPushout_tensor :
    IsPushout φ φ
      (CommRingCat.ofHom (S := CommRingCat.of (A ⊗[R] A))
        Algebra.TensorProduct.includeLeftRingHom)
      (CommRingCat.ofHom (S := CommRingCat.of (A ⊗[R] A))
        Algebra.TensorProduct.includeRight.toRingHom) :=
  halg ▸ CommRingCat.isPushout_tensorProduct R A A

/-- The tensor product `A ⊗[R] A` compared with the categorical pushout of `φ` with itself. -/
def tensorIsoPushout : CommRingCat.of (A ⊗[R] A) ≅ pushout φ φ :=
  (isPushout_tensor φ halg).isoPushout

/-- The isomorphism `tensorIsoPushout` carries the left inclusion into `A ⊗[R] A` to
`pushout.inl`. -/
theorem includeLeft_tensorIsoPushout :
    CommRingCat.ofHom (S := CommRingCat.of (A ⊗[R] A))
        Algebra.TensorProduct.includeLeftRingHom ≫ (tensorIsoPushout φ halg).hom =
      pushout.inl φ φ :=
  (isPushout_tensor φ halg).inl_isoPushout_hom

/-- The isomorphism `tensorIsoPushout` carries the right inclusion into `A ⊗[R] A` to
`pushout.inr`. -/
theorem includeRight_tensorIsoPushout :
    CommRingCat.ofHom (S := CommRingCat.of (A ⊗[R] A))
        Algebra.TensorProduct.includeRight.toRingHom ≫ (tensorIsoPushout φ halg).hom =
      pushout.inr φ φ :=
  (isPushout_tensor φ halg).inr_isoPushout_hom

/-- Maps out of `A ⊗[R] A` agree as soon as they agree on the two inclusions. -/
theorem tensor_hom_ext {T : CommRingCat.{u}} {k k' : CommRingCat.of (A ⊗[R] A) ⟶ T}
    (hl : CommRingCat.ofHom (S := CommRingCat.of (A ⊗[R] A))
        Algebra.TensorProduct.includeLeftRingHom ≫ k =
      CommRingCat.ofHom (S := CommRingCat.of (A ⊗[R] A))
        Algebra.TensorProduct.includeLeftRingHom ≫ k')
    (hr : CommRingCat.ofHom (S := CommRingCat.of (A ⊗[R] A))
        Algebra.TensorProduct.includeRight.toRingHom ≫ k =
      CommRingCat.ofHom (S := CommRingCat.of (A ⊗[R] A))
        Algebra.TensorProduct.includeRight.toRingHom ≫ k') :
    k = k' :=
  (isPushout_tensor φ halg).hom_ext hl hr

end Tensor

/-! ### The ambient chart and its presentation -/

section Chart

variable {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens) (U : X.Opens) (hUV : U ≤ f ⁻¹ᵁ V)

/-- The comparison map from the pushout of `f.appLE V U hUV` with itself to the ring of sections
of `pullback f f` over the ambient chart. -/
abbrev chartPushoutSection :
    pushout (f.appLE V U hUV) (f.appLE V U hUV) ⟶
      Γ(Limits.pullback f f, Stacks.LeibnizDerivation.ambientChart f U) :=
  AlgebraicGeometry.pushoutSection (IsPullback.of_hasPullback f f) hUV hUV rfl

/-- For affine opens `V` and `U`, the comparison map `chartPushoutSection` is an isomorphism. -/
theorem isIso_chartPushoutSection (hV : IsAffineOpen V) (hU : IsAffineOpen U) :
    IsIso (chartPushoutSection f V U hUV) :=
  AlgebraicGeometry.isIso_pushoutSection_of_isAffineOpen _ hUV hUV rfl hV hU hU

/-- Precomposed with `pushout.inl`, the comparison map `chartPushoutSection` is the comorphism of
the first projection on the ambient chart. -/
theorem inl_chartPushoutSection :
    pushout.inl (f.appLE V U hUV) (f.appLE V U hUV) ≫ chartPushoutSection f V U hUV =
      (pullback.fst f f).appLE U (Stacks.LeibnizDerivation.ambientChart f U)
        (Stacks.LeibnizDerivation.ambientChart_le_fst_preimage f U) :=
  pushout.inl_desc _ _ _

/-- Precomposed with `pushout.inr`, the comparison map `chartPushoutSection` is the comorphism of
the second projection on the ambient chart. -/
theorem inr_chartPushoutSection :
    pushout.inr (f.appLE V U hUV) (f.appLE V U hUV) ≫ chartPushoutSection f V U hUV =
      (pullback.snd f f).appLE U (Stacks.LeibnizDerivation.ambientChart f U)
        (Stacks.LeibnizDerivation.ambientChart_le_snd_preimage f U) :=
  pushout.inr_desc _ _ _

/-- The comorphism of the diagonal on the ambient chart. -/
abbrev diagAppLE :
    Γ(Limits.pullback f f, Stacks.LeibnizDerivation.ambientChart f U) ⟶ Γ(X, U) :=
  (pullback.diagonal f).appLE (Stacks.LeibnizDerivation.ambientChart f U) U
    (Stacks.LeibnizDerivation.le_diagonal_preimage_ambientChart f U)

/-- The comorphism of a retraction `g` of the diagonal, followed by that of the diagonal, is the
identity of `Γ(X, U)`. -/
private theorem appLE_comp_diagAppLE_of_diagonal_comp_eq_id (g : Limits.pullback f f ⟶ X)
    (hg : pullback.diagonal f ≫ g = 𝟙 X)
    (hle : Stacks.LeibnizDerivation.ambientChart f U ≤ g ⁻¹ᵁ U) :
    g.appLE U (Stacks.LeibnizDerivation.ambientChart f U) hle ≫ diagAppLE f U = 𝟙 Γ(X, U) := by
  rw [Scheme.Hom.appLE_comp_appLE]
  refine ((Stacks.DiagonalConormal.appLE_congr hg U U _ (by simp)).trans
      (Stacks.DiagonalConormal.id_appLE U U _ (le_refl U))).trans ?_
  exact X.presheaf.map_id _

/-- The comorphism of the first projection followed by that of the diagonal is the identity of
`Γ(X, U)`. -/
theorem fst_appLE_comp_diagAppLE :
    (pullback.fst f f).appLE U (Stacks.LeibnizDerivation.ambientChart f U)
        (Stacks.LeibnizDerivation.ambientChart_le_fst_preimage f U) ≫ diagAppLE f U =
      𝟙 Γ(X, U) :=
  appLE_comp_diagAppLE_of_diagonal_comp_eq_id f U _ (pullback.diagonal_fst f) _

/-- The comorphism of the second projection followed by that of the diagonal is the identity of
`Γ(X, U)`. -/
theorem snd_appLE_comp_diagAppLE :
    (pullback.snd f f).appLE U (Stacks.LeibnizDerivation.ambientChart f U)
        (Stacks.LeibnizDerivation.ambientChart_le_snd_preimage f U) ≫ diagAppLE f U =
      𝟙 Γ(X, U) :=
  appLE_comp_diagAppLE_of_diagonal_comp_eq_id f U _ (pullback.diagonal_snd f) _

/-- The comparison map `chartPushoutSection` followed by the comorphism of the diagonal is the
codiagonal `pushout.desc (𝟙 Γ(X, U)) (𝟙 Γ(X, U))`. -/
theorem chartPushoutSection_comp_diagAppLE :
    chartPushoutSection f V U hUV ≫ diagAppLE f U =
      pushout.desc (𝟙 Γ(X, U)) (𝟙 Γ(X, U)) rfl := by
  refine pushout.hom_ext ?_ ?_
  · rw [← Category.assoc, inl_chartPushoutSection, pushout.inl_desc,
      fst_appLE_comp_diagAppLE]
  · rw [← Category.assoc, inr_chartPushoutSection, pushout.inr_desc,
      snd_appLE_comp_diagAppLE]

end Chart


/-! ### The affine model of the diagonal over an affine chart -/

section Presentation

variable {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens) (U : X.Opens) (hUV : U ≤ f ⁻¹ᵁ V)
  [Algebra Γ(S, V) Γ(X, U)]
  (halg : CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, U)) = f.appLE V U hUV)
  (hV : IsAffineOpen V) (hU : IsAffineOpen U)

/-- **The ring of sections of the ambient chart of the diagonal is the tensor square.** -/
def tensorIsoChart :
    CommRingCat.of ((Γ(X, U) : Type u) ⊗[Γ(S, V)] Γ(X, U)) ≅
      Γ(Limits.pullback f f, Stacks.LeibnizDerivation.ambientChart f U) :=
  tensorIsoPushout (f.appLE V U hUV) halg ≪≫
    @asIso _ _ _ _ (chartPushoutSection f V U hUV)
      (isIso_chartPushoutSection f V U hUV hV hU)

/-- The isomorphism `tensorIsoChart` carries the left inclusion into the tensor square to the
comorphism of the first projection on the ambient chart. -/
theorem includeLeft_tensorIsoChart :
    CommRingCat.ofHom (S := CommRingCat.of ((Γ(X, U) : Type u) ⊗[Γ(S, V)] Γ(X, U)))
        Algebra.TensorProduct.includeLeftRingHom ≫
      (tensorIsoChart f V U hUV halg hV hU).hom =
      (pullback.fst f f).appLE U (Stacks.LeibnizDerivation.ambientChart f U)
        (Stacks.LeibnizDerivation.ambientChart_le_fst_preimage f U) := by
  rw [tensorIsoChart, Iso.trans_hom, ← Category.assoc,
    includeLeft_tensorIsoPushout (f.appLE V U hUV) halg, asIso_hom,
    inl_chartPushoutSection]

/-- The isomorphism `tensorIsoChart` carries the right inclusion into the tensor square to the
comorphism of the second projection on the ambient chart. -/
theorem includeRight_tensorIsoChart :
    CommRingCat.ofHom (S := CommRingCat.of ((Γ(X, U) : Type u) ⊗[Γ(S, V)] Γ(X, U)))
        Algebra.TensorProduct.includeRight.toRingHom ≫
      (tensorIsoChart f V U hUV halg hV hU).hom =
      (pullback.snd f f).appLE U (Stacks.LeibnizDerivation.ambientChart f U)
        (Stacks.LeibnizDerivation.ambientChart_le_snd_preimage f U) := by
  rw [tensorIsoChart, Iso.trans_hom, ← Category.assoc,
    includeRight_tensorIsoPushout (f.appLE V U hUV) halg, asIso_hom,
    inr_chartPushoutSection]

/-- **Under the tensor presentation, the comorphism of the diagonal is the multiplication
map.** -/
theorem tensorIsoChart_comp_diagAppLE :
    (tensorIsoChart f V U hUV halg hV hU).hom ≫ diagAppLE f U =
      Stacks.DiagonalConormal.lmulHom Γ(S, V) Γ(X, U) := by
  refine tensor_hom_ext (f.appLE V U hUV) halg ?_ ?_
  · rw [← Category.assoc, includeLeft_tensorIsoChart, fst_appLE_comp_diagAppLE]
    exact (includeLeft_comp_lmulHom (R := Γ(S, V)) (A := Γ(X, U))).symm
  · rw [← Category.assoc, includeRight_tensorIsoChart, snd_appLE_comp_diagAppLE]
    exact (includeRight_comp_lmulHom (R := Γ(S, V)) (A := Γ(X, U))).symm

/-- **The Kähler ideal is the ideal of the diagonal in the ambient chart**, read through the
tensor presentation. -/
theorem kaehlerIdeal_eq_comap_ker_diagAppLE :
    KaehlerDifferential.ideal Γ(S, V) Γ(X, U) =
      Ideal.comap (tensorIsoChart f V U hUV halg hV hU).hom.hom
        (RingHom.ker (diagAppLE f U).hom) := by
  rw [RingHom.comap_ker, ← CommRingCat.hom_comp,
    tensorIsoChart_comp_diagAppLE f V U hUV halg hV hU]
  exact (Stacks.DiagonalConormal.ker_lmulHom Γ(S, V) Γ(X, U)).symm

/-- **The generator formula in the chart.** The element `1 ⊗ b - b ⊗ 1` of the tensor square
is the section `p₂^♯ b - p₁^♯ b` of the ambient chart — the section whose conormal class
[Stacks, Tag 08S2] computes. -/
theorem tensorIsoChart_one_tmul_sub_tmul_one (b : Γ(X, U)) :
    (tensorIsoChart f V U hUV halg hV hU).hom.hom
        ((1 : Γ(X, U)) ⊗ₜ[Γ(S, V)] b - b ⊗ₜ[Γ(S, V)] (1 : Γ(X, U))) =
      ((pullback.snd f f).appLE U (Stacks.LeibnizDerivation.ambientChart f U)
          (Stacks.LeibnizDerivation.ambientChart_le_snd_preimage f U)).hom b -
        ((pullback.fst f f).appLE U (Stacks.LeibnizDerivation.ambientChart f U)
          (Stacks.LeibnizDerivation.ambientChart_le_fst_preimage f U)).hom b := by
  rw [map_sub]
  refine congrArg₂ (· - ·) ?_ ?_
  · exact congr($(includeRight_tensorIsoChart f V U hUV halg hV hU) b)
  · exact congr($(includeLeft_tensorIsoChart f V U hUV halg hV hU) b)

end Presentation

end Stacks.DiagonalChart

end
