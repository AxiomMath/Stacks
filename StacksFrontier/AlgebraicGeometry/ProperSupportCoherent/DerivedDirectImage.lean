module

public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedAmplitude.UpperBounds
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.UniformVanishing
public import StacksFrontier.AlgebraicGeometry.ProperCoherentImage.Basic
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.UnboundedDerivedDirectImage.QuasiCoherence
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
import StacksCore.Tactic.StacksAttribute

/-!
# The derived direct image of a bounded coherent complex with proper support

Let `S` be a Noetherian scheme, let `f : X ⟶ S` be a morphism locally of finite type and let `E`
be an object of `D^b_Coh(𝒪_X)` such that the support of every `H^i(E)` is proper over `S`. Then
`Rf_*E` is an object of `D^b_Coh(𝒪_S)`. This is [Stacks, Tag 08E2].

Everything below lives in the namespace `Stacks.AlgebraicGeometry.ProperSupportCoherent`.

## Main definitions

* `HasCoherentBoundedDirectImages`: the property of an `𝒪_X`-module that all of its higher
  direct images along `f` are coherent and that they vanish in large degrees.

## Main results

* `isCoherent_isWeakSerre`: coherent `𝒪_Y`-modules form a weak Serre subcategory, in the
  five-term formulation.
* `derivedCategoryBBounded_derivedPushforward_of_bounded`: the dévissage. For a bounded `E`
  whose cohomology sheaves have coherent, eventually vanishing higher direct images, `Rf_*E` is
  an object of `D^b_Coh(𝒪_S)`. No hypothesis on `f` or `S`.
* `derivedCategoryBBounded_derivedPushforward_of_isProperOver_supp`: the dévissage behind
  [Stacks, Tag 08E2], with [Stacks, Tag 02O5] as its only hypothesis, in the named form
  `AlgebraicGeometry.ProperCoherentImage.HigherDirectImageIsCoherentOverAffineBase`. That
  hypothesis is supplied, and the tag's label attached, in
  `StacksFrontier/AlgebraicGeometry/ProperSupportCoherent/DerivedDirectImageUnconditional.lean`.
* `derivedCategoryBBounded_derivedPushforward_of_isAffineHom`: the same conclusion for an affine
  `f`, where the appeal to [Stacks, Tag 02O5] is discharged.

## Implementation notes

The source argues with the spectral sequence `R^p f_* H^q(E) ⇒ R^{p+q} f_* E`. Since `E` is
bounded the same content is reached by the finite dévissage along the canonical truncation
triangles `τ_{≤a}E → E → τ_{≥a+1}E`, which is how the quasi-coherent analogue
[Stacks, Tag 08D5] part (1) is organised in
`StacksFrontier/AlgebraicGeometry/UnboundedDerivedDirectImage/QuasiCoherence.lean`: on an object
concentrated in one degree the cohomology of `Rf_*` is a higher direct image, `Rf_*` is exact,
and `D^b_Coh(𝒪_S)` is a triangulated subcategory of `D(𝒪_S)` because coherent modules form a
weak Serre subcategory.

The dévissage runs with the single hypothesis `HasCoherentBoundedDirectImages`, which packages
both halves of the conclusion: coherence of `R^p f_* H^q(E)` gives coherence of the cohomology
of `Rf_*E`, and the eventual vanishing of `R^p f_* H^q(E)` gives its boundedness above.
Negative degrees cost nothing, the higher direct images vanishing there, so boundedness below is
free. Because the property is stated of the *higher direct images* rather than of the module it
is stable under isomorphism, and that is all the dévissage needs of it; the induction hypothesis
is restricted to the degrees of the window, so the zero cohomology sheaves outside it never have
to be discussed.

Both halves at a cohomology sheaf of `E` come from [Stacks, Tag 08DS] and the reduction behind
it. Coherence is the conclusion of that tag, which this library proves granted
[Stacks, Tag 02O5], which is carried here in the named form
`AlgebraicGeometry.ProperCoherentImage.HigherDirectImageIsCoherentOverAffineBase` — the
affine-base case of that tag's first assertion, equivalent to the assertion itself by
`higherDirectImageIsCoherent_iff_overAffineBase`. The eventual vanishing is unconditional: the
reduction
`exists_isProper_rightDerivedPlus_iso` replaces `f` by a *proper* morphism `Z ⟶ S`, which is
quasi-compact and quasi-separated, so the uniform vanishing degree of [Stacks, Tag 01XJ]
applies. This is where `S` has to be Noetherian rather than merely locally Noetherian: over a
base that is not quasi-compact there is no uniform vanishing degree and `Rf_*E` need not be
bounded above — on the disjoint union of the `Spec kₙ`, with `Zₙ = P^n` over the `n`-th
component, the proper morphism `Z ⟶ S` has nonvanishing higher direct images in unbounded
degrees. A Noetherian scheme is by definition quasi-compact and locally Noetherian, so this is
the source's hypothesis and not a strengthening of it.

`Rf_*` is `AlgebraicGeometry.derivedPushforwardModules`, the unbounded derived direct image read
on `AlgebraicGeometry.Scheme.Modules`, and `D^b_Coh(𝒪_S)` is
`DerivedCategoryB.derivedCategoryBBounded` at the coherence predicate — the object property on
`D(𝒪_S)` of [Stacks, Tag 06UP], in the spelling already used for `D_Coh` in
`StacksFrontier/AlgebraicGeometry/DeRham/CoherentDirectImage.lean`.

Coherence of `𝒪_Y`-modules is a weak Serre class by [Stacks, Tag 01BY], but instance search does
not cross the `AlgebraicGeometry.Scheme.Modules` abbreviation on its own, so that class is
installed here at the binders the statements use.

## References

* [Stacks Project, Tag 08E2](https://stacks.math.columbia.edu/tag/08E2)
* [Stacks Project, Tag 08DS](https://stacks.math.columbia.edu/tag/08DS)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated

universe u

namespace Stacks.AlgebraicGeometry.ProperSupportCoherent

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### Coherent modules as a weak Serre subcategory -/

/-- Coherent `𝒪_Y`-modules are a weak Serre class, at the spelling of the category of modules on
a scheme. -/
local instance isWeakSerreClass_isCoherent (Y : Scheme.{u}) :
    ObjectProperty.IsWeakSerreClass (fun M : Y.Modules => M.IsCoherent) :=
  @_root_.SheafOfModules.coherentModules_isWeakSerreClass _ _ Y.ringCatSheaf

/-- **Coherent `𝒪_Y`-modules form a weak Serre subcategory**, in the five-term formulation: in
an exact sequence `M₀ → M₁ → M₂ → M₃ → M₄` of `𝒪_Y`-modules whose four outer terms are coherent,
the middle term is coherent. -/
@[sga "6 I 3.4" "special case"]
theorem isCoherent_isWeakSerre (Y : Scheme.{u}) :
    WeakSerre.IsWeakSerre (fun M : Y.Modules => M.IsCoherent) := by
  refine ⟨inferInstance,
    ObjectProperty.exists_prop_of_isWeakSerreClass (fun M : Y.Modules => M.IsCoherent),
    fun E h₀ h₁ h₃ h₄ => ?_⟩
  exact prop_mid_of_exact₄
    (ObjectProperty.prop_obj₂_of_exact (P := fun M : Y.Modules => M.IsCoherent))
    E.zero₀ E.zero₁ E.zero₂ E.exact₁ E.exact₂ E.exact₃ h₀ h₁ h₃ h₄

section DerivedPushforward

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-! ### Modules with coherent, eventually vanishing higher direct images -/

/-- Every higher direct image `R^p f_* M` is coherent, and they vanish for `p` large. -/
def HasCoherentBoundedDirectImages (M : X.Modules) : Prop :=
  (∀ p : ℤ, (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj M).IsCoherent) ∧
    ∃ N : ℤ, ∀ p : ℤ, N ≤ p →
      IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj M)

/-- `HasCoherentBoundedDirectImages` depends only on the isomorphism class of the module. -/
theorem HasCoherentBoundedDirectImages.of_iso {M M' : X.Modules} (e : M ≅ M')
    (h : HasCoherentBoundedDirectImages f M) : HasCoherentBoundedDirectImages f M' := by
  obtain ⟨hcoh, N, hN⟩ := h
  refine ⟨fun p => ?_, N, fun p hp => ?_⟩
  · have := hcoh p
    exact Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso (R := S.ringCatSheaf)
      (((Scheme.Modules.pushforward f).rightDerivedPlus p).mapIso e.symm)
  · exact IsZero.of_iso (hN p hp)
      (((Scheme.Modules.pushforward f).rightDerivedPlus p).mapIso e.symm)

/-! ### A module in a single degree -/

/-- **`H^i(Rf_*(M[0])) ≅ R^i f_* M`.** On a bounded below object the unbounded derived direct
image agrees with the bounded below one, the K-injective complexes computing both, and the
cohomology of the latter is the higher direct image. -/
theorem nonempty_homology_derivedPushforward_single_zero (M : X.Modules) (i : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor S.Modules i).obj
        ((derivedPushforwardModules f).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj M)) ≅
      ((Scheme.Modules.pushforward f).rightDerivedPlus i).obj M) := by
  obtain ⟨e⟩ := Stacks.Perfect.CechAugmentation.nonempty_obj_iso_rightDerivedFunctorPlus
    (Scheme.Modules.pushforward f) (derivedPushforwardModules f)
    (derivedPushforwardModulesUnit f)
    (fun I hI => RingedSpace.isIso_derivedPushforwardUnit_app_of_isKInjective _ I hI)
    ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M) 0 (by
      change ((DerivedCategory.singleFunctor X.Modules 0).obj M).IsGE 0
      infer_instance)
  exact ⟨(DerivedCategory.homologyFunctor S.Modules i).mapIso e⟩

/-- **`Rf_*(M[0])` is an object of `D^b_Coh(𝒪_S)`** when the higher direct images of `M` are
coherent and vanish in large degrees. Its cohomology in degree `i` is `R^i f_* M`, which also
vanishes for `i < 0`. -/
theorem derivedCategoryBBounded_derivedPushforward_single_zero (M : X.Modules)
    (hM : HasCoherentBoundedDirectImages f M) :
    DerivedCategoryB.derivedCategoryBBounded (fun N : S.Modules => N.IsCoherent)
      ((derivedPushforwardModules f).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj M)) := by
  obtain ⟨hcoh, N, hN⟩ := hM
  refine ⟨⟨⟨0, fun n hn => ?_⟩, ⟨N, fun n hn => ?_⟩⟩, fun n => ?_⟩
  · exact IsZero.of_iso
      (Stacks.AlgebraicGeometry.HigherDirectImage.isZero_higherDirectImage_of_neg f M n hn)
      (nonempty_homology_derivedPushforward_single_zero f M n).some
  · exact IsZero.of_iso (hN n hn.le)
      (nonempty_homology_derivedPushforward_single_zero f M n).some
  · have := hcoh n
    exact Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso (R := S.ringCatSheaf)
      (nonempty_homology_derivedPushforward_single_zero f M n).some

/-- **`Rf_*(M[c])` is an object of `D^b_Coh(𝒪_S)`**, in every degree `c`: `M[c]` is a shift of
`M[0]`, the derived direct image commutes with the shift and `D^b_Coh(𝒪_S)` is stable under
it. -/
theorem derivedCategoryBBounded_derivedPushforward_singleFunctor (M : X.Modules)
    (hM : HasCoherentBoundedDirectImages f M) (c : ℤ) :
    DerivedCategoryB.derivedCategoryBBounded (fun N : S.Modules => N.IsCoherent)
      ((derivedPushforwardModules f).obj
        ((DerivedCategory.singleFunctor X.Modules c).obj M)) := by
  have hzero := derivedCategoryBBounded_derivedPushforward_single_zero f M hM
  have hshift : DerivedCategoryB.derivedCategoryBBounded (fun N : S.Modules => N.IsCoherent)
      ((shiftFunctor (DerivedCategory S.Modules) (-c)).obj
        ((derivedPushforwardModules f).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj M))) :=
    ⟨⟨DerivedCategoryB.isBoundedBelow_shift (-c) hzero.1.1,
      DerivedCategoryB.isBoundedAbove_shift (-c) hzero.1.2⟩,
      DerivedCategoryB.derivedCategoryB_shift_mem _ (isCoherent_isWeakSerre S) (-c) hzero.2⟩
  refine (DerivedCategoryB.derivedCategoryBBounded_isClosedUnderIsomorphisms
    (fun N : S.Modules => N.IsCoherent) (isCoherent_isWeakSerre S)).of_iso ?_ hshift
  exact (((derivedPushforwardModules f).commShiftIso (-c)).app
      ((DerivedCategory.singleFunctor X.Modules 0).obj M)).symm ≪≫
    (derivedPushforwardModules f).mapIso
      (((DerivedCategory.singleFunctors X.Modules).shiftIso (-c) c 0 (by omega)).app M)

/-! ### An object concentrated in one degree -/

/-- **`Rf_*E` is an object of `D^b_Coh(𝒪_S)` for `E` concentrated in a single degree `a`**: such
an `E` is a module placed in degree `a`, namely `H^a(E)`. -/
theorem derivedCategoryBBounded_derivedPushforward_of_pure (a : ℤ)
    (E : DerivedCategory X.Modules)
    (hE : HasCoherentBoundedDirectImages f
      ((DerivedCategory.homologyFunctor X.Modules a).obj E))
    (hGE : E.IsGE a) (hLE : E.IsLE a) :
    DerivedCategoryB.derivedCategoryBBounded (fun N : S.Modules => N.IsCoherent)
      ((derivedPushforwardModules f).obj E) := by
  have hGE' := hGE
  have hLE' := hLE
  obtain ⟨M, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE E a
  have hM : HasCoherentBoundedDirectImages f M :=
    HasCoherentBoundedDirectImages.of_iso f
      ((DerivedCategory.homologyFunctor X.Modules a).mapIso e ≪≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules a).app M) hE
  exact (DerivedCategoryB.derivedCategoryBBounded_isClosedUnderIsomorphisms
      (fun N : S.Modules => N.IsCoherent) (isCoherent_isWeakSerre S)).of_iso
    ((derivedPushforwardModules f).mapIso e).symm
    (derivedCategoryBBounded_derivedPushforward_singleFunctor f M hM a)

/-! ### A bounded object -/

/-- **`Rf_*E` is an object of `D^b_Coh(𝒪_S)` for a bounded `E` whose cohomology sheaves have
coherent, eventually vanishing higher direct images.** Induction on the length of the window:
the canonical truncation triangle splits off the bottom degree, `Rf_*` is exact, and
`D^b_Coh(𝒪_S)` is a triangulated subcategory of `D(𝒪_S)`, coherent modules forming a weak Serre
subcategory. -/
theorem derivedCategoryBBounded_derivedPushforward_of_bounded :
    ∀ (k : ℕ) (a : ℤ) (E : DerivedCategory X.Modules),
      (∀ j : ℤ, a ≤ j → HasCoherentBoundedDirectImages f
        ((DerivedCategory.homologyFunctor X.Modules j).obj E)) →
      E.IsGE a → E.IsLE (a + (k : ℤ)) →
      DerivedCategoryB.derivedCategoryBBounded (fun N : S.Modules => N.IsCoherent)
        ((derivedPushforwardModules f).obj E) := by
  intro k
  induction k with
  | zero =>
    intro a E hE hGE hLE
    have hLE' : E.IsLE a :=
      DerivedCategory.TStructure.t.isLE_of_le E (a + ((0 : ℕ) : ℤ)) a (by omega)
    exact derivedCategoryBBounded_derivedPushforward_of_pure f a E (hE a le_rfl) hGE hLE'
  | succ k ih =>
    intro a E hE hGE hLE
    have hGE' := hGE
    have hLE' := hLE
    have hT : (DerivedCategory.TStructure.t.triangleLEGE a (a + 1) rfl).obj E ∈
        distTriang (DerivedCategory X.Modules) :=
      DerivedCategory.TStructure.t.triangleLEGE_distinguished a (a + 1) rfl E
    have h₁ : DerivedCategoryB.derivedCategoryBBounded (fun N : S.Modules => N.IsCoherent)
        ((derivedPushforwardModules f).obj
          ((DerivedCategory.TStructure.t.truncLE a).obj E)) := by
      refine derivedCategoryBBounded_derivedPushforward_of_pure f a _ ?_ inferInstance
        inferInstance
      have := AlgebraicGeometry.isIso_homology_truncLE E a a le_rfl
      exact HasCoherentBoundedDirectImages.of_iso f
        (asIso ((DerivedCategory.homologyFunctor X.Modules a).map
          ((DerivedCategory.TStructure.t.truncLEι a).app E))).symm (hE a le_rfl)
    have h₃ : DerivedCategoryB.derivedCategoryBBounded (fun N : S.Modules => N.IsCoherent)
        ((derivedPushforwardModules f).obj
          ((DerivedCategory.TStructure.t.truncGE (a + 1)).obj E)) := by
      have hb : ((DerivedCategory.TStructure.t.truncGE (a + 1)).obj E).IsLE (a + 1 + (k : ℤ)) :=
        DerivedCategory.TStructure.t.isLE_of_le _ (a + ((k + 1 : ℕ) : ℤ)) (a + 1 + (k : ℤ))
          (by push_cast; omega)
      refine ih (a + 1) _ (fun j hj => ?_) inferInstance hb
      have := AlgebraicGeometry.isIso_homology_truncGE E (a + 1) j hj
      exact HasCoherentBoundedDirectImages.of_iso f
        (asIso ((DerivedCategory.homologyFunctor X.Modules j).map
          ((DerivedCategory.TStructure.t.truncGEπ (a + 1)).app E))) (hE j (by omega))
    have hdist := (derivedPushforwardModules f).map_distinguished _ hT
    exact ⟨DerivedCategoryB.isBounded_mem_obj₂_of_distinguished _ hdist h₁.1 h₃.1,
      DerivedCategoryB.derivedCategoryB_mem_obj₂_of_distinguished _ (isCoherent_isWeakSerre S)
        _ hdist h₁.2 h₃.2⟩

/-! ### Stacks 08E2 -/

/-- **The hypothesis of [Stacks, Tag 08DS] in this library, out of the named `Prop` that stands
for [Stacks, Tag 02O5].** `HigherDirectImageIsCoherentOverAffineBase` is the affine-base case of
the first assertion of that tag, equivalent to the assertion itself by
`AlgebraicGeometry.ProperCoherentImage.higherDirectImageIsCoherent_iff_overAffineBase`. -/
theorem forall_isCoherent_rightDerivedPlus_of_isProper [IsLocallyNoetherian S]
    (haff : AlgebraicGeometry.ProperCoherentImage.HigherDirectImageIsCoherentOverAffineBase.{u})
    (Z : Scheme.{u}) (g : Z ⟶ S) (hg : IsProper g) (G : Z.Modules) (hG : G.IsCoherent) (q : ℕ) :
    (((Scheme.Modules.pushforward g).rightDerivedPlus (q : ℤ)).obj G).IsCoherent := by
  have := hg
  have := hG
  exact AlgebraicGeometry.ProperCoherentImage.isCoherent_higherDirectImage_of_isProper haff g G q

/-- The higher direct images of a coherent module with proper support vanish in large degrees. -/
private theorem exists_isZero_rightDerivedPlus_of_isProperOver_supp [IsNoetherian S]
    [LocallyOfFiniteType f] (M : X.Modules) (hM : M.IsCoherent)
    (hsupp : IsProperOver f
      ⟨SheafOfModules.supp M, @SheafOfModules.isClosed_supp _ _ _ hM.isFiniteType⟩) :
    ∃ N : ℤ, ∀ p : ℤ, N ≤ p →
      IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj M) := by
  have := hM
  have : M.IsFiniteType := hM.isFiniteType
  have : M.IsQuasicoherent := isQuasicoherent_of_isCoherent M
  obtain ⟨J, G, hG, hJ, he⟩ := exists_isProper_rightDerivedPlus_iso f M hsupp
  have := hJ
  have := hG
  have : G.IsQuasicoherent := isQuasicoherent_of_isCoherent G
  obtain ⟨N, hN⟩ :=
    Stacks.AlgebraicGeometry.HigherDirectImageQcoh.exists_isZero_rightDerivedPlus_pushforward
      (J.subschemeι ≫ f)
  exact ⟨N, fun p hp => IsZero.of_iso (hN p hp G inferInstance) (he p).some⟩

/-- **The hypothesis of the dévissage at a coherent module whose support is proper over `S`.**
Coherence of the higher direct images is [Stacks, Tag 08DS], carried here with
[Stacks, Tag 02O5] as the hypothesis `haff`. Their vanishing in large degrees is
unconditional: by `exists_isProper_rightDerivedPlus_iso` they are the higher direct images of a
coherent module along a *proper* morphism `Z ⟶ S`, which is quasi-compact and quasi-separated
over the quasi-compact base `S`, so [Stacks, Tag 01XJ] provides a uniform vanishing degree. -/
theorem hasCoherentBoundedDirectImages_of_isProperOver_supp [IsNoetherian S]
    [LocallyOfFiniteType f] (M : X.Modules) (hM : M.IsCoherent)
    (hsupp : IsProperOver f
      ⟨SheafOfModules.supp M, @SheafOfModules.isClosed_supp _ _ _ hM.isFiniteType⟩)
    (haff : AlgebraicGeometry.ProperCoherentImage.HigherDirectImageIsCoherentOverAffineBase.{u}) :
    HasCoherentBoundedDirectImages f M := by
  have := hM
  have : M.IsFiniteType := hM.isFiniteType
  have : M.IsQuasicoherent := isQuasicoherent_of_isCoherent M
  refine ⟨fun p => isCoherent_rightDerivedPlus_of_isProperOver_supp f M hsupp
    (forall_isCoherent_rightDerivedPlus_of_isProper haff) p, ?_⟩
  exact exists_isZero_rightDerivedPlus_of_isProperOver_supp f M hM hsupp

/-- **The hypothesis of the dévissage at a coherent module with proper support, for an affine
`f`.** The same as `hasCoherentBoundedDirectImages_of_isProperOver_supp`, with the appeal to
[Stacks, Tag 02O5] discharged by
`isCoherent_rightDerivedPlus_of_isAffineHom`: the closed subscheme the reduction produces is
proper and affine over `S`, hence finite over it. -/
theorem hasCoherentBoundedDirectImages_of_isAffineHom [IsNoetherian S] [LocallyOfFiniteType f]
    [IsAffineHom f] (M : X.Modules) (hM : M.IsCoherent)
    (hsupp : IsProperOver f
      ⟨SheafOfModules.supp M, @SheafOfModules.isClosed_supp _ _ _ hM.isFiniteType⟩) :
    HasCoherentBoundedDirectImages f M := by
  have := hM
  have : M.IsFiniteType := hM.isFiniteType
  have : M.IsQuasicoherent := isQuasicoherent_of_isCoherent M
  refine ⟨fun p => isCoherent_rightDerivedPlus_of_isAffineHom f M hsupp p, ?_⟩
  exact exists_isZero_rightDerivedPlus_of_isProperOver_supp f M hM hsupp

/-- A bounded `E` whose cohomology sheaves all satisfy `HasCoherentBoundedDirectImages` has
`Rf_*E` in `D^b_Coh(𝒪_S)`. -/
private theorem derivedCategoryBBounded_derivedPushforward_of_hasCoherentBoundedDirectImages
    (E : DerivedCategory X.Modules)
    (h : ∀ j : ℤ, HasCoherentBoundedDirectImages f
      ((DerivedCategory.homologyFunctor X.Modules j).obj E))
    (a b : ℤ) (hGE : E.IsGE a) (hLE : E.IsLE b) :
    DerivedCategoryB.derivedCategoryBBounded (fun N : S.Modules => N.IsCoherent)
      ((derivedPushforwardModules f).obj E) := by
  have hLE' := hLE
  exact derivedCategoryBBounded_derivedPushforward_of_bounded f (b - a).toNat a E
    (fun j _ => h j) hGE
    (DerivedCategory.TStructure.t.isLE_of_le E b (a + (((b - a).toNat : ℕ) : ℤ)) (by omega))

/-- **The dévissage behind [Stacks, Tag 08E2], with [Stacks, Tag 02O5] as its only hypothesis.**
Let `S` be a Noetherian scheme, `f : X ⟶ S` locally of finite type and `E` a bounded object of
`D(𝒪_X)` whose cohomology sheaves are coherent with support proper over `S`. Then `Rf_*E` is an
object of `D^b_Coh(𝒪_S)`.

The hypothesis `haff` is
`AlgebraicGeometry.ProperCoherentImage.HigherDirectImageIsCoherentOverAffineBase`, the named
`Prop` this library carries for [Stacks, Tag 02O5]: the affine-base case of that tag's first
assertion, equivalent to the assertion itself. It is the hypothesis that
`isCoherent_rightDerivedPlus_of_isProperOver_supp`, this library's form of [Stacks, Tag 08DS],
needs. It is supplied in
`StacksFrontier/AlgebraicGeometry/ProperSupportCoherent/DerivedDirectImageUnconditional.lean`, where
`derivedCategoryBBounded_derivedPushforward_of_properSupp` carries the tag's label. -/
theorem derivedCategoryBBounded_derivedPushforward_of_isProperOver_supp [IsNoetherian S]
    [LocallyOfFiniteType f] (E : DerivedCategory X.Modules)
    (hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsCoherent)
    (hsupp : ∀ j : ℤ, IsProperOver f
      ⟨SheafOfModules.supp ((DerivedCategory.homologyFunctor X.Modules j).obj E),
        @SheafOfModules.isClosed_supp _ _ _ (hcoh j).isFiniteType⟩)
    (haff : AlgebraicGeometry.ProperCoherentImage.HigherDirectImageIsCoherentOverAffineBase.{u})
    (a b : ℤ) (hGE : E.IsGE a) (hLE : E.IsLE b) :
    DerivedCategoryB.derivedCategoryBBounded (fun N : S.Modules => N.IsCoherent)
      ((derivedPushforwardModules f).obj E) := by
  exact derivedCategoryBBounded_derivedPushforward_of_hasCoherentBoundedDirectImages f E
    (fun j => hasCoherentBoundedDirectImages_of_isProperOver_supp f _ (hcoh j) (hsupp j) haff)
    a b hGE hLE

/-- **[Stacks, Tag 08E2] for an affine `f`**, unconditionally: for `S` Noetherian, `f` locally of
finite type and affine, and `E` a bounded object of `D(𝒪_X)` whose cohomology sheaves are
coherent with support proper over `S`, `Rf_*E` is an object of `D^b_Coh(𝒪_S)`.

`IsAffineHom f` is a hypothesis the source does not make, so this is a special case of the tag
rather than one of its clauses, and its label is not attached. -/
theorem derivedCategoryBBounded_derivedPushforward_of_isAffineHom [IsNoetherian S]
    [LocallyOfFiniteType f] [IsAffineHom f] (E : DerivedCategory X.Modules)
    (hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsCoherent)
    (hsupp : ∀ j : ℤ, IsProperOver f
      ⟨SheafOfModules.supp ((DerivedCategory.homologyFunctor X.Modules j).obj E),
        @SheafOfModules.isClosed_supp _ _ _ (hcoh j).isFiniteType⟩)
    (a b : ℤ) (hGE : E.IsGE a) (hLE : E.IsLE b) :
    DerivedCategoryB.derivedCategoryBBounded (fun N : S.Modules => N.IsCoherent)
      ((derivedPushforwardModules f).obj E) := by
  exact derivedCategoryBBounded_derivedPushforward_of_hasCoherentBoundedDirectImages f E
    (fun j => hasCoherentBoundedDirectImages_of_isAffineHom f _ (hcoh j) (hsupp j)) a b hGE hLE

end DerivedPushforward

end Stacks.AlgebraicGeometry.ProperSupportCoherent

end
