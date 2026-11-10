module

public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.Coherence
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.ProperSupport
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.SchemeTheoreticCoherent
public import StacksFrontier.AlgebraicGeometry.ProperCoherentImage.FiniteFibres
public import StacksFrontier.AlgebraicGeometry.RelativeCechAcyclic.Basic

/-!
# Higher direct images of a coherent module whose support is proper over the base

Let `S` be a locally Noetherian scheme, let `f : X ⟶ S` be locally of finite type — *not*
proper — and let `F` be a coherent `𝒪_X`-module whose support is proper over `S` in the sense of
[Stacks, Tag 0CYM]. Then `R ᵖ f_* F` is a coherent `𝒪_S`-module for every `p`. This is
[Stacks, Tag 08DS].

The reduction the source performs is carried out in full here: `F` is the direct image of a
coherent module `G` on its scheme-theoretic support `Z`, the composite `g : Z ⟶ S` is proper
([Stacks, Tag 0CYS]), the closed immersion `Z ⟶ X` is affine so `R ᵖ f_*(i_* G) ≅ R ᵖ g_* G`,
and the conclusion for `g` is [Stacks, Tag 02O5]. What remains to be supplied is exactly
[Stacks, Tag 02O5], which is carried as the single hypothesis `h02O5` of
`isCoherent_rightDerivedPlus_of_isProperOver_supp`; it is discharged, giving the statement with
no hypothesis at all, in
`StacksFrontier/AlgebraicGeometry/ProperSupportCoherent/Unconditional.lean`.

## Main definitions

All names below lie in the namespace `Stacks.AlgebraicGeometry.ProperSupportCoherent`.

* `rightDerivedPushforwardCompIso`: `R ⁿ (i ≫ f)_* G ≅ R ⁿ f_*(i_* G)` for `i` affine and `G`
  quasi-coherent, in Mathlib's `ℕ`-indexing.
* `rightDerivedPlusPushforwardCompIso`: the same isomorphism in the `ℤ`-indexing
  `Functor.rightDerivedPlus`, at a nonnegative degree.

## Main results

* `exists_isProper_rightDerivedPlus_iso`: the reduction of [Stacks, Tag 08DS] to
  [Stacks, Tag 02O5] — a module of finite type whose support is proper over `S` has, in every
  degree, higher direct images isomorphic to those of a coherent module along a *proper* morphism
  to `S`.
* `isCoherent_rightDerivedPlus_of_isProperOver_supp`: [Stacks, Tag 08DS], with
  [Stacks, Tag 02O5] as its only hypothesis.
* `isCoherent_pushforward_of_isProperOver_supp`: the same for the ordinary direct image `f_* F`.
* `nonempty_rightDerivedPlusPushforwardCompIso`: the transfer isomorphism in every degree,
  negative ones included.
* `isCoherent_rightDerivedPlus_of_isAffineHom`: the conclusion of [Stacks, Tag 08DS] when `f` is
  in addition affine, where the appeal to [Stacks, Tag 02O5] is discharged, a proper affine
  morphism being finite.

## Implementation notes

The hypotheses on `F` are quasi-coherence together with finite type rather than coherence. The
source `X` is locally Noetherian here, because `f` is locally of finite type over a locally
Noetherian base, and on a locally Noetherian scheme the two are the same condition
([Stacks, Tag 01XZ]); this is also the form in which the scheme-theoretic support and
[Stacks, Tag 0CYS] are stated, so no transport is needed.

The transfer `R ⁿ (i ≫ f)_* G ≅ R ⁿ f_*(i_* G)` is the collapse of the relative Leray spectral
sequence at a module acyclic for `i_*`, obtained directly as
`Stacks.AcyclicCollapse.objIso` rather than through a spectral sequence. Its two hypotheses are
`Stacks.AlgebraicGeometry.RelativeCechAcyclic.rightAcyclic_pushforward_obj_injective`, which
needs nothing of `i` or `f`, and the vanishing of `R ⁿ i_* G` for `n > 0`, which is
[Stacks, Tag 01XC] for the affine morphism `i`. The equality
`i_* ⋙ f_* = (i ≫ f)_*` of functors is
`Stacks.AlgebraicGeometry.RelativeCechAcyclic.pushforward_comp`, an `rfl`, so the two sides of
the statement are the same object up to that definitional identification.

Degrees are handled uniformly: in negative degrees both higher direct images vanish, so the
isomorphism is between zero objects, and in nonnegative degrees the two indexings of the right
derived functors are compared by `Stacks.DerivedIndexing.rightDerivedIso`.

## References

* [Stacks Project, Tag 08DS](https://stacks.math.columbia.edu/tag/08DS)
* [Stacks Project, Tag 0CYS](https://stacks.math.columbia.edu/tag/0CYS)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 01Y6](https://stacks.math.columbia.edu/tag/01Y6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.ProperSupportCoherent

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### Pushing forward along an affine morphism -/

section Transfer

variable {Z X S : Scheme.{u}} (i : Z ⟶ X) [IsAffineHom i] (f : X ⟶ S) (G : Z.Modules)
  [G.IsQuasicoherent]

/-- **`R ⁿ (i ≫ f)_* G ≅ R ⁿ f_*(i_* G)` for `i` affine and `G` quasi-coherent**, in Mathlib's
`ℕ`-indexing.

This is the collapse [Stacks, Tag 089W] of the relative Leray spectral sequence for the pair
`(i_*, f_*)` at `G`: the pushforward of an injective module is acyclic for any pushforward, and
`R ⁿ i_* G = 0` for `n > 0` by [Stacks, Tag 01XC]. The source of the isomorphism is
`R ⁿ (i_* ⋙ f_*) G`, which is `R ⁿ (i ≫ f)_* G` because the two functors are equal. -/
noncomputable def rightDerivedPushforwardCompIso (n : ℕ) :
    ((Scheme.Modules.pushforward (i ≫ f)).rightDerived n).obj G ≅
      ((Scheme.Modules.pushforward f).rightDerived n).obj
        ((Scheme.Modules.pushforward i).obj G) :=
  Stacks.AcyclicCollapse.objIso (Scheme.Modules.pushforward i) (Scheme.Modules.pushforward f)
    (fun I hI ↦
      Stacks.AlgebraicGeometry.RelativeCechAcyclic.rightAcyclic_pushforward_obj_injective i f I hI)
    (fun m hm ↦ Stacks.AffineHigherDirectImage.isZero_rightDerived_pushforward i G m hm) n

/-- **`R ⁿ (i ≫ f)_* G ≅ R ⁿ f_*(i_* G)` for `i` affine and `G` quasi-coherent**, in the
`ℤ`-indexing `Functor.rightDerivedPlus` at a nonnegative degree.

This is `rightDerivedPushforwardCompIso` read through
`Stacks.DerivedIndexing.rightDerivedIso`, the comparison of the two indexings. -/
noncomputable def rightDerivedPlusPushforwardCompIso (n : ℕ) :
    ((Scheme.Modules.pushforward (i ≫ f)).rightDerivedPlus (n : ℤ)).obj G ≅
      ((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj
        ((Scheme.Modules.pushforward i).obj G) :=
  ((Stacks.DerivedIndexing.rightDerivedIso
      (Scheme.Modules.pushforward (i ≫ f)) n).app G).symm ≪≫
    rightDerivedPushforwardCompIso i f G n ≪≫
    (Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) n).app
      ((Scheme.Modules.pushforward i).obj G)

/-- **`R ᵖ (i ≫ f)_* G ≅ R ᵖ f_*(i_* G)` for `i` affine and `G` quasi-coherent, in every
degree.** In negative degrees both sides vanish, so there is nothing to compare; in nonnegative
degrees this is `rightDerivedPlusPushforwardCompIso`. -/
theorem nonempty_rightDerivedPlusPushforwardCompIso (p : ℤ) :
    Nonempty (((Scheme.Modules.pushforward (i ≫ f)).rightDerivedPlus p).obj G ≅
      ((Scheme.Modules.pushforward f).rightDerivedPlus p).obj
        ((Scheme.Modules.pushforward i).obj G)) := by
  rcases lt_or_ge p 0 with hp | hp
  · exact ⟨(Stacks.AlgebraicGeometry.HigherDirectImage.isZero_higherDirectImage_of_neg
      (i ≫ f) G p hp).iso
      (Stacks.AlgebraicGeometry.HigherDirectImage.isZero_higherDirectImage_of_neg f
        ((Scheme.Modules.pushforward i).obj G) p hp)⟩
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    exact ⟨rightDerivedPlusPushforwardCompIso i f G n⟩

end Transfer

/-! ### The reduction of Tag 08DS to Tag 02O5 -/

section Reduction

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType f]
  (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]

/-- **The reduction of [Stacks, Tag 08DS] to [Stacks, Tag 02O5].** If the support of a
quasi-coherent module `F` of finite type is proper over `S`, then there is a closed subscheme
`Z ⊆ X` proper over `S` carrying a coherent module `G` whose higher direct images along
`Z ⟶ S` are, in every degree, isomorphic to those of `F` along `f`.

`Z` is the scheme-theoretic support of `F`: it is proper over `S` by [Stacks, Tag 0CYS], it
carries a coherent descent `G` of `F` by [Stacks, Tag 01Y5], and the comparison of higher direct
images is `rightDerivedPlusPushforwardCompIso` for the closed immersion `Z ⟶ X`, which is
affine. -/
theorem exists_isProper_rightDerivedPlus_iso
    (hF : IsProperOver f ⟨SheafOfModules.supp F, SheafOfModules.isClosed_supp F⟩) :
    ∃ (J : X.IdealSheafData) (G : J.subscheme.Modules),
      G.IsCoherent ∧ IsProper (J.subschemeι ≫ f) ∧
        ∀ p : ℤ, Nonempty
          (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F ≅
            ((Scheme.Modules.pushforward (J.subschemeι ≫ f)).rightDerivedPlus p).obj G) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨G, hG, ⟨e⟩⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_coherent_module_on_schemeTheoreticSupport F
  have : G.IsQuasicoherent := isQuasicoherent_of_isCoherent G
  refine ⟨AlgebraicGeometry.Scheme.Modules.schemeTheoreticSupport F, G, hG,
    (AlgebraicGeometry.Scheme.Modules.isProperOver_supp_iff_isProper_schemeTheoreticSupport
      f F).1 hF, fun p ↦ ?_⟩
  obtain ⟨c⟩ := nonempty_rightDerivedPlusPushforwardCompIso
    (AlgebraicGeometry.Scheme.Modules.schemeTheoreticSupport F).subschemeι f G p
  exact ⟨((Scheme.Modules.pushforward f).rightDerivedPlus p).mapIso e.symm ≪≫ c.symm⟩

/-- **[Stacks, Tag 08DS], with [Stacks, Tag 02O5] as its only hypothesis.** For `S` locally
Noetherian, `f` locally of finite type and `F` quasi-coherent of finite type with support proper
over `S`, every higher direct image `R ᵖ f_* F` is coherent, granted the conclusion of
[Stacks, Tag 02O5] for proper morphisms to `S`.

The hypothesis `h02O5` is the statement of [Stacks, Tag 02O5] over the base `S`, in the
nonnegative degrees the source states it for; it is used at the single morphism `Z ⟶ S` produced
by `exists_isProper_rightDerivedPlus_iso`. Negative degrees need no hypothesis, the higher
direct image vanishing there.

It is discharged in
`StacksFrontier/AlgebraicGeometry/ProperSupportCoherent/Unconditional.lean`, which proves the
resulting hypothesis-free statement. -/
theorem isCoherent_rightDerivedPlus_of_isProperOver_supp
    (hF : IsProperOver f ⟨SheafOfModules.supp F, SheafOfModules.isClosed_supp F⟩)
    (h02O5 : ∀ (Z : Scheme.{u}) (g : Z ⟶ S), IsProper g → ∀ G : Z.Modules, G.IsCoherent →
      ∀ q : ℕ, (((Scheme.Modules.pushforward g).rightDerivedPlus (q : ℤ)).obj G).IsCoherent)
    (p : ℤ) :
    (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F).IsCoherent := by
  rcases lt_or_ge p 0 with hp | hp
  · exact Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_isZero
      (R := S.ringCatSheaf)
      (Stacks.AlgebraicGeometry.HigherDirectImage.isZero_higherDirectImage_of_neg f F p hp)
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    obtain ⟨J, G, hG, hJ, he⟩ := exists_isProper_rightDerivedPlus_iso f F hF
    have := h02O5 _ _ hJ G hG n
    exact Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso (R := S.ringCatSheaf)
      (he (n : ℤ)).some

/-- **The direct image in [Stacks, Tag 08DS].** The degree-zero case of
`isCoherent_rightDerivedPlus_of_isProperOver_supp`, stated for the ordinary direct image
`f_* F`, which is `R ⁰ f_* F` because the pushforward is left exact. -/
theorem isCoherent_pushforward_of_isProperOver_supp
    (hF : IsProperOver f ⟨SheafOfModules.supp F, SheafOfModules.isClosed_supp F⟩)
    (h02O5 : ∀ (Z : Scheme.{u}) (g : Z ⟶ S), IsProper g → ∀ G : Z.Modules, G.IsCoherent →
      ∀ q : ℕ, (((Scheme.Modules.pushforward g).rightDerivedPlus (q : ℤ)).obj G).IsCoherent) :
    ((Scheme.Modules.pushforward f).obj F).IsCoherent :=
  have := isCoherent_rightDerivedPlus_of_isProperOver_supp f F hF h02O5 0
  Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso (R := S.ringCatSheaf)
    (Stacks.AlgebraicGeometry.HigherDirectImage.higherDirectImageZeroIso f F).symm

/-- **[Stacks, Tag 08DS] for an affine `f`.** Here the appeal to [Stacks, Tag 02O5] is
discharged: the morphism `Z ⟶ S` produced by the reduction is the composite of a closed
immersion with `f`, hence affine, and it is proper, so it is finite and
[Stacks, Tag 01Y6] applies.

`IsAffineHom f` is a hypothesis the source does not make, so this is a special case of the tag
rather than one of its clauses. -/
theorem isCoherent_rightDerivedPlus_of_isAffineHom [IsAffineHom f]
    (hF : IsProperOver f ⟨SheafOfModules.supp F, SheafOfModules.isClosed_supp F⟩) (p : ℤ) :
    (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F).IsCoherent := by
  obtain ⟨J, G, hG, hJ, he⟩ := exists_isProper_rightDerivedPlus_iso f F hF
  have :=
    AlgebraicGeometry.ProperCoherentImage.isCoherent_higherDirectImage_of_isProper_of_isAffineHom
      (J.subschemeι ≫ f) G hG p
  exact Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso (R := S.ringCatSheaf)
    (he p).some

end Reduction

end Stacks.AlgebraicGeometry.ProperSupportCoherent

end
