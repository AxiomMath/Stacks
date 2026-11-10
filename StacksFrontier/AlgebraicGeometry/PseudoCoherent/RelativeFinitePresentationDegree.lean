module

public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentLocal
public import
  StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeFinitePresentation.FinitePushforward
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeFinitePresentation.Transport
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.RelativeFinitePresentation.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffinePairLocality
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FinitePresentationDegreeMinusOne
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentReflection
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Relative pseudo-coherence of a sheaf of modules in degree minus one

Let `f : X ⟶ S` be a morphism of schemes locally of finite type and let `ℱ` be a sheaf of
`𝒪_X`-modules. Stacks 09UM describes relative `m`-pseudo-coherence of `ℱ` in the three ranges
`0 < m`, `m = 0` and `m = -1`. This file proves the case `m = -1`: relative
`(-1)`-pseudo-coherence is the conjunction of quasi-coherence and relative finite presentation.

## Main results

* `Scheme.Modules.isPseudoCoherentFromAfterPushforward_singleFunctor_neg_one_iff`:
  the local condition of Stacks 09UI in degree `-1` for a sheaf of modules placed in degree zero
  is finite presentation of its direct image. This is Stacks 09V9(2) read along the closed
  immersion.
* `Scheme.Hom.isModulePseudoCoherentFrom_neg_one_iff_isFinitelyPresentedRelative`:
  **Stacks 09UM, the degree-minus-one clause.**

## Implementation notes

By Stacks 09UJ relative `(-1)`-pseudo-coherence is the local condition of Stacks 09UI at every
compatible pair of affine opens `U ⊆ f ⁻¹ᵁ V`, and at such a pair the condition says that the
direct image of `ℱ|_U` along a closed immersion `i : U ⟶ 𝔸ⁿ_V` over `V` is of finite presentation.

Unlike the degree-zero clause, where Stacks 01C4 lets the condition be read as a property of
`ℱ|_U` itself, there is no such transfer of finite presentation along `i_*`; the right-hand side
of the per-pair statement is therefore kept as finite presentation of `i_*(ℱ|_U)`. The two
implications of the clause then come from two different readings of that condition:

* quasi-coherence of `ℱ` is local on `X`, and on each affine open it follows from finite
  presentation of `i_*(ℱ|_U)` because `i_*` is fully faithful
  (`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_isFinitePresentation_pushforward`);
* relative finite presentation is checked on affine pairs (Stacks 09T7), where the structure
  morphism of `𝔸ⁿ_V` is locally of finite presentation, so Stacks 09T8 turns finite presentation
  of `i_*(ℱ|_U)` into its finite presentation relative to `V` and Stacks 09T9 moves that across
  the finite morphism `i` to `ℱ|_U`.

The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`,
which is made a local instance; there is no global instance, so a user of these results makes the
same declaration.

## References

* [The Stacks Project, Lemma 36.61.8 (09UM)](https://stacks.math.columbia.edu/tag/09UM)
* [The Stacks Project, Definition 36.61.1 (09UI)](https://stacks.math.columbia.edu/tag/09UI)
* [The Stacks Project, Lemma 36.61.5 (09UJ)](https://stacks.math.columbia.edu/tag/09UJ)
* [The Stacks Project, Lemma 36.60.11 (09V9)](https://stacks.math.columbia.edu/tag/09V9)
* [The Stacks Project, Lemma 36.57.4 (09T7)](https://stacks.math.columbia.edu/tag/09T7)
* [The Stacks Project, Lemma 36.57.5 (09T8)](https://stacks.math.columbia.edu/tag/09T8)
* [The Stacks Project, Lemma 36.57.6 (09T9)](https://stacks.math.columbia.edu/tag/09T9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace Scheme.Modules

attribute [local instance] HasDerivedCategory.standard

/-- **The local condition of Stacks 09UI in degree `-1` for a sheaf of modules is finite
presentation of its direct image.** For a closed immersion `i` out of an open subscheme `U` of
`X`, the derived pushforward along `i` of the restriction of `ℱ` to `U`, placed in degree zero,
is `(-1)`-pseudo-coherent exactly when `i_*(ℱ|_U)` is of finite presentation.

Pushing forward along a closed immersion and restricting to an open subscheme are both exact, so
both carry a module placed in degree zero to a module placed in degree zero; by Stacks 09V9(2)
the condition is then finite presentation of `i_*(ℱ|_U)`.

In contrast to the degree-zero statement
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_singleFunctor_zero_iff`,
the right-hand side is not a property of `ℱ|_U`: finite presentation is not transferred along
`i_*` the way finite type is by Stacks 01C4. -/
public theorem isPseudoCoherentFromAfterPushforward_singleFunctor_neg_one_iff
    {X Y : Scheme.{u}} (U : X.Opens) (i : (U : Scheme.{u}) ⟶ Y) [IsClosedImmersion i]
    (F : X.Modules) :
    IsPseudoCoherentFromAfterPushforward i
        ((restrictFunctor U.ι).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj F)) (-1) ↔
      ((pushforward i).obj ((restrictFunctor U.ι).obj F)).IsFinitePresentation := by
  rw [isPseudoCoherentFromAfterPushforward_iff]
  refine Iff.trans ?_
    (RingedSpace.isPseudoCoherentFrom_singleFunctor_zero_neg_one_iff_isFinitePresentation.{u,
      u + 1} _)
  let e := (pushforward i).mapDerivedCategory.mapIso
      ((Functor.mapDerivedCategorySingleFunctor (restrictFunctor U.ι) 0).app F) ≪≫
    (Functor.mapDerivedCategorySingleFunctor (pushforward i) 0).app
      ((restrictFunctor U.ι).obj F)
  exact ⟨fun h => h.of_iso e, fun h => h.of_iso e.symm⟩

end Scheme.Modules

/-- The structure morphism of the affine space `𝔸ⁿ_V` is locally of finite presentation. -/
private theorem locallyOfFinitePresentation_affineSpace_over (n : ℕ) (V : Scheme.{u}) :
    LocallyOfFinitePresentation (AffineSpace.over (ULift.{u} (Fin n)) V).hom := by
  rw [AffineSpace.over_hom_eq]; infer_instance

/-- Relative finite presentation only depends on the ring map that defines the algebra structure
of the base. -/
private theorem finitePresentationRel_congr_algebraMap {R A M : Type u} [CommRing R] [CommRing A]
    [AddCommGroup M] [Module A M] {φ ψ : R →+* A} (hφψ : φ = ψ)
    (h : @Module.FinitePresentationRel R A _ _ φ.toAlgebra M _ _) :
    @Module.FinitePresentationRel R A _ _ ψ.toAlgebra M _ _ := by
  subst hφψ
  exact h

/-- Relative finite presentation of the sections of a module over a pair of opens depends only on
the opens, and not on the containment witnessing that the source open lies over the target one. -/
private theorem finitePresentationRel_congr_opens {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    {U U' : X.Opens} {V V' : S.Opens} (eU : U = U') (eV : V = V') (h : U ≤ f ⁻¹ᵁ V)
    (h' : U' ≤ f ⁻¹ᵁ V') :
    (letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U h).hom.toAlgebra;
      Module.FinitePresentationRel Γ(S, V) Γ(X, U) Γ(F, U)) ↔
    (letI : Algebra Γ(S, V') Γ(X, U') := (f.appLE V' U' h').hom.toAlgebra;
      Module.FinitePresentationRel Γ(S, V') Γ(X, U') Γ(F, U')) := by
  subst eU
  subst eV
  rfl

namespace Scheme.Hom

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 09UM, the degree-minus-one clause.** For a morphism of schemes locally of finite
type, a sheaf of `𝒪_X`-modules is `(-1)`-pseudo-coherent relative to the base if and only if it
is quasi-coherent and finitely presented relative to the base.

Stacks 09UJ turns relative `(-1)`-pseudo-coherence into the local condition of Stacks 09UI at
every compatible pair of affine opens `U ⊆ f ⁻¹ᵁ V`, where by Stacks 09V9(2) it says that the
direct image of `ℱ|_U` along a closed immersion `i : U ⟶ 𝔸ⁿ_V` over `V` is of finite
presentation. Finite presentation of `i_*(ℱ|_U)` gives quasi-coherence of `ℱ|_U`, and
quasi-coherence is local on `X`; it also gives relative finite presentation of `ℱ|_U` over `V`
by Stacks 09T8 and 09T9, which is the affine-pair criterion of Stacks 09T7. Conversely Stacks
09T7 restricts relative finite presentation to the pair, and Stacks 09T9 and 09T8 turn it back
into finite presentation of `i_*(ℱ|_U)` at a closed immersion of our own choosing. -/
@[stacks 09UM "degree_minus_one", sga "6 III 1.2.1"]
public theorem isModulePseudoCoherentFrom_neg_one_iff_isFinitelyPresentedRelative
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (F : X.Modules) :
    IsModulePseudoCoherentFrom f F (-1) ↔
      (F.IsQuasicoherent ∧ IsFinitelyPresentedRelative f F) := by
  constructor
  · intro hF
    have hqc : F.IsQuasicoherent := by
      refine Stacks.Modules.isQuasicoherent_of_restrict F
        (I := {p : X.affineOpens × S.affineOpens // (p.1 : X.Opens) ≤ f ⁻¹ᵁ (p.2 : S.Opens)})
        (fun p => (p.1.1 : X.Opens)) ?_ ?_
      · refine top_unique fun x _ => ?_
        obtain ⟨V, hV, hfxV, -⟩ :=
          exists_isAffineOpen_mem_and_subset (U := ⊤) (x := f.base x) (by simp)
        obtain ⟨U, hU, hxU, hUV⟩ :=
          exists_isAffineOpen_mem_and_subset (U := f ⁻¹ᵁ V) (x := x) hfxV
        exact Opens.mem_iSup.mpr ⟨⟨(⟨U, hU⟩, ⟨V, hV⟩), hUV⟩, hxU⟩
      · intro p
        obtain ⟨n, i, hi, hio, hpc⟩ :=
          isPseudoCoherentFromOnAffinePair_of_isPseudoCoherentFrom f hF p.1.1 p.1.2 p.2
        have := hi
        exact Scheme.Modules.isQuasicoherent_of_isFinitePresentation_pushforward i _
          ((Scheme.Modules.isPseudoCoherentFromAfterPushforward_singleFunctor_neg_one_iff
            _ i F).1 hpc)
    have := hqc
    refine ⟨hqc, (isFinitelyPresentedRelative_iff_affine f F).2 fun U hU V hV hUV => ?_⟩
    have hUa : IsAffine (U : Scheme.{u}) := hU
    have hVa : IsAffine (V : Scheme.{u}) := hV
    obtain ⟨n, i, hi, hio, hpc⟩ :=
      isPseudoCoherentFromOnAffinePair_of_isPseudoCoherentFrom f hF ⟨U, hU⟩ ⟨V, hV⟩ hUV
    have := hi
    have hfin :=
      (Scheme.Modules.isPseudoCoherentFromAfterPushforward_singleFunctor_neg_one_iff U i F).1 hpc
    have := hfin
    have hover := locallyOfFinitePresentation_affineSpace_over n (V : Scheme.{u})
    have := locallyOfFiniteType_resLE f V U hUV
    have hrelU : IsFinitelyPresentedRelative (f.resLE V U hUV) (F.restrict U.ι) :=
      (isFinitelyPresentedRelative_pushforward_iff i (f.resLE V U hUV) _ hio _).1
        ((isFinitelyPresentedRelative_iff_isFinitePresentation _ _).2 hfin)
    have hWT : (⊤ : (U : Scheme.{u}).Opens) ≤ f.resLE V U hUV ⁻¹ᵁ ⊤ := by simp
    have hsec := (isFinitelyPresentedRelative_iff_affine (f.resLE V U hUV)
      (F.restrict U.ι)).1 hrelU ⊤ (isAffineOpen_top _) ⊤ (isAffineOpen_top _) hWT
    have hUV' : U.ι ''ᵁ ⊤ ≤ f ⁻¹ᵁ V.ι ''ᵁ ⊤ := (f.le_resLE_preimage_iff hUV ⊤ ⊤).mp hWT
    have hsec' := finitePresentationRel_congr_algebraMap
      (congrArg CommRingCat.Hom.hom (Scheme.Hom.resLE_appLE f hUV ⊤ ⊤ hWT)) hsec
    let : Algebra Γ((V : Scheme.{u}), ⊤) Γ((U : Scheme.{u}), ⊤) :=
      (f.appLE (V.ι ''ᵁ ⊤) (U.ι ''ᵁ ⊤) hUV').hom.toAlgebra
    let : Module Γ((U : Scheme.{u}), ⊤) Γ(F, U.ι ''ᵁ ⊤) := by
      change Module Γ(X, U.ι ''ᵁ ⊤) Γ(F, U.ι ''ᵁ ⊤)
      infer_instance
    let e : Γ(F.restrict U.ι, ⊤) ≃ₗ[Γ((U : Scheme.{u}), ⊤)] Γ(F, U.ι ''ᵁ ⊤) :=
      { (F.restrictAppIso U.ι ⊤).addCommGroupIsoToAddEquiv with
        map_smul' := fun r m => by
          change (F.restrictAppIso U.ι ⊤).hom (r • m) = r • (F.restrictAppIso U.ι ⊤).hom m
          have hr : (U.ι.appIso ⊤).inv r = r := by
            rw [Scheme.Opens.ι_appIso]
            exact CategoryTheory.id_apply r
          have h0 := Scheme.Modules.smul_restrictAppIso_hom_apply U.ι F ⊤ r m
          rw [hr] at h0
          exact h0 }
    have ht := Module.FinitePresentationRel.of_linearEquiv e hsec'
    exact (finitePresentationRel_congr_opens f F U.ι_image_top V.ι_image_top hUV' hUV).mp ht
  · rintro ⟨hqc, hrel⟩
    have := hqc
    refine isPseudoCoherentFrom_of_forall_affinePair f _ (-1) fun U V hUV => ?_
    obtain ⟨n, i, hi, hio⟩ := exists_isClosedImmersion_affineSpace_resLE f V U hUV
    have := hi
    have hUa : IsAffine (U.1 : Scheme.{u}) := U.2
    have hVa : IsAffine (V.1 : Scheme.{u}) := V.2
    have hover := locallyOfFinitePresentation_affineSpace_over n (V.1 : Scheme.{u})
    have := locallyOfFiniteType_resLE f V.1 U.1 hUV
    have hfin := (isFinitelyPresentedRelative_iff_isFinitePresentation
      (AffineSpace.over (ULift.{u} (Fin n)) (V.1 : Scheme.{u})).hom
      ((Scheme.Modules.pushforward i).obj (F.restrict U.1.ι))).1
        ((isFinitelyPresentedRelative_pushforward_iff i (f.resLE V.1 U.1 hUV) _ hio _).2
          (isFinitelyPresentedRelative_resLE F hrel U.1 V.1 hUV))
    exact ⟨n, i, hi, hio,
      (Scheme.Modules.isPseudoCoherentFromAfterPushforward_singleFunctor_neg_one_iff
        U.1 i F).2 hfin⟩

end Scheme.Hom

end AlgebraicGeometry

end
