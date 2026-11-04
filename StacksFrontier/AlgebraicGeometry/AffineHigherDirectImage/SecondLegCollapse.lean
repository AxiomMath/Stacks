module

public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.PushforwardTExactness
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.Qcqs
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AugmentationInvertedByDerivedFunctor
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionAlongAComposite

/-!
# Vanishing of a higher direct image descends along an affine second leg

Let `g : A ⟶ B` be a quasi-compact and quasi-separated morphism of schemes, let `c : B ⟶ C` be
an **affine** morphism and let `M` be a quasi-coherent `𝒪_A`-module.  If the degree `n` higher
direct image of `M` along the composite `g ≫ c` vanishes, then so does the degree `n` higher
direct image along `g`.

This is the degeneration of the relative Leray spectral sequence along an affine second leg, in
the only form a vanishing argument needs.  No spectral sequence is constructed.  The argument is
carried out in the unbounded derived category, where all three inputs are available
unconditionally:

* `R(g ≫ c)_* ≅ Rg_* ⋙ Rc_*`, the composition isomorphism for the chosen derived direct images
  (`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso`);
* `H ⁱ(Rc_*E) ≅ c_*H ⁱ(E)` for an affine `c` and an `E` with quasi-coherent cohomology, together
  with the conservativity of `c_*` on quasi-coherent modules, which together are
  `Stacks.AlgebraicGeometry.AffinePushforwardTExactness`'s
  `isZero_homology_of_isZero_homology_derivedPushforward`;
* quasi-coherence of the cohomology sheaves of `Rg_*M`, which is [Stacks, Tag 01XJ] and is where
  the quasi-compactness and quasi-separatedness of `g` are used.

The passage between Mathlib's `ℕ`-indexed `Functor.rightDerived`, the `ℤ`-indexed
`Functor.rightDerivedPlus` and the cohomology of the unbounded derived direct image is
`nonempty_homologyFunctor_derivedPushforward_iso` below, read in both directions.

## Main results

* `Stacks.AffineHigherDirectImage.nonempty_homologyFunctor_derivedPushforward_iso`:
  `H ⁱ(Rf_*(F[0])) ≅ R ⁱ f_* F`, up to isomorphism, for an arbitrary morphism of schemes.
* `Stacks.AffineHigherDirectImage.isQuasicoherent_homologyFunctor_derivedPushforward`:
  [Stacks, Tag 01XJ] read at the unbounded derived direct image.
* `Stacks.AffineHigherDirectImage.isZero_rightDerived_pushforward_of_comp_eq_of_isAffineHom`:
  **the statement above**, with the composite given by an equation `g ≫ c = p` so that it can be
  applied to a morphism already named.

## Implementation notes

The isomorphism comparing the two models of the derived direct image is only ever produced
inside a `Nonempty`, because
`Stacks.Perfect.CechAugmentation.nonempty_obj_iso_rightDerivedFunctorPlus` chooses an injective
resolution; nothing below depends on which isomorphism is chosen, every use being the transport
of a `Prop`.

**No `@[stacks ...]` attribute.** [Stacks, Tag 01F6] asserts a spectral sequence, and nothing
here produces one; the statement proved is a consequence of its degeneration which the source
states nowhere as a numbered result — it is a step inside the proof of [Stacks, Tag 0FZI].

## References

* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 01F6](https://stacks.math.columbia.edu/tag/01F6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry RingedSpaceModuleAdjunction DerivedCategory
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.AlgebraicGeometry.AffinePushforwardTExactness

universe u

namespace Stacks.AffineHigherDirectImage

attribute [local instance 10000] HasDerivedCategory.standard

variable {X Y : Scheme.{u}}

/-! ### The two models of a higher direct image -/

/-- **`H ⁱ(Rf_*(F[0]))` is `R ⁱ f_* F`.**  The unbounded derived direct image of a module placed
in degree zero has the same cohomology as the bounded below right derived functor of the direct
image, in every degree.

The comparison from degreewise direct image to the unbounded derived direct image is invertible
at every K-injective complex, which is the hypothesis of
`Stacks.Perfect.CechAugmentation.nonempty_obj_iso_rightDerivedFunctorPlus`; the module placed in
degree zero is bounded below, which is its other hypothesis. -/
theorem nonempty_homologyFunctor_derivedPushforward_iso (f : X ⟶ Y) (F : X.Modules) (i : ℤ) :
    Nonempty ((homologyFunctor Y.Modules i).obj
        ((derivedPushforward f.toLRSHom.toShHom).obj ((singleFunctor X.Modules 0).obj F)) ≅
      ((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F) := by
  have hE : ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj F).obj.IsGE 0 := by
    show ((singleFunctor X.Modules 0).obj F).IsGE 0
    infer_instance
  obtain ⟨e⟩ := Stacks.Perfect.CechAugmentation.nonempty_obj_iso_rightDerivedFunctorPlus
    (modulePushforward f.toLRSHom.toShHom) (derivedPushforward f.toLRSHom.toShHom)
    (derivedPushforwardUnit f.toLRSHom.toShHom)
    (fun I hI => isIso_derivedPushforwardUnit_app_of_isKInjective _ I hI)
    ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj F) 0 hE
  exact ⟨(homologyFunctor Y.Modules i).mapIso e⟩

/-- **[Stacks, Tag 01XJ] at the unbounded derived direct image.**  The cohomology sheaves of
`Rf_*(F[0])` are quasi-coherent for a quasi-compact and quasi-separated `f` and a quasi-coherent
`F`. -/
theorem isQuasicoherent_homologyFunctor_derivedPushforward (f : X ⟶ Y) [QuasiCompact f]
    [QuasiSeparated f] (F : X.Modules) [F.IsQuasicoherent] (i : ℤ) :
    ((homologyFunctor Y.Modules i).obj
      ((derivedPushforward f.toLRSHom.toShHom).obj
        ((singleFunctor X.Modules 0).obj F))).IsQuasicoherent := by
  obtain ⟨e⟩ := nonempty_homologyFunctor_derivedPushforward_iso f F i
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso e.symm
    (Stacks.AlgebraicGeometry.HigherDirectImageQcoh.isQuasicoherent_higherDirectImage f F i)

/-! ### Descent of the vanishing along an affine second leg -/

/-- **Vanishing of a higher direct image descends along an affine second leg.**  Let
`g : A ⟶ B` be quasi-compact and quasi-separated, let `c : B ⟶ C` be affine, let `p` be the
composite and let `M` be a quasi-coherent `𝒪_A`-module.  If `R ⁿ p_* M = 0` then
`R ⁿ g_* M = 0`.

The cohomology sheaves of `Rg_*M` are quasi-coherent by [Stacks, Tag 01XJ], so the direct image
along the affine `c` commutes with them, and `R ⁿ p_* M = c_*(R ⁿ g_* M)`; the direct image
along an affine morphism is conservative on quasi-coherent modules, which is the faithfulness of
[Stacks, Tag 01SB]. -/
theorem isZero_rightDerived_pushforward_of_comp_eq_of_isAffineHom {A B C : Scheme.{u}}
    (g : A ⟶ B) [QuasiCompact g] [QuasiSeparated g] (c : B ⟶ C) [IsAffineHom c] (p : A ⟶ C)
    (hp : g ≫ c = p) (M : A.Modules) [M.IsQuasicoherent] (n : ℕ)
    (h : IsZero (((Scheme.Modules.pushforward p).rightDerived n).obj M)) :
    IsZero (((Scheme.Modules.pushforward g).rightDerived n).obj M) := by
  subst hp
  have h₁ : IsZero (((Scheme.Modules.pushforward (g ≫ c)).rightDerivedPlus (n : ℤ)).obj M) :=
    (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff
      (Scheme.Modules.pushforward (g ≫ c)) n M).1 h
  obtain ⟨e⟩ := nonempty_homologyFunctor_derivedPushforward_iso (g ≫ c) M (n : ℤ)
  have h₂ : IsZero ((homologyFunctor C.Modules (n : ℤ)).obj
      ((derivedPushforward (g ≫ c).toLRSHom.toShHom).obj
        ((singleFunctor A.Modules 0).obj M))) := h₁.of_iso e
  have h₃ : IsZero ((homologyFunctor C.Modules (n : ℤ)).obj
      ((derivedPushforward c.toLRSHom.toShHom).obj
        ((derivedPushforward g.toLRSHom.toShHom).obj ((singleFunctor A.Modules 0).obj M)))) :=
    h₂.of_iso ((homologyFunctor C.Modules (n : ℤ)).mapIso
      ((derivedPushforwardCompIso g.toLRSHom.toShHom c.toLRSHom.toShHom).app
        ((singleFunctor A.Modules 0).obj M)))
  have h₄ := isZero_homology_of_isZero_homology_derivedPushforward c
    ((derivedPushforward g.toLRSHom.toShHom).obj ((singleFunctor A.Modules 0).obj M))
    (fun i => isQuasicoherent_homologyFunctor_derivedPushforward g M i) h₃
  obtain ⟨e'⟩ := nonempty_homologyFunctor_derivedPushforward_iso g M (n : ℤ)
  exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff
    (Scheme.Modules.pushforward g) n M).2 (h₄.of_iso e'.symm)

end Stacks.AffineHigherDirectImage

end
