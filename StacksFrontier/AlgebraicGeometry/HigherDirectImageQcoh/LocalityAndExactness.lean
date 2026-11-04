module

public import StacksFrontier.AlgebraicGeometry.HigherDirectImageAffine.AffineMorphismVanishing
public import StacksFrontier.AlgebraicGeometry.ProjectiveCoherentImage.Basic
public import StacksFrontier.AlgebraicGeometry.QcohShortExact.QcohExtension
public import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-coherence of higher direct images: the locality and exactness inputs

[Stacks, Tag 01XJ] part (1) asserts that the higher direct images `R ᵖ f_* F` of a
quasi-coherent module along a quasi-compact quasi-separated morphism of schemes are
quasi-coherent. The proof of the source has three separable ingredients, and this file supplies
the two that are not cohomological:

* **locality on the base.** Quasi-coherence is local on `S` and higher direct images commute with
  restriction to an open of the base ([Stacks, Tag 01E5]), so the assertion for `f` follows from
  the assertion for every `f ∣_ V` with `V` an affine open of `S`. This is
  `isQuasicoherent_rightDerivedPlus_of_affineOpens`, which needs no hypothesis on `f` or on `F`
  at all.
* **the five-term exactness step.** In the source's induction over the quasi-compact opens of
  `X`, the module `R ᵖ g_* F` is read off a long exact Mayer–Vietoris sequence: it "sits in the
  middle of a short exact sequence with a cokernel of a map between quasi-coherent sheaves on the
  left and a kernel of a map between quasi-coherent sheaves on the right". That argument is
  `isQuasicoherent_of_exact₄`, which is about an arbitrary four-arrow exact sequence of modules on
  an arbitrary scheme and mentions no cohomology.

The base case of the induction, `isQuasicoherent_rightDerivedPlus_restrict_isAffineOpen`, is also
recorded here: over an affine base the inclusion of an affine open composed with `f` is an affine
morphism, so [Stacks, Tag 01XC] applies.

What is *not* here, and is the whole remaining content of Tag 01XJ part (1), is the
Mayer–Vietoris long exact sequence for the four opens `U ⊔ V`, `U`, `V`, `U ⊓ V` of `X`; see the
implementation notes.

## Main results

All three live in the namespace `Stacks.AlgebraicGeometry.HigherDirectImageQcoh`.

* `isQuasicoherent_of_exact₄`: the middle term of a four-arrow exact sequence is quasi-coherent
  as soon as the four outer terms are.
* `isQuasicoherent_rightDerivedPlus_of_affineOpens`: quasi-coherence of `R ᵖ f_* F` is local on
  the base.
* `isQuasicoherent_rightDerivedPlus_restrict_isAffineOpen`: the base case of the induction of
  [Stacks, Tag 01XJ] over an affine base.

## Implementation notes

**The exactness step.** From an exact sequence `A → B → M → C → D` one extracts the short exact
sequence `0 ⟶ coker a ⟶ M ⟶ ker d ⟶ 0`: the left map is `cokernel.desc a b`, a monomorphism
exactly because the sequence is exact at `B`
(`CategoryTheory.ShortComplex.exact_iff_mono_cokernel_desc`), and the right map is
`kernel.lift d c`, an epimorphism exactly because the sequence is exact at `C`
(`CategoryTheory.ShortComplex.exact_iff_epi_kernel_lift`). Exactness in the middle is exactness at
`M` transported along the epimorphism `cokernel.π a` and the monomorphism `kernel.ι d`, in two
applications of `CategoryTheory.ShortComplex.exact_iff_of_epi_of_isIso_of_mono`; the transport has
to be done in two steps because that lemma takes a morphism of short complexes, and the two
comparison maps point in opposite directions. Quasi-coherence of the two ends is then the kernel
and cokernel closure, and the conclusion is the extension case of [Stacks, Tag 01IE].

**Why the locality statement is unconditional.** `isQuasicoherent_rightDerivedPlus_of_affineOpens`
carries no `QuasiCompact`/`QuasiSeparated` hypothesis: those are needed to prove the hypothesis
`h`, not to deduce the conclusion from it. The negative degrees are discharged separately,
because the scheme-level form of [Stacks, Tag 01E5] available here,
`AlgebraicGeometry.ProjectiveCoherentImage.higherDirectImageRestrictObjIso`, is stated in a degree
presented as a natural number; in negative degrees the higher direct image vanishes outright and
no comparison is needed.

**The remaining input, stated precisely.** The source's induction uses
[Stacks, Tag 08DR] (`Stacks.AlgebraicGeometry.CompactOpenInduction.of_isCompact`), whose step
concerns a quasi-compact open `U`, an affine open `V` and their union. Feeding it needs the long
exact sequence relating `R ᵖ` of the four functors `restrictPush O W ⋙ modulePushforward f` for
`W = U ⊔ V, U, V, U ⊓ V`. The integer-indexed relative Mayer–Vietoris sequence
`Stacks.Cohomology.RelativeMayerVietoris.relativeMayerVietorisPlus` ([Stacks, Tag 01EC]) is
available, but only for a cover of the *whole* source: its hypothesis is
`Set.range iU.hom.base ∪ Set.range iV.hom.base = Set.univ`. Equivalently
`Stacks.Cohomology.RestrictionCover.restrictionCoverShortExact_object` requires `U ⊔ V = ⊤`, the
left term of the short complex being the identity functor. The missing statement is that same
short complex with `restrictPush O (U ⊔ V)` in place of the identity functor, for arbitrary `U`
and `V`; its proof is the existing one with the single open `W` at which sections are taken
replaced by `W ⊓ (U ⊔ V)`, since the only use of `U ⊔ V = ⊤` is
`Stacks.Cohomology.RestrictionCover.openIntersection_cover`.

## References

* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 01IE](https://stacks.math.columbia.edu/tag/01IE)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.HigherDirectImageQcoh

/-! ### The five-term exactness step -/

variable {X : Scheme.{u}}

/-- **The middle of a four-arrow exact sequence of quasi-coherent modules is quasi-coherent.**
Let `A ⟶ B ⟶ M ⟶ C ⟶ D` be exact at `B`, at `M` and at `C`, with `A`, `B`, `C`, `D` all
quasi-coherent. Then `M` is quasi-coherent.

This is the step [Stacks, Tag 01XJ] takes from the relative Mayer–Vietoris sequence, where `M` is
a higher direct image and the four neighbouring terms are already known to be quasi-coherent: `M`
sits in a short exact sequence whose left term is `coker (A ⟶ B)` and whose right term is
`ker (C ⟶ D)`. -/
theorem isQuasicoherent_of_exact₄ {A B M C D : X.Modules} (a : A ⟶ B) (b : B ⟶ M) (c : M ⟶ C)
    (d : C ⟶ D) (hab : a ≫ b = 0) (hbc : b ≫ c = 0) (hcd : c ≫ d = 0)
    (eB : (ShortComplex.mk a b hab).Exact) (eM : (ShortComplex.mk b c hbc).Exact)
    (eC : (ShortComplex.mk c d hcd).Exact)
    (hA : A.IsQuasicoherent) (hB : B.IsQuasicoherent) (hC : C.IsQuasicoherent)
    (hD : D.IsQuasicoherent) : M.IsQuasicoherent := by
  have := hA; have := hB; have := hC; have := hD
  set φ : cokernel a ⟶ M := cokernel.desc a b hab with hφ
  set ψ : M ⟶ kernel d := kernel.lift d c hcd with hψ
  have hπφ : cokernel.π a ≫ φ = b := by rw [hφ]; exact cokernel.π_desc a b hab
  have hψι : ψ ≫ kernel.ι d = c := by rw [hψ]; exact kernel.lift_ι d c hcd
  -- the two outer maps are a monomorphism and an epimorphism, by exactness at `B` and at `C`
  have hmono : Mono φ := (ShortComplex.exact_iff_mono_cokernel_desc _).1 eB
  have hepi : Epi ψ := (ShortComplex.exact_iff_epi_kernel_lift _).1 eC
  -- the composite vanishes
  have hzero : φ ≫ ψ = 0 := by
    have h₁ : cokernel.π a ≫ φ ≫ ψ = 0 := by
      rw [← Category.assoc, hπφ]
      have : b ≫ ψ ≫ kernel.ι d = 0 := by rw [← Category.assoc, Category.assoc, hψι]; exact hbc
      exact (cancel_mono (kernel.ι d)).1 (by simpa using this)
    exact (cancel_epi (cokernel.π a)).1 (by simpa using h₁)
  -- exactness in the middle, transported from exactness at `M` in two steps
  have eQMC : (ShortComplex.mk φ c (by rw [← hψι, ← Category.assoc, hzero, zero_comp])).Exact := by
    refine (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
      (S₁ := ShortComplex.mk b c hbc) (S₂ := ShortComplex.mk φ c _)
      { τ₁ := cokernel.π a, τ₂ := 𝟙 M, τ₃ := 𝟙 C
        comm₁₂ := by simpa using hπφ
        comm₂₃ := by simp }).1 eM
  have eQMK : (ShortComplex.mk φ ψ hzero).Exact := by
    refine (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
      (S₁ := ShortComplex.mk φ ψ hzero) (S₂ := ShortComplex.mk φ c _)
      { τ₁ := 𝟙 (cokernel a), τ₂ := 𝟙 M, τ₃ := kernel.ι d
        comm₁₂ := by simp
        comm₂₃ := by simpa using hψι.symm }).2 eQMC
  exact QcohExtension.isQuasicoherent_X₂_of_shortExact (ShortComplex.mk φ ψ hzero)
    (ShortComplex.ShortExact.mk' eQMK hmono hepi) inferInstance inferInstance

/-! ### Locality on the base -/

variable {S : Scheme.{u}}

/-- **Quasi-coherence of a higher direct image is local on the base.** If for every affine open
`V` of `S` the `p`-th higher direct image along `f ∣_ V` of the restriction of `F` to `f⁻¹(V)` is
quasi-coherent, then `R ᵖ f_* F` is quasi-coherent.

This is the first paragraph of the proof of [Stacks, Tag 01XJ]: quasi-coherence is local on `S`
(`Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_of_restrict_affineOpens`) and
forming higher direct images commutes with restriction to an open of the base, which is
[Stacks, Tag 01E5]. No hypothesis on `f` or on `F` is used: quasi-compactness and
quasi-separatedness are what the hypothesis `h` needs, not what this deduction needs. -/
theorem isQuasicoherent_rightDerivedPlus_of_affineOpens (f : X ⟶ S) (F : X.Modules) (p : ℤ)
    (h : ∀ V : S.affineOpens,
      (((Scheme.Modules.pushforward (f ∣_ (V : S.Opens))).rightDerivedPlus p).obj
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ (V : S.Opens)).ι).obj F)).IsQuasicoherent) :
    (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F).IsQuasicoherent := by
  rcases lt_or_ge p 0 with hp | hp
  · exact HigherDirectImage.isQuasicoherent_higherDirectImage_of_neg f F p hp
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = (n : ℤ) := ⟨p.toNat, (Int.toNat_of_nonneg hp).symm⟩
    refine QuasicoherentColimits.isQuasicoherent_of_restrict_affineOpens _ fun V => ?_
    have := h V
    exact (SheafOfModules.isQuasicoherent (V : S.Opens).toScheme.ringCatSheaf).prop_of_iso
      (_root_.AlgebraicGeometry.ProjectiveCoherentImage.higherDirectImageRestrictObjIso f
        (V : S.Opens) F n) inferInstance

/-! ### The base case of the induction over quasi-compact opens -/

/-- **The base case of the induction of [Stacks, Tag 01XJ] over an affine base.** For `S` affine,
`F` quasi-coherent and `W` an affine open of `X`, every higher direct image along the restriction
`W.ι ≫ f` of the restriction of `F` to `W` is quasi-coherent.

Both `W` and `S` are affine, so `W.ι ≫ f` is an affine morphism, and
[Stacks, Tag 01XC] gives the conclusion in every integer degree. -/
theorem isQuasicoherent_rightDerivedPlus_restrict_isAffineOpen (f : X ⟶ S) [IsAffine S]
    (F : X.Modules) [F.IsQuasicoherent] {W : X.Opens} (hW : IsAffineOpen W) (p : ℤ) :
    (((Scheme.Modules.pushforward (W.ι ≫ f)).rightDerivedPlus p).obj
      ((Scheme.Modules.restrictFunctor W.ι).obj F)).IsQuasicoherent := by
  have : IsAffine W.toScheme := hW
  have : ((Scheme.Modules.restrictFunctor W.ι).obj F).IsQuasicoherent := inferInstance
  exact HigherDirectImageAffine.isQuasicoherent_higherDirectImage_of_isAffineHom (W.ι ≫ f) _ p

end Stacks.AlgebraicGeometry.HigherDirectImageQcoh

end
