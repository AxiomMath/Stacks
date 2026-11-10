module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.VectorBundlePullbackIso
public import StacksFrontier.AlgebraicGeometry.Constructions.GradedAlgebraSheafQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Constructions.SymmetricAlgebraAffineSections
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankSections
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Local
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffinePairStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineLocalFree

/-!
# The vector bundle of a finite locally free sheaf is an affine-space bundle

Let `X` be a scheme and let `ℰ` be a finite locally free `𝒪_X`-module of rank `r`. The vector
bundle associated to `ℰ` is the relative spectrum `p : E = Spec_X(Sym(ℰ)) ⟶ X` of the symmetric
algebra of `ℰ`. This file proves that `p` is an affine-space bundle of rank `r`: every point of
`X` has an open neighbourhood over which `p` restricts to the projection `𝔸^r_U ⟶ U`.

Over an affine open `V` on which `ℰ` is free with basis indexed by `Fin r` the ring of sections
`Γ(V, Sym(ℰ))` is the polynomial algebra `Γ(X, V)[x_1, …, x_r]`, whose spectrum is `𝔸^r_V`; and
the part of `E` over `V` is the spectrum of those sections. Combined with the rank-zero
isomorphism of Stacks 02TY this gives that tag, in rank zero, for the relative spectrum of the
symmetric algebra itself.

## Main results

* `Stacks.Chow.exists_isAffineOpen_basis_sections` — a finite locally free sheaf of rank `r` has,
  around every point, an affine open on which its sections are free with a basis indexed by
  `Fin r`.
* `Stacks.Chow.exists_iso_affineSpace_of_mvPolynomialSections` — the part of the relative spectrum
  of a quasi-coherent algebra over an affine open whose sections are a polynomial algebra in `r`
  variables is affine `r`-space over that open, compatibly with the two projections.
* `Stacks.Chow.isAffineSpaceBundle_vectorBundleToBase` — **the projection
  `Spec_X(Sym(ℰ)) ⟶ X` of the vector bundle of a finite locally free sheaf of rank `r` is an
  affine-space bundle of rank `r`.**
* `Stacks.Chow.flatPullbackChow_bijective_vectorBundleToBase_zero` — **Stacks 02TY in rank zero,
  stated for the relative spectrum of the symmetric algebra.**

## Implementation notes

The local identification is assembled from three cartesian squares and one algebra isomorphism.
Mathlib's `AlgebraicGeometry.isPullback_morphismRestrict` and the gluing square
`AlgebraicGeometry.Scheme.Cover.RelativeGluingData.isPullback_natTrans_ι_toBase` of the relative
spectrum are two pullback squares over the same cospan, so their upper-left corners agree: the
part of `E` over an affine open `V` is `Spec Γ(V, Sym(ℰ))`, over `V` through the structure map of
the algebra sheaf. `Stacks.SymAlgSections.symSectionsRingEquiv` identifies those sections with
`Sym_{Γ(X, V)}(Γ(ℰ, V))` and `SymmetricAlgebra.equivMvPolynomial` identifies that with a
polynomial ring once a basis of `Γ(ℰ, V)` is chosen; both identifications fix the base ring, which
is what makes the composite an isomorphism over `V`. The last step is
`AlgebraicGeometry.AffineSpace.isoSpecFinOfIso`, which reads affine `r`-space over a scheme
presented as a spectrum as the spectrum of a polynomial ring in `Fin r` variables.

A basis of `Γ(ℰ, V)` indexed by `Fin r` is obtained from the local trivialisations of `ℰ` by
shrinking a trivialising open to an affine one, transporting the trivialisation along
`Stacks.Modules.nonempty_restrictIsoFree_of_range_subset`, and reading it as a basis through the
index-preserving module-sheaf dictionary `tilde_fixed_free_iff_basis` of Stacks 05JM. The index
type of the trivialisations is `ULift (Fin r)` and is renamed to `Fin r` by `Module.Basis.reindex`,
matching the polynomial ring of `AffineSpace.isoSpecFinOfIso`.

In rank `r ≥ 1` the isomorphism of Stacks 02TY is available in this repository only for a bundle
presented as the complement of the divisor at infinity in a projective completion, and the
identification of `Spec_X(Sym(ℰ))` with such a complement needs the projective space bundle
formula of Stacks 02TX and Stacks 02TR, neither of which is proved here; so only the rank-zero
half is restated below.

That identification is available over an *affine* base, and in terms of rings rather than
sheaves: over an affine open `V` of `X`, with `R = Γ(X, V)` and `M = Γ(ℰ, V)`, the complement of
the divisor at infinity is the standard open `D₊(T)` of the chart `Proj Γ(V, Sym^*(ℰ)[T])`
(`Stacks.Chow.ProjectiveCompletion.chart_preimage_openT`) and its ring of functions is `Sym_R(M)`
(`Stacks.Chow.ProjectiveCompletion.chartAwayEquiv`, in
`StacksFrontier/AlgebraicGeometry/Chow/ProjectiveCompletionChern/ChartRing.lean`). Neither the
comparison of its two ends with `AlgebraicGeometry.Scheme.Modules.vectorBundle` and with
`Stacks.RelativeProj.projectiveBundle` nor any gluing over a non-affine base is used below.

## References

* [Stacks Project, Tag 02TY](https://stacks.math.columbia.edu/tag/02TY)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 05JM](https://stacks.math.columbia.edu/tag/05JM)
* [Stacks Project, Tag 01M0](https://stacks.math.columbia.edu/tag/01M0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.Chow

/-! ### A basis of the sections over a small enough affine open -/

/-- **A finite locally free sheaf of rank `r` has free sections of rank `r` over small enough
affine opens.** Around every point there is an affine open `V` on which `Γ(ℰ, V)` is a free
`Γ(X, V)`-module with a basis indexed by `Fin r`. -/
theorem exists_isAffineOpen_basis_sections {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]
    (r : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (x : X) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧
      Nonempty (Module.Basis (Fin r) Γ(X, V) Γ(E, V)) := by
  obtain ⟨U, hxU, ⟨e⟩⟩ := Scheme.Modules.isFiniteLocallyFreeOfRank_of_sheaf E r x
  obtain ⟨V, hV, hxV, hVU⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset hxU
  have hr : Set.range hV.fromSpec.base ⊆ Set.range U.ι.base := by
    rw [← Scheme.Hom.coe_opensRange, hV.opensRange_fromSpec, Scheme.Opens.range_ι]
    exact hVU
  obtain ⟨e'⟩ := Stacks.Modules.nonempty_restrictIsoFree_of_range_subset U.ι hV.fromSpec E
    (ULift.{u} (Fin r)) hr e
  have hb := (tilde_fixed_free_iff_basis Γ(X, V) Γ(E, V) (ULift.{u} (Fin r))).mp
    ⟨Stacks.Modules.tildeIsoRestrictFromSpec E hV ≪≫ e'⟩
  exact ⟨V, hV, hxV, hb.map fun b ↦ b.reindex Equiv.ulift⟩

/-! ### The local identification with affine space -/

/-- **The relative spectrum of a quasi-coherent algebra whose sections over an affine open are a
polynomial algebra in `r` variables is affine `r`-space over that open.** The identification is
compatible with the two projections, so it exhibits the restriction of the structure morphism as
the projection of affine `r`-space. -/
theorem exists_iso_affineSpace_of_mvPolynomialSections {X : Scheme.{u}}
    (A : Stacks.RelativeSpec.AlgebraSheaf X)
    [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent A] (V : X.affineOpens) (r : ℕ)
    (ψ : A.right.obj.obj (op (V.1 : X.Opens)) ≃+* MvPolynomial (Fin r) Γ(X, (V.1 : X.Opens)))
    (hψ : ∀ s : Γ(X, (V.1 : X.Opens)),
      ψ ((A.hom.hom.app (op (V.1 : X.Opens))).hom s) = MvPolynomial.C s) :
    ∃ e : (relativeSpecToBase A ⁻¹ᵁ (V.1 : X.Opens)).toScheme ≅
        𝔸(ULift.{u} (Fin r); (V.1 : X.Opens).toScheme),
      e.hom ≫ (𝔸(ULift.{u} (Fin r); (V.1 : X.Opens).toScheme) ↘ (V.1 : X.Opens).toScheme) =
        relativeSpecToBase A ∣_ (V.1 : X.Opens) := by
  have h1 := isPullback_morphismRestrict (relativeSpecToBase A) (V.1 : X.Opens)
  have h2 := (relativeSpecGluingData A).isPullback_natTrans_ι_toBase V
  let φ : A.right.obj.obj (op (V.1 : X.Opens)) ≅
      CommRingCat.of (MvPolynomial (Fin r) Γ(X, (V.1 : X.Opens))) :=
    { hom := CommRingCat.ofHom ψ.toRingHom
      inv := CommRingCat.ofHom ψ.symm.toRingHom
      hom_inv_id := CommRingCat.hom_ext (RingHom.ext fun x ↦ ψ.symm_apply_apply x)
      inv_hom_id := CommRingCat.hom_ext (RingHom.ext fun x ↦ ψ.apply_symm_apply x) }
  have hφ : A.hom.hom.app (op (V.1 : X.Opens)) ≫ φ.hom =
      CommRingCat.ofHom
        (MvPolynomial.C (σ := Fin r) (R := Γ(X, (V.1 : X.Opens)))) :=
    CommRingCat.hom_ext (RingHom.ext hψ)
  have hover : (AffineSpace.isoSpecFinOfIso r V.2.isoSpec).inv ≫
      (𝔸(ULift.{u} (Fin r); (V.1 : X.Opens).toScheme) ↘ (V.1 : X.Opens).toScheme) =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.C (σ := Fin r) (R := Γ(X, (V.1 : X.Opens))))) ≫ V.2.isoSpec.inv :=
    AffineSpace.isoSpecFinOfIso_inv_over r V.2.isoSpec
  have hC : CommRingCat.ofHom
      (MvPolynomial.C (σ := Fin r) (R := Γ(X, (V.1 : X.Opens)))) ≫ φ.inv =
      A.hom.hom.app (op (V.1 : X.Opens)) := φ.comp_inv_eq.mpr hφ.symm
  set e₂₃ : (relativeSpecGluingData A).functor.obj V ≅
      𝔸(ULift.{u} (Fin r); (V.1 : X.Opens).toScheme) :=
    Scheme.Spec.mapIso φ.symm.op ≪≫ (AffineSpace.isoSpecFinOfIso r V.2.isoSpec).symm with he₂₃
  have hstep : e₂₃.hom ≫
      (𝔸(ULift.{u} (Fin r); (V.1 : X.Opens).toScheme) ↘ (V.1 : X.Opens).toScheme) =
      (specSectionsToBase A).app V := by
    rw [he₂₃]
    change Spec.map φ.inv ≫ (AffineSpace.isoSpecFinOfIso r V.2.isoSpec).inv ≫ _ = _
    rw [hover, ← Spec.map_comp_assoc, hC]
    rfl
  refine ⟨h1.isoIsPullback _ _ h2 ≪≫ e₂₃, ?_⟩
  change ((h1.isoIsPullback _ _ h2).hom ≫ e₂₃.hom) ≫ _ = _
  rw [Category.assoc, hstep]
  exact h1.isoIsPullback_hom_fst _ _ h2

/-! ### The sections of the symmetric algebra over a trivialising affine open -/

/-- **`Γ(V, Sym(ℰ))` is a polynomial ring in `r` variables** over an affine open `V` carrying a
basis of `Γ(ℰ, V)` indexed by `Fin r`: the symmetric algebra of a free module of rank `r` is the
polynomial algebra on its basis. -/
def symmetricAlgebraSectionsMvPolynomialEquiv {X : Scheme.{u}} (E : X.Modules)
    [E.IsQuasicoherent] {V : X.Opens} (hV : IsAffineOpen V) {r : ℕ}
    (b : Module.Basis (Fin r) Γ(X, V) Γ(E, V)) :
    (Scheme.Modules.symmetricAlgebraSheaf X E).right.obj.obj (op V) ≃+*
      MvPolynomial (Fin r) Γ(X, V) :=
  (Stacks.SymAlgSections.symSectionsRingEquiv E hV).symm.trans
    (SymmetricAlgebra.equivMvPolynomial b).toRingEquiv

/-- The identification of `Γ(V, Sym(ℰ))` with a polynomial ring carries the structure map of the
algebra sheaf to the inclusion of constants, so it is an isomorphism of `Γ(X, V)`-algebras. -/
theorem symmetricAlgebraSectionsMvPolynomialEquiv_app {X : Scheme.{u}} (E : X.Modules)
    [E.IsQuasicoherent] {V : X.Opens} (hV : IsAffineOpen V) {r : ℕ}
    (b : Module.Basis (Fin r) Γ(X, V) Γ(E, V)) (s : Γ(X, V)) :
    symmetricAlgebraSectionsMvPolynomialEquiv E hV b
        (((Scheme.Modules.symmetricAlgebraSheaf X E).hom.hom.app (op V)).hom s) =
      MvPolynomial.C s := by
  rw [← Stacks.SymAlgSections.symSectionsRingEquiv_algebraMap E hV s]
  change (SymmetricAlgebra.equivMvPolynomial b)
      ((Stacks.SymAlgSections.symSectionsRingEquiv E hV).symm
        (Stacks.SymAlgSections.symSectionsRingEquiv E hV
          (algebraMap Γ(X, V) (SymmetricAlgebra Γ(X, V) Γ(E, V)) s))) = _
  rw [RingEquiv.symm_apply_apply, AlgEquiv.commutes, MvPolynomial.algebraMap_eq]

/-! ### The vector bundle of a finite locally free sheaf -/

/-- **The projection `p : Spec_X(Sym(ℰ)) ⟶ X` of the vector bundle of a finite locally free sheaf
`ℰ` of rank `r` is an affine-space bundle of rank `r`.** Over an affine open on which `ℰ` is free
the sections of `Sym(ℰ)` form a polynomial ring in `r` variables, whose spectrum is affine
`r`-space over that open. -/
theorem isAffineSpaceBundle_vectorBundleToBase {X : Scheme.{u}} (E : X.Modules)
    [E.IsQuasicoherent] (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    IsAffineSpaceBundle (Scheme.Modules.vectorBundleToBase X E) r := by
  intro y
  obtain ⟨V, hV, hyV, ⟨b⟩⟩ := exists_isAffineOpen_basis_sections E r y
  obtain ⟨e, he⟩ := exists_iso_affineSpace_of_mvPolynomialSections
    (Scheme.Modules.symmetricAlgebraSheaf X E) ⟨V, hV⟩ r
    (symmetricAlgebraSectionsMvPolynomialEquiv E hV b)
    (symmetricAlgebraSectionsMvPolynomialEquiv_app E hV b)
  exact ⟨V, hyV, e, he⟩

/-- The projection of the vector bundle of a finite locally free sheaf is locally of finite
type. -/
theorem locallyOfFiniteType_vectorBundleToBase {X : Scheme.{u}} (E : X.Modules)
    [E.IsQuasicoherent] (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    LocallyOfFiniteType (Scheme.Modules.vectorBundleToBase X E) :=
  locallyOfFiniteType_of_isAffineSpaceBundle _ r (isAffineSpaceBundle_vectorBundleToBase E r)

/-- The projection of the vector bundle of a finite locally free sheaf is flat. -/
theorem flat_vectorBundleToBase {X : Scheme.{u}} (E : X.Modules)
    [E.IsQuasicoherent] (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    AlgebraicGeometry.Flat (Scheme.Modules.vectorBundleToBase X E) :=
  flat_of_isAffineSpaceBundle _ r (isAffineSpaceBundle_vectorBundleToBase E r)

/-- The projection of the vector bundle of a finite locally free sheaf of rank `r` has relative
dimension `r`. -/
theorem relativeDimension_vectorBundleToBase {X : Scheme.{u}} (E : X.Modules)
    [E.IsQuasicoherent] (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    letI _ := locallyOfFiniteType_vectorBundleToBase E r
    AlgebraicGeometry.RelativeDimension (Scheme.Modules.vectorBundleToBase X E) r :=
  let _ := locallyOfFiniteType_vectorBundleToBase E r
  relativeDimension_of_isAffineSpaceBundle _ r (isAffineSpaceBundle_vectorBundleToBase E r)

/-- The projection of the vector bundle of a finite locally free sheaf of rank zero is an
isomorphism. -/
theorem isIso_vectorBundleToBase_zero {X : Scheme.{u}} (E : X.Modules)
    [E.IsQuasicoherent]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 0] :
    IsIso (Scheme.Modules.vectorBundleToBase X E) :=
  isIso_of_isAffineSpaceBundle_zero _ (isAffineSpaceBundle_vectorBundleToBase E 0)

/-- **Stacks 02TY in rank zero, for the relative spectrum of the symmetric algebra.** Let `X` be
locally of finite type over the base of chapter 42, let `ℰ` be a finite locally free sheaf of rank
zero on `X` and let `p : E = Spec_X(Sym(ℰ)) ⟶ X` be the associated vector bundle. Then
`p^* : A_k(X) ⟶ A_k(E)` is bijective for every `k`.

The bundle is the relative spectrum of `Sym(ℰ)`, which is the tag's own object;
`Stacks.Chow.isAffineSpaceBundle_vectorBundleToBase` supplies the local triviality that
`Stacks.Chow.flatPullbackChow_bijective_of_isAffineSpaceBundle_zero` needs, and the flatness,
local finite type and relative dimension of `p` come from it as well. The instance of Stacks 02S1
that writes the map down is not an extra assumption: a rank-zero bundle projection is an
isomorphism, so it is produced by
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_of_isIso`. -/
@[stacks 02TY "the isomorphism in rank zero, the bundle now the relative spectrum of the \
symmetric algebra of a finite locally free sheaf of rank zero rather than an abstract \
affine-space bundle"]
theorem flatPullbackChow_bijective_vectorBundleToBase_zero (C : ChowSituation.{u})
    {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (E : X.Modules)
    [E.IsQuasicoherent]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 0] (k : ℤ) :
    letI _ := locallyOfFiniteType_vectorBundleToBase E 0
    letI _ := flat_vectorBundleToBase E 0
    letI _ := isIso_vectorBundleToBase_zero E
    Function.Bijective (flatPullbackChow C
      (Scheme.Modules.vectorBundleToBase X E ≫ sX) sX
      (Scheme.Modules.vectorBundleToBase X E) rfl 0
      (relativeDimension_vectorBundleToBase E 0) k
      (flatPullbackFactorsThroughRationalEquivalence_of_isIso C
        (Scheme.Modules.vectorBundleToBase X E ≫ sX) sX
        (Scheme.Modules.vectorBundleToBase X E) rfl
        (relativeDimension_vectorBundleToBase E 0) k)) :=
  let _ := locallyOfFiniteType_vectorBundleToBase E 0
  let _ := flat_vectorBundleToBase E 0
  let _ := isIso_vectorBundleToBase_zero E
  flatPullbackChow_bijective_of_isAffineSpaceBundle_zero C
    (Scheme.Modules.vectorBundleToBase X E ≫ sX) sX (Scheme.Modules.vectorBundleToBase X E) rfl
    (relativeDimension_vectorBundleToBase E 0)
    (isAffineSpaceBundle_vectorBundleToBase E 0) k _

end Stacks.Chow

end
