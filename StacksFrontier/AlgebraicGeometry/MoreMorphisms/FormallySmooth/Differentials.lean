module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.Surjective
public import StacksFrontier.AlgebraicGeometry.Assembly.Basic
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.Sheaf
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FormallySmooth.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.AmpleAndExtension.LocallyProjectiveCover
public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothAffineLocal

/-!
# Differentials of a formally smooth morphism of schemes

The sheaf of relative differentials of a formally smooth morphism of schemes is locally
projective on its source.

## Main results

* `AlgebraicGeometry.Scheme.Hom.relativeDifferentials_isQuasicoherent`: the sheaf of relative
  differentials of a morphism of schemes is quasi-coherent.
* `AlgebraicGeometry.isLocallyProjective_relativeDifferentials`: **Stacks 06B5**, and
  **Stacks 061I** restricted to morphisms of schemes.

## Implementation notes

Local projectivity, `AlgebraicGeometry.Scheme.Modules.IsLocallyProjective` of Tag 05JP, asks
for projective sections on *every* affine open of the source, and an affine open of `X` need
not lie over an affine open of `S`. So the proof produces the affine opens that do — those
contained in the inverse image of an affine open of `S`, which cover `X` because the affine
opens of either scheme are a basis — and upgrades the conclusion to all affine opens with the
affine-open-cover criterion `AlgebraicGeometry.isLocallyProjective_iff_exists_affineOpen_cover`
of Tag 05JQ. That criterion consumes quasi-coherence, which is why it is established first.

On one such pair `U ≤ f ⁻¹ᵁ V` the chain is the one the source gives. Formal smoothness
restricts to `f.resLE V U` by Tag 02H3, becomes formal smoothness of `Γ(S, V) ⟶ Γ(X, U)` by the
affine criterion of Tag 02H4 together with `AlgebraicGeometry.arrowResLEAppIso`, and then
`Ω[Γ(X, U)⁄Γ(S, V)]` is a projective `Γ(X, U)`-module by
`Algebra.FormallySmooth.projective_kaehlerDifferential`. Tag 01UT,
`Stacks.AlgebraicGeometry.AffineDifferentialsIso.existsUnique_affineDifferentialsIso`,
identifies the sections of `Ω_{X/S}` on `U` with that module, and projectivity transports.

The comparison of Tag 01UT lands in `CommRingCat.KaehlerDifferential`, whose underlying module
instance search will not unfold; the linear equivalence is therefore retyped against the plain
`Ω[Γ(X, U)⁄Γ(S, V)]`, where the scalars are the ones the projectivity instance is stated for.

Quasi-coherence is not proved directly either: `Ω_{X/S}` is isomorphic to the conormal sheaf of
the diagonal of `f` by Tag 08S2, and the conormal sheaf of an immersion is quasi-coherent by
Tag 01R2.

## References

* [Stacks Project, Tag 06B5](https://stacks.math.columbia.edu/tag/06B5)
* [Stacks Project, Tag 061I](https://stacks.math.columbia.edu/tag/061I)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The sheaf of relative differentials of a morphism of schemes is quasi-coherent: it is
isomorphic to the conormal sheaf of the diagonal, which is the conormal sheaf of an
immersion. -/
instance Scheme.Hom.relativeDifferentials_isQuasicoherent {X S : Scheme.{u}} (f : X ⟶ S) :
    (Scheme.Hom.relativeDifferentials f).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Stacks.Tag08S2Assembly.relativeDifferentialsIsoDiagonalConormal f).symm
    (Stacks.Conormal.conormalSheaf_isQuasicoherent (pullback.diagonal f))

/-- **Stacks 06B5.** The sheaf of relative differentials of a formally smooth morphism of
schemes is locally projective on its source. This is **Stacks 061I** for a morphism of
algebraic spaces that is a morphism of schemes. -/
@[stacks 06B5, stacks 061I "for morphisms of schemes", ega "IV 17.2.3" "(i) locally projective"]
theorem isLocallyProjective_relativeDifferentials {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : FormallySmooth f) :
    Scheme.Modules.IsLocallyProjective (Scheme.Hom.relativeDifferentials f) := by
  rw [AlgebraicGeometry.isLocallyProjective_iff_exists_affineOpen_cover]
  refine ⟨Σ V : S.affineOpens, {U : X.affineOpens // (U : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens)},
    fun i => (i.2.1 : X.Opens), TopologicalSpace.IsOpenCover.mk ?_, fun i => i.2.1.2, ?_⟩
  · rw [iSup_sigma]
    exact (iSup_congr fun V : S.affineOpens =>
      Stacks.Smooth.iSup_affineOpens_le_eq X (f ⁻¹ᵁ (V : S.Opens))).trans
        (f.iSup_preimage_eq_top (iSup_affineOpens_eq_top S))
  · rintro ⟨V, U, hUV⟩
    show Module.Projective Γ(X, (U : X.Opens))
      Γ(Scheme.Hom.relativeDifferentials f, (U : X.Opens))
    let _ : IsAffine (U : X.Opens) := U.2
    let _ : IsAffine (V : S.Opens) := V.2
    let _ : Algebra Γ(S, (V : S.Opens)) Γ(X, (U : X.Opens)) :=
      (f.appLE (V : S.Opens) (U : X.Opens) hUV).hom.toAlgebra
    have : Algebra.FormallySmooth Γ(S, (V : S.Opens)) Γ(X, (U : X.Opens)) := by
      rw [← RingHom.formallySmooth_algebraMap]
      exact (RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff
          (arrowResLEAppIso f (V : S.Opens) (U : X.Opens) hUV)).mp
        ((formallySmooth_iff_appTop_formallySmooth _).mp
          (hf.resLE (U : X.Opens) (V : S.Opens) hUV))
    obtain ⟨e, -⟩ :=
      Stacks.AlgebraicGeometry.AffineDifferentialsIso.existsUnique_affineDifferentialsIso
        f U.2 hUV V.2
    have eL : Ω[Γ(X, (U : X.Opens))⁄Γ(S, (V : S.Opens))] ≃ₗ[Γ(X, (U : X.Opens))]
        Γ(Scheme.Hom.relativeDifferentials f, (U : X.Opens)) := e.symm.toLinearEquiv
    exact Module.Projective.of_equiv' eL

end AlgebraicGeometry

end
