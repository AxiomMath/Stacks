module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.HyperplaneChain
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.FreeTower.Bundle
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.LocalTower
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumExists

/-!
# Projective bundles are hyperplane chains locally on the base

Let `ℰ` be a module on a scheme `X`, finite locally free of rank `n + 1`, and `π : 𝐏(ℰ) ⟶ X` its
projective bundle with the twist `𝒪(1)`. Over an affine open `V` on which `ℰ` is free the bundle
is `ℙⁿ_V = V ×_ℤ ℙⁿ_ℤ` with the pullback of `𝒪(1)` (Stacks 01OE), so the zero schemes of the
pulled-back coordinates `T_{n-1}, …, T₀` form a hyperplane chain
(`Stacks.Chow.IsHyperplaneChain`), and so does every base change of the part of the bundle over
`V`.

## Main definitions

* `Stacks.Chow.HasHyperplaneChain`: the module is invertible and some global sections of it have
  zero schemes forming a hyperplane chain.

## Main results

* `Stacks.Chow.HasHyperplaneChain.of_isPullback`: stability under base change, with any module
  isomorphic to the pullback.
* `Stacks.Chow.hasHyperplaneChain_freeModule`: the projective bundle of a free module.
* `Stacks.Chow.exists_isAffineOpen_hasHyperplaneChain_projectiveBundle`: **every point of the
  base of a projective bundle has an affine open neighbourhood over which every base change of the
  bundle, with its twist, has a hyperplane chain.**

## References

* [Stacks Project, Tag 01OE](https://stacks.math.columbia.edu/tag/01OE)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- **A hyperplane chain of sections.** The module `L` on `P` is invertible and has global
sections `σ_j` whose zero schemes form a hyperplane chain of length `n` over the base. -/
def HasHyperplaneChain (n : ℕ) {P U : Scheme.{u}} (π : P ⟶ U) (L : P.Modules) : Prop :=
  ∃ (_ : AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L)
    (σ : ℕ → Γ(L, ⊤)), IsHyperplaneChain n π (fun j => Stacks.Divisors.zeroScheme P L (σ j))

/-- **Hyperplane chains of sections are stable under base change.** In a cartesian square
`P' = U' ×_U P`, a hyperplane chain of sections of `L` gives one of every module isomorphic to the
pullback of `L`: the pulled-back sections, whose zero schemes are the inverse images. -/
theorem HasHyperplaneChain.of_isPullback {n : ℕ} {P U : Scheme.{u}} {π : P ⟶ U}
    {L : P.Modules} (h : HasHyperplaneChain n π L) {P' U' : Scheme.{u}} {π' : P' ⟶ U'}
    {g' : P' ⟶ P} {g : U' ⟶ U} (hsq : IsPullback g' π' π g) {L' : P'.Modules}
    (e : L' ≅ (Scheme.Modules.pullback g').obj L) : HasHyperplaneChain n π' L' := by
  obtain ⟨hL, σ, hc⟩ := h
  have hLp : AlgebraicGeometry.SheafOfModules.IsInvertible P'.sheaf.obj
      P'.ringCatSheaf.property ((Scheme.Modules.pullback g').obj L) :=
    Stacks.RelativeProj.isInvertible_pullback_obj g' L hL
  have hL' : AlgebraicGeometry.SheafOfModules.IsInvertible P'.sheaf.obj
      P'.ringCatSheaf.property L' :=
    Stacks.UFDExtensionGlobal.isInvertible_of_iso e.symm hLp
  refine ⟨hL', fun j => Scheme.Modules.Hom.app e.inv ⊤ (pullbackGlobalSections g' L (σ j)), ?_⟩
  convert hc.of_isPullback hsq using 2 with j
  rw [← Stacks.Divisors.zeroScheme_pullback]
  exact AlgebraicGeometry.zeroScheme_eq_of_iso e (Scheme.Modules.app_inv_app e.symm ⊤ _)

/-- A hyperplane chain of sections transported along an isomorphism of total spaces over the
base. -/
theorem HasHyperplaneChain.of_iso_left {n : ℕ} {P P' U : Scheme.{u}} {π : P ⟶ U}
    {π' : P' ⟶ U} {L : P.Modules} {L' : P'.Modules} (e : P ≅ P') (he : e.hom ≫ π' = π)
    (eL : L ≅ (Scheme.Modules.pullback e.hom).obj L') (h : HasHyperplaneChain n π' L') :
    HasHyperplaneChain n π L :=
  h.of_isPullback (IsPullback.of_horiz_isIso (g := 𝟙 U) ⟨by simp [he]⟩) eL

open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.RelativeProj
open Stacks.SymGraded Stacks.AmpleProjectiveImmersion Stacks.TwistPullbackPinned
open Stacks.AlgebraicGeometry.RelativeProjTwists Stacks.AlgebraicGeometry.ProjTwistSections

/-- **The projective bundle of a free module of rank `n + 1`, with its twist, has a hyperplane
chain of sections**: it is the base change of `ℙⁿ_ℤ` with `𝒪(1)` (Stacks 01OE), whose coordinate
hyperplanes form one. -/
theorem hasHyperplaneChain_freeModule (U : Scheme.{u}) (n : ℕ) :
    HasHyperplaneChain n
      (relativeProj (schemeSheafGradedAlgebra (freeModule (X := U) (coordIndex.{u} n))
        (isQuasicoherentPieces_free (X := U) (coordIndex.{u} n)))).toBase
      (Stacks.ProjectiveBundleSplitting.tautologicalTwist
        (freeModule (X := U) (coordIndex.{u} n))
        (isQuasicoherentPieces_free (X := U) (coordIndex.{u} n))) :=
  HasHyperplaneChain.of_isPullback
    ⟨inferInstance, fun j => coordGlobalSection.{u} n ⟨n - j, by omega⟩,
      FreeTower.isHyperplaneChain_projectiveSpaceAtUniverse n⟩
    (FreeTower.isPullback_projectiveBundleToIntegralModel U n)
    (FreeTower.exists_tautologicalTwist_iso_pullback U n).choose

/-- **Over an affine open on which the module is free, the projective bundle has a hyperplane
chain of sections.** Every point of `X` has an affine open neighbourhood `V` on which `ℰ` is free
of rank `n + 1`, and over `V` the bundle, with its twist, is the bundle of the free module
(`Stacks.ProjectiveBundle.restrictBundleIso`). -/
theorem exists_isAffineOpen_hasHyperplaneChain_relativeProj (n : ℕ) {X : Scheme.{u}}
    (E : X.Modules) (hqc : IsQuasicoherentPieces E)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)] (x : X) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧
      HasHyperplaneChain n ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ∣_ V)
        ((Scheme.Modules.pullback
          ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ V).ι).obj
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E hqc)) := by
  have := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (n + 1)
  have : E.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
  obtain ⟨V, hV, hxV, ⟨e⟩⟩ := Stacks.ProjectiveBundle.exists_affine_restrict_free E (n + 1) x
  refine ⟨V, hV, hxV, ?_⟩
  let i := Stacks.ProjectiveBundle.restrictBundleIso E hqc hV
    (freeModule (X := V.toScheme) (coordIndex.{u} n))
    (isQuasicoherentPieces_free (X := V.toScheme) (coordIndex.{u} n)) e
  refine (hasHyperplaneChain_freeModule V.toScheme n).of_iso_left i.symm ?_ ?_
  · rw [Iso.symm_hom, Iso.inv_comp_eq,
      Stacks.ProjectiveBundle.restrictBundleIso_hom_morphismRestrict]
  · exact (Stacks.ProjectiveBundle.pullbackInvHomIso i _).symm ≪≫
      (Scheme.Modules.pullback i.inv).mapIso
        (Stacks.ProjectiveBundle.restrictBundleIsoTwistIso E hqc hV _ _ e)

/-- **Every point of the base of the projective bundle `𝐏(ℰ) = Proj(Sym ℰ)` of a module of rank
`n + 1` has an affine open neighbourhood `V` over which every base change of the bundle, with the
pullback of `𝒪(1)`, has a hyperplane chain of sections**: for every cartesian square
`Q = V ×_X 𝐏(ℰ)`. -/
theorem exists_isAffineOpen_hasHyperplaneChain_projectiveBundle (n : ℕ) {X : Scheme.{u}}
    (F : X.Modules) [F.IsQuasicoherent]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F (n + 1)] (x : X) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧
      ∀ (Q : Scheme.{u}) (c : Q ⟶ Stacks.RelativeProj.projectiveBundle X F) (q : Q ⟶ V)
        (_ : IsPullback c q (Stacks.RelativeProj.projectiveBundleToBase X F) V.ι),
        HasHyperplaneChain n q
          ((Scheme.Modules.pullback c).obj (Stacks.RelativeProj.tautologicalDatumTwist F)) := by
  set hqc := isQuasicoherentPieces_of_isQuasicoherent F
  set πs := (relativeProj (schemeSheafGradedAlgebra F hqc)).toBase
  obtain ⟨V, hV, hxV, H⟩ := exists_isAffineOpen_hasHyperplaneChain_relativeProj n F hqc x
  refine ⟨V, hV, hxV, fun Q c q hsq => ?_⟩
  have hb : IsPullback (Stacks.RelativeProj.bundlePresentationIso F).inv
      (Stacks.RelativeProj.projectiveBundleToBase X F) πs (𝟙 X) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [Category.comp_id]
      exact Stacks.RelativeProj.bundlePresentationIso_inv_comp_toBase F⟩
  have sq1 : IsPullback (c ≫ (Stacks.RelativeProj.bundlePresentationIso F).inv) q πs V.ι := by
    simpa using hsq.paste_horiz hb
  have sq2 : IsPullback (πs ⁻¹ᵁ V).ι (πs ∣_ V) πs V.ι := (isPullback_morphismRestrict πs V).flip
  let φ := sq2.lift (c ≫ (Stacks.RelativeProj.bundlePresentationIso F).inv) q sq1.w
  have hφ₁ : φ ≫ (πs ⁻¹ᵁ V).ι = c ≫ (Stacks.RelativeProj.bundlePresentationIso F).inv :=
    sq2.lift_fst _ _ _
  have hφ₂ : φ ≫ (πs ∣_ V) = q := sq2.lift_snd _ _ _
  have hleft : IsPullback φ q (πs ∣_ V) (𝟙 _) := by
    refine IsPullback.of_right ?_ hφ₂ sq2
    rw [hφ₁, Category.id_comp]
    exact sq1
  exact H.of_isPullback hleft (pullbackObjIsoOfComm hφ₁.symm _)

end Stacks.Chow

end
