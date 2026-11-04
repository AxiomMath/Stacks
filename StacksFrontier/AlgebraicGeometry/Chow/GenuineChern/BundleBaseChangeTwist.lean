module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BundleBaseChangeDegreeOne
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Bundle
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.TwistPullbackIso

/-!
# Base change of the projective bundle of a finite locally free module, with its twist

Let `g : X' ⟶ X` be a morphism of schemes, `ℰ` a finite locally free module on `X` and `ℰ'` a
finite locally free module on `X'` identified with `g^*ℰ`. Then `𝐏(ℰ') = X' ×_X 𝐏(ℰ)` and the
twist `𝒪_{𝐏(ℰ)}(1)` pulls back to `𝒪_{𝐏(ℰ')}(1)` ([Stacks, Tag 01O3] for the symmetric algebra,
with the twists of [Stacks, Tag 01NR]). This file states that for the objects
`Stacks.Chow.bundle`, `Stacks.Chow.bundleProj` and `Stacks.Chow.bundleTwist`.

## Main definitions

* `Stacks.Chow.bundleBaseChangeHom`: the base-change morphism `𝐏(ℰ') ⟶ 𝐏(ℰ)`.
* `Stacks.Chow.bundleBaseChangeIso`: `𝐏(ℰ') ≅ X' ×_X 𝐏(ℰ)`, over `X'`.
* `Stacks.Chow.BundleBaseChange` and `Stacks.Chow.bundleBaseChange`: the isomorphism over `X'`
  together with the identification of twists compatible with the tautological quotients.

## Main results

* `Stacks.Chow.isPullback_bundleBaseChangeHom`: the base-change square is cartesian.
* `Stacks.Chow.existsUnique_bundleBaseChangeTwistIso`: the twist pulls back to the twist, by a
  unique isomorphism compatible with the tautological quotients.
* `Stacks.Chow.exists_bundleBaseChange`: **`𝐏(g^*ℰ) = X' ×_X 𝐏(ℰ)` with `𝒪(1)` pulling back to
  `𝒪(1)`**, as an existence statement.
* `Stacks.ProjectiveBundle.exists_chart_baseChangeHom`: the chart formula of the base-change
  morphism.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.ProjectiveBundle

open Stacks.SymGraded Stacks.AlgebraicGeometry.RelativeProj Opposite

variable {X X' : Scheme.{u}} (g : X' ⟶ X) (E : X.Modules) [E.IsQuasicoherent]
  (hqc : IsQuasicoherentPieces E) (E' : X'.Modules) [E'.IsQuasicoherent]
  (hqc' : IsQuasicoherentPieces E') (hE : E' ≅ (Scheme.Modules.pullback g).obj E)

/-- **The base-change morphism is chart-wise `Proj` of a graded ring map that is the pullback in
degree one.** Every point of `X'` has an affine neighbourhood `U'` mapping into an affine open `U`
of `X`, over which the base-change morphism is `Proj φ` on charts, for a graded ring map
`φ : Γ(U, Sym E) ⟶ Γ(U', Sym E')` that carries a degree-one section `x` of `E` to the restriction
of its pullback, read in `E'` through `hE`. -/
theorem exists_chart_baseChangeHom (x' : X') :
    ∃ (U' : X'.Opens) (hU' : IsAffineOpen U') (_ : x' ∈ U') (U : X.Opens)
      (hU : IsAffineOpen U) (hUU' : U' ≤ g ⁻¹ᵁ U)
      (φ : (schemeSheafGradedAlgebra E hqc).grading U →+*ᵍ
        (schemeSheafGradedAlgebra E' hqc').grading U')
      (hφ : HomogeneousIdeal.irrelevant ((schemeSheafGradedAlgebra E' hqc').grading U') ≤
        (HomogeneousIdeal.irrelevant ((schemeSheafGradedAlgebra E hqc).grading U)).map φ),
      (relativeProj (schemeSheafGradedAlgebra E' hqc')).chart U' hU' ≫
          baseChangeHom g E hqc E' hqc' hE =
        AlgebraicGeometry.Proj.map φ hφ ≫
          (relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU ∧
      ∀ x : Γ(E, U), φ (DirectSum.of ((schemeSheafGradedAlgebra E hqc).sectionPieces U) 1
          ((Scheme.Modules.symmetricAlgebraGen X E).val.app (op U) x)) =
        DirectSum.of ((schemeSheafGradedAlgebra E' hqc').sectionPieces U') 1
          ((Scheme.Modules.symmetricAlgebraGen X' E').val.app (op U')
            (E'.val.map (homOfLE hUU').op
              (((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _ hE.inv).val.app
                (op U) x))) := by
  obtain ⟨W, W', h, hx⟩ := exists_affineZariskiSite_le_preimage g x'
  exact ⟨W'.toOpens, W'.2, hx, W.toOpens, W.2, h, baseChangeGradedHom g E hqc E' hqc' hE W W' h,
    irrelevant_le_baseChangeGradedHom g E hqc E' hqc' hE W W' h,
    chart_baseChangeHom g E hqc E' hqc' hE W W' h,
    baseChangeGradedHom_of_one g E E' hE hqc hqc' W W' h⟩

end Stacks.ProjectiveBundle

namespace Stacks.Chow

variable {X X' : Scheme.{u}} (g : X' ⟶ X) (E : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (E' : X'.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E']
  (hE : E' ≅ (Scheme.Modules.pullback g).obj E)

/-- A finite locally free module is quasi-coherent. -/
theorem isQuasicoherent_of_isFiniteLocallyFree (F : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F] : F.IsQuasicoherent :=
  Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree F

/-- **The base-change morphism of projective bundles** `𝐏(ℰ') ⟶ 𝐏(ℰ)` for `ℰ' ≅ g^*ℰ`. -/
def bundleBaseChangeHom : bundle E' ⟶ bundle E :=
  haveI := isQuasicoherent_of_isFiniteLocallyFree E
  haveI := isQuasicoherent_of_isFiniteLocallyFree E'
  Stacks.ProjectiveBundle.baseChangeHom g E (bundlePieces E) E' (bundlePieces E') hE

/-- **The base-change square of projective bundles is cartesian**: `𝐏(ℰ') = X' ×_X 𝐏(ℰ)`. -/
theorem isPullback_bundleBaseChangeHom :
    IsPullback (bundleProj E') (bundleBaseChangeHom g E E' hE) g (bundleProj E) :=
  have := isQuasicoherent_of_isFiniteLocallyFree E
  have := isQuasicoherent_of_isFiniteLocallyFree E'
  Stacks.ProjectiveBundle.isPullback_baseChangeHom g E (bundlePieces E) E' (bundlePieces E') hE

/-- The base-change morphism lies over `g`. -/
@[reassoc]
theorem bundleBaseChangeHom_bundleProj :
    bundleBaseChangeHom g E E' hE ≫ bundleProj E = bundleProj E' ≫ g :=
  (isPullback_bundleBaseChangeHom g E E' hE).w.symm

/-- **The base-change isomorphism** `𝐏(ℰ') ≅ X' ×_X 𝐏(ℰ)`. -/
def bundleBaseChangeIso : bundle E' ≅ pullback g (bundleProj E) :=
  (isPullback_bundleBaseChangeHom g E E' hE).isoPullback

/-- The base-change isomorphism lies over `X'`. -/
@[reassoc (attr := simp)]
theorem bundleBaseChangeIso_hom_fst :
    (bundleBaseChangeIso g E E' hE).hom ≫ pullback.fst g (bundleProj E) = bundleProj E' :=
  (isPullback_bundleBaseChangeHom g E E' hE).isoPullback_hom_fst

/-- The base-change isomorphism followed by the second projection is the base-change morphism. -/
@[reassoc (attr := simp)]
theorem bundleBaseChangeIso_hom_snd :
    (bundleBaseChangeIso g E E' hE).hom ≫ pullback.snd g (bundleProj E) =
      bundleBaseChangeHom g E E' hE :=
  (isPullback_bundleBaseChangeHom g E E' hE).isoPullback_hom_snd

/-- The second projection of an isomorphism `𝐏(ℰ') ≅ X' ×_X 𝐏(ℰ)` over `X'` lies over `g`. -/
@[reassoc]
theorem snd_bundleProj_of_hom_fst (e : bundle E' ≅ pullback g (bundleProj E))
    (he : e.hom ≫ pullback.fst g (bundleProj E) = bundleProj E') :
    (e.hom ≫ pullback.snd g (bundleProj E)) ≫ bundleProj E = bundleProj E' ≫ g := by
  rw [Category.assoc, ← pullback.condition, ← Category.assoc, he]

/-- **The twist of `𝐏(ℰ)` pulls back to the twist of `𝐏(ℰ')`**, along the second projection of the
base-change isomorphism, by a unique isomorphism carrying the pulled-back tautological quotient
`π'^*g^*ℰ ≅ h^*π^*ℰ ⟶ h^*𝒪_{𝐏(ℰ)}(1)` to the tautological quotient
`π'^*g^*ℰ ≅ π'^*ℰ' ⟶ 𝒪_{𝐏(ℰ')}(1)`. -/
theorem existsUnique_bundleBaseChangeTwistIso :
    ∃! φ : (Scheme.Modules.pullback
        ((bundleBaseChangeIso g E E' hE).hom ≫ pullback.snd g (bundleProj E))).obj
          (bundleTwist E) ≅ bundleTwist E',
      Stacks.Chow.GenuineChern.twistQuotientPullback g (bundlePieces E) (bundlePieces E')
          ((bundleBaseChangeIso g E E' hE).hom ≫ pullback.snd g (bundleProj E))
          (snd_bundleProj_of_hom_fst g E E' _ (bundleBaseChangeIso_hom_fst g E E' hE)) ≫
          φ.hom =
        Stacks.Chow.GenuineChern.twistQuotientTarget g (bundlePieces E') hE.inv := by
  have := isQuasicoherent_of_isFiniteLocallyFree E
  have := isQuasicoherent_of_isFiniteLocallyFree E'
  refine Stacks.Chow.GenuineChern.existsUnique_twistIso g (bundlePieces E) (bundlePieces E')
    hE.inv _ _ fun x' => ?_
  rw [bundleBaseChangeIso_hom_snd]
  exact Stacks.ProjectiveBundle.exists_chart_baseChangeHom g E (bundlePieces E) E'
    (bundlePieces E') hE x'

/-- **The base change of the projective bundle of a finite locally free module, with its twist**:
an isomorphism `𝐏(ℰ') ≅ X' ×_X 𝐏(ℰ)` over `X'`, and an isomorphism of the pullback of
`𝒪_{𝐏(ℰ)}(1)` along the second projection with `𝒪_{𝐏(ℰ')}(1)` that carries the pulled-back
tautological quotient to the tautological quotient of `ℰ'` (both read on `π'^*g^*ℰ`). -/
structure BundleBaseChange (hE : E' ≅ (Scheme.Modules.pullback g).obj E) where
  /-- `𝐏(ℰ') ≅ X' ×_X 𝐏(ℰ)`. -/
  iso : bundle E' ≅ pullback g (bundleProj E)
  /-- The isomorphism lies over `X'`. -/
  iso_hom_fst : iso.hom ≫ pullback.fst g (bundleProj E) = bundleProj E'
  /-- The twist pulls back to the twist. -/
  twistIso : (Scheme.Modules.pullback (iso.hom ≫ pullback.snd g (bundleProj E))).obj
      (bundleTwist E) ≅ bundleTwist E'
  /-- The identification of twists carries the pulled-back tautological quotient to the
  tautological quotient. -/
  twistIso_spec :
    Stacks.Chow.GenuineChern.twistQuotientPullback g (bundlePieces E) (bundlePieces E')
        (iso.hom ≫ pullback.snd g (bundleProj E))
        (snd_bundleProj_of_hom_fst g E E' iso iso_hom_fst) ≫ twistIso.hom =
      Stacks.Chow.GenuineChern.twistQuotientTarget g (bundlePieces E') hE.inv

/-- **The base change of the projective bundle and its twist**, along an arbitrary morphism of
schemes ([Stacks, Tag 01O3] for `Sym ℰ`, with the twists of [Stacks, Tag 01NR]). The twist
isomorphism is the unique one compatible with the tautological quotients
(`Stacks.Chow.existsUnique_bundleBaseChangeTwistIso`). -/
def bundleBaseChange : BundleBaseChange g E E' hE where
  iso := bundleBaseChangeIso g E E' hE
  iso_hom_fst := bundleBaseChangeIso_hom_fst g E E' hE
  twistIso := (existsUnique_bundleBaseChangeTwistIso g E E' hE).exists.choose
  twistIso_spec := (existsUnique_bundleBaseChangeTwistIso g E E' hE).exists.choose_spec

/-- **`𝐏(g^*ℰ) = X' ×_X 𝐏(ℰ)`, and `𝒪(1)` pulls back to `𝒪(1)`.** For a morphism of schemes
`g : X' ⟶ X`, a finite locally free `ℰ` on `X` and a finite locally free `ℰ'` on `X'` identified
with `g^*ℰ`, the projective bundle of `ℰ'` is the base change of that of `ℰ` over `X'`, and the
pullback of the twist of `𝐏(ℰ)` along the second projection is the twist of `𝐏(ℰ')`. -/
theorem exists_bundleBaseChange (hE : E' ≅ (Scheme.Modules.pullback g).obj E) :
    ∃ e : bundle E' ≅ pullback g (bundleProj E),
      e.hom ≫ pullback.fst g (bundleProj E) = bundleProj E' ∧
        Nonempty ((Scheme.Modules.pullback (e.hom ≫ pullback.snd g (bundleProj E))).obj
          (bundleTwist E) ≅ bundleTwist E') :=
  ⟨(bundleBaseChange g E E' hE).iso, (bundleBaseChange g E E' hE).iso_hom_fst,
    ⟨(bundleBaseChange g E E' hE).twistIso⟩⟩

end Stacks.Chow

end
