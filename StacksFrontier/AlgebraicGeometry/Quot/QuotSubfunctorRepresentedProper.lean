/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotHilbertPolynomialAffineReduction
public import StacksFrontier.AlgebraicGeometry.Quot.QuotHilbertPolynomialClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowTwistWitness

/-!
# Subfunctors of the Quot presheaf represented by schemes proper over the base

For a Quot situation `F/X/B` (Stacks 09TR), a subfunctor `Q` of the Quot presheaf is
*represented by a scheme proper over `B`* when the universe lift of the functor of points of a
scheme `Z` of the site is isomorphic to `Q`, by an isomorphism under which the canonical morphism
`Q ⟶ B` becomes a proper morphism `h_Z ⟶ B`.  This is the form in which the affine case of
Stacks 0DPB is used in the proofs of Stacks 0DPB and 0DPC: over an affine base the Quot spaces
are schemes.

## Main definitions

* `QuotSituation.IsRepresentedProper`: `Q` is represented by a scheme proper over `B`.

## Main results

* `QuotSituation.IsRepresentedProper.exists_over_schemeSpace`: over the algebraic space of a
  scheme `W`, the representing morphism is `h_q` for a proper morphism `q : Z ⟶ W` of schemes.
* `QuotPushforwardSituation.isRepresentedProper_hilbertPolynomialQuot_of_directImage`: being
  represented by a proper scheme moves along the isomorphism of Stacks 0DP4 on `Quot^P`.
* `QuotSituation.isProperAlgebraicSpaceOver_hilbertPolynomialQuot_of_isRepresentedProper`:
  `Quot^{P, L}_{F/X/B}` is an algebraic space proper over `B` once all its base changes to affine
  schemes over `B` are represented by schemes proper over them.

## References

* [Stacks Project, Tag 0DP4](https://stacks.math.columbia.edu/tag/0DP4)
* [Stacks Project, Tag 0DPB](https://stacks.math.columbia.edu/tag/0DPB)
* [Stacks Project, Tag 0DPC](https://stacks.math.columbia.edu/tag/0DPC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotSituation

variable (D : QuotSituation B S hS)

/-- **A subfunctor of the Quot presheaf represented by a scheme proper over `B`**: there are a
scheme `Z` of the site, an isomorphism of the universe lift of `h_Z` with `Q`, and a proper
morphism `q : h_Z ⟶ B` which the canonical morphism `Q ⟶ B` becomes under it. -/
def IsRepresentedProper (Q : Subfunctor D.quotSitePresheaf) : Prop :=
  ∃ (Z : BigFppfOver B S hS) (e : yoneda.obj Z ⋙ uliftFunctor.{u + 1, u} ≅ Q.toFunctor)
    (q : yoneda.obj Z ⟶ D.Y.obj),
    e.hom ≫ Q.ι ≫ D.quotSitePresheafToBase = Functor.whiskerRight q uliftFunctor.{u + 1, u} ∧
      IsProper B S hS q

variable {D}

/-- Being represented by a scheme proper over `B` is preserved by equality of subfunctors. -/
theorem IsRepresentedProper.of_eq {Q Q' : Subfunctor D.quotSitePresheaf} (h : Q = Q')
    (hQ : D.IsRepresentedProper Q) : D.IsRepresentedProper Q' :=
  h ▸ hQ

/-- **Over the algebraic space of a scheme `W`, a representation by a proper scheme is a proper
morphism of schemes `Z ⟶ W`**, for the base change of a Quot situation to `W`. -/
theorem IsRepresentedProper.exists_over_schemeSpace {W : BigFppfOver B S hS}
    (p : schemeSpace W ⟶ D.Y) {Q : Subfunctor (D.canonicalBaseChanged p).quotSitePresheaf}
    (hQ : (D.canonicalBaseChanged p).IsRepresentedProper Q) :
    ∃ (Z : BigFppfOver B S hS) (q : Z ⟶ W)
      (e : yoneda.obj Z ⋙ uliftFunctor.{u + 1, u} ≅ Q.toFunctor),
      e.hom ≫ Q.ι ≫ (D.canonicalBaseChanged p).quotSitePresheafToBase =
          Functor.whiskerRight (yoneda.map q) uliftFunctor.{u + 1, u} ∧
        _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map q) := by
  obtain ⟨Z, e, q, he, hq⟩ := hQ
  have hq' := Yoneda.fullyFaithful.map_preimage q
  exact ⟨Z, Yoneda.fullyFaithful.preimage q, e, by rwa [hq'],
    isProper_toScheme_map_of_isProper_yoneda_map B S hS _ (by rwa [hq'])⟩

variable (D) in
/-- **The reduction of Stacks 0DPB and 0DPC to affine bases, in terms of representability by
proper schemes.**  `Quot^{P, L}_{F/X/B}` is an algebraic space proper over `B` as soon as, for
every scheme `W` of the site with affine underlying scheme and every `ξ : h_W ⟶ B`, the
subfunctor `Quot^{P, L_W}_{F_W/X_W/W}` of the base change of `F/X/B` to `W` is represented by a
scheme proper over `W`. -/
theorem isProperAlgebraicSpaceOver_hilbertPolynomialQuot_of_isRepresentedProper
    (L : Modules.{u, u} B S hS D.X.1 D.X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]
    (P : ℤ → ℤ)
    (h : ∀ (W : BigFppfOver B S hS) (ξ : yoneda.obj W ⟶ D.Y.obj),
      IsAffine ((BigFppfOver.toScheme B S hS).obj W) →
        (D.canonicalBaseChanged
          (ObjectProperty.homMk (Y := D.Y) (X := schemeSpace W) ξ)).IsRepresentedProper
          (@hilbertPolynomialQuot B S hS
            (D.canonicalBaseChanged (ObjectProperty.homMk (Y := D.Y) (X := schemeSpace W) ξ))
            ((modulePullback B S hS (D.baseChangedSourceProjection
              (ObjectProperty.homMk (Y := D.Y) (X := schemeSpace W) ξ))).obj L)
            (isInvertible_modulePullback B S hS (D.baseChangedSourceProjection
              (ObjectProperty.homMk (Y := D.Y) (X := schemeSpace W) ξ)) L) P)) :
    D.IsProperAlgebraicSpaceOver (D.hilbertPolynomialQuot L P) :=
  D.isProperAlgebraicSpaceOver_hilbertPolynomialQuot_of_represented L P fun W ξ hW =>
    (h W ξ hW).exists_over_schemeSpace _

end QuotSituation

namespace QuotPushforwardSituation

variable (D : QuotPushforwardSituation B S hS) (hπ : IsClosedImmersion B S hS D.π.hom)
  (M : Modules.{u, u} B S hS D.Y.1 D.Y.2)
  [hM : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.Y.1)
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS D.Y.1 D.Y.2).O)).property M]
  (P : ℤ → ℤ)

include hπ in
/-- **Representability by a proper scheme moves along Stacks 0DP4 on `Quot^P`**: if
`Quot^{P, M}_{π_*F/Y/B}` is represented by a scheme proper over `B`, so is
`Quot^{P, π^*M}_{F/X/B}`, through the isomorphism of the two over `B`
(`AlgebraicGeometry.Space.QuotPushforwardSituation.directImageHilbertPolynomialQuotIso`). -/
theorem isRepresentedProper_hilbertPolynomialQuot_of_directImage
    (h : D.directImageSituation.IsRepresentedProper
      (D.directImageSituation.hilbertPolynomialQuot M (hL := hM) P)) :
    D.sourceSituation.IsRepresentedProper
      (D.sourceSituation.hilbertPolynomialQuot ((modulePullback B S hS D.π).obj M)
        (hL := isInvertible_modulePullback B S hS D.π M) P) := by
  obtain ⟨Z, e, q, he, hq⟩ := h
  let i := D.directImageHilbertPolynomialQuotIso hπ M P
  refine ⟨Z, e ≪≫ i.symm, q, Eq.trans ?_ he, hq⟩
  ext T z
  show ULift.up (yonedaEquiv (i.hom.app T (i.inv.app T (e.hom.app T z))).1.toBase.hom) =
    ULift.up (yonedaEquiv (e.hom.app T z).1.toBase.hom)
  exact congrArg (fun y => ULift.up.{u + 1} (yonedaEquiv y.1.toBase.hom))
    (types_congr_hom (i.inv_hom_id_app T) (e.hom.app T z))

end QuotPushforwardSituation

end AlgebraicGeometry.Space

end
