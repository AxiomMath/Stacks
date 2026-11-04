module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionEquivalence
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineEtaleChartTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineFibreProduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleLocalCharacterization

/-!
# Essential surjectivity of the completion functor: the pieces of the gluing

Let `X = Spec R` be a Noetherian affine scheme of the big fppf site of `S`, let `T ⊆ |X|` be
closed, and let `g : W ⟶ X_{/T}` be a rig-étale morphism from a locally Noetherian formal
algebraic space. Steps 2 and 3 of the proof of **Stacks 0ARA** choose an affine étale covering
`{Wᵢ ⟶ W}` as in Definition 0AIM, algebraize the `Wᵢ` and the `Wᵢ ×_W Wⱼ` by Step 1 and glue
the algebraizations.

This file proves the inputs of that gluing which concern `W` alone.

* A representable étale morphism `c : W' ⟶ W` followed by a rig-étale `g : W ⟶ Y` is
  rig-étale. Every affine étale chart of `W'` composed with `c` is an affine étale chart of `W`,
  so this is immediate from the definition of rig-étaleness (Definition 0AQM); no Noetherian
  hypothesis enters.
* For `W` separated (in the sense of clause (2) of Stacks 0AJ7) and locally Noetherian, and
  `Wᵢ ⟶ W`, `Wⱼ ⟶ W` affine étale charts, the fibre product `Wᵢ ×_W Wⱼ` is a Noetherian affine
  formal algebraic space (Stacks 0AN3 and Stacks 0AKX) whose map to `W` is representable
  étale. So Step 1 applies to it: with `g` rig-étale, `Wᵢ ×_W Wⱼ ⟶ X_{/T}` is the completion
  of a finite-type modification of `X`, which is the first sentence of Step 2.

## Main results

* `AlgebraicGeometry.FormalSpace.isRigEtale_comp_of_isRepresentableEtale`.
* `AlgebraicGeometry.FormalSpace.isNoetherian_pullback_of_isSeparated`.
* `AlgebraicGeometry.FormalSpace.exists_finiteTypeModification_completion_iso_pullback`: the
  algebraization of `Wᵢ ×_W Wⱼ` in Step 2.

## References

* [Stacks Project, Tag 0ARA](https://stacks.math.columbia.edu/tag/0ARA)
* [Stacks Project, Tag 0AQM](https://stacks.math.columbia.edu/tag/0AQM)
* [Stacks Project, Tag 0AN3](https://stacks.math.columbia.edu/tag/0AN3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] Space.pointTopology

/-- A representable étale morphism `c : W' ⟶ W` followed by a rig-étale morphism `g : W ⟶ Y`
is rig-étale. An affine étale chart `U ⟶ W'` composed with `c` is an affine étale chart of `W`,
so every chart square of `c ≫ g` is a chart square of `g`. -/
theorem isRigEtale_comp_of_isRepresentableEtale {W' W Y : FppfSheaf B S hS} (c : W' ⟶ W)
    (hc : IsRepresentableEtale B S hS c) (g : W ⟶ Y) (hg : IsRigEtale B S hS g) :
    IsRigEtale B S hS (c ≫ g) := by
  intro U V hU hV a b t ha hb hae hbe hsq
  have hac : IsRepresentableEtale B S hS (a ≫ c) :=
    IsRepresentableEtale.comp B S hS (a := a) (b := c) ⟨ha, hae⟩ hc
  exact hg U V hU hV (a ≫ c) b t hac.1 hb hac.2 hbe (by rw [Category.assoc]; exact hsq)

/-- The fibre product of two affine étale charts of a separated locally Noetherian formal
algebraic space is a Noetherian affine formal algebraic space, and its map to the space is
representable étale. Affineness is Stacks 0AN3 clause (1); Noetherianity is the implication
(2) ⟹ (1) of Stacks 0AKX for the composite chart `Wᵢ ×_W Wⱼ ⟶ Wᵢ ⟶ W`. -/
theorem isNoetherian_pullback_of_isSeparated {W Wi Wj : FppfSheaf B S hS}
    (hW : IsLocallyNoetherian B S hS W) (hWsep : IsSeparated B S hS W) (wi : Wi ⟶ W)
    (wj : Wj ⟶ W) (hi : IsAffineFormalAlgebraicSpace B S hS Wi)
    (hj : IsAffineFormalAlgebraicSpace B S hS Wj) (hwi : IsRepresentableEtale B S hS wi)
    (hwj : IsRepresentableEtale B S hS wj) :
    IsAffineFormalAlgebraicSpace B S hS (pullback wi wj) ∧
      IsNoetherian B S hS (pullback wi wj) ∧
      IsRepresentableEtale B S hS (pullback.fst wi wj ≫ wi) := by
  have haff : IsAffineFormalAlgebraicSpace B S hS (pullback wi wj) :=
    isAffineFormalAlgebraicSpace_pullback B S hS wi wj
      (hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace B S hS hW.1) hWsep hi hj
  have hrep : IsRepresentableEtale B S hS (pullback.fst wi wj ≫ wi) :=
    (isRepresentableEtale_pullback_fst B S hS wi wj hwj).comp B S hS hwi
  exact ⟨haff, isNoetherian_of_isLocallyNoetherian_of_isRepresentableEtale B S hS hW _ haff hrep,
    hrep⟩

/-- **The algebraization of `Wᵢ ×_W Wⱼ` in Step 2 of the proof of Stacks 0ARA.** Let
`X = Spec R` be a Noetherian affine scheme of the site, `T ⊆ |X|` closed, `W` a separated
locally Noetherian formal algebraic space with a rig-étale `g : W ⟶ X_{/T}`, and `Wᵢ ⟶ W`,
`Wⱼ ⟶ W` affine étale charts. Then `Wᵢ ×_W Wⱼ ⟶ X_{/T}` is, up to isomorphism over `X_{/T}`, the
completion of a finite-type modification of `X` away from `T`: Step 1
(`exists_finiteTypeModification_completion_iso_of_isNoetherian`) applies to it by
`isNoetherian_pullback_of_isSeparated` and `isRigEtale_comp_of_isRepresentableEtale`. -/
theorem exists_finiteTypeModification_completion_iso_pullback
    {R : Type u} [CommRing R] [IsNoetherianRing R] (hR : B.Contains (Spec (.of R)))
    (s : Spec (.of R) ⟶ S)
    (T : Set (Space.points B S hS (yoneda.obj (affineOver B S hS hR s)))) (hT : IsClosed T)
    {W Wi Wj : FppfSheaf B S hS} (hW : IsLocallyNoetherian B S hS W)
    (hWsep : IsSeparated B S hS W)
    (g : W ⟶ Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS hR s)) T)
    (hg : IsRigEtale B S hS g) (wi : Wi ⟶ W) (wj : Wj ⟶ W)
    (hi : IsAffineFormalAlgebraicSpace B S hS Wi) (hj : IsAffineFormalAlgebraicSpace B S hS Wj)
    (hwi : IsRepresentableEtale B S hS wi) (hwj : IsRepresentableEtale B S hS wj) :
    ∃ M : Space.FiniteTypeModification B S hS
        (Space.openSubspaceOfPoints B S hS (yoneda.obj (affineOver B S hS hR s)) Tᶜ),
      Nonempty ((Space.completionOverFunctor B S hS T).obj M.obj ≅
        Over.mk (pullback.fst wi wj ≫ wi ≫ g)) := by
  obtain ⟨haff, hnoeth, hrep⟩ := isNoetherian_pullback_of_isSeparated hW hWsep wi wj hi hj hwi hwj
  have hrig := isRigEtale_comp_of_isRepresentableEtale _ hrep g hg
  rw [Category.assoc] at hrig
  exact exists_finiteTypeModification_completion_iso_of_isNoetherian hR s T hT haff hnoeth _ hrig

end AlgebraicGeometry.FormalSpace

end
