module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactInclusionDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.CoheratorFlatPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentSeparator

/-!
# The hypothesis of Stacks 09TG: the commutative square of derived direct images

Let `j : V ⟶ W` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf site
`B`, whose direct image preserves quasi-coherence, so that it restricts to
`j_* : QCoh(𝒪_V) ⥤ QCoh(𝒪_W)`.  [Stacks, Tag 09TG] asks that the right derived functor `Φ` of this
restriction *fit into a commutative diagram*

```
D(QCoh(𝒪_V)) --i_V--> D_QCoh(𝒪_V)
     | Φ                  | Rj_*
     v                     v
D(QCoh(𝒪_W)) --i_W--> D_QCoh(𝒪_W)
```

The diagram commutes when the **canonical** comparison `i_W ∘ Φ ⟶ Rj_* ∘ i_V` is invertible, not
merely when the two composites are abstractly isomorphic.  That comparison is
`Stacks.DerivedCoherator.pushforwardSquareComparison`: the unique transformation out of the right
derived functor `Φ ⋙ D(ι_W)` of `j_* ⋙ ι_W` which, on a complex `K` of quasi-coherent
`𝒪_V`-modules, is the comparison `j_* K ⟶ Rj_* K` of `Rj_*`.  It is stated after composing with the
inclusions `D_QCoh ⥤ D`, where `i ⋙ J` is the functor `D(ι)` induced by the inclusion of the
quasi-coherent modules (`quasicoherentDerivedComparisonCompιIso`).

All names are in the namespace `AlgebraicGeometry.Space`.

## Main definitions

* `DerivedPushforwardSquareCommutes`: the square of 09TG commutes for one morphism `j`: the
  canonical comparison is invertible.
* `DerivedPushforwardComputedOnKInjectives`: the equivalent condition that `Rj_*` is computed by
  `j_*` on K-injective complexes of quasi-coherent `𝒪_V`-modules.
* `ExistsAffineEtaleDerivedPushforwardSquare`: **the hypothesis of [Stacks, Tag 09TG]**: the square
  commutes for every étale `j : V ⟶ W` with `W ⊆ X` a quasi-compact open subspace and `V` affine.

## Main results

* `derivedPushforwardSquareCommutes_iff`: the two conditions agree.
* `affineEtaleDerivedPushforwardSquareCommutes_of_kInjectives`: the hypothesis of 09TG from the
  K-injective condition for one model of each `Rj_*`.

## References

* [Stacks Project, Tag 09TG](https://stacks.math.columbia.edu/tag/09TG)
* [Stacks Project, Tag 08F1](https://stacks.math.columbia.edu/tag/08F1)
* [Stacks Project, Tag 08GY](https://stacks.math.columbia.edu/tag/08GY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The square for one morphism -/

section Square

variable {V W : AlgebraicSpaces B S hS} (j : V ⟶ W)

/-- `QCoh(𝒪_V)` is Grothendieck abelian at the universe of the schemes (Stacks 077V (1)). -/
lemma isGrothendieckAbelian_quasicoherentSheaves_algebraicSpace (Z : AlgebraicSpaces B S hS) :
    IsGrothendieckAbelian.{u} (QuasicoherentSheaves.{u, u} B S hS Z.1 Z.2) :=
  quasicoherentSheaves_isGrothendieckAbelian B S hS Z.1 Z.2

/-- **The square of [Stacks, Tag 09TG] commutes** for `j : V ⟶ W`, a right derived functor
`(Φ, βΦ)` of `j_* : QCoh(𝒪_V) ⥤ QCoh(𝒪_W)` and a right derived functor `(Rj, βj)` of the direct
image of all modules: the canonical comparison `Φ ⋙ D(ι_W) ⟶ D(ι_V) ⋙ Rj` is invertible. -/
def DerivedPushforwardSquareCommutes (hpush : PushforwardPreservesQuasicoherence B S hS j)
    (Φ : DerivedCategory (QuasicoherentSheaves.{u, u} B S hS V.1 V.2) ⥤
      DerivedCategory (QuasicoherentSheaves.{u, u} B S hS W.1 W.2))
    (βΦ : (quasicoherentPushforward B S hS j hpush).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Φ)
    (hΦ : Φ.IsRightDerivedFunctor βΦ
      (HomotopyCategory.quasiIso (QuasicoherentSheaves.{u, u} B S hS V.1 V.2) (ComplexShape.up ℤ)))
    (Rj : DerivedCategory (Modules.{u, u} B S hS V.1 V.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (βj : (modulePushforward B S hS j).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj) : Prop :=
  letI := isGrothendieckAbelian_quasicoherentSheaves_algebraicSpace B S hS V
  IsIso (Stacks.DerivedCoherator.pushforwardSquareComparison.{u}
    (quasicoherentSheavesι B S hS V) (quasicoherentSheavesι B S hS W)
    (quasicoherentPushforward B S hS j hpush) (modulePushforward B S hS j)
    (quasicoherentPushforwardCompιIso B S hS j hpush) Φ βΦ Rj βj)

/-- **`Rj_*` is computed by `j_*` on K-injective complexes of quasi-coherent modules**: the
comparison `βj` of a right derived functor of the direct image is invertible at every K-injective
complex of quasi-coherent `𝒪_V`-modules.  This is equivalent to
`AlgebraicGeometry.Space.DerivedPushforwardSquareCommutes`, by
`AlgebraicGeometry.Space.derivedPushforwardSquareCommutes_iff`. -/
def DerivedPushforwardComputedOnKInjectives
    (Rj : DerivedCategory (Modules.{u, u} B S hS V.1 V.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (βj : (modulePushforward B S hS j).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj) : Prop :=
  ∀ I : CochainComplex (QuasicoherentSheaves.{u, u} B S hS V.1 V.2) ℤ, I.IsKInjective →
    IsIso (βj.app ((HomotopyCategory.quotient (Modules.{u, u} B S hS V.1 V.2)
      (ComplexShape.up ℤ)).obj (((quasicoherentSheavesι B S hS V).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I)))

/-- **The square of [Stacks, Tag 09TG] commutes exactly when `Rj_*` is computed by `j_*` on the
K-injective complexes of quasi-coherent modules.** -/
theorem derivedPushforwardSquareCommutes_iff (hpush : PushforwardPreservesQuasicoherence B S hS j)
    (Φ : DerivedCategory (QuasicoherentSheaves.{u, u} B S hS V.1 V.2) ⥤
      DerivedCategory (QuasicoherentSheaves.{u, u} B S hS W.1 W.2))
    (βΦ : (quasicoherentPushforward B S hS j hpush).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Φ)
    (hΦ : Φ.IsRightDerivedFunctor βΦ
      (HomotopyCategory.quasiIso (QuasicoherentSheaves.{u, u} B S hS V.1 V.2) (ComplexShape.up ℤ)))
    (Rj : DerivedCategory (Modules.{u, u} B S hS V.1 V.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (βj : (modulePushforward B S hS j).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj) :
    DerivedPushforwardSquareCommutes B S hS j hpush Φ βΦ hΦ Rj βj ↔
      DerivedPushforwardComputedOnKInjectives B S hS j Rj βj :=
  let := isGrothendieckAbelian_quasicoherentSheaves_algebraicSpace B S hS V
  Stacks.DerivedCoherator.isIso_pushforwardSquareComparison_iff.{u}
    (quasicoherentSheavesι B S hS V) (quasicoherentSheavesι B S hS W)
    (quasicoherentPushforward B S hS j hpush) (modulePushforward B S hS j)
    (quasicoherentPushforwardCompιIso B S hS j hpush) Φ βΦ Rj βj

/-- A right derived functor of the direct image on quasi-coherent modules exists: `QCoh(𝒪_V)` is
Grothendieck abelian. -/
lemma hasRightDerivedFunctor_quasicoherentPushforward
    (hpush : PushforwardPreservesQuasicoherence B S hS j) :
    ((quasicoherentPushforward B S hS j hpush).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso (QuasicoherentSheaves.{u, u} B S hS V.1 V.2)
          (ComplexShape.up ℤ)) :=
  let := isGrothendieckAbelian_quasicoherentSheaves_algebraicSpace B S hS V
  Stacks.DerivedCoherator.hasRightDerivedFunctor_of_isGrothendieckAbelian.{u} _

end Square

/-! ### The hypothesis of Stacks 09TG -/

section Hypothesis

variable (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **The hypothesis of [Stacks, Tag 09TG].**  For every étale morphism `j : V ⟶ W` of algebraic
spaces with `W ⊆ X` a quasi-compact open subspace and `V` affine, whose direct image preserves
quasi-coherence (which Stacks 03M9 grants in the source), the right derived functor
`Φ : D(QCoh(𝒪_V)) ⥤ D(QCoh(𝒪_W))` of `j_* : QCoh(𝒪_V) ⥤ QCoh(𝒪_W)` fits into the commutative square
with `Rj_*`: the canonical comparison is invertible.

The derived functors are asserted to exist with their comparison maps, the source's "the right
derived functor" being determined only up to a unique isomorphism. -/
def ExistsAffineEtaleDerivedPushforwardSquare : Prop :=
  ∀ (W : AlgebraicSpaces B S hS) (jW : W ⟶ (⟨F, hF⟩ : AlgebraicSpaces B S hS)),
    IsOpenImmersion B S hS jW.hom → IsQuasiCompactSpace B S hS W.1 →
    ∀ (V : AlgebraicSpaces B S hS) (j : V ⟶ W), IsEtale B S hS j.hom →
      IsAffineSpace B S hS V.1 →
      ∀ hpush : PushforwardPreservesQuasicoherence B S hS j,
      ∃ (Φ : DerivedCategory (QuasicoherentSheaves.{u, u} B S hS V.1 V.2) ⥤
            DerivedCategory (QuasicoherentSheaves.{u, u} B S hS W.1 W.2))
        (βΦ : (quasicoherentPushforward B S hS j hpush).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Φ)
        (hΦ : Φ.IsRightDerivedFunctor βΦ (HomotopyCategory.quasiIso
          (QuasicoherentSheaves.{u, u} B S hS V.1 V.2) (ComplexShape.up ℤ)))
        (Rj : DerivedCategory (Modules.{u, u} B S hS V.1 V.2) ⥤
            DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
        (βj : (modulePushforward B S hS j).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj),
        Rj.IsRightDerivedFunctor βj
            (HomotopyCategory.quasiIso (Modules.{u, u} B S hS V.1 V.2) (ComplexShape.up ℤ)) ∧
          DerivedPushforwardSquareCommutes B S hS j hpush Φ βΦ hΦ Rj βj

/-- **The hypothesis of [Stacks, Tag 09TG] from the K-injective condition.**  It suffices that for
every `j` as in `AlgebraicGeometry.Space.ExistsAffineEtaleDerivedPushforwardSquare` some right
derived functor of the direct image is computed by `j_*` on K-injective complexes of quasi-coherent
modules. -/
theorem affineEtaleDerivedPushforwardSquareCommutes_of_kInjectives
    (h : ∀ (W : AlgebraicSpaces B S hS) (jW : W ⟶ (⟨F, hF⟩ : AlgebraicSpaces B S hS)),
      IsOpenImmersion B S hS jW.hom → IsQuasiCompactSpace B S hS W.1 →
      ∀ (V : AlgebraicSpaces B S hS) (j : V ⟶ W), IsEtale B S hS j.hom →
        IsAffineSpace B S hS V.1 → PushforwardPreservesQuasicoherence B S hS j →
        ∃ (Rj : DerivedCategory (Modules.{u, u} B S hS V.1 V.2) ⥤
              DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
          (βj : (modulePushforward B S hS j).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
              DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rj),
          Rj.IsRightDerivedFunctor βj
              (HomotopyCategory.quasiIso (Modules.{u, u} B S hS V.1 V.2) (ComplexShape.up ℤ)) ∧
            DerivedPushforwardComputedOnKInjectives B S hS j Rj βj) :
    ExistsAffineEtaleDerivedPushforwardSquare B S hS F hF := by
  intro W jW hjW hWqc V j hj hV hpush
  obtain ⟨Rj, βj, hRj, hK⟩ := h W jW hjW hWqc V j hj hV hpush
  have := hasRightDerivedFunctor_quasicoherentPushforward B S hS j hpush
  exact ⟨_, _, inferInstance, Rj, βj, hRj,
    (derivedPushforwardSquareCommutes_iff B S hS j hpush
      (((quasicoherentPushforward B S hS j hpush).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
          (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)))
      (((quasicoherentPushforward B S hS j hpush).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
          (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)))
      inferInstance Rj βj).2 hK⟩

end Hypothesis

end AlgebraicGeometry.Space

end
