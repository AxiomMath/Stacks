module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusDescent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The inverse image along the geometric Frobenius

Let `k` be a finite field with `q = p ^ f` elements and let `X` be a scheme over `k` with
geometric Frobenius `π_X`. This file states Stacks Tag 03SR in full: for a sheaf `ℱ` on the small
étale site of `X` there are canonical isomorphisms `π_X^{-1} ℱ ≅ ℱ` and `ℱ ≅ (π_X)_* ℱ`. The
inverse image `π_X^{-1}` exists here with nothing assumed of the coefficient category.

## Main definitions

* `Stacks.EtaleCohomology.geometricFrobeniusSheafPullbackIso` — the inverse image along `π_X` is
  canonically isomorphic to the identity functor, for sheaves with values in any category.
* `Stacks.EtaleCohomology.geometricFrobeniusDescentIsos` — Stacks Tag 03SR: the inverse image
  and the direct image along `π_X` are both canonically isomorphic to the identity functor.

## Main results

* `CategoryTheory.Functor.hasLeftKanExtension_of_isEquivalence` — every functor has a left Kan
  extension along an equivalence of categories.
* `Stacks.EtaleCohomology.isEquivalence_smallEtaleBaseChange_geometricFrobenius` — base change
  along `π_X` is an equivalence of the small étale site.
* `Stacks.EtaleCohomology.isEquivalence_sheafPushforwardContinuous_geometricFrobenius` — direct
  image along `π_X` is an equivalence of sheaf categories, for any coefficients.
* `Stacks.EtaleCohomology.sheafAdjunctionContinuous_unit_comp_geometricFrobeniusSheafPullbackIso`
  — the inverse-image isomorphism is the left-adjoint mate of the direct-image isomorphism.
* `Stacks.EtaleCohomology.sheafPullbackIso_trans_geometricFrobeniusInverseImageIso_types` — for
  sheaves of sets the sheafified left Kan extension exists unconditionally and gives the same
  isomorphism.

## Implementation notes

The inverse image is Mathlib's `CategoryTheory.Functor.sheafPullback`, the left adjoint of direct
image, as for `Stacks.EtaleCohomology.etaleModuleInverseImage`. Its existence needs the direct
image to be a right adjoint, and here the direct image is even an equivalence: base change by
`π_X` is isomorphic to the identity functor of the small étale site, by the iterated relative
Frobenius `γ_U` of Tag 0CCG. The same fact gives the left Kan extensions along base change by
`π_X` for every coefficient category, so where sheafification exists (for instance for sets,
abelian groups and modules with `u`-small carriers, by Mathlib) the construction of the inverse
image as a sheafified left Kan extension also applies with nothing assumed, and agrees with the
abstract one.

## References

* [Stacks Project, Tag 03SR](https://stacks.math.columbia.edu/tag/03SR)
* [Stacks Project, Tag 0CCG](https://stacks.math.columbia.edu/tag/0CCG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor

/-- Every functor `F : C ⥤ H` has a left Kan extension along an equivalence `L : C ⥤ D`: the
composite of a quasi-inverse of `L` with `F`, with the unit of the equivalence as the unit of
the extension. -/
public lemma hasLeftKanExtension_of_isEquivalence {C : Type u₁} {D : Type u₂} {H : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} H] (L : C ⥤ D) [L.IsEquivalence]
    (F : C ⥤ H) : L.HasLeftKanExtension F :=
  let α : F ≅ L.asEquivalence.functor ⋙ L.asEquivalence.inverse ⋙ F :=
    F.leftUnitor.symm ≪≫ isoWhiskerRight L.asEquivalence.unitIso F ≪≫ Functor.associator _ _ _
  (isUniversalOfIsLeftKanExtension (L := L.asEquivalence.functor) _ α.hom).hasInitial

end CategoryTheory.Functor

namespace Stacks.EtaleCohomology

section GeometricFrobenius

variable {k : Type u} [Field k] [Fintype k] (X : CategoryTheory.Over (Spec (.of k))) (p f : ℕ)
  [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ f)

/-- Base change along the geometric Frobenius `π_X` is an equivalence of the small étale site of
`X`: it is isomorphic to the identity functor, by the relative Frobenius `γ_U` of each étale
`X`-scheme `U`. -/
public instance isEquivalence_smallEtaleBaseChange_geometricFrobenius :
    (smallEtaleBaseChange (Stacks.Frobenius.geometricFrobenius X p f hcard).left).IsEquivalence :=
  Functor.isEquivalence_of_iso (geometricFrobeniusEtaleSiteIso X p f hcard)

/-- Every presheaf on the small étale site of `X`, with values in any category, has a left Kan
extension along base change by the geometric Frobenius, since that base change is an
equivalence. This is the presheaf pullback along `π_X`. -/
public instance hasLeftKanExtension_smallEtaleBaseChange_geometricFrobenius_op
    {A : Type*} [Category* A] (F : X.left.Etaleᵒᵖ ⥤ A) :
    (smallEtaleBaseChange
      (Stacks.Frobenius.geometricFrobenius X p f hcard).left).op.HasLeftKanExtension F :=
  Functor.hasLeftKanExtension_of_isEquivalence _ F

/-- Direct image of sheaves along the geometric Frobenius `π_X` is an equivalence, for sheaves
with values in any category: it is isomorphic to the identity functor
(`geometricFrobeniusPushforwardIso`). -/
public instance isEquivalence_sheafPushforwardContinuous_geometricFrobenius
    (A : Type*) [Category* A] :
    ((smallEtaleBaseChange
        (Stacks.Frobenius.geometricFrobenius X p f hcard).left).sheafPushforwardContinuous A
      (smallEtaleTopology X.left) (smallEtaleTopology X.left)).IsEquivalence :=
  Functor.isEquivalence_of_iso (geometricFrobeniusPushforwardIso X p f hcard A)

variable (A : Type*) [Category* A]

/-- The inverse image `π_X^{-1}` along the geometric Frobenius, the left adjoint of direct image
`(π_X)_*` (which exists, since `(π_X)_*` is an equivalence), is canonically isomorphic to the
identity functor of sheaves on the small étale site of `X`, for sheaves with values in any
category. It is the left-adjoint mate of `geometricFrobeniusPushforwardIso`. -/
@[sga "5 XII 7.3" "more general"]
public def geometricFrobeniusSheafPullbackIso :
    Functor.sheafPullback
        (smallEtaleBaseChange (Stacks.Frobenius.geometricFrobenius X p f hcard).left) A
        (smallEtaleTopology X.left) (smallEtaleTopology X.left) ≅
      𝟭 (Sheaf (smallEtaleTopology X.left) A) :=
  Adjunction.leftAdjointUniq
    (Functor.sheafAdjunctionContinuous
      (smallEtaleBaseChange (Stacks.Frobenius.geometricFrobenius X p f hcard).left) A
      (smallEtaleTopology X.left) (smallEtaleTopology X.left))
    (Adjunction.id.ofNatIsoRight (geometricFrobeniusPushforwardIso X p f hcard A))

/-- The inverse-image isomorphism along the geometric Frobenius is the left-adjoint mate of the
direct-image isomorphism: composed with the unit of the adjunction `π_X^{-1} ⊣ (π_X)_*`, its
direct image is the direct-image isomorphism. This determines it uniquely. -/
@[sga "5 XII 7.3" "partial"]
public lemma sheafAdjunctionContinuous_unit_comp_geometricFrobeniusSheafPullbackIso
    (F : Sheaf (smallEtaleTopology X.left) A) :
    (Functor.sheafAdjunctionContinuous
          (smallEtaleBaseChange (Stacks.Frobenius.geometricFrobenius X p f hcard).left) A
          (smallEtaleTopology X.left) (smallEtaleTopology X.left)).unit.app F ≫
        ((smallEtaleBaseChange
          (Stacks.Frobenius.geometricFrobenius X p f hcard).left).sheafPushforwardContinuous A
          (smallEtaleTopology X.left) (smallEtaleTopology X.left)).map
            ((geometricFrobeniusSheafPullbackIso X p f hcard A).hom.app F) =
      (geometricFrobeniusPushforwardIso X p f hcard A).hom.app F := by
  simp [geometricFrobeniusSheafPullbackIso, Adjunction.ofNatIsoRight, Adjunction.id]

/-- **Stacks Project, Tag 03SR.** Let `k` be a finite field with `q = p ^ f` elements, let `X` be
a scheme over `k` with geometric Frobenius `π_X = F_X^f`, and let `ℱ` be a sheaf on the small
étale site `X_étale`, with values in any category (sets, abelian groups, `Λ`-modules, ...).
Then there are canonical isomorphisms `π_X^{-1} ℱ ≅ ℱ` and `ℱ ≅ (π_X)_* ℱ`, natural in `ℱ`.

Here `(π_X)_*` is precomposition with base change along `π_X`, and the inverse image `π_X^{-1}`
is the left adjoint of `(π_X)_*`; its existence is proved, not assumed, since `(π_X)_*` is an
equivalence. Where the coefficients admit sheafification it agrees with the sheafified left Kan
extension (`CategoryTheory.Functor.sheafPullbackConstruction.sheafPullbackIso`), whose Kan
extensions exist by `hasLeftKanExtension_smallEtaleBaseChange_geometricFrobenius_op`. On
sections over an étale `φ : U ⟶ X` the second isomorphism is restriction along the inverse of
`γ_U = (F_U^f, φ) : U ⟶ U ×_{φ, X, π_X} X` (`geometricFrobeniusPushforwardIso_hom_app_hom_app`),
and the first is its left-adjoint mate
(`sheafAdjunctionContinuous_unit_comp_geometricFrobeniusSheafPullbackIso`). -/
@[stacks 03SR, sga "4½ Rapport 1.2", sga "5 XII 7.3" "more general"]
public def geometricFrobeniusDescentIsos :
    (Functor.sheafPullback
        (smallEtaleBaseChange (Stacks.Frobenius.geometricFrobenius X p f hcard).left) A
        (smallEtaleTopology X.left) (smallEtaleTopology X.left) ≅
      𝟭 (Sheaf (smallEtaleTopology X.left) A)) ×
    (𝟭 (Sheaf (smallEtaleTopology X.left) A) ≅
      (smallEtaleBaseChange
          (Stacks.Frobenius.geometricFrobenius X p f hcard).left).sheafPushforwardContinuous A
        (smallEtaleTopology X.left) (smallEtaleTopology X.left)) :=
  ⟨geometricFrobeniusSheafPullbackIso X p f hcard A, geometricFrobeniusPushforwardIso X p f hcard A⟩

/-- For sheaves of sets, the coefficients of the source statement, the sheafified left Kan
extension along base change by `π_X` exists with nothing assumed, so the constructed inverse
image `geometricFrobeniusInverseImageIso` applies unconditionally; it agrees with the first
isomorphism of Tag 03SR under the comparison of the constructed and abstract inverse images. -/
public lemma sheafPullbackIso_trans_geometricFrobeniusInverseImageIso_types :
    Functor.sheafPullbackConstruction.sheafPullbackIso
        (smallEtaleBaseChange (Stacks.Frobenius.geometricFrobenius X p f hcard).left) (Type u)
        (smallEtaleTopology X.left) (smallEtaleTopology X.left) ≪≫
      geometricFrobeniusInverseImageIso X p f hcard (Type u) =
    geometricFrobeniusSheafPullbackIso X p f hcard (Type u) :=
  Iso.ext (Adjunction.leftAdjointUniq_trans _ _ _)

end GeometricFrobenius

end Stacks.EtaleCohomology

end
