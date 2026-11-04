module

public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.BaseChangeIso
public import StacksFrontier.AlgebraicGeometry.FiniteEtaleColimits.Basic
public import StacksFrontier.AlgebraicGeometry.QuasicoherentAlgebraEqualizer.FlatPullback

/-!
# Flat base change preserves coequalizers of finite étale covers

Let `g : P ⟶ X` be a flat morphism of schemes. Base change along `g` carries a coequalizer of two
morphisms of finite étale covers of `X` to a coequalizer of the base-changed morphisms.

Under the anti-equivalence of Stacks Tag 01SA a coequalizer in `FÉt_X` is an equalizer of
quasi-coherent algebras, namely of the two maps `a^♯, b^♯ : Z_*𝒪 ⇉ Y_*𝒪`; base change of covers
corresponds to extension of scalars of algebras
(`Stacks.AlgebraPullbackQcoh.baseChangeIso`), and extension of scalars along a flat morphism
preserves that equalizer
(`Stacks.QuasicoherentAlgebraEqualizer.preservesLimit_parallelPair_qcohAlgebraPullback`).
Transporting the resulting equalizer back along the fully faithful contravariant pushforward
functor (`Stacks.FundamentalGroup.isColimitCoforkOfIsLimitFork`) gives the coequalizer downstairs.

This is the fourth assertion of Stacks Tag 0BN9, which holds for every morphism of schemes, in the
case of a flat morphism.

## Main definitions

* `Stacks.FundamentalGroup.baseChangeAlgebraIso` — the algebra of a base-changed cover is the
  extension of scalars of the algebra of the cover.

## Main results

* `Stacks.FundamentalGroup.isLimitForkMapOpOfIsColimit` — the image of a colimit cofork of finite
  étale covers under the pushforward functor is an equalizer of algebras.
* `Stacks.FundamentalGroup.isColimitCoforkBaseChange` — **base change along a flat morphism
  preserves the coequalizer of two morphisms of finite étale covers.**

## References

* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 0BN9](https://stacks.math.columbia.edu/tag/0BN9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence Stacks.AlgebraPullbackQcoh
open Stacks.QuasicoherentAlgebraEqualizer

universe u

namespace Stacks.FundamentalGroup

variable {X P : Scheme.{u}} (g : P ⟶ X)

/-- The pullback of the algebra of a finite étale cover is the algebra of the base-changed
cover. -/
def baseChangeAlgebraIso (V : FiniteEtaleOver X) :
    (qcohAlgebraPullback g).obj ((finiteEtalePushforwardFunctor X).obj (op V)) ≅
      (finiteEtalePushforwardFunctor P).obj (op ((finiteEtaleBaseChange g).obj V)) :=
  (baseChangeIso g).app (op ((affineOfFiniteEtale X).obj V))

/-- The isomorphisms `baseChangeAlgebraIso g` are natural in the finite étale cover. -/
theorem baseChangeAlgebraIso_naturality {V V' : FiniteEtaleOver X} (h : V ⟶ V') :
    (qcohAlgebraPullback g).map ((finiteEtalePushforwardFunctor X).map h.op) ≫
        (baseChangeAlgebraIso g V).hom =
      (baseChangeAlgebraIso g V').hom ≫
        (finiteEtalePushforwardFunctor P).map ((finiteEtaleBaseChange g).map h).op :=
  (baseChangeIso g).hom.naturality (((affineOfFiniteEtale X).map h).op)

section Coequalizer

variable {Y Z : FiniteEtaleOver X} (a b : Y ⟶ Z)

/-- The image under the pushforward functor of a colimit cofork is an equalizer of algebras. -/
def isLimitForkMapOpOfIsColimit (c : Cofork a b) (hc : IsColimit c) :
    IsLimit (Fork.ofι ((finiteEtalePushforwardFunctor X).map c.π.op)
      (map_op_comp_eq_of_comp_eq (finiteEtalePushforwardFunctor X) c.condition)) := by
  refine Fork.isLimitOfIsos _ (isLimitForkMapOpFiniteEtaleCoequalizerπ a b) _ (Iso.refl _)
    (Iso.refl _)
    ((finiteEtalePushforwardFunctor X).mapIso
      (hc.coconePointUniqueUpToIso (isColimit_finiteEtaleCofork a b)).op)
    (by simp) (by simp) ?_
  change (finiteEtalePushforwardFunctor X).map _ ≫ (finiteEtalePushforwardFunctor X).map c.π.op =
    (finiteEtalePushforwardFunctor X).map _ ≫ 𝟙 _
  rw [Category.comp_id, ← Functor.map_comp]
  exact congrArg (finiteEtalePushforwardFunctor X).map (congrArg Quiver.Hom.op
    (hc.comp_coconePointUniqueUpToIso_hom (isColimit_finiteEtaleCofork a b)
      WalkingParallelPair.one))

/-- The base change of a cofork is a cofork. -/
theorem comp_map_cofork_π (c : Cofork a b) :
    (finiteEtaleBaseChange g).map a ≫ (finiteEtaleBaseChange g).map c.π =
      (finiteEtaleBaseChange g).map b ≫ (finiteEtaleBaseChange g).map c.π := by
  rw [← Functor.map_comp, ← Functor.map_comp, c.condition]

/-- The fork condition for the pulled-back algebras. -/
theorem qcohAlgebraPullback_map_op_comp_eq (c : Cofork a b) :
    (qcohAlgebraPullback g).map ((finiteEtalePushforwardFunctor X).map c.π.op) ≫
        (qcohAlgebraPullback g).map ((finiteEtalePushforwardFunctor X).map a.op) =
      (qcohAlgebraPullback g).map ((finiteEtalePushforwardFunctor X).map c.π.op) ≫
        (qcohAlgebraPullback g).map ((finiteEtalePushforwardFunctor X).map b.op) := by
  rw [← (qcohAlgebraPullback g).map_comp, ← (qcohAlgebraPullback g).map_comp,
    map_op_comp_eq_of_comp_eq (finiteEtalePushforwardFunctor X) c.condition]

/-- Pulling the equalizer of algebras back along a flat morphism leaves it an equalizer. -/
def isLimitForkQcohPullbackOfIsColimit [Flat g] (c : Cofork a b) (hc : IsColimit c) :
    IsLimit (Fork.ofι ((qcohAlgebraPullback g).map
        ((finiteEtalePushforwardFunctor X).map c.π.op))
      (qcohAlgebraPullback_map_op_comp_eq g a b c)) :=
  isLimitForkMapOfIsLimit (qcohAlgebraPullback g)
    (map_op_comp_eq_of_comp_eq (finiteEtalePushforwardFunctor X) c.condition)
    (isLimitForkMapOpOfIsColimit a b c hc)

/-- The algebras of the base-changed covers form an equalizer fork. -/
def isLimitForkMapOpBaseChange [Flat g] (c : Cofork a b) (hc : IsColimit c) :
    IsLimit (Fork.ofι
      ((finiteEtalePushforwardFunctor P).map ((finiteEtaleBaseChange g).map c.π).op)
      (map_op_comp_eq_of_comp_eq (finiteEtalePushforwardFunctor P)
        (comp_map_cofork_π g a b c))) :=
  Fork.isLimitOfIsos
    (Fork.ofι ((qcohAlgebraPullback g).map ((finiteEtalePushforwardFunctor X).map c.π.op))
      (qcohAlgebraPullback_map_op_comp_eq g a b c))
    (isLimitForkQcohPullbackOfIsColimit g a b c hc)
    (Fork.ofι ((finiteEtalePushforwardFunctor P).map ((finiteEtaleBaseChange g).map c.π).op)
      (map_op_comp_eq_of_comp_eq (finiteEtalePushforwardFunctor P)
        (comp_map_cofork_π g a b c)))
    (baseChangeAlgebraIso g Z) (baseChangeAlgebraIso g Y) (baseChangeAlgebraIso g c.pt)
    (baseChangeAlgebraIso_naturality g a).symm (baseChangeAlgebraIso_naturality g b).symm
    (baseChangeAlgebraIso_naturality g c.π).symm

/-- **Base change along a flat morphism preserves the coequalizer of two morphisms of finite
étale covers.** -/
def isColimitCoforkBaseChange [Flat g] (c : Cofork a b) (hc : IsColimit c) :
    IsColimit (Cofork.ofπ ((finiteEtaleBaseChange g).map c.π) (comp_map_cofork_π g a b c)) :=
  isColimitCoforkOfIsLimitFork (finiteEtalePushforwardFunctor P)
    ((finiteEtaleBaseChange g).map c.π)
    (map_op_comp_eq_of_comp_eq _ (comp_map_cofork_π g a b c))
    (isLimitForkMapOpBaseChange g a b c hc)

end Coequalizer

end Stacks.FundamentalGroup

end
