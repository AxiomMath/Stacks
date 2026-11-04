module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcompCocontinuous
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcompSlice
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentDenseSubsite

/-!
# Restriction along étale postcomposition preserves quasi-coherence, over any sheaf of rings

Let `f : Y ⟶ X` be an étale morphism of algebraic spaces and `R` an arbitrary sheaf of rings on
the small étale site of `X`.  Restriction of sheaves of `R`-modules along postcomposition of
étale charts with `f` lands in modules over the restricted sheaf of rings, and it preserves
quasi-coherence.  For `R = 𝒪_X` this is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_etaleModulePullback`.

Postcomposition with an étale morphism is continuous and cocontinuous, and so is its localization
at every chart, which is what `Stacks.SheafOfModules.isQuasicoherentOnSite_restriction` asks for.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_postcompRestriction`: restriction along an
  étale morphism preserves quasi-coherence, over any sheaf of rings.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **Restriction along an étale morphism preserves quasi-coherence, over any sheaf of rings.** -/
theorem isQuasicoherentOnSite_postcompRestriction (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    (R : Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u}) (M : SheafOfModules.{u} R)
    (hM : M.IsQuasicoherentOnSite) :
    ((SheafOfModules.pushforward.{u} (F := smallEtalePostcomp B S hS f hf)
      (S := ((smallEtalePostcomp B S hS f hf).sheafPushforwardContinuous RingCat.{u}
        (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)).obj R)
      (𝟙 _)).obj M).IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_restriction (smallEtalePostcomp B S hS f hf) R M hM

end AlgebraicGeometry.Space
