module

public import StacksFrontier.AlgebraicGeometry.Spaces.Rebase.Derived
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectnessAlongAnEquivalence

/-!
# Perfect objects along the change of base scheme

Let `h : W ⟶ S` be a morphism of a big fppf site and `F` an algebraic space over `W`, with
lower-shriek extension `Λ_h F` over `S`.  The equivalence `Φ : D(𝒪_F) ⥤ D(𝒪_{Λ_h F})` of
`AlgebraicGeometry.Space.rebaseDerivedExtension` carries perfect objects to perfect objects: it is
the derived functor of the pushforward of modules along an equivalence of ringed sites whose
structure map is invertible.

## Main results

* `AlgebraicGeometry.Space.isPerfect_rebaseDerivedExtension_obj`: `Φ K` is perfect for `K`
  perfect.

## References

* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (W S : Scheme.{u}) (hW : B.Contains W) (hS : B.Contains S)
  (h : B.obj hW ⟶ B.obj hS) {F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u}
  (hF : IsAlgebraicSpace B W hW F)
  (hF' : IsAlgebraicSpace B S hS ((OverShriek.relocalizePresheafFunctor h).obj F))

/-- The structure map of the reindexing of `𝒪_{Λ_h F}` back along the equivalence of small étale
sites is invertible. -/
instance isIso_reindexBackSharp_relocalizeEquivalence :
    IsIso (Stacks.SheafOfModules.reindexBackSharp (J' := SmallEtale.topology B W hW F)
      (SmallEtale.relocalizeEquivalence B W S hW hS h F)
      (relocalizeRingSheafSE B W S hW hS h hF')) := by
  have : IsIso ((sheafToPresheaf _ _).map (Stacks.SheafOfModules.reindexBackSharp
      (J' := SmallEtale.topology B W hW F) (SmallEtale.relocalizeEquivalence B W S hW hS h F)
      (relocalizeRingSheafSE B W S hW hS h hF'))) :=
    inferInstanceAs (IsIso (Functor.whiskerRight
      (NatTrans.op (SmallEtale.relocalizeEquivalence B W S hW hS h F).counit) _))
  exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)

/-- **`Φ` carries perfect objects to perfect objects**: for a perfect object `K` of `D(𝒪_F)`,
`Φ K` is a perfect object of `D(𝒪_{Λ_h F})`. -/
theorem isPerfect_rebaseDerivedExtension_obj
    (K : @DerivedCategory (Modules.{u, u} B W hW F hF) _ _
      (HasDerivedCategory.standard (Modules.{u, u} B W hW F hF))) :
    letI := HasDerivedCategory.standard (Modules.{u, u} B W hW F hF)
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS _ hF')
    (smallEtaleRingedSite B W hW F hF).IsPerfect K →
      (smallEtaleRingedSite B S hS _ hF').IsPerfect
        ((rebaseDerivedExtension B W S hW hS h hF hF').obj K) :=
  let := HasDerivedCategory.standard (Modules.{u, u} B W hW F hF)
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS _ hF')
  fun hK => RingedSite.isPerfect_mapDerivedCategory_pushforwardEquivalenceOfIsIso
    (X := smallEtaleRingedSite B S hS _ hF') (Y := smallEtaleRingedSite B W hW F hF)
    (SmallEtale.relocalizeEquivalence B W S hW hS h F).symm
    (hfun := inferInstanceAs
      ((SmallEtale.relocalizeEquivalence B W S hW hS h F).inverse.IsContinuous
        (SmallEtale.topology B S hS _) (SmallEtale.topology B W hW F)))
    (hinv := inferInstanceAs
      ((SmallEtale.relocalizeEquivalence B W S hW hS h F).functor.IsContinuous
        (SmallEtale.topology B W hW F) (SmallEtale.topology B S hS _)))
    (Stacks.SheafOfModules.reindexBackSharp (J' := SmallEtale.topology B W hW F)
      (SmallEtale.relocalizeEquivalence B W S hW hS h F) (relocalizeRingSheafSE B W S hW hS h hF'))
    (hρ := isIso_reindexBackSharp_relocalizeEquivalence B W S hW hS h hF') K hK

end AlgebraicGeometry.Space

end
