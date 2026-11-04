module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentEtaleLocality
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCoversTopLocality
import all StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentEtaleLocality

/-!
# Étale locality of the second clause of Stacks 06WJ, at a free section universe

`AlgebraicGeometry.Stack.isQuasicoherentOnSite_restrictModuleToSmallEtale_of_etaleCover` of
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentEtaleLocality` says that
quasi-coherence of the restriction of a presheaf of modules to the small étale site is étale-local
on the object, for modules whose sections lie in the universe of the structure sheaf.  This file
proves the same statement with the universe of the module sections free.

## Main results

* `AlgebraicGeometry.Stack.isQuasicoherentOnSite_restrictModuleToSmallEtale_of_etaleCover'`:
  **the second clause of Stacks 06WJ is étale-local on the object**, at a free section universe.

## Implementation notes

The universe of the module sections is independent of the universe of the structure sheaf for the
sheaf condition and for the comparison isomorphism of the base file, and the two results of
Stacks 03DN and 03DM that the locality statement consumes are taken here in the forms with that
universe left free,
`Stacks.SheafOfModules.isQuasicoherentOnSite_of_coversTop_isQuasicoherentOnSite` and
`Stacks.SheafOfModules.isQuasicoherentOnSite_of_reindex'`, rather than in the forms
`Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_isQuasicoherentOnSite` and
`Stacks.SheafOfModules.isQuasicoherentOnSite_of_reindex`, which require the sections and the
scalars to lie in one universe.  The comparison isomorphism of the base file and its covering
lemma are private there and universe-free already, so this file imports that module with
`import all` and uses them rather than restating them.

## References

* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

universe u v w m

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

variable {𝒳 : Type v} [Category.{w} 𝒳]

/-- Quasi-coherence of the restriction at the source of an arrow lying over an étale morphism of
schemes gives quasi-coherence of the restriction at the target over the chart of that arrow.

The small étale site of the scheme below the source is the localization at the chart of the small
étale site of the scheme below the target (Stacks 03S3), and the comparison isomorphism
identifies the two modules across that equivalence, so Stacks 03DM applies.

The universe of the module sections is free here. -/
private theorem isQuasicoherentOnSite_over_etaleChart'
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) {z x : 𝒳} (φ : z ⟶ x)
    (hφ : Etale (B.inclusion.map (p.map φ).left))
    (F : PresheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hF : Presheaf.IsSheaf (associatedTopology B S hS p (etaleTopology B)) F.presheaf)
    (hQC : (⟨restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B) F,
        restrictModuleToSmallEtale_isSheaf B E h S hS p hp z F hF⟩ :
      SheafOfModules (SmallEtale.structureSheaf E (p.obj z).left.1
        (contains_base B E h S hS p z))).IsQuasicoherentOnSite) :
    ((⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F,
        restrictModuleToSmallEtale_isSheaf B E h S hS p hp x F hF⟩ :
      SheafOfModules (SmallEtale.structureSheaf E (p.obj x).left.1
        (contains_base B E h S hS p x))).over
      (etaleChart B E h S hS p φ hφ)).IsQuasicoherentOnSite := by
  let hx := contains_base B E h S hS p x
  let U := etaleChart B E h S hS p φ hφ
  let R := SmallEtale.structureSheaf E (p.obj x).left.1 hx
  let M : SheafOfModules R :=
    ⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
      (etaleTopology_le_topology B) F,
      restrictModuleToSmallEtale_isSheaf B E h S hS p hp x F hF⟩
  let eqv := smallEtaleEquivalenceOver E (p.obj x).left.1 hx U
  let N : SheafOfModules (SmallEtale.structureSheaf E U.obj.left.1 U.obj.left.property) :=
    ⟨restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
      (etaleTopology_le_topology B) F,
      restrictModuleToSmallEtale_isSheaf B E h S hS p hp z F hF⟩
  have eM : ((SheafOfModules.pushforward.{m}
      (𝟙 (Stacks.SheafOfModules.reindexRing
        (SmallEtale.topology E U.obj.left.1 U.obj.left.property) eqv (R.over U)))).obj
      (M.over U)).val ≅ N.val :=
    (PresheafOfModules.pushforwardComp (F := eqv.functor) (G := Over.forget U)
      (T := R.obj) (𝟙 _) (𝟙 _)).app M.val ≪≫
      restrictModulePostcomposeIso B E h S hS p hp φ hφ F
  let eSheaf : (SheafOfModules.pushforward.{m}
      (𝟙 (Stacks.SheafOfModules.reindexRing
        (SmallEtale.topology E U.obj.left.1 U.obj.left.property) eqv (R.over U)))).obj
      (M.over U) ≅ N :=
    (SheafOfModules.fullyFaithfulForget _).preimageIso eM
  exact Stacks.SheafOfModules.isQuasicoherentOnSite_of_reindex' eqv (R.over U) (M.over U)
    (SheafOfModules.IsQuasicoherentOnSite.of_iso eSheaf.symm hQC)

/-- **The second clause of Stacks 06WJ is étale-local on the object.** If arrows `φ i : y i ⟶ x`
of `𝒳` lie over étale morphisms of schemes which are jointly surjective onto the scheme below
`x`, and the restriction to the small étale site is quasi-coherent at every `y i`, then it is
quasi-coherent at `x`.

The charts of the `φ i` cover the final object of the small étale site of the scheme below `x`,
and quasi-coherence is local on a covering of the final object (Stacks 03DN).

The universe of the module sections is free here;
`AlgebraicGeometry.Stack.isQuasicoherentOnSite_restrictModuleToSmallEtale_of_etaleCover` is this
statement at the universe of the structure sheaf. -/
theorem isQuasicoherentOnSite_restrictModuleToSmallEtale_of_etaleCover'
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) (x : 𝒳)
    (F : PresheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hF : Presheaf.IsSheaf (associatedTopology B S hS p (etaleTopology B)) F.presheaf)
    {I : Type (u + 1)} (y : I → 𝒳) (φ : ∀ i, y i ⟶ x)
    (hetale : ∀ i, Etale (B.inclusion.map (p.map (φ i)).left))
    (hcov : ∀ t : B.inclusion.obj (p.obj x).left,
      ∃ i, t ∈ Set.range (B.inclusion.map (p.map (φ i)).left))
    (hQC : ∀ i, (⟨restrictModuleToSmallEtale B E h S hS p hp (y i) (etaleTopology B)
        (etaleTopology_le_topology B) F,
        restrictModuleToSmallEtale_isSheaf B E h S hS p hp (y i) F hF⟩ :
      SheafOfModules (SmallEtale.structureSheaf E (p.obj (y i)).left.1
        (contains_base B E h S hS p (y i)))).IsQuasicoherentOnSite) :
    (⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F,
        restrictModuleToSmallEtale_isSheaf B E h S hS p hp x F hF⟩ :
      SheafOfModules (SmallEtale.structureSheaf E (p.obj x).left.1
        (contains_base B E h S hS p x))).IsQuasicoherentOnSite := by
  let M : SheafOfModules (SmallEtale.structureSheaf E (p.obj x).left.1
      (contains_base B E h S hS p x)) :=
    ⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
      (etaleTopology_le_topology B) F,
      restrictModuleToSmallEtale_isSheaf B E h S hS p hp x F hF⟩
  exact Stacks.SheafOfModules.isQuasicoherentOnSite_of_coversTop_isQuasicoherentOnSite M
    (coversTop_etaleChart B E h S hS p x y φ hetale hcov) fun i =>
    isQuasicoherentOnSite_over_etaleChart' B E h S hS p hp (φ i) (hetale i) F hF (hQC i)

end AlgebraicGeometry.Stack

end
