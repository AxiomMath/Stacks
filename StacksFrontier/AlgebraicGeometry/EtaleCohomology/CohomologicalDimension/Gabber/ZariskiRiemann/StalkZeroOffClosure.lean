module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.CenteredGermDeathOfValuation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.AffineLineStalkCount
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedFunctorAdditive

/-!
# The higher direct images of a proper model vanish off the closure of the generic point

Let `B` be a domain with fraction field `K`, `M` a proper model `f : Y ⟶ Spec B` with point
`j : η = Spec K ⟶ Y`, and `F` an abelian sheaf on `η_étale`. At a geometric point `s` of `Y`
whose image is not in the closure of the image of `j`, the stalk of `R^q j_* F` vanishes.

By Stacks 03Q9
(`AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.stalkRightDerivedIsoStrictHenselization`)
the stalk is the cohomology of `η ×_Y Spec 𝒪^{sh}_{Y,s}`. Every point of `Spec 𝒪^{sh}_{Y,s}` maps
to a generization of the image `y` of `s`, so a point of `η ×_Y Spec 𝒪^{sh}_{Y,s}` would give a
point of the image of `j` specializing to `y`; hence this scheme is empty, every abelian sheaf on
its étale site is zero, and so is its cohomology. A geometric point with a separably closed field
is first replaced by its algebraic closure, which does not change the stalk.

This is the case of a point off the closure in the vanishing of germs of higher direct images
in Gabber's theorem on cohomological dimension, and uses only the isomorphism of Stacks 03Q9
between stalks of higher direct images and cohomology over the strict henselization.

## Main results

* `AlgebraicGeometry.isEmpty_strictHenselizationBaseChange_of_not_mem_closure` —
  `X ×_S Spec 𝒪^{sh}_{S,s}` is empty when the image of `s` is off the closure of the image of
  `X ⟶ S`.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.stalkZeroOffClosure` — a proof of
  `AlgebraicGeometry.Scheme.ZariskiRiemann.StalkZeroOffClosure`.

## References

* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry

/-- **The base change to the strict henselization is empty off the closure of the image.** If
the image of a geometric point `s` of `S` is not in the closure of the image of `f : X ⟶ S`, then
`X ×_S Spec 𝒪^{sh}_{S,s}` has no points: every point of `Spec 𝒪^{sh}_{S,s}` maps to a
generization of the image of `s`, so a point of the base change would give a point of the image
of `f` specializing to it. -/
theorem isEmpty_strictHenselizationBaseChange_of_not_mem_closure (B : BigEtaleSite.{u})
    {X S : Scheme.{u}} (hS : B.Contains S) (f : X ⟶ S) (s : GeometricPoint S)
    (hs : s.hom (default : Spec (.of s.residueField)) ∉ closure (Set.range f)) :
    IsEmpty (strictHenselizationBaseChange B hS f s) := by
  refine ⟨fun z ↦ hs ?_⟩
  have hsp : ∀ w, strictHenselizationToBase B S hS s w ⤳
      s.hom (default : Spec (.of s.residueField)) := by
    intro w
    have hz : strictHenselizationToBase B S hS s w ∈
        Set.range (S.fromSpecStalk (s.hom (IsLocalRing.closedPoint s.residueField))) := by
      rw [strictHenselizationToBase, Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    rw [range_fromSpecStalk] at hz
    rwa [show (default : Spec (.of s.residueField)) = IsLocalRing.closedPoint s.residueField from
      Subsingleton.elim _ _]
  have hj : f (pullback.fst f (strictHenselizationToBase B S hS s) z) =
      strictHenselizationToBase B S hS s
        (pullback.snd f (strictHenselizationToBase B S hS s) z) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  exact closure_mono (Set.singleton_subset_iff.2 (Set.mem_range_self _))
    (specializes_iff_mem_closure.1 (hj ▸ hsp _))

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.ZariskiRiemann

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

open Stacks.EtaleCohomology

namespace ProperModel

variable {B : Type u} [CommRing B] [IsDomain B] (M : ProperModel B)

omit [IsDomain B] in
/-- **The stalk of `R^q j_*F` vanishes off the closure of `j(η)`**, at a geometric point with
an algebraically closed field: by Stacks 03Q9 it is the cohomology of the empty scheme
`η ×_Y Spec 𝒪^{sh}_{Y,s}`. -/
theorem isZero_stalk_rightDerived_of_not_mem_closure
    (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (s : GeometricPoint M.Y)
    (hs : s.hom (default : Spec (.of s.residueField)) ∉ closure (Set.range M.j)) :
    IsZero ((smallEtaleStalkAb s.hom).obj
      (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F)) := by
  have := isEmpty_strictHenselizationBaseChange_of_not_mem_closure
    (BigEtaleSite.containing M.Y) (BigEtaleSite.contains_containing M.Y) M.j s hs
  have : ((Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange
      (BigEtaleSite.containing M.Y) (BigEtaleSite.contains_containing M.Y) M.j s))
      Ab.{u + 1}).rightDerived q).Additive := Functor.additive_rightDerived _ q
  refine IsZero.of_iso (Functor.map_isZero _ ?_) (M.stalkRightDerivedIsoStrictHenselization F q s)
  refine isZero_of_forall_isZero_sections.{u, u + 1} _ fun V ↦
    isZero_sections_of_isEmpty.{u, u + 1} _ V ⟨fun x ↦ IsEmpty.elim ‹_› (V.hom x)⟩

end ProperModel

/-- **`R^q j_* F` vanishes off the closure of `j(η)`**: a proof of
`AlgebraicGeometry.Scheme.ZariskiRiemann.StalkZeroOffClosure`. The stalk at a geometric point
`s` with a separably closed field is the stalk at `s` composed with the algebraic closure, which
vanishes by
`AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.isZero_stalk_rightDerived_of_not_mem_closure`. -/
theorem stalkZeroOffClosure : StalkZeroOffClosure.{u} := by
  intro B _ _ M F q Ω _ _ s hs
  let π : Spec (.of (AlgebraicClosure Ω)) ⟶ Spec (.of Ω) :=
    Spec.map (CommRingCat.ofHom (algebraMap Ω (AlgebraicClosure Ω)))
  obtain ⟨e⟩ := Stacks.EtaleCohomology.Purity.nonempty_stalk_comp_iso_stalk
    (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F) s π
  refine IsZero.of_iso ?_ e.symm
  refine M.isZero_stalk_rightDerived_of_not_mem_closure F q ⟨AlgebraicClosure Ω, π ≫ s⟩ ?_
  change (π ≫ s) (default : Spec (.of (AlgebraicClosure Ω))) ∉ _
  rwa [Scheme.Hom.comp_apply, Subsingleton.elim (π _) (default : Spec (.of Ω))]

end AlgebraicGeometry.Scheme.ZariskiRiemann
