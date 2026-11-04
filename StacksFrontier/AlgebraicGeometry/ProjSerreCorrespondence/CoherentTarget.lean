module

public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.ProjCoherentModule.Basic
public import StacksFrontier.AlgebraicGeometry.ProjSerreCorrespondence.Faithful

/-!
# The arrow of Stacks 0BXF at its own target, `Coh(𝒪_X)`

Let `A` be a graded ring which is Noetherian as a ring, let `X = Proj A` and let `d` be a
positive integer. Stacks 0BXF's arrow has `Coh(𝒪_X)` for its target, not all sheaves of
`𝒪_X`-modules. This file corestricts the functor to the coherent ones: the sheaf associated to a
finitely generated graded module over a Noetherian graded ring is coherent, by
`AlgebraicGeometry.ProjectiveSpectrum.Proj.isCoherent_associatedModuleSheafFunctor_obj`, so
`M ↦ M̃` lands in `Coh(𝒪_X)` and so does the functor it induces on the quotient category.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.coherentAssociatedSheafFunctor`: `M ↦ M̃` on
  `Mod^fg_A`, with `Coh(𝒪_X)` for its target.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.coherentIrrelevantQuotientFunctor`: **the
  arrow `Mod^fg_A / Mod^fg_{A, irrelevant} ⟶ Coh(𝒪_X)` of Stacks 0BXF.**

## Main results

* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.isCoherent_finiteAssociatedSheafFunctor_obj`:
  `M̃` is coherent for every finitely generated graded module.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.coherentIrrelevantQuotientFunctorιIso`: the
  corestricted arrow composed with the inclusion of `Coh(𝒪_X)` is the arrow into all sheaves of
  modules.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.faithful_coherentIrrelevantQuotientFunctor`
  and `exists_pos_faithful_coherentIrrelevantQuotientFunctor`: **the arrow into `Coh(𝒪_X)` is
  faithful**, at exactly the source's hypotheses in the second.

## Implementation notes

The target category is the library's `AlgebraicGeometry.SheafOfModules.CoherentModules`, Tag 01BV's
`Coh(𝒪_X)`, so that its abelian structure
(`AlgebraicGeometry.CoherentAbelian.coherentModulesAbelian`) and the exactness of its inclusion
come with it; no object property of its own is introduced here. Its predicate is the *root*
`SheafOfModules.IsCoherent`, which is the one
`AlgebraicGeometry.ProjectiveSpectrum.Proj.isCoherent_associatedModuleSheafFunctor_obj` produces
and the one Tag 0B5Q is stated over — inside a namespace beginning with `Stacks.` the
unqualified spelling would resolve to `Stacks.SheafOfModules.IsCoherent` instead, and the two
are bridged only by `AlgebraicGeometry.CoherentAbelian.coherentModules_eq`.

Corestricting is `CategoryTheory.ObjectProperty.lift`, and the factorization through the
quotient category is `CategoryTheory.Localization.lift` again, at the same inverted morphisms:
the inclusion of a full subcategory is fully faithful, hence reflects isomorphisms, so a
morphism inverted by `M ↦ M̃` is inverted by its corestriction. That the two arrows agree —
`coherentIrrelevantQuotientFunctorιIso` — is `CategoryTheory.Localization.liftNatIso` applied to
`CategoryTheory.ObjectProperty.liftCompιIso`, and faithfulness of the corestriction follows from
it because a functor whose composite with a further functor is faithful is faithful.

## References

* [Stacks Project, Tag 0BXF](https://stacks.math.columbia.edu/tag/0BXF)
* [Stacks Project, Tag 01BV](https://stacks.math.columbia.edu/tag/01BV)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality

namespace Stacks.AlgebraicGeometry.ProjSerreCorrespondence

universe u w

attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮] [IsNoetherianRing S] {d : ℕ}

/-- **The sheaf associated to a finitely generated graded module over a Noetherian graded ring is
coherent.** This is the finiteness half of Stacks 0B5Q, which is what lets the arrow of Stacks
0BXF have `Coh(𝒪_X)` for its target. -/
public theorem isCoherent_finiteAssociatedSheafFunctor_obj (M : FiniteGradedModules.{u, u, w} 𝒮) :
    ((finiteAssociatedSheafFunctor.{u, w} 𝒮).obj M).IsCoherent :=
  have := M.property
  _root_.AlgebraicGeometry.ProjectiveSpectrum.Proj.isCoherent_associatedModuleSheafFunctor_obj
    𝒮 M.obj

/-- **`M ↦ M̃` on the finitely generated graded modules, with `Coh(𝒪_X)` for its target.** -/
public def coherentAssociatedSheafFunctor :
    FiniteGradedModules.{u, u, w} 𝒮 ⥤
      _root_.AlgebraicGeometry.SheafOfModules.CoherentModules
        ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
          (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (ProjectiveSpectrum.Proj.structureSheaf 𝒮)) :=
  ObjectProperty.lift _ (finiteAssociatedSheafFunctor.{u, w} 𝒮)
    (isCoherent_finiteAssociatedSheafFunctor_obj 𝒮)

/-- The corestriction composed with the inclusion of `Coh(𝒪_X)` is `M ↦ M̃` again. -/
public def coherentAssociatedSheafFunctorιIso :
    coherentAssociatedSheafFunctor.{u, w} 𝒮 ⋙ ObjectProperty.ι _ ≅
      finiteAssociatedSheafFunctor.{u, w} 𝒮 :=
  ObjectProperty.liftCompιIso _ (finiteAssociatedSheafFunctor.{u, w} 𝒮)
    (isCoherent_finiteAssociatedSheafFunctor_obj 𝒮)

/-- A morphism of finitely generated graded modules whose kernel and cokernel are irrelevant is
inverted by the corestricted functor: the inclusion of a full subcategory reflects
isomorphisms. -/
public theorem isInvertedBy_isoModSerre_coherentAssociatedSheafFunctor (hd : 0 < d) :
    haveI := isSerreClass_irrelevantModules 𝒮 hd
    (ObjectProperty.isoModSerre (irrelevantModules.{u, u, w} 𝒮 d)).IsInvertedBy
      (coherentAssociatedSheafFunctor.{u, w} 𝒮) := by
  have := isSerreClass_irrelevantModules.{u, u, w} 𝒮 hd
  intro X Y f hf
  have := (ObjectProperty.fullyFaithfulι
    (fun M : _root_.SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (ProjectiveSpectrum.Proj.structureSheaf 𝒮)) => M.IsCoherent)).reflectsIsomorphisms
  have : IsIso ((ObjectProperty.ι _).map ((coherentAssociatedSheafFunctor.{u, w} 𝒮).map f)) :=
    isInvertedBy_isoModSerre_irrelevantModules 𝒮 hd f hf
  exact isIso_of_reflects_iso ((coherentAssociatedSheafFunctor.{u, w} 𝒮).map f)
    (ObjectProperty.ι _)

/-- **The arrow of Stacks 0BXF: the functor `Mod^fg_A / Mod^fg_{A, irrelevant} ⟶ Coh(𝒪_X)`
induced by `M ↦ M̃`.** This is the functor the proposition asserts is an equivalence, at the
proposition's own target. -/
public def coherentIrrelevantQuotientFunctor (hd : 0 < d) :
    IrrelevantQuotient 𝒮 hd ⥤
      _root_.AlgebraicGeometry.SheafOfModules.CoherentModules
        ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
          (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (ProjectiveSpectrum.Proj.structureSheaf 𝒮)) :=
  haveI := isSerreClass_irrelevantModules 𝒮 hd
  Localization.lift (coherentAssociatedSheafFunctor.{u, w} 𝒮)
    (isInvertedBy_isoModSerre_coherentAssociatedSheafFunctor 𝒮 hd) (toIrrelevantQuotient 𝒮 hd)

/-- The arrow into `Coh(𝒪_X)` composed with the quotient functor is `M ↦ M̃` again. -/
public def coherentIrrelevantQuotientFunctorFac (hd : 0 < d) :
    toIrrelevantQuotient 𝒮 hd ⋙ coherentIrrelevantQuotientFunctor.{u, w} 𝒮 hd ≅
      coherentAssociatedSheafFunctor.{u, w} 𝒮 :=
  haveI := isSerreClass_irrelevantModules 𝒮 hd
  Localization.fac (coherentAssociatedSheafFunctor.{u, w} 𝒮)
    (isInvertedBy_isoModSerre_coherentAssociatedSheafFunctor 𝒮 hd) (toIrrelevantQuotient 𝒮 hd)

/-- **The arrow into `Coh(𝒪_X)` is the arrow into all sheaves of modules**, composed with the
inclusion of the coherent ones. Both lift `M ↦ M̃` through the localization, and the two lifts of
isomorphic functors are isomorphic. -/
public def coherentIrrelevantQuotientFunctorιIso (hd : 0 < d) :
    coherentIrrelevantQuotientFunctor.{u, w} 𝒮 hd ⋙ ObjectProperty.ι _ ≅
      irrelevantQuotientFunctor.{u, w} 𝒮 hd := by
  haveI := isSerreClass_irrelevantModules 𝒮 hd
  haveI : Localization.Lifting (toIrrelevantQuotient.{u, u, w} 𝒮 hd)
      (ObjectProperty.isoModSerre (irrelevantModules.{u, u, w} 𝒮 d))
      (finiteAssociatedSheafFunctor.{u, w} 𝒮) (irrelevantQuotientFunctor.{u, w} 𝒮 hd) :=
    ⟨irrelevantQuotientFunctorFac 𝒮 hd⟩
  haveI : Localization.Lifting (toIrrelevantQuotient.{u, u, w} 𝒮 hd)
      (ObjectProperty.isoModSerre (irrelevantModules.{u, u, w} 𝒮 d))
      (coherentAssociatedSheafFunctor.{u, w} 𝒮 ⋙ ObjectProperty.ι _)
      (coherentIrrelevantQuotientFunctor.{u, w} 𝒮 hd ⋙ ObjectProperty.ι _) :=
    ⟨(Functor.associator (toIrrelevantQuotient.{u, u, w} 𝒮 hd)
        (coherentIrrelevantQuotientFunctor.{u, w} 𝒮 hd) (ObjectProperty.ι _)).symm ≪≫
      Functor.isoWhiskerRight (coherentIrrelevantQuotientFunctorFac 𝒮 hd) (ObjectProperty.ι _)⟩
  exact Localization.liftNatIso (toIrrelevantQuotient.{u, u, w} 𝒮 hd)
    (ObjectProperty.isoModSerre (irrelevantModules.{u, u, w} 𝒮 d))
    (coherentAssociatedSheafFunctor.{u, w} 𝒮 ⋙ ObjectProperty.ι _)
    (finiteAssociatedSheafFunctor.{u, w} 𝒮) _ _ (coherentAssociatedSheafFunctorιIso 𝒮)

/-- **The arrow of Stacks 0BXF into `Coh(𝒪_X)` is faithful**, under the hypotheses of the kernel
identification. -/
public theorem faithful_coherentIrrelevantQuotientFunctor
    {r : ℕ} (f : Fin r → S) (deg : Fin r → ℕ) (hdeg : ∀ i, 0 < deg i)
    (hf : ∀ i, f i ∈ 𝒮 (deg i))
    (hgen : Algebra.adjoin (Veronese.gradeZero 𝒮) (Set.range f) = ⊤)
    (hd : 0 < d) (hdvd : ∀ i, deg i ∣ d) :
    (coherentIrrelevantQuotientFunctor.{u, w} 𝒮 hd).Faithful := by
  have := faithful_irrelevantQuotientFunctor 𝒮 f deg hdeg hf hgen hd hdvd
  have : (coherentIrrelevantQuotientFunctor.{u, w} 𝒮 hd ⋙ ObjectProperty.ι _).Faithful :=
    Functor.Faithful.of_iso (coherentIrrelevantQuotientFunctorιIso 𝒮 hd).symm
  exact Functor.Faithful.of_comp (coherentIrrelevantQuotientFunctor.{u, w} 𝒮 hd)
    (ObjectProperty.ι _)

/-- **The faithfulness of Stacks 0BXF's arrow into `Coh(𝒪_X)`, at exactly the source's
hypotheses**: `A` Noetherian graded, with `d` produced as the source produces it, the least
common multiple of the degrees of a finite homogeneous generating set.

The degree cannot be quantified away: for `A = k[x]` with `deg x = 2` the module `A(1)` has
vanishing associated sheaf and is not irrelevant at `d = 1`. -/
public theorem exists_pos_faithful_coherentIrrelevantQuotientFunctor :
    ∃ (d : ℕ) (hd : 0 < d), (coherentIrrelevantQuotientFunctor.{u, w} 𝒮 hd).Faithful := by
  classical
  obtain ⟨r, f, deg, hdeg, hf, hgen⟩ := exists_homogeneous_generators_of_isNoetherianRing 𝒮
  have hpos : 0 < Finset.univ.lcm deg := Nat.pos_of_ne_zero fun h0 => by
    obtain ⟨i, -, hi⟩ := Finset.lcm_eq_zero_iff.mp h0
    exact absurd hi (hdeg i).ne'
  exact ⟨Finset.univ.lcm deg, hpos,
    faithful_coherentIrrelevantQuotientFunctor 𝒮 f deg hdeg hf hgen hpos
      fun i => Finset.dvd_lcm (Finset.mem_univ i)⟩

end Stacks.AlgebraicGeometry.ProjSerreCorrespondence

end
