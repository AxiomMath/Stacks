module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegreeHom
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncationLevelHomology
public import
  StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.SequentialProIsomorphism
public import
  StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.SingleDegreeRestrictionLifting
public import StacksFrontier.AlgebraicGeometry.Duality.IdealPowerCohomologyProIso
public import StacksFrontier.CategoryTheory.Triangulated.InducedTStructureTruncation
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ProIsomorphismInterleaving

/-!
# The source presentation of Stacks 0G2H

Let `j : U ⟶ X` be an open immersion of Noetherian schemes and let `(K_n)` be a Deligne system
with complex `𝓕^•` and ideal sheaf `𝓘`. The one-degree truncation system `(τ^{≥p}τ^{≤p}K_n)` is
pro-isomorphic to the system `(𝓘^n H^p(𝓕^•))` placed in cohomological degree `p`. Consequently
the core case of [Stacks, Tag 0G2H] for such a truncation follows from the `Ext`-colimit statement
for the ideal powers of a coherent module.

## Main definitions

* `Stacks.Duality.ofOpSequenceCompIso`: a functor applied to an inverse sequence assembled from
  its successive maps is the sequence assembled from the images of those maps.
* `AlgebraicGeometry.truncGELECompιIsoSingleFunctor`: the one-degree truncation of a system in
  `D^b_{Coh}(𝒪_X)`, viewed in `D(𝒪_X)`, is `H^p` of the system placed in degree `p`.
* `AlgebraicGeometry.DeligneSystem.homologySystemIso`: `H^p` of the system of a Deligne system
  is `n ↦ H^p(𝓘^n𝓕^•)`.

## Main results

* `AlgebraicGeometry.DeligneSystem.nonempty_proIso_truncGELE_system`: the source presentation, a
  pro-isomorphism from the one-degree truncation system to `(𝓘^n H^p(𝓕^•))` in degree `p`.
* `AlgebraicGeometry.DeligneSystem.restrictionLifting_truncGELE_of_single_degree`: the core case
  of [Stacks, Tag 0G2H] for a one-degree truncation of the system, from the core case for the
  ideal powers of a coherent module.

## References

* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
* [Stacks Project, Tag 0G4R](https://stacks.math.columbia.edu/tag/0G4R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open InverseSequence
open CategoryTheory.Triangulated Opposite

attribute [local instance] CategoryTheory.uliftCategory
attribute [local instance] HasDerivedCategory.standard

universe v v' u u'

namespace Stacks.Duality

/-- **The transitions of the image of an inverse sequence under a functor.** The sequence
assembled from the images `H(f n)` of the successive maps has as its transition from level `m` to
level `n` the image under `H` of the transition of the original sequence. -/
public lemma tr_ofOpSequence_comp {𝒞 : Type u} [Category.{v} 𝒞] {𝒟 : Type u'} [Category.{v'} 𝒟]
    {Y : ℕ → 𝒞} (f : ∀ n : ℕ, Y (n + 1) ⟶ Y n) (H : 𝒞 ⥤ 𝒟) {m n : ℕ} (h : n ≤ m) :
    tr (Functor.ofOpSequence (X := fun k => H.obj (Y k)) (fun k => H.map (f k))) h =
      H.map (tr (Functor.ofOpSequence f) h) :=
  tr_ofOpSequence_eq _ (fun _ _ h => H.map (tr (Functor.ofOpSequence f) h))
    (fun _ => by rw [ProIso.tr_refl, H.map_id])
    (fun _ _ _ hkm hmn => by rw [← H.map_comp, ProIso.tr_trans _ hmn hkm])
    (fun n => by rw [tr, Functor.ofOpSequence_map_homOfLE_succ]; rfl) h

/-- **A functor applied to an inverse sequence assembled from its successive maps.** The sequence
assembled from the maps `f n`, followed by `H`, is isomorphic to the sequence assembled from the
maps `H(f n)`, by the isomorphism whose components are identities. -/
public def ofOpSequenceCompIso {𝒞 : Type u} [Category.{v} 𝒞] {𝒟 : Type u'} [Category.{v'} 𝒟]
    {Y : ℕ → 𝒞} (f : ∀ n : ℕ, Y (n + 1) ⟶ Y n) (H : 𝒞 ⥤ 𝒟) :
    Functor.ofOpSequence f ⋙ H ≅
      Functor.ofOpSequence (X := fun k => H.obj (Y k)) (fun k => H.map (f k)) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    rintro ⟨m⟩ ⟨n⟩ g
    have h : n ≤ m := leOfHom g.unop
    obtain rfl : g = (homOfLE h).op := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    exact (Category.comp_id _).trans
      ((tr_ofOpSequence_comp f H h).symm.trans (Category.id_comp _).symm))

end Stacks.Duality

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- **The one-degree truncation of a system in `D^b_{Coh}(𝒪_X)` is its cohomology placed in that
degree.** For a system `(G_n)` in `D^b_{Coh}(𝒪_X)`, the system `(τ^{≥p}τ^{≤p}G_n)` viewed in
`D(𝒪_X)` is the `singleFunctor` in degree `p` of the system `(H^p(G_n))`. -/
public def truncGELECompιIsoSingleFunctor (G : ℕᵒᵖ ⥤ BoundedCoherentDerived X) (p : ℤ) :
    (G ⋙ (boundedCoherentTStructure X).truncGELE p p) ⋙ (boundedCoherentDerived X).ι ≅
      ((G ⋙ (boundedCoherentDerived X).ι) ⋙ DerivedCategory.homologyFunctor X.Modules p) ⋙
        DerivedCategory.singleFunctor X.Modules p :=
  have e₁ : (G ⋙ (boundedCoherentTStructure X).truncGELE p p) ⋙ (boundedCoherentDerived X).ι ≅
      (G ⋙ (boundedCoherentDerived X).ι) ⋙
        (DerivedCategory.TStructure.t (C := X.Modules)).truncGELE p p :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft G ((boundedCoherentDerived X).ιTruncGELEIso
        DerivedCategory.TStructure.t p p) ≪≫
      (Functor.associator _ _ _).symm
  have e₃ : ((G ⋙ (boundedCoherentDerived X).ι) ⋙
        (DerivedCategory.TStructure.t (C := X.Modules)).truncGELE p p) ⋙
        DerivedCategory.homologyFunctor X.Modules p ≅
      (G ⋙ (boundedCoherentDerived X).ι) ⋙ DerivedCategory.homologyFunctor X.Modules p :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (G ⋙ (boundedCoherentDerived X).ι)
        (Stacks.TruncationLevel.truncGELECompHomologyIso p)
  e₁ ≪≫ DerivedCategory.isoCompSingleFunctorOfIsLEOfIsGE
      ((G ⋙ (boundedCoherentDerived X).ι) ⋙
        (DerivedCategory.TStructure.t (C := X.Modules)).truncGELE p p) p
      (fun _ => by dsimp; infer_instance) (fun _ => by dsimp; infer_instance) ≪≫
    Functor.isoWhiskerRight e₃ (DerivedCategory.singleFunctor X.Modules p)

namespace DeligneSystem

variable {U : Scheme.{u}} {j : U ⟶ X} [IsOpenImmersion j] [IsNoetherian X] (D : DeligneSystem j)

/-- **The cohomology of the system of a Deligne system is the cohomology of the ideal-power
subcomplexes.** `(H^p(K_n)) ≅ (H^p(𝓘^n𝓕^•))`, the right-hand side being
`Stacks.Duality.cohomologySystem`. -/
public def homologySystemIso (p : ℤ) :
    (D.system ⋙ (boundedCoherentDerived X).ι) ⋙ DerivedCategory.homologyFunctor X.Modules p ≅
      Stacks.Duality.cohomologySystem D.powers p :=
  Functor.isoWhiskerRight D.representation (DerivedCategory.homologyFunctor X.Modules p) ≪≫
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.homologyFunctorFactors X.Modules p) ≪≫
        Stacks.Duality.ofOpSequenceCompIso D.powers.transition
          (HomologicalComplex.homologyFunctor X.Modules (ComplexShape.up ℤ) p)

/-- **The source presentation of [Stacks, Tag 0G2H].** The one-degree truncation system
`(τ^{≥p}τ^{≤p}K_n)` of a Deligne system, viewed in `D(𝒪_X)`, is pro-isomorphic to the system
`(𝓘^n H^p(𝓕^•))` placed in cohomological degree `p`. -/
public theorem nonempty_proIso_truncGELE_system (p : ℤ) :
    Nonempty (ProIso ((D.system ⋙ (boundedCoherentTStructure X).truncGELE p p) ⋙
        (boundedCoherentDerived X).ι)
      (Stacks.Duality.idealPowerSystem D.idealSheaf (D.complex.homology p) ⋙
        DerivedCategory.singleFunctor X.Modules p)) := by
  refine (Stacks.Duality.cohomologyIdealPowersProIso_comp D.idealSheaf D.complex p
    D.isCoherent_complex D.powers (DerivedCategory.singleFunctor X.Modules p)).map fun e => ?_
  refine Pro.proIsoTrans (Pro.proIsoOfNatIso ?_) e
  exact truncGELECompιIsoSingleFunctor D.system p ≪≫
    Functor.isoWhiskerRight (D.homologySystemIso p) (DerivedCategory.singleFunctor X.Modules p)

/-- **The core case of [Stacks, Tag 0G2H] for a one-degree truncation of a Deligne system, from
the `Ext`-colimit statement for the ideal powers of a coherent module.** Let `L` be an object of
`D^b_{Coh}(𝒪_X)` concentrated in degree `q`. If for every coherent module `B` the system
`(𝓘^n H^p(𝓕^•))` placed in degree `p` has the restriction-lifting property against `B` placed in
degree `q`, then the one-degree truncation system `(τ^{≥p}τ^{≤p}K_n)` has the restriction-lifting
property against `L`. -/
public lemma restrictionLifting_truncGELE_of_single_degree (p q : ℤ)
    (L : BoundedCoherentDerived X)
    (hGE : (boundedCoherentTStructure X).IsGE L q)
    (hLE : (boundedCoherentTStructure X).IsLE L q)
    (hext : ∀ B : X.Modules, B.IsCoherent →
      RestrictionLifting
        (Stacks.Duality.idealPowerSystem D.idealSheaf (D.complex.homology p) ⋙
          DerivedCategory.singleFunctor X.Modules p)
        (Scheme.Modules.restrictFunctor j).mapDerivedCategory
        ((DerivedCategory.singleFunctor X.Modules q).obj B)) :
    RestrictionLifting (D.system ⋙ (boundedCoherentTStructure X).truncGELE p p)
      (restrictBoundedCoherent j) L := by
  obtain ⟨B, hB, ⟨eL⟩⟩ := exists_isCoherent_iso_singleFunctor_obj L q hGE hLE
  obtain ⟨eS⟩ := D.nonempty_proIso_truncGELE_system p
  exact restrictionLifting_of_singleFunctor_proIso j _ L p q _ B eS eL (hext B hB)

end DeligneSystem

end AlgebraicGeometry

end
