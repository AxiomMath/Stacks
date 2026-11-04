module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedUnitOfResolution
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringCohomologicalDescent

/-!
# When the direct image along an augmentation already computes the derived direct image

Let `S` be a simplicial-site situation (Stacks 09WE) and `a` an augmentation of `S` towards a
site `(D, K)` (Stacks 0D6Z). The canonical comparison `a_*L ⟶ R a_*L` of
`StacksFrontier/CategoryTheory/Sites/Simplicial/HypercoveringCohomologicalDescent.lean` is
invertible at a complex `L` of abelian sheaves on the total site as soon as *one* K-injective
resolution `q : L ⟶ J` of `L` has `a_*q` a quasi-isomorphism. That is the content of this module:
it turns the derived-functor statement `a_*L = R a_*L` into the statement that `a_*` inverts one
chosen resolution, which is a statement about complexes.

Nothing is assumed of `L`, and nothing beyond the augmentation is assumed of the situation: the
comparison is invertible at K-injective complexes with no hypothesis at all, which is
Stacks 070K, and the naturality square of the comparison transports that along the resolution.

## Main results

* `CategoryTheory.SimplicialSiteSituation.Augmentation.exists_kInjective_resolution_total`: every
  complex of abelian sheaves on the total site admits a quasi-isomorphism into a K-injective one.
* `CategoryTheory.SimplicialSiteSituation.Augmentation`
  `.isIso_homotopyTotalPushforward_map_of_quasiIso`: the degreewise direct image followed by
  localization inverts the class of a morphism of complexes whose direct image is a
  quasi-isomorphism.
* `CategoryTheory.SimplicialSiteSituation.Augmentation`
  `.isIso_derivedTotalPushforwardUnit_app_of_quasiIso`: the criterion.
* `CategoryTheory.SimplicialSiteSituation.Augmentation`
  `.inverseImageComputesDerivedPushforward_of_quasiIso`: its instance at the inverse images of
  K-injective complexes, which is the predicate
  `CategoryTheory.SimplicialSiteSituation.Augmentation.InverseImageComputesDerivedPushforward`.
* `CategoryTheory.SimplicialSiteSituation.Augmentation`
  `.isIso_homotopyTotalPushforward_map_of_isIso_derivedTotalPushforwardUnit_app`: the converse of
  the criterion, which is what lets the predicate be read off one spelling of `a_*` and used for
  another.
* `CategoryTheory.SimplicialSiteSituation.Augmentation`
  `.isIso_homotopyTotalPushforward_map_of_inverseImageComputesDerivedPushforward`: the predicate
  itself read that way, at one K-injective resolution of `a⁻¹I`.

## Implementation notes

The general statement behind the criterion is
`CategoryTheory.Functor.isIso_rightDerivedUnit_app_of_quasiIso`, about an arbitrary right derived
functor; it is applied here with the degreewise direct image followed by localization as the
functor. The only step specific to the augmentation is the identification of the image of the
class of `q` under that functor with the class of `a_*q`, which is
`CategoryTheory.Functor.mapHomotopyCategory_map`.

The three inputs of the criterion — the existence of K-injective resolutions on the total site,
that identification, and the general statement — are three separate declarations rather than
three steps of one proof. Each of them is near the per-declaration elaboration budget on its own,
because the construction of `R a_*` is an unfolded chain of abbreviations and its
right-derived-functor instance is re-synthesized wherever it appears.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.SimplicialSiteSituation.Augmentation

attribute [local instance] HasDerivedCategory.standard

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K)

/-- **Every complex of abelian sheaves on the total site admits a K-injective resolution.**
Abelian sheaves on a site are a Grothendieck abelian category. -/
theorem exists_kInjective_resolution_total :
    ∀ X : CochainComplex (Sheaf S.totalTopology AddCommGrpCat.{u}) ℤ,
      ∃ (I : CochainComplex (Sheaf S.totalTopology AddCommGrpCat.{u}) ℤ) (f : X ⟶ I),
        I.IsKInjective ∧ QuasiIso f :=
  Stacks.Cohomology.Localization.enoughKInjectives

/-- The localization functor `Qh` inverts the class of a quasi-isomorphism. -/
private theorem isIso_Qh_map_quotient_map_of_quasiIso {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] {X Y : CochainComplex C ℤ} (f : X ⟶ Y)
    (hf : QuasiIso f) :
    IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f)) := by
  apply Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
  rwa [HomotopyCategory.quotient_map_mem_quasiIso_iff]

/-- The degreewise direct image followed by localization inverts the class of a morphism of
complexes of abelian sheaves on the total site whose direct image is a quasi-isomorphism. -/
theorem isIso_homotopyTotalPushforward_map_of_quasiIso
    {L J : CochainComplex (Sheaf S.totalTopology AddCommGrpCat.{u}) ℤ} (q : L ⟶ J)
    (hpush : QuasiIso (((abelianTotalPushforward S D K a).mapHomologicalComplex
      (ComplexShape.up ℤ)).map q)) :
    IsIso ((homotopyTotalPushforward S D K a).map
      ((HomotopyCategory.quotient (Sheaf S.totalTopology AddCommGrpCat.{u})
        (ComplexShape.up ℤ)).map q)) := by
  rw [Functor.comp_map, Functor.mapHomotopyCategory_map]
  exact isIso_Qh_map_quotient_map_of_quasiIso _ hpush

/-- **One resolution suffices.** The comparison `a_*L ⟶ R a_*L` is invertible at a complex `L` of
abelian sheaves on the total site as soon as some quasi-isomorphism `q : L ⟶ J` into a
K-injective complex has `a_*q` a quasi-isomorphism. -/
theorem isIso_derivedTotalPushforwardUnit_app_of_quasiIso
    {L J : CochainComplex (Sheaf S.totalTopology AddCommGrpCat.{u}) ℤ} (hJ : J.IsKInjective)
    (q : L ⟶ J) (hq : QuasiIso q)
    (hF : IsIso ((homotopyTotalPushforward S D K a).map
      ((HomotopyCategory.quotient (Sheaf S.totalTopology AddCommGrpCat.{u})
        (ComplexShape.up ℤ)).map q))) :
    IsIso ((derivedTotalPushforwardUnit S D K a).app
      ((HomotopyCategory.quotient (Sheaf S.totalTopology AddCommGrpCat.{u})
        (ComplexShape.up ℤ)).obj L)) :=
  Functor.isIso_rightDerivedUnit_app_of_quasiIso (homotopyTotalPushforward S D K a)
    (exists_kInjective_resolution_total S) DerivedCategory.Qh
    (derivedTotalPushforward S D K a) (derivedTotalPushforwardUnit S D K a) hJ q hq hF

/-- **The predicate `InverseImageComputesDerivedPushforward` from one resolution per K-injective
complex**: it is enough that, for every K-injective complex `I` of abelian sheaves on `(D, K)`,
some K-injective resolution of `a⁻¹I` is sent by `a_*` to a quasi-isomorphism. -/
theorem inverseImageComputesDerivedPushforward_of_quasiIso
    (h : ∀ I : CochainComplex (Sheaf K AddCommGrpCat.{u}) ℤ, I.IsKInjective →
      ∃ (J : CochainComplex (Sheaf S.totalTopology AddCommGrpCat.{u}) ℤ) (_ : J.IsKInjective)
        (q : ((totalInverseImageAb S D K a).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ J),
        QuasiIso q ∧ QuasiIso (((abelianTotalPushforward S D K a).mapHomologicalComplex
          (ComplexShape.up ℤ)).map q)) :
    InverseImageComputesDerivedPushforward S D K a := by
  intro I hI
  obtain ⟨J, hJ, q, hq, hpush⟩ := h I hI
  exact isIso_derivedTotalPushforwardUnit_app_of_quasiIso S D K a hJ q hq
    (isIso_homotopyTotalPushforward_map_of_quasiIso S D K a q hpush)

/-- **The converse of the criterion**: if the comparison `a_*L ⟶ R a_*L` is invertible at a
complex `L` of abelian sheaves on the total site, then the degreewise direct image followed by
localization inverts every quasi-isomorphism `q : L ⟶ J` into a K-injective complex.

Taken with `isIso_derivedTotalPushforwardUnit_app_of_quasiIso` this says that, for one chosen
resolution, `a_*L = R a_*L` and invertibility of `a_*q` are the same condition. The second is a
condition on the functor `a_*` at one morphism, so it transports along an isomorphism of `a_*`;
the first mentions `R a_*` and its comparison and does not. That is what makes
`InverseImageComputesDerivedPushforward` usable for another spelling of the same direct image.

The proof is the naturality square of the comparison at the class of `q`, the same square as in
the criterion, read in the other direction: the right edge is the comparison at the K-injective
complex `J` and the lower edge is invertible because the localization inverts `q`, so the two
horizontal edges are invertible together. It is spelled out rather than obtained from
`CategoryTheory.Functor.isIso_map_of_isIso_rightDerivedUnit_app` because feeding the general
statement an invertibility hypothesis at `R a_*` exceeds the per-declaration elaboration
budget. -/
theorem isIso_homotopyTotalPushforward_map_of_isIso_derivedTotalPushforwardUnit_app
    {L J : CochainComplex (Sheaf S.totalTopology AddCommGrpCat.{u}) ℤ} (hJ : J.IsKInjective)
    (q : L ⟶ J) (hq : QuasiIso q)
    (hL : IsIso ((derivedTotalPushforwardUnit S D K a).app
      ((HomotopyCategory.quotient (Sheaf S.totalTopology AddCommGrpCat.{u})
        (ComplexShape.up ℤ)).obj L))) :
    IsIso ((homotopyTotalPushforward S D K a).map
      ((HomotopyCategory.quotient (Sheaf S.totalTopology AddCommGrpCat.{u})
        (ComplexShape.up ℤ)).map q)) := by
  have _ := hJ
  have hαJ : IsIso ((derivedTotalPushforwardUnit S D K a).app
      ((HomotopyCategory.quotient (Sheaf S.totalTopology AddCommGrpCat.{u})
        (ComplexShape.up ℤ)).obj J)) :=
    Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective
      (homotopyTotalPushforward S D K a) (derivedTotalPushforward S D K a)
      (derivedTotalPushforwardUnit S D K a) J
  have hQh := isIso_Qh_map_quotient_map_of_quasiIso q hq
  have hcomp : IsIso ((homotopyTotalPushforward S D K a).map
      ((HomotopyCategory.quotient (Sheaf S.totalTopology AddCommGrpCat.{u})
        (ComplexShape.up ℤ)).map q) ≫
      (derivedTotalPushforwardUnit S D K a).app
        ((HomotopyCategory.quotient (Sheaf S.totalTopology AddCommGrpCat.{u})
          (ComplexShape.up ℤ)).obj J)) := by
    rw [(derivedTotalPushforwardUnit S D K a).naturality
      ((HomotopyCategory.quotient (Sheaf S.totalTopology AddCommGrpCat.{u})
        (ComplexShape.up ℤ)).map q)]
    have _ := hL
    have : IsIso ((DerivedCategory.Qh ⋙ derivedTotalPushforward S D K a).map
        ((HomotopyCategory.quotient (Sheaf S.totalTopology AddCommGrpCat.{u})
          (ComplexShape.up ℤ)).map q)) := by
      rw [Functor.comp_map]
      have _ := hQh
      infer_instance
    infer_instance
  have _ := hαJ
  have _ := hcomp
  exact IsIso.of_isIso_comp_right ((homotopyTotalPushforward S D K a).map
      ((HomotopyCategory.quotient (Sheaf S.totalTopology AddCommGrpCat.{u})
        (ComplexShape.up ℤ)).map q))
    ((derivedTotalPushforwardUnit S D K a).app
      ((HomotopyCategory.quotient (Sheaf S.totalTopology AddCommGrpCat.{u})
        (ComplexShape.up ℤ)).obj J))

/-- **The predicate `InverseImageComputesDerivedPushforward`, read as a statement about one
K-injective resolution.** If `a⁻¹` of a K-injective complex is computed by `a_*`, then `a_*`
inverts, after localization, every quasi-isomorphism of the complex `a⁻¹I` into a K-injective
complex.

This is the form in which the predicate can be transported to another spelling of `a_*`: the
conclusion mentions neither `R a_*` nor its comparison. The passage from the class of the complex
`a⁻¹I` to the inverse image of the class of `I` — the same object of the homotopy category — is
`CategoryTheory.Functor.mapHomotopyCategoryFactors`. -/
theorem isIso_homotopyTotalPushforward_map_of_inverseImageComputesDerivedPushforward
    (h : InverseImageComputesDerivedPushforward S D K a)
    (I : CochainComplex (Sheaf K AddCommGrpCat.{u}) ℤ) (hI : I.IsKInjective)
    {Jc : CochainComplex (Sheaf S.totalTopology AddCommGrpCat.{u}) ℤ} (hJc : Jc.IsKInjective)
    (q : ((totalInverseImageAb S D K a).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ Jc)
    (hq : QuasiIso q) :
    IsIso ((homotopyTotalPushforward S D K a).map
      ((HomotopyCategory.quotient (Sheaf S.totalTopology AddCommGrpCat.{u})
        (ComplexShape.up ℤ)).map q)) :=
  isIso_homotopyTotalPushforward_map_of_isIso_derivedTotalPushforwardUnit_app S D K a hJc q hq
    ((NatTrans.isIso_app_iff_of_iso (derivedTotalPushforwardUnit S D K a)
      ((Functor.mapHomotopyCategoryFactors (totalInverseImageAb S D K a)
        (ComplexShape.up ℤ)).app I)).mp (h I hI))

end CategoryTheory.SimplicialSiteSituation.Augmentation

end
