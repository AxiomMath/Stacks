module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.DenseOpen
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationMapHelpers
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricFieldChange.QuasiFiniteCodimensionOne
public import StacksFrontier.RingTheory.Henselian.Henselization.Existence
public import StacksFrontier.RingTheory.Henselian.PermanenceOfProperties
public import StacksFrontier.RingTheory.RegularLocalRing.Basic

/-!
# Restriction of finite étale covers across a regular boundary is fully faithful

Let `X` be a scheme whose underlying space is Noetherian and `U ⊆ X` a dense open such that the
local ring `𝒪_{X, x}` is regular at every point `x ∉ U`. Then restriction of finite étale covers
`FÉt_X ⟶ FÉt_U` is fully faithful.

This is [Stacks, Tag 0BQF] once its local hypothesis is checked: the punctured spectrum of a
strict henselization of a regular local ring `R` of positive dimension is connected. Indeed the
strict henselization `R^sh` is again regular ([Stacks, Tag 06LN]), hence a domain, of the same
positive dimension ([Stacks, Tag 06LK]); so its spectrum is irreducible and the punctured
spectrum is a nonempty open subset of it. A point outside the dense open `U` of a locally
Noetherian scheme is not a generic point of an irreducible component, so its local ring has
positive dimension.

## Main results

* `AlgebraicGeometry.isConnectedPuncturedStrictHenselization_of_isRegularLocalRing`: the local
  hypothesis of [Stacks, Tag 0BQF] for a regular local ring of positive dimension.
* `AlgebraicGeometry.nonempty_fullyFaithful_finiteEtaleBaseChange_inf_of_isRegularLocalRing`:
  for an affine open `A` of a locally Noetherian scheme `X` and a dense open `U ⊆ X` with regular
  local rings outside `U`, base change of finite étale covers from `A` to `U ∩ A` is fully
  faithful.

## References

* [Stacks Project, Tag 0BQF](https://stacks.math.columbia.edu/tag/0BQF)
* [Stacks Project, Tag 06LK](https://stacks.math.columbia.edu/tag/06LK)
* [Stacks Project, Tag 06LN](https://stacks.math.columbia.edu/tag/06LN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

/-- Base change of finite étale covers along an isomorphism is fully faithful. -/
noncomputable def finiteEtaleBaseChangeFullyFaithfulOfIsIso {X Y : Scheme.{u}} (i : X ⟶ Y)
    [IsIso i] : (finiteEtaleBaseChange i).FullyFaithful := by
  let a := (finiteEtaleBaseChangeComp (inv i) i (𝟙 Y) (IsIso.inv_hom_id i).symm).symm ≪≫
    finiteEtaleBaseChangeId
  let b := (finiteEtaleBaseChangeComp i (inv i) (𝟙 X) (IsIso.hom_inv_id i).symm).symm ≪≫
    finiteEtaleBaseChangeId
  have : (finiteEtaleBaseChange (inv i)).Faithful := b.faithful_of_comp
  exact Functor.FullyFaithful.ofCompFaithful ((Functor.FullyFaithful.id _).ofIso a.symm)

/-- Full faithfulness of base change of finite étale covers is invariant under precomposition
with an isomorphism. -/
theorem nonempty_fullyFaithful_finiteEtaleBaseChange_of_iso {T T' S : Scheme.{u}} (e : T ≅ T')
    (g : T' ⟶ S) (h : T ⟶ S) (hh : h = e.hom ≫ g)
    (H : Nonempty (finiteEtaleBaseChange g).FullyFaithful) :
    Nonempty (finiteEtaleBaseChange h).FullyFaithful :=
  ⟨((Classical.choice H).comp (finiteEtaleBaseChangeFullyFaithfulOfIsIso e.hom)).ofIso
    (finiteEtaleBaseChangeComp e.hom g h hh).symm⟩

/-- The punctured spectrum of a local domain of positive dimension is connected: the spectrum is
irreducible, the punctured spectrum is open in it, and it is nonempty because the generic point is
not the closed point. -/
private lemma isConnected_compl_closedPoint_of_isDomain (S : Type u) [CommRing S] [IsLocalRing S]
    [IsDomain S] (hdim : ringKrullDim S ≠ 0) :
    _root_.IsConnected ({closedPoint S}ᶜ : Set (PrimeSpectrum S)) := by
  have hne : (⊥ : Ideal S) ≠ maximalIdeal S := fun hbot ↦
    hdim (ringKrullDim_eq_zero_of_isField (IsLocalRing.isField_iff_maximalIdeal_eq.2 hbot.symm))
  have hopen : IsOpen ({closedPoint S}ᶜ : Set (PrimeSpectrum S)) :=
    ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2
      (IsLocalRing.maximalIdeal.isMaximal S)).isOpen_compl
  exact IsIrreducible.isConnected
    ⟨⟨⟨⊥, Ideal.isPrime_bot⟩, fun hη ↦ hne (congrArg PrimeSpectrum.asIdeal hη)⟩,
      (IrreducibleSpace.isIrreducible_univ _).2.open_subset hopen (Set.subset_univ _)⟩

/-- **The local hypothesis of [Stacks, Tag 0BQF] at a regular point.** The punctured spectrum of
every strict henselization of a regular local ring of positive dimension is connected: the
strict henselization is a regular local ring, hence a domain, of the same positive dimension. -/
theorem isConnectedPuncturedStrictHenselization_of_isRegularLocalRing (R : Type u)
    [CommRing R] [IsRegularLocalRing R] (hdim : ringKrullDim R ≠ 0) :
    IsConnectedPuncturedStrictHenselization R := by
  intro κsep _ _ _ Rsh _ _ _ h
  -- The residue field of `R` in its two spellings.
  let : Algebra (ResidueField R) κsep :=
    ((algebraMap (maximalIdeal R).ResidueField κsep).comp
      (algebraMap (ResidueField R) (maximalIdeal R).ResidueField)).toAlgebra
  have : IsScalarTower (ResidueField R) (maximalIdeal R).ResidueField κsep :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.IsSeparable (ResidueField R) (maximalIdeal R).ResidueField :=
    Algebra.IsSeparable.of_equiv_equiv (RingEquiv.refl (ResidueField R))
      (residueFieldEquivMaximalIdealResidueField R) (RingHom.ext fun _ ↦ rfl)
  have : Algebra.IsSeparable (maximalIdeal R).ResidueField κsep := IsSepClosure.separable
  have : IsSepClosure (ResidueField R) κsep :=
    ⟨IsSepClosure.sep_closed (maximalIdeal R).ResidueField,
      Algebra.IsSeparable.trans (ResidueField R) (maximalIdeal R).ResidueField κsep⟩
  -- The strict henselization in the sense of `IsLocalRing.IsHenselization`.
  have := h.isLocalHom
  have : IsLocalRing.IsHenselization R κsep Rsh := by
    refine ⟨h.henselian, h.isFilteredColimitEtale,
      h.residueFieldEquiv.trans (residueFieldEquivMaximalIdealResidueField Rsh).symm,
      fun x ↦ ?_⟩
    have hbase : algebraMap (ResidueField R) κsep (residue R x)
        = algebraMap (maximalIdeal R).ResidueField κsep
          (algebraMap R (maximalIdeal R).ResidueField x) := by
      rw [IsScalarTower.algebraMap_apply (ResidueField R) (maximalIdeal R).ResidueField κsep,
        algebraMap_residueField_residue]
    have hcomp : h.residueFieldEquiv (algebraMap (maximalIdeal R).ResidueField κsep
        (algebraMap R (maximalIdeal R).ResidueField x))
        = Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal Rsh) (algebraMap R Rsh)
            (IsLocalRing.maximalIdeal_comap (algebraMap R Rsh)).symm
            (algebraMap R (maximalIdeal R).ResidueField x) :=
      DFunLike.congr_fun h.residueFieldEquiv_comp
        (algebraMap R (maximalIdeal R).ResidueField x)
    have hlast : residueFieldEquivMaximalIdealResidueField Rsh
        (residue Rsh (algebraMap R Rsh x))
        = algebraMap Rsh (maximalIdeal Rsh).ResidueField (algebraMap R Rsh x) :=
      algebraMap_residueField_residue Rsh (algebraMap R Rsh x)
    change (residueFieldEquivMaximalIdealResidueField Rsh).symm
      (h.residueFieldEquiv (algebraMap (ResidueField R) κsep (residue R x)))
        = residue Rsh (algebraMap R Rsh x)
    rw [hbase, hcomp, Ideal.ResidueField.map_algebraMap, ← hlast,
      RingEquiv.symm_apply_apply]
  -- A henselization, needed to apply Stacks 06LN and 06LK.
  obtain ⟨Rh, _, _, _, _, hHen, hInd, _, hResBij⟩ := IsLocalRing.exists_henselization R
  have : IsLocalRing.IsHenselization R (ResidueField R) Rh :=
    IsLocalRing.IsHenselization.of_ind_etale hHen hInd
      ⟨RingEquiv.ofBijective (ResidueField.map (algebraMap R Rh)) hResBij, fun a ↦ by
        change ResidueField.map (algebraMap R Rh) (residue R a) = _
        rw [ResidueField.map_residue]⟩
  have : IsRegularLocalRing Rsh :=
    (isRegularLocalRing_iff_henselizations R Rh Rsh κsep).2.1 inferInstance
  have : IsDomain Rsh := IsRegularLocalRing.isDomain Rsh
  have hd := ringKrullDim_eq_henselization_eq_strictHenselization R Rh Rsh κsep
  exact isConnected_compl_closedPoint_of_isDomain Rsh (by rwa [← hd.2, ← hd.1])

/-- A point outside a dense open of a locally Noetherian scheme has a local ring of positive
dimension: a point whose local ring has dimension zero is a generic point of an irreducible
component, and those lie in every dense open. -/
theorem ringKrullDim_stalk_ne_zero_of_notMem_of_dense {X : Scheme.{u}} [IsLocallyNoetherian X]
    {U : X.Opens} (hU : Dense (U : Set X)) (x : X) (hx : x ∉ U) :
    ringKrullDim (X.presheaf.stalk x) ≠ 0 := fun hdim ↦
  hx (scheme_genericPoints_mem_dense_open X U.2 hU
    ((ringKrullDim_stalk_eq_zero_iff_mem_genericPoints X x).mp hdim))

/-- **Full faithfulness of restriction across a regular boundary, on an affine open.** Let `X` be
locally Noetherian, `U ⊆ X` a dense open with `𝒪_{X, x}` regular for every `x ∉ U`, and `A ⊆ X`
an affine open. Then base change of finite étale covers along `U ∩ A ⟶ A` is fully faithful. -/
theorem nonempty_fullyFaithful_finiteEtaleBaseChange_inf_of_isRegularLocalRing
    {X : Scheme.{u}} [IsLocallyNoetherian X] (U : X.Opens) (hU : Dense (U : Set X))
    (hreg : ∀ x : X, x ∉ U → IsRegularLocalRing (X.presheaf.stalk x)) (A : X.affineOpens) :
    Nonempty (finiteEtaleBaseChange (X.homOfLE (inf_le_right : U ⊓ A.1 ≤ A.1))).FullyFaithful := by
  let W : (A.1 : X.Opens).toScheme.Opens := A.1.ι ⁻¹ᵁ U
  have : IsAffine (A.1 : X.Opens).toScheme := A.2
  have : IsNoetherian (A.1 : X.Opens).toScheme := {}
  have hFF := fullyFaithful_finiteEtaleBaseChange_of_dense_of_noetherianSpace
    (A.1 : X.Opens).toScheme W (hU.preimage A.1.ι.isOpenEmbedding.isOpenMap) (fun y hy ↦ by
      have hy' : A.1.ι y ∉ U := hy
      let iso := (asIso (A.1.ι.stalkMap y)).commRingCatIsoToRingEquiv
      have := hreg _ hy'
      have : IsRegularLocalRing ((A.1 : X.Opens).toScheme.presheaf.stalk y) :=
        IsRegularLocalRing.of_ringEquiv iso
      refine isConnectedPuncturedStrictHenselization_of_isRegularLocalRing _ ?_
      rw [← ringKrullDim_eq_of_ringEquiv iso]
      exact ringKrullDim_stalk_ne_zero_of_notMem_of_dense hU _ hy')
  -- Identify `U ⊓ A` with the preimage of `U` in `A`.
  have hEq : U ⊓ A.1 = A.1.ι ''ᵁ W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm]
  let e : (U ⊓ A.1).toScheme ≅ W.toScheme := X.isoOfEq hEq ≪≫ (A.1.ι.isoImage W).symm
  refine nonempty_fullyFaithful_finiteEtaleBaseChange_of_iso e W.ι _ ?_ hFF
  apply (cancel_mono A.1.ι).1
  simp only [Category.assoc, Scheme.homOfLE_ι, e, Iso.trans_hom, Iso.symm_hom,
    Scheme.Hom.isoImage_inv_ι, Scheme.isoOfEq_hom_ι]

end AlgebraicGeometry

end
