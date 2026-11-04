module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.ExtendAtCodimensionOne
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.ExtendFromLocalExtensions
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.GlueFiniteEtaleAffine
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.RegularBoundaryFullyFaithful
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.RegularPurity
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Extending a cover unramified in codimension one across a regular boundary

Let `X` be a locally Noetherian scheme, `U ⊆ X` a dense open and `Y → U` finite étale. If `Y` is
unramified over `X` in codimension one and the local ring `𝒪_{X, x}` is regular at every point
`x` outside `U`, then `Y` is the restriction of a finite étale cover of `X`. This is
[Stacks, Tag 0H2W].

## Main results

* `AlgebraicGeometry.exists_finiteEtale_extension_of_isUnramifiedInCodimensionOne`:
  [Stacks, Tag 0H2W].

## Implementation notes

The proof has a local and a global part.

Locally, on an affine open `A`, the cover is extended by Noetherian induction on the open over
which it is already extended (`exists_finiteEtale_extension_of_forall_extends`). At a point
`x ∈ A` of least dimension outside the current open `V`, the local scheme `Spec 𝒪_{X, x}` meets
`V` in its punctured spectrum, and the restriction of the cover there extends over
`Spec 𝒪_{X, x}`:

* if `dim 𝒪_{X, x} ≥ 2`, by purity for the regular local ring `𝒪_{X, x}`
  (`hasPurity_of_isRegularLocalRing`, [Stacks, Tag 0BMA]);
* if `dim 𝒪_{X, x} = 1`, because the cover is unramified at `x`: the integral closure of the
  discrete valuation ring `𝒪_{X, x}` in the generic fibre is finite étale
  (`exists_finiteEtale_extension_stalk_of_isUnramifiedInCodimensionOne`). In that case the
  punctured spectrum is the generic point, which lies in `U`, so the extended cover may be
  replaced by the original one there (`nonempty_iso_restrict_iff_of_preimage_eq`).

The extension then spreads out over a neighbourhood of `x` by [Stacks, Tag 0BQ5] and
[Stacks, Tag 0EY3] (`exists_finiteEtale_extension_neighborhood_of_extends`). A point outside
the dense open `U` has local ring of positive dimension, so the two cases are exhaustive.

Globally, the extensions over the affine opens are unique up to unique isomorphism, because
restriction of finite étale covers across the regular boundary is fully faithful
(`nonempty_fullyFaithful_finiteEtaleBaseChange_inf_of_isRegularLocalRing`,
[Stacks, Tag 0BQF]), and so they glue (`exists_finiteEtale_extension_of_affine_extensions`).
This is what lets `X` be only locally Noetherian.

## References

* [Stacks Project, Lemma 58.31.2 (0H2W)](https://stacks.math.columbia.edu/tag/0H2W)
* [Stacks Project, Lemma 58.21.3 (0BMA)](https://stacks.math.columbia.edu/tag/0BMA)
* [Stacks Project, Lemma 58.21.6 (0EY7)](https://stacks.math.columbia.edu/tag/0EY7)
* [Stacks Project, Lemma 58.12.2 (0BQF)](https://stacks.math.columbia.edu/tag/0BQF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- At a point `x ∉ O` whose local ring has dimension one, the preimage of the open `O` in
`Spec 𝒪_{X, x}` is the punctured spectrum as soon as `O` contains the generic points of the
irreducible components of `X` through `x`: the proper generizations of `x` are such generic
points. -/
theorem preimage_fromSpecStalk_eq_puncturedSpectrum_of_ringKrullDim_eq_one {X : Scheme.{u}}
    [IsLocallyNoetherian X] (O : X.Opens) (x : X) (hxO : x ∉ O)
    (hdim : ringKrullDim (X.presheaf.stalk x) = 1)
    (hgen : ∀ z : X, z ⤳ x → z ∈ genericPoints X → z ∈ O) :
    (X.fromSpecStalk x) ⁻¹ᵁ O = Stacks.puncturedSpectrum (X.presheaf.stalk x) := by
  ext y
  refine ⟨fun hy hclosed ↦ ?_, fun hy ↦ ?_⟩
  · have hyO : X.fromSpecStalk x y ∈ O := hy
    rw [show y = IsLocalRing.closedPoint (X.presheaf.stalk x) from hclosed,
      Scheme.fromSpecStalk_closedPoint] at hyO
    exact hxO hyO
  · have hspec : X.fromSpecStalk x y ⤳ x := by
      have hmem : X.fromSpecStalk x y ∈ Set.range (X.fromSpecStalk x) := ⟨y, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at hmem
    have hne : X.fromSpecStalk x y ≠ x := by
      intro heq
      apply hy
      apply (X.fromSpecStalk x).isEmbedding.injective
      rw [heq, Scheme.fromSpecStalk_closedPoint]
    have hlt : x < X.fromSpecStalk x y :=
      lt_of_le_not_ge (hspec : x ≤ _) fun h ↦ hne (hspec.antisymm h).eq
    have hx1 : Order.coheight x = 1 := by
      have h := ringKrullDim_stalk_eq_coheight x
      rw [hdim] at h
      exact_mod_cast h.symm
    have hfin : Order.coheight (X.fromSpecStalk x y) < ⊤ := by
      have hlt' : ringKrullDim (X.presheaf.stalk (X.fromSpecStalk x y)) < ⊤ :=
        ringKrullDim_lt_top
      rw [ringKrullDim_stalk_eq_coheight] at hlt'
      exact WithBot.coe_lt_coe.mp (by simpa using hlt')
    have h0 : Order.coheight (X.fromSpecStalk x y) = 0 :=
      Order.lt_one_iff.mp (hx1 ▸ Order.coheight_strictAnti hlt hfin)
    have hgp : X.fromSpecStalk x y ∈ genericPoints X := by
      rw [← ringKrullDim_stalk_eq_zero_iff_mem_genericPoints, ringKrullDim_stalk_eq_coheight,
        h0]
      rfl
    exact hgen _ hspec hgp

/-- **Purity extends the restriction to a punctured spectrum.** If purity holds for `𝒪_{X, x}`
and the preimage of the open `V` in `Spec 𝒪_{X, x}` is the punctured spectrum, then the
restriction there of any finite étale cover of `V` extends over `Spec 𝒪_{X, x}`. -/
theorem exists_finiteEtale_extension_stalk_of_hasPurity {X : Scheme.{u}} (V : X.Opens) (x : X)
    (hpre : (X.fromSpecStalk x) ⁻¹ᵁ V = Stacks.puncturedSpectrum (X.presheaf.stalk x))
    (hpur : HasPurity (X.presheaf.stalk x)) (F : FiniteEtaleOver V.toScheme) :
    ∃ L : FiniteEtaleOver (Spec (X.presheaf.stalk x)),
      Nonempty ((finiteEtaleBaseChange ((X.fromSpecStalk x) ⁻¹ᵁ V).ι).obj L ≅
        (finiteEtaleBaseChange ((X.fromSpecStalk x) ∣_ V)).obj F) := by
  let e := (Spec (X.presheaf.stalk x)).isoOfEq hpre
  let G := (finiteEtaleBaseChange e.inv).obj
    ((finiteEtaleBaseChange ((X.fromSpecStalk x) ∣_ V)).obj F)
  obtain ⟨L, ⟨i⟩⟩ := hpur.mem_essImage G
  exact ⟨L, ⟨(finiteEtaleBaseChangeComp e.hom _ _ (Scheme.isoOfEq_hom_ι _ hpre).symm).app L ≪≫
    (finiteEtaleBaseChange e.hom).mapIso i ≪≫
    ((finiteEtaleBaseChangeComp e.hom e.inv (𝟙 _) e.hom_inv_id.symm).app _).symm ≪≫
    finiteEtaleBaseChangeId.app _⟩⟩

/-- **Extension over an affine open.** Under the hypotheses of [Stacks, Tag 0H2W], for every
affine open `A ⊆ X` the restriction of the cover to `U ∩ A` extends to a finite étale cover of
`A`. -/
theorem exists_finiteEtale_extension_inf_affineOpen_of_isUnramifiedInCodimensionOne
    {X : Scheme.{u}} [IsLocallyNoetherian X] (U : X.Opens) (hdense : DenseRange U.ι.base)
    {Y : Scheme.{u}} (f : Y ⟶ U) [IsFinite f] [Etale f]
    (hunr : Stacks.FundamentalGroup.IsUnramifiedInCodimensionOne U.ι f)
    (hreg : ∀ x : X, x ∉ U → IsRegularLocalRing (X.presheaf.stalk x)) (A : X.affineOpens) :
    ∃ F : FiniteEtaleOver (A : X.Opens).toScheme,
      Nonempty ((finiteEtaleBaseChange (X.homOfLE (inf_le_right : U ⊓ A.1 ≤ A.1))).obj F ≅
        (finiteEtaleBaseChange (X.homOfLE (inf_le_left : U ⊓ A.1 ≤ U))).obj
          (MorphismProperty.Over.mk (P := finiteEtale) (Q := ⊤) f ⟨‹_›, ‹_›⟩)) := by
  let E : FiniteEtaleOver U.toScheme :=
    MorphismProperty.Over.mk (P := finiteEtale) (Q := ⊤) f ⟨‹_›, ‹_›⟩
  have hU : Dense (U : Set X) := by rwa [DenseRange, Scheme.Opens.range_ι] at hdense
  refine exists_finiteEtale_extension_of_forall_extends A.1 A.2.isCompact (U ⊓ A.1)
    inf_le_right ((finiteEtaleBaseChange (X.homOfLE inf_le_left)).obj E) ?_
  intro V hUV F hF x hxA hxV hpre
  obtain ⟨iF⟩ := hF
  have hxU : x ∉ U := fun hx ↦ hxV (hUV ⟨hx, hxA⟩)
  have := hreg x hxU
  have hd0 := ringKrullDim_stalk_ne_zero_of_notMem_of_dense hU x hxU
  by_cases hd1 : ringKrullDim (X.presheaf.stalk x) = 1
  · -- Codimension one: the punctured spectrum is the generic point, which lies in `U`.
    obtain ⟨L, hL⟩ :=
      exists_finiteEtale_extension_stalk_of_isUnramifiedInCodimensionOne U hdense f hunr x hxU
        hd1
    have hgenUA : ∀ z : X, z ⤳ x → z ∈ genericPoints X → z ∈ U ⊓ A.1 := fun z hz hgz ↦
      ⟨scheme_genericPoints_mem_dense_open X U.2 hU hgz, hz.mem_open A.1.2 hxA⟩
    have hpUA := preimage_fromSpecStalk_eq_puncturedSpectrum_of_ringKrullDim_eq_one (U ⊓ A.1) x
      (fun h ↦ hxU h.1) hd1 hgenUA
    have hpU := preimage_fromSpecStalk_eq_puncturedSpectrum_of_ringKrullDim_eq_one U x hxU hd1
      fun z hz hgz ↦ (hgenUA z hz hgz).1
    obtain ⟨i₁⟩ := (nonempty_iso_restrict_iff_of_preimage_eq (inf_le_left : U ⊓ A.1 ≤ U) x
      (hpUA.trans hpU.symm) E L).1 hL
    refine ⟨L, (nonempty_iso_restrict_iff_of_preimage_eq hUV x (hpUA.trans hpre.symm) F L).2
      ⟨i₁ ≪≫ (finiteEtaleBaseChange ((X.fromSpecStalk x) ∣_ (U ⊓ A.1))).mapIso iF.symm⟩⟩
  · -- Dimension at least two: purity.
    have hd2 : (2 : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x) := by
      have hnn : (0 : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x) :=
        ringKrullDim_nonneg_of_nontrivial
      have hle1 : (1 : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x) := by
        simpa using (ENat.WithBot.add_one_le_iff (n := 0)).mpr
          (lt_of_le_of_ne hnn (Ne.symm hd0))
      rw [show (2 : WithBot ℕ∞) = 1 + 1 from rfl]
      simpa using (ENat.WithBot.add_one_le_iff (n := 1)).mpr
        (lt_of_le_of_ne hle1 (Ne.symm hd1))
    exact exists_finiteEtale_extension_stalk_of_hasPurity V x hpre
      (hasPurity_of_isRegularLocalRing _ hd2) F

/-- **Stacks Project, Tag 0H2W.** Let `X` be a locally Noetherian scheme, `U ⊆ X` a dense open
and `f : Y ⟶ U` finite étale. If `Y` is unramified over `X` in codimension one and `𝒪_{X, x}` is
regular for every `x` outside `U`, then `f` is the restriction of a finite étale cover of `X`:
there is a finite étale `p : Y' ⟶ X` and an isomorphism `Y' ×_X U ≅ Y` over `U`. -/
@[stacks 0H2W "a finite étale cover unramified in codimension one extends across a regular \
complement", sga "1 X 3.3" "partial", sga "2 XIV 1.11" "Regular case"]
public theorem exists_finiteEtale_extension_of_isUnramifiedInCodimensionOne
    {X : Scheme.{u}} [IsLocallyNoetherian X] (U : X.Opens) (hdense : DenseRange U.ι.base)
    {Y : Scheme.{u}} (f : Y ⟶ U) [IsFinite f] [Etale f]
    (hunr : Stacks.FundamentalGroup.IsUnramifiedInCodimensionOne U.ι f)
    (hreg : ∀ x : X, x ∉ U → IsRegularLocalRing (X.presheaf.stalk x)) :
    ∃ (Y' : Scheme.{u}) (p : Y' ⟶ X), IsFinite p ∧ Etale p ∧
      ∃ e : pullback p U.ι ≅ Y, e.hom ≫ f = pullback.snd p U.ι := by
  have hU : Dense (U : Set X) := by rwa [DenseRange, Scheme.Opens.range_ι] at hdense
  obtain ⟨F, ⟨i⟩⟩ := exists_finiteEtale_extension_of_affine_extensions U
    (MorphismProperty.Over.mk (P := finiteEtale) (Q := ⊤) f ⟨‹_›, ‹_›⟩)
    (exists_finiteEtale_extension_inf_affineOpen_of_isUnramifiedInCodimensionOne U hdense f
      hunr hreg)
    (nonempty_fullyFaithful_finiteEtaleBaseChange_inf_of_isRegularLocalRing U hU hreg)
  exact ⟨F.left, F.hom, F.prop.1, F.prop.2,
    (Over.forget U.toScheme).mapIso
      ((MorphismProperty.Over.forget finiteEtale ⊤ U.toScheme).mapIso i),
    MorphismProperty.Over.w i.hom⟩

end AlgebraicGeometry

end
