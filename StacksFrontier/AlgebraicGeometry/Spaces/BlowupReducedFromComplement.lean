module

public import StacksFrontier.AlgebraicGeometry.CartierAffineLocal.Basic
public import StacksFrontier.AlgebraicGeometry.CartierComplementDense.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupSeparation
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupIsomorphismOffCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierComplement

/-!
# The blowup of a reduced algebraic space is reduced

Let `S` be a scheme, let `X` be an algebraic space over `S`, let `Z ⊆ X` be a closed subspace and
let `b : X' ⟶ X` be the blowup of `X` in `Z`. If `X` is reduced, so is `X'`.

## Main results

* `AlgebraicGeometry.Space.isReduced_of_isEffectiveCartierDivisor_of_isReduced_compl`: a scheme
  is reduced as soon as the open complement of an effective Cartier divisor on it is reduced.
* `AlgebraicGeometry.Space.hasEtaleLocalProperty_isReduced_of_isEffectiveCartierDivisor`: the
  same for an algebraic space and an effective Cartier divisor on it.
* `AlgebraicGeometry.Space.hasEtaleLocalProperty_isReduced_of_isEtale`: reducedness passes from
  the target of an étale morphism of algebraic spaces to its source.
* `AlgebraicGeometry.Space.hasEtaleLocalProperty_isReduced_of_isBlowupAlong'`: the blowup of a
  reduced algebraic space in a closed subspace is reduced.

## Implementation notes

The source reads reducedness of the blowup off its construction as a relative `Proj`. The proof
here uses only the universal property of the blowup, through two of its consequences: the
exceptional divisor `E = b⁻¹(Z)` is an effective Cartier divisor (Stacks 085T, part (2)), and
`b` is an isomorphism over `X ∖ Z` (Stacks 085T, part (1)). So the complement `X' ∖ E` is
isomorphic to the open subspace `X ∖ Z` of `X`, hence reduced, and the following observation
finishes the proof: on an affine open `Spec(A)` of an étale scheme chart of `X'` on which `E` is
cut out by a nonzerodivisor `f`, the ring `A` injects into `A_f`, which is a ring of sections of
the reduced complement, so `A` is reduced.

No identification of the blowup of a scheme chart, taken among algebraic spaces, with the scheme
blowup is needed, which is why this statement carries no hypothesis besides reducedness of `X`,
in contrast with `AlgebraicGeometry.Space.isReduced_of_isBlowupAlong`.

## References

* [Stacks Project, Tag 085W](https://stacks.math.columbia.edu/tag/085W)
* [Stacks Project, Tag 085T](https://stacks.math.columbia.edu/tag/085T)
* [Stacks Project, Tag 07ZU](https://stacks.math.columbia.edu/tag/07ZU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

/-- **A scheme is reduced as soon as the complement of an effective Cartier divisor on it is
reduced.** Around every point the divisor is cut out on an affine open `Spec(A)` by a
nonzerodivisor `f`; then `A` injects into the sections of the complement over `Spec(A)`, which
form a reduced ring, so `A` and its localizations, the stalks, are reduced. -/
theorem isReduced_of_isEffectiveCartierDivisor_of_isReduced_compl {T : Scheme.{u}}
    (I : T.IdealSheafData) (hI : Stacks.Divisors.IsEffectiveCartierDivisor I)
    (hU : IsReduced (Scheme.Opens.toScheme (X := T) I.support.compl)) : IsReduced T := by
  set U : T.Opens := I.support.compl
  have key : ∀ t : T, ∃ A : T.affineOpens, t ∈ (A : Set T) ∧ _root_.IsReduced Γ(T, A.1) := by
    intro t
    obtain ⟨A, htA, f, hf, hgen⟩ := Stacks.CartierAffineLocal.exists_affineOpen_isRegular I hI t
    refine ⟨A, htA, ?_⟩
    have hinj :=
      Stacks.AlgebraicGeometry.CartierComplementDense.injective_res_of_affine_nonZeroDivisor
        I A f (isRegular_iff_mem_nonZeroDivisors.mp hf) hgen
    have he : U.ι ''ᵁ (U.ι ⁻¹ᵁ (A.1 ⊓ U)) = A.1 ⊓ U := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact inf_eq_right.2 inf_le_right
    have hinj' := Stacks.AlgebraicGeometry.CartierComplementDense.injective_res_of_le
      (he.le.trans inf_le_left) he.ge hinj
    have hred : _root_.IsReduced Γ(U.toScheme, U.ι ⁻¹ᵁ (A.1 ⊓ U)) := inferInstance
    have : _root_.IsReduced Γ(T, U.ι ''ᵁ (U.ι ⁻¹ᵁ (A.1 ⊓ U))) := hred
    exact isReduced_of_injective _ hinj'
  have hstalk : ∀ t : T, _root_.IsReduced (T.presheaf.stalk t) := by
    intro t
    obtain ⟨A, htA, hA⟩ := key t
    have : IsReduced A.1.toScheme := isReduced_of_isOpenImmersion A.2.isoSpec.hom
    have := isReduced_stalk_of_isReduced A.1.toScheme ⟨t, htA⟩
    exact isReduced_of_injective _
      (A.1.stalkIso ⟨t, htA⟩).symm.commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isReduced_stalk T

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Reducedness passes from the target of an étale morphism of algebraic spaces to its
source**: an étale scheme chart of the source composes to an étale scheme chart of the
target. -/
theorem hasEtaleLocalProperty_isReduced_of_isEtale {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G)
    (hf : IsEtale B S hS f)
    (hred : HasEtaleLocalProperty B S hS G (fun T : Scheme.{u} => IsReduced T)) :
    HasEtaleLocalProperty B S hS F (fun T : Scheme.{u} => IsReduced T) :=
  (exists_atlas_iff_forall_etale B S hS F (fun T : Scheme.{u} => IsReduced T) hF).mpr
    fun V g hg => (exists_atlas_iff_forall_etale B S hS G (fun T : Scheme.{u} => IsReduced T)
      hG).mp hred V (g ≫ f) (presheaf_etale_of_isEtale B S hS
        (isEtale_comp B S hS (isEtale_of_presheaf_etale B S hS hg) hf))

/-- **An algebraic space is reduced as soon as the open complement of an effective Cartier
divisor on it is reduced.** On every étale scheme chart the divisor is an effective Cartier
divisor of the chart, and its complement there is an étale chart of the complement, hence
reduced; so the chart is reduced by
`AlgebraicGeometry.Space.isReduced_of_isEffectiveCartierDivisor_of_isReduced_compl`. -/
theorem hasEtaleLocalProperty_isReduced_of_isEffectiveCartierDivisor (X : AlgebraicSpaces B S hS)
    (D : ClosedSubspaces B S hS X.1) (hD : IsEffectiveCartierDivisor B S hS X D)
    (hred : HasEtaleLocalProperty B S hS (openComplement B S hS D.1).toFunctor
      (fun T : Scheme.{u} => IsReduced T)) :
    HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsReduced T) := by
  obtain ⟨hUalg, hU⟩ := isOpenSubspace_openComplement B S hS X.2 D.1 D.2
  refine (exists_atlas_iff_forall_etale B S hS X.1 (fun T : Scheme.{u} => IsReduced T) X.2).mpr
    fun A q hq => ?_
  set T := BigFppfOver.toScheme B S hS
  have hclosed : _root_.AlgebraicGeometry.IsClosedImmersion (T.map (D.2.2.rep.snd q)) :=
    D.2.2.property_snd q
  have hopen : _root_.AlgebraicGeometry.IsOpenImmersion (T.map (hU.rep.snd q)) :=
    hU.property_snd q
  have hI : Stacks.Divisors.IsEffectiveCartierDivisor (T.map (D.2.2.rep.snd q)).ker :=
    (isSchemeEffectiveCartierPullback_iff B S hS X D A q).1
      (hasEffectiveCartierEtalePullbacks_of_isEffectiveCartier B S hS X D hD A q
        (isEtale_of_presheaf_etale B S hS hq))
  have hsupport : ((T.map (D.2.2.rep.snd q)).ker.support : Set (T.obj A)) =
      Set.range (T.map (D.2.2.rep.snd q)) := by
    have hcl : IsClosed (Set.range (T.map (D.2.2.rep.snd q))) :=
      (_root_.AlgebraicGeometry.IsClosedImmersion.iff_isPreimmersion.mp hclosed).2
    rw [Scheme.Hom.support_ker, hcl.closure_eq]
  have hrange :
      (T.map (hU.rep.snd q)).opensRange = (T.map (D.2.2.rep.snd q)).ker.support.compl := by
    refine TopologicalSpace.Opens.ext ?_
    rw [Scheme.Hom.coe_opensRange, range_snd_openComplement B S hS X D hU q,
      TopologicalSpace.Closeds.coe_compl, hsupport]
  -- The chart of the complement is reduced, being an étale chart of the reduced complement.
  have hsq := (hU.rep.isPullback q).flip
  have hfst : IsEtale B S hS (hU.rep.fst q) :=
    isEtale_of_isPullback_yoneda B S hS hsq (isEtale_of_presheaf_etale B S hS hq)
  have hPred : IsReduced (T.obj (hU.rep.pullback q)) :=
    (exists_atlas_iff_forall_etale B S hS _ (fun T : Scheme.{u} => IsReduced T) hUalg).mp hred
      _ (hU.rep.fst q) (presheaf_etale_of_isEtale B S hS hfst)
  have hcompl : IsReduced ((T.map (hU.rep.snd q)).opensRange).toScheme :=
    isReduced_of_isOpenImmersion (T.map (hU.rep.snd q)).isoOpensRange.inv
  rw [hrange] at hcompl
  exact isReduced_of_isEffectiveCartierDivisor_of_isReduced_compl _ hI hcompl

variable {B S hS}

/-- **Stacks 085W, with nothing assumed.** The blowup `b : X' ⟶ X` of a reduced algebraic space
`X` over `S` in a closed subspace `Z` is reduced.

The exceptional divisor `b⁻¹(Z)` is an effective Cartier divisor on `X'` and its complement is
`b⁻¹(X ∖ Z)`, which `b` maps isomorphically onto the open subspace `X ∖ Z` of the reduced space
`X` (Stacks 085T); so
`AlgebraicGeometry.Space.hasEtaleLocalProperty_isReduced_of_isEffectiveCartierDivisor`
applies. -/
theorem hasEtaleLocalProperty_isReduced_of_isBlowupAlong' {X X' : AlgebraicSpaces B S hS}
    {Z : ClosedSubspaces B S hS X.1} {b : X' ⟶ X} (hb : IsBlowupAlong B S hS Z b)
    (hX : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsReduced T)) :
    HasEtaleLocalProperty B S hS X'.1 (fun T : Scheme.{u} => IsReduced T) := by
  set W := openComplementOfClosedSubspace B S hS X Z with hW
  have hZW : subspacePointSet B S hS X.1 Z.1 = (subspacePointSet B S hS X.1 W.1)ᶜ := by
    rw [hW, subspacePointSet_openComplement, compl_compl]
  have heq := preimage_eq_openComplement_preimage W Z b hZW
  have hPalg : IsAlgebraicSpace B S hS (W.1.preimage b.hom).toFunctor :=
    (isOpenSubspace_preimage B S hS b.hom W.1 X.2 X'.2 W.2).1
  have hWred : HasEtaleLocalProperty B S hS W.1.toFunctor (fun T : Scheme.{u} => IsReduced T) :=
    hasEtaleLocalProperty_isReduced_of_isEtale B S hS W.2.1 X.2 W.1.ι
      (isEtale_of_isOpenImmersion B S hS W.2.2) hX
  have hiso : IsIso (W.1.fromPreimage b.hom) := isIso_fromPreimage_openComplement hb
  have hPred : HasEtaleLocalProperty B S hS (W.1.preimage b.hom).toFunctor
      (fun T : Scheme.{u} => IsReduced T) :=
    hasEtaleLocalProperty_isReduced_of_isEtale B S hS hPalg W.2.1 (W.1.fromPreimage b.hom)
      (isEtale_of_isIso B S hS _) hWred
  rw [heq] at hPred
  exact hasEtaleLocalProperty_isReduced_of_isEffectiveCartierDivisor B S hS X'
    ⟨Z.1.preimage b.hom, isClosedSubspace_preimage B S hS b.hom Z.1 X.2 X'.2 Z.2⟩
    hb.isPullbackDefined hPred

end AlgebraicGeometry.Space

end
