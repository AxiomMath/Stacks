module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.VeryReasonableConditions
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleImageSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.FppfCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# The two forms of a very reasonable atlas

Stacks 03IH says that two conditions on an algebraic space `X` over a scheme `S` are
equivalent: `(1)` there is a Zariski covering of `X` by open subspaces, each carrying a
quasi-compact surjective étale chart by a scheme, and `(2)` there is a family of étale charts
of `X` by schemes which is jointly surjective and whose self-intersection projections are
quasi-compact. Condition `(2)` is `AlgebraicGeometry.Space.IsVeryReasonableSpace`, the
formulation of very reasonableness the library carries, so this is the comparison that makes
that definition agree with the Zariski-local one.

From `(1)` to `(2)`: a single quasi-compact surjective étale chart of an open subspace already
witnesses very reasonableness of that subspace — its self-intersection projections are
quasi-compact because quasi-compactness of a morphism of algebraic spaces may be tested on the
represented base changes of its target (Stacks 03KG) — and very reasonableness is Zariski local
(`AlgebraicGeometry.Space.isVeryReasonableSpace_of_isZariskiCover`).

From `(2)` to `(1)`: the open subspace attached to a chart is the one whose points are the image
of the points of its source, which is open because an étale morphism is open on points
(Stacks 03IR); the chart factors through it as a surjective étale chart by Stacks 06NF, the
self-intersection is unchanged by that factorization because the inclusion of an open subspace
is a monomorphism, so the projections stay quasi-compact, and the factored chart is therefore
quasi-compact by Stacks 03KG. Those open subspaces cover `X` because the original family of
charts is jointly surjective and factors through their coproduct.

## Main results

* `AlgebraicGeometry.Space.isVeryReasonableSpace_iff_exists_isZariskiCover_quasiCompact_chart`:
  **Stacks 03IH**, the equivalence of the two conditions.

## Implementation notes

Joint surjectivity of a family of charts is local surjectivity of the induced morphism out of
the coproduct of the representable presheaves, as in
`AlgebraicGeometry.Space.IsVeryReasonableSpace`; surjectivity of a single chart onto an open
subspace is local surjectivity of that chart. Both coproduct comparisons needed here are
instances of `CategoryTheory.Presheaf.isLocallySurjective_of_isLocallySurjective_fac`: a
morphism through which a locally surjective morphism factors is itself locally surjective.
In particular the atlas produced in the direction `(1) ⇒ (2)` is indexed by `PUnit`, the
coproduct over which the single chart is read as a jointly surjective family.

## References

* [Stacks Project, Tag 03IH](https://stacks.math.columbia.edu/tag/03IH)
* [Stacks Project, Tag 03IR](https://stacks.math.columbia.edu/tag/03IR)
* [Stacks Project, Tag 03KG](https://stacks.math.columbia.edu/tag/03KG)
* [Stacks Project, Tag 06NF](https://stacks.math.columbia.edu/tag/06NF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An étale chart of an algebraic space over `S` whose first self-intersection projection is
quasi-compact factors through an open subspace as a quasi-compact surjective étale chart of
that subspace.

The open subspace is the one cut out by the image of the points of the source, and the
factorization is the one of Stacks 06NF. -/
private theorem exists_isOpenSubspace_quasiCompact_chart_of_isEtale
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X) (hφ : IsEtale B S hS φ)
    (hfst : IsQuasiCompact B S hS (pullback.fst φ φ)) :
    ∃ (G : Subfunctor X) (_ : IsOpenSubspace B S hS G) (ψ : yoneda.obj U ⟶ G.toFunctor),
      ψ ≫ G.ι = φ ∧ IsEtale B S hS ψ ∧
        Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) ψ ∧
        IsQuasiCompact B S hS ψ := by
  have hU : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  have hφ' := presheaf_etale_of_isEtale B S hS hφ
  obtain ⟨G, hG, himage⟩ := exists_isOpenSubspace_range_pointsMap_eq B S hS hX _
    (isOpen_range_pointsMap_of_isEtale B S hS φ hU hX hφ)
  obtain ⟨ψ, rfl⟩ : ∃ ψ : yoneda.obj U ⟶ G.toFunctor, ψ ≫ G.ι = φ :=
    ⟨factorThroughEtaleImage B S hS hX U φ G hG himage,
      factorThroughEtaleImage_comp B S hS hX U φ G hG himage⟩
  have hψsurj := surjective_factor_through_etaleImage B S hS U _ G hG himage ψ rfl
  have hψetale := etale_factor_through_etaleImage B S hS U _ hφ' G hG ψ rfl
  have hpb : IsPullback (pullback.fst ψ ψ) (pullback.snd ψ ψ) (ψ ≫ G.ι) (ψ ≫ G.ι) :=
    IsPullback.of_isLimit (pullbackIsPullbackOfCompMono ψ ψ G.ι)
  exact ⟨G, hG, ψ, rfl, isEtale_of_presheaf_etale B S hS hψetale,
    isLocallySurjective_of_surjective_etale B S hS ψ hψsurj hψetale,
    ((isQuasiCompact_tfae B S hS hU hG.1 ψ).out 4 1 rfl rfl).mp
      ⟨U, ψ, (surjective_iff_surjective_pointsMap B S hS G.toFunctor hG.1 U ψ).mp hψsurj,
        isEtale_of_presheaf_etale B S hS hψetale,
        isQuasiCompact_of_domainIso B S hS hpb.isoPullback.symm hpb.isoPullback_inv_fst hfst⟩⟩

/-- **Stacks 03IH.** An algebraic space over `S` is very reasonable — it has a jointly
surjective family of étale charts by schemes whose two self-intersection projections are
quasi-compact — if and only if it has a Zariski covering by open subspaces each of which
carries a quasi-compact surjective étale chart by a scheme. -/
@[stacks 03IH]
theorem isVeryReasonableSpace_iff_exists_isZariskiCover_quasiCompact_chart
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X) :
    IsVeryReasonableSpace B S hS X ↔
      ∃ (I : Type u) (Xᵢ : I → Subfunctor X), IsZariskiCover B S hS I Xᵢ ∧
        ∃ (U : I → BigFppfOver B S hS) (φ : ∀ i, yoneda.obj (U i) ⟶ (Xᵢ i).toFunctor),
          ∀ i, IsEtale B S hS (φ i) ∧
            Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (φ i) ∧
            IsQuasiCompact B S hS (φ i) := by
  classical
  constructor
  · rintro ⟨I, U, φ, hsurj, hprops⟩
    choose Xᵢ hXᵢ ψ hfac hψetale hψsurj hψqc using fun i : I ↦
      exists_isOpenSubspace_quasiCompact_chart_of_isEtale B S hS hX (U i) (φ i) (hprops i).1
        (hprops i).2.1
    refine ⟨I, Xᵢ, ⟨hXᵢ, ?_⟩, U, ψ, fun i ↦ ⟨hψetale i, hψsurj i, hψqc i⟩⟩
    have hcomp : (Sigma.desc fun i ↦ ψ i ≫ Sigma.ι (fun i ↦ (Xᵢ i).toFunctor) i) ≫
        (Sigma.desc fun i ↦ (Xᵢ i).ι) = Sigma.desc φ :=
      Sigma.hom_ext _ _ fun i ↦ by
        rw [← Category.assoc, Sigma.ι_desc, Category.assoc, Sigma.ι_desc, Sigma.ι_desc, hfac i]
    have : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc φ) := hsurj
    exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac _ hcomp
  · rintro ⟨I, Xᵢ, hcover, U, φ, hφ⟩
    refine isVeryReasonableSpace_of_isZariskiCover B S hS X I Xᵢ hcover fun i ↦ ?_
    obtain ⟨hetale, hlocsurj, hqc⟩ := hφ i
    have hfst : IsQuasiCompact B S hS (pullback.fst (φ i) (φ i)) :=
      ((isQuasiCompact_tfae B S hS (isAlgebraicSpace_yoneda B S hS (U i))
        (hcover.1 i).1 (φ i)).out 1 2 rfl rfl).mp hqc (U i) (φ i)
    refine ⟨PUnit.{u + 1}, fun _ ↦ U i, fun _ ↦ φ i, ?_, fun _ ↦ ⟨hetale, hfst, ?_⟩⟩
    · have : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (φ i) := hlocsurj
      exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac _
        (Sigma.ι_desc (fun _ : PUnit.{u + 1} ↦ φ i) PUnit.unit)
    · exact isQuasiCompact_of_domainIso B S hS (pullbackSymmetry (φ i) (φ i))
        (pullbackSymmetry_hom_comp_snd _ _) hfst

end AlgebraicGeometry.Space

end
