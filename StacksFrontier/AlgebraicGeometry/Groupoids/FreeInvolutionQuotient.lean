module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatQuotient.FppfQuotient
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineRelationRepresentable
public import StacksFrontier.CategoryTheory.EquivalenceRelation.FreeInvolution
public import StacksFrontier.CategoryTheory.EquivalenceRelation.Slice

/-!
# The quotient of a scheme by a free involution

Let `σ` be an involution of a scheme `Y` acting freely, in the sense that no nonempty scheme
maps to `Y` by a morphism fixed by `σ`, and suppose every finite set of points of `Y` lies in an
affine open. The two morphisms `Y ⨿ Y ⇉ Y`, the codiagonal and `(𝟙, σ)`, form a finite locally
free equivalence relation on `Y`, so the quotient theorem for finite locally free equivalence
relations produces a scheme `S` and a finite locally free surjection `π : Y ⟶ S` whose kernel
pair is this relation. The base change of `π` along itself is the codiagonal-type morphism
`(𝟙, σ) : Y ⨿ Y ⟶ Y`, which is étale; étaleness is fppf local on the base, so `π` is étale.
Thus `π` is an étale double cover.

## Main results

* `AlgebraicGeometry.exists_etale_quotient_of_free_involution`: the quotient of `Y` by a free
  involution exists and `Y ⟶ S` is finite, surjective and étale, with kernel pair `Y ⨿ Y`.

## References

* [Stacks Project, Tag 08KF](https://stacks.math.columbia.edu/tag/08KF)
* [Stacks Project, Tag 07S7](https://stacks.math.columbia.edu/tag/07S7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Morphisms

universe u

namespace AlgebraicGeometry

/-- The codiagonal `Y ⨿ Y ⟶ Y` is finite and étale: on each summand of the open cover by the
two summands it is the identity. -/
theorem etale_isFinite_coprod_desc_id_id (Y : Scheme.{u}) :
    Etale (coprod.desc (𝟙 Y) (𝟙 Y)) ∧ IsFinite (coprod.desc (𝟙 Y) (𝟙 Y)) := by
  refine ⟨?_, inferInstance⟩
  have _ : IsZariskiLocalAtSource @Etale :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale) (Q := RingHom.Etale)
  refine IsZariskiLocalAtSource.of_openCover (P := @Etale.{u}) (coprodOpenCover.{u, 0} Y Y) ?_
  have : Etale (𝟙 Y) := inferInstance
  rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩)
  · exact (coprod.inl_desc (𝟙 Y) (𝟙 Y)).symm ▸ this
  · exact (coprod.inr_desc (𝟙 Y) (𝟙 Y)).symm ▸ this

/-- For an automorphism `σ` of `Y`, the morphism `(𝟙, σ) : Y ⨿ Y ⟶ Y` is finite and étale. -/
theorem etale_isFinite_coprod_desc_id_of_isIso {Y : Scheme.{u}} (σ : Y ⟶ Y) [IsIso σ] :
    Etale (coprod.desc (𝟙 Y) σ) ∧ IsFinite (coprod.desc (𝟙 Y) σ) := by
  have heq : coprod.desc (𝟙 Y) σ = coprod.map (𝟙 Y) σ ≫ coprod.desc (𝟙 Y) (𝟙 Y) := by
    refine coprod.hom_ext ?_ ?_ <;> simp
  obtain ⟨he, hf⟩ := etale_isFinite_coprod_desc_id_id Y
  rw [heq]
  exact ⟨inferInstance, inferInstance⟩

/-- **The quotient of a scheme by a free involution is an étale double cover.** Let `σ` be an
involution of `Y` with no fixed points in the scheme-theoretic sense (every morphism `c` with
`c ≫ σ = c` has empty source), and suppose that every finite set of points of `Y` lies in an
affine open. Then there is a scheme `S` and a finite étale surjection `π : Y ⟶ S` whose kernel
pair is `Y ⨿ Y`, with projections the codiagonal and `(𝟙, σ)`. -/
theorem exists_etale_quotient_of_free_involution {Y : Scheme.{u}} (σ : Y ⟶ Y)
    (hσ : σ ≫ σ = 𝟙 Y)
    (hfree : ∀ {T : Scheme.{u}} (c : T ⟶ Y), c ≫ σ = c → IsEmpty T)
    (haff : ∀ E : Set Y, E.Finite → ∃ O : Y.Opens, IsAffineOpen O ∧ E ⊆ O) :
    ∃ (S : Scheme.{u}) (π : Y ⟶ S), Etale π ∧ Surjective π ∧ IsFinite π ∧
      IsPullback (coprod.desc (𝟙 Y) (𝟙 Y)) (coprod.desc (𝟙 Y) σ) π π := by
  classical
  have _ : IsIso σ := ⟨⟨σ, hσ, hσ⟩⟩
  -- the relation in `Scheme`
  have hrelY : IsEquivalenceRelation (coprod.desc (𝟙 Y) (𝟙 Y)) (coprod.desc (𝟙 Y) σ) := by
    have h := isEquivalenceRelation_coprod_desc_of_free_involution (𝟙 Y) σ hσ σ
      (by simp) (fun {T} c hc => by
        have _ : IsEmpty T := hfree c (by simpa using hc.symm)
        exact ⟨fun f g => isInitialOfIsEmpty.hom_ext f g⟩)
    simpa only [Category.id_comp] using h
  obtain ⟨het, hft⟩ := etale_isFinite_coprod_desc_id_id Y
  obtain ⟨hes, hfs⟩ := etale_isFinite_coprod_desc_id_of_isIso σ
  -- the base and the site
  obtain ⟨B, hB⟩ := BigFppfSite.exists_containing ({⊤_ Scheme.{u}, Y} : Set Scheme.{u})
  have hS₀ : B.Contains (⊤_ Scheme.{u}) := hB _ (by simp)
  have hY : B.Contains Y := hB Y (by simp)
  let _ : EssentiallySmall.{u} (BigFppfOver B (⊤_ Scheme.{u}) hS₀) :=
    inferInstanceAs (EssentiallySmall.{u} (CostructuredArrow (𝟭 B.Schemes) (B.obj hS₀)))
  let _ : HasSheafify (BigFppfOver.topology B (⊤_ Scheme.{u}) hS₀) (Type u) :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, u} (BigFppfOver.topology B _ hS₀) _
  -- the relation over the terminal scheme
  let t' : Over.mk (terminal.from (Y ⨿ Y)) ⟶ Over.mk (terminal.from Y) :=
    Over.homMk (coprod.desc (𝟙 Y) (𝟙 Y)) (terminal.hom_ext _ _)
  let s' : Over.mk (terminal.from (Y ⨿ Y)) ⟶ Over.mk (terminal.from Y) :=
    Over.homMk (coprod.desc (𝟙 Y) σ) (terminal.hom_ext _ _)
  have _ : IsEquivalenceRelation t'.left s'.left := hrelY
  have hrel : IsEquivalenceRelation t' s' := isEquivalenceRelation_of_left t' s'
  obtain ⟨M, π, -, hflfπ, hsurjπ, hpbπ⟩ :=
    GroupoidScheme.exists_schemeQuotient_of_isFiniteLocallyFree_relation B _ hS₀ t' s'
      (@isFiniteLocallyFree_of_etale_of_isFinite _ _ _ het hft)
      (@isFiniteLocallyFree_of_etale_of_isFinite _ _ _ hes hfs) hrel hY haff
  have hpb : IsPullback (coprod.desc (𝟙 Y) (𝟙 Y)) (coprod.desc (𝟙 Y) σ) π.left π.left :=
    have _ : PreservesLimit (cospan π π) (Over.forget (⊤_ Scheme.{u})) :=
      (Over.preservesLimitsOfShape_forget_of_isConnected (J := WalkingCospan)).preservesLimit
    (Over.forget _).map_isPullback hpbπ
  have _ : Flat π.left := IsFiniteLocallyFree.flat π.left
  have _ : LocallyOfFinitePresentation π.left :=
    IsFiniteLocallyFree.locallyOfFinitePresentation π.left
  have hcov : Presieve.singleton π.left ∈ Scheme.fppfPrecoverage M.left := by
    change Presieve.singleton π.left ∈
      Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation) M.left
    rw [Scheme.singleton_mem_precoverage_iff]
    exact ⟨hsurjπ.surj, ⟨inferInstance, inferInstance⟩⟩
  have hetπ : Etale π.left := by
    refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
      (P := @Etale) (K := Scheme.fppfPrecoverage) hcov ?_
    rintro _ _ _ ⟨⟩
    rw [← hpb.isoPullback_inv_snd]
    exact MorphismProperty.RespectsIso.precomp (@Etale) _ _ hes
  exact ⟨M.left, π.left, hetπ, hsurjπ, IsFiniteLocallyFree.isFinite π.left, hpb⟩

end AlgebraicGeometry

end
