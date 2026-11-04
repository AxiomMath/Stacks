module

public import StacksFrontier.AlgebraicGeometry.ProEtale.AppProetaleAlgebras
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.AffineCoversTop
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.LocallyConstantTrivialization
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.TestingFamily
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.WContractibleCover
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.SliceTestingFamily

/-!
# The pro-étale site has a testing family of w-contractible affines

Let `S` be a scheme. The affine objects `W` of the small pro-étale site `S_proét` whose ring of
global sections is w-contractible form a testing family of weakly contractible objects, in every
value universe:

* every object of `S_proét` is covered by such objects: its affine opens cover it, and each
  affine object `T` is covered by the spectrum of a faithfully flat ind-étale w-contractible
  extension of `Γ(T, ⊤)` (Stacks 0983), a single surjective weakly étale morphism of affine
  schemes (Stacks 098I);
* each such `W` is weakly contractible on its slice site, for sheaves of sets in any universe,
  since every covering sieve of `W` is refined by a clopen decomposition of `W`
  (Stacks 098H).

The small pro-étale site is not essentially small, so this family is what the
derived-completeness results for sites with enough weakly contractible objects are applied with
on `S_proét`.

## Main definitions

* `AlgebraicGeometry.Scheme.ProEt.IsAffineWContractible`: the affine objects of `S_proét`
  whose ring of global sections is w-contractible.
* `AlgebraicGeometry.Scheme.ProEt.testingFamily`: the testing family they form, in any value
  universe.

## Main results

* `AlgebraicGeometry.Scheme.ProEt.exists_isAffineWContractible_cover_of_isAffine`: an affine
  object of `S_proét` is covered by a single affine object with w-contractible ring of global
  sections.
* `AlgebraicGeometry.Scheme.ProEt.hasEnoughObjects_isAffineWContractible`: every object of
  `S_proét` is covered by such objects.

## References

* [Stacks Project, Tag 0983](https://stacks.math.columbia.edu/tag/0983)
* [Stacks Project, Tag 098H](https://stacks.math.columbia.edu/tag/098H)
* [Stacks Project, Tag 098I](https://stacks.math.columbia.edu/tag/098I)
* [Stacks Project, Tag 0990](https://stacks.math.columbia.edu/tag/0990)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite ProetaleWContractible

universe t u

namespace AlgebraicGeometry.Scheme.ProEt

variable {S : Scheme.{u}}

/-- The affine objects of `S_proét` whose ring of global sections is w-contractible. -/
def IsAffineWContractible : ObjectProperty S.ProEt := fun W ↦
  IsAffine W.left ∧ IsWContractible.{u, u} Γ(W.left, ⊤)

/-- **Stacks 098I for an affine object of `S_proét`.** An affine object `T` of `S_proét` is
covered by a single affine object whose ring of global sections is w-contractible: the
spectrum of a faithfully flat ind-étale w-contractible extension of `Γ(T, ⊤)` (Stacks 0983). -/
theorem exists_isAffineWContractible_cover_of_isAffine (T : S.ProEt) [IsAffine T.left] :
    ∃ (V : S.ProEt) (p : V ⟶ T), IsAffineWContractible V ∧
      Sieve.ofArrows (fun _ : PUnit.{u + 1} ↦ V) (fun _ ↦ p) ∈ ProEt.topology S T := by
  classical
  let A := Γ(T.left, ⊤)
  obtain ⟨D, hD, f, hff, hind, hwd⟩ := ProEtale.exists_faithfullyFlat_ind_etale_wContractible A
  let _ : CommRing D := hD
  let _ : Algebra A D := f.toAlgebra
  let r : CommRingCat.of A ⟶ CommRingCat.of D := CommRingCat.ofHom f
  have hri : CommRingCat.etale.ind.{u} r :=
    (MorphismProperty.ind_iff_ind_underMk _).mpr hind
  have hweak : Algebra.WeaklyEtale A D := Algebra.weaklyEtale_of_ind_etale
    (StacksDraft.indEtale_iff.mpr (CommAlgCat.ind_etale_iff_ind_algebraMap.mpr hri))
  let g₀ : Spec (CommRingCat.of D) ⟶ T.left := Spec.map r ≫ T.left.isoSpec.inv
  obtain ⟨hflat, hsurj⟩ := (flat_and_surjective_SpecMap_iff r).mpr hff
  have hdiag : Flat (pullback.diagonal (Spec.map r)) := by
    show Flat (pullback.diagonal (Spec.map (CommRingCat.ofHom (algebraMap A D))))
    rw [diagonal_SpecMap A D]
    have hm : Flat (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.lmul' A (S := D)).toRingHom)) := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      exact ((Algebra.weaklyEtale_iff A D).mp hweak).2
    exact MorphismProperty.comp_mem _ _ _ hm inferInstance
  have hwer : WeaklyEtale (Spec.map r) := ⟨hflat, hdiag⟩
  have hweg : WeaklyEtale g₀ := inferInstance
  have hsurjg : Surjective g₀ := inferInstance
  have hqcg : QuasiCompact g₀ := quasiCompact_of_compactSpace _
  have hT : WeaklyEtale T.hom := T.prop
  let V : S.ProEt := ProEt.mk (g₀ ≫ T.hom)
  let p : V ⟶ T := MorphismProperty.Over.homMk g₀ (by rw [ProEt.mk_hom]; rfl)
  refine ⟨V, p, ⟨inferInstanceAs (IsAffine (Spec (CommRingCat.of D))),
    isWContractible_of_isWeaklyContractible (Spec (CommRingCat.of D))
      (((main_theorem D).out 1 2).mp hwd)⟩, ?_⟩
  have hmem : Presieve.map (ProEt.forget S ⋙ Over.forget S) (Presieve.singleton p) ∈
      Scheme.proetalePrecoverage ((ProEt.forget S ⋙ Over.forget S).obj T) := by
    have hmap : (ProEt.forget S ⋙ Over.forget S).map p = g₀ := rfl
    rw [Presieve.map_singleton, hmap]
    exact @Scheme.Hom.singleton_mem_propQCPrecoverage @WeaklyEtale _ _ g₀ hweg hsurjg hqcg
  show Sieve.generate (Presieve.ofArrows _ _) ∈ _
  rw [Presieve.ofArrows_pUnit]
  exact Precoverage.generate_mem_toGrothendieck hmem

/-- **Stacks 098I for `S_proét`.** Every object of `S_proét` is covered by affine objects whose
rings of global sections are w-contractible: its affine opens cover it, and each of them is
covered by a single such object. -/
theorem hasEnoughObjects_isAffineWContractible :
    (ProEt.topology S).HasEnoughObjects (IsAffineWContractible (S := S)) := by
  intro T
  classical
  let E : PreZeroHypercover T := {
    I₀ := T.left.affineCover.I₀
    X i := ProEt.mk (T.left.affineCover.f i ≫ T.hom)
    f i := MorphismProperty.Over.homMk (T.left.affineCover.f i) (by
      rw [ProEt.mk_hom]; rfl) }
  have hmap : E.map (ProEt.forget S ⋙ Over.forget S) =
      T.left.affineCover.toPreZeroHypercover := by
    apply PreZeroHypercover.ext rfl
    all_goals simp [E, ProEt.forget, MorphismProperty.Over.forget,
      MorphismProperty.Comma.forget, Over.forget, ProEt.mk]
  have hE : E.presieve₀ ∈ ProEt.precoverage S T := by
    rw [ProEt.precoverage, Precoverage.mem_comap_iff, ← PreZeroHypercover.presieve₀_map]
    show (E.map (ProEt.forget S ⋙ Over.forget S)).presieve₀ ∈
      Scheme.proetalePrecoverage T.left
    rw [hmap]
    exact ProEtale.zariskiPrecoverage_le_proetalePrecoverage T.left T.left.affineCover.mem₀
  have (j : E.I₀) : IsAffine (E.X j).left := inferInstanceAs (IsAffine (T.left.affineCover.X j))
  choose V p hV hp using fun j ↦ exists_isAffineWContractible_cover_of_isAffine (E.X j)
  refine ⟨E.I₀, V, fun j ↦ p j ≫ E.f j, ?_, hV⟩
  refine (ProEt.topology S).transitive (Precoverage.generate_mem_toGrothendieck hE) _ ?_
  rintro Z _ ⟨W, i, q, ⟨j⟩, rfl⟩
  have hle : Sieve.ofArrows (fun _ : PUnit.{u + 1} ↦ V j) (fun _ ↦ p j) ≤
      (Sieve.ofArrows V fun j ↦ p j ≫ E.f j).pullback (E.f j) := by
    intro Y a ha
    obtain ⟨_, b, hb⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 ha
    show Sieve.ofArrows V _ (a ≫ E.f j)
    rw [hb, Category.assoc]
    exact Sieve.downward_closed _ (Sieve.ofArrows_mk V (fun j ↦ p j ≫ E.f j) j) b
  have hpb := (ProEt.topology S).pullback_stable i
    ((ProEt.topology S).superset_covering hle (hp j))
  rwa [← Sieve.pullback_comp] at hpb

variable (S) in
/-- **The testing family of `S_proét`.** The affine objects of `S_proét` whose rings of global
sections are w-contractible form a testing family of weakly contractible objects in every value
universe `t`. -/
def testingFamily : Stacks.WeaklyContractible.SliceTestingFamily.{t}
    S.ProEt (ProEt.topology S) where
  B := IsAffineWContractible
  surjective_app_over W hW _ _ φ hφ :=
    haveI := hW.1
    surjective_app_over_of_isWContractible W hW.2 φ hφ
  hasEnoughObjects := hasEnoughObjects_isAffineWContractible

end AlgebraicGeometry.Scheme.ProEt

end
