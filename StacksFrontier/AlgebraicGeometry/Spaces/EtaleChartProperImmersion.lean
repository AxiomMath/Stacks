module

public import StacksFrontier.AlgebraicGeometry.AffineProductClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.StandardAffineChart
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeLocalCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFiniteReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedAffineIntersections
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteRepresentability
public import StacksFrontier.AlgebraicGeometry.VeryAmpleAffineBase.CoordinateChoice

/-!
# An affine étale chart immersed in a representable proper morphism

This file proves one step of the proof of [Stacks, Tag 0ADD]: if `Z` is a quasi-compact separated
algebraic space over `S` and `v : V ⟶ Z` is an étale morphism from an affine scheme, then `v`
factors as an immersion `V ⟶ Q` followed by a representable proper morphism `Q ⟶ Z`.

## Main results

* `AlgebraicGeometry.Space.exists_isImmersion_isProper_of_isEtale_of_isAffine`: the factorization.

## References

* [Stacks Project, Tag 0ADD](https://stacks.math.columbia.edu/tag/0ADD)
* [Stacks Project, Tag 0AHS](https://stacks.math.columbia.edu/tag/0AHS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Finitely many functions on one factor generate a fibre product over the other.** Let
`p : P ⟶ U` and `q : P ⟶ V` be morphisms of schemes such that `Γ(V) ⟶ Γ(P)` is of finite type and
the canonical map `Γ(U) ⊗_ℤ Γ(V) ⟶ Γ(P)` is surjective. Then there are finitely many global
sections `c₁, …, cₘ` of `U` whose pullbacks generate `Γ(P)` as a `Γ(V)`-algebra, that is, such that
evaluation `Γ(V)[t₁, …, tₘ] ⟶ Γ(P)` at their pullbacks is surjective. -/
theorem exists_surjective_eval₂Hom_of_surjective_globalSectionsTensorLift {P U V : Scheme.{u}}
    (p : P ⟶ U) (q : P ⟶ V) (hq : RingHom.FiniteType q.appTop.hom)
    (hsurj : Function.Surjective (globalSectionsTensorLift p q)) :
    ∃ (m : ℕ) (c : ULift.{u} (Fin m) → Γ(U, ⊤)),
      Function.Surjective (MvPolynomial.eval₂Hom q.appTop.hom fun k ↦ p.appTop (c k)) := by
  classical
  let : Algebra Γ(V, ⊤) Γ(P, ⊤) := q.appTop.hom.toAlgebra
  have htop : Algebra.adjoin Γ(V, ⊤) (Set.range p.appTop.hom) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨t, rfl⟩ := hsurj y
    induction t using TensorProduct.inductionOn with
    | tmul a b =>
      rw [globalSectionsTensorLift_tmul]
      exact mul_mem (Algebra.subset_adjoin ⟨a, rfl⟩) (Subalgebra.algebraMap_mem _ b)
    | add x y hx hy =>
      rw [map_add]
      exact add_mem hx hy
  obtain ⟨s, hs⟩ := hq.out
  choose w hw hmem using fun y : Γ(P, ⊤) ↦
    Stacks.CoordinateChoice.exists_finset_subset_adjoin (R := Γ(V, ⊤))
      (show y ∈ Algebra.adjoin Γ(V, ⊤) (Set.range p.appTop.hom) from htop ▸ Algebra.mem_top)
  set T : Finset Γ(P, ⊤) := s.biUnion w
  have hTr : ∀ y ∈ T, y ∈ Set.range p.appTop.hom := fun y hy ↦ by
    obtain ⟨x, -, hyx⟩ := Finset.mem_biUnion.1 hy
    exact hw x hyx
  have hadj : Algebra.adjoin Γ(V, ⊤) (T : Set Γ(P, ⊤)) = ⊤ := by
    rw [eq_top_iff, ← hs, Algebra.adjoin_le_iff]
    exact fun y hy ↦ Algebra.adjoin_mono (Finset.coe_subset.2 (Finset.subset_biUnion_of_mem w hy))
      (hmem y)
  let c : ULift.{u} (Fin T.card) → Γ(U, ⊤) := fun k ↦
    (hTr _ (T.equivFin.symm k.down).2).choose
  have hc : ∀ k, p.appTop (c k) = T.equivFin.symm k.down := fun k ↦
    (hTr _ (T.equivFin.symm k.down).2).choose_spec
  refine ⟨T.card, c, fun y ↦ ?_⟩
  have hrange : Set.range (fun k ↦ p.appTop (c k)) = (T : Set Γ(P, ⊤)) := by
    ext x
    simp only [hc, Set.mem_range, Finset.mem_coe]
    refine ⟨?_, fun hx ↦ ⟨⟨T.equivFin ⟨x, hx⟩⟩, by simp⟩⟩
    rintro ⟨k, rfl⟩
    exact (T.equivFin.symm k.down).2
  have hy : y ∈ Algebra.adjoin Γ(V, ⊤) (Set.range fun k ↦ p.appTop (c k)) := by
    rw [hrange, hadj]
    exact Algebra.mem_top
  rwa [Algebra.adjoin_range_eq_range_aeval] at hy

/-- **An affine étale chart of a quasi-compact separated algebraic space is immersed, over the
space, in a representable proper morphism.** Let `Z` be a quasi-compact algebraic space over `S`
which is separated, and let `v : V ⟶ Z` be an étale morphism from an object of the site with affine
underlying scheme. Then there are an algebraic space `Q`, a representable proper morphism
`q : Q ⟶ Z` and an immersion `i : V ⟶ Q` with `i ≫ q = v`. -/
theorem exists_isImmersion_isProper_of_isEtale_of_isAffine
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZ : IsAlgebraicSpace B S hS Z)
    (hqc : IsQuasiCompactSpace B S hS Z)
    (hsep : IsAbsolutelySeparated B S hS B.contains_terminal Z)
    (V : BigFppfOver B S hS) (_ : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (v : yoneda.obj V ⟶ Z) (_ : IsEtale B S hS v) :
    ∃ (Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS Q)
      (q : Q ⟶ Z) (i : yoneda.obj V ⟶ Q),
      IsProper B S hS q ∧ yoneda.relativelyRepresentable q ∧ IsImmersion B S hS i ∧ i ≫ q = v := by
  classical
  rename_i hVaff hv
  obtain ⟨D, f, hDaff, hfs, hfe⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS Z hZ).1 hqc
  have hfe' := (isEtale_iff_presheaf_of_yoneda B S hS f).1 hfe
  have hve' := (isEtale_iff_presheaf_of_yoneda B S hS v).1 hv
  have hrep : yoneda.relativelyRepresentable v :=
    Functor.relativelyRepresentable.of_diag hZ.diagonal_representable v
  set P := hrep.pullback f
  set pV : P ⟶ V := hrep.fst' f
  set pD : P ⟶ D := hrep.snd f
  have hpb : IsPullback (yoneda.map pV) (yoneda.map pD) v f := hrep.isPullback' f
  obtain ⟨hPaff, hsurj⟩ := (isAbsolutelySeparated_iff_hasAffineIntersections B S hS
    B.contains_terminal Z hZ).1 hsep V D P v f pV pD hVaff hDaff hpb
  have hpDet : Etale ((BigFppfOver.toScheme B S hS).map pD) :=
    hve'.property f (yoneda.map pV) pD hpb
  have hft : RingHom.FiniteType ((BigFppfOver.toScheme B S hS).map pD).appTop.hom :=
    HasRingHomProperty.appTop @LocallyOfFiniteType _ inferInstance
  obtain ⟨m, c, hc⟩ := exists_surjective_eval₂Hom_of_surjective_globalSectionsTensorLift
    ((BigFppfOver.toScheme B S hS).map pV) ((BigFppfOver.toScheme B S hS).map pD) hft hsurj
  let Dsch := (BigFppfOver.toScheme B S hS).obj D
  let Dhom : Dsch ⟶ S := B.inclusion.map D.hom
  have hAlft : LocallyOfFiniteType (𝔸(ULift.{u} (Fin m); S) ↘ S) := inferInstance
  have hAqc : QuasiCompact (𝔸(ULift.{u} (Fin m); S) ↘ S) := inferInstance
  have hA : B.Contains 𝔸(ULift.{u} (Fin m); S) :=
    @contains_of_locallyOfFiniteType_of_quasiCompact B S hS (Over.mk (𝟙 (B.obj hS))) _
      (𝔸(ULift.{u} (Fin m); S) ↘ S) hAlft hAqc
  have hPpr := isProper_projectiveSpaceOver m S
  have hPn : B.Contains (projectiveSpaceOver m S) :=
    @contains_of_locallyOfFiniteType_of_quasiCompact B S hS (Over.mk (𝟙 (B.obj hS))) _
      (projectiveSpaceOver m S ↘ S) inferInstance inferInstance
  have hE : B.Contains 𝔸(ULift.{u} (Fin m); Dsch) :=
    @contains_of_locallyOfFiniteType_of_quasiCompact B S hS D _
      (𝔸(ULift.{u} (Fin m); Dsch) ↘ Dsch) inferInstance inferInstance
  let Aₛ : BigFppfOver B S hS := BigFppfOver.mk B S hS hA (𝔸(ULift.{u} (Fin m); S) ↘ S)
  let Pₛ : BigFppfOver B S hS := BigFppfOver.mk B S hS hPn (projectiveSpaceOver m S ↘ S)
  let Eₛ : BigFppfOver B S hS := BigFppfOver.mk B S hS hE (𝔸(ULift.{u} (Fin m); Dsch) ↘ Dsch ≫ Dhom)
  let πD : Eₛ ⟶ D := Over.homMk (ObjectProperty.homMk (𝔸(ULift.{u} (Fin m); Dsch) ↘ Dsch))
    (by apply ObjectProperty.hom_ext; rfl)
  let μ : Eₛ ⟶ Aₛ := BigFppfOver.homMk B S hS hA _ (AffineSpace.map (ULift.{u} (Fin m)) Dhom)
    (AffineSpace.map_over Dhom)
  let cV : V ⟶ Aₛ := BigFppfOver.homMk B S hS hA _
    (AffineSpace.homOfVector (B.inclusion.map V.hom) c) (AffineSpace.homOfVector_over _ _)
  let r : P ⟶ Eₛ := BigFppfOver.homMk B S hS hE _
    (AffineSpace.homOfVector ((BigFppfOver.toScheme B S hS).map pD)
      fun k ↦ ((BigFppfOver.toScheme B S hS).map pV).appTop (c k))
    (by
      rw [← Category.assoc, AffineSpace.homOfVector_over]
      exact BigFppfOver.toScheme_map_comp_structureHom B S hS pD)
  let e := Equiv.ulift.{u}.trans (finSuccAboveEquiv (0 : Fin (m + 1)))
  let α : Aₛ ⟶ Pₛ := BigFppfOver.homMk B S hS hPn _ (projectiveSpaceOver.affineChart m 0 e S)
    (projectiveSpaceOver.affineChart_over m 0 e S)
  have hcomp : ∀ {Y X X' : Scheme.{u}} (g₁ : Y ⟶ X) (g₂ : X ⟶ X') (w : ULift.{u} (Fin m) → Γ(Y, ⊤)),
      AffineSpace.homOfVector g₁ w ≫ AffineSpace.map (ULift.{u} (Fin m)) g₂ =
        AffineSpace.homOfVector (g₁ ≫ g₂) w :=
    fun g₁ g₂ w ↦ by
      ext1
      · simp
      · rename_i k
        rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.map_appTop_coord,
          AffineSpace.homOfVector_appTop_coord, AffineSpace.homOfVector_appTop_coord]
  have hrπ : r ≫ πD = pD := by
    apply (BigFppfOver.toScheme B S hS).map_injective
    rw [Functor.map_comp]
    exact AffineSpace.homOfVector_over _ _
  have hrμ : r ≫ μ = pV ≫ cV := by
    apply (BigFppfOver.toScheme B S hS).map_injective
    rw [Functor.map_comp, Functor.map_comp]
    change AffineSpace.homOfVector _ _ ≫ AffineSpace.map (ULift.{u} (Fin m)) Dhom =
      (BigFppfOver.toScheme B S hS).map pV ≫ AffineSpace.homOfVector _ c
    rw [hcomp, AffineSpace.comp_homOfVector, BigFppfOver.toScheme_map_comp_structureHom,
      BigFppfOver.toScheme_map_comp_structureHom]
    rfl
  have hterm : ∀ T : BigFppfOver B S hS,
      (BigFppfOver.toScheme B S hS).map (Over.mkIdTerminal.from T) = B.inclusion.map T.hom := by
    intro T
    simp
  have hsite : IsPullback μ πD (Over.mkIdTerminal.from Aₛ) (Over.mkIdTerminal.from D) := by
    have _ : ReflectsLimit (cospan (Over.mkIdTerminal.from Aₛ) (Over.mkIdTerminal.from D))
        (BigFppfOver.toScheme B S hS) :=
      reflectsLimit_of_reflectsIsomorphisms _ _
    refine IsPullback.of_map_of_faithful (BigFppfOver.toScheme B S hS) ?_
    rw [hterm, hterm]
    exact AffineSpace.isPullback_map (n := ULift.{u} (Fin m)) Dhom
  let tZ := isTerminal_yoneda_obj_base B S hS
  let g : yoneda.obj Eₛ ⟶ yoneda.obj Aₛ ⨯ Z := prod.lift (yoneda.map μ) (yoneda.map πD ≫ f)
  have hL : IsPullback g (yoneda.map πD) prod.snd f := by
    refine IsPullback.of_right ?_ (prod.lift_snd _ _) (isPullback_prod_fst_snd_yoneda_obj Aₛ Z)
    rw [prod.lift_fst, show f ≫ tZ.from Z = yoneda.map (Over.mkIdTerminal.from D) from
      tZ.hom_ext _ _]
    exact hsite.map yoneda
  let j : yoneda.obj V ⟶ yoneda.obj Aₛ ⨯ Z := prod.lift (yoneda.map cV) v
  have hsq : IsPullback (yoneda.map pV) (yoneda.map r) j g := by
    refine IsPullback.of_bot ?_ ?_ hL
    · rw [prod.lift_snd, ← Functor.map_comp, hrπ]
      exact hpb
    · refine prod.hom_ext ?_ ?_
      · simp only [Category.assoc, prod.lift_fst, j, g, ← Functor.map_comp, hrμ]
      · simp only [Category.assoc, prod.lift_snd, j, g, ← Functor.map_comp_assoc, hrπ]
        exact hpb.w
  have hbc := fun (Q : MorphismProperty Scheme.{u}) ↦
    MorphismProperty.relative_isStableUnderBaseChange
    (F := yoneda) (Q.inverseImage (BigFppfOver.toScheme B S hS))
  have _ := Stacks.Descent.isClosedImmersion_descendsAlong_fppf.{u}
  have hj : IsClosedImmersion B S hS j :=
    presheaf_of_surjectiveEtaleChart_of_descendsAlong
      (Q := @_root_.AlgebraicGeometry.IsClosedImmersion)
      (Functor.relativelyRepresentable.of_diag
        (isAlgebraicSpace_prod_yoneda_obj Aₛ hZ).diagonal_representable j)
      ((hbc _).of_isPullback hL.flip hfs) ((hbc _).of_isPullback hL.flip hfe') hsq
      (presheaf_yoneda_map_of_inverseImage B S hS inferInstance r
        (AffineSpace.isClosedImmersion_homOfVector _ _ hc))
  let k : yoneda.obj Aₛ ⨯ Z ⟶ yoneda.obj Pₛ ⨯ Z := prod.map (yoneda.map α) (𝟙 Z)
  have hk : IsOpenImmersion B S hS k :=
    (hbc _).of_isPullback (IsPullback.of_prod_fst_with_id (yoneda.map α) Z)
      (isOpenImmersion_yoneda_map B S hS α
        (inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion
          (projectiveSpaceOver.affineChart m 0 e S))))
  have hQ : IsAlgebraicSpace B S hS (yoneda.obj Pₛ ⨯ Z) := isAlgebraicSpace_prod_yoneda_obj Pₛ hZ
  refine ⟨yoneda.obj Pₛ ⨯ Z, hQ, prod.snd, j ≫ k, ?_, relativelyRepresentable_prod_snd Pₛ Z,
    isImmersion_comp B S hS j k (isImmersion_of_isClosedImmersion B S hS hj)
      (isImmersion_of_isOpenImmersion B S hS hk), by simp [j, k]⟩
  exact (presheaf_isProper_iff B S hS prod.snd hQ hZ (relativelyRepresentable_prod_snd Pₛ Z)).2
    (presheaf_prod_snd inferInstance Pₛ Z (by rw [hterm]; exact hPpr))

end AlgebraicGeometry.Space

end
