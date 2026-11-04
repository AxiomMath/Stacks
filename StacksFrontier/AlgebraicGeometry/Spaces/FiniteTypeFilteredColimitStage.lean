module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiImageSubsheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeFilteredColimit

/-!
# A morphism from a module of finite type into a filtered colimit lands in one stage

Let `U` be a quasi-compact algebraic space and `c` a filtered colimit cocone of `𝒪_U`-modules
whose transition maps are injective.  A morphism `m : 𝒢 ⟶ c.pt` from an `𝒪_U`-module of finite
type then lands in one stage: there is an index `k` such that every section of `𝒢` is carried
by `m` into the image of the sections of the `k`-th stage.  For `m` the identity this is the
second assertion of Stacks 01BB for algebraic spaces,
`AlgebraicGeometry.Space.exists_isIso_ι_of_isFiniteType_of_isQuasiCompactSpace`.

## Main results

* `AlgebraicGeometry.Space.exists_stage_of_isFiniteType_of_isQuasiCompactSpace`: a morphism from
  a module of finite type into a filtered colimit with injective transition maps, on a
  quasi-compact algebraic space, lands in one stage.

## References

* [Stacks Project, Tag 01BB](https://stacks.math.columbia.edu/tag/01BB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.SheafOfModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Stage

variable {U : AlgebraicSpaces B S hS}

/-- **A morphism from a module of finite type into a filtered colimit with injective transition
maps, on a quasi-compact algebraic space, lands in one stage**: every section of the source is
carried to the image of a section of that stage. -/
theorem exists_stage_of_isFiniteType_of_isQuasiCompactSpace
    (hUqc : IsQuasiCompactSpace B S hS U.1) {I : Type u} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ Modules.{u, u} B S hS U.1 U.2) (c : Cocone D) (hc : IsColimit c)
    (hmono : ∀ {i j : I} (f : i ⟶ j), Mono (D.map f))
    {G : Modules.{u, u} B S hS U.1 U.2} (m : G ⟶ c.pt) (hft : G.IsFiniteType) :
    ∃ k, ∀ (Z : (smallEtaleRingedSite B S hS U.1 U.2).Cᵒᵖ) (x : G.val.obj Z),
      ∃ y, (c.ι.app k).val.app Z y = m.val.app Z x := by
  classical
  have : ∀ (i j : I) (f : i ⟶ j), Mono (D.map f) := fun _ _ f => hmono f
  have : EssentiallySmall.{u} (smallEtaleRingedSite B S hS U.1 U.2).C :=
    inferInstanceAs (EssentiallySmall.{u} (SmallEtale B S hS U.1))
  have : IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS U.1 U.2) :=
    SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _
  have : G.IsFiniteType := hft
  set J := (smallEtaleRingedSite B S hS U.1 U.2).J with hJ
  obtain ⟨I₀, W, hW, hgen⟩ :=
    (isFiniteTypeSections_of_isFiniteType (J := J) G).exists_generators
  choose n s hs using hgen
  obtain ⟨U₀, φ, haff, hsurj, het⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS U.1 U.2).1 hUqc
  have hid : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (𝟙 (yoneda.obj U₀)) := by
    have het₀ : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map (𝟙 U₀)) := by
      rw [CategoryTheory.Functor.map_id]
      infer_instance
    simpa using (presheaf_yoneda_map_etale_iff B S hS (𝟙 U₀)).2 het₀
  have hchart : IsEtaleChart B S hS U.1 (CostructuredArrow.mk φ) := by
    have h₀ := het U₀ (𝟙 (yoneda.obj U₀)) hid
    rwa [Category.id_comp] at h₀
  set A : SmallEtale B S hS U.1 := ⟨CostructuredArrow.mk φ, hchart⟩ with hA
  have hAaff : IsAffine
      ((SmallEtale.toOver B S hS U.1 ⋙ BigFppfOver.toScheme B S hS).obj A) := haff
  have hAcov : J.CoversTop (fun _ : PUnit.{u + 2} => A) :=
    SmallEtale.coversTop_of_isSurjective B S hS U.1 U.2 A
      ((presheafSurjective_iff_isSurjective_yoneda B S hS U.1 U.2 U₀ φ).1 hsurj)
  obtain ⟨ι₁, hι₁, V, f₁, hVaff, hle₁, hcov₁⟩ :=
    SmallEtale.exists_finite_affine_refinement B S hS U.1 A hAaff _ (hW A)
  have := hι₁
  choose b hb using fun t => (Sieve.mem_ofObjects_iff W (f₁ t)).1
    (hle₁ _ (Sieve.ofArrows_mk V f₁ t))
  set q : ∀ t, V t ⟶ W (b t) := fun t => (hb t).some with hq
  have hs₁ : ∀ t, GeneratesLocally J G.val
      (fun j => G.val.restrictₛₗ (q t).op (s (b t) j)) := fun t =>
    generatesLocally_restrict (q t) (hs (b t))
  choose Sv hSv hSvlift using fun t : ι₁ =>
    Stacks.Sites.exists_covering_stage_of_finite_family D c hc
      (fun j => m.val.app _ (G.val.restrictₛₗ (q t).op (s (b t) j)))
  choose ι₂ hι₂ V₂ f₂ hV₂aff hle₂ hcov₂ using fun t =>
    SmallEtale.exists_finite_affine_refinement B S hS U.1 (V t) (hVaff t) _ (hSv t)
  have := hι₂
  choose kk zz hzz using fun (t : ι₁) (m : ι₂ t) =>
    hSvlift t (V₂ t m) (f₂ t m) (hle₂ t _ (Sieve.ofArrows_mk _ _ m))
      (isQuasiCompactObject_of_isAffine B S hS U.1 (V₂ t m) (hV₂aff t m))
  obtain ⟨k, hk⟩ :=
    Stacks.Filtered.exists_hom_of_finite (I := I) (fun p : Σ t : ι₁, ι₂ t => kk p.1 p.2)
  have hlift : ∀ (t : ι₁) (l : ι₂ t), ∃ z : Fin (n (b t)) →
        ToType ((D.obj k).val.obj (op (V₂ t l))),
      ∀ j, (c.ι.app k).val.app (op (V₂ t l)) (z j) =
        c.pt.val.map (f₂ t l).op (m.val.app _ (G.val.restrictₛₗ (q t).op (s (b t) j))) := by
    intro t l
    obtain ⟨w⟩ := hk ⟨t, l⟩
    refine ⟨fun j => (D.map w).val.app (op (V₂ t l)) (zz t l j), fun j => ?_⟩
    exact (congrArg (fun ψ : D.obj (kk t l) ⟶ c.pt => ψ.val.app (op (V₂ t l)) (zz t l j))
      (c.w w)).trans (hzz t l j)
  choose z hz using hlift
  have hs₂ : ∀ (t : ι₁) (l : ι₂ t), GeneratesLocally J G.val
      (fun j => G.val.restrictₛₗ (f₂ t l).op
        (G.val.restrictₛₗ (q t).op (s (b t) j))) := fun t l =>
    generatesLocally_restrict (f₂ t l) (hs₁ t)
  have hVcov : J.CoversTop V :=
    Stacks.Sites.coversTop_of_exists_hom
      (Stacks.Sites.coversTop_bind hAcov (fun (_ : PUnit.{u + 2}) t => f₁ t) (fun _ => hcov₁))
      fun p => ⟨p.2, ⟨𝟙 _⟩⟩
  have hcovTop : J.CoversTop (fun p : Σ t : ι₁, ι₂ t => V₂ p.1 p.2) :=
    Stacks.Sites.coversTop_bind hVcov f₂ hcov₂
  refine ⟨k, fun Z x => ?_⟩
  have : Mono (c.ι.app k) := hc.mono_ι_app_of_isFiltered k
  let N := ImageSubsheaf.monoRangeSubmodule (c.ι.app k)
  show m.val.app Z x ∈ N.obj Z
  refine N.isSheaf _ ?_
  refine J.transitive (hcovTop Z.unop) _ fun Y g hg => ?_
  obtain ⟨p, ⟨h⟩⟩ := (Sieve.mem_ofObjects_iff _ g).1 hg
  obtain ⟨Sv', hSv', hlin⟩ := hs₂ p.1 p.2 Y h (G.val.map g.op x)
  refine J.superset_covering (fun Y'' a ha => ?_) hSv'
  obtain ⟨coef, hcoef⟩ := hlin Y'' a ha
  have hstep : ∀ j, (c.ι.app k).val.app (op Y'')
      (coef j • (D.obj k).val.restrictₛₗ (a ≫ h).op (z p.1 p.2 j)) =
        m.val.app (op Y'') (coef j • G.val.restrictₛₗ (a ≫ h).op
          (G.val.restrictₛₗ (f₂ p.1 p.2).op (G.val.restrictₛₗ (q p.1).op (s (b p.1) j)))) := by
    intro j
    rw [map_smul, map_smul]
    congr 1
    have e₁ := PresheafOfModules.naturality_apply (c.ι.app k).val (a ≫ h).op (z p.1 p.2 j)
    have e₂ := PresheafOfModules.naturality_apply m.val (a ≫ h).op
      (G.val.restrictₛₗ (f₂ p.1 p.2).op (G.val.restrictₛₗ (q p.1).op (s (b p.1) j)))
    have e₃ := PresheafOfModules.naturality_apply m.val (f₂ p.1 p.2).op
      (G.val.restrictₛₗ (q p.1).op (s (b p.1) j))
    refine e₁.trans (Eq.trans ?_ e₂.symm)
    exact congrArg (c.pt.val.map (a ≫ h).op) ((hz p.1 p.2 j).trans e₃.symm)
  have hfin : m.val.app (op Y'') (G.val.restrictₛₗ a.op (G.val.map g.op x)) =
      c.pt.val.map (a ≫ g).op (m.val.app Z x) := by
    have e₁ := PresheafOfModules.naturality_apply m.val a.op (G.val.map g.op x)
    have e₂ := PresheafOfModules.naturality_apply m.val g.op x
    refine e₁.trans ?_
    rw [e₂, op_comp]
    exact (c.pt.val.map_comp_apply g.op a.op _).symm
  refine ⟨∑ j, coef j • (D.obj k).val.restrictₛₗ (a ≫ h).op (z p.1 p.2 j), ?_⟩
  refine (map_sum ((c.ι.app k).val.app (op Y'')).hom _ _).trans ?_
  refine (Finset.sum_congr rfl fun j _ => hstep j).trans ?_
  refine (map_sum (m.val.app (op Y'')).hom _ _).symm.trans ?_
  refine Eq.trans ?_ hfin
  exact congrArg (m.val.app (op Y'')) hcoef

end Stage

end AlgebraicGeometry.Space

end
