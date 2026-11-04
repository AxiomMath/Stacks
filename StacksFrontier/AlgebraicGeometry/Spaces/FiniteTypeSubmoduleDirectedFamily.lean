module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.FreeModuleSections
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.CategoryTheory.Sites.Modules.SubmoduleSupLocal
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ModuleFilteredColimitSections

/-!
# A finite type submodule inside a directed family of submodules, on a quasi-compact space

Let `X` be a quasi-compact algebraic space, `M` an `𝒪_X`-module and `(N_i)` a directed family of
submodules of `M` such that every local section of `M` lies, locally, in some `N_i`.  Then every
submodule of `M` of finite type is contained in a single `N_i`.

This is the containment form of the second assertion of Stacks 01BB on the small étale site: the
family need not be indexed by a small category, and no colimit is formed.

## Main results

* `AlgebraicGeometry.Space.exists_le_of_isFiniteType_of_isQuasiCompactSpace`: the containment.

## Implementation notes

Quasi-compactness of `X` gives one affine étale chart covering the final object (Stacks 03H6).
Over it, the covering family carrying the finitely many local generators of the finite type
submodule is refined by finitely many affine charts
(`AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_refinement`).  Each restricted
generator is a section over an affine, hence quasi-compact, chart lying locally in members of the
family, so it lies in one member (`Stacks.SheafOfModules.exists_mem_of_isQuasiCompactObject`);
finitely many generators in all have a common member, and local generation puts the whole
submodule into it.

## References

* [Stacks Project, Tag 01BB](https://stacks.math.columbia.edu/tag/01BB)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 090H](https://stacks.math.columbia.edu/tag/090H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.SheafOfModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U : AlgebraicSpaces B S hS}

/-- **A finite type submodule lies in one member of a locally exhausting directed family.**  On a
quasi-compact algebraic space, let `(N_i)` be a directed family of submodules of an `𝒪_X`-module
`M` such that every local section of `M` lies, along every arrow of some covering sieve, in some
`N_i`.  Then every submodule of `M` of finite type is contained in one `N_i`. -/
theorem exists_le_of_isFiniteType_of_isQuasiCompactSpace
    (hUqc : IsQuasiCompactSpace B S hS U.1) {M : Modules.{u, u} B S hS U.1 U.2}
    {ι : Type*} [Nonempty ι] (N : ι → M.Submodule) (hN : Directed (· ≤ ·) N)
    (hloc : ∀ (V : SmallEtale B S hS U.1) (x : M.val.obj (op V)),
      ∃ T : Sieve V, T ∈ SmallEtale.topology B S hS U.1 V ∧
        ∀ ⦃Y : SmallEtale B S hS U.1⦄ (f : Y ⟶ V), T f →
          ∃ i, M.val.map f.op x ∈ (N i).obj (op Y))
    (G : M.Submodule) (hG : G.toSheafOfModules.IsFiniteType) :
    ∃ i, G ≤ N i := by
  classical
  set J := (smallEtaleRingedSite B S hS U.1 U.2).J
  -- finite type, in the sectionwise form
  have : ∀ X : (smallEtaleRingedSite B S hS U.1 U.2).C,
      HasSheafify (J.over X) AddCommGrpCat.{u} := by
    change ∀ X : SmallEtale B S hS U.1,
      HasSheafify ((SmallEtale.topology B S hS U.1).over X) AddCommGrpCat.{u}
    infer_instance
  obtain ⟨I₀, W, hW, hgen⟩ :=
    (isFiniteTypeSections_of_isFiniteType (J := J) G.toSheafOfModules).exists_generators
  choose n s hs using hgen
  -- an affine étale chart covering the final object
  obtain ⟨U₀, φ, haff, hsurj, het⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS U.1 U.2).1 hUqc
  have hchart : IsEtaleChart B S hS U.1 (CostructuredArrow.mk φ) := by
    have h := het U₀ (𝟙 (yoneda.obj U₀)) (presheaf_etale_id B S hS U₀)
    rwa [Category.id_comp] at h
  set A : SmallEtale B S hS U.1 := ⟨CostructuredArrow.mk φ, hchart⟩
  have hAaff : IsAffine
      ((SmallEtale.toOver B S hS U.1 ⋙ BigFppfOver.toScheme B S hS).obj A) := haff
  have hAcov : J.CoversTop (fun _ : PUnit.{u + 2} => A) :=
    SmallEtale.coversTop_of_isSurjective B S hS U.1 U.2 A
      ((presheafSurjective_iff_isSurjective_yoneda B S hS U.1 U.2 U₀ φ).1 hsurj)
  -- a finite affine family over `A`, each member over some `W b`
  obtain ⟨ι₁, hι₁, V, f₁, hVaff, hle₁, hcov₁⟩ :=
    SmallEtale.exists_finite_affine_refinement B S hS U.1 A hAaff _ (hW A)
  choose b hb using fun t => (Sieve.mem_ofObjects_iff W (f₁ t)).1
    (hle₁ _ (Sieve.ofArrows_mk V f₁ t))
  set q : ∀ t, V t ⟶ W (b t) := fun t => (hb t).some
  -- the restricted generators, as sections of `M`
  let σ : ∀ t (j : Fin (n (b t))), M.val.obj (op (V t)) := fun t j =>
    (G.toSheafOfModules.val.restrictₛₗ (q t).op (s (b t) j)).1
  have hσ (p : Σ t : ι₁, Fin (n (b t))) : ∃ i, σ p.1 p.2 ∈ (N i).obj (op (V p.1)) :=
    have ⟨T, hT, hTN⟩ := hloc (V p.1) (σ p.1 p.2)
    exists_mem_of_isQuasiCompactObject N hN
      (isQuasiCompactObject_of_isAffine B S hS U.1 (V p.1) (hVaff p.1)) _ T hT hTN
  choose i hi using hσ
  have := Fintype.ofFinite ι₁
  obtain ⟨i₀, hi₀⟩ := hN.finset_le (Finset.univ.image i)
  have hσ₀ : ∀ t j, σ t j ∈ (N i₀).obj (op (V t)) := fun t j =>
    _root_.SheafOfModules.Submodule.le_iff.1
      (hi₀ (i ⟨t, j⟩) (Finset.mem_image_of_mem _ (Finset.mem_univ _))) _ (hi ⟨t, j⟩)
  -- local generation by the restricted generators
  have hs₁ : ∀ t, GeneratesLocally J G.toSheafOfModules.val
      (fun j => G.toSheafOfModules.val.restrictₛₗ (q t).op (s (b t) j)) := fun t =>
    generatesLocally_restrict (q t) (hs (b t))
  have hVcov : J.CoversTop V :=
    Stacks.Sites.coversTop_of_exists_hom
      (Stacks.Sites.coversTop_bind hAcov (fun (_ : PUnit.{u + 2}) t => f₁ t) (fun _ => hcov₁))
      fun p => ⟨p.2, ⟨𝟙 _⟩⟩
  refine ⟨i₀, _root_.SheafOfModules.Submodule.le_iff.2 fun Z x hx => ?_⟩
  let x' : G.toSheafOfModules.val.obj Z := ⟨x, hx⟩
  refine (N i₀).isSheaf x (J.transitive (hVcov Z.unop) _ fun Y g hg => ?_)
  obtain ⟨t, ⟨h⟩⟩ := (Sieve.mem_ofObjects_iff _ g).1 hg
  obtain ⟨S', hS', hlin⟩ := hs₁ t Y h (G.toSheafOfModules.val.map g.op x')
  refine J.superset_covering (fun Y'' a ha => ?_) hS'
  obtain ⟨coef, hcoef⟩ := hlin Y'' a ha
  change M.val.map (a ≫ g).op x ∈ (N i₀).obj (op Y'')
  rw [op_comp, M.val.map_comp_apply]
  change (G.toSheafOfModules.val.restrictₛₗ a.op (G.toSheafOfModules.val.map g.op x')).1 ∈ _
  rw [← congrArg Subtype.val hcoef]
  have hP : (∑ j, coef j • G.toSheafOfModules.val.restrictₛₗ (a ≫ h).op
      (G.toSheafOfModules.val.restrictₛₗ (q t).op (s (b t) j))) ∈
        ((N i₀).obj (op Y'')).comap (G.ι.val.app (op Y'')).hom :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.mem_comap.2 ((N i₀).map_mem (a ≫ h).op (hσ₀ t j)))
  exact hP

end AlgebraicGeometry.Space

end
