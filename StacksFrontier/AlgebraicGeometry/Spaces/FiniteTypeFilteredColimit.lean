module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjects
public import StacksFrontier.AlgebraicGeometry.Spaces.FreeModuleSections
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ModuleFilteredColimitSections

/-!
# A finite type filtered colimit of modules on a quasi-compact algebraic space is a stage

Let `X` be a quasi-compact algebraic space and let `D` be a filtered diagram of `𝒪_X`-modules
whose transition maps are monomorphisms.  If the colimit of `D` is of finite type then the
colimit is already one of its stages: some component `c.ι.app i` of the colimit cocone is an
isomorphism.

This is the analogue for algebraic spaces of the second assertion of Stacks 01BB, which is
stated there for a sheaf of modules on a quasi-compact topological space.

## Main results

* `AlgebraicGeometry.Space.exists_isIso_ι_of_isFiniteType_of_isQuasiCompactSpace`: a filtered
  colimit of `𝒪_X`-modules with monomorphic transition maps which is of finite type on a
  quasi-compact algebraic space `X` equals one of its stages.

## Implementation notes

Monomorphy of the components of the colimit cocone is formal: the small étale site of an
algebraic space is essentially small, so its category of `𝒪_X`-modules is Grothendieck
abelian, and `CategoryTheory.Limits.IsColimit.mono_ι_app_of_isFiltered` applies.

Surjectivity is where the geometry enters, and it replaces the stalk argument of the source,
which does not transport to the small étale site.  Quasi-compactness of `X` gives a single
*affine* étale chart covering the final object (Stacks 03H6), finite type gives a covering
family carrying finitely many generating sections, and over an affine chart every covering
sieve is refined by a *finite* family of affine charts
(`AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_refinement`).  Two such refinements
produce a finite family of affine charts which covers the final object, over each member of
which finitely many sections generate the colimit and each of those sections comes from a
stage: the second refinement is taken inside the sieve supplied by
`Stacks.Sites.exists_covering_stage_of_finite_family`, whose hypothesis is quasi-compactness
of the object, and affine charts are quasi-compact objects
(`AlgebraicGeometry.Space.isQuasiCompactObject_of_isAffine`).  Finitely many sections in total
have a common stage `k`, and local generation then exhibits `c.ι.app k` as locally surjective,
hence epimorphic.

The module universe is the universe of the schemes, which is where the structure sheaf itself
lives and the only one at which `AlgebraicGeometry.Space.Modules` is abelian and cocomplete;
see `StacksFrontier/AlgebraicGeometry/Spaces/ModulesAbelian.lean`.

## References

* [Stacks Project, Tag 01BB](https://stacks.math.columbia.edu/tag/01BB)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.SheafOfModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U : AlgebraicSpaces B S hS}

/-- **The analogue for algebraic spaces of Stacks 01BB, second assertion.** A filtered colimit
of `𝒪_X`-modules whose transition maps are monomorphisms and whose colimit is of finite type on
a quasi-compact algebraic space `X` is already one of its stages. -/
theorem exists_isIso_ι_of_isFiniteType_of_isQuasiCompactSpace
    (hUqc : IsQuasiCompactSpace B S hS U.1) {I : Type u} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ Modules.{u, u} B S hS U.1 U.2) (c : Cocone D) (hc : IsColimit c)
    (hmono : ∀ {i j : I} (f : i ⟶ j), Mono (D.map f)) (hft : c.pt.IsFiniteType) :
    ∃ i, IsIso (c.ι.app i) := by
  classical
  have : ∀ (i j : I) (f : i ⟶ j), Mono (D.map f) := fun _ _ f => hmono f
  have : EssentiallySmall.{u} (smallEtaleRingedSite B S hS U.1 U.2).C :=
    inferInstanceAs (EssentiallySmall.{u} (SmallEtale B S hS U.1))
  have : IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS U.1 U.2) :=
    SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _
  have : c.pt.IsFiniteType := hft
  set J := (smallEtaleRingedSite B S hS U.1 U.2).J with hJ
  -- finite type, in the sectionwise form
  obtain ⟨I₀, W, hW, hgen⟩ :=
    (isFiniteTypeSections_of_isFiniteType (J := J) c.pt).exists_generators
  choose n s hs using hgen
  -- an affine étale chart covering the final object
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
    rw [Category.id_comp] at h₀
    exact h₀
  set A : SmallEtale B S hS U.1 := ⟨CostructuredArrow.mk φ, hchart⟩ with hA
  have hAaff : IsAffine
      ((SmallEtale.toOver B S hS U.1 ⋙ BigFppfOver.toScheme B S hS).obj A) := haff
  have hAcov : J.CoversTop (fun _ : PUnit.{u + 2} => A) :=
    SmallEtale.coversTop_of_isSurjective B S hS U.1 U.2 A
      ((presheafSurjective_iff_isSurjective_yoneda B S hS U.1 U.2 U₀ φ).1 hsurj)
  -- first refinement: a finite affine family over `A`, each member over some `W b`
  obtain ⟨ι₁, hι₁, V, f₁, hVaff, hle₁, hcov₁⟩ :=
    SmallEtale.exists_finite_affine_refinement B S hS U.1 A hAaff _ (hW A)
  have := hι₁
  choose b hb using fun t => (Sieve.mem_ofObjects_iff W (f₁ t)).1
    (hle₁ _ (Sieve.ofArrows_mk V f₁ t))
  set q : ∀ t, V t ⟶ W (b t) := fun t => (hb t).some with hq
  have hs₁ : ∀ t, GeneratesLocally J c.pt.val
      (fun j => c.pt.val.restrictₛₗ (q t).op (s (b t) j)) := fun t =>
    generatesLocally_restrict (q t) (hs (b t))
  -- the sieve on `V t` over which the finitely many generators come from one stage
  choose Sv hSv hSvlift using fun t : ι₁ =>
    Stacks.Sites.exists_covering_stage_of_finite_family D c hc
      (fun j => c.pt.val.restrictₛₗ (q t).op (s (b t) j))
  -- second refinement: a finite affine family over each `V t`, inside that sieve
  choose ι₂ hι₂ V₂ f₂ hV₂aff hle₂ hcov₂ using fun t =>
    SmallEtale.exists_finite_affine_refinement B S hS U.1 (V t) (hVaff t) _ (hSv t)
  have := hι₂
  -- over each member of the second refinement every generator comes from a stage
  choose kk zz hzz using fun (t : ι₁) (m : ι₂ t) =>
    hSvlift t (V₂ t m) (f₂ t m) (hle₂ t _ (Sieve.ofArrows_mk _ _ m))
      (isQuasiCompactObject_of_isAffine B S hS U.1 (V₂ t m) (hV₂aff t m))
  obtain ⟨k, hk⟩ :=
    Stacks.Filtered.exists_hom_of_finite (I := I) (fun p : Σ t : ι₁, ι₂ t => kk p.1 p.2)
  have hlift : ∀ (t : ι₁) (m : ι₂ t), ∃ z : Fin (n (b t)) →
        ToType ((D.obj k).val.obj (op (V₂ t m))),
      ∀ j, (c.ι.app k).val.app (op (V₂ t m)) (z j) =
        c.pt.val.restrictₛₗ (f₂ t m).op (c.pt.val.restrictₛₗ (q t).op (s (b t) j)) := by
    intro t m
    obtain ⟨w⟩ := hk ⟨t, m⟩
    refine ⟨fun j => (D.map w).val.app (op (V₂ t m)) (zz t m j), fun j => ?_⟩
    rw [show (c.ι.app k).val.app (op (V₂ t m)) ((D.map w).val.app (op (V₂ t m)) (zz t m j)) =
        (c.ι.app (kk t m)).val.app (op (V₂ t m)) (zz t m j) from
      congrArg (fun ψ : D.obj (kk t m) ⟶ c.pt => ψ.val.app (op (V₂ t m)) (zz t m j)) (c.w w)]
    exact hzz t m j
  choose z hz using hlift
  have hs₂ : ∀ (t : ι₁) (m : ι₂ t), GeneratesLocally J c.pt.val
      (fun j => c.pt.val.restrictₛₗ (f₂ t m).op
        (c.pt.val.restrictₛₗ (q t).op (s (b t) j))) := fun t m =>
    generatesLocally_restrict (f₂ t m) (hs₁ t)
  -- the second refinement is a finite family of affine charts covering the final object
  have hVcov : J.CoversTop V :=
    Stacks.Sites.coversTop_of_exists_hom
      (Stacks.Sites.coversTop_bind hAcov (fun (_ : PUnit.{u + 2}) t => f₁ t) (fun _ => hcov₁))
      fun p => ⟨p.2, ⟨𝟙 _⟩⟩
  have hcovTop : J.CoversTop (fun p : Σ t : ι₁, ι₂ t => V₂ p.1 p.2) :=
    Stacks.Sites.coversTop_bind hVcov f₂ hcov₂
  -- the stage `k` is already the whole colimit
  refine ⟨k, ?_⟩
  have : Mono (c.ι.app k) := hc.mono_ι_app_of_isFiltered k
  have : Epi (c.ι.app k) := by
    refine EpiMono.epi_of_isLocallySurjective _ ⟨fun {Z} x => ?_⟩
    refine J.transitive (hcovTop Z) _ fun Y g hg => ?_
    obtain ⟨p, ⟨h⟩⟩ := (Sieve.mem_ofObjects_iff _ g).1 hg
    obtain ⟨Sv', hSv', hlin⟩ := hs₂ p.1 p.2 Y h (c.pt.val.map g.op x)
    refine J.superset_covering ?_ hSv'
    intro Y'' a ha
    obtain ⟨coef, hcoef⟩ := hlin Y'' a ha
    have hstep : ∀ j, (c.ι.app k).val.app (op Y'')
        (coef j • (D.obj k).val.restrictₛₗ (a ≫ h).op (z p.1 p.2 j)) =
          coef j • c.pt.val.restrictₛₗ (a ≫ h).op
            (c.pt.val.restrictₛₗ (f₂ p.1 p.2).op
              (c.pt.val.restrictₛₗ (q p.1).op (s (b p.1) j))) := fun j =>
      calc (c.ι.app k).val.app (op Y'')
              (coef j • (D.obj k).val.restrictₛₗ (a ≫ h).op (z p.1 p.2 j))
            = coef j • (c.ι.app k).val.app (op Y'')
                ((D.obj k).val.restrictₛₗ (a ≫ h).op (z p.1 p.2 j)) :=
              ((c.ι.app k).val.app (op Y'')).hom.map_smul _ _
        _ = coef j • c.pt.val.restrictₛₗ (a ≫ h).op
                ((c.ι.app k).val.app (op (V₂ p.1 p.2)) (z p.1 p.2 j)) :=
              congrArg (fun w : ToType (c.pt.val.obj (op Y'')) => coef j • w)
                (PresheafOfModules.naturality_apply (c.ι.app k).val (a ≫ h).op (z p.1 p.2 j))
        _ = coef j • c.pt.val.restrictₛₗ (a ≫ h).op
                (c.pt.val.restrictₛₗ (f₂ p.1 p.2).op
                  (c.pt.val.restrictₛₗ (q p.1).op (s (b p.1) j))) :=
              congrArg (fun w => coef j • c.pt.val.restrictₛₗ (a ≫ h).op w) (hz p.1 p.2 j)
    have hfin : c.pt.val.map (a ≫ g).op x =
        c.pt.val.restrictₛₗ a.op (c.pt.val.map g.op x) := by
      rw [op_comp]
      exact c.pt.val.map_comp_apply g.op a.op x
    refine ⟨∑ j, coef j • (D.obj k).val.restrictₛₗ (a ≫ h).op (z p.1 p.2 j), ?_⟩
    change (c.ι.app k).val.app (op Y'')
        (∑ j, coef j • (D.obj k).val.restrictₛₗ (a ≫ h).op (z p.1 p.2 j)) =
      c.pt.val.map (a ≫ g).op x
    exact ((map_sum ((c.ι.app k).val.app (op Y'')).hom _ _).trans
      (Finset.sum_congr rfl fun j _ => hstep j)).trans (hcoef.trans hfin.symm)
  exact isIso_of_mono_of_epi _

end AlgebraicGeometry.Space

end
