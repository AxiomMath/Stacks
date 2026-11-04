module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.FiniteCaseTrim
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RestrictionOfScalars
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace

/-!
# A section of a surjective étale space over a finite scheme, after an étale cover

Let `Z → U` be a finite morphism of schemes and let `W` be an algebraic space over `U`
equipped with a surjective étale morphism `w : W → Z`. Stacks 05XQ asserts that `w` admits a
section after a surjective étale base change of `U`: there is a surjective étale `T → U` and a
section `σ : Z_T → W_T` of `W_T → Z_T`.

Sections are recorded as in `StacksFrontier.AlgebraicGeometry.Spaces.SectionSpace`: a section of
`W_T → Z_T` is a morphism `Z_T = T ×_U Z → W` over `Z`, that is, an element of
`AlgebraicGeometry.Space.SectionsOver`.

## The shape of the argument

Choosing a scheme atlas `p : V → W` replaces `w` by the surjective étale morphism of schemes
`V → Z`, which is a one-member étale covering of `Z = Z ×_U U`. Property (B) for the finite
morphism `Z → U`, [Stacks, Tag 04DQ], then supplies an étale covering of `U` over each member
of which `Z` breaks up into pieces mapping to `V`; assembling those pieces gives a morphism
`Z_T → V` over `Z` for `T` a member of the covering. Shrinking each member to an affine open
around a chosen preimage of a point of `U` keeps the sizes below the cutoff of the site, so the
coproduct of these affine opens over all points of `U` is an object of the site, surjective and
étale over `U`, and the local sections glue to a section over it.

Both the base change `T → U` and the section it carries are produced by the same construction
when the base `U` is an object of the big fppf site over a scheme `S` rather than the base
scheme of the site; there the base change of `Z` is the fibre product `T ×_U Z` taken in the
site over `S`. In that form the lemma says that the functor of sections is *surjective over*
`U`: the restriction of scalars `Res_{Z/U}(W)` of Stacks 05YA assigns to `T` a morphism
`T ⟶ U` together with a section of `W_T ⟶ Z_T`, so a section over a base change of `U` which
is surjective on points exhibits `h_T ⟶ U` as a factor of `Res_{Z/U}(W) ⟶ U` on points, and
surjectivity of `Res_{Z/U}(W) ⟶ U` follows from surjectivity of `T → U`.

## Main results

* `AlgebraicGeometry.exists_contains_surjective_etale_section_of_isFinite`: the étale cover of
  the base carrying a section, at the level of schemes.
* `AlgebraicGeometry.Space.exists_surjective_etale_sectionsOver`: **Stacks 05XQ**.
* `AlgebraicGeometry.Space.exists_surjective_etale_section_of_isFinite`: the same statement
  with the base an object of the site over `S`.
* `AlgebraicGeometry.Space.isSurjective_restrictionOfScalars_projection`: **Stacks 05XQ**, as
  surjectivity of `Res_{Z/U}(W) ⟶ U`.

## References

* [Stacks Project, Tag 05XQ](https://stacks.math.columbia.edu/tag/05XQ)
* [Stacks Project, Tag 05YA](https://stacks.math.columbia.edu/tag/05YA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry

/-- A coproduct of schemes indexed by the points of `S`, each of size at most that of `S`, is
again an object of the big fppf site containing `S`: the index set and all the sizes are at
most `2 ^ size S`, which is below the cutoff because the cutoff is a strong limit. -/
private theorem contains_sigma_indexedByPoints (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (Y : S → Scheme.{u}) (hY : ∀ s, (Y s).size ≤ S.size) :
    B.Contains (∐ Y) :=
  (schemeSize_coproduct_le Y ((2 : Cardinal.{u}) ^ S.size)
    (S.aleph0_le_size.trans (Cardinal.cantor S.size).le) (Scheme.mk_le_two_pow_size S)
    fun s => (hY s).trans (Cardinal.cantor S.size).le).trans_lt
      (B.cutoff_isStrongPrelimit hS)

/-- A morphism of the big fppf site over `S` whose image under the Yoneda embedding has the
relatively representable property attached to `Q` has `Q` itself. -/
private theorem map_of_presheaf_yoneda (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (Q : MorphismProperty Scheme.{u}) {V Z : BigFppfOver B S hS}
    {g : yoneda.obj V ⟶ yoneda.obj Z} (m : V ⟶ Z) (hm : yoneda.map m = g)
    (hg : (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf g) :
    Q ((BigFppfOver.toScheme B S hS).map m) :=
  hg.property (𝟙 (yoneda.obj Z)) (𝟙 (yoneda.obj V)) m
    (by simpa [hm] using (IsPullback.of_id_fst (f := yoneda.map m)))

/-- Choosing an atlas `p : V → W` of an algebraic space `W` with a surjective étale morphism
`w : W → Z` to a scheme, `p ≫ w` is `yoneda.map f` for a surjective étale `f : V ⟶ Z`. -/
private theorem exists_atlas_comp_eq_yoneda_map (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {Z : BigFppfOver B S hS} (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (w : W ⟶ yoneda.obj Z) (hW : IsAlgebraicSpace B S hS W)
    (hw_surjective : Space.IsSurjective B S hS w)
    (hw_etale : Space.IsEtale B S hS w) :
    ∃ (V : BigFppfOver B S hS) (p : yoneda.obj V ⟶ W) (f : V ⟶ Z), p ≫ w = yoneda.map f ∧
      Etale ((BigFppfOver.toScheme B S hS).map f) ∧
        Surjective ((BigFppfOver.toScheme B S hS).map f) := by
  obtain ⟨V, p, hp_surjective, hp_etale⟩ := hW.exists_atlas
  have hpw_surjective : Space.IsSurjective B S hS (p ≫ w) := by
    intro z
    obtain ⟨x, hx⟩ := hw_surjective z
    obtain ⟨v, hv⟩ :=
      (Space.presheafSurjective_iff_isSurjective_yoneda B S hS W hW V p).mp hp_surjective x
    refine ⟨v, ?_⟩
    rw [Space.pointsMap_comp]
    change Space.pointsMap B S hS W w (Space.pointsMap B S hS (yoneda.obj V) p v) = z
    rw [hv, hx]
  have hf : yoneda.map (yoneda.preimage (p ≫ w)) = p ≫ w := yoneda.map_preimage (p ≫ w)
  exact ⟨V, p, _, hf.symm, map_of_presheaf_yoneda B S hS @Etale _ hf (hw_etale V p hp_etale),
    map_of_presheaf_yoneda B S hS @Surjective _ hf
      ((Space.presheafSurjective_iff_isSurjective_yoneda B S hS (yoneda.obj Z)
        (isAlgebraicSpace_yoneda B S hS Z) V (p ≫ w)).mpr hpw_surjective)⟩

/-- A lift of `g.left` through `f.left` is the underlying morphism of a lift of `g` through `f`
in the over category. -/
private theorem exists_over_comp_eq {C : Type*} [Category C] {A : C} {X V Z : Over A}
    (f : V ⟶ Z) (g : X ⟶ Z) (a : X.left ⟶ V.left) (h : a ≫ f.left = g.left) :
    ∃ m : X ⟶ V, m ≫ f = g :=
  ⟨Over.homMk a (by rw [← Over.w f, ← Category.assoc, h, Over.w g]),
    Over.OverMorphism.ext h⟩

/-- **A section of a surjective étale cover over each member of an étale covering of the
base.** For `π : Z ⟶ U` finite and `f : X ⟶ Z` surjective étale, property (B) for `π`,
[Stacks, Tag 04DQ], applied to the one-member étale covering `{f}` of `Z = Z ×_U U`, produces
an étale covering of `U` over each member of which `Z` acquires a morphism to `X` over `Z`. -/
private theorem exists_etale_cover_sections_of_isFinite {X Z U : Scheme.{u}} (π : Z ⟶ U)
    [IsFinite π] (f : X ⟶ Z) [Etale f] [Surjective f] :
    ∃ 𝒱 : U.Cover.{u} Scheme.etalePrecoverage, ∀ j,
      ∃ s : pullback π (𝒱.f j ≫ 𝟙 U) ⟶ X, s ≫ f = pullback.fst π (𝒱.f j ≫ 𝟙 U) := by
  classical
  let P := pullback π (𝟙 U)
  let eZ : Z ≅ P := (asIso (pullback.fst π (𝟙 U))).symm
  let fP : X ⟶ P := f ≫ eZ.hom
  have hfP_etale : Etale fP := by
    dsimp [fP]
    infer_instance
  have hfP_surj : Surjective fP := by
    constructor
    intro y
    obtain ⟨x, hx⟩ := f.surjective (eZ.inv y)
    refine ⟨x, ?_⟩
    show eZ.hom (f x) = y
    rw [hx]
    simp
  let 𝒰 : P.Cover.{u} Scheme.etalePrecoverage :=
    { I₀ := PUnit.{u + 1}
      X := fun _ => X
      f := fun _ => fP
      mem₀ := by
        show Presieve.ofArrows (fun _ : PUnit.{u + 1} => X) (fun _ => fP) ∈
          Scheme.etalePrecoverage P
        rw [Presieve.ofArrows_pUnit]
        exact (Scheme.singleton_mem_precoverage_iff (P := @Etale) fP).2
          ⟨hfP_surj.surj, hfP_etale⟩ }
  obtain ⟨𝒱, h𝒱⟩ := Stacks.EtaleCohomology.hasPropertyB_of_isFinite π (𝟙 U) 𝒰
  refine ⟨𝒱, fun j => ?_⟩
  obtain ⟨q, hqfst, -, W, e, a, ha⟩ := h𝒱 j
  refine ⟨e.inv ≫ Sigma.desc a, ?_⟩
  have hsum : Sigma.desc a ≫ f = e.hom ≫ pullback.fst π (𝒱.f j ≫ 𝟙 U) := by
    refine Sigma.hom_ext _ _ fun i => ?_
    have hfprod : fP ≫ pullback.fst π (𝟙 U) = f := by dsimp [fP]; simp [eZ]
    calc
      Sigma.ι W i ≫ Sigma.desc a ≫ f = a i ≫ f := by simp
      _ = a i ≫ fP ≫ pullback.fst π (𝟙 U) := by rw [hfprod]
      _ = (a i ≫ fP) ≫ pullback.fst π (𝟙 U) := (Category.assoc _ _ _).symm
      _ = (Sigma.ι W i ≫ e.hom ≫ q) ≫ pullback.fst π (𝟙 U) := by rw [ha i]
      _ = Sigma.ι W i ≫ e.hom ≫ pullback.fst π (𝒱.f j ≫ 𝟙 U) := by
        rw [Category.assoc, Category.assoc, hqfst]
  rw [Category.assoc, hsum, ← Category.assoc, e.inv_hom_id, Category.id_comp]

/-- **One étale neighbourhood of each point of the base, carrying a section.** The members of
the covering of `AlgebraicGeometry.exists_etale_cover_sections_of_isFinite` are shrunk to an
affine open around a chosen preimage of each point of `U`; being affine and locally of finite
type over `U`, such an open has size at most that of `U`. -/
private theorem exists_pointwise_affine_etale_sections {X Z U : Scheme.{u}} (π : Z ⟶ U)
    [IsFinite π] (f : X ⟶ Z) [Etale f] [Surjective f] :
    ∃ (Y : U → Scheme.{u}) (g : ∀ x, Y x ⟶ U) (s : ∀ x, pullback π (g x) ⟶ X),
      (∀ x, Etale (g x)) ∧ (∀ x, (Y x).size ≤ U.size) ∧ (∀ x, ∃ y : Y x, g x y = x) ∧
        (∀ x, s x ≫ f = pullback.fst π (g x)) := by
  classical
  obtain ⟨𝒱, hsections⟩ := exists_etale_cover_sections_of_isFinite π f
  let : Scheme.JointlySurjective Scheme.etalePrecoverage := by
    refine ⟨fun {X} R hR x => ?_⟩
    change R ∈ Scheme.precoverage @Etale X at hR
    obtain ⟨hJ, -⟩ := hR
    change R ∈ Scheme.jointlySurjectivePrecoverage X at hJ
    rw [Scheme.jointlySurjectivePrecoverage,
      Presieve.mem_comap_jointlySurjectivePrecoverage_iff] at hJ
    exact hJ x
  choose i y hy using 𝒱.exists_eq
  have hA : ∀ x, ∃ A : (𝒱.X (i x)).affineOpens, y x ∈ (A : (𝒱.X (i x)).Opens) := by
    intro x
    obtain ⟨-, ⟨A, hA, rfl⟩, hyA, -⟩ :=
      (𝒱.X (i x)).isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (y x)) isOpen_univ
    exact ⟨⟨A, hA⟩, hyA⟩
  choose A hA_mem using hA
  let Y : U → Scheme.{u} := fun x => (A x : (𝒱.X (i x)).Opens).toScheme
  let a : ∀ x, Y x ⟶ 𝒱.X (i x) := fun x => (A x : (𝒱.X (i x)).Opens).ι
  let g : ∀ x, Y x ⟶ U := fun x => a x ≫ 𝒱.f (i x)
  have hEtale : ∀ x, Etale (g x) := by
    intro x
    have : Etale (𝒱.f (i x)) := 𝒱.map_prop (i x)
    exact Etale.etale_comp _ _
  have hsize : ∀ x, (Y x).size ≤ U.size := by
    intro x
    have : IsAffine (Y x) := (A x).2
    have : Etale (g x) := hEtale x
    exact Scheme.size_le_of_locallyOfFiniteType (g x)
  let q : ∀ x, pullback π (g x) ⟶ pullback π (𝒱.f (i x) ≫ 𝟙 U) := fun x =>
    pullback.map π (g x) π (𝒱.f (i x) ≫ 𝟙 U) (𝟙 Z) (a x) (𝟙 U) (by simp) (by simp [g])
  refine ⟨Y, g, fun x => q x ≫ Classical.choose (hsections (i x)), hEtale, hsize,
    fun x => ⟨⟨y x, hA_mem x⟩, hy x⟩, fun x => ?_⟩
  rw [Category.assoc, Classical.choose_spec (hsections (i x))]
  show pullback.lift (pullback.fst π (g x) ≫ 𝟙 Z) (pullback.snd π (g x) ≫ a x) _ ≫
    pullback.fst π (𝒱.f (i x) ≫ 𝟙 U) = pullback.fst π (g x)
  rw [pullback.lift_fst, Category.comp_id]

/-- **Local sections over the members of a family glue to one over their coproduct.** The base
change of `π` along `Sigma.desc g` is the coproduct of its base changes along the `g i`, the
comparison morphism being an open immersion onto each piece and bijective, so the local
sections assemble. -/
private theorem exists_section_over_sigmaDesc {X Z U : Scheme.{u}} (π : Z ⟶ U) (f : X ⟶ Z)
    (Y : U → Scheme.{u}) (g : ∀ x, Y x ⟶ U) (s : ∀ x, pullback π (g x) ⟶ X)
    (hs : ∀ x, s x ≫ f = pullback.fst π (g x)) :
    ∃ t : pullback π (Sigma.desc g) ⟶ X, t ≫ f = pullback.fst π (Sigma.desc g) := by
  classical
  let τ : (∐ Y) ⟶ U := Sigma.desc g
  let q : ∀ i : U, pullback π (g i) ⟶ pullback π τ := fun i =>
    pullback.map π (g i) π τ (𝟙 Z) (Sigma.ι Y i) (𝟙 U) (by simp) (by simp [τ])
  let d : (∐ fun i : U => pullback π (g i)) ⟶ pullback π τ := Sigma.desc q
  have hdι (i : U) : Sigma.ι (fun i : U => pullback π (g i)) i ≫ d = q i := Sigma.ι_desc q i
  have hqrange (i : U) :
      Set.range (q i) = pullback.snd π τ ⁻¹' Set.range (Sigma.ι Y i) := by
    dsimp [q]
    rw [Scheme.Pullback.range_map]
    simp
  have hd_surj : Surjective d := by
    apply Surjective.sigmaDesc_of_union_range_eq_univ
    refine Set.eq_univ_of_forall fun z => ?_
    obtain ⟨⟨i, v⟩, ha⟩ := (sigmaMk Y).surjective (pullback.snd π τ z)
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    rw [hqrange i]
    exact ⟨v, by simpa using ha⟩
  have hq_open (i : U) : IsOpenImmersion (q i) := by
    dsimp [q]
    infer_instance
  have hdisj {i j : U} (hij : i ≠ j) : Disjoint (Set.range (q i)) (Set.range (q j)) := by
    refine Set.disjoint_left.mpr fun z hz₁ hz₂ => ?_
    rw [hqrange i] at hz₁
    rw [hqrange j] at hz₂
    obtain ⟨y₁, hy₁⟩ := hz₁
    obtain ⟨y₂, hy₂⟩ := hz₂
    have hσ : (sigmaMk Y) ⟨i, y₁⟩ = (sigmaMk Y) ⟨j, y₂⟩ := by
      rw [sigmaMk_mk, sigmaMk_mk]
      exact hy₁.trans hy₂.symm
    exact hij (congrArg Sigma.fst ((sigmaMk Y).injective hσ))
  have hd_injective : Function.Injective d := by
    intro x₁ x₂ hx
    obtain ⟨⟨i, xa⟩, ha⟩ := (sigmaMk fun i : U => pullback π (g i)).surjective x₁
    obtain ⟨⟨j, yb⟩, hb⟩ := (sigmaMk fun i : U => pullback π (g i)).surjective x₂
    have hxa : Sigma.ι (fun i : U => pullback π (g i)) i xa = x₁ := by simpa using ha
    have hyb : Sigma.ι (fun i : U => pullback π (g i)) j yb = x₂ := by simpa using hb
    have hqeq : q i xa = q j yb := by
      rw [← hdι i, ← hdι j, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hxa, hyb, hx]
    have hidx : i = j := by
      by_contra hij
      exact Set.disjoint_left.mp (hdisj hij) ⟨xa, rfl⟩ ⟨yb, hqeq.symm⟩
    subst hidx
    rw [← hxa, ← hyb, (q i).injective hqeq]
  have hd_open : IsOpenImmersion d := by
    refine IsOpenImmersion.of_forall_source_exists d hd_injective fun z => ?_
    obtain ⟨⟨i, v⟩, ha⟩ := (sigmaMk fun i : U => pullback π (g i)).surjective z
    refine ⟨pullback π (g i), Sigma.ι (fun i : U => pullback π (g i)) i, inferInstance,
      ⟨v, by simpa using ha⟩, ?_⟩
    show IsOpenImmersion (Sigma.ι (fun i : U => pullback π (g i)) i ≫ Sigma.desc q)
    rw [hdι]
    exact hq_open i
  have : IsOpenImmersion d := hd_open
  have : Surjective d := hd_surj
  have : IsIso d := isIso_of_isOpenImmersion_of_opensRange_eq_top d
    (by ext z; exact ⟨fun _ => trivial, fun _ => (d.surjective z).imp fun _ h => h⟩)
  let e : (∐ fun i : U => pullback π (g i)) ≅ pullback π τ := asIso d
  have hqfst (i : U) : q i ≫ pullback.fst π τ = pullback.fst π (g i) := by
    show pullback.lift (pullback.fst π (g i) ≫ 𝟙 Z) (pullback.snd π (g i) ≫ Sigma.ι Y i) _ ≫
      pullback.fst π τ = _
    rw [pullback.lift_fst, Category.comp_id]
  refine ⟨e.inv ≫ Sigma.desc s, (cancel_epi d).1 (Sigma.hom_ext _ _ fun i => ?_)⟩
  calc
    Sigma.ι (fun i : U => pullback π (g i)) i ≫ d ≫ (e.inv ≫ Sigma.desc s) ≫ f
        = s i ≫ f := by simp [e]
    _ = q i ≫ pullback.fst π τ := (hs i).trans (hqfst i).symm
    _ = Sigma.ι (fun i : U => pullback π (g i)) i ≫ d ≫ pullback.fst π τ := by
      rw [← Category.assoc, hdι]

/-- **A surjective étale morphism of the site over the base, carrying a section.** For
`π : Z ⟶ U` finite and `f : X ⟶ Z` surjective étale, with `U` a scheme of the big fppf site
`B`, there is a scheme `T` of `B` and a surjective étale `τ : T ⟶ U` together with a morphism
`Z ×_U T ⟶ X` over `Z`.

This is the content of Stacks 05XQ at the level of schemes, with no reference to a site beyond
the size condition: `T` is the coproduct, over the points of `U`, of the affine étale
neighbourhoods of `AlgebraicGeometry.exists_pointwise_affine_etale_sections`, and it lies in `B`
because the cutoff is a strong limit. -/
theorem exists_contains_surjective_etale_section_of_isFinite (B : BigFppfSite.{u})
    (U : Scheme.{u}) (hU : B.Contains U) {X Z : Scheme.{u}} (π : Z ⟶ U) [IsFinite π]
    (f : X ⟶ Z) [Etale f] [Surjective f] :
    ∃ (T : Scheme.{u}) (_ : B.Contains T) (τ : T ⟶ U), Surjective τ ∧ Etale τ ∧
      ∃ t : pullback π τ ⟶ X, t ≫ f = pullback.fst π τ := by
  classical
  obtain ⟨Y, g, s, hg_etale, hg_size, hg_points, hs⟩ :=
    exists_pointwise_affine_etale_sections π f
  obtain ⟨t, ht⟩ := exists_section_over_sigmaDesc π f Y g s hs
  refine ⟨∐ Y, contains_sigma_indexedByPoints B U hU Y hg_size, Sigma.desc g, ?_, ?_, t, ht⟩
  · refine ⟨fun x => ⟨sigmaMk Y ⟨x, Classical.choose (hg_points x)⟩, ?_⟩⟩
    rw [sigmaMk_mk, ← Scheme.Hom.comp_apply, Sigma.ι_desc]
    exact Classical.choose_spec (hg_points x)
  · let : ∀ i, Etale (g i) := hg_etale
    let : IsZariskiLocalAtSource @Etale :=
      HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale) (Q := RingHom.Etale)
    exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale) fun _ => inferInstance

/-- **Stacks 05XQ.** Let `Z → U` be a finite morphism of schemes, let `W` be an algebraic space
over `U` and let `w : W → Z` be surjective and étale. Then there is a surjective étale morphism
`T → U` together with a section of `W_T → Z_T`. -/
@[stacks 05XQ]
theorem Space.exists_surjective_etale_sectionsOver (B : BigFppfSite.{u}) (U : Scheme.{u})
    (hU : B.Contains U) (Z : BigFppfOver B U hU) [IsFinite (B.inclusion.map Z.hom)]
    (W : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u) (w : W ⟶ yoneda.obj Z)
    (hW : IsAlgebraicSpace B U hU W) (hw_surjective : Space.IsSurjective B U hU w)
    (hw_etale : Space.IsEtale B U hU w) :
    ∃ T : BigFppfOver B U hU, Surjective (B.inclusion.map T.hom) ∧
      Etale (B.inclusion.map T.hom) ∧ Nonempty (Space.SectionsOver B U hU Z T W w) := by
  classical
  obtain ⟨V, p, f, hf, hf_etale, hf_surjective⟩ :=
    exists_atlas_comp_eq_yoneda_map B U hU W w hW hw_surjective hw_etale
  let π : B.inclusion.obj Z.left ⟶ B.inclusion.obj (B.obj hU) := B.inclusion.map Z.hom
  let fₛ : B.inclusion.obj V.left ⟶ B.inclusion.obj Z.left := B.inclusion.map f.left
  let : IsFinite π := ‹IsFinite (B.inclusion.map Z.hom)›
  let : Etale fₛ := hf_etale
  let : Surjective fₛ := hf_surjective
  obtain ⟨T₀, hT, τ, hτ₀_surjective, hτ₀_etale, t, ht⟩ :=
    exists_contains_surjective_etale_section_of_isFinite B
      (B.inclusion.obj (B.obj hU)) hU π fₛ
  let τB : B.inclusion.obj (B.obj hT) ⟶ B.inclusion.obj (B.obj hU) := τ
  let T : BigFppfOver B U hU := Over.mk (B.inclusion.preimage τB)
  have hτB : B.inclusion.map T.hom = τ := B.inclusion.map_preimage τB
  have hτ_surjective : Surjective (B.inclusion.map T.hom) := by rwa [hτB]
  have hτ_etale : Etale (B.inclusion.map T.hom) := by rwa [hτB]
  let : HasBinaryProducts (BigFppfOver B U hU) :=
    Over.ConstructProducts.over_binaryProduct_of_pullback
  let τ' : B.inclusion.obj T.left ⟶ B.inclusion.obj (B.obj hU) := B.inclusion.map T.hom
  let e₀ : B.inclusion.obj (T ⨯ Z).left ≅ pullback π τ' :=
    B.inclusion.mapIso (Over.prodLeftIsoPullback T Z) ≪≫
      PreservesPullback.iso B.inclusion T.hom Z.hom ≪≫ (pullbackSymmetry π τ').symm
  let t' : pullback π τ' ⟶ B.inclusion.obj V.left := (pullback.congrHom rfl hτB).hom ≫ t
  have ht' : t' ≫ fₛ = pullback.fst π τ' := by
    rw [Category.assoc, ht]
    simp only [pullback.congrHom, pullback.map, Category.comp_id, asIso_hom]
    exact pullback.lift_fst _ _ _
  let α : (T ⨯ Z).left ⟶ V.left := B.inclusion.preimage (e₀.hom ≫ t')
  have hαf : B.inclusion.map α ≫ fₛ = B.inclusion.map ((prod.snd : T ⨯ Z ⟶ Z).left) := by
    rw [B.inclusion.map_preimage, Category.assoc, ht']
    calc
      e₀.hom ≫ pullback.fst π τ'
          = (B.inclusion.mapIso (Over.prodLeftIsoPullback T Z)).hom ≫
            (PreservesPullback.iso B.inclusion T.hom Z.hom).hom ≫ pullback.snd τ' π := by
        simp [e₀]
      _ = B.inclusion.map ((Over.prodLeftIsoPullback T Z).hom ≫ pullback.snd T.hom Z.hom) := by
        rw [PreservesPullback.iso_hom_snd]
        simp only [Functor.mapIso_hom, ← Functor.map_comp]
      _ = B.inclusion.map ((prod.snd : T ⨯ Z ⟶ Z).left) := by
        rw [Over.prodLeftIsoPullback_hom_snd]
  obtain ⟨m, hm⟩ := exists_over_comp_eq f prod.snd α
    (B.inclusion.map_injective (by simpa [fₛ] using hαf))
  refine ⟨T, hτ_surjective, hτ_etale,
    ⟨⟨(PreservesLimitPair.iso yoneda T Z).inv ≫ yoneda.map m ≫ p, ?_⟩⟩⟩
  calc
    ((PreservesLimitPair.iso yoneda T Z).inv ≫ yoneda.map m ≫ p) ≫ w
        = (PreservesLimitPair.iso yoneda T Z).inv ≫ yoneda.map m ≫ yoneda.map f := by
      rw [Category.assoc, Category.assoc, hf]
    _ = (PreservesLimitPair.iso yoneda T Z).inv ≫ yoneda.map (prod.snd : T ⨯ Z ⟶ Z) := by
      rw [← yoneda.map_comp, hm]
    _ = prod.snd := PreservesLimitPair.iso_inv_snd yoneda T Z

/-- **Stacks 05XQ, with the base an object of the site over `S`.** Let `ζ : Z ⟶ U` be a
morphism of the big fppf site of `S` whose underlying morphism of schemes is finite, let `W` be
an algebraic space over `S` and let `w : W ⟶ Z` be surjective and étale. Then there is a
morphism `τ : T ⟶ U` of the site, surjective and étale on underlying schemes, together with a
section of `W_T ⟶ Z_T` over `Z_T = T ×_U Z`, recorded as a morphism `T ×_U Z ⟶ W` over `Z`.

The scheme-level content is that of
`AlgebraicGeometry.Space.exists_surjective_etale_sectionsOver`, where the base is the base
scheme of the site; here the base change `Z_T` is the fibre product over `U` inside the site
over `S` rather than a product in the site over `U`. -/
theorem Space.exists_surjective_etale_section_of_isFinite (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {U Z : BigFppfOver B S hS} (ζ : Z ⟶ U)
    [IsFinite ((BigFppfOver.toScheme B S hS).map ζ)]
    (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (w : W ⟶ yoneda.obj Z)
    (hW : IsAlgebraicSpace B S hS W) (hw_surjective : Space.IsSurjective B S hS w)
    (hw_etale : Space.IsEtale B S hS w) :
    ∃ (T : BigFppfOver B S hS) (τ : T ⟶ U),
      Surjective ((BigFppfOver.toScheme B S hS).map τ) ∧
        Etale ((BigFppfOver.toScheme B S hS).map τ) ∧
        ∃ σ : yoneda.obj (pullback τ ζ) ⟶ W, σ ≫ w = yoneda.map (pullback.snd τ ζ) := by
  classical
  obtain ⟨V, p, f, hf, hf_etale, hf_surjective⟩ :=
    exists_atlas_comp_eq_yoneda_map B S hS W w hW hw_surjective hw_etale
  let π : (BigFppfOver.toScheme B S hS).obj Z ⟶ (BigFppfOver.toScheme B S hS).obj U :=
    (BigFppfOver.toScheme B S hS).map ζ
  let fₛ : (BigFppfOver.toScheme B S hS).obj V ⟶ (BigFppfOver.toScheme B S hS).obj Z :=
    (BigFppfOver.toScheme B S hS).map f
  let : IsFinite π := ‹IsFinite ((BigFppfOver.toScheme B S hS).map ζ)›
  let : Etale fₛ := hf_etale
  let : Surjective fₛ := hf_surjective
  obtain ⟨T₀, hT₀, τ₀, hτ₀_surjective, hτ₀_etale, t, ht⟩ :=
    exists_contains_surjective_etale_section_of_isFinite B
      ((BigFppfOver.toScheme B S hS).obj U) U.left.2 π fₛ
  let αT : B.obj hT₀ ⟶ U.left := B.inclusion.preimage τ₀
  let T : BigFppfOver B S hS := Over.mk (αT ≫ U.hom)
  let τ : T ⟶ U := Over.homMk αT rfl
  have hτ : (BigFppfOver.toScheme B S hS).map τ = τ₀ :=
    B.inclusion.map_preimage (X := B.obj hT₀) (Y := U.left) τ₀
  have hτ_surjective : Surjective ((BigFppfOver.toScheme B S hS).map τ) := by rwa [hτ]
  have hτ_etale : Etale ((BigFppfOver.toScheme B S hS).map τ) := by rwa [hτ]
  let t' : pullback π ((BigFppfOver.toScheme B S hS).map τ) ⟶
      (BigFppfOver.toScheme B S hS).obj V := (pullback.congrHom rfl hτ).hom ≫ t
  have ht' : t' ≫ fₛ = pullback.fst π ((BigFppfOver.toScheme B S hS).map τ) := by
    rw [Category.assoc, ht]
    simp only [pullback.congrHom, pullback.map, Category.comp_id, asIso_hom]
    exact pullback.lift_fst _ _ _
  have hcomparison :
      ((PreservesPullback.iso (BigFppfOver.toScheme B S hS) τ ζ).hom ≫
            (pullbackSymmetry ((BigFppfOver.toScheme B S hS).map τ)
              ((BigFppfOver.toScheme B S hS).map ζ)).hom) ≫
          pullback.fst ((BigFppfOver.toScheme B S hS).map ζ)
            ((BigFppfOver.toScheme B S hS).map τ) =
        (BigFppfOver.toScheme B S hS).map (pullback.snd τ ζ) := by
    rw [Category.assoc, pullbackSymmetry_hom_comp_fst, PreservesPullback.iso_hom_snd]
  let α : (pullback τ ζ).left ⟶ V.left :=
    B.inclusion.preimage (((PreservesPullback.iso (BigFppfOver.toScheme B S hS) τ ζ).hom ≫
      (pullbackSymmetry ((BigFppfOver.toScheme B S hS).map τ)
        ((BigFppfOver.toScheme B S hS).map ζ)).hom) ≫ t')
  have hαf : B.inclusion.map α ≫ fₛ = (BigFppfOver.toScheme B S hS).map (pullback.snd τ ζ) := by
    rw [B.inclusion.map_preimage, Category.assoc, ht', hcomparison]
  obtain ⟨m, hm⟩ := exists_over_comp_eq f (pullback.snd τ ζ) α
    (B.inclusion.map_injective (by rw [B.inclusion.map_comp]; exact hαf))
  refine ⟨T, τ, hτ_surjective, hτ_etale, yoneda.map m ≫ p, ?_⟩
  calc
    (yoneda.map m ≫ p) ≫ w = yoneda.map m ≫ yoneda.map f := by rw [Category.assoc, hf]
    _ = yoneda.map (m ≫ f) := (yoneda.map_comp m f).symm
    _ = yoneda.map (pullback.snd τ ζ) := by rw [hm]

/-- **Stacks 05XQ.** Let `ζ : Z ⟶ U` be a morphism of the big fppf site of `S` whose underlying
morphism of schemes is finite, let `W` be an algebraic space over `S` and let `w : W ⟶ Z` be
surjective and étale. Then the restriction of scalars `Res_{Z/U}(W) ⟶ U` of Stacks 05YA — the
functor assigning to `T` a morphism `T ⟶ U` together with a section of `W_T ⟶ Z_T` — is
surjective.

A point of `U` is hit by a point of `Res_{Z/U}(W)` because the base change `τ : T ⟶ U` of
`AlgebraicGeometry.Space.exists_surjective_etale_section_of_isFinite` carries a section, so
`h_T ⟶ U` factors through `Res_{Z/U}(W)`, and `τ` is surjective on points. -/
@[stacks 05XQ "surjectivity of `Res_{Z/U}(W) ⟶ U` for `Z ⟶ U` finite"]
theorem Space.isSurjective_restrictionOfScalars_projection (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {U Z : BigFppfOver B S hS} (ζ : Z ⟶ U)
    [IsFinite ((BigFppfOver.toScheme B S hS).map ζ)] (W : AlgebraicSpaces B S hS)
    (w : W ⟶ (schemeSpace Z : AlgebraicSpaces B S hS))
    (hw_surjective : Space.IsSurjective B S hS w.hom)
    (hw_etale : Space.IsEtale B S hS w.hom) :
    Space.IsSurjective B S hS
      (Space.restrictionOfScalars B S hS w
        (ObjectProperty.homMk (yoneda.map ζ) :
          (schemeSpace Z : AlgebraicSpaces B S hS) ⟶
            schemeSpace U)).projection := by
  classical
  obtain ⟨T, τ, hτ_surjective, -, σ, hσ⟩ :=
    Space.exists_surjective_etale_section_of_isFinite B S hS ζ W.obj w.hom W.property
      hw_surjective hw_etale
  let ζ' : (⟨yoneda.obj Z, isAlgebraicSpace_yoneda B S hS Z⟩ : AlgebraicSpaces B S hS) ⟶
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ := ObjectProperty.homMk (yoneda.map ζ)
  have hover : ((PreservesPullback.iso yoneda τ ζ).inv ≫ σ) ≫ w.hom =
      pullback.snd (yoneda.map τ) (yoneda.map ζ) :=
    (Category.assoc _ _ _).trans ((congrArg ((PreservesPullback.iso yoneda τ ζ).inv ≫ ·) hσ).trans
      (PreservesPullback.iso_inv_snd yoneda τ ζ))
  let pr : Space.RestrictionPair B S hS w ζ' (yoneda.obj T) :=
    { base := yoneda.map τ
      lift := (PreservesPullback.iso yoneda τ ζ).inv ≫ σ
      over := hover }
  have hbase : pr.base = yoneda.map τ := rfl
  have hproj : yonedaEquiv.symm
        (((Space.restrictionOfScalars B S hS w ζ').pairEquiv T).symm pr) ≫
      (Space.restrictionOfScalars B S hS w ζ').projection = yoneda.map τ := by
    refine yonedaEquiv.injective ?_
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply,
      (Space.restrictionOfScalars B S hS w ζ').projection_pairEquiv T _,
      Equiv.apply_symm_apply, hbase, yonedaEquiv_yoneda_map]
  have hpoints : Function.Surjective (Space.pointsMap B S hS (yoneda.obj T) (yoneda.map τ)) :=
    Space.isSurjective_yoneda_map B S hS τ hτ_surjective
  rw [← hproj, Space.pointsMap_comp] at hpoints
  exact hpoints.of_comp

/-- **Stacks 05XQ, relative to a base in the site.** Let `π : Z ⟶ T` be a morphism of the big fppf
site of `U` whose underlying morphism of schemes is finite, and let `f : V ⟶ Z` be a morphism of
the site whose underlying morphism of schemes is surjective and étale. Then there is a morphism
`g : T' ⟶ T` of the site, surjective and étale on underlying schemes, over which `f` acquires a
section: a morphism `Z ×_T T' ⟶ V` lifting the projection to `Z`.

This is the scheme-theoretic content of Stacks 05XQ, with the base `U` of
`AlgebraicGeometry.Space.exists_surjective_etale_sectionsOver` replaced by an arbitrary object
`T` of the site. -/
theorem Space.exists_surjective_etale_lift_of_isFinite (B : BigFppfSite.{u}) (U : Scheme.{u})
    (hU : B.Contains U) {T Z V : BigFppfOver B U hU} (π : Z ⟶ T)
    [IsFinite ((BigFppfOver.toScheme B U hU).map π)] (f : V ⟶ Z)
    [Surjective ((BigFppfOver.toScheme B U hU).map f)]
    [Etale ((BigFppfOver.toScheme B U hU).map f)] :
    ∃ (T' : BigFppfOver B U hU) (g : T' ⟶ T) (t : pullback π g ⟶ V),
      Surjective ((BigFppfOver.toScheme B U hU).map g) ∧
        Etale ((BigFppfOver.toScheme B U hU).map g) ∧ t ≫ f = pullback.fst π g := by
  classical
  let G := BigFppfOver.toScheme B U hU
  obtain ⟨T₀, hT₀, τ, hτ_surj, hτ_et, t, ht⟩ :=
    exists_contains_surjective_etale_section_of_isFinite B (G.obj T) T.left.property
      (G.map π) (G.map f)
  let τB : B.inclusion.obj (B.obj hT₀) ⟶ B.inclusion.obj T.left := τ
  let T' : BigFppfOver B U hU := Over.mk (B.inclusion.preimage τB ≫ T.hom)
  let gC : T' ⟶ T := Over.homMk (B.inclusion.preimage τB)
  have hgC : G.map gC = τ := B.inclusion.map_preimage τB
  have hg_surj : Surjective (G.map gC) := by rwa [hgC]
  have hg_et : Etale (G.map gC) := by rwa [hgC]
  -- the underlying scheme of the fibre product in the site is the fibre product of schemes
  let e : G.obj (pullback π gC) ≅ pullback (G.map π) τ :=
    PreservesPullback.iso G π gC ≪≫ pullback.congrHom rfl hgC
  have he : e.hom ≫ pullback.fst (G.map π) τ = G.map (pullback.fst π gC) := by
    simp only [e, Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.lift_fst,
      Category.comp_id]
    exact PreservesPullback.iso_hom_fst G π gC
  let tS : G.obj (pullback π gC) ⟶ G.obj V := e.hom ≫ t
  have htS : tS ≫ G.map f = G.map (pullback.fst π gC) := by
    rw [Category.assoc, ht, he]
  obtain ⟨tC, htC⟩ := exists_over_comp_eq f (pullback.fst π gC) (B.inclusion.preimage tS)
    (B.inclusion.map_injective (by rwa [Functor.map_comp, B.inclusion.map_preimage]))
  exact ⟨T', gC, tC, hg_surj, hg_et, htC⟩

end AlgebraicGeometry

end
