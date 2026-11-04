module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.ClosedSubsetIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Sections of a module supported on a subset of an algebraic space

The sections of an `𝒪_F`-module whose support on an étale chart maps into a fixed subset `T`
of the points of `F` form a submodule of the module sheaf on the small étale site, in the
sense of `SheafOfModules.Submodule`: the membership condition is stable under restriction and
is local on covering sieves.

## Main definitions

* `AlgebraicGeometry.Space.moduleAddSheaf` is the abelian sheaf underlying a module sheaf on
  the small étale site, at the site's own topology.
* `AlgebraicGeometry.Space.SectionSupportedIn` is the condition on a section of a module over
  an étale chart that its support maps into a fixed subset of the points of `F`.
* `AlgebraicGeometry.Space.supportedSectionsSubmodule` is the resulting submodule of the
  module sheaf.
* `AlgebraicGeometry.Space.chartPointsMap` is the map `|φ| : |W| → |F|` on points of an étale
  chart `φ : W → F`, read on the scheme underlying the chart.

## Main results

* `AlgebraicGeometry.Space.supportedSectionsSubmoduleData` constructs that submodule together
  with the criterion that identifies its sections over every chart.
* `AlgebraicGeometry.Space.SmallEtale.exists_mem_arrows_pointsMap_eq`: every covering sieve of
  the small étale site of `F` is jointly surjective on the points of its target.
* `AlgebraicGeometry.Space.isCompact_preimage_chartPointsMap_range`: the preimage in an affine
  étale chart of the points of an open subspace whose inclusion is quasi-compact is
  quasi-compact.
* `AlgebraicGeometry.Space.exists_fg_ideal_zeroLocus_eq_preimage_chartPointsMap`: for a closed
  `T ⊆ |F|` whose complement is the point set of an open subspace with quasi-compact inclusion,
  the preimage of `T` on an affine étale chart is the zero locus of a finitely generated ideal of
  the sections over that chart.

## References

* [Stacks Project, Tag 0859](https://stacks.math.columbia.edu/tag/0859)
* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
* [Stacks Project, Tag 07ZP](https://stacks.math.columbia.edu/tag/07ZP)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-! ### Covering sieves of the small étale site are jointly surjective on points -/

/-- Every covering sieve of the small étale site of `F` is jointly surjective on points: each
point of the target chart is the image of a point of the source of some member of the sieve. -/
theorem SmallEtale.exists_mem_arrows_pointsMap_eq
    {U : SmallEtale B S hS F} {R : Sieve U}
    (hR : R ∈ SmallEtale.topology B S hS F U)
    (x : points B S hS (yoneda.obj ((SmallEtale.toOver B S hS F).obj U))) :
    ∃ (V : SmallEtale B S hS F) (f : V ⟶ U), R.arrows f ∧
      ∃ y : points B S hS (yoneda.obj ((SmallEtale.toOver B S hS F).obj V)),
        pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS F).obj V))
          (yoneda.map ((SmallEtale.toOver B S hS F).map f)) y = x := by
  rw [Precoverage.mem_toGrothendieck_iff] at hR
  induction hR with
  | of U R hR =>
      obtain ⟨E, rfl, hE⟩ := hR
      obtain ⟨i, y, hy⟩ := exists_pointsMap_eq_of_isCovering B S hS F U E hE x
      exact ⟨E.X i, E.f i, ⟨E.X i, 𝟙 _, E.f i, ⟨i⟩, by simp⟩, y, hy⟩
  | top U =>
      refine ⟨U, 𝟙 U, trivial, x, ?_⟩
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
      exact congrFun (pointsMap_id B S hS _) x
  | pullback U T _ V g ih =>
      obtain ⟨Z, h, hh, z, hz⟩ := ih (pointsMap B S hS
        (yoneda.obj ((SmallEtale.toOver B S hS F).obj V))
        (yoneda.map ((SmallEtale.toOver B S hS F).map g)) x)
      obtain ⟨w, hw, -⟩ := exists_points_of_isPullback B S hS
        ((IsPullback.of_hasPullback g h).map (SmallEtale.toOver B S hS F ⋙ yoneda)) x z hz.symm
      refine ⟨Limits.pullback g h, Limits.pullback.fst g h, ?_, w, hw⟩
      simpa [Limits.pullback.condition] using T.downward_closed hh (Limits.pullback.snd g h)
  | transitive U T T' _ _ ih₁ ih₂ =>
      obtain ⟨Z, g, hg, z, hz⟩ := ih₁ x
      obtain ⟨W, k, hk, w, hw⟩ := ih₂ hg z
      refine ⟨W, k ≫ g, hk, w, ?_⟩
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
        pointsMap_comp_apply, hw, hz]

/-! ### Sections supported in a subset -/

variable (hF : IsAlgebraicSpace B S hS F)

/-- The abelian sheaf on the small étale site of `F` underlying an `𝒪_F`-module, at the topology
of the site itself rather than at the `J` projection of the ringed site. -/
noncomputable def moduleAddSheaf (G : Modules.{u, m} B S hS F hF) :
    Sheaf (SmallEtale.topology B S hS F) AddCommGrpCat.{m} :=
  (SheafOfModules.toSheaf _).obj G

/-- A section is supported in `T` when its support on its chart maps into `T`. -/
def SectionSupportedIn (T : Set (points B S hS F))
    (G : Modules.{u, m} B S hS F hF)
    (W : SmallEtale B S hS F) (s : G.val.obj (op W)) : Prop :=
  supportOfSection B S hS F (moduleAddSheaf B S hS F hF G) W s ⊆
    pointsMap B S hS _ W.1.hom ⁻¹' T

variable {B S hS F hF} {T : Set (points B S hS F)} {G : Modules.{u, m} B S hS F hF}

/-- The zero section is supported in every subset: its support is empty. -/
theorem sectionSupportedIn_zero (W : SmallEtale B S hS F) :
    SectionSupportedIn B S hS F hF T G W 0 :=
  (supportOfSection_zero B S hS F (moduleAddSheaf B S hS F hF G) W).le.trans
    (Set.empty_subset _)

/-- Sections supported in a subset are closed under addition. -/
theorem sectionSupportedIn_add {W : SmallEtale B S hS F} {a b : G.val.obj (op W)}
    (ha : SectionSupportedIn B S hS F hF T G W a)
    (hb : SectionSupportedIn B S hS F hF T G W b) :
    SectionSupportedIn B S hS F hF T G W (a + b) := by
  intro x hx
  rcases supportOfSection_add_subset B S hS F (moduleAddSheaf B S hS F hF G) W a b hx with h | h
  exacts [ha h, hb h]

/-- A section every restriction of which is killed whenever a supported section is killed is
itself supported. -/
theorem sectionSupportedIn_of_restrict_eq_zero {W : SmallEtale B S hS F}
    (a b : G.val.obj (op W)) (ha : SectionSupportedIn B S hS F hF T G W a)
    (h : ∀ (V : SmallEtale B S hS F) (f : V ⟶ W),
      G.val.map f.op a = 0 → G.val.map f.op b = 0) :
    SectionSupportedIn B S hS F hF T G W b :=
  fun _ hx => ha (supportOfSection_subset_of_restrict B S hS F
    (moduleAddSheaf B S hS F hF G) W a b h hx)

/-- Sections supported in a subset are closed under the action of the structure sheaf. -/
theorem sectionSupportedIn_smul {W : SmallEtale B S hS F}
    (c : ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS F hF).O)).obj.obj (op W))
    {a : G.val.obj (op W)} (ha : SectionSupportedIn B S hS F hF T G W a) :
    SectionSupportedIn B S hS F hF T G W (c • a) :=
  sectionSupportedIn_of_restrict_eq_zero a (c • a) ha fun _ f h0 =>
    (G.val.map_smul f.op c a).trans (by rw [h0, smul_zero])

/-- A point lies in the support of a restriction exactly when its image lies in the support. -/
private theorem mem_supportOfSection_restrict_iff {V W : SmallEtale B S hS F} (f : V ⟶ W)
    (s : G.val.obj (op W)) (y : points B S hS (yoneda.obj ((SmallEtale.toOver B S hS F).obj V))) :
    y ∈ supportOfSection B S hS F (moduleAddSheaf B S hS F hF G) V (G.val.map f.op s) ↔
      pointsMap B S hS _ (yoneda.map f.hom.left) y ∈
        supportOfSection B S hS F (moduleAddSheaf B S hS F hF G) W s := by
  have := supportOfSection_restrict B S hS F (moduleAddSheaf B S hS F hF G) W s V f
  exact Set.ext_iff.1 this y

/-- Sections supported in a subset are stable under restriction to a chart over the given
one: the support of the restriction is the preimage of the support. -/
theorem sectionSupportedIn_restrict {W₁ W₂ : SmallEtale B S hS F} (g : W₂ ⟶ W₁)
    (s : G.val.obj (op W₁)) (hs : SectionSupportedIn B S hS F hF T G W₁ s) :
    SectionSupportedIn B S hS F hF T G W₂ (G.val.map g.op s) := by
  intro y hy
  have h2 : pointsMap B S hS _ W₁.obj.hom (pointsMap B S hS _ (yoneda.map g.hom.left) y) ∈ T :=
    hs ((mem_supportOfSection_restrict_iff g s y).1 hy)
  rwa [pointsMap_chart_hom B S hS F g y] at h2

/-- Being supported in a subset is local on covering sieves: a section whose restriction to
every member of a covering sieve is supported in `T` is itself supported in `T`. -/
theorem sectionSupportedIn_of_sieve {W : SmallEtale B S hS F} (s : G.val.obj (op W))
    {R : Sieve W} (hR : R ∈ SmallEtale.topology B S hS F W)
    (h : ∀ ⦃V : SmallEtale B S hS F⦄ (f : V ⟶ W), R.arrows f →
      SectionSupportedIn B S hS F hF T G V (G.val.map f.op s)) :
    SectionSupportedIn B S hS F hF T G W s := by
  intro x hx
  obtain ⟨V, f, hf, y, hy⟩ := SmallEtale.exists_mem_arrows_pointsMap_eq B S hS F hR x
  rw [Set.mem_preimage, ← hy]
  have h3 : pointsMap B S hS _ V.obj.hom y ∈ T :=
    h f hf ((mem_supportOfSection_restrict_iff f s y).2 (hy ▸ hx))
  rwa [← pointsMap_chart_hom B S hS F f y] at h3

/-! ### The subsheaf of supported sections -/

variable (B S hS F hF)

/-- The subsheaf of sections supported in `T`, together with its defining local membership
criterion. -/
@[stacks 0859 "supported-section subsheaf", stacks 085A "the subsheaf of sections supported on T"]
noncomputable def supportedSectionsSubmoduleData (T : Set (points B S hS F))
    (G : Modules.{u, m} B S hS F hF) :
    {N : G.Submodule // ∀ (W : SmallEtale B S hS F)
      (s : G.val.obj (op W)),
      s ∈ N.toSubmodule.obj (op W) ↔
        SectionSupportedIn B S hS F hF T G W s} :=
  ⟨{ toSubmodule :=
       { obj := fun W =>
           { carrier := {s | SectionSupportedIn B S hS F hF T G W.unop s}
             add_mem' := sectionSupportedIn_add
             zero_mem' := sectionSupportedIn_zero _
             smul_mem' := fun c _ ha => sectionSupportedIn_smul c ha }
         map := fun f _ hs => sectionSupportedIn_restrict f.unop _ hs }
     isSheaf := fun {_} s hs => sectionSupportedIn_of_sieve s hs fun _ _ hf => hf },
    fun _ _ => Iff.rfl⟩

/-- The submodule sheaf whose local sections are supported in `T`. -/
noncomputable def supportedSectionsSubmodule (T : Set (points B S hS F))
    (G : Modules.{u, m} B S hS F hF) : G.Submodule :=
  (supportedSectionsSubmoduleData B S hS F hF T G).1

/-- A section of `G` over an étale chart lies in the supported-section subsheaf exactly when
its support maps into `T`. -/
theorem mem_supportedSectionsSubmodule_iff (T : Set (points B S hS F))
    (G : Modules.{u, m} B S hS F hF) (W : SmallEtale B S hS F) (s : G.val.obj (op W)) :
    s ∈ (supportedSectionsSubmodule B S hS F hF T G).toSubmodule.obj (op W) ↔
      SectionSupportedIn B S hS F hF T G W s :=
  (supportedSectionsSubmoduleData B S hS F hF T G).2 W s

/-! ### The closed subset on an affine chart -/

section FiniteTypeIdeal

attribute [local instance] pointTopology

variable {B S hS F}

/-- The map `|φ| : |W| → |F|` on points induced by an étale chart `φ : W → F` of `F`, read on
the scheme underlying the chart through the comparison homeomorphism
`AlgebraicGeometry.Space.schemePointsHomeomorph`. -/
noncomputable def chartPointsMap (W : SmallEtale B S hS F) :
    chartScheme W → points B S hS F :=
  pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS F).obj W)) W.1.hom ∘
    (schemePointsHomeomorph B S hS ((SmallEtale.toOver B S hS F).obj W)).symm

/-- The preimage of a set of points of `F` in the scheme underlying an étale chart is the
preimage of its preimage on the points of the chart. -/
theorem preimage_chartPointsMap (W : SmallEtale B S hS F) (A : Set (points B S hS F)) :
    chartPointsMap W ⁻¹' A =
      (schemePointsHomeomorph B S hS ((SmallEtale.toOver B S hS F).obj W)).symm ⁻¹'
        (pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS F).obj W)) W.1.hom ⁻¹' A) :=
  rfl

/-- The map on points induced by an étale chart is continuous. -/
theorem continuous_chartPointsMap (W : SmallEtale B S hS F) :
    Continuous (chartPointsMap W) :=
  (continuous_pointsMap B S hS W.1.hom).comp
    (schemePointsHomeomorph B S hS ((SmallEtale.toOver B S hS F).obj W)).symm.continuous

/-- The preimage in an affine étale chart of the points of an open subspace with quasi-compact
inclusion is quasi-compact. -/
theorem isCompact_preimage_chartPointsMap_range (hF : IsAlgebraicSpace B S hS F)
    {U : Subfunctor F} (hU : IsOpenSubspace B S hS U) (hUqc : IsQuasiCompact B S hS U.ι)
    (W : SmallEtale B S hS F) (hW : IsAffine (chartScheme W)) :
    IsCompact (chartPointsMap W ⁻¹' Set.range (pointsMap B S hS U.toFunctor U.ι)) := by
  have hAalg : IsAlgebraicSpace B S hS (yoneda.obj ((SmallEtale.toOver B S hS F).obj W)) :=
    isAlgebraicSpace_yoneda B S hS _
  have hAqc : IsQuasiCompactSpace B S hS (yoneda.obj ((SmallEtale.toOver B S hS F).obj W)) :=
    isQuasiCompactSpace_yoneda_of_isAffine B S hS _ hW
  have hPalg : IsAlgebraicSpace B S hS (pullback W.1.hom U.ι) :=
    isAlgebraicSpace_pullback B S hS W.1.hom U.ι hAalg hU.1 hF
  have hPcompact : CompactSpace (points B S hS (pullback W.1.hom U.ι)) :=
    (isQuasiCompactSpace_iff_compactSpace_points B S hS _ hPalg).1
      (hUqc _ hAalg hAqc W.1.hom)
  have hsq : IsPullback (pullback.fst W.1.hom U.ι) (pullback.snd W.1.hom U.ι) W.1.hom U.ι :=
    IsPullback.of_hasPullback _ _
  have hrange : Set.range (pointsMap B S hS (pullback W.1.hom U.ι)
        (pullback.fst W.1.hom U.ι)) =
      pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS F).obj W)) W.1.hom ⁻¹'
        Set.range (pointsMap B S hS U.toFunctor U.ι) := by
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      rw [Set.mem_preimage, ← pointsMap_comp_apply, hsq.w, pointsMap_comp_apply]
      exact Set.mem_range_self _
    · rintro ⟨y, hy⟩
      obtain ⟨w, hw, -⟩ := exists_point_of_isPullback_presheaf B S hS hsq x y hy.symm
      exact ⟨w, hw⟩
  rw [preimage_chartPointsMap, ← hrange]
  exact ((schemePointsHomeomorph B S hS _).symm.isCompact_preimage).2
    (isCompact_range (continuous_pointsMap B S hS (pullback.fst W.1.hom U.ι)))

/-- Let `T ⊆ |F|` be a closed subset of the points of an algebraic space `F`, and let `U ⊆ F` be
the open subspace whose points are the complement of `T`. If the inclusion `U → F` is
quasi-compact then on every affine étale chart `φ : W → F` the preimage `|φ|⁻¹(T)` is the zero
locus of a finitely generated ideal of `𝒪_F(W)`. -/
@[stacks 0859 "part (1): a finite type ideal cutting out the closed subset on an affine chart"]
theorem exists_fg_ideal_zeroLocus_eq_preimage_chartPointsMap (hF : IsAlgebraicSpace B S hS F)
    {T : Set (points B S hS F)} (hT : IsClosed T) {U : Subfunctor F}
    (hU : IsOpenSubspace B S hS U)
    (hUT : Set.range (pointsMap B S hS U.toFunctor U.ι) = Tᶜ)
    (hUqc : IsQuasiCompact B S hS U.ι) (W : SmallEtale B S hS F)
    (hW : IsAffine (chartScheme W)) :
    ∃ I : Ideal Γ(chartScheme W, ⊤), I.FG ∧
      chartPointsMap W ⁻¹' T =
        (chartScheme W).zeroLocus (U := ⊤) (I : Set Γ(chartScheme W, ⊤)) := by
  have hclosed : IsClosed (chartPointsMap W ⁻¹' T) :=
    hT.preimage (continuous_chartPointsMap W)
  have hcompl : (chartPointsMap W ⁻¹' T)ᶜ =
      chartPointsMap W ⁻¹' Set.range (pointsMap B S hS U.toFunctor U.ι) := by
    rw [hUT, Set.preimage_compl]
  have hcpt : IsCompact (chartPointsMap W ⁻¹' T)ᶜ :=
    hcompl ▸ isCompact_preimage_chartPointsMap_range hF hU hUqc W hW
  have hretro : IsRetrocompact (chartPointsMap W ⁻¹' T)ᶜ :=
    (QuasiSeparatedSpace.isRetrocompact_iff_isCompact hclosed.isOpen_compl).2 hcpt
  obtain ⟨I, hIFG, hI⟩ := exists_fg_ideal_zeroLocus_eq_inter (chartScheme W)
    (chartPointsMap W ⁻¹' T) hclosed hretro ⊤ (isAffineOpen_top (chartScheme W))
  exact ⟨I, hIFG, by simpa using hI⟩

end FiniteTypeIdeal

end AlgebraicGeometry.Space

end
