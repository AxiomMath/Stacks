module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectsSmall
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleTypesUnderEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupDominating
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceFromQuasicoherentIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraDegreeZero
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.LargestQuasicoherentSubmodule
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ClosedSubspaceApproximation
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeOnSiteKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectsDirected

/-!
# Closed subspaces as limits of finitely presented closed subspaces, from Stacks 0829

Let `Y` be an algebraic space over a scheme `S` and `X ⊆ Y` a closed subspace.  Stacks 0A0U writes
`X` as a directed inverse limit of closed subspaces of `Y` of finite presentation over `Y`, the
transition morphisms and the projections being closed immersions.  Its proof: the ideal sheaf
`𝓘 ⊆ 𝒪_Y` of `X` is the filtered colimit of its finite type quasi-coherent submodules `𝓘_i`
(Stacks 0829), each `𝓘_i` cuts out a closed subspace `X_i` of finite presentation over `Y`, and
`X = lim X_i`.  This file carries that proof out with the conclusion of Stacks 0829 for `Y` as the
one hypothesis; quasi-compactness and quasi-separatedness of `Y` enter only through it.

## Main results

* `AlgebraicGeometry.Space.mem_localClosure_subobjectUnion`: when a quasi-coherent module is the
  colimit of its finite type quasi-coherent submodules, each of its sections lies locally in one
  of them.
* `AlgebraicGeometry.Space.exists_mem_range_of_isAffine`: over an affine étale chart each section
  lies in a single one: a finite affine refinement with jointly faithfully flat restrictions, a
  common upper bound in the directed system, and descent of membership in the range of a map of
  modules cartesian on affine charts.
* `AlgebraicGeometry.Space.definingIdealAt_chartOpens_eq`: the defining ideal of a closed subspace
  at the chart cut out by an affine open of an étale chart is the chart ideal sheaf restricted to
  that open.
* `AlgebraicGeometry.Space.isFinitePresentation_subobjectStage`: the closed subspace cut out by a
  finite type quasi-coherent submodule of the ideal sheaf is of finite presentation over `Y`.
* `hasClosedSubspaceApproximation_of_isColimit_finiteTypeQuasicoherentSubobjectCocone`: **the
  source's proof of Stacks 0A0U**, from the conclusion of Stacks 0829 for `Y`.

## Implementation notes

The index of the approximation is a small model of the directed system of finite type
quasi-coherent submodules of `𝓘`, preordered by inclusion of the submodules it names: the
conclusion asks for an index in `Type u`, and those submodules form only an essentially small
category.

No `stacks` attribute is carried: the hypothesis is the conclusion of Stacks 0829, which on a
quasi-compact and quasi-separated space is not yet available here unconditionally.

## References

* [Stacks Project, Tag 0A0U](https://stacks.math.columbia.edu/tag/0A0U)
* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
* [Stacks Project, Tag 084Q](https://stacks.math.columbia.edu/tag/084Q)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

section Union

variable (M : Modules.{u, u} B S hS F hF) [M.IsQuasicoherentOnSite]

omit [M.IsQuasicoherentOnSite] in
/-- A finite type quasi-coherent submodule contained in another has its range contained in the
range of the other. -/
theorem range_arrow_le_range_arrow_of_hom {G G' : FiniteTypeQuasicoherentSubobject B S hS F hF M}
    (f : G ⟶ G') (X : (SmallEtale B S hS F)ᵒᵖ) :
    LinearMap.range (G.obj.arrow.val.app X).hom ≤ LinearMap.range (G'.obj.arrow.val.app X).hom := by
  rintro _ ⟨x, rfl⟩
  refine ⟨(Subobject.underlying.map f.hom).val.app X x, ?_⟩
  rw [← Subobject.underlying_arrow f.hom]
  rfl

/-- The sections of `M` lying in the range of some finite type quasi-coherent submodule. -/
noncomputable def subobjectUnion : M.val.Submodule where
  obj X :=
    { carrier := {s | ∃ G : FiniteTypeQuasicoherentSubobject B S hS F hF M,
        s ∈ LinearMap.range (G.obj.arrow.val.app X).hom}
      zero_mem' := by
        have := isFiltered_finiteTypeQuasicoherentSubobject B S hS F hF M
        exact ⟨(IsFiltered.nonempty (C := FiniteTypeQuasicoherentSubobject B S hS F hF M)).some,
          Submodule.zero_mem _⟩
      add_mem' := by
        rintro a b ⟨G₁, h₁⟩ ⟨G₂, h₂⟩
        have := isFiltered_finiteTypeQuasicoherentSubobject B S hS F hF M
        exact ⟨IsFiltered.max G₁ G₂, Submodule.add_mem _
          (range_arrow_le_range_arrow_of_hom M (IsFiltered.leftToMax G₁ G₂) _ h₁)
          (range_arrow_le_range_arrow_of_hom M (IsFiltered.rightToMax G₁ G₂) _ h₂)⟩
      smul_mem' := by
        rintro r a ⟨G, h⟩
        exact ⟨G, Submodule.smul_mem _ r h⟩ }
  map {X Y} g := by
    rintro _ ⟨G, x, rfl⟩
    exact ⟨G, _, PresheafOfModules.naturality_apply G.obj.arrow.val g x⟩

/-- **Every section of `M` lies locally in a finite type quasi-coherent submodule**, as soon as
`M` is the colimit of the canonical diagram of those submodules. -/
theorem mem_localClosure_subobjectUnion
    (hc : IsColimit (finiteTypeQuasicoherentSubobjectCocone B S hS F hF M))
    (X : (SmallEtale B S hS F)ᵒᵖ) (s : M.val.obj X) :
    s ∈ (Stacks.SheafOfModules.localClosure M (subobjectUnion M)).obj X := by
  let P := Stacks.SheafOfModules.localClosure M (subobjectUnion M)
  have hmem : ∀ (G : FiniteTypeQuasicoherentSubobject B S hS F hF M) (Y) (m),
      G.obj.arrow.val.app Y m ∈ P.obj Y := fun G Y m => by
    rw [Stacks.SheafOfModules.mem_localClosure_obj]
    refine GrothendieckTopology.superset_covering _ (fun Z g _ => ?_)
      (GrothendieckTopology.top_mem _ Y.unop)
    exact ⟨G, _, PresheafOfModules.naturality_apply G.obj.arrow.val g.op m⟩
  let lift : ∀ G : FiniteTypeQuasicoherentSubobject B S hS F hF M,
      (G.obj : Modules.{u, u} B S hS F hF) ⟶ P.toSheafOfModules := fun G =>
    Stacks.SheafOfModules.sheafFactorThruSubmodule G.obj.arrow P (hmem G)
  let c : Cocone (finiteTypeQuasicoherentSubobjectFunctor B S hS F hF M) :=
    { pt := P.toSheafOfModules
      ι :=
        { app := lift
          naturality := fun G G' f => by
            rw [← cancel_mono P.ι]
            simp only [Functor.const_obj_obj, Functor.const_obj_map, lift]
            exact Subobject.underlying_arrow f.hom } }
  have hr : hc.desc c ≫ P.ι = 𝟙 M := by
    refine hc.hom_ext fun G => ?_
    rw [← Category.assoc, hc.fac]
    change lift G ≫ P.ι = G.obj.arrow ≫ 𝟙 M
    rw [Category.comp_id]
    exact Stacks.SheafOfModules.sheafFactorThruSubmodule_ι G.obj.arrow P (hmem G)
  have e : (P.ι.val.app X) ((hc.desc c).val.app X s) = s :=
    congrArg (fun φ : M ⟶ M => φ.val.app X s) hr
  rw [← e]
  exact ((hc.desc c).val.app X s).2

/-- **Over an affine étale chart, every section of `M` lies in a single finite type
quasi-coherent submodule**, when `M` is the colimit of those submodules.  Locally the section
lies in one; a finite affine refinement with jointly faithfully flat restrictions picks finitely
many of them, a common upper bound contains all of those local memberships, and membership in the
range of a map of modules cartesian on affine charts descends along the refinement. -/
theorem exists_mem_range_of_isAffine
    (hc : IsColimit (finiteTypeQuasicoherentSubobjectCocone B S hS F hF M))
    {W : SmallEtale B S hS F}
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W))
    (s : M.val.obj (op W)) :
    ∃ G : FiniteTypeQuasicoherentSubobject B S hS F hF M,
      s ∈ LinearMap.range (G.obj.arrow.val.app (op W)).hom := by
  classical
  have := isFiltered_finiteTypeQuasicoherentSubobject B S hS F hF M
  have hs := mem_localClosure_subobjectUnion M hc (op W) s
  obtain ⟨n, z, φ, hzaff, hzT, hff⟩ :=
    exists_finite_affine_faithfullyFlat_pi_le B S hS F hF hW
      (T := (subobjectUnion M).toSubfunctor.sieveOfSection s) hs
  have hloc : ∀ i, ∃ G : FiniteTypeQuasicoherentSubobject B S hS F hF M,
      M.val.map (φ i).op s ∈ LinearMap.range (G.obj.arrow.val.app (op (z i))).hom :=
    fun i => hzT i
  choose Gi hGi using hloc
  let O : Finset (FiniteTypeQuasicoherentSubobject B S hS F hF M) := Finset.univ.image Gi
  let G := IsFiltered.sup O ∅
  have hto : ∀ i, Gi i ⟶ G := fun i =>
    IsFiltered.toSup O ∅ (Finset.mem_image_of_mem Gi (Finset.mem_univ i))
  refine ⟨G, ?_⟩
  let A := chartRing B S hS F hF W
  let Bi : Fin n → Type u := fun i => chartRing B S hS F hF (z i)
  let algI : ∀ i, Algebra A (Bi i) := fun i => chartAlgebra (hF := hF) (φ i)
  let NG : Modules.{u, u} B S hS F hF := (G.obj : Modules.{u, u} B S hS F hF)
  let modP : ∀ i, Module A (NG.val.obj (op (z i))) := fun i => chartSectionsModule NG (φ i)
  let modN : ∀ i, Module A (M.val.obj (op (z i))) := fun i => chartSectionsModule M (φ i)
  have towP : ∀ i, IsScalarTower A (Bi i) (NG.val.obj (op (z i))) :=
    fun i => chartSections_isScalarTower NG (φ i)
  have towN : ∀ i, IsScalarTower A (Bi i) (M.val.obj (op (z i))) :=
    fun i => chartSections_isScalarTower M (φ i)
  have hFF : Module.FaithfullyFlat A (∀ i, Bi i) := hff
  let bT : NG.val.obj (op W) →ₗ[A] M.val.obj (op W) := (G.obj.arrow.val.app (op W)).hom
  let bW : ∀ i, NG.val.obj (op (z i)) →ₗ[Bi i] M.val.obj (op (z i)) :=
    fun i => (G.obj.arrow.val.app (op (z i))).hom
  let rP : ∀ i, NG.val.obj (op W) →ₗ[A] NG.val.obj (op (z i)) :=
    fun i => chartRestrictLinear NG (φ i)
  let rN : ∀ i, M.val.obj (op W) →ₗ[A] M.val.obj (op (z i)) :=
    fun i => chartRestrictLinear M (φ i)
  have hsq : ∀ (i) (q : NG.val.obj (op W)), rN i (bT q) = bW i (rP i q) := fun i q =>
    (PresheafOfModules.naturality_apply G.obj.arrow.val (φ i).op q).symm
  have hP : ∀ i, Function.Surjective ((rP i).liftBaseChange (Bi i)) := fun i =>
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF NG G.property.1 W (z i) hW
      (hzaff i) (φ i)).2
  have hN : ∀ i, Function.Injective ((rN i).liftBaseChange (Bi i)) := fun i =>
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF M ‹_› W (z i) hW
      (hzaff i) (φ i)).1
  have hn : ∀ i, rN i s ∈ LinearMap.range (bW i) := fun i =>
    range_arrow_le_range_arrow_of_hom M (hto i) _ (hGi i)
  exact Module.BaseChange.mem_range_of_forall_mem_range_of_liftBaseChange A Bi bT bW rP rN hsq
    hP hN hn

end Union

/-! ### Ideal sheaves on a chart, read on its affine opens -/

section IdealSheaf

/-- A property of an affine open transfers along an equality of the underlying opens. -/
private theorem affineOpens_property_of_eq {V : Scheme.{u}} {P : V.affineOpens → Prop}
    {A A' : V.affineOpens} (h : A'.1 = A.1) (hA : P A') : P A := by
  obtain rfl : A' = A := Subtype.ext h
  exact hA

/-- An inclusion of ideal sheaves on a scheme can be tested after restriction to the affine
opens, on global sections there. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.le_of_forall_comap_ι_le {V : Scheme.{u}}
    {I J : V.IdealSheafData}
    (h : ∀ A : V.affineOpens,
      (I.comap A.1.ι).ideal ⟨⊤, @isAffineOpen_top _ A.2⟩ ≤
        (J.comap A.1.ι).ideal ⟨⊤, @isAffineOpen_top _ A.2⟩) : I ≤ J := by
  intro A
  have hA := h A
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Ideal.comap_le_comap_iff_of_surjective _
      (ConcreteCategory.bijective_of_isIso (A.1.ι.appIso ⊤).inv).2] at hA
  exact affineOpens_property_of_eq (P := fun A => I.ideal A ≤ J.ideal A) A.1.ι_image_top hA

/-- Finite generation of an ideal sheaf on an affine open can be read after restriction to that
open, on global sections there. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.fg_ideal_of_fg_comap_ι {V : Scheme.{u}}
    (I : V.IdealSheafData) (A : V.affineOpens)
    (h : ((I.comap A.1.ι).ideal ⟨⊤, @isAffineOpen_top _ A.2⟩).FG) : (I.ideal A).FG := by
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at h
  have h' := h.map (A.1.ι.appIso ⊤).inv.hom
  rw [Ideal.map_comap_of_surjective _
    (ConcreteCategory.bijective_of_isIso (A.1.ι.appIso ⊤).inv).2] at h'
  exact affineOpens_property_of_eq (P := fun A => (I.ideal A).FG) A.1.ι_image_top h'

variable (B S hS)

/-- **The defining ideal of a closed subspace at the chart cut out by an affine open of an
étale chart** is the chart ideal sheaf restricted to that open, on its global sections. -/
theorem definingIdealAt_chartOpens_eq (Y : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS Y.1) (U : SmallEtale B S hS Y.1)
    (A : (etaleChartScheme B S hS U).affineOpens) :
    definingIdealAt B S hS Y Z (op ((chartOpens B S hS U).obj A.1)) =
      ((etaleChartKer B S hS Y Z U).comap A.1.ι).ideal ⟨⊤, @isAffineOpen_top _ A.2⟩ := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj ((chartOpens B S hS U).obj A.1).1.left) :=
    A.2
  have h1 := ker_rep_snd_eq_ofIdealTop_definingIdealAt B S hS Y Z ((chartOpens B S hS U).obj A.1)
  have h2 := comap_chartKer B S hS Y Z U.1.hom (chartOpenOverι B S hS U A.1)
    ((chartOpens B S hS U).obj A.1).1.hom rfl
  have h3 : (etaleChartKer B S hS Y Z U).comap A.1.ι =
      Scheme.IdealSheafData.ofIdealTop
        (definingIdealAt B S hS Y Z (op ((chartOpens B S hS U).obj A.1))) :=
    h2.trans ((chartKer_eq B S hS Y Z _).trans h1)
  rw [h3]
  have : IsAffine (A.1 : Scheme.{u}) := A.2
  exact (Scheme.IdealSheafData.equivOfIsAffine (X := (A.1 : Scheme.{u})).apply_symm_apply _).symm

end IdealSheaf

/-! ### The approximation -/

section Approximation

variable (B S hS)
variable (Y : AlgebraicSpaces B S hS) (X : ClosedSubspaces B S hS Y.1)

/-- The defining ideal sheaf of `X`, as an `𝒪_Y`-module. -/
noncomputable abbrev definingIdealModule : Modules.{u, u} B S hS Y.1 Y.2 :=
  (definingIdealSheaf B S hS Y X).toSheafOfModules

/-- The defining ideal sheaf of `X` is quasi-coherent. -/
instance : (definingIdealModule B S hS Y X).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_definingIdealSheaf B S hS Y X

variable {B S hS Y X}

/-- The inclusion of a finite type quasi-coherent submodule of the defining ideal sheaf of `X`
into `𝒪_Y` is a monomorphism. -/
theorem mono_arrow_comp_ι
    (G : FiniteTypeQuasicoherentSubobject B S hS Y.1 Y.2 (definingIdealModule B S hS Y X)) :
    Mono (G.obj.arrow ≫ (definingIdealSheaf B S hS Y X).ι) := by
  have h : Mono (definingIdealSheaf B S hS Y X).ι := inferInstance
  exact @mono_comp _ _ _ _ _ _ inferInstance _ h

/-- The sheaf of ideals of `𝒪_Y` which a finite type quasi-coherent submodule of the defining
ideal sheaf of `X` is, as a submodule of `𝒪_Y`: the range of its inclusion into `𝒪_Y`. -/
noncomputable abbrev subobjectIdeal
    (G : FiniteTypeQuasicoherentSubobject B S hS Y.1 Y.2 (definingIdealModule B S hS Y X)) :
    (SheafOfModules.unit (structureRingSheaf B S hS Y)).Submodule :=
  @SheafOfModules.monoRangeSubmodule _ _ _ _ _ _
    (G.obj.arrow ≫ (definingIdealSheaf B S hS Y X).ι) (mono_arrow_comp_ι G)

/-- `G` is isomorphic to the sheaf of ideals it defines. -/
noncomputable def isoSubobjectIdeal
    (G : FiniteTypeQuasicoherentSubobject B S hS Y.1 Y.2 (definingIdealModule B S hS Y X)) :
    (G.obj : Modules.{u, u} B S hS Y.1 Y.2) ≅ (subobjectIdeal G).toSheafOfModules :=
  @SheafOfModules.isoMonoRangeSubmodule _ _ _ _ _ _
    (G.obj.arrow ≫ (definingIdealSheaf B S hS Y X).ι) (mono_arrow_comp_ι G)

/-- The sheaf of ideals defined by `G` is quasi-coherent. -/
theorem isQuasicoherentOnSite_subobjectIdeal
    (G : FiniteTypeQuasicoherentSubobject B S hS Y.1 Y.2 (definingIdealModule B S hS Y X)) :
    (subobjectIdeal G).toSheafOfModules.IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso (isoSubobjectIdeal G) G.property.1

/-- The sheaf of ideals defined by `G` is of finite type. -/
theorem isFiniteTypeOnSite_subobjectIdeal
    (G : FiniteTypeQuasicoherentSubobject B S hS Y.1 Y.2 (definingIdealModule B S hS Y X)) :
    SheafOfModules.IsFiniteTypeOnSite (subobjectIdeal G).toSheafOfModules :=
  Stacks.SheafOfModules.isFiniteTypeOnSite_of_isFiniteType _
    (Stacks.SheafOfModules.Intrinsic.isFiniteType_of_iso (isoSubobjectIdeal G) G.property.2)

/-- The closed subspace of `Y` cut out by a finite type quasi-coherent submodule of the defining
ideal sheaf of `X`. -/
noncomputable def subobjectStage
    (G : FiniteTypeQuasicoherentSubobject B S hS Y.1 Y.2 (definingIdealModule B S hS Y X)) :
    ClosedSubspaces B S hS Y.1 :=
  (exists_definingIdealSheaf_eq_of_isQuasicoherentOnSite B S hS Y (subobjectIdeal G)
    (isQuasicoherentOnSite_subobjectIdeal G)).choose

/-- The defining ideal sheaf of the closed subspace cut out by `G` is the sheaf of ideals defined
by `G`. -/
theorem definingIdealSheaf_subobjectStage
    (G : FiniteTypeQuasicoherentSubobject B S hS Y.1 Y.2 (definingIdealModule B S hS Y X)) :
    definingIdealSheaf B S hS Y (subobjectStage G) = subobjectIdeal G :=
  (exists_definingIdealSheaf_eq_of_isQuasicoherentOnSite B S hS Y (subobjectIdeal G)
    (isQuasicoherentOnSite_subobjectIdeal G)).choose_spec

/-- A section of `𝒪_Y` lies in the sheaf of ideals defined by `G` if and only if it is the image
of a section of `G`. -/
theorem mem_subobjectIdeal_iff
    (G : FiniteTypeQuasicoherentSubobject B S hS Y.1 Y.2 (definingIdealModule B S hS Y X))
    (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (x : (SheafOfModules.unit (structureRingSheaf B S hS Y)).val.obj U) :
    x ∈ (subobjectIdeal G).obj U ↔
      ∃ m, (G.obj.arrow ≫ (definingIdealSheaf B S hS Y X).ι).val.app U m = x :=
  Iff.rfl

/-- If `G` is contained in `G'`, a section of the defining ideal sheaf of `X` in the range of `G`
lies, as a section of `𝒪_Y`, in the sheaf of ideals defined by `G'`. -/
theorem mem_subobjectIdeal
    {G G' : FiniteTypeQuasicoherentSubobject B S hS Y.1 Y.2 (definingIdealModule B S hS Y X)}
    (f : G ⟶ G') (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (m : (definingIdealModule B S hS Y X).val.obj U)
    (hm : m ∈ LinearMap.range (G.obj.arrow.val.app U).hom) :
    (definingIdealSheaf B S hS Y X).ι.val.app U m ∈ (subobjectIdeal G').obj U := by
  obtain ⟨m', hm'⟩ := range_arrow_le_range_arrow_of_hom _ f U hm
  exact (mem_subobjectIdeal_iff G' U _).2 ⟨m', by rw [← hm']; rfl⟩

/-- The sheaf of ideals defined by `G` is monotone in `G`. -/
theorem subobjectIdeal_mono
    {G G' : FiniteTypeQuasicoherentSubobject B S hS Y.1 Y.2 (definingIdealModule B S hS Y X)}
    (f : G ⟶ G') : subobjectIdeal G ≤ subobjectIdeal G' := by
  intro U x hx
  obtain ⟨m, rfl⟩ := (mem_subobjectIdeal_iff G U x).1 hx
  exact mem_subobjectIdeal f U _ ⟨m, rfl⟩

/-- The sheaf of ideals defined by `G` is contained in the defining ideal sheaf of `X`. -/
theorem subobjectIdeal_le
    (G : FiniteTypeQuasicoherentSubobject B S hS Y.1 Y.2 (definingIdealModule B S hS Y X)) :
    subobjectIdeal G ≤ definingIdealSheaf B S hS Y X := by
  intro U x hx
  obtain ⟨m, rfl⟩ := (mem_subobjectIdeal_iff G U x).1 hx
  exact ((G.obj.arrow.val.app U) m).2

/-- The closed subspace cut out by a finite type quasi-coherent submodule of the defining ideal
sheaf is of finite presentation over `Y`: its ideal is of finite type, so finitely generated
over every affine open of a chart. -/
theorem isFinitePresentation_subobjectStage
    (G : FiniteTypeQuasicoherentSubobject B S hS Y.1 Y.2 (definingIdealModule B S hS Y X)) :
    IsFinitePresentation B S hS (subobjectStage G).1.ι := by
  refine (isFinitePresentation_ι_iff_fg_chartKer Y (subobjectStage G)).2 fun A => ?_
  let U0 : SmallEtale B S hS Y.1 :=
    ⟨CostructuredArrow.mk (atlasHom B S hS Y), atlasHom_etale B S hS Y⟩
  refine Scheme.IdealSheafData.fg_ideal_of_fg_comap_ι
    (etaleChartKer B S hS Y (subobjectStage G) U0) A ?_
  rw [← definingIdealAt_chartOpens_eq B S hS Y (subobjectStage G) U0 A]
  let W := (chartOpens B S hS U0).obj A.1
  have hW : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj W) := A.2
  change ((definingIdealSheaf B S hS Y (subobjectStage G)).obj (op W)).FG
  rw [definingIdealSheaf_subobjectStage]
  exact Module.Finite.iff_fg.1 (module_finite_sections_of_isFiniteTypeOnSite
    (subobjectIdeal G).toSheafOfModules (isQuasicoherentOnSite_subobjectIdeal G)
    (isFiniteTypeOnSite_subobjectIdeal G) W hW)

variable (hc : IsColimit (finiteTypeQuasicoherentSubobjectCocone B S hS Y.1 Y.2
  (definingIdealModule B S hS Y X)))
include hc

/-- The defining ideal of `X` on the chart cut out by an affine open of an étale chart is
contained in the supremum of those of the stages. -/
theorem definingIdealAt_le_iSup_subobjectStage {ι : Type*}
    (Gs : ι → FiniteTypeQuasicoherentSubobject B S hS Y.1 Y.2 (definingIdealModule B S hS Y X))
    (hGs : ∀ G, ∃ i, Nonempty (G ⟶ Gs i)) (W : SmallEtale B S hS Y.1)
    (hW : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj W)) :
    definingIdealAt B S hS Y X (op W) ≤
      ⨆ i, definingIdealAt B S hS Y (subobjectStage (Gs i)) (op W) := by
  intro x hx
  obtain ⟨G, hG⟩ := exists_mem_range_of_isAffine (definingIdealModule B S hS Y X) hc hW ⟨x, hx⟩
  obtain ⟨i, ⟨f⟩⟩ := hGs G
  refine Submodule.mem_iSup_of_mem i ?_
  change x ∈ (definingIdealSheaf B S hS Y (subobjectStage (Gs i))).obj (op W)
  rw [definingIdealSheaf_subobjectStage]
  exact mem_subobjectIdeal f (op W) ⟨x, hx⟩ hG

/- The global instance `Abelian (SheafOfModules.{max u v r w} O)` of the cohomology of modules
leaves a stuck universe constraint against `Modules.{u, u}`; the abelian structure used here is the
one at the pinned universes. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck in
omit hc in
/-- **The approximation of Stacks 0A0U**, built from the finite type quasi-coherent submodules of
the defining ideal sheaf of `X`: the stages are the closed subspaces they cut out, indexed by a
small model of the directed system of those submodules. -/
noncomputable def closedSubspaceApproximationOfIsColimit :
    ClosedSubspaceApproximation B S hS Y X := by
  classical
  let C := FiniteTypeQuasicoherentSubobject B S hS Y.1 Y.2 (definingIdealModule B S hS Y X)
  have hfil : IsFiltered C := isFiltered_finiteTypeQuasicoherentSubobject B S hS Y.1 Y.2 _
  have : EssentiallySmall.{u} C :=
    essentiallySmall_finiteTypeQuasicoherentSubobject B S hS Y.1 Y.2 _
  let e := equivSmallModel.{u} C
  let Gs : SmallModel.{u} C → C := fun a => e.inverse.obj a
  let pre : Preorder (SmallModel.{u} C) := Preorder.lift fun a => (Gs a).obj
  have hle : ∀ G : C, G.obj ≤ (Gs (e.functor.obj G)).obj := fun G =>
    leOfHom (e.unitIso.hom.app G).hom
  have hdir : IsDirected (SmallModel.{u} C) (· ≤ ·) := ⟨fun a b =>
    ⟨e.functor.obj (IsFiltered.max (Gs a) (Gs b)),
      (leOfHom (IsFiltered.leftToMax (Gs a) (Gs b)).hom).trans (hle _),
      (leOfHom (IsFiltered.rightToMax (Gs a) (Gs b)).hom).trans (hle _)⟩⟩
  let Z : SmallModel.{u} C → ClosedSubspaces B S hS Y.1 := fun a => subobjectStage (Gs a)
  have hanti : ∀ ⦃i j : SmallModel.{u} C⦄, i ≤ j → (Z j).1 ≤ (Z i).1 := fun i j hij =>
    le_of_definingIdealSheaf_le B S hS Y (Z j) (Z i) (by
      rw [definingIdealSheaf_subobjectStage, definingIdealSheaf_subobjectStage]
      exact subobjectIdeal_mono (ObjectProperty.homMk (homOfLE hij)))
  have hXle : ∀ i, X.1 ≤ (Z i).1 := fun i =>
    le_of_definingIdealSheaf_le B S hS Y X (Z i) (by
      rw [definingIdealSheaf_subobjectStage]
      exact subobjectIdeal_le _)
  have hsup : ∀ U, etaleChartKer B S hS Y X U ≤ ⨆ i, etaleChartKer B S hS Y (Z i) U := by
    intro U
    refine Scheme.IdealSheafData.le_of_forall_comap_ι_le fun A => ?_
    rw [← definingIdealAt_chartOpens_eq B S hS Y X U A]
    refine (definingIdealAt_le_iSup_subobjectStage hc Gs
      (fun G => ⟨e.functor.obj G, ⟨e.unitIso.hom.app G⟩⟩) ((chartOpens B S hS U).obj A.1)
      A.2).trans (iSup_le fun i => ?_)
    rw [definingIdealAt_chartOpens_eq]
    exact Scheme.IdealSheafData.comap_mono A.1.ι
      (le_iSup (fun i => etaleChartKer B S hS Y (Z i) U) i) _
  let i₀ : SmallModel.{u} C := e.functor.obj hfil.nonempty.some
  exact
    { index := SmallModel.{u} C
      indexPreorder := pre
      point := i₀
      indexDirected := hdir
      stage := Z
      stage_antitone := hanti
      le_stage := hXle
      stage_isFinitePresentation := fun i => isFinitePresentation_subobjectStage _
      isLimit := isLimitClosedSubspaceCone B S hS i₀ (fun i => (Z i).1) hanti X.1 hXle
        (iInf_le_of_etaleChartKer_le_iSup B S hS Y Z X hsup) }

end Approximation

variable (B S hS) in
/-- **Stacks 0A0U from Stacks 0829.**  Let `Y` be an algebraic space over a scheme `S` on which
every quasi-coherent module is the colimit of its finite type quasi-coherent submodules (the
conclusion of Stacks 0829, which holds when `Y` is quasi-compact and quasi-separated).  Then every
closed subspace `X ⊆ Y` is a directed inverse limit of closed subspaces of `Y` of finite
presentation over `Y`, the transition morphisms and the projections being closed immersions.

This is the source's proof: the ideal sheaf `𝓘` of `X` is the colimit of its finite type
quasi-coherent submodules `𝓘_i`, each cuts out a closed subspace `X_i = V(𝓘_i)` whose inclusion
is of finite presentation, and `X = lim X_i` because, on every affine étale chart, every section
of `𝓘` lies in some `𝓘_i`. -/
theorem hasClosedSubspaceApproximation_of_isColimit_finiteTypeQuasicoherentSubobjectCocone
    (Y : AlgebraicSpaces B S hS)
    (h0829 : ∀ G : Modules.{u, u} B S hS Y.1 Y.2, G.IsQuasicoherentOnSite →
      Nonempty (IsColimit (finiteTypeQuasicoherentSubobjectCocone B S hS Y.1 Y.2 G)))
    (X : ClosedSubspaces B S hS Y.1) : HasClosedSubspaceApproximation B S hS Y X :=
  ⟨closedSubspaceApproximationOfIsColimit
    (h0829 _ (isQuasicoherentOnSite_definingIdealSheaf B S hS Y X)).some⟩

end AlgebraicGeometry.Space

end
