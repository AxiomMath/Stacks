module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentGenericFreeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealCoproductGenericIso
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentHomColimitBijective
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentSchemeTheoreticSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissage
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentFiniteProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentSubquotientNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPointsInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureSheafCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforwardExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQuasicoherentPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentIntersectionPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportClosedFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePushforwardQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.HomOverIdealUnitLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealComplementChartOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperModuleSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactOpenSubspace

/-!
# A coherent module with integral scheme-theoretic support contains a sum of ideals

[Stacks, Tag 07UQ]: Let `X` be a Noetherian algebraic space over `S` and let `ℱ` be a coherent
`𝒪_X`-module whose scheme-theoretic support is a reduced closed subspace `i : Z → X` with `|Z|`
irreducible.  Then there are an integer `r > 0`, a nonzero sheaf of ideals `ℐ ⊆ 𝒪_Z` and an
injective map of coherent modules `i_*(ℐ^{⊕ r}) → ℱ` whose cokernel is supported on a proper
closed subspace of `Z`.

The proof follows the source.  On `Z`, the module `𝒢` with `i_*𝒢 = ℱ` is free of some rank `r`
over an affine open immersion chart `C` (`StacksFrontier/AlgebraicGeometry/Spaces/
CoherentGenericFreeChart.lean`); `ℐ` is a power of the ideal cutting out the complement of `C`,
and the map `(ℐ)^{⊕ r} → 𝒢` extends the trivialization by [Stacks, Tag 07UM].  Everything that
has to be checked about that map is checked over the affine charts mapping to `C`, where it is
the isomorphism of a basis.

## Main results

* `AlgebraicGeometry.Space.eq_zero_of_forall_affine_map_eq_zero`: a section vanishing over every
  affine chart above its chart is zero.
* `AlgebraicGeometry.Space.mono_biproduct_desc_of_injective_on_affine_idealUnitCharts` and
  `AlgebraicGeometry.Space.supportOfSheaf_cokernel_subset_idealZeroLocus_of_surjective_affine`:
  injectivity, and the support of the cokernel, tested over affine charts carrying the unit
  ideal.
* `AlgebraicGeometry.Space.exists_idealPowModule_hom_val_app_one`: [Stacks, Tag 07UM] at a
  section over an open immersion chart.
* `AlgebraicGeometry.Space.exists_mono_biproduct_idealSheaf_cokernel_support_subset`: the case
  `Z = X`.
* `AlgebraicGeometry.Space.isCoherent_modulePushforward_quasicoherentIdeal`: the direct image
  along a closed immersion carries a quasi-coherent sheaf of ideals to a coherent module when
  the target is locally Noetherian.  That it preserves quasi-coherence at all is
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_isClosedImmersion`, in
  `StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionQuasicoherentPushforward.lean`.
* `AlgebraicGeometry.Space.exists_mono_modulePushforward_idealSum_of_schemeTheoreticSupport`:
  **[Stacks, Tag 07UQ]**.

## References

* [Stacks Project, Tag 07UQ](https://stacks.math.columbia.edu/tag/07UQ)
* [Stacks Project, Tag 07UM](https://stacks.math.columbia.edu/tag/07UM)
* [Stacks Project, Tag 07UG](https://stacks.math.columbia.edu/tag/07UG)
* [Stacks Project, Tag 07U0](https://stacks.math.columbia.edu/tag/07U0)
* [Stacks Project, Tag 07UD](https://stacks.math.columbia.edu/tag/07UD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Sections over the affine charts -/

section Affine

variable (X : AlgebraicSpaces B S hS)

/-- **A section of a sheaf of modules vanishing on every affine chart over its chart is zero.**
The affine charts cover, by [Stacks, Tag 04JS], and a sheaf is separated. -/
theorem eq_zero_of_forall_affine_map_eq_zero {P : Modules.{u, u} B S hS X.1 X.2}
    {W : SmallEtale B S hS X.1} (s : P.val.obj (op W))
    (h : ∀ A : SmallEtale B S hS X.1, IsAffine (chartScheme A) → ∀ g : A ⟶ W,
      P.val.map g.op s = 0) : s = 0 := by
  refine (Presheaf.IsSheaf.isSeparated P.isSheaf) W _
    ((SmallEtale.isCoverDense_affineEtaleInclusion B S hS X.1 X.2).is_cover W) s 0 ?_
  rintro Y f ⟨⟨A, lift, map, fac⟩⟩
  rw [← fac]
  have e := congrArg (fun φ => (ConcreteCategory.hom φ) s)
    (P.val.presheaf.map_comp map.op lift.op)
  refine (e.trans ?_).trans (map_zero _).symm
  change P.val.presheaf.map lift.op (P.val.map map.op s) = 0
  rw [h ((AffineEtale.inclusion B S hS X.1).obj A) A.property map]
  exact (P.val.presheaf.map lift.op).hom.map_zero

/-- **A morphism to the structure sheaf vanishing on the sections over every affine chart
carrying the unit ideal of a sheaf of ideals with nonempty unit locus is zero**, on an
étale-locally reduced algebraic space with irreducible space of points.  The vanishing passes
from the affine charts to every chart carrying the unit ideal by
`AlgebraicGeometry.Space.eq_zero_of_forall_affine_map_eq_zero`, since an affine chart over such
a chart carries the unit ideal too; the statement for every chart is
`AlgebraicGeometry.Space.eq_zero_of_val_app_eq_zero_on_idealUnitCharts`. -/
theorem eq_zero_of_val_app_eq_zero_on_affine_idealUnitCharts
    (hred : HasEtaleLocalProperty B S hS X.1 (fun Y : Scheme.{u} => IsReduced Y))
    (hirr : IrreducibleSpace (points B S hS X.1))
    (J : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (hJ : (idealUnitLocus B S hS X J).Nonempty)
    {K : Modules.{u, u} B S hS X.1 X.2}
    (θ : K ⟶ spaceStructureSheafModule B S hS X)
    (hθ : ∀ W : SmallEtale B S hS X.1, IsAffine (chartScheme W) → J.obj (op W) = ⊤ →
      ∀ x : K.val.obj (op W), θ.val.app (op W) x = 0) :
    θ = 0 := by
  refine eq_zero_of_val_app_eq_zero_on_idealUnitCharts B S hS X hred hirr J hJ θ
    fun W hW x => eq_zero_of_forall_affine_map_eq_zero B S hS X _ fun A hA g => ?_
  exact (PresheafOfModules.naturality_apply θ.val g.op x).symm.trans
    (hθ A hA (SheafOfModules.Submodule.unit_obj_eq_top_of_map J g.op hW) _)

/-- **The cokernel of a morphism which is surjective on the sections over the affine charts
carrying the unit ideal of a sheaf of ideals is supported in the zero locus of the ideal.**

A section `t` of the cokernel over a chart below one carrying the unit ideal vanishes over every
affine chart `A` above it: over `A` it lifts locally to the target, and each lift vanishes in
the cokernel over every affine chart above its own chart, where it comes from the source. -/
theorem supportOfSheaf_cokernel_subset_idealZeroLocus_of_surjective_affine
    (J : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    {P F : Modules.{u, u} B S hS X.1 X.2} (φ : P ⟶ F)
    (hsurj : ∀ W : SmallEtale B S hS X.1, IsAffine (chartScheme W) → J.obj (op W) = ⊤ →
      ∀ s : F.val.obj (op W), ∃ y : P.val.obj (op W), φ.val.app (op W) y = s) :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj
        (cokernel (C := Modules.{u, u} B S hS X.1 X.2) φ)) ⊆
      idealZeroLocus B S hS X J := by
  refine supportOfSheaf_subset_idealZeroLocus_of_forall_subsingleton B S hS X _ J ?_
  intro V hV W g
  have hπ : ∀ (Y : SmallEtale B S hS X.1) (y : P.val.obj (op Y)),
      (cokernel.π (C := Modules.{u, u} B S hS X.1 X.2) φ).val.app (op Y)
        (φ.val.app (op Y) y) = 0 := fun Y y =>
    congrArg (fun k : P ⟶ cokernel (C := Modules.{u, u} B S hS X.1 X.2) φ => k.val.app (op Y) y)
      (cokernel.condition (C := Modules.{u, u} B S hS X.1 X.2) φ)
  have hzero : ∀ t : (cokernel (C := Modules.{u, u} B S hS X.1 X.2) φ).val.obj (op W),
      t = 0 := by
    intro t
    refine eq_zero_of_forall_affine_map_eq_zero B S hS X t fun A hA a => ?_
    obtain ⟨Sv, hSv, hcov⟩ := Stacks.SheafOfModules.EpiMono.exists_covering_of_epi
      (cokernel.π (C := Modules.{u, u} B S hS X.1 X.2) φ)
      ((cokernel (C := Modules.{u, u} B S hS X.1 X.2) φ).val.map a.op t)
    refine (Presheaf.IsSheaf.isSeparated
      (cokernel (C := Modules.{u, u} B S hS X.1 X.2) φ).isSheaf) A Sv hSv _ 0 ?_
    intro Y f hf
    obtain ⟨b, hb⟩ := hcov f hf
    refine hb.symm.trans (Eq.trans ?_ (map_zero _).symm)
    refine eq_zero_of_forall_affine_map_eq_zero B S hS X _ fun A' hA' a' => ?_
    have hA'top : J.obj (op A') = ⊤ :=
      SheafOfModules.Submodule.unit_obj_eq_top_of_map J (a' ≫ f ≫ a ≫ g).op hV
    obtain ⟨y, hy⟩ := hsurj A' hA' hA'top (F.val.map a'.op b)
    refine (PresheafOfModules.naturality_apply
      (cokernel.π (C := Modules.{u, u} B S hS X.1 X.2) φ).val a'.op b).symm.trans ?_
    exact (congrArg (fun z => (cokernel.π (C := Modules.{u, u} B S hS X.1 X.2) φ).val.app
      (op A') z) hy.symm).trans (hπ A' y)
  exact ⟨fun a b => by rw [hzero a, hzero b]⟩

/-- A finite sum of morphisms of modules, read on a section, is the sum of the values. -/
theorem sum_val_app_apply {L G : Modules.{u, u} B S hS X.1 X.2} {ι : Type*}
    (s : Finset ι)
    (f : ι → (L ⟶ G)) (W : (SmallEtale B S hS X.1)ᵒᵖ) (x : L.val.obj W) :
    (∑ i ∈ s, f i).val.app W x = ∑ i ∈ s, (f i).val.app W x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    rfl

/-- **A map out of a finite direct sum of copies of a sheaf of ideals which is injective over
the affine charts carrying the unit ideal of a sheaf of ideals with nonempty unit locus is a
monomorphism**, on an étale-locally reduced algebraic space with irreducible space of points.

If `ψ : L ⟶ ⨁ J` is killed by the map, the coordinates of `ψ`, read as morphisms `L ⟶ 𝒪_X`,
vanish on the sections over every affine chart carrying the unit ideal, so they vanish by
`AlgebraicGeometry.Space.eq_zero_of_val_app_eq_zero_on_affine_idealUnitCharts`. -/
theorem mono_biproduct_desc_of_injective_on_affine_idealUnitCharts
    (hred : HasEtaleLocalProperty B S hS X.1 (fun Y : Scheme.{u} => IsReduced Y))
    (hirr : IrreducibleSpace (points B S hS X.1))
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (hI : (idealUnitLocus B S hS X I).Nonempty) {r : ℕ}
    (J : (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).Submodule)
    {G : Modules.{u, u} B S hS X.1 X.2}
    (Φ : Fin r → (J.toSheafOfModules ⟶ G))
    (hinj : ∀ W : SmallEtale B S hS X.1, IsAffine (chartScheme W) → I.obj (op W) = ⊤ →
      ∀ y : Fin r → J.toSheafOfModules.val.obj (op W),
        ∑ k, (Φ k).val.app (op W) (y k) = 0 → ∀ k, y k = 0) :
    Mono (biproduct.desc Φ) := by
  have _ : Mono J.ι := SheafOfModules.Submodule.mono_ι_via_forget J
  refine Preadditive.mono_of_cancel_zero _ ?_
  intro L ψ hψ
  let π : ∀ k : Fin r, (⨁ fun _ : Fin r => J.toSheafOfModules) ⟶ J.toSheafOfModules :=
    fun k => biproduct.π _ k
  have hdec : ψ ≫ biproduct.desc Φ = ∑ k, (ψ ≫ π k) ≫ Φ k := by
    rw [biproduct.desc_eq, Preadditive.comp_sum]
    exact Finset.sum_congr rfl fun k _ => (Category.assoc _ _ _).symm
  have hcoord : ∀ k, ψ ≫ π k ≫ J.ι = 0 := by
    intro k
    refine eq_zero_of_val_app_eq_zero_on_affine_idealUnitCharts B S hS X hred hirr I hI _
      fun W hW hWtop x => ?_
    have h0 := congrArg (fun m => m.val.app (op W) x) (hdec.symm.trans hψ)
    have h1 : ∑ k, (Φ k).val.app (op W) ((ψ ≫ π k).val.app (op W) x) = 0 :=
      (sum_val_app_apply B S hS X Finset.univ _ (op W) x).symm.trans h0
    have h2 := hinj W hW hWtop _ h1 k
    change (J.ι.val.app (op W) ((ψ ≫ π k).val.app (op W) x)) = 0
    rw [h2, map_zero]
  refine biproduct.hom_ext _ _ fun k => ?_
  rw [zero_comp]
  refine (cancel_mono J.ι).1 ?_
  rw [zero_comp, Category.assoc]
  exact hcoord k

end Affine

/-! ### Charts lying in an open immersion chart, and in the complement of an ideal -/

section Charts

variable {B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **A chart has at most one morphism to an open immersion chart**: the structure morphism of
the target is a monomorphism and the Yoneda embedding is faithful. -/
theorem hom_ext_of_isOpenImmersion {C W : SmallEtale B S hS F}
    (hC : IsOpenImmersion B S hS C.1.hom) (f g : W ⟶ C) : f = g := by
  have _ : Mono C.1.hom := mono_of_presheaf_isOpenImmersion hC
  have h : yoneda.map f.hom.left = yoneda.map g.hom.left :=
    (cancel_mono C.1.hom).1 ((CostructuredArrow.w f.hom).trans (CostructuredArrow.w g.hom).symm)
  exact ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ (yoneda.map_injective h))

/-- **A chart whose point set lies in that of an open immersion chart maps to it**, by
[Stacks, Tag 03IE] in the form `AlgebraicGeometry.Space.exists_hom_of_range_pointsMap_subset`. -/
theorem nonempty_hom_of_range_subset {C W : SmallEtale B S hS F}
    (hC : IsOpenImmersion B S hS C.1.hom)
    (h : Set.range (pointsMap B S hS (yoneda.obj W.obj.left) W.1.hom) ⊆
      Set.range (pointsMap B S hS (yoneda.obj C.obj.left) C.1.hom)) : Nonempty (W ⟶ C) := by
  obtain ⟨σ, hσ⟩ := exists_hom_of_range_pointsMap_subset C hC W.1.hom h
  exact ⟨ObjectProperty.homMk (CostructuredArrow.homMk σ hσ)⟩

/-- The point set of a chart mapping to another chart lies in the point set of the latter. -/
theorem range_subset_of_hom {C W : SmallEtale B S hS F} (g : W ⟶ C) :
    Set.range (pointsMap B S hS (yoneda.obj W.obj.left) W.1.hom) ⊆
      Set.range (pointsMap B S hS (yoneda.obj C.obj.left) C.1.hom) := by
  rintro _ ⟨w, rfl⟩
  refine ⟨pointsMap B S hS _ (yoneda.map g.hom.left) w, ?_⟩
  rw [← pointsMap_comp_apply B S hS (yoneda.map g.hom.left) C.1.hom w, CostructuredArrow.w g.hom]

variable (B S hS)

/-- **A chart of `X` whose point set lies in the unit locus of `ℐ` is a chart of the open
complement `U = X ∖ V(ℐ)`**, postcomposed with the inclusion, on the nose.  The chart morphism
factors through `U` by [Stacks, Tag 03IE], the factorization is étale by cancellation, and the
two full-subcategory objects agree because their structure morphisms do. -/
theorem exists_pc_eq_of_range_subset_idealUnitLocus (X : AlgebraicSpaces B S hS)
    (I : IdealSheaves B S hS X.1 X.2) (W : SmallEtale B S hS X.1)
    (hW : Set.range (pointsMap B S hS (yoneda.obj W.obj.left) W.1.hom) ⊆
      idealUnitLocus B S hS X I) :
    ∃ P : SmallEtale B S hS (idealComplement B S hS X I).1, pc B S hS X I P = W := by
  obtain ⟨g, hg⟩ := (factorsThrough_openSubspace_iff_points B S hS X.2
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS _)
    (idealComplementSubfunctor B S hS X I)
    (isOpenSubspace_idealComplementSubfunctor B S hS X I) W.1.hom).2
      (hW.trans (range_pointsMap_idealComplementι B S hS X I).ge)
  refine ⟨⟨CostructuredArrow.mk g, ?_⟩, ?_⟩
  · exact presheaf_etale_of_postcomp B S hS (presheaf_etale_idealComplementι B S hS X I)
      W.property hg
  · exact ObjectProperty.FullSubcategory.ext
      (congrArg (fun α : yoneda.obj W.obj.left ⟶ X.1 =>
        (CostructuredArrow.mk α : CostructuredArrow yoneda X.1)) hg)

/-- The point set of a chart of the open complement `U = X ∖ V(ℐ)`, read as a chart of `X`, lies
in the unit locus of `ℐ`. -/
theorem range_pc_subset_idealUnitLocus (X : AlgebraicSpaces B S hS)
    (I : IdealSheaves B S hS X.1 X.2) (P : SmallEtale B S hS (idealComplement B S hS X I).1) :
    Set.range (pointsMap B S hS (yoneda.obj (pc B S hS X I P).obj.left) (pc B S hS X I P).1.hom) ⊆
      idealUnitLocus B S hS X I := by
  rintro _ ⟨w, rfl⟩
  rw [← range_pointsMap_idealComplementι B S hS X I]
  exact ⟨_, (pointsMap_comp_apply B S hS P.1.hom (idealComplementι B S hS X I).hom w).symm⟩

/-- The point set of a chart carrying the unit ideal lies in the unit locus. -/
theorem range_subset_idealUnitLocus_of_eq_top (X : AlgebraicSpaces B S hS)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (W : SmallEtale B S hS X.1) (hW : I.obj (op W) = ⊤) :
    Set.range (pointsMap B S hS (yoneda.obj W.obj.left) W.1.hom) ⊆
      idealUnitLocus B S hS X I :=
  fun x hx => ⟨W, hW, hx⟩

end Charts

/-! ### Extending a section over the open complement through a power of the ideal -/

section Extension

variable (Y : AlgebraicSpaces B S hS) (I : IdealSheaves B S hS Y.1 Y.2)
  {C : SmallEtale B S hS Y.1} (hC : IsOpenImmersion B S hS C.1.hom)
  (hIC : idealUnitLocus B S hS Y I ⊆
    Set.range (pointsMap B S hS (yoneda.obj C.obj.left) C.1.hom))

include hC hIC

/-- **A section over an open immersion chart containing the unit locus of `ℐ` is a global
section of the restriction to `U = X ∖ V(ℐ)`**: every chart of `U` maps to the chart, in exactly
one way, and the section is restricted along that map. -/
theorem exists_sections_restrictToIdealComplement (G : Modules.{u, u} B S hS Y.1 Y.2)
    (s : G.val.obj (op C)) :
    ∃ σ : ((restrictToIdealComplement B S hS Y I).obj G).sections,
      ∀ (P : SmallEtale B S hS (idealComplement B S hS Y I).1) (f : pc B S hS Y I P ⟶ C),
        σ.1 (op P) = G.val.map f.op s := by
  have hlift : ∀ P : SmallEtale B S hS (idealComplement B S hS Y I).1,
      Nonempty (pc B S hS Y I P ⟶ C) := fun P =>
    nonempty_hom_of_range_subset hC ((range_pc_subset_idealUnitLocus B S hS Y I P).trans hIC)
  refine ⟨⟨fun P => G.val.map (hlift P.unop).some.op s, ?_⟩, fun P f => ?_⟩
  · intro P P' f
    have e := congrArg (fun φ => (ConcreteCategory.hom φ) s)
      (G.val.presheaf.map_comp (hlift P.unop).some.op
        ((smallEtalePostcomp B S hS (idealComplementι B S hS Y I)
          (isEtale_idealComplementι B S hS Y I)).map f.unop).op)
    refine e.symm.trans ?_
    exact congrArg (fun g : pc B S hS Y I P'.unop ⟶ C =>
      (ConcreteCategory.hom (G.val.presheaf.map g.op)) s) (hom_ext_of_isOpenImmersion hC _ _)
  · rw [hom_ext_of_isOpenImmersion hC f (hlift P).some]

omit hIC in
/-- **[Stacks, Tag 07UM] at a section over an open immersion chart whose point set is the unit
locus of `ℐ`.**  On a Noetherian algebraic space, for a quasi-coherent sheaf of ideals `ℐ` and a
section `s` of a coherent module `G` over such a chart `C`, there are `n` and a morphism
`Ψ : ℐⁿ ⟶ G` sending the unit section, over every chart `W` mapping to `C`, to the restriction of
`s`.

The section `s` is a global section of `G|_U` by
`AlgebraicGeometry.Space.exists_sections_restrictToIdealComplement`, that is, a morphism
`𝒪_U ⟶ G|_U`, and the surjectivity of the first display of [Stacks, Tag 07UM] at `𝒢 = 𝒪_X`
extends it to `Ψ`.  A chart mapping to `C` lies in the unit locus, so it is a chart of `U`, and
there `Ψ` is read off its restriction. -/
theorem exists_idealPowModule_hom_val_app_one
    (hIC : idealUnitLocus B S hS Y I =
      Set.range (pointsMap B S hS (yoneda.obj C.obj.left) C.1.hom))
    (hIc : IsCartesianOnAffineCharts I.toSheafOfModules) (hZt : B.Contains (⊤_ Scheme.{u}))
    (hN : IsNoetherian B S hS hZt Y.1) (hIq : I.toSheafOfModules.IsQuasicoherentOnSite)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (hG : IsCoherent B S hS Y.1 Y.2 G)
    (s : G.val.obj (op C)) :
    ∃ (n : ℕ) (Ψ : idealPowModule I n (SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))) ⟶ G),
      ∀ (W : SmallEtale B S hS Y.1) (g : W ⟶ C)
        (h1 : SheafOfModules.unitOf
            (1 : ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).obj.obj (op W)) ∈
          (idealPowSubmodule I n (SheafOfModules.unit
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)))).obj (op W)),
        Ψ.val.app (op W) ⟨_, h1⟩ = G.val.map g.op s := by
  have : Fact (HasEtaleLocalProperty B S hS Y.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨hN.2.2⟩
  obtain ⟨σ, hσ⟩ := exists_sections_restrictToIdealComplement B S hS Y I hC hIC.le G s
  let θ : (restrictToIdealComplement B S hS Y I).obj (SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))) ⟶
      (restrictToIdealComplement B S hS Y I).obj G :=
    ((restrictToIdealComplement B S hS Y I).obj G).unitHomEquiv.symm σ
  obtain ⟨n, Ψ, hΨ⟩ := exists_homRestrict_eq B S hS Y I hIc _ G θ hZt hN hIq
    hG.toIsQuasicoherentOnSite (isCoherent_structureSheaf B S hS Y.1 Y.2)
  refine ⟨n, Ψ, fun W g h1 => ?_⟩
  have hW : Set.range (pointsMap B S hS (yoneda.obj W.obj.left) W.1.hom) ⊆
      idealUnitLocus B S hS Y I := (range_subset_of_hom g).trans hIC.ge
  obtain ⟨P, rfl⟩ := exists_pc_eq_of_range_subset_idealUnitLocus B S hS Y I W hW
  have h2 : (restrictToIdealComplement B S hS Y I).map Ψ =
      (idealPowRestrictIso B S hS Y I n _).hom ≫ θ := (Iso.inv_comp_eq _).1 hΨ
  have h3 := congrArg (fun m => m.val.app (op P) ⟨_, h1⟩) h2
  refine h3.trans ?_
  change θ.val.app (op P)
    (1 : ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (idealComplement B S hS Y I).1
      (idealComplement B S hS Y I).2).O)).obj.obj (op P)) = _
  refine (SheafOfModules.unitHomEquiv_apply_coe _ θ (op P)).symm.trans ?_
  exact (congrArg (fun z : ((restrictToIdealComplement B S hS Y I).obj G).sections =>
    z.1 (op P)) (Equiv.apply_symm_apply _ σ)).trans (hσ P g)

end Extension

/-! ### The case `Z = X` -/

section Integral

variable (hZt : B.Contains (⊤_ Scheme.{u})) (Y : AlgebraicSpaces B S hS)

/-! The two tests of the map `(ℐᴺ)^{⊕ r} → G` of [Stacks, Tag 07UQ] -- injectivity and
surjectivity over the affine charts carrying the unit ideal -- are stated here for an arbitrary
family `Φ` of maps out of a submodule of the structure sheaf which reads on sections as
multiplication against a basis.  That hypothesis, `hval` below, is everything the source's
argument uses about `Φ`: over such a chart the map *is* the isomorphism of a basis.  Both proofs
restrict the basis to the chart with
`AlgebraicGeometry.Space.exists_basis_restrict` and then read `hval` against it. -/

/-- **A family of maps out of a submodule of `𝒪_Y` which reads as multiplication against a basis
is injective over the affine charts carrying the unit ideal.**  A family of sections killed by
the sum is a family of coordinates killed by the restricted basis, so it vanishes. -/
theorem forall_eq_zero_of_sum_val_app_eq_zero_of_val_app_eq_smul
    {C : SmallEtale B S hS Y.1} (hCaff : IsAffine (chartScheme C))
    {G : Modules.{u, u} B S hS Y.1 Y.2} (hGcart : IsCartesianOnAffineCharts G)
    {n : ℕ} (b : Module.Basis (Fin n) (chartRing B S hS Y.1 Y.2 C) (G.val.obj (op C)))
    (I : IdealSheaves B S hS Y.1 Y.2)
    (J : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).Submodule)
    (Φ : Fin n → (J.toSheafOfModules ⟶ G))
    (hmapC : ∀ W : SmallEtale B S hS Y.1, I.obj (op W) = ⊤ → Nonempty (W ⟶ C))
    (hval : ∀ (k : Fin n) (W : SmallEtale B S hS Y.1) (g : W ⟶ C)
      (a : chartRing B S hS Y.1 Y.2 W) (ha : SheafOfModules.unitOf a ∈ J.obj (op W)),
      (Φ k).val.app (op W) ⟨_, ha⟩ = a • chartRestrictLinear G g (b k)) :
    ∀ W : SmallEtale B S hS Y.1, IsAffine (chartScheme W) → I.obj (op W) = ⊤ →
      ∀ y : Fin n → J.toSheafOfModules.val.obj (op W),
        ∑ k, (Φ k).val.app (op W) (y k) = 0 → ∀ k, y k = 0 := by
  intro W hW hWtop y hy k
  obtain ⟨g⟩ := hmapC W hWtop
  obtain ⟨b', hb'⟩ := exists_basis_restrict G hGcart hCaff hW g b
  have hsum : ∑ k, (show chartRing B S hS Y.1 Y.2 W from (y k).1) • b' k = 0 := by
    refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) hy
    rw [hb' k]
    exact (hval k W g _ (y k).2).symm
  exact Subtype.ext (Fintype.linearIndependent_iff.mp b'.linearIndependent _ hsum k)

/-- **A family of maps out of a submodule of `𝒪_Y` which reads as multiplication against a basis
has surjective sum over the affine charts carrying the unit ideal.**  The coordinates of a
section against the restricted basis are the sections of the submodule which the sum carries to
it, since over such a chart the submodule carries the unit ideal. -/
theorem exists_biproduct_desc_val_app_eq_of_val_app_eq_smul
    {C : SmallEtale B S hS Y.1} (hCaff : IsAffine (chartScheme C))
    {G : Modules.{u, u} B S hS Y.1 Y.2} (hGcart : IsCartesianOnAffineCharts G)
    {n : ℕ} (b : Module.Basis (Fin n) (chartRing B S hS Y.1 Y.2 C) (G.val.obj (op C)))
    (I : IdealSheaves B S hS Y.1 Y.2)
    (J : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).Submodule)
    (Φ : Fin n → (J.toSheafOfModules ⟶ G))
    (hmapC : ∀ W : SmallEtale B S hS Y.1, I.obj (op W) = ⊤ → Nonempty (W ⟶ C))
    (hmem : ∀ W : SmallEtale B S hS Y.1, (W ⟶ C) → ∀ a : chartRing B S hS Y.1 Y.2 W,
      SheafOfModules.unitOf a ∈ J.obj (op W))
    (hval : ∀ (k : Fin n) (W : SmallEtale B S hS Y.1) (g : W ⟶ C)
      (a : chartRing B S hS Y.1 Y.2 W) (ha : SheafOfModules.unitOf a ∈ J.obj (op W)),
      (Φ k).val.app (op W) ⟨_, ha⟩ = a • chartRestrictLinear G g (b k)) :
    ∀ W : SmallEtale B S hS Y.1, IsAffine (chartScheme W) → I.obj (op W) = ⊤ →
      ∀ t : G.val.obj (op W), ∃ z, (biproduct.desc Φ).val.app (op W) z = t := by
  intro W hW hWtop t
  obtain ⟨g⟩ := hmapC W hWtop
  obtain ⟨b', hb'⟩ := exists_basis_restrict G hGcart hCaff hW g b
  refine ⟨(∑ k : Fin n,
    ((biproduct.ι (fun _ : Fin n => J.toSheafOfModules) k).val.app (op W)).hom
      ⟨b'.repr t k, hmem W g (b'.repr t k)⟩ :
        (biproduct (fun _ : Fin n => J.toSheafOfModules)).val.obj (op W)), ?_⟩
  rw [map_sum]
  refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) (b'.sum_repr t)
  have e1 := congrArg (fun m => m.val.app (op W) ⟨_, hmem W g (b'.repr t k)⟩)
    (biproduct.ι_desc Φ k)
  exact e1.trans ((hval k W g _ (hmem W g (b'.repr t k))).trans
    (congrArg (b'.repr t k • ·) (hb' k).symm))

/-- **[Stacks, Tag 07UQ], the case `Z = X`.**  On a Noetherian algebraic space `Y` which is
étale-locally reduced with irreducible space of points, a coherent module `G` whose support is
all of `|Y|` receives an injective map `ℐ^{⊕ r} → G` from a direct sum of `r > 0` copies of a
nonzero quasi-coherent sheaf of ideals, whose cokernel is supported on a proper closed subset.

`G` is free of rank `r` over an affine open immersion chart `C` with a point, by
`AlgebraicGeometry.Space.exists_isOpenImmersion_isAffine_chart_basis`.  Let `ℐ` cut out the
complement `T` of the image of `C`; each basis section of `G(C)` extends by
`AlgebraicGeometry.Space.exists_idealPowModule_hom_val_app_one`, which is [Stacks, Tag 07UM], to
a morphism out of a power of `ℐ`, and a common power `ℐᴺ` is the sheaf of ideals of the lemma.
Over every affine chart mapping to `C` the map `(ℐᴺ)^{⊕ r} → G` is the isomorphism of a basis,
so it is injective by
`AlgebraicGeometry.Space.mono_biproduct_desc_of_injective_on_affine_idealUnitCharts` — the
source's argument that a nonzero section of `ℐ^{⊕ r}` is nonzero on a dense open — and its
cokernel is supported in `T` by
`AlgebraicGeometry.Space.supportOfSheaf_cokernel_subset_idealZeroLocus_of_surjective_affine`.
If `r` were `0` the cokernel would be `G`, whose support is everything. -/
theorem exists_mono_biproduct_idealSheaf_cokernel_support_subset
    (hN : IsNoetherian B S hS hZt Y.1)
    (hred : HasEtaleLocalProperty B S hS Y.1 (fun V : Scheme.{u} => IsReduced V))
    (hirr : IrreducibleSpace (points B S hS Y.1))
    (G : Modules.{u, u} B S hS Y.1 Y.2) (hG : IsCoherent B S hS Y.1 Y.2 G)
    (hsupp : supportOfSheaf B S hS Y.1 ((SheafOfModules.toSheaf _).obj G) = Set.univ) :
    ∃ (r : ℕ) (J : (SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).Submodule),
      J.toSheafOfModules.IsQuasicoherentOnSite ∧ 0 < r ∧ J ≠ ⊥ ∧
      ∃ ψ : (⨁ fun _ : Fin r => J.toSheafOfModules) ⟶ G,
        Mono ψ ∧ ∃ (Q : Modules.{u, u} B S hS Y.1 Y.2) (q : G ⟶ Q) (hq : ψ ≫ q = 0),
          Nonempty (IsColimit (CokernelCofork.ofπ q hq)) ∧
          ∃ T : Set (points B S hS Y.1), IsClosed T ∧ T ≠ Set.univ ∧
            supportOfSheaf B S hS Y.1 ((SheafOfModules.toSheaf _).obj Q) ⊆ T := by
  have : Fact (HasEtaleLocalProperty B S hS Y.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨hN.2.2⟩
  obtain ⟨x⟩ : Nonempty (points B S hS Y.1) := inferInstance
  obtain ⟨C, hCoi, hCaff, ⟨c⟩, n, ⟨b⟩⟩ :=
    exists_isOpenImmersion_isAffine_chart_basis B S hS Y hZt hN hred x G hG
  set R := Set.range (pointsMap B S hS (yoneda.obj C.obj.left) C.1.hom) with hRdef
  have hRopen : IsOpen R := isOpen_range_pointsMap_of_isOpenImmersion B S hS C.1.hom hCoi
  obtain ⟨p, -⟩ := surjective_pointsToScheme B S hS C.obj.left c
  have hRne : R.Nonempty := ⟨_, p, rfl⟩
  set T : Set (points B S hS Y.1) := Rᶜ with hTdef
  have hT : IsClosed T := hRopen.isClosed_compl
  have hTne : T ≠ Set.univ := by
    obtain ⟨y, hy⟩ := hRne
    intro h
    exact (h.symm ▸ Set.mem_univ y : y ∈ T) hy
  set I := reducedIdealSheaf B S hS Y T hT with hIdef
  have hzl : idealZeroLocus B S hS Y I = T := idealZeroLocus_reducedIdealSheaf B S hS Y T hT
  have hul : idealUnitLocus B S hS Y I = R := by
    have h1 : (idealZeroLocus B S hS Y I)ᶜ = idealUnitLocus B S hS Y I := compl_compl _
    rw [hzl, hTdef, compl_compl] at h1
    exact h1.symm
  have hIq : I.toSheafOfModules.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_reducedIdealSheaf B S hS Y T hT
  have hIc : IsCartesianOnAffineCharts I.toSheafOfModules :=
    isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS Y.1 Y.2 _ hIq
  have hGcart : IsCartesianOnAffineCharts G :=
    isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS Y.1 Y.2 G
      hG.toIsQuasicoherentOnSite
  have hext := fun k => exists_idealPowModule_hom_val_app_one B S hS Y I hCoi hul hIc hZt hN hIq
    G hG (b k)
  choose m Ψ hΨ using hext
  set N := Finset.univ.sup m with hNdef
  have hmN : ∀ k, m k ≤ N := fun k => Finset.le_sup (Finset.mem_univ k)
  set J := idealPowSubmodule I N (SheafOfModules.unit
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))) with hJdef
  let Φ : Fin n → (J.toSheafOfModules ⟶ G) := fun k =>
    idealPowModuleHomOfLE I _ (hmN k) ≫ Ψ k
  -- the charts mapping to `C` carry the unit ideal of `ℐᴺ`
  have htop : ∀ (W : SmallEtale B S hS Y.1), (W ⟶ C) → J.obj (op W) = ⊤ := fun W g =>
    idealPowSubmodule_obj_eq_top_of_range_subset_idealUnitLocus B S hS Y I N _ W
      ((range_subset_of_hom g).trans hul.ge)
  have hmem : ∀ (W : SmallEtale B S hS Y.1), (W ⟶ C) → ∀ a : chartRing B S hS Y.1 Y.2 W,
      SheafOfModules.unitOf a ∈ J.obj (op W) :=
    fun W g a => (htop W g).symm ▸ Submodule.mem_top
  have hval : ∀ (k : Fin n) (W : SmallEtale B S hS Y.1) (g : W ⟶ C)
      (a : chartRing B S hS Y.1 Y.2 W) (ha : SheafOfModules.unitOf a ∈ J.obj (op W)),
      (Φ k).val.app (op W) ⟨_, ha⟩ = a • chartRestrictLinear G g (b k) := by
    intro k W g a ha
    have h1 := hmem W g 1
    have hy : (⟨_, ha⟩ : J.toSheafOfModules.val.obj (op W)) =
        a • (⟨_, h1⟩ : J.toSheafOfModules.val.obj (op W)) := by
      refine Subtype.ext ?_
      change a = a * 1
      rw [mul_one]
    calc (Φ k).val.app (op W) ⟨_, ha⟩ = (Φ k).val.app (op W) (a • ⟨_, h1⟩) := congrArg _ hy
      _ = a • (Φ k).val.app (op W) ⟨_, h1⟩ := ((Φ k).val.app (op W)).hom.map_smul a _
      _ = a • chartRestrictLinear G g (b k) := congrArg (a • ·) (hΨ k W g _)
  have hJq : J.toSheafOfModules.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_idealPowModule B S hS Y I _ hZt hN hIq
      (isCoherent_structureSheaf B S hS Y.1 Y.2) N
  clear_value Φ J
  have hInon : (idealUnitLocus B S hS Y I).Nonempty := hul ▸ hRne
  have hmapC : ∀ W : SmallEtale B S hS Y.1, I.obj (op W) = ⊤ → Nonempty (W ⟶ C) :=
    fun W hWtop => nonempty_hom_of_range_subset hCoi
      ((range_subset_idealUnitLocus_of_eq_top B S hS Y I W hWtop).trans hul.le)
  -- injectivity over the affine charts carrying the unit ideal
  have hmono : Mono (biproduct.desc Φ) :=
    mono_biproduct_desc_of_injective_on_affine_idealUnitCharts B S hS Y hred hirr I hInon J Φ
      (forall_eq_zero_of_sum_val_app_eq_zero_of_val_app_eq_smul B S hS Y hCaff hGcart b I J Φ
        hmapC hval)
  -- surjectivity over the affine charts carrying the unit ideal
  have hsurj := exists_biproduct_desc_val_app_eq_of_val_app_eq_smul B S hS Y hCaff hGcart b I J Φ
    hmapC hmem hval
  have hcok := (supportOfSheaf_cokernel_subset_idealZeroLocus_of_surjective_affine B S hS Y I
    (biproduct.desc Φ) hsurj).trans hzl.le
  -- the map is not zero, because the support of `G` is everything
  have hnz : biproduct.desc Φ ≠ 0 := by
    intro h0
    have _ := cokernel.π_of_zero h0
    have hGT : supportOfSheaf B S hS Y.1 ((SheafOfModules.toSheaf _).obj G) ⊆ T := by
      rw [supportOfSheaf_eq_of_iso B S hS Y
        (asIso (cokernel.π (C := Modules.{u, u} B S hS Y.1 Y.2) (biproduct.desc Φ)))]
      exact hcok
    exact hTne (Set.eq_univ_of_univ_subset (hsupp ▸ hGT))
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · exfalso
      subst hn0
      exact hnz (biproduct.hom_ext' _ _ fun j => j.elim0)
    · exact hn0
  have hJne : J ≠ ⊥ := by
    intro hJ
    subst hJ
    refine hnz (biproduct.hom_ext' _ _ fun j => ?_)
    rw [comp_zero]
    exact (SheafOfModules.Submodule.isZero_toSheafOfModules_bot _).eq_of_src _ _
  exact ⟨n, J, hJq, hn, hJne, biproduct.desc Φ, hmono,
    cokernel (C := Modules.{u, u} B S hS Y.1 Y.2) (biproduct.desc Φ),
    cokernel.π (C := Modules.{u, u} B S hS Y.1 Y.2) (biproduct.desc Φ), cokernel.condition _,
    ⟨cokernelIsCokernel _⟩, T, hT, hTne, hcok⟩

end Integral

/-! ### Direct images along a closed immersion -/

section Pushforward

variable {Z X : AlgebraicSpaces B S hS}

/-- **The direct image of a quasi-coherent sheaf of ideals along a closed immersion into a
locally Noetherian algebraic space is coherent.**  It is a quasi-coherent submodule of the
direct image `i_*𝒪_Z`, which is coherent by
`AlgebraicGeometry.Space.isCoherent_structureSheafPushforward`, so this is the submodule clause
of [Stacks, Tag 07UD]. -/
theorem isCoherent_modulePushforward_quasicoherentIdeal
    (hX : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom) (I : QuasicoherentIdeals B S hS Z) :
    IsCoherent B S hS X.1 X.2 ((modulePushforward B S hS i).obj I.1.toSheafOfModules) := by
  have : Fact (HasEtaleLocalProperty B S hS X.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨hX⟩
  have _ : Mono ((modulePushforward B S hS i).map I.1.ι) :=
    mono_modulePushforward_map B S hS i _ (SheafOfModules.Submodule.mono_ι_via_forget I.1)
  exact isCoherent_of_mono_of_isQuasicoherentOnSite B S hS X.1 X.2
    ((modulePushforward B S hS i).map I.1.ι)
    (isQuasicoherentOnSite_modulePushforward_of_isClosedImmersion B S hS i hi _ I.2)
    (isCoherent_structureSheafPushforward B S hS hX i hi)

/-- **A closed subspace of a Noetherian algebraic space is Noetherian**: it is quasi-compact
because an immersion into a Noetherian space has quasi-compact source, quasi-separated because a
closed immersion is, and locally Noetherian because a closed immersion is locally of finite
type. -/
theorem isNoetherian_closedSubfunctor (hZt : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hX : IsNoetherian B S hS hZt X.1) {Z : Subfunctor X.1}
    (hZ : IsClosedSubspace B S hS Z) : IsNoetherian B S hS hZt Z.toFunctor :=
  ⟨isQuasiCompactSpace_of_isImmersion_of_isNoetherian B S hS hZt X.2 hZ.1 hX Z.ι
      (isImmersion_of_isClosedImmersion B S hS hZ.2),
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZt hZ.1 hX.2.1
      (isQuasiSeparated_of_isClosedImmersion B S hS hZ.2),
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hZ.1 X.2 Z.ι
      (isLocallyOfFiniteType_of_isClosedImmersion B S hS Z.ι hZ.2) hX.2.2⟩

end Pushforward

/-! ### [Stacks, Tag 07UQ] -/

section Tag07UQ

variable (hZt : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS)

/-- **[Stacks, Tag 07UQ].**  Let `X` be a Noetherian algebraic space over `S` and let `ℱ` be a
coherent `𝒪_X`-module whose scheme-theoretic support `i : Z → X` is reduced with `|Z|`
irreducible.  Then there are an integer `r > 0`, a nonzero quasi-coherent sheaf of ideals
`ℐ ⊆ 𝒪_Z` and an injective map of coherent modules `i_*(ℐ^{⊕ r}) → ℱ` whose cokernel is
supported on a proper closed subspace of `Z`, namely on the image of a closed `T ⊊ |Z|`.

The scheme-theoretic support is a closed subspace (it is part of the conclusion), `ℱ = i_*𝒢` for
a quasi-coherent `𝒪_Z`-module `𝒢` by [Stacks, Tag 07U0], `𝒢` is coherent by
[Stacks, Tag 07UG], and its support is all of `|Z|` because the support of `ℱ` is the image of
`|Z|` and `i` is injective on points.  The case `Z = X`,
`AlgebraicGeometry.Space.exists_mono_biproduct_idealSheaf_cokernel_support_subset`, applies to
`𝒢` on the Noetherian space `Z`; the direct image is exact, so it keeps the injection and
carries the cokernel to the cokernel, whose support is then in the image of `T`.  The source
`i_*(ℐ^{⊕ r})` is quasi-coherent, the direct image along a closed immersion preserving
quasi-coherence, and it is a submodule of the coherent `ℱ`, hence coherent by
[Stacks, Tag 07UD]. -/
@[stacks 07UQ]
theorem exists_mono_modulePushforward_idealSum_of_schemeTheoreticSupport
    (noeth : IsNoetherian B S hS hZt X.1) (F : Modules.{u, u} B S hS X.1 X.2)
    (coh : IsCoherent B S hS X.1 X.2 F)
    (redIrr : IsReducedIrreducible B S hS (schemeTheoreticSupport B S hS X F)) :
    ∃ hZ : IsClosedSubspace B S hS (schemeTheoreticSupport B S hS X F),
      ∃ (r : ℕ) (I : (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
          (closedSubfunctorSpace B S hS hZ).1 (closedSubfunctorSpace B S hS hZ).2).O))).Submodule),
        I.toSheafOfModules.IsQuasicoherentOnSite ∧ 0 < r ∧ I ≠ ⊥ ∧
        IsCoherent B S hS X.1 X.2 ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj
          (⨁ fun _ : Fin r => I.toSheafOfModules)) ∧
        ∃ φ : (modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj
            (⨁ fun _ : Fin r => I.toSheafOfModules) ⟶ F, Mono φ ∧
          ∃ (Q : Modules.{u, u} B S hS X.1 X.2) (q : F ⟶ Q) (w : φ ≫ q = 0),
            Nonempty (IsColimit (CokernelCofork.ofπ q w)) ∧
            ∃ T : Set (points B S hS (schemeTheoreticSupport B S hS X F).toFunctor),
              IsClosed T ∧ T ≠ Set.univ ∧
              supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj Q) ⊆
                pointsMap B S hS _ (closedSubfunctorι B S hS hZ).hom '' T := by
  have _ := coh
  have hfact : Fact (HasEtaleLocalProperty B S hS X.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨noeth.2.2⟩
  have hFft : SheafOfModules.IsFiniteTypeOnSite F := isFiniteTypeOnSite_of_isCoherentOnSite B S hS X F
  obtain ⟨hZ, hid⟩ := exists_isClosedSubspace_schemeTheoreticSupport B S hS X F
    coh.toIsQuasicoherentOnSite coh.toIsCoherentOnSite.isFiniteType
  obtain ⟨hZsupp, G, hGq, ⟨eG⟩⟩ := exists_module_on_schemeTheoreticSupport B S hS X F
    coh.toIsQuasicoherentOnSite coh.toIsCoherentOnSite.isFiniteType
  let i := closedSubfunctorι B S hS hZ
  have hi : IsClosedImmersion B S hS i.hom := hZ.2
  have hGc : IsCoherent B S hS (closedSubfunctorSpace B S hS hZ).1
      (closedSubfunctorSpace B S hS hZ).2 G :=
    isCoherent_of_modulePushforward_closedSubspace B S hS X noeth.2.2 F
      ⟨schemeTheoreticSupport B S hS X F, hZ⟩ G hGq eG
  -- the support of `G` is everything
  have hGft : SheafOfModules.IsFiniteTypeOnSite G :=
    isFiniteTypeOnSite_of_isCoherentOnSite B S hS (closedSubfunctorSpace B S hS hZ) G
  have hsuppG : supportOfSheaf B S hS (closedSubfunctorSpace B S hS hZ).1
      ((SheafOfModules.toSheaf _).obj G) = Set.univ := by
    have h1 := supportOfSheaf_modulePushforward_eq_image_of_isClosedImmersion B S hS i hi G
      (isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS _ hZ.1 G)
    rw [supportOfSheaf_eq_of_iso B S hS X eG,
      supportOfSheaf_eq_range_pointsMap_schemeTheoreticSupport B S hS X F
        coh.toIsQuasicoherentOnSite hFft,
      ← Set.image_univ] at h1
    exact (Set.image_injective.2 (pointsMap_hom_injective_of_isClosedImmersion B S hS i hi)
      h1).symm
  obtain ⟨r, J, hJq, hr, hJne, ψ, hψ, Q, q, hq, ⟨hcol⟩, T, hT, hTne, hQ⟩ :=
    exists_mono_biproduct_idealSheaf_cokernel_support_subset B S hS hZt
      (closedSubfunctorSpace B S hS hZ) (isNoetherian_closedSubfunctor B S hS hZt X noeth hZ)
      redIrr.1 redIrr.2 G hGc hsuppG
  let φ := (modulePushforward B S hS i).map ψ ≫ eG.hom
  have hmono : Mono φ := by
    have h1 : Mono ((modulePushforward B S hS i).map ψ) :=
      mono_modulePushforward_map B S hS i ψ hψ
    have h2 : Mono eG.hom := mono_of_mono_fac eG.hom_inv_id
    exact mono_comp _ _
  -- the source is coherent
  have hJc : IsCoherent B S hS (closedSubfunctorSpace B S hS hZ).1
      (closedSubfunctorSpace B S hS hZ).2 J.toSheafOfModules := by
    have : Fact (HasEtaleLocalProperty B S hS (closedSubfunctorSpace B S hS hZ).1
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) :=
      ⟨(isNoetherian_closedSubfunctor B S hS hZt X noeth hZ).2.2⟩
    have _ : Mono J.ι := SheafOfModules.Submodule.mono_ι_via_forget J
    exact isCoherent_of_mono_of_isQuasicoherentOnSite B S hS _ _ J.ι hJq
      (isCoherent_structureSheaf B S hS _ _)
  have hcoh : IsCoherent B S hS X.1 X.2 ((modulePushforward B S hS i).obj
      (⨁ fun _ : Fin r => J.toSheafOfModules)) :=
    isCoherent_of_mono_of_isQuasicoherentOnSite B S hS X.1 X.2 φ
      (isQuasicoherentOnSite_modulePushforward_of_isClosedImmersion B S hS i hi _
        (isCoherent_biproductConst B S hS _ _ _ hJc r).toIsQuasicoherentOnSite) coh
  -- the cokernel
  have hTimg : IsClosed (pointsMap B S hS _ i.hom '' T) :=
    isClosedMorphism_of_isClosedImmersion B S hS hZ.1 X.2 i.hom hi T hT
  have eQ : cokernel (C := Modules.{u, u} B S hS (closedSubfunctorSpace B S hS hZ).1
      (closedSubfunctorSpace B S hS hZ).2) ψ ≅ Q :=
    (cokernelIsCokernel ψ).coconePointUniqueUpToIso hcol
  have hsupp : supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj
      (cokernel (C := Modules.{u, u} B S hS X.1 X.2) φ)) ⊆ pointsMap B S hS _ i.hom '' T := by
    have e1 : cokernel (C := Modules.{u, u} B S hS X.1 X.2) φ ≅
        cokernel (C := Modules.{u, u} B S hS X.1 X.2) ((modulePushforward B S hS i).map ψ) :=
      cokernelCompIsIso _ _
    rw [supportOfSheaf_eq_of_iso B S hS X (e1.trans (modulePushforwardCokernelIso B S hS i hi ψ))]
    refine supportOfSheaf_modulePushforward_subset_of_isClosed B S hS i _ _ hTimg ?_
    rw [supportOfSheaf_eq_of_iso B S hS _ eQ]
    exact hQ.trans (Set.subset_preimage_image _ _)
  exact ⟨hZ, r, J, hJq, hr, hJne, hcoh, φ, hmono,
    cokernel (C := Modules.{u, u} B S hS X.1 X.2) φ,
    cokernel.π (C := Modules.{u, u} B S hS X.1 X.2) φ, cokernel.condition _,
    ⟨cokernelIsCokernel _⟩, T, hT, hTne, hsupp⟩

end Tag07UQ

end AlgebraicGeometry.Space

end
