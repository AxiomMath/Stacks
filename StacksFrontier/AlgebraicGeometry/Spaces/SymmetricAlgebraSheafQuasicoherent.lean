module

public import StacksFrontier.AlgebraicGeometry.Spaces.SymmetricAlgebraSheafAffineSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartAffineOpenCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraAntiEquivalence
public import StacksFrontier.AlgebraicGeometry.Size.FlatSurjective
public import Mathlib.Algebra.FreeAlgebra.Cardinality
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The symmetric algebra of a quasi-coherent module on an algebraic space is quasi-coherent

Let `W` be an algebraic space and `𝒢` a quasi-coherent `𝒪_W`-module.  This file proves that the
sheaf of commutative `𝒪_W`-algebras `Sym(𝒢)`
(`AlgebraicGeometry.Space.symmetricAlgebraSheaf`) is **quasi-coherent**, and that it is **of
finite presentation** when `𝒢` is.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherent_symmetricAlgebraSheaf`: `Sym(𝒢)` is quasi-coherent.
* `AlgebraicGeometry.Space.isFinitePresentation_symmetricAlgebraSheaf`: `Sym(𝒢)` is of finite
  presentation when `𝒢` is.
* `AlgebraicGeometry.Space.sectionsBelowCutoff_symmetricAlgebraSheaf`: for `𝒢` quasi-coherent of
  finite presentation, `Sym(𝒢)` has fewer than `B.cutoff` sections over every étale chart.

## References

* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.PresheafOfModules Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The comparison morphism from the objectwise direct sum of the homogeneous pieces of a sheaf of
graded `𝒪_W`-algebras to the module underlying its ungraded realization: the sheafification unit
of the ungraded realization on sections. -/
def gradedDirectSumHom (W : AlgebraicSpaces B S hS)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS W))
    (hc : ∀ (i j : ℤ) (V : (SmallEtale B S hS W.1)ᵒᵖ) (a : (A.piece i).val.obj V)
      (b : (A.piece j).val.obj V), HEq ((A.mul i j).app V a b) ((A.mul j i).app V b a)) :
    Stacks.directSum (R := (structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat)
        (fun n : ℤ => (A.piece n).val) ⟶
      (AlgebraSheaf.underlyingModule (gradedAlgebraSheaf B S hS W A hc)).val where
  app X :=
    letI : Module (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj X)
        ((AlgebraSheaf.underlyingModule (gradedAlgebraSheaf B S hS W A hc)).val.obj X) :=
      ((AlgebraSheaf.underlyingModule (gradedAlgebraSheaf B S hS W A hc)).val.obj X).isModule
    ModuleCat.ofHom
      (X := (Stacks.directSum
        (R := (structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat)
        (fun n : ℤ => (A.piece n).val)).obj X)
      (Y := (AlgebraSheaf.underlyingModule (gradedAlgebraSheaf B S hS W A hc)).val.obj X)
    { toFun := fun z => A.toPresheafGradedAlgebra.totalUnit (SmallEtale.topology B S hS W.1) X z
      map_add' := fun z z' => map_add _ z z'
      map_smul' := fun r z => A.toPresheafGradedAlgebra.map_smul_totalPresheaf
        A.ungradedStructureMap (A.toPresheafGradedAlgebra.toTotalSheaf _) rfl X r z }
  naturality {X Y} f := by
    refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
    exact CategoryTheory.congr_fun
      ((A.toPresheafGradedAlgebra.toTotalSheaf (SmallEtale.topology B S hS W.1)).naturality f) z

variable (W : AlgebraicSpaces B S hS) (G : SheafOfModules.{u} (structureRingSheaf B S hS W))

/-- The homogeneous pieces of `Sym(𝒢)` are cartesian between affine charts, for `𝒢`
quasi-coherent. -/
theorem isIso_restrictionBaseChange_symmetricAlgebra_piece (hG : G.IsQuasicoherentOnSite) (n : ℤ)
    (U V : SmallEtale B S hS W.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS W.1 ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((SmallEtale.toOver B S hS W.1 ⋙ BigFppfOver.toScheme B S hS).obj V))
    (f : V ⟶ U) :
    IsIso (restrictionBaseChange.{u + 1, u, u, u} (R := structurePresheaf B S hS W.1)
      ((symmetricAlgebra B S hS W G).piece n).val f.op) := by
  have := isIso_restrictionBaseChange_val_of_isQuasicoherentOnSite B S hS W G hG U V hU hV f
  exact (isIso_restrictionBaseChange_iff_of_bijective_app
    (PresheafOfModules.sheafifyUnit.{u, u + 1, u, u} (R := structureRingSheaf B S hS W)
      (𝟙 (structureRingSheaf B S hS W).obj) (PresheafOfModules.symPowInt n G.val)) f.op
    (bijective_symmetricAlgebra_sheafifyUnit_of_isAffine B S hS W G hG n U hU)
    (bijective_symmetricAlgebra_sheafifyUnit_of_isAffine B S hS W G hG n V hV)).1
    (isIso_restrictionBaseChange_symPowInt (O := structurePresheaf B S hS W.1) n G.val f.op)

/-- **`Sym(𝒢)` is a quasi-coherent sheaf of `𝒪_W`-algebras** for `𝒢` quasi-coherent. -/
@[ega "II 1.7.7" "more general"]
theorem isQuasicoherent_symmetricAlgebraSheaf (hG : G.IsQuasicoherentOnSite) :
    (symmetricAlgebraSheaf B S hS W G).IsQuasicoherent := by
  refine (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS W.1 W.2 _).2
    fun U V hU hV f => ?_
  refine (bijective_sectionsBaseChange_iff_isIso_restrictionBaseChange B S hS W.1 W.2 _ f).2 ?_
  have hD : IsIso (restrictionBaseChange.{u + 1, u, u, u} (R := structurePresheaf B S hS W.1)
      (Stacks.directSum (fun n : ℤ => ((symmetricAlgebra B S hS W G).piece n).val)) f.op) :=
    isIso_restrictionBaseChange_colimit (structurePresheaf B S hS W.1)
      (Discrete.functor fun n : ℤ => ((symmetricAlgebra B S hS W G).piece n).val)
      (Stacks.directSumCofan _) (Stacks.directSumIsColimit _) f.op
      (fun ⟨n⟩ => isIso_restrictionBaseChange_symmetricAlgebra_piece B S hS W G hG n U V hU hV f)
  exact (isIso_restrictionBaseChange_iff_of_bijective_app
    (gradedDirectSumHom B S hS W (symmetricAlgebra B S hS W G)
      (symmetricAlgebra_mul_comm B S hS W G)) f.op
    (bijective_totalUnit_of_isAffine B S hS W (symmetricAlgebra B S hS W G) U hU)
    (bijective_totalUnit_of_isAffine B S hS W (symmetricAlgebra B S hS W G) V hV)).1 hD

/-- **`Sym(𝒢)` is of finite presentation** for `𝒢` quasi-coherent of finite presentation. -/
theorem isFinitePresentation_symmetricAlgebraSheaf (hG : G.IsQuasicoherentOnSite)
    (hfp : SheafOfModules.IsFinitePresentationOnSite G) :
    (symmetricAlgebraSheaf B S hS W G).IsFinitePresentation := fun V hV =>
  finitePresentation_symmetricAlgebraSheaf_algebraMap B S hS W G hG V hV
    (module_finitePresentation_sections_of_isFinitePresentationOnSite G hG hfp V hV)

/-! ### The size of the sections -/

/-- The sections of a sheaf of algebras over an étale chart inject into the product of its
sections over the affine opens of the chart. -/
theorem AlgebraSheaf.mk_sections_le_mk_pi_affineOpens (A : AlgebraSheaf.{u, u} B S hS W.1 W.2)
    (V : SmallEtale B S hS W.1) :
    #(A.right.obj.obj (op V)) ≤
      #(∀ W' : (chartScheme V).affineOpens,
        A.right.obj.obj (op ((chartOpens B S hS V).obj (W' : (chartScheme V).Opens)))) := by
  classical
  let incl : ∀ W' : (chartScheme V).affineOpens,
      (chartOpens B S hS V).obj (W' : (chartScheme V).Opens) ⟶ V := fun W' =>
    ObjectProperty.homMk (CostructuredArrow.homMk
      (chartOpenOverι B S hS V (W' : (chartScheme V).Opens)) rfl)
  have hcov : Sieve.ofArrows (fun W' : (chartScheme V).affineOpens =>
      (chartOpens B S hS V).obj (W' : (chartScheme V).Opens)) incl ∈
      SmallEtale.topology B S hS W.1 V := by
    refine SmallEtale.ofArrows_mem_topology B S hS W.1 _ _ ?_
    refine Scheme.ofArrows_mem_etalePrecoverage_iff.2 ⟨fun x => ?_, fun W' => ?_⟩
    · obtain ⟨U', hU', hxU', -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
        (chartScheme V).isBasis_affineOpens) (show x ∈ (⊤ : (chartScheme V).Opens) from trivial)
      refine ⟨⟨U', hU'⟩, ?_⟩
      show x ∈ Set.range (Scheme.Opens.ι (X := chartScheme V) U')
      rwa [Scheme.Opens.range_ι]
    · exact inferInstanceAs
        (_root_.AlgebraicGeometry.Etale (W' : (chartScheme V).Opens).ι)
  have hsheaf : Presieve.IsSheaf (SmallEtale.topology B S hS W.1)
      (A.right.obj ⋙ CategoryTheory.forget CommRingCat.{u}) :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      (GrothendieckTopology.HasSheafCompose.isSheaf _ A.right.property)
  refine Cardinal.mk_le_of_injective (f := fun x W' => A.right.obj.map (incl W').op x)
    fun x y hxy => ?_
  refine (hsheaf.isSeparated _ hcov).ext fun Z g hg => ?_
  obtain ⟨Y, h, k, ⟨W'⟩, rfl⟩ := hg
  rw [op_comp, Functor.map_comp]
  exact congrArg ((A.right.obj ⋙ CategoryTheory.forget CommRingCat.{u}).map h.op)
    (congrFun hxy W')

/-- The symmetric algebra of a module has at most `max (#R) (#M) ℵ₀` elements. -/
theorem mk_symmetricAlgebra_le {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M] :
    #(SymmetricAlgebra R M) ≤ #R ⊔ #M ⊔ ℵ₀ := by
  have hsurj : Function.Surjective (FreeAlgebra.lift R (SymmetricAlgebra.ι R M)) := by
    intro x
    induction x using SymmetricAlgebra.induction with
    | algebraMap r => exact ⟨algebraMap R _ r, AlgHom.commutes _ r⟩
    | ι m => exact ⟨FreeAlgebra.ι R m, FreeAlgebra.lift_ι_apply _ m⟩
    | mul x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a * b, map_mul _ a b⟩
    | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, map_add _ a b⟩
  exact (Cardinal.mk_le_of_surjective hsurj).trans (FreeAlgebra.cardinalMk_le_max R M)

/-- A finitely generated module has at most `max (#R) ℵ₀` elements. -/
theorem mk_le_of_module_finite {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] : #M ≤ #R ⊔ ℵ₀ := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  refine (Cardinal.mk_le_of_surjective hf).trans ?_
  rw [Cardinal.mk_arrow, Cardinal.lift_uzero, Cardinal.mk_fin, Cardinal.lift_natCast]
  exact Cardinal.power_nat_le_max

/-- **`Sym(𝒢)` has fewer than `B.cutoff` sections over every étale chart**, for `𝒢`
quasi-coherent of finite presentation. -/
theorem sectionsBelowCutoff_symmetricAlgebraSheaf (hG : G.IsQuasicoherentOnSite)
    (hfp : SheafOfModules.IsFinitePresentationOnSite G) :
    AlgebraSheaf.SectionsBelowCutoff B S hS (symmetricAlgebraSheaf B S hS W G) := by
  intro V
  have hV : B.Contains (chartScheme V) := V.obj.left.left.property
  set κ : Cardinal.{u} := 2 ^ (chartScheme V).size ⊔ ℵ₀ with hκ
  have hκlt : κ < B.cutoff := max_lt (B.cutoff_isStrongPrelimit hV) B.aleph0_lt_cutoff
  have hκ0 : ℵ₀ ≤ κ := le_sup_right
  have hκ2 : 2 ^ (chartScheme V).size ≤ κ := le_sup_left
  have hbound : ∀ W' : (chartScheme V).affineOpens,
      #((symmetricAlgebraSheaf B S hS W G).right.obj.obj
        (op ((chartOpens B S hS V).obj (W' : (chartScheme V).Opens)))) ≤ κ := by
    intro W'
    set O := (chartOpens B S hS V).obj (W' : (chartScheme V).Opens)
    have hW' : IsAffine ((SmallEtale.toOver B S hS W.1 ⋙ BigFppfOver.toScheme B S hS).obj O) :=
      W'.2
    have hR : #(((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj
        (op O)) ≤ κ :=
      ((Scheme.mk_sections_le_two_pow_size _ ⊤).trans
        (Cardinal.power_le_power_left two_ne_zero
          (Scheme.size_coe_opens_le (chartScheme V) (W' : (chartScheme V).Opens)))).trans hκ2
    have hfin : Module.Finite
        (((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat RingCat).obj (op O))
        ((commStructureVal B S hS G).obj (op O)) :=
      have hfp' := module_finitePresentation_sections_of_isFinitePresentationOnSite G hG hfp _ hW'
      ⟨by obtain ⟨s, hs, -⟩ := hfp'.out; exact ⟨s, hs⟩⟩
    rw [← Cardinal.mk_congr (symmetricAlgebraSheafSectionsRingEquiv B S hS W G hG _ hW').toEquiv]
    exact mk_symmetricAlgebra_le.trans (max_le (max_le hR
      (mk_le_of_module_finite.trans (max_le hR hκ0))) hκ0)
  refine (AlgebraSheaf.mk_sections_le_mk_pi_affineOpens B S hS W _ V).trans_lt ?_
  rw [Cardinal.mk_pi]
  refine (Cardinal.prod_le_prod _ _ hbound).trans_lt ?_
  rw [Cardinal.prod_const']
  calc κ ^ #(chartScheme V).affineOpens ≤ κ ^ κ :=
        Cardinal.power_le_power_left (Cardinal.aleph0_pos.trans_le hκ0).ne'
          ((chartScheme V).mk_affineOpens_le_size.trans ((Cardinal.cantor _).le.trans hκ2))
    _ = 2 ^ κ := Cardinal.power_self_eq hκ0
    _ < B.cutoff := B.cutoff_isStrongPrelimit hκlt

end AlgebraicGeometry.Space

end
