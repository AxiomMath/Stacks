module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import StacksCore.Algebra.Homology.ShortComplex.ShortExact
public import StacksCore.Topology.Compact.ClosedPoints
public import StacksCore.Topology.Compact.ClosedSubsets
public import StacksFrontier.Algebra.Homology.DerivedCategory.InverseLimitHelpers
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.GlobalGeneration.Stalks
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CanonicalSectionsMap
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.BiproductQuasicoherent
public import StacksFrontier.Topology.Sheaves.Functors.Module.SemilinearStalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Serre's criterion for affineness

A quasi-compact scheme is affine if the first cohomology of every quasi-coherent ideal sheaf
vanishes.

## Main results

* `Stacks.SerreCriterionH1.idealSpan_eq_top_of_finite_basicOpen_cover`: if the first cohomology of
  every quasi-coherent ideal sheaf vanishes, then finitely many global sections whose basic open
  sets cover `X` generate the unit ideal of `Γ(X, ⊤)`.
* `Stacks.SerreCriterionH1.exists_affine_basicOpen_mem_of_forall_isZero_H1_ideal`: under the same
  hypothesis, if `X` is quasi-compact and $T_0$, then every point of `X` lies in an affine basic
  open set `X.basicOpen f` of a global section `f`.

## Implementation notes

An ideal sheaf is represented by a subobject of the structure sheaf in the abelian category of
sheaves of modules. Its first cohomology is the first right derived functor of evaluation on the
top open set. Vanishing is expressed categorically by `IsZero`.

## References

* [Serre-criterion]
* [EGA, II, Theorem 5.2.1 (d') and IV (1.7.17)]
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Scheme.Modules
open scoped AlgebraicGeometry ZeroObject

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.SerreCriterionH1

/-- Evaluation of sheaves of modules on `X` at an open set `U` is an additive functor. -/
noncomputable local instance evaluationAdditive (X : AlgebraicGeometry.Scheme.{u})
    (U : X.Opensᵒᵖ) : (SheafOfModules.evaluation X.ringCatSheaf U).Additive where
  map_add := rfl

private theorem epi_evaluation_map_of_isZero_rightDerived_kernel
    {X : AlgebraicGeometry.Scheme.{u}} {M N : SheafOfModules X.ringCatSheaf} (q : M ⟶ N) [Epi q]
    (h : IsZero (((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).rightDerived 1).obj
      (kernel q))) :
    Epi ((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).map q) :=
  Functor.epi_map_g _ (ShortComplex.shortExact_mk_kernel_ι q)
    (h.of_iso (CategoryTheory.rightDerivedPlusObjIso _ (kernel q) 1))

/-- A quasi-coherent source of a monomorphism into `M` has vanishing `R¹` if all quasi-coherent
subobjects of `M` do. -/
private theorem isZero_rightDerived1_of_mono {X : AlgebraicGeometry.Scheme.{u}}
    {M B : SheafOfModules X.ringCatSheaf} (u : B ⟶ M) [Mono u] (hB : B.IsQuasicoherent)
    (hM : ∀ J : Subobject M, (Subobject.underlying.obj J).IsQuasicoherent →
      IsZero (((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).rightDerived 1).obj
        (Subobject.underlying.obj J))) :
    IsZero (((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).rightDerived 1).obj B) :=
  (hM (Subobject.mk u) ((SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Subobject.underlyingIso u).symm hB)).of_iso
      (((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).rightDerived 1).mapIso
        (Subobject.underlyingIso u).symm)

private theorem isZero_evaluation_rightDerived1_middle_of_endpoints
    (X : AlgebraicGeometry.Scheme.{u})
    (S : ShortComplex (SheafOfModules X.ringCatSheaf)) (hS : S.ShortExact)
    (h₁ : IsZero (((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).rightDerived 1).obj
      S.X₁))
    (h₃ : IsZero (((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).rightDerived 1).obj
      S.X₃)) :
    IsZero (((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).rightDerived 1).obj
      S.X₂) := by
  let E := SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)
  exact (Functor.isZero_rightDerivedPlus_X₂ E hS 1
    (h₁.of_iso (CategoryTheory.rightDerivedPlusObjIso E S.X₁ 1))
    (h₃.of_iso (CategoryTheory.rightDerivedPlusObjIso E S.X₃ 1))).of_iso
    (CategoryTheory.rightDerivedPlusObjIso E S.X₂ 1).symm

private theorem epi_evaluation_structureSheafMap_of_isZero_H1_ideal
    (X : AlgebraicGeometry.Scheme.{u})
    (hH₁ : ∀ (I : Subobject (SheafOfModules.unit X.ringCatSheaf)),
      (Subobject.underlying.obj I).IsQuasicoherent →
        IsZero (((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).rightDerived 1).obj
          (Subobject.underlying.obj I)))
    (D : X.IdealSheafData) :
    Epi ((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).map
      (SheafOfModules.unitToPushforwardObjUnit D.subschemeι.toRingCatSheafHom)) := by
  let q := SheafOfModules.unitToPushforwardObjUnit D.subschemeι.toRingCatSheafHom
  have : Epi q :=
    Stacks.AlgebraicGeometry.ClosedImmersionTFAE.epi_unitToPushforwardObjUnit_of_isClosedImmersion
      D.subschemeι
  exact epi_evaluation_map_of_isZero_rightDerived_kernel q
    (isZero_rightDerived1_of_mono (kernel.ι q) inferInstance hH₁)

private theorem imageSubobject_isQuasicoherent
    (X : AlgebraicGeometry.Scheme.{u}) {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    (Subobject.underlying.obj (imageSubobject f)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Subobject.underlyingIso (image.ι f)).symm (AlgebraicGeometry.isQuasicoherent_image f)

private lemma nonempty_presentation_spec (R : CommRingCat.{u})
    (M : (Spec R).Modules) [M.IsQuasicoherent] : Nonempty M.Presentation :=
  ⟨@SheafOfModules.Presentation.ofIsIso.{u, u, u} _ _ _ _ _ _ _ _ M.fromTildeΓ
    (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M)
    (presentationTilde (moduleSpecΓFunctor.obj M) Set.univ (by simp) _ (Submodule.span_eq _))⟩

private lemma nonempty_presentation_of_isAffine (X : Scheme.{u}) [IsAffine X]
    (M : X.Modules) [M.IsQuasicoherent] : Nonempty M.Presentation := by
  let e := X.isoSpec
  let N := M.restrict e.inv
  let P := presentationRestrict e.hom (nonempty_presentation_spec _ N).some
  let eP := ((restrictFunctorComp e.hom e.inv).symm ≪≫
    restrictFunctorCongr e.hom_inv_id ≪≫ restrictFunctorId).app M
  exact ⟨@SheafOfModules.Presentation.ofIsIso.{u, u, u} _ _ _ _ _ _ _ _ eP.hom
    (Iso.isIso_hom eP) P⟩

private lemma isQuasicoherent_of_affine_restrict (X : Scheme.{u}) (M : X.Modules)
    (h : ∀ U : X.Opens, IsAffineOpen U → (M.restrict U.ι).IsQuasicoherent) :
    M.IsQuasicoherent := by
  obtain ⟨S, hS, hcov⟩ := Opens.isBasis_iff_cover.mp X.isBasis_affineOpens ⊤
  let U : S → X.Opens := fun i ↦ i.1
  have cov : (Opens.grothendieckTopology X).CoversTop U := by
    rw [Opens.coversTop_iff, IsOpenCover]
    exact (sSup_eq_iSup' S).symm.trans hcov.symm
  refine SheafOfModules.QuasicoherentData.isQuasicoherent.{u, u, u, u} (M := M)
    (SheafOfModules.QuasicoherentData.mk (M := M) S U cov (fun i ↦ ?_))
  have : (M.restrict (U i).ι).IsQuasicoherent := h (U i) (hS i.2)
  have : IsAffine (U i).toScheme := hS i.2
  have : ((overEquiv (U i)).inverse).IsEquivalence :=
    (overEquiv (U i)).isEquivalence_inverse
  let F := (overEquiv (U i)).inverse
  have hF : PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1} F :=
    ((overEquiv (U i)).symm.toAdjunction).leftAdjoint_preservesColimits.{u, u}
  let P₀ := (nonempty_presentation_of_isAffine _ (M.restrict (U i).ι)).some
  let η := (Opens.sheafOfModulesEquivOverInverseUnit (U i) X.ringCatSheaf).symm
  let P := @SheafOfModules.Presentation.map _ _ _ _ _ _ _ _ _ _ _ _ _ P₀ F hF η
  exact P.ofIsIso (((overEquiv (U i)).inverse.mapIso
    ((overFunctorEquiv (U i)).app M).symm) ≪≫
      ((overEquiv (U i)).unitIso.app (M.over (U i))).symm).hom

private lemma isQuasicoherent_kernel {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) : (kernel f).IsQuasicoherent := by
  refine isQuasicoherent_of_affine_restrict X (kernel f) fun U hU => ?_
  have : IsAffine U.toScheme := hU
  have : PreservesFiniteLimits (Scheme.Modules.restrictFunctor U.ι) :=
    Stacks.LocalCohomology.preservesFiniteLimits_restrictFunctor U.ι
  exact (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
    (PreservesKernel.iso (Scheme.Modules.restrictFunctor U.ι) f).symm inferInstance

private theorem isZero_rightDerived1_subobject_biprod
    (X : AlgebraicGeometry.Scheme.{u})
    (hH₁ : ∀ (I : Subobject (SheafOfModules.unit X.ringCatSheaf)),
      (Subobject.underlying.obj I).IsQuasicoherent →
        IsZero (((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).rightDerived 1).obj
          (Subobject.underlying.obj I)))
    (M : SheafOfModules X.ringCatSheaf)
    (hMqc : M.IsQuasicoherent)
    (hM : ∀ (J : Subobject M), (Subobject.underlying.obj J).IsQuasicoherent →
      IsZero (((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).rightDerived 1).obj
        (Subobject.underlying.obj J)))
    (I : Subobject (M ⊞ SheafOfModules.unit X.ringCatSheaf))
    (hI : (Subobject.underlying.obj I).IsQuasicoherent) :
    IsZero (((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).rightDerived 1).obj
      (Subobject.underlying.obj I)) := by
  let p := I.arrow ≫ biprod.snd
  let q := factorThruImageSubobject p
  let S : ShortComplex (SheafOfModules X.ringCatSheaf) :=
    ShortComplex.mk (kernel.ι q) q (kernel.condition q)
  have hS : S.ShortExact := ShortComplex.shortExact_mk_kernel_ι q
  let u := kernel.ι q ≫ I.arrow ≫ biprod.fst
  have hu : Mono u := by
    rw [Preadditive.mono_iff_cancel_zero]
    intro Z f hf
    apply (cancel_mono (kernel.ι q)).1
    apply (cancel_mono I.arrow).1
    apply biprod.hom_ext
    · simpa only [u, Category.assoc, zero_comp] using hf
    · simp only [Category.assoc, zero_comp]
      show f ≫ kernel.ι q ≫ p = 0
      simpa [q] using f ≫= kernel.condition_assoc q (imageSubobject p).arrow
  have : M.IsQuasicoherent := hMqc
  have himageQC : (Subobject.underlying.obj (imageSubobject p)).IsQuasicoherent := by
    have : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
      Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X
    exact imageSubobject_isQuasicoherent X p
  exact isZero_evaluation_rightDerived1_middle_of_endpoints X S hS
    (isZero_rightDerived1_of_mono u (isQuasicoherent_kernel q) hM)
    (hH₁ (imageSubobject p) himageQC)

private theorem exists_section_indicator_of_disjoint_cover
    (Y : AlgebraicGeometry.Scheme.{u}) (A B : Y.Opens)
    (hcover : A ⊔ B = ⊤) (hdisj : A ⊓ B = ⊥) :
    ∃ s : ToType (Y.sheaf.obj.obj (Opposite.op ⊤)),
      ConcreteCategory.hom (Y.sheaf.obj.map (homOfLE (show A ≤ ⊤ from le_top)).op) s = 1 ∧
      ConcreteCategory.hom (Y.sheaf.obj.map (homOfLE (show B ≤ ⊤ from le_top)).op) s = 0 := by
  let O : Bool → Y.Opens := fun b => if b then A else B
  let sec : (b : Bool) → Γ(Y, O b) := fun b => if b then 1 else 0
  have hO : ⨆ b, O b = ⊤ := by
    rw [iSup_bool_eq]
    simpa [O] using hcover
  have hcompat : TopCat.Presheaf.IsCompatible Y.sheaf.obj O sec := by
    intro i j
    by_cases hij : i = j
    · subst j
      rw [Subsingleton.elim (Opens.infLELeft (O i) (O i)) (Opens.infLERight (O i) (O i))]
    · have hbot : O i ⊓ O j = ⊥ := by
        cases i <;> cases j <;> simp_all [O, inf_comm]
      have huniq : Unique (ToType (Y.presheaf.obj (Opposite.op (O i ⊓ O j)))) := by
        rw [hbot]
        exact CategoryTheory.Limits.Concrete.uniqueOfTerminalOfPreserves _
          (TopCat.Sheaf.isTerminalOfEmpty Y.sheaf)
      exact (huniq.uniq _).trans (huniq.uniq _).symm
  obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' O ⊤
    (fun b => homOfLE (show O b ≤ ⊤ from le_top)) hO.ge sec hcompat
  exact ⟨s, hs true, hs false⟩

private theorem exists_global_section_lift_to_closed_subscheme
    (X : AlgebraicGeometry.Scheme.{u})
    (hH₁ : ∀ (I : Subobject (SheafOfModules.unit X.ringCatSheaf)),
      (Subobject.underlying.obj I).IsQuasicoherent →
        IsZero (((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).rightDerived 1).obj
          (Subobject.underlying.obj I)))
    (D : X.IdealSheafData)
    (s : ToType (((SheafOfModules.pushforward D.subschemeι.toRingCatSheafHom).obj
      (SheafOfModules.unit D.subscheme.ringCatSheaf)).val.obj (Opposite.op ⊤))) :
    ∃ f : Γ(X, ⊤),
      ConcreteCategory.hom
        ((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).map
          (SheafOfModules.unitToPushforwardObjUnit D.subschemeι.toRingCatSheafHom)) f = s :=
  (ModuleCat.epi_iff_surjective _).mp
    (epi_evaluation_structureSheafMap_of_isZero_H1_ideal X hH₁ D) s

private theorem exists_global_section_lifting_indicator
    (X : AlgebraicGeometry.Scheme.{u})
    (hH₁ : ∀ (I : Subobject (SheafOfModules.unit X.ringCatSheaf)),
      (Subobject.underlying.obj I).IsQuasicoherent →
        IsZero (((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).rightDerived 1).obj
          (Subobject.underlying.obj I)))
    (D : X.IdealSheafData) (A B : D.subscheme.Opens)
    (hcover : A ⊔ B = ⊤) (hdisj : A ⊓ B = ⊥) :
    ∃ s : ToType (D.subscheme.sheaf.obj.obj (Opposite.op ⊤)),
      ConcreteCategory.hom (D.subscheme.sheaf.obj.map
        (homOfLE (show A ≤ ⊤ from le_top)).op) s = 1 ∧
      ConcreteCategory.hom (D.subscheme.sheaf.obj.map
        (homOfLE (show B ≤ ⊤ from le_top)).op) s = 0 ∧
      ∃ f : Γ(X, ⊤),
        ConcreteCategory.hom
          ((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).map
            (SheafOfModules.unitToPushforwardObjUnit D.subschemeι.toRingCatSheafHom)) f = s := by
  obtain ⟨s, hsA, hsB⟩ := exists_section_indicator_of_disjoint_cover D.subscheme A B hcover hdisj
  let sM : ToType (((SheafOfModules.pushforward D.subschemeι.toRingCatSheafHom).obj
    (SheafOfModules.unit D.subscheme.ringCatSheaf)).val.obj (Opposite.op ⊤)) := s
  refine ⟨s, hsA, hsB, ?_⟩
  simpa [sM] using exists_global_section_lift_to_closed_subscheme X hH₁ D sM

private theorem preimage_sup_eq_top_and_inf_eq_bot {X Y : Scheme.{u}} (i : Y ⟶ X)
    (U V : X.Opens) (x : X) (hxU : x ∈ U) (hV : (V : Set X) = {x}ᶜ)
    (hrange : Set.range i.base = (U : Set X)ᶜ ∪ {x}) :
    i ⁻¹ᵁ U ⊔ i ⁻¹ᵁ V = ⊤ ∧ i ⁻¹ᵁ U ⊓ i ⁻¹ᵁ V = ⊥ := by
  have hyW (y : Y) : i.base y ∈ (U : Set X)ᶜ ∪ {x} := by
    rw [← hrange]
    exact Set.mem_range_self y
  have hyV (y : Y) : i.base y ∈ V ↔ i.base y ≠ x := Set.ext_iff.mp hV _
  constructor
  · ext y
    show (i.base y ∈ U ∨ i.base y ∈ V) ↔ True
    refine iff_true_intro ?_
    rcases hyW y with hyZ | hyx
    · exact Or.inr ((hyV y).2 fun heq => hyZ (heq ▸ hxU))
    · exact Or.inl (hyx ▸ hxU)
  · ext y
    show (i.base y ∈ U ∧ i.base y ∈ V) ↔ False
    refine iff_false_intro ?_
    rintro ⟨hyU, hyNotx⟩
    rcases hyW y with hyZ | hyx
    · exact hyZ hyU
    · exact (hyV y).1 hyNotx hyx

/-- The basic open of the restriction of `g` to `V` is `V ⊓ Y.basicOpen g`. -/
private theorem basicOpen_res_top {Y : Scheme.{u}} (g : Γ(Y, ⊤)) (V : Y.Opens) :
    Y.basicOpen (Y.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op g) = V ⊓ Y.basicOpen g :=
  AlgebraicGeometry.Scheme.basicOpen_res _ _ _

private theorem le_basicOpen_of_res_eq_one {Y : Scheme.{u}} (g : Γ(Y, ⊤)) (V : Y.Opens)
    (h : Y.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op g = 1) :
    V ≤ Y.basicOpen g := by
  have hres := basicOpen_res_top g V
  rw [h, AlgebraicGeometry.Scheme.basicOpen_one] at hres
  exact inf_eq_left.mp hres.symm

private theorem inf_basicOpen_eq_bot_of_res_eq_zero {Y : Scheme.{u}} (g : Γ(Y, ⊤))
    (V : Y.Opens) (h : Y.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op g = 0) :
    V ⊓ Y.basicOpen g = ⊥ := by
  have hres := basicOpen_res_top g V
  rw [h, AlgebraicGeometry.Scheme.basicOpen_zero] at hres
  exact hres.symm

private theorem exists_basicOpen_containing_closedPoint_subset_affine
    (X : AlgebraicGeometry.Scheme.{u})
    (hH₁ : ∀ (I : Subobject (SheafOfModules.unit X.ringCatSheaf)),
      (Subobject.underlying.obj I).IsQuasicoherent →
        IsZero (((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).rightDerived 1).obj
          (Subobject.underlying.obj I)))
    (U : X.Opens) (_hU : AlgebraicGeometry.IsAffineOpen U)
    (x : X) (hxU : x ∈ U) (hxclosed : IsClosed ({x} : Set X)) :
    ∃ f : Γ(X, ⊤), x ∈ X.basicOpen f ∧ X.basicOpen f ≤ U := by
  let W : TopologicalSpace.Closeds X :=
    ⟨(U : Set X)ᶜ ∪ {x}, (U.isOpen.isClosed_compl).union hxclosed⟩
  let D : X.IdealSheafData := AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal W
  let i := D.subschemeι
  let Xminusx : X.Opens := ⟨({x} : Set X)ᶜ, hxclosed.isOpen_compl⟩
  let A : D.subscheme.Opens := i ⁻¹ᵁ U
  let B : D.subscheme.Opens := i ⁻¹ᵁ Xminusx
  have hrange : Set.range i.base = (W : Set X) := by
    show Set.range (D.subschemeι : D.subscheme → X) = (W : Set X)
    rw [AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι]
    simp [D, W]
  obtain ⟨hcover, hdisj⟩ := preimage_sup_eq_top_and_inf_eq_bot i U Xminusx x hxU rfl hrange
  obtain ⟨s, hsA, hsB, ⟨f, hf⟩⟩ :=
    exists_global_section_lifting_indicator X hH₁ D A B hcover hdisj
  have hf' : i.appTop f = s := hf
  have hA_le : A ≤ D.subscheme.basicOpen (i.appTop f) :=
    le_basicOpen_of_res_eq_one _ A (by rwa [hf'])
  have hB_disj : B ⊓ D.subscheme.basicOpen (i.appTop f) = ⊥ :=
    inf_basicOpen_eq_bot_of_res_eq_zero _ B (by rwa [hf'])
  obtain ⟨y, hy⟩ : x ∈ Set.range i.base := hrange ▸ (Or.inr rfl : x ∈ (W : Set X))
  refine ⟨f, ?_, ?_⟩
  · have hx' : i.base y ∈ X.basicOpen f := by
      show y ∈ i ⁻¹ᵁ X.basicOpen f
      rw [AlgebraicGeometry.Scheme.Hom.preimage_basicOpen_top i f]
      exact hA_le (show i.base y ∈ U from hy ▸ hxU)
    simpa [hy] using hx'
  · intro z hz
    by_contra hzu
    obtain ⟨y, rfl⟩ : z ∈ Set.range i.base := hrange ▸ (Or.inl hzu : z ∈ (W : Set X))
    have hyB : y ∈ B := by
      show i.base y ∉ ({x} : Set X)
      exact fun heq => hzu (Set.mem_singleton_iff.mp heq ▸ hxU)
    have hybasic : y ∈ D.subscheme.basicOpen (i.appTop f) := by
      rwa [← AlgebraicGeometry.Scheme.Hom.preimage_basicOpen_top i f]
    have hyinf : y ∈ B ⊓ D.subscheme.basicOpen (i.appTop f) := ⟨hyB, hybasic⟩
    simp [hB_disj] at hyinf

private theorem exists_closedPoint_in_closure
    (X : AlgebraicGeometry.Scheme.{u}) [CompactSpace X] [T0Space X] (x : X) :
    ∃ y : X, y ∈ closure ({x} : Set X) ∧ IsClosed ({y} : Set X) := by
  let C : Type u := {y : X // y ∈ closure ({x} : Set X)}
  have : CompactSpace C := isCompact_iff_compactSpace.mp isClosed_closure.isCompact
  have : Nonempty C := ⟨⟨x, subset_closure rfl⟩⟩
  obtain ⟨y, -, hyC⟩ :=
    (isClosed_univ (X := C)).exists_closed_singleton Set.univ_nonempty
  exact ⟨y, y.property, by simpa [Set.image_singleton] using
    isClosed_closure.isClosedEmbedding_subtypeVal.isClosedMap _ hyC⟩

private theorem exists_affine_basicOpen_mem_of_forall_isZero_H1_ideal
    (X : AlgebraicGeometry.Scheme.{u}) [CompactSpace X] [T0Space X]
    (hH₁ : ∀ (I : Subobject (SheafOfModules.unit X.ringCatSheaf)),
      (Subobject.underlying.obj I).IsQuasicoherent →
        IsZero (((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).rightDerived 1).obj
          (Subobject.underlying.obj I)))
    (x : X) :
    ∃ f : Γ(X, ⊤), IsAffineOpen (X.basicOpen f) ∧ x ∈ X.basicOpen f := by
  obtain ⟨y, hyx, hyclosed⟩ := exists_closedPoint_in_closure X x
  obtain ⟨U, hyU⟩ : ∃ U : X.affineOpens, y ∈ (U : X.Opens) := by
    have hyTop : y ∈ (⨆ U : X.affineOpens, (U : X.Opens)) := by
      rw [iSup_affineOpens_eq_top]
      trivial
    exact Opens.mem_iSup.mp hyTop
  obtain ⟨f, hybasic, hfU⟩ :=
    exists_basicOpen_containing_closedPoint_subset_affine X hH₁ U U.2 y hyU hyclosed
  let fU : Γ(X, U.1) := X.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op f
  have hres := basicOpen_res_top f U.1
  have hbasic : X.basicOpen f = X.basicOpen fU := by
    rw [inf_eq_right.mpr hfU] at hres
    exact hres.symm
  refine ⟨f, ?_⟩
  rw [hbasic] at hybasic ⊢
  exact ⟨(X.affineBasicOpen fU).property,
    (specializes_iff_mem_closure.mpr hyx).mem_open (X.basicOpen fU).2 hybasic⟩

private abbrev FinIndex (n : ℕ) := ULift.{u, 0} (Fin n)

private noncomputable def freePUnitIsoUnit (X : Scheme.{u}) :
    SheafOfModules.free (PUnit.{u + 1}) ≅ SheafOfModules.unit X.ringCatSheaf := by
  let F : PUnit.{u + 1} → SheafOfModules X.ringCatSheaf := fun _ =>
    SheafOfModules.unit X.ringCatSheaf
  let c : Cofan F := Cofan.mk (SheafOfModules.unit X.ringCatSheaf) fun _ => 𝟙 _
  have hc : IsColimit c := Cofan.IsColimit.mk c
    (fun t => t.inj PUnit.unit)
    (fun t ⟨⟩ => by simp [c])
    (fun t m hm => by simpa [c] using hm PUnit.unit)
  exact (SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf) PUnit).coconePointUniqueUpToIso hc

private noncomputable def freeFinSuccIso (X : Scheme.{u}) (n : ℕ) :
    (SheafOfModules.free (FinIndex n) : X.Modules) ⊞ SheafOfModules.unit X.ringCatSheaf ≅
      SheafOfModules.free (FinIndex (n + 1)) :=
  let e : FinIndex n ⊕ PUnit.{u + 1} ≃ FinIndex (n + 1) :=
    (Equiv.sumCongr (Equiv.ulift : FinIndex n ≃ Fin n)
        (Equiv.ofUnique (PUnit.{u + 1}) (Fin 1))).trans
      (finSumFinEquiv.trans Equiv.ulift.symm)
  biprod.mapIso (Iso.refl _) (freePUnitIsoUnit X).symm ≪≫
    biprod.isoCoprod _ _ ≪≫ SheafOfModules.freeSumIso (R := X.ringCatSheaf) _ _ ≪≫
      (SheafOfModules.freeFunctor (R := X.ringCatSheaf)).mapIso e.toIso

private theorem freeFin_pos_isQuasicoherent (X : Scheme.{u}) :
    ∀ n : ℕ, (SheafOfModules.free (FinIndex (n + 1)) : X.Modules).IsQuasicoherent := by
  intro n
  induction n with
  | zero =>
      let e : FinIndex 1 ≃ PUnit.{u + 1} :=
        (Equiv.ulift : FinIndex 1 ≃ Fin 1).trans (Equiv.ofUnique _ _)
      exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
        (((SheafOfModules.freeFunctor (R := X.ringCatSheaf)).mapIso e.toIso ≪≫
          freePUnitIsoUnit X).symm)
        (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X)
  | succ n ih =>
      have := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X
      exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
        (freeFinSuccIso X (n + 1)) inferInstance

private theorem isZero_rightDerived1_subobject_freeFin
    (X : AlgebraicGeometry.Scheme.{u})
    (hH₁ : ∀ (I : Subobject (SheafOfModules.unit X.ringCatSheaf)),
      (Subobject.underlying.obj I).IsQuasicoherent →
    IsZero (((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).rightDerived 1).obj
          (Subobject.underlying.obj I))) :
    ∀ n (I : Subobject (SheafOfModules.free (FinIndex (n + 1)) : X.Modules)),
      (Subobject.underlying.obj I).IsQuasicoherent →
        IsZero (((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).rightDerived 1).obj
          (Subobject.underlying.obj I)) := by
  intro n
  induction n with
  | zero =>
      intro I hI
      let e : SheafOfModules.free (FinIndex 1) ≅ SheafOfModules.unit X.ringCatSheaf :=
        (SheafOfModules.freeFunctor (R := X.ringCatSheaf)).mapIso
          ((Equiv.ulift : FinIndex 1 ≃ Fin 1).trans (Equiv.ofUnique _ _)).toIso ≪≫
            freePUnitIsoUnit X
      exact isZero_rightDerived1_of_mono (I.arrow ≫ e.hom) hI hH₁
  | succ n ih =>
      intro I hI
      exact isZero_rightDerived1_of_mono (I.arrow ≫ (freeFinSuccIso X (n + 1)).inv) hI
        (isZero_rightDerived1_subobject_biprod X hH₁
          (SheafOfModules.free (FinIndex (n + 1)) : X.Modules)
          (freeFin_pos_isQuasicoherent X n) ih)

private theorem sectionsMap_unitHomEquiv_symm_eval
    (X : Scheme.{u}) (r s : (SheafOfModules.unit X.ringCatSheaf).sections) :
    (SheafOfModules.sectionsMap ((SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm r)
      s).eval (Opposite.op ⊤) =
      @Mul.mul Γ(X, ⊤) inferInstance (r.eval (Opposite.op ⊤)) (s.eval (Opposite.op ⊤)) := by
  show @Mul.mul Γ(X, ⊤) inferInstance (s.eval (Opposite.op ⊤)) (r.eval (Opposite.op ⊤)) = _
  exact mul_comm _ _

private noncomputable def sectionFromTop
    (X : Scheme.{u}) (M : SheafOfModules X.ringCatSheaf)
    (t : ToType (M.val.obj (Opposite.op ⊤))) : M.sections :=
  ⟨fun U => M.val.presheaf.map
    (homOfLE (show U.unop ≤ ⊤ from le_top)).op t, by
    intro U V i
    let cU := (homOfLE (show U.unop ≤ ⊤ from le_top)).op
    let cV := (homOfLE (show V.unop ≤ ⊤ from le_top)).op
    have hc : cU ≫ i = cV := Subsingleton.elim _ _
    change M.val.presheaf.map i (M.val.presheaf.map cU t) =
      M.val.presheaf.map cV t
    rw [← hc, Functor.map_comp]
    exact (AddCommGrpCat.comp_apply (M.val.presheaf.map cU)
      (M.val.presheaf.map i) t).symm⟩

private theorem sectionFromTop_eval_top
    (X : Scheme.{u}) (M : SheafOfModules X.ringCatSheaf)
    (t : ToType (M.val.obj (Opposite.op ⊤))) :
    (sectionFromTop X M t).eval (Opposite.op ⊤) = t := by
  show M.val.map (homOfLE (show ⊤ ≤ ⊤ from le_top)).op t = t
  rw [show (homOfLE (show ⊤ ≤ ⊤ from le_top)).op = 𝟙 (Opposite.op ⊤) from
    Subsingleton.elim _ _]
  exact congrArg (fun f => f t) (M.val.map_id _)

private theorem span_germ_sectionFromTop_eq_top (X : Scheme.{u}) {I : Type u}
    (f : I → Γ(X, ⊤)) (x : X) (i : I) (hi : x ∈ X.basicOpen (f i)) :
    Submodule.span (R := (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X.toTopCat)
      X.ringCatSheaf.obj x : RingCat))
        (Set.range fun j ↦
          (TopCat.Presheaf.Γgerm (SheafOfModules.unit X.ringCatSheaf).val.presheaf x).hom
            ((sectionFromTop X (SheafOfModules.unit X.ringCatSheaf) (f j)).eval
              (Opposite.op ⊤))) = ⊤ := by
  let unit := SheafOfModules.unit X.ringCatSheaf
  let family : I → unit.sections := fun i => sectionFromTop X unit (f i)
  let T := (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X.toTopCat)
    X.ringCatSheaf.obj x : RingCat)
  let gmod := (TopCat.Presheaf.Γgerm unit.val.presheaf x).hom
    ((family i).eval (Opposite.op ⊤))
  let g : T := (SemilinearStalk.commStalkRingEquiv X.sheaf.obj x).symm
    (X.presheaf.germ ⊤ x (Set.mem_univ x) (f i))
  have hg : IsUnit g := RingHom.isUnit_map _ ((Scheme.mem_basicOpen_top X (f i) x).mp hi)
  let e : ToType (TopCat.Presheaf.stalk unit.val.presheaf x) ≃ₗ[T] T :=
    LocallyFreeRank.unitStalkLEquiv X.ringCatSheaf.obj x
  have hge : e gmod = g := by
    have hunit : e gmod = ConcreteCategory.hom
        (TopCat.Presheaf.germ (C := RingCat) (X := X.toTopCat) X.ringCatSheaf.obj ⊤ x
          (Set.mem_univ x)) (f i) := by
      show e ((TopCat.Presheaf.Γgerm unit.val.presheaf x).hom
        ((family i).eval (Opposite.op ⊤))) = _
      rw [show (family i).eval (Opposite.op ⊤) = f i from sectionFromTop_eval_top X unit (f i)]
      show LocallyFreeRank.unitStalkLEquiv X.ringCatSheaf.obj x
        (TopCat.Presheaf.germ unit.val.presheaf ⊤ x (Set.mem_univ x) (f i)) = _
      exact LocallyFreeRank.unitStalkLEquiv_germ X.ringCatSheaf.obj x ⊤ (Set.mem_univ x) (f i)
    rw [hunit]
    show ConcreteCategory.hom
        (TopCat.Presheaf.germ (C := RingCat) (X := X.toTopCat) X.ringCatSheaf.obj ⊤ x
          (Set.mem_univ x)) (f i) =
      (SemilinearStalk.commStalkRingEquiv X.sheaf.obj x).symm
        (X.presheaf.germ ⊤ x (Set.mem_univ x) (f i))
    exact (SemilinearStalk.commStalkRingEquiv X.sheaf.obj x).injective
      ((SemilinearStalk.commStalkRingEquiv_germ X.sheaf.obj x ⊤ (Set.mem_univ x) (f i)).trans
        ((SemilinearStalk.commStalkRingEquiv X.sheaf.obj x).apply_symm_apply _).symm)
  let J : Submodule T (ToType (TopCat.Presheaf.stalk unit.val.presheaf x)) :=
    Submodule.span (R := T) (Set.range fun j ↦
    (TopCat.Presheaf.Γgerm unit.val.presheaf x).hom
      ((family j).eval (Opposite.op ⊤)))
  have hgin : gmod ∈ J := Submodule.subset_span ⟨i, rfl⟩
  refine Submodule.eq_top_iff'.2 fun z => ?_
  have heval : e ((e z * ↑hg.unit⁻¹) • gmod) = e z := by
    rw [e.map_smul, hge, smul_eq_mul, mul_assoc, hg.val_inv_mul, mul_one]
  rw [← e.injective heval]
  exact J.smul_mem _ hgin

private theorem surjective_evaluation_map_of_epi_free (X : Scheme.{u})
    (hH₁ : ∀ (I : Subobject (SheafOfModules.unit X.ringCatSheaf)),
      (Subobject.underlying.obj I).IsQuasicoherent →
        IsZero (((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).rightDerived 1).obj
          (Subobject.underlying.obj I)))
    {I : Type u} [Finite I] [Nonempty I]
    (q : (SheafOfModules.free I : X.Modules) ⟶ SheafOfModules.unit X.ringCatSheaf) [Epi q] :
    Function.Surjective (ConcreteCategory.hom
      ((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).map q)) := by
  have := Fintype.ofFinite I
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card I = n + 1 :=
    ⟨Fintype.card I - 1, by
      have := Fintype.card_pos (α := I)
      lia⟩
  let eI : I ≃ FinIndex (n + 1) :=
    ((Fintype.equivFin I).trans (Equiv.cast (congrArg Fin hn))).trans Equiv.ulift.symm
  let eFree : (SheafOfModules.free I : X.Modules) ≅
      SheafOfModules.free (FinIndex (n + 1)) :=
    (SheafOfModules.freeFunctor (R := X.ringCatSheaf)).mapIso eI.toIso
  have : (SheafOfModules.free I : X.Modules).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso eFree.symm
      (freeFin_pos_isQuasicoherent X n)
  have : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X
  exact (ModuleCat.epi_iff_surjective _).mp
    (epi_evaluation_map_of_isZero_rightDerived_kernel q
      (isZero_rightDerived1_of_mono (kernel.ι q ≫ eFree.hom) (isQuasicoherent_kernel q)
        (isZero_rightDerived1_subobject_freeFin X hH₁ n)))

private theorem biproduct_ι_isoCoproduct_hom_freeHomEquiv_symm (X : Scheme.{u}) {I : Type u}
    [HasBiproduct (fun _ : I => SheafOfModules.unit X.ringCatSheaf)]
    (family : I → (SheafOfModules.unit X.ringCatSheaf).sections) (i : I) :
    biproduct.ι (fun _ : I => SheafOfModules.unit X.ringCatSheaf) i ≫
        (biproduct.isoCoproduct _).hom ≫
          (SheafOfModules.unit X.ringCatSheaf).freeHomEquiv.symm family =
      (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm (family i) := by
  have hi : biproduct.ι (fun _ : I => SheafOfModules.unit X.ringCatSheaf) i ≫
      (biproduct.isoCoproduct _).hom = SheafOfModules.ιFree (R := X.ringCatSheaf) i := by
    simpa only [biproduct.isoCoproduct_hom, SheafOfModules.ιFree, SheafOfModules.free]
      using biproduct.ι_desc (Sigma.ι (fun _ : I => SheafOfModules.unit X.ringCatSheaf)) i
  exact ((reassoc_of% hi) _).trans
    ((SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply _ i).symm.trans
      (congrArg (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm
        (congrFun ((SheafOfModules.unit X.ringCatSheaf).freeHomEquiv.apply_symm_apply family) i)))

private theorem eval_unitHomEquiv_comp_freeHomEquiv_symm_mem_span (X : Scheme.{u})
    {I : Type u} [Finite I] (f : I → Γ(X, ⊤))
    (η : SheafOfModules.unit X.ringCatSheaf ⟶ (SheafOfModules.free I : X.Modules))
    (r : Γ(X, ⊤)) (hr : ((SheafOfModules.unit X.ringCatSheaf).unitHomEquiv (η ≫
      (SheafOfModules.unit X.ringCatSheaf).freeHomEquiv.symm
        fun i => sectionFromTop X (SheafOfModules.unit X.ringCatSheaf) (f i))).eval
          (Opposite.op ⊤) = r) :
    r ∈ Ideal.span (Set.range f) := by
  classical
  have := Fintype.ofFinite I
  let unit := SheafOfModules.unit X.ringCatSheaf
  let family : I → unit.sections := fun i => sectionFromTop X unit (f i)
  let q := unit.freeHomEquiv.symm family
  let : HasBiproduct (fun _ : I => unit) := HasBiproduct.of_hasCoproduct _
  let B : SheafOfModules X.ringCatSheaf := ⨁ fun _ : I => unit
  let eB : B ≅ SheafOfModules.free I := biproduct.isoCoproduct _
  let a := η ≫ eB.inv
  let qB := eB.hom ≫ q
  have ha : a = ∑ i, (a ≫ biproduct.π (fun _ : I => unit) i) ≫
      biproduct.ι (fun _ : I => unit) i := by
    simp only [Category.assoc, ← Preadditive.comp_sum]
    exact ((congrArg (fun k => a ≫ k)
      (IsBilimit.total (biproduct.isBilimit (fun _ : I => unit)))).trans
        (Category.comp_id a)).symm
  have htotal : η ≫ q = ∑ i, (a ≫ biproduct.π (fun _ : I => unit) i) ≫
      (biproduct.ι (fun _ : I => unit) i ≫ qB) := by
    calc
      η ≫ q = a ≫ qB := by simp [a, qB, Category.assoc]
      _ = (∑ i, (a ≫ biproduct.π (fun _ : I => unit) i) ≫
          biproduct.ι (fun _ : I => unit) i) ≫ qB :=
          congrArg (fun k => k ≫ qB) ha
      _ = ∑ i, (a ≫ biproduct.π (fun _ : I => unit) i) ≫
          (biproduct.ι (fun _ : I => unit) i ≫ qB) := by
        simp only [Preadditive.sum_comp, Category.assoc]
  have hb (i : I) : biproduct.ι (fun _ : I => unit) i ≫ qB =
      unit.unitHomEquiv.symm (family i) :=
    biproduct_ι_isoCoproduct_hom_freeHomEquiv_symm X family i
  let c (i : I) := unit.unitHomEquiv (a ≫ biproduct.π (fun _ : I => unit) i)
  have hterm (i : I) :
      (unit.unitHomEquiv ((a ≫ biproduct.π (fun _ : I => unit) i) ≫
        (biproduct.ι (fun _ : I => unit) i ≫ qB))).eval (Opposite.op ⊤) =
          @Mul.mul Γ(X, ⊤) inferInstance (f i) ((c i).eval (Opposite.op ⊤)) := by
    rw [unit.unitHomEquiv_comp_apply, hb, sectionsMap_unitHomEquiv_symm_eval]
    exact congrArg
      (fun z : Γ(X, ⊤) => @Mul.mul Γ(X, ⊤) inferInstance z ((c i).eval (Opposite.op ⊤)))
      (sectionFromTop_eval_top X unit (f i))
  have hsum : (unit.unitHomEquiv (η ≫ q)).eval (Opposite.op ⊤) =
      ∑ i, @Mul.mul Γ(X, ⊤) inferInstance (f i) ((c i).eval (Opposite.op ⊤)) := by
    let ev : (unit ⟶ unit) →+ Γ(X, ⊤) :=
      { toFun g := (unit.unitHomEquiv g).eval (.op ⊤)
        map_zero' := rfl
        map_add' _ _ := rfl }
    show ev (η ≫ q) = _
    rw [htotal, map_sum]
    exact Finset.sum_congr rfl (fun i _ => hterm i)
  rw [← hr, hsum]
  exact Ideal.sum_mem _ fun i _ =>
    Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_range_self i))

private theorem idealSpan_eq_top_of_finite_basicOpen_cover
    (X : Scheme.{u})
    (hH₁ : ∀ (I : Subobject (SheafOfModules.unit X.ringCatSheaf)),
      (Subobject.underlying.obj I).IsQuasicoherent →
        IsZero (((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).rightDerived 1).obj
          (Subobject.underlying.obj I)))
    {I : Type u} [Fintype I] [Nonempty I]
    (f : I → Γ(X, ⊤)) (hcover : ∀ x : X, ∃ i, x ∈ X.basicOpen (f i)) :
    Ideal.span (Set.range f) = ⊤ := by
  classical
  let unit := SheafOfModules.unit X.ringCatSheaf
  let family : I → unit.sections := fun i => sectionFromTop X unit (f i)
  let q := unit.freeHomEquiv.symm family
  have hq : Epi q := (AlgebraicGeometry.generates_iff_stalkwise_generates
    (O_X := X.ringCatSheaf) (F := unit) family).2 fun x =>
      (hcover x).elim fun i hi => span_germ_sectionFromTop_eq_top X f x i hi
  let E := SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)
  obtain ⟨t, ht⟩ := surjective_evaluation_map_of_epi_free X hH₁ q
    ((1 : Γ(X, ⊤)) : ToType (E.obj unit))
  let η := (SheafOfModules.free I).unitHomEquiv.symm
    (sectionFromTop X (SheafOfModules.free I) t)
  have hval : (unit.unitHomEquiv (η ≫ q)).eval (Opposite.op ⊤) = (1 : Γ(X, ⊤)) := by
    rw [SheafOfModules.unitHomEquiv_comp_apply]
    dsimp only [η]
    rw [Equiv.apply_symm_apply]
    show ConcreteCategory.hom (E.map q)
      ((sectionFromTop X (SheafOfModules.free I) t).eval (Opposite.op ⊤)) = _
    exact (congrArg (ConcreteCategory.hom (E.map q))
      (sectionFromTop_eval_top X (SheafOfModules.free I) t)).trans ht
  exact (Ideal.eq_top_iff_one _).2
    (eval_unitHomEquiv_comp_freeHomEquiv_symm_mem_span X f η _ hval)

end Stacks.SerreCriterionH1
