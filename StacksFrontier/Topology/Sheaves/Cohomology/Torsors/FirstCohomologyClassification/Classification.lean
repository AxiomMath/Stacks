module

public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.PresheavesOfGroupsAndActions
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.AlternatingCochainGroups
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.DegreeOneComparison
public import StacksFrontier.Homology.Injectives.Sheaf.AbelianSheavesOnSpace
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.FirstCohomology
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CohomologyPresheafLocallyZero
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.FirstCohomologyClassification.TorsorClasses
public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.FirstCohomologyClassification.TransitionCocycles
import all StacksFrontier.Topology.Sheaves.Cohomology.Torsors.FirstCohomologyClassification.TorsorClasses
import all StacksFrontier.Topology.Sheaves.Cohomology.Torsors.FirstCohomologyClassification.TransitionCocycles

/-!
# Torsors and first cohomology

For an abelian sheaf `H` on a topological space `X`, isomorphism classes of
`H`-torsors are canonically in bijection with the first sheaf cohomology group
of `H`.

## Main results

* `Stacks.Cohomology.SheafTorsor.torsorClassEquivSheafCohomologyOne` is the canonical bijection
  between torsor classes and first cohomology.
* `Stacks.Cohomology.SheafTorsor.torsorClassEquivSheafCohomologyOne_of_cocycle` characterizes it
  using transition cocycles and the canonical Čech comparison.
* `Stacks.Cohomology.SheafTorsor.torsorClassEquivSheafCohomologyOne_of_global_section` and
  `Stacks.Cohomology.SheafTorsor.torsorClassEquivSheafCohomologyOne_pairing` give its compatibility
  with the trivial torsor and contracted products.

## Implementation notes

The classification is bundled with its characterizing laws in one construction
claim. Cohomology is represented by the first right-derived functor of global sections, and the
existence of the classification is proved through an injective resolution of `H`.

## References

* [Stacks Project, Tag 02FQ](https://stacks.math.columbia.edu/tag/02FQ)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

universe u v w
universe z

namespace Stacks.Cohomology.SheafTorsor

private lemma sheafSections_preservesFiniteLimits (X : TopCat.{u})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
    (U : Opens X) : PreservesFiniteLimits
      ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}).obj (op U)) := by
  show PreservesFiniteLimits (sheafToPresheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{max u v} ⋙ (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{max u v}).obj (op U))
  infer_instance

attribute [local instance] sheafSections_preservesFiniteLimits

private lemma sheaf_mono_app_injective {X : TopCat.{u}}
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
    {H A : TopCat.Sheaf AddCommGrpCat.{max u v} X} (φ : H ⟶ A) [Mono φ]
    (V : Opens X) : Function.Injective (φ.hom.app (op V)) := by
  let Γ : TopCat.Sheaf AddCommGrpCat.{max u v} X ⥤ AddCommGrpCat.{max u v} :=
    (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}).obj (op V)
  let : PreservesFiniteLimits Γ := sheafSections_preservesFiniteLimits X V
  exact (AddCommGrpCat.mono_iff_injective (Γ.map φ)).mp inferInstance

private lemma sheaf_exact_on_sections {X : TopCat.{u}}
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{max u v} X))
    (hS : S.Exact) [Mono S.f] (V : Opens X) (a : S.X₂.presheaf.obj (op V))
    (ha : S.g.hom.app (op V) a = 0) : ∃ h, S.f.hom.app (op V) h = a := by
  let Γ : TopCat.Sheaf AddCommGrpCat.{max u v} X ⥤ AddCommGrpCat.{max u v} :=
    (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}).obj (op V)
  let : Γ.Additive := sheafSections_additive X V
  let : PreservesFiniteLimits Γ := sheafSections_preservesFiniteLimits X V
  exact (S.map Γ).ab_exact_iff.mp
    (hS.map_of_mono_of_preservesKernel Γ inferInstance inferInstance) a ha

private noncomputable abbrev resolutionShortComplex {C : Type u} [Category.{v} C] [Abelian C]
    {H : C} (J : InjectiveResolution H) : ShortComplex C :=
  ShortComplex.mk (J.ι.f 0) (J.cocomplex.toCycles 0 1) (by
    rw [← cancel_mono (J.cocomplex.iCycles 1), Category.assoc,
      HomologicalComplex.toCycles_i, zero_comp]
    exact J.ι_f_zero_comp_complex_d)
private lemma resolutionShortComplex_shortExact {C : Type u} [Category.{v} C] [Abelian C]
    {H : C} (J : InjectiveResolution H) : (resolutionShortComplex J).ShortExact := by
  let S := resolutionShortComplex J
  have hE : S.Exact := by
    let φ : S ⟶ ShortComplex.mk (J.ι.f 0) (J.cocomplex.d 0 1) J.ι_f_zero_comp_complex_d :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := J.cocomplex.iCycles 1
        comm₁₂ := by
          dsimp only [S, resolutionShortComplex]
          rw [Category.id_comp, Category.comp_id]
        comm₂₃ := by simp [S, resolutionShortComplex] }
    have : Epi φ.τ₁ := by
      show Epi (𝟙 S.X₁)
      infer_instance
    have : IsIso φ.τ₂ := by
      show IsIso (𝟙 S.X₂)
      infer_instance
    have : Mono φ.τ₃ := by
      show Mono (J.cocomplex.iCycles 1)
      infer_instance
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 J.exact₀
  have hmono : Mono S.f := by
    dsimp [S, resolutionShortComplex]
    exact mono_of_isLimit_fork J.isLimitKernelFork
  have hepi : Epi S.g := by
    dsimp [S, resolutionShortComplex]
    have hepi' : Epi (J.cocomplex.sc' 0 1 2).toCycles := (J.exact_succ 0).epi_toCycles
    rw [← epi_comp_iff_of_isIso _ (J.cocomplex.cyclesIsoSc' 0 1 2 (by simp) (by simp)).hom,
      J.cocomplex.toCycles_cyclesIsoSc'_hom 0 1 2 (by simp) (by simp)]
    exact hepi'
  exact ⟨hE⟩

private lemma exists_equiv_of_surjections {A B D : Type*} (f : A → B) (g : A → D)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hfg : ∀ a a', f a = f a' ↔ g a = g a') :
    ∃ e : B ≃ D, ∀ a, e (f a) = g a := by
  classical
  choose fi hfi using hf
  choose gi hgi using hg
  refine ⟨{ toFun := fun b => g (fi b)
            invFun := fun d => f (gi d)
            left_inv := ?_
            right_inv := ?_ }, ?_⟩
  · intro b
    exact ((hfg _ _).mpr (hgi _)).trans (hfi b)
  · intro d
    exact ((hfg _ _).mp (hfi _)).trans (hgi d)
  · intro a
    exact (hfg _ _).mp (hfi _)

private def resolutionCyclesIso {C : Type u} [Category.{v} C] [Abelian C]
    {H : C} (J : InjectiveResolution H) (Γ : C ⥤ AddCommGrpCat.{w})
    [Γ.Additive] [PreservesFiniteLimits Γ] :
    Γ.obj (J.cocomplex.cycles 1) ≅
      ((Γ.mapHomologicalComplex (.up ℕ)).obj J.cocomplex).cycles 1 :=
  (KernelFork.mapIsLimit _ (J.cocomplex.cyclesIsKernel 1 2 (by simp)) Γ).conePointUniqueUpToIso
    (((Γ.mapHomologicalComplex (.up ℕ)).obj J.cocomplex).cyclesIsKernel 1 2 (by simp))

private lemma resolutionCyclesIso_hom_i {C : Type u} [Category.{v} C] [Abelian C]
    {H : C} (J : InjectiveResolution H) (Γ : C ⥤ AddCommGrpCat.{w})
    [Γ.Additive] [PreservesFiniteLimits Γ] :
    (resolutionCyclesIso J Γ).hom ≫
      ((Γ.mapHomologicalComplex (.up ℕ)).obj J.cocomplex).iCycles 1 =
        Γ.map (J.cocomplex.iCycles 1) := by
  exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

private lemma resolutionCyclesIso_toCycles {C : Type u} [Category.{v} C] [Abelian C]
    {H : C} (J : InjectiveResolution H) (Γ : C ⥤ AddCommGrpCat.{w})
    [Γ.Additive] [PreservesFiniteLimits Γ] :
    Γ.map (J.cocomplex.toCycles 0 1) ≫ (resolutionCyclesIso J Γ).hom =
      ((Γ.mapHomologicalComplex (.up ℕ)).obj J.cocomplex).toCycles 0 1 := by
  rw [← cancel_mono (((Γ.mapHomologicalComplex (.up ℕ)).obj J.cocomplex).iCycles 1),
    Category.assoc, resolutionCyclesIso_hom_i, ← Γ.map_comp,
    HomologicalComplex.toCycles_i, HomologicalComplex.toCycles_i]
  rfl

private lemma exists_extEquivResolutionHomology {C : Type u} [Category.{v} C] [Abelian C]
    [HasExt.{w} C] {H : C} (J : InjectiveResolution H) (c : C)
    (Γ : C ⥤ AddCommGrpCat.{v}) [Γ.Additive] [PreservesFiniteLimits Γ]
    (ψ : preadditiveCoyoneda.obj (op c) ≅ Γ) :
    ∃ e : Abelian.Ext.{w} c H 1 ≃
        ((Γ.mapHomologicalComplex (.up ℕ)).obj J.cocomplex).homology 1,
      ∀ q : c ⟶ J.cocomplex.cycles 1,
        e ((Abelian.Ext.mk₀ q).comp (resolutionShortComplex_shortExact J).extClass (zero_add 1)) =
          -(((Γ.mapHomologicalComplex (.up ℕ)).obj J.cocomplex).homologyπ 1
            ((resolutionCyclesIso J Γ).hom ((ψ.hom.app _) q))) := by
  let S := resolutionShortComplex J
  let hS := resolutionShortComplex_shortExact J
  let : Injective (resolutionShortComplex J).X₂ := by
    show Injective (J.cocomplex.X 0)
    infer_instance
  let K := (Γ.mapHomologicalComplex (.up ℕ)).obj J.cocomplex
  let η := resolutionCyclesIso J Γ
  let f : (c ⟶ J.cocomplex.cycles 1) →+ Abelian.Ext.{w} c H 1 :=
    hS.extClass.postcomp c (zero_add 1) |>.comp Abelian.Ext.addEquiv₀.symm.toAddMonoidHom
  let g : (c ⟶ J.cocomplex.cycles 1) →+ K.homology 1 :=
    -((K.homologyπ 1).hom.comp (η.hom.hom.comp (ψ.hom.app _).hom))
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨q, hq⟩ := Abelian.Ext.covariant_sequence_exact₁ c hS a
      (Abelian.Ext.eq_zero_of_injective _) (n₀ := 0) rfl
    obtain ⟨q, rfl⟩ := (Abelian.Ext.mk₀_bijective _ _).2 q
    exact ⟨q, hq⟩
  have hg : Function.Surjective g := by
    intro a
    obtain ⟨z, hz⟩ := (AddCommGrpCat.epi_iff_surjective (K.homologyπ 1)).mp inferInstance (-a)
    obtain ⟨q, hq⟩ := (ConcreteCategory.bijective_of_isIso ((ψ.hom.app _) ≫ η.hom)).2 z
    refine ⟨q, ?_⟩
    show -(K.homologyπ 1 (η.hom ((ψ.hom.app _) q))) = a
    change η.hom ((ψ.hom.app _) q) = z at hq
    rw [hq, hz, neg_neg]
  have hf0 (q : c ⟶ J.cocomplex.cycles 1) :
      f q = 0 ↔ ∃ t : c ⟶ J.cocomplex.X 0, t ≫ S.g = q := by
    constructor
    · intro hq
      obtain ⟨t, ht⟩ := Abelian.Ext.covariant_sequence_exact₃ c hS (Abelian.Ext.mk₀ q)
        (zero_add 1) hq
      obtain ⟨t, rfl⟩ := (Abelian.Ext.mk₀_bijective _ _).2 t
      exact ⟨t, (Abelian.Ext.mk₀_bijective _ _).1 (by simpa using ht)⟩
    · rintro ⟨t, rfl⟩
      show (Abelian.Ext.mk₀ (t ≫ S.g)).comp hS.extClass (zero_add 1) = 0
      rw [← Abelian.Ext.mk₀_comp_mk₀,
        Abelian.Ext.comp_assoc (h₂₃ := zero_add 1) (h := (rfl : 0 + 0 + 1 = 1))]
      show (Abelian.Ext.mk₀ t).comp
        ((Abelian.Ext.mk₀ (resolutionShortComplex J).g).comp hS.extClass (zero_add 1))
          (zero_add 1) = 0
      rw [hS.comp_extClass, Abelian.Ext.comp_zero]
  have hg0 (q : c ⟶ J.cocomplex.cycles 1) :
      g q = 0 ↔ ∃ t : c ⟶ J.cocomplex.X 0, t ≫ S.g = q := by
    let T := ShortComplex.mk (K.toCycles 0 1) (K.homologyπ 1)
      (K.toCycles_comp_homologyπ 0 1)
    have hT : T.Exact := T.exact_of_g_is_cokernel (K.homologyIsCokernel 0 1 (by simp))
    have ht (t : c ⟶ J.cocomplex.X 0) :
        K.toCycles 0 1 ((ψ.hom.app _) t) = η.hom ((ψ.hom.app _) (t ≫ S.g)) := by
      rw [← resolutionCyclesIso_toCycles J Γ]
      show η.hom (Γ.map S.g ((ψ.hom.app _) t)) = _
      congr 1
      exact ConcreteCategory.congr_hom (ψ.hom.naturality S.g) t |>.symm
    constructor
    · intro hq
      have hq' : K.homologyπ 1 (η.hom ((ψ.hom.app _) q)) = 0 := neg_eq_zero.mp hq
      obtain ⟨t, ht'⟩ := T.ab_exact_iff.mp hT _ hq'
      obtain ⟨t, rfl⟩ := (ConcreteCategory.bijective_of_isIso (ψ.hom.app (J.cocomplex.X 0))).2 t
      refine ⟨t, ?_⟩
      apply (ConcreteCategory.bijective_of_isIso (ψ.hom.app _)).1
      apply (ConcreteCategory.bijective_of_isIso η.hom).1
      exact (ht t).symm.trans ht'
    · rintro ⟨t, rfl⟩
      show -(K.homologyπ 1 (η.hom ((ψ.hom.app _) (t ≫ S.g)))) = 0
      rw [← ht, ← ConcreteCategory.comp_apply, K.toCycles_comp_homologyπ]
      simp
  obtain ⟨e, he⟩ := exists_equiv_of_surjections f g hf hg (fun a b => by
    rw [← sub_eq_zero, ← map_sub, hf0, ← hg0, map_sub, sub_eq_zero])
  exact ⟨e, he⟩

private def globalSectionsCoyonedaIso (X : TopCat.{u})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}] :
    preadditiveCoyoneda.obj
      (op ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}).obj
        (AddCommGrpCat.of (ULift.{max u v} ℤ)))) ≅
      (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}).obj
        (op (⊤ : Opens X)) := by
  let Γ := (sheafSections (Opens.grothendieckTopology X)
    AddCommGrpCat.{max u v}).obj (op (⊤ : Opens X))
  letI : Γ.Additive := sheafSections_additive X ⊤
  exact Stacks.Cohomology.Locality.adjCoyonedaIso
    (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}
      (Limits.isTerminalTop : IsTerminal (⊤ : Opens X)))
    (AddCommGrpCat.of (ULift.{max u v} ℤ)) ≪≫
      Functor.isoWhiskerLeft Γ (uliftZHomIso.{max u v})

private lemma globalSectionsCoyonedaIso_apply (X : TopCat.{u})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})
    (q : (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}).obj
      (AddCommGrpCat.of (ULift.{max u v} ℤ)) ⟶ A) :
    (globalSectionsCoyonedaIso X).hom.app A q =
      (((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}).homEquiv _
        _ q).app
        (op (⊤ : Opens X))) ⟨1⟩ := by
  show ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}
    (Limits.isTerminalTop : IsTerminal (⊤ : Opens X))).homEquiv _ _ q) ⟨1⟩ = _
  rfl

private lemma globalSectionsCoyonedaIso_restrict (X : TopCat.{u})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})
    (q : (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}).obj
      (AddCommGrpCat.of (ULift.{max u v} ℤ)) ⟶ A) (V : Opens X) :
    (((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}).homEquiv _ _
      q).app
        (op V)) ⟨1⟩ =
      A.obj.map (homOfLE (le_top : V ≤ ⊤)).op
        ((globalSectionsCoyonedaIso X).hom.app A q) := by
  rw [globalSectionsCoyonedaIso_apply]
  let q' := (sheafificationAdjunction (Opens.grothendieckTopology X)
    AddCommGrpCat.{max u v}).homEquiv _ _ q
  exact ConcreteCategory.congr_hom (q'.naturality (homOfLE (le_top : V ≤ ⊤)).op) ⟨1⟩

private lemma resolution_affine_fiber (X : TopCat.{u})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
    (H : TopCat.Sheaf AddCommGrpCat.{max u v} X) (J : InjectiveResolution H)
    (F : Torsor X H) (Ui : X → Opens X) (hUi : (⊤ : Opens X) = ⨆ i, Ui i)
    (s : ∀ i, F.F.obj (Ui i)) (z : CechCochains.cocycles1 Ui H.presheaf)
    (hz : IsTransitionCocycle F Ui s z)
    (r : CechOne.CechOneResolutionRepresentative X ⊤ Ui hUi H J z) :
    ∃ g : F.F.toPresheafOfSets.Hom (abelianSheafOfSets (J.cocomplex.X 0)).toPresheafOfSets,
      (∀ V (h : H.presheaf.obj (op V)) (t : F.F.obj V),
        g.app V (F.action.act (Multiplicative.ofAdd h) t) =
          (J.ι.f 0).hom.app (op V) h +
            (g.app V t : (J.cocomplex.X 0).presheaf.obj (op V))) ∧
      (∀ V, Function.Injective (g.app V)) ∧
      (∀ V (a : (J.cocomplex.X 0).presheaf.obj (op V)),
        (J.cocomplex.d 0 1).hom.app (op V) a =
          (J.cocomplex.X 1).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
            (-((CechOne.abelianResolutionSections X ⊤ J).iCycles 1 r.cycle)) ↔
          ∃ t, g.app V t = a) := by
  let A := J.cocomplex.X 0
  let B := J.cocomplex.X 1
  let φ : H ⟶ A := J.ι.f 0
  let d : A ⟶ B := J.cocomplex.d 0 1
  let c := (CechOne.abelianResolutionSections X ⊤ J).iCycles 1 r.cycle
  let b := cechZeroSection A Ui r.b
  obtain ⟨g, hg, hga⟩ := exists_affine_map φ F Ui hUi s b
    (transition_coboundary φ F Ui s z hz r.b r.coboundary)
  have hdφ (V : Opens X) (h : H.presheaf.obj (op V)) :
      d.hom.app (op V) (φ.hom.app (op V) h) = 0 := by
    have he := congrArg (fun f : H ⟶ B => f.hom.app (op V) h)
      J.ι_f_zero_comp_complex_d
    exact he
  have hb (i : X) : d.hom.app (op (Ui i)) (b i) =
      B.presheaf.map (homOfLE (le_top : Ui i ≤ ⊤)).op (-c) := by
    have hWi : Ui i ≤ CechCochains.inter Ui (fun _ : Fin 1 => i) := le_iInf fun _ => le_rfl
    have hr := congrArg (B.presheaf.map (homOfLE hWi).op) (r.restriction (fun _ => i))
    have hl : B.presheaf.map (homOfLE hWi).op
          (B.presheaf.map
            (homOfLE (le_top : CechCochains.inter Ui (fun _ : Fin 1 => i) ≤ ⊤)).op c) =
        B.presheaf.map (homOfLE (le_top : Ui i ≤ ⊤)).op c :=
      abelianSheaf_res_comp B hWi
        (le_top : CechCochains.inter Ui (fun _ : Fin 1 => i) ≤ ⊤) c
    have hrr : B.presheaf.map (homOfLE hWi).op
          (-(d.hom.app (op (CechCochains.inter Ui (fun _ : Fin 1 => i)))
            (r.b (fun _ => i)))) =
        -(d.hom.app (op (Ui i)) (b i)) :=
      (map_neg _ _).trans (congrArg (fun y => -y)
        (abelianSheafHom_naturality d hWi (r.b (fun _ => i))))
    have hchain : B.presheaf.map (homOfLE (le_top : Ui i ≤ ⊤)).op c =
        -(d.hom.app (op (Ui i)) (b i)) := hl.symm.trans (hr.trans hrr)
    rw [map_neg, hchain, neg_neg]
  have hq (V : Opens X) (t : F.F.obj V) : d.hom.app (op V) (g.app V t) =
      B.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (-c) := by
    apply abelianSheaf_eq_of_cover B Ui hUi V
    intro i
    rw [abelianSheafHom_naturality, abelianSheaf_res_comp]
    show d.hom.app (op (V ⊓ Ui i))
      ((abelianSheafOfSets A).res inf_le_left (g.app V t)) = _
    rw [← g.naturality, hg i (V ⊓ Ui i) inf_le_right, map_add, hdφ,
      zero_add, ← abelianSheafHom_naturality, hb, abelianSheaf_res_comp]
  let : Mono φ := (resolutionShortComplex_shortExact J).mono_f
  obtain ⟨hinj, hfiber⟩ := affine_map_fiber φ d F g hga
    (sheaf_mono_app_injective φ)
    (sheaf_exact_on_sections (ShortComplex.mk φ d J.ι_f_zero_comp_complex_d) J.exact₀)
    (-c) hq
  exact ⟨g, hga, hinj, hfiber⟩

@[ega "IV 16.5.15" "special case", sga "4½ Arcata 1.6.6" "special case"]
private theorem nonempty_torsorCohomologyClassification (X : TopCat.{u})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
    (H : TopCat.Sheaf AddCommGrpCat.{max u v} X) :
    Nonempty (TorsorCohomologyClassification X H) := by
  classical
  let : EnoughInjectives
      (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}) :=
    Stacks.Injectives.abelianSheaf_enoughInjectives X
  let : LocallySmall.{max u v}
      (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}) := inferInstance
  let hExt : HasExt.{max u v}
      (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}) :=
    hasExt_of_enoughInjectives _
  let : HasExt.{max u v} (TopCat.Sheaf AddCommGrpCat.{max u v} X) := hExt
  let J := injectiveResolution H
  let Γ : TopCat.Sheaf AddCommGrpCat.{max u v} X ⥤ AddCommGrpCat.{max u v} :=
    (sheafSections (Opens.grothendieckTopology X)
      AddCommGrpCat.{max u v}).obj (op (⊤ : Opens X))
  let : Γ.Additive := sheafSections_additive X ⊤
  let : PreservesFiniteLimits Γ := sheafSections_preservesFiniteLimits X ⊤
  let c := (constantSheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{max u v}).obj (AddCommGrpCat.of (ULift.{max u v} ℤ))
  let ψ := globalSectionsCoyonedaIso X
  obtain ⟨e, he⟩ := @exists_extEquivResolutionHomology _ _ _
    hExt _ J c Γ _ _ ψ
  let equiv : TorsorClass X H ≃ sheafCohomologyOne X H :=
    (torsorClassesEquivCategorical X H).trans
      ((Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1.{max u v} H).trans
        (e.trans (J.isoRightDerivedObj Γ 1).symm.addCommGroupIsoToAddEquiv.toEquiv))
  have hc (F : Torsor X H) (Ui : X → Opens X)
      (hUi : (⊤ : Opens X) = ⨆ i, Ui i) (s : ∀ i, F.F.obj (Ui i))
      (z : CechCochains.cocycles1 Ui H.presheaf) (hz : IsTransitionCocycle F Ui s z) :
      equiv (Quotient.mk _ F) = CechOne.cechH1ToRightDerivedSections X ⊤ Ui hUi H
        (CechCochains.cls Ui H.presheaf z) := by
    obtain ⟨r, hr⟩ := CechOne.exists_cechOneResolutionRepresentative X ⊤ Ui hUi H J z
    obtain ⟨g, hga, hginj, hgfiber⟩ := resolution_affine_fiber X H J F Ui hUi s z hz r
    let Q := J.cocomplex.cycles 1
    let η := resolutionCyclesIso J Γ
    let q : c ⟶ Q := (ψ.inv.app Q) (η.inv (-r.cycle))
    let q' := (sheafificationAdjunction (Opens.grothendieckTopology X)
      AddCommGrpCat.{max u v}).homEquiv _ _ q
    have hη (t : (CechOne.abelianResolutionSections X ⊤ J).cycles 1) :
        η.hom (η.inv t) = t := η.inv_hom_id_apply t
    have hq : (ψ.hom.app Q) q = η.inv (-r.cycle) := ψ.inv_hom_id_app_apply Q _
    have hqi : Γ.map (J.cocomplex.iCycles 1) ((ψ.hom.app Q) q) =
        -((CechOne.abelianResolutionSections X ⊤ J).iCycles 1 r.cycle) := by
      rw [← resolutionCyclesIso_hom_i J Γ]
      show (CechOne.abelianResolutionSections X ⊤ J).iCycles 1
        (η.hom ((ψ.hom.app Q) q)) = _
      rw [hq, hη, map_neg]
    have hqres (V : Opens X) :
        (J.cocomplex.iCycles 1).hom.app (op V) (q'.app (op V) ⟨1⟩) =
          (J.cocomplex.X 1).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
            (-((CechOne.abelianResolutionSections X ⊤ J).iCycles 1 r.cycle)) := by
      rw [globalSectionsCoyonedaIso_restrict X Q q V, ← abelianSheafHom_naturality]
      show (J.cocomplex.X 1).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
        (Γ.map (J.cocomplex.iCycles 1) ((ψ.hom.app Q) q)) = _
      rw [hqi]
    have hfiber (V : Opens X) (a : (J.cocomplex.X 0).presheaf.obj (op V)) :
        (resolutionShortComplex J).g.hom.app (op V) a = q'.app (op V) ⟨1⟩ ↔
          ∃ t, g.app V t = a := by
      have hinjV := sheaf_mono_app_injective (J.cocomplex.iCycles 1) V
      have hd : (J.cocomplex.iCycles 1).hom.app (op V)
          ((resolutionShortComplex J).g.hom.app (op V) a) =
          (J.cocomplex.d 0 1).hom.app (op V) a :=
        congrArg (fun f : J.cocomplex.X 0 ⟶ J.cocomplex.X 1 =>
          f.hom.app (op V) a) (J.cocomplex.toCycles_i 0 1)
      refine Iff.trans (Iff.symm hinjV.eq_iff) ?_
      rw [hd, hqres]
      exact hgfiber V a
    let gi : (toCategoricalTorsor X H F).1.presheaf ⟶
        (J.cocomplex.X 0).obj ⋙ forget AddCommGrpCat.{max u v} := {
      app := fun U => ↾(fun t => g.app U.unop t.down)
      naturality := by
        intro U V f
        ext t
        exact g.naturality f.unop.le t.down }
    have hclass : Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1.{max u v} H
        (Quotient.mk (Stacks.Cohomology.Torsors.torsorSetoid H) (toCategoricalTorsor X H F)) =
        (Abelian.Ext.mk₀.{max u v} q).comp (ShortComplex.ShortExact.extClass.{max u v}
          (resolutionShortComplex_shortExact J)) (zero_add 1) := by
      have heq := (Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1_eq_boundary_iff.{max u v}
        (resolutionShortComplex J) (resolutionShortComplex_shortExact J) q'
        (toCategoricalTorsor X H F)).mpr (by
          refine ⟨gi, ?_, ?_, ?_⟩
          · intro U h t
            exact hga U.unop h t.down
          · intro U t t' ht
            exact ULift.down_injective (hginj U.unop ht)
          · intro U a
            show (resolutionShortComplex J).g.hom.app U a = q'.app U ⟨1⟩ ↔
              ∃ t : ULift (F.F.obj U.unop), g.app U.unop t.down = a
            rw [hfiber U.unop a]
            exact ⟨fun ⟨t, ht⟩ => ⟨⟨t⟩, ht⟩, fun ⟨t, ht⟩ => ⟨t.down, ht⟩⟩)
      exact heq.trans <| congrArg (fun y => (Abelian.Ext.mk₀.{max u v} y).comp
        (ShortComplex.ShortExact.extClass.{max u v}
          (resolutionShortComplex_shortExact J)) (zero_add 1)) (Equiv.symm_apply_apply _ q)
    refine Eq.trans (congrArg (fun y => (J.isoRightDerivedObj Γ 1).inv y)
      ((congrArg (fun y => e y) hclass).trans (he q))) ?_
    rw [hr]
    show (J.isoRightDerivedObj Γ 1).inv
      (-((CechOne.abelianResolutionSections X ⊤ J).homologyπ 1
        (η.hom ((ψ.hom.app Q) q)))) = _
    rw [hq, hη]
    simp only [map_neg, neg_neg]
    rfl
  exact ⟨{
    equiv := equiv
    of_point_cocycle := hc
    of_global_section := by
      intro F s
      let Ui : X → Opens X := fun _ => ⊤
      have hUi : (⊤ : Opens X) = ⨆ i, Ui i := by
        apply le_antisymm
        · intro x _
          exact Opens.mem_iSup.mpr ⟨x, trivial⟩
        · exact le_top
      have hz : IsTransitionCocycle F Ui (fun _ => s) 0 := by
        intro i
        exact F.action.one_act _
      rw [hc F Ui hUi (fun _ => s) 0 hz]
      exact (CechOne.cechH1ToRightDerivedSections X ⊤ Ui hUi H).map_zero
    pairing := by
      intro F G K p
      obtain ⟨Ui, hUi, ⟨s⟩, ⟨t⟩⟩ := torsor_common_cover F G
      let zF := torsorTransitionCocycle F Ui s
      let zG := torsorTransitionCocycle G Ui t
      have hzF := torsorTransitionCocycle_spec F Ui s
      have hzG := torsorTransitionCocycle_spec G Ui t
      have hzK := torsorPairing_transitionCocycle F G K p Ui s t zF zG hzF hzG
      rw [hc K Ui hUi _ _ hzK, hc F Ui hUi s zF hzF, hc G Ui hUi t zG hzG]
      exact (CechOne.cechH1ToRightDerivedSections X ⊤ Ui hUi H).map_add
        (CechCochains.cls Ui H.presheaf zF) (CechCochains.cls Ui H.presheaf zG) }⟩


/-- **Stacks Project, Tag 02FQ.** The canonical classification, with the
transition-cocycle, trivial-torsor and contracted-product laws. -/
@[stacks 02FQ, ega "IV 16.5.15" "abelian sheaf of groups"]
noncomputable def torsorCohomologyClassification (X : TopCat.{u})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
    (H : TopCat.Sheaf AddCommGrpCat.{max u v} X) :
    TorsorCohomologyClassification X H :=
  Classical.choice (by exact nonempty_torsorCohomologyClassification X H)

/-- The canonical bijection between torsor classes and first sheaf cohomology. -/
@[stacks 02FQ "the canonical bijection",
  sga "4½ Cycle 1.1.1" "topological space",
  ega "IV 16.5.15" "abelian sheaf of groups", sga "4½ Arcata 1.6.6" "topological space"]
noncomputable def torsorClassEquivSheafCohomologyOne (X : TopCat.{u})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
    (H : TopCat.Sheaf AddCommGrpCat.{max u v} X) :
    TorsorClass X H ≃ sheafCohomologyOne X H :=
  (torsorCohomologyClassification X H).equiv

/-- Local transition cocycles compute the canonical torsor class. -/
theorem torsorClassEquivSheafCohomologyOne_of_cocycle (X : TopCat.{u})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
    (H : TopCat.Sheaf AddCommGrpCat.{max u v} X) (F : Torsor X H)
    {I : Type w} (Ui : I → Opens X)
    (hUi : (⊤ : Opens X) = ⨆ i, Ui i) (s : ∀ i, F.F.obj (Ui i))
    (z : CechCochains.cocycles1 Ui H.presheaf) (hz : IsTransitionCocycle F Ui s z) :
    torsorClassEquivSheafCohomologyOne X H (Quotient.mk _ F) =
      CechOne.cechH1ToRightDerivedSections X ⊤ Ui hUi H (CechCochains.cls Ui H.presheaf z) :=
  (torsorCohomologyClassification X H).of_cocycle F Ui hUi s z hz

/-- A torsor with a global section represents zero in first cohomology. -/
theorem torsorClassEquivSheafCohomologyOne_of_global_section (X : TopCat.{u})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
    (H : TopCat.Sheaf AddCommGrpCat.{max u v} X) (F : Torsor X H) (s : F.F.obj ⊤) :
    torsorClassEquivSheafCohomologyOne X H (Quotient.mk _ F) = 0 :=
  (torsorCohomologyClassification X H).of_global_section F s

/-- In particular the trivial torsor represents zero. -/
theorem torsorClassEquivSheafCohomologyOne_of_isTrivial (X : TopCat.{u})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
    (H : TopCat.Sheaf AddCommGrpCat.{max u v} X) (F : Torsor X H)
    (hF : F.action.IsTrivial) :
    torsorClassEquivSheafCohomologyOne X H (Quotient.mk _ F) = 0 := by
  obtain ⟨φ, _⟩ := hF
  exact torsorClassEquivSheafCohomologyOne_of_global_section X H F
    (φ.app ⊤ (Multiplicative.ofAdd (0 : H.presheaf.obj (op ⊤))))

/-- A pairing of torsors sends their contracted product to the sum of their classes. -/
theorem torsorClassEquivSheafCohomologyOne_pairing (X : TopCat.{u})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
    (H : TopCat.Sheaf AddCommGrpCat.{max u v} X) (F G K : Torsor X H)
    (p : TorsorPairing F G K) :
    torsorClassEquivSheafCohomologyOne X H (Quotient.mk _ K) =
      torsorClassEquivSheafCohomologyOne X H (Quotient.mk _ F) +
        torsorClassEquivSheafCohomologyOne X H (Quotient.mk _ G) :=
  (torsorCohomologyClassification X H).pairing F G K p

/-- The group of torsor classes. The laws above identify its zero with the
trivial torsor and its addition with contracted product, independently of the
chosen representatives. -/
noncomputable instance instAddCommGroupTorsorClass (X : TopCat.{u})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
    (H : TopCat.Sheaf AddCommGrpCat.{max u v} X) : AddCommGroup (TorsorClass X H) :=
  (torsorClassEquivSheafCohomologyOne X H).addCommGroup

/-- The torsor classification as an additive equivalence. -/
@[sga "3 III 4.3.1" "partial", sga "4½ Cycle 1.1.1" "special case"]
noncomputable def torsorClassAddEquivSheafCohomologyOne (X : TopCat.{u})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
    (H : TopCat.Sheaf AddCommGrpCat.{max u v} X) :
    TorsorClass X H ≃+ sheafCohomologyOne X H :=
  (torsorClassEquivSheafCohomologyOne X H).addEquiv

/-- The additive equivalence has exactly the original underlying bijection. -/
@[simp]
theorem torsorClassAddEquivSheafCohomologyOne_toEquiv (X : TopCat.{u})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
    (H : TopCat.Sheaf AddCommGrpCat.{max u v} X) :
    (torsorClassAddEquivSheafCohomologyOne X H).toEquiv =
      torsorClassEquivSheafCohomologyOne X H := rfl

/-- A global section identifies a torsor class with the neutral element. -/
theorem torsorClass_eq_zero_of_global_section (X : TopCat.{u})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
    (H : TopCat.Sheaf AddCommGrpCat.{max u v} X) (F : Torsor X H) (s : F.F.obj ⊤) :
    (Quotient.mk _ F : TorsorClass X H) = 0 := by
  apply (torsorClassAddEquivSheafCohomologyOne X H).injective
  rw [AddEquiv.map_zero]
  exact torsorClassEquivSheafCohomologyOne_of_global_section X H F s

/-- A bi-equivariant pairing computes addition on torsor classes. -/
theorem torsorClass_eq_add_of_pairing (X : TopCat.{u})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
    (H : TopCat.Sheaf AddCommGrpCat.{max u v} X) (F G K : Torsor X H)
    (p : TorsorPairing F G K) :
    (Quotient.mk _ K : TorsorClass X H) = Quotient.mk _ F + Quotient.mk _ G := by
  apply (torsorClassAddEquivSheafCohomologyOne X H).injective
  rw [AddEquiv.map_add]
  exact torsorClassEquivSheafCohomologyOne_pairing X H F G K p

end Stacks.Cohomology.SheafTorsor
