module
import all StacksFrontier.CategoryTheory.Sites.Cohomology.ObjectSections.DerivedSectionsVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.ForgetModuleHelpers
import all StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.ForgetModuleHelpers

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Localization.Adjunction
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Adjunction
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ObjectSections.DerivedSectionsVanishing
public import StacksFrontier.CategoryTheory.Localization.HomBijective

/-!
# ForgetModuleHelpersUnconditional

Stronger forms of declarations of
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.ForgetModuleHelpers`, stated as
separate declarations beside the ones there: over more general coefficient universes, or with
inputs that are carried there as hypotheses discharged, together with the new results built on
them.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Localization
open scoped ZeroObject

namespace Stacks.Cohomology.ForgetModule

universe u

attribute [local instance] HasDerivedCategory.standard

open ModuleSheafCohomology

section SmallSite

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

end SmallSite

section General

universe w v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (O : Sheaf J RingCat.{w})

/-- Extension of scalars `F ↦ O ⊗_ℤ F` from abelian presheaves to presheaves of `O`-modules, the
left adjoint of the forgetful functor, assembled from its corepresentation
`ModuleSheafCohomology.tensorPresheafHomAddEquiv`. -/
public def tensorPresheafFunctor :
    (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ PresheafOfModules.{w} O.obj :=
  Adjunction.leftAdjointOfEquiv (G := PresheafOfModules.toPresheaf O.obj)
    (fun P M ↦ (tensorPresheafHomAddEquiv O.obj P M).toEquiv)
    (fun P M M' g h ↦ by
      change tensorPresheafUnit O.obj P ≫ (PresheafOfModules.toPresheaf O.obj).map (h ≫ g) = _
      rw [Functor.map_comp]
      exact (Category.assoc _ _ _).symm)

/-- `Stacks.Cohomology.ForgetModule.tensorPresheafFunctor` is left adjoint to forgetting the
module structure on presheaves. -/
public def tensorPresheafAdjunction :
    tensorPresheafFunctor J O ⊣ PresheafOfModules.toPresheaf O.obj :=
  Adjunction.adjunctionOfEquivLeft (G := PresheafOfModules.toPresheaf O.obj)
    (fun P M ↦ (tensorPresheafHomAddEquiv O.obj P M).toEquiv)
    (fun P M M' g h ↦ by
      change tensorPresheafUnit O.obj P ≫ (PresheafOfModules.toPresheaf O.obj).map (h ≫ g) = _
      rw [Functor.map_comp]
      exact (Category.assoc _ _ _).symm)

/-- Extension of scalars `- ⊗_ℤ O`, the left adjoint of the forgetful functor from sheaves of
`O`-modules to abelian sheaves: extension of scalars of the underlying presheaf, sheafified. -/
public def tensorSheafUnconditional : Sheaf J AddCommGrpCat.{w} ⥤ SheafOfModules.{w} O :=
  sheafToPresheaf J AddCommGrpCat.{w} ⋙ tensorPresheafFunctor J O ⋙
    PresheafOfModules.sheafification (𝟙 O.obj)

/-- Extension of scalars is left adjoint to forgetting the module structure: the composite of
the presheaf-level adjunction with the sheafification adjunction for presheaves of modules,
restricted along the fully faithful inclusion of sheaves into presheaves. -/
public def tensorSheafAdjunctionUnconditional :
    tensorSheafUnconditional J O ⊣ SheafOfModules.toSheaf O :=
  ((tensorPresheafAdjunction J O).comp
      (PresheafOfModules.sheafificationAdjunction (𝟙 O.obj))).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf J AddCommGrpCat.{w}) (Functor.FullyFaithful.id _)
    (Functor.rightUnitor _).symm (Iso.refl _)

variable [EnoughInjectives (SheafOfModules.{w} O)]

/-- Extension of scalars preserves the inclusion of a short exact sequence of abelian sheaves
whose quotient is sectionwise torsion free. -/
public lemma tensorSheaf_map_mono_of_shortExact_unconditional
    (S : ShortComplex (Sheaf J AddCommGrpCat.{w})) (hS : S.ShortExact)
    (hP : ∀ V, Module.IsTorsionFree ℤ (S.X₃.obj.obj V)) :
    Mono ((tensorSheafUnconditional J O).map S.f) := by
  let T := tensorSheafUnconditional J O
  let adj := tensorSheafAdjunctionUnconditional J O
  let I := Injective.under (T.obj S.X₁)
  let i : T.obj S.X₁ ⟶ I := Injective.ι _
  obtain ⟨g, hg⟩ := _root_.Stacks.Cohomology.ObjectSections.exists_extension_of_isTorsionFree
    J O I S hS hP (adj.homEquiv _ _ i)
  have fac : T.map S.f ≫ (adj.homEquiv _ _).symm g = i := by
    show (tensorSheafUnconditional J O).map S.f ≫ (adj.homEquiv _ _).symm g = i
    rw [← adj.homEquiv_naturality_left_symm, hg, Equiv.symm_apply_apply]
  have : Mono (T.map S.f ≫ (adj.homEquiv _ _).symm g) := by
    rw [fac]
    infer_instance
  exact mono_of_mono (T.map S.f) ((adj.homEquiv _ _).symm g)

/-- Extension of scalars is exact on short exact sequences of abelian sheaves whose quotient is
sectionwise torsion free. -/
public lemma tensorSheaf_map_shortExact_unconditional
    (S : ShortComplex (Sheaf J AddCommGrpCat.{w})) (hS : S.ShortExact)
    (hP : ∀ V, Module.IsTorsionFree ℤ (S.X₃.obj.obj V)) :
    letI := (tensorSheafAdjunctionUnconditional J O).left_adjoint_additive
    (S.map (tensorSheafUnconditional J O)).ShortExact := by
  let := (tensorSheafAdjunctionUnconditional J O).left_adjoint_additive
  let := (tensorSheafAdjunctionUnconditional J O).leftAdjoint_preservesColimits
  have h := (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi
    (tensorSheafUnconditional J O)).mp inferInstance S hS
  exact ShortComplex.ShortExact.mk' h.1
    (tensorSheaf_map_mono_of_shortExact_unconditional J O S hS hP) h.2

/-- Extension of scalars preserves acyclicity of a complex of abelian sheaves with sectionwise
torsion-free terms. -/
public lemma tensorSheaf_map_acyclic_unconditional
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ) (hK : K.Acyclic)
    (hP : ∀ i V, Module.IsTorsionFree ℤ ((K.X i).obj.obj V)) :
    letI := (tensorSheafAdjunctionUnconditional J O).left_adjoint_additive
    ((tensorSheafUnconditional J O).mapHomologicalComplex (.up ℤ) |>.obj K).Acyclic := by
  let := (tensorSheafAdjunctionUnconditional J O).left_adjoint_additive
  let T := tensorSheafUnconditional J O
  let S (i : ℤ) := ShortComplex.mk (K.iCycles i) (K.toCycles i (i + 1)) (by
    rw [← cancel_mono (K.iCycles (i + 1))]
    simp)
  have hs (i : ℤ) : ((S i).map T).ShortExact :=
    tensorSheaf_map_shortExact_unconditional J O (S i)
      (_root_.Stacks.Cohomology.ForgetModule.cycles_shortExact K hK i)
      (isTorsionFree_of_mono J (K.iCycles (i + 1)) (hP (i + 1)))
  intro j
  obtain ⟨i, rfl⟩ : ∃ i : ℤ, i + 1 = j := ⟨j - 1, by omega⟩
  rw [HomologicalComplex.exactAt_iff' _ i (i + 1) (i + 1 + 1) (by simp) (by simp)]
  have hm : Mono (T.map (K.iCycles (i + 1 + 1))) := (hs (i + 1 + 1)).mono_f
  let S' := ShortComplex.mk (T.map (K.iCycles (i + 1)))
    (T.map (K.d (i + 1) (i + 1 + 1))) (by
      rw [← T.map_comp, K.iCycles_d, T.map_zero])
  let f : (S (i + 1)).map T ⟶ S' :=
    { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := T.map (K.iCycles (i + 1 + 1))
      comm₂₃ := by simp [S, S', ← T.map_comp] }
  have hS' : S'.Exact :=
    (ShortComplex.exact_iff_of_epi_of_isIso_of_mono f).mp (hs (i + 1)).exact
  have he : Epi (T.map (K.toCycles i (i + 1))) := (hs i).epi_g
  let f' : (((T.mapHomologicalComplex (.up ℤ)).obj K).sc' i (i + 1) (i + 1 + 1)) ⟶ S' :=
    { τ₁ := T.map (K.toCycles i (i + 1)), τ₂ := 𝟙 _, τ₃ := 𝟙 _
      comm₁₂ := by
        show T.map (K.toCycles i (i + 1)) ≫ T.map (K.iCycles (i + 1)) =
          T.map (K.d i (i + 1)) ≫ 𝟙 _
        rw [← T.map_comp, K.toCycles_i, Category.comp_id] }
  have : Epi f'.τ₁ := he
  have : IsIso f'.τ₂ := IsIso.id _
  have : IsIso f'.τ₃ := IsIso.id _
  have : Mono f'.τ₃ := IsIso.mono_of_iso f'.τ₃
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono f').mpr hS'

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- A biproduct of sectionwise torsion-free abelian sheaves is sectionwise torsion free. -/
public lemma torsionFree_biprod_general (F G : Sheaf J AddCommGrpCat.{w})
    (hF : ∀ V, Module.IsTorsionFree ℤ (F.obj.obj V))
    (hG : ∀ V, Module.IsTorsionFree ℤ (G.obj.obj V)) (V : Cᵒᵖ) :
    Module.IsTorsionFree ℤ ((F ⊞ G).obj.obj V) := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro n x hx
  by_cases hn : n = 0
  · exact Or.inl hn
  right
  have mono_smul (H : Sheaf J AddCommGrpCat.{w})
      (hH : ∀ W, Module.IsTorsionFree ℤ (H.obj.obj W)) : Mono (n • 𝟙 H) := by
    apply (sheafToPresheaf _ _).mono_of_mono_map
    have (W : Cᵒᵖ) : Mono (((sheafToPresheaf _ _).map (n • 𝟙 H)).app W) := by
      have := hH W
      rw [AddCommGrpCat.mono_iff_injective]
      show Function.Injective (fun y : H.obj.obj W => n • y)
      exact IsSMulRegular.of_ne_zero hn
    exact NatTrans.mono_of_mono_app _
  have := mono_smul F hF
  have := mono_smul G hG
  have hb : n • 𝟙 (F ⊞ G) = biprod.map (n • 𝟙 F) (n • 𝟙 G) := by
    apply biprod.hom_ext <;> simp
  have hm : Mono (n • 𝟙 (F ⊞ G)) := by rw [hb]; infer_instance
  have hi := (AddCommGrpCat.mono_iff_injective ((n • 𝟙 (F ⊞ G)).hom.app V)).mp
    inferInstance
  change Function.Injective (fun y : (F ⊞ G).obj.obj V => n • y) at hi
  apply hi
  simpa only [smul_zero] using hx

/-- Extension of scalars preserves a quasi-isomorphism between complexes of abelian sheaves with
sectionwise torsion-free terms. -/
public lemma tensorSheaf_map_quasiIso_unconditional
    {K L : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ} (q : K ⟶ L) [QuasiIso q]
    (hK : ∀ i V, Module.IsTorsionFree ℤ ((K.X i).obj.obj V))
    (hL : ∀ i V, Module.IsTorsionFree ℤ ((L.X i).obj.obj V)) :
    letI := (tensorSheafAdjunctionUnconditional J O).left_adjoint_additive
    QuasiIso (((tensorSheafUnconditional J O).mapHomologicalComplex (.up ℤ)).map q) := by
  let := (tensorSheafAdjunctionUnconditional J O).left_adjoint_additive
  apply Functor.quasiIso_of_acyclic_mappingCone
  have h := tensorSheaf_map_acyclic_unconditional J O (CochainComplex.mappingCone q)
    (Functor.acyclic_mappingCone q inferInstance) (fun i =>
      let e := HomologicalComplex.homotopyCofiber.XIsoBiprod q i (i + 1) rfl
      @isTorsionFree_of_mono _ _ _ _ _ _ e.hom (IsIso.mono_of_iso e.hom)
        (torsionFree_biprod_general J (K.X (i + 1)) (L.X i) (hK (i + 1)) (hL i)))
  intro i
  exact (exactAt_iff_of_quasiIsoAt (CochainComplex.mappingCone.mapHomologicalComplexIso q
    (tensorSheafUnconditional J O)).hom i).mp (h i)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Every cohomologically bounded above complex of abelian sheaves receives a
quasi-isomorphism from one with sectionwise torsion-free terms. This is Stacks 05T7 for the
class of sectionwise torsion-free sheaves. -/
public lemma exists_torsionFree_resolution_of_isLE_general
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ) (n : ℤ) [K.IsLE n] :
    ∃ (G : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ) (q : G ⟶ K), QuasiIso q ∧
      (∀ i V, Module.IsTorsionFree ℤ ((G.X i).obj.obj V)) := by
  let P : ObjectProperty (Sheaf J AddCommGrpCat.{w}) := fun F =>
    ∀ V, Module.IsTorsionFree ℤ (F.obj.obj V)
  have hP : ∀ F : Sheaf J AddCommGrpCat.{w},
      ∃ (G : Sheaf J AddCommGrpCat.{w}) (_ : P G) (q : G ⟶ F), Epi q := by
    intro F
    obtain ⟨G, q, hG, hq⟩ := exists_isTorsionFree_epi J F
    exact ⟨G, hG, q, hq⟩
  let : P.ContainsZero := by
    obtain ⟨G, hG, q, hq⟩ := hP 0
    exact ⟨0, isZero_zero _, isTorsionFree_of_mono J (0 : 0 ⟶ G) hG⟩
  obtain ⟨G, q, hq, hG, _⟩ := (CochainComplex.exists_quasiIso_prop P hP n).2 K
  exact ⟨G, q, hq, hG⟩

/-- Precomposition with a quasi-isomorphism of sectionwise torsion-free complexes of abelian
sheaves is bijective on morphisms into the underlying abelian complex of a K-injective complex
of modules, in the homotopy category. -/
public lemma toSheaf_precomp_bijective_of_torsionFree_general
    {K L : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ} (q : K ⟶ L) [QuasiIso q]
    (hK : ∀ i V, Module.IsTorsionFree ℤ ((K.X i).obj.obj V))
    (hL : ∀ i V, Module.IsTorsionFree ℤ ((L.X i).obj.obj V))
    (I : CochainComplex (SheafOfModules.{w} O) ℤ) [I.IsKInjective] :
    let Q := HomotopyCategory.quotient (Sheaf J AddCommGrpCat.{w}) (.up ℤ)
    let V := (SheafOfModules.toSheaf O).mapHomotopyCategory (.up ℤ)
    Function.Bijective (fun a : Q.obj L ⟶ V.obj
      ((HomotopyCategory.quotient _ (.up ℤ)).obj I) => Q.map q ≫ a) := by
  let := (tensorSheafAdjunctionUnconditional J O).left_adjoint_additive
  let F := (tensorSheafUnconditional J O).mapHomotopyCategory (.up ℤ)
  let Q := HomotopyCategory.quotient (Sheaf J AddCommGrpCat.{w}) (.up ℤ)
  apply adjunction_precomp_bijective
    ((tensorSheafAdjunctionUnconditional J O).mapHomotopyCategory (.up ℤ))
  have hiso : IsIso (DerivedCategory.Qh.map (F.map (Q.map q))) := by
    apply Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ (.up ℤ))
    show HomotopyCategory.quasiIso _ (.up ℤ)
      ((HomotopyCategory.quotient _ (.up ℤ)).map
        (((tensorSheafUnconditional J O).mapHomologicalComplex (.up ℤ)).map q))
    rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact tensorSheaf_map_quasiIso_unconditional J O q hK hL
  exact precomp_bijective_of_localization DerivedCategory.Qh (F.map (Q.map q))
    (CochainComplex.IsKInjective.Qh_map_bijective _ I)
    (CochainComplex.IsKInjective.Qh_map_bijective _ I)

/-- **Morphisms from a cohomologically bounded above sectionwise torsion-free complex into the
underlying abelian complex of a K-injective complex of modules are computed in the homotopy
category.** -/
public lemma toSheaf_localization_map_bijective_of_isLE_general
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ) (n : ℤ) [K.IsLE n]
    (hK : ∀ i V, Module.IsTorsionFree ℤ ((K.X i).obj.obj V))
    (I : CochainComplex (SheafOfModules.{w} O) ℤ) [I.IsKInjective] :
    let Q := HomotopyCategory.quotient (Sheaf J AddCommGrpCat.{w}) (.up ℤ)
    let G := (SheafOfModules.toSheaf O).mapHomologicalComplex (.up ℤ)
    Function.Bijective (DerivedCategory.Qh.map :
      (Q.obj K ⟶ Q.obj (G.obj I)) → _) := by
  let Q := HomotopyCategory.quotient (Sheaf J AddCommGrpCat.{w}) (.up ℤ)
  apply localization_map_bijective_of_refinements (HomotopyCategory.quasiIso _ (.up ℤ))
  intro Z s hs
  obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective Z
  obtain ⟨s, rfl⟩ := Q.map_surjective s
  have hqs : QuasiIso s := (HomotopyCategory.quotient_map_mem_quasiIso_iff s).mp hs
  have : CochainComplex.IsLE L n := (CochainComplex.isLE_iff L n).mpr (fun i hi =>
    have := hqs.quasiIsoAt i
    (exactAt_iff_of_quasiIsoAt s i).mpr (K.exactAt_of_isLE n i hi))
  obtain ⟨P, q, hq, hP⟩ := exists_torsionFree_resolution_of_isLE_general J L n
  refine ⟨Q.obj P, Q.map q, (HomotopyCategory.quotient_map_mem_quasiIso_iff q).mpr hq, ?_⟩
  let e := ((SheafOfModules.toSheaf O).mapHomotopyCategoryFactors (.up ℤ)).app I
  have hb : Function.Bijective
      (fun a : Q.obj K ⟶ ((SheafOfModules.toSheaf O).mapHomotopyCategory
        (.up ℤ)).obj ((HomotopyCategory.quotient _ (.up ℤ)).obj I) =>
        (Q.map q ≫ Q.map s) ≫ a) := by
    simpa only [Functor.map_comp] using
      toSheaf_precomp_bijective_of_torsionFree_general J O (q ≫ s) hP hK I
  constructor
  · intro a b hab
    apply (cancel_mono e.inv).mp
    apply hb.injective
    simpa only [Category.assoc] using
      congrArg (fun t => t ≫ e.inv) hab
  · intro b
    obtain ⟨a, ha⟩ := hb.surjective (b ≫ e.inv)
    refine ⟨a ≫ e.hom, ?_⟩
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      congrArg (fun t => t ≫ e.hom) ha

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- A complex concentrated in one degree at a sectionwise torsion-free abelian sheaf has
sectionwise torsion-free terms. -/
public lemma torsionFree_single_general (F : Sheaf J AddCommGrpCat.{w})
    (hF : ∀ V, Module.IsTorsionFree ℤ (F.obj.obj V)) (n i : ℤ) :
    ∀ V, Module.IsTorsionFree ℤ
      ((((CochainComplex.singleFunctor _ n).obj F).X i).obj.obj V) := by
  by_cases hi : i = n
  · subst i
    exact isTorsionFree_of_mono J (HomologicalComplex.singleObjXSelf (.up ℤ) n F).hom hF
  · have hz := HomologicalComplex.isZero_single_obj_X (.up ℤ) n F i hi
    have : Mono (0 : ((CochainComplex.singleFunctor _ n).obj F).X i ⟶ F) :=
      ⟨fun _ _ _ => hz.eq_of_tgt _ _⟩
    exact isTorsionFree_of_mono J (0 : ((CochainComplex.singleFunctor _ n).obj F).X i ⟶ F) hF

end General

end Stacks.Cohomology.ForgetModule

end
