module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Localization.Adjunction
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Adjunction
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
public import StacksFrontier.CategoryTheory.Localization.HomBijective

/-!
# Extension of scalars and torsion-free resolutions, for forgetting the module structure

Let `(C, O)` be a small site with a sheaf of rings. Comparing unbounded derived sections of a
complex of `O`-modules with derived sections of its underlying complex of abelian sheaves comes
down to one statement: morphisms out of a cohomologically bounded above complex of sectionwise
torsion-free abelian sheaves into the underlying abelian complex of a K-injective complex of
`O`-modules are already computed in the homotopy category
(`Stacks.Cohomology.ForgetModule.toSheaf_localization_map_bijective_of_isLE`).

This file collects that statement and the machinery it needs. It is the common input of the two
comparison theorems built on it — Tag 0D6J on a general site
(`Stacks.Cohomology.ForgetModule.sectionsForgetComparison_isIso`) and Tag 0D5Y on a ringed space
(`Stacks.Cohomology.UnderlyingAbelianSheaf.sectionsForgetComparison_isIso`) — which is why it
lives here rather than in either of them.

## Main definitions

* `Stacks.Cohomology.ForgetModule.tensorSheaf`: extension of scalars `- ⊗_ℤ O`, as a functor
  from abelian sheaves to sheaves of `O`-modules.
* `Stacks.Cohomology.ForgetModule.tensorSheafAdjunction`: it is left adjoint to
  `SheafOfModules.toSheaf`.

## Main results

* `Stacks.Cohomology.ForgetModule.tensorSheaf_map_quasiIso`: extension of scalars preserves
  quasi-isomorphisms between complexes with sectionwise torsion-free terms.
* `Stacks.Cohomology.ForgetModule.exists_torsionFree_resolution_of_isLE` (Tag 05T7 for the class
  of sectionwise torsion-free sheaves): a cohomologically bounded above complex of abelian
  sheaves receives a quasi-isomorphism from one with sectionwise torsion-free terms.
* `Stacks.Cohomology.ForgetModule.toSheaf_localization_map_bijective_of_isLE`: morphisms from
  such a complex into the underlying abelian complex of a K-injective complex of modules are
  computed in the homotopy category.

## Implementation notes

Extension of scalars is built from the hom-set description
`ModuleSheafCohomology.tensorSheafHomIso` rather than as a sheafified tensor product, so that
the adjunction comes for free from `CategoryTheory.Adjunction.adjunctionOfEquivLeft`. Being a
left adjoint it is right exact; the content of
`Stacks.Cohomology.ForgetModule.tensorSheaf_map_shortExact` is left exactness on short exact
sequences with sectionwise torsion-free quotient, which comes from
`ModuleSheafCohomology.exists_extension_of_isTorsionFree`.

## References

* [Stacks Project, Tag 0D6J](https://stacks.math.columbia.edu/tag/0D6J)
* [Stacks Project, Tag 0D5Y](https://stacks.math.columbia.edu/tag/0D5Y)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 05T7](https://stacks.math.columbia.edu/tag/05T7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Localization
open scoped ZeroObject

namespace Stacks.Cohomology.ForgetModule

universe u

attribute [local instance] HasDerivedCategory.standard

open ModuleSheafCohomology

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- Morphisms out of the sheafified extension of scalars of an abelian sheaf `F` into a sheaf of
modules `M` are the morphisms from `F` into the underlying abelian sheaf of `M`. -/
public def tensorSheafHomEquiv (O : Sheaf J RingCat.{u})
    (F : Sheaf J AddCommGrpCat.{u}) (M : SheafOfModules.{u} O) :
    ((PresheafOfModules.sheafification (𝟙 O.obj)).obj (tensorPresheaf O.obj F.obj) ⟶ M) ≃
      (F ⟶ (SheafOfModules.toSheaf O).obj M) :=
  (Iso.addCommGroupIsoToAddEquiv ((tensorSheafHomIso J O F.obj).app M)).toEquiv |>.trans
    ((asIso ((sheafificationAdjunction J AddCommGrpCat.{u}).counit.app F)).homCongr
      (Iso.refl _))

/-- `Stacks.Cohomology.ForgetModule.tensorSheafHomEquiv` is natural in the sheaf of modules. -/
public lemma tensorSheafHomEquiv_naturality (O : Sheaf J RingCat.{u})
    (F : Sheaf J AddCommGrpCat.{u}) (M N : SheafOfModules.{u} O) (f : M ⟶ N)
    (g : (PresheafOfModules.sheafification (𝟙 O.obj)).obj (tensorPresheaf O.obj F.obj) ⟶ M) :
    tensorSheafHomEquiv J O F N (g ≫ f) =
      tensorSheafHomEquiv J O F M g ≫ (SheafOfModules.toSheaf O).map f := by
  have h := ConcreteCategory.congr_hom ((tensorSheafHomIso J O F.obj).hom.naturality f) g
  change inv ((sheafificationAdjunction J AddCommGrpCat.{u}).counit.app F) ≫
      (tensorSheafHomIso J O F.obj).hom.app N (g ≫ f) =
    (inv ((sheafificationAdjunction J AddCommGrpCat.{u}).counit.app F) ≫
      (tensorSheafHomIso J O F.obj).hom.app M g) ≫
        (SheafOfModules.toSheaf O).map f
  change (tensorSheafHomIso J O F.obj).hom.app N (g ≫ f) =
    (tensorSheafHomIso J O F.obj).hom.app M g ≫
      (SheafOfModules.toSheaf O).map f at h
  exact (congrArg
      (fun k => inv ((sheafificationAdjunction J AddCommGrpCat.{u}).counit.app F) ≫ k) h).trans
    (Category.assoc _ _ _).symm

/-- Extension of scalars `- ⊗_ℤ O`, the left adjoint of the forgetful functor from sheaves of
`O`-modules to abelian sheaves. -/
public def tensorSheaf (O : Sheaf J RingCat.{u}) :
    Sheaf J AddCommGrpCat.{u} ⥤ SheafOfModules.{u} O :=
  Adjunction.leftAdjointOfEquiv (tensorSheafHomEquiv J O) (tensorSheafHomEquiv_naturality J O)

/-- Extension of scalars is left adjoint to forgetting the module structure. -/
public def tensorSheafAdjunction (O : Sheaf J RingCat.{u}) :
    tensorSheaf J O ⊣ SheafOfModules.toSheaf O :=
  Adjunction.adjunctionOfEquivLeft (tensorSheafHomEquiv J O) (tensorSheafHomEquiv_naturality J O)

/-- Extension of scalars preserves the inclusion of a short exact sequence of abelian sheaves
whose quotient is sectionwise torsion free. -/
public lemma tensorSheaf_map_mono_of_shortExact (O : Sheaf J RingCat.{u})
    (S : ShortComplex (Sheaf J AddCommGrpCat.{u})) (hS : S.ShortExact)
    (hP : ∀ V, Module.IsTorsionFree ℤ (S.X₃.obj.obj V)) :
    Mono ((tensorSheaf J O).map S.f) := by
  let T := tensorSheaf J O
  let adj := tensorSheafAdjunction J O
  let I := Injective.under (T.obj S.X₁)
  let i : T.obj S.X₁ ⟶ I := Injective.ι _
  obtain ⟨g, hg⟩ := exists_extension_of_isTorsionFree J O I S hS hP (adj.homEquiv _ _ i)
  have fac : T.map S.f ≫ (adj.homEquiv _ _).symm g = i := by
    change (tensorSheaf J O).map S.f ≫ (adj.homEquiv _ _).symm g = i
    rw [← adj.homEquiv_naturality_left_symm, hg]
    exact (adj.homEquiv _ _).symm_apply_apply i
  have : Mono (T.map S.f ≫ (adj.homEquiv _ _).symm g) := by
    rw [fac]
    infer_instance
  exact mono_of_mono (T.map S.f) ((adj.homEquiv _ _).symm g)

/-- Extension of scalars is exact on short exact sequences of abelian sheaves whose quotient is
sectionwise torsion free. -/
public lemma tensorSheaf_map_shortExact (O : Sheaf J RingCat.{u})
    (S : ShortComplex (Sheaf J AddCommGrpCat.{u})) (hS : S.ShortExact)
    (hP : ∀ V, Module.IsTorsionFree ℤ (S.X₃.obj.obj V)) :
    letI := (tensorSheafAdjunction J O).left_adjoint_additive
    (S.map (tensorSheaf J O)).ShortExact := by
  let := (tensorSheafAdjunction J O).left_adjoint_additive
  let := (tensorSheafAdjunction J O).leftAdjoint_preservesColimits
  have h := (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi
    (tensorSheaf J O)).mp inferInstance S hS
  exact ShortComplex.ShortExact.mk' h.1 (tensorSheaf_map_mono_of_shortExact J O S hS hP) h.2

/-- The cycles in degree `i` map to zero in the cycles in degree `i + 1`. -/
private lemma iCycles_comp_toCycles {A : Type*} [Category A] [Abelian A]
    (K : CochainComplex A ℤ) (i : ℤ) : K.iCycles i ≫ K.toCycles i (i + 1) = 0 := by
  rw [← cancel_mono (K.iCycles (i + 1))]
  simp

/-- In an acyclic cochain complex the cycles in one degree are an extension of the cycles in the
next degree by the cycles in the current one. -/
public lemma cycles_shortExact {A : Type*} [Category A] [Abelian A]
    (K : CochainComplex A ℤ) (hK : K.Acyclic) (i : ℤ) :
    (ShortComplex.mk (K.iCycles i) (K.toCycles i (i + 1)) (by
      rw [← cancel_mono (K.iCycles (i + 1))]
      simp)).ShortExact := by
  let S := ShortComplex.mk (K.iCycles i) (K.toCycles i (i + 1)) (iCycles_comp_toCycles K i)
  let S' := ShortComplex.mk (K.iCycles i) (K.d i (i + 1)) (K.iCycles_d i (i + 1))
  let f : S ⟶ S' := { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := K.iCycles (i + 1) }
  have hS : S.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono f).mpr
    (S'.exact_of_f_is_kernel (K.cyclesIsKernel i (i + 1) (by simp)))
  refine ShortComplex.ShortExact.mk' hS inferInstance ?_
  have he := ((K.exactAt_iff' i (i + 1) (i + 2) (by simp) (by simp; omega)).mp
    (hK (i + 1))).epi_toCycles
  have : Epi (K.toCycles i (i + 1) ≫
      (K.cyclesIsoSc' i (i + 1) (i + 2) (by simp) (by simp; omega)).hom) := by
    rw [K.toCycles_cyclesIsoSc'_hom]
    exact he
  exact (epi_comp_iff_of_isIso (K.toCycles i (i + 1))
    (K.cyclesIsoSc' i (i + 1) (i + 2) (by simp) (by simp; omega)).hom).mp this

/-- Extension of scalars preserves acyclicity of a complex of abelian sheaves with sectionwise
torsion-free terms. -/
public lemma tensorSheaf_map_acyclic (O : Sheaf J RingCat.{u})
    (K : CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ) (hK : K.Acyclic)
    (hP : ∀ i V, Module.IsTorsionFree ℤ ((K.X i).obj.obj V)) :
    letI := (tensorSheafAdjunction J O).left_adjoint_additive
    ((tensorSheaf J O).mapHomologicalComplex (.up ℤ) |>.obj K).Acyclic := by
  let := (tensorSheafAdjunction J O).left_adjoint_additive
  letI := (tensorSheafAdjunction J O).leftAdjoint_preservesColimits
  let T := tensorSheaf J O
  let S (i : ℤ) := ShortComplex.mk (K.iCycles i) (K.toCycles i (i + 1))
    (iCycles_comp_toCycles K i)
  have hs (i : ℤ) : ((S i).map T).ShortExact :=
    tensorSheaf_map_shortExact J O (S i) (cycles_shortExact K hK i)
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
  let f' : (((T.mapHomologicalComplex (.up ℤ)).obj K).sc' i (i + 1) (i + 1 + 1)) ⟶ S' :=
    { τ₁ := T.map (K.toCycles i (i + 1)), τ₂ := 𝟙 _, τ₃ := 𝟙 _
      comm₁₂ := by
        change T.map (K.toCycles i (i + 1)) ≫ T.map (K.iCycles (i + 1)) =
          T.map (K.d i (i + 1)) ≫ 𝟙 _
        rw [← T.map_comp, K.toCycles_i, Category.comp_id] }
  have : Epi f'.τ₁ := (hs i).epi_g
  have : IsIso f'.τ₂ := IsIso.id _
  have : Mono f'.τ₃ := inferInstanceAs (Mono (𝟙 _))
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono f').mpr hS'

/-- A biproduct of sectionwise torsion-free abelian sheaves is sectionwise torsion free. -/
public lemma torsionFree_biprod (F G : Sheaf J AddCommGrpCat.{u})
    (hF : ∀ V, Module.IsTorsionFree ℤ (F.obj.obj V))
    (hG : ∀ V, Module.IsTorsionFree ℤ (G.obj.obj V)) (V : Cᵒᵖ) :
    Module.IsTorsionFree ℤ ((F ⊞ G).obj.obj V) := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro n x hx
  by_cases hn : n = 0
  · exact Or.inl hn
  right
  have mono_smul (H : Sheaf J AddCommGrpCat.{u})
      (hH : ∀ W, Module.IsTorsionFree ℤ (H.obj.obj W)) : Mono (n • 𝟙 H) := by
    apply (sheafToPresheaf _ _).mono_of_mono_map
    have (W : Cᵒᵖ) : Mono (((sheafToPresheaf _ _).map (n • 𝟙 H)).app W) := by
      have := hH W
      rw [AddCommGrpCat.mono_iff_injective]
      change Function.Injective (fun y : H.obj.obj W => n • y)
      exact IsSMulRegular.of_ne_zero hn
    exact NatTrans.mono_of_mono_app _
  have := mono_smul F hF
  have := mono_smul G hG
  have hb : n • 𝟙 (F ⊞ G) = biprod.map (n • 𝟙 F) (n • 𝟙 G) := by
    apply biprod.hom_ext <;> simp
  have hm : Mono (n • 𝟙 (F ⊞ G)) := by
    rw [hb]
    infer_instance
  have hi := (AddCommGrpCat.mono_iff_injective ((n • 𝟙 (F ⊞ G)).hom.app V)).mp
    inferInstance
  change Function.Injective (fun y : (F ⊞ G).obj.obj V => n • y) at hi
  apply hi
  simpa only [smul_zero] using hx

/-- Extension of scalars preserves a quasi-isomorphism between complexes of abelian sheaves with
sectionwise torsion-free terms. -/
public lemma tensorSheaf_map_quasiIso (O : Sheaf J RingCat.{u})
    {K L : CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ} (q : K ⟶ L) [QuasiIso q]
    (hK : ∀ i V, Module.IsTorsionFree ℤ ((K.X i).obj.obj V))
    (hL : ∀ i V, Module.IsTorsionFree ℤ ((L.X i).obj.obj V)) :
    letI := (tensorSheafAdjunction J O).left_adjoint_additive
    QuasiIso (((tensorSheaf J O).mapHomologicalComplex (.up ℤ)).map q) := by
  let := (tensorSheafAdjunction J O).left_adjoint_additive
  apply Functor.quasiIso_of_acyclic_mappingCone
  have h := tensorSheaf_map_acyclic J O (CochainComplex.mappingCone q)
    (Functor.acyclic_mappingCone q inferInstance) (fun i =>
      let e := HomologicalComplex.homotopyCofiber.XIsoBiprod q i (i + 1) rfl
      @isTorsionFree_of_mono _ _ _ _ _ _ e.hom (IsIso.mono_of_iso e.hom)
        (torsionFree_biprod J (K.X (i + 1)) (L.X i) (hK (i + 1)) (hL i)))
  intro i
  exact (exactAt_iff_of_quasiIsoAt
    (CochainComplex.mappingCone.mapHomologicalComplexIso q (tensorSheaf J O)).hom i).mp (h i)

/-- Every cohomologically bounded above complex of abelian sheaves receives a
quasi-isomorphism from one with sectionwise torsion-free terms. This is Stacks 05T7 for the
class of sectionwise torsion-free sheaves. -/
public lemma exists_torsionFree_resolution_of_isLE
    (K : CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ) (n : ℤ) [K.IsLE n] :
    ∃ (G : CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ) (q : G ⟶ K), QuasiIso q ∧
      (∀ i V, Module.IsTorsionFree ℤ ((G.X i).obj.obj V)) := by
  let P : ObjectProperty (Sheaf J AddCommGrpCat.{u}) := fun F =>
    ∀ V, Module.IsTorsionFree ℤ (F.obj.obj V)
  have hP : ∀ F : Sheaf J AddCommGrpCat.{u},
      ∃ (G : Sheaf J AddCommGrpCat.{u}) (_ : P G) (q : G ⟶ F), Epi q := by
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
public lemma toSheaf_precomp_bijective_of_torsionFree (O : Sheaf J RingCat.{u})
    {K L : CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ} (q : K ⟶ L) [QuasiIso q]
    (hK : ∀ i V, Module.IsTorsionFree ℤ ((K.X i).obj.obj V))
    (hL : ∀ i V, Module.IsTorsionFree ℤ ((L.X i).obj.obj V))
    (I : CochainComplex (SheafOfModules.{u} O) ℤ) [I.IsKInjective] :
    let Q := HomotopyCategory.quotient (Sheaf J AddCommGrpCat.{u}) (.up ℤ)
    let V := (SheafOfModules.toSheaf O).mapHomotopyCategory (.up ℤ)
    Function.Bijective (fun a : Q.obj L ⟶ V.obj
      ((HomotopyCategory.quotient _ (.up ℤ)).obj I) => Q.map q ≫ a) := by
  let := (tensorSheafAdjunction J O).left_adjoint_additive
  let F := (tensorSheaf J O).mapHomotopyCategory (.up ℤ)
  let Q := HomotopyCategory.quotient (Sheaf J AddCommGrpCat.{u}) (.up ℤ)
  apply adjunction_precomp_bijective ((tensorSheafAdjunction J O).mapHomotopyCategory (.up ℤ))
  have hiso : IsIso (DerivedCategory.Qh.map (F.map (Q.map q))) := by
    apply Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ (.up ℤ))
    change HomotopyCategory.quasiIso _ (.up ℤ)
      ((HomotopyCategory.quotient _ (.up ℤ)).map
        (((tensorSheaf J O).mapHomologicalComplex (.up ℤ)).map q))
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr
      (tensorSheaf_map_quasiIso J O q hK hL)
  exact precomp_bijective_of_localization DerivedCategory.Qh (F.map (Q.map q))
    (CochainComplex.IsKInjective.Qh_map_bijective _ I)
    (CochainComplex.IsKInjective.Qh_map_bijective _ I)

/-- **Morphisms from a cohomologically bounded above sectionwise torsion-free complex into the
underlying abelian complex of a K-injective complex of modules are computed in the homotopy
category.** -/
public lemma toSheaf_localization_map_bijective_of_isLE (O : Sheaf J RingCat.{u})
    (K : CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ) (n : ℤ) [K.IsLE n]
    (hK : ∀ i V, Module.IsTorsionFree ℤ ((K.X i).obj.obj V))
    (I : CochainComplex (SheafOfModules.{u} O) ℤ) [I.IsKInjective] :
    let Q := HomotopyCategory.quotient (Sheaf J AddCommGrpCat.{u}) (.up ℤ)
    let G := (SheafOfModules.toSheaf O).mapHomologicalComplex (.up ℤ)
    Function.Bijective (DerivedCategory.Qh.map :
      (Q.obj K ⟶ Q.obj (G.obj I)) → _) := by
  let Q := HomotopyCategory.quotient (Sheaf J AddCommGrpCat.{u}) (.up ℤ)
  apply localization_map_bijective_of_refinements (HomotopyCategory.quasiIso _ (.up ℤ))
  intro Z s hs
  obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective Z
  obtain ⟨s, rfl⟩ := Q.map_surjective s
  have hqs : QuasiIso s := (HomotopyCategory.quotient_map_mem_quasiIso_iff s).mp hs
  have : CochainComplex.IsLE L n := (CochainComplex.isLE_iff L n).mpr (fun i hi =>
    let := hqs.quasiIsoAt i
    (exactAt_iff_of_quasiIsoAt s i).mpr (K.exactAt_of_isLE n i hi))
  obtain ⟨P, q, hq, hP⟩ := exists_torsionFree_resolution_of_isLE J L n
  refine ⟨Q.obj P, Q.map q, (HomotopyCategory.quotient_map_mem_quasiIso_iff q).mpr hq, ?_⟩
  let e := ((SheafOfModules.toSheaf O).mapHomotopyCategoryFactors (.up ℤ)).app I
  have hb : Function.Bijective
      (fun a : Q.obj K ⟶ ((SheafOfModules.toSheaf O).mapHomotopyCategory
        (.up ℤ)).obj ((HomotopyCategory.quotient _ (.up ℤ)).obj I) =>
        (Q.map q ≫ Q.map s) ≫ a) := by
    simpa only [Functor.map_comp] using
      toSheaf_precomp_bijective_of_torsionFree J O (q ≫ s) hP hK I
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

/-- A complex concentrated in one degree at a sectionwise torsion-free abelian sheaf has
sectionwise torsion-free terms. -/
public lemma torsionFree_single (F : Sheaf J AddCommGrpCat.{u})
    (hF : ∀ V, Module.IsTorsionFree ℤ (F.obj.obj V)) (n i : ℤ) :
    ∀ V, Module.IsTorsionFree ℤ
      ((((CochainComplex.singleFunctor _ n).obj F).X i).obj.obj V) := by
  by_cases hi : i = n
  · subst i
    exact isTorsionFree_of_mono J (HomologicalComplex.singleObjXSelf (.up ℤ) n F).hom hF
  · have hz := HomologicalComplex.isZero_single_obj_X (.up ℤ) n F i hi
    have := hz.mono (0 : ((CochainComplex.singleFunctor _ n).obj F).X i ⟶ F)
    exact isTorsionFree_of_mono J (0 : ((CochainComplex.singleFunctor _ n).obj F).X i ⟶ F) hF

end Stacks.Cohomology.ForgetModule

end
