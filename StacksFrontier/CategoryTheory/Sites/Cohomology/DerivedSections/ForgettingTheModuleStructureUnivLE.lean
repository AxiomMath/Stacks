module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Localization.Adjunction
public import StacksFrontier.Algebra.Homology.DerivedCategory.AdjointAcyclicObjects
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Adjunction
public import StacksFrontier.CategoryTheory.Localization.HomBijective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.ForgettingTheModuleStructure
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.ExactAbelianLowerShriek
public import StacksFrontier.Homology.Injectives.KInjective.RightDerivedCriterion
import StacksCore.Tactic.StacksAttribute

/-!
# Forgetting the module structure in derived sections, with the universes independent

Let `(C, O)` be a site with a sheaf of rings, and let `T` be a functor from abelian sheaves on
`C` to abelian groups which is corepresented by a sectionwise torsion-free abelian sheaf `A₀` —
sections over an object, corepresented by the free abelian sheaf on that object, and global
sections, corepresented by the constant sheaf `ℤ`, are the two cases of Stacks 0D6J. Then for
`K` in the unbounded derived category `D(O)` the canonical map

`R(T ∘ forget)(K) ⟶ RT(K_ab)`

is an isomorphism: the derived functor of `T` on sheaves of modules is the derived functor of
`T` on abelian sheaves, applied to the underlying abelian complex.

This is the statement of `Stacks.Cohomology.ForgetModule.sectionsForgetComparison_isIso` and
`Stacks.Cohomology.ForgetModule.globalSectionsForgetComparison_isIso`, which are stated for a
ringed site whose objects, morphisms and structure rings live in one universe. Here the site is
`C : Type u` with `Category.{v} C`, the structure rings are in `RingCat.{r}` and the module
sections and abelian coefficients are in the universe `max u v r t`, as for the big étale site
of a scheme, whose objects are one universe above its morphisms and its structure rings.

## Main definitions

* `Stacks.Cohomology.ForgetModuleUnivLE.tensorSheaf` and
  `Stacks.Cohomology.ForgetModuleUnivLE.tensorSheafAdjunction`: extension of scalars
  `- ⊗_ℤ O`, left adjoint to forgetting the module structure.
* `Stacks.Cohomology.ForgetModuleUnivLE.forgetDerivedUnit`: the comparison exhibiting
  `RT ∘ forget` as a right derived functor of `T ∘ forget`.

## Main results

* `Stacks.Cohomology.ForgetModuleUnivLE.toSheaf_localization_map_bijective_of_isLE`: morphisms
  from a bounded above sectionwise torsion-free complex of abelian sheaves into the underlying
  abelian complex of a K-injective complex of modules are computed in the homotopy category.
* `Stacks.Cohomology.ForgetModuleUnivLE.isRightDerivedFunctor_forget_comp`: **Stacks 0D6J** for
  a corepresented functor: `RT ∘ forget` is the right derived functor of `T ∘ forget`.
* `Stacks.Cohomology.ForgetModuleUnivLE.derivedForgetIso`: the resulting isomorphism
  `R(T ∘ forget) ≅ RT ∘ forget`.

## Implementation notes

The argument is the one of the source and of the single-universe development
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedSections/ForgetModuleHelpers.lean`:
extension of scalars is exact on sectionwise torsion-free abelian sheaves, so morphisms out of a
bounded above torsion-free complex into the underlying abelian complex of a K-injective complex of
modules are already computed in the homotopy category. The one change is how the exactness of
extension of scalars is obtained: a sectionwise torsion-free abelian sheaf has no positive `Ext`
into the underlying abelian sheaf of an injective module
(`Stacks.SheafOfModules.ext_eq_zero_of_isTorsionFree`, which holds with the universes
independent), so it is `Ext`-acyclic for the adjunction `- ⊗_ℤ O ⊣ forget`, and
`CategoryTheory.Adjunction.extAcyclic_shortExact` keeps the cycles sequences of an acyclic
torsion-free complex short exact after extending scalars.

## References

* [Stacks Project, Tag 0D6J](https://stacks.math.columbia.edu/tag/0D6J)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 05T7](https://stacks.math.columbia.edu/tag/05T7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Abelian Stacks.Localization
open scoped ZeroObject

namespace Stacks.Cohomology.ForgetModuleUnivLE

universe t r v u

attribute [local instance] HasDerivedCategory.standard

/-! ### Sectionwise torsion-free abelian sheaves -/

section TorsionFree

universe w

variable {D : Type u} [Category.{v} D] (K : GrothendieckTopology D) [HasSheafify K Ab.{w}]

/-- A biproduct of sectionwise torsion-free abelian sheaves is sectionwise torsion free. -/
lemma torsionFree_biprod (F G : Sheaf K Ab.{w})
    (hF : ∀ V, Module.IsTorsionFree ℤ (F.obj.obj V))
    (hG : ∀ V, Module.IsTorsionFree ℤ (G.obj.obj V)) (V : Dᵒᵖ) :
    Module.IsTorsionFree ℤ ((F ⊞ G).obj.obj V) := by
  refine ExactAbelianLowerShriek.isTorsionFree_of_mono_zsmul (fun n hn => ?_) V
  have := ExactAbelianLowerShriek.mono_zsmul_of_isTorsionFree hF n hn
  have := ExactAbelianLowerShriek.mono_zsmul_of_isTorsionFree hG n hn
  have hb : n • 𝟙 (F ⊞ G) = biprod.map (n • 𝟙 F) (n • 𝟙 G) := by
    apply biprod.hom_ext <;> simp
  rw [hb]
  infer_instance

/-- Every cohomologically bounded above complex of abelian sheaves receives a
quasi-isomorphism from one with sectionwise torsion-free terms (Stacks 05T7 for the class of
sectionwise torsion-free sheaves). -/
lemma exists_torsionFree_resolution_of_isLE
    (X : CochainComplex (Sheaf K Ab.{w}) ℤ) (n : ℤ) [X.IsLE n] :
    ∃ (G : CochainComplex (Sheaf K Ab.{w}) ℤ) (q : G ⟶ X), QuasiIso q ∧
      (∀ i V, Module.IsTorsionFree ℤ ((G.X i).obj.obj V)) := by
  let P : ObjectProperty (Sheaf K Ab.{w}) := fun F =>
    ∀ V, Module.IsTorsionFree ℤ (F.obj.obj V)
  have hP : ∀ F : Sheaf K Ab.{w},
      ∃ (G : Sheaf K Ab.{w}) (_ : P G) (q : G ⟶ F), Epi q := by
    intro F
    obtain ⟨G, q, hG, hq⟩ := ModuleSheafCohomology.exists_isTorsionFree_epi K F
    exact ⟨G, hG, q, hq⟩
  let : P.ContainsZero := by
    obtain ⟨G, hG, -, -⟩ := hP 0
    exact ⟨0, isZero_zero _, ModuleSheafCohomology.isTorsionFree_of_mono K (0 : 0 ⟶ G) hG⟩
  obtain ⟨G, q, hq, hG, _⟩ := (CochainComplex.exists_quasiIso_prop P hP n).2 X
  exact ⟨G, q, hq, hG⟩

/-- A complex concentrated in one degree at a sectionwise torsion-free abelian sheaf has
sectionwise torsion-free terms. -/
lemma torsionFree_single (F : Sheaf K Ab.{w})
    (hF : ∀ V, Module.IsTorsionFree ℤ (F.obj.obj V)) (n i : ℤ) :
    ∀ V, Module.IsTorsionFree ℤ
      ((((CochainComplex.singleFunctor _ n).obj F).X i).obj.obj V) := by
  obtain rfl | hi := eq_or_ne i n
  · exact ModuleSheafCohomology.isTorsionFree_of_mono K
      (HomologicalComplex.singleObjXSelf (.up ℤ) i F).hom hF
  · have hz := HomologicalComplex.isZero_single_obj_X (.up ℤ) n F i hi
    have : Mono (0 : ((CochainComplex.singleFunctor _ n).obj F).X i ⟶ F) :=
      ⟨fun _ _ _ => hz.eq_of_tgt _ _⟩
    exact ModuleSheafCohomology.isTorsionFree_of_mono K
      (0 : ((CochainComplex.singleFunctor _ n).obj F).X i ⟶ F) hF

end TorsionFree

section Modules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J Ab.{max u v r t}] [J.WEqualsLocallyBijective Ab.{max u v r t}]
  (O : Sheaf J RingCat.{r})

/-! ### Extension of scalars -/

/-- Morphisms out of the sheafified extension of scalars of an abelian sheaf `F` into a sheaf of
modules `M` are the morphisms from `F` into the underlying abelian sheaf of `M`. -/
def tensorSheafHomEquiv (F : Sheaf J Ab.{max u v r t}) (M : SheafOfModules.{max u v r t} O) :
    ((PresheafOfModules.sheafification (𝟙 O.obj)).obj
        (Stacks.SheafOfModules.tensorPresheaf.{u, v, max u v t, r} O.obj F.obj) ⟶ M) ≃
      (F ⟶ (SheafOfModules.toSheaf O).obj M) :=
  (Iso.addCommGroupIsoToAddEquiv
      ((Stacks.SheafOfModules.tensorSheafHomIso.{max u v t, r, v, u} J O F.obj).app
        M)).toEquiv |>.trans
    ((asIso ((sheafificationAdjunction J Ab.{max u v r t}).counit.app F)).homCongr
      (Iso.refl _))

/-- The bijection `tensorSheafHomEquiv` is natural in the sheaf of modules `M`: postcomposing with
`f : M ⟶ N` corresponds to postcomposing with the underlying morphism of abelian sheaves. -/
lemma tensorSheafHomEquiv_naturality (F : Sheaf J Ab.{max u v r t})
    (M N : SheafOfModules.{max u v r t} O) (f : M ⟶ N)
    (g : (PresheafOfModules.sheafification (𝟙 O.obj)).obj
      (Stacks.SheafOfModules.tensorPresheaf.{u, v, max u v t, r} O.obj F.obj) ⟶ M) :
    tensorSheafHomEquiv.{t, r, v, u} J O F N (g ≫ f) =
      tensorSheafHomEquiv.{t, r, v, u} J O F M g ≫ (SheafOfModules.toSheaf O).map f := by
  have h := ConcreteCategory.congr_hom
    ((Stacks.SheafOfModules.tensorSheafHomIso.{max u v t, r, v, u} J O F.obj).hom.naturality f) g
  change inv ((sheafificationAdjunction J Ab.{max u v r t}).counit.app F) ≫
      (Stacks.SheafOfModules.tensorSheafHomIso.{max u v t, r, v, u} J O F.obj).hom.app N (g ≫ f) =
    (inv ((sheafificationAdjunction J Ab.{max u v r t}).counit.app F) ≫
      (Stacks.SheafOfModules.tensorSheafHomIso.{max u v t, r, v, u} J O F.obj).hom.app M g) ≫
        (SheafOfModules.toSheaf O).map f
  change (Stacks.SheafOfModules.tensorSheafHomIso.{max u v t, r, v, u} J O F.obj).hom.app N
      (g ≫ f) =
    (Stacks.SheafOfModules.tensorSheafHomIso.{max u v t, r, v, u} J O F.obj).hom.app M g ≫
      (SheafOfModules.toSheaf O).map f at h
  exact (congrArg
      (fun k => inv ((sheafificationAdjunction J Ab.{max u v r t}).counit.app F) ≫ k) h).trans
    (Category.assoc _ _ _).symm

/-- Extension of scalars `- ⊗_ℤ O`, the left adjoint of the forgetful functor from sheaves of
`O`-modules to abelian sheaves. -/
def tensorSheaf : Sheaf J Ab.{max u v r t} ⥤ SheafOfModules.{max u v r t} O :=
  Adjunction.leftAdjointOfEquiv (tensorSheafHomEquiv.{t, r, v, u} J O)
    (tensorSheafHomEquiv_naturality.{t, r, v, u} J O)

/-- Extension of scalars is left adjoint to forgetting the module structure. -/
def tensorSheafAdjunction : tensorSheaf.{t, r, v, u} J O ⊣ SheafOfModules.toSheaf O :=
  Adjunction.adjunctionOfEquivLeft (tensorSheafHomEquiv.{t, r, v, u} J O)
    (tensorSheafHomEquiv_naturality.{t, r, v, u} J O)

/-- Extension of scalars is an additive functor. -/
instance : (tensorSheaf.{t, r, v, u} J O).Additive :=
  (tensorSheafAdjunction.{t, r, v, u} J O).left_adjoint_additive

variable [HasExt.{max u v r t} (Sheaf J Ab.{max u v r t})]
  [EnoughInjectives (Sheaf J Ab.{max u v r t})]
  [EnoughInjectives (SheafOfModules.{max u v r t} O)]

omit [EnoughInjectives (SheafOfModules.{max u v r t} O)] in
/-- A sectionwise torsion-free abelian sheaf is `Ext`-acyclic for extension of scalars: it has no
positive `Ext` into the underlying abelian sheaf of an injective module (Stacks 03FD). -/
lemma extAcyclic_of_isTorsionFree {F : Sheaf J Ab.{max u v r t}}
    (hF : ∀ V, Module.IsTorsionFree ℤ (F.obj.obj V)) :
    (tensorSheafAdjunction.{t, r, v, u} J O).extAcyclic F := fun I _ n hn => by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := Stacks.SheafOfModules.ext_eq_zero_of_isTorsionFree.{max u v r t, max u v t, r, v, u}
    J O I F hF m
  exact ⟨fun a b => by rw [h a, h b]⟩

/-- Extension of scalars preserves acyclicity of a complex of abelian sheaves with sectionwise
torsion-free terms. -/
lemma tensorSheaf_map_acyclic (K : CochainComplex (Sheaf J Ab.{max u v r t}) ℤ) (hK : K.Acyclic)
    (hP : ∀ i V, Module.IsTorsionFree ℤ ((K.X i).obj.obj V)) :
    (((tensorSheaf.{t, r, v, u} J O).mapHomologicalComplex (.up ℤ)).obj K).Acyclic := by
  have := (tensorSheafAdjunction.{t, r, v, u} J O).leftAdjoint_preservesColimits.{0, 0}
  refine CochainComplex.acyclic_mapHomologicalComplex_of_cyclesShortExact _ K fun i j hij => ?_
  have hc : ∀ V, Module.IsTorsionFree ℤ ((K.cycles j).obj.obj V) := fun V => by
    have := hP j V
    exact Function.Injective.moduleIsTorsionFree ((K.iCycles j).hom.app V)
      ((AddCommGrpCat.mono_iff_injective _).mp inferInstance) (map_zsmul _)
  exact ((tensorSheafAdjunction.{t, r, v, u} J O).extAcyclic_shortExact _
      (K.cyclesShortComplex_shortExact hij (hK j))
      (extAcyclic_of_isTorsionFree.{t, r, v, u} J O (hP i))
      (extAcyclic_of_isTorsionFree.{t, r, v, u} J O hc)).2

/-- Extension of scalars preserves a quasi-isomorphism between complexes of abelian sheaves with
sectionwise torsion-free terms. -/
lemma tensorSheaf_map_quasiIso {K L : CochainComplex (Sheaf J Ab.{max u v r t}) ℤ} (q : K ⟶ L)
    [QuasiIso q] (hK : ∀ i V, Module.IsTorsionFree ℤ ((K.X i).obj.obj V))
    (hL : ∀ i V, Module.IsTorsionFree ℤ ((L.X i).obj.obj V)) :
    QuasiIso (((tensorSheaf.{t, r, v, u} J O).mapHomologicalComplex (.up ℤ)).map q) := by
  apply Functor.quasiIso_of_acyclic_mappingCone
  have h := tensorSheaf_map_acyclic.{t, r, v, u} J O (CochainComplex.mappingCone q)
    (Functor.acyclic_mappingCone q inferInstance) (fun i =>
      let e := HomologicalComplex.homotopyCofiber.XIsoBiprod q i (i + 1) rfl
      @ModuleSheafCohomology.isTorsionFree_of_mono _ _ _ _ _ _ e.hom (IsIso.mono_of_iso e.hom)
        (torsionFree_biprod J (K.X (i + 1)) (L.X i) (hK (i + 1)) (hL i)))
  intro i
  exact (exactAt_iff_of_quasiIsoAt
    (CochainComplex.mappingCone.mapHomologicalComplexIso q
      (tensorSheaf.{t, r, v, u} J O)).hom i).mp (h i)

/-- Precomposition with a quasi-isomorphism of sectionwise torsion-free complexes of abelian
sheaves is bijective on morphisms into the underlying abelian complex of a K-injective complex
of modules, in the homotopy category. -/
lemma toSheaf_precomp_bijective_of_torsionFree
    {K L : CochainComplex (Sheaf J Ab.{max u v r t}) ℤ} (q : K ⟶ L) [QuasiIso q]
    (hK : ∀ i V, Module.IsTorsionFree ℤ ((K.X i).obj.obj V))
    (hL : ∀ i V, Module.IsTorsionFree ℤ ((L.X i).obj.obj V))
    (I : CochainComplex (SheafOfModules.{max u v r t} O) ℤ) [I.IsKInjective] :
    let Q := HomotopyCategory.quotient (Sheaf J Ab.{max u v r t}) (.up ℤ)
    let V := (SheafOfModules.toSheaf O).mapHomotopyCategory (.up ℤ)
    Function.Bijective (fun a : Q.obj L ⟶ V.obj
      ((HomotopyCategory.quotient _ (.up ℤ)).obj I) => Q.map q ≫ a) := by
  let F := (tensorSheaf.{t, r, v, u} J O).mapHomotopyCategory (.up ℤ)
  let Q := HomotopyCategory.quotient (Sheaf J Ab.{max u v r t}) (.up ℤ)
  apply adjunction_precomp_bijective
    ((tensorSheafAdjunction.{t, r, v, u} J O).mapHomotopyCategory (.up ℤ))
  have hiso : IsIso (DerivedCategory.Qh.map (F.map (Q.map q))) := by
    apply Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ (.up ℤ))
    change HomotopyCategory.quasiIso _ (.up ℤ)
      ((HomotopyCategory.quotient _ (.up ℤ)).map
        (((tensorSheaf.{t, r, v, u} J O).mapHomologicalComplex (.up ℤ)).map q))
    rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact tensorSheaf_map_quasiIso.{t, r, v, u} J O q hK hL
  exact precomp_bijective_of_localization DerivedCategory.Qh (F.map (Q.map q))
    (CochainComplex.IsKInjective.Qh_map_bijective _ I)
    (CochainComplex.IsKInjective.Qh_map_bijective _ I)

/-- **Morphisms from a cohomologically bounded above sectionwise torsion-free complex into the
underlying abelian complex of a K-injective complex of modules are computed in the homotopy
category.** -/
lemma toSheaf_localization_map_bijective_of_isLE
    (K : CochainComplex (Sheaf J Ab.{max u v r t}) ℤ) (n : ℤ) [K.IsLE n]
    (hK : ∀ i V, Module.IsTorsionFree ℤ ((K.X i).obj.obj V))
    (I : CochainComplex (SheafOfModules.{max u v r t} O) ℤ) [I.IsKInjective] :
    let Q := HomotopyCategory.quotient (Sheaf J Ab.{max u v r t}) (.up ℤ)
    let G := (SheafOfModules.toSheaf O).mapHomologicalComplex (.up ℤ)
    Function.Bijective (DerivedCategory.Qh.map :
      (Q.obj K ⟶ Q.obj (G.obj I)) → _) := by
  let Q := HomotopyCategory.quotient (Sheaf J Ab.{max u v r t}) (.up ℤ)
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
      toSheaf_precomp_bijective_of_torsionFree.{t, r, v, u} J O (q ≫ s) hP hK I
  refine ⟨fun a b hab => ?_, fun b => ?_⟩
  · apply (cancel_mono e.inv).mp
    apply hb.injective
    simpa only [Category.assoc] using hab =≫ e.inv
  · obtain ⟨a, ha⟩ := hb.surjective (b ≫ e.inv)
    refine ⟨a ≫ e.hom, ?_⟩
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using ha =≫ e.hom

/-- Morphisms out of a sectionwise torsion-free abelian sheaf, in every shift, into the
underlying abelian complex of a K-injective complex of modules are computed in the homotopy
category. -/
lemma qh_map_bijective_single_of_isKInjective (A₀ : Sheaf J Ab.{max u v r t})
    (hA₀ : ∀ V, Module.IsTorsionFree ℤ (A₀.obj.obj V))
    (I : CochainComplex (SheafOfModules.{max u v r t} O) ℤ) [I.IsKInjective] (n : ℤ) :
    Function.Bijective (DerivedCategory.Qh.map :
      ((HomotopyCategory.quotient (Sheaf J Ab.{max u v r t}) (ComplexShape.up ℤ)).obj
            ((CochainComplex.singleFunctor (Sheaf J Ab.{max u v r t}) 0).obj A₀) ⟶
          (HomotopyCategory.quotient (Sheaf J Ab.{max u v r t}) (ComplexShape.up ℤ)).obj
            ((((SheafOfModules.toSheaf O).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj I)⟦n⟧)) → _) :=
  DerivedLowerShriek.qh_map_bijective_of_iso
    ((HomotopyCategory.quotient (Sheaf J Ab.{max u v r t}) (ComplexShape.up ℤ)).mapIso
      (((SheafOfModules.toSheaf O).mapCochainComplexShiftIso n).app I))
    (toSheaf_localization_map_bijective_of_isLE.{t, r, v, u} J O
      ((CochainComplex.singleFunctor (Sheaf J Ab.{max u v r t}) 0).obj A₀) 0
      (torsionFree_single J A₀ hA₀ 0) (I⟦n⟧))

/-! ### The comparison for a corepresented functor -/

section Comparison

omit [EnoughInjectives (Sheaf J Ab.{max u v r t})]
  [EnoughInjectives (SheafOfModules.{max u v r t} O)]
  [HasExt.{max u v r t} (Sheaf J Ab.{max u v r t})]

variable (T : Sheaf J Ab.{max u v r t} ⥤ Ab.{max u v r t}) [T.Additive]
  (RT : DerivedCategory (Sheaf J Ab.{max u v r t}) ⥤ DerivedCategory Ab.{max u v r t})
  (α : T.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RT)

/-- The comparison `T(forget K) ⟶ RT(K_ab)`, for `K` a complex of modules: the derived unit of
`T` read on the underlying abelian complex. It exhibits `RT ∘ forget` as a right derived functor
of `T ∘ forget` when `T` is corepresented by a sectionwise torsion-free sheaf
(`Stacks.Cohomology.ForgetModuleUnivLE.isRightDerivedFunctor_forget_comp`). -/
def forgetDerivedUnit :
    (SheafOfModules.toSheaf O ⋙ T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ ((SheafOfModules.toSheaf O).mapDerivedCategory ⋙ RT) :=
  Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (SheafOfModules.toSheaf O ⋙ T))
        (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft ((SheafOfModules.toSheaf O).mapHomotopyCategory (ComplexShape.up ℤ)) α ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (SheafOfModules.toSheaf O).mapDerivedCategoryFactorsh.inv RT ≫
    (Functor.associator _ _ _).hom

variable [RT.IsRightDerivedFunctor α
  (HomotopyCategory.quasiIso (Sheaf J Ab.{max u v r t}) (ComplexShape.up ℤ))]
  (A₀ : Sheaf J Ab.{max u v r t}) (e : preadditiveCoyoneda.obj (op A₀) ≅ T)
  (hA₀ : ∀ V, Module.IsTorsionFree ℤ (A₀.obj.obj V))

include e hA₀ in
/-- **Stacks 0D6J for a functor corepresented by a sectionwise torsion-free sheaf, with the
universes independent.** If `T` is corepresented by a sectionwise torsion-free abelian sheaf
`A₀` and `RT` is its unbounded right derived functor, then `RT ∘ forget` is the unbounded right
derived functor of `T ∘ forget` on sheaves of `O`-modules: the derived functor of `T` computed
in `D(O)` is the one computed in `D(Ab)` on the underlying abelian complex. -/
theorem isRightDerivedFunctor_forget_comp
    [IsGrothendieckAbelian.{max u v r t} (Sheaf J Ab.{max u v r t})] :
    ((SheafOfModules.toSheaf O).mapDerivedCategory ⋙ RT).IsRightDerivedFunctor
      (forgetDerivedUnit.{t, r, v, u} J O T RT α)
      (HomotopyCategory.quasiIso (SheafOfModules.{max u v r t} O) (ComplexShape.up ℤ)) := by
  let := Stacks.SheafOfModules.sheafModulesGrothendieck.{u, v, r, t} J O
  let : HasExt.{max u v r t} (Sheaf J Ab.{max u v r t}) :=
    hasExt_of_enoughInjectives.{max u v r t} _
  have : ((SheafOfModules.toSheaf O ⋙ T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso (SheafOfModules.{max u v r t} O) (ComplexShape.up ℤ)) :=
    DerivedLowerShriek.alongFunctor_hasRightDerivedFunctor_of_isGrothendieckAbelian _
  refine Stacks.Injectives.rightDerived_of_kInjective_units _ _ _ fun I _ => ?_
  have hα : IsIso (α.app ((HomotopyCategory.quotient (Sheaf J Ab.{max u v r t})
      (ComplexShape.up ℤ)).obj
        (((SheafOfModules.toSheaf O).mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) :=
    Stacks.Cohomology.DerivedLowerShriek.rightDerivedUnit_isIso_of_corepresentable T A₀ e RT α _
      (qh_map_bijective_single_of_isKInjective.{t, r, v, u} J O A₀ hA₀ I)
  have hα' : IsIso (α.app (((SheafOfModules.toSheaf O).mapHomotopyCategory
      (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) :=
    (NatTrans.isIso_app_iff_of_iso α
      (((SheafOfModules.toSheaf O).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app I)).mp hα
  dsimp only [forgetDerivedUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  infer_instance

/-- **`R(T ∘ forget) ≅ RT ∘ forget`** (Stacks 0D6J): the derived functor of a functor `T`
corepresented by a sectionwise torsion-free sheaf, computed on unbounded complexes of modules, is
the derived functor of `T` on abelian sheaves applied to the underlying abelian complex. -/
def derivedForgetIso [IsGrothendieckAbelian.{max u v r t} (Sheaf J Ab.{max u v r t})]
    [((SheafOfModules.toSheaf O ⋙ T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso (SheafOfModules.{max u v r t} O) (ComplexShape.up ℤ))] :
    ((SheafOfModules.toSheaf O ⋙ T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
        (HomotopyCategory.quasiIso (SheafOfModules.{max u v r t} O) (ComplexShape.up ℤ)) ≅
      (SheafOfModules.toSheaf O).mapDerivedCategory ⋙ RT :=
  have := isRightDerivedFunctor_forget_comp.{t, r, v, u} J O T RT α A₀ e hA₀
  Functor.rightDerivedUnique _ _
    (((SheafOfModules.toSheaf O ⋙ T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso (SheafOfModules.{max u v r t} O) (ComplexShape.up ℤ)))
    (forgetDerivedUnit.{t, r, v, u} J O T RT α)
    (HomotopyCategory.quasiIso (SheafOfModules.{max u v r t} O) (ComplexShape.up ℤ))

end Comparison

end Modules

end Stacks.Cohomology.ForgetModuleUnivLE

end
