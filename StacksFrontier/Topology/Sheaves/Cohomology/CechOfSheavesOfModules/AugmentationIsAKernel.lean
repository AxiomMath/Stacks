module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfSheavesOfModules.InjectiveVanishing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Čech cohomology of a sheaf of modules in degree zero

For a cover `V = ⋃ i, U i` of an open subset of a space carrying a sheaf of rings, the
augmented module-valued Čech complex

`0 ⟶ Γ(V, ℱ) ⟶ Č⁰(𝒰, ℱ) ⟶ Č¹(𝒰, ℱ)`

of a sheaf of modules `ℱ` is exact: the augmentation is a kernel of the first Čech
differential.  This is the sheaf condition for the cover, and it is the degree-zero clause of
[Stacks, Tag 01EP].

## Main definitions

* `Stacks.Cohomology.CechSheaf.cechAugmentation`: the augmentation `Γ(V, ℱ) ⟶ Č⁰(𝒰, ℱ)`, as a
  morphism of `R(V)`-modules.
* `Stacks.Cohomology.CechSheaf.augmentedKernelFork`: it as a kernel fork of the first Čech
  differential.

## Main results

* `Stacks.Cohomology.CechSheaf.mcomp_cechAugmentation`: its components are the restrictions of
  the given section.
* `Stacks.Cohomology.CechSheaf.injective_cechAugmentation` and
  `Stacks.Cohomology.CechSheaf.exists_cechAugmentation_eq`: separatedness and gluing, in the
  componentwise form the Čech complex presents them.
* `Stacks.Cohomology.CechSheaf.isIso_kernelLift_cechAugmentation` and
  `Stacks.Cohomology.CechSheaf.isLimit_augmentedKernelFork`: **the augmentation is a kernel of
  the first Čech differential.**  This is the hypothesis `inducesIsoKernel` of
  `StacksDraft.TotalComplexQuasiIso.Hypotheses` ([Stacks, Tag 0133]) in Čech degree zero, and
  the hypothesis `IsLimit (augFork U P hT)` that
  `Stacks.Cohomology.CechZero.homologyZeroIso` asks for.
* `Stacks.Cohomology.CechSheaf.homologyZeroIso`: consequently `Ȟ⁰(𝒰, ℱ) ≅ Γ(V, ℱ)`.
* `Stacks.Cohomology.CechSheaf.cechAugmentationNatTrans`: **the augmentation is natural in the
  sheaf of modules**, which is what makes the comparison of [Stacks, Tag 0133] functorial.
* `Stacks.Cohomology.CechSheaf.sectionsTerminalFunctorIso`: and its source, sections at the
  terminal object of the slice over `V`, is `SheafOfModules.evaluation` at `V`.

## Implementation notes

The source of the augmentation is `Γ(V, ℱ)` in the presentation the Čech complex itself uses:
the sections at the terminal object `Over.mk (𝟙 V)` of the slice category, which is what
`Stacks.Cohomology.CechSheaf.sectionsPresheaf` evaluates to there.  That module and
`SheafOfModules.evaluation ℱ (op V)` carry the same underlying abelian group — this is `rfl`,
and is what lets the element layer of the positive-degree half of Stacks Tag 01EP be used on
sections over `V` — but their `R(V)`-actions differ by restriction of scalars along the
endomorphism of `R(V)` induced by the unique endomorphism of the terminal object, which is the
identity only provably.  So the two are *not* interchangeable as objects of `ModuleCat (R(V))`,
and the presentation used here is the one in which the augmentation is literally the Čech
`lift` of the restriction maps.  `sectionsTerminalFunctorIso` then crosses between the two, once:
the restriction of scalars is along the identity, by `over_map_terminal_hom_eq_id`, so
`CategoryTheory.ModuleCat.restrictScalarsId'App` applies.  The naturality of the augmentation,
`cechAugmentationNatTrans`, is stated on the `sectionsPresheaf` side throughout and relies on
`sectionsPresheafMap` to keep it there; see its docstring for why mixing the spellings makes the
square unreassociable.  The earlier treatment of the positive-degree half of Stacks Tag 01EP,
`Stacks.Cohomology.CechSheaf.isZero_cechComplex_homology_of_injective`, recorded this mismatch
as the obstruction to the degree-zero clause; the resolution is not to bridge the two module
structures but to state the
augmentation on the side the complex is built on.

Everything below the definition is done on *elements*, through
`Stacks.Cohomology.CechSheaf.mcomp`, `mmk` and `md`, exactly as the positive-degree clause of
Stacks Tag 01EP is: no isomorphism of complexes is built, and the
products of the Čech complex are never compared with the cosimplicial powers `_ ^⦋n⦌`, which is
why no `set_option` is needed.  The two sheaf axioms enter as
`Stacks.Cohomology.Basis.eq_of_res_eq` and
`Stacks.Cohomology.Basis.exists_res_eq_of_compatible`, whose index type is unrestricted, so no
`Shrink` is needed here either.

`Stacks.Cohomology.Basis.res` takes the inclusion of opens as a *proof*, and proofs of a
containment of opens are equal; so restrictions along provably equal containments are
interchangeable with no transport, and the containments appearing below are never matched up by
hand.  Tuples of length one are identified with indices through
`Stacks.CategoryTheory.CechComplex.inter_eq_single`, and pairs through `inter_eq_inf`.

In Čech degree `1` the two face maps of a pair `y : Fin 2 → ι` are
`(0 : Fin 2).succAbove = fun _ ↦ 1` and `(1 : Fin 2).succAbove = fun _ ↦ 0`, so the degree-zero
differential of a cochain `s` at `y` is
`s(y 1)|_{U(y 0) ∩ U(y 1)} - s(y 0)|_{U(y 0) ∩ U(y 1)}`; that difference vanishing is the
compatibility condition `exists_res_eq_of_compatible` asks for.

The passage from exactness of `Γ(V, ℱ) ⟶ Č⁰ ⟶ Č¹` to `IsIso` of the comparison with the kernel
is `CategoryTheory.ShortComplex.exact_iff_epi_kernel_lift` for epimorphy and
`CategoryTheory.mono_of_mono_fac` through `CategoryTheory.Limits.kernel.lift_ι` for monomorphy;
`ModuleCat` is abelian, hence balanced.

## References

* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
* [Stacks Project, Tag 01FG](https://stacks.math.columbia.edu/tag/01FG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.CategoryTheory.CechComplex
open Stacks.Cohomology.Basis (res res_id res_res res_zero res_sub res_sum res_zsmul)

universe uX uR uM uI

attribute [local instance] ModuleCat.hasLimitsOfSize
attribute [local instance] AddCommGrpCat.hasLimitsOfSize

namespace Stacks.Cohomology.CechSheaf

noncomputable section

variable {X : Type uX} [TopologicalSpace X]
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{uR}}
  {ι : Type uI} [UnivLE.{uI, uM}]
  (V : Opens X) (U : ι → Opens X) (hU : V = ⨆ i, U i) (I : SheafOfModules.{uM} R)

/-! ### Reindexing tuples of length one -/

omit [UnivLE.{uI, uM}] in
/-- A tuple of length one is the constant tuple at its only value. -/
theorem eq_const_of_fin_one (x : Fin 1 → ι) : x = fun _ => x 0 :=
  funext (Fin.forall_fin_one.2 rfl)

omit [UnivLE.{uI, uM}] in
/-- The open selected by a tuple of length one is the corresponding member of the cover. -/
theorem inter_single (i : ι) : inter U (fun _ : Fin 1 => i) = U i :=
  inter_eq_single U _

omit [UnivLE.{uI, uM}] in
include hU in
/-- Each member of the cover is contained in the covered open. -/
theorem le_covered (i : ι) : U i ≤ V := by
  rw [hU]; exact le_iSup U i

omit [UnivLE.{uI, uM}] in
include hU in
/-- The open selected by a tuple of length one is contained in the covered open. -/
theorem inter_le_covered' (x : Fin 1 → ι) : inter U x ≤ V :=
  inter_le_covered (m := 0) V U hU x

/-- **A section over `V` in the presentation the Čech complex uses, read as a section of the
underlying abelian sheaf.**  The two carry the same underlying abelian group, so this is the
identity; it exists only so that the restriction maps `Stacks.Cohomology.Basis.res` of
Stacks Tag 01EW apply to it syntactically. -/
def secV (t : ToType ((sectionsPresheaf V I).obj (op (Over.mk (𝟙 V))))) :
    ToType ((abSections I).obj (op V)) := t

/-- The inverse of `secV`, also the identity. -/
def secVInv (t : ToType ((abSections I).obj (op V))) :
    ToType ((sectionsPresheaf V I).obj (op (Over.mk (𝟙 V)))) := t

omit [UnivLE.{uI, uM}] in
/-- `secV` is injective, being the identity. -/
theorem secV_injective : Function.Injective (secV V I) := fun _ _ h => h

omit [UnivLE.{uI, uM}] in
/-- `secV` undoes `secVInv`. -/
@[simp]
theorem secV_secVInv (t : ToType ((abSections I).obj (op V))) : secV V I (secVInv V I t) = t := rfl

/-! ### The augmentation -/

/-- **The augmentation of the module-valued Čech complex**: the map from the sections of `ℱ`
over `V` to the degree-zero term of the Čech complex, given on each factor by restriction.

The source is the sections at the terminal object of the slice over `V`, which is the
presentation the Čech complex itself uses. -/
def cechAugmentation :
    (sectionsPresheaf V I).obj (op (Over.mk (𝟙 V))) ⟶
      ((cechComplexFunctor (coverObject U hU)).obj (sectionsPresheaf V I)).X 0 :=
  lift (coverObject U hU) (sectionsPresheaf V I)
    fun _ => (sectionsPresheaf V I).map (Over.mkIdTerminal.from _).op

/-- The raw component of the augmentation at a tuple is the restriction of the given section to
the open underlying the corresponding product in the slice category. -/
theorem rawcomp_cechAugmentation
    (t : ToType ((sectionsPresheaf V I).obj (op (Over.mk (𝟙 V))))) (x : Fin 1 → ι) :
    rawcomp V U hU I (ConcreteCategory.hom (cechAugmentation V U hU I) t) x =
      res (abSections I)
        (leOfHom (Over.mkIdTerminal.from (inter (coverObject U hU) x)).left) (secV V I t) := by
  rw [rawcomp, cechAugmentation, ← ConcreteCategory.comp_apply, lift_comp_π]
  rfl

/-- **The components of the augmentation** are the restrictions of the given section to the
opens selected by the tuples. -/
theorem mcomp_cechAugmentation
    (t : ToType ((sectionsPresheaf V I).obj (op (Over.mk (𝟙 V))))) (x : Fin 1 → ι) :
    mcomp V U hU I (ConcreteCategory.hom (cechAugmentation V U hU I) t) x =
      res (abSections I) (inter_le_covered' V U hU x) (secV V I t) := by
  rw [mcomp, rawcomp_cechAugmentation, res_res]

/-- **The augmentation is a cocycle**, on elements: both terms of the degree-zero differential
are the restriction of the same section over `V`. -/
theorem md_cechAugmentation
    (t : ToType ((sectionsPresheaf V I).obj (op (Over.mk (𝟙 V))))) :
    md V U hU I (ConcreteCategory.hom (cechAugmentation V U hU I) t) = 0 := by
  refine mcech_ext V U hU I _ _ fun y => ?_
  rw [mcomp_md, mcomp_zero, Fin.sum_univ_two]
  simp only [mcomp_cechAugmentation, res_res, Fin.isValue, Fin.val_zero, Fin.val_one, pow_zero,
    pow_one, one_zsmul, neg_one_zsmul]
  exact add_neg_cancel _

/-- The augmentation is a cycle of the Čech complex. -/
theorem cechAugmentation_comp_d :
    cechAugmentation V U hU I ≫
        ((cechComplexFunctor (coverObject U hU)).obj (sectionsPresheaf V I)).d 0 1 = 0 := by
  ext t
  exact md_cechAugmentation V U hU I t

omit [UnivLE.{uI, uM}] in
/-- **A morphism of presheaves acts componentwise on the Čech complex.**  The degree-`n` term is
the product indexed by the tuples, and the induced morphism is the product of the morphisms on
the factors; this is `CategoryTheory.Limits.limMap_π`.

This is the only fact about the action of `CategoryTheory.cechComplexFunctor` on morphisms that
is needed to make the augmentation natural in the sheaf, and it keeps the cosimplicial powers
`_ ^⦋n⦌` out of the proof. -/
@[reassoc (attr := simp)]
theorem cech_map_comp_π {C' : Type*} [Category C'] [HasFiniteProducts C'] {κ : Type uM}
    (W : κ → C') {A' : Type*} [Category A'] [Preadditive A'] [HasProducts.{uM} A']
    {P Q : C'ᵒᵖ ⥤ A'} (φ : P ⟶ Q) (n : ℕ) (x : Fin (n + 1) → κ) :
    ((cechComplexFunctor W).map φ).f n ≫ π W Q n x = π W P n x ≫ φ.app (op (inter W x)) :=
  limMap_π _ _

/-! ### The two sheaf axioms, componentwise -/

/-- **Separatedness, componentwise.**  A section over `V` is determined by its restrictions to
the members of the cover, so the augmentation is injective. -/
theorem injective_cechAugmentation :
    Function.Injective (ConcreteCategory.hom (cechAugmentation V U hU I)) := by
  intro t t' h
  refine secV_injective V I
    (Basis.eq_of_res_eq (abSheaf I) U (le_covered V U hU) hU.le _ _ fun i => ?_)
  have h0 := congrArg (fun z => mcomp V U hU I z (fun _ : Fin 1 => i)) h
  simp only [mcomp_cechAugmentation] at h0
  have key : ∀ s : ToType ((sectionsPresheaf V I).obj (op (Over.mk (𝟙 V)))),
      res (abSections I) (le_covered V U hU i) (secV V I s) =
        res (abSections I) (inter_single U i).ge
          (res (abSections I) (inter_le_covered' V U hU (fun _ => i)) (secV V I s)) :=
    fun s => (res_res _ _ _ (secV V I s)).symm
  rw [key t, key t', h0]

/-- **Gluing, componentwise.**  A degree-zero cocycle of the Čech complex is the augmentation of
a section over `V`: its components agree on the pairwise intersections, which is exactly the
compatibility the sheaf condition asks for. -/
@[ega "III 1.2.4" "partial"]
theorem exists_cechAugmentation_eq
    (s : ToType (((cechComplexFunctor (coverObject U hU)).obj (sectionsPresheaf V I)).X 0))
    (hs : md V U hU I s = 0) :
    ∃ t, ConcreteCategory.hom (cechAugmentation V U hU I) t = s := by
  set sf : ∀ i : ι, ToType ((abSections I).obj (op (U i))) := fun i =>
    res (abSections I) (inter_single U i).ge (mcomp V U hU I s (fun _ => i)) with hsf
  have hpair : ∀ (i j : ι) (W : Opens X) (h₁ : W ≤ U i) (h₂ : W ≤ U j),
      res (abSections I) h₁ (sf i) = res (abSections I) h₂ (sf j) := by
    intro i j W h₁ h₂
    set y : Fin 2 → ι := fun a => if a = 0 then i else j with hy
    have h0 : (y ∘ (0 : Fin 2).succAbove) = fun _ : Fin 1 => j :=
      funext (Fin.forall_fin_one.2 (by simp [hy]))
    have h1 : (y ∘ (1 : Fin 2).succAbove) = fun _ : Fin 1 => i :=
      funext (Fin.forall_fin_one.2 (by simp [hy]))
    have hwi : W ≤ inter U y := by
      rw [inter_eq_inf U y]
      refine le_inf ?_ ?_
      · simpa [hy] using h₁
      · simpa [hy] using h₂
    have hz : mcomp V U hU I (md V U hU I s) y = 0 := by rw [hs, mcomp_zero]
    rw [mcomp_md] at hz
    have hz2 := congrArg (res (abSections I) hwi) hz
    rw [res_zero, res_sum, Fin.sum_univ_two, res_zsmul, res_zsmul, res_res, res_res] at hz2
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul,
      neg_one_zsmul] at hz2
    have hzz : res (abSections I) (hwi.trans (inter_le_reindex U y (0 : Fin 2).succAbove))
          (mcomp V U hU I s (y ∘ (0 : Fin 2).succAbove)) =
        res (abSections I) (hwi.trans (inter_le_reindex U y (1 : Fin 2).succAbove))
          (mcomp V U hU I s (y ∘ (1 : Fin 2).succAbove)) := by
      rw [← sub_eq_zero, sub_eq_add_neg]; exact hz2
    have hside : ∀ (a : Fin 2) (c : ι) (h : W ≤ U c), y ∘ a.succAbove = (fun _ : Fin 1 => c) →
        res (abSections I) h (sf c) =
          res (abSections I) (hwi.trans (inter_le_reindex U y a.succAbove))
            (mcomp V U hU I s (y ∘ a.succAbove)) := fun a c h hc => by
      rw [hsf, res_res]
      exact (res_mcomp_congr V U hU I s hc _ _).symm
    rw [hside 1 i h₁ h1, hside 0 j h₂ h0, hzz]
  obtain ⟨t, ht⟩ := Basis.exists_res_eq_of_compatible (abSheaf I) U (le_covered V U hU) hU.le sf
    fun i j Z h₁ h₂ => hpair i j Z h₁ h₂
  refine ⟨secVInv V I t, mcech_ext V U hU I _ _ fun x => ?_⟩
  have hx : x = fun _ : Fin 1 => x 0 := eq_const_of_fin_one x
  have hle : inter U x ≤ inter U (fun _ : Fin 1 => x 0) := by rw [← hx]
  have hle2 : inter U x ≤ U (x 0) := hle.trans (inter_single U (x 0)).le
  have hta : res (abSections I) (le_covered V U hU (x 0)) (secV V I (secVInv V I t)) =
      sf (x 0) := ht (x 0)
  have e1 : mcomp V U hU I s x =
      res (abSections I) hle (mcomp V U hU I s (fun _ : Fin 1 => x 0)) :=
    (res_id _ _).symm.trans (res_mcomp_congr V U hU I s hx le_rfl hle)
  have e2 : res (abSections I) (inter_le_covered' V U hU x) (secV V I (secVInv V I t)) =
      res (abSections I) hle2
        (res (abSections I) (le_covered V U hU (x 0)) (secV V I (secVInv V I t))) :=
    (res_res _ _ _ _).symm
  rw [mcomp_cechAugmentation, e2, hta, hsf, res_res, e1]

/-! ### The augmentation is a kernel of the first differential -/

/-- The augmented complex `Γ(V, ℱ) ⟶ Č⁰(𝒰, ℱ) ⟶ Č¹(𝒰, ℱ)`. -/
def augmentedShortComplex : ShortComplex (ModuleCat.{uM} (SectionRing R V)) :=
  ShortComplex.mk _ _ (cechAugmentation_comp_d V U hU I)

/-- **The augmented Čech complex is exact in degree zero**: this is the sheaf condition for the
cover, through `exists_cechAugmentation_eq`. -/
theorem exact_augmentedShortComplex : (augmentedShortComplex V U hU I).Exact := by
  rw [augmentedShortComplex, ShortComplex.moduleCat_exact_iff]
  intro s hs
  exact exists_cechAugmentation_eq V U hU I s hs

/-- The augmentation is a monomorphism, by separatedness. -/
instance mono_cechAugmentation : Mono (cechAugmentation V U hU I) :=
  (ModuleCat.mono_iff_injective _).2 (injective_cechAugmentation V U hU I)

/-- **The degree-zero clause of [Stacks, Tag 01EP]: the augmentation is a kernel of the first
Čech differential.**  The comparison with the kernel is a monomorphism because the augmentation
is, and an epimorphism because the augmented complex is exact; `ModuleCat` is balanced. -/
theorem isIso_kernelLift_cechAugmentation :
    IsIso (kernel.lift
      (((cechComplexFunctor (coverObject U hU)).obj (sectionsPresheaf V I)).d 0 1)
      (cechAugmentation V U hU I) (cechAugmentation_comp_d V U hU I)) := by
  have := mono_of_mono_fac (kernel.lift_ι _ _ (cechAugmentation_comp_d V U hU I))
  exact @isIso_of_mono_of_epi _ _ _ _ _ _ this
    ((augmentedShortComplex V U hU I).exact_iff_epi_kernel_lift.1
      (exact_augmentedShortComplex V U hU I))

/-- The augmentation, as a kernel fork of the first Čech differential. -/
def augmentedKernelFork :
    KernelFork (((cechComplexFunctor (coverObject U hU)).obj (sectionsPresheaf V I)).d 0 1) :=
  KernelFork.ofι _ (cechAugmentation_comp_d V U hU I)

/-- **The augmentation is a limit kernel fork.**  This is the form
`Stacks.Cohomology.CechZero.homologyZeroIso` and
`StacksDraft.TotalComplexQuasiIso.Hypotheses` ask for. -/
def isLimit_augmentedKernelFork : IsLimit (augmentedKernelFork V U hU I) :=
  haveI := isIso_kernelLift_cechAugmentation V U hU I
  IsLimit.ofIsoLimit (limit.isLimit _)
    (Fork.ext (asIso (kernel.lift _ _ (cechAugmentation_comp_d V U hU I))).symm (by
      change inv (kernel.lift _ (cechAugmentation V U hU I)
            (cechAugmentation_comp_d V U hU I)) ≫ cechAugmentation V U hU I = kernel.ι _
      rw [IsIso.inv_comp_eq]
      exact (kernel.lift_ι _ (cechAugmentation V U hU I)
        (cechAugmentation_comp_d V U hU I)).symm))

/-- **`Ȟ⁰(𝒰, ℱ) ≅ Γ(V, ℱ)`.**  The degree-zero module-valued Čech cohomology of a sheaf of
modules, for a cover of an open `V`, is the module of sections over `V`. -/
def homologyZeroIso :
    ((cechComplexFunctor (coverObject U hU)).obj (sectionsPresheaf V I)).homology 0 ≅
      (sectionsPresheaf V I).obj (op (Over.mk (𝟙 V))) :=
  (CochainComplex.isoHomologyπ₀ _).symm ≪≫
    IsLimit.conePointUniqueUpToIso
      (((cechComplexFunctor (coverObject U hU)).obj
        (sectionsPresheaf V I)).cyclesIsKernel 0 1 (by simp))
      (isLimit_augmentedKernelFork V U hU I)

/-! ### The augmentation as a natural transformation -/

/-- **Sections over `V` in the presentation the Čech complex uses, as a functor of the sheaf of
modules**: the sections of the restriction to the slice over `V`, at the terminal object of that
slice.  This is the source of `cechAugmentation`, functorially. -/
def sectionsTerminalFunctor :
    SheafOfModules.{uM} R ⥤ ModuleCat.{uM} (SectionRing R V) :=
  sectionsPresheafFunctor.{uX, uR, uM} V ⋙
    (evaluation (Over V)ᵒᵖ (ModuleCat.{uM} (SectionRing R V))).obj (op (Over.mk (𝟙 V)))

/-- **A morphism of sheaves of modules, as a morphism of the presheaves of sections on the
slice.**

This is `sectionsPresheafFunctor V` on morphisms, named so that it carries the type
`sectionsPresheaf V I ⟶ sectionsPresheaf V J`.  `sectionsPresheaf V I` is by definition
`(sectionsPresheafFunctor V).obj I`, but the two are not *syntactically* equal, and a composite
mixing them is well typed only at default transparency -- `rw` then refuses it with "the target
expression is not type-correct under the `implicit` transparency level".  Naming the morphism at
the `sectionsPresheaf` spelling keeps the whole naturality square in one spelling, which is what
makes it reassociable. -/
def sectionsPresheafMap {I J : SheafOfModules.{uM} R} (f : I ⟶ J) :
    sectionsPresheaf.{uX, uR, uM} V I ⟶ sectionsPresheaf.{uX, uR, uM} V J :=
  (sectionsPresheafFunctor.{uX, uR, uM} V).map f

/-- **The components of the augmentation**: against the Čech projection at a tuple `x`, the
augmentation is the restriction map to the open selected by `x`.  This is `lift_comp_π`, isolated
so that `cechAugmentation` never has to be unfolded inside a composite. -/
@[reassoc (attr := simp)]
theorem cechAugmentation_comp_π (I : SheafOfModules.{uM} R) (x : Fin 1 → ι) :
    cechAugmentation V U hU I ≫ π (coverObject U hU) (sectionsPresheaf V I) 0 x =
      (sectionsPresheaf V I).map (Over.mkIdTerminal.from (inter (coverObject U hU) x)).op := by
  rw [cechAugmentation, lift_comp_π]

/-- **The augmentation `Γ(V, ℱ) ⟶ Č⁰(𝒰, ℱ)` is natural in the sheaf of modules.**

Against the Čech projection at a tuple `x` both sides are the restriction to `inter U x` composed
with the action of the morphism of sheaves, so the square is the naturality of
`sectionsPresheafMap V f` at the unique map from the terminal object of the slice; the morphism
induced on the Čech complex acts componentwise by `cech_map_comp_π`.

This is what [Stacks, Tag 0133] needs in order to make its comparison natural in the sheaf: the
augmentation of the degree-zero column of the Čech double complex of an injective resolution. -/
def cechAugmentationNatTrans :
    sectionsTerminalFunctor.{uX, uR, uM} V ⟶
      cechComplexFunctorOfCover.{uX, uR, uM} V U hU ⋙
        HomologicalComplex.eval (ModuleCat.{uM} (SectionRing R V)) (ComplexShape.up ℕ) 0 where
  app I := cechAugmentation V U hU I
  naturality I J f := by
    change (sectionsPresheafMap.{uX, uR, uM} V f).app (op (Over.mk (𝟙 V))) ≫
        cechAugmentation V U hU J =
      cechAugmentation V U hU I ≫
        ((cechComplexFunctor (coverObject U hU)).map (sectionsPresheafMap.{uX, uR, uM} V f)).f 0
    refine hom_ext (coverObject U hU) (sectionsPresheaf V J) (fun x => ?_)
    rw [Category.assoc, cechAugmentation_comp_π, Category.assoc, cech_map_comp_π,
      cechAugmentation_comp_π_assoc]
    exact ((sectionsPresheafMap.{uX, uR, uM} V f).naturality
      (Over.mkIdTerminal.from (inter (coverObject U hU) x)).op).symm


omit [UnivLE.{uI, uM}] in
/-- **The structure ring map out of the terminal object of the slice is the identity.**  There is
only one endomorphism of a terminal object, so the ring map whose restriction of scalars
`PresheafOfModules.forgetToPresheafModuleCat` takes at the terminal object is the identity of
`R(V)`. -/
theorem over_map_terminal_hom_eq_id :
    ((R.over V).obj.map (Over.mkIdTerminal.op.to (op (Over.mk (𝟙 V))))).hom =
      RingHom.id ((R.over V).obj.obj (op (Over.mk (𝟙 V)))) := by
  rw [Over.mkIdTerminal.op.hom_ext (Over.mkIdTerminal.op.to (op (Over.mk (𝟙 V)))) (𝟙 _),
    CategoryTheory.Functor.map_id]
  rfl

/-! ### Sections at the terminal object are sections over `V` -/

/-- **Sections at the terminal object of the slice over `V` are sections over `V`.**

The two carry the same underlying abelian group -- `sectionsTerminalFunctor V` *is*
`SheafOfModules.evaluation R (op V)` followed by a restriction of scalars, on the nose -- and the
ring map being restricted along is the identity by `over_map_terminal_hom_eq_id`, so
`CategoryTheory.ModuleCat.restrictScalarsId'App` identifies them, naturally.

This is the comparison the abutment clause of [Stacks, Tag 01ES] needs: that clause is stated
with `SheafOfModules.evaluation`, whereas the augmentation's source is sections at the terminal
object of the slice. -/
def sectionsTerminalFunctorIso :
    sectionsTerminalFunctor.{uX, uR, uM} V ≅ SheafOfModules.evaluation.{uM} R (op V) :=
  NatIso.ofComponents
    (fun F => ModuleCat.restrictScalarsId'App _ (over_map_terminal_hom_eq_id.{uX, uR} V)
      ((SheafOfModules.evaluation.{uM} R (op V)).obj F))
    (fun _ => ModuleCat.restrictScalarsId'App_hom_naturality _
      (over_map_terminal_hom_eq_id.{uX, uR} V) _)


end

end Stacks.Cohomology.CechSheaf

end
