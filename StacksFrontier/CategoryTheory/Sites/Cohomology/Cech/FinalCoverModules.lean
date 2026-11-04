module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.AcyclicCoveringFamily
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.FinalCoverCofree
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.CategoryTheory.Sites.Modules.CofreeAlongRingCone
public import StacksFrontier.CategoryTheory.Sites.Modules.CofreeSlice
public import StacksFrontier.CategoryTheory.Sites.Modules.Injective
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.AcyclicCovering

/-!
# The Čech complex of a sheaf of modules along a family covering the final object

Let `C` be a site, `R` a sheaf of rings on `C`, `A` a ring with a ring map `φ : A ⟶ Γ(C, R)`
into the global sections of `R`, and `D : ι → C` a family of objects covering the final object
(`CategoryTheory.GrothendieckTopology.CoversTop`) all of whose finite nonempty products `D_x`
exist. For a sheaf of `R`-modules `N` the *Čech complex* `Č(D, N)` is the complex of `A`-modules
with `Č^n(D, N) = ∏_{x : Fin (n + 1) → ι} N(D_x)` (`cechFunctor`), and the restriction of global
sections into degree zero is the augmentation `Γ(C, N) ⟶ Č^0(D, N)` (`augmentation`), where
`Γ(C, N)` is a module over `A` through `φ` (`baseGlobalSections`, which is
`Stacks.Cohomology.SiteModules.globalSectionsFunctor` followed by restriction of scalars).

This file proves the three properties of `Č(D, -)` from which the comparison with derived global
sections is deduced in `FinalCoverDerived.lean`:

* the augmentation identifies `Γ(C, N)` with the kernel of the first Čech differential, for every
  sheaf of modules `N` (`isLimit_augmentationFork`): this is the sheaf condition for a covering of
  the final object, `CategoryTheory.Presheaf.FamilyOfElementsOnObjects.IsCompatible.section_`;
* for an injective sheaf of modules the Čech complex is exact in positive degrees
  (`isZero_homology_cechFunctor_of_injective`): an injective sheaf of modules is injective as a
  presheaf of modules (`SheafOfModules.injective_val`), hence a retract of its cofree hull
  (`Stacks.CategoryTheory.PresheafOfModules.cofreeHull`), whose Čech complex is contractible in
  positive degrees (`Stacks.CechSite.FinalCover.isZero_homology_complexFunctor_of_retract_of_pi`);
  no covering hypothesis is needed for this;
* the term of degree `p` of `Č(D, -)` is a product of sections functors
  (`cechTermFunctorIso`), so it preserves finite limits, and it carries an injective resolution of
  a sheaf of modules which is acyclic on every `D_x` to a complex exact away from degree zero
  (`exactAt_cechTerm_cochainComplex`).

## References

* [Stacks Project, Tag 03AW](https://stacks.math.columbia.edu/tag/03AW)
* [Stacks Project, Tag 03F7](https://stacks.math.columbia.edu/tag/03F7)
* [Stacks Project, Tag 03OW](https://stacks.math.columbia.edu/tag/03OW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite ComplexShape
open Stacks.Cohomology.SiteModules

universe w v u r uA t m

namespace Stacks.CechSite.FinalCover

/-- Modules in a universe `m` have products indexed by types in any universe `t ≤ m`. -/
theorem hasProducts_moduleCat (A : Type uA) [Ring A] [UnivLE.{t, m}] :
    HasProducts.{t} (ModuleCat.{m} A) :=
  fun _ ↦ (ModuleCat.hasLimitsOfSize.{t, t, m}).has_limits_of_shape _

attribute [local instance high] hasProducts_moduleCat

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

/-- Restriction of scalars preserves finite limits, whatever the universes of the two rings. -/
theorem preservesFiniteLimits_restrictScalars {S S' : Type*} [Ring S] [Ring S'] (f : S →+* S') :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{m} f) :=
  ⟨fun _ _ _ ↦ ⟨fun {_} ↦ inferInstance⟩⟩

attribute [local instance] preservesFiniteLimits_restrictScalars

/-- Restriction of scalars carries exact short complexes to exact short complexes, whatever the
universes of the two rings: it does not change the underlying maps. -/
theorem exact_map_restrictScalars {S S' : Type*} [Ring S] [Ring S'] (f : S →+* S')
    {T : ShortComplex (ModuleCat.{m} S')} (hT : T.Exact) :
    (T.map (ModuleCat.restrictScalars.{m} f)).Exact := by
  rwa [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hT ⊢

/-- Products of modules indexed by types in `w` are exact. -/
theorem ab4StarOfSize_moduleCat (A : Type uA) [Ring A] :
    AB4StarOfSize.{w} (ModuleCat.{max u v w} A) where
  ofShape K := by
    have : AB4StarOfSize.{w} AddCommGrpCat.{max u v w} := AB4StarOfSize_shrink.{w, max u v} _
    have : PreservesFiniteColimits (forget₂ (ModuleCat.{max u v w} A) AddCommGrpCat.{max u v w}) :=
      ⟨fun _ _ _ ↦ inferInstance⟩
    have : ReflectsFiniteColimits (forget₂ (ModuleCat.{max u v w} A) AddCommGrpCat.{max u v w}) :=
      {}
    have : PreservesLimitsOfSize.{w, w}
        (forget₂ (ModuleCat.{max u v w} A) AddCommGrpCat.{max u v w}) :=
      ModuleCat.forget₂AddCommGroup_preservesLimitsOfSize.{w, w, max u v w}
    exact HasExactLimitsOfShape.domain_of_functor (Discrete K)
      (forget₂ (ModuleCat.{max u v w} A) AddCommGrpCat.{max u v w})

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r})
  {A : Type uA} [Ring A] (φ : A →+* GlobalSectionRing R)

/-- Evaluation of sheaves of modules at an object is additive. -/
instance sheafOfModulesEvaluation_additive (X : Cᵒᵖ) :
    (SheafOfModules.evaluation.{m} R X).Additive := by
  dsimp [SheafOfModules.evaluation]
  infer_instance

/-! ### The ring cone of a ring mapping to the global sections -/

/-- The ring maps `A ⟶ Γ(C, R) ⟶ R(T)`. -/
def ringCone (T : Cᵒᵖ) : A →+* R.obj.obj T := (globalSectionEval R T).comp φ

/-- The ring maps `A ⟶ R(T)` are compatible with the restriction maps of `R`: a global section is
a compatible family. -/
theorem isRingCone_ringCone :
    Stacks.CategoryTheory.PresheafOfModules.IsRingCone (ringCone R φ) := by
  intro T T' f
  ext a
  exact ((φ a).2 f).symm

variable {ι : Type w} (D : ι → C)

section Defs

/-- **A sheaf of `R`-modules as a presheaf of `A`-modules**, by restriction of scalars along the
ring maps `A ⟶ R(T)`. -/
abbrev basePresheaf : SheafOfModules.{max u v w} R ⥤ (Cᵒᵖ ⥤ ModuleCat.{max u v w} A) :=
  SheafOfModules.forget R ⋙ Stacks.CategoryTheory.PresheafOfModules.toBasePresheaf
    (ringCone R φ) (isRingCone_ringCone R φ)

/-- **Global sections `Γ(C, N)` of a sheaf of `R`-modules, as an `A`-module.** -/
abbrev baseGlobalSections : SheafOfModules.{max u v w} R ⥤ ModuleCat.{max u v w} A :=
  globalSectionsFunctor R ⋙ ModuleCat.restrictScalars φ

variable [∀ (n : ℕ) (x : Fin (n + 1) → ι), HasProduct (fun a ↦ D (x a))]

/-- **The Čech complex `Č(D, N)` of a sheaf of modules**, a complex of `A`-modules whose term of
degree `n` is `∏_{x : Fin (n + 1) → ι} N(D_x)`. -/
abbrev cechFunctor : SheafOfModules.{max u v w} R ⥤ CochainComplex (ModuleCat.{max u v w} A) ℕ :=
  basePresheaf R φ ⋙ complexFunctor D (ModuleCat.{max u v w} A)

/-- Evaluation of a global section at an object, as a map of `A`-modules. -/
def sectionsEval (N : SheafOfModules.{max u v w} R) (V : C) :
    (baseGlobalSections R φ).obj N ⟶ ((basePresheaf R φ).obj N).obj (op V) :=
  ModuleCat.ofHom
    (X := (baseGlobalSections R φ).obj N) (Y := ((basePresheaf R φ).obj N).obj (op V))
    { toFun := fun s ↦ (s : N.sections).val (op V)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

/-- Evaluation of a global section at an object, on elements. -/
@[simp]
lemma sectionsEval_apply (N : SheafOfModules.{max u v w} R) (V : C) (s : N.sections) :
    (sectionsEval R φ N V).hom s = s.val (op V) := rfl

/-- Evaluation of global sections is compatible with the restriction maps. -/
@[reassoc (attr := simp)]
lemma sectionsEval_comp_map (N : SheafOfModules.{max u v w} R) {V W : C} (g : W ⟶ V) :
    sectionsEval R φ N V ≫ ((basePresheaf R φ).obj N).map g.op = sectionsEval R φ N W := by
  ext s
  exact (s : N.sections).2 g.op

/-- Evaluation of global sections is natural in the sheaf of modules. -/
@[reassoc (attr := simp)]
lemma sectionsEval_naturality {N N' : SheafOfModules.{max u v w} R} (f : N ⟶ N') (V : C) :
    (baseGlobalSections R φ).map f ≫ sectionsEval R φ N' V =
      sectionsEval R φ N V ≫ ((basePresheaf R φ).map f).app (op V) := rfl

/-- **The augmentation `Γ(C, N) ⟶ Č^0(D, N)`**: a global section goes to the family of its values
on the objects `D_x`, `x : Fin 1 → ι`. -/
def augmentation :
    baseGlobalSections R φ ⟶ cechFunctor R φ D ⋙ HomologicalComplex.eval _ (up ℕ) 0 where
  app N := lift D ((basePresheaf R φ).obj N) fun x ↦ sectionsEval R φ N (inter D x)
  naturality N N' f := by
    refine hom_ext D ((basePresheaf R φ).obj N') fun x ↦ ?_
    simp only [Functor.comp_map, HomologicalComplex.eval_map, Category.assoc, map_f_π,
      lift_comp_π, lift_comp_π_assoc]
    rfl

/-- The components of the augmentation. -/
@[reassoc (attr := simp)]
lemma augmentation_app_π (N : SheafOfModules.{max u v w} R) (x : Fin 1 → ι) :
    (augmentation R φ D).app N ≫ π D ((basePresheaf R φ).obj N) 0 x =
      sectionsEval R φ N (inter D x) :=
  lift_comp_π D _ _ x

/-- The augmentation lands in the kernel of the first Čech differential. -/
@[reassoc (attr := simp)]
lemma augmentation_app_comp_d (N : SheafOfModules.{max u v w} R) :
    (augmentation R φ D).app N ≫ ((cechFunctor R φ D).obj N).d 0 1 = 0 := by
  refine hom_ext D ((basePresheaf R φ).obj N) fun y ↦ ?_
  rw [Category.assoc]
  refine (congrArg ((augmentation R φ D).app N ≫ ·)
    (d_zero_comp_π D ((basePresheaf R φ).obj N) y)).trans ?_
  rw [Preadditive.comp_sub, zero_comp, sub_eq_zero]
  refine (augmentation_app_π_assoc R φ D N _ _).trans
    ((sectionsEval_comp_map R φ N _).trans ?_)
  exact ((augmentation_app_π_assoc R φ D N _ _).trans (sectionsEval_comp_map R φ N _)).symm

end Defs

/-! ### Degree zero: the sheaf condition for a covering of the final object -/

section DegreeZero

variable [∀ (n : ℕ) (x : Fin (n + 1) → ι), HasProduct (fun a ↦ D (x a))]

/-- The products `D_x` over the tuples `x : Fin 1 → ι` cover the final object as soon as the
members of the family do. -/
theorem coversTop_inter (hD : J.CoversTop D) :
    J.CoversTop (fun x : Fin 1 → ι ↦ inter D x) := by
  intro X
  refine J.superset_covering ?_ (hD X)
  rintro T a ⟨i, ⟨b⟩⟩
  exact ⟨fun _ ↦ i, ⟨b ≫ interLift D fun _ ↦ 𝟙 (D i)⟩⟩

/-- A projection of `inter D y`, transported along an equality of indices. -/
lemma interπ_eqToHom {n : ℕ} {y : Fin (n + 1) → ι} {b b' : Fin (n + 1)} (hb : b = b') {T : C}
    (e₁ : D (y b) = T) (e₂ : D (y b') = T) :
    interπ D y b ≫ eqToHom e₁ = interπ D y b' ≫ eqToHom e₂ := by
  subst hb
  rfl

/-- Transport of a component of a Čech cochain along an equality of tuples. -/
lemma map_π_apply_eq {N : SheafOfModules.{max u v w} R} {x x' : Fin 1 → ι} (e : x = x')
    {Z : C} (k : Z ⟶ inter D x) (k' : Z ⟶ inter D x')
    (hk : ∀ a, k ≫ interπ D x a ≫ eqToHom (congrArg D (congrFun e a)) = k' ≫ interπ D x' a)
    (z : ((cechFunctor R φ D).obj N).X 0) :
    N.val.map k.op ((π D ((basePresheaf R φ).obj N) 0 x).hom z) =
      N.val.map k'.op ((π D ((basePresheaf R φ).obj N) 0 x').hom z) := by
  subst e
  obtain rfl : k = k' := inter_hom_ext D fun a ↦ by simpa using hk a
  rfl

/-- **A cocycle of degree zero is a compatible family on the objects `D_x`.** -/
theorem isCompatible_of_d_eq_zero (N : SheafOfModules.{max u v w} R)
    (z : ((cechFunctor R φ D).obj N).X 0) (hz : ((cechFunctor R φ D).obj N).d 0 1 z = 0) :
    Presheaf.FamilyOfElementsOnObjects.IsCompatible
      (F := N.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat)
      (fun x : Fin 1 → ι ↦ (π D ((basePresheaf R φ).obj N) 0 x).hom z) := by
  intro Z x x' f g
  let y : Fin 2 → ι := ![x 0, x' 0]
  let h : Z ⟶ inter D y := interLift D (x := y)
    (Fin.cases (f ≫ interπ D x 0) (Fin.cases (g ≫ interπ D x' 0) finZeroElim))
  have hz' : (((complexFunctor D (ModuleCat.{max u v w} A)).obj
      ((basePresheaf R φ).obj N)).d 0 1).hom z = 0 := hz
  have hy := congrArg (fun t ↦ t.hom z) (d_zero_comp_π D ((basePresheaf R φ).obj N) y)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hz', map_zero, ModuleCat.hom_sub,
    LinearMap.sub_apply] at hy
  have e1 : y ∘ (1 : Fin 2).succAbove = x := funext fun a ↦ by
    rw [Subsingleton.elim a 0]
    rfl
  have e0 : y ∘ (0 : Fin 2).succAbove = x' := funext fun a ↦ by
    rw [Subsingleton.elim a 0]
    rfl
  change N.val.map f.op _ = N.val.map g.op _
  rw [← map_π_apply_eq R φ D e1 (h ≫ interMap D y (1 : Fin 2).succAbove) f ?_ z,
    ← map_π_apply_eq R φ D e0 (h ≫ interMap D y (0 : Fin 2).succAbove) g ?_ z]
  · have k : ∀ b : Fin 2, N.val.map (h ≫ interMap D y b.succAbove).op
        ((π D ((basePresheaf R φ).obj N) 0 (y ∘ b.succAbove)).hom z) =
        N.val.map h.op ((((basePresheaf R φ).obj N).map (interMap D y b.succAbove).op).hom
          ((π D ((basePresheaf R φ).obj N) 0 (y ∘ b.succAbove)).hom z)) := fun b ↦ by
      rw [op_comp]
      exact PresheafOfModules.map_comp_apply N.val _ _ _
    rw [k, k, sub_eq_zero.mp hy.symm]
  · refine Fin.forall_fin_one.2 ?_
    rw [Category.assoc, interMap_comp_interπ_assoc]
    refine (congrArg (h ≫ ·)
      (interπ_eqToHom D (by decide : (0 : Fin 2).succAbove 0 = 1) _ rfl)).trans ?_
    rw [eqToHom_refl, Category.comp_id]
    exact interLift_comp_interπ D _ 1
  · refine Fin.forall_fin_one.2 ?_
    rw [Category.assoc, interMap_comp_interπ_assoc]
    refine (congrArg (h ≫ ·)
      (interπ_eqToHom D (by decide : (1 : Fin 2).succAbove 0 = 0) _ rfl)).trans ?_
    rw [eqToHom_refl, Category.comp_id]
    exact interLift_comp_interπ D _ 0

/-- The presheaf of sets underlying a sheaf of modules is a sheaf. -/
theorem isSheaf_forget (N : SheafOfModules.{max u v w} R) :
    Presheaf.IsSheaf J (N.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat) :=
  Presheaf.isSheaf_comp_of_isSheaf _ _ _ N.isSheaf

/-- The components of the augmentation, on elements. -/
lemma π_augmentation_apply (N : SheafOfModules.{max u v w} R) (x : Fin 1 → ι) (s : N.sections) :
    (π D ((basePresheaf R φ).obj N) 0 x).hom (((augmentation R φ D).app N).hom s) =
      s.val (op (inter D x)) :=
  congrArg (fun g ↦ g.hom s) (augmentation_app_π R φ D N x)

/-- **The sheaf condition for a covering of the final object, in Čech form**: the augmentation
exhibits the global sections `Γ(C, N)` of a sheaf of modules as the kernel of the first Čech
differential. -/
theorem isLimit_augmentationFork (hD : J.CoversTop D) (N : SheafOfModules.{max u v w} R) :
    Nonempty (IsLimit (KernelFork.ofι ((augmentation R φ D).app N)
      (augmentation_app_comp_d R φ D N))) := by
  refine (ShortComplex.exact_and_mono_f_iff_f_is_kernel
    (ShortComplex.mk ((augmentation R φ D).app N) (((cechFunctor R φ D).obj N).d 0 1)
      (augmentation_app_comp_d R φ D N))).1 ⟨?_, ?_⟩
  · rw [ShortComplex.moduleCat_exact_iff]
    intro z hz
    have hx := isCompatible_of_d_eq_zero R φ D N z hz
    refine ⟨hx.section_ (coversTop_inter D hD) (isSheaf_forget R N), ?_⟩
    let Z := fun x : Fin 1 → ι ↦ ((basePresheaf R φ).obj N).obj (op (inter D x))
    have hinj : Function.Injective (ModuleCat.piIsoPi.{uA, w, max u v} Z).hom.hom :=
      (ModuleCat.mono_iff_injective _).1 inferInstance
    refine hinj (funext fun x ↦ ?_)
    have key : ∀ t, (ModuleCat.piIsoPi.{uA, w, max u v} Z).hom.hom t x = (Pi.π Z x).hom t :=
      fun t ↦ by
        rw [← ModuleCat.piIsoPi_hom_ker_subtype.{uA, w, max u v} Z x]
        rfl
    exact (key _).trans (((π_augmentation_apply R φ D N x _).trans
      (hx.section_apply _ _ x)).trans (key z).symm)
  · rw [ModuleCat.mono_iff_injective]
    intro s s' hss
    refine (coversTop_inter D hD).sections_ext ⟨_, isSheaf_forget R N⟩ (x := s) (y := s')
      fun x ↦ ?_
    rw [← π_augmentation_apply R φ D N x s, ← π_augmentation_apply R φ D N x s']
    exact congrArg _ hss

end DegreeZero

/-! ### Positive degrees: injective sheaves of modules -/

section Injective

variable [∀ (n : ℕ) (x : Fin (n + 1) → ι), HasProduct (fun a ↦ D (x a))]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] [HasSheafify J AddCommGrpCat.{max u v w}]

open Stacks.CategoryTheory.PresheafOfModules in
/-- **The Čech complex of an injective sheaf of modules is exact in positive degrees**, for any
family of objects whatsoever. An injective sheaf of modules is injective as a presheaf of modules,
hence a retract of its cofree hull, and the image of the cofree hull in presheaves of `A`-modules
is a product of cofree presheaves, whose Čech complex is contractible in positive degrees. -/
theorem isZero_homology_cechFunctor_of_injective (I : SheafOfModules.{max u v w} R) [Injective I]
    (n : ℕ) (hn : 0 < n) : IsZero (((cechFunctor R φ D).obj I).homology n) := by
  have : UnivLE.{v, max u v w} := inferInstance
  have : Injective I.val := SheafOfModules.injective_val I
  have := mono_toCofreeHull I.val
  let F := toBasePresheaf (ringCone R φ) (isRingCone_ringCone R φ)
  let e := PreservesProduct.iso F (fun W : C ↦ cofreeOne (op W) (I.val.obj (op W)))
  exact isZero_homology_complexFunctor_of_retract_of_pi D (fun W : C ↦ W)
    (fun W ↦ cofreeOneBaseValue (ringCone R φ) (op W) (I.val.obj (op W))) (F.obj I.val)
    (fun W : C ↦ F.obj (cofreeOne (op W) (I.val.obj (op W))))
    (fun W ↦ toBasePresheafCofreeOneIso _ _ (op W) _) (F.map (toCofreeHull I.val) ≫ e.hom)
    (e.inv ≫ F.map (Injective.factorThru (𝟙 I.val) (toCofreeHull I.val)))
    (by rw [Category.assoc, Iso.hom_inv_id_assoc, ← F.map_comp, Injective.comp_factorThru,
      F.map_id]) n hn

end Injective

/-! ### The terms of the Čech complex are products of sections functors -/

section Terms

variable [∀ (n : ℕ) (x : Fin (n + 1) → ι), HasProduct (fun a ↦ D (x a))]

/-- Sections of a sheaf of modules over an object, as an `A`-module. -/
abbrev baseSections (V : C) : SheafOfModules.{max u v w} R ⥤ ModuleCat.{max u v w} A :=
  SheafOfModules.evaluation R (op V) ⋙ ModuleCat.restrictScalars (ringCone R φ (op V))

/-- The term of degree `n` of the Čech complex, as a functor of the sheaf of modules. -/
abbrev cechTermFunctor (n : ℕ) : SheafOfModules.{max u v w} R ⥤ ModuleCat.{max u v w} A :=
  cechFunctor R φ D ⋙ HomologicalComplex.eval _ (up ℕ) n

/-- The family, indexed by the tuples `x : Fin (n + 1) → ι`, of the sections functors over the
products `D_x`; its product is the Čech term of degree `n`. -/
def cechEvalFamily (n : ℕ) :
    SheafOfModules.{max u v w} R ⥤ (Discrete (Fin (n + 1) → ι) ⥤ ModuleCat.{max u v w} A) where
  obj N := Discrete.functor fun x ↦ (baseSections R φ (inter D x)).obj N
  map f := Discrete.natTrans fun x ↦ (baseSections R φ (inter D x.as)).map f

/-- **The Čech term of degree `n` is the product of the sections functors over the `D_x`.** -/
def cechTermFunctorIso (n : ℕ) : cechTermFunctor R φ D n ≅ cechEvalFamily R φ D n ⋙ lim :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun f ↦ by
    simp only [Iso.refl_hom]
    refine limit.hom_ext fun ⟨x⟩ ↦ ?_
    exact (map_f_π D ((basePresheaf R φ).map f) n x).trans
      (limMap_π ((cechEvalFamily R φ D n).map f) ⟨x⟩).symm

/-- The family of sections functors preserves finite limits. -/
instance preservesFiniteLimits_cechEvalFamily (n : ℕ) :
    PreservesFiniteLimits (cechEvalFamily R φ D n) :=
  preservesFiniteLimits_of_evaluation _ fun ⟨x⟩ ↦
    inferInstanceAs (PreservesFiniteLimits (baseSections R φ (inter D x)))

/-- **The Čech term of degree `n` preserves finite limits.** -/
instance preservesFiniteLimits_cechTermFunctor (n : ℕ) :
    PreservesFiniteLimits (cechTermFunctor R φ D n) :=
  preservesFiniteLimits_of_natIso (cechTermFunctorIso R φ D n).symm

variable [HasSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [EnoughInjectives (SheafOfModules.{max u v w} R)]

/-- **The Čech term of degree `n` of an injective resolution is exact away from degree zero**,
for a sheaf of modules whose higher cohomology vanishes on every product `D_x`: each factor is
exact away from degree zero by acyclicity, exactness over a discrete index is exactness in each
component, and products of modules are exact. -/
lemma exactAt_cechTerm_cochainComplex {N : SheafOfModules.{max u v w} R}
    (I : InjectiveResolution N) (n : ℕ)
    (hac : ∀ (x : Fin (n + 1) → ι) (m : ℕ), 0 < m →
      IsZero (((SheafOfModules.evaluation R (op (inter D x))).rightDerived m).obj N))
    (q : ℤ) (hq : q ≠ 0) :
    (((cechTermFunctor R φ D n).mapHomologicalComplex (up ℤ)).obj I.cochainComplex).ExactAt q := by
  have hfactor : ∀ x : Fin (n + 1) → ι,
      ((I.cochainComplex.sc q).map (baseSections R φ (inter D x))).Exact := by
    intro x
    have hx := CategoryTheory.InjectiveResolution.exactAt_mapHomologicalComplex_cochainComplex
      (SheafOfModules.evaluation R (op (inter D x))) I (hac x) q hq
    rw [HomologicalComplex.exactAt_iff] at hx
    exact exact_map_restrictScalars (ringCone R φ (op (inter D x))) hx
  have hfam : ((I.cochainComplex.sc q).map (cechEvalFamily R φ D n)).Exact :=
    CategoryTheory.ShortComplex.exact_of_app_discrete _ fun ⟨x⟩ ↦ hfactor x
  have : AB4StarOfSize.{w} (ModuleCat.{max u v w} A) := ab4StarOfSize_moduleCat.{w, v, u} A
  rw [HomologicalComplex.exactAt_iff]
  exact ShortComplex.exact_of_iso
    (ShortComplex.mapNatIso (I.cochainComplex.sc q) (cechTermFunctorIso R φ D n)).symm
    (hfam.map lim)

end Terms

end Stacks.CechSite.FinalCover

end
