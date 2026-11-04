module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroUnitULift
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroUnitSections
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSiteOfPresentation

/-!
# Raising the universe of a module corepresenting the sections over an object

Let `R` be a sheaf of rings on a site `C` whose morphisms lie in the universe `r` of the rings.
A sheaf of `R`-modules `T` with sections in `Type r` *corepresents the sections over `V`* through
`t ∈ T(V)` when every morphism `T ⟶ N` is determined by, and can be prescribed through, the image
of `t`; the extension by zero `j_{V!} O_V` of Stacks 03DI does so through its tautological section
(Stacks 0G1V). This file proves that the universe lift `Λ T` of the sections of such a `T`
corepresents the sections over `V` of sheaves of modules with sections in **any larger universe**,
through `ULift.up t`. Morphisms out of `Λ T` into a module whose sections do not lie in `Type r`
are not morphisms of the original category, so this is not formal: it is checked on one model,
the sheafification of the free presheaf of modules on the arrows into `V`, through the
compatibility of the universe lift with sheafification
(`PresheafOfModules.sheafificationUliftObjIso`), and transported to every corepresenting module.

## Main definitions

* `Stacks.SheafOfModules.IsCorepresentingSection`: `T` corepresents the sections over `V`
  through `t`.

## Main results

* `Stacks.SheafOfModules.isIso_of_isCorepresentingSection`: a morphism between two modules
  corepresenting the sections over `V`, carrying one corepresenting section to the other, is an
  isomorphism.
* `Stacks.SheafOfModules.isCorepresentingSection_uliftForPresentation`: **the universe lift of a
  module corepresenting the sections over `V` through `t` corepresents them, at the raised
  universe, through `ULift.up t`.**
* `Stacks.SheafOfModules.isCorepresentingSection_extensionByZeroUnit`: `j_{V!} O_V` corepresents
  the sections over `V` through the section attached by Stacks 0G1V to its identity.

## References

* [Stacks Project, Tag 0G1V](https://stacks.math.columbia.edu/tag/0G1V)
* [Stacks Project, Tag 03DI](https://stacks.math.columbia.edu/tag/03DI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v r t u₁ w v₁

namespace Stacks.SheafOfModules

section Corepresentation

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- `T` **corepresents the sections over `V`** through `t ∈ T(V)`: for every sheaf of modules `N`
(with sections in the universe of those of `T`), evaluation of morphisms `T ⟶ N` at `t` is a
bijection onto `N(V)`. -/
def IsCorepresentingSection {T : _root_.SheafOfModules.{v} R} (V : C) (t : T.val.obj (op V)) :
    Prop :=
  ∀ N : _root_.SheafOfModules.{v} R,
    Function.Bijective (fun ψ : T ⟶ N => (ψ.val.app (op V)).hom t)

/-- Precomposition with an isomorphism is a bijection on morphisms. -/
private theorem bijective_comp_left_of_isIso {D : Type*} [Category D] {X Y : D} (Z : D)
    (σ : X ⟶ Y) [IsIso σ] : Function.Bijective (fun ψ : Y ⟶ Z => σ ≫ ψ) :=
  ⟨fun _ _ e => (cancel_epi σ).1 e, fun ψ => ⟨inv σ ≫ ψ, by simp⟩⟩

/-- **A morphism between two modules corepresenting the sections over `V` is an isomorphism as
soon as it carries one corepresenting section to the other.** -/
theorem isIso_of_isCorepresentingSection {A B : _root_.SheafOfModules.{v} R} {V : C}
    {a : A.val.obj (op V)} {b : B.val.obj (op V)} (hA : IsCorepresentingSection V a)
    (hB : IsCorepresentingSection V b) (φ : A ⟶ B) (hφ : (φ.val.app (op V)).hom a = b) :
    IsIso φ := by
  obtain ⟨ψ, hψ⟩ := (hB A).2 a
  refine ⟨ψ, (hA A).1 ?_, (hB B).1 ?_⟩
  · show (ψ.val.app (op V)).hom ((φ.val.app (op V)).hom a) = a
    rw [hφ]
    exact hψ
  · show (φ.val.app (op V)).hom ((ψ.val.app (op V)).hom b) = b
    rw [show (ψ.val.app (op V)).hom b = a from hψ, hφ]

/-- Corepresenting the sections over `V` is carried along an isomorphism. -/
theorem IsCorepresentingSection.of_isIso {A B : _root_.SheafOfModules.{v} R} {V : C}
    {a : A.val.obj (op V)} (hA : IsCorepresentingSection V a) (σ : A ⟶ B) (hσ : IsIso σ) :
    IsCorepresentingSection V ((σ.val.app (op V)).hom a) := by
  intro N
  have h : (fun ψ : B ⟶ N => (ψ.val.app (op V)).hom ((σ.val.app (op V)).hom a)) =
      (fun ψ : A ⟶ N => (ψ.val.app (op V)).hom a) ∘ (fun ψ : B ⟶ N => σ ≫ ψ) := rfl
  rw [h]
  have := hσ
  exact (hA N).comp (bijective_comp_left_of_isIso N σ)

end Corepresentation

section FreePresheaf

variable {C : Type u₁} [Category.{r} C] (R₀ : Cᵒᵖ ⥤ RingCat.{r})

/-- The family of restrictions of a section `s` over `V` along the arrows `X ⟶ V`. -/
def restrictionFamily (V : C) (N : PresheafOfModules.{v} R₀) (s : N.obj (op V)) (X : Cᵒᵖ) :
    (X.unop ⟶ V) → N.obj X :=
  fun h => N.restrictₛₗ h.op s

/-- The morphism out of the universe lift of the free presheaf of modules on the arrows into `V`
determined by a section `s` of the target over `V`: the basis element indexed by `h : X ⟶ V` is
sent to the restriction of `s` along `h`. -/
def uliftBaseDesc (V : C) (N : PresheafOfModules.{max t r} R₀) (s : N.obj (op V)) :
    (extensionByZeroUnitPresheafBase R₀ V).uliftSections.{t} ⟶ N where
  app X := ModuleCat.ofHom
    { toFun := fun x => Finsupp.linearCombination (R₀.obj X)
        (restrictionFamily R₀ V N s X) x.down
      map_add' := fun x y => map_add (Finsupp.linearCombination (R₀.obj X)
        (restrictionFamily R₀ V N s X)) x.down y.down
      map_smul' := fun c x => map_smul (Finsupp.linearCombination (R₀.obj X)
        (restrictionFamily R₀ V N s X)) c x.down }
  naturality {X Y} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨x⟩ := x
    change Finsupp.linearCombination (R₀.obj Y) (restrictionFamily R₀ V N s Y)
        (extensionByZeroUnitBaseRestriction R₀ V f x) =
      N.restrictₛₗ f (Finsupp.linearCombination (R₀.obj X) (restrictionFamily R₀ V N s X) x)
    induction x using Finsupp.induction_linear with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | single a c =>
      rw [extensionByZeroUnitBaseRestriction_single, Finsupp.linearCombination_single,
        Finsupp.linearCombination_single, map_smulₛₗ]
      refine congrArg (R₀.map f c • ·) ?_
      change N.map (f.unop ≫ a).op s = N.map f (N.map a.op s)
      exact N.map_comp_apply a.op f s

/-- `Stacks.SheafOfModules.uliftBaseDesc` sends the lift of `Finsupp.single a c` to `c` times the
restriction of `s` along `a`. -/
lemma uliftBaseDesc_app_up_single (V : C) (N : PresheafOfModules.{max t r} R₀)
    (s : N.obj (op V)) (X : Cᵒᵖ) (a : X.unop ⟶ V) (c : R₀.obj X) :
    ((uliftBaseDesc.{r, t} R₀ V N s).app X).hom (ULift.up (Finsupp.single a c)) =
      c • N.restrictₛₗ a.op s :=
  Finsupp.linearCombination_single (R₀.obj X) c a

/-- The tautological section of the free presheaf of modules on the arrows into `V`. -/
abbrev baseGen (V : C) : (extensionByZeroUnitPresheafBase R₀ V).obj (op V) :=
  (Finsupp.single (𝟙 V) 1 : (V ⟶ V) →₀ R₀.obj (op V))

/-- The universe lift of the tautological section. -/
abbrev uliftBaseGen (V : C) :
    ((extensionByZeroUnitPresheafBase R₀ V).uliftSections.{t}).obj (op V) :=
  ULift.up (baseGen R₀ V)

/-- **Morphisms out of the universe lift of the free presheaf of modules on the arrows into `V`,
into a presheaf of modules with sections in any universe containing those of the rings, are the
sections over `V`.** -/
theorem bijective_uliftBase_eval (V : C) (N : PresheafOfModules.{max t r} R₀) :
    Function.Bijective (fun ψ : (extensionByZeroUnitPresheafBase R₀ V).uliftSections.{t} ⟶ N =>
      (ψ.app (op V)).hom (uliftBaseGen.{r, t} R₀ V)) := by
  refine Function.bijective_iff_has_inverse.2
    ⟨uliftBaseDesc.{r, t} R₀ V N, fun ψ => ?_, fun s => ?_⟩
  · refine PresheafOfModules.uliftSections_hom_ext (fun X x => ?_)
    induction x using Finsupp.induction_linear with
    | zero =>
      exact ((uliftBaseDesc.{r, t} R₀ V N _).app X).hom.map_zero.trans
        (ψ.app X).hom.map_zero.symm
    | add x y hx hy =>
      exact (((uliftBaseDesc.{r, t} R₀ V N _).app X).hom.map_add (ULift.up x)
        (ULift.up y)).trans
        ((congrArg₂ (· + ·) hx hy).trans ((ψ.app X).hom.map_add (ULift.up x) (ULift.up y)).symm)
    | single a c =>
      rw [uliftBaseDesc_app_up_single]
      have h₁ : (ULift.up (Finsupp.single a c) :
          ((extensionByZeroUnitPresheafBase R₀ V).uliftSections.{t}).obj X) =
          c • ((extensionByZeroUnitPresheafBase R₀ V).uliftSections.{t}).restrictₛₗ a.op
            (uliftBaseGen.{r, t} R₀ V) := by
        refine congrArg ULift.up ?_
        show Finsupp.single a c =
          c • extensionByZeroUnitBaseRestriction R₀ V a.op (Finsupp.single (𝟙 V) 1)
        rw [extensionByZeroUnitBaseRestriction_single, map_one, Finsupp.smul_single,
          smul_eq_mul, mul_one]
        simp
      rw [h₁, map_smul]
      refine congrArg (c • ·) ?_
      exact (PresheafOfModules.naturality_apply ψ a.op _).symm
  · show ((uliftBaseDesc.{r, t} R₀ V N s).app (op V)).hom
      (ULift.up (Finsupp.single (𝟙 V) 1)) = s
    rw [uliftBaseDesc_app_up_single]
    refine (one_smul _ _).trans ?_
    exact ConcreteCategory.congr_hom (N.presheaf.map_id (op V)) s

end FreePresheaf

section Sheaf

variable {C : Type u₁} [Category.{r} C] (J : GrothendieckTopology C) (R : Sheaf J RingCat.{r})
  [HasWeakSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{max t r}] [J.WEqualsLocallyBijective AddCommGrpCat.{max t r}]

/-- The sheafification of the free presheaf of modules on the arrows into `V`: a model of
`j_{V!} O_V` built from an explicit presheaf. -/
abbrev freeSheafOfArrows (V : C) : _root_.SheafOfModules.{r} R :=
  (PresheafOfModules.sheafification.{r} (𝟙 R.obj)).obj (extensionByZeroUnitPresheafBase R.obj V)

/-- The tautological section of `Stacks.SheafOfModules.freeSheafOfArrows`. -/
abbrev freeSheafOfArrowsGen (V : C) : (freeSheafOfArrows J R V).val.obj (op V) :=
  (((PresheafOfModules.sheafificationAdjunction.{r} (𝟙 R.obj)).unit.app
    (extensionByZeroUnitPresheafBase R.obj V)).app (op V)).hom (baseGen R.obj V)

/-- **The universe lift of the free sheaf of modules on the arrows into `V` corepresents the
sections over `V` at the raised universe.** The universe lift commutes with sheafification, and
morphisms out of the universe lift of the free presheaf are the sections over `V`. -/
theorem isCorepresentingSection_uliftForPresentation_freeSheafOfArrows (V : C) :
    IsCorepresentingSection
      (T := _root_.SheafOfModules.uliftForPresentation.{u₁, r, r, r, t} (freeSheafOfArrows J R V))
      V (ULift.up (freeSheafOfArrowsGen J R V)) := by
  intro N
  let P := extensionByZeroUnitPresheafBase R.obj V
  let e := PresheafOfModules.sheafificationUliftObjIso.{u₁, r, r, r, t} (𝟙 R.obj) P
  let adj := PresheafOfModules.sheafificationAdjunction.{max t r} (𝟙 R.obj)
  have key : adj.homEquiv _ _ e.hom =
      PresheafOfModules.uliftSheafificationUnit.{u₁, r, r, r, t} (𝟙 R.obj) P := by
    have he : e.hom = (adj.homEquiv _ _).symm
        (PresheafOfModules.uliftSheafificationUnit.{u₁, r, r, r, t} (𝟙 R.obj) P) := by
      rw [Adjunction.homEquiv_counit]
      simp [e, PresheafOfModules.sheafificationUliftObjIso, adj]
    rw [he, Equiv.apply_symm_apply]
  have h : (fun ψ : _root_.SheafOfModules.uliftForPresentation.{u₁, r, r, r, t}
        (freeSheafOfArrows J R V) ⟶ N =>
          (ψ.val.app (op V)).hom (ULift.up (freeSheafOfArrowsGen J R V))) =
      (fun φ => (φ.app (op V)).hom (uliftBaseGen.{r, t} R.obj V)) ∘ (adj.homEquiv _ _) ∘
        (fun ψ => e.hom ≫ ψ) := by
    funext ψ
    show _ = ((adj.homEquiv _ _ (e.hom ≫ ψ)).app (op V)).hom (uliftBaseGen.{r, t} R.obj V)
    rw [Adjunction.homEquiv_naturality_right, key]
    rfl
  rw [h]
  exact (bijective_uliftBase_eval.{r, t} R.obj V _).comp
    ((adj.homEquiv _ _).bijective.comp (bijective_comp_left_of_isIso _ e.hom))

/-- The free sheaf of modules on the arrows into `V` corepresents the sections over `V`, read
off its universe lift through the full faithfulness of the universe lift. -/
theorem isCorepresentingSection_freeSheafOfArrows (V : C) :
    IsCorepresentingSection V (freeSheafOfArrowsGen J R V) := by
  intro N
  have h : (fun ψ : freeSheafOfArrows J R V ⟶ N =>
        (ψ.val.app (op V)).hom (freeSheafOfArrowsGen J R V)) =
      ULift.down ∘ (fun ψ' : _root_.SheafOfModules.uliftForPresentation.{u₁, r, r, r, t}
          (freeSheafOfArrows J R V) ⟶
            _root_.SheafOfModules.uliftForPresentation.{u₁, r, r, r, t} N =>
          (ψ'.val.app (op V)).hom (ULift.up (freeSheafOfArrowsGen J R V))) ∘
        (fun ψ => (_root_.SheafOfModules.uliftForPresentationFunctor.{u₁, r, r, r, t}).map ψ) :=
    rfl
  rw [h]
  exact Equiv.ulift.bijective.comp
    ((isCorepresentingSection_uliftForPresentation_freeSheafOfArrows.{r, t} J R V _).comp
      ⟨(_root_.SheafOfModules.uliftForPresentationFunctor.{u₁, r, r, r, t}).map_injective,
        (_root_.SheafOfModules.uliftForPresentationFunctor.{u₁, r, r, r, t}).map_surjective⟩)

/-- **The universe lift of a module corepresenting the sections over `V` through `t`
corepresents them at the raised universe through `ULift.up t`.** Such a module is isomorphic to
the free sheaf of modules on the arrows into `V`, by an isomorphism carrying the tautological
section to `t`, and the universe lift of the latter corepresents the sections. -/
theorem isCorepresentingSection_uliftForPresentation {T : _root_.SheafOfModules.{r} R} {V : C}
    {s : T.val.obj (op V)} (hT : IsCorepresentingSection V s) :
    IsCorepresentingSection
      (T := _root_.SheafOfModules.uliftForPresentation.{u₁, r, r, r, t} T) V (ULift.up s) := by
  obtain ⟨σ, hσ⟩ := (isCorepresentingSection_freeSheafOfArrows.{r, t} J R V T).2 s
  have : IsIso σ := isIso_of_isCorepresentingSection
    (isCorepresentingSection_freeSheafOfArrows.{r, t} J R V) hT σ hσ
  have := (isCorepresentingSection_uliftForPresentation_freeSheafOfArrows.{r, t} J R V).of_isIso
    ((_root_.SheafOfModules.uliftForPresentationFunctor.{u₁, r, r, r, t}).map σ)
    (Functor.map_isIso _ σ)
  have hs : (((_root_.SheafOfModules.uliftForPresentationFunctor.{u₁, r, r, r, t}).map σ).val.app
      (op V)).hom (ULift.up (freeSheafOfArrowsGen J R V)) = ULift.up s := congrArg ULift.up hσ
  exact (congrArg (fun x => IsCorepresentingSection
    (T := (_root_.SheafOfModules.uliftForPresentationFunctor.{u₁, r, r, r, t}).obj T) V x) hs).mp
      this

end Sheaf

section ExtensionByZero

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C) (R : Sheaf J RingCat.{w})
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

omit [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **`j_{V!} O_V` corepresents the sections over `V`** (Stacks 0G1V), through the section
attached by `Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv` to its identity. -/
theorem isCorepresentingSection_extensionByZeroUnit (V : C)
    [(_root_.SheafOfModules.pushforward.{w} (F := Over.forget V)
      (𝟙 (R.over V) : (R.over V) ⟶ (R.over V))).IsRightAdjoint] :
    IsCorepresentingSection V (Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv J R V _
      (𝟙 ((_root_.SheafOfModules.pullback.{w} (F := Over.forget V)
        (𝟙 (R.over V) : (R.over V) ⟶ (R.over V))).obj
          (_root_.SheafOfModules.unit (R.over V))))) := by
  intro N
  have h : (fun ψ : (_root_.SheafOfModules.pullback.{w} (F := Over.forget V)
        (𝟙 (R.over V) : (R.over V) ⟶ (R.over V))).obj
          (_root_.SheafOfModules.unit (R.over V)) ⟶ N =>
          (ψ.val.app (op V)).hom (Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv J R V _
            (𝟙 _))) =
      Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv J R V N := by
    funext ψ
    conv_rhs => rw [← Category.id_comp ψ]
    rw [Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv_naturality]
    rfl
  rw [h]
  exact (Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv J R V N).bijective

end ExtensionByZero

end Stacks.SheafOfModules

end
