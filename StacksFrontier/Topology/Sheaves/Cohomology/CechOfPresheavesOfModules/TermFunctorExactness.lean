module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Sets.Opens
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Degreewise exactness of the Čech complex of presheaves of modules

(Stacks project tag 01EJ, Lemma 20.10.1.)

Let $R : (\mathrm{Opens}\,X)^{op} \to \mathrm{RingCat}$ be a presheaf of rings on a topological
space $X$, and let $\mathcal{U} : U = \bigcup_{i \in I} U_i$ be an open covering of an open
$U \subseteq X$. For a tuple $(i_0, \ldots, i_p) \in I^{p+1}$ write
$U_{i_0 \ldots i_p} = U_{i_0} \cap \cdots \cap U_{i_p}$. For a presheaf of $R$-modules
$\mathcal{F}$ the degree-$p$ Čech cochain module is
$$
  \check{\mathcal{C}}^p(\mathcal{U}, \mathcal{F})
    = \prod_{(i_0, \ldots, i_p) \in I^{p+1}} \mathcal{F}(U_{i_0 \ldots i_p}),
$$
an $R(U)$-module via the restriction maps $R(U) \to R(U_{i_0\ldots i_p})$ (tag 01EI). The
product ranges over all tuples (ordinary, not alternating, Čech cochains, as in tag 01ED).

The Čech functor is exact. Since a short exact sequence of complexes is one that is short
exact in each degree, this is stated degreewise: the functor
$\check{\mathcal{C}}^p(\mathcal{U}, -)$ sends short exact sequences of presheaves of
$R$-modules to short exact sequences of $R(U)$-modules, for every $p$.

## Main definitions

* `CechOpenCover`: an open covering of an open subset `U` of a topological space.
* `cechInter`: the intersection `U_{σ 0} ∩ ⋯ ∩ U_{σ p}` attached to a tuple `σ`.
* `cechTermFunctor`: the functor `F ↦ F(U_{σ 0 … σ p})` into `R(U)`-modules.
* `cechObj`: the degree-`p` Čech term `F ↦ ∏_σ F(U_{σ 0 … σ p})`.

## Main results

* `moduleCat_hasExactLimitsOfShape_discrete`: products of modules are exact (AB4*).
* `piObj_preservesFiniteLimits`, `piObj_preservesFiniteColimits`: into a category with exact
  products, a product of functors preserving finite limits (resp. colimits) preserves them.
* `cechTermFunctor_exact`: each Čech factor sends short exact sequences to short exact
  sequences.
* `cech_functor_exact`: the degree-`p` Čech term sends short exact sequences to short exact
  sequences.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace

variable {X : TopCat}

/-- A product of additive functors into a preadditive category with products is additive. -/
theorem additive_piObj {J A B : Type*} [Category A] [Category B] [Preadditive A]
    [Preadditive B] [HasProducts B] (F : J → (A ⥤ B)) [∀ j, (F j).Additive] :
    (∏ᶜ F).Additive where
  map_add := by
    intro M N f g
    apply (isLimitOfPreserves ((evaluation A B).obj N)
      (limit.isLimit (Discrete.functor F))).hom_ext
    rintro ⟨j⟩
    have h1 := (Pi.π F j).naturality (f + g)
    have h2 := (Pi.π F j).naturality f
    have h3 := (Pi.π F j).naturality g
    simp only [Functor.map_add] at h1
    dsimp [Pi.π] at *
    change (∏ᶜ F).map (f + g) ≫ (limit.π (Discrete.functor F) { as := j }).app N
        = ((∏ᶜ F).map f + (∏ᶜ F).map g) ≫ (limit.π (Discrete.functor F) { as := j }).app N
    rw [h1, Preadditive.add_comp, h2, h3, Preadditive.comp_add]

/-- The auxiliary functor `A ⥤ (Discrete J ⥤ B)` sending `a` to the discrete
diagram `j ↦ (F j).obj a`. Composing with `lim` recovers `∏ᶜ F`. -/
@[simps]
def piDiscreteFunctor {J A B : Type*} [Category A] [Category B]
    (F : J → (A ⥤ B)) : A ⥤ (Discrete J ⥤ B) where
  obj a := Discrete.functor (fun j => (F j).obj a)
  map {a a'} f := Discrete.natTrans (fun j => (F j.as).map f)
  map_id a := by
    ext ⟨j⟩
    simp [Discrete.natTrans]
  map_comp f g := by
    ext ⟨j⟩
    simp [Discrete.natTrans]

section PiPreserves
open Limits

variable {J A B : Type*} [Category A] [Category B] [HasProducts B]

/-- The diagram `Discrete.functor F ⋙ (evaluation A B).obj a` agrees with the
discrete diagram `j ↦ (F j).obj a`. -/
def piDiscreteDiagIso (F : J → (A ⥤ B)) (a : A) :
    Discrete.functor F ⋙ (evaluation A B).obj a ≅ (piDiscreteFunctor F).obj a :=
  Discrete.natIso (fun _ => Iso.refl _)

/-- Each evaluation of `piDiscreteFunctor F` recovers `F j`. -/
@[simps!]
def piDiscreteFunctorCompEval (F : J → (A ⥤ B)) (j : J) :
    piDiscreteFunctor F ⋙ (evaluation (Discrete J) B).obj ⟨j⟩ ≅ F j :=
  NatIso.ofComponents (fun _ => Iso.refl _)

/-- If every `F j` preserves finite limits, then so does `piDiscreteFunctor F`. -/
instance piDiscreteFunctor_preservesFiniteLimits (F : J → (A ⥤ B))
    [∀ j, PreservesFiniteLimits (F j)] :
    PreservesFiniteLimits (piDiscreteFunctor F) :=
  ⟨fun _ _ _ => preservesLimitsOfShape_of_evaluation _ _
    fun ⟨j⟩ => preservesLimitsOfShape_of_natIso (piDiscreteFunctorCompEval F j).symm⟩

/-- If every `F j` preserves finite colimits, then so does `piDiscreteFunctor F`. -/
instance piDiscreteFunctor_preservesFiniteColimits (F : J → (A ⥤ B))
    [∀ j, PreservesFiniteColimits (F j)] :
    PreservesFiniteColimits (piDiscreteFunctor F) :=
  ⟨fun _ _ _ => preservesColimitsOfShape_of_evaluation _ _
    fun ⟨j⟩ => preservesColimitsOfShape_of_natIso (piDiscreteFunctorCompEval F j).symm⟩

/-- `∏ᶜ F` is naturally isomorphic to `piDiscreteFunctor F ⋙ lim`. -/
noncomputable def piObjIsoCompLim (F : J → (A ⥤ B)) :
    (∏ᶜ F : A ⥤ B) ≅ piDiscreteFunctor F ⋙ lim :=
  NatIso.ofComponents
    (fun a =>
      (preservesLimitIso ((evaluation A B).obj a) (Discrete.functor F)) ≪≫
        HasLimit.isoOfNatIso (piDiscreteDiagIso F a))
    (by
      intro a a' f
      apply limit.hom_ext
      intro ⟨j⟩
      simp [piDiscreteDiagIso])

variable [HasFiniteColimits B] [HasExactLimitsOfShape (Discrete J) B]

/-- A product of finite-limit-preserving functors preserves finite limits. -/
instance piObj_preservesFiniteLimits (F : J → (A ⥤ B))
    [∀ j, PreservesFiniteLimits (F j)] :
    PreservesFiniteLimits (∏ᶜ F : A ⥤ B) :=
  preservesFiniteLimits_of_natIso (piObjIsoCompLim F).symm

/-- A product of finite-colimit-preserving functors into a category `B` with exact products
preserves finite colimits. -/
instance piObj_preservesFiniteColimits (F : J → (A ⥤ B))
    [∀ j, PreservesFiniteColimits (F j)] :
    PreservesFiniteColimits (∏ᶜ F : A ⥤ B) :=
  preservesFiniteColimits_of_natIso (piObjIsoCompLim F).symm

end PiPreserves

universe u_ML u_R

/-- Grothendieck's axiom AB4* for module categories: `ModuleCat R` has exact products, i.e. for
every index type `J` the limit functor over `Discrete J` preserves finite colimits. -/
instance moduleCat_hasExactLimitsOfShape_discrete (R : Type u_R) [Ring R] (J : Type) :
    HasExactLimitsOfShape (Discrete J) (ModuleCat.{u_ML} R) := by
  refine @hasExactLimitsOfShape_of_preservesEpi (ModuleCat.{u_ML} R) _ _ (Discrete J) _ _
    ⟨fun {F G} η hη => ?_⟩
  rw [NatTrans.epi_iff_epi_app] at hη
  rw [ModuleCat.epi_iff_surjective]
  intro y
  choose g hg using fun j =>
    (ModuleCat.epi_iff_surjective (η.app j)).1 (hη j) (ConcreteCategory.hom (limit.π G j) y)
  have hL := isLimitOfPreserves (forget (ModuleCat.{u_ML} R)) (limit.isLimit F)
  have hsec : g ∈ (F ⋙ forget (ModuleCat.{u_ML} R)).sections := by
    rintro ⟨j⟩ ⟨j'⟩ ⟨⟨(rfl : j = j')⟩⟩
    simp
  refine ⟨(Types.isLimitEquivSections hL).symm ⟨g, hsec⟩, ?_⟩
  apply Concrete.isLimit_ext G (limit.isLimit G)
  intro j
  have hpa : ConcreteCategory.hom (limit.π F j)
      ((Types.isLimitEquivSections hL).symm ⟨g, hsec⟩) = g j :=
    Types.isLimitEquivSections_symm_apply hL ⟨g, hsec⟩ j
  have key := ConcreteCategory.congr_hom (limMap_π η j)
    ((Types.isLimitEquivSections hL).symm ⟨g, hsec⟩)
  rwa [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hpa, hg j] at key

/-- An open covering `U = ⋃ i, obj i` of an open `U` of a topological space `X`. -/
structure CechOpenCover (X : TopCat) where
  /-- The index set of the covering. -/
  ι : Type
  /-- The open subset `U` being covered. -/
  U : Opens X
  /-- The opens of the covering. -/
  obj : ι → Opens X
  /-- Each member of the covering is contained in `U`. -/
  le : ∀ i, obj i ≤ U
  /-- The covering covers `U`. -/
  covers : ⨆ i, obj i = U

variable (R : (Opens X)ᵒᵖ ⥤ RingCat) (𝒰 : CechOpenCover X)

/-- The `(p+1)`-fold intersection `U_{σ 0} ∩ ⋯ ∩ U_{σ p}` associated to a tuple
`σ : Fin (p+1) → I`. -/
@[ega "III 6.6.4", sga "4½ Arcata 6.1"]
def cechInter (p : ℕ) (σ : Fin (p + 1) → 𝒰.ι) : Opens X := ⨅ k, 𝒰.obj (σ k)

/-- Every `(p+1)`-fold intersection is contained in `U` (the tuple is nonempty). -/
theorem cechInter_le_U (p : ℕ) (σ : Fin (p + 1) → 𝒰.ι) : cechInter 𝒰 p σ ≤ 𝒰.U :=
  le_trans (iInf_le _ (0 : Fin (p + 1))) (𝒰.le _)

/-- The restriction ring map `R(U) → R(U_{σ 0 … σ p})` of the structure presheaf
of rings, used to give each Čech factor its `R(U)`-module structure. -/
def cechRestMap (p : ℕ) (σ : Fin (p + 1) → 𝒰.ι) :
    R.obj (Opposite.op 𝒰.U) ⟶ R.obj (Opposite.op (cechInter 𝒰 p σ)) :=
  R.map (homOfLE (cechInter_le_U 𝒰 p σ)).op

/-- The single factor `F ↦ F(U_{σ 0 … σ p})` of the Čech complex in degree `p`,
viewed as a functor into `R(U)`-modules via restriction of scalars. -/
@[ega "III 6.6.4" "the section factor Γ(U_ρ"]
noncomputable def cechTermFunctor (p : ℕ) (σ : Fin (p + 1) → 𝒰.ι) :
    PresheafOfModules R ⥤ ModuleCat (R.obj (Opposite.op 𝒰.U)) :=
  PresheafOfModules.evaluation R (Opposite.op (cechInter 𝒰 p σ)) ⋙
    ModuleCat.restrictScalars (cechRestMap R 𝒰 p σ).hom

/-- Each Čech factor `cechTermFunctor R 𝒰 p σ` is additive. -/
instance (p : ℕ) (σ : Fin (p + 1) → 𝒰.ι) : (cechTermFunctor R 𝒰 p σ).Additive := by
  unfold cechTermFunctor; infer_instance

/-- The degree-`p` term of the Čech complex functor:
`F ↦ ∏_{σ : Fin (p+1) → I} F(U_{σ 0 … σ p})`, as a functor
`PMod(O_X) ⥤ Mod_{O_X(U)}`. This is `Č^p(𝒰, -)`. -/
@[sga "4 V 2.4.3" "partial"]
noncomputable def cechObj (p : ℕ) :
    PresheafOfModules R ⥤ ModuleCat (R.obj (Opposite.op 𝒰.U)) :=
  ∏ᶜ (fun σ : Fin (p + 1) → 𝒰.ι => cechTermFunctor R 𝒰 p σ)

/-- The degree-`p` Čech term `cechObj R 𝒰 p` is additive. -/
instance (p : ℕ) : (cechObj R 𝒰 p).Additive := by
  unfold cechObj; exact additive_piObj _

/-- Restriction of scalars preserves finite limits. -/
instance restrictScalars_preservesFiniteLimits (p : ℕ) (σ : Fin (p + 1) → 𝒰.ι) :
    PreservesFiniteLimits (ModuleCat.restrictScalars (cechRestMap R 𝒰 p σ).hom) := by
  apply Functor.preservesFiniteLimits_of_preservesKernels

/-- Each single Čech factor (evaluation ⋙ restrictScalars) preserves finite
limits. -/
instance cechTermFunctor_preservesFiniteLimits (p : ℕ) (σ : Fin (p + 1) → 𝒰.ι) :
    PreservesFiniteLimits (cechTermFunctor R 𝒰 p σ) := by
  unfold cechTermFunctor; infer_instance

/-- Restriction of scalars preserves finite colimits. -/
instance cechRestMap_restrictScalars_preservesFiniteColimits (p : ℕ) (σ : Fin (p + 1) → 𝒰.ι) :
    PreservesFiniteColimits (ModuleCat.restrictScalars (cechRestMap R 𝒰 p σ).hom) := by
  apply Functor.preservesFiniteColimits_of_preservesCokernels

/-- Each single Čech factor (evaluation ⋙ restrictScalars) preserves finite
colimits. -/
instance cechTermFunctor_preservesFiniteColimits (p : ℕ) (σ : Fin (p + 1) → 𝒰.ι) :
    PreservesFiniteColimits (cechTermFunctor R 𝒰 p σ) := by
  unfold cechTermFunctor; infer_instance

/-- Each Čech factor `F ↦ F(U_{σ 0 … σ p})` (an evaluation functor followed by restriction of
scalars) sends short exact sequences to short exact sequences. -/
theorem cechTermFunctor_exact (p : ℕ) (σ : Fin (p + 1) → 𝒰.ι)
    (S : ShortComplex (PresheafOfModules R)) (hS : S.ShortExact) :
    (S.map (cechTermFunctor R 𝒰 p σ)).ShortExact :=
  hS.map_of_exact _

/-- **Stacks tag 01EJ, Lemma 20.10.1 (degreewise exactness of the Čech functor).**

The Čech functor is exact: for every short exact sequence of presheaves of
`O_X`-modules and every cohomological degree `p`, the induced sequence of
degree-`p` Čech cochain modules is short exact. Since a short exact sequence of
complexes is precisely one that is short exact in every degree, this is exactly
the statement that the Čech functor `Č^•(𝒰, -) : PMod(O_X) ⥤ Comp⁺(Mod_{O_X(U)})`
is exact. -/
theorem cech_functor_exact (p : ℕ) (S : ShortComplex (PresheafOfModules R))
    (hS : S.ShortExact) : (S.map (cechObj R 𝒰 p)).ShortExact := by
  have : PreservesFiniteLimits (cechObj R 𝒰 p) := by unfold cechObj; infer_instance
  have : PreservesFiniteColimits (cechObj R 𝒰 p) := by unfold cechObj; infer_instance
  exact hS.map_of_exact _
