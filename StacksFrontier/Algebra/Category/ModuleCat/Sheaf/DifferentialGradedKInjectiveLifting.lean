module

public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import StacksCore.Algebra.Homology.QuasiIso
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedCategoryLocalization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedHomotopyCategoryTriangulated
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedInjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedKInjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedKInjectiveExtension
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedInjectiveDetection

/-!
# Lifting properties of K-injective differential graded modules

Let `X` be a ringed site and let `A` be a sheaf of differential graded algebras on it, and let
`I` be a right differential graded `A`-module that is K-injective and graded injective.

Two lifting properties of such an `I` are proved. The first: for a quasi-isomorphism
`b : M ⟶ M'` of right differential graded `A`-modules and a morphism `a : M ⟶ I` there is a
morphism `M' ⟶ I` whose composite with `b` is homotopic to `a`. The second: being K-injective
and graded injective is itself detected by a lifting property against a *set* of monomorphisms
of acyclic right differential graded modules, which is what makes the construction of
K-injective resolutions possible.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.translate` is the translation of a right differential
  graded module by an integer, obtained from the differential graded shift functors of axiom
  (B).

## Main results

* `SheafOfModules.DifferentialGradedModule.quotient_obj_translate`: the translation of a module
  represents the translation of its homotopy class.
* `SheafOfModules.DifferentialGradedModule.acyclic_translate`: a translation of an acyclic
  module is acyclic.
* `SheafOfModules.DifferentialGradedModule.isKInjective_translate` and
  `SheafOfModules.DifferentialGradedModule.isKInjective_shift`: translations of a K-injective
  module are K-injective.
* `SheafOfModules.DifferentialGradedModule.homotopic_comp_cone_inclusion` and
  `SheafOfModules.DifferentialGradedModule.homotopic_cone_identity_inclusion`: the composite of
  a morphism with the canonical inclusion of its target into its cone is homotopic to zero, so
  in particular the inclusion of a module into the cone of its identity is.
* `SheafOfModules.DifferentialGradedModule.mono_cone_inclusion`: that inclusion is a
  monomorphism.
* `SheafOfModules.DifferentialGradedModule.exists_homotopic_lift_of_quasiIso` is **Tag 0FSX**:
  the lifting property across a quasi-isomorphism, up to homotopy.
  The argument does not use graded injectivity, and
  `SheafOfModules.DifferentialGradedModule.IsKInjective.exists_homotopic_lift_of_quasiIso` is
  the same lifting property for a K-injective module which need not be graded injective.
* **Tag 0FSY** is `exists_acyclic_monomorphisms_isKInjective_gradedInjective_iff` of the same
  namespace: a set of monomorphisms of acyclic right differential graded modules whose lifting
  property is equivalent to being K-injective and graded injective.

## Implementation notes

**The lifting property across a quasi-isomorphism.** The argument is the cone argument. The
cone `C` of `b` is acyclic because `b` is a quasi-isomorphism, so the morphism `C ⟶ I[1]`
obtained from the canonical projection `C ⟶ M[1]` followed by the translate of `a` is homotopic
to zero, `I[1]` being K-injective along with `I`. A null homotopy of that morphism is a degree
`-1` action-linear graded map `h : C ⟶ I`; its restriction along the canonical inclusion
`M' ⟶ C` is a morphism of differential graded modules `c : M' ⟶ I`, and its restriction along
the degreewise inclusion of `M` in the first summand of `C` is a homotopy from `b ≫ c` to `a`.
This is where the two degreewise summands of the cone are used: the equation satisfied by a
null homotopy of `C ⟶ I[1]` reads on the second summand as the statement that `c` is a
morphism of complexes and on the first summand as the homotopy identity.

Graded injectivity of `I` is not used for it: the source's proof deduces the lifting property
from the long exact sequence of a short exact sequence of modules which is not admissible, which
is where graded injectivity enters, whereas the cone of `b` gives the same conclusion from
K-injectivity alone. The hypothesis is kept, since it is the hypothesis of the source.

The translation functors are those of the homotopy category, lifted from the differential
graded shifts of axiom (B); `translate A n M` is a module representing the `n`-fold translate
of the homotopy class of `M`, and `translate A 1 M` is the shift of the cone construction.

**The detecting family.** It is the disjoint union of two families. The first is a family
detecting graded injectivity, Tag 0FSS, which is where the extension property for the
non-K-injective half comes from. The second consists of the inclusions `N ⟶ cone (𝟙 N)` for
`N` a nonzero acyclic right differential graded module; each is a monomorphism between acyclic
modules and each is homotopic to zero, so a morphism `N ⟶ I` which factors through it is
homotopic to zero. Since every nonzero acyclic module occurs as the source of a member of that
second family, the vanishing of the homotopy classes of morphisms from an acyclic module into
`I` is immediate, and the transfinite recursion of the source — which builds a general acyclic
module out of the members of a *small* detecting family of acyclic modules — is not needed. The
family of acyclic modules used here is the one that
`SheafOfModules.DifferentialGradedModule.exists_small_acyclic_family` exhibits: all nonzero
acyclic modules, as a type one universe above the modules. That is not the set-indexed family of
Tag 0FST — which is
`SheafOfModules.DifferentialGradedModule.exists_set_indexed_acyclic_family` — and it does not
need to be, because the argument here replaces the source's transfinite recursion and so asks
nothing about the size of the family; the index type of the family produced here is
correspondingly one universe above the module universe. The
converse implication is the extension property of Tag 0FSW, which applies to every member of
the family because every member is a monomorphism with acyclic source.

The zero acyclic module is excluded from the second family because the inclusion of a zero
object into the cone of its identity detects nothing; it needs no member, since all morphisms
out of a zero module agree.

**The base and the universes.** The base is the structure sheaf of a ringed site, as for the
triangulated structure of the homotopy category, and the universes of the site, the algebra
pieces and the module pieces are independent. The two sheafification hypotheses of the first
half are those that make the category of sheaves of modules abelian, which is what gives the
cone of a quasi-isomorphism its acyclicity. The detecting family is produced at the module
universe `max u v w` rather than at a free `w`, as in Tag 0FSS: the family detecting graded
injectivity exists only there, since the Grothendieck abelian structure of the category of
graded modules is available only at a module universe containing the universes of the site.

## References

* [Stacks Project, Tag 0FSX](https://stacks.math.columbia.edu/tag/0FSX)
* [Stacks Project, Tag 0FSY](https://stacks.math.columbia.edu/tag/0FSY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace SheafOfModules.DifferentialGradedModule

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}

/-! ### Translations of differential graded modules -/

/-- The translation of a right differential graded module by an integer, read off the
differential graded shift functors of axiom (B). -/
def translate (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (n : ℤ)
    (M : DifferentialGradedModule.{u, v, w} A) : DifferentialGradedModule.{u, v, w} A :=
  asModule A (((shiftAxiomB A).axiomB.shiftFunctor n).obj (asObject A M))

/-- The translation of a module represents the translation of its homotopy class. -/
theorem quotient_obj_translate (n : ℤ) (M : DifferentialGradedModule.{u, v, w} A) :
    (HomotopyCategory.quotient A).obj (translate A n M) =
      (shiftFunctor (HomotopyCategory.{u, v, w} A) n).obj
        ((HomotopyCategory.quotient A).obj M) := by
  change _ = (HomotopyCategory.quotient A).obj (asModule A
    ((shiftFunctor (dgCategoryData.{u, v, w} A).category.K n).obj (asObject A M)))
  rw [(dgConeSituation A).shift.kShift_functor, dgConeSituation_shift]
  rfl

/-- The complex of a translation is the translation of the complex. -/
theorem translate_complex (n : ℤ) (M : DifferentialGradedModule.{u, v, w} A) :
    (translate A n M).complex =
      (CochainComplex.shiftFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) n).obj M.complex :=
  (shiftAxiomB A).shifted_complex n M

/-- A translation of an acyclic right differential graded module is acyclic. -/
theorem acyclic_translate (n : ℤ) {M : DifferentialGradedModule.{u, v, w} A}
    (hM : M.complex.Acyclic) : (translate A n M).complex.Acyclic := by
  rw [translate_complex]
  intro i
  exact ShortComplex.exact_of_iso
    ((CochainComplex.shiftShortComplexFunctorIso
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) n i (n + i)
        rfl).app M.complex).symm (hM (n + i))

/-- A translation of a K-injective right differential graded module is K-injective. -/
theorem isKInjective_translate {I : DifferentialGradedModule.{u, v, w} A}
    (hI : IsKInjective I) (n : ℤ) : IsKInjective (translate A n I) := by
  intro N hN
  rw [quotient_obj_translate]
  have hsub : Subsingleton ((HomotopyCategory.quotient A).obj (translate A (-n) N) ⟶
      (HomotopyCategory.quotient A).obj I) := hI _ (acyclic_translate (-n) hN)
  rw [quotient_obj_translate] at hsub
  refine ⟨fun f g => ?_⟩
  apply (shiftEquiv (HomotopyCategory.{u, v, w} A) (-n)).functor.map_injective
  exact (cancel_mono ((shiftFunctorCompIsoId (HomotopyCategory.{u, v, w} A) n (-n)
    (by omega)).app ((HomotopyCategory.quotient A).obj I)).hom).1 (hsub.elim _ _)

/-- The shift of a K-injective right differential graded module is K-injective. -/
theorem isKInjective_shift {I : DifferentialGradedModule.{u, v, w} A}
    (hI : IsKInjective I) : IsKInjective (shift I) := by
  have h := isKInjective_translate hI 1
  rwa [show translate A 1 I = shift I from (shiftAxiomB A).shift_one I] at h

/-! ### Transport lemmas for the two degreewise summands of a cone -/

/-- Membership in the relation of the cochain complex shape, from the successor equation.

The proof is elaborated at the type of the relation rather than at the equation it unfolds to;
a proof of the equation is not type-correct in the position of a proof of the relation at the
transparency at which `rw` and `simp` build motives. -/
public lemma up_rel {i j : ℤ} (h : i + 1 = j) : (ComplexShape.up ℤ).Rel i j := by
  simpa using h

/-- Applications of heterogeneously equal bundled biadditive maps to heterogeneously equal
elements are heterogeneously equal. -/
public lemma gradedBilinear_apply_heq {ι κ : Type*}
    {B : ι → Type*} {D : κ → Type*} {S : Type*}
    [∀ i, AddZeroClass (B i)] [∀ j, AddCommMonoid (D j)] [AddZeroClass S]
    {i i' : ι} {j j' : κ} (hi : i = i') (hj : j = j')
    {f : B i →+ S →+ D j} {g : B i' →+ S →+ D j'}
    (hf : HEq f g) {x : B i} {y : B i'} (hx : HEq x y) (s : S) :
    HEq (f x s) (g y s) := by
  subst i'
  subst j'
  cases hf
  cases hx
  rfl

private lemma sheaf_biprod_ext
    {F G K : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (e : F ≅ G ⊞ K) (U : X.Cᵒᵖ) (x y : F.val.obj U)
    (h₁ : (e.hom ≫ biprod.fst).val.app U x = (e.hom ≫ biprod.fst).val.app U y)
    (h₂ : (e.hom ≫ biprod.snd).val.app U x = (e.hom ≫ biprod.snd).val.app U y) : x = y := by
  have ht : (e.hom ≫ biprod.fst) ≫ (biprod.inl ≫ e.inv) +
      (e.hom ≫ biprod.snd) ≫ (biprod.inr ≫ e.inv) = 𝟙 _ := by
    calc
      _ = e.hom ≫ (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) ≫ e.inv := by
        simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc]
      _ = _ := by simp
  have he (z : F.val.obj U) :
      (biprod.inl ≫ e.inv).val.app U ((e.hom ≫ biprod.fst).val.app U z) +
        (biprod.inr ≫ e.inv).val.app U ((e.hom ≫ biprod.snd).val.app U z) = z :=
    congrArg (fun t => t.val.app U z) ht
  have hx := he x
  rw [h₁, h₂] at hx
  exact hx.symm.trans (he y)

private lemma cone_point_heq
    {K L : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (b : K ⟶ L) {n m : ℤ} (e : n = m) (U : X.Cᵒᵖ)
    {x : ((CochainComplex.mappingCone b).X n).val.obj U}
    {y : ((CochainComplex.mappingCone b).X m).val.obj U}
    (h₁ : HEq
      (((HomologicalComplex.homotopyCofiber.XIsoBiprod b n (n + 1) (up_rel rfl)).hom ≫
        biprod.fst).val.app U x)
      (((HomologicalComplex.homotopyCofiber.XIsoBiprod b m (m + 1) (up_rel rfl)).hom ≫
        biprod.fst).val.app U y))
    (h₂ : HEq
      (((HomologicalComplex.homotopyCofiber.XIsoBiprod b n (n + 1) rfl).hom ≫
        biprod.snd).val.app U x)
      (((HomologicalComplex.homotopyCofiber.XIsoBiprod b m (m + 1) rfl).hom ≫
        biprod.snd).val.app U y)) : HEq x y := by
  subst m
  exact heq_of_eq (sheaf_biprod_ext
    (HomologicalComplex.homotopyCofiber.XIsoBiprod b n (n + 1) (up_rel rfl)) U x y
    (eq_of_heq h₁) (eq_of_heq h₂))

private lemma inl_comp_xiso_fst
    {K L : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (b : K ⟶ L) (j : ℤ) :
    HomologicalComplex.homotopyCofiber.inlX b (j + 1) j (up_rel rfl) ≫
        ((HomologicalComplex.homotopyCofiber.XIsoBiprod b j (j + 1) (up_rel rfl)).hom ≫
          biprod.fst) = 𝟙 _ := by
  rw [← Category.assoc, HomologicalComplex.homotopyCofiber.inlX_XIsoBiprod_hom, biprod.inl_fst]

private lemma inl_comp_xiso_snd
    {K L : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (b : K ⟶ L) (j : ℤ) :
    HomologicalComplex.homotopyCofiber.inlX b (j + 1) j (up_rel rfl) ≫
        ((HomologicalComplex.homotopyCofiber.XIsoBiprod b j (j + 1) (up_rel rfl)).hom ≫
          biprod.snd) = 0 := by
  rw [← Category.assoc, HomologicalComplex.homotopyCofiber.inlX_XIsoBiprod_hom, biprod.inl_snd]

private lemma inl_fst_apply_heq
    {K L : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (b : K ⟶ L) (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel j i) (U : X.Cᵒᵖ)
    (x : (K.X i).val.obj U) :
    HEq (((HomologicalComplex.homotopyCofiber.XIsoBiprod b j (j + 1) (up_rel rfl)).hom ≫
        biprod.fst).val.app U
      ((HomologicalComplex.homotopyCofiber.inlX b i j hij).val.app U x)) x := by
  obtain rfl : i = j + 1 := by simpa using hij.symm
  exact heq_of_eq (congrArg (fun f => f.val.app U x) (inl_comp_xiso_fst b j))

private lemma inl_snd_apply
    {K L : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (b : K ⟶ L) (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel j i) (U : X.Cᵒᵖ)
    (x : (K.X i).val.obj U) :
    ((HomologicalComplex.homotopyCofiber.XIsoBiprod b j (j + 1) (up_rel rfl)).hom ≫
        biprod.snd).val.app U
      ((HomologicalComplex.homotopyCofiber.inlX b i j hij).val.app U x) = 0 := by
  obtain rfl : i = j + 1 := by simpa using hij.symm
  exact congrArg (fun f => f.val.app U x) (inl_comp_xiso_snd b j)

/-! ### The canonical inclusion into a cone -/

/-- Transporting the target degree of a degreewise inclusion into a mapping cone. -/
private lemma inlX_comp_eqToHom
    {K L : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (b : K ⟶ L) (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel (i - 1) i)
    (hij' : (ComplexShape.up ℤ).Rel j i) (h : i - 1 = j) :
    HomologicalComplex.homotopyCofiber.inlX b i (i - 1) hij ≫
        eqToHom (congrArg (HomologicalComplex.homotopyCofiber b).X h) =
      HomologicalComplex.homotopyCofiber.inlX b i j hij' := by
  subst h
  simp

/-- The degreewise inclusion of a module into the first summand of a cone is compatible with
the actions, up to the degree transport, given the formulas for the action on the cone. -/
private lemma inlX_mul_heq {M M' : DifferentialGradedModule.{u, v, w} A} (b : M ⟶ M')
    {cm : ∀ n i : ℤ, BilinearMap ((HomologicalComplex.homotopyCofiber b.toHomologicalComplex).X n)
      (A.complex.X i) ((HomologicalComplex.homotopyCofiber b.toHomologicalComplex).X (n + i))}
    (hfst : ∀ (n i : ℤ) (U : X.Cᵒᵖ) x a, HEq
      (((HomologicalComplex.homotopyCofiber.XIsoBiprod b.toHomologicalComplex (n + i)
        (n + i + 1) (up_rel rfl)).hom ≫ biprod.fst).val.app U ((cm n i).app U x a))
      ((M.mul (n + 1) i).app U (((HomologicalComplex.homotopyCofiber.XIsoBiprod
        b.toHomologicalComplex n (n + 1) (up_rel rfl)).hom ≫ biprod.fst).val.app U x) a))
    (hsnd : ∀ (n i : ℤ) (U : X.Cᵒᵖ) x a,
      ((HomologicalComplex.homotopyCofiber.XIsoBiprod b.toHomologicalComplex (n + i)
        (n + i + 1) (up_rel rfl)).hom ≫ biprod.snd).val.app U ((cm n i).app U x a) =
      (M'.mul n i).app U (((HomologicalComplex.homotopyCofiber.XIsoBiprod
        b.toHomologicalComplex n (n + 1) (up_rel rfl)).hom ≫ biprod.snd).val.app U x) a)
    (n m : ℤ) (U : X.Cᵒᵖ) (x : (M.complex.X n).val.obj U) (a : (A.complex.X m).val.obj U) :
    HEq ((HomologicalComplex.homotopyCofiber.inlX b.toHomologicalComplex (n + m) (n + m - 1)
        (up_rel (by omega))).val.app U ((M.mul n m).app U x a))
      ((cm (n - 1) m).app U ((HomologicalComplex.homotopyCofiber.inlX b.toHomologicalComplex n
        (n - 1) (up_rel (by omega))).val.app U x) a) := by
  apply cone_point_heq b.toHomologicalComplex (by omega : n + m - 1 = (n - 1) + m) U
  · have h₁ := inl_fst_apply_heq b.toHomologicalComplex (n + m) (n + m - 1)
      (up_rel (by omega)) U ((M.mul n m).app U x a)
    have h₂ := hfst (n - 1) m U
      ((HomologicalComplex.homotopyCofiber.inlX b.toHomologicalComplex n (n - 1)
        (up_rel (by omega))).val.app U x) a
    have h₃ := heq_dependent_apply
      (fun i (y : (M.complex.X i).val.obj U) => (M.mul i m).app U y a)
      (by omega : n - 1 + 1 = n)
      (inl_fst_apply_heq b.toHomologicalComplex n (n - 1) (up_rel (by omega)) U x)
    exact h₁.trans (h₂.trans h₃).symm
  · have h₂ := hsnd (n - 1) m U
      ((HomologicalComplex.homotopyCofiber.inlX b.toHomologicalComplex n (n - 1)
        (up_rel (by omega))).val.app U x) a
    rw [inl_snd_apply b.toHomologicalComplex n (n - 1) (up_rel (by omega)) U x, map_zero,
      AddMonoidHom.zero_apply] at h₂
    exact (heq_of_eq (inl_snd_apply b.toHomologicalComplex (n + m) (n + m - 1)
      (up_rel (by omega)) U ((M.mul n m).app U x a))).trans
      ((congr_arg_heq (fun i => (0 : (M'.complex.X i).val.obj U))
        (by omega : n + m - 1 = (n - 1) + m)).trans (heq_of_eq h₂.symm))

/-- The composite of a morphism of right differential graded modules with the canonical
inclusion of its target into its cone is homotopic to zero, and that inclusion is a
monomorphism. -/
private theorem coneInclusion_facts {M M' : DifferentialGradedModule.{u, v, w} A} (b : M ⟶ M')
    (P : ConePackage b) : Homotopic (b ≫ P.inclusion) 0 ∧ Mono P.inclusion := by
  rcases P with ⟨⟨Cc, cm, ca, co, cd⟩, inc, proj, hC, e, he, hfst, hsnd, hinc, hproj⟩
  dsimp only at hC
  have hC' : Cc = HomologicalComplex.homotopyCofiber b.toHomologicalComplex := hC
  subst hC'
  have he' : e = fun n => HomologicalComplex.homotopyCofiber.XIsoBiprod
      b.toHomologicalComplex n (n + 1) (up_rel rfl) :=
    funext (fun n => eq_of_heq (he n))
  subst e
  have hinc' : inc.toHomologicalComplex =
      HomologicalComplex.homotopyCofiber.inr b.toHomologicalComplex := eq_of_heq hinc
  refine ⟨⟨{
      app n := HomologicalComplex.homotopyCofiber.inlX b.toHomologicalComplex n (n - 1)
          (up_rel (by omega))
      map_mul := ?_
      comm := ?_ }⟩, ?_⟩
  · intro n m U x c
    exact inlX_mul_heq b hfst hsnd n m U x c
  · intro n
    have hd := HomologicalComplex.homotopyCofiber.inlX_d b.toHomologicalComplex (n - 1) n (n + 1)
      (up_rel (by omega)) (up_rel rfl)
    rw [comp_f, zero_f, sub_zero, hinc']
    simp only [HomologicalComplex.homotopyCofiber.inr_f, Category.assoc,
      inlX_comp_eqToHom b.toHomologicalComplex (n + 1) n _ (up_rel rfl) (by omega),
      HomologicalComplex.homotopyCofiber_d]
    rw [hd]
    abel
  · refine mono_of_mono_f inc fun n => ?_
    rw [hinc']
    simp only [HomologicalComplex.homotopyCofiber.inr_f]
    have : IsSplitMono (HomologicalComplex.homotopyCofiber.inrX b.toHomologicalComplex n) :=
      IsSplitMono.mk' ⟨HomologicalComplex.homotopyCofiber.sndX b.toHomologicalComplex n,
        HomologicalComplex.homotopyCofiber.inrX_sndX b.toHomologicalComplex n⟩
    infer_instance

/-- The composite of a morphism with the canonical inclusion of its target into its cone is
homotopic to zero. -/
theorem homotopic_comp_cone_inclusion {M M' : DifferentialGradedModule.{u, v, w} A}
    (b : M ⟶ M') : Homotopic (b ≫ (conePackage b).inclusion) 0 :=
  (coneInclusion_facts b (conePackage b)).1

/-- The canonical inclusion of the target of a morphism into its cone is a monomorphism. -/
theorem mono_cone_inclusion {M M' : DifferentialGradedModule.{u, v, w} A} (b : M ⟶ M') :
    Mono (conePackage b).inclusion :=
  (coneInclusion_facts b (conePackage b)).2

/-- The canonical inclusion of a right differential graded module into the cone of its identity
is homotopic to zero. -/
theorem homotopic_cone_identity_inclusion (N : DifferentialGradedModule.{u, v, w} A) :
    Homotopic ((conePackage (𝟙 N)).inclusion) 0 := by
  simpa only [Category.id_comp] using homotopic_comp_cone_inclusion (𝟙 N)

/-! ### The lifting property from a null homotopy on the cone -/

/-- If every pair of morphisms from the cone of `b` into the shift of `I` is homotopic, then
every morphism `a : M ⟶ I` lifts across `b` up to homotopy. -/
private theorem exists_lift_of_nullhomotopic_cone
    {M M' I : DifferentialGradedModule.{u, v, w} A}
    (a : M ⟶ I) (b : M ⟶ M') (P : ConePackage b) (S : ShiftPackage I)
    (hzero : ∀ f g : P.cone ⟶ S.shifted, Homotopic f g) :
    ∃ c : M' ⟶ I, Homotopic (b ≫ c) a := by
  rcases P with ⟨⟨C, cm, ca, co, cd⟩, inc, proj, hC, e, he, hfst, hsnd, hinc, hproj⟩
  rcases S with ⟨⟨Jm, jm, ja, jo, jd⟩, hJ, hmul⟩
  dsimp only at hC hJ
  have hC' : C = HomologicalComplex.homotopyCofiber b.toHomologicalComplex := hC
  subst hC'
  subst Jm
  have he' : e = fun n => HomologicalComplex.homotopyCofiber.XIsoBiprod
      b.toHomologicalComplex n (n + 1) (up_rel rfl) :=
    funext (fun n => eq_of_heq (he n))
  subst e
  let N : DifferentialGradedModule.{u, v, w} A := ⟨_, cm, ca, co, cd⟩
  let T : DifferentialGradedModule.{u, v, w} A := ⟨_, jm, ja, jo, jd⟩
  let f : N ⟶ T := {
    toHomologicalComplex := (CochainComplex.HomComplex.Cocycle.homOf
      ((CochainComplex.mappingCone.fst b.toHomologicalComplex).rightShift 1 0 (zero_add 1))) ≫
      (CochainComplex.shiftFunctor _ (1 : ℤ)).map a.toHomologicalComplex
    map_mul := by
      intro n m U x z
      change (a.toHomologicalComplex.f (n + m + 1)).val.app U
        (((HomologicalComplex.homotopyCofiber.XIsoBiprod b.toHomologicalComplex
          (n + m) (n + m + 1) (up_rel rfl)).hom ≫ biprod.fst).val.app U
            ((cm n m).app U x z)) =
        (jm n m).app U ((a.toHomologicalComplex.f (n + 1)).val.app U
          (((HomologicalComplex.homotopyCofiber.XIsoBiprod b.toHomologicalComplex
            n (n + 1) (up_rel rfl)).hom ≫ biprod.fst).val.app U x)) z
      have h := heq_dependent_apply
        (fun i y => (a.toHomologicalComplex.f i).val.app U y)
        (by omega : n + m + 1 = n + 1 + m) (hfst n m U x z)
      have ht := gradedBilinear_apply_heq (B := fun i => (I.complex.X i).val.obj U)
        (D := fun i => (I.complex.X i).val.obj U) rfl
        (by omega : n + m + 1 = n + 1 + m) (hmul n m U) (HEq.rfl (a :=
          (a.toHomologicalComplex.f (n + 1)).val.app U
            (((HomologicalComplex.homotopyCofiber.XIsoBiprod b.toHomologicalComplex
              n (n + 1) (up_rel rfl)).hom ≫ biprod.fst).val.app U x))) z
      exact eq_of_heq (h.trans ((heq_of_eq (a.map_mul (n + 1) m U _ z)).trans ht.symm)) }
  let z : N ⟶ T := {
    toHomologicalComplex := 0
    map_mul := by
      intro n m U x a
      change 0 = (jm n m).app U 0 a
      rw [map_zero, AddMonoidHom.zero_apply] }
  obtain ⟨H⟩ := hzero f z
  let h (n : ℤ) : N.complex.X n ⟶ I.complex.X n :=
    H.app n ≫ eqToHom (congrArg I.complex.X (by omega : n - 1 + 1 = n))
  have hh (n : ℤ) :
      (HomologicalComplex.homotopyCofiber.fstX b.toHomologicalComplex n (n + 1)
            (up_rel rfl)) ≫ a.toHomologicalComplex.f (n + 1) =
        -h n ≫ I.complex.d n (n + 1) + N.complex.d n (n + 1) ≫ h (n + 1) := by
    have hc := H.comm n
    change _ - _ = H.app n ≫ ((-1 : ℤ) • I.complex.d (n - 1 + 1) (n + 1)) +
      (N.complex.d n (n + 1) ≫ H.app (n + 1)) ≫
        eqToHom (congrArg I.complex.X (by omega : (n + 1) - 1 + 1 = n + 1)) at hc
    change (HomologicalComplex.homotopyCofiber.fstX b.toHomologicalComplex n (n + 1)
      (up_rel rfl)) ≫ a.toHomologicalComplex.f (n + 1) - 0 = _ at hc
    simpa only [sub_zero, h, Category.assoc, Preadditive.neg_comp,
      Preadditive.comp_neg, HomologicalComplex.eqToHom_comp_d I.complex
        (show (ComplexShape.up ℤ).Rel (n - 1 + 1) (n + 1) by simp)
        (show (ComplexShape.up ℤ).Rel n (n + 1) by simp), neg_one_zsmul] using hc
  have hm (n m : ℤ) (U : X.Cᵒᵖ) (x : (N.complex.X n).val.obj U)
      (z : (A.complex.X m).val.obj U) :
      (h (n + m)).val.app U ((N.mul n m).app U x z) =
        (I.mul n m).app U ((h n).val.app U x) z := by
    have h₁ := sheaf_eqToHom_apply_heq
      (congrArg I.complex.X (by omega : n + m - 1 + 1 = n + m)) U
      ((H.app (n + m)).val.app U ((N.mul n m).app U x z))
    have h₂ := H.map_mul n m U x z
    have h₃ := gradedBilinear_apply_heq
      (B := fun i => (I.complex.X i).val.obj U)
      (D := fun i => (I.complex.X i).val.obj U) rfl
      (by omega : (n - 1) + m + 1 = (n - 1 + 1) + m)
      (hmul (n - 1) m U) (HEq.rfl (a := (H.app n).val.app U x)) z
    have h₄ := heq_dependent_apply
      (fun i (x : (I.complex.X i).val.obj U) => (I.mul i m).app U x z)
      (by omega : n - 1 + 1 = n)
      (sheaf_eqToHom_apply_heq (congrArg I.complex.X
        (by omega : n - 1 + 1 = n)) U ((H.app n).val.app U x)).symm
    exact eq_of_heq (h₁.trans (h₂.trans (h₃.trans h₄)))
  let l (n : ℤ) : M.complex.X n ⟶ N.complex.X (n - 1) :=
    HomologicalComplex.homotopyCofiber.inlX b.toHomologicalComplex n (n - 1)
      (up_rel (by omega))
  have hl (n m : ℤ) (U : X.Cᵒᵖ) (x : (M.complex.X n).val.obj U)
      (a : (A.complex.X m).val.obj U) :
      HEq ((l (n + m)).val.app U ((M.mul n m).app U x a))
        ((N.mul (n - 1) m).app U ((l n).val.app U x) a) :=
    inlX_mul_heq b hfst hsnd n m U x a
  have hinc' : inc.toHomologicalComplex =
      HomologicalComplex.homotopyCofiber.inr b.toHomologicalComplex := eq_of_heq hinc
  let c : M' ⟶ I := {
    toHomologicalComplex := {
      f n := HomologicalComplex.homotopyCofiber.inrX b.toHomologicalComplex n ≫ h n
      comm' n m hnm := by
        obtain rfl : m = n + 1 := by simp only [ComplexShape.up_Rel] at hnm; omega
        have hc := congrArg
          (fun k => HomologicalComplex.homotopyCofiber.inrX b.toHomologicalComplex n ≫ k)
          (hh n)
        dsimp only [N] at hc
        rw [Preadditive.comp_add] at hc
        simp only [Preadditive.comp_neg,
          HomologicalComplex.homotopyCofiber.inrX_fstX_assoc, zero_comp,
          HomologicalComplex.homotopyCofiber_d,
          HomologicalComplex.homotopyCofiber.inrX_d_assoc] at hc
        simp only [Category.assoc] at hc ⊢
        exact neg_add_eq_zero.mp hc.symm }
    map_mul := by
      intro n m U x z
      have hi := inc.map_mul n m U x z
      rw [hinc'] at hi
      simp only [HomologicalComplex.homotopyCofiber.inr_f] at hi
      exact (congrArg (fun y => (h (n + m)).val.app U y) hi).trans
        (hm n m U
          ((HomologicalComplex.homotopyCofiber.inrX b.toHomologicalComplex n).val.app U x) z) }
  have hh' (n p : ℤ) (hp : (ComplexShape.up ℤ).Rel n p) :
      HomologicalComplex.homotopyCofiber.fstX b.toHomologicalComplex n p hp ≫
          a.toHomologicalComplex.f p =
        -h n ≫ I.complex.d n p + N.complex.d n p ≫ h p := by
    obtain rfl : p = n + 1 := by simpa using hp.symm
    exact hh n
  have hl' (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel j i) (hji : i - 1 = j) :
      HomologicalComplex.homotopyCofiber.inlX b.toHomologicalComplex i j hij ≫ h j =
        (l i ≫ h (i - 1)) ≫ eqToHom (congrArg I.complex.X hji) := by
    subst hji
    simp only [eqToHom_refl, Category.comp_id, l]
  refine ⟨c, ⟨{ app := fun n => l n ≫ h (n - 1), map_mul := ?_, comm := ?_ }⟩⟩
  · intro n m U x a
    exact (heq_dependent_apply
      (fun i (y : (N.complex.X i).val.obj U) => (h i).val.app U y)
      (by omega : n + m - 1 = (n - 1) + m) (hl n m U x a)).trans
      (heq_of_eq (hm (n - 1) m U ((l n).val.app U x) a))
  · intro n
    have hc := congrArg (fun k => l n ≫ k) (hh' (n - 1) n (up_rel (by omega)))
    dsimp only [l, N, HomologicalComplex.homotopyCofiber_d] at hc
    simp only [Preadditive.comp_add, Preadditive.comp_neg, Category.assoc,
      HomologicalComplex.homotopyCofiber.inlX_fstX_assoc,
      HomologicalComplex.homotopyCofiber.inlX_d_assoc b.toHomologicalComplex
        (n - 1) n (n + 1) (up_rel (by omega)) (up_rel rfl),
      Preadditive.add_comp, Preadditive.neg_comp] at hc
    rw [hl' (n + 1) n (up_rel rfl) (by omega)] at hc
    change b.toHomologicalComplex.f n ≫
        (HomologicalComplex.homotopyCofiber.inrX b.toHomologicalComplex n ≫ h n) -
      a.toHomologicalComplex.f n = _
    simp only [Category.assoc] at hc ⊢
    rw [hc]
    dsimp only [l]
    abel

/-! ### Acyclicity of the cone of a quasi-isomorphism, and the lifting property -/

section Abelian

variable [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Let `I` be a K-injective right differential graded module. For a quasi-isomorphism
`b : M ⟶ M'` of right differential graded modules and a morphism `a : M ⟶ I` there is a morphism
`c : M' ⟶ I` with `b ≫ c` homotopic to `a`.

This is Tag 0FSX without its graded injectivity hypothesis, which the cone argument does not
use. -/
theorem IsKInjective.exists_homotopic_lift_of_quasiIso
    {M M' I : DifferentialGradedModule.{u, v, w} A} (hI : IsKInjective I) (a : M ⟶ I)
    (b : M ⟶ M') (hb : QuasiIso b.toHomologicalComplex) :
    ∃ c : M' ⟶ I, Homotopic (b ≫ c) a := by
  refine exists_lift_of_nullhomotopic_cone a b (conePackage b) (shiftPackage I) fun f g => ?_
  refine (HomotopyCategory.quotient_map_eq_iff f g).mp ?_
  exact (isKInjective_shift hI (cone b) ((acyclic_cone_iff_quasiIso _ b).2 hb)).elim _ _

/-- **Stacks Tag 0FSX.** Let `I` be a K-injective and graded injective right differential
graded module. For a quasi-isomorphism `b : M ⟶ M'` of right differential graded modules and a
morphism `a : M ⟶ I` there is a morphism `c : M' ⟶ I` making the triangle commute up to
homotopy, that is with `b ≫ c` homotopic to `a`. -/
@[stacks 0FSX]
theorem exists_homotopic_lift_of_quasiIso {M M' I : DifferentialGradedModule.{u, v, w} A}
    (hI : IsKInjective I) (_hI' : GradedInjective I) (a : M ⟶ I) (b : M ⟶ M')
    (hb : QuasiIso b.toHomologicalComplex) : ∃ c : M' ⟶ I, Homotopic (b ≫ c) a :=
  hI.exists_homotopic_lift_of_quasiIso a b hb

end Abelian

/-! ### A set of acyclic monomorphisms detecting K-injectivity and graded injectivity -/

section Detection

variable [HasWeakSheafify X.J (Type max u v w)]
  [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]

/-- **Stacks Tag 0FSY.** For a sheaf of differential graded algebras `A` on a ringed site there
is a set `Idx` and, for each `r : Idx`, a monomorphism `Ms r ⟶ Ms' r` of *acyclic* right
differential graded `A`-modules, such that a right differential graded `A`-module `I` is
K-injective (Tag 0FSU) and graded injective (Tag 0FSP) if and only if every morphism
`Ms r ⟶ I` extends along `Ms r ⟶ Ms' r` to a morphism `Ms' r ⟶ I`. -/
@[stacks 0FSY]
theorem exists_acyclic_monomorphisms_isKInjective_gradedInjective_iff
    (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    ∃ (Idx : Type (max u v w + 1))
      (Ms Ms' : Idx → DifferentialGradedModule.{u, v, max u v w} A)
      (i : ∀ r, Ms r ⟶ Ms' r),
      (∀ r, Mono (i r)) ∧ (∀ r, (Ms r).complex.Acyclic) ∧ (∀ r, (Ms' r).complex.Acyclic) ∧
        ∀ I : DifferentialGradedModule.{u, v, max u v w} A,
          (IsKInjective I ∧ GradedInjective I) ↔
            ∀ (r : Idx) (f : Ms r ⟶ I), ∃ g : Ms' r ⟶ I, i r ≫ g = f := by
  obtain ⟨T, Mt, Mt', jt, hjt, hMt, hMt', hT⟩ :
      ∃ (T : Type max u v w) (Mt Mt' : T → DifferentialGradedModule.{u, v, max u v w} A)
        (jt : ∀ s, Mt s ⟶ Mt' s),
        (∀ s, Mono (jt s)) ∧ (∀ s, (Mt s).complex.Acyclic) ∧ (∀ s, (Mt' s).complex.Acyclic) ∧
          ∀ I : DifferentialGradedModule.{u, v, max u v w} A,
            GradedInjective I ↔ ∀ (s : T) (f : Mt s ⟶ I), ∃ g : Mt' s ⟶ I, jt s ≫ g = f :=
    exists_acyclic_monomorphisms_gradedInjective_iff A
  refine ⟨ULift.{max u v w + 1} T ⊕
      {N : DifferentialGradedModule.{u, v, max u v w} A //
        N.complex.Acyclic ∧ ¬ IsZero N.complex},
    Sum.elim (fun s => Mt s.down) (fun s => s.1),
    Sum.elim (fun s => Mt' s.down) (fun s => cone (𝟙 s.1)),
    fun r => match r with
      | Sum.inl s => jt s.down
      | Sum.inr s => (conePackage (𝟙 s.1)).inclusion,
    ?_, ?_, ?_, ?_⟩
  · rintro (s | s)
    exacts [hjt s.down, mono_cone_inclusion (𝟙 s.1)]
  · rintro (s | s)
    exacts [hMt s.down, s.2.1]
  · rintro (s | s)
    exacts [hMt' s.down, (acyclic_cone_iff_quasiIso _ (𝟙 s.1)).2
      (show QuasiIso (𝟙 (s.1).complex) from inferInstance)]
  · intro I
    constructor
    · rintro ⟨hK, hG⟩ (s | s) f
      · have := hjt s.down
        exact exists_extension_of_acyclic_of_mono hK hG (jt s.down) (hMt s.down) f
      · have := mono_cone_inclusion (𝟙 s.1)
        exact exists_extension_of_acyclic_of_mono hK hG (conePackage (𝟙 s.1)).inclusion s.2.1 f
    · intro hall
      refine ⟨?_, (hT I).mpr fun s f => hall (Sum.inl ⟨s⟩) f⟩
      intro N hN
      have key : ∀ f : N ⟶ I, (HomotopyCategory.quotient A).map f =
          (HomotopyCategory.quotient A).map (0 : N ⟶ I) := by
        intro f
        by_cases hz : IsZero N.complex
        · refine congrArg _ (DifferentialGradedModule.Hom.ext fun n => ?_)
          rw [zero_f]
          exact ((HomologicalComplex.eval _ _ n).map_isZero hz).eq_of_src _ _
        · obtain ⟨g, hg⟩ : ∃ g : cone (𝟙 N) ⟶ I, (conePackage (𝟙 N)).inclusion ≫ g = f :=
            hall (Sum.inr ⟨N, hN, hz⟩) f
          rw [← hg, Functor.map_comp, (HomotopyCategory.quotient_map_eq_iff _ _).mpr
            (homotopic_cone_identity_inclusion N), ← Functor.map_comp, zero_comp]
      refine ⟨fun p q => ?_⟩
      obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient A).map_surjective p
      obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient A).map_surjective q
      rw [key f, key g]

end Detection

end SheafOfModules.DifferentialGradedModule
