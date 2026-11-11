module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Skeleton
import StacksCore.Tactic.StacksAttribute
import StacksFrontier.CategoryTheory.Limits.FunctorCategory.ShortExactColimit

/-!
# Simplicial objects in abelian categories

Let `A` be an abelian category and `J` any category. The functor category `J ⥤ A` is again
abelian, with kernels and cokernels computed objectwise, so all the exactness notions in `J ⥤ A`
are detected by the evaluation functors `(evaluation J A).obj j : (J ⥤ A) ⥤ A`: a morphism is a
monomorphism (resp. an epimorphism) if and only if each of its components is, and a short complex
`S : ShortComplex (J ⥤ A)` is exact if and only if each of the short complexes
`S.X₁.obj j ⟶ S.X₂.obj j ⟶ S.X₃.obj j` is exact. Taking `J := SimplexCategoryᵒᵖ` this is the
statement for simplicial objects of `A`, and taking `J := SimplexCategory` the statement for
cosimplicial objects of `A`, since `SimplicialObject A` and `CosimplicialObject A` are these
functor categories.

Let now `C` be a category with zero morphisms, let `k : ℕ` and let `U` be a `k`-truncated
simplicial object of `C` whose terms vanish below the top degree, `U_i = 0` for `i < k`; write
`A = U_k` for its top term. No further hypothesis is needed to pin `U` down, because a
non-identity morphism `φ : ⦋k⦌ ⟶ ⦋k⦌` of `Δ` is not bijective, hence factors as an epimorphism
onto some `⦋j⦌` with `j < k` followed by a monomorphism, so `U(φ)` factors through `U_j = 0` and
is zero; the requirement that all `U(φ)` vanish except `U(id_{⦋k⦌})` is therefore automatic. For
any `k`-truncated simplicial object `V` of `C`, a morphism `U ⟶ V` is determined by its top
component `A ⟶ V_k`, and the top components so obtained are exactly the `f : A ⟶ V_k` killed by
every non-surjective simplicial operator into `⦋k⦌`; dually, a morphism `V ⟶ U` is determined by
its top component `V_k ⟶ A`, and those obtained are exactly the `f : V_k ⟶ A` killed by every
non-injective simplicial operator out of `⦋k⦌`. Since a non-surjective `φ : ⦋m⦌ ⟶ ⦋k⦌` factors
through a face map `δ_i : ⦋k - 1⦌ ⟶ ⦋k⦌` and a non-injective `ψ : ⦋k⦌ ⟶ ⦋m⦌` factors through a
degeneracy map `σ_i : ⦋k⦌ ⟶ ⦋k - 1⦌`, these two conditions are the classical
`d^k_i ∘ f = 0` for `i = 0, …, k` and `f ∘ s^{k-1}_i = 0` for `i = 0, …, k - 1`. Together the two
descriptions say `Mor(U, V) = {f : A → V_k | d^k_i ∘ f = 0}` and
`Mor(V, U) = {f : V_k → A | f ∘ s^{k-1}_i = 0}`.

Finally, let `V` be a simplicial object of an abelian category `A`. For every `n` the
`n`-skeleton of `V` is `i_{n!} sk_n V`, the left Kan extension along `Δ_{≤ n} ⊆ Δ` of the
`n`-truncation of `V`, and it comes with a canonical morphism `i_{n!} sk_n V ⟶ V`, the counit of
the adjunction `i_{n!} ⊣ sk_n`, which is an isomorphism in degrees `≤ n`. These skeleta form an
`ℕ`-indexed sequence whose transition morphisms are monomorphisms, and `V`, equipped with the
canonical morphisms, is its colimit: `V = colim_n i_{n!} sk_n V`.

## Main results

* `CategoryTheory.Abelian.functorCategoryAbelian` (Mathlib): the functor category `J ⥤ A`, `A`
  abelian, is abelian; this is the abelian structure on `SimplicialObject A` and
  `CosimplicialObject A`.
* `CategoryTheory.SimplicialObject.mono_iff_mono_app`,
  `CategoryTheory.CosimplicialObject.mono_iff_mono_app`: a morphism of (co)simplicial objects of
  an abelian category is a monomorphism if and only if it is one in each degree.
* `CategoryTheory.SimplicialObject.epi_iff_epi_app`,
  `CategoryTheory.CosimplicialObject.epi_iff_epi_app`: a morphism of (co)simplicial objects of
  an abelian category is an epimorphism if and only if it is one in each degree.
* `CategoryTheory.ShortComplex.exact_iff_exact_map_evaluation`: a short complex of functors
  `J ⥤ A`, `A` abelian, is exact if and only if it is exact after evaluation at every object of
  `J`; equivalently, exactness of a sequence of (co)simplicial objects of `A` is exactness in
  each degree.
* `CategoryTheory.SimplicialObject.Truncated.app_top_injective_and_exists_iff`: the two hom-sets
  of a top-degree-concentrated `k`-truncated simplicial object, computed by the top component.
* `CategoryTheory.SimplicialObject.exists_mono_isColimit_sk`: the skeleta of a simplicial
  object of an abelian category form a sequence with monomorphic transition maps whose colimit,
  with the canonical morphisms as the structure maps of the colimit cocone, is the object itself.

## References

* [Stacks, Tag 018Z](https://stacks.math.columbia.edu/tag/018Z)
* [Stacks, Tag 0190](https://stacks.math.columbia.edu/tag/0190)
* [Stacks, Tag 0193](https://stacks.math.columbia.edu/tag/0193)
-/

universe w' w v u v' u'

namespace CategoryTheory

namespace ShortComplex

variable {J : Type u} [Category.{v} J] {A : Type u'} [Category.{v'} A] [Abelian A]

/-- **Stacks 018Z (4)**.
A short complex `S` of functors `J ⥤ A`, with `A` an abelian category, is exact if and only if
evaluating it at each object `j` of `J` gives an exact short complex of `A`. For
`J = SimplexCategoryᵒᵖ` (resp. `J = SimplexCategory`) this says that a sequence of (co)simplicial
objects of `A` is exact if and only if it is exact in each degree. -/
@[stacks 018Z "(4): a sequence of (co)simplicial objects of an abelian category is exact if and
  only if it is exact in each degree, stated for functors `J ⥤ A` from any category `J`"]
public theorem exact_iff_exact_map_evaluation (S : ShortComplex (J ⥤ A)) :
    S.Exact ↔ ∀ j : J, (S.map ((evaluation J A).obj j)).Exact :=
  jointlyReflectIsomorphisms_evaluation.exact_iff S

end ShortComplex

variable {A : Type u'} [Category.{v'} A] [Abelian A]

add_to_stacks 018Z "(1): the categories `SimplicialObject A` and `CosimplicialObject A` of
  simplicial and cosimplicial objects of an abelian category `A` are abelian; they are the functor
  categories `SimplexCategoryᵒᵖ ⥤ A` and `SimplexCategory ⥤ A`, which this instance makes
  abelian." CategoryTheory.Abelian.functorCategoryAbelian

namespace SimplicialObject

/-- **Stacks 018Z (2)**, simplicial objects.
A morphism `f : X ⟶ Y` of simplicial objects of an abelian category is a monomorphism if and only
if each component `f_n : X_n ⟶ Y_n` is a monomorphism. -/
@[stacks 018Z "(2) for simplicial objects: a morphism is a monomorphism if and only if it is a
  monomorphism in each degree"]
public theorem mono_iff_mono_app {X Y : SimplicialObject A} (f : X ⟶ Y) :
    Mono f ↔ ∀ n : ℕ, Mono (f.app (Opposite.op (SimplexCategory.mk n))) :=
  (NatTrans.mono_iff_mono_app f).trans ⟨fun h _ => h _, fun h k => h k.unop.len⟩

/-- **Stacks 018Z (3)**, simplicial objects.
A morphism `f : X ⟶ Y` of simplicial objects of an abelian category is an epimorphism if and only
if each component `f_n : X_n ⟶ Y_n` is an epimorphism. -/
@[stacks 018Z "(3) for simplicial objects: a morphism is an epimorphism if and only if it is an
  epimorphism in each degree"]
public theorem epi_iff_epi_app {X Y : SimplicialObject A} (f : X ⟶ Y) :
    Epi f ↔ ∀ n : ℕ, Epi (f.app (Opposite.op (SimplexCategory.mk n))) :=
  (NatTrans.epi_iff_epi_app f).trans ⟨fun h _ => h _, fun h k => h k.unop.len⟩

end SimplicialObject

namespace CosimplicialObject

/-- **Stacks 018Z (2)**, cosimplicial objects.
A morphism `f : X ⟶ Y` of cosimplicial objects of an abelian category is a monomorphism if and
only if each component `f_n : X_n ⟶ Y_n` is a monomorphism. -/
@[stacks 018Z "(2) for cosimplicial objects: a morphism is a monomorphism if and only if it is a
  monomorphism in each degree"]
public theorem mono_iff_mono_app {X Y : CosimplicialObject A} (f : X ⟶ Y) :
    Mono f ↔ ∀ n : ℕ, Mono (f.app (SimplexCategory.mk n)) :=
  (NatTrans.mono_iff_mono_app f).trans ⟨fun h _ => h _, fun h k => h k.len⟩

/-- **Stacks 018Z (3)**, cosimplicial objects.
A morphism `f : X ⟶ Y` of cosimplicial objects of an abelian category is an epimorphism if and
only if each component `f_n : X_n ⟶ Y_n` is an epimorphism. -/
@[stacks 018Z "(3) for cosimplicial objects: a morphism is an epimorphism if and only if it is an
  epimorphism in each degree"]
public theorem epi_iff_epi_app {X Y : CosimplicialObject A} (f : X ⟶ Y) :
    Epi f ↔ ∀ n : ℕ, Epi (f.app (SimplexCategory.mk n)) :=
  (NatTrans.epi_iff_epi_app f).trans ⟨fun h _ => h _, fun h k => h k.len⟩

end CosimplicialObject

end CategoryTheory

namespace CategoryTheory.SimplicialObject.Truncated

open Opposite Simplicial Limits
open scoped SimplexCategory.Truncated CategoryTheory.SimplicialObject.Truncated

section TruncatedSimplexCategory

variable {k : ℕ}

/-- An object of the `k`-truncated simplex category of length `k` is `⦋k⦌`. -/
private lemma eq_top_of_len {X : SimplexCategory.Truncated k} (h : X.obj.len = k) : X = ⦋k⦌ₖ := by
  obtain ⟨⟨n⟩, hn⟩ := X
  have h' : n = k := h
  subst h'
  rfl

/-- An object of the opposite of the `k`-truncated simplex category of length `k` is `op ⦋k⦌`. -/
private lemma eq_op_top_of_len {X : (SimplexCategory.Truncated k)ᵒᵖ} (h : X.unop.obj.len = k) :
    X = op ⦋k⦌ₖ := congrArg op (eq_top_of_len h)

/-- An object of the opposite of the `k`-truncated simplex category is either of length `< k` or
`op ⦋k⦌`. -/
private lemma len_lt_or_eq_op_top (X : (SimplexCategory.Truncated k)ᵒᵖ) :
    X.unop.obj.len < k ∨ X = op ⦋k⦌ₖ :=
  (lt_or_eq_of_le X.unop.property).imp id eq_op_top_of_len

/-- A morphism into `⦋k⦌` from an object of length `< k` is not surjective. -/
private lemma not_surjective_of_len_lt {X : SimplexCategory.Truncated k} (hX : X.obj.len < k)
    (φ : X ⟶ ⦋k⦌ₖ) : ¬ Function.Surjective φ.hom.toOrderHom := fun h => by
  have : k ≤ X.obj.len := by simpa using Fintype.card_le_of_surjective _ h
  omega

/-- A morphism out of `⦋k⦌` to an object of length `< k` is not injective. -/
private lemma not_injective_of_len_lt {X : SimplexCategory.Truncated k} (hX : X.obj.len < k)
    (ψ : ⦋k⦌ₖ ⟶ X) : ¬ Function.Injective ψ.hom.toOrderHom := fun h => by
  have : k ≤ X.obj.len := by simpa using Fintype.card_le_of_injective _ h
  omega

/-- A bijective endomorphism of an object of the `k`-truncated simplex category is the
identity. -/
private lemma eq_id_of_bijective {X : SimplexCategory.Truncated k} (φ : X ⟶ X)
    (hφ : Function.Bijective φ.hom.toOrderHom) : φ = 𝟙 X :=
  have := SimplexCategory.isIso_of_bijective hφ
  ObjectProperty.hom_ext _ (SimplexCategory.eq_id_of_isIso _)

end TruncatedSimplexCategory

section HomExt

variable {C : Type u} [Category.{v} C] {k : ℕ} {U V : SimplicialObject.Truncated C k}

/-- Two morphisms of `k`-truncated simplicial objects with the same top component agree, as soon as
the hom-sets in the degrees `< k` are trivial. -/
private lemma hom_ext_of_app_top
    (h : ∀ X : (SimplexCategory.Truncated k)ᵒᵖ, X.unop.obj.len < k →
      ∀ a b : U.obj X ⟶ V.obj X, a = b)
    {g g' : U ⟶ V} (hgg' : g.app (op ⦋k⦌ₖ) = g'.app (op ⦋k⦌ₖ)) : g = g' := by
  ext X
  rcases len_lt_or_eq_op_top X with hX | rfl
  · exact h X hX _ _
  · exact hgg'

end HomExt

section TopDegree

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {k : ℕ}
  {U V : SimplicialObject.Truncated C k}

/-- An operator that factors through an object of length `< k` acts by zero on a `k`-truncated
simplicial object concentrated in degree `k`. -/
private lemma map_op_eq_zero_of_factorization
    (hU : ∀ (m : ℕ) (hm : m < k), IsZero (U _⦋m,hm.le⦌ₖ))
    {X Y M : SimplexCategory.Truncated k} (hM : M.obj.len < k)
    {φ : X ⟶ Y} {a : X ⟶ M} {b : M ⟶ Y} (h : φ = a ≫ b) : U.map φ.op = 0 := by
  rw [h, op_comp, U.map_comp, (hU M.obj.len hM).eq_zero_of_tgt (U.map b.op), zero_comp]

/-- A `k`-truncated simplicial object concentrated in degree `k` kills every operator that is not
bijective: such an operator factors through an object of length `< k`, namely through its own
source or target if one of the two is not `⦋k⦌`, and through a face `δ i : ⦋k - 1⦌ ⟶ ⦋k⦌`
otherwise. -/
private lemma map_op_eq_zero_of_not_bijective
    (hU : ∀ (m : ℕ) (hm : m < k), IsZero (U _⦋m,hm.le⦌ₖ))
    {X Y : SimplexCategory.Truncated k} (φ : X ⟶ Y)
    (hφ : ¬ Function.Bijective φ.hom.toOrderHom) : U.map φ.op = 0 := by
  rcases lt_or_eq_of_le X.property with hX | hX
  · exact map_op_eq_zero_of_factorization hU hX (a := 𝟙 X) (b := φ) (by simp)
  rcases lt_or_eq_of_le Y.property with hY | hY
  · exact map_op_eq_zero_of_factorization hU hY (a := φ) (b := 𝟙 Y) (by simp)
  obtain rfl := eq_top_of_len hX
  obtain rfl := eq_top_of_len hY
  obtain _ | j := k
  · exact absurd (by rw [Subsingleton.elim φ.hom (𝟙 _)]; simp) hφ
  obtain ⟨i, θ, hθ⟩ := SimplexCategory.eq_comp_δ_of_not_surjective (n := j) φ.hom
    (fun h => hφ (Finite.surjective_iff_bijective.mp h))
  exact map_op_eq_zero_of_factorization hU (M := ⟨SimplexCategory.mk j, by simp⟩) (by simp)
    (a := ObjectProperty.homMk θ) (b := ObjectProperty.homMk (SimplexCategory.δ i))
    (ObjectProperty.hom_ext _ hθ)

/-- The components of the extension of a morphism `f` between the degree `k` terms of two
`k`-truncated simplicial objects: `f` in degree `k`, and zero in the degrees `< k`. -/
private def appTop (f : U _⦋k⦌ₖ ⟶ V _⦋k⦌ₖ) (X : (SimplexCategory.Truncated k)ᵒᵖ) :
    U.obj X ⟶ V.obj X :=
  if h : X.unop.obj.len = k then
    eqToHom (congrArg U.obj (eq_op_top_of_len h)) ≫ f ≫
      eqToHom (congrArg V.obj (eq_op_top_of_len h).symm)
  else 0

private lemma appTop_top (f : U _⦋k⦌ₖ ⟶ V _⦋k⦌ₖ) : appTop f (op ⦋k⦌ₖ) = f := by
  rw [appTop, dite_eq_left rfl]
  simp

private lemma appTop_eq_zero (f : U _⦋k⦌ₖ ⟶ V _⦋k⦌ₖ) {X : (SimplexCategory.Truncated k)ᵒᵖ}
    (hX : X.unop.obj.len < k) : appTop f X = 0 :=
  dite_eq_right (by omega)

/-- The extension of `f : U_k ⟶ V_k` by zero is a morphism `U ⟶ V` as soon as `f` is killed on the
right by every non-surjective operator into `⦋k⦌` and on the left by every non-injective operator
out of `⦋k⦌`. Those are exactly its naturality squares at an operator between `⦋k⦌` and a lower
degree; at an operator between two lower degrees the square reads `0 = 0`, and at an endomorphism
of `⦋k⦌` the operator is either the identity or non-bijective, in which case both conditions
apply. -/
private def homOfAppTop (f : U _⦋k⦌ₖ ⟶ V _⦋k⦌ₖ)
    (hs : ∀ (m : SimplexCategory.Truncated k) (φ : m ⟶ ⦋k⦌ₖ),
      ¬ Function.Surjective φ.hom.toOrderHom → f ≫ V.map φ.op = 0)
    (hi : ∀ (m : SimplexCategory.Truncated k) (ψ : ⦋k⦌ₖ ⟶ m),
      ¬ Function.Injective ψ.hom.toOrderHom → U.map ψ.op ≫ f = 0) : U ⟶ V where
  app := appTop f
  naturality {X Y} ψ := by
    obtain ⟨φ, rfl⟩ : ∃ φ : Y.unop ⟶ X.unop, ψ = φ.op := ⟨ψ.unop, rfl⟩
    rcases len_lt_or_eq_op_top X with hX | rfl
    · rcases len_lt_or_eq_op_top Y with hY | rfl
      · simp [appTop_eq_zero f hX, appTop_eq_zero f hY]
      · rw [appTop_eq_zero f hX, appTop_top, zero_comp, hi _ φ (not_injective_of_len_lt hX φ)]
    · rcases len_lt_or_eq_op_top Y with hY | rfl
      · rw [appTop_eq_zero f hY, appTop_top, comp_zero, hs _ φ (not_surjective_of_len_lt hY φ)]
      · by_cases hb : Function.Bijective φ.hom.toOrderHom
        · rw [eq_id_of_bijective φ hb]
          simp
        · rw [appTop_top, hs _ φ fun h => hb (Finite.surjective_iff_bijective.mp h),
            hi _ φ fun h => hb (Finite.injective_iff_bijective.mp h)]

/-- The extension of `f : U_k ⟶ V_k` to a morphism `U ⟶ V`, for `U` concentrated in degree `k`
and `f` killed by every non-surjective operator into `⦋k⦌`. -/
private def homFromTop (hU : ∀ (m : ℕ) (hm : m < k), IsZero (U _⦋m,hm.le⦌ₖ))
    (f : U _⦋k⦌ₖ ⟶ V _⦋k⦌ₖ)
    (hf : ∀ (m : SimplexCategory.Truncated k) (φ : m ⟶ ⦋k⦌ₖ),
      ¬ Function.Surjective φ.hom.toOrderHom → f ≫ V.map φ.op = 0) : U ⟶ V :=
  homOfAppTop f hf fun _ ψ hψ => by
    rw [map_op_eq_zero_of_not_bijective hU ψ fun h => hψ h.injective, zero_comp]

/-- The extension of `f : V_k ⟶ U_k` to a morphism `V ⟶ U`, for `U` concentrated in degree `k`
and `f` killed by every non-injective operator out of `⦋k⦌`. -/
private def homToTop (hU : ∀ (m : ℕ) (hm : m < k), IsZero (U _⦋m,hm.le⦌ₖ))
    (f : V _⦋k⦌ₖ ⟶ U _⦋k⦌ₖ)
    (hf : ∀ (m : SimplexCategory.Truncated k) (ψ : ⦋k⦌ₖ ⟶ m),
      ¬ Function.Injective ψ.hom.toOrderHom → V.map ψ.op ≫ f = 0) : V ⟶ U :=
  homOfAppTop f (fun _ φ hφ => by
    rw [map_op_eq_zero_of_not_bijective hU φ fun h => hφ h.surjective, comp_zero]) hf

end TopDegree

section HomSets

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- Statement (1) of [Stacks, Tag 0190], with the vanishing conditions stated over all
non-surjective (resp. non-injective) operators; the whole lemma is
`CategoryTheory.SimplicialObject.Truncated.exists_iso_sk_surjSum_cosk_injSum`.
Let `U` be a `k`-truncated simplicial object of `C` with `U_i = 0` for `i < k`, and write
`A = U_k`. Then for every `k`-truncated simplicial object `V`:

* a morphism `U ⟶ V` is determined by its top component `A ⟶ V_k`, and a morphism `f : A ⟶ V_k`
  is the top component of one if and only if `f ≫ V(φ) = 0` for every non-surjective
  `φ : ⦋m⦌ ⟶ ⦋k⦌`, i.e. if and only if `d^k_i ∘ f = 0` for `i = 0, …, k`;
* a morphism `V ⟶ U` is determined by its top component `V_k ⟶ A`, and a morphism `f : V_k ⟶ A`
  is the top component of one if and only if `V(ψ) ≫ f = 0` for every non-injective
  `ψ : ⦋k⦌ ⟶ ⦋m⦌`, i.e. if and only if `f ∘ s^{k-1}_i = 0` for `i = 0, …, k - 1`. -/
public theorem app_top_injective_and_exists_iff {k : ℕ} {U : SimplicialObject.Truncated C k}
    (hU : ∀ (m : ℕ) (hm : m < k), IsZero (U _⦋m,hm.le⦌ₖ)) (V : SimplicialObject.Truncated C k) :
    (Function.Injective (fun g : U ⟶ V => g.app (op ⦋k⦌ₖ)) ∧
      ∀ f : U _⦋k⦌ₖ ⟶ V _⦋k⦌ₖ, (∃ g : U ⟶ V, g.app (op ⦋k⦌ₖ) = f) ↔
        ∀ (m : SimplexCategory.Truncated k) (φ : m ⟶ ⦋k⦌ₖ),
          ¬ Function.Surjective φ.hom.toOrderHom → f ≫ V.map φ.op = 0) ∧
    (Function.Injective (fun g : V ⟶ U => g.app (op ⦋k⦌ₖ)) ∧
      ∀ f : V _⦋k⦌ₖ ⟶ U _⦋k⦌ₖ, (∃ g : V ⟶ U, g.app (op ⦋k⦌ₖ) = f) ↔
        ∀ (m : SimplexCategory.Truncated k) (ψ : ⦋k⦌ₖ ⟶ m),
          ¬ Function.Injective ψ.hom.toOrderHom → V.map ψ.op ≫ f = 0) := by
  refine ⟨⟨fun g g' h => hom_ext_of_app_top (fun _ hX => (hU _ hX).eq_of_src) h,
      fun f => ⟨?_, fun hf => ⟨homFromTop hU f hf, appTop_top f⟩⟩⟩,
    ⟨fun g g' h => hom_ext_of_app_top (fun _ hX => (hU _ hX).eq_of_tgt) h,
      fun f => ⟨?_, fun hf => ⟨homToTop hU f hf, appTop_top f⟩⟩⟩⟩
  · rintro ⟨g, rfl⟩ m φ hφ
    rw [← g.naturality φ.op, map_op_eq_zero_of_not_bijective hU φ fun h => hφ h.surjective,
      zero_comp]
  · rintro ⟨g, rfl⟩ m ψ hψ
    rw [g.naturality ψ.op, map_op_eq_zero_of_not_bijective hU ψ fun h => hψ h.injective, comp_zero]

end HomSets

end CategoryTheory.SimplicialObject.Truncated

namespace CategoryTheory.SimplicialObject

open CategoryTheory.Limits Opposite

section Formal

variable {C : Type u} [Category.{v} C]

/-- A cocone over a filtered diagram whose structure morphisms are isomorphisms from some index
on is a colimit cocone. -/
private noncomputable def isColimitOfIsIsoIotaApp {J : Type w} [Category.{w'} J] [IsFiltered J]
    {F : J ⥤ C} (c : Cocone F) (i₀ : J) (h : ∀ ⦃j : J⦄, (i₀ ⟶ j) → IsIso (c.ι.app j)) :
    IsColimit c :=
  have h₀ := h (𝟙 i₀)
  have : F.IsEventuallyConstantFrom i₀ := fun {j} f => by
    have : IsIso (F.map f ≫ c.ι.app j) := by rw [c.w]; exact h₀
    have := h f
    exact IsIso.of_isIso_comp_right (F.map f) (c.ι.app j)
  this.isColimitOfIsIso c

end Formal

section Skeleta

variable {C : Type u} [Category.{v} C]

/-- For `m ≤ n` the counit `i_{n!} sk_n V ⟶ V` becomes an isomorphism after `m`-truncation. -/
private theorem isIso_truncation_map_skAdj_counit_app [HasFiniteColimits C]
    (V : SimplicialObject C) {m n : ℕ} (hmn : m ≤ n) :
    IsIso ((truncation (C := C) m).map ((skAdj n).counit.app V)) :=
  have (k : (SimplexCategory.Truncated m)ᵒᵖ) :
      IsIso (((truncation (C := C) m).map ((skAdj n).counit.app V)).app k) :=
    isIso_skAdj_counit_app_app V _ (k.unop.property.trans hmn)
  NatIso.isIso_of_isIso_app _

/-- For `m ≤ n` the `m`-skeleton of `V` maps to its `n`-skeleton over `V`: there is a morphism
`i_{m!} sk_m V ⟶ i_{n!} sk_n V` whose composite with the counit `i_{n!} sk_n V ⟶ V` is the
counit `i_{m!} sk_m V ⟶ V`. -/
private theorem exists_hom_sk_of_le [HasFiniteColimits C] (V : SimplicialObject C) {m n : ℕ}
    (hmn : m ≤ n) :
    ∃ g : (sk m).obj V ⟶ (sk n).obj V,
      g ≫ (skAdj n).counit.app V = (skAdj m).counit.app V :=
  have := isIso_truncation_map_skAdj_counit_app V hmn
  ⟨(Truncated.sk m).map (inv ((truncation m).map ((skAdj n).counit.app V))) ≫
      (skAdj m).counit.app ((sk n).obj V), by
    rw [Category.assoc, ← (skAdj (C := C) m).counit_naturality ((skAdj n).counit.app V),
      ← Functor.map_comp_assoc, IsIso.inv_hom_id]
    simp⟩

end Skeleta

section Abelian

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The counit `i_{n!} sk_n V ⟶ V` is a monomorphism. -/
private theorem mono_skAdj_counit_app (V : SimplicialObject A) (n : ℕ) :
    Mono ((skAdj n).counit.app V) :=
  have (k : SimplexCategoryᵒᵖ) : Mono (((skAdj n).counit.app V).app k) :=
    (isLeast_subobject_mk_skAdj_counit_app V n k.unop.len).choose
  NatTrans.mono_of_mono_app _

/-- **Stacks 0193**.
Let `V` be a simplicial object of an abelian category `A`. Then there are monomorphisms
`f n : i_{n!} sk_n V ⟶ i_{(n + 1)!} sk_{n + 1} V` between consecutive skeleta of `V` such that `V`,
equipped with the canonical morphisms `i_{n!} sk_n V ⟶ V` (the counits of `i_{n!} ⊣ sk_n`), is the
colimit of the resulting sequence: `V = colim_n i_{n!} sk_n V`. -/
@[stacks 0193]
public theorem exists_mono_isColimit_sk (V : SimplicialObject A) :
    ∃ (f : (n : ℕ) → (sk n).obj V ⟶ (sk (n + 1)).obj V)
      (ι : Functor.ofSequence (X := fun n ↦ (sk n).obj V) f ⟶ (Functor.const ℕ).obj V),
      (∀ n, Mono (f n)) ∧ (∀ n, ι.app n = (skAdj n).counit.app V) ∧
        Nonempty (IsColimit (Cocone.mk V ι)) := by
  choose f hf using fun n => exists_hom_sk_of_le V (Nat.le_add_right n 1)
  refine ⟨f, NatTrans.ofSequence (fun n => (skAdj n).counit.app V) (fun n => ?_),
    fun n => ?_, fun n => rfl, ⟨?_⟩⟩
  · simp only [Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
    exact (hf n).trans (Category.comp_id _).symm
  · have := mono_skAdj_counit_app V n
    exact mono_of_mono_fac (hf n)
  · exact evaluationJointlyReflectsColimits _ fun k =>
      isColimitOfIsIsoIotaApp _ k.unop.len fun {_} hij =>
        isIso_skAdj_counit_app_app V k (leOfHom hij)

end Abelian

end CategoryTheory.SimplicialObject
