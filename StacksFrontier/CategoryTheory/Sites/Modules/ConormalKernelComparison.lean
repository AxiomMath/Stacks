module

public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentHomotopy

/-!
# The kernel of a conormal map is a canonical invariant of the presentation

Let `R ⟶ A₁ ⟶ B` and `R ⟶ A₂ ⟶ B` be two presentations of a sheaf of commutative rings `B`
on a site, both locally surjective, and let `ψ : A₁ ⟶ A₂` be a factorisation, that is a
morphism with `ψ ≫ φ₂ = φ₁` over the base `R`.  It induces a map of conormal sequences, hence
a map

`Ker(I₁/I₁² ⟶ B ⊗[A₁] Ω[A₁/R]) ⟶ Ker(I₂/I₂² ⟶ B ⊗[A₂] Ω[A₂/R])`

on the degree `-1` cohomology sheaves of the two naive cotangent complexes.  This file proves
that this map does not depend on `ψ`, only on the two presentations, and that it is an
isomorphism as soon as a factorisation exists in the other direction.

The degree `0` counterpart is
`Stacks.Sites.Conormal.isIso_cokernel_map_conormalSequence_f`, which needs no hypothesis at
all: there both cokernels are `Ω[B/R]`.  In degree `-1` no such description of the two kernels
is available, and what replaces it is the homotopy of Stacks 00S1 (2): two factorisations
induce maps of conormal sheaves differing by `f ≫ h`, which dies on the kernel of `f`.

## Main definitions

* `Stacks.Sites.Conormal.kernelMapOfFac`: the map on the kernels of the two conormal maps
  induced by a factorisation.

## Main results

* `Stacks.Sites.Conormal.kernelMapOfFac_eq`: it depends only on the two presentations.  This
  is Stacks 00S1 (2) read in degree `-1`.
* `Stacks.Sites.Conormal.kernelMapOfFac_id` and
  `Stacks.Sites.Conormal.kernelMapOfFac_comp`: it is the identity for the identity
  factorisation and compatible with composition.
* `Stacks.Sites.Conormal.isIso_kernelMapOfFac`: it is an isomorphism as soon as a
  factorisation exists in the other direction.
* `Stacks.Sites.Conormal.conormalMapOfFac_eq_of_conormalToTensorApp_eq_zero`: the same
  invariance on the local sections of the presheaf conormal sequence, which is the form the
  local study of a presentation uses, and
  `Stacks.Sites.Conormal.sub_mem_sq_of_one_tmul_d_eq_zero`: the same for two ring maps,
  obtained by reading that statement on a one-object site.
* `Stacks.Sites.Conormal.conormalToTensorApp_conormalMapOfFac`: the objectwise naturality of
  the conormal map, which transports the vanishing of `1 ⊗ d f` along a factorisation, and
  `Stacks.Sites.Conormal.one_tmul_d_eq_zero_of_fac`: the same for two ring maps.
* `Stacks.Sites.Conormal.sub_mem_sq_of_substitution` and
  `Stacks.Sites.Conormal.mem_ker_sq_of_fac_mem_ker_sq`: the two halves of the degree `-1`
  comparison along a factorisation `u` admitting no factorisation back, read on one element of
  the kernel against a substitution of lifts out of a third presentation.

## Implementation notes

Two spellings of the first term of a conormal sequence, as `conormalSheaf` and as the first
term of `conormalSequence`, are definitionally equal only at default transparency, so a goal
mentioning both is not type-correct at the transparency `rw` and `simp` check their motives
at.  Each proof therefore takes place in an arbitrary preadditive category, where no such
spelling occurs: the four lemmas `comp_ι_eq_of_comp_eq_add`, `eq_id_of_comp_ι_eq`,
`comp_comp_ι_eq` and `isIso_of_comp_ι` carry all the diagram chasing, and the conormal-sequence
statements are instances of them.  Nothing is computed on local sections.

The generality is that of an arbitrary morphism `ψ` of sheaves of rings between the two
presenting algebras, not of a morphism of the two families of generators: comparing a
polynomial presentation `A[E] ⟶ B` with its evaluation `A[A[E]] ⟶ A[E]` is of the former kind
only.

## References

* [Stacks Project, Tag 00S1](https://stacks.math.columbia.edu/tag/00S1), part (2), the
  homotopy used here.
* [Stacks Project, Tag 08TS](https://stacks.math.columbia.edu/tag/08TS), the conormal
  sequence.
* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY), the independence of
  the naive cotangent complex from the presentation, of which this is the degree `-1`
  comparison for presentations that factor through each other.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w z

namespace Stacks.Sites.Conormal

/-! ### Diagram lemmas

The four statements of this section are the whole content of the proofs below, written in an
arbitrary preadditive category so that no two spellings of one object are in play. -/

section Diagram

variable {D : Type*} [Category D] {K K' L X Y Z : D}

section Preadditive

variable [Preadditive D]

/-- A morphism `k` restricting a morphism `g` along two monomorphisms, and one restricting a
morphism `g'`, agree as soon as `g` and `g'` differ by a morphism factoring through a `f`
that `ι` kills. -/
theorem comp_ι_eq_of_comp_eq_add (ι : K ⟶ X) (f : X ⟶ Y) (h : Y ⟶ Z) (ι' : K' ⟶ Z)
    (k k' : K ⟶ K') (g g' : X ⟶ Z) (hι : ι ≫ f = 0) (hk : k ≫ ι' = ι ≫ g)
    (hk' : k' ≫ ι' = ι ≫ g') (hg : g = f ≫ h + g') : k ≫ ι' = k' ≫ ι' := by
  rw [hk, hk', hg, Preadditive.comp_add, ← Category.assoc, hι, zero_comp, zero_add]

end Preadditive

/-- A morphism restricting the identity along a monomorphism is the identity. -/
theorem eq_id_of_comp_ι_eq (ι : K ⟶ X) [Mono ι] (k : K ⟶ K) (g : X ⟶ X)
    (hk : k ≫ ι = ι ≫ g) (hg : g = 𝟙 X) : k = 𝟙 K := by
  refine (cancel_mono ι).mp ?_
  rw [hk, hg, Category.comp_id, Category.id_comp]

/-- Restrictions along monomorphisms compose. -/
theorem comp_comp_ι_eq (ι : K ⟶ X) (ι' : K' ⟶ Y) (ι'' : L ⟶ Z) (k : K ⟶ K') (k' : K' ⟶ L)
    (m : K ⟶ L) (g : X ⟶ Y) (g' : Y ⟶ Z) (p : X ⟶ Z) (hk : k ≫ ι' = ι ≫ g)
    (hk' : k' ≫ ι'' = ι' ≫ g') (hm : m ≫ ι'' = ι ≫ p) (hp : g ≫ g' = p) :
    (k ≫ k') ≫ ι'' = m ≫ ι'' := by
  rw [Category.assoc, hk', ← Category.assoc, hk, Category.assoc, hp, hm]

/-- A restriction along monomorphisms whose two composites with a restriction back are the
identity is an isomorphism. -/
theorem isIso_of_comp_ι (k : K ⟶ K') (k' : K' ⟶ K) (hkk : k ≫ k' = 𝟙 K)
    (hk'k : k' ≫ k = 𝟙 K') : IsIso k :=
  ⟨k', hkk, hk'k⟩

end Diagram

/-! ### The invariance on local sections

The sheaf statements below are about the kernel of a morphism of sheaves of modules.  The same
invariance holds on the local sections of the presheaf conormal sequence, where it is what the
local study of a presentation uses, and there it is a direct consequence of the degree `-1`
homotopy identity: a local section killed by the conormal map is killed by the homotopy's
source, so the two factorisations have the same value on it. -/

section Objectwise

variable {C : Type u} [Category.{v} C]
  {P₁ P₂ T R₀ : Cᵒᵖ ⥤ CommRingCat.{w}} (φ₁ : P₁ ⟶ T) (φ₂ : P₂ ⟶ T) (ψ ψ' : P₁ ⟶ P₂)
  (hψ : ψ ≫ φ₂ = φ₁) (hψ' : ψ' ≫ φ₂ = φ₁)
  (a₁ : R₀ ⟶ P₁) (a₂ : R₀ ⟶ P₂) (ha : a₁ ≫ ψ = a₂) (ha' : a₁ ≫ ψ' = a₂)

include hψ hψ' ha ha' in
/-- **Stacks 00S1 (2) in degree `-1`, on local sections.** Two factorisations of one
presentation through another have the same value on a local section of the conormal module
that the conormal map kills, because the degree `-1` homotopy identity expresses their
difference as the homotopy applied to that value. -/
theorem conormalMapOfFac_eq_of_conormalToTensorApp_eq_zero (X : Cᵒᵖ)
    (c : (conormalPresheaf φ₁).obj X) (hc : conormalToTensorApp φ₁ a₁ X c = 0) :
    conormalMapOfFac φ₁ φ₂ ψ hψ X c = conormalMapOfFac φ₁ φ₂ ψ' hψ' X c := by
  have h := tensorHomotopyOfFac_conormalToTensorApp φ₁ φ₂ ψ ψ' hψ hψ' a₁ a₂ ha ha' X c
  exact sub_eq_zero.mp (h.symm.trans
    ((congrArg (tensorHomotopyOfFac φ₁ φ₂ ψ ψ' hψ hψ' a₁ a₂ ha ha' X) hc).trans (map_zero _)))

include hψ ha in
/-- On local sections, the induced map on the tensor term carries `1 ⊗ d x` to
`1 ⊗ d (ψ x)`. -/
theorem tensorMapOfFacₛₗ_one_tmul_d (X : Cᵒᵖ) (x : P₁.obj X) :
    tensorMapOfFacₛₗ φ₁ φ₂ ψ hψ a₁ a₂ ha X
        ((1 : P₁.obj X ⧸ kernelIdeal φ₁ X) ⊗ₜ[P₁.obj X]
          CommRingCat.KaehlerDifferential.d (f := a₁.app X) x) =
      (1 : P₂.obj X ⧸ kernelIdeal φ₂ X) ⊗ₜ[P₂.obj X]
        CommRingCat.KaehlerDifferential.d (f := a₂.app X) (ψ.app X x) :=
  (TensorProduct.map_tmul _ _ _ _).trans
    (congrArg₂ (fun b (ω : (differentialsPresheaf a₂).obj X) ↦ b ⊗ₜ[P₂.obj X] ω)
      (map_one (quotientMapOfFac φ₁ φ₂ ψ hψ X).hom)
      (differentialsMapOfFac_d ψ a₁ a₂ ha X x))

include hψ ha in
/-- **The objectwise naturality of the conormal map.** On local sections the left-hand map of
the conormal sequence commutes with the maps induced by a factorisation.  This is the
objectwise form of `Stacks.Sites.Conormal.conormalSequence_f_naturality`, and it is what
transports the vanishing of `1 ⊗ d f` along a factorisation. -/
theorem conormalToTensorApp_conormalMapOfFac (X : Cᵒᵖ) (c : (conormalPresheaf φ₁).obj X) :
    conormalToTensorApp φ₂ a₂ X (conormalMapOfFac φ₁ φ₂ ψ hψ X c) =
      tensorMapOfFacₛₗ φ₁ φ₂ ψ hψ a₁ a₂ ha X (conormalToTensorApp φ₁ a₁ X c) := by
  obtain ⟨x, rfl⟩ := (kernelIdeal φ₁ X).toCotangent_surjective c
  exact (conormalToTensorApp_toCotangent φ₂ a₂ X _).trans
    (((congrArg (tensorMapOfFacₛₗ φ₁ φ₂ ψ hψ a₁ a₂ ha X)
        (conormalToTensorApp_toCotangent φ₁ a₁ X x)).trans
      (tensorMapOfFacₛₗ_one_tmul_d φ₁ φ₂ ψ hψ a₁ a₂ ha X (x : P₁.obj X))).symm)

end Objectwise

/-! ### The invariance at the ring level

A ring map is a morphism of constant presheaves, so the statement above read on a one-object
site is a statement about ring maps: two ring maps factoring one presentation through another
agree, modulo the square of the second kernel, on an element of the first kernel whose
universal differential dies in the tensor term.  That is the form the local study of a
polynomial presentation needs, where the two maps are a substitution of local lifts of
finitely many variables and the truncation to the variables of one polynomial, neither of
which is natural in the object of the site. -/

section RingLevel

open Opposite

variable {Pr Pr' T R₀ : CommRingCat.{w}} (φ : Pr ⟶ T) (φ' : Pr' ⟶ T) (u v : Pr ⟶ Pr')
  (hu : u ≫ φ' = φ) (hv : v ≫ φ' = φ)
  (b : R₀ ⟶ Pr) (b' : R₀ ⟶ Pr') (hbu : b ≫ u = b') (hbv : b ≫ v = b')

include hu in
/-- A factorisation of a presentation through another carries the kernel into the kernel. -/
theorem mem_ker_of_fac {q : Pr} (hq : q ∈ RingHom.ker φ.hom) :
    u.hom q ∈ RingHom.ker φ'.hom := by
  change φ'.hom (u.hom q) = 0
  rw [← CommRingCat.comp_apply, hu]
  exact hq

include hu in
/-- A factorisation of a presentation through another carries the square of the kernel into the
square of the kernel. -/
theorem map_mem_ker_sq_of_fac {z : Pr} (hz : z ∈ RingHom.ker φ.hom ^ 2) :
    u.hom z ∈ RingHom.ker φ'.hom ^ 2 := by
  rw [pow_two] at hz ⊢
  refine Submodule.mul_induction_on hz (fun m hm n hn ↦ ?_) (fun x y hx hy ↦ ?_)
  · rw [map_mul]
    exact Ideal.mul_mem_mul (mem_ker_of_fac φ φ' u hu hm) (mem_ker_of_fac φ φ' u hu hn)
  · rw [map_add]
    exact Ideal.add_mem _ hx hy

private theorem const_map_comp_eq {X Y Z : CommRingCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (hf : f ≫ g = h) : (Functor.const (Discrete PUnit.{1})ᵒᵖ).map f ≫
      (Functor.const (Discrete PUnit.{1})ᵒᵖ).map g = (Functor.const (Discrete PUnit.{1})ᵒᵖ).map h :=
  ((Functor.const (Discrete PUnit.{1})ᵒᵖ).map_comp f g).symm.trans
    (congrArg (Functor.const (Discrete PUnit.{1})ᵒᵖ).map hf)

/-- A kernel element whose universal differential vanishes has vanishing conormal image, read on
the constant presheaves. -/
private theorem conormalToTensorApp_const_toCotangent_eq_zero (q : Pr)
    (hq : q ∈ RingHom.ker φ.hom)
    (hd : (1 : Pr ⧸ RingHom.ker φ.hom) ⊗ₜ[Pr]
        CommRingCat.KaehlerDifferential.d (f := b) q = 0) :
    conormalToTensorApp ((Functor.const (Discrete PUnit.{1})ᵒᵖ).map φ)
      ((Functor.const (Discrete PUnit.{1})ᵒᵖ).map b) (op ⟨PUnit.unit⟩)
      ((RingHom.ker φ.hom).toCotangent ⟨q, hq⟩) = 0 :=
  (conormalToTensorApp_toCotangent ((Functor.const (Discrete PUnit.{1})ᵒᵖ).map φ)
    ((Functor.const (Discrete PUnit.{1})ᵒᵖ).map b) (op ⟨PUnit.unit⟩) ⟨q, hq⟩).trans hd

include hu hv hbu hbv in
/-- **Stacks 00S1 (2) in degree `-1`, for ring maps.** Two factorisations `u, v` of a
presentation `φ` through a presentation `φ'`, both over the base ring, agree modulo the
square of the kernel of `φ'` on an element of the kernel of `φ` whose universal differential
vanishes in `(Pr/I) ⊗ Ω`. -/
theorem sub_mem_sq_of_one_tmul_d_eq_zero (q : Pr) (hq : q ∈ RingHom.ker φ.hom)
    (hd : (1 : Pr ⧸ RingHom.ker φ.hom) ⊗ₜ[Pr]
        CommRingCat.KaehlerDifferential.d (f := b) q = 0) :
    u.hom q - v.hom q ∈ RingHom.ker φ'.hom ^ 2 := by
  have hmu := mem_ker_of_fac φ φ' u hu hq
  have hmv := mem_ker_of_fac φ φ' v hv hq
  have h := conormalMapOfFac_eq_of_conormalToTensorApp_eq_zero
    ((Functor.const (Discrete PUnit.{1})ᵒᵖ).map φ)
    ((Functor.const (Discrete PUnit.{1})ᵒᵖ).map φ')
    ((Functor.const (Discrete PUnit.{1})ᵒᵖ).map u)
    ((Functor.const (Discrete PUnit.{1})ᵒᵖ).map v)
    (const_map_comp_eq u φ' φ hu) (const_map_comp_eq v φ' φ hv)
    ((Functor.const (Discrete PUnit.{1})ᵒᵖ).map b)
    ((Functor.const (Discrete PUnit.{1})ᵒᵖ).map b')
    (const_map_comp_eq b u b' hbu) (const_map_comp_eq b v b' hbv)
    (op ⟨PUnit.unit⟩) ((RingHom.ker φ.hom).toCotangent ⟨q, hq⟩)
    (conormalToTensorApp_const_toCotangent_eq_zero φ b q hq hd)
  refine (Ideal.toCotangent_eq_zero (RingHom.ker φ'.hom)
    ⟨u.hom q - v.hom q, Ideal.sub_mem _ hmu hmv⟩).mp ?_
  have hsplit : (⟨u.hom q - v.hom q, Ideal.sub_mem _ hmu hmv⟩ : RingHom.ker φ'.hom) =
      ⟨u.hom q, hmu⟩ - ⟨v.hom q, hmv⟩ := rfl
  rw [hsplit, map_sub]
  exact sub_eq_zero.mpr h

include hu hbu in
/-- **The naturality of the degree `-1` map of the conormal sequence, for ring maps.**  A
factorisation `u` of a presentation `φ` through a presentation `φ'` over the base carries an
element of the kernel of `φ` whose universal differential vanishes to one whose universal
differential vanishes.  Together with
`Stacks.Sites.Conormal.sub_mem_sq_of_one_tmul_d_eq_zero` this is the whole ring-level content
of Stacks 00S1 (2) in degree `-1`; it is obtained, like that statement, by reading the
presheaf lemma on a one-object site with constant presheaves. -/
theorem one_tmul_d_eq_zero_of_fac (q : Pr) (hq : q ∈ RingHom.ker φ.hom)
    (hd : (1 : Pr ⧸ RingHom.ker φ.hom) ⊗ₜ[Pr]
        CommRingCat.KaehlerDifferential.d (f := b) q = 0) :
    (1 : Pr' ⧸ RingHom.ker φ'.hom) ⊗ₜ[Pr']
      CommRingCat.KaehlerDifferential.d (f := b') (u.hom q) = 0 := by
  have h := conormalToTensorApp_conormalMapOfFac
    ((Functor.const (Discrete PUnit.{1})ᵒᵖ).map φ)
    ((Functor.const (Discrete PUnit.{1})ᵒᵖ).map φ')
    ((Functor.const (Discrete PUnit.{1})ᵒᵖ).map u) (const_map_comp_eq u φ' φ hu)
    ((Functor.const (Discrete PUnit.{1})ᵒᵖ).map b)
    ((Functor.const (Discrete PUnit.{1})ᵒᵖ).map b') (const_map_comp_eq b u b' hbu)
    (op ⟨PUnit.unit⟩) ((RingHom.ker φ.hom).toCotangent ⟨q, hq⟩)
  refine Eq.trans (conormalToTensorApp_toCotangent
    ((Functor.const (Discrete PUnit.{1})ᵒᵖ).map φ')
    ((Functor.const (Discrete PUnit.{1})ᵒᵖ).map b') (op ⟨PUnit.unit⟩)
    ⟨u.hom q, mem_ker_of_fac φ φ' u hu hq⟩).symm (h.trans ?_)
  exact (congrArg _ (conormalToTensorApp_const_toCotangent_eq_zero φ b q hq hd)).trans
    (map_zero _)

end RingLevel

/-! ### Substituting a lift of the variables

The comparison of two presentations that this chapter needs is along a factorisation
`u : P₁ ⟶ P₂` of `φ₁` through `φ₂` for which *no* factorisation back exists: over a site, a
lift of a generator through a locally surjective presentation exists only locally.  What is
available instead is a factorisation back out of a *third* presentation `φ : Pr ⟶ T` which
`φ₂` also factors: over a covering object the finitely many variables occurring in one
polynomial do lift through `φ₁`, so substituting those lifts gives `σ : Pr ⟶ P₁` with
`σ ≫ φ₁ = φ`, where `Pr` is the polynomial ring on just those variables and `t : Pr ⟶ P₂`
is the inclusion.

The two statements of this section are what that configuration yields on one element of the
kernel whose universal differential vanishes.  They are the ring-level content of the degree
`-1` comparison: the first says that the conormal class of `t q` is the image of the conormal
class of `σ q`, the second that an element of the kernel of `φ₁` whose image under `u` is a
conormal boundary is already one.  Both are instances of
`Stacks.Sites.Conormal.sub_mem_sq_of_one_tmul_d_eq_zero`, which is how the second-order Taylor
expansion of the informal argument is avoided: the homotopy of Stacks 00S1 (2) already
expresses the difference of two factorisations modulo the square of the kernel. -/

section Substitution

variable {Pr P₁ P₂ T R₀ : CommRingCat.{w}} (φ : Pr ⟶ T) (φ₁ : P₁ ⟶ T) (φ₂ : P₂ ⟶ T)
  (u : P₁ ⟶ P₂) (σ : Pr ⟶ P₁) (t : Pr ⟶ P₂)
  (hu : u ≫ φ₂ = φ₁) (hσ : σ ≫ φ₁ = φ) (ht : t ≫ φ₂ = φ)
  (b : R₀ ⟶ Pr) (b₁ : R₀ ⟶ P₁) (b₂ : R₀ ⟶ P₂)
  (hbσ : b ≫ σ = b₁) (hbu : b₁ ≫ u = b₂) (hbt : b ≫ t = b₂)

include hu hσ ht hbσ hbu hbt in
/-- **The surjectivity half of the degree `-1` comparison, for ring maps.**  Let `q` be an
element of the kernel of a presentation `φ` whose universal differential vanishes, let `t` be
a factorisation of `φ` through `φ₂` and let `σ` be one through `φ₁`.  Then the images of `q`
under `u ∘ σ` and under `t` agree modulo the square of the kernel of `φ₂`, so the conormal
class of `t q` is the image under `u` of the conormal class of `σ q` — and the latter lies in
the kernel of its own conormal map by
`Stacks.Sites.Conormal.one_tmul_d_eq_zero_of_fac`. -/
theorem sub_mem_sq_of_substitution (q : Pr) (hq : q ∈ RingHom.ker φ.hom)
    (hd : (1 : Pr ⧸ RingHom.ker φ.hom) ⊗ₜ[Pr]
        CommRingCat.KaehlerDifferential.d (f := b) q = 0) :
    u.hom (σ.hom q) - t.hom q ∈ RingHom.ker φ₂.hom ^ 2 := by
  have hsu : (σ ≫ u) ≫ φ₂ = φ := by rw [Category.assoc, hu, hσ]
  have hbsu : b ≫ (σ ≫ u) = b₂ := by rw [← Category.assoc, hbσ, hbu]
  have h := sub_mem_sq_of_one_tmul_d_eq_zero φ φ₂ (σ ≫ u) t hsu ht b b₂ hbsu hbt q hq hd
  rwa [CommRingCat.comp_apply] at h

end Substitution

section SubstitutionBack

variable {P₁ P₂ T R₀ : CommRingCat.{w}} (φ₁ : P₁ ⟶ T) (φ₂ : P₂ ⟶ T)
  (u : P₁ ⟶ P₂) (σ : P₂ ⟶ P₁) (hu : u ≫ φ₂ = φ₁) (hσ : σ ≫ φ₁ = φ₂)
  (b₁ : R₀ ⟶ P₁) (b₂ : R₀ ⟶ P₂) (hbu : b₁ ≫ u = b₂) (hbσ : b₂ ≫ σ = b₁)

include hu hσ hbu hbσ in
/-- **The injectivity half of the degree `-1` comparison, for ring maps.**  If a factorisation
`σ` of `φ₂` through `φ₁` back along `u` exists, then an element of the kernel of `φ₁` whose
universal differential vanishes and whose image under `u` lies in the square of the kernel of
`φ₂` already lies in the square of the kernel of `φ₁`: the two factorisations `σ ∘ u` and the
identity of `φ₁` through itself agree on it modulo that square. -/
theorem mem_ker_sq_of_fac_mem_ker_sq (q : P₁) (hq : q ∈ RingHom.ker φ₁.hom)
    (hd : (1 : P₁ ⧸ RingHom.ker φ₁.hom) ⊗ₜ[P₁]
        CommRingCat.KaehlerDifferential.d (f := b₁) q = 0)
    (h : u.hom q ∈ RingHom.ker φ₂.hom ^ 2) :
    q ∈ RingHom.ker φ₁.hom ^ 2 := by
  have hus : (u ≫ σ) ≫ φ₁ = φ₁ := by rw [Category.assoc, hσ, hu]
  have hbus : b₁ ≫ (u ≫ σ) = b₁ := by rw [← Category.assoc, hbu, hbσ]
  have hdiff := sub_mem_sq_of_one_tmul_d_eq_zero φ₁ φ₁ (u ≫ σ) (𝟙 P₁) hus
    (Category.id_comp φ₁) b₁ b₁ hbus (Category.comp_id b₁) q hq hd
  rw [CommRingCat.comp_apply, CommRingCat.id_apply] at hdiff
  have hσu : σ.hom (u.hom q) ∈ RingHom.ker φ₁.hom ^ 2 :=
    map_mem_ker_sq_of_fac φ₂ φ₁ σ hσ h
  rw [show q = σ.hom (u.hom q) - (σ.hom (u.hom q) - q) from (sub_sub_cancel _ _).symm]
  exact Ideal.sub_mem _ hσu hdiff

end SubstitutionBack

/-! ### The map on kernels attached to a factorisation -/



variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

section Fac

variable (R B A₁ A₂ : Sheaf J CommRingCat.{w}) (a₁ : R ⟶ A₁) (a₂ : R ⟶ A₂)
  (φ₁ : A₁ ⟶ B) (φ₂ : A₂ ⟶ B) (ψ ψ' : A₁ ⟶ A₂)
  (hψ : ψ ≫ φ₂ = φ₁) (hψ' : ψ' ≫ φ₂ = φ₁) (ha : a₁ ≫ ψ = a₂) (ha' : a₁ ≫ ψ' = a₂)
  [Presheaf.IsLocallySurjective J φ₁.hom] [Presheaf.IsLocallySurjective J φ₂.hom]

include hψ ha in
/-- The map on the kernels of the two conormal maps, that is on the degree `-1` cohomology
sheaves of the two naive cotangent complexes, induced by a factorisation `ψ ≫ φ₂ = φ₁` over
the base `R`. -/
noncomputable def kernelMapOfFac :
    kernel (conormalSequence.{v, u, w, z} J R A₁ B a₁ φ₁).f ⟶
      kernel (conormalSequence.{v, u, w, z} J R A₂ B a₂ φ₂).f :=
  kernel.map _ _ (conormalSheafMapOfFac.{v, u, w, z} J B A₁ A₂ φ₁ φ₂ ψ hψ)
    (tensorSheafMapOfFac.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha)
    (conormalSequence_f_naturality.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
include hψ ha in
/-- The map on kernels is the restriction of the map of conormal sheaves. -/
theorem kernelMapOfFac_comp_ι :
    kernelMapOfFac.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha ≫
        kernel.ι (conormalSequence.{v, u, w, z} J R A₂ B a₂ φ₂).f =
      kernel.ι (conormalSequence.{v, u, w, z} J R A₁ B a₁ φ₁).f ≫
        conormalSheafMapOfFac.{v, u, w, z} J B A₁ A₂ φ₁ φ₂ ψ hψ :=
  kernel.lift_ι _ _ _

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
include hψ hψ' ha ha' in
/-- **Stacks 00S1 (2) in degree `-1`.** The map on the kernels of the two conormal maps does
not depend on the chosen factorisation: two factorisations induce maps of conormal sheaves
differing by the homotopy precomposed with the left-hand map of the first conormal sequence,
and that composite vanishes on the kernel of that map. -/
theorem kernelMapOfFac_eq :
    kernelMapOfFac.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha =
      kernelMapOfFac.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ' hψ' ha' := by
  refine (cancel_mono (kernel.ι (conormalSequence.{v, u, w, z} J R A₂ B a₂ φ₂).f)).mp ?_
  exact comp_ι_eq_of_comp_eq_add
    (kernel.ι (conormalSequence.{v, u, w, z} J R A₁ B a₁ φ₁).f)
    (conormalSequence.{v, u, w, z} J R A₁ B a₁ φ₁).f
    (conormalHomotopyOfFac.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ ψ' hψ hψ' ha ha')
    (kernel.ι (conormalSequence.{v, u, w, z} J R A₂ B a₂ φ₂).f)
    (kernelMapOfFac.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha)
    (kernelMapOfFac.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ' hψ' ha')
    (conormalSheafMapOfFac.{v, u, w, z} J B A₁ A₂ φ₁ φ₂ ψ hψ)
    (conormalSheafMapOfFac.{v, u, w, z} J B A₁ A₂ φ₁ φ₂ ψ' hψ')
    (kernel.condition (conormalSequence.{v, u, w, z} J R A₁ B a₁ φ₁).f)
    (kernelMapOfFac_comp_ι.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha)
    (kernelMapOfFac_comp_ι.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ' hψ' ha')
    (conormalSheafMapOfFac_eq_add.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ ψ' hψ hψ' ha ha')

end Fac

section Id

variable (R B A : Sheaf J CommRingCat.{w}) (a : R ⟶ A) (φ : A ⟶ B)
  [Presheaf.IsLocallySurjective J φ.hom]

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The identity factorisation induces the identity on kernels. -/
theorem kernelMapOfFac_id :
    kernelMapOfFac.{v, u, w, z} J R B A A a a φ φ (𝟙 A) (Category.id_comp φ)
        (Category.comp_id a) =
      𝟙 (kernel (conormalSequence.{v, u, w, z} J R A B a φ).f) :=
  eq_id_of_comp_ι_eq (kernel.ι (conormalSequence.{v, u, w, z} J R A B a φ).f)
    (kernelMapOfFac.{v, u, w, z} J R B A A a a φ φ (𝟙 A) (Category.id_comp φ)
      (Category.comp_id a))
    (conormalSheafMapOfFac.{v, u, w, z} J B A A φ φ (𝟙 A) (Category.id_comp φ))
    (kernelMapOfFac_comp_ι.{v, u, w, z} J R B A A a a φ φ (𝟙 A) (Category.id_comp φ)
      (Category.comp_id a))
    (conormalSheafMapOfFac_id.{v, u, w, z} J A B φ)

end Id

section Comp

variable (R B A₁ A₂ A₃ : Sheaf J CommRingCat.{w})
  (a₁ : R ⟶ A₁) (a₂ : R ⟶ A₂) (a₃ : R ⟶ A₃)
  (φ₁ : A₁ ⟶ B) (φ₂ : A₂ ⟶ B) (φ₃ : A₃ ⟶ B) (ψ : A₁ ⟶ A₂) (χ : A₂ ⟶ A₃)
  (hψ : ψ ≫ φ₂ = φ₁) (hχ : χ ≫ φ₃ = φ₂) (ha : a₁ ≫ ψ = a₂) (hb : a₂ ≫ χ = a₃)
  [Presheaf.IsLocallySurjective J φ₁.hom] [Presheaf.IsLocallySurjective J φ₂.hom]
  [Presheaf.IsLocallySurjective J φ₃.hom]

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
include hψ hχ ha hb in
/-- The maps on kernels induced by two composable factorisations compose. -/
theorem kernelMapOfFac_comp :
    kernelMapOfFac.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha ≫
        kernelMapOfFac.{v, u, w, z} J R B A₂ A₃ a₂ a₃ φ₂ φ₃ χ hχ hb =
      kernelMapOfFac.{v, u, w, z} J R B A₁ A₃ a₁ a₃ φ₁ φ₃ (ψ ≫ χ)
        (by rw [Category.assoc, hχ, hψ]) (by rw [← Category.assoc, ha, hb]) := by
  have hψχ : (ψ ≫ χ) ≫ φ₃ = φ₁ := by rw [Category.assoc, hχ, hψ]
  have haψχ : a₁ ≫ (ψ ≫ χ) = a₃ := by rw [← Category.assoc, ha, hb]
  refine (cancel_mono (kernel.ι (conormalSequence.{v, u, w, z} J R A₃ B a₃ φ₃).f)).mp ?_
  exact comp_comp_ι_eq (kernel.ι (conormalSequence.{v, u, w, z} J R A₁ B a₁ φ₁).f)
    (kernel.ι (conormalSequence.{v, u, w, z} J R A₂ B a₂ φ₂).f)
    (kernel.ι (conormalSequence.{v, u, w, z} J R A₃ B a₃ φ₃).f)
    (kernelMapOfFac.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha)
    (kernelMapOfFac.{v, u, w, z} J R B A₂ A₃ a₂ a₃ φ₂ φ₃ χ hχ hb)
    (kernelMapOfFac.{v, u, w, z} J R B A₁ A₃ a₁ a₃ φ₁ φ₃ (ψ ≫ χ) hψχ haψχ)
    (conormalSheafMapOfFac.{v, u, w, z} J B A₁ A₂ φ₁ φ₂ ψ hψ)
    (conormalSheafMapOfFac.{v, u, w, z} J B A₂ A₃ φ₂ φ₃ χ hχ)
    (conormalSheafMapOfFac.{v, u, w, z} J B A₁ A₃ φ₁ φ₃ (ψ ≫ χ) hψχ)
    (kernelMapOfFac_comp_ι.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha)
    (kernelMapOfFac_comp_ι.{v, u, w, z} J R B A₂ A₃ a₂ a₃ φ₂ φ₃ χ hχ hb)
    (kernelMapOfFac_comp_ι.{v, u, w, z} J R B A₁ A₃ a₁ a₃ φ₁ φ₃ (ψ ≫ χ) hψχ haψχ)
    (conormalSheafMapOfFac_comp.{v, u, w, z} J B A₁ A₂ A₃ φ₁ φ₂ φ₃ ψ χ hψ hχ)

end Comp

section Iso

variable (R B A₁ A₂ : Sheaf J CommRingCat.{w}) (a₁ : R ⟶ A₁) (a₂ : R ⟶ A₂)
  (φ₁ : A₁ ⟶ B) (φ₂ : A₂ ⟶ B) (ψ : A₁ ⟶ A₂) (χ : A₂ ⟶ A₁)
  (hψ : ψ ≫ φ₂ = φ₁) (hχ : χ ≫ φ₁ = φ₂) (ha : a₁ ≫ ψ = a₂) (hb : a₂ ≫ χ = a₁)
  [Presheaf.IsLocallySurjective J φ₁.hom] [Presheaf.IsLocallySurjective J φ₂.hom]

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
include hψ hχ ha hb in
/-- **The degree `-1` comparison of Stacks 08TY, for presentations that factor through each
other.**  If two presentations of `B` over `R` admit factorisations in both directions then the
induced map on the kernels of their conormal maps is an isomorphism: the two composites are
factorisations of a presentation through itself, hence induce the same map on kernels as the
identity factorisation, which is the identity. -/
theorem isIso_kernelMapOfFac :
    IsIso (kernelMapOfFac.{v, u, w, z} J R B A₁ A₂ a₁ a₂ φ₁ φ₂ ψ hψ ha) := by
  have hψχ : (ψ ≫ χ) ≫ φ₁ = φ₁ := by rw [Category.assoc, hχ, hψ]
  have haψχ : a₁ ≫ (ψ ≫ χ) = a₁ := by rw [← Category.assoc, ha, hb]
  have hχψ : (χ ≫ ψ) ≫ φ₂ = φ₂ := by rw [Category.assoc, hψ, hχ]
  have haχψ : a₂ ≫ (χ ≫ ψ) = a₂ := by rw [← Category.assoc, hb, ha]
  refine isIso_of_comp_ι _ (kernelMapOfFac.{v, u, w, z} J R B A₂ A₁ a₂ a₁ φ₂ φ₁ χ hχ hb) ?_ ?_
  · refine Eq.trans (kernelMapOfFac_comp.{v, u, w, z} J R B A₁ A₂ A₁ a₁ a₂ a₁ φ₁ φ₂ φ₁
      ψ χ hψ hχ ha hb) ?_
    refine Eq.trans (kernelMapOfFac_eq.{v, u, w, z} J R B A₁ A₁ a₁ a₁ φ₁ φ₁ (ψ ≫ χ) (𝟙 A₁)
      hψχ (Category.id_comp φ₁) haψχ (Category.comp_id a₁)) ?_
    exact kernelMapOfFac_id.{v, u, w, z} J R B A₁ a₁ φ₁
  · refine Eq.trans (kernelMapOfFac_comp.{v, u, w, z} J R B A₂ A₁ A₂ a₂ a₁ a₂ φ₂ φ₁ φ₂
      χ ψ hχ hψ hb ha) ?_
    refine Eq.trans (kernelMapOfFac_eq.{v, u, w, z} J R B A₂ A₂ a₂ a₂ φ₂ φ₂ (χ ≫ ψ) (𝟙 A₂)
      hχψ (Category.id_comp φ₂) haχψ (Category.comp_id a₂)) ?_
    exact kernelMapOfFac_id.{v, u, w, z} J R B A₂ a₂ φ₂

end Iso

end Stacks.Sites.Conormal

end
