module

public import StacksFrontier.AlgebraicGeometry.Limits.AffineLimitGlobalSections
public import StacksFrontier.RingTheory.FinitePresentation.BaseChangedColimitDescent

/-!
# Algebra 05LI part (1) along a directed inverse system of affine schemes

Let `α` be a nonempty directed preorder, let `E : αᵒᵖ ⥤ Scheme` be an inverse system of affine
schemes over a ring `Rv`, and let `c` be a limit cone.  Let `A` be an `Rv`-algebra, `M` a finite
`A`-module, `N` an `A`-module and `v : M → N` an `A`-linear map.  If the base change of `v` to
`A ⊗[Rv] Γ(c.pt, ⊤)` vanishes, then its base change to `A ⊗[Rv] Γ(E.obj a, ⊤)` vanishes at some
stage.

This is **the affine endgame of the source's proof of Stacks 083J part (2)**: there `Rv` is the
ring of functions of the affine stage `T₀`, `A` is the ring of functions of the affine chart `W₀`
of the source space, `M` and `N` are the sections of `ℱ` and `𝒢` on that chart, and
`A ⊗[Rv] Γ(T_i, ⊤)` is the ring of functions of the chart base change
`W_i = W₀ ×_{T₀} T_i` — the system of affine schemes the source applies Algebra, Lemma 05LI
part (1) to.

## Main results

* `AlgebraicGeometry.exists_baseChange_eq_zero_of_isAffine_of_isLimit_of_directed`: the statement
  above.

## Implementation notes

Two inputs meet here and neither is reproved.

The geometry is the description of the global sections of the limit as a filtered colimit of the
global sections of the stages, in its two elementwise halves
`AlgebraicGeometry.exists_appTop_eq_of_isAffine_of_isLimit_of_directed` and
`AlgebraicGeometry.exists_ge_appTop_map_eq_zero_of_isAffine_of_isLimit_of_directed`
(Stacks 01YW).  The index poset lives in the universe of the schemes, and that is not a
convenience: `StacksFrontier/AlgebraicGeometry/SmallnessNecessary/Basic.lean` exhibits a directed
inverse system of nonempty affine schemes indexed one universe up whose limit is the *empty*
scheme, so that the unit of a stage dies in the limit and at no later stage.  The statement
proved here is therefore false for an index one universe up, with no smallness hypothesis.

The algebra is `Stacks.FinitePresentation.ColimitDescent.exists_baseChange_eq_zero_baseChanged`,
Algebra 05LI part (1) along the system of base-changed algebras `A ⊗[Rv] T_i`.  What this file
adds is only the plumbing between them: the transition homomorphisms of the global sections, read
as `Rv`-algebra maps, and the `Algebra (Γ(E.obj a, ⊤)) (Γ(c.pt, ⊤))` structures carried by the
legs of the cone, together with the scalar towers over `Rv`.

The compatibility of the `Rv`-algebra structures with the transition morphisms and with the legs
is carried as the hypotheses `hmap` and `hleg` rather than derived: the `Rv`-algebra structure on
the sections of a stage is an instance argument here, so that a consumer may supply the one it
already has, and nothing in the statement forces it to come from a morphism to a fixed affine
base.

## References

* [Stacks Project, Tag 05LI](https://stacks.math.columbia.edu/tag/05LI)
* [Stacks Project, Tag 01YW](https://stacks.math.columbia.edu/tag/01YW)
* [Stacks Project, Tag 083J](https://stacks.math.columbia.edu/tag/083J)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits Opposite

open scoped TensorProduct

universe u t

variable {α : Type u} [Preorder α] [IsDirected α (· ≤ ·)] [Nonempty α]
  (E : αᵒᵖ ⥤ Scheme.{u}) (c : Cone E) (hc : IsLimit c) [∀ a, IsAffine (E.obj a)]
  {Rv : Type u} [CommRing Rv]
  [∀ a : α, Algebra Rv (Γ(E.obj (op a), ⊤) : Type u)] [Algebra Rv (Γ(c.pt, ⊤) : Type u)]

/-- A transition homomorphism of the system of global sections, as an `Rv`-algebra map. -/
def sectionsTransitionAlgHom
    (hmap : ∀ (a b : α) (h : a ≤ b) (r : Rv),
      (E.map (homOfLE h).op).appTop.hom (algebraMap Rv (Γ(E.obj (op a), ⊤) : Type u) r) =
        algebraMap Rv (Γ(E.obj (op b), ⊤) : Type u) r)
    (a b : α) (h : a ≤ b) :
    (Γ(E.obj (op a), ⊤) : Type u) →ₐ[Rv] (Γ(E.obj (op b), ⊤) : Type u) :=
  { (E.map (homOfLE h).op).appTop.hom with commutes' := hmap a b h }

/-- A leg of the cone, read on global sections as an `Rv`-algebra map. -/
def sectionsLegAlgHom
    (hleg : ∀ (a : α) (r : Rv),
      (c.π.app (op a)).appTop.hom (algebraMap Rv (Γ(E.obj (op a), ⊤) : Type u) r) =
        algebraMap Rv (Γ(c.pt, ⊤) : Type u) r)
    (a : α) : (Γ(E.obj (op a), ⊤) : Type u) →ₐ[Rv] (Γ(c.pt, ⊤) : Type u) :=
  { (c.π.app (op a)).appTop.hom with commutes' := hleg a }

include hc in
/-- **Algebra 05LI part (1) along a directed inverse system of affine schemes.**  If the base
change of an `A`-linear map out of a finite `A`-module to `A ⊗[Rv] Γ(c.pt, ⊤)` vanishes, then its
base change to `A ⊗[Rv] Γ(E.obj a, ⊤)` vanishes at some stage `a`.

This is the affine endgame of the source's proof of Stacks 083J part (2): the base-changed
algebras `A ⊗[Rv] Γ(E.obj a, ⊤)` are the rings of functions of the chart base changes
`W_i = W₀ ×_{T₀} T_i`. -/
theorem exists_baseChange_eq_zero_of_isAffine_of_isLimit_of_directed
    (hmap : ∀ (a b : α) (h : a ≤ b) (r : Rv),
      (E.map (homOfLE h).op).appTop.hom (algebraMap Rv (Γ(E.obj (op a), ⊤) : Type u) r) =
        algebraMap Rv (Γ(E.obj (op b), ⊤) : Type u) r)
    (hleg : ∀ (a : α) (r : Rv),
      (c.π.app (op a)).appTop.hom (algebraMap Rv (Γ(E.obj (op a), ⊤) : Type u) r) =
        algebraMap Rv (Γ(c.pt, ⊤) : Type u) r)
    (hcomm : ∀ (a b : α) (h : a ≤ b) (x : (Γ(E.obj (op a), ⊤) : Type u)),
      (c.π.app (op b)).appTop.hom ((E.map (homOfLE h).op).appTop.hom x) =
        (c.π.app (op a)).appTop.hom x)
    {A : Type u} [CommRing A] [Algebra Rv A]
    {M N : Type t} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (hM : Module.Finite A M) (v : M →ₗ[A] N)
    (h : LinearMap.baseChange (A ⊗[Rv] (Γ(c.pt, ⊤) : Type u)) v = 0) :
    ∃ a : α, LinearMap.baseChange (A ⊗[Rv] (Γ(E.obj (op a), ⊤) : Type u)) v = 0 := by
  let : ∀ a : α, Algebra (Γ(E.obj (op a), ⊤) : Type u) (Γ(c.pt, ⊤) : Type u) := fun a ↦
    (sectionsLegAlgHom E c hleg a).toRingHom.toAlgebra
  let : ∀ a : α, IsScalarTower Rv (Γ(E.obj (op a), ⊤) : Type u) (Γ(c.pt, ⊤) : Type u) :=
    fun a ↦ IsScalarTower.of_algebraMap_eq fun r ↦
      ((sectionsLegAlgHom E c hleg a).commutes r).symm
  have : DirectedSystem (fun a : α ↦ (Γ(E.obj (op a), ⊤) : Type u))
      fun a b h ↦ ⇑(sectionsTransitionAlgHom E hmap a b h) := by
    refine ⟨fun a x ↦ ?_, fun a b d hab hbd x ↦ ?_⟩
    · change (E.map (homOfLE (le_refl a)).op).appTop.hom x = x
      rw [show (homOfLE (le_refl a)).op = (𝟙 (op a) : op a ⟶ op a) from Subsingleton.elim _ _]
      simp
    · change (E.map (homOfLE hbd).op).appTop.hom ((E.map (homOfLE hab).op).appTop.hom x) =
        (E.map (homOfLE (hab.trans hbd)).op).appTop.hom x
      rw [show (homOfLE (hab.trans hbd)).op =
        (homOfLE hbd).op ≫ (homOfLE hab).op from Subsingleton.elim _ _, Functor.map_comp]
      rfl
  exact Stacks.FinitePresentation.ColimitDescent.exists_baseChange_eq_zero_baseChanged
    (fun a b h ↦ sectionsTransitionAlgHom E hmap a b h)
    (fun a b h x ↦ hcomm a b h x)
    (fun r ↦ by
      obtain ⟨a, x, hx⟩ := exists_appTop_eq_of_isAffine_of_isLimit_of_directed E c hc r
      exact ⟨a, x, hx⟩)
    (fun a x hx ↦ by
      obtain ⟨b, hab, hb⟩ :=
        exists_ge_appTop_map_eq_zero_of_isAffine_of_isLimit_of_directed E c hc a x hx
      exact ⟨b, hab, hb⟩)
    hM v h

end AlgebraicGeometry

end
