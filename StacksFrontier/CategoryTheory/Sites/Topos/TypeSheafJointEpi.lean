module

public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Sheafification
import StacksCore.Tactic.EgaSgaAttribute

/-! # A jointly locally surjective family of morphisms of sheaves of types

Let `(C, J)` be a site and let `ψ i : A i ⟶ B` be a family of morphisms of sheaves of sets on it.
Call the family *jointly locally surjective* if every section of `B` over an object `X` is, after
restriction along the arrows of some covering sieve of `X`, in the image of one of the `ψ i`
(which one is allowed to depend on the arrow).  This file proves that a jointly locally
surjective family has epimorphic coproduct morphism `⨿ A ⟶ B`.

The converse is `Stacks.Sheaves.TypeSheaf.exists_covering_of_epi_sigmaDesc` in
`StacksFrontier.CategoryTheory.Sites.Topos.TypeSheafSections`, so together the two say that
`CategoryTheory.Limits.Sigma.desc ψ` is an epimorphism exactly when the family is jointly
locally surjective.  This is the form in which an `∃`-quantified local condition on sections — in
the application, "the sections admit, locally, a finite-free factorization *of some rank*" — is
turned into a single categorical statement, which a functor between categories of sheaves of sets
can then be applied to.

## Main results

* `Stacks.Sheaves.TypeSheaf.epi_sigmaDesc_of_forall_exists_covering`: a jointly locally
  surjective family of morphisms of sheaves of types has epimorphic coproduct morphism.

## Implementation notes

The section universe stays free; what is needed is
`CategoryTheory.Sheaf.isLocallySurjective_iff_epi`, which asks for `HasSheafify J (Type t)` and
nothing else.  A caller will usually be at `t = max u v`, where that instance is Mathlib's, but
no universe is identified here.

The proof is the obvious one: the sieve supplied by the hypothesis is contained in the image
sieve of `CategoryTheory.Limits.Sigma.desc ψ`, because a section of `A i` over `V` gives a
section of `⨿ A` over `V` by `CategoryTheory.Limits.Sigma.ι`, and a sieve containing a covering
sieve is covering.

## References

* [Stacks Project, Tag 00WM](https://stacks.math.columbia.edu/tag/00WM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w t v u

namespace Stacks.Sheaves.TypeSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J (Type t)]

/-- **A jointly locally surjective family of morphisms of sheaves of types has epimorphic
coproduct morphism.**  If every section of `B` over an object is, on a covering of that object,
in the image of one of the `ψ i`, then `⨿ A ⟶ B` is an epimorphism.

This is the converse of `Stacks.Sheaves.TypeSheaf.exists_covering_of_epi_sigmaDesc`. -/
@[sga "3 IV 4.4.3" "(iii) ⇒ (i)", sga "3 VIB 10.15" "partial", sga "3 VIIA 8.1.4" "partial"]
theorem epi_sigmaDesc_of_forall_exists_covering {ι : Type w} (A : ι → Sheaf J (Type t))
    [HasCoproduct A] {B : Sheaf J (Type t)} (ψ : ∀ i, A i ⟶ B)
    (h : ∀ (X : C) (b : B.obj.obj (op X)), ∃ S : Sieve X, S ∈ J X ∧
      ∀ ⦃V : C⦄ (g : V ⟶ X), S g → ∃ (i : ι) (a : (A i).obj.obj (op V)),
        (ψ i).hom.app (op V) a = B.obj.map g.op b) :
    Epi (Limits.Sigma.desc ψ) := by
  refine (Sheaf.isLocallySurjective_iff_epi (Limits.Sigma.desc ψ)).1 ⟨?_⟩
  intro U b
  obtain ⟨S, hS, hfac⟩ := h U b
  refine J.superset_covering ?_ hS
  intro V g hg
  obtain ⟨i, a, ha⟩ := hfac g hg
  refine ⟨(Limits.Sigma.ι A i).hom.app (op V) a, ?_⟩
  have hid : Limits.Sigma.ι A i ≫ Limits.Sigma.desc ψ = ψ i := Limits.Sigma.ι_comp_desc ψ i
  refine Eq.trans ?_ ha
  exact congrArg (fun m : A i ⟶ B => (ConcreteCategory.hom (m.hom.app (op V))) a) hid

end Stacks.Sheaves.TypeSheaf

end
