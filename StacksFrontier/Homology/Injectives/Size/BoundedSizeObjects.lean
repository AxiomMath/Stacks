module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.SetTheory.Cardinal.Order
public import StacksCore.CategoryTheory.Abelian.Basic
public import StacksFrontier.Homology.Injectives.Size.SubobjectCardinality
import StacksCore.Tactic.StacksAttribute

/-!
# Objects of bounded size in a Grothendieck abelian category

Let `C` be a Grothendieck abelian category and fix a cardinal `κ`. An object `M` whose set of
subobjects has cardinality at most `κ` is a quotient of a coproduct of at most `κ` copies of a
generator `U`: choosing, for each proper subobject `S` of `M`, a map `U ⟶ M` not factoring
through `S`, the induced map from the coproduct has image subobject `⊤`, hence is an
epimorphism. Consequently the objects satisfying a fixed size bound have only a set of
isomorphism classes: each of them is a cokernel of a subobject of the single object
`∐_{κ} U`, and the subobjects of a fixed object form a set.

## Main definitions

No new definitions are introduced.

## Main results

* `Stacks.Injectives.exists_epi_coproduct_of_subobject_cardinality_le`: a bounded-size object
  is a quotient of a bounded coproduct of copies of a generator.
* `Stacks.Injectives.essentiallySmall_subobject_cardinality_le`: the objects satisfying a
  fixed size bound form an essentially small class.

## Implementation notes

The size of `M` is written directly as `Cardinal.mk (Subobject M)`. Part (1) uses an index type
in the universe in which the Grothendieck axioms supply coproducts, which is why the two
cardinals are compared after lifting. Part (2) expresses "the isomorphism classes form a set"
by essential smallness of the corresponding object property in that same universe.

## References

* [Stacks Project, Tag 079E](https://stacks.math.columbia.edu/tag/079E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace Stacks.Injectives

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/-- Part (1) with the index type taken to be `κ.out`, which is the form part (2) consumes. -/
private theorem exists_epi_coproduct_out (U M : C) (hU : IsSeparator U)
    (κ : Cardinal.{w})
    (hM : Cardinal.lift.{w} (Cardinal.mk (Subobject M)) ≤
      Cardinal.lift.{max u v} κ) :
    ∃ (f : (∐ fun (_ : κ.out) => U) ⟶ M), Epi f := by
  classical
  obtain ⟨e⟩ : Nonempty (Subobject M ↪ κ.out) := by
    apply (Cardinal.lift_mk_le').mp
    simpa using hM
  rw [IsSeparator] at hU
  have hchoose : ∀ S : Subobject M, S ≠ ⊤ →
      ∃ f : U ⟶ M, ¬ S.Factors f := by
    intro S hS
    by_contra! hs
    have hE : Epi S.arrow := by
      constructor
      intro X f g hfg
      apply hU
      intro G hG h
      rw [ObjectProperty.singleton_iff] at hG
      obtain rfl : U = G := hG
      rw [← S.factorThru_arrow h (hs h), Category.assoc, hfg, Category.assoc]
    exact hS ((Subobject.isIso_arrow_iff_eq_top S).1
      (isIso_of_mono_of_epi S.arrow))
  let φ : κ.out → (U ⟶ M) := fun i =>
    if hS : Function.invFun e i = ⊤ then 0
    else Classical.choose (hchoose (Function.invFun e i) hS)
  have hφ (S : Subobject M) (hS : S ≠ ⊤) :
      ¬ S.Factors (φ (e S)) := by
    simpa only [φ, Function.leftInverse_invFun e.injective S, dite_eq_right hS]
      using Classical.choose_spec (hchoose S hS)
  let q : (∐ fun (_ : κ.out) => U) ⟶ M := Sigma.desc φ
  have hq : Epi q := by
    have hi : imageSubobject q = ⊤ := by
      by_contra htop
      apply hφ (imageSubobject q) htop
      simpa [q] using imageSubobject_factors_comp_self q
        (Sigma.ι _ (e (imageSubobject q)))
    have : IsIso (imageSubobject q).arrow :=
      (Subobject.isIso_arrow_iff_eq_top _).2 hi
    rw [← imageSubobject_arrow_comp q]; infer_instance
  exact ⟨q, hq⟩

/-- If the cardinality of the set of subobjects of `M` is at most `κ`, then `M` is a
quotient of a coproduct, indexed by a type of cardinality at most `κ`, of copies of the
generator `U`. -/
@[stacks 079E "part (1)"]
theorem exists_epi_coproduct_of_subobject_cardinality_le (U M : C) (hU : IsSeparator U)
    (κ : Cardinal.{w})
    (hM : Cardinal.lift.{w} (Cardinal.mk (Subobject M)) ≤
      Cardinal.lift.{max u v} κ) :
    ∃ (ι : Type w), Cardinal.mk ι ≤ κ ∧
      ∃ (f : (∐ fun (_ : ι) => U) ⟶ M), Epi f :=
  ⟨κ.out, (Cardinal.mk_out κ).le, exists_epi_coproduct_out U M hU κ hM⟩

/-- For every cardinal `κ`, the objects whose sets of subobjects have cardinality at most
`κ` have only a set of isomorphism classes. -/
@[stacks 079E "part (2)"]
theorem essentiallySmall_subobject_cardinality_le (κ : Cardinal.{w}) :
    ObjectProperty.EssentiallySmall.{w}
      (fun M : C => Cardinal.lift.{w} (Cardinal.mk (Subobject M)) ≤
        Cardinal.lift.{max u v} κ) := by
  classical
  let U : C := separator C
  let P : C := ∐ fun (_ : κ.out) => U
  let Q : ObjectProperty C := fun X =>
    ∃ S : Subobject P, cokernel S.arrow = X
  have hQ : ObjectProperty.Small.{w} Q := by
    apply small_of_surjective (f := fun S : Subobject P =>
      (⟨cokernel S.arrow, ⟨S, rfl⟩⟩ : Subtype Q))
    rintro ⟨_, S, rfl⟩; exact ⟨S, rfl⟩
  have hle : (fun M : C => Cardinal.lift.{w} (Cardinal.mk (Subobject M)) ≤
      Cardinal.lift.{max u v} κ) ≤ Q.isoClosure := by
    intro M hM
    obtain ⟨f, hf⟩ := exists_epi_coproduct_out U M (isSeparator_separator C) κ hM
    let S : Subobject P := kernelSubobject f
    let e : cokernel S.arrow ≅ M :=
      cokernel.mapIso (f := (kernelSubobject f).arrow) (kernel.ι f) (kernelSubobjectIso f)
        (Iso.refl _) (by simp) ≪≫ (Abelian.isoCokernelKernel f).symm
    exact ⟨_, ⟨S, rfl⟩, ⟨e.symm⟩⟩
  exact ObjectProperty.EssentiallySmall.of_le hle

end Stacks.Injectives
