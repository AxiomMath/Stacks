module

public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.Basic
public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.HomEvaluation
public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.LeftModule

/-!
# Left differential graded module structures and maps into the endomorphism algebra

Let `R` be a commutative ring, `A` a differential graded `R`-algebra and `M` a cochain complex of
`R`-modules, with endomorphism differential graded algebra `E = Hom^•(M, M)`. To give a left
differential graded `A`-module structure on `M` is the same thing as giving a homomorphism
`A ⟶ E` of differential graded `R`-algebras (Tag 0FQ3).

A left differential graded `A`-module structure on `M` is presented here as a left differential
graded `A`-module `L` (an `A`-module with a grading and a differential satisfying the Leibniz rule
`d(a x) = d(a) x + (-1)^n a d(x)`) together with an identification `i` of its underlying complex
with `M`; through `i` the module `L` puts the multiplication
`A^n × M^p → M^{p + n}, (a, y) ↦ i(a · i⁻¹(y))` on `M`.

## Main definitions

* `DifferentialGraded.LeftModule.toEndomorphismHom`: the homomorphism `A ⟶ E` attached to a left
  differential graded module `L` and an identification of its underlying complex with `M`.

## Main results

* `DifferentialGraded.LeftModule.toEndomorphismHom_spec_surjective_eq_iff` (Tag 0FQ3): the
  homomorphism attached to `(L, i)` sends a homogeneous `a` to multiplication by `a` on `M`, with
  no sign; every homomorphism `A ⟶ E` arises in this way; and two pairs give the same homomorphism
  exactly when they put the same multiplication on `M`. Hence `(L, i) ↦ toEndomorphismHom L i` is
  a bijection from left differential graded `A`-module structures on `M` to homomorphisms
  `A ⟶ E`.

## References

* [Stacks Project, Tag 0FQ3](https://stacks.math.columbia.edu/tag/0FQ3)
-/

@[expose] public section

open CategoryTheory CochainComplex CochainComplex.HomComplex

universe u v

variable {R : Type u} [CommRing R]

namespace DifferentialGraded.LeftModule

variable (A : DifferentialGradedAlgebra.{u, v} R)

/-- The homomorphism of differential graded algebras from `A` into the endomorphism algebra of `M`
attached to a left differential graded `A`-module `L` and an identification `i` of its underlying
complex with `M`: a homogeneous element goes to its action on `M`, transported through `i`. -/
noncomputable def toEndomorphismHom (L : LeftModule A) (M : CochainComplex (ModuleCat.{u} R) ℤ)
    (i : toCochainComplex A L ≅ M) : A.Hom (endomorphismDGA M).algebra :=
  (A.leftActionEquivHom M).val (leftAction A L M i)

/-- The components of the action attached to `(L, i)` are the multiplication of `L`, transported
through `i`. -/
private theorem leftAction_action_v_apply (L : LeftModule A)
    (M : CochainComplex (ModuleCat.{u} R) ℤ) (i : toCochainComplex A L ≅ M) (n p : ℤ)
    (a : A.grading n) (y : M.X p) :
    ((leftAction A L M i).action n a).v p (p + n) rfl y =
      i.hom.f (p + n)
        (⟨(a : A.A) • (show L.grading p from i.inv.f p y).1, by
          simpa only [add_comm] using
            L.smul_mem n p (a : A.A) _ a.property (show L.grading p from i.inv.f p y).2⟩ :
          L.grading (p + n)) :=
  rfl

/-- **Stacks 0FQ3.** Giving a left differential graded `A`-module structure on a complex `M` is the
same thing as giving a homomorphism of differential graded `R`-algebras from `A` into the
endomorphism algebra `E = Hom^•(M, M)`. A structure is a left differential graded `A`-module `L`
with an identification `i` of its underlying complex with `M`; it corresponds to
`toEndomorphismHom A L M i`, and:

* this homomorphism sends a homogeneous `a ∈ A^n` to the cochain `M^p → M^{p + n}` which is
  multiplication by `a` transported through `i`, with no sign;
* every homomorphism `A ⟶ E` arises from some structure;
* two structures `(L, i)` and `(L', i')` give the same homomorphism if and only if they put the
  same multiplication `A^n × M^p → M^{p + n}` on `M`.

So the correspondence is a bijection between multiplications on `M` making it a left differential
graded `A`-module and homomorphisms `A ⟶ E`. -/
@[stacks 0FQ3 "left module structures on a complex and algebra homomorphisms"]
theorem toEndomorphismHom_spec_surjective_eq_iff (M : CochainComplex (ModuleCat.{u} R) ℤ) :
    (∀ (L : LeftModule A) (i : toCochainComplex A L ≅ M) (n p : ℤ) (a : A.grading n)
        (x : L.grading p),
        ((endomorphismDGA M).cochainEquiv n
            ⟨(toEndomorphismHom A L M i).toAlgebraHom a,
              (toEndomorphismHom A L M i).map_grading n a a.property⟩).v p (p + n) rfl
            (i.hom.f p x) =
          i.hom.f (p + n)
            (⟨(a : A.A) • (x : L.M), by
              simpa only [add_comm] using
                L.smul_mem n p (a : A.A) (x : L.M) a.property x.property⟩ :
              L.grading (p + n))) ∧
    (∀ φ : A.Hom (endomorphismDGA M).algebra,
      ∃ (L : LeftModule A) (i : toCochainComplex A L ≅ M), toEndomorphismHom A L M i = φ) ∧
    (∀ (L : LeftModule A) (i : toCochainComplex A L ≅ M)
        (L' : LeftModule A) (i' : toCochainComplex A L' ≅ M),
      toEndomorphismHom A L M i = toEndomorphismHom A L' M i' ↔
        ∀ (n p : ℤ) (a : A.grading n) (y : M.X p),
          i.hom.f (p + n)
              (⟨(a : A.A) • (show L.grading p from i.inv.f p y).1, by
                simpa only [add_comm] using
                  L.smul_mem n p (a : A.A) _ a.property (show L.grading p from i.inv.f p y).2⟩ :
                L.grading (p + n)) =
            i'.hom.f (p + n)
              (⟨(a : A.A) • (show L'.grading p from i'.inv.f p y).1, by
                simpa only [add_comm] using
                  L'.smul_mem n p (a : A.A) _ a.property (show L'.grading p from i'.inv.f p y).2⟩ :
                L'.grading (p + n))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro L i n p a x
    rw [toEndomorphismHom, (A.leftActionEquivHom M).property (leftAction A L M i) n a]
    exact leftAction_apply A L M i n p a x
  · intro φ
    let s := (A.leftActionEquivHom M).val.symm φ
    obtain ⟨L, i, hi⟩ := DifferentialGradedAlgebra.LeftAction.exists_leftModule A M s
    refine ⟨L, i, ?_⟩
    have hs : leftAction A L M i = s := by
      refine DifferentialGradedAlgebra.LeftAction.ext_action fun n a => ?_
      refine Cochain.ext _ _ fun p q hpq => ?_
      subst hpq
      apply ModuleCat.hom_ext
      ext y
      have hy : y = i.hom.f p (i.inv.f p y) := by
        change y = (i.inv.f p ≫ i.hom.f p) y
        rw [← HomologicalComplex.comp_f, i.inv_hom_id]
        rfl
      change ((leftAction A L M i).action n a).v p (p + n) rfl y =
        (s.action n a).v p (p + n) rfl y
      rw [hy]
      exact (leftAction_apply A L M i n p a (i.inv.f p y)).trans (hi n p a (i.inv.f p y)).symm
    rw [toEndomorphismHom, hs]
    exact (A.leftActionEquivHom M).val.apply_symm_apply φ
  · intro L i L' i'
    rw [toEndomorphismHom, toEndomorphismHom, (A.leftActionEquivHom M).val.injective.eq_iff]
    constructor
    · intro h n p a y
      have h' := congrArg (fun t : A.LeftAction M => (t.action n a).v p (p + n) rfl y) h
      exact (leftAction_action_v_apply A L M i n p a y).symm.trans
        (h'.trans (leftAction_action_v_apply A L' M i' n p a y))
    · intro h
      refine DifferentialGradedAlgebra.LeftAction.ext_action fun n a => ?_
      refine Cochain.ext _ _ fun p q hpq => ?_
      subst hpq
      apply ModuleCat.hom_ext
      ext y
      exact (leftAction_action_v_apply A L M i n p a y).trans
        ((h n p a y).trans (leftAction_action_v_apply A L' M i' n p a y).symm)

end DifferentialGraded.LeftModule
