module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVarietyZero
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.IndiscreteQuotientStack
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet
public import StacksFrontier.Deformation.Artin.FormalObject.NonEffectiveSystem

/-!
# Tag 0CXX fails for the zero abelian variety

Tag 0CXX asserts that for an algebraically closed field `k` which is not the algebraic closure of
a finite field and an abelian variety `A` over `k`, the classifying stack `𝒳 = [Spec(k)/A]` has a
system of objects, over an inverse system of `k`-algebras with surjective transition maps and
locally nilpotent kernels, which is not effective in the sense of Tag 0CXT.

As printed this is false. The zero group scheme `Spec k` is an abelian variety by Tag 03RO
(`AlgebraicGeometry.isAbelianVariety_tensorUnit`), and its group algebraic space is the trivial
group `𝟙_` over `Spec k`. The pointwise groupoids of its trivial action on `Spec k` are trivial,
so the projection of `[Spec(k)/0]` to the big fppf site is full and faithful
(`AlgebraicGeometry.Stack.full_quotientStack_p`), and every system of objects of it is effective.
The lemma needs `A ≠ 0`, that is `1 ≤ dim A`; the corrected statement is
`Deformation.Artin.exists_nonEffectiveSystem_quotientStack_abelianVariety`.

## Main results

* `Deformation.Artin.isEffectiveSystem_quotientStack_zero`: for `A = 0`, every system of objects
  of `[Spec(k)/A]` is effective over every base cocone.
* `Deformation.Artin.not_exists_nonEffectiveSystem_quotientStack_zero`: the conclusion of
  Tag 0CXX fails for `A = 0`, over every field and every big fppf site.
* `Deformation.Artin.not_forall_exists_nonEffectiveSystem_quotientStack_zero`: **Tag 0CXX is
  false as printed**, refuted for `k` the algebraic closure of `ℚ`.

## References

* [Stacks Project, Tag 03RO](https://stacks.math.columbia.edu/tag/03RO)
* [Stacks Project, Tag 0CXT](https://stacks.math.columbia.edu/tag/0CXT)
* [Stacks Project, Tag 0CXX](https://stacks.math.columbia.edu/tag/0CXX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Deformation.Artin

universe u u₁ v₁

section Zero

open AlgebraicGeometry MonoidalCategory

variable (k : Type u) [Field k] (C : BigFppfSite.{u})
  (hk : C.Contains (Spec (CommRingCat.of k)))


/-- `Spec k` has exactly one point over every object of the big fppf site over `Spec k`: it is the
terminal object there. -/
public theorem subsingleton_fieldAsAlgebraicSpace_obj (T : (fppfOverField k C hk)ᵒᵖ) :
    Subsingleton ((fieldAsAlgebraicSpace k C hk).obj.obj T) :=
  ⟨fun a b => Over.mkIdTerminal.hom_ext a b⟩

/-- `Spec k` has a point over every object of the big fppf site over `Spec k`. -/
public theorem nonempty_fieldAsAlgebraicSpace_obj (T : (fppfOverField k C hk)ᵒᵖ) :
    Nonempty ((fieldAsAlgebraicSpace k C hk).obj.obj T) :=
  ⟨Over.mkIdTerminal.from _⟩

/-- The group algebraic space of the zero abelian variety over `k`: the trivial group over
`Spec k`. Its underlying sheaf is the functor of points of `Spec k` over itself, which is the
scheme underlying the zero abelian variety `𝟙_ (Over (Spec k))`. -/
public theorem tensorUnit_left_fieldAsAlgebraicSpace :
    (𝟙_ (Over (fieldAsAlgebraicSpace k C hk).obj)).left =
      yoneda.obj (Over.mk (𝟙 (C.obj hk))) :=
  rfl

/-- For the zero abelian variety `A = 0` over `k`, every system of objects of `[Spec(k)/A]` is
effective in the sense of Tag 0CXT, over every base cocone: `[Spec(k)/0]` is the base itself. -/
public theorem isEffectiveSystem_quotientStack_zero
    (Q : Space.ActionGroupoidConstruction (fieldAsAlgebraicSpace k C hk)
      (𝟙_ (Over (fieldAsAlgebraicSpace k C hk).obj))
      (𝟙_ (Over (fieldAsAlgebraicSpace k C hk).obj))
      (fieldAsAlgebraicSpace k C hk).property (fieldAsAlgebraicSpace k C hk).property)
    {J : Type u₁} [Category.{v₁} J] (ξ : J ⥤ (Stack.quotientStack Q.groupoid).obj)
    (c : Cocone (ξ ⋙ (Stack.quotientStack Q.groupoid).p)) :
    IsEffectiveSystem (Stack.quotientStack Q.groupoid).p ξ c :=
  Stack.isEffectiveSystem_quotientStack_trivialGroup
    (subsingleton_fieldAsAlgebraicSpace_obj k C hk) (nonempty_fieldAsAlgebraicSpace_obj k C hk)
    _ _ Q ξ c

/-- **Tag 0CXX is false for the zero abelian variety.** For `A = 0` over any field `k`, the
conclusion of Tag 0CXX fails: there is no inverse system of `k`-algebras with surjective,
locally nilpotent transition maps and system of objects of `[Spec(k)/A]` over the spectra of its
levels which is not effective, because every system of objects of `[Spec(k)/0]` is effective
(`Deformation.Artin.isEffectiveSystem_quotientStack_zero`). The zero group scheme is an abelian
variety in the sense of Tag 03RO (`AlgebraicGeometry.isAbelianVariety_tensorUnit`), so the
lemma needs the hypothesis `A ≠ 0`; see
`Deformation.Artin.not_forall_exists_nonEffectiveSystem_quotientStack_zero` for the refutation of
the statement as printed. -/
public theorem not_exists_nonEffectiveSystem_quotientStack_zero
    (Q : Space.ActionGroupoidConstruction (fieldAsAlgebraicSpace k C hk)
      (𝟙_ (Over (fieldAsAlgebraicSpace k C hk).obj))
      (𝟙_ (Over (fieldAsAlgebraicSpace k C hk).obj))
      (fieldAsAlgebraicSpace k C hk).property (fieldAsAlgebraicSpace k C hk).property) :
    ¬ ∃ (R : ℕᵒᵖ ⥤ CommAlgCat.{u} k) (cS : Cone R)
      (ξ : ℕ ⥤ (Stack.quotientStack Q.groupoid).obj)
      (c : Cocone (ξ ⋙ (Stack.quotientStack Q.groupoid).p))
      (f : ∀ n : ℕ, (schemeOverField k C hk).obj
        ((ξ ⋙ (Stack.quotientStack Q.groupoid).p).obj n) ≅ Spec (.of (R.obj (.op n))))
      (fL : (schemeOverField k C hk).obj c.pt ≅ Spec (.of cS.pt)),
      Nonempty (IsLimit cS) ∧
      (∀ {i j : ℕᵒᵖ} (g : i ⟶ j), Function.Surjective (R.map g).hom) ∧
      (∀ {i j : ℕᵒᵖ} (g : i ⟶ j),
        (RingHom.ker (R.map g).hom.toRingHom).LocallyNilpotent) ∧
      (∀ {i j : ℕ} (g : i ⟶ j), (schemeOverField k C hk).map
          ((ξ ⋙ (Stack.quotientStack Q.groupoid).p).map g) ≫ (f j).hom =
        (f i).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (R.map g.op).hom.toRingHom).op) ∧
      (∀ n : ℕ, (schemeOverField k C hk).map (c.ι.app n) ≫ fL.hom =
        (f n).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (cS.π.app (.op n)).hom.toRingHom).op) ∧
      (fL.inv ≫ C.inclusion.map c.pt.hom =
        Scheme.Spec.map (CommRingCat.ofHom (algebraMap k cS.pt)).op) ∧
      ¬ IsEffectiveSystem (Stack.quotientStack Q.groupoid).p ξ c := by
  rintro ⟨R, cS, ξ, c, f, fL, -, -, -, -, -, -, hne⟩
  exact hne (isEffectiveSystem_quotientStack_zero k C hk Q ξ c)

end Zero

section Refutation

open AlgebraicGeometry MonoidalCategory

/-- A field of characteristic zero has no finite subfield, so it is not algebraic over one: the
hypothesis of Tag 0CXX on `k` holds for every algebraically closed field of characteristic zero,
such as the algebraic closure of `ℚ`. -/
public theorem forall_finite_subfield_not_isAlgebraic_of_charZero (K : Type*) [Field K]
    [CharZero K] : ∀ F : Subfield K, Finite F → ¬ Algebra.IsAlgebraic F K := by
  intro F hF _
  have : CharZero F := ⟨fun m n h => by
    have := congrArg (fun x : F => (x : K)) h
    simpa using this⟩
  have := CharZero.infinite F
  exact not_finite F

/-- **Tag 0CXX is false as printed.** The source's statement is: for `k` an algebraically closed
field which is not the algebraic closure of a finite field, `A` an abelian variety over `k` and
`𝒳 = [Spec(k)/A]`, there are an inverse system of `k`-algebras `Rₙ` with surjective transition
maps whose kernels are locally nilpotent and a system `(ξₙ)` of objects of `𝒳` over
`(Spec(Rₙ))` which is not effective in the sense of Tag 0CXT. It fails for the zero abelian
variety `A = Spec k`, which is an abelian variety by Tag 03RO
(`AlgebraicGeometry.isAbelianVariety_tensorUnit`): its group algebraic space is the trivial group
`𝟙_` over `Spec k`, the quotient `[Spec(k)/0]` is the base itself, and every system of objects of
it is effective (`Deformation.Artin.isEffectiveSystem_quotientStack_zero`).

The statement refuted is the source's, read at `A = 0`, for every field `k` meeting the source's
hypotheses, every big fppf site containing `Spec k`, and every presentation of the action
groupoid of the trivial action; the counterexample is `k` the algebraic closure of `ℚ`, a site
supplied by `AlgebraicGeometry.BigFppfSite.exists_contains`, and the action groupoid of
`AlgebraicGeometry.Space.actionGroupoidConstruction`. The corrected statement assumes `1 ≤ dim A`
and is `Deformation.Artin.exists_nonEffectiveSystem_quotientStack_abelianVariety`. -/
@[stacks 0CXX "as printed it is false: the zero abelian variety A = Spec k (an abelian variety by \
  Tag 03RO) gives [Spec(k)/A] = Spec k, over which every system of objects is effective; refuted \
  for k the algebraic closure of Q. The corrected statement needs 1 ≤ dim A"]
public theorem not_forall_exists_nonEffectiveSystem_quotientStack_zero :
    ¬ ∀ (k : Type) [Field k] [IsAlgClosed k],
      (∀ F : Subfield k, Finite F → ¬ Algebra.IsAlgebraic F k) →
      ∀ (C : BigFppfSite.{0}) (hk : C.Contains (Spec (CommRingCat.of k)))
        (Q : Space.ActionGroupoidConstruction (fieldAsAlgebraicSpace k C hk)
          (𝟙_ (Over (fieldAsAlgebraicSpace k C hk).obj))
          (𝟙_ (Over (fieldAsAlgebraicSpace k C hk).obj))
          (fieldAsAlgebraicSpace k C hk).property (fieldAsAlgebraicSpace k C hk).property),
      ∃ (R : ℕᵒᵖ ⥤ CommAlgCat.{0} k) (cS : Cone R)
        (ξ : ℕ ⥤ (Stack.quotientStack Q.groupoid).obj)
        (c : Cocone (ξ ⋙ (Stack.quotientStack Q.groupoid).p))
        (f : ∀ n : ℕ, (schemeOverField k C hk).obj
          ((ξ ⋙ (Stack.quotientStack Q.groupoid).p).obj n) ≅ Spec (.of (R.obj (.op n))))
        (fL : (schemeOverField k C hk).obj c.pt ≅ Spec (.of cS.pt)),
        Nonempty (IsLimit cS) ∧
        (∀ {i j : ℕᵒᵖ} (g : i ⟶ j), Function.Surjective (R.map g).hom) ∧
        (∀ {i j : ℕᵒᵖ} (g : i ⟶ j),
          (RingHom.ker (R.map g).hom.toRingHom).LocallyNilpotent) ∧
        (∀ {i j : ℕ} (g : i ⟶ j), (schemeOverField k C hk).map
            ((ξ ⋙ (Stack.quotientStack Q.groupoid).p).map g) ≫ (f j).hom =
          (f i).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (R.map g.op).hom.toRingHom).op) ∧
        (∀ n : ℕ, (schemeOverField k C hk).map (c.ι.app n) ≫ fL.hom =
          (f n).hom ≫
            Scheme.Spec.map (CommRingCat.ofHom (cS.π.app (.op n)).hom.toRingHom).op) ∧
        (fL.inv ≫ C.inclusion.map c.pt.hom =
          Scheme.Spec.map (CommRingCat.ofHom (algebraMap k cS.pt)).op) ∧
        ¬ IsEffectiveSystem (Stack.quotientStack Q.groupoid).p ξ c := by
  intro h
  let k := AlgebraicClosure ℚ
  obtain ⟨C, hk⟩ := BigFppfSite.exists_contains (Spec (CommRingCat.of k))
  let B := fieldAsAlgebraicSpace k C hk
  exact not_exists_nonEffectiveSystem_quotientStack_zero k C hk _
    (h k (forall_finite_subfield_not_isAlgebraic_of_charZero k) C hk
      (Space.actionGroupoidConstruction B (𝟙_ (Over B.obj)) (𝟙_ (Over B.obj)) B.property
        B.property))

end Refutation

end Deformation.Artin
