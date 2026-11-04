module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.Resolution
public import StacksFrontier.Cotangent.StandardResolution

/-!
# Base change of the standard resolution along an injective algebra map

For a composable pair of algebra maps `A → B → C`, the standard resolutions of `B` and `C` over
`A` determine an augmented simplicial `B`-algebra obtained by pushing out the former resolution
along its augmentation to `B`. Degreewise, this is `Qₙ ⊗_{Pₙ} B`, augmented to `C`. When
`B → C` is injective, every term of the standard resolution of `C` is moreover a polynomial
algebra over the corresponding term for `B`.

## Main definitions

* `CommAlgCat.baseChangedStandardResolution`: the augmented base-changed resolution.

## Main results

* `CommAlgCat.standardResolution_isPolynomialAlgebra`: the polynomial algebra structure in each
  simplicial degree.

## Implementation notes

The pushout is formed in simplicial commutative `A`-algebras, hence degreewise. Its canonical
map from the constant algebra `B` is converted to a simplicial `B`-algebra by the equivalence
between `B`-algebras and rings under `B`. The construction does not require `B → C` to be
injective; that hypothesis is used only for the polynomiality and resolution results.

The relative algebra structure for polynomiality is induced by the degreewise component of the
natural map of standard resolutions. Polynomiality uses the predicate
`CommAlgCat.IsPolynomialAlgebra`, which permits an arbitrary type of polynomial generators: in
degree `n` the generators are the elements of the degree-`n` term for `C` outside the image of
the degree-`n` term for `B`.

## References

* [Stacks Project, Tag 08SD](https://stacks.math.columbia.edu/tag/08SD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite Simplicial

universe u v

namespace CommAlgCat


/-- The standard resolution of `C` over `A`, base changed along the standard
resolution of `B` to give an augmented simplicial `B`-algebra. -/
@[stacks 08SD "base_changed_standard_resolution", implicit_reducible]
noncomputable def baseChangedStandardResolution
    (A : Type u) [CommRing A]
    {B C : CommAlgCat.{max u v} A} (f : B ⟶ C) :
    SimplicialObject.Augmented (CommAlgCat.{max u v} B) := by
  let F : CommAlgCat.{max u v} A ⥤ CommRingCat.{max u v} :=
    forget₂ (CommAlgCat.{max u v} A) CommRingCat.{max u v}
  let E := (commAlgCatEquivUnder (CommRingCat.of B)).inverse
  let P := standardResolution A B
  let Q := standardResolution A C
  let g := whiskerRight (((standardResolutionFunctor A).map f).left) F
  let h := whiskerRight P.hom F
  let k := whiskerRight Q.hom F
  let l := whiskerRight ((SimplicialObject.const _).map f) F
  let w : g ≫ k = h ≫ l := by
    dsimp [g, h, k, l, P, Q]
    exact congrArg (fun η => whiskerRight η F)
      (((standardResolutionFunctor A).map f).w)
  let a : pushout g h ⟶ (SimplicialObject.const _).obj C ⋙ F :=
    pushout.desc k l w
  let X : SimplexCategoryᵒᵖ ⥤ CommRingCat.{max u v} := pushout g h
  let s : (Functor.const SimplexCategoryᵒᵖ).obj (CommRingCat.of B) ⟶ X :=
    pushout.inr g h
  let U : SimplexCategoryᵒᵖ ⥤ Under (CommRingCat.of B) := Under.lift X s
  let Y : SimplexCategoryᵒᵖ ⥤ Under (CommRingCat.of B) :=
    (Functor.const SimplexCategoryᵒᵖ).obj
      (Under.mk (F.map f))
  let β : U ⟶ Y := {
    app := fun n => Under.homMk (a.app n) (by
      change (pushout.inr g h).app n ≫ a.app n = l.app n
      exact congrArg (fun η => η.app n) (pushout.inr_desc k l w))
    naturality := by
      intro i j m
      refine Comma.hom_ext _ _ ?_ ?_
      · rfl
      · change X.map m ≫ a.app j = a.app i
        exact (a.naturality m).trans (Category.comp_id _)
  }
  exact {
    left := U ⋙ E
    right := E.obj (Y.obj (op ⦋0⦌))
    hom := whiskerRight β E ≫ (Functor.constComp _ _ _).hom
  }



private lemma isPolynomialAlgebra_of_rename {A : Type u} [CommRing A] {R : Type v}
    {S : Type (max u v)}
    [CommRing R] [CommRing S] [Algebra A R] [Algebra A S]
    (g : R →ₐ[A] S) (hg : Function.Injective g) :
    letI : Algebra (MvPolynomial R A) (MvPolynomial S A) :=
      (MvPolynomial.rename g).toRingHom.toAlgebra
    ∃ ι : Type (max u v), Nonempty
      (MvPolynomial ι (MvPolynomial R A) ≃ₐ[MvPolynomial R A] MvPolynomial S A) := by
  let _ : Algebra (MvPolynomial R A) (MvPolynomial S A) :=
    (MvPolynomial.rename g).toRingHom.toAlgebra
  classical
  let U := {s : S // s ∉ Set.range g}
  let e : S ≃ U ⊕ R :=
    ((Equiv.Set.sumCompl (Set.range (g : R → S))).symm.trans
      (Equiv.sumComm (Set.range (g : R → S)) U)).trans
      (Equiv.sumCongr (Equiv.refl U) (Equiv.ofInjective g hg).symm)
  have he : e ∘ g = Sum.inr := by
    funext r
    simp [e, Equiv.Set.sumCompl_symm_apply_of_mem]
  let E : MvPolynomial S A ≃ₐ[A] MvPolynomial U (MvPolynomial R A) :=
    (MvPolynomial.renameEquiv A e).trans (MvPolynomial.sumAlgEquiv A U R)
  have hc : E.toAlgHom.comp (MvPolynomial.rename g) =
      IsScalarTower.toAlgHom A (MvPolynomial R A) (MvPolynomial U (MvPolynomial R A)) := by
    apply MvPolynomial.algHom_ext
    intro r
    rw [AlgHom.comp_apply, MvPolynomial.rename_X]
    show (MvPolynomial.sumAlgEquiv A U R)
      ((MvPolynomial.renameEquiv A e) (MvPolynomial.X (g r))) = _
    rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X,
      show e (g r) = Sum.inr r from congrFun he r]
    exact MvPolynomial.sumAlgEquiv_X_inr A U R r
  let E' : MvPolynomial S A ≃ₐ[MvPolynomial R A] MvPolynomial U (MvPolynomial R A) :=
    AlgEquiv.ofRingEquiv (f := E.toRingEquiv) (AlgHom.congr_fun hc)
  exact ⟨U, ⟨E'.symm⟩⟩

private theorem standardResolutionIterate_map_injective {A : Type u} [CommRing A]
    {B C : CommAlgCat.{max u v} A} (f : B ⟶ C) (hf : Function.Injective f.hom) :
    ∀ n : ℕ, Function.Injective ((((polynomialComonad A).toFunctor.iterate n).map f).hom) := by
  intro n
  induction n with
  | zero => exact hf
  | succ n ih => exact MvPolynomial.rename_injective _ ih

private theorem standardResolutionIterate_isPolynomialAlgebra {A : Type u} [CommRing A]
    {B C : CommAlgCat.{max u v} A} (f : B ⟶ C) (hf : Function.Injective f.hom) (n : ℕ) :
    let P := ((polynomialComonad A).toFunctor.iterate (n + 1)).obj B
    let Q := ((polynomialComonad A).toFunctor.iterate (n + 1)).obj C
    letI : Algebra P Q := ((((polynomialComonad A).toFunctor.iterate
      (n + 1)).map f).hom).toRingHom.toAlgebra
    IsPolynomialAlgebra P (CommAlgCat.of P Q) := by
  let R := ((polynomialComonad A).toFunctor.iterate n).obj B
  let S := ((polynomialComonad A).toFunctor.iterate n).obj C
  let g : R →ₐ[A] S := (((polynomialComonad A).toFunctor.iterate n).map f).hom
  let _ : Algebra (MvPolynomial R A) (MvPolynomial S A) :=
    (MvPolynomial.rename g).toRingHom.toAlgebra
  change ∃ ι, Nonempty
    (MvPolynomial ι (MvPolynomial R A) ≃ₐ[MvPolynomial R A] MvPolynomial S A)
  exact isPolynomialAlgebra_of_rename g (standardResolutionIterate_map_injective f hf n)


private theorem isPolynomialAlgebra_transport {A : Type u} [CommRing A]
    (P P' Q Q' : CommAlgCat.{max u v} A) (eP : P = P') (eQ : Q = Q')
    (f : P ⟶ Q) (g : P' ⟶ Q')
    (hm : f = eqToHom eP ≫ g ≫ eqToHom eQ.symm)
    (hp : (letI : Algebra P' Q' := g.hom.toRingHom.toAlgebra;
      IsPolynomialAlgebra P' (CommAlgCat.of P' Q'))) :
    (letI : Algebra P Q := f.hom.toRingHom.toAlgebra;
      IsPolynomialAlgebra P (CommAlgCat.of P Q)) := by
  cases eP
  cases eQ
  obtain rfl : f = g := by simpa using hm
  exact hp


private theorem standardResolution_map_eq_iterate_map {A : Type u} [CommRing A]
    {B C : CommAlgCat.{max u v} A} (f : B ⟶ C) (n : ℕ) :
    let eB := standardResolution_obj A B n
    let eC := standardResolution_obj A C n
    (((standardResolutionFunctor A).map f).left.app
      (Opposite.op (SimplexCategory.mk n))) =
      eqToHom eB ≫ (((polynomialComonad A).toFunctor.iterate (n + 1)).map f) ≫
        eqToHom eC.symm := by
  simpa [standardResolutionFunctor] using Functor.congr_hom (standardEndofunctor_obj A n) f


/-- Every term of the standard resolution of `C` is a polynomial algebra over
the corresponding term of the standard resolution of `B`, when `B → C` is injective. -/
@[stacks 08SD "polynomiality"]
theorem standardResolution_isPolynomialAlgebra
    (A : Type u) [CommRing A]
    {B C : CommAlgCat.{max u v} A} (f : B ⟶ C)
    (hf : Function.Injective f.hom) (n : SimplexCategoryᵒᵖ) :
    let P := (standardResolution A B).left.obj n
    let Q := (standardResolution A C).left.obj n
    letI : Algebra P Q :=
      (((standardResolutionFunctor A).map f).left.app n).hom.toAlgebra
    IsPolynomialAlgebra P (CommAlgCat.of P Q) := by
  let k := n.unop.len
  have hn : n = Opposite.op (SimplexCategory.mk k) := rfl
  have eB : (standardResolution A B).left.obj n =
      ((polynomialComonad A).toFunctor.iterate (k + 1)).obj B :=
    standardResolution_obj A B k
  have eC : (standardResolution A C).left.obj n =
      ((polynomialComonad A).toFunctor.iterate (k + 1)).obj C :=
    standardResolution_obj A C k
  let m := ((standardResolutionFunctor A).map f).left.app n
  let g := ((polynomialComonad A).toFunctor.iterate (k + 1)).map f
  have hm : m = eqToHom eB ≫ g ≫ eqToHom eC.symm := by
    simpa [m, g, hn] using standardResolution_map_eq_iterate_map f k
  exact isPolynomialAlgebra_transport _ _ _ _ eB eC m g hm
    (standardResolutionIterate_isPolynomialAlgebra f hf k)

end CommAlgCat

end
