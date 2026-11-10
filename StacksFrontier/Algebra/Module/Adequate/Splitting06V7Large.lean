module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import StacksFrontier.Algebra.Module.Adequate.LaurentLargeLift
public import StacksFrontier.Algebra.Module.Adequate.SplittingSymmetricLarge

/-!
# Tag 06V7: splitting an extension of a linearly adequate functor, at independent universes

Let `A` be a ring. An extension

`0 → F → E → L → 0`

of module-valued functors on the commutative `A`-algebras with `L` linearly adequate splits,
provided `F` commutes with flat base change and its weight-one part on the symmetric algebra of
two copies of a finitely presented module decomposes as the direct sum of the two factor
images. This is Stacks 06V7, and it is proved here with the algebra carriers and the module
values in universes independent of the base ring: the algebras are objects of
`CommAlgCat.{max u v} A` and the values lie in `Type (max u v w)`, which is the universe
discipline of `AdequateFunctor.ModuleValuedFunctor.{max u v w, v} A`.

`StacksFrontier.Algebra.Module.Adequate.Splitting` proves the same statements at the diagonal
`ModuleValuedFunctor.{u, u} A`; that proof is left untouched, and nothing here depends on it.

## Main results

* `AdequateFunctor.exists_retraction_of_shortExact_of_baseChange_weightOne_large`
  (Stacks 06V7): the splitting, from the two properties of the kernel term that it uses.
* `AdequateFunctor.exists_retraction_of_shortExact_large` (Stacks 06V7): an extension of a
  linearly adequate functor by an adequate functor admits a retraction onto its kernel term.

## Implementation notes

The argument is the one of Stacks 06V6: present `L` as `Hom_A(M, -)`, lift the tautological
element to weight one in `E`, check additivity on the symmetric algebra of two copies of `M`,
and conclude with Stacks 06V5 that the resulting transformation is a morphism of module-valued
functors.

One step is invisible at the diagonal. The representability statement
`AdequateFunctor.exists_linearRepresentation_large` produces its module in
`Type (max u v w)` — it is a quotient of the dual of `finiteFreeModule.{max u v w} A n` — but
the splitting argument evaluates `E` and `L` at `SymmetricAlgebra A M`, which must be an object
of `CommAlgCat.{max u v} A`, so `M` has to have a carrier in `Type (max u v)`. The two demands
are compatible because `M` is finitely presented, hence a quotient of a finite free module, and
`Module.FinitePresentation.equiv_quotient` realises it on a carrier in any universe containing
that of `A`. `AdequateFunctor.exists_linearRepresentation_smallCarrier_large` performs that
transport; the comparison is a linear equivalence between modules in two different universes,
which `LinearEquiv` allows, so nothing is lost. At the diagonal all three universes agree and
the step is a no-op, which is why the original proof does not contain it.

The weight-one coproduct is consumed at `HasWeightOneCoproductLarge.{u, max u v, w}`: the
module it quantifies over has to be the transported one, whose carrier is in
`Type (max u v)`. The predicate's own universe arguments only ever occur as `max u v` and
`max u v w`, so that instantiation is the same statement at a carrier universe large enough to
hold the transported module, and `adequate_hasWeightOneCoproduct_large` supplies it.

## References

* [Stacks Project, Tag 06V7](https://stacks.math.columbia.edu/tag/06V7)
* [Stacks Project, Tag 06V6](https://stacks.math.columbia.edu/tag/06V6)
* [Stacks Project, Tag 06V5](https://stacks.math.columbia.edu/tag/06V5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v w uM uN uB

namespace AdequateFunctor

/-! ### Transporting the representing module to a smaller carrier -/

/-- Precomposition with an `A`-linear equivalence, as a `B`-linear equivalence between the
`A`-linear duals valued in `B`. The two modules may live in different universes. -/
public noncomputable def homCongrLeftLarge {A : Type u} [CommRing A]
    {M : Type uM} {N : Type uN} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (eqv : N ≃ₗ[A] M) (B : Type uB) [CommRing B] [Algebra A B] :
    (M →ₗ[A] B) ≃ₗ[B] (N →ₗ[A] B) where
  toFun g := g.comp eqv.toLinearMap
  map_add' g h := by ext n; rfl
  map_smul' c g := by ext n; rfl
  invFun g := g.comp eqv.symm.toLinearMap
  left_inv g := by ext m; simp
  right_inv g := by ext n; simp

/-- `AdequateFunctor.exists_linearRepresentation_large` with the representing module placed on
a carrier in `Type (max u v)`, so that its symmetric algebra is an object of
`CommAlgCat.{max u v} A`.

The module produced by the representability statement lies in `Type (max u v w)`, which is the
universe its construction as a quotient of a dual of `finiteFreeModule.{max u v w} A n`
dictates; being finitely presented it is also realised on a carrier in `Type (max u v)`, and
the comparison `L(B) ≃ₗ[B] Hom_A(M, B)` crosses that universe gap without loss. -/
public lemma exists_linearRepresentation_smallCarrier_large {A : Type u} [CommRing A]
    (L : ModuleValuedFunctor.{max u v w, v} A) (hL : IsLinearlyAdequate (𝟭 _) L) :
    ∃ (M : Type (max u v)) (_ : AddCommGroup M) (_ : Module A M),
      Module.FinitePresentation A M ∧
      ∃ e : ∀ B : CommAlgCat.{max u v} A, algebraValueLarge L B ≃ₗ[B] (M →ₗ[A] B),
        ∀ (B C : CommAlgCat.{max u v} A) (f : B ⟶ C) (x : algebraValueLarge L B),
          e C (algebraMapValueLarge L f.hom x) = f.hom.toLinearMap.comp (e B x) := by
  obtain ⟨M, hMadd, hMmod, hMfp, e, he⟩ := exists_linearRepresentation_large.{u, v, w} L hL
  let := hMadd
  let := hMmod
  let := hMfp
  have : Small.{max u v} A := small_lift.{u, max u v} A
  obtain ⟨N, hNadd, hNmod, K, eqv, -, -, -⟩ :
      ∃ (N : Type (max u v)) (_ : AddCommGroup N) (_ : Module A N) (K : Submodule A N)
        (_ : M ≃ₗ[A] N ⧸ K), Module.Free A N ∧ Module.Finite A N ∧ K.FG :=
    Module.FinitePresentation.equiv_quotient A M
  let := hNadd
  let := hNmod
  refine ⟨N ⧸ K, inferInstance, inferInstance, Module.FinitePresentation.of_equiv eqv,
    fun B => (e B).trans (homCongrLeftLarge eqv.symm (B : Type (max u v))), ?_⟩
  intro B C f x
  change (e C (algebraMapValueLarge L f.hom x)).comp eqv.symm.toLinearMap =
    f.hom.toLinearMap.comp ((e B x).comp eqv.symm.toLinearMap)
  rw [he B C f x, LinearMap.comp_assoc]

/-! ### The section of the extension -/

/-- Given the representability of `L` by a finitely presented module, an extension of `L`
whose kernel term has the two properties of Stacks 06V7 admits a section.
Independent-universe form. -/
public lemma exists_section_of_linearRepresentation_large {A : Type u} {M : Type v}
    [CommRing A] [AddCommGroup M] [Module A M] [Module.FinitePresentation A M]
    {F E L : ModuleValuedFunctor.{max u v w, v} A}
    (i : F ⟶ E) (p : E ⟶ L) (hip : i ≫ p = 0)
    (hS : (ShortComplex.mk i p hip).ShortExact)
    (hflat : LaurentLarge.PreservesFlatBaseChange.{u, max u v, max u v w} A F)
    (hweight : HasWeightOneCoproductLarge.{u, v, w} F)
    (hE : LaurentLarge.PreservesFlatBaseChange.{u, max u v, max u v w} A E)
    (hL : LaurentLarge.PreservesFlatBaseChange.{u, max u v, max u v w} A L)
    (e : ∀ B : CommAlgCat.{max u v} A, algebraValueLarge L B ≃ₗ[B] (M →ₗ[A] B))
    (hnat : ∀ (B C : CommAlgCat.{max u v} A) (f : B ⟶ C) (x : algebraValueLarge L B),
      e C (algebraMapValueLarge L f.hom x) = f.hom.toLinearMap.comp (e B x)) :
    ∃ s : L ⟶ E, s ≫ p = 𝟙 L := by
  let B := CommAlgCat.of A (SymmetricAlgebra A M)
  let C := CommAlgCat.of A (SymmetricAlgebra A (M × M))
  let ξ := (e B).symm (SymmetricAlgebra.ι A M)
  have heξ : e B ξ = SymmetricAlgebra.ι A M := (e B).apply_symm_apply _
  have key (D : CommAlgCat.{max u v} A) (g : B ⟶ D) :
      e D (algebraMapValueLarge L g.hom ξ) = g.hom.toLinearMap.comp (SymmetricAlgebra.ι A M) := by
    rw [hnat, heξ]
  have hwξ : ξ ∈ LaurentLarge.weightSpace A (SymmetricAlgebra A M) L
      (symmetricPower A M) 1 := by
    change (LaurentPolynomial.T 1 : LaurentPolynomial (SymmetricAlgebra A M)) •
      algebraMapValueLarge L (constantLaurentMapLarge A (SymmetricAlgebra A M)) ξ =
      algebraMapValueLarge L (gradedLaurentMapLarge A (SymmetricAlgebra A M)
        (symmetricPower A M)) ξ
    apply (e (CommAlgCat.of A (LaurentPolynomial (SymmetricAlgebra A M)))).injective
    rw [map_smul, key _ (CommAlgCat.ofHom (constantLaurentMapLarge A _)),
      key _ (CommAlgCat.ofHom (gradedLaurentMapLarge A _ _))]
    apply LinearMap.ext
    intro m
    change LaurentPolynomial.T 1 * LaurentPolynomial.C (SymmetricAlgebra.ι A M m) =
      gradedLaurentMapLarge A (SymmetricAlgebra A M) (symmetricPower A M)
        (SymmetricAlgebra.ι A M m)
    rw [gradedLaurentMapLarge_symmetricAlgebra_eq_degreeOne A M (symmetricPower A M)
      (symmetricAlgebra_generator_mem_symmetricPower_one A M),
      symmetricAlgebraLaurentDegreeOneMapLarge, SymmetricAlgebra.lift_ι_apply]
    exact mul_comm _ _
  have hp : Epi p := hS.epi_g
  obtain ⟨θ, hθ, hpθ⟩ := exists_weightSpace_lift_of_epi_large p hE hL
    (symmetricPower A M) 1 ξ hwξ
  have hξadd : algebraMapValueLarge L (symmetricMapLarge
        (LinearMap.inl A M M + LinearMap.inr A M M)) (p.app _ θ) =
      algebraMapValueLarge L (symmetricMapLarge (LinearMap.inl A M M)) (p.app _ θ) +
      algebraMapValueLarge L (symmetricMapLarge (LinearMap.inr A M M)) (p.app _ θ) := by
    rw [hpθ]
    apply (e C).injective
    rw [map_add, key C (CommAlgCat.ofHom (symmetricMapLarge _)),
      key C (CommAlgCat.ofHom (symmetricMapLarge _)),
      key C (CommAlgCat.ofHom (symmetricMapLarge _))]
    apply LinearMap.ext
    intro m
    change symmetricMapLarge _ (SymmetricAlgebra.ι A M m) =
      symmetricMapLarge _ (SymmetricAlgebra.ι A M m) +
        symmetricMapLarge _ (SymmetricAlgebra.ι A M m)
    simp only [symmetricMapLarge, SymmetricAlgebra.lift_ι_apply, LinearMap.comp_apply,
      LinearMap.add_apply, map_add]
  have hθadd := weightOne_lift_additive_large i p hip hS hflat hweight hE θ hθ hξadd
  let s (D : CommAlgCat.{max u v} A) (x : algebraValueLarge L D) : algebraValueLarge E D :=
    algebraMapValueLarge E (SymmetricAlgebra.lift (e D x)) θ
  have hsadd (D : CommAlgCat.{max u v} A) (x y : algebraValueLarge L D) :
      s D (x + y) = s D x + s D y := by
    dsimp only [s]
    rw [map_add]
    exact evaluate_primitive_add_large E θ hθadd _ _
  have hsnat (D D' : CommAlgCat.{max u v} A) (f : D ⟶ D') (x : algebraValueLarge L D) :
      s D' (algebraMapValueLarge L f.hom x) = algebraMapValueLarge E f.hom (s D x) := by
    dsimp only [s]
    rw [hnat, algebraMapValueLarge_comp]
    have hh : SymmetricAlgebra.lift (f.hom.toLinearMap.comp (e D x)) =
        f.hom.comp (SymmetricAlgebra.lift (e D x)) := by
      ext m
      simp
    rw [hh]
  let φ : L.presheaf ⟶ E.presheaf :=
    { app X := AddCommGrpCat.ofHom (AddMonoidHom.mk' (s X.unop.unop) (hsadd X.unop.unop))
      naturality := by
        intro X Y f
        ext x
        exact hsnat X.unop.unop Y.unop.unop f.unop.unop x }
  obtain ⟨s', hs'⟩ :=
    AdequateFunctor.Laurent.naturalTransformation_lifts_of_units_of_flatBaseChange_large.{w, v, u}
      A L E φ
      (by
        intro D x a
        rcases D with ⟨⟨D⟩⟩
        change Units D at a
        change s D ((a : D) • x) = (a : D) • s D x
        dsimp only [s]
        rw [map_smul]
        exact weightOne_unit_evaluation_large E θ hθ _ a)
      (by
        intro D D' f hf
        exact hE D.unop.unop D'.unop.unop f.unop.unop.hom hf)
  refine ⟨s', ?_⟩
  ext D x
  have hsx := congrArg (fun τ => (τ.app D).hom x) hs'
  change s'.app D x = s D.unop.unop x at hsx
  change p.app D (s'.app D x) = x
  rw [hsx]
  change p.app D (algebraMapValueLarge E
    (SymmetricAlgebra.lift (e D.unop.unop x)) θ) = x
  rw [algebraMapValueLarge_naturality, hpθ]
  apply (e D.unop.unop).injective
  rw [key D.unop.unop (CommAlgCat.ofHom (SymmetricAlgebra.lift (e D.unop.unop x)))]
  exact SymmetricAlgebra.lift_comp_ι _

/-! ### Tag 06V7 -/

/-- An extension of a linearly adequate functor splits if its kernel functor commutes with
flat base change and has a direct weight-one coproduct decomposition. Independent-universe
form of [Stacks, Tag 06V7]. -/
public lemma exists_retraction_of_shortExact_of_baseChange_weightOne_large
    {A : Type u} [CommRing A]
    {F E L : ModuleValuedFunctor.{max u v w, v} A}
    (i : F ⟶ E) (p : E ⟶ L) (hip : i ≫ p = 0)
    (hS : (ShortComplex.mk i p hip).ShortExact)
    (hflat : LaurentLarge.PreservesFlatBaseChange.{u, max u v, max u v w} A F)
    (hweight : HasWeightOneCoproductLarge.{u, max u v, w} F)
    (hL : IsLinearlyAdequate (𝟭 _) L) :
    ∃ r : E ⟶ F, i ≫ r = 𝟙 F := by
  obtain ⟨M, hMadd, hMmod, hMfp, e, he⟩ :=
    exists_linearRepresentation_smallCarrier_large.{u, v, w} L hL
  let := hMadd
  let := hMmod
  let := hMfp
  have hLa : IsAdequate (𝟭 _) L := by
    obtain ⟨n, m, f, hf⟩ := (isLinearlyAdequate_iff L).mp hL
    exact (isAdequate_iff L).mpr ⟨_, _, f, hf⟩
  have hLf := adequate_preservesFlatBaseChange_large.{u, v, w} L hLa
  obtain ⟨s, hs⟩ := exists_section_of_linearRepresentation_large.{u, max u v, w}
    i p hip hS hflat hweight
    (preservesFlatBaseChange_of_shortExact_large.{u, v, w} (ShortComplex.mk i p hip) hS hflat hLf)
    hLf e he
  exact ⟨_, (ShortComplex.Splitting.ofExactOfSection _ hS.exact s hs hS.mono_f).f_r⟩

/-- **Stacks 06V7** at independent universes. An extension of a linearly adequate functor by an
adequate functor admits a retraction onto its kernel term. An adequate functor commutes with
flat base change by Stacks 06UW, and its weight-one part decomposes by Stacks 06UZ, which are
the only two properties of the kernel term the splitting uses. -/
public lemma exists_retraction_of_shortExact_large {A : Type u} [CommRing A]
    {F E L : ModuleValuedFunctor.{max u v w, v} A}
    (i : F ⟶ E) (p : E ⟶ L) (hip : i ≫ p = 0)
    (hS : (ShortComplex.mk i p hip).ShortExact)
    (hF : IsAdequate (𝟭 _) F)
    (hL : IsLinearlyAdequate (𝟭 _) L) :
    ∃ r : E ⟶ F, i ≫ r = 𝟙 F :=
  exists_retraction_of_shortExact_of_baseChange_weightOne_large i p hip hS
    (adequate_preservesFlatBaseChange_large.{u, v, w} F hF)
    (adequate_hasWeightOneCoproduct_large.{u, max u v, w} F hF) hL

end AdequateFunctor

end
