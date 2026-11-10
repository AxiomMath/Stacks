module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import StacksFrontier.Algebra.Module.Adequate.LaurentDomainLift
public import StacksFrontier.Algebra.Module.Adequate.SplittingRepresentabilityDomain
public import StacksFrontier.Algebra.Module.Adequate.SplittingSymmetricDomain

/-!
# Tag 06V7 on a restricted domain of algebras

Let `A` be a ring and `Q` a property of commutative `A`-algebras. An extension

`0 → F → E → L → 0`

of module-valued functors defined on the full subcategory of algebras satisfying `Q`, with `L`
linearly adequate and `F` adequate, splits — provided the domain has a base algebra object and
is closed under the three constructions the argument evaluates at: the symmetric algebra of a
finitely generated module, the Laurent polynomial algebra, and the root extension of a
polynomial. This is [Stacks, Tag 06V7] on a restricted domain.

`StacksFrontier.Algebra.Module.Adequate.Splitting06V7Large` proves the same statement for functors
on all commutative `A`-algebras; that proof is left untouched, and nothing here depends on its
conclusion. The restricted-domain statement is *not* an instance of it: the middle term `E` of
the extension is an arbitrary functor on the domain, not the restriction of a functor on all
algebras, so the domain has to be carried through the whole argument rather than enlarged.

## Main results

* `AdequateFunctor.LaurentDomain.exists_retraction_of_shortExact_of_baseChange_weightOne` —
  the splitting, from the two properties of the kernel term that it uses.
* `AdequateFunctor.LaurentDomain.exists_retraction_of_shortExact` — [Stacks, Tag 06V7] on a
  restricted domain: an extension of a linearly adequate functor by an adequate functor on such
  a domain admits a retraction onto its kernel term.

## Implementation notes

The argument is the one of [Stacks, Tag 06V6]: present `L` as `Hom_A(M, -)`, lift the
tautological element to weight one in `E`, check additivity on the symmetric algebra of two
copies of `M`, and conclude with [Stacks, Tag 06V5] that the resulting transformation is a
morphism of module-valued functors.

Three closure hypotheses on `Q` are genuinely needed, one for each auxiliary algebra the
argument evaluates at.

* `hsym`, the symmetric algebra of a finitely generated module: the tautological element lives
  in `L(Sym_A M)` and the additivity check happens over `Sym_A (M × M)`.
* `hlau`, the Laurent polynomial algebra: the weight spaces of [Stacks, Tag 06UY] are defined
  by comparing two maps into `B[T, T⁻¹]`, and the decomposition of [Stacks, Tag 06UZ] needs the
  double Laurent algebra `B[T, T⁻¹][S, S⁻¹]` as well, so the closure is iterated — exactly as
  `AdequateFunctor.exists_lift_from_finite_free_kernel_on` iterates its own `hlau`.
* `hadj`, the root extension: [Stacks, Tag 06V5] turns the scalar `b` into a sum of two units
  after adjoining a root of `X ^ 2 - b X + 1`, and its flat-base-change obligation is consumed
  precisely at the morphism `B → AdjoinRoot (X ^ 2 - b X + 1)`. This one is not decoration: the
  object does not exist in the domain without it, and the descent cannot be stated.

A base algebra object is needed as well, but for a different reason: it is what makes extension
of scalars to the domain full, hence what lets the presenting morphism of a linearly adequate
functor be read off as a map of modules. That is the same use
`AdequateFunctor.exists_lift_from_finite_free_kernel_on` and
`AdequateFunctor.isAdequate_of_isLinearlyAdequate_on` make of it.

No `@[stacks]` attribute is placed here: the tagged statement of 06V7 is
`AdequateFunctor.exists_retraction_of_shortExact`, over all commutative algebras, and this is
that statement transported to a restricted domain.

## References

* [Stacks Project, Tag 06UZ](https://stacks.math.columbia.edu/tag/06UZ)
* [Stacks Project, Tag 06V5](https://stacks.math.columbia.edu/tag/06V5)
* [Stacks Project, Tag 06V6](https://stacks.math.columbia.edu/tag/06V6)
* [Stacks Project, Tag 06V7](https://stacks.math.columbia.edu/tag/06V7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AdequateFunctor.LaurentDomain

universe w v u

variable {A : Type u} [CommRing A] {Q : ObjectProperty (CommAlgCat.{max u v} A)}

/-! ### Closure hypotheses on the domain -/

/-- The domain contains the symmetric algebra of every finitely generated module. -/
public abbrev SymmetricAlgebraClosed (Q : ObjectProperty (CommAlgCat.{max u v} A)) : Prop :=
  ∀ (V : Type (max u v)) [AddCommGroup V] [Module A V] [Module.Finite A V],
    Q (CommAlgCat.of A (SymmetricAlgebra A V))

/-- The domain contains the Laurent polynomial algebra of each of its members. -/
public abbrev LaurentClosed (Q : ObjectProperty (CommAlgCat.{max u v} A)) : Prop :=
  ∀ (R : Type (max u v)) [CommRing R] [Algebra A R], Q (CommAlgCat.of A R) →
    Q (CommAlgCat.of A (LaurentPolynomial R))

/-- The domain contains the root extension of every polynomial over each of its members. -/
public abbrev AdjoinRootClosed (Q : ObjectProperty (CommAlgCat.{max u v} A)) : Prop :=
  ∀ (R : Type (max u v)) [CommRing R] [Algebra A R], Q (CommAlgCat.of A R) →
    ∀ p : Polynomial R,
      Q (@CommAlgCat.of A _ (AdjoinRoot p) _
        (RingHom.toAlgebra ((algebraMap R (AdjoinRoot p)).comp (algebraMap A R))))

/-! ### Reading the morphism carried by a morphism of the domain -/

/-- The morphism of the domain carried by the algebra map underlying a morphism of the domain is
that morphism. The subcategory is full, so this is a definitional identity; it is recorded so
that the two spellings can be exchanged by `rw`. -/
public lemma algMor_map_hom (Q : ObjectProperty (CommAlgCat.{max u v} A))
    {X Y : Q.FullSubcategory} (g : X ⟶ Y) :
    algMor Q (Q.ι.map g).hom X.property Y.property = g.op.op := rfl

/-- A linearly adequate module-valued functor on a domain of algebras with a base algebra object
is adequate. This is `AdequateFunctor.isAdequate_of_isLinearlyAdequate_on`, restated here so
that this file does not have to import the big-site machinery that states it. -/
private lemma isAdequate_of_isLinearlyAdequate (b : BaseAlgebraObject.{v} Q.ι)
    {L : ModuleValuedFunctorOn.{max u v w} Q.ι}
    (hL : IsLinearlyAdequate.{max u v w, v} Q.ι L) :
    IsAdequate.{max u v w, v} Q.ι L := by
  obtain ⟨n, m, f, ⟨e⟩⟩ := hL
  exact ⟨_, _, moduleHomOfExtensionNatTransOn.{max u v w} b f,
    ⟨e ≪≫ kernelIsoOfEq (moduleExtension_natTransOn_eq_map.{max u v w} b f)⟩⟩

/-! ### The section of the extension -/

/-- Given the representability of `L` by a finitely presented module, an extension of `L` on a
domain of algebras whose kernel term has the two properties of [Stacks, Tag 06V7] admits a
section. -/
private lemma exists_section_of_linearRepresentation
    {M : Type (max u v)} [AddCommGroup M] [Module A M] [Module.FinitePresentation A M]
    (hS : Q (CommAlgCat.of A (SymmetricAlgebra A M)))
    (hSL : Q (CommAlgCat.of A (LaurentPolynomial (SymmetricAlgebra A M))))
    (hSLL : Q (CommAlgCat.of A (LaurentPolynomial (LaurentPolynomial
      (SymmetricAlgebra A M)))))
    (hT : Q (CommAlgCat.of A (SymmetricAlgebra A (M × M))))
    (hTL : Q (CommAlgCat.of A (LaurentPolynomial (SymmetricAlgebra A (M × M)))))
    (hadj : AdjoinRootClosed.{v} Q)
    {F E L : ModuleValuedFunctorOn.{max u v w} Q.ι}
    (i : F ⟶ E) (p : E ⟶ L) (hip : i ≫ p = 0)
    (hSE : (ShortComplex.mk i p hip).ShortExact)
    (hflat : PreservesFlatBaseChange Q F)
    (hweight : HasWeightOneCoproduct.{w} Q F)
    (hE : PreservesFlatBaseChange Q E)
    (hLf : PreservesFlatBaseChange Q L)
    (e : ∀ (B : Type (max u v)) [CommRing B] [Algebra A B] (hB : Q (CommAlgCat.of A B)),
      L.obj (algObj Q B hB) ≃ₗ[B] (M →ₗ[A] B))
    (hnat : ∀ (B C : Type (max u v)) [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
      (f : B →ₐ[A] C) (hB : Q (CommAlgCat.of A B)) (hC : Q (CommAlgCat.of A C))
      (x : L.obj (algObj Q B hB)),
      e C hC (algebraMapValue L f hB hC x) = f.toLinearMap.comp (e B hB x)) :
    ∃ s : L ⟶ E, s ≫ p = 𝟙 L := by
  let ξ := (e (SymmetricAlgebra A M) hS).symm (SymmetricAlgebra.ι A M)
  have hξe (C : Type (max u v)) [CommRing C] [Algebra A C] (hC : Q (CommAlgCat.of A C))
      (f : SymmetricAlgebra A M →ₐ[A] C) :
      e C hC (algebraMapValue L f hS hC ξ) = f.toLinearMap.comp (SymmetricAlgebra.ι A M) := by
    rw [hnat _ _ f hS hC ξ, show e _ hS ξ = _ from (e _ hS).apply_symm_apply _]
  have hwξ : ξ ∈ weightSpace Q (SymmetricAlgebra A M) hS hSL L (symmetricPower A M) 1 := by
    change (LaurentPolynomial.T 1 : LaurentPolynomial (SymmetricAlgebra A M)) •
      algebraMapValue L (constantLaurentMapLarge A (SymmetricAlgebra A M)) hS hSL ξ =
      algebraMapValue L (gradedLaurentMapLarge A (SymmetricAlgebra A M)
        (symmetricPower A M)) hS hSL ξ
    apply (e (LaurentPolynomial (SymmetricAlgebra A M)) hSL).injective
    rw [map_smul, hξe _ hSL, hξe _ hSL]
    refine LinearMap.ext fun m => ?_
    change LaurentPolynomial.T 1 * LaurentPolynomial.C (SymmetricAlgebra.ι A M m) =
      gradedLaurentMapLarge A (SymmetricAlgebra A M) (symmetricPower A M)
        (SymmetricAlgebra.ι A M m)
    rw [gradedLaurentMapLarge_symmetricAlgebra_eq_degreeOne A M (symmetricPower A M)
      (symmetricAlgebra_generator_mem_symmetricPower_one A M),
      symmetricAlgebraLaurentDegreeOneMapLarge, SymmetricAlgebra.lift_ι_apply]
    exact mul_comm _ _
  have hp : Epi p := hSE.epi_g
  obtain ⟨θ, hθ, hpθ⟩ := exists_weightSpace_lift_of_epi hS hSL hSLL p hE hLf
    (symmetricPower A M) 1 ξ hwξ
  have hξadd : algebraMapValue L (symmetricMapLarge
        (LinearMap.inl A M M + LinearMap.inr A M M)) hS hT
          (p.app (algObj Q (SymmetricAlgebra A M) hS) θ) =
      algebraMapValue L (symmetricMapLarge (LinearMap.inl A M M)) hS hT
        (p.app (algObj Q (SymmetricAlgebra A M) hS) θ) +
      algebraMapValue L (symmetricMapLarge (LinearMap.inr A M M)) hS hT
        (p.app (algObj Q (SymmetricAlgebra A M) hS) θ) := by
    rw [hpθ]
    apply (e (SymmetricAlgebra A (M × M)) hT).injective
    rw [map_add, hξe _ hT, hξe _ hT, hξe _ hT]
    refine LinearMap.ext fun m => ?_
    change symmetricMapLarge _ (SymmetricAlgebra.ι A M m) =
      symmetricMapLarge _ (SymmetricAlgebra.ι A M m) +
        symmetricMapLarge _ (SymmetricAlgebra.ι A M m)
    simp only [symmetricMapLarge, SymmetricAlgebra.lift_ι_apply, LinearMap.comp_apply,
      LinearMap.add_apply, map_add]
  have hθadd := weightOne_lift_additive hS hSL hSLL hT hTL i p hip hSE hflat hweight hE
    θ hθ hξadd
  let s (D : Q.FullSubcategory) (x : L.obj (Opposite.op (Opposite.op D))) :
      E.obj (Opposite.op (Opposite.op D)) :=
    algebraMapValue E (SymmetricAlgebra.lift (e (D.obj : Type (max u v)) D.property x))
      hS D.property θ
  have hsadd (D : Q.FullSubcategory) (x y : L.obj (Opposite.op (Opposite.op D))) :
      s D (x + y) = s D x + s D y := by
    dsimp only [s]
    rw [map_add]
    exact evaluate_primitive_add hS hT D.property E θ hθadd _ _
  have hsnat (D D' : Q.FullSubcategory) (g : D ⟶ D')
      (x : L.obj (Opposite.op (Opposite.op D))) :
      s D' (algebraMapValue L (Q.ι.map g).hom D.property D'.property x) =
        algebraMapValue E (Q.ι.map g).hom D.property D'.property (s D x) := by
    dsimp only [s]
    rw [hnat (D.obj : Type (max u v)) (D'.obj : Type (max u v))
        (Q.ι.map g).hom D.property D'.property x,
      algebraMapValue_comp E
        (SymmetricAlgebra.lift (e (D.obj : Type (max u v)) D.property x))
        (Q.ι.map g).hom hS D.property D'.property]
    refine algebraMapValue_congr E (SymmetricAlgebra.algHom_ext (LinearMap.ext fun m => ?_))
      hS D'.property θ
    change SymmetricAlgebra.lift ((Q.ι.map g).hom.toLinearMap.comp
          (e (D.obj : Type (max u v)) D.property x)) (SymmetricAlgebra.ι A M m) =
      (Q.ι.map g).hom (SymmetricAlgebra.lift
        (e (D.obj : Type (max u v)) D.property x) (SymmetricAlgebra.ι A M m))
    simp only [SymmetricAlgebra.lift_ι_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  let φ : L.presheaf ⟶ E.presheaf :=
    { app X := AddCommGrpCat.ofHom (AddMonoidHom.mk' (s X.unop.unop) (hsadd X.unop.unop))
      naturality X Y f := by
        ext x
        exact hsnat X.unop.unop Y.unop.unop f.unop.unop x }
  obtain ⟨s', hs'⟩ :=
    naturalTransformation_lifts_of_units_of_flatBaseChange.{w, v, u} A Q hadj L E φ
      (by
        rintro ⟨⟨D⟩⟩ x a
        change Units (D.obj : Type (max u v)) at a
        change s D ((a : (D.obj : Type (max u v))) • x) =
          (a : (D.obj : Type (max u v))) • s D x
        dsimp only [s]
        rw [map_smul]
        exact weightOne_unit_evaluation hS hSL D.property E θ hθ _ a)
      (fun {D D'} f hf => hE _ _ D.unop.unop.property D'.unop.unop.property
        (Q.ι.map f.unop.unop).hom hf)
  refine ⟨s', ?_⟩
  ext D x
  have hsx := congrArg (fun τ => (τ.app D).hom x) hs'
  change s'.app D x = s D.unop.unop x at hsx
  change p.app D (s'.app D x) = x
  rw [hsx]
  change p.app (algObj Q (D.unop.unop.obj : Type (max u v)) D.unop.unop.property)
    (algebraMapValue E (SymmetricAlgebra.lift
      (e (D.unop.unop.obj : Type (max u v)) D.unop.unop.property x)) hS
        D.unop.unop.property θ) = x
  rw [algebraMapValue_naturality p (SymmetricAlgebra.lift
      (e (D.unop.unop.obj : Type (max u v)) D.unop.unop.property x)) hS
      D.unop.unop.property θ, hpθ]
  apply (e (D.unop.unop.obj : Type (max u v)) D.unop.unop.property).injective
  rw [hξe]
  exact SymmetricAlgebra.lift_comp_ι _

/-! ### Tag 06V7 on a restricted domain -/

/-- An extension of a linearly adequate module-valued functor on a domain of algebras splits if
its kernel functor commutes with flat base change inside the domain and has a direct weight-one
coproduct decomposition. Restricted-domain form of [Stacks, Tag 06V7]. -/
public theorem exists_retraction_of_shortExact_of_baseChange_weightOne
    (b : BaseAlgebraObject.{v} Q.ι)
    (hsym : SymmetricAlgebraClosed.{v} Q) (hlau : LaurentClosed.{v} Q)
    (hadj : AdjoinRootClosed.{v} Q)
    {F E L : ModuleValuedFunctorOn.{max u v w} Q.ι}
    (i : F ⟶ E) (p : E ⟶ L) (hip : i ≫ p = 0)
    (hSE : (ShortComplex.mk i p hip).ShortExact)
    (hflat : PreservesFlatBaseChange Q F)
    (hweight : HasWeightOneCoproduct.{w} Q F)
    (hL : IsLinearlyAdequate.{max u v w, v} Q.ι L) :
    ∃ r : E ⟶ F, i ≫ r = 𝟙 F := by
  obtain ⟨M, hMadd, hMmod, hMfp, e, he⟩ :=
    exists_linearRepresentation_smallCarrier.{u, v, w} b L hL
  have hS : Q (CommAlgCat.of A (SymmetricAlgebra A M)) := hsym M
  have hSL : Q (CommAlgCat.of A (LaurentPolynomial (SymmetricAlgebra A M))) := hlau _ hS
  have hSLL : Q (CommAlgCat.of A (LaurentPolynomial (LaurentPolynomial
    (SymmetricAlgebra A M)))) := hlau _ hSL
  have hT : Q (CommAlgCat.of A (SymmetricAlgebra A (M × M))) := hsym (M × M)
  have hTL : Q (CommAlgCat.of A (LaurentPolynomial (SymmetricAlgebra A (M × M)))) :=
    hlau _ hT
  have hLf := adequate_preservesFlatBaseChange.{w} L (isAdequate_of_isLinearlyAdequate.{w} b hL)
  obtain ⟨s, hs⟩ := exists_section_of_linearRepresentation.{w} hS hSL hSLL hT hTL hadj
    i p hip hSE hflat hweight (preservesFlatBaseChange_of_shortExact _ hSE hflat hLf) hLf
    (fun B _ _ hB => e ⟨CommAlgCat.of A B, hB⟩)
    (fun B C _ _ _ _ f hB hC x =>
      he ⟨CommAlgCat.of A B, hB⟩ ⟨CommAlgCat.of A C, hC⟩
        (ObjectProperty.homMk (CommAlgCat.ofHom f)) x)
  let splitting := ShortComplex.Splitting.ofExactOfSection _ hSE.exact s hs hSE.mono_f
  exact ⟨splitting.r, splitting.f_r⟩

/-- **Stacks 06V7 on a restricted domain of algebras.** An extension of a linearly adequate
module-valued functor by an adequate one, on a domain of algebras with a base algebra object
closed under symmetric algebras, Laurent polynomial algebras and root extensions, admits a
retraction onto its kernel term.

An adequate functor commutes with flat base change inside the domain by [Stacks, Tag 06UW], and
its weight-one part decomposes by [Stacks, Tag 06UZ], which are the only two properties of the
kernel term the splitting uses. -/
public theorem exists_retraction_of_shortExact (b : BaseAlgebraObject.{v} Q.ι)
    (hsym : SymmetricAlgebraClosed.{v} Q) (hlau : LaurentClosed.{v} Q)
    (hadj : AdjoinRootClosed.{v} Q)
    {F E L : ModuleValuedFunctorOn.{max u v w} Q.ι}
    (i : F ⟶ E) (p : E ⟶ L) (hip : i ≫ p = 0)
    (hSE : (ShortComplex.mk i p hip).ShortExact)
    (hF : IsAdequate.{max u v w, v} Q.ι F)
    (hL : IsLinearlyAdequate.{max u v w, v} Q.ι L) :
    ∃ r : E ⟶ F, i ≫ r = 𝟙 F :=
  exists_retraction_of_shortExact_of_baseChange_weightOne.{w} b hsym hlau hadj i p hip hSE
    (adequate_preservesFlatBaseChange.{w} F hF)
    (adequate_hasWeightOneCoproduct.{w} hlau F hF) hL

end AdequateFunctor.LaurentDomain

end
