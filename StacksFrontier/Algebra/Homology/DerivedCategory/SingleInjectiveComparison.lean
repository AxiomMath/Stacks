module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Abelian.Injective.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-!
# Comparing natural transformations into a homology functor

Let `A` and `D` be abelian categories, let `E : A ⥤ D` be an additive functor preserving finite
limits, let `q : ℤ` and let `α, β : P ⟶ homologyFunctor A (.up ℤ) q ⋙ E` be two natural
transformations out of a functor `P : CochainComplex A ℤ ⥤ D`. This file proves that if `A` has
enough injectives, if both `α` and `β` are invertible at every complex `J[-q]` concentrated in
degree `q` on an injective object, and if `β` is invertible at a complex `K`, then `α` is
invertible at `K` as well.

The point is that `α` need not be invertible on all of `CochainComplex A ℤ` for the conclusion
to hold at `K`: the two transformations are compared through a two-step injective resolution of
the single object `K.homology q`, which the functors `P` and `homologyFunctor ⋙ E` see as a
short exact sequence of their values.

## Main results

* `Stacks.HomologyComparison.isIso_app_of_exact_of_isIso`: the diagram lemma behind the
  comparison. Given `f : X ⟶ I` and `g : I ⟶ J` whose image under the target functor is a left
  exact short complex, invertibility of `β` at `X`, `I`, `J` and of `α` at `I`, `J` forces
  invertibility of `α` at `X`.
* `Stacks.HomologyComparison.exists_injective_homology_kernel`: every cochain complex `K` admits
  maps into, and between, two single complexes on injective objects which realize
  `K.homology q` as the kernel of a map of injectives.
* `Stacks.HomologyComparison.isIso_app_of_isIso_app_single_injective`: the comparison itself.
* `Stacks.HomologyComparison.isIso_map_limMap_of_isIso_whiskerRight`: a limit-preserving functor
  carries `limMap η` to an isomorphism as soon as `η` becomes invertible after whiskering.

## Implementation notes

`exists_injective_homology_kernel` produces the data as an existential rather than as a
structure: the two injectives it names are `Injective.under (K.homology q)` and
`Injective.under (cokernel (Injective.ι (K.homology q)))`, which carry no information beyond
the existence of the embedding, and no consumer needs the choice to be functorial.

The exactness hypothesis of `isIso_app_of_exact_of_isIso` is stated on the target functor only.
It is transported to the source functor along `β`, which is why `β` is required to be invertible
at all three objects while `α` is required to be invertible only at the two injective ones.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Stacks.HomologyComparison

/-- A comparison of two natural transformations at an object which the target functor presents
as the kernel of a map between two objects where both transformations are already invertible.

The short complex `Q.map f ⟶ Q.map g` is assumed left exact, and `β` is assumed invertible at
all three objects; `α` is then invertible at `X` as soon as it is invertible at `I` and `J`. -/
theorem isIso_app_of_exact_of_isIso
    {C D : Type*} [Category* C] [Category* D] [Abelian D]
    {P Q : C ⥤ D} (α β : P ⟶ Q) {X I J : C} (f : X ⟶ I) (g : I ⟶ J)
    [IsIso (β.app X)] [IsIso (β.app I)] [IsIso (β.app J)]
    [IsIso (α.app I)] [IsIso (α.app J)] [Mono (Q.map f)]
    (zero : Q.map f ≫ Q.map g = 0)
    (exact : (ShortComplex.mk (Q.map f) (Q.map g) zero).Exact) : IsIso (α.app X) := by
  have z : P.map f ≫ P.map g = 0 := by
    rw [← cancel_mono (β.app J), Category.assoc, β.naturality,
      ← Category.assoc, β.naturality, Category.assoc, zero, comp_zero, zero_comp]
  let S := ShortComplex.mk (P.map f) (P.map g) z
  let T := ShortComplex.mk (Q.map f) (Q.map g) zero
  let e : S ≅ T := ShortComplex.isoMk (asIso (β.app X))
    (asIso (β.app I)) (asIso (β.app J)) (β.naturality f).symm (β.naturality g).symm
  have hS : S.Exact := (ShortComplex.exact_iff_of_iso e).2 exact
  have : Mono (P.map f) := mono_of_mono_fac (β.naturality f)
  have hz : (Q.map f ≫ inv (α.app I)) ≫ P.map g = 0 := by
    rw [← cancel_mono (α.app J), Category.assoc, Category.assoc,
      α.naturality g, IsIso.inv_hom_id_assoc, zero, zero_comp]
  let t := hS.lift (Q.map f ≫ inv (α.app I)) hz
  have ht : t ≫ P.map f = Q.map f ≫ inv (α.app I) := hS.lift_f _ hz
  refine ⟨⟨t, ?_, ?_⟩⟩
  · apply (cancel_mono (P.map f)).1
    rw [Category.assoc, ht, ← Category.assoc, ← α.naturality f]
    simp
  · apply (cancel_mono (Q.map f)).1
    rw [Category.assoc, ← α.naturality f, ← Category.assoc, ht]
    simp

/-- A map from the degree-`q` homology of a cochain complex to an injective object is induced by
a map of complexes into the single complex on that object. -/
theorem exists_homToSingle_homologyMap
    {A : Type*} [Category* A] [Abelian A] (K : CochainComplex A ℤ)
    (q : ℤ) (J : A) [Injective J] (f : K.homology q ⟶ J) :
    ∃ g : K ⟶ (CochainComplex.singleFunctor A q).obj J,
      homologyMap g q ≫ (singleObjHomologySelfIso (.up ℤ) q J).hom = f := by
  let t := Injective.factorThru f (K.homologyι q)
  let g := mkHomToSingle (K.pOpcycles q ≫ t) (fun i hi => by simp)
  refine ⟨g, ?_⟩
  rw [← cancel_mono (singleObjOpcyclesSelfIso (.up ℤ) q J).hom, Category.assoc,
    singleObjHomologySelfIso_hom_singleObjOpcyclesSelfIso_hom,
    homologyι_naturality g q]
  have h : opcyclesMap g q = t ≫ (singleObjOpcyclesSelfIso (.up ℤ) q J).hom := by
    rw [← cancel_epi (K.pOpcycles q), p_opcyclesMap]
    dsimp [g]
    simp only [mkHomToSingle_f, Category.assoc]
    rw [← cancel_mono (singleObjOpcyclesSelfIso (.up ℤ) q J).inv]
    simp
  rw [h, ← Category.assoc, Injective.comp_factorThru]

/-- Composing the projection to a cokernel with a monomorphism out of it leaves the cokernel
sequence exact: `X ⟶ Y ⟶ Z` is exact whenever `Y ⟶ Z` is `cokernel.π f` followed by a
monomorphism. -/
theorem exact_cokernelπ_comp_mono {C : Type*} [Category* C] [Abelian C] {X Y Z : C}
    (f : X ⟶ Y) (i : cokernel f ⟶ Z) [Mono i] :
    (ShortComplex.mk f (cokernel.π f ≫ i)
      (by rw [← Category.assoc, cokernel.condition, zero_comp])).Exact := by
  rw [ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero, ← cancel_mono i, zero_comp,
    Category.assoc]
  exact kernel.condition _

/-- Every cochain complex maps to a single complex on an injective object, and on into a second
one, so that in degree-`q` homology the first map is a monomorphism and the resulting short
complex is exact. This realizes `K.homology q` as the kernel of a map of injective objects. -/
theorem exists_injective_homology_kernel
    {A : Type*} [Category* A] [Abelian A] [EnoughInjectives A]
    (K : CochainComplex A ℤ) (q : ℤ) :
    ∃ (I J : A) (_ : Injective I) (_ : Injective J)
      (f : K ⟶ (CochainComplex.singleFunctor A q).obj I)
      (g : (CochainComplex.singleFunctor A q).obj I ⟶
        (CochainComplex.singleFunctor A q).obj J)
      (zero : homologyMap f q ≫ homologyMap g q = 0),
      Mono (homologyMap f q) ∧
        (ShortComplex.mk (homologyMap f q) (homologyMap g q) zero).Exact := by
  let k := Injective.ι (K.homology q)
  let I := Injective.under (K.homology q)
  let J := Injective.under (cokernel k)
  obtain ⟨f, hf⟩ := exists_homToSingle_homologyMap K q I k
  let g := (CochainComplex.singleFunctor A q).map (cokernel.π k ≫ Injective.ι (cokernel k))
  let eI := singleObjHomologySelfIso (.up ℤ) q I
  let eJ := singleObjHomologySelfIso (.up ℤ) q J
  have hg : homologyMap g q ≫ eJ.hom = eI.hom ≫ cokernel.π k ≫ Injective.ι (cokernel k) := by
    simpa only [g, eI, eJ, CochainComplex.singleFunctor, CochainComplex.singleFunctors,
      Category.assoc] using
      singleObjHomologySelfIso_hom_naturality (.up ℤ) q
        (cokernel.π k ≫ Injective.ι (cokernel k))
  have z : homologyMap f q ≫ homologyMap g q = 0 := by
    rw [← cancel_mono eJ.hom, Category.assoc, hg, ← Category.assoc, ← Category.assoc, hf]
    simp [k]
  have : Mono (homologyMap f q) := mono_of_mono_fac hf
  refine ⟨I, J, inferInstance, inferInstance, f, g, z, inferInstance, ?_⟩
  let e : ShortComplex.mk (homologyMap f q) (homologyMap g q) z ≅
      ShortComplex.mk k (cokernel.π k ≫ Injective.ι (cokernel k))
        (by rw [← Category.assoc, cokernel.condition, zero_comp]) :=
    ShortComplex.isoMk (Iso.refl _) eI eJ (by simpa using hf.symm)
      (by simpa [Category.assoc] using hg.symm)
  exact (ShortComplex.exact_iff_of_iso e).2
    (exact_cokernelπ_comp_mono k (Injective.ι (cokernel k)))

/-- Two natural transformations into `homologyFunctor ⋙ E` which are both invertible at the
single complexes on injective objects agree, as to invertibility, at every cochain complex: if
one of them is invertible at `K`, so is the other.

`E` is required to be additive and to preserve finite limits, so that it carries the left exact
short complex of homology objects produced by `exists_injective_homology_kernel` to a left exact
short complex. -/
theorem isIso_app_of_isIso_app_single_injective
    {A D : Type*} [Category* A] [Abelian A] [EnoughInjectives A]
    [Category* D] [Abelian D]
    (E : A ⥤ D) [E.Additive] [PreservesFiniteLimits E]
    (q : ℤ) {P : CochainComplex A ℤ ⥤ D}
    (α β : P ⟶ HomologicalComplex.homologyFunctor A (.up ℤ) q ⋙ E)
    (hα : ∀ (J : A) [Injective J], IsIso (α.app ((CochainComplex.singleFunctor A q).obj J)))
    (hβ : ∀ (J : A) [Injective J], IsIso (β.app ((CochainComplex.singleFunctor A q).obj J)))
    (K : CochainComplex A ℤ) [IsIso (β.app K)] : IsIso (α.app K) := by
  obtain ⟨I, J, _, _, f, g, z, _, he⟩ := exists_injective_homology_kernel K q
  have := hα I
  have := hα J
  have := hβ I
  have := hβ J
  have z' : E.map (HomologicalComplex.homologyMap f q) ≫
      E.map (HomologicalComplex.homologyMap g q) = 0 := by rw [← E.map_comp, z, E.map_zero]
  have : Mono ((HomologicalComplex.homologyFunctor A (.up ℤ) q ⋙ E).map f) := by
    change Mono (E.map (HomologicalComplex.homologyMap f q))
    infer_instance
  exact isIso_app_of_exact_of_isIso α β f g z'
    (he.map_of_mono_of_preservesKernel E inferInstance inferInstance)

/-- A functor preserving limits of shape `J` carries `limMap η` to an isomorphism whenever `η`
becomes an isomorphism after whiskering with it. -/
theorem isIso_map_limMap_of_isIso_whiskerRight
    {C D J : Type*} [Category* C] [Category* D] [Category* J]
    [HasLimitsOfShape J C] [HasLimitsOfShape J D]
    (E : C ⥤ D) [PreservesLimitsOfShape J E] {F G : J ⥤ C}
    (η : F ⟶ G) [IsIso (Functor.whiskerRight η E)] : IsIso (E.map (limMap η)) := by
  have h := (preservesLimitNatIso E).hom.naturality η
  change E.map (limMap η) ≫ (preservesLimitIso E G).hom =
    (preservesLimitIso E F).hom ≫ limMap (Functor.whiskerRight η E) at h
  have : IsIso (E.map (limMap η) ≫ (preservesLimitIso E G).hom) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (preservesLimitIso E G).hom

end Stacks.HomologyComparison

end
