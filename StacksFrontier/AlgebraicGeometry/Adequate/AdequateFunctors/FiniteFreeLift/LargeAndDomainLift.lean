module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.FiniteFreeLift.SmallLift

/-!
# Tag 06V0 in a larger universe and on a restricted domain of algebras

This file is the last part of
`StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.FiniteFreeLift`. It proves the
lifting property of Tag 06V0 for a module in a universe containing the ring's, giving
`AdequateFunctor.exists_lift_from_finite_free_kernel`, and carries the argument to the
module-valued functors on a domain of algebras, giving
`AdequateFunctor.exists_lift_from_finite_free_kernel_on`.

## References

* [Stacks Project, Tag 06V0](https://stacks.math.columbia.edu/tag/06V0)
-/

@[expose] public section

open CategoryTheory
universe w v u z u₁ v₁

namespace AdequateFunctor


open scoped DirectSum
open TensorProduct

/-- An element of the universal solution algebra tensored with `M` on which the graded and
constant Laurent maps differ by the weight `T` is a tuple combination of the universal
variables. -/
private lemma exists_tuple_of_weightOne (A : Type u) [CommRing A]
    (M : Type (max u w)) [AddCommGroup M] [Module A M] {n m : ℕ}
    (f : (Fin n → A) →ₗ[A] (Fin m → A))
    (y : TensorProduct A (universalSolutionAlgebraLifted.{v} A f) M)
    (hyWeight : (LaurentPolynomial.T (1 : ℤ) :
        LaurentPolynomial (universalSolutionAlgebraLifted.{v} A f)) •
        (TensorProduct.map
          (constantLaurentMapLarge A (universalSolutionAlgebraLifted.{v} A f)).toLinearMap
          LinearMap.id) y =
      (TensorProduct.map (gradedLaurentMapLarge A (universalSolutionAlgebraLifted.{v} A f)
        (symmetricPower A (ULift.{v} (universalSolutionModule A f)))).toLinearMap
        LinearMap.id) y) :
    ∃ mvec : Fin n → M,
      y = ∑ i, universalSolutionVariableLifted A f i ⊗ₜ[A] mvec i := by
  have hyDegree := moduleExtension_weightOne_mem_degreeOne_large A
    (universalSolutionAlgebraLifted.{v} A f) M
    (symmetricPower A (ULift.{v} (universalSolutionModule A f)))
    (fun d x hx => gradedLaurentMapLarge_mem A _
      (symmetricPower A (ULift.{v} (universalSolutionModule A f))) d x hx) y hyWeight
  let vars := universalSolutionVariableLifted A f
  rw [DirectSum.decomposeTensor_apply] at hyDegree
  obtain ⟨z, hz⟩ := hyDegree
  let Q := ULift (universalSolutionModule A f)
  let q : (Fin n → A) →ₗ[A] Q :=
    (ULift.moduleEquiv.{u, u, v}.symm.toLinearMap).comp
      (Submodule.mkQ (LinearMap.range (transposeLinearMap A f)))
  let ρ : Q →ₗ[A] ↥(symmetricPower A Q 1) :=
    (SymmetricAlgebra.ι A Q).codRestrict _ (fun a => by
      simp [symmetricPower])
  have hρ : Function.Surjective ρ := by
    intro z
    have hz' : (z : SymmetricAlgebra A Q) ∈ LinearMap.range (SymmetricAlgebra.ι A Q) := by
      simpa [symmetricPower] using z.property
    obtain ⟨a, ha⟩ := LinearMap.mem_range.mp hz'
    exact ⟨a, Subtype.ext ha⟩
  obtain ⟨zQ, hzQ⟩ := TensorProduct.map_surjective hρ
    (g' := LinearMap.id) (fun x : M => ⟨x, rfl⟩) z
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨a, ha⟩ := Submodule.mkQ_surjective (LinearMap.range (transposeLinearMap A f)) x.down
    refine ⟨a, ?_⟩
    dsimp [q]
    apply ULift.ext
    exact ha
  obtain ⟨zV, hzV⟩ := TensorProduct.map_surjective hq
    (g' := LinearMap.id) (fun x : M => ⟨x, rfl⟩) zQ
  let mvec : Fin n → M := TensorProduct.piScalarRight A A M (Fin n)
    (TensorProduct.comm A (Fin n → A) M zV)
  have hmvec : mvec = ∑ i, Pi.single i (mvec i) := by
    ext i
    simp [Pi.single_apply]
  have hcomm : TensorProduct.comm A (Fin n → A) M zV =
      (TensorProduct.piScalarRight A A M (Fin n)).symm mvec := by
    dsimp [mvec]
    exact ((TensorProduct.piScalarRight A A M (Fin n)).symm_apply_apply _).symm
  have hzVrep : zV = ∑ i, Pi.single i 1 ⊗ₜ[A] mvec i := by
    apply (TensorProduct.comm A (Fin n → A) M).injective
    rw [hcomm, hmvec]
    simp [TensorProduct.piScalarRight_symm_single]
  have hz' : z = TensorProduct.map ρ LinearMap.id
      (TensorProduct.map q LinearMap.id zV) := by
    calc
      z = TensorProduct.map ρ LinearMap.id zQ := hzQ.symm
      _ = TensorProduct.map ρ LinearMap.id (TensorProduct.map q LinearMap.id zV) :=
        congrArg (TensorProduct.map ρ LinearMap.id) hzV.symm
  have hcomp : ((symmetricPower A Q 1).subtype.comp ρ).comp q =
      (SymmetricAlgebra.ι A Q).comp q := by
    ext a
    rfl
  have hzRep : y = ∑ i, vars i ⊗ₜ[A] mvec i := by
    rw [hz.symm, hz']
    change TensorProduct.map (symmetricPower A Q 1).subtype LinearMap.id
      (TensorProduct.map ρ LinearMap.id (TensorProduct.map q LinearMap.id zV)) = _
    rw [TensorProduct.map_map, TensorProduct.map_map, hcomp, hzVrep, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.map_tmul]
    rfl
  exact ⟨mvec, hzRep⟩

/-- Descending the universe lift, the extension of `f` acts on sections as the base change
of `f`. -/
private lemma down_extensionMap_apply {n m : ℕ} (A : Type u) [CommRing A]
    (f : (Fin n → A) →ₗ[A] (Fin m → A)) (R : CommAlgCat.{max u v} A)
    (z : TensorProduct A R (finiteFreeModule.{w} A n)) :
    TensorProduct.map LinearMap.id (finiteFreeDownEquiv.{w, u} A).toLinearMap
      ((((moduleExtensionFunctor.{max u w, v} A).map
        ((ModuleCat.uliftFunctor.{w, u} A).map (ModuleCat.ofHom f))).app
          (Opposite.op (Opposite.op R))) z) =
      f.baseChange R
        (TensorProduct.map LinearMap.id (finiteFreeDownEquiv.{w, u} A).toLinearMap z) := by
  induction z using TensorProduct.inductionOn with
  | tmul b z =>
      rw [moduleExtensionFunctor_map_app_tmul.{max u w, v}
        A ((ModuleCat.uliftFunctor.{w, u} A).map (ModuleCat.ofHom f))
        (Opposite.op (Opposite.op R)) b z]
      rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- The tuple of universe-lifted universal solutions is killed by the extension of `f`,
evaluated at the universal solution algebra. This is the computation at the single algebra the
proof of [Stacks, Tag 06V0] evaluates its exact row at. -/
private lemma finiteFreeExtension_tupleTensorFiniteFree_eq_zero {n m : ℕ} (A : Type u)
    [CommRing A] (f : (Fin n → A) →ₗ[A] (Fin m → A)) :
    (((moduleExtensionFunctor.{max u w, v} A).map
          ((ModuleCat.uliftFunctor.{w, u} A).map (ModuleCat.ofHom f))).app
        (Opposite.op (Opposite.op (CommAlgCat.of A
          (universalSolutionAlgebraLifted.{v} A f))))).hom
      (tupleTensorFiniteFree.{w} A (universalSolutionAlgebraLifted.{v} A f)
        (universalSolutionVariableLifted A f)) = 0 := by
  apply (TensorProduct.congr (LinearEquiv.refl A (universalSolutionAlgebraLifted.{v} A f))
    (finiteFreeDownEquiv.{w, u} (A := A) (n := m))).injective
  rw [map_zero]
  refine (down_extensionMap_apply.{w, v} A f
    (CommAlgCat.of A (universalSolutionAlgebraLifted.{v} A f)) _).trans ?_
  rw [tupleTensorFiniteFree_down]
  exact universalSolution_tuple_in_ker_lifted A f

/-- The graded and the constant Laurent maps differ by the weight `T` on the tuple of
universal variables. -/
private lemma map_gradedLaurent_tupleTensorFiniteFree {n m : ℕ} (A : Type u) [CommRing A]
    (f : (Fin n → A) →ₗ[A] (Fin m → A)) :
    TensorProduct.map (gradedLaurentMapLarge A (universalSolutionAlgebraLifted.{v} A f)
        (symmetricPower A (ULift.{v} (universalSolutionModule A f)))).toLinearMap LinearMap.id
      (tupleTensorFiniteFree.{w} A (universalSolutionAlgebraLifted.{v} A f)
        (universalSolutionVariableLifted A f)) =
    (LaurentPolynomial.T (1 : ℤ) :
        LaurentPolynomial (universalSolutionAlgebraLifted.{v} A f)) •
      TensorProduct.map (constantLaurentMapLarge A
        (universalSolutionAlgebraLifted.{v} A f)).toLinearMap LinearMap.id
        (tupleTensorFiniteFree.{w} A (universalSolutionAlgebraLifted.{v} A f)
          (universalSolutionVariableLifted A f)) := by
  simp only [tupleTensorFiniteFree, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  change gradedLaurentMapLarge A _ (symmetricPower A (ULift (universalSolutionModule A f)))
    (SymmetricAlgebra.ι A (ULift (universalSolutionModule A f))
      (ULift.up (Submodule.mkQ (LinearMap.range (transposeLinearMap A f))
        (Pi.single j 1)))) ⊗ₜ[A] _ = _
  rw [gradedLaurentMapLarge_symmetricAlgebra_generator]
  exact congrArg (· ⊗ₜ[A] _) (mul_comm _ _)

/-- Applying the map determined by a tuple to the tuple of `vars` gives the corresponding
combination. -/
private lemma map_linearMapOfTuple_tupleTensorFiniteFree {n : ℕ} (A : Type u) [CommRing A]
    (B : Type (max u v)) [CommRing B] [Algebra A B] (M : Type (max u w)) [AddCommGroup M]
    [Module A M] (vars : Fin n → B) (mvec : Fin n → M) :
    TensorProduct.map LinearMap.id
      ((linearMapOfTuple A M mvec).comp (finiteFreeDownEquiv.{w, u} A).toLinearMap)
      (tupleTensorFiniteFree.{w} A B vars) = ∑ i, vars i ⊗ₜ[A] mvec i := by
  simp only [tupleTensorFiniteFree, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact congrArg (vars i ⊗ₜ[A] ·) (linearMapOfTuple_single A M mvec i)

/-- The lifting property of Tag 06V0, with the module in a universe containing the ring's. -/
private theorem exists_lift_from_finite_free_kernel_large
    (A : Type u) [CommRing A] (M : Type (max u w)) [AddCommGroup M] [Module A M]
    (n m : ℕ) (L : ModuleValuedFunctor.{max u v w, v} A)
    (i : L ⟶ moduleExtensionOfCarrier A (finiteFreeModule.{w} A n))
    (d : moduleExtensionOfCarrier A (finiteFreeModule.{w} A n) ⟶
      moduleExtensionOfCarrier A (finiteFreeModule.{w} A m))
    (φ : L ⟶ moduleExtensionOfCarrier A M) [Mono i] (hd : i ≫ d = 0)
    (h : (ShortComplex.mk i d hd).Exact) :
    ∃ ψ : moduleExtensionOfCarrier A (finiteFreeModule.{w} A n) ⟶
      moduleExtensionOfCarrier A M, i ≫ ψ = φ := by
  let f := finiteFreeExtensionMap A d
  let B := universalSolutionAlgebraLifted A f
  let vars := universalSolutionVariableLifted A f
  let X₀ : ((CommAlgCat.{max u v} A)ᵒᵖ)ᵒᵖ :=
    Opposite.op (Opposite.op (CommAlgCat.of A B))
  let x := tupleTensorFiniteFree A B vars
  have hbase : d = (moduleExtensionFunctor.{max u w, v} A).map
      ((ModuleCat.uliftFunctor.{w, u} A).map (ModuleCat.ofHom f)) :=
    finiteFreeExtensionNatTrans_eq_map A d
  have hx : (d.app X₀).hom x = 0 := by
    rw [hbase]
    exact finiteFreeExtension_tupleTensorFiniteFree_eq_zero.{w} A f
  let S := ShortComplex.mk i d hd
  have hS : S.Exact := by simpa [S] using h
  obtain ⟨ℓ, hℓ⟩ := exact_component_preimage_large A S hS X₀ x hx
  let Y : ((CommAlgCat.{max u v} A)ᵒᵖ)ᵒᵖ :=
    Opposite.op (Opposite.op (CommAlgCat.of A (LaurentPolynomial B)))
  let g := gradedLaurentMapLarge A B (symmetricPower A (ULift (universalSolutionModule A f)))
  let c := constantLaurentMapLarge A B
  let uG := (CommAlgCat.ofHom g).op.op
  let uC := (CommAlgCat.ofHom c).op.op
  have hscale : (moduleExtensionOfCarrier A (finiteFreeModule.{w} A n)).map uG x =
      (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial B) •
        (moduleExtensionOfCarrier A (finiteFreeModule.{w} A n)).map uC x :=
    map_gradedLaurent_tupleTensorFiniteFree.{w} A f
  have hNat (u : X₀ ⟶ Y) : (i.app Y).hom (L.map u ℓ) =
      (moduleExtensionOfCarrier A (finiteFreeModule.{w} A n)).map u x := by
    rw [← hℓ]
    exact PresheafOfModules.naturality_apply i u ℓ
  have hLscale : (L.map uG ℓ : L.obj Y) =
      (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial B) • (L.map uC ℓ : L.obj Y) := by
    apply PresheafOfModules.injective_of_mono i Y
    rw [hNat uG, hscale, ← hNat uC]
    exact ((i.app Y).hom.map_smul _ _).symm
  let y : TensorProduct A B M := (φ.app X₀).hom ℓ
  have hPhi (u : X₀ ⟶ Y) : (φ.app Y).hom (L.map u ℓ) =
      (moduleExtensionOfCarrier A M).map u y := by
    simpa only [y] using PresheafOfModules.naturality_apply φ u ℓ
  have hyWeight : (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial B) •
        (TensorProduct.map c.toLinearMap LinearMap.id) y =
      (TensorProduct.map g.toLinearMap LinearMap.id) y := by
    have h := (((φ.app Y).hom.map_smul _ _).symm.trans
      (congrArg (φ.app Y).hom hLscale.symm)).trans (hPhi uG)
    rwa [hPhi uC] at h
  obtain ⟨mvec, hzRep⟩ := exists_tuple_of_weightOne A M f y hyWeight
  let mMap := (linearMapOfTuple A M mvec).comp (finiteFreeDownEquiv.{w, u} A).toLinearMap
  let ψ := moduleExtensionHomLarge A mMap
  have hψx : (ψ.app X₀).hom x = y :=
    (map_linearMapOfTuple_tupleTensorFiniteFree.{w} A B M vars mvec).trans hzRep.symm
  exact ⟨ψ, lift_eq_of_eq_at_universalSolution A M n m L i d φ ψ hd f hbase ℓ hℓ hψx⟩


/-- **Stacks Lemma 06V0.** A morphism from the kernel of a morphism between finite free
module-valued functors to a module-valued functor extends to the middle finite free functor. -/
@[stacks 06V0]
public theorem exists_lift_from_finite_free_kernel
    (A : Type u) [CommRing A] (M : Type (max u w)) [AddCommGroup M] [Module A M]
    (n m : ℕ) (L : ModuleValuedFunctor.{max u v w, v} A)
    (i : L ⟶ moduleExtensionOfCarrier A (finiteFreeModule.{w} A n))
    (d : moduleExtensionOfCarrier A (finiteFreeModule.{w} A n) ⟶
      moduleExtensionOfCarrier A (finiteFreeModule.{w} A m))
    (φ : L ⟶ moduleExtensionOfCarrier A M) [Mono i] (hd : i ≫ d = 0)
    (h : (ShortComplex.mk i d hd).Exact) :
    ∃ ψ : moduleExtensionOfCarrier A (finiteFreeModule.{w} A n) ⟶
      moduleExtensionOfCarrier A M, i ≫ ψ = φ :=
  exists_lift_from_finite_free_kernel_large A M n m L i d φ hd h


/-! ### Tag 06V0 on a restricted domain of algebras

The proof above evaluates the given morphisms at exactly two algebras: the universal solution
algebra `B` and its Laurent polynomial algebra `B[T, T⁻¹]`. So it carries over to the
module-valued functors on a *domain* of algebras as soon as that domain contains those two
algebras and has a base object, the latter being what makes extension of scalars to it full.
The domain is taken to be the full subcategory cut out by a property of algebras, so that its
objects are algebras with a proof and its morphisms are algebra maps: no transport along an
isomorphism of algebras is then needed anywhere in the argument. -/

/-- The module-valued functor on a domain of algebras associated to an `A`-module. -/
public noncomputable abbrev moduleExtensionOfCarrierOn {A : Type u} [CommRing A]
    {C : Type u₁} [Category.{v₁} C] (ι : C ⥤ CommAlgCat.{max u v} A)
    (M : Type w) [AddCommGroup M] [Module A M] :=
  (moduleExtensionFunctorOn.{w, v} ι).obj (ModuleCat.of A M)

/-- Exactness of a short complex of module-valued functors on a domain of algebras can be
tested on sections. -/
public lemma exact_component_preimage_on {A : Type u} [CommRing A]
    {C : Type u₁} [Category.{v₁} C] (ι : C ⥤ CommAlgCat.{max u v} A)
    (S : ShortComplex (ModuleValuedFunctorOn.{max u v w, v} ι)) (hS : S.Exact)
    (X : (Cᵒᵖ)ᵒᵖ) (x : S.X₂.obj X) (hx : S.g.app X x = 0) :
    ∃ y : S.X₁.obj X, S.f.app X y = x := by
  let E := PresheafOfModules.evaluation (algebraRingDiagramOn.{v} ι) X
  let : CategoryTheory.Limits.PreservesFiniteLimits E := inferInstance
  let : CategoryTheory.Limits.PreservesFiniteColimits E := inferInstance
  let : E.PreservesZeroMorphisms := inferInstance
  have hE : (S.map E).Exact := hS.map E
  have hx' : ((S.map E).g.hom) x = 0 := hx
  obtain ⟨y, hy⟩ := (ShortComplex.exact_iff_of_hasForget (S := S.map E)).mp hE x hx'
  exact ⟨y, hy⟩

/-- A morphism between the module-valued functors of finite free modules on a domain of
algebras with a base object is the image of a linear map of the finite free modules. This is
the only use the proof of [Stacks, Tag 06V0] makes of fullness of extension of scalars, and on
a restricted domain it is `AdequateFunctor.moduleExtension_natTransOn_eq_map`. -/
private lemma exists_finiteFreeExtensionMapOn {n m : ℕ} (A : Type u) [CommRing A]
    {C : Type u₁} [Category.{v₁} C] {ι : C ⥤ CommAlgCat.{max u v} A}
    (b : BaseAlgebraObject.{v} ι)
    (d : moduleExtensionOfCarrierOn.{max u w} ι (finiteFreeModule.{w} A n) ⟶
      moduleExtensionOfCarrierOn.{max u w} ι (finiteFreeModule.{w} A m)) :
    ∃ f : (Fin n → A) →ₗ[A] (Fin m → A),
      d = (moduleExtensionFunctorOn.{max u w, v} ι).map
        ((ModuleCat.uliftFunctor.{w, u} A).map (ModuleCat.ofHom f)) := by
  let dM : finiteFreeModule.{w} A n ⟶ finiteFreeModule.{w} A m :=
    moduleHomOfExtensionNatTransOn.{max u w} b d
  refine ⟨((ModuleCat.fullyFaithfulUliftFunctor.{u, u, w} A).preimage dM).hom, ?_⟩
  have hd : d = (moduleExtensionFunctorOn.{max u w, v} ι).map dM :=
    moduleExtension_natTransOn_eq_map.{max u w} b d
  have hf : (ModuleCat.uliftFunctor.{w, u} A).map (ModuleCat.ofHom
      ((ModuleCat.fullyFaithfulUliftFunctor.{u, u, w} A).preimage dM).hom) = dM := by
    have h₁ : ModuleCat.ofHom
        ((ModuleCat.fullyFaithfulUliftFunctor.{u, u, w} A).preimage dM).hom =
          (ModuleCat.fullyFaithfulUliftFunctor.{u, u, w} A).preimage dM := by
      apply ModuleCat.hom_ext
      rfl
    rw [h₁]
    exact (ModuleCat.fullyFaithfulUliftFunctor.{u, u, w} A).map_preimage dM
  rw [hf]
  exact hd

/-- Naturality half of the restricted-domain [Stacks, Tag 06V0]: a candidate lift agreeing
with the given morphism at the universal solution algebra agrees with it everywhere. Every
object of the domain receives an algebra map from the universal solution algebra, namely the one
classifying the tuple of coordinates of the section being tested, and naturality along that map
transports the single agreement to that object. -/
private lemma lift_eq_of_eq_at_universalSolution_on
    (A : Type u) [CommRing A] (M : Type (max u w)) [AddCommGroup M] [Module A M]
    (Q : ObjectProperty (CommAlgCat.{max u v} A))
    (n m : ℕ) (L : ModuleValuedFunctorOn.{max u v w, v} Q.ι)
    (i : L ⟶ moduleExtensionOfCarrierOn.{max u w} Q.ι (finiteFreeModule.{w} A n))
    (d : moduleExtensionOfCarrierOn.{max u w} Q.ι (finiteFreeModule.{w} A n) ⟶
      moduleExtensionOfCarrierOn.{max u w} Q.ι (finiteFreeModule.{w} A m))
    (φ : L ⟶ moduleExtensionOfCarrierOn.{max u w} Q.ι M)
    (ψ : moduleExtensionOfCarrierOn.{max u w} Q.ι (finiteFreeModule.{w} A n) ⟶
      moduleExtensionOfCarrierOn.{max u w} Q.ι M)
    [Mono i] (hd : i ≫ d = 0)
    (f : (Fin n → A) →ₗ[A] (Fin m → A))
    (hbase : d = (moduleExtensionFunctorOn.{max u w, v} Q.ι).map
      ((ModuleCat.uliftFunctor.{w, u} A).map (ModuleCat.ofHom f)))
    (hB : Q (CommAlgCat.of A (universalSolutionAlgebraLifted.{v} A f)))
    (ℓ : L.obj (Opposite.op (Opposite.op
      (⟨CommAlgCat.of A (universalSolutionAlgebraLifted.{v} A f), hB⟩ : Q.FullSubcategory))))
    (hℓ : (i.app (Opposite.op (Opposite.op
        (⟨CommAlgCat.of A (universalSolutionAlgebraLifted.{v} A f), hB⟩ :
          Q.FullSubcategory)))).hom ℓ =
      tupleTensorFiniteFree.{w} A (universalSolutionAlgebraLifted.{v} A f)
        (universalSolutionVariableLifted A f))
    (hψx : (ψ.app (Opposite.op (Opposite.op
        (⟨CommAlgCat.of A (universalSolutionAlgebraLifted.{v} A f), hB⟩ :
          Q.FullSubcategory)))).hom
        (tupleTensorFiniteFree.{w} A (universalSolutionAlgebraLifted.{v} A f)
          (universalSolutionVariableLifted A f)) =
      (φ.app (Opposite.op (Opposite.op
        (⟨CommAlgCat.of A (universalSolutionAlgebraLifted.{v} A f), hB⟩ :
          Q.FullSubcategory)))).hom ℓ) :
    i ≫ ψ = φ := by
  let B := universalSolutionAlgebraLifted.{v} A f
  let vars := universalSolutionVariableLifted A f
  let X₀ : ((Q.FullSubcategory)ᵒᵖ)ᵒᵖ :=
    Opposite.op (Opposite.op (⟨CommAlgCat.of A B, hB⟩ : Q.FullSubcategory))
  let x := tupleTensorFiniteFree.{w} A B vars
  let y : TensorProduct A B M := (φ.app X₀).hom ℓ
  ext X ξ
  rcases X with ⟨⟨T⟩⟩
  let XC : ((Q.FullSubcategory)ᵒᵖ)ᵒᵖ := Opposite.op (Opposite.op T)
  let D : Type (max u v) := (T.obj : Type (max u v))
  let eₙ := finiteFreeDownEquiv.{w, u} (A := A) (n := n)
  let eₘ := finiteFreeDownEquiv.{w, u} (A := A) (n := m)
  let ξ₀ : TensorProduct A D (Fin n → A) :=
    TensorProduct.map (LinearMap.id : D →ₗ[A] D) eₙ.toLinearMap ((i.app XC).hom ξ)
  let xC : Fin n → D := TensorProduct.piScalarRight A D D (Fin n) ξ₀
  have htuple : tupleTensor A D xC = ξ₀ := by
    apply (TensorProduct.piScalarRight A D D (Fin n)).injective
    ext j
    simp [xC, tupleTensor, TensorProduct.piScalarRight_apply,
      TensorProduct.piScalarRightHom_tmul, Pi.single_apply]
  have hiξ : tupleTensorFiniteFree.{w} A D xC = (i.app XC).hom ξ := by
    apply (TensorProduct.congr (LinearEquiv.refl A D) eₙ).injective
    change TensorProduct.map (LinearMap.id : D →ₗ[A] D) eₙ.toLinearMap
        (tupleTensorFiniteFree.{w} A D xC) =
      TensorProduct.map (LinearMap.id : D →ₗ[A] D) eₙ.toLinearMap ((i.app XC).hom ξ)
    rw [tupleTensorFiniteFree_down]
    exact htuple
  have hker : (d.app XC).hom ((i.app XC).hom ξ) = 0 := by
    have hh := congrArg (fun η => (η.app XC).hom ξ) hd
    simpa using hh
  have hzero : f.baseChange D (tupleTensor A D xC) = 0 := by
    have h := down_extensionMap_apply.{w, v} A f T.obj ((i.app XC).hom ξ)
    have hD : (d.app XC).hom ((i.app XC).hom ξ) =
        ((moduleExtensionFunctor.{max u w, v} A).map
          ((ModuleCat.uliftFunctor.{w, u} A).map (ModuleCat.ofHom f))).app
          (Opposite.op (Opposite.op T.obj)) ((i.app XC).hom ξ) := by
      rw [hbase]
      rfl
    rw [← hD, hker] at h
    rw [htuple]
    exact h.symm.trans (map_zero _)
  have hrel : ∀ j, ∑ k, f (Pi.single k 1) j • xC k = 0 := by
    intro j
    have hc := congrArg
      (fun z => TensorProduct.piScalarRight A D D (Fin m) z j) hzero
    rw [piScalarRight_baseChange_tupleTensor] at hc
    exact hc
  let e := universalSolutionAlgHomLifted A D f xC hrel
  let u : X₀ ⟶ XC :=
    (ObjectProperty.homMk (X := (⟨CommAlgCat.of A B, hB⟩ : Q.FullSubcategory)) (Y := T)
      (CommAlgCat.ofHom e)).op.op
  have hvarsC (j : Fin n) : e (vars j) = xC j :=
    universalSolutionAlgHomLifted_variable A D f xC hrel j
  have hiNaturality : (i.app XC).hom ξ =
      (moduleExtensionOfCarrierOn.{max u w} Q.ι (finiteFreeModule.{w} A n)).map u x := by
    have hFmap : (moduleExtensionOfCarrierOn.{max u w} Q.ι
        (finiteFreeModule.{w} A n)).map u x = tupleTensorFiniteFree.{w} A D xC := by
      change (TensorProduct.map e.toLinearMap LinearMap.id)
          (tupleTensorFiniteFree.{w} A B vars) = tupleTensorFiniteFree.{w} A D xC
      simp only [tupleTensorFiniteFree, map_sum]
      apply Finset.sum_congr rfl
      intro j hj
      change e (vars j) ⊗ₜ[A] (⟨Pi.single j 1⟩ : finiteFreeModule.{w} A n) =
        xC j ⊗ₜ[A] (⟨Pi.single j 1⟩ : finiteFreeModule.{w} A n)
      rw [hvarsC j]
    exact hiξ.symm.trans hFmap.symm
  have hLξ : L.map u ℓ = ξ := by
    apply PresheafOfModules.injective_of_mono i XC
    have hNatI : (i.app XC).hom (L.map u ℓ) =
        (moduleExtensionOfCarrierOn.{max u w} Q.ι (finiteFreeModule.{w} A n)).map u
          ((i.app X₀).hom ℓ) := PresheafOfModules.naturality_apply i u ℓ
    exact hNatI.trans
      ((congrArg ((moduleExtensionOfCarrierOn.{max u w} Q.ι
        (finiteFreeModule.{w} A n)).map u) hℓ).trans hiNaturality.symm)
  have hφξ : (φ.app XC).hom ξ =
      (moduleExtensionOfCarrierOn.{max u w} Q.ι M).map u y :=
    (congrArg (φ.app XC).hom hLξ.symm).trans
      (by simpa [y] using (PresheafOfModules.naturality_apply φ u ℓ))
  have hψξ : (ψ.app XC).hom ((i.app XC).hom ξ) =
      (moduleExtensionOfCarrierOn.{max u w} Q.ι M).map u y := by
    have hNatψ : (ψ.app XC).hom ((moduleExtensionOfCarrierOn.{max u w} Q.ι
          (finiteFreeModule.{w} A n)).map u x) =
        (moduleExtensionOfCarrierOn.{max u w} Q.ι M).map u ((ψ.app X₀).hom x) :=
      PresheafOfModules.naturality_apply ψ u x
    exact (congrArg (ψ.app XC).hom hiNaturality).trans
      (hNatψ.trans (congrArg ((moduleExtensionOfCarrierOn.{max u w} Q.ι M).map u) hψx))
  exact hψξ.trans hφξ.symm

/-- A linear map into a module in a larger universe, read as a morphism of the associated
module-valued functors on a domain of algebras. -/
public noncomputable def moduleExtensionHomLargeOn (A : Type u) [CommRing A]
    {C : Type u₁} [Category.{v₁} C] (ι : C ⥤ CommAlgCat.{max u v} A)
    {M N : Type (max u w)} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (f : M →ₗ[A] N) :
    moduleExtensionOfCarrierOn.{max u w} ι M ⟶ moduleExtensionOfCarrierOn.{max u w} ι N :=
  (moduleExtensionFunctorOn.{max u w, v} ι).map (ModuleCat.ofHom f)

/-- **Stacks Lemma 06V0 on a restricted domain of algebras.** A morphism from the kernel of a
morphism between finite free module-valued functors on a domain of algebras to a module-valued
functor of a module extends to the middle finite free functor, provided the domain contains the
universal solution algebra of the morphism and its Laurent polynomial algebra and has a base
object.

No `@[stacks]` attribute is placed here: this is the library's Tag 06V0 carried to a restricted
domain, not a further part of that tag's covering set. -/
public theorem exists_lift_from_finite_free_kernel_on
    (A : Type u) [CommRing A] (M : Type (max u w)) [AddCommGroup M] [Module A M]
    (Q : ObjectProperty (CommAlgCat.{max u v} A))
    (hsym : ∀ (V : Type (max u v)) [AddCommGroup V] [Module A V] [Module.Finite A V],
      Q (CommAlgCat.of A (SymmetricAlgebra A V)))
    (hlau : ∀ (R : Type (max u v)) [CommRing R] [Algebra A R], Q (CommAlgCat.of A R) →
      Q (CommAlgCat.of A (LaurentPolynomial R)))
    (b : BaseAlgebraObject.{v} Q.ι)
    (n m : ℕ) (L : ModuleValuedFunctorOn.{max u v w, v} Q.ι)
    (i : L ⟶ moduleExtensionOfCarrierOn.{max u w} Q.ι (finiteFreeModule.{w} A n))
    (d : moduleExtensionOfCarrierOn.{max u w} Q.ι (finiteFreeModule.{w} A n) ⟶
      moduleExtensionOfCarrierOn.{max u w} Q.ι (finiteFreeModule.{w} A m))
    (φ : L ⟶ moduleExtensionOfCarrierOn.{max u w} Q.ι M) [Mono i] (hd : i ≫ d = 0)
    (h : (ShortComplex.mk i d hd).Exact) :
    ∃ ψ : moduleExtensionOfCarrierOn.{max u w} Q.ι (finiteFreeModule.{w} A n) ⟶
      moduleExtensionOfCarrierOn.{max u w} Q.ι M, i ≫ ψ = φ := by
  obtain ⟨f, hbase⟩ := exists_finiteFreeExtensionMapOn.{w} A b d
  let B := universalSolutionAlgebraLifted.{v} A f
  let vars := universalSolutionVariableLifted A f
  have : Module.Finite A (ULift.{v} (universalSolutionModule A f)) := inferInstance
  have hB : Q (CommAlgCat.of A B) :=
    hsym (ULift.{v} (universalSolutionModule A f))
  let X₀ : ((Q.FullSubcategory)ᵒᵖ)ᵒᵖ :=
    Opposite.op (Opposite.op (⟨CommAlgCat.of A B, hB⟩ : Q.FullSubcategory))
  let x := tupleTensorFiniteFree.{w} A B vars
  have hx : (d.app X₀).hom x = 0 := by
    rw [hbase]
    exact finiteFreeExtension_tupleTensorFiniteFree_eq_zero.{w} A f
  let S := ShortComplex.mk i d hd
  have hS : S.Exact := by simpa [S] using h
  obtain ⟨ℓ, hℓ⟩ := exact_component_preimage_on.{w} Q.ι S hS X₀ x hx
  have hBL : Q (CommAlgCat.of A (LaurentPolynomial B)) := hlau B hB
  let Y : ((Q.FullSubcategory)ᵒᵖ)ᵒᵖ :=
    Opposite.op (Opposite.op
      (⟨CommAlgCat.of A (LaurentPolynomial B), hBL⟩ : Q.FullSubcategory))
  let g := gradedLaurentMapLarge A B (symmetricPower A (ULift (universalSolutionModule A f)))
  let c := constantLaurentMapLarge A B
  let uG : X₀ ⟶ Y :=
    (ObjectProperty.homMk (X := (⟨CommAlgCat.of A B, hB⟩ : Q.FullSubcategory))
      (Y := (⟨CommAlgCat.of A (LaurentPolynomial B), hBL⟩ : Q.FullSubcategory))
      (CommAlgCat.ofHom g)).op.op
  let uC : X₀ ⟶ Y :=
    (ObjectProperty.homMk (X := (⟨CommAlgCat.of A B, hB⟩ : Q.FullSubcategory))
      (Y := (⟨CommAlgCat.of A (LaurentPolynomial B), hBL⟩ : Q.FullSubcategory))
      (CommAlgCat.ofHom c)).op.op
  have hscale : (moduleExtensionOfCarrierOn.{max u w} Q.ι
        (finiteFreeModule.{w} A n)).map uG x =
      (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial B) •
        (moduleExtensionOfCarrierOn.{max u w} Q.ι (finiteFreeModule.{w} A n)).map uC x :=
    map_gradedLaurent_tupleTensorFiniteFree.{w} A f
  have hNat (u : X₀ ⟶ Y) : (i.app Y).hom (L.map u ℓ) =
      (moduleExtensionOfCarrierOn.{max u w} Q.ι (finiteFreeModule.{w} A n)).map u x := by
    rw [← hℓ]
    exact PresheafOfModules.naturality_apply i u ℓ
  have hLscale : (L.map uG ℓ : L.obj Y) =
      (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial B) • (L.map uC ℓ : L.obj Y) := by
    apply PresheafOfModules.injective_of_mono i Y
    rw [hNat uG, hscale, ← hNat uC]
    exact ((i.app Y).hom.map_smul _ _).symm
  let y : TensorProduct A B M := (φ.app X₀).hom ℓ
  have hPhi (u : X₀ ⟶ Y) : (φ.app Y).hom (L.map u ℓ) =
      (moduleExtensionOfCarrierOn.{max u w} Q.ι M).map u y := by
    simpa only [y] using PresheafOfModules.naturality_apply φ u ℓ
  have hyWeight : (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial B) •
        (TensorProduct.map c.toLinearMap LinearMap.id) y =
      (TensorProduct.map g.toLinearMap LinearMap.id) y := by
    have h := (((φ.app Y).hom.map_smul _ _).symm.trans
      (congrArg (φ.app Y).hom hLscale.symm)).trans (hPhi uG)
    rwa [hPhi uC] at h
  obtain ⟨mvec, hzRep⟩ := exists_tuple_of_weightOne A M f y hyWeight
  let mMap := (linearMapOfTuple A M mvec).comp (finiteFreeDownEquiv.{w, u} A).toLinearMap
  let ψ := moduleExtensionHomLargeOn.{w} A Q.ι mMap
  have hψx : (ψ.app X₀).hom x = y :=
    (map_linearMapOfTuple_tupleTensorFiniteFree.{w} A B M vars mvec).trans hzRep.symm
  exact ⟨ψ, lift_eq_of_eq_at_universalSolution_on A M Q n m L i d φ ψ hd f hbase hB ℓ hℓ hψx⟩

end AdequateFunctor
