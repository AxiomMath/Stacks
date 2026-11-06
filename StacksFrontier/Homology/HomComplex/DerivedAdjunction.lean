module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Homology.BifunctorFlip
public import Mathlib.Algebra.Homology.BifunctorHomotopy
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.Algebra.Homology.Localization
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Localization.Bifunctor
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimits
public import StacksFrontier.Algebra.Homology.KFlat
public import StacksFrontier.CategoryTheory.Triangulated.DistinguishedOfIso
public import StacksFrontier.CategoryTheory.Triangulated.Localization
public import StacksFrontier.CategoryTheory.Triangulated.Quotient
public import StacksFrontier.Homology.HomComplex.Currying
public import StacksFrontier.Homology.HomComplex.Evaluation
public import StacksFrontier.Homology.HomComplex.KoszulBraiding
public import StacksFrontier.Homology.HomComplex.RHom
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.TensorComplex.Monoidal
public import StacksFrontier.Homology.Tor.KFlatHomotopyTensor


/-!
# The derived-Hom adjunction, currying, and evaluation

Let `R` be a commutative ring. Derived tensor product and derived Hom are bifunctors on the
unbounded derived category `D(R)` of `R`-modules, and derived Hom is the internal Hom for derived
tensor product: there is an additive equivalence `Hom(K, RHom(L, M)) ≃+ Hom(K ⊗ᴸ L, M)`, natural
in all three variables. This module constructs that adjunction together with its K-flat and
K-injective models, and then derives its two standard consequences: the currying isomorphism
`RHom(K, RHom(L, M)) ≅ RHom(K ⊗ᴸ L, M)`, and the canonical evaluation morphism
`RHom(L, M) ⊗ᴸ K ⟶ RHom(RHom(K, L), M)`.

## Main definitions

* `DerivedHomAdjunction`: the derived tensor and derived-Hom bifunctors on `D(R)`, together with
  the associativity and symmetry of derived tensor product and the natural Hom equivalence.
* `DerivedHomData`: a `DerivedHomAdjunction` enriched by its comparison isomorphisms with total
  tensor complexes of K-flat representatives and Hom complexes of K-injective representatives.
* `DerivedHomData.tensorUnitLeft`, `DerivedHomData.homZeroEquiv`: the tensor unit descended from
  complexes through localization, and the resulting degree-zero Hom identification.
* `derivedHomAdjunction`: the canonical `DerivedHomData`, for modules in the ring's own universe.
* `derivedHomAdjunctionULift`: the same construction over `ULift R`, so that the module universe
  may be chosen independently of the ring universe.
* `uliftModuleEquivalence`, `uliftDerivedEquivalence`, `derivedScalarEquivalence`: restriction of
  scalars along `ULift.ringEquiv.symm` and its lift to derived categories.
* `DerivedHomAdjunction.transport`: transport of an entire adjunction along an additive
  equivalence of derived categories.
* `derivedHomAdjunctionOverRing`: the resulting adjunction on `D(R)` itself, in an independently
  chosen module universe.
* `DerivedHomAdjunction.internalCurryMor`: the internalized evaluation morphism, obtained from
  associativity, symmetry and evaluation.
* `DerivedHomCurrying`: the currying isomorphism for a `DerivedHomData`, bundled with its
  naturality, its chain-model characterization and its degree-zero comparison.

## Main results

* `homInternalHomEquiv` ([stacks 0A63]): the characterization equation
  `Hom(K, RHom(L, M)) ≃+ Hom(K ⊗ᴸ L, M)` in `D(R)`.
* `derivedHomCurrying` ([stacks 0A65]): the currying isomorphism
  `RHom(K, RHom(L, M)) ≅ RHom(K ⊗ᴸ L, M)`, functorial in all three variables; on K-flat and
  K-injective representatives it is the Hom-complex currying map of [stacks 0A5Y], and on
  degree-zero cohomology it is the adjunction of [stacks 0A63].
* `exists_evaluationToIteratedDerivedHom` ([stacks 0A67]): the canonical morphism
  `RHom(L, M) ⊗ᴸ K ⟶ RHom(RHom(K, L), M)`, natural in all three variables, which on K-flat and
  K-injective representatives is the chain-level evaluation map of [stacks 0A60].
* `homComplex_isKInjective_of_kFlat`: a Hom complex out of a K-flat complex into a K-injective
  complex is K-injective.

## Implementation notes

The tagged equation of [stacks 0A63] uses the fixed construction `derivedHomAdjunctionOverRing`;
it has no parameter supplying an adjunction. The underlying construction claim is
`derivedHomAdjunction`, whose model comparisons identify the bifunctors with total tensor and Hom
complexes and identify the adjunction with `Stacks.HomComplex.TensorHomMap.Phi`. The comparisons
  are natural
isomorphisms on categories of representatives, and `tensorIso` and `homIso` are their components.
The tensor unit is defined by descending the ordinary complex unitor through localization; its
naturality and model comparison, and the induced `homZeroEquiv_symm_map` formula, are proved from
that construction.

Mathlib's monoidal category of modules forces the ring and module universes to agree, so the
construction is first carried out over `ULift.{v} R` with modules in `max u v`, and then
transported to `D(R)` along `uliftDerivedEquivalence`. This is why the tagged statements are
phrased for `ModuleCat.{max u v} R`, with the ring universe, the module enlargement and the
derived-morphism universe independent.

The symmetric monoidal structure on `CochainComplex (ModuleCat R) ℤ` is not a global instance --
it fixes the Koszul sign convention -- so the construction takes `[SymmetricCategory (C R)]` as a
hypothesis and the canonical data instantiates it with `CochainComplex.Koszul.koszulSymmetric`.
Likewise the chain-level evaluation map of [stacks 0A60] enters as the canonical morphism
`ChainEvaluation.chainEvaluation` rather than through a choice.

[stacks 0A67] is stated existentially: the evaluation family is `internalCurryMor` of the
canonical adjunction, and what the tag asserts is that *some* such family exists with the three
naturality laws and the K-flat/K-injective comparison.

### Results owned by other tags

Two inputs to the construction are the content of tags realized elsewhere, and are taken from
their conceptual providers rather than restated here:

* `CochainComplex.KFlat.exists_kFlat_resolution` (tag 06Y4, in
  `StacksFrontier.Homology.KFlat.Resolution`): every cochain complex of modules admits a
  termwise-surjective quasi-isomorphism from a K-flat complex with flat terms. It is stated with
  large-universe K-flatness, so `exists_kFlat_resolution` below reads it at a module universe
  equal to the ring's, where that notion is `CochainComplex.KFlat`.
* `TotalTensorComplex.tleft_isTriangulated` and `tright_isTriangulated` (tag 064J, in
  `StacksFrontier.Homology.TensorComplex.Monoidal`): tensoring with a fixed complex on either side
  and totalizing is a triangulated endofunctor of the homotopy category. These supply the
  triangulated structure that makes the K-flat objects a triangulated subcategory and that makes
  tensoring with a K-flat complex preserve quasi-isomorphisms.

`StacksFrontier.Homology.TensorComplex.Monoidal` reaches the functors `Tleft` and `Tright` through
`StacksFrontier.Homology.TensorComplex.ExactFunctor`, whose `main_left` and `main_right` are the
covering set for tag 06Y8. Tag 064J rests on that tag here, and tag 06Y2 -- and hence tag 06Y4
-- rests on it as well; nothing in this module needs 06Y8 directly.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0A65](https://stacks.math.columbia.edu/tag/0A65)
* [Stacks Project, Tag 0A67](https://stacks.math.columbia.edu/tag/0A67)
-/

@[expose] public noncomputable section

namespace StacksDraft.DerivedHom

section HomComplexAux

open CategoryTheory MonoidalCategory CochainComplex CochainComplex.HomComplex

universe u

/-- The value of the degree-`r` cochain `Φ^r(x)` of `Stacks.HomComplex.TensorHomMap.Phiv` on an
  element: its
`(s, t)` component sends `y` to the pure tensor `x ⊗ y` in the summand `K^r ⊗ L^s` of
`Tot^t(K ⊗ L)`. -/
public lemma phiv_v_apply {R : Type u} [CommRing R]
    (K L : CochainComplex (ModuleCat R) ℤ) (r : ℤ) (x : K.X r) (s t : ℤ) (hst : s + r = t)
    (y : L.X s) :
    ((Stacks.HomComplex.TensorHomMap.Phiv R K L r x).v s t hst).hom y =
      (HomologicalComplex.ιTensorObj K L r s t (by omega)).hom (x ⊗ₜ[R] y) := by
  rw [Stacks.HomComplex.TensorHomMap.Phiv_v]
  simp

/-- Applying the Hom-complex differential to the image of a cochain under a morphism of Hom
complexes is the image of its differential. -/
public lemma homComplexMap_δ {R : Type u} [CommRing R]
    {K L K' L' : CochainComplex (ModuleCat R) ℤ}
    (f : HomComplexR R K L ⟶ HomComplexR R K' L') (n m : ℤ) (z : Cochain K L n) :
    δ n m ((f.f n).hom z) = (f.f m).hom (δ n m z) :=
  ConcreteCategory.congr_hom (f.comm n m) z

/-- A Hom complex from a K-flat complex to a K-injective complex is K-injective.
Currying sends a map from an acyclic complex to a zero-cocycle out of its tensor product
with the K-flat complex. K-injectivity makes this a boundary, and inverse currying
transports the boundary back to a null homotopy. -/
public theorem homComplex_isKInjective_of_kFlat {R : Type u} [CommRing R]
    (L I : CochainComplex (ModuleCat.{u} R) ℤ) (hL : L.KFlat) [I.IsKInjective] :
    (CochainComplex.HomComplexR R L I).IsKInjective := by
  refine ⟨fun {A} f hA ↦ ?_⟩
  let e := Stacks.HomComplex.Currying.curryIso A L I
  -- Only the fact that currying is *an* isomorphism is used below; keeping its definition
  -- visible makes the defeq checks in the null-homotopy transport blow up.
  clear_value e
  let z : Cocycle (HomologicalComplex.tensorObj A L) I 0 :=
    ⟨(e.hom.f 0).hom (Cochain.ofHom f), by
      change δ 0 1 ((e.hom.f 0).hom (Cochain.ofHom f)) = 0
      rw [homComplexMap_δ e.hom, δ_ofHom]
      exact (e.hom.f 1).hom.map_zero⟩
  obtain ⟨b, hb⟩ := IsKInjective.eq_δ_of_cocycle z (hL A hA) (-1) (by decide)
  refine ⟨(Cochain.equivHomotopy f 0).symm ⟨(e.inv.f (-1)).hom b, ?_⟩⟩
  rw [Cochain.ofHom_zero, add_zero]
  have hinv := homComplexMap_δ e.inv (-1) 0 b
  rw [hinv, hb]
  exact (ConcreteCategory.congr_hom (HomologicalComplex.congr_hom e.hom_inv_id 0)
    (Cochain.ofHom f)).symm

/-- Every cochain complex of `R`-modules admits a termwise-surjective quasi-isomorphism from a
K-flat complex with flat terms. This is `CochainComplex.KFlat.exists_kFlat_resolution` read at a
module universe equal to the ring's, where large-universe K-flatness is `CochainComplex.KFlat`. -/
private theorem exists_kFlat_resolution {R : Type u} [CommRing R]
    (M : CochainComplex (ModuleCat.{u} R) ℤ) :
    ∃ (K : CochainComplex (ModuleCat.{u} R) ℤ) (f : K ⟶ M),
      K.KFlat ∧ (∀ n : ℤ, Module.Flat R (K.X n)) ∧ QuasiIso f ∧
        ∀ n : ℤ, Function.Surjective (f.f n).hom := by
  obtain ⟨K, f, hK, hflat, hqis, hsurj⟩ :=
    CochainComplex.KFlat.exists_kFlat_resolution.{u, u} M
  exact ⟨K, f, hK, hflat, hqis, hsurj⟩

end HomComplexAux

section Adjunction

universe u v t w w'

open CochainComplex.KFlatHomotopyTensor

open CategoryTheory CategoryTheory.Functor MonoidalCategory


/-- The tensor--Hom adjunction on the derived category, with the natural associativity and
symmetry of derived tensor product. The ring, module, and derived-morphism universes are
independent. Concrete K-flat/K-injective comparisons are recorded separately in
`DerivedHomData`. -/
public structure DerivedHomAdjunction (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)] where
  /-- The derived tensor product bifunctor. -/
  tensor : DerivedCategory (ModuleCat.{v} R) × DerivedCategory (ModuleCat.{v} R) ⥤
    DerivedCategory (ModuleCat.{v} R)
  /-- Associativity of the canonical derived tensor product. -/
  tensorAssoc (K L M : DerivedCategory (ModuleCat.{v} R)) :
    tensor.obj (tensor.obj (K, L), M) ≅ tensor.obj (K, tensor.obj (L, M))
  /-- The derived tensor product is symmetric. -/
  tensorSwap (K L : DerivedCategory (ModuleCat.{v} R)) :
    tensor.obj (K, L) ≅ tensor.obj (L, K)
  /-- Naturality of tensor associativity. -/
  tensorAssoc_naturality {K K' L L' M M' : DerivedCategory (ModuleCat.{v} R)}
      (f : K ⟶ K') (g : L ⟶ L') (h : M ⟶ M') :
    tensor.map (tensor.map (f, g), h) ≫ (tensorAssoc K' L' M').hom =
      (tensorAssoc K L M).hom ≫ tensor.map (f, tensor.map (g, h))
  /-- Naturality of tensor symmetry. -/
  tensorSwap_naturality {K K' L L' : DerivedCategory (ModuleCat.{v} R)}
      (f : K ⟶ K') (g : L ⟶ L') :
    tensor.map (f, g) ≫ (tensorSwap K' L').hom =
      (tensorSwap K L).hom ≫ tensor.map (g, f)
  /-- The derived-Hom bifunctor, contravariant in its first variable. -/
  hom : (DerivedCategory (ModuleCat.{v} R))ᵒᵖ × DerivedCategory (ModuleCat.{v} R) ⥤
    DerivedCategory (ModuleCat.{v} R)
  /-- The canonical Hom equivalence for arbitrary objects of the derived category. -/
  homEquiv (K L M : DerivedCategory (ModuleCat.{v} R)) :
    (K ⟶ hom.obj (Opposite.op L, M)) ≃+ (tensor.obj (K, L) ⟶ M)
  /-- Naturality of the Hom equivalence in its first variable. -/
  homEquiv_naturality_left {K K' L M : DerivedCategory (ModuleCat.{v} R)}
      (f : K' ⟶ K) (a : K ⟶ hom.obj (Opposite.op L, M)) :
    homEquiv K' L M (f ≫ a) =
      tensor.map (f, 𝟙 L) ≫ homEquiv K L M a
  /-- Dinaturality of the Hom equivalence in the internal-Hom variable. -/
  homEquiv_dinaturality {K L L' M : DerivedCategory (ModuleCat.{v} R)}
      (g : L' ⟶ L) (a : K ⟶ hom.obj (Opposite.op L, M)) :
    homEquiv K L' M (a ≫ hom.map (g.op, 𝟙 M)) =
      tensor.map (𝟙 K, g) ≫ homEquiv K L M a
  /-- Naturality of the Hom equivalence in its target. -/
  homEquiv_naturality_right {K L M M' : DerivedCategory (ModuleCat.{v} R)}
      (g : M ⟶ M') (a : K ⟶ hom.obj (Opposite.op L, M)) :
    homEquiv K L M' (a ≫ hom.map (𝟙 (Opposite.op L), g)) =
      homEquiv K L M a ≫ g

namespace DerivedHomAdjunction

variable {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (d : DerivedHomAdjunction R)

/-- Tensor symmetry as an isomorphism of bifunctors. -/
public def tensorSymmetry :
    d.tensor ≅ CategoryTheory.Prod.swap _ _ ⋙ d.tensor :=
  NatIso.ofComponents (fun X ↦ d.tensorSwap X.1 X.2)
    (fun f ↦ d.tensorSwap_naturality f.1 f.2)

/-- Evaluation is the transpose of the identity on internal Hom. -/
public def evaluation (L M : DerivedCategory (ModuleCat.{v} R)) :
    d.tensor.obj (d.hom.obj (Opposite.op L, M), L) ⟶ M :=
  d.homEquiv _ L M (𝟙 _)

/-- The canonical internalized evaluation: associate, interchange the two right factors,
and evaluate twice, then transpose. -/
public def internalCurryMor (K L M : DerivedCategory (ModuleCat.{v} R)) :
    d.tensor.obj (d.hom.obj (Opposite.op L, M), K) ⟶
      d.hom.obj (Opposite.op (d.hom.obj (Opposite.op K, L)), M) :=
  let A := d.hom.obj (Opposite.op L, M)
  let B := d.hom.obj (Opposite.op K, L)
  (d.homEquiv (d.tensor.obj (A, K)) B M).symm
    ((d.tensorAssoc A K B).hom ≫
      d.tensor.map (show (A, d.tensor.obj (K, B)) ⟶ (A, d.tensor.obj (B, K)) from
        (𝟙 A, (d.tensorSwap K B).hom)) ≫
      d.tensor.map (show (A, d.tensor.obj (B, K)) ⟶ (A, L) from
        (𝟙 A, d.evaluation K L)) ≫ d.evaluation L M)

/-- The tensor bifunctor preserves identity pairs. -/
public theorem tensor_map_id (A B : DerivedCategory (ModuleCat.{v} R)) :
    d.tensor.map (show (A, B) ⟶ (A, B) from (𝟙 A, 𝟙 B)) = 𝟙 (d.tensor.obj (A, B)) :=
  d.tensor.map_id (A, B)

/-- The tensor bifunctor preserves composition of pairs. -/
@[reassoc] public theorem tensor_map_comp {A B C D E F : DerivedCategory (ModuleCat.{v} R)}
    (f : A ⟶ B) (g : C ⟶ D) (h : B ⟶ E) (k : D ⟶ F) :
    d.tensor.map (show (A, C) ⟶ (B, D) from (f, g)) ≫
      d.tensor.map (show (B, D) ⟶ (E, F) from (h, k)) =
      d.tensor.map (show (A, C) ⟶ (E, F) from (f ≫ h, g ≫ k)) :=
  (d.tensor.map_comp (show (A, C) ⟶ (B, D) from (f, g))
    (show (B, D) ⟶ (E, F) from (h, k))).symm

/-- Evaluation is dinatural in its source. -/
@[reassoc] public theorem evaluation_naturality_left {L L' M : DerivedCategory (ModuleCat.{v} R)}
    (f : L' ⟶ L) :
    d.tensor.map (d.hom.map (f.op, 𝟙 M), 𝟙 L') ≫ d.evaluation L' M =
      d.tensor.map (show (d.hom.obj (Opposite.op L, M), L') ⟶
        (d.hom.obj (Opposite.op L, M), L) from
        (𝟙 (d.hom.obj (Opposite.op L, M)), f)) ≫ d.evaluation L M := by
  rw [evaluation, ← d.homEquiv_naturality_left, Category.comp_id]
  simpa only [evaluation, Category.id_comp] using d.homEquiv_dinaturality f (𝟙 _)

/-- Evaluation is natural in its target. -/
@[reassoc] public theorem evaluation_naturality_right {L M M' : DerivedCategory (ModuleCat.{v} R)}
    (f : M ⟶ M') :
    d.tensor.map (d.hom.map (𝟙 (Opposite.op L), f), 𝟙 L) ≫ d.evaluation L M' =
      d.evaluation L M ≫ f := by
  rw [evaluation, ← d.homEquiv_naturality_left, Category.comp_id]
  simpa only [evaluation, Category.id_comp] using d.homEquiv_naturality_right f (𝟙 _)

attribute [reassoc] tensorAssoc_naturality tensorSwap_naturality

/-- Internalized evaluation is covariantly natural in its tensor argument. -/
public theorem internalCurryMor_naturality_left {K K' L M : DerivedCategory (ModuleCat.{v} R)}
    (f : K ⟶ K') :
    d.tensor.map (𝟙 (d.hom.obj (Opposite.op L, M)), f) ≫ d.internalCurryMor K' L M =
      d.internalCurryMor K L M ≫ d.hom.map ((d.hom.map (f.op, 𝟙 L)).op, 𝟙 M) := by
  apply (d.homEquiv _ _ M).injective
  rw [d.homEquiv_naturality_left, d.homEquiv_dinaturality]
  simp only [internalCurryMor, AddEquiv.apply_symm_apply]
  rw [d.tensorAssoc_naturality_assoc]
  have h := d.tensorAssoc_naturality (𝟙 (d.hom.obj (Opposite.op L, M))) (𝟙 K)
    (d.hom.map (show (Opposite.op K', L) ⟶ (Opposite.op K, L) from (f.op, 𝟙 L)))
  rw [d.tensor_map_id] at h
  rw [reassoc_of% h]
  simp only [← Category.assoc, d.tensor_map_comp, Category.comp_id]
  congr 2
  simp only [Category.assoc]
  rw [d.tensorSwap_naturality_assoc, d.tensorSwap_naturality_assoc,
    d.evaluation_naturality_left]

/-- Internalized evaluation is covariantly natural in its target. -/
public theorem internalCurryMor_naturality_right {K L M M' : DerivedCategory (ModuleCat.{v} R)}
    (f : M ⟶ M') :
    d.tensor.map (d.hom.map (𝟙 (Opposite.op L), f), 𝟙 K) ≫ d.internalCurryMor K L M' =
      d.internalCurryMor K L M ≫
        d.hom.map (𝟙 (Opposite.op (d.hom.obj (Opposite.op K, L))), f) := by
  apply (d.homEquiv _ _ M').injective
  rw [d.homEquiv_naturality_left, d.homEquiv_naturality_right]
  simp only [internalCurryMor, AddEquiv.apply_symm_apply]
  rw [d.tensorAssoc_naturality_assoc, d.tensor_map_id]
  simp only [Category.assoc]
  rw [← d.evaluation_naturality_right]
  simp only [← Category.assoc, d.tensor_map_comp, Category.id_comp, Category.comp_id]

/-- Internalized evaluation is contravariantly natural in its middle argument. -/
public theorem internalCurryMor_naturality_middle {K L L' M : DerivedCategory (ModuleCat.{v} R)}
    (f : L ⟶ L') :
    d.tensor.map (d.hom.map (f.op, 𝟙 M), 𝟙 K) ≫ d.internalCurryMor K L M =
      d.internalCurryMor K L' M ≫ d.hom.map ((d.hom.map (𝟙 (Opposite.op K), f)).op, 𝟙 M) := by
  apply (d.homEquiv _ _ M).injective
  rw [d.homEquiv_naturality_left, d.homEquiv_dinaturality]
  simp only [internalCurryMor, AddEquiv.apply_symm_apply]
  rw [d.tensorAssoc_naturality_assoc, d.tensor_map_id]
  have h := d.tensorAssoc_naturality (𝟙 (d.hom.obj (Opposite.op L', M))) (𝟙 K)
    (d.hom.map (show (Opposite.op K, L) ⟶ (Opposite.op K, L') from
      (𝟙 (Opposite.op K), f)))
  rw [d.tensor_map_id] at h
  rw [reassoc_of% h]
  simp only [← Category.assoc, d.tensor_map_comp, Category.id_comp, Category.comp_id]
  simp only [Category.assoc]
  rw [cancel_epi]
  rw [d.tensorSwap_naturality_assoc, d.evaluation_naturality_right]
  let A := d.hom.obj (Opposite.op L', M)
  let B := d.hom.obj (Opposite.op K, L)
  simpa only [← Category.assoc, d.tensor_map_comp, Category.id_comp, Category.comp_id] using
    congrArg (fun q : d.tensor.obj (A, L) ⟶ M ↦
      d.tensor.map (show (A, d.tensor.obj (K, B)) ⟶ (A, L) from
        (𝟙 A, (d.tensorSwap K B).hom ≫ d.evaluation K L)) ≫ q)
      (d.evaluation_naturality_left (M := M) f)

end DerivedHomAdjunction

namespace Model
open CochainComplex HomComplex
set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R]
/-- The cochain complexes used for the concrete models. -/
abbrev Complex := CochainComplex (ModuleCat.{u} R) ℤ
/-- The full subcategory of K-flat tensor representatives. -/
abbrev KFlatComplexes : ObjectProperty (Complex R) := fun K => K.KFlat
/-- The full subcategory of K-injective target representatives. -/
abbrev KInjectiveComplexes : ObjectProperty (Complex R) := fun K => K.IsKInjective

/-- The ordinary Hom-complex bifunctor, with the pre/postcomposition maps of 0A62. -/
def homComplexFunctor : (Complex R)ᵒᵖ × Complex R ⥤ Complex R where
  obj X := HomComplexR R X.1.unop X.2
  map {X Y} f := Stacks.HomComplex.TensorHomMap.precomp R Y.1.unop X.1.unop X.2 f.1.unop ≫
    Stacks.HomComplex.TensorHomMap.postcomp R Y.1.unop X.2 Y.2 f.2
  map_id X := by
    ext n : 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change ((Cochain.ofHom (𝟙 X.1.unop)).comp z (zero_add n)).comp
      (Cochain.ofHom (𝟙 X.2)) (add_zero n) = z
    apply Cochain.ext
    intro p q hpq
    simp only [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
      Cochain.ofHom_v, HomologicalComplex.id_f, Category.id_comp, Category.comp_id]
  map_comp {X Y Z} f g := by
    ext n : 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Cochain.ext
    intro p q hpq
    change (((Cochain.ofHom (g.1.unop ≫ f.1.unop)).comp z (zero_add n)).comp
      (Cochain.ofHom (f.2 ≫ g.2)) (add_zero n)).v p q hpq =
      (((Cochain.ofHom g.1.unop).comp
        (((Cochain.ofHom f.1.unop).comp z (zero_add n)).comp
          (Cochain.ofHom f.2) (add_zero n)) (zero_add n)).comp
          (Cochain.ofHom g.2) (add_zero n)).v p q hpq
    simp only [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
      Cochain.ofHom_v, HomologicalComplex.comp_f, Category.assoc]


variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]
/-- The ordinary total tensor product on model representatives, followed by localization. -/
abbrev tensorToDerived := ((𝟭 (Complex R)).prod (KFlatComplexes R).ι) ⋙
  tensor (Complex R) ⋙ DerivedCategory.Q
/-- Localization of an arbitrary complex and a K-flat second complex. -/
abbrev tensorSource := (DerivedCategory.Q (C := ModuleCat.{u} R)).prod
  ((KFlatComplexes R).ι ⋙ DerivedCategory.Q)
/-- The ordinary Hom complex on model representatives, followed by localization. -/
abbrev homToDerived := ((𝟭 (Complex R)ᵒᵖ).prod (KInjectiveComplexes R).ι) ⋙
  homComplexFunctor R ⋙ DerivedCategory.Q
/-- Localization of an arbitrary source complex and a K-injective target. -/
abbrev homSource := (DerivedCategory.Q (C := ModuleCat.{u} R)).op.prod
  ((KInjectiveComplexes R).ι ⋙ DerivedCategory.Q)

/-- The signed symmetry of the ordinary total tensor product. -/
def complexSwap (K L : Complex R) : K ⊗ L ≅ L ⊗ K := by
  letI := CochainComplex.Koszul.koszulSymmetric R
  exact β_ K L

/-! ### The flip of the Hom-complex functor, and short exactness from a degreewise splitting -/

/-- The contravariant functor `X ↦ Hom^•(X, I)` from complexes of `R`-modules to complexes,
obtained by flipping the Hom-complex bifunctor at a fixed target `I`. -/
public abbrev homComplexFunctorFlip (R : Type u) [CommRing R]
    (I : CochainComplex (ModuleCat.{u} R) ℤ) :=
  (CategoryTheory.Functor.curry.obj (homComplexFunctor R)).flip.obj I

/-- The functor `X ↦ Hom^•(X, I)` is additive. -/
public lemma homComplexFunctorFlip_additive (R : Type u) [CommRing R]
    (I : CochainComplex (ModuleCat.{u} R) ℤ) : (homComplexFunctorFlip R I).Additive where
  map_add {X Y} f g := by
    ext n : 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change ((Cochain.ofHom (f + g).unop).comp z (zero_add n)).comp
        (Cochain.ofHom (𝟙 I)) (add_zero n) =
      (((Cochain.ofHom f.unop).comp z (zero_add n)).comp
        (Cochain.ofHom (𝟙 I)) (add_zero n)) +
      (((Cochain.ofHom g.unop).comp z (zero_add n)).comp
        (Cochain.ofHom (𝟙 I)) (add_zero n))
    rw [Cochain.comp_id, Cochain.comp_id, Cochain.comp_id]
    change (Cochain.ofHom (f.unop + g.unop)).comp z (zero_add n) =
      (Cochain.ofHom f.unop).comp z (zero_add n) +
        (Cochain.ofHom g.unop).comp z (zero_add n)
    rw [Cochain.ofHom_add]
    exact Cochain.add_comp _ _ _ _

/-- Precomposition of degree-`n` cochains with a family of degreewise maps `f p : X.X p ⟶ Y.X p`,
as a map `Hom^n(Y, I) ⟶ Hom^n(X, I)`; the family need not commute with the differentials. -/
public abbrev cochainPrecomp {X Y I : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : ∀ p, X.X p ⟶ Y.X p) (n : ℤ) :
    (HomComplexR R Y I).X n ⟶ (HomComplexR R X I).X n :=
  ModuleCat.ofHom
    { toFun := fun z ↦ Cochain.mk (fun p q hpq ↦ f p ≫ z.v p q hpq)
      map_add' := by intros; ext; simp [Preadditive.comp_add]
      map_smul' := by intros; ext; simp }

/-- If a short complex of cochain complexes is split in each degree, then applying
`Hom^•(-, I)` to it gives a short exact sequence of Hom complexes. -/
public lemma homComplex_shortExact_of_degreewiseSplit
    (R : Type u) [CommRing R] (I : CochainComplex (ModuleCat.{u} R) ℤ)
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (σ : ∀ n, (S.map (HomologicalComplex.eval _ _ n)).Splitting) :
    let := homComplexFunctorFlip_additive R I
    (S.op.map (homComplexFunctorFlip R I)).ShortExact := by
  let := homComplexFunctorFlip_additive R I
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  apply ShortComplex.Splitting.shortExact
  refine { r := cochainPrecomp R (fun p ↦ (σ p).s) n
           s := cochainPrecomp R (fun p ↦ (σ p).r) n
           f_r := ?_, s_g := ?_, id := ?_ }
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change Cochain S.X₃ I n at z
    apply Cochain.ext
    intro p q hpq
    change (σ p).s ≫ (((Cochain.ofHom S.g).comp z (zero_add n)).comp
      (Cochain.ofHom (𝟙 I)) (add_zero n)).v p q hpq = z.v p q hpq
    simp only [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
      Cochain.ofHom_v, HomologicalComplex.id_f, Category.comp_id, ← Category.assoc]
    simpa using congrArg (fun f ↦ f ≫ z.v p q hpq) (σ p).s_g
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change Cochain S.X₁ I n at z
    apply Cochain.ext
    intro p q hpq
    change (((Cochain.ofHom S.f).comp
      (Cochain.mk (fun p q hpq ↦ (σ p).r ≫ z.v p q hpq)) (zero_add n)).comp
      (Cochain.ofHom (𝟙 I)) (add_zero n)).v p q hpq = z.v p q hpq
    simp only [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
      Cochain.ofHom_v, HomologicalComplex.id_f, Category.comp_id, Cochain.mk_v,
      ← Category.assoc]
    simpa using congrArg (fun f ↦ f ≫ z.v p q hpq) (σ p).f_r
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change Cochain S.X₂ I n at z
    apply Cochain.ext
    intro p q hpq
    change ((((Cochain.ofHom S.g).comp
      (Cochain.mk (fun p q hpq ↦ (σ p).s ≫ z.v p q hpq)) (zero_add n)).comp
      (Cochain.ofHom (𝟙 I)) (add_zero n)).v p q hpq) +
      (show S.X₂.X p ⟶ S.X₁.X p from (σ p).r) ≫ (((Cochain.ofHom S.f).comp z (zero_add n)).comp
      (Cochain.ofHom (𝟙 I)) (add_zero n)).v p q hpq = z.v p q hpq
    simp only [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
      Cochain.ofHom_v, HomologicalComplex.id_f, Category.comp_id, Cochain.mk_v]
    have hid := (σ p).id
    change (show S.X₂.X p ⟶ S.X₁.X p from (σ p).r) ≫ S.f.f p +
      S.g.f p ≫ (show S.X₃.X p ⟶ S.X₂.X p from (σ p).s) = 𝟙 (S.X₂.X p) at hid
    simpa only [Preadditive.add_comp, Category.assoc, Category.id_comp, add_comm] using
      congrArg (fun f : S.X₂.X p ⟶ S.X₂.X p ↦ f ≫ z.v p q hpq) hid

end Model

set_option backward.isDefEq.respectTransparency false in
/-- The concrete construction data for the derived tensor--Hom adjunction. This is the
auxiliary construction `ch15-aux-derived-tensor-hom`, not the assertion of Tag 0A63.

The model API uses the existing monoidal category of complexes, whose module universe equals
the ring universe. `derivedHomAdjunctionULift` applies this construction to the lifted ring
to obtain these same concrete comparisons in an independently chosen module universe. -/
public structure DerivedHomData (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] extends DerivedHomAdjunction R where
  /-- The natural localization comparison on all complexes and K-flat second arguments. -/
  tensorComparison : Model.tensorSource R ⋙ tensor ≅ Model.tensorToDerived R
  /-- The natural localization comparison on all source complexes and K-injective targets. -/
  homComparison : Model.homSource R ⋙ hom ≅ Model.homToDerived R
  /-- The tensor symmetry is the localized signed interchange map. -/
  tensorSwap_comparison (K L : CochainComplex (ModuleCat R) ℤ)
      (hK : K.KFlat) (hL : L.KFlat) :
    (tensorSwap (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)).hom ≫
      (tensorComparison.app (L, ⟨K, hK⟩)).hom =
      (tensorComparison.app (K, ⟨L, hL⟩)).hom ≫
        DerivedCategory.Q.map (Model.complexSwap R K L).hom
  /-- On K-flat/K-injective models, the inverse equivalence is the concrete transpose defined
  by the tensor--Hom unit `Stacks.HomComplex.TensorHomMap.Phi`. -/
  homEquiv_symm_map_eq (K L I : CochainComplex (ModuleCat R) ℤ) (hL : L.KFlat)
      [I.IsKInjective] (h : K ⊗ L ⟶ I) :
    (homEquiv (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
        (DerivedCategory.Q.obj I)).symm
        ((tensorComparison.app (K, ⟨L, hL⟩)).hom ≫ DerivedCategory.Q.map h) =
      DerivedCategory.Q.map
          (Stacks.HomComplex.TensorHomMap.Phi R K L ≫ Stacks.HomComplex.TensorHomMap.postcomp R L (K
            ⊗ L) I h) ≫
        (homComparison.app (Opposite.op L, ⟨I, inferInstance⟩)).inv

  /-- The adjunction-defined internalized evaluation is computed by the chain-level map of
  Stacks 0A60 on K-flat/K-injective representatives. -/
  internalCurryMor_comparison
      (K L M : CochainComplex (ModuleCat R) ℤ) (hK : K.KFlat)
      [L.IsKInjective] [M.IsKInjective] :
    toDerivedHomAdjunction.internalCurryMor (DerivedCategory.Q.obj K)
        (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M) =
      tensor.map ((homComparison.app (Opposite.op L, ⟨M, inferInstance⟩)).hom, 𝟙
        (DerivedCategory.Q.obj K)) ≫
        (tensorComparison.app (CochainComplex.HomComplexR R L M, ⟨K, hK⟩)).hom ≫
        DerivedCategory.Q.map
          (ChainEvaluation.chainEvaluation K L M) ≫
        (homComparison.app (Opposite.op (CochainComplex.HomComplexR R K L), ⟨M,
          inferInstance⟩)).inv ≫
        hom.map (show
          (Opposite.op (DerivedCategory.Q.obj (CochainComplex.HomComplexR R K L)),
            DerivedCategory.Q.obj M) ⟶
          (Opposite.op (hom.obj (Opposite.op (DerivedCategory.Q.obj K), DerivedCategory.Q.obj L)),
            DerivedCategory.Q.obj M) from
          ((homComparison.app (Opposite.op K, ⟨L, inferInstance⟩)).hom.op,
            𝟙 (DerivedCategory.Q.obj M)))

namespace DerivedHomData
set_option backward.isDefEq.respectTransparency false
variable {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)] (d : DerivedHomData R)
/-- The component of the natural tensor comparison at a K-flat second representative. -/
def tensorIso (K L : Model.Complex R) (hL : L.KFlat) :
    d.tensor.obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj (K ⊗ L) := d.tensorComparison.app (K, ⟨L, hL⟩)
/-- The component of the natural Hom comparison at a K-injective target. -/
def homIso (L I : Model.Complex R) [I.IsKInjective] :
    d.hom.obj (Opposite.op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj (CochainComplex.HomComplexR R L I) :=
  d.homComparison.app (Opposite.op L, ⟨I, inferInstance⟩)
/-- The tensor comparison is natural in both chain maps. -/
theorem tensorIso_naturality {K K' L L' : Model.Complex R} (f : K ⟶ K') (g : L ⟶ L')
    (hL : L.KFlat) (hL' : L'.KFlat) :
    d.tensor.map (DerivedCategory.Q.map f, DerivedCategory.Q.map g) ≫
      (d.tensorIso K' L' hL').hom =
      (d.tensorIso K L hL).hom ≫ DerivedCategory.Q.map (f ⊗ₘ g) :=
  d.tensorComparison.hom.naturality
    (show (K, ⟨L, hL⟩) ⟶ (K', ⟨L', hL'⟩) from (f, ⟨g⟩))

/-- The K-injective comparison is natural in both chain maps, with the source contravariant. -/
@[reassoc] theorem homIso_naturality {L L' I I' : Model.Complex R}
    [I.IsKInjective] [I'.IsKInjective] (f : L' ⟶ L) (g : I ⟶ I') :
    d.hom.map ((DerivedCategory.Q.map f).op, DerivedCategory.Q.map g) ≫
      (d.homIso L' I').hom =
      (d.homIso L I).hom ≫ DerivedCategory.Q.map
        (Stacks.HomComplex.TensorHomMap.precomp R L' L I f ≫ Stacks.HomComplex.TensorHomMap.postcomp
          R L' I I' g) :=
  d.homComparison.hom.naturality
    (show (Opposite.op L, ⟨I, inferInstance⟩) ⟶
      (Opposite.op L', ⟨I', inferInstance⟩) from (f.op, ⟨g⟩))

/-- Tensoring on the right by the localized complex unit. -/
abbrev tensorRightUnit : DerivedCategory (ModuleCat.{u} R) ⥤
    DerivedCategory (ModuleCat.{u} R) :=
  (curry.obj d.tensor).flip.obj (DerivedCategory.Q.obj (𝟙_ (Model.Complex R)))
omit [HasDerivedCategory.{w} (ModuleCat.{u} R)] in
/-- The ordinary complex tensor unit is K-flat. -/
lemma unit_kFlat : (𝟙_ (Model.Complex R)).KFlat := by
  intro M hM
  exact HomologicalComplex.Acyclic.of_iso (ρ_ M).symm hM

/-- Restriction of the natural tensor comparison to the unit in its second variable. -/
def tensorRightUnitComparison :
    DerivedCategory.Q ⋙ d.tensorRightUnit ≅
      tensorRight (𝟙_ (Model.Complex R)) ⋙ DerivedCategory.Q :=
  NatIso.ofComponents (fun K => d.tensorIso K _ (unit_kFlat (R := R))) (by
    intro K L f
    simpa using d.tensorIso_naturality f (𝟙 (𝟙_ (Model.Complex R)))
      (unit_kFlat (R := R)) (unit_kFlat (R := R)))

/-- The right unitor obtained by descending the ordinary complex unitor through localization. -/
def tensorRightUnitor : d.tensorRightUnit ≅ 𝟭 _ := by
  letI : Localization.Lifting DerivedCategory.Q (HomologicalComplex.quasiIso _ _)
      (tensorRight (𝟙_ (Model.Complex R)) ⋙ DerivedCategory.Q) d.tensorRightUnit :=
    ⟨d.tensorRightUnitComparison⟩
  exact Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso _ _)
    (tensorRight (𝟙_ (Model.Complex R)) ⋙ DerivedCategory.Q) DerivedCategory.Q
    d.tensorRightUnit (𝟭 _)
    (isoWhiskerRight (rightUnitorNatIso (Model.Complex R)) DerivedCategory.Q)

/-- The descended right unitor is represented by the ordinary right unitor. -/
theorem tensorRightUnitor_comparison (K : Model.Complex R) :
    (d.tensorRightUnitor.app (DerivedCategory.Q.obj K)).hom =
      (d.tensorIso K _ (unit_kFlat (R := R))).hom ≫ DerivedCategory.Q.map (ρ_ K).hom := by
  simp [tensorRightUnitor, Localization.liftNatIso, Localization.liftNatTrans_app,
    tensorRightUnitComparison]

/-- The left unitor obtained from the localized signed symmetry and the descended right unitor. -/
def tensorUnitLeft (K : DerivedCategory (ModuleCat.{u} R)) :
    d.tensor.obj (DerivedCategory.Q.obj (𝟙_ (Model.Complex R)), K) ≅ K :=
  d.tensorSwap _ K ≪≫ d.tensorRightUnitor.app K

/-- Naturality of the left unitor follows from the two natural isomorphisms defining it. -/
theorem tensorUnitLeft_naturality {K K' : DerivedCategory (ModuleCat.{u} R)}
    (f : K ⟶ K') :
    d.tensor.map (𝟙 (DerivedCategory.Q.obj (𝟙_ (Model.Complex R))), f) ≫
      (d.tensorUnitLeft K').hom = (d.tensorUnitLeft K).hom ≫ f := by
  dsimp only [tensorUnitLeft, Iso.trans_hom]
  rw [← Category.assoc, d.tensorSwap_naturality, Category.assoc]
  simpa [tensorRightUnit, Category.assoc] using congrArg ((d.tensorSwap _ K).hom ≫ ·)
    (d.tensorRightUnitor.hom.naturality f)

/-- The derived left unitor agrees with the ordinary left unitor on K-flat representatives. -/
theorem tensorUnitLeft_comparison (K : Model.Complex R) (hK : K.KFlat) :
    (d.tensorIso (𝟙_ (Model.Complex R)) K hK).hom ≫
      DerivedCategory.Q.map (λ_ K).hom = (d.tensorUnitLeft (DerivedCategory.Q.obj K)).hom := by
  dsimp only [tensorUnitLeft, Iso.trans_hom]
  rw [d.tensorRightUnitor_comparison]
  dsimp only [tensorIso]
  rw [← Category.assoc, d.tensorSwap_comparison _ K (unit_kFlat (R := R)) hK]
  rw [Category.assoc, ← Functor.map_comp]
  congr 2
  let := CochainComplex.Koszul.koszulSymmetric R
  exact (braiding_rightUnitor K).symm

/-- Degree-zero derived Hom, expressed as morphisms from the tensor unit. The unit is
constructed by localization, so it is shared by all subsequent uses of the adjunction. -/
def homZeroEquiv (K M : DerivedCategory (ModuleCat R)) :
    (DerivedCategory.Q.obj (𝟙_ (Model.Complex R)) ⟶
      d.hom.obj (Opposite.op K, M)) ≃+ (K ⟶ M) where
  toFun a := (d.tensorUnitLeft K).inv ≫ d.homEquiv _ K M a
  invFun a := (d.homEquiv _ K M).symm ((d.tensorUnitLeft K).hom ≫ a)
  left_inv a := by simp
  right_inv a := by simp
  map_add' a b := by simp [Preadditive.comp_add]

/-- The unit identification on representatives is the transpose defined by
  `Stacks.HomComplex.TensorHomMap.Phi`. -/
theorem homZeroEquiv_symm_map (L I : Model.Complex R) (hL : L.KFlat)
    [I.IsKInjective] (f : L ⟶ I) :
    (d.homZeroEquiv (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj I)).symm
        (DerivedCategory.Q.map f) =
      DerivedCategory.Q.map
        (Stacks.HomComplex.TensorHomMap.Phi R (𝟙_ (Model.Complex R)) L ≫
          Stacks.HomComplex.TensorHomMap.postcomp R L ((𝟙_ (Model.Complex R)) ⊗ L) I ((λ_ L).hom ≫
            f)) ≫
        (d.homIso L I).inv := by
  change (d.homEquiv _ _ _).symm
    ((d.tensorUnitLeft (DerivedCategory.Q.obj L)).hom ≫ DerivedCategory.Q.map f) = _
  rw [← d.tensorUnitLeft_comparison L hL, Category.assoc, ← Functor.map_comp]
  exact d.homEquiv_symm_map_eq _ L I hL ((λ_ L).hom ≫ f)

end DerivedHomData

namespace Construction

open Limits

set_option backward.isDefEq.respectTransparency false

attribute [local instance] HasDerivedCategory.standard

-- The derived category here has an independent Hom universe `w`.
private lemma homotopy_quasiIso_iff_isIso_Qh {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    {X Y : KC R} (f : X ⟶ Y) :
    HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ) f ↔
      IsIso ((DerivedCategory.Qh (C := ModuleCat.{u} R)).map f) :=
  (DerivedCategory.isIso_Qh_map_iff f).symm

private lemma kFlat_tright_preserves_quasiIso {R : Type u} [CommRing R]
    (K : C R) (hK : K.KFlat) :
    HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ) ≤
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)).inverseImage
        (Tright K) := by
  let P := HomotopyCategory.subcategoryAcyclic (ModuleCat.{u} R)
  obtain ⟨e, he⟩ := TotalTensorComplex.tright_isTriangulated K
  let := e
  let := he
  have h : P ≤ P.inverseImage (Tright K) := by
    intro X hX
    obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    have hM : M.Acyclic :=
      (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic M).1 hX
    change P ((HomotopyCategory.quotient _ _).obj (M ⊗ K))
    exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2
      (hK M hM)
  rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  intro X Y f hf
  exact (P.inverseImage_trW_iff (F := Tright K) f).1 (P.trW_monotone h f hf)

attribute [local instance] homotopyTensorLifting

private noncomputable abbrev kFlatQ (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    (KFlatObjects R).FullSubcategory ⥤ DerivedCategory (ModuleCat.{u} R) :=
  (KFlatObjects R).ι ⋙ DerivedCategory.Qh

private lemma kFlatQ_isLocalization (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    (kFlatQ R).IsLocalization (KFlatQuasiIso R) := by
  have := kFlatLocalizer_isLocalizedEquivalence (R := R)
  exact LocalizerMorphism.IsLocalizedEquivalence.isLocalization
    (kFlatLocalizer R) (DerivedCategory.Qh (C := ModuleCat.{u} R))

attribute [local instance] kFlatQ_isLocalization

private lemma kFlatQ_essSurj (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] : (kFlatQ R).EssSurj :=
  Localization.essSurj (kFlatQ R) (KFlatQuasiIso R)

attribute [local instance] kFlatQ_essSurj

private noncomputable abbrev kFlatTensorToDerived (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :=
  ((((Functor.whiskeringLeft₂ (DerivedCategory (ModuleCat.{u} R))).obj (KFlatObjects R).ι).obj
    (KFlatObjects R).ι).obj
      (homotopyTensor R ⋙ (Functor.whiskeringRight _ _ _).obj
        (DerivedCategory.Qh (C := ModuleCat.{u} R))))

set_option backward.isDefEq.respectTransparency false in
private lemma kFlatTensorToDerived_inverts {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [SymmetricCategory (C R)] :
    MorphismProperty.IsInvertedBy₂ (KFlatQuasiIso R) (KFlatQuasiIso R)
      (kFlatTensorToDerived R) := by
  rintro ⟨K, L⟩ ⟨K', L'⟩ ⟨f, g⟩ ⟨hf, hg⟩
  have h₁ := homotopyTensor_right_preserves_quasiIso L.1 L.2 f.hom hf
  have h₁' : IsIso ((DerivedCategory.Qh (C := ModuleCat.{u} R)).map
      (((homotopyTensor R).flip.obj L.1).map f.hom)) :=
    (homotopy_quasiIso_iff_isIso_Qh _).1 h₁
  have h₂ := homotopyTensor_right_preserves_quasiIso K'.1 K'.2 g.hom hg
  have h₂' : IsIso ((DerivedCategory.Qh (C := ModuleCat.{u} R)).map
      (((homotopyTensor R).flip.obj K'.1).map g.hom)) :=
    (homotopy_quasiIso_iff_isIso_Qh _).1 h₂
  have h₃ := (NatIso.isIso_map_iff (isoWhiskerRight ((homotopyTensorBraiding R).app K'.1)
    (DerivedCategory.Qh (C := ModuleCat.{u} R))) g.hom).2 h₂'
  exact IsIso.comp_isIso' h₁' h₃

private noncomputable def derivedTensor (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [SymmetricCategory (C R)] :
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R) ⥤
      DerivedCategory (ModuleCat.{u} R) :=
  Localization.lift₂ (kFlatTensorToDerived R) kFlatTensorToDerived_inverts
    (kFlatQ R) (kFlatQ R)

@[instance_reducible]
private noncomputable def derivedTensorLifting (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [SymmetricCategory (C R)] :
    Localization.Lifting₂ (kFlatQ R) (kFlatQ R) (KFlatQuasiIso R) (KFlatQuasiIso R)
      (kFlatTensorToDerived R) (derivedTensor R) := by
  unfold derivedTensor
  infer_instance

attribute [local instance] derivedTensorLifting

private noncomputable def derivedTensorComparisonIso (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [SymmetricCategory (C R)] :=
  Localization.Lifting₂.iso (kFlatQ R) (kFlatQ R) (KFlatQuasiIso R) (KFlatQuasiIso R)
    (kFlatTensorToDerived R) (derivedTensor R)

private noncomputable def derivedTensorComparison {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [SymmetricCategory (C R)] (K L : C R) (hK : K.KFlat) (hL : L.KFlat) :
    ((derivedTensor R).obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj (K ⊗ L) :=
  (((derivedTensor R).mapIso
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).app K).symm).app
      (DerivedCategory.Q.obj L)) ≪≫
    ((derivedTensor R).obj ((DerivedCategory.Qh).obj
      ((HomotopyCategory.quotient _ _).obj K))).mapIso
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).app L).symm ≪≫
    ((derivedTensorComparisonIso R).app
      ⟨(HomotopyCategory.quotient _ _).obj K, hK⟩).app
      ⟨(HomotopyCategory.quotient _ _).obj L, hL⟩ ≪≫
    DerivedCategory.Qh.mapIso (homotopyTensorComparison K L) ≪≫
    (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).app (K ⊗ L)


private noncomputable abbrev mixedTensorToDerived (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :=
  homotopyTensor R ⋙
    (whiskeringRight _ _ _).obj (DerivedCategory.Qh (C := ModuleCat.{u} R)) ⋙
    (whiskeringLeft _ _ _).obj (KFlatObjects R).ι

private lemma mixedTensorToDerived_inverts (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    (HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)).IsInvertedBy
      (mixedTensorToDerived R) := by
  intro X Y f hf
  have h (L : (KFlatObjects R).FullSubcategory) :
      IsIso (((mixedTensorToDerived R).map f).app L) :=
    (DerivedCategory.isIso_Qh_map_iff _).2
      (homotopyTensor_right_preserves_quasiIso L.1 L.2 f hf)
  exact NatIso.isIso_of_isIso_app _

private noncomputable def mixedTensor (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    DerivedCategory (ModuleCat.{u} R) ⥤
      (KFlatObjects R).FullSubcategory ⥤ DerivedCategory (ModuleCat.{u} R) :=
  Localization.lift (mixedTensorToDerived R) (mixedTensorToDerived_inverts R)
    DerivedCategory.Qh

private noncomputable def mixedTensorComparison (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    DerivedCategory.Qh ⋙ mixedTensor R ≅ mixedTensorToDerived R :=
  Localization.fac (mixedTensorToDerived R) (mixedTensorToDerived_inverts R)
    DerivedCategory.Qh

private noncomputable abbrev derivedTensorRestricted (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [SymmetricCategory (C R)] :=
  derivedTensor R ⋙ (whiskeringLeft _ _ _).obj (kFlatQ R)

private noncomputable def derivedTensorMixedComparison (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [SymmetricCategory (C R)] :
    derivedTensorRestricted R ≅ mixedTensor R := by
  letI : Localization.Lifting (kFlatQ R) (KFlatQuasiIso R)
      (kFlatTensorToDerived R) (derivedTensorRestricted R) :=
    ⟨derivedTensorComparisonIso R⟩
  letI : Localization.Lifting (kFlatQ R) (KFlatQuasiIso R)
      (kFlatTensorToDerived R) (mixedTensor R) :=
    ⟨isoWhiskerLeft (KFlatObjects R).ι (mixedTensorComparison R)⟩
  exact Localization.liftNatIso (kFlatQ R) (KFlatQuasiIso R)
    (kFlatTensorToDerived R) (kFlatTensorToDerived R) _ _ (Iso.refl _)

private noncomputable abbrev kFlatQuotient (R : Type u) [CommRing R] :
    (Model.KFlatComplexes R).FullSubcategory ⥤ (KFlatObjects R).FullSubcategory :=
  (KFlatObjects R).lift
    ((Model.KFlatComplexes R).ι ⋙ HomotopyCategory.quotient _ _)
    (fun K => K.2)

private noncomputable def mixedModelComparison (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [SymmetricCategory (C R)] :
    (((whiskeringLeft₂ (DerivedCategory (ModuleCat.{u} R))).obj DerivedCategory.Q).obj
      ((Model.KFlatComplexes R).ι ⋙ DerivedCategory.Q)).obj (derivedTensor R) ≅
    (((whiskeringLeft₂ (DerivedCategory (ModuleCat.{u} R))).obj (𝟭 (C R))).obj
      (Model.KFlatComplexes R).ι).obj
        (curriedTensor (C R) ⋙ (whiskeringRight _ _ _).obj DerivedCategory.Q) := by
  let q := DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)
  let h := Localization.Lifting₂.iso
    (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ))
    (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ))
    (homotopyEquivalences R) (homotopyEquivalences R)
    (curriedTensor (C R) ⋙ (Functor.whiskeringRight _ _ _).obj
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ))) (homotopyTensor R)
  exact ((((whiskeringLeft₂ (DerivedCategory (ModuleCat.{u} R))).mapIso q.symm).app
      ((Model.KFlatComplexes R).ι ⋙ DerivedCategory.Q)).app (derivedTensor R)) ≪≫
    ((((whiskeringLeft₂ (DerivedCategory (ModuleCat.{u} R))).obj
      (HomotopyCategory.quotient _ _ ⋙ DerivedCategory.Qh)).mapIso
        (isoWhiskerLeft (Model.KFlatComplexes R).ι q.symm)).app (derivedTensor R)) ≪≫
    isoWhiskerLeft (HomotopyCategory.quotient _ _ ⋙ DerivedCategory.Qh)
      (isoWhiskerRight (derivedTensorMixedComparison R)
        ((whiskeringLeft _ _ _).obj (kFlatQuotient R))) ≪≫
    isoWhiskerLeft (HomotopyCategory.quotient _ _)
      (isoWhiskerRight (mixedTensorComparison R)
        ((whiskeringLeft _ _ _).obj (kFlatQuotient R))) ≪≫
    (((whiskeringLeft₂ (DerivedCategory (ModuleCat.{u} R))).obj (𝟭 (C R))).obj
      (Model.KFlatComplexes R).ι).mapIso
      (isoWhiskerRight h ((whiskeringRight _ _ _).obj DerivedCategory.Qh) ≪≫
        isoWhiskerLeft (curriedTensor (C R))
          ((whiskeringRight (C R) (C R) (DerivedCategory (ModuleCat.{u} R))).mapIso q))

private noncomputable def tensorComparison (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [SymmetricCategory (C R)] :
    Model.tensorSource R ⋙ uncurry.obj (derivedTensor R) ≅ Model.tensorToDerived R := by
  let e := uncurry.mapIso (mixedModelComparison R)
  refine NatIso.ofComponents (fun X => e.app X) ?_
  intro X Y f
  have h := e.hom.naturality f
  change (((derivedTensor R).map (DerivedCategory.Q.map f.1)).app
      (DerivedCategory.Q.obj X.2.obj) ≫
      ((derivedTensor R).obj (DerivedCategory.Q.obj Y.1)).map
        (DerivedCategory.Q.map f.2.hom)) ≫ (e.app Y).hom =
    (e.app X).hom ≫ (DerivedCategory.Q.map (f.1 ▷ X.2.obj) ≫
      DerivedCategory.Q.map (Y.1 ◁ f.2.hom)) at h
  change (((derivedTensor R).map (DerivedCategory.Q.map f.1)).app
      (DerivedCategory.Q.obj X.2.obj) ≫
      ((derivedTensor R).obj (DerivedCategory.Q.obj Y.1)).map
        (DerivedCategory.Q.map f.2.hom)) ≫ (e.app Y).hom =
    (e.app X).hom ≫ DerivedCategory.Q.map (f.1 ⊗ₘ f.2.hom)
  rw [MonoidalCategory.tensorHom_def, Functor.map_comp]
  exact h


private noncomputable def derivedTensorBraiding (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [SymmetricCategory (C R)] : derivedTensor R ≅ (derivedTensor R).flip := by
  let e : kFlatTensorToDerived R ≅ (kFlatTensorToDerived R).flip :=
    (((whiskeringLeft₂ (DerivedCategory (ModuleCat.{u} R))).obj (KFlatObjects R).ι).obj
      (KFlatObjects R).ι).mapIso
      (isoWhiskerRight (homotopyTensorBraiding R)
        ((whiskeringRight _ _ _).obj (DerivedCategory.Qh (C := ModuleCat.{u} R))))
  exact Localization.lift₂NatIso (kFlatQ R) (kFlatQ R) (KFlatQuasiIso R) (KFlatQuasiIso R)
    (kFlatTensorToDerived R) (kFlatTensorToDerived R).flip
    (derivedTensor R) (derivedTensor R).flip e


set_option backward.isDefEq.respectTransparency false in
private lemma derivedTensorBraiding_app {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [SymmetricCategory (C R)] (K L : (KFlatObjects R).FullSubcategory) :
    ((derivedTensorBraiding R).hom.app ((kFlatQ R).obj K)).app ((kFlatQ R).obj L) =
      ((derivedTensorComparisonIso R).hom.app K).app L ≫
        DerivedCategory.Qh.map (((homotopyTensorBraiding R).hom.app K.1).app L.1) ≫
        ((derivedTensorComparisonIso R).inv.app L).app K := by
  dsimp only [derivedTensorBraiding, Localization.lift₂NatIso]
  rw [Localization.lift₂NatTrans_app_app]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private lemma derivedTensorBraiding_naturality {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [SymmetricCategory (C R)] {K K' L L' : DerivedCategory (ModuleCat.{u} R)} (f : K ⟶ K') (g : L ⟶
      L') :
    ((derivedTensor R).map f).app L ≫ ((derivedTensor R).obj K').map g ≫
        ((derivedTensorBraiding R).hom.app K').app L' =
      ((derivedTensorBraiding R).hom.app K).app L ≫
        ((derivedTensor R).map g).app K ≫ ((derivedTensor R).obj L').map f := by
  have h := (uncurry.map (derivedTensorBraiding R).hom).naturality
    ((f, g) : (K, L) ⟶ (K', L'))
  simp only [uncurry_obj_map, uncurry_map_app, Category.assoc,
    flip_obj_obj, flip_obj_map, flip_map_app] at h
  rw [((derivedTensor R).map g).naturality f] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
private lemma derivedTensorComparison_braiding {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [SymmetricCategory (C R)] (K L : C R) (hK : K.KFlat) (hL : L.KFlat) :
    ((derivedTensorBraiding R).hom.app (DerivedCategory.Q.obj K)).app
        (DerivedCategory.Q.obj L) ≫ (derivedTensorComparison L K hL hK).hom =
      (derivedTensorComparison K L hK hL).hom ≫ DerivedCategory.Q.map (β_ K L).hom := by
  dsimp only [derivedTensorComparison, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv]
  simp only [Category.assoc]
  erw [← derivedTensorBraiding_naturality_assoc]
  erw [derivedTensorBraiding_app
    ⟨(HomotopyCategory.quotient _ _).obj K, hK⟩
    ⟨(HomotopyCategory.quotient _ _).obj L, hL⟩]
  rw [homotopyTensorBraiding_app]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_app_assoc,
    Iso.map_inv_hom_id_assoc, DerivedCategory.quotientCompQhIso_hom_naturality]
  rfl

/-- The K-injective objects of the homotopy category of complexes of `R`-modules. -/
abbrev KInjectiveObjects (R : Type u) [CommRing R] : ObjectProperty (KC R) :=
  fun I => CochainComplex.IsKInjective I.as

private noncomputable abbrev kInjectiveQ (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    (KInjectiveObjects R).FullSubcategory ⥤ DerivedCategory (ModuleCat.{u} R) :=
  (KInjectiveObjects R).ι ⋙ DerivedCategory.Qh

private lemma kInjectiveQ_map_bijective (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (X Y : (KInjectiveObjects R).FullSubcategory) :
    Function.Bijective ((kInjectiveQ R).map : (X ⟶ Y) → _) := by
  let : CochainComplex.IsKInjective Y.obj.as := Y.property
  exact (CochainComplex.IsKInjective.Qh_map_bijective X.obj Y.obj.as).comp
    (Functor.FullyFaithful.ofFullyFaithful (KInjectiveObjects R).ι).homEquiv.bijective

private lemma kInjectiveQ_full (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] : (kInjectiveQ R).Full where
  map_surjective := (kInjectiveQ_map_bijective R _ _).surjective

private lemma kInjectiveQ_faithful (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] : (kInjectiveQ R).Faithful where
  map_injective h := (kInjectiveQ_map_bijective R _ _).injective h

private lemma kInjectiveQ_essSurj (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] : (kInjectiveQ R).EssSurj := by
  refine ⟨fun X ↦ ?_⟩
  obtain ⟨I, f, hf, hI⟩ := CochainComplex.exists_quasiIso_isKInjective
    (DerivedCategory.Q.objPreimage X)
  let := hf
  refine ⟨⟨(HomotopyCategory.quotient _ _).obj I, hI⟩, ⟨?_⟩⟩
  exact (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).app I ≪≫
    (asIso (DerivedCategory.Q.map f)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso X

attribute [local instance] kInjectiveQ_full kInjectiveQ_faithful kInjectiveQ_essSurj

private noncomputable def kInjectiveEquivalence (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    (KInjectiveObjects R).FullSubcategory ≌ DerivedCategory (ModuleCat.{u} R) :=
  haveI : (kInjectiveQ R).IsEquivalence :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  (kInjectiveQ R).asEquivalence

open CochainComplex HomComplex

/-- The map on cocycles induced by a morphism of Hom complexes. -/
public def homCocyclesMap {R : Type u} [CommRing R] {K L K' L' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : HomComplexR R K L ⟶ HomComplexR R K' L') (n : ℤ) :
    Cocycle K L n →+ Cocycle K' L' n where
  toFun z := ⟨(f.f n).hom (z : Cochain K L n), by
    change δ n (n + 1) ((f.f n).hom (z : Cochain K L n)) = 0
    rw [homComplexMap_δ f n (n + 1) (z : Cochain K L n), z.δ_eq_zero]
    exact (f.f (n + 1)).hom.map_zero⟩
  map_zero' := Subtype.ext (f.f n).hom.map_zero
  map_add' x y := Subtype.ext ((f.f n).hom.map_add (x : Cochain K L n) (y : Cochain K L n))

/-- The map on cohomology classes induced by a morphism of Hom complexes. -/
public def homClassesMap {R : Type u} [CommRing R] {K L K' L' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : HomComplexR R K L ⟶ HomComplexR R K' L') (n : ℤ) :
    CohomologyClass K L n →+ CohomologyClass K' L' n :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom K' L' n).comp (homCocyclesMap f n)) (by
      rintro z ⟨m, hm, b, hb⟩
      change CohomologyClass.mk (homCocyclesMap f n z) = 0
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ m hm]
      refine ⟨(f.f m).hom b, ?_⟩
      change δ m n ((f.f m).hom b) = (f.f n).hom (z : Cochain K L n)
      rw [homComplexMap_δ f m n b, hb])

/-- The left homology map data, in each degree `n`, of the morphism of underlying complexes of
abelian groups induced by a morphism of Hom complexes; it is given by `homCocyclesMap` and
`homClassesMap`. -/
public def homLeftHomologyMapData {R : Type u} [CommRing R]
    {K L K' L' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : HomComplexR R K L ⟶ HomComplexR R K' L') (n : ℤ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor AddCommGrpCat (.up ℤ) n).map
        (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).map f))
      (leftHomologyData K L n) (leftHomologyData K' L' n) := by
  let F := ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).map f
  refine { φK := AddCommGrpCat.ofHom (homCocyclesMap f n)
           φH := AddCommGrpCat.ofHom (homClassesMap f n)
           commi := ?_, commf' := ?_, commπ := ?_ }
  · ext z; rfl
  · have hi : AddCommGrpCat.ofHom (homCocyclesMap f n) ≫
          (leftHomologyData K' L' n).i =
        (leftHomologyData K L n).i ≫ F.f n := by ext z; rfl
    rw [← cancel_mono (leftHomologyData K' L' n).i, Category.assoc, hi, ← Category.assoc,
      ShortComplex.LeftHomologyData.f'_i, Category.assoc, ShortComplex.LeftHomologyData.f'_i]
    exact ((HomologicalComplex.shortComplexFunctor _ _ n).map F).comm₁₂.symm
  · ext z; rfl

private lemma homClassesMap_precomp {R : Type u} [CommRing R] {K K' L : C R}
    (f : K' ⟶ K) (n : ℤ) (z : Cocycle K L n) :
    homClassesMap (Stacks.HomComplex.TensorHomMap.precomp R K' K L f) n (CohomologyClass.mk z) =
      CohomologyClass.mk (z.precomp f) := rfl

/-- Postcomposition with `f : L ⟶ L'` sends the class of a cocycle `z` to the class of
`z.postcomp f`. -/
public lemma homClassesMap_postcomp {R : Type u} [CommRing R]
    {K L L' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : L ⟶ L') (n : ℤ) (z : Cocycle K L n) :
    homClassesMap (Stacks.HomComplex.TensorHomMap.postcomp R K L L' f) n (CohomologyClass.mk z) =
      CohomologyClass.mk (z.postcomp f) := rfl

private lemma homClassesMap_precomp_toHom {R : Type u} [CommRing R] {K K' L : C R}
    (f : K' ⟶ K) (n : ℤ) (z : CohomologyClass K L n) :
    CohomologyClass.toHom (homClassesMap (Stacks.HomComplex.TensorHomMap.precomp R K' K L f) n z) =
      (HomotopyCategory.quotient _ _).map f ≫ CohomologyClass.toHom z := by
  obtain ⟨z, rfl⟩ := z.mk_surjective
  rw [homClassesMap_precomp, CohomologyClass.toHom_mk,
    Cocycle.equivHomShift_symm_precomp, Functor.map_comp]
  rfl

/-- Under `CohomologyClass.toHom`, the map induced by postcomposition with `f : L ⟶ L'` is
postcomposition with the shifted map `f⟦n⟧'` in the homotopy category. -/
public lemma homClassesMap_postcomp_toHom {R : Type u} [CommRing R]
    {K L L' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : L ⟶ L') (n : ℤ) (z : CohomologyClass K L n) :
    CohomologyClass.toHom (homClassesMap (Stacks.HomComplex.TensorHomMap.postcomp R K L L' f) n z) =
      CohomologyClass.toHom z ≫ (HomotopyCategory.quotient _ _).map (f⟦n⟧') := by
  obtain ⟨z, rfl⟩ := z.mk_surjective
  rw [homClassesMap_postcomp, CohomologyClass.toHom_mk,
    Cocycle.equivHomShift_symm_postcomp, Functor.map_comp]
  rfl

/-- A morphism of Hom complexes is a quasi-isomorphism if and only if the induced map on
cohomology classes is bijective in every degree. -/
public lemma homComplex_quasiIso_iff {R : Type u} [CommRing R]
    {K L K' L' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : HomComplexR R K L ⟶ HomComplexR R K' L') :
    QuasiIso f ↔ ∀ n, Function.Bijective (homClassesMap f n) := by
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology f
    (forget₂ (ModuleCat R) AddCommGrpCat), quasiIso_iff]
  apply forall_congr'
  intro n
  rw [quasiIsoAt_iff, (homLeftHomologyMapData f n).quasiIso_iff,
    ConcreteCategory.isIso_iff_bijective]
  rfl

/-- Precomposition with an isomorphism is bijective on morphisms. -/
lemma precomp_bijective {D : Type*} [Category* D] {A B : D}
    (f : A ⟶ B) [IsIso f] (T : D) :
    Function.Bijective (fun g : B ⟶ T => f ≫ g) := by
  refine ⟨fun g h eq => (cancel_epi f).1 eq, fun g => ⟨inv f ≫ g, ?_⟩⟩
  simp

/-- Postcomposition with an isomorphism is bijective on morphisms. -/
lemma postcomp_bijective {D : Type*} [Category* D] {A B : D}
    (f : A ⟶ B) [IsIso f] (T : D) :
    Function.Bijective (fun g : T ⟶ A => g ≫ f) := by
  refine ⟨fun g h eq => (cancel_mono f).1 eq, fun g => ⟨g ≫ inv f, ?_⟩⟩
  simp

private lemma homClassesMap_precomp_bijective {R : Type u} [CommRing R] {K K' I : C R}
    (f : K' ⟶ K) (n : ℤ)
    (hf : Function.Bijective (fun g : (HomotopyCategory.quotient _ _).obj K ⟶
        (HomotopyCategory.quotient _ _).obj (I⟦n⟧) =>
      (HomotopyCategory.quotient _ _).map f ≫ g)) :
    Function.Bijective (homClassesMap (Stacks.HomComplex.TensorHomMap.precomp R K' K I f) n) := by
  apply (Function.Bijective.of_comp_iff' (CohomologyClass.toHom_bijective K' I n) _).1
  simpa only [Function.comp_def, homClassesMap_precomp_toHom] using
    hf.comp (CohomologyClass.toHom_bijective K I n)

/-- Precomposition with a quasi-isomorphism `f : K' ⟶ K` is a quasi-isomorphism of Hom complexes
`Hom^•(K, I) ⟶ Hom^•(K', I)` whenever the target complex `I` is K-injective. -/
lemma precomp_quasiIso_of_isKInjective {R : Type u} [CommRing R]
    {K K' I : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : K' ⟶ K) [QuasiIso f] [I.IsKInjective] :
    QuasiIso (Stacks.HomComplex.TensorHomMap.precomp R K' K I f) := by
  rw [homComplex_quasiIso_iff]
  intro n
  have hI := IsKInjective.rightOrthogonal (I⟦n⟧)
  rw [← ObjectProperty.isLocal_trW, ← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic] at hI
  exact homClassesMap_precomp_bijective f n
    (hI _ ((HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 ‹QuasiIso f›))

/-- Precomposition with a homotopy equivalence is a quasi-isomorphism of Hom complexes. -/
lemma precomp_quasiIso_of_homotopyEquivalence {R : Type u} [CommRing R]
    {K K' I : C R} (f : K' ⟶ K) (hf : homotopyEquivalences R f) :
    QuasiIso (Stacks.HomComplex.TensorHomMap.precomp R K' K I f) := by
  rw [homComplex_quasiIso_iff]
  intro n
  have : IsIso ((HomotopyCategory.quotient _ _).map f) :=
    Localization.inverts (HomotopyCategory.quotient _ _) (homotopyEquivalences R) f hf
  exact homClassesMap_precomp_bijective f n (precomp_bijective _ _)

/-- Postcomposition with a homotopy equivalence is a quasi-isomorphism of Hom complexes. -/
lemma postcomp_quasiIso_of_homotopyEquivalence {R : Type u} [CommRing R]
    {K I I' : C R} (f : I ⟶ I') (hf : homotopyEquivalences R f) :
    QuasiIso (Stacks.HomComplex.TensorHomMap.postcomp R K I I' f) := by
  rw [homComplex_quasiIso_iff]
  intro n
  have : IsIso ((HomotopyCategory.quotient _ _).map f) :=
    Localization.inverts (HomotopyCategory.quotient _ _) (homotopyEquivalences R) f hf
  have : IsIso ((HomotopyCategory.quotient _ _).map (f⟦n⟧')) := by
    rw [← Functor.comp_map]
    exact (NatIso.isIso_map_iff ((HomotopyCategory.quotient _ _).commShiftIso n) f).2
      (by change IsIso (((HomotopyCategory.quotient _ _).map f)⟦n⟧'); infer_instance)
  apply (Function.Bijective.of_comp_iff' (CohomologyClass.toHom_bijective K I' n) _).1
  simpa only [Function.comp_def, homClassesMap_postcomp_toHom] using
    (postcomp_bijective ((HomotopyCategory.quotient _ _).map (f⟦n⟧')) _).comp
      (CohomologyClass.toHom_bijective K I n)

private noncomputable abbrev complexHomToDerived (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    (C R)ᵒᵖ ⥤ C R ⥤ DerivedCategory (ModuleCat.{u} R) :=
  curry.obj (Model.homComplexFunctor R ⋙ (DerivedCategory.Q (C := ModuleCat.{u} R)))

private lemma complexHomToDerived_inverts (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    MorphismProperty.IsInvertedBy₂ (homotopyEquivalences R).op (homotopyEquivalences R)
      (complexHomToDerived R) := by
  rintro ⟨K, I⟩ ⟨K', I'⟩ ⟨f, g⟩ ⟨hf, hg⟩
  have := precomp_quasiIso_of_homotopyEquivalence (I := I) f.unop hf
  have := postcomp_quasiIso_of_homotopyEquivalence (K := K'.unop) g hg
  apply (NatIso.isIso_map_iff
    (currying.counitIso.app (Model.homComplexFunctor R ⋙ DerivedCategory.Q)) (f, g)).2
  change IsIso (DerivedCategory.Q.map
    (Stacks.HomComplex.TensorHomMap.precomp R K'.unop K.unop I f.unop ≫
      Stacks.HomComplex.TensorHomMap.postcomp R K'.unop I I' g))
  infer_instance

private noncomputable def homotopyHom (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    (KC R)ᵒᵖ ⥤ KC R ⥤ DerivedCategory (ModuleCat.{u} R) :=
  Localization.lift₂ (complexHomToDerived R) (complexHomToDerived_inverts R)
    (HomotopyCategory.quotient _ _).op (HomotopyCategory.quotient _ _)

@[instance_reducible]
private noncomputable def homotopyHomLifting (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    Localization.Lifting₂ (HomotopyCategory.quotient _ _).op (HomotopyCategory.quotient _ _)
      (homotopyEquivalences R).op (homotopyEquivalences R)
      (complexHomToDerived R) (homotopyHom R) := by
  unfold homotopyHom
  infer_instance

attribute [local instance] homotopyHomLifting

private noncomputable def homotopyHomComparison (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :=
  Localization.Lifting₂.iso (HomotopyCategory.quotient _ _).op (HomotopyCategory.quotient _ _)
    (homotopyEquivalences R).op (homotopyEquivalences R)
    (complexHomToDerived R) (homotopyHom R)

private lemma kInjectiveQ_isLocalization (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    (kInjectiveQ R).IsLocalization
      (MorphismProperty.isomorphisms (KInjectiveObjects R).FullSubcategory) := by
  have : (kInjectiveQ R).IsEquivalence := ⟨inferInstance, inferInstance, inferInstance⟩
  exact Functor.IsLocalization.of_isEquivalence _ _ le_rfl

attribute [local instance] kInjectiveQ_isLocalization

private theorem homComplexFunctor_map_left {R : Type u} [CommRing R]
    {K K' I : C R} (f : K' ⟶ K) :
    (Model.homComplexFunctor R).map
        (show (Opposite.op K, I) ⟶ (Opposite.op K', I) from (f.op, 𝟙 I)) =
      Stacks.HomComplex.TensorHomMap.precomp R K' K I f := by
  simp [Model.homComplexFunctor]

private lemma homotopyHom_precomp_inverts {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (I : C R) [I.IsKInjective] {X Y : KC R} (f : X ⟶ Y)
    (hf : HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ) f) :
    IsIso (((homotopyHom R).flip.obj ((HomotopyCategory.quotient _ _).obj I)).map f.op) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  obtain ⟨K', rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
  have : QuasiIso f := (HomotopyCategory.quotient_map_mem_quasiIso_iff f).1 hf
  have := precomp_quasiIso_of_isKInjective (I := I) f
  let e : (HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).op ⋙
      (homotopyHom R).flip.obj ((HomotopyCategory.quotient _ _).obj I) ≅
      (complexHomToDerived R).flip.obj I :=
    ((flipFunctor _ _ _).mapIso (homotopyHomComparison R)).app I
  have he := e.hom.naturality f.op
  change ((homotopyHom R).flip.obj ((HomotopyCategory.quotient _ _).obj I)).map
      ((HomotopyCategory.quotient _ _).map f).op ≫ (e.app (Opposite.op K)).hom =
    (e.app (Opposite.op K')).hom ≫ DerivedCategory.Q.map
      ((Model.homComplexFunctor R).map
        (show (Opposite.op K', I) ⟶ (Opposite.op K, I) from (f.op, 𝟙 I))) at he
  rw [homComplexFunctor_map_left] at he
  have : IsIso (((homotopyHom R).flip.obj
      ((HomotopyCategory.quotient _ _).obj I)).map
      ((HomotopyCategory.quotient _ _).map f).op ≫ (e.app (Opposite.op K)).hom) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (e.app (Opposite.op K)).hom

private noncomputable abbrev injectiveHomToDerived (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    (KC R)ᵒᵖ ⥤ (KInjectiveObjects R).FullSubcategory ⥤
      DerivedCategory (ModuleCat.{u} R) :=
  homotopyHom R ⋙ (whiskeringLeft _ _ _).obj (KInjectiveObjects R).ι

private lemma injectiveHomToDerived_inverts (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    MorphismProperty.IsInvertedBy₂
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)).op
      (MorphismProperty.isomorphisms (KInjectiveObjects R).FullSubcategory)
      (injectiveHomToDerived R) := by
  rintro ⟨K, I⟩ ⟨K', I'⟩ ⟨f, g⟩ ⟨hf, hg⟩
  have : CochainComplex.IsKInjective I.obj.as := I.property
  have h₁ := homotopyHom_precomp_inverts I.obj.as f.unop hf
  have : IsIso g := hg
  exact IsIso.comp_isIso' h₁ (by infer_instance)

private noncomputable def derivedHom (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    (DerivedCategory (ModuleCat.{u} R))ᵒᵖ ⥤
      DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R) :=
  Localization.lift₂ (injectiveHomToDerived R) (injectiveHomToDerived_inverts R)
    DerivedCategory.Qh.op (kInjectiveQ R)

@[instance_reducible]
private noncomputable def derivedHomLifting (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    Localization.Lifting₂ DerivedCategory.Qh.op (kInjectiveQ R)
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)).op
      (MorphismProperty.isomorphisms (KInjectiveObjects R).FullSubcategory)
      (injectiveHomToDerived R) (derivedHom R) := by
  unfold derivedHom
  infer_instance

attribute [local instance] derivedHomLifting

private noncomputable def derivedHomComparison (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :=
  Localization.Lifting₂.iso DerivedCategory.Qh.op (kInjectiveQ R)
    (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)).op
    (MorphismProperty.isomorphisms (KInjectiveObjects R).FullSubcategory)
    (injectiveHomToDerived R) (derivedHom R)

private noncomputable abbrev kInjectiveQuotient (R : Type u) [CommRing R] :
    (Model.KInjectiveComplexes R).FullSubcategory ⥤ (KInjectiveObjects R).FullSubcategory :=
  (KInjectiveObjects R).lift
    ((Model.KInjectiveComplexes R).ι ⋙ HomotopyCategory.quotient _ _)
    (fun I => I.property)

private noncomputable def homModelComparison (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    (((whiskeringLeft₂ (DerivedCategory (ModuleCat.{u} R))).obj DerivedCategory.Q.op).obj
      ((Model.KInjectiveComplexes R).ι ⋙ DerivedCategory.Q)).obj (derivedHom R) ≅
    (((whiskeringLeft₂ (DerivedCategory (ModuleCat.{u} R))).obj (𝟭 (C R)ᵒᵖ)).obj
      (Model.KInjectiveComplexes R).ι).obj (complexHomToDerived R) := by
  let q := DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)
  exact ((((whiskeringLeft₂ (DerivedCategory (ModuleCat.{u} R))).mapIso (NatIso.op q)).app
      ((Model.KInjectiveComplexes R).ι ⋙ DerivedCategory.Q)).app (derivedHom R)) ≪≫
    ((((whiskeringLeft₂ (DerivedCategory (ModuleCat.{u} R))).obj
      (HomotopyCategory.quotient _ _ ⋙ DerivedCategory.Qh).op).mapIso
        (isoWhiskerLeft (Model.KInjectiveComplexes R).ι q.symm)).app (derivedHom R)) ≪≫
    (((whiskeringLeft₂ (DerivedCategory (ModuleCat.{u} R))).obj
      (HomotopyCategory.quotient _ _).op).obj (kInjectiveQuotient R)).mapIso
        (derivedHomComparison R) ≪≫
    (((whiskeringLeft₂ (DerivedCategory (ModuleCat.{u} R))).obj (𝟭 (C R)ᵒᵖ)).obj
      (Model.KInjectiveComplexes R).ι).mapIso (homotopyHomComparison R)

private noncomputable def homComparison (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    Model.homSource R ⋙ uncurry.obj (derivedHom R) ≅ Model.homToDerived R := by
  let e := uncurry.mapIso (homModelComparison R)
  refine NatIso.ofComponents (fun X => e.app X) ?_
  intro X Y f
  have h := e.hom.naturality f
  change (((derivedHom R).map (DerivedCategory.Q.map f.1.unop).op).app
      (DerivedCategory.Q.obj X.2.obj) ≫
      ((derivedHom R).obj (Opposite.op (DerivedCategory.Q.obj Y.1.unop))).map
        (DerivedCategory.Q.map f.2.hom)) ≫ (e.app Y).hom =
    (e.app X).hom ≫
      (DerivedCategory.Q.map ((Model.homComplexFunctor R).map
        (show (X.1, X.2.obj) ⟶ (Y.1, X.2.obj) from (f.1, 𝟙 _))) ≫
      DerivedCategory.Q.map ((Model.homComplexFunctor R).map
        (show (Y.1, X.2.obj) ⟶ (Y.1, Y.2.obj) from (𝟙 _, f.2.hom)))) at h
  rw [← Functor.map_comp, ← Functor.map_comp] at h
  change (((derivedHom R).map (DerivedCategory.Q.map f.1.unop).op).app
      (DerivedCategory.Q.obj X.2.obj) ≫
      ((derivedHom R).obj (Opposite.op (DerivedCategory.Q.obj Y.1.unop))).map
        (DerivedCategory.Q.map f.2.hom)) ≫ (e.app Y).hom =
    (e.app X).hom ≫ DerivedCategory.Q.map
      ((Model.homComplexFunctor R).map
        (show (X.1, X.2.obj) ⟶ (Y.1, Y.2.obj) from (f.1, f.2.hom)))
  have hp : (show (X.1, X.2.obj) ⟶ (Y.1, Y.2.obj) from
      (show (X.1, X.2.obj) ⟶ (Y.1, X.2.obj) from (f.1, 𝟙 _)) ≫
      (show (Y.1, X.2.obj) ⟶ (Y.1, Y.2.obj) from (𝟙 _, f.2.hom))) =
      (f.1, f.2.hom) := by apply Prod.ext <;> simp
  exact h.trans (congrArg
    (fun m : (X.1, X.2.obj) ⟶ (Y.1, Y.2.obj) =>
      (e.app X).hom ≫ DerivedCategory.Q.map ((Model.homComplexFunctor R).map m)) hp)

private def addHomCongr {D : Type*} [Category* D] [Preadditive D]
    {A B A' B' : D} (e : A ≅ A') (f : B ≅ B') : (A ⟶ B) ≃+ (A' ⟶ B') where
  toEquiv := e.homCongr f
  map_add' x y := by simp [Iso.homCongr, Preadditive.comp_add, Preadditive.add_comp]

private noncomputable def zeroHomClassEquiv {R : Type u} [CommRing R] (K I : C R) :
    CohomologyClass K I 0 ≃+
      ((HomotopyCategory.quotient _ _).obj K ⟶ (HomotopyCategory.quotient _ _).obj I) :=
  CohomologyClass.homAddEquiv.trans
    (addHomCongr (Iso.refl _) ((HomotopyCategory.quotient _ _).mapIso
      ((shiftFunctorZero (C R) ℤ).app I)))

private noncomputable def derivedHomClassEquiv {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (K I : C R) [I.IsKInjective] :
    CohomologyClass K I 0 ≃+ (DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj I) :=
  (zeroHomClassEquiv K I).trans
    ((AddEquiv.ofBijective (DerivedCategory.Qh.mapAddHom)
      (IsKInjective.Qh_map_bijective ((HomotopyCategory.quotient _ _).obj K) I)).trans
      (addHomCongr ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).app K)
        ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).app I)))

private noncomputable def modelHomEquiv {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [SymmetricCategory (C R)]
    (K L I : C R) (hL : L.KFlat) [I.IsKInjective] :
    (DerivedCategory.Q.obj K ⟶
      ((derivedHom R).obj (Opposite.op (DerivedCategory.Q.obj L))).obj
        (DerivedCategory.Q.obj I)) ≃+
    (((derivedTensor R).obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L) ⟶
      DerivedCategory.Q.obj I) := by
  letI := homComplex_isKInjective_of_kFlat L I hL
  let e := Stacks.HomComplex.Currying.curryIso K L I
  let c := AddEquiv.ofBijective (homClassesMap e.hom 0)
    ((homComplex_quasiIso_iff e.hom).1 (by infer_instance) 0)
  exact (addHomCongr (Iso.refl _)
      ((homComparison R).app (Opposite.op L, ⟨I, inferInstance⟩))).trans
    ((derivedHomClassEquiv K (HomComplexR R L I)).symm.trans
      (c.trans ((derivedHomClassEquiv (K ⊗ L) I).trans
        (addHomCongr ((tensorComparison R).app (K, ⟨L, hL⟩)).symm (Iso.refl _)))))

private lemma zeroHomClassEquiv_mk {R : Type u} [CommRing R] {K I : C R} (f : K ⟶ I) :
    zeroHomClassEquiv K I (CohomologyClass.mk (Cocycle.ofHom f)) =
      (HomotopyCategory.quotient _ _).map f := by
  change (𝟙 _ ≫ (HomotopyCategory.quotient _ _).map
      (Cocycle.equivHomShift.symm (Cocycle.ofHom f))) ≫
      (HomotopyCategory.quotient _ _).map ((shiftFunctorZero (C R) ℤ).hom.app I) = _
  rw [Category.id_comp, ← Functor.map_comp]
  congr 1
  ext n
  simp [Cocycle.equivHomShift_symm_apply, Cocycle.homOf, Cochain.rightShift_v,
    CochainComplex.shiftFunctorZero_hom_app_f]

private lemma derivedHomClassEquiv_mk {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] {K I : C R} [I.IsKInjective] (f : K ⟶ I) :
    derivedHomClassEquiv K I (CohomologyClass.mk (Cocycle.ofHom f)) =
      DerivedCategory.Q.map f := by
  change ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).app K).inv ≫
      DerivedCategory.Qh.map (zeroHomClassEquiv K I (CohomologyClass.mk (Cocycle.ofHom f))) ≫
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).app I).hom = _
  rw [zeroHomClassEquiv_mk]
  simp only [Iso.app_inv, Iso.app_hom]
  rw [DerivedCategory.quotientCompQhIso_hom_naturality]
  simp

private abbrev chainTranspose {R : Type u} [CommRing R] {K L I : C R} (h : K ⊗ L ⟶ I) :=
  Stacks.HomComplex.TensorHomMap.Phi R K L ≫ Stacks.HomComplex.TensorHomMap.postcomp R L (K ⊗ L) I h

private lemma chainTranspose_apply {R : Type u} [CommRing R] {K L I : C R}
    (h : K ⊗ L ⟶ I) (r s t : ℤ) (hrs : s + r = t) (x : K.X r) (y : L.X s) :
    ((((chainTranspose h).f r).hom x).v s t hrs).hom y =
      (h.f t).hom ((HomologicalComplex.ιTensorObj K L r s t (by omega)).hom
        (x ⊗ₜ[R] y)) := by
  change (((Stacks.HomComplex.TensorHomMap.Phiv R K L r x).comp (Cochain.ofHom h) (add_zero r)).v s
    t hrs).hom y = _
  rw [Cochain.comp_v _ _ _ s t t hrs (add_zero t), Cochain.ofHom_v]
  exact congrArg (h.f t).hom (phiv_v_apply K L r x s t hrs y)

private lemma ofHom_homComplex_apply {R : Type u} [CommRing R]
    {K L I : C R} (f : K ⟶ HomComplexR R L I)
    (r q s t : ℤ) (hrq : r + 0 = q) (hqt : s + q = t) (x : K.X r) (y : L.X s) :
    ((((Cochain.ofHom f).v r q hrq).hom x).v s t hqt).hom y =
      (((f.f r).hom x).v s t (by omega)).hom y := by
  simp only [add_zero] at hrq
  cases hrq
  rw [Cochain.ofHom_v]

private lemma curry_chainTranspose {R : Type u} [CommRing R] {K L I : C R}
    (h : K ⊗ L ⟶ I) :
    ((Stacks.HomComplex.Currying.curryIso K L I).hom.f 0).hom
      (Cochain.ofHom (chainTranspose h)) = Cochain.ofHom h := by
  apply Cochain.ext₀
  intro t
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro r s hrs
  change r + s = t at hrs
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change ((((Stacks.HomComplex.Currying.curryIso K L I).hom.f 0).hom
    (Cochain.ofHom (chainTranspose h))).v t t (add_zero t)).hom
      ((HomologicalComplex.ιTensorObj K L r s t hrs).hom (x ⊗ₜ[R] y)) = _
  rw [Stacks.HomComplex.Currying.curryIso_hom_apply]
  rw [ofHom_homComplex_apply]
  exact chainTranspose_apply h r s t (by omega) x y

private lemma homClassesMap_curry_chainTranspose {R : Type u} [CommRing R] {K L I : C R}
    (h : K ⊗ L ⟶ I) :
    homClassesMap (Stacks.HomComplex.Currying.curryIso K L I).hom 0
      (CohomologyClass.mk (Cocycle.ofHom (chainTranspose h))) =
      CohomologyClass.mk (Cocycle.ofHom h) := by
  change CohomologyClass.mk (homCocyclesMap _ _ (Cocycle.ofHom (chainTranspose h))) = _
  congr 1
  exact Subtype.ext (curry_chainTranspose h)

private lemma modelHomEquiv_transpose {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [SymmetricCategory (C R)]
    (K L I : C R) (hL : L.KFlat) [I.IsKInjective] (h : K ⊗ L ⟶ I) :
    modelHomEquiv K L I hL
      (DerivedCategory.Q.map (chainTranspose h) ≫
        ((homComparison R).app (Opposite.op L, ⟨I, inferInstance⟩)).inv) =
      ((tensorComparison R).app (K, ⟨L, hL⟩)).hom ≫ DerivedCategory.Q.map h := by
  let := homComplex_isKInjective_of_kFlat L I hL
  dsimp [modelHomEquiv, addHomCongr, Iso.homCongr]
  simp only [Category.id_comp, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  erw [Category.comp_id]
  change (tensorComparison R).hom.app (K, ⟨L, hL⟩) ≫
    derivedHomClassEquiv (K ⊗ L) I
      (homClassesMap (Stacks.HomComplex.Currying.curryIso K L I).hom 0
        ((derivedHomClassEquiv K (HomComplexR R L I)).symm
          (DerivedCategory.Q.map (chainTranspose h)))) = _
  rw [← derivedHomClassEquiv_mk (chainTranspose h), AddEquiv.symm_apply_apply,
    homClassesMap_curry_chainTranspose, derivedHomClassEquiv_mk]

private lemma modelHomEquiv_symm_map_eq {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [SymmetricCategory (C R)]
    (K L I : C R) (hL : L.KFlat) [I.IsKInjective] (h : K ⊗ L ⟶ I) :
    (modelHomEquiv K L I hL).symm
      (((tensorComparison R).app (K, ⟨L, hL⟩)).hom ≫ DerivedCategory.Q.map h) =
    DerivedCategory.Q.map (chainTranspose h) ≫
      ((homComparison R).app (Opposite.op L, ⟨I, inferInstance⟩)).inv :=
  (modelHomEquiv K L I hL).symm_apply_eq.mpr (modelHomEquiv_transpose K L I hL h).symm

private lemma homComplexFunctor_map_apply {R : Type u} [CommRing R]
    {K K' I I' : C R} (f : K' ⟶ K) (g : I ⟶ I') (n : ℤ)
    (z : Cochain K I n) (p q : ℤ) (hpq : p + n = q) (x : K'.X p) :
    (((((Model.homComplexFunctor R).map
      (show (Opposite.op K, I) ⟶ (Opposite.op K', I') from (f.op, g))).f n).hom z).v
        p q hpq).hom x =
      (g.f q).hom ((z.v p q hpq).hom ((f.f p).hom x)) := by
  change ((((Cochain.ofHom f).comp z (zero_add n)).comp
    (Cochain.ofHom g) (add_zero n)).v p q hpq).hom x = _
  simp only [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  rfl

private lemma chainTranspose_naturality {R : Type u} [CommRing R]
    {K K' L L' I I' : C R} (f : K' ⟶ K) (g : L' ⟶ L) (h : I ⟶ I')
    (a : K ⊗ L ⟶ I) :
    chainTranspose ((f ⊗ₘ g) ≫ a ≫ h) =
      f ≫ chainTranspose a ≫ (Model.homComplexFunctor R).map
        (show (Opposite.op L, I) ⟶ (Opposite.op L', I') from (g.op, h)) := by
  ext n : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Cochain.ext
  intro p q hpq
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  change ((((chainTranspose ((f ⊗ₘ g) ≫ a ≫ h)).f n).hom x).v p q hpq).hom y =
    (((((Model.homComplexFunctor R).map
        (show (Opposite.op L, I) ⟶ (Opposite.op L', I') from (g.op, h))).f n).hom
      (((chainTranspose a).f n).hom ((f.f n).hom x))).v p q hpq).hom y
  rw [chainTranspose_apply, homComplexFunctor_map_apply, chainTranspose_apply]
  change (h.f q).hom ((a.f q).hom (((f ⊗ₘ g).f q).hom
      ((HomologicalComplex.ιTensorObj K' L' n p q (by omega)).hom (x ⊗ₜ[R] y)))) = _
  congr 2
  change ((HomologicalComplex.ιTensorObj K' L' n p q (by omega) ≫
    (f ⊗ₘ g).f q).hom (x ⊗ₜ[R] y)) = _
  rw [CochainComplex.ιTensorObj_tensorHom]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rfl

/-- Every morphism `Q(K) ⟶ Q(I)` in the derived category between the images of cochain complexes
with `I` K-injective comes from an honest morphism of complexes `K ⟶ I`. -/
lemma Q_map_surjective_of_isKInjective
    {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]
    (K I : CochainComplex D ℤ) [I.IsKInjective] :
    Function.Surjective (DerivedCategory.Q.map : (K ⟶ I) → _) := by
  intro f
  obtain ⟨g, hg⟩ := (IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient D (.up ℤ)).obj K) I).surjective
    ((DerivedCategory.quotientCompQhIso D).hom.app K ≫ f ≫
      (DerivedCategory.quotientCompQhIso D).inv.app I)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient D (.up ℤ)).map_surjective g
  refine ⟨g, ?_⟩
  apply (cancel_epi ((DerivedCategory.quotientCompQhIso D).hom.app K)).1
  rw [← DerivedCategory.quotientCompQhIso_hom_naturality, hg]
  simp

private lemma tensorComparison_naturality {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [SymmetricCategory (C R)]
    {K K' L L' : C R} (f : K ⟶ K') (g : L ⟶ L') (hL : L.KFlat) (hL' : L'.KFlat) :
    (uncurry.obj (derivedTensor R)).map (DerivedCategory.Q.map f, DerivedCategory.Q.map g) ≫
      ((tensorComparison R).app (K', ⟨L', hL'⟩)).hom =
    ((tensorComparison R).app (K, ⟨L, hL⟩)).hom ≫ DerivedCategory.Q.map (f ⊗ₘ g) :=
  (tensorComparison R).hom.naturality
    (show (K, ⟨L, hL⟩) ⟶ (K', ⟨L', hL'⟩) from (f, ⟨g⟩))

private lemma homComparison_inv_naturality {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    {L L' I I' : C R} [I.IsKInjective] [I'.IsKInjective] (g : L' ⟶ L) (h : I ⟶ I') :
    DerivedCategory.Q.map ((Model.homComplexFunctor R).map
        (show (Opposite.op L, I) ⟶ (Opposite.op L', I') from (g.op, h))) ≫
      ((homComparison R).app (Opposite.op L', ⟨I', inferInstance⟩)).inv =
    ((homComparison R).app (Opposite.op L, ⟨I, inferInstance⟩)).inv ≫
      (uncurry.obj (derivedHom R)).map
        (show (Opposite.op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I) ⟶
          (Opposite.op (DerivedCategory.Q.obj L'), DerivedCategory.Q.obj I') from
            ((DerivedCategory.Q.map g).op, DerivedCategory.Q.map h)) :=
  (homComparison R).inv.naturality
    (show (Opposite.op L, ⟨I, inferInstance⟩) ⟶
      (Opposite.op L', ⟨I', inferInstance⟩) from (g.op, ⟨h⟩))

private lemma modelHomEquiv_symm_naturality {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [SymmetricCategory (C R)]
    {K K' L L' I I' : C R} (hL : L.KFlat) (hL' : L'.KFlat)
    [I.IsKInjective] [I'.IsKInjective]
    (f : K' ⟶ K) (g : L' ⟶ L) (h : I ⟶ I')
    (a : ((derivedTensor R).obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L) ⟶
      DerivedCategory.Q.obj I) :
    (modelHomEquiv K' L' I' hL').symm
      ((uncurry.obj (derivedTensor R)).map
        (show (DerivedCategory.Q.obj K', DerivedCategory.Q.obj L') ⟶
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) from
            (DerivedCategory.Q.map f, DerivedCategory.Q.map g)) ≫
        a ≫ DerivedCategory.Q.map h) =
      DerivedCategory.Q.map f ≫ (modelHomEquiv K L I hL).symm a ≫
        (uncurry.obj (derivedHom R)).map
        (show (Opposite.op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I) ⟶
          (Opposite.op (DerivedCategory.Q.obj L'), DerivedCategory.Q.obj I') from
            ((DerivedCategory.Q.map g).op, DerivedCategory.Q.map h)) := by
  obtain ⟨b, hb⟩ := Q_map_surjective_of_isKInjective (K ⊗ L) I
    (((tensorComparison R).app (K, ⟨L, hL⟩)).inv ≫ a)
  have ha : a = ((tensorComparison R).app (K, ⟨L, hL⟩)).hom ≫ DerivedCategory.Q.map b := by
    rw [hb]
    simp
  rw [ha, modelHomEquiv_symm_map_eq]
  have ht := tensorComparison_naturality f g hL' hL
  simp only [← Category.assoc] at ht ⊢
  rw [ht]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [modelHomEquiv_symm_map_eq, chainTranspose_naturality]
  simp only [Functor.map_comp, Category.assoc]
  rw [homComparison_inv_naturality]

private abbrev HomTriple (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :=
  (DerivedCategory (ModuleCat.{u} R))ᵒᵖ ×
    (DerivedCategory (ModuleCat.{u} R))ᵒᵖ × DerivedCategory (ModuleCat.{u} R)

private def additiveHomFunctor (D : Type*) [Category.{t} D] [Preadditive D] :
    Dᵒᵖ × D ⥤ AddCommGrpCat.{t} where
  obj X := AddCommGrpCat.of (X.1.unop ⟶ X.2)
  map f := AddCommGrpCat.ofHom
    { toFun := fun a => f.1.unop ≫ a ≫ f.2
      map_zero' := by simp
      map_add' := by intros; simp [Preadditive.comp_add, Preadditive.add_comp] }
  map_id X := by ext a; simp
  map_comp f g := by ext a; simp [Category.assoc]

private noncomputable abbrev adjunctionHomSource (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] : HomTriple R ⥤ AddCommGrpCat.{w} :=
  (𝟭 _).prod (uncurry.obj (derivedHom R)) ⋙ additiveHomFunctor (DerivedCategory (ModuleCat.{u} R))

private noncomputable def tensorHomSource (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [SymmetricCategory (C R)] :
    HomTriple R ⥤ (DerivedCategory (ModuleCat.{u} R))ᵒᵖ × DerivedCategory (ModuleCat.{u} R) where
  obj X := (Opposite.op ((uncurry.obj (derivedTensor R)).obj (X.1.unop, X.2.1.unop)), X.2.2)
  map f := (((uncurry.obj (derivedTensor R)).map (f.1.unop, f.2.1.unop)).op, f.2.2)
  map_id X := by
    apply Prod.ext
    · change ((uncurry.obj (derivedTensor R)).map (𝟙 _)).op = _
      rw [CategoryTheory.Functor.map_id, op_id]
      rfl
    · rfl
  map_comp {X Y Z} f g := by
    apply Prod.ext
    · change ((uncurry.obj (derivedTensor R)).map
        ((show (Z.1.unop, Z.2.1.unop) ⟶ (Y.1.unop, Y.2.1.unop) from
          (g.1.unop, g.2.1.unop)) ≫
          (show (Y.1.unop, Y.2.1.unop) ⟶ (X.1.unop, X.2.1.unop) from
            (f.1.unop, f.2.1.unop)))).op = _
      rw [CategoryTheory.Functor.map_comp, op_comp]
      rfl
    · rfl

private noncomputable abbrev adjunctionHomTarget (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [SymmetricCategory (C R)] :
    HomTriple R ⥤ AddCommGrpCat.{w} :=
  tensorHomSource R ⋙ additiveHomFunctor (DerivedCategory (ModuleCat.{u} R))

private abbrev HomModels (R : Type u) [CommRing R] :=
  (C R)ᵒᵖ × (Model.KFlatComplexes R).FullSubcategoryᵒᵖ ×
    (Model.KInjectiveComplexes R).FullSubcategory

private noncomputable abbrev homModelsQ (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] : HomModels R ⥤ HomTriple R :=
  DerivedCategory.Q.op.prod
    (((Model.KFlatComplexes R).ι ⋙ DerivedCategory.Q).op.prod
      ((Model.KInjectiveComplexes R).ι ⋙ DerivedCategory.Q))

private noncomputable def modelAdjunctionIso (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [SymmetricCategory (C R)] :
    homModelsQ R ⋙ adjunctionHomTarget R ≅ homModelsQ R ⋙ adjunctionHomSource R := by
  refine NatIso.ofComponents (fun X => ?_) ?_
  · letI : X.2.2.obj.IsKInjective := X.2.2.property
    exact (modelHomEquiv X.1.unop X.2.1.unop.obj X.2.2.obj X.2.1.unop.property).symm.toAddCommGrpIso
  · intro X Y f
    let : X.2.2.obj.IsKInjective := X.2.2.property
    let : Y.2.2.obj.IsKInjective := Y.2.2.property
    ext a
    change (modelHomEquiv Y.1.unop Y.2.1.unop.obj Y.2.2.obj Y.2.1.unop.property).symm
      ((uncurry.obj (derivedTensor R)).map
        (show (DerivedCategory.Q.obj Y.1.unop, DerivedCategory.Q.obj Y.2.1.unop.obj) ⟶
          (DerivedCategory.Q.obj X.1.unop, DerivedCategory.Q.obj X.2.1.unop.obj) from
          (DerivedCategory.Q.map f.1.unop, DerivedCategory.Q.map f.2.1.unop.hom)) ≫
            a ≫ DerivedCategory.Q.map f.2.2.hom) =
      DerivedCategory.Q.map f.1.unop ≫
        (modelHomEquiv X.1.unop X.2.1.unop.obj X.2.2.obj X.2.1.unop.property).symm a ≫
        (uncurry.obj (derivedHom R)).map
          (show (Opposite.op (DerivedCategory.Q.obj X.2.1.unop.obj), DerivedCategory.Q.obj
            X.2.2.obj) ⟶
            (Opposite.op (DerivedCategory.Q.obj Y.2.1.unop.obj), DerivedCategory.Q.obj Y.2.2.obj)
              from
            ((DerivedCategory.Q.map f.2.1.unop.hom).op, DerivedCategory.Q.map f.2.2.hom))
    exact modelHomEquiv_symm_naturality
      X.2.1.unop.property Y.2.1.unop.property f.1.unop f.2.1.unop.hom f.2.2.hom a

/-- Naturality of a family of isomorphisms `F.obj X' ≅ G.obj X'` transported along
isomorphisms `X ≅ X'`: if `f` and `g` correspond under the isomorphisms and `g` is natural, then
so is `f` for the transported isomorphisms. -/
public lemma naturality_transport {D E : Type*} [Category* D] [Category* E]
    (F G : D ⥤ E) {X Y X' Y' : D} (eX : X ≅ X') (eY : Y ≅ Y')
    (a : F.obj X' ≅ G.obj X') (b : F.obj Y' ≅ G.obj Y')
    (f : X ⟶ Y) (g : X' ⟶ Y') (hf : f ≫ eY.hom = eX.hom ≫ g)
    (hg : F.map g ≫ b.hom = a.hom ≫ G.map g) :
    F.map f ≫ (F.mapIso eY ≪≫ b ≪≫ (G.mapIso eY).symm).hom =
      (F.mapIso eX ≪≫ a ≪≫ (G.mapIso eX).symm).hom ≫ G.map f := by
  have hgi : eX.inv ≫ f = g ≫ eY.inv := by
    apply (cancel_mono eY.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hf, Iso.inv_hom_id_assoc]
  dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Functor.mapIso_inv]
  simp only [Category.assoc]
  rw [← F.map_comp_assoc, hf, F.map_comp_assoc, reassoc_of% hg]
  rw [← G.map_comp, ← G.map_comp, hgi]

private abbrev HomotopyModels (R : Type u) [CommRing R] :=
  (KC R)ᵒᵖ × (KFlatObjects R).FullSubcategoryᵒᵖ ×
    (KInjectiveObjects R).FullSubcategory

private noncomputable abbrev homotopyModelsQ (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] : HomotopyModels R ⥤ HomTriple R :=
  DerivedCategory.Qh.op.prod ((kFlatQ R).op.prod (kInjectiveQ R))

private abbrev homotopyModelsW (R : Type u) [CommRing R] : MorphismProperty (HomotopyModels R) :=
  (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)).op.prod
    ((KFlatQuasiIso R).op.prod (MorphismProperty.isomorphisms (KInjectiveObjects
      R).FullSubcategory))

private lemma homotopyModelsQ_isLocalization (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    (homotopyModelsQ R).IsLocalization (homotopyModelsW R) := by
  change (DerivedCategory.Qh.op.prod ((kFlatQ R).op.prod (kInjectiveQ R))).IsLocalization
    ((HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)).op.prod
      ((KFlatQuasiIso R).op.prod (MorphismProperty.isomorphisms (KInjectiveObjects
        R).FullSubcategory)))
  have := kFlatQ_isLocalization R
  have := kInjectiveQ_isLocalization R
  infer_instance

attribute [local instance] homotopyModelsQ_isLocalization

private def homotopyModelsRep {R : Type u} [CommRing R] (X : HomotopyModels R) : HomModels R :=
  (Opposite.op X.1.unop.as,
    Opposite.op ⟨X.2.1.unop.obj.as, X.2.1.unop.property⟩,
    ⟨X.2.2.obj.as, X.2.2.property⟩)

private noncomputable def homotopyModelsIso {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (X : HomotopyModels R) :
    (homotopyModelsQ R).obj X ≅ (homModelsQ R).obj (homotopyModelsRep X) :=
  Iso.prod ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).app X.1.unop.as).symm.op
    (Iso.prod ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).app X.2.1.unop.obj.as).symm.op
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).app X.2.2.obj.as))

private noncomputable def homotopyModelsRepMap {R : Type u} [CommRing R]
    {X Y : HomotopyModels R} (f : X ⟶ Y) : homotopyModelsRep X ⟶ homotopyModelsRep Y :=
  (f.1.unop.out.op, (ObjectProperty.homMk f.2.1.unop.hom.out).op,
    ObjectProperty.homMk f.2.2.hom.out)

private lemma homotopyModelsIso_naturality {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] {X Y : HomotopyModels R} (f : X ⟶ Y) :
    (homotopyModelsQ R).map f ≫ (homotopyModelsIso Y).hom =
      (homotopyModelsIso X).hom ≫ (homModelsQ R).map (homotopyModelsRepMap f) := by
  apply Prod.ext
  · apply Quiver.Hom.unop_inj
    change (DerivedCategory.quotientCompQhIso _).inv.app Y.1.unop.as ≫
        DerivedCategory.Qh.map f.1.unop =
      DerivedCategory.Q.map f.1.unop.out ≫
        (DerivedCategory.quotientCompQhIso _).inv.app X.1.unop.as
    simpa only [Functor.comp_map, HomotopyCategory.quotient_map_out] using
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).inv.naturality f.1.unop.out).symm
  · apply Prod.ext
    · apply Quiver.Hom.unop_inj
      change (DerivedCategory.quotientCompQhIso _).inv.app Y.2.1.unop.obj.as ≫
          DerivedCategory.Qh.map f.2.1.unop.hom =
        DerivedCategory.Q.map f.2.1.unop.hom.out ≫
          (DerivedCategory.quotientCompQhIso _).inv.app X.2.1.unop.obj.as
      simpa only [Functor.comp_map, HomotopyCategory.quotient_map_out] using
        ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).inv.naturality
          f.2.1.unop.hom.out).symm
    · change DerivedCategory.Qh.map f.2.2.hom ≫
          (DerivedCategory.quotientCompQhIso _).hom.app Y.2.2.obj.as =
        (DerivedCategory.quotientCompQhIso _).hom.app X.2.2.obj.as ≫
          DerivedCategory.Q.map f.2.2.hom.out
      simpa only [Functor.comp_map, HomotopyCategory.quotient_map_out] using
        (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.naturality f.2.2.hom.out

private noncomputable def homotopyAdjunctionIso (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [SymmetricCategory (C R)] :
    homotopyModelsQ R ⋙ adjunctionHomTarget R ≅ homotopyModelsQ R ⋙ adjunctionHomSource R := by
  refine NatIso.ofComponents (fun X =>
    (adjunctionHomTarget R).mapIso (homotopyModelsIso X) ≪≫
      (modelAdjunctionIso R).app (homotopyModelsRep X) ≪≫
      ((adjunctionHomSource R).mapIso (homotopyModelsIso X)).symm) ?_
  intro X Y f
  exact naturality_transport (adjunctionHomTarget R) (adjunctionHomSource R)
    (homotopyModelsIso X) (homotopyModelsIso Y)
    ((modelAdjunctionIso R).app (homotopyModelsRep X))
    ((modelAdjunctionIso R).app (homotopyModelsRep Y))
    ((homotopyModelsQ R).map f) ((homModelsQ R).map (homotopyModelsRepMap f))
    (homotopyModelsIso_naturality f)
    ((modelAdjunctionIso R).hom.naturality (homotopyModelsRepMap f))

private noncomputable def adjunctionIso (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [SymmetricCategory (C R)] :
    adjunctionHomTarget R ≅ adjunctionHomSource R :=
  Localization.liftNatIso (homotopyModelsQ R) (homotopyModelsW R)
    (homotopyModelsQ R ⋙ adjunctionHomTarget R) (homotopyModelsQ R ⋙ adjunctionHomSource R)
    (adjunctionHomTarget R) (adjunctionHomSource R) (homotopyAdjunctionIso R)

private lemma adjunctionIso_model (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [SymmetricCategory (C R)] (X : HomModels R) :
    (adjunctionIso R).app ((homModelsQ R).obj X) = (modelAdjunctionIso R).app X := by
  let Xh : HomotopyModels R :=
    (Opposite.op ((HomotopyCategory.quotient _ _).obj X.1.unop),
      Opposite.op ⟨(HomotopyCategory.quotient _ _).obj X.2.1.unop.obj, X.2.1.unop.property⟩,
      ⟨(HomotopyCategory.quotient _ _).obj X.2.2.obj, X.2.2.property⟩)
  let e : (homotopyModelsQ R).obj Xh ≅ (homModelsQ R).obj X := homotopyModelsIso Xh
  have hc : (adjunctionIso R).hom.app ((homotopyModelsQ R).obj Xh) =
      (adjunctionHomTarget R).map e.hom ≫ (modelAdjunctionIso R).hom.app X ≫
        (adjunctionHomSource R).map e.inv := by
    dsimp only [adjunctionIso, Localization.liftNatIso]
    rw [Localization.liftNatTrans_app]
    simp only [Localization.Lifting.iso,
      Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Category.id_comp, Category.comp_id]
    rfl
  apply Iso.ext
  apply (cancel_epi ((adjunctionHomTarget R).map e.hom)).1
  change (adjunctionHomTarget R).map e.hom ≫ (adjunctionIso R).hom.app ((homModelsQ R).obj X) = _
  rw [(adjunctionIso R).hom.naturality e.hom, hc]
  simp only [Category.assoc, ← Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id,
    ]
  erw [Category.comp_id]
  rfl

private noncomputable def homEquiv (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [SymmetricCategory (C R)]
    (K L M : DerivedCategory (ModuleCat.{u} R)) :
    (K ⟶ (uncurry.obj (derivedHom R)).obj (Opposite.op L, M)) ≃+
      ((uncurry.obj (derivedTensor R)).obj (K, L) ⟶ M) :=
  ((adjunctionIso R).app (Opposite.op K, Opposite.op L, M)).symm.addCommGroupIsoToAddEquiv

private lemma homEquiv_model (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [SymmetricCategory (C R)]
    (K L I : C R) (hL : L.KFlat) [I.IsKInjective] :
    homEquiv R (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj I) =
      modelHomEquiv K L I hL := by
  have h := adjunctionIso_model R
    (Opposite.op K, Opposite.op ⟨L, hL⟩, ⟨I, inferInstance⟩)
  dsimp only [homEquiv]
  rw [show (adjunctionIso R).app (Opposite.op (DerivedCategory.Q.obj K),
      Opposite.op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I) =
      (modelAdjunctionIso R).app (Opposite.op K, Opposite.op ⟨L, hL⟩, ⟨I, inferInstance⟩) from h]
  rfl

private lemma homEquiv_naturality {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [SymmetricCategory (C R)]
    {K K' L L' M M' : DerivedCategory (ModuleCat.{u} R)}
    (f : K' ⟶ K) (g : L' ⟶ L) (h : M ⟶ M')
    (a : K ⟶ (uncurry.obj (derivedHom R)).obj (Opposite.op L, M)) :
    homEquiv R K' L' M' (f ≫ a ≫ (uncurry.obj (derivedHom R)).map
      (show (Opposite.op L, M) ⟶ (Opposite.op L', M') from (g.op, h))) =
    (uncurry.obj (derivedTensor R)).map (show (K', L') ⟶ (K, L) from (f, g)) ≫
      homEquiv R K L M a ≫ h := by
  have hn := (adjunctionIso R).inv.naturality
    (show (Opposite.op K, Opposite.op L, M) ⟶ (Opposite.op K', Opposite.op L', M') from
      (f.op, g.op, h))
  exact ConcreteCategory.congr_hom hn a

private lemma derivedTensorMixedComparison_app (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [SymmetricCategory (C R)]
    (K L : (KFlatObjects R).FullSubcategory) :
    ((derivedTensorMixedComparison R).hom.app ((kFlatQ R).obj K)).app L ≫
        ((mixedTensorComparison R).hom.app K.obj).app L =
      ((derivedTensorComparisonIso R).hom.app K).app L := by
  dsimp only [derivedTensorMixedComparison, Localization.liftNatIso]
  rw [Localization.liftNatTrans_app]
  dsimp only [Localization.Lifting.iso, NatTrans.comp_app, Iso.refl_hom,
    NatTrans.id_app, isoWhiskerLeft_inv, whiskerLeft_app]
  simp only [Category.id_comp, Category.assoc]
  erw [Iso.inv_hom_id_app_app, Category.comp_id]

private lemma tensorComparison_eq (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [SymmetricCategory (C R)]
    (K L : C R) (hK : K.KFlat) (hL : L.KFlat) :
    (tensorComparison R).app (K, ⟨L, hL⟩) = derivedTensorComparison K L hK hL := by
  apply Iso.ext
  let q := DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)
  let Kh : (KFlatObjects R).FullSubcategory := ⟨(HomotopyCategory.quotient _ _).obj K, hK⟩
  let Lh : (KFlatObjects R).FullSubcategory := ⟨(HomotopyCategory.quotient _ _).obj L, hL⟩
  change (((derivedTensor R).map (q.inv.app K)).app (DerivedCategory.Q.obj L) ≫
      ((derivedTensor R).obj ((kFlatQ R).obj Kh)).map (q.inv.app L) ≫
      ((derivedTensorMixedComparison R).hom.app ((kFlatQ R).obj Kh)).app Lh ≫
      ((mixedTensorComparison R).hom.app Kh.obj).app Lh ≫
      DerivedCategory.Qh.map (homotopyTensorComparison K L).hom ≫ q.hom.app (K ⊗ L)) =
    (((derivedTensor R).map (q.inv.app K)).app (DerivedCategory.Q.obj L) ≫
      ((derivedTensor R).obj ((kFlatQ R).obj Kh)).map (q.inv.app L) ≫
      ((derivedTensorComparisonIso R).hom.app Kh).app Lh ≫
      DerivedCategory.Qh.map (homotopyTensorComparison K L).hom ≫ q.hom.app (K ⊗ L))
  erw [reassoc_of% (derivedTensorMixedComparison_app R Kh Lh)]

private lemma kFlat_tensor {R : Type u} [CommRing R] (K L : C R)
    (hK : K.KFlat) (hL : L.KFlat) : (K ⊗ L).KFlat := by
  intro N hN
  exact HomologicalComplex.Acyclic.of_iso (α_ N K L) (hL (N ⊗ K) (hK N hN))

private abbrev Flat (R : Type u) [CommRing R] := (Model.KFlatComplexes R).FullSubcategory

private noncomputable abbrev flatQ (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    Flat R ⥤ DerivedCategory (ModuleCat.{u} R) :=
  (Model.KFlatComplexes R).ι ⋙ DerivedCategory.Q

private noncomputable def flatTensor (R : Type u) [CommRing R] : Flat R × Flat R ⥤ Flat R :=
  (Model.KFlatComplexes R).lift
    (((Model.KFlatComplexes R).ι.prod (Model.KFlatComplexes R).ι) ⋙ tensor (C R))
    (fun X => kFlat_tensor X.1.obj X.2.obj X.1.property X.2.property)

private noncomputable def flatTensorComparison (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [SymmetricCategory (C R)] :
    ((flatQ R).prod (flatQ R)) ⋙ uncurry.obj (derivedTensor R) ≅ flatTensor R ⋙ flatQ R :=
  isoWhiskerLeft ((Model.KFlatComplexes R).ι.prod (𝟭 (Flat R))) (tensorComparison R)

private abbrev tensorAssocSource {D : Type*} [Category* D] (T : D × D ⥤ D) :=
  prod.inverseAssociator D D D ⋙ T.prod (𝟭 D) ⋙ T

private abbrev tensorAssocTarget {D : Type*} [Category* D] (T : D × D ⥤ D) :=
  (𝟭 D).prod T ⋙ T

private noncomputable def flatAssociator (R : Type u) [CommRing R] :
    tensorAssocSource (flatTensor R) ≅ tensorAssocTarget (flatTensor R) := by
  refine NatIso.ofComponents (fun X => (Model.KFlatComplexes R).isoMk
    (α_ X.1.obj X.2.1.obj X.2.2.obj)) ?_
  intro X Y f
  exact (Model.KFlatComplexes R).ι.map_injective
    (associator_naturality f.1.hom f.2.1.hom f.2.2.hom)

private noncomputable def modelTensorAssociator (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [SymmetricCategory (C R)] :
    (flatQ R).prod ((flatQ R).prod (flatQ R)) ⋙ tensorAssocSource (uncurry.obj (derivedTensor R)) ≅
      (flatQ R).prod ((flatQ R).prod (flatQ R)) ⋙ tensorAssocTarget (uncurry.obj (derivedTensor R))
        := by
  let T := uncurry.obj (derivedTensor R)
  let e := flatTensorComparison R
  let eL := isoWhiskerLeft (prod.inverseAssociator (Flat R) (Flat R) (Flat R))
    (isoWhiskerRight (NatIso.prod e (Iso.refl (flatQ R))) T ≪≫
      isoWhiskerLeft ((flatTensor R).prod (𝟭 (Flat R))) e)
  let eR := isoWhiskerRight (NatIso.prod (Iso.refl (flatQ R)) e) T ≪≫
    isoWhiskerLeft ((𝟭 (Flat R)).prod (flatTensor R)) e
  exact eL ≪≫ isoWhiskerRight (flatAssociator R) (flatQ R) ≪≫ eR.symm

private noncomputable def descendIsoOfFullEssSurj
    {D E A : Type*} [Category* D] [Category* E] [Category* A]
    (L : D ⥤ E) [L.Full] [L.EssSurj] (F G : E ⥤ A) (e : L ⋙ F ≅ L ⋙ G) : F ≅ G := by
  refine NatIso.ofComponents (fun X =>
    F.mapIso (L.objObjPreimageIso X).symm ≪≫ e.app (L.objPreimage X) ≪≫
      G.mapIso (L.objObjPreimageIso X)) ?_
  intro X Y f
  let g := L.preimage ((L.objObjPreimageIso X).hom ≫ f ≫ (L.objObjPreimageIso Y).inv)
  apply naturality_transport F G (L.objObjPreimageIso X).symm
    (L.objObjPreimageIso Y).symm (e.app _) (e.app _) f (L.map g)
  · dsimp [g]
    rw [L.map_preimage]
    simp
  · exact e.hom.naturality g

private lemma kFlatQuotient_full (R : Type u) [CommRing R] : (kFlatQuotient R).Full where
  map_surjective f := ⟨ObjectProperty.homMk f.hom.out,
    (KFlatObjects R).ι.map_injective (HomotopyCategory.quotient_map_out f.hom)⟩

private lemma kFlatQuotient_essSurj (R : Type u) [CommRing R] : (kFlatQuotient R).EssSurj where
  mem_essImage X := ⟨⟨X.obj.as, X.property⟩, ⟨Iso.refl _⟩⟩

attribute [local instance] kFlatQuotient_full kFlatQuotient_essSurj

private noncomputable abbrev flatTripleQ (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :=
  (kFlatQ R).prod ((kFlatQ R).prod (kFlatQ R))

private abbrev flatTripleW (R : Type u) [CommRing R] :=
  (KFlatQuasiIso R).prod ((KFlatQuasiIso R).prod (KFlatQuasiIso R))

private lemma prod_full {A B D E : Type*} [Category* A] [Category* B]
    [Category* D] [Category* E] (F : A ⥤ B) (G : D ⥤ E) [F.Full] [G.Full] :
    (F.prod G).Full where
  map_surjective f := by
    obtain ⟨f₁, h₁⟩ := F.map_surjective f.1
    obtain ⟨f₂, h₂⟩ := G.map_surjective f.2
    exact ⟨(f₁, f₂), Prod.ext h₁ h₂⟩

private lemma prod_essSurj {A B D E : Type*} [Category* A] [Category* B]
    [Category* D] [Category* E] (F : A ⥤ B) (G : D ⥤ E) [F.EssSurj] [G.EssSurj] :
    (F.prod G).EssSurj where
  mem_essImage X := ⟨(F.objPreimage X.1, G.objPreimage X.2),
    ⟨Iso.prod (F.objObjPreimageIso X.1) (G.objObjPreimageIso X.2)⟩⟩

attribute [local instance] prod_full prod_essSurj

private noncomputable def homotopyTensorAssociator (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [SymmetricCategory (C R)] :
    flatTripleQ R ⋙ tensorAssocSource (uncurry.obj (derivedTensor R)) ≅
      flatTripleQ R ⋙ tensorAssocTarget (uncurry.obj (derivedTensor R)) := by
  let L := (kFlatQuotient R).prod ((kFlatQuotient R).prod (kFlatQuotient R))
  let q : kFlatQuotient R ⋙ kFlatQ R ≅ flatQ R :=
    isoWhiskerLeft (Model.KFlatComplexes R).ι (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R))
  let q₃ : L ⋙ flatTripleQ R ≅ (flatQ R).prod ((flatQ R).prod (flatQ R)) :=
    NatIso.prod q (NatIso.prod q q)
  let F := tensorAssocSource (uncurry.obj (derivedTensor R))
  let G := tensorAssocTarget (uncurry.obj (derivedTensor R))
  exact descendIsoOfFullEssSurj L (flatTripleQ R ⋙ F) (flatTripleQ R ⋙ G)
    (isoWhiskerRight q₃ F ≪≫ modelTensorAssociator R ≪≫ (isoWhiskerRight q₃ G).symm)

private noncomputable def tensorAssociator (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [SymmetricCategory (C R)] :
    tensorAssocSource (uncurry.obj (derivedTensor R)) ≅
      tensorAssocTarget (uncurry.obj (derivedTensor R)) := by
  let F := tensorAssocSource (uncurry.obj (derivedTensor R))
  let G := tensorAssocTarget (uncurry.obj (derivedTensor R))
  haveI : (flatTripleQ R).IsLocalization (flatTripleW R) := inferInstanceAs
    (((kFlatQ R).prod ((kFlatQ R).prod (kFlatQ R))).IsLocalization
      ((KFlatQuasiIso R).prod ((KFlatQuasiIso R).prod (KFlatQuasiIso R))))
  exact Localization.liftNatIso (flatTripleQ R) (flatTripleW R)
    (flatTripleQ R ⋙ F) (flatTripleQ R ⋙ G) F G (homotopyTensorAssociator R)

private noncomputable def adjunctionCore (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [SymmetricCategory (C R)] :
    DerivedHomAdjunction R where
  tensor := uncurry.obj (derivedTensor R)
  tensorAssoc K L M := (tensorAssociator R).app (K, L, M)
  tensorSwap K L := ((derivedTensorBraiding R).app K).app L
  tensorAssoc_naturality {K K' L L' M M'} f g h :=
    (tensorAssociator R).hom.naturality
      (show (K, L, M) ⟶ (K', L', M') from (f, g, h))
  tensorSwap_naturality f g := by
    simpa only [uncurry_obj_map, Category.assoc, Iso.app_hom] using
      derivedTensorBraiding_naturality f g
  hom := uncurry.obj (derivedHom R)
  homEquiv := homEquiv R
  homEquiv_naturality_left {K K' L M} f a := by
    have hn := homEquiv_naturality f (𝟙 L) (𝟙 M) a
    have hm : (uncurry.obj (derivedHom R)).map
        (show (Opposite.op L, M) ⟶ (Opposite.op L, M) from ((𝟙 L).op, 𝟙 M)) = 𝟙 _ :=
      (uncurry.obj (derivedHom R)).map_id (Opposite.op L, M)
    rw [hm, Category.comp_id, Category.comp_id] at hn
    exact hn
  homEquiv_dinaturality g a := by
    simpa only [Category.id_comp, Category.comp_id] using homEquiv_naturality (𝟙 _) g (𝟙 _) a
  homEquiv_naturality_right {K L M M'} h a := by
    have hn := homEquiv_naturality (𝟙 K) (𝟙 L) h a
    have hm : (uncurry.obj (derivedTensor R)).map
        (show (K, L) ⟶ (K, L) from (𝟙 K, 𝟙 L)) = 𝟙 _ :=
      (uncurry.obj (derivedTensor R)).map_id (K, L)
    rw [hm] at hn
    simpa only [Category.id_comp, op_id] using hn

private lemma adjunctionCore_symm_map_eq (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [SymmetricCategory (C R)]
    (K L I : C R) (hL : L.KFlat) [I.IsKInjective] (h : K ⊗ L ⟶ I) :
    ((adjunctionCore R).homEquiv (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
        (DerivedCategory.Q.obj I)).symm
      (((tensorComparison R).app (K, ⟨L, hL⟩)).hom ≫ DerivedCategory.Q.map h) =
    DerivedCategory.Q.map (chainTranspose h) ≫
      ((homComparison R).app (Opposite.op L, ⟨I, inferInstance⟩)).inv := by
  dsimp only [adjunctionCore]
  rw [homEquiv_model R K L I hL]
  exact modelHomEquiv_symm_map_eq K L I hL h

private lemma descendIsoOfFullEssSurj_app
    {D E A : Type*} [Category* D] [Category* E] [Category* A]
    (L : D ⥤ E) [L.Full] [L.EssSurj] (F G : E ⥤ A) (e : L ⋙ F ≅ L ⋙ G) (X : D) :
    (descendIsoOfFullEssSurj L F G e).app (L.obj X) = e.app X := by
  let i := L.objObjPreimageIso (L.obj X)
  let f := L.preimage i.hom
  have hn : F.map i.hom ≫ e.hom.app X =
      e.hom.app (L.objPreimage (L.obj X)) ≫ G.map i.hom := by
    have hn := e.hom.naturality f
    change F.map (L.map f) ≫ e.hom.app X =
      e.hom.app (L.objPreimage (L.obj X)) ≫ G.map (L.map f) at hn
    simpa only [f, L.map_preimage] using hn
  apply Iso.ext
  change F.map i.inv ≫ e.hom.app (L.objPreimage (L.obj X)) ≫ G.map i.hom = e.hom.app X
  rw [← hn]
  simp only [← F.map_comp_assoc, i.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

private lemma tensorAssociator_model (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [SymmetricCategory (C R)]
    (X : Flat R × Flat R × Flat R) :
    (tensorAssociator R).app (((flatQ R).prod ((flatQ R).prod (flatQ R))).obj X) =
      (modelTensorAssociator R).app X := by
  let L := (kFlatQuotient R).prod ((kFlatQuotient R).prod (kFlatQuotient R))
  let q : kFlatQuotient R ⋙ kFlatQ R ≅ flatQ R :=
    isoWhiskerLeft (Model.KFlatComplexes R).ι (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R))
  let q₃ : L ⋙ flatTripleQ R ≅ (flatQ R).prod ((flatQ R).prod (flatQ R)) :=
    NatIso.prod q (NatIso.prod q q)
  let F := tensorAssocSource (uncurry.obj (derivedTensor R))
  let G := tensorAssocTarget (uncurry.obj (derivedTensor R))
  have hc : (tensorAssociator R).hom.app ((flatTripleQ R).obj (L.obj X)) =
      F.map (q₃.hom.app X) ≫ (modelTensorAssociator R).hom.app X ≫ G.map (q₃.inv.app X) := by
    dsimp only [tensorAssociator, Localization.liftNatIso]
    rw [Localization.liftNatTrans_app]
    simp only [Localization.Lifting.iso, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
      Category.id_comp, Category.comp_id]
    change ((descendIsoOfFullEssSurj L (flatTripleQ R ⋙ F) (flatTripleQ R ⋙ G)
      (isoWhiskerRight q₃ F ≪≫ modelTensorAssociator R ≪≫
        (isoWhiskerRight q₃ G).symm)).app (L.obj X)).hom = _
    rw [descendIsoOfFullEssSurj_app]
    rfl
  apply Iso.ext
  apply (cancel_epi (F.map (q₃.hom.app X))).1
  change F.map (q₃.hom.app X) ≫ (tensorAssociator R).hom.app _ = _
  rw [(tensorAssociator R).hom.naturality (q₃.hom.app X)]
  dsimp only [Functor.comp_obj]
  rw [hc]
  simp only [Category.assoc, Iso.app_hom]
  change F.map (q₃.hom.app X) ≫ (modelTensorAssociator R).hom.app X ≫
      G.map (q₃.inv.app X) ≫ G.map (q₃.hom.app X) =
    F.map (q₃.hom.app X) ≫ (modelTensorAssociator R).hom.app X
  simp only [← G.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id  ]
  erw [Category.comp_id]

private lemma adjunctionCore_braiding_comparison (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [SymmetricCategory (C R)]
    (K L : C R) (hK : K.KFlat) (hL : L.KFlat) :
    ((adjunctionCore R).tensorSwap (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)).hom ≫
        ((tensorComparison R).app (L, ⟨K, hK⟩)).hom =
      ((tensorComparison R).app (K, ⟨L, hL⟩)).hom ≫ DerivedCategory.Q.map (β_ K L).hom := by
  rw [tensorComparison_eq R L K hL hK, tensorComparison_eq R K L hK hL]
  exact derivedTensorComparison_braiding K L hK hL


private def chainUntranspose {R : Type u} [CommRing R] {K L I : C R}
    (f : K ⟶ HomComplexR R L I) : K ⊗ L ⟶ I :=
  Cocycle.homOf (homCocyclesMap (Stacks.HomComplex.Currying.curryIso K L I).hom 0
    (Cocycle.ofHom f))

private lemma chainTranspose_untranspose {R : Type u} [CommRing R] {K L I : C R}
    (f : K ⟶ HomComplexR R L I) : chainTranspose (chainUntranspose f) = f := by
  apply Cochain.ofHom_injective
  apply (ConcreteCategory.bijective_of_isIso
    ((HomologicalComplex.eval _ _ 0).map (Stacks.HomComplex.Currying.curryIso K L I).hom)).injective
  change ((Stacks.HomComplex.Currying.curryIso K L I).hom.f 0).hom
    (Cochain.ofHom (chainTranspose (chainUntranspose f))) = _
  exact (curry_chainTranspose _).trans (Cocycle.cochain_ofHom_homOf_eq_coe _)

private lemma chainUntranspose_apply {R : Type u} [CommRing R] {K L I : C R}
    (f : K ⟶ HomComplexR R L I) (r s t : ℤ) (hrs : r + s = t)
    (x : K.X r) (y : L.X s) :
    ((chainUntranspose f).f t).hom
      ((HomologicalComplex.ιTensorObj K L r s t hrs).hom (x ⊗ₜ[R] y)) =
      (((f.f r).hom x).v s t (by omega)).hom y := by
  rw [← chainTranspose_apply (chainUntranspose f) r s t (by omega) x y,
    chainTranspose_untranspose]

private lemma adjunctionCore_map_eq {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [SymmetricCategory (C R)]
    {P L I : C R} (hL : L.KFlat) [I.IsKInjective] (f : P ⟶ HomComplexR R L I) :
    (adjunctionCore R).homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L)
      (DerivedCategory.Q.obj I)
      (DerivedCategory.Q.map f ≫ ((homComparison R).app (Opposite.op L, ⟨I, inferInstance⟩)).inv) =
      ((tensorComparison R).app (P, ⟨L, hL⟩)).hom ≫
        DerivedCategory.Q.map (chainUntranspose f) := by
  apply (adjunctionCore R).homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L)
    (DerivedCategory.Q.obj I) |>.symm.injective
  rw [AddEquiv.symm_apply_apply]
  simpa only [chainTranspose_untranspose] using
    (adjunctionCore_symm_map_eq R P L I hL (chainUntranspose f)).symm

private lemma evaluation_model {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [SymmetricCategory (C R)]
    {P L I : C R} (hL : L.KFlat) [I.IsKInjective] (f : P ⟶ HomComplexR R L I) :
    (adjunctionCore R).tensor.map
      (DerivedCategory.Q.map f ≫ ((homComparison R).app (Opposite.op L, ⟨I, inferInstance⟩)).inv,
        𝟙 (DerivedCategory.Q.obj L)) ≫ (adjunctionCore R).evaluation _ _ =
      ((tensorComparison R).app (P, ⟨L, hL⟩)).hom ≫
        DerivedCategory.Q.map (chainUntranspose f) := by
  rw [DerivedHomAdjunction.evaluation, ← DerivedHomAdjunction.homEquiv_naturality_left,
    Category.comp_id]
  exact adjunctionCore_map_eq hL f

private lemma associator_comparison {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [SymmetricCategory (C R)]
    (P K T : C R) (hP : P.KFlat) (hK : K.KFlat) (hT : T.KFlat) :
    ((adjunctionCore R).tensorAssoc (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K)
      (DerivedCategory.Q.obj T)).hom ≫
      (adjunctionCore R).tensor.map (show
        (DerivedCategory.Q.obj P, (adjunctionCore R).tensor.obj (DerivedCategory.Q.obj K,
          DerivedCategory.Q.obj T)) ⟶
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj (K ⊗ T)) from
        (𝟙 (DerivedCategory.Q.obj P), ((tensorComparison R).app (K, ⟨T, hT⟩)).hom)) ≫
      ((tensorComparison R).app (P, ⟨K ⊗ T, kFlat_tensor K T hK hT⟩)).hom =
    (adjunctionCore R).tensor.map (((tensorComparison R).app (P, ⟨K, hK⟩)).hom,
        𝟙 (DerivedCategory.Q.obj T)) ≫
      ((tensorComparison R).app (P ⊗ K, ⟨T, hT⟩)).hom ≫
      DerivedCategory.Q.map (α_ P K T).hom := by
  change ((tensorAssociator R).app (((flatQ R).prod ((flatQ R).prod (flatQ R))).obj
    (⟨P, hP⟩, ⟨K, hK⟩, ⟨T, hT⟩))).hom ≫ _ = _
  rw [tensorAssociator_model]
  dsimp [modelTensorAssociator, flatTensorComparison, flatAssociator, flatTensor, adjunctionCore]
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
    Category.comp_id, Category.assoc, ← CategoryTheory.Functor.map_comp_assoc,
    Iso.inv_hom_id_app ]
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp]
  erw [Iso.inv_hom_id_app]
  erw [Category.comp_id]
  rfl

private lemma tensorHom_apply {R : Type u} [CommRing R] {A A' B B' : C R}
    (f : A ⟶ A') (g : B ⟶ B') (r s n : ℤ) (hrs : r + s = n)
    (x : A.X r) (y : B.X s) :
    ((f ⊗ₘ g).f n).hom ((HomologicalComplex.ιTensorObj A B r s n hrs).hom (x ⊗ₜ[R] y)) =
      (HomologicalComplex.ιTensorObj A' B' r s n hrs).hom
        ((f.f r).hom x ⊗ₜ[R] (g.f s).hom y) :=
  ConcreteCategory.congr_hom (CochainComplex.ιTensorObj_tensorHom R f g r s n hrs)
    (x ⊗ₜ[R] y)

private lemma associator_apply {R : Type u} [CommRing R] (A B C : C R)
    (r s t n : ℤ) (h : r + s + t = n) (x : A.X r) (y : B.X s) (z : C.X t) :
    ((α_ A B C).hom.f n).hom
      ((HomologicalComplex.ιTensorObj (A ⊗ B) C (r + s) t n h).hom
        ((HomologicalComplex.ιTensorObj A B r s (r + s) rfl).hom (x ⊗ₜ[R] y) ⊗ₜ[R] z)) =
      (HomologicalComplex.ιTensorObj A (B ⊗ C) r (s + t) n (by omega)).hom
        (x ⊗ₜ[R] (HomologicalComplex.ιTensorObj B C s t (s + t) rfl).hom (y ⊗ₜ[R] z)) := by
  have hh := GradedObject.Monoidal.ιTensorObj₃'_associator_hom A.X B.X C.X r s t n h
  exact ConcreteCategory.congr_hom hh ((x ⊗ₜ[R] y) ⊗ₜ[R] z)

/-- The symmetry isomorphism of the tensor product of complexes on a pure tensor of homogeneous
elements: `k ⊗ t ↦ (-1)^{rs} t ⊗ k`. -/
public lemma complexSwap_apply {R : Type u} [CommRing R] (K T : C R)
    (r s n : ℤ) (h : r + s = n) (k : K.X r) (t : T.X s) :
    ((Model.complexSwap R K T).hom.f n).hom
        ((HomologicalComplex.ιTensorObj K T r s n h).hom (k ⊗ₜ[R] t)) =
      (r * s).negOnePow •
        (HomologicalComplex.ιTensorObj T K s r n (by omega)).hom (t ⊗ₜ[R] k) :=
  ConcreteCategory.congr_hom
    (CochainComplex.Koszul.koszulSymmetric_braiding_ιTensorObj R K T r s n h) (k ⊗ₜ[R] t)

private lemma chainTranspose_injective {R : Type u} [CommRing R] {P L I : C R} :
    Function.Injective (chainTranspose : (P ⊗ L ⟶ I) → _) := by
  intro a b h
  apply Cochain.ofHom_injective
  rw [← curry_chainTranspose a, ← curry_chainTranspose b, h]

private lemma chainUntranspose_precomp {R : Type u} [CommRing R] {P F L I : C R}
    (f : P ⟶ HomComplexR R L I) (g : F ⟶ L) :
    chainUntranspose (f ≫ Stacks.HomComplex.TensorHomMap.precomp R F L I g) =
      (P ◁ g) ≫ chainUntranspose f := by
  apply chainTranspose_injective
  rw [chainTranspose_untranspose]
  have h := chainTranspose_naturality (𝟙 P) g (𝟙 I) (chainUntranspose f)
  rw [homComplexFunctor_map_left] at h
  simpa only [Category.comp_id, Category.id_comp, chainTranspose_untranspose,
    id_tensorHom] using h.symm

private lemma chain_internalCurry {R : Type u} [CommRing R] (P K T L M : C R)
    (f : P ⟶ HomComplexR R L M) (g : T ⟶ HomComplexR R K L) :
    chainUntranspose ((f ▷ K) ≫
      (ChainEvaluation.chainEvaluation K L M) ≫
      Stacks.HomComplex.TensorHomMap.precomp R T (HomComplexR R K L) M g) =
      (α_ P K T).hom ≫ (P ◁ (Model.complexSwap R K T).hom) ≫
        (P ◁ chainUntranspose g) ≫ chainUntranspose f := by
  apply HomologicalComplex.hom_ext
  intro n
  apply GradedObject.Monoidal.tensorObj₃'_ext
  intro t r s h
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro pk z
  induction pk using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    simpa only [TensorProduct.add_tmul, _root_.map_add] using congrArg₂ (· + ·) ha hb
  | tmul p k =>
    change ((chainUntranspose _).f n).hom
      ((HomologicalComplex.ιTensorObj (P ⊗ K) T (t + r) s n h).hom
        ((HomologicalComplex.ιTensorObj P K t r (t + r) rfl).hom (p ⊗ₜ[R] k) ⊗ₜ[R] z)) = _
    rw [chainUntranspose_apply]
    have hf := tensorHom_apply f (𝟙 K) t r (t + r) rfl p k
    change ((f ▷ K).f (t + r)).hom _ = _ at hf
    simp only [HomologicalComplex.id_f, ModuleCat.id_apply] at hf
    simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply]
    change (((Cochain.ofHom g).comp
      (((ChainEvaluation.chainEvaluation K L M).f
        (t + r)).hom (((f ▷ K).f (t + r)).hom
          ((HomologicalComplex.ιTensorObj P K t r (t + r) rfl).hom (p ⊗ₜ[R] k))))
        (zero_add (t + r))).v s n (by omega)).hom z = _
    rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
    rw [hf]
    obtain ⟨a, ha⟩ : ∃ a : ℤ, s = a - r := ⟨s + r, by omega⟩
    rcases ha with rfl
    obtain rfl : n = a + t := by omega
    have he := ChainEvaluation.chainEvaluation_tmul K L M t r (t + r)
      (a - r) (a + t) a rfl (by omega) (by omega) (by omega)
      ((f.f t).hom p) k ((g.f (a - r)).hom z)
    simp only [ModuleCat.comp_apply]
    change ((((ChainEvaluation.chainEvaluation K L M).f
      (t + r)).hom ((HomologicalComplex.ιTensorObj (HomComplexR R L M) K t r
        (t + r) rfl).hom ((f.f t).hom p ⊗ₜ[R] k))).v (a - r) (a + t) (by omega)).hom
        ((g.f (a - r)).hom z) = _
    rw [show ((((ChainEvaluation.chainEvaluation K L M).f
      (t + r)).hom ((HomologicalComplex.ιTensorObj (HomComplexR R L M) K t r
        (t + r) rfl).hom ((f.f t).hom p ⊗ₜ[R] k))).v (a - r) (a + t) (by omega)).hom
        ((g.f (a - r)).hom z) = _ from he]
    change _ = ((chainUntranspose f).f (a + t)).hom
      (((P ◁ chainUntranspose g).f (a + t)).hom
        (((P ◁ (Model.complexSwap R K T).hom).f (a + t)).hom
          (((α_ P K T).hom.f (a + t)).hom
            ((HomologicalComplex.ιTensorObj (P ⊗ K) T (t + r) (a - r) (a + t) (by omega)).hom
              ((HomologicalComplex.ιTensorObj P K t r (t + r) rfl).hom (p ⊗ₜ[R] k) ⊗ₜ[R] z)))))
    rw [associator_apply]
    rw [show P ◁ (Model.complexSwap R K T).hom = 𝟙 P ⊗ₘ (Model.complexSwap R K T).hom from rfl,
      tensorHom_apply, complexSwap_apply]
    simp only [HomologicalComplex.id_f, ModuleCat.id_apply, TensorProduct.tmul_smul,
      map_zsmul_unit]
    rw [show P ◁ chainUntranspose g = 𝟙 P ⊗ₘ chainUntranspose g from rfl,
      tensorHom_apply, chainUntranspose_apply, chainUntranspose_apply]
    simp only [HomologicalComplex.id_f, ModuleCat.id_apply]
    let φ : Cochain L M t := (f.f t).hom p
    let ψ : Cochain K L (a - r) := (g.f (a - r)).hom z
    change (r + -a * r).negOnePow •
      (φ.v a (a + t) rfl).hom ((ψ.v r a (by omega)).hom k) =
      (r * (a - r)).negOnePow •
        (φ.v (r + (a - r)) (a + t) (by omega)).hom ((ψ.v r (r + (a - r)) (by omega)).hom k)
    have aux (b : ℤ) (hb : b = a) (h₁ : b + t = a + t) (h₂ : r + (a - r) = b) :
        (φ.v b (a + t) h₁).hom ((ψ.v r b h₂).hom k) =
          (φ.v a (a + t) rfl).hom ((ψ.v r a (by omega)).hom k) := by
      subst b
      rfl
    rw [aux (r + (a - r)) (by omega)]
    congr 1
    rw [show r + -a * r = -(r * a) + r by ring,
      show r * (a - r) = r * a - r * r by ring]
    simp only [sub_eq_add_neg, Int.negOnePow_add, Int.negOnePow_neg,
      Int.negOnePow_mul_self]


private lemma internalCurry_test {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (d : DerivedHomAdjunction R)
    (P K T L M : DerivedCategory (ModuleCat.{u} R))
    (p : P ⟶ d.hom.obj (Opposite.op L, M))
    (b : T ⟶ d.hom.obj (Opposite.op K, L)) :
    d.homEquiv (d.tensor.obj (P, K)) T M
      (d.tensor.map (p, 𝟙 K) ≫ d.internalCurryMor K L M ≫ d.hom.map (b.op, 𝟙 M)) =
    (d.tensorAssoc P K T).hom ≫ d.tensor.map (𝟙 P, (d.tensorSwap K T).hom) ≫
      d.tensor.map (show (P, d.tensor.obj (T, K)) ⟶
        (d.hom.obj (Opposite.op L, M), L) from
        (p, d.tensor.map (show (T, K) ⟶ (d.hom.obj (Opposite.op K, L), K) from
          (b, 𝟙 K)) ≫ d.evaluation K L)) ≫ d.evaluation L M := by
  rw [d.homEquiv_naturality_left, d.homEquiv_dinaturality]
  simp only [DerivedHomAdjunction.internalCurryMor, AddEquiv.apply_symm_apply]
  rw [d.tensor_map_comp_assoc]
  simp only [Category.id_comp, Category.comp_id]
  rw [d.tensorAssoc_naturality_assoc]
  simp only [← Category.assoc, d.tensor_map_comp, Category.id_comp, Category.comp_id]
  congr 2
  rw [d.tensorSwap_naturality]

private lemma evaluation_model_comp {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [SymmetricCategory (C R)]
    {P F L I : C R} (hF : F.KFlat) [I.IsKInjective]
    (f : P ⟶ HomComplexR R L I) (g : F ⟶ L) :
    (adjunctionCore R).tensor.map (show
      (DerivedCategory.Q.obj P, DerivedCategory.Q.obj F) ⟶
      ((adjunctionCore R).hom.obj (Opposite.op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I),
        DerivedCategory.Q.obj L) from
      (DerivedCategory.Q.map f ≫ ((homComparison R).app (Opposite.op L, ⟨I, inferInstance⟩)).inv,
        DerivedCategory.Q.map g)) ≫ (adjunctionCore R).evaluation _ _ =
      ((tensorComparison R).app (P, ⟨F, hF⟩)).hom ≫
        DerivedCategory.Q.map (chainUntranspose
          (f ≫ Stacks.HomComplex.TensorHomMap.precomp R F L I g)) := by
  let d := adjunctionCore R
  have hn := homComparison_inv_naturality (R := R) g (𝟙 I)
  rw [homComplexFunctor_map_left, CategoryTheory.Functor.map_id] at hn
  have he := evaluation_model (R := R) hF (f ≫ Stacks.HomComplex.TensorHomMap.precomp R F L I g)
  rw [Functor.map_comp, Category.assoc, hn] at he
  let p := DerivedCategory.Q.map f ≫
    ((homComparison R).app (Opposite.op L, ⟨I, inferInstance⟩)).inv
  let H := d.hom.map (show
    (Opposite.op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I) ⟶
    (Opposite.op (DerivedCategory.Q.obj F), DerivedCategory.Q.obj I) from
    ((DerivedCategory.Q.map g).op, 𝟙 _))
  simp only [← Category.assoc] at he
  change d.tensor.map (show
    (DerivedCategory.Q.obj P, DerivedCategory.Q.obj F) ⟶
    (d.hom.obj (Opposite.op (DerivedCategory.Q.obj F), DerivedCategory.Q.obj I),
      DerivedCategory.Q.obj F) from
    (p ≫ H, 𝟙 (DerivedCategory.Q.obj F))) ≫
    d.evaluation (DerivedCategory.Q.obj F) (DerivedCategory.Q.obj I) = _ at he
  have hp := d.tensor_map_comp p (𝟙 (DerivedCategory.Q.obj F)) H (𝟙 (DerivedCategory.Q.obj F))
  simp only [Category.id_comp] at hp
  rw [← hp, Category.assoc, d.evaluation_naturality_left, d.tensor_map_comp_assoc] at he
  erw [Category.comp_id, Category.id_comp] at he
  exact he


private abbrev tensorModelIso {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [SymmetricCategory (C R)]
    (K L : C R) (hL : L.KFlat) :
    (adjunctionCore R).tensor.obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj (K ⊗ L) := (tensorComparison R).app (K, ⟨L, hL⟩)

private abbrev homModelIso {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [SymmetricCategory (C R)]
    (L I : C R) [I.IsKInjective] :
    (adjunctionCore R).hom.obj (Opposite.op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj (HomComplexR R L I) :=
  (homComparison R).app (Opposite.op L, ⟨I, inferInstance⟩)

private lemma internalCurry_model_test {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (P K T L M : C R) (hP : P.KFlat) (hK : K.KFlat) (hT : T.KFlat)
    [L.IsKInjective] [M.IsKInjective]
    (f : P ⟶ HomComplexR R L M) (g : T ⟶ HomComplexR R K L) :
    letI := CochainComplex.Koszul.koszulSymmetric R
    let d := adjunctionCore R
    d.homEquiv (d.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj K))
      (DerivedCategory.Q.obj T) (DerivedCategory.Q.obj M)
      (d.tensor.map (DerivedCategory.Q.map f ≫ (homModelIso L M).inv, 𝟙 (DerivedCategory.Q.obj K)) ≫
        d.internalCurryMor (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
          (DerivedCategory.Q.obj M) ≫
        d.hom.map ((DerivedCategory.Q.map g ≫ (homModelIso K L).inv).op, 𝟙 (DerivedCategory.Q.obj
          M))) =
      d.tensor.map ((tensorModelIso P K hK).hom, 𝟙 (DerivedCategory.Q.obj T)) ≫
        (tensorModelIso (P ⊗ K) T hT).hom ≫
        DerivedCategory.Q.map (chainUntranspose ((f ▷ K) ≫
          ChainEvaluation.chainEvaluation K L M ≫
          Stacks.HomComplex.TensorHomMap.precomp R T (HomComplexR R K L) M g)) := by
  let := CochainComplex.Koszul.koszulSymmetric R
  let d := adjunctionCore R
  let p := DerivedCategory.Q.map f ≫ (homModelIso L M).inv
  let b := DerivedCategory.Q.map g ≫ (homModelIso K L).inv
  change d.homEquiv (d.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj K))
    (DerivedCategory.Q.obj T) (DerivedCategory.Q.obj M)
    (d.tensor.map (p, 𝟙 (DerivedCategory.Q.obj K)) ≫
      d.internalCurryMor (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj
        M) ≫
      d.hom.map (b.op, 𝟙 (DerivedCategory.Q.obj M))) = _
  rw [internalCurry_test]
  have hg := evaluation_model (R := R) hK g
  change d.tensor.map (show
    (DerivedCategory.Q.obj T, DerivedCategory.Q.obj K) ⟶
    (d.hom.obj (Opposite.op (DerivedCategory.Q.obj K), DerivedCategory.Q.obj L),
      DerivedCategory.Q.obj K) from
    (b, 𝟙 _)) ≫ d.evaluation (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) =
    (tensorModelIso T K hK).hom ≫ DerivedCategory.Q.map (chainUntranspose g) at hg
  rw [hg]
  have hb := adjunctionCore_braiding_comparison R K T hK hT
  change (d.tensorSwap _ _).hom ≫ (tensorModelIso T K hK).hom =
    (tensorModelIso K T hT).hom ≫ DerivedCategory.Q.map (Model.complexSwap R K T).hom at hb
  rw [d.tensor_map_comp_assoc]
  simp only [Category.id_comp]
  rw [← Category.assoc (d.tensorSwap _ _).hom, hb, Category.assoc]
  have hsplit := d.tensor_map_comp (𝟙 (DerivedCategory.Q.obj P))
    (tensorModelIso K T hT).hom p
    (DerivedCategory.Q.map (Model.complexSwap R K T).hom ≫
      DerivedCategory.Q.map (chainUntranspose g))
  simp only [Category.id_comp] at hsplit
  rw [← reassoc_of% hsplit]
  rw [← CategoryTheory.Functor.map_comp]
  have he := evaluation_model_comp (R := R) (kFlat_tensor K T hK hT) f
    ((Model.complexSwap R K T).hom ≫ chainUntranspose g)
  change d.tensor.map (p, DerivedCategory.Q.map _) ≫ d.evaluation _ _ =
    (tensorModelIso P (K ⊗ T) (kFlat_tensor K T hK hT)).hom ≫
      DerivedCategory.Q.map _ at he
  rw [he, reassoc_of% (associator_comparison P K T hP hK hT)]
  simp only [← CategoryTheory.Functor.map_comp]
  congr 2
  rw [chainUntranspose_precomp f ((Model.complexSwap R K T).hom ≫ chainUntranspose g),
    MonoidalCategory.whiskerLeft_comp, Category.assoc]
  exact congrArg DerivedCategory.Q.map (chain_internalCurry P K T L M f g).symm

private lemma internalCurry_comparison {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K L M : C R) (hK : K.KFlat) [L.IsKInjective] [M.IsKInjective] :
    letI := CochainComplex.Koszul.koszulSymmetric R
    let d := adjunctionCore R
    d.internalCurryMor (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj
      M) =
      d.tensor.map ((homModelIso L M).hom, 𝟙 (DerivedCategory.Q.obj K)) ≫
        (tensorModelIso (HomComplexR R L M) K hK).hom ≫
        DerivedCategory.Q.map (ChainEvaluation.chainEvaluation K L M) ≫
        (homModelIso (HomComplexR R K L) M).inv ≫
        d.hom.map ((homModelIso K L).hom.op, 𝟙 (DerivedCategory.Q.obj M)) := by
  let := CochainComplex.Koszul.koszulSymmetric R
  let d := adjunctionCore R
  obtain ⟨P, f, hP, _, hf, _⟩ := exists_kFlat_resolution (HomComplexR R L M)
  obtain ⟨T, g, hT, _, hg, _⟩ := exists_kFlat_resolution (HomComplexR R K L)
  let := hf
  let := hg
  let p : DerivedCategory.Q.obj P ≅ d.hom.obj (Opposite.op (DerivedCategory.Q.obj L),
    DerivedCategory.Q.obj M) :=
    asIso (DerivedCategory.Q.map f) ≪≫ (homModelIso L M).symm
  let b : DerivedCategory.Q.obj T ≅ d.hom.obj (Opposite.op (DerivedCategory.Q.obj K),
    DerivedCategory.Q.obj L) :=
    asIso (DerivedCategory.Q.map g) ≪≫ (homModelIso K L).symm
  let tp := d.tensor.mapIso (p.prod (Iso.refl (DerivedCategory.Q.obj K)))
  let hb := d.hom.mapIso (b.op.prod (Iso.refl (DerivedCategory.Q.obj M)))
  apply (cancel_epi tp.hom).1
  apply (cancel_mono hb.hom).1
  apply (d.homEquiv (d.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj K))
    (DerivedCategory.Q.obj T) (DerivedCategory.Q.obj M)).injective
  change d.homEquiv (d.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj K))
    (DerivedCategory.Q.obj T) (DerivedCategory.Q.obj M)
    ((d.tensor.map (p.hom, 𝟙 (DerivedCategory.Q.obj K)) ≫
      d.internalCurryMor (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj
        M)) ≫
      d.hom.map (b.hom.op, 𝟙 (DerivedCategory.Q.obj M))) = _
  rw [Category.assoc]
  erw [internalCurry_model_test P K T L M hP hK hT f g]
  have hcancel : (homModelIso K L).hom.op ≫ b.hom.op = (DerivedCategory.Q.map g).op := by
    rw [← op_comp]
    congr 1
    simp only [Iso.trans_hom, asIso_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom, Category.assoc,
      Iso.inv_hom_id_app, comp_obj, prod_obj, id_obj, ObjectProperty.ι_obj, b]
    erw [Category.comp_id]
  have hhom := homComparison_inv_naturality (R := R) g (𝟙 M)
  rw [homComplexFunctor_map_left, CategoryTheory.Functor.map_id] at hhom
  have hpair :
      d.hom.map (show
        (Opposite.op (DerivedCategory.Q.obj (HomComplexR R K L)), DerivedCategory.Q.obj M) ⟶
        (Opposite.op (d.hom.obj (Opposite.op (DerivedCategory.Q.obj K), DerivedCategory.Q.obj L)),
          DerivedCategory.Q.obj M) from
        ((homModelIso K L).hom.op, 𝟙 (DerivedCategory.Q.obj M))) ≫
        d.hom.map (show
          (Opposite.op (d.hom.obj (Opposite.op (DerivedCategory.Q.obj K), DerivedCategory.Q.obj
            L)), DerivedCategory.Q.obj M) ⟶
          (Opposite.op (DerivedCategory.Q.obj T), DerivedCategory.Q.obj M) from
          (b.hom.op, 𝟙 (DerivedCategory.Q.obj M))) =
      d.hom.map (show
        (Opposite.op (DerivedCategory.Q.obj (HomComplexR R K L)), DerivedCategory.Q.obj M) ⟶
        (Opposite.op (DerivedCategory.Q.obj T), DerivedCategory.Q.obj M) from
        ((DerivedCategory.Q.map g).op, 𝟙 (DerivedCategory.Q.obj M))) := by
    rw [← d.hom.map_comp]
    congr 1
    exact Prod.ext hcancel (Category.id_comp _)
  have ht : d.tensor.map (show
      (DerivedCategory.Q.obj P, DerivedCategory.Q.obj K) ⟶
      (d.hom.obj (Opposite.op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj M),
        DerivedCategory.Q.obj K) from
      (p.hom, 𝟙 (DerivedCategory.Q.obj K))) ≫
      d.tensor.map (show
        (d.hom.obj (Opposite.op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj M),
          DerivedCategory.Q.obj K) ⟶
        (DerivedCategory.Q.obj (HomComplexR R L M), DerivedCategory.Q.obj K) from
        ((homModelIso L M).hom, 𝟙 (DerivedCategory.Q.obj K))) =
    d.tensor.map (show (DerivedCategory.Q.obj P, DerivedCategory.Q.obj K) ⟶
      (DerivedCategory.Q.obj (HomComplexR R L M), DerivedCategory.Q.obj K) from
      (DerivedCategory.Q.map f, 𝟙 (DerivedCategory.Q.obj K))) := by
    rw [d.tensor_map_comp]
    simp only [Iso.trans_hom, asIso_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom, Category.assoc,
      Iso.inv_hom_id_app, comp_obj, prod_obj, id_obj, ObjectProperty.ι_obj, Category.comp_id, p]
    erw [Category.comp_id]
  have htp : tp.hom = d.tensor.map (show
      (DerivedCategory.Q.obj P, DerivedCategory.Q.obj K) ⟶
      (d.hom.obj (Opposite.op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj M),
        DerivedCategory.Q.obj K) from
      (p.hom, 𝟙 (DerivedCategory.Q.obj K))) := rfl
  have hhb : hb.hom = d.hom.map (show
      (Opposite.op (d.hom.obj (Opposite.op (DerivedCategory.Q.obj K), DerivedCategory.Q.obj L)),
        DerivedCategory.Q.obj M) ⟶
      (Opposite.op (DerivedCategory.Q.obj T), DerivedCategory.Q.obj M) from
      (b.hom.op, 𝟙 (DerivedCategory.Q.obj M))) := rfl
  rw [htp, hhb]
  simp only [Category.assoc]
  erw [reassoc_of% ht, hpair, ← hhom]
  have htensor := tensorComparison_naturality (R := R) f (𝟙 K) hK hK
  rw [CategoryTheory.Functor.map_id] at htensor
  change d.tensor.map (DerivedCategory.Q.map f, 𝟙 (DerivedCategory.Q.obj K)) ≫
    (tensorModelIso (HomComplexR R L M) K hK).hom =
    (tensorModelIso P K hK).hom ≫ DerivedCategory.Q.map (f ▷ K) at htensor
  rw [reassoc_of% htensor]
  simp only [← CategoryTheory.Functor.map_comp_assoc]
  rw [d.homEquiv_naturality_left, adjunctionCore_map_eq]

end Construction

/-- The canonical derived tensor and derived-Hom data used in the characterization equation
of Stacks 0A63 and the later functorial results, constructed as data
rather than asserted to exist. -/
@[no_expose] public noncomputable def derivedHomAdjunction {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] : DerivedHomData R := by
  letI := CochainComplex.Koszul.koszulSymmetric R
  exact
    { toDerivedHomAdjunction := Construction.adjunctionCore R
      tensorComparison := Construction.tensorComparison R
      homComparison := Construction.homComparison R
      tensorSwap_comparison := Construction.adjunctionCore_braiding_comparison R
      homEquiv_symm_map_eq := Construction.adjunctionCore_symm_map_eq R
      internalCurryMor_comparison := Construction.internalCurry_comparison }

/-- The canonical derived associator is represented by the associator of K-flat complexes,
using the canonical tensor comparisons and any proof that `K ⊗ T` is K-flat. -/
public theorem derivedHomAdjunction_tensorAssoc_comparison {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (P K T : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : P.KFlat) (hK : K.KFlat) (hT : T.KFlat) (hKT : (K ⊗ T).KFlat) :
    let d := derivedHomAdjunction (R := R)
    (d.tensorAssoc (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K)
      (DerivedCategory.Q.obj T)).hom ≫
      d.tensor.map (𝟙 (DerivedCategory.Q.obj P), (d.tensorIso K T hT).hom) ≫
      (d.tensorIso P (K ⊗ T) hKT).hom =
    d.tensor.map ((d.tensorIso P K hK).hom, 𝟙 (DerivedCategory.Q.obj T)) ≫
      (d.tensorIso (P ⊗ K) T hT).hom ≫ DerivedCategory.Q.map (α_ P K T).hom := by
  let := CochainComplex.Koszul.koszulSymmetric R
  exact Construction.associator_comparison P K T hP hK hT

/-- The canonical construction in an independently chosen universe of modules, with all
K-flat/K-injective comparison fields retained. The scalar ring `ULift.{v} R` is canonically
isomorphic to `R`; its universe `max u v` also accommodates the modules. -/
public noncomputable abbrev derivedHomAdjunctionULift {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} (ULift.{v} R))] :
    DerivedHomData (ULift.{v} R) :=
  derivedHomAdjunction


/-- Restriction of scalars along `ULift.ringEquiv.symm`, with its explicit inverse.
The scalar, module, and lift universes are independent. -/
public def uliftModuleEquivalence (R : Type u) [CommRing R] :
    ModuleCat.{v} (ULift.{t} R) ≌ ModuleCat.{v} R :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv ULift.ringEquiv.symm

/-- The functor of `uliftModuleEquivalence` is additive. -/
instance (R : Type u) [CommRing R] : (uliftModuleEquivalence.{u,v,t} R).functor.Additive :=
  inferInstanceAs (ModuleCat.restrictScalars _).Additive
/-- The inverse of `uliftModuleEquivalence` is additive. -/
instance (R : Type u) [CommRing R] : (uliftModuleEquivalence.{u,v,t} R).inverse.Additive :=
  inferInstanceAs (ModuleCat.restrictScalars _).Additive

/-- The derived equivalence induced by `uliftModuleEquivalence`. Both directions are
the exact restriction-of-scalars functors applied to complexes and localized at quasi-isomorphisms.
The two choices of derived-morphism universe are independent. -/
public def uliftDerivedEquivalence (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} (ULift.{t} R))]
    [HasDerivedCategory.{w'} (ModuleCat.{v} R)] :
    DerivedCategory (ModuleCat.{v} (ULift.{t} R)) ≌
      DerivedCategory (ModuleCat.{v} R) := by
  let e := uliftModuleEquivalence.{u,v,t} R
  let E := e.mapHomologicalComplex (ComplexShape.up ℤ)
  letI : Localization.Lifting DerivedCategory.Q (HomologicalComplex.quasiIso _ _)
      (E.functor ⋙ DerivedCategory.Q) e.functor.mapDerivedCategory :=
    ⟨e.functor.mapDerivedCategoryFactors⟩
  letI : Localization.Lifting DerivedCategory.Q (HomologicalComplex.quasiIso _ _)
      (E.inverse ⋙ DerivedCategory.Q) e.inverse.mapDerivedCategory :=
    ⟨e.inverse.mapDerivedCategoryFactors⟩
  exact Localization.equivalence
    DerivedCategory.Q (HomologicalComplex.quasiIso _ _)
    DerivedCategory.Q (HomologicalComplex.quasiIso _ _)
    (E.functor ⋙ DerivedCategory.Q) e.functor.mapDerivedCategory
    (E.inverse ⋙ DerivedCategory.Q) e.inverse.mapDerivedCategory
    (Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ e.inverse.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight E.unitIso.symm _ ≪≫
      Functor.leftUnitor _)
    (Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ e.functor.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight E.counitIso _ ≪≫
      Functor.leftUnitor _)

/-- The functor of `uliftDerivedEquivalence` is additive. -/
instance (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} (ULift.{t} R))]
    [HasDerivedCategory.{w'} (ModuleCat.{v} R)] :
    (uliftDerivedEquivalence.{u,v,t,w,w'} R).functor.Additive :=
  inferInstanceAs (uliftModuleEquivalence R).functor.mapDerivedCategory.Additive

/-- The inverse of `uliftDerivedEquivalence` is additive. -/
instance (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} (ULift.{t} R))]
    [HasDerivedCategory.{w'} (ModuleCat.{v} R)] :
    (uliftDerivedEquivalence.{u,v,t,w,w'} R).inverse.Additive :=
  inferInstanceAs (uliftModuleEquivalence R).inverse.mapDerivedCategory.Additive

universe u₁ u₂ v₁ v₂ w₁ w₂
namespace DerivedHomAdjunction
variable {R : Type u₁} [CommRing R] [HasDerivedCategory.{w₁} (ModuleCat.{v₁} R)]
  {S : Type u₂} [CommRing S] [HasDerivedCategory.{w₂} (ModuleCat.{v₂} S)]
  (d : DerivedHomAdjunction R)
  (e : DerivedCategory (ModuleCat.{v₁} R) ≌ DerivedCategory (ModuleCat.{v₂} S))
  [e.functor.Additive]

/-- The functor of `e.symm` is additive. -/
local instance : e.symm.functor.Additive := inferInstanceAs e.inverse.Additive

/-- Conjugate the tensor bifunctor by an additive equivalence. -/
public abbrev transportTensor :
    DerivedCategory (ModuleCat.{v₂} S) × DerivedCategory (ModuleCat.{v₂} S) ⥤
      DerivedCategory (ModuleCat.{v₂} S) := e.inverse.prod e.inverse ⋙ d.tensor ⋙ e.functor

/-- Conjugate the internal-Hom bifunctor by an additive equivalence. -/
public abbrev transportHom :
    (DerivedCategory (ModuleCat.{v₂} S))ᵒᵖ × DerivedCategory (ModuleCat.{v₂} S) ⥤
      DerivedCategory (ModuleCat.{v₂} S) := e.inverse.op.prod e.inverse ⋙ d.hom ⋙ e.functor

/-- Transport the additive tensor--Hom equivalence using the two adjunctions of
an equivalence of categories. -/
public def transportHomEquiv (K L M : DerivedCategory (ModuleCat.{v₂} S)) :
    (K ⟶ (d.transportHom e).obj (Opposite.op L, M)) ≃+
      ((d.transportTensor e).obj (K, L) ⟶ M) :=
  (e.symm.toAdjunction.homAddEquiv K (d.hom.obj
    (Opposite.op (e.inverse.obj L), e.inverse.obj M))).symm.trans
      ((d.homEquiv (e.inverse.obj K) (e.inverse.obj L) (e.inverse.obj M)).trans
        (e.toAdjunction.homAddEquiv (d.tensor.obj (e.inverse.obj K, e.inverse.obj L)) M).symm)

/-- Associativity after transport, using the unit of the equivalence to
identify the intermediate tensor objects. -/
public def transportTensorAssoc (K L M : DerivedCategory (ModuleCat.{v₂} S)) :
    (d.transportTensor e).obj ((d.transportTensor e).obj (K, L), M) ≅
      (d.transportTensor e).obj (K, (d.transportTensor e).obj (L, M)) :=
  e.functor.mapIso
    (d.tensor.mapIso ((e.unitIso.app _).symm.prod (Iso.refl _)) ≪≫
      d.tensorAssoc _ _ _ ≪≫
      d.tensor.mapIso ((Iso.refl _).prod (e.unitIso.app _)))

/-- Transport the entire tensor--Hom adjunction, including all naturality laws,
associativity, and symmetry, along an additive equivalence. -/
public def transport : DerivedHomAdjunction S where
  tensor := d.transportTensor e
  hom := d.transportHom e
  tensorAssoc := d.transportTensorAssoc e
  tensorSwap K L := e.functor.mapIso (d.tensorSwap (e.inverse.obj K) (e.inverse.obj L))
  tensorAssoc_naturality {K K' L L' M M'} f g h := by
    dsimp [transportTensorAssoc]
    simp only [← e.functor.map_comp]
    congr 1
    simp only [Iso.prod_hom, Iso.symm_hom, Iso.refl_hom, Iso.app_inv, Iso.app_hom]
    have hl := e.unitIso.inv.naturality
      (d.tensor.map (show (e.inverse.obj K, e.inverse.obj L) ⟶
        (e.inverse.obj K', e.inverse.obj L') from (e.inverse.map f, e.inverse.map g)))
    have hr := e.unitIso.hom.naturality
      (d.tensor.map (show (e.inverse.obj L, e.inverse.obj M) ⟶
        (e.inverse.obj L', e.inverse.obj M') from (e.inverse.map g, e.inverse.map h)))
    dsimp at hl hr
    simp only [Category.assoc]
    rw [d.tensor_map_comp_assoc]
    simp only [Category.comp_id, hl]
    have hl' := d.tensor_map_comp
      (e.unitIso.inv.app (d.tensor.obj (e.inverse.obj K, e.inverse.obj L)))
      (𝟙 (e.inverse.obj M))
      (d.tensor.map (show (e.inverse.obj K, e.inverse.obj L) ⟶
        (e.inverse.obj K', e.inverse.obj L') from (e.inverse.map f, e.inverse.map g)))
      (e.inverse.map h)
    simp only [Category.id_comp] at hl'
    rw [← reassoc_of% hl']
    rw [d.tensorAssoc_naturality_assoc]
    simp only [← Category.assoc, d.tensor_map_comp, Category.id_comp, Category.comp_id, hr]
  tensorSwap_naturality f g := by
    dsimp
    simp only [← e.functor.map_comp]
    exact congrArg e.functor.map (d.tensorSwap_naturality _ _)
  homEquiv := d.transportHomEquiv e
  homEquiv_naturality_left f a := by
    simp only [transportHomEquiv, AddEquiv.trans_apply, Adjunction.homAddEquiv_symm_apply,
      Adjunction.homEquiv_naturality_left_symm, d.homEquiv_naturality_left]
    dsimp
    simp only [e.inverse.map_id]
  homEquiv_dinaturality g a := by
    simp only [transportHomEquiv, AddEquiv.trans_apply, Adjunction.homAddEquiv_symm_apply]
    dsimp
    erw [e.symm.toAdjunction.homEquiv_naturality_right_symm]
    simp only [e.inverse.map_id]
    rw [d.homEquiv_dinaturality, e.toAdjunction.homEquiv_naturality_left_symm]
    rfl
  homEquiv_naturality_right g a := by
    simp only [transportHomEquiv, AddEquiv.trans_apply, Adjunction.homAddEquiv_symm_apply]
    dsimp
    erw [e.symm.toAdjunction.homEquiv_naturality_right_symm]
    simp only [op_id, e.inverse.map_id,
      d.homEquiv_naturality_right, e.toAdjunction.homEquiv_naturality_right_symm]
    rfl

/-- The equivalence intertwines the original and transported tensor bifunctors. -/
public def transportTensorIso :
    e.functor.prod e.functor ⋙ (d.transport e).tensor ≅ d.tensor ⋙ e.functor :=
  isoWhiskerRight (NatIso.prod e.unitIso.symm e.unitIso.symm) (d.tensor ⋙ e.functor)

/-- The equivalence intertwines the original and transported internal-Hom bifunctors. -/
public def transportHomIso :
    e.functor.op.prod e.functor ⋙ (d.transport e).hom ≅ d.hom ⋙ e.functor :=
  isoWhiskerRight (NatIso.prod (NatIso.op e.unitIso) e.unitIso.symm) (d.hom ⋙ e.functor)
end DerivedHomAdjunction

attribute [local instance] HasDerivedCategory.standard

/-- The canonical tensor--Hom adjunction on `D(R)` in an independent admissible
module universe. Its construction transports `derivedHomAdjunctionULift` along the explicit
restriction-of-scalars equivalence. Only the chosen derived category of `R`-modules
is a parameter. -/
public def derivedHomAdjunctionOverRing (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)] :
    DerivedHomAdjunction (R := R) :=
  (derivedHomAdjunctionULift.{u,v,max u v + 1} (R := R)).toDerivedHomAdjunction.transport
    (uliftDerivedEquivalence.{u,max u v,v,max u v + 1,w} R)
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]

/-- The scalar equivalence used in `derivedHomAdjunctionOverRing`. The lifted
category uses the standard localization; the derived-morphism universe of `D(R)` remains free. -/
public abbrev derivedScalarEquivalence :
    DerivedCategory (ModuleCat.{max u v} (ULift.{v} R)) ≌
      DerivedCategory (ModuleCat.{max u v} R) :=
  uliftDerivedEquivalence.{u,max u v,v,max u v + 1,w} R

/-- Compatibility of the named scalar transport with derived tensor product,
as an isomorphism of bifunctors. -/
public def derivedTensorULiftIso :
    (derivedScalarEquivalence R).functor.prod (derivedScalarEquivalence R).functor ⋙
      (derivedHomAdjunctionOverRing.{u,v,w} R).tensor ≅
    (derivedHomAdjunctionULift.{u,v,max u v + 1} (R := R)).tensor ⋙
      (derivedScalarEquivalence R).functor :=
  (derivedHomAdjunctionULift (R := R)).toDerivedHomAdjunction.transportTensorIso
    (derivedScalarEquivalence R)

/-- Compatibility of the named scalar transport with derived Hom,
as an isomorphism of bifunctors. -/
public def derivedHomULiftIso :
    (derivedScalarEquivalence R).functor.op.prod (derivedScalarEquivalence R).functor ⋙
      (derivedHomAdjunctionOverRing.{u,v,w} R).hom ≅
    (derivedHomAdjunctionULift.{u,v,max u v + 1} (R := R)).hom ⋙
      (derivedScalarEquivalence R).functor :=
  (derivedHomAdjunctionULift (R := R)).toDerivedHomAdjunction.transportHomIso
    (derivedScalarEquivalence R)

/-- A K-flat tensor model, transported to `D(R)` by restriction of scalars. -/
public def derivedTensorModelIso (K L : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ)
    (hL : L.KFlat) :
    (derivedHomAdjunctionOverRing R).tensor.obj
      ((derivedScalarEquivalence R).functor.obj (DerivedCategory.Q.obj K),
        (derivedScalarEquivalence R).functor.obj (DerivedCategory.Q.obj L)) ≅
      (derivedScalarEquivalence R).functor.obj (DerivedCategory.Q.obj (K ⊗ L)) :=
  (derivedTensorULiftIso R).app (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≪≫
    (derivedScalarEquivalence R).functor.mapIso
      ((derivedHomAdjunctionULift (R := R)).tensorIso K L hL)

/-- A K-injective Hom model, transported to `D(R)` by restriction of scalars. -/
public def derivedHomModelIso (L I : CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ)
    [I.IsKInjective] :
    (derivedHomAdjunctionOverRing R).hom.obj
      (Opposite.op ((derivedScalarEquivalence R).functor.obj (DerivedCategory.Q.obj L)),
        (derivedScalarEquivalence R).functor.obj (DerivedCategory.Q.obj I)) ≅
      (derivedScalarEquivalence R).functor.obj
        (DerivedCategory.Q.obj (CochainComplex.HomComplexR (ULift.{v} R) L I)) :=
  (derivedHomULiftIso R).app (Opposite.op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I) ≪≫
    (derivedScalarEquivalence R).functor.mapIso
      ((derivedHomAdjunctionULift (R := R)).homIso L I)


attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 0A63.** The canonical characterization equation in `D(R)`:
`Hom(K, RHom(L, M)) ≃+ Hom(K ⊗ᴸ L, M)`. The bifunctors and the equivalence are
transported from the fixed K-flat/K-injective construction, with compatibility given by
`derivedTensorULiftIso` and `derivedHomULiftIso`. No adjunction or scalar equivalence is
supplied as a parameter. The ring, module enlargement, and derived-morphism universes are
independent. -/
@[stacks 0A63]
public noncomputable def homInternalHomEquiv {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (K L M : DerivedCategory (ModuleCat.{max u v} R)) :
    (K ⟶ (derivedHomAdjunctionOverRing R).hom.obj (Opposite.op L, M)) ≃+
      ((derivedHomAdjunctionOverRing R).tensor.obj (K, L) ⟶ M) :=
  (derivedHomAdjunctionOverRing R).homEquiv K L M

/-- The tagged equivalence is exactly the transport of the lifted construction's adjunction. -/
public theorem homInternalHomEquiv_eq_transport {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (K L M : DerivedCategory (ModuleCat.{max u v} R)) :
    homInternalHomEquiv K L M =
      (derivedHomAdjunctionULift (R := R)).toDerivedHomAdjunction.transportHomEquiv
        (derivedScalarEquivalence R) K L M := rfl


end Adjunction

section Currying

open CategoryTheory MonoidalCategory

universe u v w

section

open CochainComplex HomComplex


/-- The canonical currying isomorphism for a derived-Hom adjunction, characterized on
K-flat/K-injective representatives by Hom-complex currying, together with its functoriality
in the two contravariant variables and the covariant target variable. -/
public structure DerivedHomCurrying {R : Type u} [CommRing R]
    [HasDerivedCategory.{v} (ModuleCat.{u} R)] (d : DerivedHomData R) where
  /-- The object-level currying isomorphism. -/
  iso (K L M : DerivedCategory (ModuleCat R)) :
    d.hom.obj (Opposite.op K, d.hom.obj (Opposite.op L, M)) ≅
      d.hom.obj (Opposite.op (d.tensor.obj (K, L)), M)
  /-- Contravariant naturality in the first source object. -/
  naturality_left {K K' L M : DerivedCategory (ModuleCat R)} (f : K' ⟶ K) :
    d.hom.map (f.op, 𝟙 (d.hom.obj (Opposite.op L, M))) ≫ (iso K' L M).hom =
      (iso K L M).hom ≫
        d.hom.map ((d.tensor.map (f, 𝟙 L)).op, 𝟙 M)
  /-- Contravariant naturality in the second source object. -/
  naturality_middle {K L L' M : DerivedCategory (ModuleCat R)} (f : L' ⟶ L) :
    d.hom.map
          (𝟙 (Opposite.op K), d.hom.map (f.op, 𝟙 M)) ≫
        (iso K L' M).hom =
      (iso K L M).hom ≫
        d.hom.map ((d.tensor.map (𝟙 K, f)).op, 𝟙 M)
  /-- Covariant naturality in the target object. -/
  naturality_right {K L M M' : DerivedCategory (ModuleCat R)} (f : M ⟶ M') :
    d.hom.map
          (𝟙 (Opposite.op K), d.hom.map (𝟙 (Opposite.op L), f)) ≫
        (iso K L M').hom =
      (iso K L M).hom ≫
        d.hom.map (𝟙 (Opposite.op (d.tensor.obj (K, L))), f)
  /-- On a K-flat second source and a K-injective target, currying is the image of the
  Hom-complex currying map of 0A5Y under localization, after the derived-Hom and tensor
  comparisons. The first source complex is arbitrary. -/
  representative_comparison (K L I : CochainComplex (ModuleCat R) ℤ) (hL : L.KFlat)
      [I.IsKInjective] :
    letI := homComplex_isKInjective_of_kFlat L I hL
    (iso (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
        (DerivedCategory.Q.obj I)).hom ≫
      d.hom.map ((d.tensorIso K L hL).inv.op, 𝟙 (DerivedCategory.Q.obj I)) ≫
      (d.homIso (HomologicalComplex.tensorObj K L) I).hom =
    d.hom.map (𝟙 (Opposite.op (DerivedCategory.Q.obj K)), (d.homIso L I).hom) ≫
      (d.homIso K (CochainComplex.HomComplexR R L I)).hom ≫
      DerivedCategory.Q.map (Stacks.HomComplex.Currying.curryIso K L I).hom
  /-- On degree-zero cohomology, currying is the fixed tensor--Hom adjunction of 0A63.
  The adjunction in 0A63 is itself characterized on representatives by
    `Stacks.HomComplex.TensorHomMap.Phi`. -/
  comparison (K L M : DerivedCategory (ModuleCat R))
      (a : K ⟶ d.hom.obj (Opposite.op L, M)) :
    let U := DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat R) ℤ))
    (d.tensorUnitLeft (d.tensor.obj (K, L))).inv ≫
      d.homEquiv U (d.tensor.obj (K, L)) M
        ((d.homEquiv U K (d.hom.obj (Opposite.op L, M))).symm
            ((d.tensorUnitLeft K).hom ≫ a) ≫ (iso K L M).hom) =
      d.homEquiv K L M a

namespace DerivedHomCurrying

variable {R : Type u} [CommRing R] [HasDerivedCategory.{v} (ModuleCat.{u} R)]
    {d : DerivedHomData R}

/-- The tensor unit is supplied by the localization construction in 0A63. -/
public noncomputable abbrev tensorUnitLeft (_c : DerivedHomCurrying d)
    (K : DerivedCategory (ModuleCat R)) := d.tensorUnitLeft K

/-- Naturality of the unit used by currying, inherited from 0A63. -/
public theorem tensorUnitLeft_naturality (_c : DerivedHomCurrying d)
    {K K' : DerivedCategory (ModuleCat R)} (f : K ⟶ K') :
    d.tensor.map (𝟙 (DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat R) ℤ))), f) ≫
      (d.tensorUnitLeft K').hom = (d.tensorUnitLeft K).hom ≫ f :=
  d.tensorUnitLeft_naturality f

/-- The unit used by currying agrees with the ordinary unit on K-flat representatives. -/
public theorem tensorUnitLeft_comparison (_c : DerivedHomCurrying d)
    (K : CochainComplex (ModuleCat R) ℤ) (hK : K.KFlat) :
    (d.tensorIso (𝟙_ (CochainComplex (ModuleCat R) ℤ)) K hK).hom ≫
      (DerivedCategory.Q.mapIso (λ_ K)).hom = (d.tensorUnitLeft (DerivedCategory.Q.obj K)).hom :=
  d.tensorUnitLeft_comparison K hK

/-- The degree-zero identification `H⁰(RHom(K, M)) ≃+ Hom(K, M)`, with degree-zero
cohomology expressed as morphisms from `R[0]`. Its formula uses the fixed adjunction and
the left unitor characterized on K-flat representatives. -/
public noncomputable abbrev homZeroEquiv (_c : DerivedHomCurrying d)
    (K M : DerivedCategory (ModuleCat R)) := d.homZeroEquiv K M

/-- Taking degree-zero cohomology of currying gives precisely the adjunction of 0A63. -/
public theorem homZeroEquiv_comp_iso (c : DerivedHomCurrying d)
    (K L M : DerivedCategory (ModuleCat R))
    (a : DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat R) ℤ)) ⟶
      d.hom.obj (Opposite.op K, d.hom.obj (Opposite.op L, M))) :
    c.homZeroEquiv (d.tensor.obj (K, L)) M (a ≫ (c.iso K L M).hom) =
      d.homEquiv K L M (c.homZeroEquiv K (d.hom.obj (Opposite.op L, M)) a) := by
  simpa [homZeroEquiv, DerivedHomData.homZeroEquiv] using
    c.comparison K L M (c.homZeroEquiv K (d.hom.obj (Opposite.op L, M)) a)

end DerivedHomCurrying


end

section

/-- Every object of the derived category of a category with enough injectives and exact
countable products is represented by a K-injective complex. -/
public lemma exists_kInjective_model {C : Type u} [Category.{v} C] [Abelian C]
    [EnoughInjectives C] [Limits.HasProductsOfShape ℕ C]
    [HasExactLimitsOfShape (Discrete ℕ) C] [HasDerivedCategory.{w} C]
    (X : DerivedCategory C) :
    ∃ I : CochainComplex C ℤ,
      I.IsKInjective ∧ Nonempty (DerivedCategory.Q.obj I ≅ X) := by
  obtain ⟨I, f, hf, hI⟩ :=
    CochainComplex.exists_quasiIso_isKInjective (DerivedCategory.Q.objPreimage X)
  exact ⟨I, hI, ⟨(asIso (DerivedCategory.Q.map f)).symm ≪≫
    DerivedCategory.Q.objObjPreimageIso X⟩⟩

section Helpers

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [HasDerivedCategory.{v} (ModuleCat.{u} R)]

variable (d : DerivedHomData R)

/-- The hom-set form of currying. -/
private noncomputable def curryEquiv (X K L M : DerivedCategory (ModuleCat R)) :
    (X ⟶ d.hom.obj (Opposite.op K, d.hom.obj (Opposite.op L, M))) ≃+
      (X ⟶ d.hom.obj (Opposite.op (d.tensor.obj (K, L)), M)) :=
  (d.homEquiv X K (d.hom.obj (Opposite.op L, M))).trans <|
    (d.homEquiv (d.tensor.obj (X, K)) L M).trans <| {
      toFun := fun f ↦ (d.homEquiv X (d.tensor.obj (K, L)) M).symm
        ((d.tensorAssoc X K L).inv ≫ f)
      invFun := fun f ↦ (d.tensorAssoc X K L).hom ≫
        d.homEquiv X (d.tensor.obj (K, L)) M f
      left_inv := by intro f; simp
      right_inv := by intro f; simp
      map_add' := by intro f g; simp [Preadditive.comp_add] }

/-- Currying commutes with precomposition in the representing variable. -/
private theorem curryEquiv_naturality (d : DerivedHomData R)
    {X X' K L M : DerivedCategory (ModuleCat R)} (f : X' ⟶ X)
    (a : X ⟶ d.hom.obj (Opposite.op K, d.hom.obj (Opposite.op L, M))) :
    curryEquiv d X' K L M (f ≫ a) = f ≫ curryEquiv d X K L M a := by
  dsimp [curryEquiv]
  rw [d.homEquiv_naturality_left, d.homEquiv_naturality_left]
  apply (d.homEquiv X' (d.tensor.obj (K, L)) M).injective
  simp only [AddEquiv.apply_symm_apply]
  rw [d.homEquiv_naturality_left]
  simp only [AddEquiv.apply_symm_apply ]
  have hinv : (d.tensorAssoc X' K L).inv ≫
      d.tensor.map (d.tensor.map (f, 𝟙 K), 𝟙 L) =
      d.tensor.map (f, 𝟙 (d.tensor.obj (K, L))) ≫ (d.tensorAssoc X K L).inv := by
    apply (cancel_mono (d.tensorAssoc X K L).hom).mp
    simp only [Category.assoc ]
    rw [d.tensorAssoc_naturality]
    rw [d.tensor_map_id]
    simp
  rw [reassoc_of% hinv]

/-- The isomorphism represented by `curryEquiv`. -/
private noncomputable def curryIso (d : DerivedHomData R)
    (K L M : DerivedCategory (ModuleCat R)) :
    d.hom.obj (Opposite.op K, d.hom.obj (Opposite.op L, M)) ≅
      d.hom.obj (Opposite.op (d.tensor.obj (K, L)), M) where
  hom := curryEquiv d _ K L M (𝟙 _)
  inv := (curryEquiv d _ K L M).symm (𝟙 _)
  hom_inv_id := by
    apply (curryEquiv d _ K L M).injective
    rw [curryEquiv_naturality]
    simp
  inv_hom_id := by
    have h := curryEquiv_naturality d
      ((curryEquiv d _ K L M).symm (𝟙 _)) (𝟙 _)
    simpa using h.symm

private theorem comp_curryIso_hom (d : DerivedHomData R)
    {X K L M : DerivedCategory (ModuleCat R)}
    (a : X ⟶ d.hom.obj (Opposite.op K, d.hom.obj (Opposite.op L, M))) :
    a ≫ (curryIso d K L M).hom = curryEquiv d X K L M a := by
  simpa [curryIso] using (curryEquiv_naturality d a (𝟙 _)).symm

private theorem tensorAssoc_inv_naturality (d : DerivedHomData R)
    {X X' K K' L L' : DerivedCategory (ModuleCat R)}
    (f : X ⟶ X') (g : K ⟶ K') (h : L ⟶ L') :
    (d.tensorAssoc X K L).inv ≫ d.tensor.map (d.tensor.map (f, g), h) =
      d.tensor.map (f, d.tensor.map (g, h)) ≫ (d.tensorAssoc X' K' L').inv := by
  apply (cancel_mono (d.tensorAssoc X' K' L').hom).mp
  simp only [Category.assoc ]
  rw [d.tensorAssoc_naturality]
  simp

private theorem curryIso_naturality_left (d : DerivedHomData R)
    {K K' L M : DerivedCategory (ModuleCat R)} (f : K' ⟶ K) :
    d.hom.map (f.op, 𝟙 (d.hom.obj (Opposite.op L, M))) ≫
        (curryIso d K' L M).hom =
      (curryIso d K L M).hom ≫ d.hom.map ((d.tensor.map (f, 𝟙 L)).op, 𝟙 M) := by
  rw [comp_curryIso_hom]
  apply (d.homEquiv _ _ M).injective
  rw [d.homEquiv_dinaturality]
  dsimp [curryEquiv, curryIso]
  simp only [AddEquiv.apply_symm_apply]
  have h := d.homEquiv_dinaturality (K := d.hom.obj (Opposite.op K,
    d.hom.obj (Opposite.op L, M))) (M := d.hom.obj (Opposite.op L, M)) f (𝟙 _)
  simp only [Category.id_comp] at h
  rw [h, d.homEquiv_naturality_left, ← Category.assoc, tensorAssoc_inv_naturality]
  simp only [Category.assoc]

private theorem curryIso_naturality_middle (d : DerivedHomData R)
    {K L L' M : DerivedCategory (ModuleCat R)} (f : L' ⟶ L) :
    d.hom.map (𝟙 (Opposite.op K), d.hom.map (f.op, 𝟙 M)) ≫
        (curryIso d K L' M).hom =
      (curryIso d K L M).hom ≫ d.hom.map ((d.tensor.map (𝟙 K, f)).op, 𝟙 M) := by
  rw [comp_curryIso_hom]
  apply (d.homEquiv _ _ M).injective
  rw [d.homEquiv_dinaturality]
  dsimp [curryEquiv, curryIso]
  simp only [AddEquiv.apply_symm_apply]
  have h := d.homEquiv_naturality_right (L := K)
    (show d.hom.obj (Opposite.op L, M) ⟶ d.hom.obj (Opposite.op L', M) from
      d.hom.map (f.op, 𝟙 M)) (𝟙 _)
  simp only [Category.id_comp] at h
  rw [h, d.homEquiv_dinaturality, ← Category.assoc]
  have h := tensorAssoc_inv_naturality d
    (𝟙 (d.hom.obj (Opposite.op K, d.hom.obj (Opposite.op L, M)))) (𝟙 K) f
  rw [d.tensor_map_id] at h
  rw [h, Category.assoc]

private theorem curryIso_naturality_right (d : DerivedHomData R)
    {K L M M' : DerivedCategory (ModuleCat R)} (f : M ⟶ M') :
    d.hom.map (𝟙 (Opposite.op K), d.hom.map (𝟙 (Opposite.op L), f)) ≫
        (curryIso d K L M').hom =
      (curryIso d K L M).hom ≫ d.hom.map (𝟙 (Opposite.op (d.tensor.obj (K, L))), f) := by
  rw [comp_curryIso_hom]
  apply (d.homEquiv _ _ M').injective
  rw [d.homEquiv_naturality_right]
  dsimp [curryEquiv, curryIso]
  simp only [AddEquiv.apply_symm_apply]
  have h := d.homEquiv_naturality_right (L := K)
    (show d.hom.obj (Opposite.op L, M) ⟶ d.hom.obj (Opposite.op L, M') from
      d.hom.map (𝟙 (Opposite.op L), f)) (𝟙 _)
  simp only [Category.id_comp] at h
  rw [h, d.homEquiv_naturality_right, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private def modelCurryIso (d : DerivedHomData R)
    (K L I : CochainComplex (ModuleCat R) ℤ) (hL : L.KFlat) [I.IsKInjective] :
    d.hom.obj (Opposite.op (DerivedCategory.Q.obj K),
      d.hom.obj (Opposite.op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I)) ≅
    d.hom.obj (Opposite.op (d.tensor.obj (DerivedCategory.Q.obj K,
      DerivedCategory.Q.obj L)), DerivedCategory.Q.obj I) := by
  letI := homComplex_isKInjective_of_kFlat L I hL
  exact d.hom.mapIso ((Iso.refl _).prod (d.homIso L I)) ≪≫
    d.homIso K (CochainComplex.HomComplexR R L I) ≪≫
    DerivedCategory.Q.mapIso (Stacks.HomComplex.Currying.curryIso K L I) ≪≫
    (d.homIso (K ⊗ L) I).symm ≪≫
    d.hom.mapIso ((d.tensorIso K L hL).op.prod (Iso.refl _))

set_option backward.isDefEq.respectTransparency false in
private theorem modelCurryIso_comparison (d : DerivedHomData R)
    (K L I : CochainComplex (ModuleCat R) ℤ) (hL : L.KFlat) [I.IsKInjective] :
    letI := homComplex_isKInjective_of_kFlat L I hL
    (modelCurryIso d K L I hL).hom ≫
      d.hom.map ((d.tensorIso K L hL).inv.op, 𝟙 (DerivedCategory.Q.obj I)) ≫
      (d.homIso (K ⊗ L) I).hom =
    d.hom.map (𝟙 (Opposite.op (DerivedCategory.Q.obj K)), (d.homIso L I).hom) ≫
      (d.homIso K (CochainComplex.HomComplexR R L I)).hom ≫
      DerivedCategory.Q.map (Stacks.HomComplex.Currying.curryIso K L I).hom := by
  dsimp [modelCurryIso]
  simp only [Category.assoc, ← d.hom.map_comp_assoc]
  simp [-prod_id, Prod.mkHom, ← prod_id']

private theorem exists_kFlat_right_fraction
    {K L : CochainComplex (ModuleCat R) ℤ}
    (f : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :
    ∃ (P : CochainComplex (ModuleCat R) ℤ) (_ : P.KFlat)
      (s : P ⟶ K) (_ : IsIso (DerivedCategory.Q.map s)) (g : P ⟶ L),
      f = inv (DerivedCategory.Q.map s) ≫ DerivedCategory.Q.map g := by
  obtain ⟨A, s, hs, g, rfl⟩ := DerivedCategory.right_fac f
  obtain ⟨P, p, hP, _, hp, _⟩ := exists_kFlat_resolution A
  let := hp
  let := hs
  refine ⟨P, hP, p ≫ s, ?_, p ≫ g, ?_⟩
  · rw [CategoryTheory.Functor.map_comp]
    infer_instance
  · simp [CategoryTheory.Functor.map_comp]

private theorem exists_kFlat_model (X : DerivedCategory (ModuleCat R)) :
    ∃ (P : CochainComplex (ModuleCat R) ℤ), P.KFlat ∧
      Nonempty (DerivedCategory.Q.obj P ≅ X) := by
  obtain ⟨P, p, hP, _, hp, _⟩ :=
      exists_kFlat_resolution (DerivedCategory.Q.objPreimage X)
  let := hp
  exact ⟨P, hP, ⟨asIso (DerivedCategory.Q.map p) ≪≫
    DerivedCategory.Q.objObjPreimageIso X⟩⟩

private def iteratedHomFunctor (d : DerivedHomData R) :
    (DerivedCategory (ModuleCat R))ᵒᵖ ×
      (DerivedCategory (ModuleCat R))ᵒᵖ × DerivedCategory (ModuleCat R) ⥤
        DerivedCategory (ModuleCat R) :=
  (𝟭 _).prod d.hom ⋙ d.hom

private def tensorHomFunctor (d : DerivedHomData R) :
    (DerivedCategory (ModuleCat R))ᵒᵖ ×
      (DerivedCategory (ModuleCat R))ᵒᵖ × DerivedCategory (ModuleCat R) ⥤
        DerivedCategory (ModuleCat R) where
  obj X := d.hom.obj (Opposite.op (d.tensor.obj (X.1.unop, X.2.1.unop)), X.2.2)
  map f := d.hom.map ((d.tensor.map (f.1.unop, f.2.1.unop)).op, f.2.2)
  map_id X := by
    dsimp
    rw [d.tensor_map_id, op_id]
    exact d.hom.map_id _
  map_comp {X Y Z} f g := by
    dsimp
    rw [← d.tensor_map_comp, op_comp]
    rw [← d.hom.map_comp]
    rfl

private abbrev modelTriple (K L I : CochainComplex (ModuleCat R) ℤ) :=
  (Opposite.op (DerivedCategory.Q.obj K),
    Opposite.op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I)

omit [HasDerivedCategory.{v} (ModuleCat.{u} R)] in
private theorem homComplexFunctor_map_left
    {K K' I : CochainComplex (ModuleCat R) ℤ} (f : K' ⟶ K) :
    (Model.homComplexFunctor R).map
        (show (Opposite.op K, I) ⟶ (Opposite.op K', I) from (f.op, 𝟙 I)) =
      Stacks.HomComplex.TensorHomMap.precomp R K' K I f :=
  Construction.homComplexFunctor_map_left f

omit [HasDerivedCategory.{v} (ModuleCat.{u} R)] in
private theorem homComplexFunctor_map_right
    {K I I' : CochainComplex (ModuleCat R) ℤ} (f : I ⟶ I') :
    (Model.homComplexFunctor R).map
        (show (Opposite.op K, I) ⟶ (Opposite.op K, I') from (𝟙 _, f)) =
      Stacks.HomComplex.TensorHomMap.postcomp R K I I' f := by
  simp [Model.homComplexFunctor]

private theorem homIso_naturality_left (d : DerivedHomData R)
    {K K' I : CochainComplex (ModuleCat R) ℤ} [I.IsKInjective] (f : K' ⟶ K) :
    d.hom.map ((DerivedCategory.Q.map f).op, 𝟙 (DerivedCategory.Q.obj I)) ≫
        (d.homIso K' I).hom = (d.homIso K I).hom ≫
      DerivedCategory.Q.map (Stacks.HomComplex.TensorHomMap.precomp R K' K I f) := by
  have h := d.homIso_naturality f (𝟙 I)
  change d.hom.map ((DerivedCategory.Q.map f).op, DerivedCategory.Q.map (𝟙 I)) ≫
      (d.homIso K' I).hom = (d.homIso K I).hom ≫
        DerivedCategory.Q.map ((Model.homComplexFunctor R).map
        (show (Opposite.op K, I) ⟶ (Opposite.op K', I) from (f.op, 𝟙 I))) at h
  rw [CategoryTheory.Functor.map_id, homComplexFunctor_map_left] at h
  exact h

private theorem homIso_naturality_right (d : DerivedHomData R)
    {K I I' : CochainComplex (ModuleCat R) ℤ} [I.IsKInjective] [I'.IsKInjective]
    (f : I ⟶ I') :
    d.hom.map (𝟙 (Opposite.op (DerivedCategory.Q.obj K)), DerivedCategory.Q.map f) ≫
        (d.homIso K I').hom = (d.homIso K I).hom ≫
      DerivedCategory.Q.map (Stacks.HomComplex.TensorHomMap.postcomp R K I I' f) := by
  have h := d.homIso_naturality (𝟙 K) f
  change d.hom.map ((DerivedCategory.Q.map (𝟙 K)).op, DerivedCategory.Q.map f) ≫
      (d.homIso K I').hom = (d.homIso K I).hom ≫
        DerivedCategory.Q.map ((Model.homComplexFunctor R).map
        (show (Opposite.op K, I) ⟶ (Opposite.op K, I') from (𝟙 _, f))) at h
  rw [CategoryTheory.Functor.map_id, op_id, homComplexFunctor_map_right] at h
  exact h

private theorem modelCurryIso_naturality_left (d : DerivedHomData R)
    {K K' L I : CochainComplex (ModuleCat R) ℤ} (hL : L.KFlat) [I.IsKInjective]
    (f : K' ⟶ K) :
    d.hom.map ((DerivedCategory.Q.map f).op,
        𝟙 (d.hom.obj (Opposite.op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I))) ≫
      (modelCurryIso d K' L I hL).hom =
    (modelCurryIso d K L I hL).hom ≫
      d.hom.map ((d.tensor.map (DerivedCategory.Q.map f, 𝟙 (DerivedCategory.Q.obj L))).op,
        𝟙 (DerivedCategory.Q.obj I)) := by
  let := homComplex_isKInjective_of_kFlat L I hL
  have ha :
      d.hom.map ((DerivedCategory.Q.map f).op,
          𝟙 (d.hom.obj (Opposite.op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I))) ≫
        d.hom.map (show
          (Opposite.op (DerivedCategory.Q.obj K'),
            d.hom.obj (Opposite.op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I)) ⟶
          (Opposite.op (DerivedCategory.Q.obj K'),
            DerivedCategory.Q.obj (CochainComplex.HomComplexR R L I)) from
          (𝟙 _, (d.homIso L I).hom)) =
      d.hom.map (show
          (Opposite.op (DerivedCategory.Q.obj K),
            d.hom.obj (Opposite.op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I)) ⟶
          (Opposite.op (DerivedCategory.Q.obj K),
            DerivedCategory.Q.obj (CochainComplex.HomComplexR R L I)) from
          (𝟙 _, (d.homIso L I).hom)) ≫
        d.hom.map (show
          (Opposite.op (DerivedCategory.Q.obj K),
            DerivedCategory.Q.obj (CochainComplex.HomComplexR R L I)) ⟶
          (Opposite.op (DerivedCategory.Q.obj K'),
            DerivedCategory.Q.obj (CochainComplex.HomComplexR R L I)) from
          ((DerivedCategory.Q.map f).op, 𝟙 _)) := by
    simp only [← d.hom.map_comp]
    congr 1
    simp
  have hb := homIso_naturality_left d (I := CochainComplex.HomComplexR R L I) f
  have hc := congrArg DerivedCategory.Q.map
    (Stacks.HomComplex.Currying.curryIso_naturality_left (L := L) (M := I) f)
  simp only [CategoryTheory.Functor.map_comp] at hc
  have hd :
      DerivedCategory.Q.map (Stacks.HomComplex.TensorHomMap.precomp R (K' ⊗ L) (K ⊗ L) I (f ▷ L)) ≫
        (d.homIso (K' ⊗ L) I).inv =
      (d.homIso (K ⊗ L) I).inv ≫
        d.hom.map ((DerivedCategory.Q.map (f ▷ L)).op, 𝟙 (DerivedCategory.Q.obj I)) := by
    apply (cancel_epi (d.homIso (K ⊗ L) I).hom).mp
    simp only [Iso.hom_inv_id_assoc]
    rw [← Category.assoc, ← homIso_naturality_left]
    simp
  have ht := d.tensorIso_naturality f (𝟙 L) hL hL
  simp only [CategoryTheory.Functor.map_id, tensorHom_id] at ht
  have he :
      d.hom.map (show
        (Opposite.op (DerivedCategory.Q.obj (K ⊗ L)), DerivedCategory.Q.obj I) ⟶
        (Opposite.op (DerivedCategory.Q.obj (K' ⊗ L)), DerivedCategory.Q.obj I) from
        ((DerivedCategory.Q.map (f ▷ L)).op, 𝟙 _)) ≫
      d.hom.map (show
        (Opposite.op (DerivedCategory.Q.obj (K' ⊗ L)), DerivedCategory.Q.obj I) ⟶
        (Opposite.op (d.tensor.obj (DerivedCategory.Q.obj K', DerivedCategory.Q.obj L)),
          DerivedCategory.Q.obj I) from ((d.tensorIso K' L hL).hom.op, 𝟙 _)) =
      d.hom.map (show
        (Opposite.op (DerivedCategory.Q.obj (K ⊗ L)), DerivedCategory.Q.obj I) ⟶
        (Opposite.op (d.tensor.obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)),
          DerivedCategory.Q.obj I) from ((d.tensorIso K L hL).hom.op, 𝟙 _)) ≫
      d.hom.map (show
        (Opposite.op (d.tensor.obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)),
          DerivedCategory.Q.obj I) ⟶
        (Opposite.op (d.tensor.obj (DerivedCategory.Q.obj K', DerivedCategory.Q.obj L)),
          DerivedCategory.Q.obj I) from
        ((d.tensor.map (DerivedCategory.Q.map f, 𝟙 (DerivedCategory.Q.obj L))).op, 𝟙 _)) := by
    simp only [← d.hom.map_comp]
    congr 1
    apply Prod.ext
    · change (DerivedCategory.Q.map (f ▷ L)).op ≫ (d.tensorIso K' L hL).hom.op =
        (d.tensorIso K L hL).hom.op ≫
          (d.tensor.map (DerivedCategory.Q.map f, 𝟙 (DerivedCategory.Q.obj L))).op
      exact congrArg Quiver.Hom.op ht.symm
    · simp
  dsimp only [modelCurryIso, Iso.trans_hom, CategoryTheory.Functor.mapIso_hom, Iso.symm_hom,
    CategoryTheory.Iso.prod, CategoryTheory.Prod.mkHom, Iso.op, Iso.refl]
  simp only [Category.assoc]
  rw [reassoc_of% ha, reassoc_of% hb, reassoc_of% hc, reassoc_of% hd, he]

private def extendNatIso {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (J : C ⥤ D) [J.EssSurj] (F G : D ⥤ E)
    (e : ∀ X, F.obj (J.obj X) ≅ G.obj (J.obj X))
    (he : ∀ {X Y} (f : J.obj X ⟶ J.obj Y), F.map f ≫ (e Y).hom = (e X).hom ≫ G.map f) :
    F ≅ G :=
  NatIso.ofComponents (fun X => F.mapIso (J.objObjPreimageIso X).symm ≪≫
    e (J.objPreimage X) ≪≫ G.mapIso (J.objObjPreimageIso X)) (by
      intro X Y f
      have h := he ((J.objObjPreimageIso X).hom ≫ f ≫ (J.objObjPreimageIso Y).inv)
      apply (cancel_epi (F.map (J.objObjPreimageIso X).hom)).mp
      dsimp
      simp only [Category.assoc, ← F.map_comp_assoc, Iso.hom_inv_id,
        CategoryTheory.Functor.map_id, Category.id_comp]
      rw [reassoc_of% h]
      simp only [← G.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    ])

private theorem extendNatIso_app {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (J : C ⥤ D) [J.EssSurj] (F G : D ⥤ E)
    (e : ∀ X, F.obj (J.obj X) ≅ G.obj (J.obj X))
    (he : ∀ {X Y} (f : J.obj X ⟶ J.obj Y), F.map f ≫ (e Y).hom = (e X).hom ≫ G.map f)
    (X : C) : (extendNatIso J F G e he).hom.app (J.obj X) = (e X).hom := by
  dsimp [extendNatIso]
  rw [reassoc_of% he (J.objObjPreimageIso (J.obj X)).inv]
  simp only [← G.map_comp, Iso.inv_hom_id, Category.comp_id,
    CategoryTheory.Functor.map_id]

private abbrev homMap (d : DerivedHomData R)
    {K K' M M' : DerivedCategory (ModuleCat R)} (f : K' ⟶ K) (g : M ⟶ M') :=
  d.hom.map (show (Opposite.op K, M) ⟶ (Opposite.op K', M') from (f.op, g))

private theorem homMap_comp (d : DerivedHomData R)
    {K₁ K₂ K₃ M₁ M₂ M₃ : DerivedCategory (ModuleCat R)}
    (f : K₂ ⟶ K₁) (f' : K₃ ⟶ K₂) (g : M₁ ⟶ M₂) (g' : M₂ ⟶ M₃) :
    homMap d f g ≫ homMap d f' g' = homMap d (f' ≫ f) (g ≫ g') := by
  dsimp [homMap]
  rw [← d.hom.map_comp]
  rfl

private theorem inverse_naturality {C : Type*} [Category* C]
    {X Y X' Y' : C} (e : X ≅ Y) (e' : X' ≅ Y') (f : X ⟶ X') (g : Y ⟶ Y')
    (h : f ≫ e'.hom = e.hom ≫ g) : g ≫ e'.inv = e.inv ≫ f := by
  apply (cancel_epi e.hom).mp
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← h]
  simp

private theorem modelCurryIso_naturality_middle (d : DerivedHomData R)
    {K L L' I : CochainComplex (ModuleCat R) ℤ}
    (hL : L.KFlat) (hL' : L'.KFlat) [I.IsKInjective] (f : L' ⟶ L) :
    homMap d (𝟙 (DerivedCategory.Q.obj K)) (homMap d (DerivedCategory.Q.map f)
      (𝟙 (DerivedCategory.Q.obj I))) ≫ (modelCurryIso d K L' I hL').hom =
    (modelCurryIso d K L I hL).hom ≫ homMap d
      (d.tensor.map (𝟙 (DerivedCategory.Q.obj K), DerivedCategory.Q.map f))
      (𝟙 (DerivedCategory.Q.obj I)) := by
  let := homComplex_isKInjective_of_kFlat L I hL
  let := homComplex_isKInjective_of_kFlat L' I hL'
  have ha :
      homMap d (𝟙 (DerivedCategory.Q.obj K))
          (homMap d (DerivedCategory.Q.map f) (𝟙 (DerivedCategory.Q.obj I))) ≫
        homMap d (𝟙 (DerivedCategory.Q.obj K)) (d.homIso L' I).hom =
      homMap d (𝟙 (DerivedCategory.Q.obj K)) (d.homIso L I).hom ≫
        homMap d (𝟙 (DerivedCategory.Q.obj K))
          (DerivedCategory.Q.map (Stacks.HomComplex.TensorHomMap.precomp R L' L I f)) := by
    rw [homMap_comp, homMap_comp]
    congr 1
    exact homIso_naturality_left d f
  have hb := homIso_naturality_right d (K := K) (Stacks.HomComplex.TensorHomMap.precomp R L' L I f)
  have hc := congrArg DerivedCategory.Q.map
    (Stacks.HomComplex.Currying.curryIso_naturality_middle (K := K) (M := I) f)
  simp only [CategoryTheory.Functor.map_comp] at hc
  have hd := (CategoryTheory.CommSq.vert_inv (g := d.homIso (K ⊗ L) I)
    (h := d.homIso (K ⊗ L') I) ⟨homIso_naturality_left d (K ◁ f)⟩).w
  have ht := d.tensorIso_naturality (𝟙 K) f hL' hL
  simp only [CategoryTheory.Functor.map_id, id_tensorHom] at ht
  have he :
      homMap d (DerivedCategory.Q.map (K ◁ f)) (𝟙 (DerivedCategory.Q.obj I)) ≫
        homMap d (d.tensorIso K L' hL').hom (𝟙 (DerivedCategory.Q.obj I)) =
      homMap d (d.tensorIso K L hL).hom (𝟙 (DerivedCategory.Q.obj I)) ≫
        homMap d (d.tensor.map (𝟙 (DerivedCategory.Q.obj K), DerivedCategory.Q.map f))
          (𝟙 (DerivedCategory.Q.obj I)) := by
    rw [homMap_comp, homMap_comp, ht]
  dsimp only [homMap] at ha he ⊢
  simp only [op_id] at ha he ⊢
  dsimp only [modelCurryIso, Iso.trans_hom, CategoryTheory.Functor.mapIso_hom,
    Iso.symm_hom, CategoryTheory.Iso.prod, CategoryTheory.Prod.mkHom, Iso.op, Iso.refl]
  simp only [Category.assoc]
  rw [reassoc_of% ha, reassoc_of% hb, reassoc_of% hc, reassoc_of% hd, he]

private theorem modelCurryIso_naturality_right (d : DerivedHomData R)
    {K L I I' : CochainComplex (ModuleCat R) ℤ}
    (hL : L.KFlat) [I.IsKInjective] [I'.IsKInjective] (f : I ⟶ I') :
    homMap d (𝟙 (DerivedCategory.Q.obj K))
      (homMap d (𝟙 (DerivedCategory.Q.obj L)) (DerivedCategory.Q.map f)) ≫
        (modelCurryIso d K L I' hL).hom =
    (modelCurryIso d K L I hL).hom ≫
      homMap d (𝟙 (d.tensor.obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)))
        (DerivedCategory.Q.map f) := by
  let := homComplex_isKInjective_of_kFlat L I hL
  let := homComplex_isKInjective_of_kFlat L I' hL
  have ha :
      homMap d (𝟙 (DerivedCategory.Q.obj K))
          (homMap d (𝟙 (DerivedCategory.Q.obj L)) (DerivedCategory.Q.map f)) ≫
        homMap d (𝟙 (DerivedCategory.Q.obj K)) (d.homIso L I').hom =
      homMap d (𝟙 (DerivedCategory.Q.obj K)) (d.homIso L I).hom ≫
        homMap d (𝟙 (DerivedCategory.Q.obj K))
          (DerivedCategory.Q.map (Stacks.HomComplex.TensorHomMap.postcomp R L I I' f)) := by
    rw [homMap_comp, homMap_comp]
    congr 1
    exact homIso_naturality_right d f
  have hb := homIso_naturality_right d (K := K) (Stacks.HomComplex.TensorHomMap.postcomp R L I I' f)
  have hc := congrArg DerivedCategory.Q.map
    (Stacks.HomComplex.Currying.curryIso_naturality_right (K := K) (L := L) f)
  simp only [CategoryTheory.Functor.map_comp] at hc
  have hd := (CategoryTheory.CommSq.vert_inv (g := d.homIso (K ⊗ L) I)
    (h := d.homIso (K ⊗ L) I') ⟨homIso_naturality_right d f⟩).w
  have he :
      homMap d (𝟙 (DerivedCategory.Q.obj (K ⊗ L))) (DerivedCategory.Q.map f) ≫
        homMap d (d.tensorIso K L hL).hom (𝟙 (DerivedCategory.Q.obj I')) =
      homMap d (d.tensorIso K L hL).hom (𝟙 (DerivedCategory.Q.obj I)) ≫
        homMap d (𝟙 (d.tensor.obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)))
          (DerivedCategory.Q.map f) := by
    simp only [homMap_comp, Category.id_comp, Category.comp_id]
  dsimp only [homMap] at ha he ⊢
  simp only [op_id] at ha he ⊢
  dsimp only [modelCurryIso, Iso.trans_hom, CategoryTheory.Functor.mapIso_hom,
    Iso.symm_hom, CategoryTheory.Iso.prod, CategoryTheory.Prod.mkHom, Iso.op, Iso.refl]
  simp only [Category.assoc]
  rw [reassoc_of% ha, reassoc_of% hb, reassoc_of% hc, reassoc_of% hd, he]

private abbrev firstVariable (L M : DerivedCategory (ModuleCat R)) :
    (DerivedCategory (ModuleCat R))ᵒᵖ ⥤
      (DerivedCategory (ModuleCat R))ᵒᵖ ×
        (DerivedCategory (ModuleCat R))ᵒᵖ × DerivedCategory (ModuleCat R) :=
  (𝟭 _).prod' ((CategoryTheory.Functor.const _).obj (Opposite.op L, M))

private def modelCurryLeft (d : DerivedHomData R)
    (L I : CochainComplex (ModuleCat R) ℤ) (hL : L.KFlat) [I.IsKInjective] :
    firstVariable (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj I) ⋙ iteratedHomFunctor d ≅
      firstVariable (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj I) ⋙ tensorHomFunctor d := by
  let F := firstVariable (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj I) ⋙
    iteratedHomFunctor d
  let G := firstVariable (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj I) ⋙
    tensorHomFunctor d
  let Q := (DerivedCategory.Q (C := ModuleCat R)).op
  let W := (HomologicalComplex.quasiIso (ModuleCat R) (ComplexShape.up ℤ)).op
  let e : Q ⋙ F ≅ Q ⋙ G := NatIso.ofComponents
    (fun K => modelCurryIso d K.unop L I hL) (fun f => by
      simpa [-prod_id, F, G, firstVariable, iteratedHomFunctor, tensorHomFunctor, Q]
        using modelCurryIso_naturality_left d (I := I) hL f.unop)
  letI : Localization.Lifting Q W (Q ⋙ F) F := ⟨Iso.refl _⟩
  letI : Localization.Lifting Q W (Q ⋙ G) G := ⟨Iso.refl _⟩
  exact Localization.liftNatIso Q W (Q ⋙ F) (Q ⋙ G) F G e

private theorem modelCurryLeft_app (d : DerivedHomData R)
    (K L I : CochainComplex (ModuleCat R) ℤ) (hL : L.KFlat) [I.IsKInjective] :
    (modelCurryLeft d L I hL).hom.app (Opposite.op (DerivedCategory.Q.obj K)) =
      (modelCurryIso d K L I hL).hom := by
  dsimp only [modelCurryLeft, Localization.liftNatIso]
  erw [Localization.liftNatTrans_app]
  simp

private theorem naturality_comp_inv {C D : Type*} [Category* C] [Category* D]
    (F G : C ⥤ D) {X Y Z : C}
    (a : F.obj X ⟶ G.obj X) (b : F.obj Y ⟶ G.obj Y) (c : F.obj Z ⟶ G.obj Z)
    (f : X ⟶ Z) (g : Y ⟶ Z) [IsIso g]
    (hf : F.map f ≫ c = a ≫ G.map f) (hg : F.map g ≫ c = b ≫ G.map g) :
    F.map (f ≫ inv g) ≫ b = a ≫ G.map (f ≫ inv g) := by
  apply (cancel_mono (G.map g)).mp
  simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_inv,
    Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← hg, ← Category.assoc (inv (F.map g)), IsIso.inv_hom_id, Category.id_comp, hf]

private theorem modelCurryIso_naturality_left_derived (d : DerivedHomData R)
    {K K' L I : CochainComplex (ModuleCat R) ℤ} (hL : L.KFlat) [I.IsKInjective]
    (f : DerivedCategory.Q.obj K' ⟶ DerivedCategory.Q.obj K) :
    homMap d f
        (𝟙 (d.hom.obj (Opposite.op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I))) ≫
      (modelCurryIso d K' L I hL).hom =
    (modelCurryIso d K L I hL).hom ≫
      homMap d (d.tensor.map (f, 𝟙 (DerivedCategory.Q.obj L)))
        (𝟙 (DerivedCategory.Q.obj I)) := by
  have h := (modelCurryLeft d L I hL).hom.naturality f.op
  simp only [modelCurryLeft_app] at h
  simpa [-prod_id, firstVariable, iteratedHomFunctor, tensorHomFunctor, homMap] using h

private abbrev middleVariable (K M : DerivedCategory (ModuleCat R)) :
    (DerivedCategory (ModuleCat R))ᵒᵖ ⥤
      (DerivedCategory (ModuleCat R))ᵒᵖ ×
        (DerivedCategory (ModuleCat R))ᵒᵖ × DerivedCategory (ModuleCat R) :=
  ((CategoryTheory.Functor.const _).obj (Opposite.op K)).prod'
    ((𝟭 _).prod' ((CategoryTheory.Functor.const _).obj M))

private theorem modelCurryIso_naturality_middle_derived (d : DerivedHomData R)
    {K L L' I : CochainComplex (ModuleCat R) ℤ}
    (hL : L.KFlat) (hL' : L'.KFlat) [I.IsKInjective]
    (f : DerivedCategory.Q.obj L' ⟶ DerivedCategory.Q.obj L) :
    homMap d (𝟙 (DerivedCategory.Q.obj K)) (homMap d f (𝟙 (DerivedCategory.Q.obj I))) ≫
        (modelCurryIso d K L' I hL').hom =
    (modelCurryIso d K L I hL).hom ≫ homMap d
      (d.tensor.map (𝟙 (DerivedCategory.Q.obj K), f)) (𝟙 (DerivedCategory.Q.obj I)) := by
  obtain ⟨P, hP, s, hs, g, rfl⟩ := exists_kFlat_right_fraction f
  let := hs
  let F := middleVariable (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj I) ⋙
    iteratedHomFunctor d
  let G := middleVariable (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj I) ⋙
    tensorHomFunctor d
  have hg : F.map (DerivedCategory.Q.map g).op ≫ (modelCurryIso d K P I hP).hom =
      (modelCurryIso d K L I hL).hom ≫ G.map (DerivedCategory.Q.map g).op := by
    simpa [F, G, middleVariable, iteratedHomFunctor, tensorHomFunctor, homMap]
      using modelCurryIso_naturality_middle d (K := K) (I := I) hL hP g
  have hs' : F.map (DerivedCategory.Q.map s).op ≫ (modelCurryIso d K P I hP).hom =
      (modelCurryIso d K L' I hL').hom ≫ G.map (DerivedCategory.Q.map s).op := by
    simpa [F, G, middleVariable, iteratedHomFunctor, tensorHomFunctor, homMap]
      using modelCurryIso_naturality_middle d (K := K) (I := I) hL' hP s
  have h := naturality_comp_inv F G (modelCurryIso d K L I hL).hom
    (modelCurryIso d K L' I hL').hom (modelCurryIso d K P I hP).hom
    (DerivedCategory.Q.map g).op (DerivedCategory.Q.map s).op hg hs'
  simpa [F, G, middleVariable, iteratedHomFunctor, tensorHomFunctor, homMap,
    ← op_comp, ← op_inv] using h

private theorem modelCurryIso_naturality_right_derived (d : DerivedHomData R)
    {K L I I' : CochainComplex (ModuleCat R) ℤ}
    (hL : L.KFlat) [I.IsKInjective] [I'.IsKInjective]
    (f : DerivedCategory.Q.obj I ⟶ DerivedCategory.Q.obj I') :
    homMap d (𝟙 (DerivedCategory.Q.obj K))
      (homMap d (𝟙 (DerivedCategory.Q.obj L)) f) ≫ (modelCurryIso d K L I' hL).hom =
    (modelCurryIso d K L I hL).hom ≫
      homMap d (𝟙 (d.tensor.obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L))) f := by
  obtain ⟨g, rfl⟩ := Construction.Q_map_surjective_of_isKInjective I I' f
  exact modelCurryIso_naturality_right d hL g

private theorem modelCurryIso_naturality (d : DerivedHomData R)
    {K K' L L' I I' : CochainComplex (ModuleCat R) ℤ}
    (hL : L.KFlat) (hL' : L'.KFlat) [I.IsKInjective] [I'.IsKInjective]
    (f : DerivedCategory.Q.obj K' ⟶ DerivedCategory.Q.obj K)
    (g : DerivedCategory.Q.obj L' ⟶ DerivedCategory.Q.obj L)
    (h : DerivedCategory.Q.obj I ⟶ DerivedCategory.Q.obj I') :
    homMap d f (homMap d g h) ≫ (modelCurryIso d K' L' I' hL').hom =
    (modelCurryIso d K L I hL).hom ≫ homMap d (d.tensor.map (f, g)) h := by
  have hf := modelCurryIso_naturality_left_derived d (I := I) hL f
  have hg := modelCurryIso_naturality_middle_derived d (K := K') (I := I) hL hL' g
  have hh := modelCurryIso_naturality_right_derived d (K := K') hL' h
  have he : homMap d f (homMap d g h) =
      homMap d f (𝟙 (d.hom.obj (Opposite.op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I))) ≫
        homMap d (𝟙 (DerivedCategory.Q.obj K')) (homMap d g (𝟙 (DerivedCategory.Q.obj I))) ≫
        homMap d (𝟙 (DerivedCategory.Q.obj K')) (homMap d (𝟙 (DerivedCategory.Q.obj L')) h) := by
    simp only [homMap_comp, Category.id_comp, Category.comp_id]
  rw [he]
  simp only [Category.assoc]
  rw [hh, reassoc_of% hg, reassoc_of% hf]
  simp only [homMap_comp, Category.id_comp, Category.comp_id,
    d.tensor_map_comp]

private abbrev complexModels (R : Type u) [CommRing R] :=
  CochainComplex (ModuleCat.{u} R) ℤ ×
    {L : CochainComplex (ModuleCat.{u} R) ℤ // L.KFlat} ×
    {I : CochainComplex (ModuleCat.{u} R) ℤ // I.IsKInjective}

private abbrev modelObject (X : complexModels R) := modelTriple X.1 X.2.1.val X.2.2.val

private abbrev modelsFunctor := inducedFunctor (modelObject (R := R))

private theorem modelsFunctor_essSurj : (modelsFunctor (R := R)).EssSurj := by
  refine ⟨fun X ↦ ?_⟩
  obtain ⟨L, hL, ⟨eL⟩⟩ := exists_kFlat_model X.2.1.unop
  obtain ⟨I, hI, ⟨eI⟩⟩ := exists_kInjective_model X.2.2
  let K := DerivedCategory.Q.objPreimage X.1.unop
  let eK := DerivedCategory.Q.objObjPreimageIso X.1.unop
  exact ⟨(K, ⟨L, hL⟩, ⟨I, hI⟩), ⟨eK.symm.op.prod (eL.symm.op.prod eI)⟩⟩

private def canonicalCurryIso (d : DerivedHomData R) :
    iteratedHomFunctor d ≅ tensorHomFunctor d := by
  letI := modelsFunctor_essSurj (R := R)
  refine extendNatIso (modelsFunctor (R := R)) (iteratedHomFunctor d) (tensorHomFunctor d)
    (fun X => ?_) ?_
  · letI := X.2.2.property
    exact modelCurryIso d X.1 X.2.1.val X.2.2.val X.2.1.property
  · intro X Y f
    let := X.2.2.property
    let := Y.2.2.property
    simpa [iteratedHomFunctor, tensorHomFunctor, modelsFunctor, modelObject, modelTriple,
      homMap] using
      modelCurryIso_naturality d X.2.1.property Y.2.1.property f.1.unop f.2.1.unop f.2.2

private theorem canonicalCurryIso_app (d : DerivedHomData R)
    (K L I : CochainComplex (ModuleCat R) ℤ) (hL : L.KFlat) [I.IsKInjective] :
    (canonicalCurryIso d).hom.app (modelTriple K L I) = (modelCurryIso d K L I hL).hom := by
  let := modelsFunctor_essSurj (R := R)
  unfold canonicalCurryIso
  apply extendNatIso_app (modelsFunctor (R := R)) _ _ _ _ (K, ⟨L, hL⟩, ⟨I, inferInstance⟩)
  intro X Y f
  let := X.2.2.property
  let := Y.2.2.property
  simpa [iteratedHomFunctor, tensorHomFunctor, modelsFunctor, modelObject, modelTriple,
    homMap] using
    modelCurryIso_naturality d X.2.1.property Y.2.1.property f.1.unop f.2.1.unop f.2.2

open CochainComplex HomComplex HomologicalComplex

omit [HasDerivedCategory.{v} (ModuleCat.{u} R)] in
private theorem chainTranspose_apply {K L I : CochainComplex (ModuleCat R) ℤ}
    (h : K ⊗ L ⟶ I) (r s t : ℤ) (hrs : s + r = t) (x : K.X r) (y : L.X s) :
    ((((Construction.chainTranspose h).f r).hom x).v s t hrs).hom y =
      (h.f t).hom ((ιTensorObj K L r s t (by omega)).hom (x ⊗ₜ[R] y)) :=
  Construction.chainTranspose_apply h r s t hrs x y

private abbrev chainZero {K I : CochainComplex (ModuleCat R) ℤ} (f : K ⟶ I) :=
  Construction.chainTranspose ((λ_ K).hom ≫ f)

omit [HasDerivedCategory.{v} (ModuleCat.{u} R)] in
private theorem tensor_kFlat {K L : CochainComplex (ModuleCat R) ℤ}
    (hK : K.KFlat) (hL : L.KFlat) : (K ⊗ L).KFlat :=
  Construction.kFlat_tensor K L hK hL

omit [HasDerivedCategory.{v} (ModuleCat.{u} R)] in
private theorem unit_tensor_apply (K : CochainComplex (ModuleCat R) ℤ) (n : ℤ)
    (x : (𝟙_ (CochainComplex (ModuleCat R) ℤ)).X 0) (y : K.X n) :
    ((λ_ K).hom.f n).hom ((ιTensorObj _ K 0 n n (zero_add n)).hom (x ⊗ₜ[R] y)) =
      ((singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).hom.hom x) • y := by
  have h : (λ_ K).inv.f n = (λ_ (K.X n)).inv ≫
      ((singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).inv ▷ K.X n) ≫
        ιTensorObj (𝟙_ (CochainComplex (ModuleCat R) ℤ)) K 0 n n (zero_add n) :=
    leftUnitor'_inv K n
  have hh : ιTensorObj (𝟙_ (CochainComplex (ModuleCat R) ℤ)) K 0 n n (zero_add n) ≫
      (λ_ K).hom.f n =
    ((singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).hom ▷ K.X n) ≫
      (λ_ (K.X n)).hom := by
    apply (cancel_epi ((λ_ (K.X n)).inv ≫
      ((singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).inv ▷ K.X n))).mp
    simp only [Category.assoc]
    rw [← reassoc_of% h]
    simp
  exact ConcreteCategory.congr_hom hh (x ⊗ₜ[R] y)

omit [HasDerivedCategory.{v} (ModuleCat.{u} R)] in
private theorem chainZero_apply {K I : CochainComplex (ModuleCat R) ℤ}
    (f : K ⟶ I) (x : (𝟙_ (CochainComplex (ModuleCat R) ℤ)).X 0) :
    ((chainZero f).f 0).hom x =
      ((singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).hom.hom x) •
        Cochain.ofHom f := by
  apply Cochain.ext₀
  intro s
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  rw [chainTranspose_apply]
  change (f.f s).hom (((λ_ K).hom.f s).hom
    ((ιTensorObj _ K 0 s s _).hom (x ⊗ₜ[R] y))) = _
  rw [unit_tensor_apply, map_smul]
  rfl

omit [HasDerivedCategory.{v} (ModuleCat.{u} R)] in
private theorem ofHom_homComplex_apply
    {K L I : CochainComplex (ModuleCat R) ℤ} (f : K ⟶ HomComplexR R L I)
    (r q s t : ℤ) (hrq : r + 0 = q) (hqt : s + q = t) (x : K.X r) (y : L.X s) :
    ((((Cochain.ofHom f).v r q hrq).hom x).v s t hqt).hom y =
      (((f.f r).hom x).v s t (by omega)).hom y := by
  simp only [add_zero] at hrq
  cases hrq
  rw [Cochain.ofHom_v]

omit [HasDerivedCategory.{v} (ModuleCat.{u} R)] in
private theorem chainZero_curry {K L I : CochainComplex (ModuleCat R) ℤ}
    (h : K ⊗ L ⟶ I) :
    chainZero (Construction.chainTranspose h) ≫ (Stacks.HomComplex.Currying.curryIso K L I).hom =
      chainZero h := by
  apply from_single_hom_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((Stacks.HomComplex.Currying.curryIso K L I).hom.f 0).hom
    (((chainZero (Construction.chainTranspose h)).f 0).hom x) = ((chainZero h).f 0).hom x
  rw [chainZero_apply, chainZero_apply, map_smul]
  congr 1
  exact Construction.curry_chainTranspose h

private theorem homZeroEquiv_naturality_right (d : DerivedHomData R)
    {K M M' : DerivedCategory (ModuleCat R)} (g : M ⟶ M')
    (a : DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat R) ℤ)) ⟶
      d.hom.obj (Opposite.op K, M)) :
    d.homZeroEquiv K M' (a ≫ d.hom.map (𝟙 (Opposite.op K), g)) =
      d.homZeroEquiv K M a ≫ g := by
  dsimp [DerivedHomData.homZeroEquiv]
  rw [d.homEquiv_naturality_right, Category.assoc]

private theorem homZeroEquiv_naturality_left (d : DerivedHomData R)
    {K K' M : DerivedCategory (ModuleCat R)} (f : K' ⟶ K)
    (a : DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat R) ℤ)) ⟶
      d.hom.obj (Opposite.op K, M)) :
    d.homZeroEquiv K' M (a ≫ d.hom.map (f.op, 𝟙 M)) =
      f ≫ d.homZeroEquiv K M a := by
  dsimp [DerivedHomData.homZeroEquiv]
  rw [d.homEquiv_dinaturality]
  have h := d.tensorUnitLeft_naturality f
  apply (cancel_epi (d.tensorUnitLeft K').hom).mp
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc, ← h]
  simp

private theorem homZeroEquiv_symm_naturality_right (d : DerivedHomData R)
    {K M M' : DerivedCategory (ModuleCat R)} (g : M ⟶ M') (a : K ⟶ M) :
    (d.homZeroEquiv K M').symm (a ≫ g) =
      (d.homZeroEquiv K M).symm a ≫ d.hom.map (𝟙 (Opposite.op K), g) := by
  apply (d.homZeroEquiv K M').injective
  rw [homZeroEquiv_naturality_right]
  simp

private theorem homZeroEquiv_symm_naturality_left (d : DerivedHomData R)
    {K K' M : DerivedCategory (ModuleCat R)} (f : K' ⟶ K) (a : K ⟶ M) :
    (d.homZeroEquiv K' M).symm (f ≫ a) =
      (d.homZeroEquiv K M).symm a ≫ d.hom.map (f.op, 𝟙 M) := by
  apply (d.homZeroEquiv K' M).injective
  rw [homZeroEquiv_naturality_left]
  simp

private theorem homZeroEquiv_symm_naturality (d : DerivedHomData R)
    {K K' M M' : DerivedCategory (ModuleCat R)} (f : K' ⟶ K) (g : M ⟶ M')
    (a : K ⟶ M) :
    (d.homZeroEquiv K' M').symm (f ≫ a ≫ g) =
      (d.homZeroEquiv K M).symm a ≫ homMap d f g := by
  rw [homZeroEquiv_symm_naturality_left, homZeroEquiv_symm_naturality_right]
  change (_ ≫ homMap d (𝟙 K) g) ≫ homMap d f (𝟙 M') = _
  rw [Category.assoc, homMap_comp]
  simp

private theorem homEquiv_naturality (d : DerivedHomData R)
    {K K' L L' M M' : DerivedCategory (ModuleCat R)}
    (f : K' ⟶ K) (g : L' ⟶ L) (h : M ⟶ M')
    (a : K ⟶ d.hom.obj (Opposite.op L, M)) :
    d.homEquiv K' L' M' (f ≫ a ≫ homMap d g h) =
      d.tensor.map (f, g) ≫ d.homEquiv K L M a ≫ h := by
  have hh : homMap d g h = homMap d g (𝟙 M) ≫ homMap d (𝟙 L') h := by
    simp only [homMap_comp, Category.id_comp ]
  rw [hh, ← Category.assoc a]
  dsimp only [homMap]
  simp only [op_id]
  rw [d.homEquiv_naturality_left, d.homEquiv_naturality_right,
    d.homEquiv_dinaturality]
  simp only [← Category.assoc, d.tensor_map_comp, Category.id_comp, Category.comp_id]

private theorem modelCurryIso_homZero_map (d : DerivedHomData R)
    (K L I : CochainComplex (ModuleCat R) ℤ) (hK : K.KFlat) (hL : L.KFlat)
    [I.IsKInjective] (h : K ⊗ L ⟶ I) :
    (d.homZeroEquiv (DerivedCategory.Q.obj K)
        (d.hom.obj (Opposite.op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I))).symm
      ((d.homEquiv (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
        (DerivedCategory.Q.obj I)).symm
        ((d.tensorIso K L hL).hom ≫ DerivedCategory.Q.map h)) ≫
      (modelCurryIso d K L I hL).hom =
    (d.homZeroEquiv (d.tensor.obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L))
      (DerivedCategory.Q.obj I)).symm
        ((d.tensorIso K L hL).hom ≫ DerivedCategory.Q.map h) := by
  let := homComplex_isKInjective_of_kFlat L I hL
  erw [d.homEquiv_symm_map_eq K L I hL h]
  change (d.homZeroEquiv _ _).symm
    (DerivedCategory.Q.map (Construction.chainTranspose h) ≫ (d.homIso L I).inv) ≫ _ = _
  rw [homZeroEquiv_symm_naturality_right, d.homZeroEquiv_symm_map K _ hK,
    homZeroEquiv_symm_naturality_left, d.homZeroEquiv_symm_map (K ⊗ L) I (tensor_kFlat hK hL)]
  dsimp only [modelCurryIso, Iso.trans_hom, CategoryTheory.Functor.mapIso_hom,
    Iso.symm_hom, CategoryTheory.Iso.prod, CategoryTheory.Prod.mkHom, Iso.op, Iso.refl]
  simp only [Category.assoc, ← d.hom.map_comp_assoc]
  simp [-prod_id, Prod.mkHom, ← prod_id']
  have hc := congrArg (fun f => DerivedCategory.Q.map f ≫
    (d.homIso (K ⊗ L) I).inv ≫
      homMap d (d.tensorIso K L hL).hom (𝟙 (DerivedCategory.Q.obj I)))
    (chainZero_curry h)
  simpa only [chainZero, Construction.chainTranspose, Stacks.HomComplex.TensorHomMap.postcomp_comp,
    CategoryTheory.Functor.map_comp, Category.assoc] using hc

private theorem modelCurryIso_homZero (d : DerivedHomData R)
    (K L I : CochainComplex (ModuleCat R) ℤ) (hK : K.KFlat) (hL : L.KFlat)
    [I.IsKInjective]
    (a : DerivedCategory.Q.obj K ⟶
      d.hom.obj (Opposite.op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I)) :
    (d.homZeroEquiv (DerivedCategory.Q.obj K)
      (d.hom.obj (Opposite.op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I))).symm a ≫
      (modelCurryIso d K L I hL).hom =
    (d.homZeroEquiv (d.tensor.obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L))
      (DerivedCategory.Q.obj I)).symm
      (d.homEquiv (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
        (DerivedCategory.Q.obj I) a) := by
  obtain ⟨h, hh⟩ := Construction.Q_map_surjective_of_isKInjective (K ⊗ L) I
    ((d.tensorIso K L hL).inv ≫ d.homEquiv _ _ _ a)
  have he : (d.tensorIso K L hL).hom ≫ DerivedCategory.Q.map h =
      d.homEquiv _ _ _ a := by rw [hh]; simp
  simpa only [he, AddEquiv.symm_apply_apply] using
    modelCurryIso_homZero_map d K L I hK hL h

private theorem canonicalCurryIso_homZero_transport (d : DerivedHomData R)
    {K K' L L' M M' : DerivedCategory (ModuleCat R)}
    (f : K' ⟶ K) (g : L' ⟶ L) (h : M ⟶ M')
    (a : K ⟶ d.hom.obj (Opposite.op L, M))
    (ha : (d.homZeroEquiv K (d.hom.obj (Opposite.op L, M))).symm a ≫
        (canonicalCurryIso d).hom.app (Opposite.op K, Opposite.op L, M) =
      (d.homZeroEquiv (d.tensor.obj (K, L)) M).symm (d.homEquiv K L M a)) :
    (d.homZeroEquiv K' (d.hom.obj (Opposite.op L', M'))).symm
        (f ≫ a ≫ homMap d g h) ≫
      (canonicalCurryIso d).hom.app (Opposite.op K', Opposite.op L', M') =
    (d.homZeroEquiv (d.tensor.obj (K', L')) M').symm
      (d.homEquiv K' L' M' (f ≫ a ≫ homMap d g h)) := by
  have hn : homMap d f (homMap d g h) ≫
      (canonicalCurryIso d).hom.app (Opposite.op K', Opposite.op L', M') =
    (canonicalCurryIso d).hom.app (Opposite.op K, Opposite.op L, M) ≫
      homMap d (d.tensor.map (f, g)) h := by
    simpa [iteratedHomFunctor, tensorHomFunctor, homMap, CategoryTheory.Prod.mkHom] using
      (canonicalCurryIso d).hom.naturality
        (show (Opposite.op K, Opposite.op L, M) ⟶ (Opposite.op K', Opposite.op L', M') from
          (f.op, g.op, h))
  rw [homZeroEquiv_symm_naturality, Category.assoc, hn, ← Category.assoc, ha,
    homEquiv_naturality, homZeroEquiv_symm_naturality]

private theorem homMap_id (d : DerivedHomData R)
    (K M : DerivedCategory (ModuleCat R)) :
    homMap d (𝟙 K) (𝟙 M) = 𝟙 (d.hom.obj (Opposite.op K, M)) :=
  d.hom.map_id _

private theorem canonicalCurryIso_homZero (d : DerivedHomData R)
    (K L M : DerivedCategory (ModuleCat R))
    (a : K ⟶ d.hom.obj (Opposite.op L, M)) :
    (d.homZeroEquiv K (d.hom.obj (Opposite.op L, M))).symm a ≫
        (canonicalCurryIso d).hom.app (Opposite.op K, Opposite.op L, M) =
      (d.homZeroEquiv (d.tensor.obj (K, L)) M).symm (d.homEquiv K L M a) := by
  obtain ⟨K₀, hK, ⟨eK⟩⟩ := exists_kFlat_model K
  obtain ⟨L₀, hL, ⟨eL⟩⟩ := exists_kFlat_model L
  obtain ⟨I, hI, ⟨eI⟩⟩ := exists_kInjective_model M
  let := hI
  let a₀ := eK.hom ≫ a ≫ homMap d eL.hom eI.inv
  have ha₀ : (d.homZeroEquiv (DerivedCategory.Q.obj K₀)
      (d.hom.obj (Opposite.op (DerivedCategory.Q.obj L₀), DerivedCategory.Q.obj I))).symm a₀ ≫
      (canonicalCurryIso d).hom.app (modelTriple K₀ L₀ I) =
    (d.homZeroEquiv (d.tensor.obj (DerivedCategory.Q.obj K₀, DerivedCategory.Q.obj L₀))
      (DerivedCategory.Q.obj I)).symm (d.homEquiv _ _ _ a₀) := by
    rw [canonicalCurryIso_app d K₀ L₀ I hL]
    exact modelCurryIso_homZero d K₀ L₀ I hK hL a₀
  have he : eK.inv ≫ a₀ ≫ homMap d eL.inv eI.hom = a := by
    dsimp only [a₀]
    simp only [Category.assoc, homMap_comp, Iso.inv_hom_id, homMap_id,
      Category.comp_id, Iso.inv_hom_id_assoc]
  simpa only [he] using
    canonicalCurryIso_homZero_transport d eK.inv eL.inv eI.hom a₀ ha₀

end Helpers
set_option backward.isDefEq.respectTransparency false in
/-- **Stacks 0A65.** Derived Hom satisfies the canonical currying isomorphism
`RHom(K, RHom(L, M)) ≅ RHom(K ⊗ᴸ L, M)`, functorially in `K`, `L`, and `M`.
On K-flat/K-injective representatives this is the Hom-complex currying map of Stacks 0A5Y.
On degree-zero cohomology this is the derived tensor--Hom equivalence of Stacks 0A63. -/
@[stacks 0A65, no_expose, sga "6 I 7.4" "affine case, 1st iso", sga "7 VIII 1.1" "(1.1.2) in D(R)"]
public noncomputable def derivedHomCurrying {R : Type u} [CommRing R]
    [HasDerivedCategory.{v} (ModuleCat.{u} R)] :
    DerivedHomCurrying (derivedHomAdjunction (R := R)) := by
  let d := derivedHomAdjunction (R := R)
  let c := canonicalCurryIso d
  change DerivedHomCurrying d
  refine {
    iso := fun K L M => c.app (Opposite.op K, Opposite.op L, M)
    naturality_left := ?_
    naturality_middle := ?_
    naturality_right := ?_
    representative_comparison := ?_
    comparison := ?_ }
  · intro K K' L M f
    have hid : d.hom.map (show (Opposite.op L, M) ⟶ (Opposite.op L, M) from
        (𝟙 _, 𝟙 _)) = 𝟙 _ := d.hom.map_id _
    have hn := c.hom.naturality
      (show (Opposite.op K, Opposite.op L, M) ⟶ (Opposite.op K', Opposite.op L, M) from
        (f.op, 𝟙 _, 𝟙 _))
    simpa [c, iteratedHomFunctor, tensorHomFunctor, CategoryTheory.Prod.mkHom, hid] using hn
  · intro K L L' M f
    simpa [c, iteratedHomFunctor, tensorHomFunctor, CategoryTheory.Prod.mkHom] using
      c.hom.naturality
      (show (Opposite.op K, Opposite.op L, M) ⟶ (Opposite.op K, Opposite.op L', M) from
        (𝟙 _, f.op, 𝟙 _))
  · intro K L M M' f
    simpa [c, iteratedHomFunctor, tensorHomFunctor, CategoryTheory.Prod.mkHom,
      d.tensor_map_id] using c.hom.naturality
      (show (Opposite.op K, Opposite.op L, M) ⟶ (Opposite.op K, Opposite.op L, M') from
        (𝟙 _, 𝟙 _, f))
  · intro K L I hL hI
    change (canonicalCurryIso d).hom.app (modelTriple K L I) ≫ _ = _
    rw [canonicalCurryIso_app d K L I hL]
    exact modelCurryIso_comparison d K L I hL
  · intro K L M a
    change d.homZeroEquiv (d.tensor.obj (K, L)) M
      ((d.homZeroEquiv K (d.hom.obj (Opposite.op L, M))).symm a ≫
        (canonicalCurryIso d).hom.app (Opposite.op K, Opposite.op L, M)) = _
    rw [canonicalCurryIso_homZero, AddEquiv.apply_symm_apply]


end

section

open CochainComplex HomComplex

/-- Currying in an arbitrary larger universe of modules. Lifting the ring allows use of
Mathlib's monoidal module category, whose ring and module universes must agree. The ring
universe `u`, enlargement `v`, and derived morphism universe `w` are independent. -/
public noncomputable def derivedHomCurryingULift {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} (ULift.{v} R))] :
    DerivedHomCurrying (derivedHomAdjunctionULift (R := R)) :=
  derivedHomCurrying

attribute [local instance] HasDerivedCategory.standard

/-- Currying on `D(R)` for the scalar-transported tensor and Hom of Tag 0A63.
The unit of the named scalar equivalence identifies the intermediate Hom and tensor objects,
and the middle isomorphism is the original K-flat/K-injective currying construction. -/
public def derivedHomCurryingOverRing {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (K L M : DerivedCategory (ModuleCat.{max u v} R)) :
    let d := derivedHomAdjunctionOverRing R
    d.hom.obj (Opposite.op K, d.hom.obj (Opposite.op L, M)) ≅
      d.hom.obj (Opposite.op (d.tensor.obj (K, L)), M) := by
  let e := derivedScalarEquivalence.{u, v, w} R
  let d := derivedHomAdjunctionULift.{u, v, max u v + 1} (R := R)
  exact e.functor.mapIso
    (d.hom.mapIso ((Iso.refl _).prod (e.unitIso.app _).symm) ≪≫
      (derivedHomCurryingULift (R := R)).iso (e.inverse.obj K) (e.inverse.obj L)
        (e.inverse.obj M) ≪≫
      d.hom.mapIso ((e.unitIso.app _).symm.op.prod (Iso.refl _)))

end

end Currying

section Evaluation

universe u

open CategoryTheory MonoidalCategory CochainComplex


variable {R : Type u} [CommRing R] [HasDerivedCategory (ModuleCat R)]

/-- **Stacks 0A67.** There is a canonical morphism
`RHom_R(L, M) ⊗ᴸ_R K ⟶ RHom_R(RHom_R(K, L), M)` for arbitrary objects of `D(R)`,
natural in all three objects. On K-flat and K-injective representatives it is induced by the
chain-level evaluation map of Stacks Tag 0A60 through the standard comparison isomorphisms. -/
@[stacks 0A67]
public theorem exists_evaluationToIteratedDerivedHom :
    let D := derivedHomAdjunction (R := R)
    let e₀ := ChainEvaluation.chainEvaluation
    ∃ e : ∀ (K L M : DerivedCategory (ModuleCat R)),
        D.tensor.obj (D.hom.obj (Opposite.op L, M), K) ⟶
          D.hom.obj (Opposite.op (D.hom.obj (Opposite.op K, L)), M),
      (∀ {K K' L M : DerivedCategory (ModuleCat R)} (f : K ⟶ K'),
        D.tensor.map (𝟙 (D.hom.obj (Opposite.op L, M)), f) ≫ e K' L M =
          e K L M ≫ D.hom.map
            ((D.hom.map (f.op, 𝟙 L)).op, 𝟙 M)) ∧
      (∀ {K L L' M : DerivedCategory (ModuleCat R)} (f : L ⟶ L'),
        D.tensor.map (D.hom.map (f.op, 𝟙 M), 𝟙 K) ≫ e K L M =
          e K L' M ≫ D.hom.map
            ((D.hom.map (𝟙 (Opposite.op K), f)).op, 𝟙 M)) ∧
      (∀ {K L M M' : DerivedCategory (ModuleCat R)} (f : M ⟶ M'),
        D.tensor.map (D.hom.map (𝟙 (Opposite.op L), f), 𝟙 K) ≫ e K L M' =
          e K L M ≫ D.hom.map
            (𝟙 (Opposite.op (D.hom.obj (Opposite.op K, L))), f)) ∧
      (∀ (K L M : CochainComplex (ModuleCat R) ℤ) (hK : K.KFlat)
          [L.IsKInjective] [M.IsKInjective],
        D.tensor.map ((D.homIso L M).hom, 𝟙 (DerivedCategory.Q.obj K)) ≫
              (D.tensorIso (HomComplexR R L M) K hK).hom ≫
              DerivedCategory.Q.map (e₀ K L M) ≫
              (D.homIso (HomComplexR R K L) M).inv ≫
              D.hom.map ((D.homIso K L).hom.op, 𝟙 (DerivedCategory.Q.obj M)) =
            e (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
              (DerivedCategory.Q.obj M)) := by
  let D := derivedHomAdjunction (R := R)
  refine ⟨D.toDerivedHomAdjunction.internalCurryMor, ?_, ?_, ?_, ?_⟩
  · intro K K' L M f
    exact D.toDerivedHomAdjunction.internalCurryMor_naturality_left f
  · intro K L L' M f
    exact D.toDerivedHomAdjunction.internalCurryMor_naturality_middle f
  · intro K L M M' f
    exact D.toDerivedHomAdjunction.internalCurryMor_naturality_right f
  · intro K L M hK hL hM
    exact (D.internalCurryMor_comparison K L M hK).symm


end Evaluation

section FirstVariableTriangulated

/-! ### Triangulated behaviour of derived Hom in its first variable

Derived Hom out of a distinguished triangle is again the start of a distinguished triangle: the
statement is reduced along a K-injective representative of the second argument to the degreewise
split short exact sequence of Hom complexes, which `Model.homComplex_shortExact_of_degreewiseSplit`
supplies. These were written privately in `HomComplex/Evaluation/Iterated.lean` and in
`Perfect/SystemDuality.lean`; they are stated here, with the derived-morphism universe left free
rather than fixed to the standard model, because both modules import this one. The transport of
distinguishedness they rest on is about no derived category at all and lives in
`StacksFrontier.CategoryTheory.Triangulated.DistinguishedOfIso`. -/

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CochainComplex HomComplex
open Model (homComplexFunctorFlip homComplexFunctorFlip_additive
  homComplex_shortExact_of_degreewiseSplit)

/-- Derived Hom into a fixed second argument, as a contravariant functor of the first. -/
public abbrev derivedHomFunctor {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (d : DerivedHomData R)
    (E : DerivedCategory (ModuleCat.{u} R)) :=
  (CategoryTheory.Functor.curry.obj d.hom).flip.obj E

/-- At a K-injective second argument, derived Hom out of a complex is computed by the Hom
complex: the comparison isomorphism of `DerivedHomData.homIso`, read as an isomorphism of
functors of the first argument. -/
private def homComplexComparison {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (d : DerivedHomData R)
    (I : CochainComplex (ModuleCat.{u} R) ℤ) [I.IsKInjective] :
    DerivedCategory.Q.op ⋙ derivedHomFunctor d (DerivedCategory.Q.obj I) ≅
      homComplexFunctorFlip R I ⋙ DerivedCategory.Q :=
  NatIso.ofComponents (fun X ↦ d.homIso X.unop I) (by
    intro X Y f
    change d.hom.map (show
      (Opposite.op (DerivedCategory.Q.obj X.unop), DerivedCategory.Q.obj I) ⟶
        (Opposite.op (DerivedCategory.Q.obj Y.unop), DerivedCategory.Q.obj I) from
          ((DerivedCategory.Q.map f.unop).op, 𝟙 _)) ≫
      (d.homIso Y.unop I).hom = (d.homIso X.unop I).hom ≫
        DerivedCategory.Q.map (Stacks.HomComplex.TensorHomMap.precomp R Y.unop X.unop I f.unop ≫
          Stacks.HomComplex.TensorHomMap.postcomp R Y.unop I I (𝟙 I))
    have h := d.homIso_naturality f.unop (𝟙 I)
    rw [CategoryTheory.Functor.map_id] at h
    exact h)

/-- Derived Hom out of a distinguished triangle, into a K-injective second argument, is the start
of a distinguished triangle. -/
private lemma exists_distinguished_derivedHom_of_isKInjective
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (d : DerivedHomData R)
    (I : CochainComplex (ModuleCat.{u} R) ℤ) [I.IsKInjective]
    (T : Triangle (DerivedCategory (ModuleCat.{u} R))) (hT : T ∈ distTriang _) :
    ∃ δ, Triangle.mk
      ((derivedHomFunctor d (DerivedCategory.Q.obj I)).map T.mor₂.op)
      ((derivedHomFunctor d (DerivedCategory.Q.obj I)).map T.mor₁.op) δ ∈ distTriang _ := by
  obtain ⟨X, Y, f, ⟨e⟩⟩ := (DerivedCategory.mem_distTriang_iff T.invRotate).mp
    (inv_rot_of_distTriang _ hT)
  let S := mappingCone.triangleRotateShortComplex f
  let σ := mappingCone.triangleRotateShortComplexSplitting f
  let e' : T ≅ DerivedCategory.Q.mapTriangle.obj (triangleOfDegreewiseSplit S σ) :=
    (invRotCompRot.app T).symm ≪≫ (rotate _).mapIso e ≪≫
      DerivedCategory.Q.mapTriangleRotateIso.app (mappingCone.triangle f) ≪≫
      DerivedCategory.Q.mapTriangle.mapIso
        (mappingCone.triangleRotateIsoTriangleOfDegreewiseSplit f)
  let H := derivedHomFunctor d (DerivedCategory.Q.obj I)
  let c := homComplexComparison d I
  let a₁ := H.mapIso ((Triangle.π₁.mapIso e').symm.op) ≪≫ c.app (Opposite.op S.X₁)
  let a₂ := H.mapIso ((Triangle.π₂.mapIso e').symm.op) ≪≫ c.app (Opposite.op S.X₂)
  let a₃ := H.mapIso ((Triangle.π₃.mapIso e').symm.op) ≪≫ c.app (Opposite.op S.X₃)
  let := homComplexFunctorFlip_additive R I
  let hS := homComplex_shortExact_of_degreewiseSplit R I S σ
  have key {A B : DerivedCategory (ModuleCat.{u} R)} {X Y : CochainComplex (ModuleCat.{u} R) ℤ}
      (u : A ⟶ B) (p : DerivedCategory.Q.obj X ⟶ A) (q : DerivedCategory.Q.obj Y ⟶ B)
      (g : X ⟶ Y) (hpq : DerivedCategory.Q.map g ≫ q = p ≫ u) :
      H.map u.op ≫ (H.map p.op ≫ c.hom.app (Opposite.op X)) =
        (H.map q.op ≫ c.hom.app (Opposite.op Y)) ≫
          DerivedCategory.Q.map ((homComplexFunctorFlip R I).map g.op) := by
    rw [← Category.assoc, ← H.map_comp, ← op_comp, ← hpq, op_comp, H.map_comp]
    simp only [Category.assoc]
    exact congrArg (H.map q.op ≫ ·) (c.hom.naturality g.op)
  apply exists_distinguished_of_iso _ _ _ (DerivedCategory.triangleOfSES_distinguished hS)
    a₃ a₂ a₁
  · exact key T.mor₂ _ _ S.g e'.inv.comm₂
  · exact key T.mor₁ _ _ S.f e'.inv.comm₁

/-- Derived Hom out of a distinguished triangle, into an arbitrary second argument, is the start
of a distinguished triangle. -/
public lemma exists_distinguished_derivedHom
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (d : DerivedHomData R) (E : DerivedCategory (ModuleCat.{u} R))
    (T : Triangle (DerivedCategory (ModuleCat.{u} R))) (hT : T ∈ distTriang _) :
    ∃ δ, Triangle.mk ((derivedHomFunctor d E).map T.mor₂.op)
      ((derivedHomFunctor d E).map T.mor₁.op) δ ∈ distTriang _ := by
  obtain ⟨I, hI, ⟨e⟩⟩ := exists_kInjective_model E
  let := hI
  obtain ⟨δ, hδ⟩ := exists_distinguished_derivedHom_of_isKInjective d I T hT
  let c := (CategoryTheory.Functor.curry.obj d.hom).flip.mapIso e.symm
  exact exists_distinguished_of_iso _ _ _ hδ
    (c.app (Opposite.op T.obj₃)) (c.app (Opposite.op T.obj₂))
    (c.app (Opposite.op T.obj₁))
    (c.hom.naturality T.mor₂.op) (c.hom.naturality T.mor₁.op)

end FirstVariableTriangulated

end StacksDraft.DerivedHom
