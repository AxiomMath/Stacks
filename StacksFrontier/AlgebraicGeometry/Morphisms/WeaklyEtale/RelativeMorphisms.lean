module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Cardinal
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.CategoryTheory.RepresentedBy
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import StacksCore.Tactic.StacksAttribute

/-!
# Relative morphisms from a finite free affine scheme

For affine schemes over an affine base, the relative morphism functor out of a scheme whose ring
of global sections is finite free over the base is represented by an affine scheme.

## Main results

* `AlgebraicGeometry.relativeHom_representableBy_affine`: the relative morphism functor is
  represented by an affine scheme over the base.
* `AlgebraicGeometry.relativeHom_isSheaf`: the relative morphism functor is a Zariski sheaf on
  the slice over the base.
* `AlgebraicGeometry.isIso_of_affine_components`: a morphism of Zariski sheaves on the slice is
  an isomorphism as soon as it is bijective on the affine objects.
* `AlgebraicGeometry.algSpecHomEquiv`: algebra maps correspond to morphisms of their spectra.
* `AlgebraicGeometry.specTensorIso`: the spectrum of a tensor product is the product of the
  spectra, with `AlgebraicGeometry.specTensorIso_natural` its naturality in the right factor.
* `AlgebraicGeometry.specTensorHomEquiv`: algebra maps into a tensor product correspond to
  morphisms out of a product of spectra, with
  `AlgebraicGeometry.specTensorHomEquiv_natural` its naturality in the right factor.
* `AlgebraicGeometry.tensor_repr_map`: base-changed basis coordinates commute with an algebra
  map applied to the other tensor factor.

## Implementation notes

The relative morphism functor is written categorically on the slice over the base: it sends `T`
to the morphisms `T ⨯ₛ Z ⟶ X` over `S`. Thus it is the Yoneda functor of `X` precomposed with
the opposite of the product-with-`Z` functor. The algebra structure on global sections of `Z` is
the one induced contravariantly by its structure morphism to `S`.

The representing object is built on the algebra side: a polynomial ring in the coordinates of a
basis of `Γ(Z, 𝒪_Z)` over `Γ(S, 𝒪_S)`, cut down by the relations that the resulting map be an
algebra homomorphism. Representability is then checked on affine objects of the slice and
extended by cover-density of the affines in the Zariski topology.

## References

* [Stacks Project, Tag 05Y6](https://stacks.math.columbia.edu/tag/05Y6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- **Base-changed basis coordinates commute with a map of the other tensor factor.**  For a
basis `b` of `B` over `R`, the coordinates of `C ⊗[R] B` in the base-changed basis are computed
factorwise, so pushing `x` along `h : C →ₐ[R] D` applies `h` to each coordinate. -/
lemma tensor_repr_map {R B C D ι : Type u}
    [CommRing R] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R B] [Algebra R C] [Algebra R D]
    (b : Module.Basis ι R B) (h : C →ₐ[R] D) (x : C ⊗[R] B) (i : ι) :
    (b.baseChange D).repr (Algebra.TensorProduct.map h (AlgHom.id R B) x) i =
      h ((b.baseChange C).repr x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c z => simp [Module.Basis.baseChange_repr_tmul]
  | add x y hx hy => simp [hx, hy]

private lemma exists_universal_tensor_hom_mk_le
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] {ι : Type u} [Finite ι]
    (b : Module.Basis ι R B) :
    ∃ (Q : Type u) (_ : CommRing Q) (_ : Algebra R Q)
      (e : A →ₐ[R] Q ⊗[R] B),
      #Q ≤ #A ⊔ #R ⊔ ℵ₀ ∧
      ∀ (C : Type u) [CommRing C] [Algebra R C],
        Function.Bijective (fun k : Q →ₐ[R] C ↦
          (Algebra.TensorProduct.map k (AlgHom.id R B)).comp e) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let P := MvPolynomial (A × ι) R
  let π : MvPolynomial A R →ₐ[R] A := MvPolynomial.aeval id
  have hπ : Function.Surjective π := fun a ↦ ⟨MvPolynomial.X a, MvPolynomial.aeval_X _ _⟩
  let ψ : MvPolynomial A R →ₐ[R] P ⊗[R] B :=
    MvPolynomial.aeval (fun a ↦ ∑ i, MvPolynomial.X (a, i) ⊗ₜ[R] b i)
  have hψ (a : A) (i : ι) :
      (b.baseChange P).repr (ψ (MvPolynomial.X a)) i = MvPolynomial.X (a, i) := by
    simp [ψ, Module.Basis.baseChange_repr_tmul, Module.Basis.repr_self, Finsupp.single_apply]
  have universal (C : Type u) [CommRing C] [Algebra R C] :
      Function.Bijective (fun k : P →ₐ[R] C ↦
        (Algebra.TensorProduct.map k (AlgHom.id R B)).comp ψ) := by
    constructor
    · intro k l h
      refine MvPolynomial.algHom_ext fun ⟨a, i⟩ ↦ ?_
      have := congrArg (fun f : MvPolynomial A R →ₐ[R] C ⊗[R] B ↦
        (b.baseChange C).repr (f (MvPolynomial.X a)) i) h
      simpa only [AlgHom.comp_apply, tensor_repr_map, hψ] using this
    · intro h
      refine ⟨MvPolynomial.aeval fun ai ↦ (b.baseChange C).repr (h (MvPolynomial.X ai.1)) ai.2, ?_⟩
      refine MvPolynomial.algHom_ext fun a ↦ (b.baseChange C).ext_elem fun i ↦ ?_
      rw [AlgHom.comp_apply, tensor_repr_map, hψ]
      exact MvPolynomial.aeval_X _ _
  let J : Ideal P := Ideal.span
    { c | ∃ p : MvPolynomial A R, π p = 0 ∧ ∃ i, c = (b.baseChange P).repr (ψ p) i }
  have descent (C : Type u) [CommRing C] [Algebra R C] (k : P →ₐ[R] C) :
      J ≤ RingHom.ker k.toRingHom ↔
        RingHom.ker π.toRingHom ≤
          RingHom.ker ((Algebra.TensorProduct.map k (AlgHom.id R B)).comp ψ).toRingHom := by
    rw [Ideal.span_le]
    constructor
    · intro hk p hp
      refine (b.baseChange C).ext_elem fun i ↦ ?_
      simp only [AlgHom.toRingHom_eq_coe, RingHom.mem_ker, AlgHom.coe_toRingHom] at hp ⊢
      rw [AlgHom.comp_apply, tensor_repr_map]
      simpa using hk ⟨p, hp, i, rfl⟩
    · rintro hk c ⟨p, hp, i, rfl⟩
      simpa [tensor_repr_map] using congrArg (fun x ↦ (b.baseChange C).repr x i) (hk hp)
  let Q := P ⧸ J
  let : CommRing Q := inferInstanceAs (CommRing (P ⧸ J))
  let : Algebra R Q := inferInstanceAs (Algebra R (P ⧸ J))
  let q : P →ₐ[R] Q := Ideal.Quotient.mkₐ R J
  have hq : J ≤ RingHom.ker q.toRingHom := fun _ hp ↦ Ideal.Quotient.eq_zero_iff_mem.mpr hp
  let e : A →ₐ[R] Q ⊗[R] B :=
    π.liftOfSurjective hπ ((Algebra.TensorProduct.map q (AlgHom.id R B)).comp ψ)
      ((descent Q q).mp hq)
  have he : e.comp π = (Algebra.TensorProduct.map q (AlgHom.id R B)).comp ψ :=
    AlgHom.liftOfSurjective_comp ..
  refine ⟨Q, inferInstance, inferInstance, e, ?_, ?_⟩
  · have hprod : #(A × ι) ≤ #A ⊔ ℵ₀ := by
      simp only [Cardinal.mk_prod, Cardinal.lift_id]
      exact (Cardinal.mul_le_max #A #ι).trans
        (sup_le (sup_le le_sup_left (Cardinal.mk_le_aleph0.trans le_sup_right)) le_sup_right)
    calc #Q ≤ #P := Cardinal.mk_le_of_surjective (Ideal.Quotient.mk_surjective (I := J))
      _ ≤ #R ⊔ #(A × ι) ⊔ ℵ₀ := MvPolynomial.cardinalMk_le_max
      _ ≤ #A ⊔ #R ⊔ ℵ₀ :=
          sup_le (sup_le (le_sup_of_le_left le_sup_right)
            (hprod.trans (sup_le (le_sup_of_le_left le_sup_left) le_sup_right))) le_sup_right
  intro C _ _
  have base_change (k : Q →ₐ[R] C) :
      ((Algebra.TensorProduct.map k (AlgHom.id R B)).comp e).comp π =
        (Algebra.TensorProduct.map (k.comp q) (AlgHom.id R B)).comp ψ := by
    rw [AlgHom.comp_assoc, he, ← AlgHom.comp_assoc]
    congr 1
    ext <;> simp
  constructor
  · intro k l h
    dsimp only at h
    exact (AlgHom.cancel_right (Ideal.Quotient.mkₐ_surjective R J)).mp
      ((universal C).injective (by rw [← base_change, ← base_change, h]))
  · intro h
    obtain ⟨k, hk⟩ := (universal C).surjective (h.comp π)
    dsimp only at hk
    have hkJ : J ≤ RingHom.ker k.toRingHom := (descent C k).mpr (by
      rw [hk]
      intro p hp
      show h (π p) = 0
      rw [show π p = 0 from hp, map_zero])
    let l : Q →ₐ[R] C := Ideal.Quotient.liftₐ J k hkJ
    refine ⟨l, ?_⟩
    have hl : l.comp q = k := Ideal.Quotient.liftₐ_comp J k hkJ
    have H := base_change l
    rw [hl, hk] at H
    exact (AlgHom.cancel_right hπ).mp H

private lemma exists_universal_tensor_hom_right_mk_le
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] {ι : Type u} [Finite ι]
    (b : Module.Basis ι R B) :
    ∃ (Q : Type u) (_ : CommRing Q) (_ : Algebra R Q)
      (e : A →ₐ[R] B ⊗[R] Q),
      #Q ≤ #A ⊔ #R ⊔ ℵ₀ ∧
      ∀ (C : Type u) [CommRing C] [Algebra R C],
        Function.Bijective (fun k : Q →ₐ[R] C ↦
          (Algebra.TensorProduct.map (AlgHom.id R B) k).comp e) := by
  obtain ⟨Q, _, _, e, hQ, he⟩ := exists_universal_tensor_hom_mk_le R A B b
  refine ⟨Q, inferInstance, inferInstance, (Algebra.TensorProduct.comm R Q B).toAlgHom.comp e,
    hQ, ?_⟩
  intro C _ _
  let E : (A →ₐ[R] C ⊗[R] B) ≃ (A →ₐ[R] B ⊗[R] C) :=
    { toFun := fun h ↦ (Algebra.TensorProduct.comm R C B).toAlgHom.comp h
      invFun := fun h ↦ (Algebra.TensorProduct.comm R B C).toAlgHom.comp h
      left_inv := fun h ↦ AlgHom.ext fun x ↦
        (Algebra.TensorProduct.comm R C B).symm_apply_apply (h x)
      right_inv := fun h ↦ AlgHom.ext fun x ↦
        (Algebra.TensorProduct.comm R B C).symm_apply_apply (h x) }
  convert E.bijective.comp (he C) using 1
  funext k
  dsimp [E, Function.comp_def]
  rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc]
  congr 1
  ext <;> simp

/-- **A morphism of Zariski sheaves on the slice is an isomorphism as soon as it is bijective on
the affine objects.**  Every scheme has an affine cover, so the affine objects of `Over S` are
cover-dense in the localized Zariski topology, and a morphism of sheaves restricting to an
isomorphism on a cover-dense subcategory is an isomorphism. -/
lemma isIso_of_affine_components {S : Scheme.{u}}
    {F G : (Over S)ᵒᵖ ⥤ Type u} (α : F ⟶ G)
    (hF : Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F)
    (hG : Presheaf.IsSheaf (Scheme.zariskiTopology.over S) G)
    (hα : ∀ T : Over S, IsAffine T.left → Function.Bijective (α.app (op T))) :
    IsIso α := by
  let P : ObjectProperty (Over S) := fun T ↦ IsAffine T.left
  let J := Scheme.zariskiTopology.over S
  have : P.ι.IsCoverDense J := by
    constructor
    intro T
    rw [GrothendieckTopology.mem_over_iff]
    apply Scheme.zariskiTopology.superset_covering ?_ T.left.affineCover.mem_grothendieckTopology
    rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro _ _ ⟨i⟩
    refine ⟨Over.mk (T.left.affineCover.f i ≫ T.hom),
      Over.homMk (T.left.affineCover.f i) rfl, 𝟙 _, ?_, by simp⟩
    exact ⟨⟨⟨Over.mk (T.left.affineCover.f i ≫ T.hom),
        (inferInstance : IsAffine (T.left.affineCover.X i))⟩,
      𝟙 _, Over.homMk (T.left.affineCover.f i) rfl, by simp⟩⟩
  let φ : (⟨F, hF⟩ : Sheaf J (Type u)) ⟶ ⟨G, hG⟩ := ⟨α⟩
  have : IsIso (Functor.whiskerLeft P.ι.op φ.hom) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun T ↦ (isIso_iff_bijective _).mpr (hα T.unop.obj T.unop.property)
  have : IsIso φ := Functor.IsCoverDense.iso_of_restrict_iso (G := P.ι) φ inferInstance
  exact inferInstanceAs (IsIso ((sheafToPresheaf J (Type u)).map φ))

/-- **The relative morphism functor is a Zariski sheaf on the slice.**  The product-with-`Z`
functor on the slice is `CategoryTheory.Over.star` followed by `CategoryTheory.Over.forget`, both
continuous for the localized Zariski topologies, and the Zariski topology is subcanonical. -/
lemma relativeHom_isSheaf {S : Scheme.{u}} (Z X : Over S) :
    Presheaf.IsSheaf (Scheme.zariskiTopology.over S)
      ((prod.functor.obj Z).op ⋙ yoneda.obj X) := by
  let J := Scheme.zariskiTopology.over S
  have : (prod.functor.obj Z).IsContinuous J J := by
    show (Over.star Z ⋙ Over.forget Z).IsContinuous J J
    exact Functor.isContinuous_comp _ _ J (J.over Z) J
  apply Functor.op_comp_isSheaf_of_isSheaf _ J J
  exact (isSheaf_iff_isSheaf_of_type _ _).mpr
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)

open MonoidalCategory CartesianMonoidalCategory

section
variable (R : CommRingCat.{u}) {S : Scheme.{u}}
  (F : (CommAlgCat.{u} R)ᵒᵖ ⥤ Over S) [F.Full] [F.Faithful] [PreservesFiniteLimits F]

/-- **Algebra maps correspond to morphisms of their spectra.**  For a fully faithful `F` on
`(CommAlgCat R)ᵒᵖ`, an `R`-algebra map `A →ₐ[R] C` is the same thing as a morphism
`F(C) ⟶ F(A)` of the slice. -/
noncomputable def algSpecHomEquiv (A C : CommAlgCat.{u} R) :
    (A →ₐ[R] C) ≃ (F.obj (op C) ⟶ F.obj (op A)) :=
  (show (A →ₐ[R] C) ≃ (A ⟶ C) from
    { toFun := CommAlgCat.ofHom, invFun := fun f ↦ f.hom,
      left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl }).trans
    (Quiver.Hom.opEquiv.trans ((Functor.FullyFaithful.ofFullyFaithful F).homEquiv))

/-- **The spectrum of a tensor product is the product of the spectra.**  `F` preserves finite
limits, hence finite products, so the comparison morphism out of `F` of the tensor product — the
coproduct of `R`-algebras — is an isomorphism onto the product in the slice. -/
noncomputable def specTensorIso (B C : CommAlgCat.{u} R) :
    F.obj (op (CommAlgCat.of R (B ⊗[R] C))) ≅
      F.obj (op B) ⨯ F.obj (op C) :=
  CartesianMonoidalCategory.prodComparisonIso F (op B) (op C) ≪≫
    (tensorLeftIsoProd (F.obj (op B))).app (F.obj (op C))

/-- **`AlgebraicGeometry.specTensorIso` is natural in the right tensor factor.**  Pushing along a
map `k : Q →ₐ[R] C` of the right factor corresponds, under the isomorphism, to taking the product
of the identity of `F(B)` with the morphism of spectra induced by `k`. -/
lemma specTensorIso_natural (B Q C : CommAlgCat.{u} R)
    (k : Q →ₐ[R] C) :
    (specTensorIso R F B C).inv ≫
      F.map (CommAlgCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id R B) k)).op =
      prod.map (𝟙 _) (algSpecHomEquiv R F Q C k) ≫ (specTensorIso R F B Q).inv := by
  have hinv (D : CommAlgCat.{u} R) :
      (specTensorIso R F B D).inv =
        (tensorLeftIsoProd (F.obj (op B))).inv.app (F.obj (op D)) ≫
          inv (CartesianMonoidalCategory.prodComparison F (op B) (op D)) := by
    have h0 : (CartesianMonoidalCategory.prodComparisonIso F (op B) (op D)).inv =
        inv (CartesianMonoidalCategory.prodComparison F (op B) (op D)) := by
      apply (cancel_mono (CartesianMonoidalCategory.prodComparison F (op B) (op D))).mp
      rw [IsIso.inv_hom_id]
      exact (CartesianMonoidalCategory.prodComparisonIso F (op B) (op D)).inv_hom_id
    rw [← h0]
    rfl
  have hn := CartesianMonoidalCategory.prodComparison_inv_natural_whiskerLeft
    F (A := op B) (g := (CommAlgCat.ofHom k).op)
  have ht := (tensorLeftIsoProd (F.obj (op B))).inv.naturality
    (F.map (CommAlgCat.ofHom k).op)
  have hn' := congrArg (fun m ↦
    (tensorLeftIsoProd (F.obj (op B))).inv.app (F.obj (op C)) ≫ m) hn
  have ht' := congrArg (fun m ↦ m ≫
    inv (CartesianMonoidalCategory.prodComparison F (op B) (op Q))) ht.symm
  rw [hinv, hinv]
  exact (Category.assoc _ _ _).trans (hn'.trans ((Category.assoc _ _ _).symm.trans ht'))

/-- **Algebra maps into a tensor product correspond to morphisms out of a product of spectra.**
Combine `AlgebraicGeometry.algSpecHomEquiv` for the algebra `B ⊗[R] C` with the identification
`AlgebraicGeometry.specTensorIso` of its spectrum with the product of the two spectra. -/
noncomputable def specTensorHomEquiv (A B C : CommAlgCat.{u} R) :
    (A →ₐ[R] B ⊗[R] C) ≃
      (F.obj (op B) ⨯ F.obj (op C) ⟶ F.obj (op A)) :=
  (algSpecHomEquiv R F A (CommAlgCat.of R (B ⊗[R] C))).trans
    (specTensorIso R F B C).homFromEquiv

/-- **`AlgebraicGeometry.specTensorHomEquiv` is natural in the right tensor factor.**  Composing
an algebra map `A →ₐ[R] B ⊗[R] Q` with a map `k : Q →ₐ[R] C` of the right factor corresponds to
precomposing with the product of the identity and the morphism of spectra induced by `k`. -/
lemma specTensorHomEquiv_natural
    (A B Q C : CommAlgCat.{u} R) (e : A →ₐ[R] B ⊗[R] Q) (k : Q →ₐ[R] C) :
    specTensorHomEquiv R F A B C ((Algebra.TensorProduct.map (AlgHom.id R B) k).comp e) =
      prod.map (𝟙 _) (algSpecHomEquiv R F Q C k) ≫ specTensorHomEquiv R F A B Q e := by
  show (specTensorIso R F B C).inv ≫ F.map
    ((CommAlgCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R B) k)).op ≫
      (CommAlgCat.ofHom e).op) = _
  rw [Functor.map_comp, ← Category.assoc, specTensorIso_natural, Category.assoc]
  rfl

private lemma relativeHom_representable_of_algebra_universal_mk_le
    (A B : CommAlgCat.{u} R) {ι : Type u} [Finite ι] (b : Module.Basis ι R B)
    (hFess : ∀ T : Over S, IsAffine T.left →
      ∃ C : CommAlgCat.{u} R, Nonempty (F.obj (op C) ≅ T)) :
    ∃ C : CommAlgCat.{u} R, #C ≤ #A ⊔ #R ⊔ ℵ₀ ∧ Nonempty
      (((prod.functor.obj (F.obj (op B))).op ⋙ yoneda.obj (F.obj (op A))).RepresentableBy
        (F.obj (op C))) := by
  classical
  obtain ⟨Q, _, _, e, hQ, he⟩ := exists_universal_tensor_hom_right_mk_le R A B b
  let Q' : CommAlgCat.{u} R := .of R Q
  let W := F.obj (op Q')
  let H := (prod.functor.obj (F.obj (op B))).op ⋙ yoneda.obj (F.obj (op A))
  let α : yoneda.obj W ⟶ H := yonedaEquiv.symm (specTensorHomEquiv R F A B Q' e)
  have hspec (C : CommAlgCat.{u} R) : Function.Bijective (α.app (op (F.obj (op C)))) := by
    have hb := (specTensorHomEquiv R F A B C).bijective.comp (he C)
    have hn : ((α.app (op (F.obj (op C)))) ∘ (algSpecHomEquiv R F Q' C)) =
        (specTensorHomEquiv R F A B C) ∘
          (fun k : Q →ₐ[R] C ↦ (Algebra.TensorProduct.map (AlgHom.id R B) k).comp e) :=
      funext fun k ↦ (specTensorHomEquiv_natural R F A B Q' C e k).symm
    rw [← hn] at hb
    exact (Function.Bijective.of_comp_iff _ (algSpecHomEquiv R F Q' C).bijective).mp hb
  have : IsIso α := isIso_of_affine_components α
    ((isSheaf_iff_isSheaf_of_type _ _).mpr
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _))
    (relativeHom_isSheaf _ _) (by
      intro T hT
      obtain ⟨C, ⟨i⟩⟩ := hFess T hT
      have := (isIso_iff_bijective _).mpr (hspec C)
      exact (isIso_iff_bijective _).mp ((α.isIso_app_iff_of_iso i.op).mpr this))
  exact ⟨Q', hQ, ⟨Functor.representableByEquiv.symm (asIso α)⟩⟩
end

/-- **Stacks Project, Tag 05Y6, with the spectrum that represents the functor named and its
cardinality bounded.** If `Z` and `X` are affine schemes over an affine scheme `S` and
`Γ(Z, 𝒪_Z)` is finite free over `Γ(S, 𝒪_S)`, then the relative morphism functor `Mor_S(Z, X)` is
represented by the spectrum of a ring `Q` of cardinality at most
`max ℵ₀ (max #Γ(X, 𝒪_X) #Γ(S, 𝒪_S))`.

The ring is the one the construction produces: a polynomial ring over `Γ(S, 𝒪_S)` on the
coordinates, with respect to a basis of `Γ(Z, 𝒪_Z)`, of the image of each element of
`Γ(X, 𝒪_X)`, cut down by the relations making the resulting map an algebra homomorphism. So it is
generated by a set of cardinality at most `#Γ(X, 𝒪_X)` times a finite one, which is what bounds
it. -/
lemma relativeHom_representableBy_affine_mk_le
    (S Z X : Scheme.{u}) (f : Z ⟶ S) (g : X ⟶ S)
    [IsAffine S] [IsAffine Z] [IsAffine X]
    (hfinite : letI := f.appTop.hom.toAlgebra
      Module.Finite Γ(S, ⊤) Γ(Z, ⊤))
    (hfree : letI := f.appTop.hom.toAlgebra
      Module.Free Γ(S, ⊤) Γ(Z, ⊤)) :
    ∃ (W : Over S) (Q : Type u) (_ : CommRing Q), IsAffine W.left ∧
      #Q ≤ #Γ(X, ⊤) ⊔ #Γ(S, ⊤) ⊔ ℵ₀ ∧
      Nonempty (W.left ≅ Spec (CommRingCat.of Q)) ∧
      Nonempty
        (((Limits.prod.functor.obj (Over.mk f)).op ⋙
          yoneda.obj (Over.mk g)).RepresentableBy W) := by
  classical
  let R := Γ(S, ⊤)
  let : Algebra R Γ(Z, ⊤) := f.appTop.hom.toAlgebra
  let : Algebra R Γ(X, ⊤) := g.appTop.hom.toAlgebra
  have : Module.Finite R Γ(Z, ⊤) := hfinite
  have : Module.Free R Γ(Z, ⊤) := hfree
  let A : CommAlgCat.{u} R := .of R Γ(X, ⊤)
  let B : CommAlgCat.{u} R := .of R Γ(Z, ⊤)
  let F : (CommAlgCat.{u} R)ᵒᵖ ⥤ Over S :=
    algSpec R ⋙ Over.map S.isoSpec.inv
  have hFaff (C : CommAlgCat.{u} R) : IsAffine (F.obj (op C)).left := by
    show IsAffine (Spec (.of C))
    infer_instance
  have hFess (T : Over S) (hT : IsAffine T.left) :
      ∃ C : CommAlgCat.{u} R, Nonempty (F.obj (op C) ≅ T) := by
    let T' := (Over.map S.isoSpec.hom).obj T
    obtain ⟨C, ⟨i⟩⟩ := (essImage_algSpec (R := R) (G := T')).mpr hT
    exact ⟨C.unop, ⟨(Over.map S.isoSpec.inv).mapIso i ≪≫
      (Over.mapIso S.isoSpec).unitIso.symm.app T⟩⟩
  obtain ⟨C, hC, ⟨h⟩⟩ := relativeHom_representable_of_algebra_universal_mk_le R F A B
    (Module.Free.chooseBasis R Γ(Z, ⊤)) hFess
  let eZ : F.obj (op B) ≅ Over.mk f :=
    Over.isoMk Z.isoSpec.symm (by exact (arrowIsoSpecΓOfIsAffine f).inv.w)
  let eX : F.obj (op A) ≅ Over.mk g :=
    Over.isoMk X.isoSpec.symm (by exact (arrowIsoSpecΓOfIsAffine g).inv.w)
  refine ⟨F.obj (op C), C, inferInstance, hFaff C, hC, ⟨Iso.refl _⟩, ⟨h.ofIso ?_⟩⟩
  exact Functor.isoWhiskerRight (NatIso.op (prod.functor.mapIso eZ).symm)
    (yoneda.obj (F.obj (op A))) ≪≫
    Functor.isoWhiskerLeft (prod.functor.obj (Over.mk f)).op (yoneda.mapIso eX)

/-- **Stacks Project, Tag 05Y6.** If `Z` and `X` are affine schemes over an affine scheme `S`
and `Γ(Z, 𝒪_Z)` is finite free over `Γ(S, 𝒪_S)`, then the relative morphism
functor `Mor_S(Z, X)` is represented by an affine scheme over `S`. -/
@[stacks 05Y6]
lemma relativeHom_representableBy_affine
    (S Z X : Scheme.{u}) (f : Z ⟶ S) (g : X ⟶ S)
    [IsAffine S] [IsAffine Z] [IsAffine X]
    (hfinite : letI := f.appTop.hom.toAlgebra
      Module.Finite Γ(S, ⊤) Γ(Z, ⊤))
    (hfree : letI := f.appTop.hom.toAlgebra
      Module.Free Γ(S, ⊤) Γ(Z, ⊤)) :
    ∃ W : Over S, IsAffine W.left ∧
      Nonempty
        (((Limits.prod.functor.obj (Over.mk f)).op ⋙
          yoneda.obj (Over.mk g)).RepresentableBy W) := by
  obtain ⟨W, Q, _, hW, -, -, hr⟩ :=
    relativeHom_representableBy_affine_mk_le S Z X f g hfinite hfree
  exact ⟨W, hW, hr⟩

end AlgebraicGeometry
