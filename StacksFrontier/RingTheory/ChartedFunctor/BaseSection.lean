module

public import StacksFrontier.RingTheory.ChartedFunctor.LiftTorsor
public import StacksFrontier.RingTheory.ChartedFunctor.TangentBaseChange
public import Mathlib.RingTheory.Flat.Basic

/-!
# The section over the reduction of the base, pulled back to every algebra

Let `F` be a functor on bounded `R`-algebras, `I` an ideal of `R` of square zero, and `x` a
section of `F` over `R ⧸ I`. For every bounded `R`-algebra `P` this file pulls `x` back to the
reduction `P ⧸ I P` and so attaches to `P` the tangent `E(P)` of `F` at that section, with
coefficients in the conormal module of `I P`, and the lifts of that section to `P`. Both are
functorial in `P`, the lifts compatibly with the tangent action.

For an `R`-flat algebra `N` the conormal module of `I P` base changes:
`(I P)/(I P)² ⊗_R N ≅ I(P ⊗_R N)/(I(P ⊗_R N))²`. With the base change of the tangent this gives
`E(P) ⊗_R N ≅ E(P ⊗_R N)` at every chart point.

## Main definitions

* `Stacks.ChartedFunctor.BaseSection.pt`: the section `x` pulled back to `P ⧸ I P`.
* `Stacks.ChartedFunctor.BaseSection.tens`: the tensor product `P ⊗_R N` of bounded algebras.

## Main results

* `Stacks.ChartedFunctor.BaseSection.bijective_conormalLinMap_tens`: base change of the
  conormal module of `I P` along a flat algebra.
* `Stacks.ChartedFunctor.BaseSection.bijective_conormalLinMap_of_tensor`: the same for an algebra
  presented as a tensor product with a flat algebra.

## References

* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
-/

@[expose] public noncomputable section

open CategoryTheory Cardinal TensorProduct

universe u

namespace Stacks.ChartedFunctor

namespace BaseSection

variable {R : Type u} [CommRing R] {κ : Cardinal.{u}} [Fact (ℵ₀ < κ)]
  {F : BoundedAlg R κ ⥤ Type u} (hR : #R < κ) (I : Ideal R)

/-- The base ring as a bounded algebra over itself. -/
abbrev base : BoundedAlg R κ := BoundedAlg.of R hR

/-- The structure map of a bounded algebra. -/
abbrev toP (P : BoundedAlg R κ) : base hR ⟶ P := BoundedAlg.ofHom (Algebra.ofId R P.obj)

/-- The extension `I P` of the ideal `I` to an algebra. -/
abbrev ideal (P : BoundedAlg R κ) : Ideal P.obj := I.map (algebraMap R P.obj)

omit [Fact (ℵ₀ < κ)] in
/-- The structure map `R → P` carries `I` into `I P`. -/
lemma le_comap_ideal (P : BoundedAlg R κ) :
    I ≤ (ideal I P).comap (BoundedAlg.toAlgHom (toP hR P)) :=
  Ideal.le_comap_map

omit [Fact (ℵ₀ < κ)] in
/-- A map `P → Q` of bounded algebras carries `I P` into `I Q`. -/
lemma ideal_le_comap {P Q : BoundedAlg R κ} (g : P ⟶ Q) :
    ideal I P ≤ (ideal I Q).comap (BoundedAlg.toAlgHom g) := by
  rw [Ideal.map_le_iff_le_comap]
  intro i hi
  change BoundedAlg.toAlgHom g (algebraMap R P.obj i) ∈ ideal I Q
  rw [AlgHom.commutes]
  exact Ideal.mem_map_of_mem _ hi

omit [Fact (ℵ₀ < κ)] in
/-- The ideal `I P` has square zero when `I` does. -/
lemma ideal_sq (hI : I ^ 2 = ⊥) (P : BoundedAlg R κ) : ideal I P ^ 2 = ⊥ := by
  rw [← Ideal.map_pow, hI, Ideal.map_bot]

variable {hR I}

omit [Fact (ℵ₀ < κ)] in
/-- The structure map of `P` followed by a map `P → Q` is the structure map of `Q`. -/
lemma toP_comp {P Q : BoundedAlg R κ} (g : P ⟶ Q) : toP hR P ≫ g = toP hR Q :=
  BoundedAlg.hom_ext (AlgHom.ext fun r ↦ (BoundedAlg.toAlgHom g).commutes r)

variable (hR I) (x : F.obj (quot (base hR) I))

/-- The section `x` pulled back to the reduction `P ⧸ I P`. -/
abbrev pt (P : BoundedAlg R κ) : F.obj (quot P (ideal I P)) :=
  F.map (quotMap (toP hR P) (le_comap_ideal hR I P)) x

variable {hR I x}

omit [Fact (ℵ₀ < κ)] in
/-- The map `P ⧸ I P → Q ⧸ I Q` induced by `g : P → Q` carries the pulled-back section over `P` to
the one over `Q`. -/
lemma pt_map {P Q : BoundedAlg R κ} (g : P ⟶ Q) :
    F.map (quotMap g (ideal_le_comap I g)) (pt hR I x P) = pt hR I x Q := by
  rw [← Functor.map_comp_apply, quotMap_comp]
  have : quotMap (toP hR P ≫ g) (fun j hj ↦ ideal_le_comap I g (le_comap_ideal hR I P hj)) =
      quotMap (toP hR Q) (le_comap_ideal hR I Q) :=
    BoundedAlg.hom_ext <| AlgHom.ext fun a ↦ by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      exact congrArg (Ideal.Quotient.mk (ideal I Q)) ((BoundedAlg.toAlgHom g).commutes a)
  rw [this]

omit [Fact (ℵ₀ < κ)] in
/-- The images of a section with a chart point have chart points. -/
lemma hasChartPoint_pt {P Q : BoundedAlg R κ} (g : P ⟶ Q)
    (h : HasChartPoint F (pt hR I x P)) : HasChartPoint F (pt hR I x Q) := by
  rw [← pt_map g]
  exact h.map _

/-! ### Tensor products -/

/-- The tensor product `P ⊗_R N` of two bounded algebras. -/
abbrev tens (P N : BoundedAlg R κ) : BoundedAlg R κ :=
  BoundedAlg.of (P.obj ⊗[R] N.obj) (mk_tensorProduct_lt R Fact.out P.2 N.2)

/-- The inclusion of the left factor. -/
abbrev inclL (P N : BoundedAlg R κ) : P ⟶ tens P N :=
  BoundedAlg.ofHom Algebra.TensorProduct.includeLeft

/-- The inclusion of the right factor. -/
abbrev inclR (P N : BoundedAlg R κ) : N ⟶ tens P N :=
  BoundedAlg.ofHom Algebra.TensorProduct.includeRight

/-- The tensor product of a map with the identity of the right factor. -/
abbrev tensMap {P Q : BoundedAlg R κ} (g : P ⟶ Q) (N : BoundedAlg R κ) : tens P N ⟶ tens Q N :=
  BoundedAlg.ofHom (Algebra.TensorProduct.map (BoundedAlg.toAlgHom g) (AlgHom.id R N.obj))

/-- The left inclusion is compatible with `g ⊗ id`: `inclL P N ≫ tensMap g N = g ≫ inclL Q N`. -/
lemma inclL_tensMap {P Q : BoundedAlg R κ} (g : P ⟶ Q) (N : BoundedAlg R κ) :
    inclL P N ≫ tensMap g N = g ≫ inclL Q N :=
  BoundedAlg.hom_ext (AlgHom.ext fun _ ↦ rfl)

/-- The right inclusion is compatible with `g ⊗ id`: `inclR P N ≫ tensMap g N = inclR Q N`. -/
lemma inclR_tensMap {P Q : BoundedAlg R κ} (g : P ⟶ Q) (N : BoundedAlg R κ) :
    inclR P N ≫ tensMap g N = inclR Q N := by
  refine BoundedAlg.hom_ext (AlgHom.ext fun a ↦ ?_)
  change Algebra.TensorProduct.map (BoundedAlg.toAlgHom g) (AlgHom.id R N.obj) (1 ⊗ₜ a) = 1 ⊗ₜ a
  simp

/-! ### Base change of the conormal module -/

variable (I) in
/-- Base change of the conormal module of `I P` along a flat algebra: the linearised map
`(I P)/(I P)² ⊗_R N → I(P ⊗ N)/(I(P ⊗ N))²` is bijective. -/
theorem bijective_conormalLinMap_tens (hI : I ^ 2 = ⊥) (P N : BoundedAlg R κ)
    [Module.Flat R N.obj] :
    Function.Bijective (conormalLinMap (inclL P N) (ideal_le_comap I (inclL P N)) N.obj
      (BoundedAlg.toAlgHom (inclR P N))) := by
  set J := ideal I P
  set J' := ideal I (tens P N)
  have hJ : J ^ 2 = ⊥ := ideal_sq I hI P
  have hJ' : J' ^ 2 = ⊥ := ideal_sq I hI (tens P N)
  have inj_cot : ∀ {A : Type u} [CommRing A] (K : Ideal A), K ^ 2 = ⊥ →
      Function.Injective K.toCotangent := fun K hK a b hab ↦ by
    rw [K.toCotangent_eq, hK] at hab
    exact Subtype.ext (sub_eq_zero.1 (Ideal.mem_bot.1 hab))
  have hinc : Function.Injective ((J.restrictScalars R).subtype.rTensor N.obj) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective
  have hmemJ' : ∀ t : (J.restrictScalars R) ⊗[R] N.obj,
      (J.restrictScalars R).subtype.rTensor N.obj t ∈ J' := by
    intro t
    induction t using TensorProduct.inductionOn with
    | add s t hs ht => rw [map_add]; exact J'.add_mem hs ht
    | tmul j n =>
      change (j : P.obj) ⊗ₜ[R] n ∈ J'
      have hj : (j : P.obj) ∈ J := j.2
      have : ∀ p ∈ J, p ⊗ₜ[R] n ∈ J' := by
        intro p hp
        refine Submodule.span_induction (p := fun p _ ↦ p ⊗ₜ[R] n ∈ J') ?_ ?_ ?_ ?_ hp
        · rintro _ ⟨i, hi, rfl⟩
          have : (algebraMap R P.obj i) ⊗ₜ[R] n =
              algebraMap R (P.obj ⊗[R] N.obj) i * (1 ⊗ₜ[R] n) := by
            rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul,
              mul_one, one_mul]
          rw [this]
          exact J'.mul_mem_right _ (Ideal.mem_map_of_mem _ hi)
        · simp
        · intro a b _ _ ha hb; rw [add_tmul]; exact J'.add_mem ha hb
        · intro a b _ hb
          rw [smul_eq_mul, show (a * b) ⊗ₜ[R] n = (a ⊗ₜ[R] 1) * (b ⊗ₜ[R] n) by
            rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]]
          exact J'.mul_mem_left _ hb
      exact this _ hj
  let φ : (J.restrictScalars R) ⊗[R] N.obj →ₗ[R] J'.restrictScalars R :=
    LinearMap.codRestrict _ ((J.restrictScalars R).subtype.rTensor N.obj) hmemJ'
  have hφ : Function.Injective φ := fun a b h ↦ hinc (congrArg Subtype.val h)
  let eJ : (J.restrictScalars R) ≃ₗ[R] J.Cotangent :=
    LinearEquiv.ofBijective (J.toCotangent.restrictScalars R)
      ⟨inj_cot J hJ, J.toCotangent_surjective⟩
  let Φ : J.Cotangent ⊗[R] N.obj →ₗ[R] J'.Cotangent :=
    (J'.toCotangent.restrictScalars R) ∘ₗ φ ∘ₗ (LinearEquiv.rTensor N.obj eJ.symm).toLinearMap
  have key : conormalLinMap (inclL P N) (ideal_le_comap I (inclL P N)) N.obj
      (BoundedAlg.toAlgHom (inclR P N)) = Φ := by
    refine TensorProduct.ext' fun m n ↦ ?_
    obtain ⟨j, rfl⟩ := J.toCotangent_surjective m
    have hj : eJ.symm (J.toCotangent j) = j := eJ.symm_apply_eq.2 rfl
    simp only [Φ, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars]
    change (1 ⊗ₜ[R] n : P.obj ⊗[R] N.obj) • J'.toCotangent _ = J'.toCotangent _
    rw [← map_smul]
    congr 1
    apply Subtype.ext
    have hφj : (((φ ∘ₗ (LinearEquiv.rTensor N.obj eJ.symm).toLinearMap)
        (J.toCotangent j ⊗ₜ n) : J'.restrictScalars R) : P.obj ⊗[R] N.obj) =
          (j : P.obj) ⊗ₜ[R] n := by
      change ((eJ.symm (J.toCotangent j) : J.restrictScalars R) : P.obj) ⊗ₜ n = _
      rw [hj]
    refine Eq.trans ?_ hφj.symm
    change (1 ⊗ₜ[R] n) * ((j : P.obj) ⊗ₜ[R] 1) = (j : P.obj) ⊗ₜ[R] n
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  rw [key]
  refine ⟨(inj_cot J' hJ').comp (hφ.comp (LinearEquiv.rTensor N.obj eJ.symm).injective), ?_⟩
  let S : Ideal (P.obj ⊗[R] N.obj) :=
    { carrier := Set.range ((J.restrictScalars R).subtype.rTensor N.obj)
      add_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, map_add _ _ _⟩
      zero_mem' := ⟨0, map_zero _⟩
      smul_mem' := by
        rintro a _ ⟨t, rfl⟩
        induction a using TensorProduct.inductionOn with
        | add a a' ha ha' =>
          obtain ⟨u, hu⟩ := ha
          obtain ⟨u', hu'⟩ := ha'
          exact ⟨u + u', by rw [map_add, hu, hu', add_smul]⟩
        | tmul p n =>
          induction t using TensorProduct.inductionOn with
          | add t t' ht ht' =>
            obtain ⟨u, hu⟩ := ht
            obtain ⟨u', hu'⟩ := ht'
            exact ⟨u + u', by rw [map_add, hu, hu', map_add, smul_add]⟩
          | tmul j m =>
            refine ⟨(⟨p * j, J.mul_mem_left p j.2⟩ : J.restrictScalars R) ⊗ₜ (n * m), ?_⟩
            change (p * (j : P.obj)) ⊗ₜ[R] (n * m) = (p ⊗ₜ[R] n) • ((j : P.obj) ⊗ₜ[R] m)
            rw [smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul] }
  have hJ'S : J' ≤ S := by
    rw [Ideal.map_le_iff_le_comap]
    intro i hi
    exact ⟨(⟨algebraMap R P.obj i, Ideal.mem_map_of_mem _ hi⟩ : J.restrictScalars R) ⊗ₜ 1, rfl⟩
  intro y
  obtain ⟨j, rfl⟩ := J'.toCotangent_surjective y
  obtain ⟨s, hs⟩ := hJ'S j.2
  refine ⟨LinearEquiv.rTensor N.obj eJ s, ?_⟩
  have e₁ : ∀ s, (LinearEquiv.rTensor N.obj eJ.symm) (LinearEquiv.rTensor N.obj eJ s) = s :=
    (LinearEquiv.rTensor N.obj eJ).symm_apply_apply
  change J'.toCotangent (φ ((LinearEquiv.rTensor N.obj eJ.symm) (LinearEquiv.rTensor N.obj eJ s))) =
    J'.toCotangent j
  rw [e₁ s]
  congr 1
  exact Subtype.ext hs

omit [Fact (ℵ₀ < κ)] in
/-- The conormal module of `I P` is carried isomorphically along an isomorphism of algebras. -/
lemma bijective_mapCotangent_ideal {P Q : BoundedAlg R κ} (e : P.obj ≃ₐ[R] Q.obj) :
    Function.Bijective ((ideal I P).mapCotangent (ideal I Q) e.toAlgHom
      (ideal_le_comap I (BoundedAlg.ofHom e.toAlgHom))) := by
  have inv : ∀ {P Q : BoundedAlg R κ} (f : P.obj →ₐ[R] Q.obj) (f' : Q.obj →ₐ[R] P.obj)
      (h₁ : ideal I P ≤ (ideal I Q).comap f) (h₂ : ideal I Q ≤ (ideal I P).comap f'),
      (∀ x, f' (f x) = x) → ∀ y, (ideal I Q).mapCotangent (ideal I P) f' h₂
        ((ideal I P).mapCotangent (ideal I Q) f h₁ y) = y := by
    intro P Q f f' h₁ h₂ hff y
    obtain ⟨j, rfl⟩ := (ideal I P).toCotangent_surjective y
    exact congrArg _ (Subtype.ext (hff _))
  have h₂ := ideal_le_comap I (P := Q) (Q := P) (BoundedAlg.ofHom e.symm.toAlgHom)
  exact ⟨Function.LeftInverse.injective (inv e.toAlgHom e.symm.toAlgHom _ h₂ e.symm_apply_apply),
    Function.RightInverse.surjective (inv e.symm.toAlgHom e.toAlgHom h₂ _ e.apply_symm_apply)⟩

variable (I) in
/-- Base change of the conormal module of `I P`, for any algebra `Q` presented as the tensor
product `P ⊗_R N` of a flat `N` through the two maps `f : P → Q` and `g : N → Q`. -/
theorem bijective_conormalLinMap_of_tensor (hI : I ^ 2 = ⊥) {P Q N : BoundedAlg R κ}
    [Module.Flat R N.obj] (f : P ⟶ Q) (g : N.obj →ₐ[R] Q.obj)
    (e : (tens P N).obj ≃ₐ[R] Q.obj)
    (he₁ : ∀ p, e (p ⊗ₜ 1) = BoundedAlg.toAlgHom f p) (he₂ : ∀ n, e (1 ⊗ₜ n) = g n) :
    Function.Bijective (conormalLinMap f (ideal_le_comap I f) N.obj g) := by
  let m := (ideal I (tens P N)).mapCotangent (ideal I Q) e.toAlgHom
    (ideal_le_comap I (BoundedAlg.ofHom e.toAlgHom))
  let c := conormalLinMap (inclL P N) (ideal_le_comap I (inclL P N)) N.obj
    (BoundedAlg.toAlgHom (inclR P N))
  have key : conormalLinMap f (ideal_le_comap I f) N.obj g = m ∘ₗ c := by
    refine TensorProduct.ext' fun t n ↦ ?_
    obtain ⟨j, rfl⟩ := (ideal I P).toCotangent_surjective t
    rw [LinearMap.comp_apply, conormalLinMap_tmul, conormalLinMap_tmul,
      Ideal.mapCotangent_toCotangent, Ideal.mapCotangent_toCotangent]
    change (g n : Q.obj) • (ideal I Q).toCotangent _ = m (((1 : P.obj) ⊗ₜ[R] n) •
      (ideal I (tens P N)).toCotangent _)
    rw [← map_smul, ← map_smul, Ideal.mapCotangent_toCotangent]
    congr 1
    apply Subtype.ext
    change g n * BoundedAlg.toAlgHom f j = e ((1 ⊗ₜ[R] n) * ((j : P.obj) ⊗ₜ[R] 1))
    rw [map_mul, he₁, he₂]
  rw [key]
  exact (bijective_mapCotangent_ideal e).comp (bijective_conormalLinMap_tens I hI P N)

end BaseSection

end Stacks.ChartedFunctor

end
