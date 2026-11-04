module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import StacksFrontier.Homology.HomComplex.Basic

/-!
# The canonical map `Tot(K ⊗ Hom(M, L)) ⟶ Hom(M, Tot(K ⊗ L))`

Let `R` be a commutative ring and let `K`, `L`, `M` be cochain complexes of `R`-modules. The
Hom complex `Hom^•(M, L)` has `Hom^n(M, L) = ∏_{p+q=n} Hom_R(M^{-q}, L^p)` and differential
`d(f) = d_L ∘ f - (-1)^n f ∘ d_M`. There is a canonical morphism of complexes
`Θ : Tot(K ⊗_R Hom^•(M, L)) ⟶ Hom^•(M, Tot(K ⊗_R L))`, covariant in `K` and `L` and
contravariant in `M`, given on the summand `K^p ⊗ Hom^q(M, L)` by the canonical map
`c : A ⊗_R Hom_R(C, B) → Hom_R(C, A ⊗_R B)`, `c(a ⊗ φ)(x) = a ⊗ φ(x)`.

## Main definitions

* `Stacks.HomComplex.TensorHomComparison.canonicalC`: the canonical map `c(a ⊗ φ)(x) = a ⊗ φ(x)`.
* `Stacks.HomComplex.TensorHomComparison.HomCxMap`: the action of `Hom^•(-, -)` on morphisms of
  complexes.
* `Stacks.HomComplex.TensorHomComparison.theta`: the canonical morphism `Θ`.

## Main results

* `Stacks.HomComplex.TensorHomComparison.theta_apply`: `Θ` is given by `c` on each summand `K^p ⊗
  Hom^q(M, L)`.
* `Stacks.HomComplex.TensorHomComparison.theta_natural_K`,
  `Stacks.HomComplex.TensorHomComparison.theta_natural_L`,
  `Stacks.HomComplex.TensorHomComparison.theta_natural_M`: naturality of `Θ` in each of the three
    complexes.

## Implementation notes

Mathlib's `Cochain M L n` has `p`-th factor `M^p ⟶ L^{p+n}`; this is the Stacks factor
`Hom_R(M^{-s}, L^r)` with `s = -p` and `r = p + n`. The ring is commutative so that
`Hom_R(C, B)` and `A ⊗_R B` are again `R`-modules. The closed monoidal structure on
complexes is not available in Mathlib, so `Θ` is constructed explicitly from `c`.

## References

* [Stacks: Tag 0BYM](https://stacks.math.columbia.edu/tag/0BYM)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory MonoidalCategory CochainComplex CochainComplex.HomComplex

namespace Stacks.HomComplex.TensorHomComparison

variable {R : Type*} [CommRing R]

/-! ## The canonical map `c` -/

/-- The canonical `R`-linear map `c : A ⊗_R Hom_R(C, B) → Hom_R(C, A ⊗_R B)`,
`c(a ⊗ φ)(x) = a ⊗ φ(x)`. -/
noncomputable def canonicalC (A B C : Type*) [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [Module R A] [Module R B] [Module R C] :
    (TensorProduct R A (C →ₗ[R] B)) →ₗ[R] (C →ₗ[R] TensorProduct R A B) :=
  TensorProduct.lTensorHomToHomLTensor (RingHom.id R) C A B

/-- The canonical map satisfies `c(a ⊗ φ)(x) = a ⊗ φ(x)`. -/
theorem canonicalC_apply (A B C : Type*) [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [Module R A] [Module R B] [Module R C]
    (a : A) (φ : C →ₗ[R] B) (x : C) :
    canonicalC A B C (TensorProduct.tmul R a φ) x = TensorProduct.tmul R a (φ x) := by
  simp [canonicalC]

/-! ## The Hom complex `Hom^•(M, L)`

The degree-`n` term of `HomComplexR R M L` is the module of degree-`n` cochains
`Cochain M L n`, and its differential is `d(f) = d_L ∘ f - (-1)^n f ∘ d_M`. -/

/-- The degree-`n` term of `HomComplexR R M L` is the module of degree-`n` cochains, i.e.
the indexed product whose `p`-th factor is `Hom_R(M^p, L^{p+n})`.  In the Stacks
indexing `Hom^n(M, L) = ∏_{r+s=n} Hom_R(M^{-s}, L^r)`, the `p`-th Mathlib factor
`M^p ⟶ L^{p+n}` is the `(r, s) = (p+n, -p)` Stacks factor. -/
theorem HomComplexR_X (M L : CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    (HomComplexR R M L).X n = ModuleCat.of R (Cochain M L n) := rfl

/-- The component of a degree-`n` cochain at the Stacks index `(r, s)` with
`r + s = n` is the map `z.v (-s) r : M^{-s} ⟶ L^r`: the degree condition `(-s) + n = r`
holds whenever `r + s = n`. -/
theorem HomComplexR_v_stacks_index (n : ℤ)
    (r s : ℤ) (hrs : r + s = n) : (-s) + n = r := by omega

/-- The differential of the Hom complex is `d(f) = d_L ∘ f - (-1)^n f ∘ d_M`: on the
`(p, q)`-component, with `p + (n+1) = q`, it is
`f.v p (q-1) ≫ d_L + (-1)^{n+1} (d_M ≫ f.v (p+1) q)`. -/
theorem HomComplexR_d_v (M L : CochainComplex (ModuleCat R) ℤ) (n : ℤ) (z : Cochain M L n)
    (p q : ℤ) (hpq : p + (n + 1) = q) :
    (((HomComplexR R M L).d n (n + 1)).hom z).v p q hpq
      = z.v p (q - 1) (by omega) ≫ L.d (q - 1) q
        + (n + 1).negOnePow • (M.d p (p + 1) ≫ z.v (p + 1) q (by omega)) := by
  rw [HomComplexR_d_apply]
  exact δ_v n (n + 1) rfl z p q hpq (q - 1) (p + 1) (by omega) rfl

/-! ## Functoriality of the Hom complex

`Hom^•(M, L)` is contravariant in `M`, by precomposition, and covariant in `L`, by
postcomposition. -/

/-- Functorial action of the Hom complex in a single degree: contravariant in `M`
(precompose with `f`), covariant in `L` (postcompose with `g`). -/
noncomputable def HomCxMapDeg (M M' L L' : CochainComplex (ModuleCat R) ℤ)
    (f : M' ⟶ M) (g : L ⟶ L') (n : ℤ) :
    Cochain M L n →ₗ[R] Cochain M' L' n where
  toFun z := (Cochain.ofHom f).comp (z.comp (Cochain.ofHom g) (add_zero n)) (zero_add n)
  map_add' z z' := by simp only [Cochain.add_comp, Cochain.comp_add]
  map_smul' r z := by simp only [Cochain.comp_smul, Cochain.smul_comp, RingHom.id_apply]

/-- On the `(p, q)`-component, the map `Hom^n(M, L) → Hom^n(M', L')` is `g ∘ (-) ∘ f`, i.e.
`(HomCxMapDeg f g n z).v p q = f.f p ≫ z.v p q ≫ g.f q`. -/
theorem HomCxMapDeg_v (M M' L L' : CochainComplex (ModuleCat R) ℤ)
    (f : M' ⟶ M) (g : L ⟶ L') (n : ℤ) (z : Cochain M L n) (p q : ℤ) (hpq : p + n = q) :
    (HomCxMapDeg M M' L L' f g n z).v p q hpq
      = f.f p ≫ z.v p q hpq ≫ g.f q := by
  simp only [HomCxMapDeg, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Cochain.comp_v _ _ (zero_add n) p p q (by omega) hpq,
    Cochain.comp_v _ _ (add_zero n) p q q hpq (by omega),
    Cochain.ofHom_v, Cochain.ofHom_v]

/-- The degreewise action `HomCxMapDeg` commutes with the differentials of the Hom
complexes. -/
theorem HomCxMap_comm (M M' L L' : CochainComplex (ModuleCat R) ℤ)
    (f : M' ⟶ M) (g : L ⟶ L') :
    ∀ i j, (ComplexShape.up ℤ).Rel i j →
      ModuleCat.ofHom (HomCxMapDeg M M' L L' f g i) ≫ (HomComplexR R M' L').d i j
        = (HomComplexR R M L).d i j ≫ ModuleCat.ofHom (HomCxMapDeg M M' L L' f g j) := by
  rintro i j rfl
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Cochain.ext
  intro p q hpq
  change (((HomComplexR R M' L').d i (i + 1)).hom (HomCxMapDeg M M' L L' f g i z)).v p q hpq
      = (HomCxMapDeg M M' L L' f g (i + 1) (((HomComplexR R M L).d i (i + 1)).hom z)).v p q hpq
  rw [HomComplexR_d_v M' L' i (HomCxMapDeg M M' L L' f g i z) p q hpq,
    HomCxMapDeg_v M M' L L' f g (i + 1) (((HomComplexR R M L).d i (i + 1)).hom z) p q hpq,
    HomComplexR_d_v M L i z p q hpq,
    HomCxMapDeg_v M M' L L' f g i z p (q - 1) (by omega),
    HomCxMapDeg_v M M' L L' f g i z (p + 1) q (by omega)]
  rw [Preadditive.add_comp, Preadditive.comp_add]
  simp only [Category.assoc]
  rw [HomologicalComplex.Hom.comm g (q - 1) q,
    ← HomologicalComplex.Hom.comm_assoc f p (p + 1)]
  rw [Linear.units_smul_comp, Linear.comp_units_smul]
  simp only [Category.assoc]

/-- The morphism of complexes `Hom^•(M, L) ⟶ Hom^•(M', L')`, `z ↦ g ∘ z ∘ f`, induced by
`f : M' ⟶ M` and `g : L ⟶ L'`. -/
noncomputable def HomCxMap (M M' L L' : CochainComplex (ModuleCat R) ℤ)
    (f : M' ⟶ M) (g : L ⟶ L') : HomComplexR R M L ⟶ HomComplexR R M' L' :=
  HomologicalComplex.Hom.mk (fun n => ModuleCat.ofHom (HomCxMapDeg M M' L L' f g n))
    (HomCxMap_comm M M' L L' f g)

/-- `Hom^•(id, id) = id`. -/
theorem HomCxMap_id (M L : CochainComplex (ModuleCat R) ℤ) :
    HomCxMap M M L L (𝟙 M) (𝟙 L) = 𝟙 (HomComplexR R M L) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Cochain.ext
  intro p q hpq
  change (HomCxMapDeg M M L L (𝟙 M) (𝟙 L) n z).v p q hpq = _
  rw [HomCxMapDeg_v]
  simp

/-- In each degree, `Hom^•(f' ≫ f, g ≫ g') = Hom^•(f', g') ∘ Hom^•(f, g)`. -/
theorem HomCxMapDeg_comp (M M' M'' L L' L'' : CochainComplex (ModuleCat R) ℤ)
    (f : M' ⟶ M) (f' : M'' ⟶ M') (g : L ⟶ L') (g' : L' ⟶ L'') (n : ℤ) (z : Cochain M L n) :
    HomCxMapDeg M M'' L L'' (f' ≫ f) (g ≫ g') n z
      = HomCxMapDeg M' M'' L' L'' f' g' n (HomCxMapDeg M M' L L' f g n z) := by
  apply Cochain.ext; intro p q hpq
  rw [HomCxMapDeg_v, HomCxMapDeg_v, HomCxMapDeg_v]
  simp only [HomologicalComplex.comp_f, Category.assoc]

/-- `Hom^•(f' ≫ f, g ≫ g') = Hom^•(f, g) ≫ Hom^•(f', g')`. -/
theorem HomCxMap_comp (M M' M'' L L' L'' : CochainComplex (ModuleCat R) ℤ)
    (f : M' ⟶ M) (f' : M'' ⟶ M') (g : L ⟶ L') (g' : L' ⟶ L'') :
    HomCxMap M M'' L L'' (f' ≫ f) (g ≫ g')
      = HomCxMap M M' L L' f g ≫ HomCxMap M' M'' L' L'' f' g' := by
  ext n z
  exact HomCxMapDeg_comp M M' M'' L L' L'' f f' g g' n z

/-! ## The canonical map `Θ` -/

set_option backward.isDefEq.respectTransparency.types false in
/-- `Θ` on a summand `K^p ⊗ Hom^q(M, L)`, packaged as an `R`-bilinear map in
`(x, φ)` valued in degree-`(p+q)` cochains `M → Tot(K ⊗ L)`.  Its value at the
`(a, b)`-component (with `a + (p+q) = b`) sends `m : M^a` to
`ι_{p, b-p}(c(x ⊗ φ^{a, b-p})(m))`. -/
noncomputable def thetaBilin (K L M : CochainComplex (ModuleCat R) ℤ) (p q : ℤ) :
    K.X p →ₗ[R] Cochain M L q →ₗ[R] Cochain M (K ⊗ L) (p + q) :=
  LinearMap.mk₂ R
    (fun x φ => Cochain.mk (fun a b hab =>
      ModuleCat.ofHom
        (((HomologicalComplex.ιTensorObj K L p (b - p) b (by omega)).hom).comp
          (canonicalC (K.X p) (L.X (b - p)) (M.X a)
            (TensorProduct.tmul R x ((φ.v a (b - p) (by omega)).hom))))))
    (by intro x y φ; apply Cochain.ext; intro a b hab
        rw [Cochain.add_v]; rw [Cochain.mk_v, Cochain.mk_v, Cochain.mk_v]
        rw [TensorProduct.add_tmul, map_add, LinearMap.comp_add]; rfl)
    (by intro r x φ; apply Cochain.ext; intro a b hab
        rw [Cochain.smul_v]; rw [Cochain.mk_v, Cochain.mk_v]
        rw [show (r • x) ⊗ₜ[R] (φ.v a (b - p) (by omega)).hom
              = r • (x ⊗ₜ[R] (φ.v a (b - p) (by omega)).hom)
              from TensorProduct.smul_tmul' r x _,
          map_smul, LinearMap.comp_smul]; rfl)
    (by intro x φ ψ; apply Cochain.ext; intro a b hab
        rw [Cochain.add_v]; rw [Cochain.mk_v, Cochain.mk_v, Cochain.mk_v]
        rw [Cochain.add_v, ModuleCat.hom_add]
        rw [show x ⊗ₜ[R] ((φ.v a (b - p) (by omega)).hom + (ψ.v a (b - p) (by omega)).hom)
              = x ⊗ₜ[R] (φ.v a (b - p) (by omega)).hom + x ⊗ₜ[R] (ψ.v a (b - p) (by omega)).hom
              from TensorProduct.tmul_add x _ _,
          map_add, LinearMap.comp_add]; rfl)
    (by intro r x φ; apply Cochain.ext; intro a b hab
        rw [Cochain.smul_v]; rw [Cochain.mk_v, Cochain.mk_v]
        rw [Cochain.smul_v, ModuleCat.hom_smul]
        rw [show x ⊗ₜ[R] (r • (φ.v a (b - p) (by omega)).hom)
              = r • (x ⊗ₜ[R] (φ.v a (b - p) (by omega)).hom) from TensorProduct.tmul_smul r x _,
          map_smul, LinearMap.comp_smul]; rfl)

/-- The degree-`n` component of `Θ`, as a morphism in `ModuleCat R` out of the
term `Tot^n(K ⊗ Hom^•(M, L))`, given on each summand by `thetaBilin`. -/
noncomputable def thetaDeg (K L M : CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    (K ⊗ HomComplexR R M L).X n ⟶ (HomComplexR R M (K ⊗ L)).X n :=
  GradedObject.Monoidal.tensorObjDesc (X₁ := K.X) (X₂ := (HomComplexR R M L).X)
    (fun p q h =>
      ModuleCat.ofHom
        (show TensorProduct R (K.X p) (Cochain M L q) →ₗ[R] Cochain M (K ⊗ L) n from
          h ▸ TensorProduct.lift (thetaBilin K L M p q)))

/-- On the summand `K^p ⊗ Hom^q(M, L)`, `Θ` is given by the canonical map `c`: for
`a + (p+q) = b`, the `(a, b)`-component of `Θ(ι_{p,q}(x ⊗ φ))` is the map
`M^a → Tot^b(K ⊗ L)`, `m ↦ ι_{p, b-p}(c(x ⊗ φ^{a, b-p})(m))`. -/
theorem theta_apply (K L M : CochainComplex (ModuleCat R) ℤ) (n p q : ℤ) (h : p + q = n)
    (x : K.X p) (φ : Cochain M L q) (a b : ℤ) (hab : a + n = b) (m : M.X a) :
    (((thetaDeg K L M n).hom
        ((HomologicalComplex.ιTensorObj K (HomComplexR R M L) p q n h).hom
          (TensorProduct.tmul R x φ))) : Cochain M (K ⊗ L) n).v a b (by omega) m
      = (HomologicalComplex.ιTensorObj K L p (b - p) b (by omega)).hom
          (canonicalC (K.X p) (L.X (b - p)) (M.X a)
            (TensorProduct.tmul R x ((φ.v a (b - p) (by omega)).hom)) m) := by
  subst h
  have key : HomologicalComplex.ιTensorObj K (HomComplexR R M L) p q (p + q) rfl
        ≫ thetaDeg K L M (p + q)
      = ModuleCat.ofHom (TensorProduct.lift (thetaBilin K L M p q)) :=
    GradedObject.Monoidal.ι_tensorObjDesc (X₁ := K.X) (X₂ := (HomComplexR R M L).X) _ p q rfl
  have key2 : (thetaDeg K L M (p + q)).hom
        ((HomologicalComplex.ιTensorObj K (HomComplexR R M L) p q (p + q) rfl).hom
          (TensorProduct.tmul R x φ))
      = (TensorProduct.lift (thetaBilin K L M p q)) (TensorProduct.tmul R x φ) := by
    rw [← ModuleCat.hom_ofHom (TensorProduct.lift (thetaBilin K L M p q)), ← key]
    rfl
  rw [key2]
  simp only [TensorProduct.lift.tmul, thetaBilin, LinearMap.mk₂_apply, Cochain.mk_v,
    ModuleCat.hom_ofHom]
  rfl

/-- The differential of `Tot(K ⊗ L)` on the summand `K^p ⊗ L^s`, with `p + s = b`, is
`d_K ⊗ id` into `K^{p+1} ⊗ L^s` plus `(-1)^p (id ⊗ d_L)` into `K^p ⊗ L^{s+1}`. -/
theorem tensorObj_ι_d (K L : CochainComplex (ModuleCat R) ℤ) (p s b j : ℤ) (hps : p + s = b) (hbj :
    b + 1 = j) :
    HomologicalComplex.ιTensorObj K L p s b hps ≫ (K ⊗ L).d b j
      = (K.d p (p+1) ⊗ₘ 𝟙 (L.X s)) ≫ HomologicalComplex.ιTensorObj K L (p+1) s j (by omega)
        + p.negOnePow • ((𝟙 (K.X p) ⊗ₘ L.d s (s+1)) ≫ HomologicalComplex.ιTensorObj K L p (s+1) j
            (by omega)) := by
  subst hbj
  have hd : (K ⊗ L).d b (b+1)
      = HomologicalComplex.mapBifunctor.D₁ K L (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) b
          (b+1)
        + HomologicalComplex.mapBifunctor.D₂ K L (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)
            b (b+1) :=
    HomologicalComplex.mapBifunctor.d_eq K L (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) b
        (b+1)
  rw [hd, Preadditive.comp_add]
  have hD1 : HomologicalComplex.ιTensorObj K L p s b hps ≫ HomologicalComplex.mapBifunctor.D₁ K L
      (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) b (b+1)
       = HomologicalComplex.mapBifunctor.d₁ K L (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) p
           s (b+1) :=
    HomologicalComplex.mapBifunctor.ι_D₁ K L _ _ b (b+1) p s hps
  have hD2 : HomologicalComplex.ιTensorObj K L p s b hps ≫ HomologicalComplex.mapBifunctor.D₂ K L
      (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) b (b+1)
       = HomologicalComplex.mapBifunctor.d₂ K L (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) p
           s (b+1) :=
    HomologicalComplex.mapBifunctor.ι_D₂ K L _ _ b (b+1) p s hps
  rw [hD1, hD2]
  rw [HomologicalComplex.mapBifunctor.d₁_eq K L _ _ (show (ComplexShape.up ℤ).Rel p (p+1) by simp)
      s (b+1) (by change p + 1 + s = b + 1; omega),
    HomologicalComplex.mapBifunctor.d₂_eq K L _ _ p (show (ComplexShape.up ℤ).Rel s (s+1) by
        simp) (b+1) (by change p + (s+1) = b + 1; omega)]
  rw [show (ComplexShape.up ℤ).ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, s) = 1 by simp
      [ComplexShape.ε₁],
    show (ComplexShape.up ℤ).ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p,
        s) = p.negOnePow by simp [ComplexShape.ε₂]]
  rw [show ((curriedTensor (ModuleCat R)).map (K.d p (p+1))).app (L.X s) = K.d p (p+1) ⊗ₘ 𝟙 (L.X s)
      by simp [curriedTensor],
    show ((curriedTensor (ModuleCat R)).obj (K.X p)).map (L.d s (s+1)) = 𝟙 (K.X
        p) ⊗ₘ L.d s (s+1) by simp [curriedTensor]]
  simp only [one_smul]

/-- Elementwise form of `tensorObj_ι_d`. -/
private theorem tensorObj_d_ι_tmul (K L : CochainComplex (ModuleCat R) ℤ) (p s b j : ℤ)
    (hps : p + s = b) (hbj : b + 1 = j) (x : K.X p) (y : L.X s) :
    ((K ⊗ L).d b j).hom ((HomologicalComplex.ιTensorObj K L p s b hps).hom (x ⊗ₜ[R] y))
      = (HomologicalComplex.ιTensorObj K L (p + 1) s j (by omega)).hom
          ((K.d p (p + 1)).hom x ⊗ₜ[R] y)
        + p.negOnePow • (HomologicalComplex.ιTensorObj K L p (s + 1) j (by omega)).hom
            (x ⊗ₜ[R] (L.d s (s + 1)).hom y) :=
  DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (tensorObj_ι_d K L p s b j hps hbj)) (x ⊗ₜ[R] y)

/-- The maps `thetaDeg` commute with the differentials of `Tot(K ⊗ Hom^•(M, L))` and
`Hom^•(M, Tot(K ⊗ L))`. -/
theorem thetaDeg_comm (K L M : CochainComplex (ModuleCat R) ℤ) :
    ∀ i j, (ComplexShape.up ℤ).Rel i j →
      thetaDeg K L M i ≫ (HomComplexR R M (K ⊗ L)).d i j
        = (K ⊗ HomComplexR R M L).d i j ≫ thetaDeg K L M j := by
  rintro i j rfl
  apply GradedObject.Monoidal.tensorObj_ext
  intro p q hpq
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x φ
  apply Cochain.ext
  intro a b hab
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change ((((GradedObject.Monoidal.ιTensorObj K.X (HomComplexR R M L).X p q i hpq
            ≫ thetaDeg K L M i ≫ (HomComplexR R M (K ⊗ L)).d i (i + 1)).hom)
          (x ⊗ₜ[R] φ)).v a b hab).hom m
      = ((((GradedObject.Monoidal.ιTensorObj K.X (HomComplexR R M L).X p q i hpq
            ≫ (K ⊗ HomComplexR R M L).d i (i + 1) ≫ thetaDeg K L M (i + 1)).hom)
          (x ⊗ₜ[R] φ)).v a b hab).hom m
  set θval : Cochain M (K ⊗ L) i :=
    (thetaDeg K L M i).hom
      ((HomologicalComplex.ιTensorObj K (HomComplexR R M L) p q i hpq).hom (x ⊗ₜ[R] φ))
      with hθval
  have lhs1 : ((GradedObject.Monoidal.ιTensorObj K.X (HomComplexR R M L).X p q i hpq
            ≫ thetaDeg K L M i ≫ (HomComplexR R M (K ⊗ L)).d i (i + 1)).hom) (x ⊗ₜ[R] φ)
      = ((HomComplexR R M (K ⊗ L)).d i (i+1)).hom θval := by
    rw [hθval]; simp only [ModuleCat.comp_apply]; rfl
  rw [lhs1]
  rw [HomComplexR_d_v M (K ⊗ L) i θval a b hab]
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp, ModuleCat.hom_smul,
    LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply]
  have tA1 : ∀ (m' : M.X a), (θval.v a (b-1) (by omega)).hom m'
      = (HomologicalComplex.ιTensorObj K L p ((b-1) - p) (b-1) (by omega)).hom
          (canonicalC (K.X p) (L.X ((b-1) - p)) (M.X a)
            (x ⊗ₜ[R] ((φ.v a ((b-1) - p) (by omega)).hom)) m') := by
    intro m'
    rw [hθval]
    exact theta_apply K L M i p q hpq x φ a (b-1) (by omega) m'
  have tA2 : ∀ (m' : M.X (a+1)), (θval.v (a+1) b (by omega)).hom m'
      = (HomologicalComplex.ιTensorObj K L p (b - p) b (by omega)).hom
          (canonicalC (K.X p) (L.X (b - p)) (M.X (a+1))
            (x ⊗ₜ[R] ((φ.v (a+1) (b - p) (by omega)).hom)) m') := by
    intro m'
    rw [hθval]
    exact theta_apply K L M i p q hpq x φ (a+1) b (by omega) m'
  rw [tA1, tA2]
  simp only [canonicalC_apply]
  have dι1e := tensorObj_d_ι_tmul K L p (b - 1 - p) (b - 1) b (by omega) (by omega) x
    ((φ.v a (b - 1 - p) (by omega)).hom m)
  rw [dι1e]
  have dsrce := tensorObj_d_ι_tmul K (HomComplexR R M L) p q i (i + 1) hpq rfl x φ
  rw [show (GradedObject.Monoidal.ιTensorObj K.X (HomComplexR R M L).X p q i hpq)
        = HomologicalComplex.ιTensorObj K (HomComplexR R M L) p q i hpq from rfl]
  have rhsval : (thetaDeg K L M (i+1)).hom
        (((K ⊗ HomComplexR R M L).d i (i+1)).hom
          ((HomologicalComplex.ιTensorObj K (HomComplexR R M L) p q i hpq).hom (x ⊗ₜ[R] φ)))
      = (thetaDeg K L M (i+1)).hom
          ((HomologicalComplex.ιTensorObj K (HomComplexR R M L) (p+1) q (i+1) (by omega)).hom
            ((K.d p (p+1)).hom x ⊗ₜ[R] φ))
        + p.negOnePow • (thetaDeg K L M (i+1)).hom
            ((HomologicalComplex.ιTensorObj K (HomComplexR R M L) p (q+1) (i+1) (by omega)).hom
              (x ⊗ₜ[R] (((HomComplexR R M L).d q (q+1)).hom φ))) := by
    rw [dsrce, map_add, LinearMap.CompatibleSMul.map_smul]
  erw [rhsval]
  rw [Cochain.add_v]
  rw [Cochain.units_smul_v]
  simp only [ModuleCat.hom_add, ModuleCat.hom_smul, LinearMap.add_apply, LinearMap.smul_apply]
  rw [theta_apply K L M (i+1) (p+1) q (by omega) ((K.d p (p+1)).hom x) φ a b (by omega) m,
    theta_apply K L M (i+1) p (q+1) (by omega) x (((HomComplexR R M L).d q (q+1)).hom φ) a b
      (by omega) m]
  simp only [canonicalC_apply]
  rw [HomComplexR_d_v M L q φ a (b - p) (by omega)]
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp, ModuleCat.hom_smul,
    LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply]
  have hsign : (i + 1).negOnePow = p.negOnePow * (q + 1).negOnePow := by
    rw [← Int.negOnePow_add]; congr 1; omega
  rw [TensorProduct.tmul_add, TensorProduct.tmul_smul, map_add,
    LinearMap.CompatibleSMul.map_smul, smul_add, hsign, mul_smul, add_assoc]
  refine congr_arg₂ (· + ·) ?_ (congr_arg₂ (· + ·) ?_ rfl)
  · have key1 : ∀ (s t : ℤ) (hst : s = t) (hs : p + 1 + s = b) (hs2 : a + q = s)
        (ht : p + 1 + t = b) (ht2 : a + q = t),
        (HomologicalComplex.ιTensorObj K L (p + 1) s b hs).hom
            ((K.d p (p + 1)).hom x ⊗ₜ[R] ((φ.v a s hs2).hom) m)
          = (HomologicalComplex.ιTensorObj K L (p + 1) t b ht).hom
              ((K.d p (p + 1)).hom x ⊗ₜ[R] ((φ.v a t ht2).hom) m) := by
      intro s t hst hs hs2 ht ht2
      subst hst; rfl
    exact key1 (b - 1 - p) (b - (p + 1)) (by omega) (by omega) (by omega) (by omega) (by omega)
  · have key2 : ∀ (s t s' t' : ℤ) (hst : s = t) (hst' : s' = t')
        (hs : p + s' = b) (hs2 : a + q = s)
        (ht : p + t' = b) (ht2 : a + q = t),
        (HomologicalComplex.ιTensorObj K L p s' b hs).hom
            (x ⊗ₜ[R] ((L.d s s').hom ((φ.v a s hs2).hom m)))
          = (HomologicalComplex.ιTensorObj K L p t' b ht).hom
              (x ⊗ₜ[R] ((L.d t t').hom ((φ.v a t ht2).hom m))) := by
      intro s t s' t' hst hst' hs hs2 ht ht2
      subst hst; subst hst'; rfl
    exact congrArg (p.negOnePow • ·)
      (key2 (b - 1 - p) (b - p - 1) (b - 1 - p + 1) (b - p)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))

/-- **Stacks 0BYM**.
The canonical morphism of complexes `Θ : Tot(K ⊗_R Hom^•(M, L)) ⟶ Hom^•(M, Tot(K ⊗_R L))`,
given in degree `n` by `thetaDeg`. -/
@[stacks 0BYM]
noncomputable def theta (K L M : CochainComplex (ModuleCat R) ℤ) :
    (K ⊗ HomComplexR R M L) ⟶ HomComplexR R M (K ⊗ L) :=
  HomologicalComplex.Hom.mk (fun n => thetaDeg K L M n) (thetaDeg_comm K L M)

/-! ## Naturality of `Θ` -/

/-- `Hom^•(f, g)` acts on the `(a, b)`-component of a cochain by `f.f a ≫ - ≫ g.f b`. -/
private theorem HomCxMap_f_v (M M' L L' : CochainComplex (ModuleCat R) ℤ) (f : M' ⟶ M)
    (g : L ⟶ L') (n : ℤ) (z : Cochain M L n) (a b : ℤ) (hab : a + n = b) :
    ((((HomCxMap M M' L L' f g).f n).hom z).v a b hab) = f.f a ≫ z.v a b hab ≫ g.f b :=
  HomCxMapDeg_v M M' L L' f g n z a b hab

/-- Whiskering on the left by `K` acts on a summand `K^p ⊗ A^s` as `𝟙 ⊗ g^s`. -/
private theorem whiskerLeft_f_ι (K : CochainComplex (ModuleCat R) ℤ) {A B : CochainComplex
    (ModuleCat R) ℤ} (g : A ⟶ B) (n p s : ℤ) (h : p + s = n) (z : (K.X p ⊗ A.X s : ModuleCat R)) :
    (K ◁ g).f n ((HomologicalComplex.ιTensorObj K A p s n h).hom z)
      = (HomologicalComplex.ιTensorObj K B p s n h).hom ((𝟙 (K.X p) ⊗ₘ g.f s).hom z) := by
  have := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (GradedObject.Monoidal.ι_tensorHom (f := 𝟙 K.X) (g := g.f) p s n h)) z
  exact this

/-- Whiskering on the right by `A` acts on a summand `K^p ⊗ A^s` as `f^p ⊗ 𝟙`. -/
private theorem whiskerRight_f_ι {K K' : CochainComplex (ModuleCat R) ℤ} (f : K ⟶ K')
    (A : CochainComplex (ModuleCat R) ℤ) (n p s : ℤ) (h : p + s = n)
    (z : (K.X p ⊗ A.X s : ModuleCat R)) :
    (f ▷ A).f n ((HomologicalComplex.ιTensorObj K A p s n h).hom z)
      = (HomologicalComplex.ιTensorObj K' A p s n h).hom ((f.f p ⊗ₘ 𝟙 (A.X s)).hom z) := by
  have := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (GradedObject.Monoidal.ι_tensorHom (f := f.f) (g := 𝟙 A.X) p s n h)) z
  exact this

/-- **Stacks 0BYM** (naturality in `K`).
For `fK : K ⟶ K'`, `Θ ≫ Hom^•(id_M, fK ▷ L) = (fK ▷ Hom^•(M, L)) ≫ Θ`. -/
@[stacks 0BYM]
theorem theta_natural_K (K K' L M : CochainComplex (ModuleCat R) ℤ) (fK : K ⟶ K') :
    theta K L M ≫ HomCxMap M M (K ⊗ L) (K' ⊗ L) (𝟙 M) (fK ▷ L)
      = (fK ▷ HomComplexR R M L) ≫ theta K' L M := by
  apply HomologicalComplex.hom_ext
  intro n
  apply GradedObject.Monoidal.tensorObj_ext
  intro p q hpq
  simp only [HomologicalComplex.comp_f]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x φ
  apply Cochain.ext
  intro a b hab
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  erw [HomCxMap_f_v]
  simp only [HomologicalComplex.id_f, Category.id_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [show ((theta K L M).f n) = thetaDeg K L M n from rfl,
    show ((theta K' L M).f n) = thetaDeg K' L M n from rfl,
    show (GradedObject.Monoidal.ιTensorObj K.X (HomComplexR R M L).X p q n hpq)
        = HomologicalComplex.ιTensorObj K (HomComplexR R M L) p q n hpq from rfl]
  erw [theta_apply K L M n p q hpq x φ a b hab m, whiskerRight_f_ι, whiskerRight_f_ι]
  simp only [ModuleCat.MonoidalCategory.tensorHom_tmul]
  erw [theta_apply K' L M n p q hpq (fK.f p x) φ a b hab m]
  simp [canonicalC_apply]

/-- **Stacks 0BYM** (naturality in `L`).
For `gL : L ⟶ L'`, `Θ ≫ Hom^•(id_M, K ◁ gL) = (K ◁ Hom^•(id_M, gL)) ≫ Θ`. -/
@[stacks 0BYM]
theorem theta_natural_L (K L L' M : CochainComplex (ModuleCat R) ℤ) (gL : L ⟶ L') :
    theta K L M ≫ HomCxMap M M (K ⊗ L) (K ⊗ L') (𝟙 M) (K ◁ gL)
      = (K ◁ HomCxMap M M L L' (𝟙 M) gL) ≫ theta K L' M := by
  apply HomologicalComplex.hom_ext
  intro n
  apply GradedObject.Monoidal.tensorObj_ext
  intro p q hpq
  simp only [HomologicalComplex.comp_f]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x φ
  apply Cochain.ext
  intro a b hab
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  erw [HomCxMap_f_v]
  simp only [HomologicalComplex.id_f, Category.id_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [show ((theta K L M).f n) = thetaDeg K L M n from rfl,
    show ((theta K L' M).f n) = thetaDeg K L' M n from rfl,
    show (GradedObject.Monoidal.ιTensorObj K.X (HomComplexR R M L).X p q n hpq)
        = HomologicalComplex.ιTensorObj K (HomComplexR R M L) p q n hpq from rfl]
  erw [theta_apply K L M n p q hpq x φ a b hab m, whiskerLeft_f_ι, whiskerLeft_f_ι]
  simp only [ModuleCat.MonoidalCategory.tensorHom_tmul]
  erw [theta_apply K L' M n p q hpq x ((HomCxMap M M L L' (𝟙 M) gL).f q φ) a b hab m,
    HomCxMap_f_v]
  simp [canonicalC_apply]

/-- **Stacks 0BYM** (naturality in `M`).
For `hM : M' ⟶ M`, `Θ ≫ Hom^•(hM, id_{K ⊗ L}) = (K ◁ Hom^•(hM, id_L)) ≫ Θ`. -/
@[stacks 0BYM]
theorem theta_natural_M (K L M M' : CochainComplex (ModuleCat R) ℤ) (hM : M' ⟶ M) :
    theta K L M ≫ HomCxMap M M' (K ⊗ L) (K ⊗ L) hM (𝟙 (K ⊗ L))
      = (K ◁ HomCxMap M M' L L hM (𝟙 L)) ≫ theta K L M' := by
  apply HomologicalComplex.hom_ext
  intro n
  apply GradedObject.Monoidal.tensorObj_ext
  intro p q hpq
  simp only [HomologicalComplex.comp_f]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x φ
  apply Cochain.ext
  intro a b hab
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m'
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  erw [HomCxMap_f_v]
  simp only [HomologicalComplex.id_f, Category.comp_id, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [show ((theta K L M).f n) = thetaDeg K L M n from rfl,
    show ((theta K L M').f n) = thetaDeg K L M' n from rfl,
    show (GradedObject.Monoidal.ιTensorObj K.X (HomComplexR R M L).X p q n hpq)
        = HomologicalComplex.ιTensorObj K (HomComplexR R M L) p q n hpq from rfl]
  erw [theta_apply K L M n p q hpq x φ a b hab (hM.f a m'), whiskerLeft_f_ι]
  simp only [ModuleCat.MonoidalCategory.tensorHom_tmul]
  erw [theta_apply K L M' n p q hpq x ((HomCxMap M M' L L hM (𝟙 L)).f q φ) a b hab m',
    HomCxMap_f_v]
  simp [canonicalC_apply]

end Stacks.HomComplex.TensorHomComparison
