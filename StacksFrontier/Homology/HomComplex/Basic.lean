module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.Int.ConditionallyCompleteOrder

/-!
# The map `K → Hom^•(L, Tot(K ⊗_R L))`

Let `R` be a commutative ring and let `K`, `L` be cochain complexes of `R`-modules indexed by
`ℤ`. The total complex `Tot(K ⊗_R L)` is the monoidal tensor product `K ⊗ L` on
`CochainComplex (ModuleCat R) ℤ`, and the Hom complex `Hom^•(L, M)` has degree-`n` term
`Cochain L M n` with differential `δ`. This file constructs the morphism of complexes
`Φ : K ⟶ Hom^•(L, Tot(K ⊗_R L))` sending `β ∈ K^n` to the degree-`n` map whose component
`L^p → Tot^{n+p}(K ⊗ L)` is `y ↦ β ⊗ y`, and shows that it is natural in `K` and dinatural in
`L`.

## Main definitions

* `CochainComplex.HomComplexR`: the Hom complex `Hom^•(L, M)` as a complex of `R`-modules.
* `Stacks.HomComplex.TensorHomMap.postcomp`: postcomposition `Hom^•(L, M) ⟶ Hom^•(L, M')` by `h : M
  ⟶ M'`.
* `Stacks.HomComplex.TensorHomMap.precomp`: precomposition `Hom^•(L, M) ⟶ Hom^•(L', M)` by `g : L'
  ⟶ L`.
* `Stacks.HomComplex.TensorHomMap.Phiv`: the degree-`n` cochain `Φ^n(β) ∈ Hom^n(L, Tot(K ⊗_R L))`
  attached to
  `β ∈ K^n`.
* `Stacks.HomComplex.TensorHomMap.Phi`: the morphism of complexes `K ⟶ Hom^•(L, Tot(K ⊗_R L))`.

## Main results

* `Stacks.HomComplex.TensorHomMap.δ_phiv`: `δ (Φ^n β) = Φ^{n+1} (d_K β)`.
* `Stacks.HomComplex.TensorHomMap.Phi_natural_K`: `Φ` is natural in `K`.
* `Stacks.HomComplex.TensorHomMap.Phi_dinatural_L`: `Φ` is dinatural in `L`.
* `Stacks.HomComplex.TensorHomMap.Phi_natural_mixed`: the combined naturality for a pair of
  morphisms `f : K ⟶ K'` and
  `g : L ⟶ L'`.

## Implementation notes

The functor `(K, L) ↦ Hom^•(L, Tot(K ⊗ L))` is contravariant in `L` through the first slot of
the Hom complex and covariant in `L` through the tensor product, so the correct formulation is
naturality in `K` together with dinaturality in `L`.

The Hom complex and its functoriality in both variables need only a preadditive `R`-linear
category, so they are stated at that level of generality; the tensor–Hom map `Φ` itself uses
the monoidal structure of `ModuleCat R`.

The lemmas describing the restriction of the differential and of a tensor product of morphisms
to a summand `K^r ⊗ L^s` of the total complex are general facts about the monoidal structure of
`CochainComplex (ModuleCat R) ℤ`, so they live in the `CochainComplex` namespace.

## References

* [Stacks: Tag 0A62](https://stacks.math.columbia.edu/tag/0A62)
-/

@[expose] public section

-- Needed by `postcomp_id` and `precomp_id`, whose proofs must see through the
-- `LinearMap` bundled by `ModuleCat.ofHom`.
set_option backward.isDefEq.respectTransparency false

open CategoryTheory MonoidalCategory CochainComplex.HomComplex HomologicalComplex

namespace CochainComplex

variable {C : Type*} [Category C] [Preadditive C]

/-- The **Hom complex** `Hom^•(L, M)` of complexes `L`, `M` in an `R`-linear category, as a
complex of `R`-modules: its degree-`n` term is `Cochain L M n` and its differential is `δ`. -/
noncomputable def HomComplexR (R : Type*) [Ring R] [Linear R C]
    (L M : CochainComplex C ℤ) : CochainComplex (ModuleCat R) ℤ where
  X n := ModuleCat.of R (Cochain L M n)
  d n m := ModuleCat.ofHom (δ_hom R L M n m)
  shape n m h := by
    refine ModuleCat.hom_ext <| LinearMap.ext fun z => ?_
    change δ n m z = 0
    rw [δ_shape]
    simpa using h
  d_comp_d' i j k _ _ :=
    ModuleCat.hom_ext <| LinearMap.ext (δ_δ i j k)

/-- The differential of `HomComplexR R L M` is exactly the Hom-complex differential `δ`. -/
@[simp]
theorem HomComplexR_d_apply (R : Type*) [Ring R] [Linear R C]
    (L M : CochainComplex C ℤ) (n m : ℤ) (z : Cochain L M n) :
    ((HomComplexR R L M).d n m).hom z = δ n m z := rfl

section TensorObj

variable (R : Type*) [CommRing R]

/-- On the summand `K^r ⊗ L^s ⊆ Tot^{r+s}(K ⊗ L)`, the differential of the total complex is
`d_K(x) ⊗ y + (-1)^r x ⊗ d_L(y)`, with the first term in `K^{r+1} ⊗ L^s` and the second in
`K^r ⊗ L^{s+1}`. -/
@[reassoc]
theorem ιTensorObj_d (K L : CochainComplex (ModuleCat R) ℤ) (r s p p' : ℤ)
    (h : r + s = p) (hp : p + 1 = p') :
    ιTensorObj K L r s p h ≫ (K ⊗ L).d p p'
      = (K.d r (r + 1) ▷ L.X s) ≫ ιTensorObj K L (r + 1) s p' (by omega)
        + r.negOnePow • ((K.X r ◁ L.d s (s + 1)) ≫ ιTensorObj K L r (s + 1) p' (by omega)) := by
  change HomologicalComplex.ιMapBifunctor K L (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) r s
      p h ≫
      (HomologicalComplex.mapBifunctor K L (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)).d p
          p' = _
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    HomologicalComplex.mapBifunctor.d₁_eq K L _ _ (show (ComplexShape.up ℤ).Rel r (r+1) by
        simp) s p' (by simp; omega),
    HomologicalComplex.mapBifunctor.d₂_eq K L _ _ r (show (ComplexShape.up ℤ).Rel s (s+1) by
        simp) p' (by simp; omega)]
  rw [show (ComplexShape.up ℤ).ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (r, s) = 1 from
      ComplexShape.ε₁_def _ _,
    show (ComplexShape.up ℤ).ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (r, s) = r.negOnePow from
        rfl,
    one_smul]
  rfl

/-- On the summand `K^{i₁} ⊗ L^{i₂}`, the morphism `f ⊗ₘ g` of total complexes restricts to
`f^{i₁} ⊗ g^{i₂} : K^{i₁} ⊗ L^{i₂} → K'^{i₁} ⊗ L'^{i₂}`. -/
@[reassoc]
theorem ιTensorObj_tensorHom {K K' L L' : CochainComplex (ModuleCat R) ℤ}
    (f : K ⟶ K') (g : L ⟶ L') (i₁ i₂ j : ℤ) (h : i₁ + i₂ = j) :
    ιTensorObj K L i₁ i₂ j h ≫ (f ⊗ₘ g).f j
      = (f.f i₁ ⊗ₘ g.f i₂) ≫ ιTensorObj K' L' i₁ i₂ j h := by
  change HomologicalComplex.ιMapBifunctor K L (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) i₁
      i₂ j h ≫
      (HomologicalComplex.mapBifunctorMap f g (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ)).f
          j = _
  rw [HomologicalComplex.ι_mapBifunctorMap, tensorHom_def]
  simp only [Category.assoc]
  rfl

end TensorObj

end CochainComplex

namespace Stacks.HomComplex.TensorHomMap

section Functoriality

variable (R : Type*) [Ring R] {C : Type*} [Category C] [Preadditive C] [Linear R C]

/-- Postcomposition by a morphism `h : M ⟶ M'`, as a morphism of Hom complexes
`h_* : Hom^•(L, M) ⟶ Hom^•(L, M')`. -/
noncomputable def postcomp (L M M' : CochainComplex C ℤ) (h : M ⟶ M') :
    CochainComplex.HomComplexR R L M ⟶ CochainComplex.HomComplexR R L M' where
  f n := ModuleCat.ofHom
    { toFun z := z.comp (Cochain.ofHom h) (add_zero n)
      map_add' z w := Cochain.add_comp z w (Cochain.ofHom h) (add_zero n)
      map_smul' r z := Cochain.smul_comp r z (Cochain.ofHom h) (add_zero n) }
  comm' _ m _ :=
    ModuleCat.hom_ext <| LinearMap.ext fun z => δ_comp_ofHom z h m

/-- The degree-`n` component of `h_*` postcomposes a cochain with `h`. -/
@[simp] lemma postcomp_f_apply (L : CochainComplex C ℤ) {M M' : CochainComplex C ℤ} (h : M ⟶ M')
    (n : ℤ) (z : Cochain L M n) :
    ((postcomp R L M M' h).f n).hom z = z.comp (Cochain.ofHom h) (add_zero n) := rfl

/-- Two morphisms of complexes of modules are equal if they agree on every element. -/
private theorem hom_ext_apply {S : Type*} [Ring S] {A B : CochainComplex (ModuleCat S) ℤ}
    {f g : A ⟶ B} (h : ∀ n (x : A.X n), (f.f n).hom x = (g.f n).hom x) : f = g :=
  HomologicalComplex.hom_ext _ _ fun n => ModuleCat.hom_ext <| LinearMap.ext (h n)

/-- Postcomposition by the identity is the identity. -/
@[simp] lemma postcomp_id (L M : CochainComplex C ℤ) :
    postcomp R L M M (𝟙 M) = 𝟙 (CochainComplex.HomComplexR R L M) := by
  refine hom_ext_apply fun n z => ?_
  simp

/-- Postcomposition by a composite is the composite of the postcompositions. -/
@[simp] lemma postcomp_comp (L : CochainComplex C ℤ) {M M' M'' : CochainComplex C ℤ} (h : M ⟶ M')
    (h' : M' ⟶ M'') :
    postcomp R L M M'' (h ≫ h') = postcomp R L M M' h ≫ postcomp R L M' M'' h' := by
  refine hom_ext_apply fun n z => ?_
  change z.comp (Cochain.ofHom (h ≫ h')) (add_zero n)
      = (z.comp (Cochain.ofHom h) (add_zero n)).comp (Cochain.ofHom h') (add_zero n)
  rw [Cochain.ofHom_comp]
  exact (Cochain.comp_assoc z (Cochain.ofHom h) (Cochain.ofHom h') (add_zero n) (zero_add 0)
    (by omega)).symm

/-- Precomposition by a morphism `g : L' ⟶ L`, as a morphism of Hom complexes
`g^* : Hom^•(L, M) ⟶ Hom^•(L', M)`. -/
noncomputable def precomp (L' L M : CochainComplex C ℤ) (g : L' ⟶ L) :
    CochainComplex.HomComplexR R L M ⟶ CochainComplex.HomComplexR R L' M where
  f n := ModuleCat.ofHom
    { toFun z := (Cochain.ofHom g).comp z (zero_add n)
      map_add' z w := Cochain.comp_add (Cochain.ofHom g) z w (zero_add n)
      map_smul' r z := Cochain.comp_smul (Cochain.ofHom g) r z (zero_add n) }
  comm' _ m _ :=
    ModuleCat.hom_ext <| LinearMap.ext fun z => δ_ofHom_comp g z m

/-- The degree-`n` component of `g^*` precomposes a cochain with `g`. -/
@[simp] lemma precomp_f_apply {L' L : CochainComplex C ℤ} (M : CochainComplex C ℤ) (g : L' ⟶ L)
    (n : ℤ) (z : Cochain L M n) :
    ((precomp R L' L M g).f n).hom z = (Cochain.ofHom g).comp z (zero_add n) := rfl

/-- Precomposition by the identity is the identity. -/
@[simp] lemma precomp_id (L M : CochainComplex C ℤ) :
    precomp R L L M (𝟙 L) = 𝟙 (CochainComplex.HomComplexR R L M) := by
  refine hom_ext_apply fun n z => ?_
  simp

/-- Precomposition by a composite is the composite of the precompositions, in the other order. -/
@[simp] lemma precomp_comp {L'' L' L : CochainComplex C ℤ} (M : CochainComplex C ℤ) (g' : L'' ⟶ L')
    (g : L' ⟶ L) : precomp R L'' L M (g' ≫ g) = precomp R L' L M g ≫ precomp R L'' L' M g' := by
  refine hom_ext_apply fun n z => ?_
  change (Cochain.ofHom (g' ≫ g)).comp z (zero_add n)
      = (Cochain.ofHom g').comp ((Cochain.ofHom g).comp z (zero_add n)) (zero_add n)
  rw [Cochain.ofHom_comp]
  exact Cochain.comp_assoc (Cochain.ofHom g') (Cochain.ofHom g) z (zero_add 0) (zero_add n)
    (by omega)

end Functoriality

variable (R : Type*) [CommRing R]

/-- For `β` in an `R`-module `Kn`, the `R`-linear map `Lp → Kn ⊗ Lp`, `y ↦ β ⊗ y`. -/
noncomputable def tmulLeft {Kn Lp : ModuleCat R} (β : Kn) : Lp ⟶ Kn ⊗ Lp :=
  ModuleCat.ofHom (TensorProduct.mk R Kn Lp β)

/-- `tmulLeft β` sends `y` to the pure tensor `β ⊗ₜ y`. -/
@[simp] lemma tmulLeft_apply {Kn Lp : ModuleCat R} (β : Kn) (y : Lp) :
    (tmulLeft R β).hom y = β ⊗ₜ[R] y := rfl

/-- `tmulLeft` is additive in `β`. -/
@[simp] lemma tmulLeft_add {Kn Lp : ModuleCat R} (β β' : Kn) :
    tmulLeft R (β + β') = (tmulLeft R β + tmulLeft R β' : Lp ⟶ _) := by
  refine ModuleCat.hom_ext <| LinearMap.ext fun y => ?_
  simp [TensorProduct.add_tmul]

/-- `tmulLeft` is `R`-linear in `β`. -/
@[simp] lemma tmulLeft_smul {Kn Lp : ModuleCat R} (r : R) (β : Kn) :
    tmulLeft R (r • β) = (r • tmulLeft R β : Lp ⟶ _) := by
  refine ModuleCat.hom_ext <| LinearMap.ext fun y => ?_
  exact (TensorProduct.smul_tmul' r β y).symm

/-- For `φ : Kn ⟶ Kn'`, the composite `tmulLeft β ≫ (φ ▷ Lp)` equals `tmulLeft (φ β)`. -/
@[reassoc]
lemma tmulLeft_comp_whiskerRight {Kn Kn' Lp : ModuleCat R} (φ : Kn ⟶ Kn') (β : Kn) :
    tmulLeft R β ≫ (φ ▷ Lp) = tmulLeft R (φ.hom β) :=
  ModuleCat.hom_ext <| LinearMap.ext fun y => ModuleCat.MonoidalCategory.whiskerRight_apply φ Lp β y

/-- For `ψ : Lp ⟶ Lp'`, the composite `tmulLeft β ≫ (Kn ◁ ψ)` equals `ψ ≫ tmulLeft β`. -/
@[reassoc]
lemma tmulLeft_comp_whiskerLeft {Kn Lp Lp' : ModuleCat R} (ψ : Lp ⟶ Lp') (β : Kn) :
    tmulLeft R β ≫ (Kn ◁ ψ) = ψ ≫ tmulLeft R β :=
  ModuleCat.hom_ext <| LinearMap.ext fun y => ModuleCat.MonoidalCategory.whiskerLeft_apply Kn ψ β y

/-- For `φ : Kn ⟶ Kn'` and `ψ : Lp ⟶ Lp'`, the composite `tmulLeft β ≫ (φ ⊗ₘ ψ)` equals
`ψ ≫ tmulLeft (φ β)`. -/
@[reassoc]
lemma tmulLeft_comp_tensorHom {Kn Kn' Lp Lp' : ModuleCat R} (φ : Kn ⟶ Kn') (ψ : Lp ⟶ Lp') (β : Kn) :
    tmulLeft R β ≫ (φ ⊗ₘ ψ) = ψ ≫ tmulLeft R (φ.hom β) := by
  rw [tensorHom_def, ← Category.assoc, tmulLeft_comp_whiskerRight, tmulLeft_comp_whiskerLeft]

/-- The degree-`n` cochain `Φ^n(β) ∈ Hom^n(L, Tot(K ⊗ L))` associated to `β ∈ K^n`. Its
component `L^p → Tot^{n+p}(K ⊗ L)` is `y ↦ β ⊗ y`, landing in the summand `K^n ⊗ L^p`. -/
noncomputable def Phiv (K L : CochainComplex (ModuleCat R) ℤ) (n : ℤ) (β : K.X n) :
    Cochain L (K ⊗ L) n :=
  Cochain.mk (fun p q _ => tmulLeft R β ≫ ιTensorObj K L n p q (by omega))

/-- The `(p, q)` component of `Φ^n(β)` is `tmulLeft β` followed by the summand inclusion
`K^n ⊗ L^p → Tot^q(K ⊗ L)`. -/
@[simp] lemma Phiv_v (K L : CochainComplex (ModuleCat R) ℤ) (n : ℤ) (β : K.X n)
    (p q : ℤ) (hpq : p + n = q) :
    (Phiv R K L n β).v p q hpq = tmulLeft R β ≫ ιTensorObj K L n p q (by omega) := rfl

/-- The degree-`n` part of `Φ`, as an `R`-linear map `K^n → Hom^n(L, Tot(K ⊗ L))`. -/
noncomputable def PhivLin (K L : CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    K.X n →ₗ[R] Cochain L (K ⊗ L) n where
  toFun := Phiv R K L n
  map_add' β β' := by
    refine Cochain.ext _ _ fun p q hpq => ?_
    rw [Cochain.add_v, Phiv_v, Phiv_v, Phiv_v, ← Preadditive.add_comp, tmulLeft_add]
  map_smul' r β := by
    refine Cochain.ext _ _ fun p q hpq => ?_
    rw [Cochain.smul_v, Phiv_v, Phiv_v, RingHom.id_apply, ← Linear.smul_comp, tmulLeft_smul]

/-- Applying the Hom-complex differential `δ` to `Φ^n(β)` gives `Φ^{n+1}(d_K β)`. -/
theorem δ_phiv (K L : CochainComplex (ModuleCat R) ℤ) (n : ℤ) (β : K.X n) :
    δ n (n + 1) (Phiv R K L n β) = Phiv R K L (n + 1) ((K.d n (n + 1)).hom β) := by
  refine Cochain.ext _ _ fun p q hpq => ?_
  rw [δ_v n (n + 1) rfl _ p q hpq (p + n) (p + 1) (by omega) (by omega)]
  rw [Phiv_v, Phiv_v, Phiv_v]
  rw [Category.assoc, CochainComplex.ιTensorObj_d R K L n p (p + n) q (by omega) (by omega)]
  rw [Preadditive.comp_add, ← Category.assoc, tmulLeft_comp_whiskerRight,
    Linear.comp_units_smul, ← Category.assoc, tmulLeft_comp_whiskerLeft, Category.assoc,
    Int.negOnePow_succ, Units.neg_smul]
  abel

/-- **Stacks 0A62**.
The morphism of complexes of `R`-modules `Φ_{K,L} : K ⟶ Hom^•(L, Tot(K ⊗_R L))` whose degree-`n`
component sends `β ∈ K^n` to the cochain `y ↦ β ⊗ y`. -/
@[stacks 0A62]
noncomputable def Phi (K L : CochainComplex (ModuleCat R) ℤ) :
    K ⟶ CochainComplex.HomComplexR R L (K ⊗ L) where
  f n := ModuleCat.ofHom (PhivLin R K L n)
  comm' n m hnm := by
    obtain rfl : m = n + 1 := by simpa using hnm.symm
    exact ModuleCat.hom_ext <| LinearMap.ext fun β => δ_phiv R K L n β

/-- The degree-`n` component of `Φ` sends `β` to `Φ^n(β)`. -/
@[simp] lemma Phi_f_apply (K L : CochainComplex (ModuleCat R) ℤ) (n : ℤ) (β : K.X n) :
    ((Phi R K L).f n).hom β = Phiv R K L n β := rfl

/-- **Stacks 0A62**.
For `f : K ⟶ K'` and `g : L ⟶ L'`, postcomposing `Φ_{K,L}` with `Tot(f ⊗ g) = f ⊗ₘ g` equals
`f ≫ Φ_{K',L'}` followed by precomposition with `g`; both send `β` and `y` to `f(β) ⊗ g(y)`. -/
@[stacks 0A62]
theorem Phi_natural_mixed (K K' L L' : CochainComplex (ModuleCat R) ℤ) (f : K ⟶ K') (g : L ⟶ L') :
    Phi R K L ≫ postcomp R L (K ⊗ L) (K' ⊗ L') (f ⊗ₘ g) =
      f ≫ Phi R K' L' ≫ precomp R L L' (K' ⊗ L') g := by
  refine hom_ext_apply fun n β => ?_
  change (Phiv R K L n β).comp (Cochain.ofHom (f ⊗ₘ g)) (add_zero n)
      = (Cochain.ofHom g).comp (Phiv R K' L' n (f.f n β)) (zero_add n)
  refine Cochain.ext _ _ fun p q hpq => ?_
  rw [Cochain.comp_v _ _ (add_zero n) p q q hpq (by omega),
      Cochain.comp_v _ _ (zero_add n) p p q (by omega) hpq,
      Cochain.ofHom_v, Cochain.ofHom_v, Phiv_v, Phiv_v, Category.assoc,
      CochainComplex.ιTensorObj_tensorHom, ← Category.assoc, tmulLeft_comp_tensorHom,
      Category.assoc]

attribute [reassoc] Phi_natural_mixed

/-- For a morphism of complexes `f : K ⟶ K'`, postcomposing `Φ_{K,L}` with
`Tot(f ⊗ id_L) = f ▷ L` equals `f ≫ Φ_{K',L}`. -/
@[reassoc]
theorem Phi_natural_K {K K' : CochainComplex (ModuleCat R) ℤ}
    (L : CochainComplex (ModuleCat R) ℤ) (f : K ⟶ K') :
    Phi R K L ≫ postcomp R L (K ⊗ L) (K' ⊗ L) (f ▷ L) = f ≫ Phi R K' L := by
  rw [← tensorHom_id f L, Phi_natural_mixed, precomp_id, Category.comp_id]

/-- For a morphism of complexes `g : L ⟶ L'`, postcomposing `Φ_{K,L}` with
`Tot(id_K ⊗ g) = K ◁ g` equals precomposing `Φ_{K,L'}` with `g`. -/
@[reassoc]
theorem Phi_dinatural_L (K : CochainComplex (ModuleCat R) ℤ)
    {L L' : CochainComplex (ModuleCat R) ℤ} (g : L ⟶ L') :
    Phi R K L ≫ postcomp R L (K ⊗ L) (K ⊗ L') (K ◁ g) = Phi R K L' ≫ precomp R L L' (K ⊗ L') g := by
  rw [← id_tensorHom K g, Phi_natural_mixed, Category.id_comp]


@[deprecated (since := "2026-09-27")]
alias phi := Phi

@[deprecated (since := "2026-09-27")]
alias phi_dinatural_L := Phi_dinatural_L

@[deprecated (since := "2026-09-27")]
alias phi_f_apply := Phi_f_apply

@[deprecated (since := "2026-09-27")]
alias phi_natural_K := Phi_natural_K

@[deprecated (since := "2026-09-27")]
alias phi_natural_mixed := Phi_natural_mixed

@[deprecated (since := "2026-09-27")]
alias phiv := Phiv

@[deprecated (since := "2026-09-27")]
alias phivLin := PhivLin

@[deprecated (since := "2026-09-27")]
alias phiv_v := Phiv_v

end Stacks.HomComplex.TensorHomMap
