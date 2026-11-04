module

public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Tactic.Abel
public import StacksCore.Tactic.StacksAttribute

/-!
# Cup products on total complexes and the boundary maps of two short exact sequences

Let `Φ : A ⥤ B ⥤ D` be a bifunctor between preadditive categories, let `F₁ ⟶ F₂ ⟶ F₃` be
cochain complexes of `A` and `G₃ ⟶ G₂ ⟶ G₁` cochain complexes of `B`, let `H` be a cochain
complex of `D`, and let `γᵢ : Tot(Φ(Fᵢ, Gᵢ)) ⟶ H` be morphisms of complexes making the two
squares

```
Tot(Φ(F₁, G₂)) ⟶ Tot(Φ(F₁, G₁))        Tot(Φ(F₂, G₃)) ⟶ Tot(Φ(F₃, G₃))
      ↓                   ↓ γ₁                ↓                   ↓ γ₃
Tot(Φ(F₂, G₂)) ⟶       H                Tot(Φ(F₂, G₂)) ⟶       H
          γ₂                                      γ₂
```

commute. If `α₂` is a degree `n` cochain of `F₂` lifting `α₃`, and `α₁` is a degree `n + 1`
cochain of `F₁` with image `d(α₂)`, and symmetrically `β₂` is a degree `m` cochain of `G₂`
with image `β₁` and `β₃` is a degree `m + 1` cochain of `G₃` with image `d(β₂)`, then

`γ₁(α₁ ∪ β₁) = (-1)^{n+1} γ₃(α₃ ∪ β₃) + d(γ₂(α₂ ∪ β₂))`.

The sign `(-1)^{n+1}` is produced by the Koszul sign in the differential of the total complex:
the two terms of `d(γ₂(α₂ ∪ β₂))` are `γ₁(α₁ ∪ β₁)` and `(-1)^n γ₃(α₃ ∪ β₃)`.

## Main definitions

* `Stacks.CupProduct.cupPair`: the cup product of a `P`-valued degree `p` cochain of `K` with a
  `Q`-valued degree `q` cochain of `L`, a morphism `Φ(P, Q) ⟶ Tot(Φ(K, L))^{p + q}`.

## Main results

* `Stacks.CupProduct.cupPair_comp_d`: the graded Leibniz rule
  `d(α ∪ β) = d(α) ∪ β + (-1)^p α ∪ d(β)`.
* `Stacks.CupProduct.cupPair_comp_d_eq_zero` and
  `Stacks.CupProduct.cupPair_comp_gamma_comp_d_eq_zero`: the cup product of two cocycles is a
  cocycle, before and after `γ`.
* `Stacks.CupProduct.comp_d_eq_zero_of_comp_eq_comp_d`: a cochain whose image is `d(α₂)` is a
  cocycle when the inclusion is degreewise a monomorphism, which is what makes the
  representative `α₁` of `∂a₃` a cocycle.
* `Stacks.CupProduct.cupPair_comp_gamma₂_comp_d`: the computation of the source,
  `d(γ₂(α₂ ∪ β₂)) = γ₁(α₁ ∪ β₁) + (-1)^n γ₃(α₃ ∪ β₃)`.
* `Stacks.CupProduct.gamma_cup_boundary`: the same identity written with the sign of Tag 07MC,
  `γ₁(α₁ ∪ β₁) = (-1)^{n+1} γ₃(α₃ ∪ β₃) + d(γ₂(α₂ ∪ β₂))`.
* `Stacks.CupProduct.gamma_cup_boundary_homologyClass`: the same identity for cohomology
  classes, `[γ₁(α₁ ∪ β₁)] = (-1)^{n+1} [γ₃(α₃ ∪ β₃)]` in `H^{n+m+1}(H)`, the coboundary
  `d(γ₂(α₂ ∪ β₂))` dying under `H.homologyπ`.

## Implementation notes

A cochain is taken to be a morphism out of a fixed object, so that nothing is assumed about the
categories beyond preadditivity of the target: a `P`-valued degree `p` cochain of `K` is a
morphism `P ⟶ K^p`, and for modules over a ring, with `P` and `Q` the ring itself, these are the
cochains in the usual sense. The cup product of two such cochains is their image under `Φ`
followed by the inclusion of the summand of bidegree `(p, q)` in the total complex, so the
Leibniz rule is forced by the Koszul sign `ε₂` of `ComplexShape.up ℤ`.

The two commutative squares are the hypotheses of the statement, as in the source, and the
boundary maps appear through cochain lifts: `α₁` is a cochain of `F₁` whose image is `d(α₂)`,
which is how the source produces a representative of `∂a₃`.

The short exact sequences themselves are not assumed: only the morphisms `F₁ ⟶ F₂ ⟶ F₃` and
`G₃ ⟶ G₂ ⟶ G₁` and the two cochain lifts are used.  With no exactness between the three
morphisms there need be no cochain of `F₁` over `d(α₂)`, so the lifts are data here; when the
two sequences are short exact and the test objects are projective they exist, by
`Stacks.CupProduct.exists_comp_g_f` and `Stacks.CupProduct.exists_comp_f_f`.

In [Stacks, Tag 07MC] the complexes are the total Čech complexes `Tot(Č(𝒰, Fᵢ))` and
`Tot(Č(𝒰, Gᵢ))` of an open covering, `Φ` is the tensor product, and the pairings are the signed
Alexander--Whitney map of Tag 07MB followed by the pairings `γᵢ`; the statement on `X` is
`Stacks.Cech.Hypercohomology.cup_boundary`, whose proof applies
`gamma_cup_boundary_homologyClass` on a common refinement of two coverings.

The snake-lemma identification of `α₁` and `β₃` as representatives of `∂a₃` and `∂b₁` is in
`StacksFrontier.Algebra.Homology.CupProductBoundaryDelta`
(`Stacks.CupProduct.liftCycles_homologyπ_eq_δ`), and the forms of the identity for classes and for
arbitrary representatives are in `StacksFrontier.Algebra.Homology.CupProductBoundaryClass`.

## References

* [Stacks Project, Tag 07MC](https://stacks.math.columbia.edu/tag/07MC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape

universe v₁ v₂ v u₁ u₂ u

namespace Stacks.CupProduct

variable {A : Type u₁} {B : Type u₂} {D : Type u}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v} D]
  [HasZeroMorphisms A] [HasZeroMorphisms B] [Preadditive D]
  (Φ : A ⥤ B ⥤ D) [Φ.PreservesZeroMorphisms] [∀ X, (Φ.obj X).PreservesZeroMorphisms]

/-- The cup product of a `P`-valued degree `p` cochain `α` of `K` and a `Q`-valued degree `q`
cochain `β` of `L`: apply `Φ` to the two cochains and include the summand of bidegree `(p, q)`
in the total complex of `Φ(K, L)`. -/
noncomputable def cupPair {P : A} {Q : B} (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    [HomologicalComplex.HasMapBifunctor K L Φ (up ℤ)] (p q t : ℤ) (ht : p + q = t)
    (α : P ⟶ K.X p) (β : Q ⟶ L.X q) :
    (Φ.obj P).obj Q ⟶ (HomologicalComplex.mapBifunctor K L Φ (up ℤ)).X t :=
  (Φ.map α).app Q ≫ (Φ.obj (K.X p)).map β ≫
    HomologicalComplex.ιMapBifunctor K L Φ (up ℤ) p q t ht

private lemma pi_up (p q : ℤ) : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (p, q) = p + q := rfl

private lemma eps₁_up (p q : ℤ) : ComplexShape.ε₁ (up ℤ) (up ℤ) (up ℤ) (p, q) = 1 := rfl

private lemma eps₂_up (p q : ℤ) :
    ComplexShape.ε₂ (up ℤ) (up ℤ) (up ℤ) (p, q) = p.negOnePow := rfl

/-- The graded Leibniz rule `d(α ∪ β) = d(α) ∪ β + (-1)^p α ∪ d(β)` for the cup product on the
total complex. -/
theorem cupPair_comp_d {P : A} {Q : B} (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    [HomologicalComplex.HasMapBifunctor K L Φ (up ℤ)] (p q t : ℤ) (ht : p + q = t)
    (α : P ⟶ K.X p) (β : Q ⟶ L.X q) :
    cupPair Φ K L p q t ht α β ≫
        (HomologicalComplex.mapBifunctor K L Φ (up ℤ)).d t (t + 1) =
      cupPair Φ K L (p + 1) q (t + 1) (by omega) (α ≫ K.d p (p + 1)) β +
        (p.negOnePow : ℤ) • cupPair Φ K L p (q + 1) (t + 1) (by omega) α (β ≫ L.d q (q + 1)) := by
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add]
  congr 1
  · rw [cupPair, cupPair, Category.assoc, Category.assoc,
      HomologicalComplex.mapBifunctor.ι_D₁,
      HomologicalComplex.mapBifunctor.d₁_eq K L Φ (up ℤ) (i₁' := p + 1) rfl q (t + 1)
        (by rw [pi_up]; omega), eps₁_up]
    simp only [one_smul, Functor.map_comp, NatTrans.comp_app, Category.assoc]
    rw [← Category.assoc ((Φ.obj (K.X p)).map β), (Φ.map (K.d p (p + 1))).naturality β]
    simp [Category.assoc]
  · rw [cupPair, cupPair, Category.assoc, Category.assoc,
      HomologicalComplex.mapBifunctor.ι_D₂,
      HomologicalComplex.mapBifunctor.d₂_eq K L Φ (up ℤ) p (i₂' := q + 1) rfl (t + 1)
        (by rw [pi_up]; omega), eps₂_up]
    simp only [Functor.map_comp, Category.assoc, Preadditive.comp_zsmul, Units.smul_def]

/-- The cup product is natural in both complexes at once. -/
private theorem cupPair_comp_mapBifunctorMap {P : A} {Q : B} {K K' : CochainComplex A ℤ}
    {L L' : CochainComplex B ℤ} [HomologicalComplex.HasMapBifunctor K L Φ (up ℤ)]
    [HomologicalComplex.HasMapBifunctor K' L' Φ (up ℤ)] (f : K ⟶ K') (g : L ⟶ L')
    (p q t : ℤ) (ht : p + q = t) (α : P ⟶ K.X p) (β : Q ⟶ L.X q) :
    cupPair Φ K L p q t ht α β ≫ (HomologicalComplex.mapBifunctorMap f g Φ (up ℤ)).f t =
      cupPair Φ K' L' p q t ht (α ≫ f.f p) (β ≫ g.f q) := by
  rw [cupPair, cupPair, Category.assoc, Category.assoc, HomologicalComplex.ι_mapBifunctorMap]
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rw [← Category.assoc ((Φ.obj (K.X p)).map β), (Φ.map (f.f p)).naturality β]
  simp [Category.assoc]

/-- The cup product is natural in the first complex: pushing a cochain of `K` forward along
`f : K ⟶ K'` and then cupping agrees with cupping and then applying `Tot(Φ(f, 1))`. -/
theorem cupPair_comp_mapBifunctorMap_left {P : A} {Q : B} {K K' : CochainComplex A ℤ}
    (L : CochainComplex B ℤ) [HomologicalComplex.HasMapBifunctor K L Φ (up ℤ)]
    [HomologicalComplex.HasMapBifunctor K' L Φ (up ℤ)] (f : K ⟶ K') (p q t : ℤ) (ht : p + q = t)
    (α : P ⟶ K.X p) (β : Q ⟶ L.X q) :
    cupPair Φ K L p q t ht α β ≫
        (HomologicalComplex.mapBifunctorMap f (𝟙 L) Φ (up ℤ)).f t =
      cupPair Φ K' L p q t ht (α ≫ f.f p) β := by
  simp [cupPair_comp_mapBifunctorMap]

/-- The cup product is natural in the second complex: pushing a cochain of `L` forward along
`g : L ⟶ L'` and then cupping agrees with cupping and then applying `Tot(Φ(1, g))`. -/
theorem cupPair_comp_mapBifunctorMap_right {P : A} {Q : B} (K : CochainComplex A ℤ)
    {L L' : CochainComplex B ℤ} [HomologicalComplex.HasMapBifunctor K L Φ (up ℤ)]
    [HomologicalComplex.HasMapBifunctor K L' Φ (up ℤ)] (g : L ⟶ L') (p q t : ℤ) (ht : p + q = t)
    (α : P ⟶ K.X p) (β : Q ⟶ L.X q) :
    cupPair Φ K L p q t ht α β ≫
        (HomologicalComplex.mapBifunctorMap (𝟙 K) g Φ (up ℤ)).f t =
      cupPair Φ K L' p q t ht α (β ≫ g.f q) := by
  simp [cupPair_comp_mapBifunctorMap]

/-! ### Cocycles -/

/-- The cup product of the zero cochain with any cochain is zero. -/
@[simp]
lemma cupPair_zero_left {P : A} {Q : B} (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    [HomologicalComplex.HasMapBifunctor K L Φ (up ℤ)] (p q t : ℤ) (ht : p + q = t)
    (β : Q ⟶ L.X q) : cupPair Φ K L p q t ht (0 : P ⟶ K.X p) β = 0 := by
  rw [cupPair, Φ.map_zero, Limits.zero_app, zero_comp]

/-- The cup product of any cochain with the zero cochain is zero. -/
@[simp]
lemma cupPair_zero_right {P : A} {Q : B} (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    [HomologicalComplex.HasMapBifunctor K L Φ (up ℤ)] (p q t : ℤ) (ht : p + q = t)
    (α : P ⟶ K.X p) : cupPair Φ K L p q t ht α (0 : Q ⟶ L.X q) = 0 := by
  rw [cupPair, (Φ.obj (K.X p)).map_zero, zero_comp, comp_zero]

/-- The cup product of two cocycles is a cocycle: by the Leibniz rule
`cupPair_comp_d` both terms of `d(α ∪ β)` vanish. -/
theorem cupPair_comp_d_eq_zero {P : A} {Q : B} (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    [HomologicalComplex.HasMapBifunctor K L Φ (up ℤ)] (p q t : ℤ) (ht : p + q = t)
    (α : P ⟶ K.X p) (β : Q ⟶ L.X q) (hα : α ≫ K.d p (p + 1) = 0)
    (hβ : β ≫ L.d q (q + 1) = 0) :
    cupPair Φ K L p q t ht α β ≫
      (HomologicalComplex.mapBifunctor K L Φ (up ℤ)).d t (t + 1) = 0 := by
  rw [cupPair_comp_d, hα, hβ, cupPair_zero_left, cupPair_zero_right, smul_zero, add_zero]

/-- The cup product of two cocycles, pushed along a map of complexes `γ` out of the total
complex, is a cocycle of the target. -/
theorem cupPair_comp_gamma_comp_d_eq_zero {P : A} {Q : B} (K : CochainComplex A ℤ)
    (L : CochainComplex B ℤ) [HomologicalComplex.HasMapBifunctor K L Φ (up ℤ)]
    {H : CochainComplex D ℤ} (γ : HomologicalComplex.mapBifunctor K L Φ (up ℤ) ⟶ H)
    (p q t : ℤ) (ht : p + q = t) (α : P ⟶ K.X p) (β : Q ⟶ L.X q)
    (hα : α ≫ K.d p (p + 1) = 0) (hβ : β ≫ L.d q (q + 1) = 0) :
    (cupPair Φ K L p q t ht α β ≫ γ.f t) ≫ H.d t (t + 1) = 0 := by
  rw [Category.assoc, γ.comm, ← Category.assoc,
    cupPair_comp_d_eq_zero Φ K L p q t ht α β hα hβ, zero_comp]

/-- A cochain `α₁` of `K` whose image in `L` is `d(α₂)` is automatically a cocycle, provided
`u : K ⟶ L` is a monomorphism in the relevant degree: `u(d α₁) = d(d α₂) = 0`.  In the source
`F₁^p` is a subsheaf of `F₂^p`, so this is what makes the representative of `∂a₃` a cocycle. -/
theorem comp_d_eq_zero_of_comp_eq_comp_d {K L : CochainComplex A ℤ} (u : K ⟶ L) {P : A} (n : ℤ)
    (α₂ : P ⟶ L.X n) (α₁ : P ⟶ K.X (n + 1)) (hα : α₁ ≫ u.f (n + 1) = α₂ ≫ L.d n (n + 1))
    [Mono (u.f (n + 1 + 1))] : α₁ ≫ K.d (n + 1) (n + 1 + 1) = 0 := by
  refine zero_of_comp_mono (u.f (n + 1 + 1)) ?_
  rw [Category.assoc, ← u.comm, ← Category.assoc, hα, Category.assoc,
    HomologicalComplex.d_comp_d, comp_zero]

section

variable {F₁ F₂ F₃ : CochainComplex A ℤ} {G₁ G₂ G₃ : CochainComplex B ℤ}
  {H : CochainComplex D ℤ}
  [HomologicalComplex.HasMapBifunctor F₁ G₁ Φ (up ℤ)]
  [HomologicalComplex.HasMapBifunctor F₁ G₂ Φ (up ℤ)]
  [HomologicalComplex.HasMapBifunctor F₂ G₂ Φ (up ℤ)]
  [HomologicalComplex.HasMapBifunctor F₂ G₃ Φ (up ℤ)]
  [HomologicalComplex.HasMapBifunctor F₃ G₃ Φ (up ℤ)]

/-- The computation in the proof of the source: the differential of `γ₂(α₂ ∪ β₂)` splits as
`γ₁(α₁ ∪ β₁) + (-1)^n γ₃(α₃ ∪ β₃)`, where `β₁` and `α₃` are the images of `β₂` and `α₂` and
where `α₁` and `β₃` are cochains lifting `d(α₂)` and `d(β₂)`. -/
theorem cupPair_comp_gamma₂_comp_d {P : A} {Q : B} (u : F₁ ⟶ F₂) (v : F₂ ⟶ F₃) (k : G₃ ⟶ G₂)
    (l : G₂ ⟶ G₁)
    (γ₁ : HomologicalComplex.mapBifunctor F₁ G₁ Φ (up ℤ) ⟶ H)
    (γ₂ : HomologicalComplex.mapBifunctor F₂ G₂ Φ (up ℤ) ⟶ H)
    (γ₃ : HomologicalComplex.mapBifunctor F₃ G₃ Φ (up ℤ) ⟶ H)
    (h₁ : HomologicalComplex.mapBifunctorMap (𝟙 F₁) l Φ (up ℤ) ≫ γ₁ =
      HomologicalComplex.mapBifunctorMap u (𝟙 G₂) Φ (up ℤ) ≫ γ₂)
    (h₂ : HomologicalComplex.mapBifunctorMap (𝟙 F₂) k Φ (up ℤ) ≫ γ₂ =
      HomologicalComplex.mapBifunctorMap v (𝟙 G₃) Φ (up ℤ) ≫ γ₃)
    (n m : ℤ) (α₂ : P ⟶ F₂.X n) (β₂ : Q ⟶ G₂.X m) (α₁ : P ⟶ F₁.X (n + 1))
    (hα : α₁ ≫ u.f (n + 1) = α₂ ≫ F₂.d n (n + 1)) (β₃ : Q ⟶ G₃.X (m + 1))
    (hβ : β₃ ≫ k.f (m + 1) = β₂ ≫ G₂.d m (m + 1)) :
    cupPair Φ F₂ G₂ n m (n + m) rfl α₂ β₂ ≫ γ₂.f (n + m) ≫ H.d (n + m) (n + m + 1) =
      cupPair Φ F₁ G₁ (n + 1) m (n + m + 1) (by omega) α₁ (β₂ ≫ l.f m) ≫ γ₁.f (n + m + 1) +
        (n.negOnePow : ℤ) • (cupPair Φ F₃ G₃ n (m + 1) (n + m + 1) (by omega) (α₂ ≫ v.f n) β₃ ≫
          γ₃.f (n + m + 1)) := by
  rw [γ₂.comm (n + m) (n + m + 1), ← Category.assoc, cupPair_comp_d,
    Preadditive.add_comp, Preadditive.zsmul_comp]
  congr 1
  · rw [← hα, ← cupPair_comp_mapBifunctorMap_left Φ G₂ u (n + 1) m (n + m + 1) (by omega) α₁ β₂,
      Category.assoc, ← HomologicalComplex.comp_f, ← h₁, HomologicalComplex.comp_f,
      ← Category.assoc,
      cupPair_comp_mapBifunctorMap_right Φ F₁ l (n + 1) m (n + m + 1) (by omega) α₁ β₂]
  · rw [← hβ,
      ← cupPair_comp_mapBifunctorMap_right Φ F₂ k n (m + 1) (n + m + 1) (by omega) α₂ β₃,
      Category.assoc, ← HomologicalComplex.comp_f, h₂, HomologicalComplex.comp_f,
      ← Category.assoc,
      cupPair_comp_mapBifunctorMap_left Φ G₃ v n (m + 1) (n + m + 1) (by omega) α₂ β₃]

/-- The displayed computation of the source's **proof** of Tag 07MC, at the level of cochains.
In the situation of the source — two morphisms `F₁ ⟶ F₂ ⟶ F₃` and `G₃ ⟶ G₂ ⟶ G₁` of cochain
complexes and pairings `γᵢ : Tot(Φ(Fᵢ, Gᵢ)) ⟶ H` compatible with them — let `α₂`, `β₂` be
cochains of degree `n`, `m` with images `α₃`, `β₁`, and let `α₁`, `β₃` be cochains of degree
`n + 1`, `m + 1` with images `d(α₂)`, `d(β₂)`, so that `α₁` and `β₃` represent `∂a₃` and `∂b₁`.
Then

`γ₁(α₁ ∪ β₁) = (-1)^{n+1} γ₃(α₃ ∪ β₃) + d(γ₂(α₂ ∪ β₂))`.

The corresponding identity of cohomology classes is
`Stacks.CupProduct.gamma_cup_boundary_homologyClass` below. -/
theorem gamma_cup_boundary {P : A} {Q : B} (u : F₁ ⟶ F₂) (v : F₂ ⟶ F₃) (k : G₃ ⟶ G₂)
    (l : G₂ ⟶ G₁)
    (γ₁ : HomologicalComplex.mapBifunctor F₁ G₁ Φ (up ℤ) ⟶ H)
    (γ₂ : HomologicalComplex.mapBifunctor F₂ G₂ Φ (up ℤ) ⟶ H)
    (γ₃ : HomologicalComplex.mapBifunctor F₃ G₃ Φ (up ℤ) ⟶ H)
    (h₁ : HomologicalComplex.mapBifunctorMap (𝟙 F₁) l Φ (up ℤ) ≫ γ₁ =
      HomologicalComplex.mapBifunctorMap u (𝟙 G₂) Φ (up ℤ) ≫ γ₂)
    (h₂ : HomologicalComplex.mapBifunctorMap (𝟙 F₂) k Φ (up ℤ) ≫ γ₂ =
      HomologicalComplex.mapBifunctorMap v (𝟙 G₃) Φ (up ℤ) ≫ γ₃)
    (n m : ℤ) (α₂ : P ⟶ F₂.X n) (β₂ : Q ⟶ G₂.X m) (α₁ : P ⟶ F₁.X (n + 1))
    (hα : α₁ ≫ u.f (n + 1) = α₂ ≫ F₂.d n (n + 1)) (β₃ : Q ⟶ G₃.X (m + 1))
    (hβ : β₃ ≫ k.f (m + 1) = β₂ ≫ G₂.d m (m + 1)) :
    cupPair Φ F₁ G₁ (n + 1) m (n + m + 1) (by omega) α₁ (β₂ ≫ l.f m) ≫ γ₁.f (n + m + 1) =
      ((n + 1).negOnePow : ℤ) • (cupPair Φ F₃ G₃ n (m + 1) (n + m + 1) (by omega) (α₂ ≫ v.f n) β₃ ≫
          γ₃.f (n + m + 1)) +
        (cupPair Φ F₂ G₂ n m (n + m) rfl α₂ β₂ ≫ γ₂.f (n + m)) ≫ H.d (n + m) (n + m + 1) := by
  rw [Category.assoc, cupPair_comp_gamma₂_comp_d Φ u v k l γ₁ γ₂ γ₃ h₁ h₂ n m α₂ β₂ α₁ hα β₃ hβ,
    Int.negOnePow_succ]
  simp only [Units.val_neg, neg_smul]
  abel

/-- **The cup product and the boundary maps, for cohomology classes of complexes.**  In the
situation above the two cocycles `γ₁(α₁ ∪ β₁)` and `γ₃(α₃ ∪ β₃)` of `H` differ, up to the sign
`(-1)^{n+1}`, by the coboundary of `γ₂(α₂ ∪ β₂)`, so their classes in `H^{n+m+1}(H)` satisfy

`[γ₁(α₁ ∪ β₁)] = (-1)^{n+1} [γ₃(α₃ ∪ β₃)]`.

The classes are taken in `Hom(Φ(P, Q), H^{n+m+1}(H))`. -/
theorem gamma_cup_boundary_homologyClass {P : A} {Q : B} (u : F₁ ⟶ F₂) (v : F₂ ⟶ F₃)
    (k : G₃ ⟶ G₂) (l : G₂ ⟶ G₁)
    (γ₁ : HomologicalComplex.mapBifunctor F₁ G₁ Φ (up ℤ) ⟶ H)
    (γ₂ : HomologicalComplex.mapBifunctor F₂ G₂ Φ (up ℤ) ⟶ H)
    (γ₃ : HomologicalComplex.mapBifunctor F₃ G₃ Φ (up ℤ) ⟶ H)
    (h₁ : HomologicalComplex.mapBifunctorMap (𝟙 F₁) l Φ (up ℤ) ≫ γ₁ =
      HomologicalComplex.mapBifunctorMap u (𝟙 G₂) Φ (up ℤ) ≫ γ₂)
    (h₂ : HomologicalComplex.mapBifunctorMap (𝟙 F₂) k Φ (up ℤ) ≫ γ₂ =
      HomologicalComplex.mapBifunctorMap v (𝟙 G₃) Φ (up ℤ) ≫ γ₃)
    (n m : ℤ) (α₂ : P ⟶ F₂.X n) (β₂ : Q ⟶ G₂.X m) (α₁ : P ⟶ F₁.X (n + 1))
    (hα : α₁ ≫ u.f (n + 1) = α₂ ≫ F₂.d n (n + 1)) (β₃ : Q ⟶ G₃.X (m + 1))
    (hβ : β₃ ≫ k.f (m + 1) = β₂ ≫ G₂.d m (m + 1)) [H.HasHomology (n + m + 1)]
    (hc₁ : (cupPair Φ F₁ G₁ (n + 1) m (n + m + 1) (by omega) α₁ (β₂ ≫ l.f m) ≫
      γ₁.f (n + m + 1)) ≫ H.d (n + m + 1) (n + m + 1 + 1) = 0)
    (hc₃ : (cupPair Φ F₃ G₃ n (m + 1) (n + m + 1) (by omega) (α₂ ≫ v.f n) β₃ ≫
      γ₃.f (n + m + 1)) ≫ H.d (n + m + 1) (n + m + 1 + 1) = 0) :
    H.liftCycles (cupPair Φ F₁ G₁ (n + 1) m (n + m + 1) (by omega) α₁ (β₂ ≫ l.f m) ≫
          γ₁.f (n + m + 1)) (n + m + 1 + 1) (CochainComplex.next ℤ (n + m + 1)) hc₁ ≫
        H.homologyπ (n + m + 1) =
      ((n + 1).negOnePow : ℤ) •
        (H.liftCycles (cupPair Φ F₃ G₃ n (m + 1) (n + m + 1) (by omega) (α₂ ≫ v.f n) β₃ ≫
            γ₃.f (n + m + 1)) (n + m + 1 + 1) (CochainComplex.next ℤ (n + m + 1)) hc₃ ≫
          H.homologyπ (n + m + 1)) := by
  have hcb : ((cupPair Φ F₂ G₂ n m (n + m) rfl α₂ β₂ ≫ γ₂.f (n + m)) ≫
      H.d (n + m) (n + m + 1)) ≫ H.d (n + m + 1) (n + m + 1 + 1) = 0 := by
    rw [Category.assoc, HomologicalComplex.d_comp_d, comp_zero]
  have key : H.liftCycles (cupPair Φ F₁ G₁ (n + 1) m (n + m + 1) (by omega) α₁ (β₂ ≫ l.f m) ≫
        γ₁.f (n + m + 1)) (n + m + 1 + 1) (CochainComplex.next ℤ (n + m + 1)) hc₁ =
      ((n + 1).negOnePow : ℤ) •
          H.liftCycles (cupPair Φ F₃ G₃ n (m + 1) (n + m + 1) (by omega) (α₂ ≫ v.f n) β₃ ≫
            γ₃.f (n + m + 1)) (n + m + 1 + 1) (CochainComplex.next ℤ (n + m + 1)) hc₃ +
        H.liftCycles ((cupPair Φ F₂ G₂ n m (n + m) rfl α₂ β₂ ≫ γ₂.f (n + m)) ≫
          H.d (n + m) (n + m + 1)) (n + m + 1 + 1) (CochainComplex.next ℤ (n + m + 1)) hcb := by
    rw [← cancel_mono (H.iCycles (n + m + 1))]
    simp only [Preadditive.add_comp, Preadditive.zsmul_comp, HomologicalComplex.liftCycles_i]
    exact gamma_cup_boundary Φ u v k l γ₁ γ₂ γ₃ h₁ h₂ n m α₂ β₂ α₁ hα β₃ hβ
  have hzero : H.liftCycles ((cupPair Φ F₂ G₂ n m (n + m) rfl α₂ β₂ ≫ γ₂.f (n + m)) ≫
        H.d (n + m) (n + m + 1)) (n + m + 1 + 1) (CochainComplex.next ℤ (n + m + 1)) hcb ≫
      H.homologyπ (n + m + 1) = 0 :=
    H.liftCycles_homologyπ_eq_zero_of_boundary _ _ (CochainComplex.next ℤ (n + m + 1))
      (cupPair Φ F₂ G₂ n m (n + m) rfl α₂ β₂ ≫ γ₂.f (n + m)) rfl
  rw [key, Preadditive.add_comp, hzero, add_zero, Preadditive.zsmul_comp]

end

end Stacks.CupProduct

end
