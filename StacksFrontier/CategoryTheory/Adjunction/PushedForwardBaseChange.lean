module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormula

/-!
# A pushed-forward base change map, through the projection formula

Consider a commutative square of categories

```
     Lf
  S ---→ T
Lg |     | Lg'
   v     v
  S' --→ T'
     Lf'
```

all four functors having right adjoints, with bifunctors `A, B, A', B'` on the four corners and
comparisons `αf, αf', αg, αg'` along the four functors, compatible around the square. Write
`J = Rg(𝟙')` and `J' = Rg'(𝟙'')` for units `𝟙'` of `S'` and `𝟙''` of `T'`. Then `Rg` applied to
the base change map `bc_K : Lg(Rf K) ⟶ Rf'(Lg' K)` is identified with the projection-formula map
of `Lf ⊣ Rf` at `(K, J)`: the square

```
  A(Rf K, J) ----Φ----> Rg(Lg(Rf K)) --Rg bc_K--> Rg(Rf'(Lg' K)) --ψ--> Rf(Rg'(Lg' K))
      |                                                                      ^
      | projection formula of f                                              | Rf(Φ')
      v                                                                      |
  Rf(B(K, Lf J)) ---------------------Rf(B(1, τ))----------------------> Rf(B(K, J'))
```

commutes, where `Φ` and `Φ'` are the projection-formula maps of `g` and `g'` at the unit,
`τ : Lf J ⟶ J'` is the base change map of the transposed square at `𝟙'`, and `ψ` is the
conjugate of the identification of the two composites around the square. This is the coherence
behind the proof of [Stacks, Tag 08IB] over an affine base.

## Main definitions

* `Stacks.CategoryTheory.BaseChange.unitProjection` — `Φ_M : A(M, Rg 𝟙') ⟶ Rg(Lg M)`.
* `Stacks.CategoryTheory.BaseChange.pushforwardSquare` — `ψ : Rf' ⋙ Rg ⟶ Rg' ⋙ Rf`.
* `Stacks.CategoryTheory.BaseChange.transposedUnitBaseChange` — `τ : Lf(Rg 𝟙') ⟶ Rg' 𝟙''`.

## Main results

* `Stacks.CategoryTheory.BaseChange.unitProjection_comp_map_comp_pushforwardSquare` — the square.
* `Stacks.CategoryTheory.BaseChange.isIso_map_baseChange_of_isIso` — `Rg(bc_K)` is invertible
  when the projection-formula maps and `τ` are.
-/

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.Prod

namespace Stacks.CategoryTheory.BaseChange

open Stacks.AffineProjectionFormula

variable {S : Type*} {T : Type*} {S' : Type*} {T' : Type*}
  [Category S] [Category T] [Category S'] [Category T']
  {Lf : S ⥤ T} {Rf : T ⥤ S} {Lf' : S' ⥤ T'} {Rf' : T' ⥤ S'}
  {Lg : S ⥤ S'} {Rg : S' ⥤ S} {Lg' : T ⥤ T'} {Rg' : T' ⥤ T} {Lc : S ⥤ T'}
  (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (adjg : Lg ⊣ Rg) (adjg' : Lg' ⊣ Rg')
  (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)

/-- **The comparison of the right adjoints of the two composites around the square**,
`Rg ∘ Rf' ⟶ Rf ∘ Rg'`: the conjugate of the inverse identification `Lf ⋙ Lg' ⟶ Lg ⋙ Lf'`. -/
def pushforwardSquare : Rf' ⋙ Rg ⟶ Rg' ⋙ Rf :=
  conjugateEquiv (adjg.comp adjf') (adjf.comp adjg') (squareCompositeIso eg ef).inv

/-- The comparison `ψ : Rf' ⋙ Rg ⟶ Rg' ⋙ Rf` is an isomorphism. -/
instance : IsIso (pushforwardSquare adjf adjf' adjg adjg' eg ef) := by
  unfold pushforwardSquare; infer_instance

section Unit

variable (A' : S' × S' ⥤ S') (A : S × S ⥤ S) (αg : A ⋙ Lg ⟶ Lg.prod Lg ⋙ A')
  (o' : S') (ρ' : Functor.prod' (𝟭 S') ((Functor.const S').obj o') ⋙ A' ⟶ 𝟭 S')

/-- **The projection-formula map of `Lg ⊣ Rg` at the unit**, `A(M, Rg 𝟙') ⟶ Rg(Lg M)`: the
adjoint transpose of the comparison `Lg(A(M, Rg 𝟙')) ⟶ A'(Lg M, Lg Rg 𝟙')` followed by the counit
in the second factor and the unit constraint `A'(N, 𝟙') ⟶ N`. -/
def unitProjection (M : S) : A.obj (M, Rg.obj o') ⟶ Rg.obj (Lg.obj M) :=
  adjg.homEquiv _ _ (αg.app (M, Rg.obj o') ≫ A'.map (𝟙 (Lg.obj M) ×ₘ adjg.counit.app o') ≫
    ρ'.app (Lg.obj M))

/-- The adjunct of `Φ_M` under `Lg ⊣ Rg` is the comparison
`Lg(A(M, Rg 𝟙')) ⟶ A'(Lg M, Lg Rg 𝟙')` followed by the counit in the second factor and the unit
constraint. -/
theorem homEquiv_symm_unitProjection (M : S) :
    (adjg.homEquiv _ _).symm (unitProjection adjg A' A αg o' ρ' M) =
      αg.app (M, Rg.obj o') ≫ A'.map (𝟙 (Lg.obj M) ×ₘ adjg.counit.app o') ≫
        ρ'.app (Lg.obj M) :=
  Equiv.symm_apply_apply _ _

/-- `Φ` is natural in its argument. -/
theorem unitProjection_naturality {M M' : S} (h : M ⟶ M') :
    A.map (h ×ₘ 𝟙 (Rg.obj o')) ≫ unitProjection adjg A' A αg o' ρ' M' =
      unitProjection adjg A' A αg o' ρ' M ≫ Rg.map (Lg.map h) := by
  apply (adjg.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_right_symm,
    homEquiv_symm_unitProjection, homEquiv_symm_unitProjection]
  have h1 := αg.naturality (X := ((M, Rg.obj o') : S × S)) (Y := ((M', Rg.obj o') : S × S))
    (h ×ₘ 𝟙 (Rg.obj o'))
  have h2 := ρ'.naturality (Lg.map h)
  simp only [Functor.comp_map, Functor.prod_map, Functor.prod'_map,
    Functor.id_map, Functor.const_obj_map, Functor.id_obj, Functor.comp_obj, Functor.prod'_obj,
    Functor.const_obj_obj] at h1 h2
  rw [reassoc_of% h1, Category.assoc, Category.assoc, ← h2]
  congr 1
  rw [← A'.map_comp_assoc, ← A'.map_comp_assoc, prod_comp, prod_comp]
  congr 3
  · simp
  · simp

end Unit

section Square

variable (A : S × S ⥤ S) (A' : S' × S' ⥤ S') (B : T × T ⥤ T) (B' : T' × T' ⥤ T')
  (αf : A ⋙ Lf ⟶ Lf.prod Lf ⋙ B) (αf' : A' ⋙ Lf' ⟶ Lf'.prod Lf' ⋙ B')
  (αg : A ⋙ Lg ⟶ Lg.prod Lg ⋙ A') (αg' : B ⋙ Lg' ⟶ Lg'.prod Lg' ⋙ B')
  (o' : S') (ρ' : Functor.prod' (𝟭 S') ((Functor.const S').obj o') ⋙ A' ⟶ 𝟭 S')
  (o'' : T') (ρ'' : Functor.prod' (𝟭 T') ((Functor.const T').obj o'') ⋙ B' ⟶ 𝟭 T')
  (u : Lf'.obj o' ⟶ o'')

/-- The base change map of the transposed square at the unit, followed by the unit comparison:
`τ : Lf(Rg 𝟙') ⟶ Rg'(Lf' 𝟙') ⟶ Rg' 𝟙''`. -/
def transposedUnitBaseChange : Lf.obj (Rg.obj o') ⟶ Rg'.obj o'' :=
  map adjg adjg' ef eg o' ≫ Rg'.map u

/-- Two maps into `Rf(Rg' W)` agree as soon as their adjuncts under the composite
`Lf ⋙ Lg' ⊣ Rg' ⋙ Rf` do. -/
theorem ext_of_comp_counit {X : S} {W : T'} (x y : X ⟶ Rf.obj (Rg'.obj W))
    (h : Lg'.map (Lf.map x ≫ adjf.counit.app _) ≫ adjg'.counit.app W =
      Lg'.map (Lf.map y ≫ adjf.counit.app _) ≫ adjg'.counit.app W) : x = y := by
  apply (adjf.homEquiv _ _).symm.injective
  apply (adjg'.homEquiv _ _).symm.injective
  simpa only [Adjunction.homEquiv_counit] using h

/-- The adjunct of the left-hand composite of the square, under `Lf ⋙ Lg' ⊣ Rg' ⋙ Rf`. -/
theorem lhs_adjunct (K : T)
    (hsq : TensorComparisonCompatible eg ef A A' B B' αf αf' αg αg' (Rf.obj K) (Rg.obj o'))
    (hunit : ∀ X : S', αf'.app (X, o') ≫ B'.map (𝟙 (Lf'.obj X) ×ₘ u) ≫ ρ''.app (Lf'.obj X) =
      Lf'.map (ρ'.app X)) :
    Lg'.map (Lf.map (unitProjection adjg A' A αg o' ρ' (Rf.obj K) ≫
        Rg.map (map adjf adjf' eg ef K) ≫
          (pushforwardSquare adjf adjf' adjg adjg' eg ef).app (Lg'.obj K)) ≫
        adjf.counit.app _) ≫ adjg'.counit.app (Lg'.obj K) =
      Lg'.map (αf.app (Rf.obj K, Rg.obj o')) ≫ αg'.app (Lf.obj (Rf.obj K), Lf.obj (Rg.obj o')) ≫
        B'.map (Lg'.map (adjf.counit.app K) ×ₘ
          ((squareCompositeIso eg ef).inv.app (Rg.obj o') ≫ Lf'.map (adjg.counit.app o') ≫ u)) ≫
        ρ''.app (Lg'.obj K) := by
  have hψ := conjugateEquiv_counit (adjg.comp adjf') (adjf.comp adjg')
    (squareCompositeIso eg ef).inv (Lg'.obj K)
  simp only [Adjunction.comp_counit_app, Functor.comp_map, Functor.comp_obj] at hψ
  have hΦ : Lg.map (unitProjection adjg A' A αg o' ρ' (Rf.obj K)) ≫
        adjg.counit.app (Lg.obj (Rf.obj K)) =
      αg.app (Rf.obj K, (Rg.obj o')) ≫ A'.map (𝟙 (Lg.obj (Rf.obj K)) ×ₘ adjg.counit.app o') ≫
        ρ'.app (Lg.obj (Rf.obj K)) := by
    rw [← homEquiv_symm_unitProjection adjg A' A αg o' ρ' (Rf.obj K), Adjunction.homEquiv_counit]
  have hbc := map_baseChangeMap_comp_counit adjf adjf' eg ef K
  have hsqn := (squareCompositeIso eg ef).inv.naturality
    (unitProjection adjg A' A αg o' ρ' (Rf.obj K) ≫ Rg.map (map adjf adjf' eg ef K))
  simp only [Functor.comp_map] at hsqn
  have hαf' := αf'.naturality (X := (((Lg.obj (Rf.obj K)), Lg.obj (Rg.obj o')) : S' × S'))
    (Y := (((Lg.obj (Rf.obj K)), o') : S' × S')) (𝟙 (Lg.obj (Rf.obj K)) ×ₘ adjg.counit.app o')
  simp only [Functor.comp_map, Functor.prod_map] at hαf'
  have hρ'' := ρ''.naturality
    ((squareCompositeIso eg ef).hom.app (Rf.obj K) ≫ Lg'.map (adjf.counit.app K))
  simp only [Functor.comp_map, Functor.prod'_map, Functor.id_map, Functor.const_obj_map,
    Functor.id_obj, Functor.comp_obj, Functor.prod'_obj, Functor.const_obj_obj] at hρ''
  rw [TensorComparisonCompatible] at hsq
  calc _ = Lg'.map (Lf.map (unitProjection adjg A' A αg o' ρ' (Rf.obj K) ≫
          Rg.map (map adjf adjf' eg ef K))) ≫
        (Lg'.map (Lf.map ((pushforwardSquare adjf adjf' adjg adjg' eg ef).app (Lg'.obj K))) ≫
          Lg'.map (adjf.counit.app _) ≫ adjg'.counit.app (Lg'.obj K)) := by
        simp only [Functor.map_comp, Category.assoc]
    _ = (squareCompositeIso eg ef).inv.app (A.obj (Rf.obj K, (Rg.obj o'))) ≫ Lf'.map (Lg.map
          (unitProjection adjg A' A αg o' ρ' (Rf.obj K) ≫ Rg.map (map adjf adjf' eg ef K))) ≫
        Lf'.map (adjg.counit.app (Rf'.obj (Lg'.obj K))) ≫ adjf'.counit.app (Lg'.obj K) := by
        rw [show (pushforwardSquare adjf adjf' adjg adjg' eg ef) =
          conjugateEquiv (adjg.comp adjf') (adjf.comp adjg') (squareCompositeIso eg ef).inv
            from rfl, hψ, reassoc_of% hsqn]
    _ = (squareCompositeIso eg ef).inv.app (A.obj (Rf.obj K, (Rg.obj o'))) ≫
        Lf'.map (αg.app (Rf.obj K, (Rg.obj o'))) ≫
        Lf'.map (A'.map (𝟙 (Lg.obj (Rf.obj K)) ×ₘ adjg.counit.app o')) ≫
        Lf'.map (ρ'.app (Lg.obj (Rf.obj K))) ≫
        (squareCompositeIso eg ef).hom.app (Rf.obj K) ≫ Lg'.map (adjf.counit.app K) := by
        have h3 : Lg.map (unitProjection adjg A' A αg o' ρ' (Rf.obj K) ≫
            Rg.map (map adjf adjf' eg ef K)) ≫ adjg.counit.app (Rf'.obj (Lg'.obj K)) =
            (αg.app (Rf.obj K, (Rg.obj o')) ≫
              A'.map (𝟙 (Lg.obj (Rf.obj K)) ×ₘ adjg.counit.app o') ≫
              ρ'.app (Lg.obj (Rf.obj K))) ≫ map adjf adjf' eg ef K := by
          rw [Functor.map_comp, Category.assoc, ← Functor.comp_map Rg Lg,
            adjg.counit.naturality]
          simp only [Functor.id_map, Functor.id_obj, ← Category.assoc, hΦ]
        rw [← Functor.map_comp_assoc, h3, Functor.map_comp, Category.assoc, hbc]
        simp only [Functor.map_comp, Category.assoc]
    _ = _ := by
        rw [← hunit (Lg.obj (Rf.obj K))]
        simp only [Category.assoc]
        rw [reassoc_of% hαf', ← hρ'']
        have hsplit : B'.map (Lf'.map (𝟙 (Lg.obj (Rf.obj K))) ×ₘ Lf'.map (adjg.counit.app o')) ≫
            B'.map (𝟙 (Lf'.obj (Lg.obj (Rf.obj K))) ×ₘ u) ≫
            B'.map ((squareCompositeIso eg ef).hom.app (Rf.obj K) ≫
              Lg'.map (adjf.counit.app K) ×ₘ 𝟙 o'') =
            B'.map ((squareCompositeIso eg ef).hom.app (Rf.obj K) ×ₘ
              (squareCompositeIso eg ef).hom.app (Rg.obj o')) ≫
            B'.map (Lg'.map (adjf.counit.app K) ×ₘ
              ((squareCompositeIso eg ef).inv.app (Rg.obj o') ≫ Lf'.map (adjg.counit.app o') ≫
                u)) := by
          simp only [← B'.map_comp, prod_comp, CategoryTheory.Functor.map_id, Category.id_comp,
            Category.comp_id, Iso.hom_inv_id_app_assoc]
        rw [reassoc_of% hsplit, reassoc_of% hsq, Iso.inv_hom_id_app_assoc]

/-- The adjunct of the right-hand composite of the square, under `Lf ⋙ Lg' ⊣ Rg' ⋙ Rf`. -/
theorem rhs_adjunct (K : T) :
    Lg'.map (Lf.map (adjunctionTensorMap adjf A B αf K (Rg.obj o') ≫
        Rf.map (B.map (𝟙 K ×ₘ transposedUnitBaseChange adjg adjg' eg ef o' o'' u) ≫
          unitProjection adjg' B' B αg' o'' ρ'' K)) ≫
        adjf.counit.app _) ≫ adjg'.counit.app (Lg'.obj K) =
      Lg'.map (αf.app (Rf.obj K, Rg.obj o')) ≫ αg'.app (Lf.obj (Rf.obj K), Lf.obj (Rg.obj o')) ≫
        B'.map (Lg'.map (adjf.counit.app K) ×ₘ
          ((squareCompositeIso eg ef).inv.app (Rg.obj o') ≫ Lf'.map (adjg.counit.app o') ≫ u)) ≫
        ρ''.app (Lg'.obj K) := by
  have hΦ' : Lg'.map (unitProjection adjg' B' B αg' o'' ρ'' K) ≫ adjg'.counit.app (Lg'.obj K) =
      αg'.app (K, Rg'.obj o'') ≫ B'.map (𝟙 (Lg'.obj K) ×ₘ adjg'.counit.app o'') ≫
        ρ''.app (Lg'.obj K) := by
    rw [← homEquiv_symm_unitProjection adjg' B' B αg' o'' ρ'' K, Adjunction.homEquiv_counit]
  have hτ : Lg'.map (transposedUnitBaseChange adjg adjg' eg ef o' o'' u) ≫ adjg'.counit.app o'' =
      (squareCompositeIso eg ef).inv.app (Rg.obj o') ≫ Lf'.map (adjg.counit.app o') ≫ u := by
    rw [transposedUnitBaseChange, Functor.map_comp, Category.assoc, ← Functor.comp_map Rg' Lg',
      adjg'.counit.naturality, Functor.id_map, ← Category.assoc,
      map_baseChangeMap_comp_counit adjg adjg' ef eg o', Category.assoc]
    rfl
  have hαg' := αg'.naturality (X := ((Lf.obj (Rf.obj K), Lf.obj (Rg.obj o')) : T × T))
    (Y := ((K, Rg'.obj o'') : T × T))
    (adjf.counit.app K ×ₘ transposedUnitBaseChange adjg adjg' eg ef o' o'' u)
  simp only [Functor.comp_map, Functor.prod_map] at hαg'
  have hinner : Lf.map (adjunctionTensorMap adjf A B αf K (Rg.obj o') ≫
      Rf.map (B.map (𝟙 K ×ₘ transposedUnitBaseChange adjg adjg' eg ef o' o'' u) ≫
        unitProjection adjg' B' B αg' o'' ρ'' K)) ≫ adjf.counit.app _ =
      αf.app (Rf.obj K, Rg.obj o') ≫ B.map (adjf.counit.app K ×ₘ 𝟙 (Lf.obj (Rg.obj o'))) ≫
        B.map (𝟙 K ×ₘ transposedUnitBaseChange adjg adjg' eg ef o' o'' u) ≫
        unitProjection adjg' B' B αg' o'' ρ'' K := by
    rw [Functor.map_comp, Category.assoc, ← Functor.comp_map Rf Lf, adjf.counit.naturality,
      Functor.id_map, ← Category.assoc, map_adjunctionTensorMap_comp_counit]
    simp only [Category.assoc]
  rw [hinner]
  simp only [Functor.map_comp, Category.assoc, hΦ']
  have hB : B.map (adjf.counit.app K ×ₘ 𝟙 (Lf.obj (Rg.obj o'))) ≫
      B.map (𝟙 K ×ₘ transposedUnitBaseChange adjg adjg' eg ef o' o'' u) =
      B.map (adjf.counit.app K ×ₘ transposedUnitBaseChange adjg adjg' eg ef o' o'' u) := by
    rw [← bifunctor_map_comp_both]
    congr 2
    · exact Category.comp_id _
    · exact Category.id_comp _
  have hB' : B'.map (Lg'.map (adjf.counit.app K) ×ₘ
      Lg'.map (transposedUnitBaseChange adjg adjg' eg ef o' o'' u)) ≫
      B'.map (𝟙 (Lg'.obj K) ×ₘ adjg'.counit.app o'') =
      B'.map (Lg'.map (adjf.counit.app K) ×ₘ
        (Lg'.map (transposedUnitBaseChange adjg adjg' eg ef o' o'' u) ≫ adjg'.counit.app o'')) := by
    rw [← bifunctor_map_comp_both]
    congr 2
    · exact Category.comp_id _
  rw [← Functor.map_comp_assoc Lg' (B.map _), hB, reassoc_of% hαg', reassoc_of% hB', hτ]

/-- **The pushed-forward base change map, through the projection formula.** `Φ`, then `Rg` of the
base change map, then the comparison `ψ` of the right adjoints, is the projection-formula map of
`Lf ⊣ Rf` at `(K, J)`, followed by `τ` in the second factor and `Φ'`. The inputs are the
compatibility of the four comparisons around the square at `(Rf K, J)` and the unit
compatibility of the comparison along `Lf'`. -/
theorem unitProjection_comp_map_comp_pushforwardSquare (K : T)
    (hsq : TensorComparisonCompatible eg ef A A' B B' αf αf' αg αg' (Rf.obj K) (Rg.obj o'))
    (hunit : ∀ X : S', αf'.app (X, o') ≫ B'.map (𝟙 (Lf'.obj X) ×ₘ u) ≫ ρ''.app (Lf'.obj X) =
      Lf'.map (ρ'.app X)) :
    unitProjection adjg A' A αg o' ρ' (Rf.obj K) ≫ Rg.map (map adjf adjf' eg ef K) ≫
        (pushforwardSquare adjf adjf' adjg adjg' eg ef).app (Lg'.obj K) =
      adjunctionTensorMap adjf A B αf K (Rg.obj o') ≫
        Rf.map (B.map (𝟙 K ×ₘ transposedUnitBaseChange adjg adjg' eg ef o' o'' u) ≫
          unitProjection adjg' B' B αg' o'' ρ'' K) :=
  ext_of_comp_counit adjf adjg' _ _ ((lhs_adjunct adjf adjf' adjg adjg' eg ef A A' B B' αf αf'
    αg αg' o' ρ' o'' ρ'' u K hsq hunit).trans
      (rhs_adjunct adjf adjg adjg' eg ef A B B' αf αg' o' o'' ρ'' u K).symm)

/-- **The pushed-forward base change map is invertible** as soon as the projection-formula maps
`Φ` at `Rf K`, `Φ'` at `K` and that of `Lf ⊣ Rf` at `(K, J)` are, and the transposed base change
map `τ` at the unit is. -/
theorem isIso_map_baseChange_of_isIso (K : T)
    (hsq : TensorComparisonCompatible eg ef A A' B B' αf αf' αg αg' (Rf.obj K) (Rg.obj o'))
    (hunit : ∀ X : S', αf'.app (X, o') ≫ B'.map (𝟙 (Lf'.obj X) ×ₘ u) ≫ ρ''.app (Lf'.obj X) =
      Lf'.map (ρ'.app X))
    [IsIso (unitProjection adjg A' A αg o' ρ' (Rf.obj K))]
    [IsIso (unitProjection adjg' B' B αg' o'' ρ'' K)]
    [IsIso (adjunctionTensorMap adjf A B αf K (Rg.obj o'))]
    [IsIso (transposedUnitBaseChange adjg adjg' eg ef o' o'' u)] :
    IsIso (Rg.map (map adjf adjf' eg ef K)) := by
  have h := unitProjection_comp_map_comp_pushforwardSquare adjf adjf' adjg adjg' eg ef A A' B B'
    αf αf' αg αg' o' ρ' o'' ρ'' u K hsq hunit
  have : IsIso (B.map (𝟙 K ×ₘ transposedUnitBaseChange adjg adjg' eg ef o' o'' u)) :=
    have : IsIso (𝟙 K ×ₘ transposedUnitBaseChange adjg adjg' eg ef o' o'' u) :=
      (isIso_prod_iff (C := T) (D := T)).2 ⟨inferInstance, inferInstance⟩
    inferInstance
  have hR : IsIso (unitProjection adjg A' A αg o' ρ' (Rf.obj K) ≫
      Rg.map (map adjf adjf' eg ef K) ≫
        (pushforwardSquare adjf adjf' adjg adjg' eg ef).app (Lg'.obj K)) := by
    rw [h]; infer_instance
  have h2 : IsIso (Rg.map (map adjf adjf' eg ef K) ≫
      (pushforwardSquare adjf adjf' adjg adjg' eg ef).app (Lg'.obj K)) :=
    IsIso.of_isIso_comp_left (unitProjection adjg A' A αg o' ρ' (Rf.obj K)) _
  exact IsIso.of_isIso_comp_right _ ((pushforwardSquare adjf adjf' adjg adjg' eg ef).app _)

end Square

end Stacks.CategoryTheory.BaseChange
