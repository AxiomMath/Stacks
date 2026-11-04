module

public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiTateRealization

/-!
# The product of twisted units over the monoidal structure of the envelope

Let `C` be a graded monoidal category and `M_C` its twisted Karoubi envelope. The isomorphism
`T(n) ⊗ T(m) ≅ T(p)`, `n + m = p`, of twisted units (`TwistedKaroubi.unitTwistTensorIsoOfEq`) is
stated with the direct tensor product `TwistedKaroubi.monoidalCategoryStruct`. Monoid objects and
monoidal functors use the tensor product of `TwistedKaroubi.monoidalCategory`, which is equal to it
by definition; for a concrete `C` (such as correspondences) comparing the two unfolds the objects
of `C`. This file restates the isomorphism over `TwistedKaroubi.monoidalCategory`
(`TwistedKaroubi.tateTensorHom`) and the multiplicativity of the generators `eₙ ∈ G(T(n))^{dn}` of
a realization in that form (`TwistedKaroubi.tateGen_eq_map_tateTensorHom`).

## Main definitions

* `CategoryTheory.GradedCategory.TwistedKaroubi.tateTensorHom`: `T(n) ⊗ T(m) ⟶ T(p)`.

## Main results

* `CategoryTheory.GradedCategory.TwistedKaroubi.tateGen_eq_map_tateTensorHom`:
  `e_p = G(T(n) ⊗ T(m) ⟶ T(p))(eₙ ⊗ eₘ)`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory.GradedCategory.TwistedKaroubi

universe w v u uF

attribute [-instance] TwistedKaroubi.monoidalCategoryStruct

variable {R : Type w} [Ring R] {C : Type u} [Category.{v} C] [Preadditive C] [GradedCategory R C]
  [MonoidalCategory C] [IsGradedMonoidal R C]

/-- **`T(n) ⊗ T(m) ⟶ T(p)`** for `n + m = p`, over the monoidal structure
`TwistedKaroubi.monoidalCategory`: the isomorphism `TwistedKaroubi.unitTwistTensorIsoOfEq`. -/
noncomputable def tateTensorHom (n m p : ℤ) (h : n + m = p) :
    tateTriple R C n ⊗ tateTriple R C m ⟶ tateTriple R C p :=
  (unitTwistTensorIsoOfEq n m p h).hom

/-- The underlying morphism of `tateTensorHom n m p h` in `C` is the right unitor of `𝟙_ C`. -/
@[simp]
theorem tateTensorHom_val (n m p : ℤ) (h : n + m = p) :
    (tateTensorHom (R := R) (C := C) n m p h).val = (ρ_ (𝟙_ C)).hom :=
  unitTwistTensorIsoOfEq_hom_val n m p h

/-- **`M ⊗ N ⟶ P` for objects `M = T(n)`, `N = T(m)`, `P = T(p)`**, `n + m = p`:
`TwistedKaroubi.tateTensorHom` read at other spellings of the twisted units (such as the Tate
motives `𝟏(n)` of `M_k`), so that it composes with morphisms out of `P` without comparing
spellings. -/
noncomputable def tateTensorHomOfEq {M N P : TwistedKaroubi R C} (n m p : ℤ) (h : n + m = p)
    (hM : M = tateTriple R C n) (hN : N = tateTriple R C m) (hP : P = tateTriple R C p) :
    M ⊗ N ⟶ P :=
  eqToHom (by rw [hM, hN]) ≫ tateTensorHom n m p h ≫ eqToHom hP.symm

/-- `tateTensorHomOfEq` at the twisted units themselves is `tateTensorHom`. -/
theorem tateTensorHomOfEq_rfl (n m p : ℤ) (h : n + m = p) :
    tateTensorHomOfEq (R := R) (C := C) n m p h rfl rfl rfl = tateTensorHom n m p h := by
  simp [tateTensorHomOfEq]

variable {F : Type uF} [Field F] {G : TwistedKaroubi R C ⥤ GradedObject ℤ (ModuleCat.{uF} F)}
  [G.Monoidal] {d : ℤ} (hG : ∀ i, i ≠ d → IsZero ((G.obj (tateTriple R C 1)) i))
  {e₁ : tateLine G d 1} (he₁ : e₁ ≠ 0)

/-- **The generators are multiplicative**: `e_p = G(T(n) ⊗ T(m) ⟶ T(p))(eₙ ⊗ eₘ)` for
`n + m = p`. -/
theorem tateGen_eq_map_tateTensorHom (n m p : ℤ) (h : n + m = p)
    (hk : d * n + d * m = d * p) :
    tateGen hG he₁ p = G.map (tateTensorHom n m p h) (d * p)
      (G.gradedMul (tateTriple R C n) (tateTriple R C m) (d * n) (d * m) (d * p) hk
        (tateGen hG he₁ n) (tateGen hG he₁ m)) := by
  subst h
  exact (tateMul_tateGen hG he₁ n m).symm

/-- `tateGen_eq_map_tateTensorHom` with the generators read in other spellings `a`, `b`, `c` of
their degrees `dn`, `dm`, `dp`. -/
theorem cast_tateGen_eq_map_tateTensorHom (n m p : ℤ) (h : n + m = p) {a b c : ℤ}
    (ha : d * n = a) (hb : d * m = b) (hc : d * p = c) (hk : a + b = c) :
    (eqToHom (congrArg (G.obj (tateTriple R C p)) hc)).hom (tateGen hG he₁ p) =
      G.map (tateTensorHom n m p h) c (G.gradedMul (tateTriple R C n) (tateTriple R C m) a b c hk
        ((eqToHom (congrArg (G.obj (tateTriple R C n)) ha)).hom (tateGen hG he₁ n))
        ((eqToHom (congrArg (G.obj (tateTriple R C m)) hb)).hom (tateGen hG he₁ m))) := by
  subst ha hb hc
  simp only [eqToHom_refl, ModuleCat.hom_id, LinearMap.id_apply]
  exact tateGen_eq_map_tateTensorHom hG he₁ n m p h hk

/-- `tateGen_eq_map_tateTensorHom` at other spellings `M`, `N`, `P` of the twisted units and `a`,
`b`, `c` of the degrees: if `x`, `y`, `z` are `eₙ`, `eₘ`, `e_p` read in `G(M)^a`, `G(N)^b`,
`G(P)^c`, then `z = G(M ⊗ N ⟶ P)(x · y)`. -/
theorem eq_map_tateTensorHomOfEq_of_heq {M N P : TwistedKaroubi R C} (n m p : ℤ) (h : n + m = p)
    (hM : M = tateTriple R C n) (hN : N = tateTriple R C m) (hP : P = tateTriple R C p)
    {a b c : ℤ} (ha : d * n = a) (hb : d * m = b) (hc : d * p = c) (hk : a + b = c)
    (x : G.obj M a) (y : G.obj N b) (z : G.obj P c) (hx : x ≍ tateGen hG he₁ n)
    (hy : y ≍ tateGen hG he₁ m) (hz : z ≍ tateGen hG he₁ p) :
    z = G.map (tateTensorHomOfEq n m p h hM hN hP) c (G.gradedMul M N a b c hk x y) := by
  subst hM hN hP ha hb hc
  cases hx; cases hy; cases hz
  rw [tateTensorHomOfEq_rfl]
  exact tateGen_eq_map_tateTensorHom hG he₁ n m p h hk

end CategoryTheory.GradedCategory.TwistedKaroubi

end
