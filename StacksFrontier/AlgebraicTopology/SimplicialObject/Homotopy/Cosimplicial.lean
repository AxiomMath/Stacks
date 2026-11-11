module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty
public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplexOne
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Homotopy.Basic
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Power
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Homotopies of morphisms of cosimplicial objects

Homotopies between morphisms of cosimplicial objects, both in the family form that needs no
products and through the objects `Hom(Δ[1], V)`, their comparison with simplicial homotopies of the
opposite simplicial objects, and their preservation by functors.
-/

/-!
## Homotopies and cosimplicial objects

Let `C` be a category and let `U`, `V` be cosimplicial objects of `C`, i.e. functors `Δ ⥤ C`. A
*homotopy* from `a : U ⟶ V` to `b : U ⟶ V` is, in the form of [Stacks, Tag 0FKJ] that needs no
products in `C`, a family of morphisms `h_{n, α} : Uₙ ⟶ Vₙ`, one for each simplex `α ∈ Δ[1]ₙ`,
satisfying `h_{m, α} ∘ U(f) = V(f) ∘ h_{n, α ∘ f}` for every morphism `f : ⦋n⦌ ⟶ ⦋m⦌` of `Δ`
([Stacks, Tag 07KB]) and having `aₙ`, `bₙ` as its components at the two constant maps
`⦋n⦌ ⟶ ⦋1⦌`; `a` and `b` are *homotopic* when they are related by the equivalence relation the
existence of such a family generates. Where the products `∏_{α ∈ Δ[1]ₙ} Vₙ` exist this is the
same datum as a morphism `U ⟶ Hom(Δ[1], V)` ([Stacks, Tag 019W]), but the family form needs no
products, and that is the generality in which this file works.

This file collects five results about that notion.

Reading `Δ ⥤ C` as `Δᵒᵖ ⥤ Cᵒᵖ` turns `U`, `V` into simplicial objects `U.op`, `V.op` of `Cᵒᵖ`
and `a`, `b` into morphisms `aᵒᵖ`, `bᵒᵖ : V.op ⟶ U.op`, and the two notions of homotopy match up
under this dictionary: a homotopy from `a` to `b` exists if and only if a combinatorial
simplicial homotopy from `aᵒᵖ` to `bᵒᵖ` ([Stacks, Tag 019M]) exists. Both directions are
explicit. Writing `α_i ∈ Δ[1]ₙ` for the simplex taking the value `0` exactly `i` times, so that
`α_0` is the vertex `1` and `α_{n + 1}` the vertex `0`: from a family `h` one builds the
combinatorial homotopy whose component at `i` is `h_{n + 1, α_{i + 1}} ≫ σⁱ`, and from a
combinatorial homotopy `K` one builds the family `h_{n, α_i} = δⁱ ≫ K_{n, i}` for `i ≤ n`, with
`h_{n, α_{n + 1}} = aₙ`.

A functor carries such a family to a family of the same kind, the defining relations being
equations between composites of morphisms, and hence carries homotopic morphisms to homotopic
ones. This holds in the four combinations of variance with simplicial versus cosimplicial: a
covariant functor preserves each of the two notions, and a contravariant functor turns one into
the other, reversing the direction of the morphisms.

A self map of a Čech conerve which is the identity on the base is homotopic to the identity.
Writing `g⁰ = F.right` and `g¹ = 𝟙 Y` for the two morphisms attached to the vertices of `Δ[1]`,
the component of the homotopy at a simplex `α ∈ Δ[1]ₙ` is the self map of `Uₙ = Y ⨿_X ⋯ ⨿_X Y`
which is `g^{α(i)}` on the `i`-th factor. One fact makes this work: both `g⁰` and `g¹` satisfy
`f ≫ g = f`, so each such family of endomorphisms of the factors descends to the pushout, its
component over the base being the base inclusion itself.

Finally, for `A` preadditive the Moore cochain complex functor `s = alternatingCofaceMapComplex A`
of [Stacks, Tag 019I] carries homotopic morphisms of cosimplicial objects of `A` to chain
homotopic maps of cochain complexes, and a homotopy equivalence of cosimplicial objects to a
homotopy equivalence of cochain complexes.

### Main results

* `CategoryTheory.CosimplicialObject.exists_homotopy_iff_nonempty_homotopy_op`: there is a
  homotopy from `a` to `b` in the sense of [Stacks, Tag 0FKJ] if and only if there is a
  simplicial homotopy from `aᵒᵖ` to `bᵒᵖ` in the sense of [Stacks, Tag 019M].
* `CategoryTheory.homotopic_whiskerRight`: the four parts of [Stacks, Tag 019Y]. For any
  functors `F : D ⥤ D'`, `F : C ⥤ C'`, `F : Dᵒᵖ ⥤ C` and `F : Cᵒᵖ ⥤ D`, homotopic morphisms of
  (co)simplicial objects have homotopic images, of the kind and in the direction dictated by `F`.
* `CategoryTheory.Arrow.exists_homotopy_mapCechConerve_id`: for an endomorphism `F` of an arrow
  `f` with `F.left ∘ f = f`, there is a homotopy from the induced self map
  `Arrow.mapCechConerve F` of the Čech conerve of `f` to the identity.
* `AlgebraicTopology.homotopic_alternatingCofaceMapComplex_map`: if `a, b : U ⟶ V` are homotopic
  morphisms of cosimplicial objects of a preadditive category, then `s(a), s(b) : s(U) ⟶ s(V)`
  are homotopic maps of cochain complexes.
* `AlgebraicTopology.homotopyEquivalences_alternatingCofaceMapComplex_map`: the Moore cochain
  complex `s(a) : s(U) ⟶ s(V)` of a homotopy equivalence `a : U ⟶ V` of cosimplicial objects of
  a preadditive category is a homotopy equivalence of cochain complexes.

### References

* [Stacks, Tag 019X](https://stacks.math.columbia.edu/tag/019X)
* [Stacks, Tag 019Y](https://stacks.math.columbia.edu/tag/019Y)
* [Stacks, Tag 019Z](https://stacks.math.columbia.edu/tag/019Z)
* [Stacks, Tag 01A0](https://stacks.math.columbia.edu/tag/01A0)
* [Stacks, Tag 0FKK](https://stacks.math.columbia.edu/tag/0FKK)
* [Stacks, Tag 016N](https://stacks.math.columbia.edu/tag/016N)
* [Stacks, Tag 019I](https://stacks.math.columbia.edu/tag/019I)
* [Stacks, Tag 019M](https://stacks.math.columbia.edu/tag/019M)
* [Stacks, Tag 019N](https://stacks.math.columbia.edu/tag/019N)
* [Stacks, Tag 019S](https://stacks.math.columbia.edu/tag/019S)
* [Stacks, Tag 019T](https://stacks.math.columbia.edu/tag/019T)
* [Stacks, Tag 019W](https://stacks.math.columbia.edu/tag/019W)
* [Stacks, Tag 07KB](https://stacks.math.columbia.edu/tag/07KB)
* [Stacks, Tag 0FKJ](https://stacks.math.columbia.edu/tag/0FKJ)
-/

section

@[expose] public section

universe v u v₁ v₂ u₁ u₂

/-! ### Homotopies of cosimplicial objects as simplicial homotopies in the opposite category -/

section CosimplicialHomotopyOp

open CategoryTheory CategoryTheory.Limits Opposite Simplicial SSet

section

variable {C : Type u} [Category.{v} C] {U V : CosimplicialObject C}

/-! #### The simplices of `Δ[1]`: their vertices, faces and degeneracies -/

/-- Deleting the `j`-th vertex of the simplex `α_i` of `Δ[1]` gives `α_{i - 1}` if the jump of
`α_i` is at or before `j`, and `α_i` otherwise. -/
private lemma δ_objMk₁ {n : ℕ} (i : Fin (n + 3)) (j : Fin (n + 2)) (k : Fin (n + 2))
    (hk : (k : ℕ) = if (j : ℕ) < (i : ℕ) then (i : ℕ) - 1 else (i : ℕ)) :
    (Δ[1] : SSet.{0}).δ j (stdSimplex.objMk₁ i) = stdSimplex.objMk₁ k := by
  rcases lt_or_ge (j : ℕ) (i : ℕ) with h | h
  · rw [stdSimplex.δ_objMk₁_of_lt i j (by simpa [Fin.lt_def] using h)]
    exact congrArg _ (Fin.ext (by simp [hk, h]))
  · rw [stdSimplex.δ_objMk₁_of_le i j (by simpa [Fin.le_def] using h)]
    exact congrArg _ (Fin.ext (by simp [hk, Nat.not_lt.mpr h]))

/-- Repeating the `j`-th vertex of the simplex `α_i` of `Δ[1]` gives `α_{i + 1}` if the jump of
`α_i` is at or before `j`, and `α_i` otherwise. -/
private lemma σ_objMk₁ {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (k : Fin (n + 3))
    (hk : (k : ℕ) = if (j : ℕ) < (i : ℕ) then (i : ℕ) + 1 else (i : ℕ)) :
    (Δ[1] : SSet.{0}).σ j (stdSimplex.objMk₁ i) = stdSimplex.objMk₁ k := by
  rcases lt_or_ge (j : ℕ) (i : ℕ) with h | h
  · rw [stdSimplex.σ_objMk₁_of_lt i j (by simpa [Fin.lt_def] using h)]
    exact congrArg _ (Fin.ext (by simp [hk, h]))
  · rw [stdSimplex.σ_objMk₁_of_le i j (by simpa [Fin.le_def] using h)]
    exact congrArg _ (Fin.ext (by simp [hk, Nat.not_lt.mpr h]))

/-! #### From a homotopy in the sense of [Stacks, Tag 0FKJ] to a simplicial homotopy -/

section

variable (hh : ∀ n : SimplexCategory, (Δ[1] : SSet.{0}).obj (op n) → (U.obj n ⟶ V.obj n))
  (hnat : ∀ ⦃n m : SimplexCategory⦄ (g : n ⟶ m) (α : (Δ[1] : SSet.{0}).obj (op m)),
    U.map g ≫ hh m α = hh n ((Δ[1] : SSet.{0}).map g.op α) ≫ V.map g)

/-- The morphism `U_{n + 1} ⟶ V_n` attached to `i : Fin (n + 1)` by a homotopy `hh` in the
sense of [Stacks, Tag 0FKJ]: the component of `hh` at the simplex of `Δ[1]_{n + 1}` taking the
value `0` exactly `i + 1` times, followed by the codegeneracy `σⁱ`. -/
private noncomputable def cohom (n : ℕ) (i : Fin (n + 1)) : U.obj ⦋n + 1⦌ ⟶ V.obj ⦋n⦌ :=
  hh ⦋n + 1⦌ (stdSimplex.objMk₁ i.succ.castSucc) ≫ V.σ i

include hnat

private lemma hh_δ {n : ℕ} (i : Fin (n + 2)) (α : (Δ[1] : SSet.{0}) _⦋n + 1⦌) :
    U.δ i ≫ hh ⦋n + 1⦌ α = hh ⦋n⦌ ((Δ[1] : SSet.{0}).δ i α) ≫ V.δ i :=
  hnat _ _

private lemma hh_σ {n : ℕ} (i : Fin (n + 1)) (α : (Δ[1] : SSet.{0}) _⦋n⦌) :
    U.σ i ≫ hh ⦋n⦌ α = hh ⦋n + 1⦌ ((Δ[1] : SSet.{0}).σ i α) ≫ V.σ i :=
  hnat _ _

/-- A coface map followed by `cohom hh m j`, in the case where it cancels the codegeneracy of
`cohom`: what is left is the value of `hh` at the `i`-th face of the simplex `α_{j + 1}`. -/
private lemma δ_comp_cohom_of_comp_eq_id {m : ℕ} (i : Fin (m + 2)) (j : Fin (m + 1))
    (α : (Δ[1] : SSet.{0}) _⦋m⦌)
    (hα : (Δ[1] : SSet.{0}).δ i (stdSimplex.objMk₁ j.succ.castSucc) = α)
    (hV : V.δ i ≫ V.σ j = 𝟙 _) :
    U.δ i ≫ cohom hh m j = hh ⦋m⦌ α := by
  simp only [cohom, ← Category.assoc, hh_δ hh hnat, hα]
  simp [hV]

/-- A coface map followed by `cohom hh (p + 1) j`, in the case where it commutes past the
codegeneracy of `cohom`. -/
private lemma δ_comp_cohom_of_eq {p : ℕ} (i : Fin (p + 3)) (j : Fin (p + 2)) (j' : Fin (p + 1))
    (i' : Fin (p + 2))
    (hα : (Δ[1] : SSet.{0}).δ i (stdSimplex.objMk₁ j.succ.castSucc) =
      stdSimplex.objMk₁ j'.succ.castSucc)
    (hV : V.δ i ≫ V.σ j = V.σ j' ≫ V.δ i') :
    U.δ i ≫ cohom hh (p + 1) j = cohom hh p j' ≫ V.δ i' := by
  simp only [cohom, ← Category.assoc, hh_δ hh hnat, hα]
  simp [hV]

/-- A codegeneracy map followed by `cohom hh m j`, which it commutes past. -/
private lemma σ_comp_cohom_of_eq {m : ℕ} (i : Fin (m + 2)) (j : Fin (m + 1)) (j' : Fin (m + 2))
    (i' : Fin (m + 1))
    (hα : (Δ[1] : SSet.{0}).σ i (stdSimplex.objMk₁ j.succ.castSucc) =
      stdSimplex.objMk₁ j'.succ.castSucc)
    (hV : V.σ i ≫ V.σ j = V.σ j' ≫ V.σ i') :
    U.σ i ≫ cohom hh m j = cohom hh (m + 1) j' ≫ V.σ i' := by
  simp only [cohom, ← Category.assoc, hh_σ hh hnat, hα]
  simp [hV]

/-- A homotopy in the sense of [Stacks, Tag 0FKJ] between morphisms `a, b : U ⟶ V` of
cosimplicial objects of `C` is a combinatorial simplicial homotopy, in the sense of
[Stacks, Tag 019M], between the corresponding morphisms `V.op ⟶ U.op` of simplicial objects
of `Cᵒᵖ`. -/
private noncomputable def toSimplicialObjectHomotopy {a b : U ⟶ V}
    (ha : ∀ n : SimplexCategory, hh n (stdSimplex.const 1 0 (op n)) = a.app n)
    (hb : ∀ n : SimplexCategory, hh n (stdSimplex.const 1 1 (op n)) = b.app n) :
    SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b) where
  h {n} i := (cohom hh n i).op
  h_zero_comp_δ_zero n := congrArg Quiver.Hom.op
    ((δ_comp_cohom_of_comp_eq_id hh hnat 0 0 _
      ((δ_objMk₁ _ _ (0 : Fin (n + 2)) (by simp)).trans (stdSimplex.objMk₁_zero n))
      (V.δ_comp_σ_self' (by simp))).trans (hb ⦋n⦌))
  h_last_comp_δ_last n := congrArg Quiver.Hom.op
    ((δ_comp_cohom_of_comp_eq_id hh hnat (Fin.last (n + 1)) (Fin.last n) _
      ((δ_objMk₁ _ _ (Fin.last (n + 1)) (by simp)).trans (stdSimplex.objMk₁_last n))
      (V.δ_comp_σ_succ' (by simp))).trans (ha ⦋n⦌))
  h_succ_comp_δ_castSucc_of_lt i j hij := congrArg Quiver.Hom.op
    (δ_comp_cohom_of_eq hh hnat i.castSucc j.succ j i
      (δ_objMk₁ _ _ _ (by grind))
      (V.δ_comp_σ_of_le hij))
  h_succ_comp_δ_castSucc_succ j := congrArg Quiver.Hom.op
    ((δ_comp_cohom_of_comp_eq_id hh hnat j.castSucc.succ j.succ
          (stdSimplex.objMk₁ j.succ.castSucc) (δ_objMk₁ _ _ _ (by simp))
          (V.δ_comp_σ_self' (Fin.succ_castSucc j))).trans
      (δ_comp_cohom_of_comp_eq_id hh hnat j.castSucc.succ j.castSucc
          (stdSimplex.objMk₁ j.succ.castSucc) (δ_objMk₁ _ _ _ (by simp))
          (V.δ_comp_σ_succ' rfl)).symm)
  h_castSucc_comp_δ_succ_of_lt i j hji := congrArg Quiver.Hom.op
    (δ_comp_cohom_of_eq hh hnat i.succ j.castSucc j i
      (δ_objMk₁ _ _ _ (by grind))
      (V.δ_comp_σ_of_gt hji))
  h_comp_σ_castSucc_of_le i j hij := congrArg Quiver.Hom.op
    (σ_comp_cohom_of_eq hh hnat i.castSucc j j.succ i
      (σ_objMk₁ _ _ _ (by grind)) (V.σ_comp_σ hij))
  h_comp_σ_succ_of_lt i j hji := congrArg Quiver.Hom.op
    (σ_comp_cohom_of_eq hh hnat i.succ j j.castSucc i
      (σ_objMk₁ _ _ _ (by grind))
      (V.σ_comp_σ hji).symm)

end

/-! #### From a simplicial homotopy to a homotopy in the sense of [Stacks, Tag 0FKJ] -/

/-- The simplices of `Δ[1]_n` are enumerated by `Fin (n + 2)`. -/
private noncomputable def objMk₁Equiv (n : ℕ) : Fin (n + 2) ≃ (Δ[1] : SSet.{0}) _⦋n⦌ :=
  Equiv.ofBijective _ stdSimplex.objMk₁_bijective

section

variable {a b : U ⟶ V} (H : SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b))

/-- The component `U_{n + 1} ⟶ V_n` of a combinatorial simplicial homotopy between the
morphisms `V.op ⟶ U.op` of simplicial objects of `Cᵒᵖ` corresponding to `a` and `b`. -/
private def kUnop (n : ℕ) (i : Fin (n + 1)) : U.obj ⦋n + 1⦌ ⟶ V.obj ⦋n⦌ := (H.h i).unop

private lemma δ_zero_comp_kUnop_zero (n : ℕ) : U.δ (0 : Fin (n + 2)) ≫ kUnop H n 0 = b.app ⦋n⦌ :=
  Quiver.Hom.op_inj (H.h_zero_comp_δ_zero n)

private lemma δ_last_comp_kUnop_last (n : ℕ) :
    U.δ (Fin.last (n + 1)) ≫ kUnop H n (Fin.last n) = a.app ⦋n⦌ :=
  Quiver.Hom.op_inj (H.h_last_comp_δ_last n)

private lemma δ_castSucc_comp_kUnop_succ {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
    (hij : i ≤ j.castSucc) : U.δ i.castSucc ≫ kUnop H (n + 1) j.succ = kUnop H n j ≫ V.δ i :=
  Quiver.Hom.op_inj (H.h_succ_comp_δ_castSucc_of_lt i j hij)

private lemma δ_castSucc_succ_comp_kUnop {n : ℕ} (j : Fin (n + 1)) :
    U.δ j.castSucc.succ ≫ kUnop H (n + 1) j.succ =
      U.δ j.castSucc.succ ≫ kUnop H (n + 1) j.castSucc :=
  Quiver.Hom.op_inj (H.h_succ_comp_δ_castSucc_succ j)

private lemma δ_succ_comp_kUnop_castSucc {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
    (hji : j.castSucc < i) : U.δ i.succ ≫ kUnop H (n + 1) j.castSucc = kUnop H n j ≫ V.δ i :=
  Quiver.Hom.op_inj (H.h_castSucc_comp_δ_succ_of_lt i j hji)

private lemma σ_castSucc_comp_kUnop {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) :
    U.σ i.castSucc ≫ kUnop H n j = kUnop H (n + 1) j.succ ≫ V.σ i :=
  Quiver.Hom.op_inj (H.h_comp_σ_castSucc_of_le i j hij)

private lemma σ_succ_comp_kUnop {n : ℕ} (i j : Fin (n + 1)) (hji : j ≤ i) :
    U.σ i.succ ≫ kUnop H n j = kUnop H (n + 1) j.castSucc ≫ V.σ i :=
  Quiver.Hom.op_inj (H.h_comp_σ_succ_of_lt i j hji)

/-- The family of components of the homotopy from `a` to `b` in the sense of
[Stacks, Tag 0FKJ] attached to a combinatorial simplicial homotopy `H`: its component at the
simplex `α_i` of `Δ[1]_n` is `δⁱ ≫ K_{n, i}` for `i ≤ n`, and `a_n` at the vertex `α_{n + 1}`. -/
private def hfam (n : ℕ) : Fin (n + 2) → (U.obj ⦋n⦌ ⟶ V.obj ⦋n⦌) :=
  Fin.lastCases (a.app ⦋n⦌) (fun i => U.δ i.castSucc ≫ kUnop H n i)

private noncomputable def fam (n : SimplexCategory) (α : (Δ[1] : SSet.{0}).obj (op n)) :
    U.obj n ⟶ V.obj n :=
  hfam H n.len ((objMk₁Equiv n.len).symm α)

private lemma fam_objMk₁_castSucc (n : ℕ) (i : Fin (n + 1)) :
    fam H ⦋n⦌ (stdSimplex.objMk₁ i.castSucc) = U.δ i.castSucc ≫ kUnop H n i :=
  (congrArg (hfam H n) ((objMk₁Equiv n).symm_apply_apply i.castSucc)).trans
    (Fin.lastCases_castSucc ..)

private lemma fam_objMk₁_last (n : ℕ) :
    fam H ⦋n⦌ (stdSimplex.objMk₁ (Fin.last (n + 1))) = a.app ⦋n⦌ :=
  (congrArg (hfam H n) ((objMk₁Equiv n).symm_apply_apply (Fin.last (n + 1)))).trans
    (Fin.lastCases_last ..)

private lemma fam_const_zero (n : SimplexCategory) :
    fam H n (stdSimplex.const 1 0 (op n)) = a.app n := by
  rw [← stdSimplex.objMk₁_last n.len, fam_objMk₁_last]

private lemma fam_const_one (n : SimplexCategory) :
    fam H n (stdSimplex.const 1 1 (op n)) = b.app n := by
  rw [← stdSimplex.objMk₁_zero n.len, ← Fin.castSucc_zero, fam_objMk₁_castSucc, Fin.castSucc_zero]
  exact δ_zero_comp_kUnop_zero H n.len

/-- The family `fam H` is compatible with the coface maps. -/
private lemma δ_comp_fam {n : ℕ} (i : Fin (n + 2)) (α : (Δ[1] : SSet.{0}) _⦋n + 1⦌) :
    U.δ i ≫ fam H ⦋n + 1⦌ α = fam H ⦋n⦌ ((Δ[1] : SSet.{0}).δ i α) ≫ V.δ i := by
  obtain ⟨k, rfl⟩ := stdSimplex.objMk₁_surjective α
  induction k using Fin.lastCases with
  | last =>
      rw [δ_objMk₁ (Fin.last (n + 2)) i (Fin.last (n + 1)) (by simp [i.is_lt]),
        fam_objMk₁_last, fam_objMk₁_last]
      exact CosimplicialObject.δ_naturality a i
  | cast k =>
      rw [fam_objMk₁_castSucc]
      rcases lt_trichotomy (i : ℕ) (k : ℕ) with h | h | h
      · obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero (i := k) (fun hk => by simp [hk] at h)
        simp only [Fin.val_succ] at h
        have hij : i ≤ j.castSucc := by grind
        rw [δ_objMk₁ j.succ.castSucc i j.castSucc (by grind), fam_objMk₁_castSucc,
          ← Fin.succ_castSucc, U.δ_comp_δ_assoc hij, δ_castSucc_comp_kUnop_succ H i j hij,
          Category.assoc]
      · obtain rfl : k = i := Fin.ext h.symm
        rcases eq_or_lt_of_le (Nat.le_of_lt_succ k.is_lt) with hn | hn
        · obtain rfl : k = Fin.last (n + 1) := Fin.ext hn
          rw [δ_objMk₁ (Fin.last (n + 1)).castSucc (Fin.last (n + 1)) (Fin.last (n + 1)) (by simp),
            fam_objMk₁_last, U.δ_comp_δ_self_assoc, Fin.succ_last,
            δ_last_comp_kUnop_last H (n + 1)]
          exact CosimplicialObject.δ_naturality a (Fin.last (n + 1))
        · obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last (x := k)
            (fun hl => absurd hn (by simp [hl]))
          rw [δ_objMk₁ j.castSucc.castSucc j.castSucc j.castSucc (by simp), fam_objMk₁_castSucc,
            U.δ_comp_δ_self_assoc, ← δ_castSucc_succ_comp_kUnop H j, ← U.δ_comp_δ_self_assoc,
            δ_castSucc_comp_kUnop_succ H j.castSucc j le_rfl, Category.assoc]
      · have hi := i.is_lt
        obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last (x := k)
          (fun hl => by rw [hl, Fin.val_last] at h; omega)
        simp only [Fin.val_castSucc] at h
        have hji : j.castSucc < i := by grind
        have hle : (j.castSucc.castSucc : Fin (n + 3)) ≤ i.castSucc := by grind
        have hδδ : U.δ i ≫ U.δ j.castSucc.castSucc = U.δ j.castSucc ≫ U.δ i.succ :=
          (CosimplicialObject.δ_comp_δ'' U hle).symm
        rw [δ_objMk₁ j.castSucc.castSucc i j.castSucc (by grind), fam_objMk₁_castSucc,
          ← Category.assoc, hδδ, Category.assoc, δ_succ_comp_kUnop_castSucc H i j hji,
          Category.assoc]

/-- The family `fam H` is compatible with the codegeneracy maps. -/
private lemma σ_comp_fam {n : ℕ} (i : Fin (n + 1)) (α : (Δ[1] : SSet.{0}) _⦋n⦌) :
    U.σ i ≫ fam H ⦋n⦌ α = fam H ⦋n + 1⦌ ((Δ[1] : SSet.{0}).σ i α) ≫ V.σ i := by
  obtain ⟨k, rfl⟩ := stdSimplex.objMk₁_surjective α
  induction k using Fin.lastCases with
  | last =>
      rw [σ_objMk₁ (Fin.last (n + 1)) i (Fin.last (n + 2)) (by simp [i.is_lt]),
        fam_objMk₁_last, fam_objMk₁_last]
      exact CosimplicialObject.σ_naturality a i
  | cast j =>
      rw [fam_objMk₁_castSucc]
      rcases le_or_gt (j : ℕ) (i : ℕ) with h | h
      · rw [σ_objMk₁ j.castSucc i j.castSucc.castSucc (by grind), fam_objMk₁_castSucc,
          ← U.δ_comp_σ_of_le_assoc (by grind : (j.castSucc : Fin (n + 2)) ≤ i.castSucc),
          σ_succ_comp_kUnop H i j (Fin.le_def.mpr h), Category.assoc]
      · rw [σ_objMk₁ j.castSucc i j.succ.castSucc (by grind), fam_objMk₁_castSucc,
          ← Fin.succ_castSucc,
          ← U.δ_comp_σ_of_gt_assoc (by grind : (i.castSucc : Fin (n + 2)) < j.castSucc),
          σ_castSucc_comp_kUnop H i j (Fin.le_def.mpr h.le), Category.assoc]

/-- The family `fam H` is compatible with every structure map. -/
@[sga "4 Vbis 3.0.2.2" "partial"]
private lemma fam_naturality ⦃n m : SimplexCategory⦄ (f : n ⟶ m)
    (α : (Δ[1] : SSet.{0}).obj (op m)) :
    U.map f ≫ fam H m α = fam H n ((Δ[1] : SSet.{0}).map f.op α) ≫ V.map f := by
  let W : MorphismProperty SimplexCategory := fun n m f =>
    ∀ α : (Δ[1] : SSet.{0}).obj (op m),
      U.map f ≫ fam H m α = fam H n ((Δ[1] : SSet.{0}).map f.op α) ≫ V.map f
  have : W.IsMultiplicative :=
    { id_mem := fun n α => by simp
      comp_mem := fun {n m k} f g hf hg α => by
        rw [U.map_comp, Category.assoc, hg α, ← Category.assoc, hf _, Category.assoc, V.map_comp,
          op_comp, Functor.map_comp]
        rfl }
  exact (by simp [SimplexCategory.morphismProperty_eq_top W (δ_comp_fam H) (σ_comp_fam H)] :
    W f) α

end

end

namespace CategoryTheory.CosimplicialObject

variable {C : Type u} [Category.{v} C]

/-- **Stacks 019X**.
A homotopy of morphisms of cosimplicial objects is a simplicial homotopy in the opposite category.
Let `C` be a category with no assumptions whatsoever, let `U`, `V` be cosimplicial objects of `C`
and let `a, b : U ⟶ V`, so that `U`, `V` correspond to simplicial objects `U.op`, `V.op` of `Cᵒᵖ`
and `a`, `b` to morphisms `aᵒᵖ, bᵒᵖ : V.op ⟶ U.op`. Then there exists a homotopy `{h_{n, α}}` from
`a` to `b` in the sense of [Stacks, Tag 0FKJ] — a family of morphisms `h_{n, α} : U_n ⟶ V_n`,
indexed by the simplices `α ∈ Δ[1]_n`, satisfying `h_{m, α} ∘ U(f) = V(f) ∘ h_{n, α ∘ f}` for every
morphism `f : ⦋n⦌ ⟶ ⦋m⦌` of `Δ` and having `a_n`, `b_n` as its components at the two constant maps
`⦋n⦌ ⟶ ⦋1⦌` — if and only if there exists a homotopy `{h_{n, i}}` from `aᵒᵖ` to `bᵒᵖ` in the sense
of [Stacks, Tag 019M]. Hence `a` and `b` are homotopic if and only if `aᵒᵖ` and `bᵒᵖ` are, the two
relations being the equivalence relations generated by these two existence statements. -/
@[stacks 019X "the equivalence of (1) and (2); the primed objects are spelled `U.op` and \
  `NatTrans.op a` rather than through `cosimplicialSimplicialEquiv`, a homotopy as in 0FKJ by \
  its family of components as in 07KB, and a homotopy as in 019M by Mathlib's \
  `SimplicialObject.Homotopy`, so that neither side needs (co)products and the statement holds \
  over an arbitrary category. The final assertion, homotopic if and only if homotopic, is the \
  equivalence of the `Relation.EqvGen` of the two sides and is formal from this one, by \
  transport along the bijection `NatTrans.op : (U ⟶ V) ≃ (V.op ⟶ U.op)`; it is what 019Y (2) \
  and (4) apply"]
public theorem exists_homotopy_iff_nonempty_homotopy_op {U V : CosimplicialObject C}
    (a b : U ⟶ V) :
    (∃ h : ∀ n : SimplexCategory, (Δ[1] : SSet.{0}).obj (op n) → (U.obj n ⟶ V.obj n),
        (∀ ⦃n m : SimplexCategory⦄ (f : n ⟶ m) (α : (Δ[1] : SSet.{0}).obj (op m)),
            U.map f ≫ h m α = h n ((Δ[1] : SSet.{0}).map f.op α) ≫ V.map f) ∧
          (∀ n : SimplexCategory, h n (stdSimplex.const 1 0 (op n)) = a.app n) ∧
          (∀ n : SimplexCategory, h n (stdSimplex.const 1 1 (op n)) = b.app n)) ↔
      Nonempty (SimplicialObject.Homotopy (NatTrans.op a) (NatTrans.op b)) :=
  ⟨fun ⟨hh, hnat, ha, hb⟩ => ⟨toSimplicialObjectHomotopy hh hnat ha hb⟩,
    fun ⟨H⟩ => ⟨fam H, fam_naturality H, fam_const_zero H, fam_const_one H⟩⟩

end CategoryTheory.CosimplicialObject

end CosimplicialHomotopyOp

/-! ### Functors preserve homotopic morphisms of (co)simplicial objects -/

section FunctorsPreserveHomotopic

open CategoryTheory CategoryTheory.Limits Opposite Simplicial SSet

namespace CategoryTheory

/-- **Stacks 019Y**.
Functors preserve homotopic morphisms of (co)simplicial objects. Let `C`, `C'`, `D`, `D'` be
categories, with no assumptions whatsoever. (1) If `a, b : U ⟶ V` are homotopic morphisms of
simplicial objects of `D` in the sense of [Stacks, Tag 019M] and `F : D ⥤ D'` is a functor, then
`F(a)`, `F(b)` are homotopic morphisms `F(U) ⟶ F(V)` of simplicial objects of `D'`. (2) If
`a, b : U ⟶ V` are homotopic morphisms of cosimplicial objects of `C` in the sense of
[Stacks, Tag 0FKJ] — a family `h_{n, α} : Uₙ ⟶ Vₙ`, indexed by the simplices `α ∈ Δ[1]_n`,
satisfying `h_{m, α} ∘ U(f) = V(f) ∘ h_{n, α ∘ f}` and having `aₙ`, `bₙ` as its components at the
two constant maps `⦋n⦌ ⟶ ⦋1⦌`, and chains of such — and `F : C ⥤ C'` is a functor, then `F(a)`,
`F(b)` are homotopic morphisms `F(U) ⟶ F(V)` of cosimplicial objects of `C'`. (3) For a
contravariant functor, i.e. a functor `F : Dᵒᵖ ⥤ C`, homotopic morphisms `a, b : U ⟶ V` of
simplicial objects of `D` have homotopic images `F(a)`, `F(b) : F(V) ⟶ F(U)`, morphisms of
cosimplicial objects of `C`. (4) Likewise a functor `F : Cᵒᵖ ⥤ D` takes homotopic morphisms
`a, b : U ⟶ V` of cosimplicial objects of `C` to homotopic morphisms `F(a)`, `F(b) : F(V) ⟶ F(U)`
of simplicial objects of `D`. No (co)limit in any of the four categories is assumed to exist, and
the functor is not asked to preserve anything. -/
@[stacks 019Y "all four parts, at the chain level: `homotopic` is `Relation.EqvGen` of the \
  existence of a homotopy, as in 019K, 019W and 0FKJ. Homotopy of simplicial objects over an \
  arbitrary category is `SimplicialObject.Homotopy` (Mathlib), the notion of 019M through the \
  composites of the source's footnote; homotopy of cosimplicial objects is the family of \
  0FKJ, repeated verbatim. The source's four categories occur as they do there, each part \
  binding the two it names, so that each part applies on its own; the four are one \
  conjunction because they are one assertion read in four dualities. The passage between \
  variances is `Functor.rightOp`/`Functor.op` and `NatTrans.rightOp`/`NatTrans.op`, the \
  anti-equivalences `simplicialCosimplicialEquiv` and `cosimplicialSimplicialEquiv`"]
public theorem homotopic_whiskerRight :
    (∀ {D : Type u₁} [Category.{v₁} D] {D' : Type u₂} [Category.{v₂} D']
        {U V : SimplicialObject D} {a b : U ⟶ V} (F : D ⥤ D'),
        Relation.EqvGen (fun x y : U ⟶ V => Nonempty (SimplicialObject.Homotopy x y)) a b →
          Relation.EqvGen
            (fun x y : U ⋙ F ⟶ V ⋙ F => Nonempty (SimplicialObject.Homotopy x y))
            (Functor.whiskerRight a F) (Functor.whiskerRight b F)) ∧
      (∀ {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
          {U V : CosimplicialObject C} {a b : U ⟶ V} (F : C ⥤ C'),
          Relation.EqvGen (fun x y : U ⟶ V => ∃ h : ∀ n : SimplexCategory,
              (Δ[1] : SSet.{0}).obj (op n) → (U.obj n ⟶ V.obj n),
              (∀ ⦃n m : SimplexCategory⦄ (f : n ⟶ m) (α : (Δ[1] : SSet.{0}).obj (op m)),
                  U.map f ≫ h m α = h n ((Δ[1] : SSet.{0}).map f.op α) ≫ V.map f) ∧
                (∀ n : SimplexCategory, h n (stdSimplex.const 1 0 (op n)) = x.app n) ∧
                (∀ n : SimplexCategory, h n (stdSimplex.const 1 1 (op n)) = y.app n)) a b →
            Relation.EqvGen (fun x y : U ⋙ F ⟶ V ⋙ F => ∃ h : ∀ n : SimplexCategory,
                (Δ[1] : SSet.{0}).obj (op n) → ((U ⋙ F).obj n ⟶ (V ⋙ F).obj n),
                (∀ ⦃n m : SimplexCategory⦄ (f : n ⟶ m) (α : (Δ[1] : SSet.{0}).obj (op m)),
                    (U ⋙ F).map f ≫ h m α =
                      h n ((Δ[1] : SSet.{0}).map f.op α) ≫ (V ⋙ F).map f) ∧
                  (∀ n : SimplexCategory, h n (stdSimplex.const 1 0 (op n)) = x.app n) ∧
                  (∀ n : SimplexCategory, h n (stdSimplex.const 1 1 (op n)) = y.app n))
              (Functor.whiskerRight a F) (Functor.whiskerRight b F)) ∧
        (∀ {D : Type u₁} [Category.{v₁} D] {C : Type u₂} [Category.{v₂} C]
            {U V : SimplicialObject D} {a b : U ⟶ V} (F : Dᵒᵖ ⥤ C),
            Relation.EqvGen (fun x y : U ⟶ V => Nonempty (SimplicialObject.Homotopy x y)) a b →
              Relation.EqvGen (fun x y : V.rightOp ⋙ F ⟶ U.rightOp ⋙ F =>
                  ∃ h : ∀ n : SimplexCategory, (Δ[1] : SSet.{0}).obj (op n) →
                    ((V.rightOp ⋙ F).obj n ⟶ (U.rightOp ⋙ F).obj n),
                  (∀ ⦃n m : SimplexCategory⦄ (f : n ⟶ m) (α : (Δ[1] : SSet.{0}).obj (op m)),
                      (V.rightOp ⋙ F).map f ≫ h m α =
                        h n ((Δ[1] : SSet.{0}).map f.op α) ≫ (U.rightOp ⋙ F).map f) ∧
                    (∀ n : SimplexCategory, h n (stdSimplex.const 1 0 (op n)) = x.app n) ∧
                    (∀ n : SimplexCategory, h n (stdSimplex.const 1 1 (op n)) = y.app n))
                (Functor.whiskerRight (NatTrans.rightOp a) F)
                (Functor.whiskerRight (NatTrans.rightOp b) F)) ∧
          (∀ {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
              {U V : CosimplicialObject C} {a b : U ⟶ V} (F : Cᵒᵖ ⥤ D),
              Relation.EqvGen (fun x y : U ⟶ V => ∃ h : ∀ n : SimplexCategory,
                  (Δ[1] : SSet.{0}).obj (op n) → (U.obj n ⟶ V.obj n),
                  (∀ ⦃n m : SimplexCategory⦄ (f : n ⟶ m) (α : (Δ[1] : SSet.{0}).obj (op m)),
                      U.map f ≫ h m α = h n ((Δ[1] : SSet.{0}).map f.op α) ≫ V.map f) ∧
                    (∀ n : SimplexCategory, h n (stdSimplex.const 1 0 (op n)) = x.app n) ∧
                    (∀ n : SimplexCategory, h n (stdSimplex.const 1 1 (op n)) = y.app n)) a b →
                Relation.EqvGen (fun x y : V.op ⋙ F ⟶ U.op ⋙ F =>
                    Nonempty (SimplicialObject.Homotopy x y))
                  (Functor.whiskerRight (NatTrans.op a) F)
                  (Functor.whiskerRight (NatTrans.op b) F)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro D _ D' _ U V a b F hab
    exact Relation.EqvGen.map (fun x => Functor.whiskerRight x F)
      (fun _ _ hxy => hxy.map (·.whiskerRight F)) hab
  · intro C _ C' _ U V a b F hab
    refine Relation.EqvGen.map (fun x => Functor.whiskerRight x F) (fun x y hxy => ?_) hab
    exact (CosimplicialObject.exists_homotopy_iff_nonempty_homotopy_op _ _).mpr
      (((CosimplicialObject.exists_homotopy_iff_nonempty_homotopy_op x y).mp hxy).map
        (·.whiskerRight F.op))
  · intro D _ C _ U V a b F hab
    refine Relation.EqvGen.map (fun x => Functor.whiskerRight (NatTrans.rightOp x) F)
      (fun _ _ hxy => ?_) hab
    exact (CosimplicialObject.exists_homotopy_iff_nonempty_homotopy_op _ _).mpr
      (hxy.map (·.whiskerRight F.rightOp))
  · intro C _ D _ U V a b F hab
    refine Relation.EqvGen.map (fun x => Functor.whiskerRight (NatTrans.op x) F)
      (fun x y hxy => ?_) hab
    exact ((CosimplicialObject.exists_homotopy_iff_nonempty_homotopy_op x y).mp hxy).map
      (·.whiskerRight F)

end CategoryTheory

end FunctorsPreserveHomotopic

/-! ### Self maps of a Čech conerve over its base -/

section CechConerve

open CategoryTheory CategoryTheory.Limits Opposite Simplicial SSet

section

variable {C : Type u} [Category.{v} C] {f : Arrow C}

/-- An endomorphism `F` of an arrow `f` which is the identity on the base is the identity on `f`
also from the other side: `f ≫ F.right = f`. -/
private lemma hom_comp_right (F : f ⟶ f) (hF : F.left ≫ f.hom = f.hom) :
    f.hom ≫ F.right = f.hom :=
  (Arrow.w F).symm.trans hF

/-- Both endomorphisms of `f.right` attached to the two vertices of `Δ[1]`, namely `F.right` at
the vertex `0` and `𝟙 f.right` at the vertex `1`, leave `f.hom` unchanged. -/
private lemma hom_comp_vertexEndo (F : f ⟶ f) (hF : F.left ≫ f.hom = f.hom) (k : Fin 2) :
    f.hom ≫ ![F.right, 𝟙 f.right] k = f.hom := by
  match k with
  | 0 => simpa using hom_comp_right F hF
  | 1 => simp

end

section

variable {C : Type u} [Category.{v} C] {f : Arrow C}
  [∀ n : ℕ, HasWidePushout f.left (fun _ : Fin (n + 1) => f.right) fun _ => f.hom]

namespace CategoryTheory.Arrow

@[expose] public section

/-- The family of maps `f.hom` whose wide pushout is the degree `n` term of the Čech conerve. -/
abbrev cechLegs (f : Arrow C) (n : SimplexCategory) : Fin (n.len + 1) → (f.left ⟶ f.right) :=
  fun _ => f.hom

/-- The inclusion of the `i`-th factor `f.right` into the degree `n` term of the Čech conerve. -/
noncomputable def cechι (n : SimplexCategory) (i : Fin (n.len + 1)) :
    f.right ⟶ f.cechConerve.obj n :=
  WidePushout.ι (cechLegs f n) i

/-- The inclusion of the base `f.left` into the degree `n` term of the Čech conerve. -/
noncomputable def cechHead (n : SimplexCategory) : f.left ⟶ f.cechConerve.obj n :=
  WidePushout.head (cechLegs f n)

/-- Each factor inclusion `cechι n i` restricts along `f.hom` to the inclusion `cechHead n` of the
base. -/
lemma hom_comp_cechι (n : SimplexCategory) (i : Fin (n.len + 1)) :
    f.hom ≫ cechι (f := f) n i = cechHead n :=
  WidePushout.arrow_ι (cechLegs f n) i

/-- Two morphisms out of a term of the Čech conerve agree as soon as their components on the
factors agree. -/
lemma cech_hom_ext {n : SimplexCategory} {X : C} {g₁ g₂ : f.cechConerve.obj n ⟶ X}
    (hι : ∀ i, cechι n i ≫ g₁ = cechι n i ≫ g₂) : g₁ = g₂ :=
  WidePushout.hom_ext (cechLegs f n) g₁ g₂ hι <|
    show cechHead (f := f) n ≫ g₁ = cechHead n ≫ g₂ by
      rw [← hom_comp_cechι n 0, Category.assoc, Category.assoc, hι 0]

/-- The Čech conerve sends the `i`-th factor of degree `n` to the `g i`-th factor of degree `m`
along `g : n ⟶ m`. -/
lemma cechι_comp_map {n m : SimplexCategory} (g : n ⟶ m) (i : Fin (n.len + 1)) :
    cechι n i ≫ f.cechConerve.map g = cechι m (g.toOrderHom i) :=
  WidePushout.ι_desc (cechLegs f n) _ _ _ i

/-- The map of Čech conerves induced by an endomorphism `F` of `f` acts on the `i`-th factor of
degree `n` as `F.right`. -/
lemma cechι_comp_mapCechConerve (F : f ⟶ f) (n : SimplexCategory)
    (i : Fin (n.len + 1)) :
    cechι n i ≫ (Arrow.mapCechConerve F).app n = F.right ≫ cechι n i :=
  WidePushout.ι_desc (cechLegs f n) _ _ _ i

end

/-- The self map of the degree `n` term of the Čech conerve given by a family `φ` of
endomorphisms of the factors, `φ i` on the `i`-th factor. -/
private noncomputable def factorwise {n : SimplexCategory}
    (φ : Fin (n.len + 1) → (f.right ⟶ f.right)) (hφ : ∀ i, f.hom ≫ φ i = f.hom) :
    f.cechConerve.obj n ⟶ f.cechConerve.obj n :=
  WidePushout.desc (arrows := cechLegs f n) (cechHead n) (fun i => φ i ≫ cechι n i)
    (fun i => by rw [← Category.assoc, hφ i]; exact hom_comp_cechι n i)

private lemma cechι_comp_factorwise {n : SimplexCategory}
    (φ : Fin (n.len + 1) → (f.right ⟶ f.right)) (hφ : ∀ i, f.hom ≫ φ i = f.hom)
    (i : Fin (n.len + 1)) : cechι n i ≫ factorwise φ hφ = φ i ≫ cechι n i :=
  WidePushout.ι_desc (cechLegs f n) _ _ _ i

/-- A family which is the identity on every factor descends to the identity. -/
private lemma factorwise_eq_id {n : SimplexCategory}
    {φ : Fin (n.len + 1) → (f.right ⟶ f.right)} (h : ∀ i, φ i = 𝟙 f.right) :
    factorwise φ (fun i => by rw [h i, Category.comp_id]) = 𝟙 (f.cechConerve.obj n) :=
  cech_hom_ext fun i => by
    rw [cechι_comp_factorwise, h i, Category.id_comp, Category.comp_id]

/-- For an endomorphism `F` of the arrow `f` which is the identity on the base, a family which is
`F.right` on every factor descends to `Arrow.mapCechConerve F`. -/
private lemma factorwise_eq_mapCechConerve {n : SimplexCategory} (F : f ⟶ f)
    (hF : F.left ≫ f.hom = f.hom) {φ : Fin (n.len + 1) → (f.right ⟶ f.right)}
    (h : ∀ i, φ i = F.right) :
    factorwise φ (fun i => by rw [h i]; exact hom_comp_right F hF) =
      (Arrow.mapCechConerve F).app n :=
  cech_hom_ext fun i => by
    rw [cechι_comp_factorwise, h i, cechι_comp_mapCechConerve]

/-- Reindexing along `g : ⦋n⦌ ⟶ ⦋m⦌` carries the self map given by a family `ψ` of endomorphisms
of the factors of `U_m` to the one given by any family `φ` of endomorphisms of the factors of
`U_n` with `φ i = ψ (g(i))`. -/
private lemma map_comp_factorwise {n m : SimplexCategory} (g : n ⟶ m)
    {ψ : Fin (m.len + 1) → (f.right ⟶ f.right)} (hψ : ∀ i, f.hom ≫ ψ i = f.hom)
    {φ : Fin (n.len + 1) → (f.right ⟶ f.right)} (h : ∀ i, φ i = ψ (g.toOrderHom i)) :
    f.cechConerve.map g ≫ factorwise ψ hψ =
      factorwise φ (fun i => by rw [h i]; exact hψ _) ≫ f.cechConerve.map g :=
  cech_hom_ext fun i => by
    rw [← Category.assoc, cechι_comp_map, cechι_comp_factorwise, ← Category.assoc,
      cechι_comp_factorwise, h i, Category.assoc, cechι_comp_map]

end CategoryTheory.Arrow

end

namespace CategoryTheory.Arrow

variable {C : Type u} [Category.{v} C]

/-- A self map of a Čech conerve which is the identity on the base is homotopic to the identity. Let
`f : X ⟶ Y` be an arrow of a category `C` whose iterated pushouts `Y ⨿_X ⋯ ⨿_X Y` exist, let
`U = f.cechConerve` be the cosimplicial object of [Stacks, Tag 016N] built from `f`, and let `F` be
an endomorphism of the arrow `f` with `F.left ≫ f = f`, so that the induced self map
`Arrow.mapCechConerve F` of `U`, given by `F.right` on each factor `Y`, is the identity on the base
`X`. Then there is a homotopy from that self map to `𝟙 U` in the sense of [Stacks, Tag 0FKJ]: a
family of morphisms `h_{n, α} : U_n ⟶ U_n`, indexed by the simplices `α ∈ Δ[1]_n`, satisfying
`h_{m, α} ∘ U(g) = U(g) ∘ h_{n, α ∘ g}` for every morphism `g : ⦋n⦌ ⟶ ⦋m⦌` of `Δ`, whose component
at the constant map `⦋n⦌ ⟶ ⦋1⦌` with value `0` is the self map and whose component at the constant
map with value `1` is the identity. In particular the two are homotopic. This is the first
assertion of [Stacks, Tag 019Z]; the complete lemma is
`Arrow.homotopyEquiv_cechConerve_const_of_retraction`. -/
public theorem exists_homotopy_mapCechConerve_id {f : Arrow C}
    [∀ n : ℕ, HasWidePushout f.left (fun _ : Fin (n + 1) => f.right) fun _ => f.hom]
    (F : f ⟶ f) (hF : F.left ≫ f.hom = f.hom) :
    ∃ h : ∀ n : SimplexCategory, (Δ[1] : SSet.{0}).obj (op n) →
        (f.cechConerve.obj n ⟶ f.cechConerve.obj n),
      (∀ ⦃n m : SimplexCategory⦄ (g : n ⟶ m) (α : (Δ[1] : SSet.{0}).obj (op m)),
          f.cechConerve.map g ≫ h m α =
            h n ((Δ[1] : SSet.{0}).map g.op α) ≫ f.cechConerve.map g) ∧
        (∀ n : SimplexCategory, h n (stdSimplex.const 1 0 (op n)) = (mapCechConerve F).app n) ∧
        (∀ n : SimplexCategory, h n (stdSimplex.const 1 1 (op n)) = 𝟙 (f.cechConerve.obj n)) :=
  ⟨fun _ α => factorwise (fun i => ![F.right, 𝟙 f.right] ((stdSimplex.objEquiv α).toOrderHom i))
      (fun _ => hom_comp_vertexEndo F hF _),
    fun _ _ g _ => map_comp_factorwise g _ fun _ => rfl,
    fun _ => factorwise_eq_mapCechConerve F hF fun _ => rfl,
    fun _ => factorwise_eq_id fun _ => rfl⟩

end CategoryTheory.Arrow

end CechConerve

/-! ### The Moore cochain complex of a homotopy of cosimplicial objects -/

section MooreCochainComplex

open CategoryTheory CategoryTheory.Limits Opposite Simplicial SSet AlgebraicTopology

section

variable {A : Type u} [Category.{v} A] [Preadditive A] {U V : CosimplicialObject A}

/-- The differential of the Moore cochain complex of `W` is the alternating sum of the
coface maps of `W`. -/
@[sga "4 Vbis 2.3.9" "more general", sga "4 XVII 5.5.3" "partial"]
private lemma alternatingCofaceMapComplex_obj_d (W : CosimplicialObject A) (n : ℕ) :
    ((alternatingCofaceMapComplex A).obj W).d n (n + 1) =
      AlternatingCofaceMapComplex.objD W n :=
  CochainComplex.of_d (fun n => W.obj ⦋n⦌) (AlternatingCofaceMapComplex.objD W) n

/-- The differential of the Moore complex of the simplicial object `Wᵒᵖ` of `Aᵒᵖ` is the
opposite of the differential of the Moore cochain complex of `W`. -/
private lemma alternatingFaceMapComplex_op_d (W : CosimplicialObject A) (n : ℕ) :
    ((alternatingFaceMapComplex Aᵒᵖ).obj (Functor.op W)).d (n + 1) n =
      (AlternatingCofaceMapComplex.objD W n).op := by
  rw [alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD,
    AlternatingCofaceMapComplex.objD, op_sum]
  rfl

section

variable {a b : U ⟶ V}
  (H : _root_.Homotopy ((alternatingFaceMapComplex Aᵒᵖ).map (NatTrans.op a))
    ((alternatingFaceMapComplex Aᵒᵖ).map (NatTrans.op b)))

/-- The component from degree `p` to degree `q` given by the unop of the component of the chain
homotopy `H` from degree `q` to degree `p`. -/
private def homUnop (p q : ℕ) :
    ((alternatingCofaceMapComplex A).obj U).X p ⟶ ((alternatingCofaceMapComplex A).obj V).X q :=
  (H.hom q p).unop

private lemma op_dNext_homUnop (n : ℕ) : (dNext n (homUnop H)).op = prevD n H.hom := by
  rw [dNext_eq _ (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl),
    prevD_eq _ (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl), op_comp,
    alternatingFaceMapComplex_op_d, alternatingCofaceMapComplex_obj_d]
  rfl

private lemma op_prevD_homUnop (n : ℕ) : (prevD n (homUnop H)).op = dNext n H.hom := by
  cases n with
  | zero =>
    rw [prevD_eq_zero _ 0 (by simp), dNext_eq_zero _ 0 (by simp), op_zero]
    rfl
  | succ n =>
    rw [prevD_eq _ (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl),
      dNext_eq _ (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl), op_comp,
      alternatingFaceMapComplex_op_d, alternatingCofaceMapComplex_obj_d]
    rfl

private lemma op_dNext_add_prevD_homUnop (n : ℕ) :
    (dNext n (homUnop H) + prevD n (homUnop H)).op = dNext n H.hom + prevD n H.hom := by
  rw [op_add, op_dNext_homUnop, op_prevD_homUnop]
  exact add_comm _ _

/-- A chain homotopy between the maps of Moore complexes in `Aᵒᵖ` induced by `a` and `b` is
a cochain homotopy between the maps `s(a)`, `s(b)` of Moore cochain complexes in `A`. -/
private def homotopyUnop :
    _root_.Homotopy ((alternatingCofaceMapComplex A).map a)
      ((alternatingCofaceMapComplex A).map b) where
  hom := homUnop H
  zero p q hpq := by
    rw [homUnop, H.zero q p hpq, unop_zero]
    rfl
  comm n := Quiver.Hom.op_inj <| by
    rw [op_add, op_dNext_add_prevD_homUnop]
    exact H.comm n

end

end

namespace AlgebraicTopology

variable {A : Type u} [Category.{v} A] [Preadditive A] {U V : CosimplicialObject A}
  {a b : U ⟶ V}

/-- **Stacks 01A0**.
The Moore cochain complex functor carries homotopic morphisms to homotopic maps of cochain
complexes. Let `a, b : U ⟶ V` be homotopic morphisms of cosimplicial objects of a preadditive
category `A`: related by a chain of morphisms consecutive members of which admit a homotopy in one
direction or the other, a homotopy from `a` to `b` being a family of morphisms `h_{n, α} : Uₙ ⟶ Vₙ`
indexed by the simplices `α ∈ Δ[1]ₙ` with `h_{m, α} ∘ U(g) = V(g) ∘ h_{n, α ∘ g}` for every
morphism `g : ⦋n⦌ ⟶ ⦋m⦌` of `Δ`, whose components at the constant maps `⦋n⦌ ⟶ ⦋1⦌` with values `0`
and `1` are `a_n` and `b_n` ([Stacks, Tag 0FKJ]). Then the induced maps `s(a), s(b) : s(U) ⟶ s(V)`
of Moore cochain complexes are chain homotopic. -/
@[stacks 01A0 "the first assertion, for the Moore cochain complex `s`, with the source's \
  additive `A` weakened to preadditive, which is all `s` uses; the second, for the \
  normalized cochain complex `Q` of 019I, is `homotopic_normalizedCochainComplex_map`. A \
  homotopy is given by its family of components as in 0FKJ and 07KB, which needs no \
  products in `A`, and being homotopic is spelled `Relation.EqvGen` of the existence of \
  such a family, as in 019S",
  sga "4 XVII 5.5.3" "homotopy preservation"]
public theorem homotopic_alternatingCofaceMapComplex_map
    (h : Relation.EqvGen
      (fun a b : U ⟶ V => ∃ h : ∀ n : SimplexCategory, (Δ[1] : SSet.{0}).obj (op n) →
          (U.obj n ⟶ V.obj n),
        (∀ ⦃n m : SimplexCategory⦄ (g : n ⟶ m) (α : (Δ[1] : SSet.{0}).obj (op m)),
            U.map g ≫ h m α = h n ((Δ[1] : SSet.{0}).map g.op α) ≫ V.map g) ∧
          (∀ n : SimplexCategory, h n (stdSimplex.const 1 0 (op n)) = a.app n) ∧
          (∀ n : SimplexCategory, h n (stdSimplex.const 1 1 (op n)) = b.app n)) a b) :
    homotopic A (ComplexShape.up ℕ) ((alternatingCofaceMapComplex A).map a)
      ((alternatingCofaceMapComplex A).map b) := by
  induction h with
  | rel x y hxy =>
      obtain ⟨hh, hnat, hx, hy⟩ := hxy
      exact ⟨homotopyUnop (toSimplicialObjectHomotopy hh hnat hx hy).toChainHomotopy⟩
  | refl x => exact (homotopy_congruence A _).equivalence.refl _
  | symm x y _ ih => exact (homotopy_congruence A _).equivalence.symm ih
  | trans _ _ _ _ _ ih ih' => exact (homotopy_congruence A _).equivalence.trans ih ih'

end AlgebraicTopology

end MooreCochainComplex

/-! ### The Moore cochain complex of a homotopy equivalence of cosimplicial objects -/

section MooreCochainComplexHomotopyEquivalence

open CategoryTheory CategoryTheory.Limits Opposite Simplicial SSet AlgebraicTopology

/-- **A composite homotopic to an identity has chain homotopic Moore cochain complexes.**
If `a ≫ b : U ⟶ U` is homotopic to `𝟙 U`, for `a : U ⟶ V` and `b : V ⟶ U` morphisms of cosimplicial
objects of a preadditive category, then `s(a) ≫ s(b)` is chain homotopic to `𝟙 s(U)`. -/
private theorem homotopic_alternatingCofaceMapComplex_map_comp_id {A : Type u}
    [Category.{v} A] [Preadditive A] {U V : CosimplicialObject A} (a : U ⟶ V) (b : V ⟶ U)
    (h : Relation.EqvGen (fun f₁ f₂ : U ⟶ U => ∃ h : ∀ n : SimplexCategory,
        (Δ[1] : SSet.{0}).obj (op n) → (U.obj n ⟶ U.obj n),
      (∀ ⦃n m : SimplexCategory⦄ (u : n ⟶ m) (α : (Δ[1] : SSet.{0}).obj (op m)),
          U.map u ≫ h m α = h n ((Δ[1] : SSet.{0}).map u.op α) ≫ U.map u) ∧
        (∀ n : SimplexCategory, h n (stdSimplex.const 1 0 (op n)) = f₁.app n) ∧
        (∀ n : SimplexCategory, h n (stdSimplex.const 1 1 (op n)) = f₂.app n))
      (a ≫ b) (𝟙 U)) :
    homotopic A (ComplexShape.up ℕ)
      ((alternatingCofaceMapComplex A).map a ≫ (alternatingCofaceMapComplex A).map b)
      (𝟙 ((alternatingCofaceMapComplex A).obj U)) := by
  simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using
    homotopic_alternatingCofaceMapComplex_map h

namespace AlgebraicTopology

variable {A : Type u} [Category.{v} A] [Preadditive A] {U V : CosimplicialObject A}
  {a : U ⟶ V}

/-- The Moore cochain complex of a homotopy equivalence of cosimplicial objects is a homotopy
equivalence of cochain complexes. Let `a : U ⟶ V` be a homotopy equivalence of cosimplicial objects
of a preadditive category `A`: there is `b : V ⟶ U` such that `a ≫ b` is homotopic to `𝟙 U` and
`b ≫ a` is homotopic to `𝟙 V`, where two morphisms `f`, `g` of cosimplicial objects are *homotopic*
when they are related by the equivalence relation generated by the existence of a homotopy from one
to the other, a homotopy being a family of morphisms `h_{n, α}` indexed by the simplices
`α ∈ Δ[1]ₙ` with `h_{m, α} ∘ U(u) = V(u) ∘ h_{n, α ∘ u}` for every morphism `u : ⦋n⦌ ⟶ ⦋m⦌` of `Δ`
whose components at the constant maps `⦋n⦌ ⟶ ⦋1⦌` with values `0` and `1` are `f_n` and `g_n`
([Stacks, Tag 0FKJ]). Then `s(a) : s(U) ⟶ s(V)` is a homotopy equivalence of cochain complexes.
This is the assertion for `s` of [Stacks, Tag 0FKK], which is registered on
`homotopyEquivalences_moore_and_normalizedCochainComplex_map` together with the assertion for the
normalized cochain complex `Q`. -/
public theorem homotopyEquivalences_alternatingCofaceMapComplex_map
    (ha : ∃ b : V ⟶ U,
      Relation.EqvGen (fun f₁ f₂ : U ⟶ U => ∃ h : ∀ n : SimplexCategory,
          (Δ[1] : SSet.{0}).obj (op n) → (U.obj n ⟶ U.obj n),
        (∀ ⦃n m : SimplexCategory⦄ (u : n ⟶ m) (α : (Δ[1] : SSet.{0}).obj (op m)),
            U.map u ≫ h m α = h n ((Δ[1] : SSet.{0}).map u.op α) ≫ U.map u) ∧
          (∀ n : SimplexCategory, h n (stdSimplex.const 1 0 (op n)) = f₁.app n) ∧
          (∀ n : SimplexCategory, h n (stdSimplex.const 1 1 (op n)) = f₂.app n))
        (a ≫ b) (𝟙 U) ∧
      Relation.EqvGen (fun f₁ f₂ : V ⟶ V => ∃ h : ∀ n : SimplexCategory,
          (Δ[1] : SSet.{0}).obj (op n) → (V.obj n ⟶ V.obj n),
        (∀ ⦃n m : SimplexCategory⦄ (u : n ⟶ m) (α : (Δ[1] : SSet.{0}).obj (op m)),
            V.map u ≫ h m α = h n ((Δ[1] : SSet.{0}).map u.op α) ≫ V.map u) ∧
          (∀ n : SimplexCategory, h n (stdSimplex.const 1 0 (op n)) = f₁.app n) ∧
          (∀ n : SimplexCategory, h n (stdSimplex.const 1 1 (op n)) = f₂.app n))
        (b ≫ a) (𝟙 V)) :
    HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℕ)
      ((alternatingCofaceMapComplex A).map a) :=
  let ⟨b, hab, hba⟩ := ha
  ⟨{ hom := (alternatingCofaceMapComplex A).map a
     inv := (alternatingCofaceMapComplex A).map b
     homotopyHomInvId := (homotopic_alternatingCofaceMapComplex_map_comp_id a b hab).some
     homotopyInvHomId := (homotopic_alternatingCofaceMapComplex_map_comp_id b a hba).some },
    rfl⟩

end AlgebraicTopology

end MooreCochainComplexHomotopyEquivalence

end

end

/-!
## Homotopies of morphisms of cosimplicial objects

Let `C` be a category with finite products, let `U` and `V` be cosimplicial objects of `C`, i.e.
functors `Δ ⥤ C`, and let `a, b : U ⟶ V`. The cosimplicial object `Hom(Δ[1], V)` of
[Stacks, Tag 019V] comes with two morphisms `e₀, e₁ : Hom(Δ[1], V) ⟶ V` induced by the two vertices
`Δ[0] ⟶ Δ[1]`: in degree `n` they are the projections of `Hom(Δ[1], V)_n = ∏_{α ∈ Δ[1]_n} V_n` onto
the factors indexed by the two constant maps `[n] → [1]`. A *homotopy from `a` to `b`* is a
morphism `h : U ⟶ Hom(Δ[1], V)` with `a = e₀ ∘ h` and `b = e₁ ∘ h`; equivalently, a family of
morphisms `h_{n, α} : U_n ⟶ V_n`, one for each `α ∈ Δ[1]_n`, compatible with the structure maps and
with `a_n = h_{n, 0}`, `b_n = h_{n, 1}`. This is the notion dual to a homotopy of simplicial
objects, which is a morphism `U × Δ[1] ⟶ V` on the other side ([Stacks, Tag 019K]).

Homotopy is reflexive but neither symmetric nor transitive, so *homotopic* means related by the
equivalence relation it generates: `a` and `b` are homotopic when there is a chain
`a = a₀, a₁, …, a_n = b` in which consecutive terms admit a homotopy in one direction or the other.

### Main definitions

* `CategoryTheory.CosimplicialObject.Homotopy a b`: the type of homotopies from `a` to `b`, part
  (1) of [Stacks, Tag 019W].

### References

* [Stacks, Tag 019W](https://stacks.math.columbia.edu/tag/019W)
-/

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe v u

namespace CategoryTheory.CosimplicialObject

variable {C : Type u} [Category.{v} C] {U V : CosimplicialObject C}
  [∀ n : SimplexCategory, HasProduct fun _ : (Δ[1] : SSet.{0}).obj (op n) => V.obj n]

/-- **Stacks 019W**.
A *homotopy from `a` to `b`*, for `a b : U ⟶ V` two morphisms of cosimplicial objects of `C`: a
morphism `h : U ⟶ Hom(Δ[1], V)` into the cosimplicial object `Hom(Δ[1], V) = V.power Δ[1]` of
[Stacks, Tag 019V] such that `a = e₀ ∘ h` and `b = e₁ ∘ h`, where `e₀, e₁ : Hom(Δ[1], V) ⟶ V` are
induced by the two vertices of `Δ[1]`. The two conditions are recorded in each degree `n`, where
`e₀` and `e₁` are the projections of `Hom(Δ[1], V)_n = ∏_{α ∈ Δ[1]_n} V_n` onto the factors indexed
by the constant maps `[n] → [1]` with value `0`, resp. `1`; so the components
`h_{n, α} : U_n ⟶ V_n` of `h` satisfy `a_n = h_{n, 0}` and `b_n = h_{n, 1}`, and the naturality of
`h` is the compatibility of the `h_{n, α}` with the structure maps. -/
@[stacks 019W "the finite products of the source are replaced by the products that name \
  `Hom(Δ[1], V)`; the two conditions `a = e₀ ∘ h`, `b = e₁ ∘ h` are recorded degreewise, \
  `e₀` and `e₁` being pinned there to the two projections; part (2), homotopic, is \
  `Relation.EqvGen fun a b => Nonempty (Homotopy a b)`",
  sga "4 Vbis 3.0.2.2" "Dual form, special case"]
public structure Homotopy (a b : U ⟶ V) : Type v where
  /-- The morphism `h : U ⟶ Hom(Δ[1], V)` underlying the homotopy. -/
  h : U ⟶ V.power Δ[1]
  /-- `a = e₀ ∘ h`: in degree `n`, the component of `h` at the constant map `0 : [n] → [1]` is
  `a_n`. -/
  h₀ (n : SimplexCategory) :
    h.app n ≫ Pi.π _ (SSet.stdSimplex.const 1 0 (op n)) = a.app n
  /-- `b = e₁ ∘ h`: in degree `n`, the component of `h` at the constant map `1 : [n] → [1]` is
  `b_n`. -/
  h₁ (n : SimplexCategory) :
    h.app n ≫ Pi.π _ (SSet.stdSimplex.const 1 1 (op n)) = b.app n

end CategoryTheory.CosimplicialObject

end

end

/-!
## Degreewise description of morphisms into `Hom(K, V)`

Let `C` be a category, let `U`, `V` be cosimplicial objects of `C` (functors `Δ ⥤ C`) and let
`K` be a simplicial set for which the cosimplicial object `Hom(K, V)` of [Stacks, Tag 019V]
exists, so `Hom(K, V)_n = ∏_{α ∈ K_n} V_n`. A morphism `H : U ⟶ Hom(K, V)` of cosimplicial
objects amounts, in degree `n`, to a family of morphisms `h_{n, α} : U_n ⟶ V_n` indexed by
`α ∈ K_n`, namely `H_n = ∏_{α ∈ K_n} h_{n, α}`, and the naturality of `H` says exactly that
for every morphism `f : [n] → [m]` of `Δ` and every `α ∈ K_m`
```
h_{m, α} ∘ U(f) = V(f) ∘ h_{n, α ∘ f},
```
where `α ∘ f = K(f)(α) ∈ K_n`. For `K = Δ[1]` this is the compatibility satisfied by the
components of a homotopy of cosimplicial objects ([Stacks, Tag 019W]) and, conversely, the
condition under which a family `{h_{n, α}}` assembles into one; it is the equation by which the
notion of homotopy over an arbitrary category ([Stacks, Tag 0FKJ]) is defined.

### Main results

* `CategoryTheory.CosimplicialObject.exists_hom_power_iff`: a family of morphisms
  `h_{n, α} : U_n ⟶ V_n`, `α ∈ K_n`, is the family of components of a morphism
  `U ⟶ Hom(K, V)` if and only if it satisfies the displayed equation for every morphism `f`
  of `Δ`.

### References

* [Stacks, Tag 07KB](https://stacks.math.columbia.edu/tag/07KB)
-/

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe w v u v' u'

namespace CategoryTheory.CosimplicialObject

section

variable {C : Type u} [Category.{v} C]

/-- Given functors `F`, `G : D ⥤ C` and a family of morphisms `app X : F.obj X ⟶ G.obj X`, there is
a natural transformation `F ⟶ G` with components `app` if and only if
`F(f) ∘ app X = app Y ∘ G(f)` for every morphism `f : X ⟶ Y` of `D`. -/
private lemma exists_natTrans_app_eq_iff {D : Type u'} [Category.{v'} D] {F G : D ⥤ C}
    (app : ∀ X : D, F.obj X ⟶ G.obj X) :
    (∃ θ : F ⟶ G, ∀ X, θ.app X = app X) ↔
      ∀ ⦃X Y : D⦄ (f : X ⟶ Y), F.map f ≫ app Y = app X ≫ G.map f :=
  ⟨fun ⟨θ, hθ⟩ => funext hθ ▸ θ.naturality,
    fun hf => ⟨{ app := app, naturality := fun _ _ f => hf f }, fun _ => rfl⟩⟩

/-- For a family of morphisms `g_β : X ⟶ V_n` indexed by the simplices `β ∈ K_n` of a simplicial
set `K` and a morphism `f : [n] ⟶ [m]` of `Δ`, the `α`-th component of
`(∏_{β ∈ K_n} g_β) ∘ Hom(K, V)(f)` at a simplex `α ∈ K_m` is `V(f) ∘ g_{α ∘ f}`, where
`α ∘ f = K(f)(α)`. -/
private lemma lift_comp_power_map_π (V : CosimplicialObject C) (K : SSet.{w})
    [∀ n : SimplexCategory, HasProduct fun _ : K.obj (op n) => V.obj n] {X : C}
    {n m : SimplexCategory} (g : ∀ _ : K.obj (op n), X ⟶ V.obj n) (f : n ⟶ m)
    (α : K.obj (op m)) :
    Pi.lift g ≫ (V.power K).map f ≫ Pi.π (fun _ : K.obj (op m) => V.obj m) α
      = g (K.map f.op α) ≫ V.map f :=
  (whisker_eq _ (power_map_π V K f α)).trans (Pi.lift_comp_π_assoc ..)

end

variable {C : Type u} [Category.{v} C] {U V : CosimplicialObject C} {K : SSet.{w}}
  [∀ n : SimplexCategory, HasProduct fun _ : K.obj (op n) => V.obj n]

/-- For a family of morphisms `h_{n, α} : U_n ⟶ V_n` indexed by the simplices of a simplicial set
`K` and a morphism `f : [n] ⟶ [m]` of `Δ`, the square
`U(f) ∘ ∏_{α ∈ K_m} h_{m, α} = (∏_{α ∈ K_n} h_{n, α}) ∘ Hom(K, V)(f)` commutes if and only if
`h_{m, α} ∘ U(f) = V(f) ∘ h_{n, α ∘ f}` for every `α ∈ K_m`, where `α ∘ f = K(f)(α)`. -/
private lemma naturality_iff (h : ∀ n : SimplexCategory, K.obj (op n) → (U.obj n ⟶ V.obj n))
    {n m : SimplexCategory} (f : n ⟶ m) :
    U.map f ≫ Pi.lift (h m) = Pi.lift (h n) ≫ (V.power K).map f ↔
      ∀ α : K.obj (op m), U.map f ≫ h m α = h n (K.map f.op α) ≫ V.map f :=
  Pi.hom_ext_iff.trans <| forall_congr' fun α =>
    Eq.congr ((Category.assoc ..).trans (whisker_eq _ (Pi.lift_comp_π ..)))
      ((Category.assoc ..).trans (lift_comp_power_map_π V K (h n) f α))

/-- **Stacks 07KB**.
A family of morphisms `h_{n, α} : U_n ⟶ V_n` of `C`, indexed by the simplices `α ∈ K_n` of a
simplicial set `K`, is the family of components of a morphism `H : U ⟶ Hom(K, V)` of cosimplicial
objects, with `H_n = ∏_{α ∈ K_n} h_{n, α}`, if and only if `h_{m, α} ∘ U(f) = V(f) ∘ h_{n, α ∘ f}`
for every morphism `f : [n] → [m]` of `Δ` and every `α ∈ K_m`, where `α ∘ f = K(f)(α)`. -/
@[stacks 07KB "stated for an arbitrary simplicial set `K` in place of `Δ[1]`, and as the \
  criterion characterising the families of morphisms that assemble into a morphism \
  `U ⟶ Hom(K, V)`, which is what the source's paragraph asserts in both directions"]
public theorem exists_hom_power_iff
    (h : ∀ n : SimplexCategory, K.obj (op n) → (U.obj n ⟶ V.obj n)) :
    (∃ H : U ⟶ V.power K, ∀ n, H.app n = Pi.lift (h n)) ↔
      ∀ ⦃n m : SimplexCategory⦄ (f : n ⟶ m) (α : K.obj (op m)),
        U.map f ≫ h m α = h n (K.map f.op α) ≫ V.map f :=
  (exists_natTrans_app_eq_iff _).trans <|
    forall₂_congr fun _ _ => forall_congr' (naturality_iff h)

end CategoryTheory.CosimplicialObject

end

end

/-!
## Homotopies of morphisms of cosimplicial objects over an arbitrary category

Let `C` be a category, with no assumptions whatsoever, let `U` and `V` be cosimplicial objects
of `C`, i.e. functors `Δ ⥤ C`, and let `a, b : U ⟶ V`. A *homotopy from `a` to `b`* is a family
of morphisms `h_{n, α} : U_n ⟶ V_n` of `C`, one for each `n ≥ 0` and each simplex `α ∈ Δ[1]_n`,
such that
```
h_{m, α} ∘ U(f) = V(f) ∘ h_{n, α ∘ f}
```
for every morphism `f : ⦋n⦌ ⟶ ⦋m⦌` of `Δ` and every `α ∈ Δ[1]_m` ([Stacks, Tag 07KB]), and
such that `a_n = h_{n, 0}` and `b_n = h_{n, 1}`, where `0, 1 : ⦋n⦌ ⟶ ⦋1⦌` are the two constant
maps. Two morphisms are *homotopic* when they are related by the equivalence relation generated
by the existence of a homotopy, that is, when there is a chain `a = a₀, a₁, …, a_n = b` in which
each step carries a homotopy in one direction or the other.

This notion needs no products in `C`. When the products `∏_{α ∈ Δ[1]_n} V_n` naming
`Hom(Δ[1], V)` do exist — in particular when `C` has finite products, each `Δ[1]_n` being finite
— it agrees with the notion of [Stacks, Tag 019W], a morphism `h : U ⟶ Hom(Δ[1], V)` with
`a = e₀ ∘ h` and `b = e₁ ∘ h`: a family as above is exactly the family of components
`h_{n, α} = h_n ≫ π_α` of such a morphism, and conversely such a family assembles into one by
`h_n = ∏_{α ∈ Δ[1]_n} h_{n, α}`. That agreement is the result stated here.

### Main results

* `CategoryTheory.CosimplicialObject.exists_homotopy_iff`: a family of morphisms
  `h_{n, α} : U_n ⟶ V_n`, `α ∈ Δ[1]_n`, is the family of components of a homotopy from `a` to
  `b` in the sense of [Stacks, Tag 019W] if and only if it satisfies the relation of
  [Stacks, Tag 07KB] and has `a_n` and `b_n` as its components at the two constant maps
  `⦋n⦌ ⟶ ⦋1⦌`, i.e. if and only if it is a homotopy from `a` to `b` in the sense of
  [Stacks, Tag 0FKJ].

### References

* [Stacks, Tag 0FKJ](https://stacks.math.columbia.edu/tag/0FKJ)
-/

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial SSet

universe v u

namespace CategoryTheory.CosimplicialObject

variable {C : Type u} [Category.{v} C] {U V : CosimplicialObject C}
  [∀ n : SimplexCategory, HasProduct fun _ : (Δ[1] : SSet.{0}).obj (op n) => V.obj n]

/-- Let `H_n = ∏_{α ∈ Δ[1]_n} h_{n, α}` and let `i` be a vertex of `Δ[1]`. The component of `H_n`
at the constant simplex `i : ⦋n⦌ ⟶ ⦋1⦌` is `h_{n, i}`, so `H` has prescribed components
`g_n : U_n ⟶ V_n` at those constant simplices if and only if `h_{n, i} = g_n` for every `n`. -/
private lemma forall_app_π_const_iff {H : U ⟶ V.power Δ[1]}
    {h : ∀ n : SimplexCategory, (Δ[1] : SSet.{0}).obj (op n) → (U.obj n ⟶ V.obj n)}
    (hH : ∀ n, H.app n = Pi.lift (h n)) (i : Fin 2)
    (g : ∀ n : SimplexCategory, U.obj n ⟶ V.obj n) :
    (∀ n : SimplexCategory, H.app n ≫ Pi.π _ (stdSimplex.const 1 i (op n)) = g n) ↔
      ∀ n : SimplexCategory, h n (stdSimplex.const 1 i (op n)) = g n :=
  forall_congr' fun n => Eq.congr_left ((hH n) ▸ Pi.lift_comp_π ..)

/-- **Stacks 0FKJ**.
A *homotopy from `a` to `b`*, for `a b : U ⟶ V` morphisms of cosimplicial objects of a category `C`
with no assumptions whatsoever, is a family of morphisms `h_{n, α} : U_n ⟶ V_n` indexed by the
objects `⦋n⦌` of `Δ` and the simplices `α ∈ Δ[1]_n`, satisfying
`h_{m, α} ∘ U(f) = V(f) ∘ h_{n, α ∘ f}` for every morphism `f : ⦋n⦌ ⟶ ⦋m⦌` of `Δ`
([Stacks, Tag 07KB]) and having `a_n` and `b_n` as its components at the two constant maps
`⦋n⦌ ⟶ ⦋1⦌`, with value `0` resp. `1`. This notion agrees with the one of [Stacks, Tag 019W], which
needs the products `∏_{α ∈ Δ[1]_n} V_n` naming `Hom(Δ[1], V)`: whenever those exist, a family is a
homotopy in the above sense if and only if it is the family of components of a homotopy
`h : U ⟶ Hom(Δ[1], V)` from `a` to `b`, with `h_n = ∏_{α ∈ Δ[1]_n} h_{n, α}`. -/
@[stacks 0FKJ "the remark's comparison of its notion with the one of 019W, \
  `this new notion is the same as the old one in case finite products exist`, stated for a \
  given family and with the correspondence pinned degreewise to \
  `h_n = ∏_α h_{n, α}`; the finite products of 019W are weakened to the products naming \
  `Hom(Δ[1], V)`, and the right hand side, which needs no products, is the remark's \
  definition, in the form its dependents use. Part (2), homotopic, is `Relation.EqvGen` of \
  the existence of such a family, as in 019W and 019S; the remark's functoriality \
  assertions are 019Y (2)"]
public theorem exists_homotopy_iff (a b : U ⟶ V)
    (h : ∀ n : SimplexCategory, (Δ[1] : SSet.{0}).obj (op n) → (U.obj n ⟶ V.obj n)) :
    (∃ H : Homotopy a b, ∀ n, H.h.app n = Pi.lift (h n)) ↔
      (∀ ⦃n m : SimplexCategory⦄ (f : n ⟶ m) (α : (Δ[1] : SSet.{0}).obj (op m)),
          U.map f ≫ h m α = h n ((Δ[1] : SSet.{0}).map f.op α) ≫ V.map f) ∧
        (∀ n : SimplexCategory, h n (stdSimplex.const 1 0 (op n)) = a.app n) ∧
        (∀ n : SimplexCategory, h n (stdSimplex.const 1 1 (op n)) = b.app n) :=
  ⟨fun ⟨H, hH⟩ => ⟨(exists_hom_power_iff h).mp ⟨H.h, hH⟩,
      (forall_app_π_const_iff hH 0 a.app).mp H.h₀, (forall_app_π_const_iff hH 1 b.app).mp H.h₁⟩,
    fun ⟨hnat, h₀, h₁⟩ =>
      let ⟨H, hH⟩ := (exists_hom_power_iff h).mpr hnat
      ⟨⟨H, (forall_app_π_const_iff hH 0 a.app).mpr h₀,
        (forall_app_π_const_iff hH 1 b.app).mpr h₁⟩, hH⟩⟩

end CategoryTheory.CosimplicialObject

end

end
