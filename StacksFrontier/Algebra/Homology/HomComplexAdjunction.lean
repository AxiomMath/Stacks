module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.CategoryTheory.Adjunction.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Hom complex across an adjunction

Let `F ⊣ G` be an adjunction of additive functors between preadditive categories. Applying `F`
and `G` degreewise to cochain complexes, the Hom-set bijection of the adjunction upgrades to an
isomorphism of Hom complexes

`Hom^•(F(K), L) ≅ Hom^•(K, G(L))`

for every cochain complex `K` in the source and `L` in the target. In degree `n` it is the
bijection of the adjunction applied to each component of a cochain, and the compatibility with
the differential `CochainComplex.HomComplex.δ` is exactly the two naturality squares of the
adjunction: `Adjunction.homEquiv_naturality_right` for the half of `δ` built from the
differential of `L`, and `Adjunction.homEquiv_naturality_left` for the half built from the
differential of `K`.

## Main definitions

* `CategoryTheory.Adjunction.cochainEquiv`: the bijection of homogeneous cochains in a fixed
  degree, as an isomorphism of additive groups.
* `CategoryTheory.Adjunction.homComplexIso`: **the isomorphism of Hom complexes.**

## Main results

* `CategoryTheory.Adjunction.homComplexIso_hom_apply` and
  `CategoryTheory.Adjunction.homComplexIso_inv_apply`: the isomorphism and its inverse act on a
  cochain componentwise by the Hom-set bijection of the adjunction.

## Implementation notes

The two categories are required to have hom types in the *same* universe, because the Hom
complexes of the two sides are complexes of abelian groups in the universe of the hom types and
an isomorphism between them needs those universes to agree.

Nothing here needs the categories to be abelian: the construction only uses that composition is
additive and that `F` and `G` are additive, so that the Hom-set bijection
`f ↦ unit ≫ G.map f` is additive.
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex.HomComplex

namespace CategoryTheory.Adjunction

universe v u u'

variable {V : Type u} [Category.{v} V] [Preadditive V]
  {W : Type u'} [Category.{v} W] [Preadditive W]
  {F : V ⥤ W} {G : W ⥤ V} [F.Additive] [G.Additive]

/-- The Hom-set bijection of an adjunction `F ⊣ G`, applied componentwise to homogeneous
cochains of degree `n` from `F(K)` to `L`. -/
def cochainEquiv (adj : F ⊣ G) (K : CochainComplex V ℤ) (L : CochainComplex W ℤ) (n : ℤ) :
    Cochain ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) L n ≃+
      Cochain K ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) n where
  toFun z := Cochain.mk fun p q hpq => adj.homEquiv _ _ (z.v p q hpq)
  invFun z := Cochain.mk fun p q hpq => (adj.homEquiv _ _).symm (z.v p q hpq)
  left_inv z := by ext p q hpq; simp
  right_inv z := by ext p q hpq; simp
  map_add' z z' := by ext p q hpq; simp [Adjunction.homEquiv_apply]

/-- The component of `cochainEquiv adj K L n z` at `(p, q)` is the image of the component of `z`
under the Hom-set bijection of `adj`. -/
@[simp]
theorem cochainEquiv_v (adj : F ⊣ G) (K : CochainComplex V ℤ) (L : CochainComplex W ℤ) (n : ℤ)
    (z : Cochain ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) L n)
    (p q : ℤ) (hpq : p + n = q) :
    (cochainEquiv adj K L n z).v p q hpq = adj.homEquiv _ _ (z.v p q hpq) := rfl

/-- The component of `(cochainEquiv adj K L n).symm z` at `(p, q)` is the image of the component
of `z` under the inverse of the Hom-set bijection of `adj`. -/
@[simp]
theorem cochainEquiv_symm_v (adj : F ⊣ G) (K : CochainComplex V ℤ) (L : CochainComplex W ℤ)
    (n : ℤ) (z : Cochain K ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) n)
    (p q : ℤ) (hpq : p + n = q) :
    ((cochainEquiv adj K L n).symm z).v p q hpq = (adj.homEquiv _ _).symm (z.v p q hpq) := rfl

/-- **The Hom complex across an adjunction.** For an adjunction `F ⊣ G` of additive functors
between preadditive categories, a cochain complex `K` in the source of `F` and a cochain complex
`L` in the target, the Hom complex of `F(K)` and `L` is isomorphic to the Hom complex of `K` and
`G(L)`, degreewise by the Hom-set bijection of the adjunction. -/
@[sga "4 XVII 1.1.12" "special case"]
def homComplexIso (adj : F ⊣ G) (K : CochainComplex V ℤ) (L : CochainComplex W ℤ) :
    CochainComplex.HomComplex ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) L ≅
      CochainComplex.HomComplex K ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n => (cochainEquiv adj K L n).toAddCommGrpIso) ?_
  intro n m hnm
  ext z
  change δ n m (cochainEquiv adj K L n z) = cochainEquiv adj K L m (δ n m z)
  change n + 1 = m at hnm
  ext p q hpq
  rw [δ_v n m hnm _ p q hpq (q - 1) (p + 1) rfl rfl]
  simp only [cochainEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk, Cochain.mk_v,
    Functor.mapHomologicalComplex_obj_d]
  rw [δ_v n m hnm z p q hpq (q - 1) (p + 1) rfl rfl]
  simp [Adjunction.homEquiv_apply]

/-- The degree `n` component of `(homComplexIso adj K L).hom` sends a cochain `z` to the cochain
whose component at `(p, q)` is the image of that of `z` under the Hom-set bijection of `adj`. -/
@[simp]
theorem homComplexIso_hom_apply (adj : F ⊣ G) (K : CochainComplex V ℤ) (L : CochainComplex W ℤ)
    (n : ℤ) (z : Cochain ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) L n)
    (p q : ℤ) (hpq : p + n = q) :
    (AddCommGrpCat.Hom.hom ((homComplexIso adj K L).hom.f n) z).v p q hpq =
      adj.homEquiv _ _ (z.v p q hpq) := rfl

/-- The degree `n` component of `(homComplexIso adj K L).inv` sends a cochain `z` to the cochain
whose component at `(p, q)` is the image of that of `z` under the inverse of the Hom-set
bijection of `adj`. -/
@[simp]
theorem homComplexIso_inv_apply (adj : F ⊣ G) (K : CochainComplex V ℤ) (L : CochainComplex W ℤ)
    (n : ℤ) (z : Cochain K ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) n)
    (p q : ℤ) (hpq : p + n = q) :
    (AddCommGrpCat.Hom.hom ((homComplexIso adj K L).inv.f n) z).v p q hpq =
      (adj.homEquiv _ _).symm (z.v p q hpq) := rfl

end CategoryTheory.Adjunction

end
