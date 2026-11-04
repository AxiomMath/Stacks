module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorPlainIsoNatural
public import StacksFrontier.Algebra.DifferentialGraded.Module.InverseSystemStrict
public import StacksFrontier.RingTheory.Module.AdicSystem.Homology

/-!
# Towers of derived tensor products over a varying algebra

Let `(B, d)` be a differential graded algebra over a commutative ring `R`. A *derived tensor
tower* over `B` is an inverse system `(A_n)` of differential graded algebras, a differential
graded `(A_n, B)`-bimodule `P_n` and a differential graded `A_n`-module `X_n` for every `n`,
transition homomorphisms `X_{n+1} ⟶ X_n|_{A_{n+1}}`, comparisons
`P_{n+1} ⊗_{A_{n+1}} Y|_{A_{n+1}} ⟶ P_n ⊗_{A_n} Y` of the *plain* tensor functors, and the
requirement that each `X_n` be orthogonal on the left to the acyclic modules. Such data gives a
tower `n ↦ P_n ⊗_{A_n}^𝐋 X_n` in `D(B, d)` whose transition maps are the derived tensor products
of the transition homomorphisms followed by the comparisons
`DifferentialGraded.Bimodule.derivedTensorRestrictTrans` of the derived tensor functors, and it
also gives a tower `n ↦ P_n ⊗_{A_n} X_n` of differential graded `B`-modules.

The point of the orthogonality is that the second tower computes the first:
`DifferentialGraded.Bimodule.derivedTensorRestrictTrans_towerMap` identifies the derived
transition map with the plain one. Consequently two derived tensor towers whose *plain* towers are
isomorphic are isomorphic as functors `ℕᵒᵖ ⥤ D(B, d)`, hence pro-isomorphic, hence have
isomorphic derived limits. The hypothesis is a commuting ladder of homomorphisms of differential
graded `B`-modules; no compatibility in the derived category is assumed.

## Main definitions

* `DifferentialGraded.Bimodule.DerivedTensorTower`: the data above.
* `DifferentialGraded.Bimodule.DerivedTensorTower.tower`: the tower `n ↦ P_n ⊗_{A_n}^𝐋 X_n` of
  `D(B, d)`.
* `DifferentialGraded.Bimodule.DerivedTensorTower.plainMap`: the transition homomorphism
  `P_{n+1} ⊗_{A_{n+1}} X_{n+1} ⟶ P_n ⊗_{A_n} X_n` of the plain tower.

## Main results

* `DifferentialGraded.Bimodule.DerivedTensorTower.towerMap_objIsoPlain`: the transition map of
  the derived tower, read through the identifications with the plain tensor products, is the
  transition homomorphism of the plain tower.
* `DifferentialGraded.Bimodule.DerivedTensorTower.towerNatIso`: an isomorphism of the plain towers
  gives an isomorphism of the derived towers, as functors `ℕᵒᵖ ⥤ D(B, d)`.
* `DifferentialGraded.Bimodule.DerivedTensorTower.towerProIso` and
  `DifferentialGraded.Bimodule.DerivedTensorTower.nonempty_iso_of_isDerivedLimit`: the two derived
  towers are pro-isomorphic, and their derived limits are isomorphic.

## Implementation notes

*The indexing is by one-step maps.* An inverse system indexed by `ℕ` is pinned by its one-step
transition maps, and `CategoryTheory.Functor.ofOpSequence` builds the functor out of them; the
naturality of a transformation between two such functors is likewise only required on the
one-step maps, by `CategoryTheory.NatTrans.ofOpSequence`. The data therefore records only the
one-step transitions.

*What the tower is not.* No composition law is asked of the transition homomorphisms of the
algebras or of the modules, and no identification of a two-step restriction of scalars with a
one-step one is used: nothing below composes two transitions.

*Why the comparison of the plain functors is data and the derived one is not.* A comparison of
the plain tensor functors is a natural transformation of functors between categories of
differential graded modules, and giving one is giving homomorphisms of differential graded
modules. The derived comparison is then constructed from it by
`DifferentialGraded.Bimodule.derivedTensorRestrictTrans`, together with the compatibility with
the plain tensor products that the isomorphism of towers needs.

## References

* [Stacks Project, Tag 09LS](https://stacks.math.columbia.edu/tag/09LS) is the derived tensor
  product, [Tag 0BZ2](https://stacks.math.columbia.edu/tag/0BZ2) its comparison with the plain
  tensor product, [Tag 09KM](https://stacks.math.columbia.edu/tag/09KM) the orthogonality under
  which that comparison is invertible and
  [Tag 0H9L](https://stacks.math.columbia.edu/tag/0H9L) the comparison of the derived limits of
  pro-isomorphic inverse systems.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/- This file is stated against the admissible-sequence pretriangulated structure of Tag 09KH,
which is not an instance; it is activated here explicitly. -/
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule

variable {R : Type u} [CommRing R]

/-- **A tower of derived tensor products over a varying algebra.** The `n`-th term is
`P_n ⊗_{A_n}^𝐋 X_n`, an object of `D(B, d)`; the transition maps are built from the transition
homomorphisms `X_{n+1} ⟶ X_n|_{A_{n+1}}` of the modules and the comparisons
`P_{n+1} ⊗_{A_{n+1}} (-)|_{A_{n+1}} ⟶ P_n ⊗_{A_n} -` of the plain tensor functors. Each module is
required to be orthogonal on the left to the acyclic modules, so that each term is computed by
the plain tensor product. -/
structure DerivedTensorTower (B : DifferentialGradedAlgebra.{u, u} R) where
  /-- The `n`-th differential graded algebra of the system. -/
  alg : ℕ → DifferentialGradedAlgebra.{u, u} R
  /-- The transition homomorphism `A_{n+1} ⟶ A_n`. -/
  trans : ∀ n : ℕ, (alg (n + 1)).Hom (alg n)
  /-- The differential graded `(A_n, B)`-bimodule `P_n` that is tensored with. -/
  bimod : ∀ n : ℕ, Bimodule (alg n) B
  /-- The differential graded `A_n`-module `X_n`. -/
  mod : ∀ n : ℕ, DifferentialGradedModule.{u, u, u} (alg n)
  /-- The transition homomorphism `X_{n+1} ⟶ X_n|_{A_{n+1}}` of the modules. -/
  modTrans : ∀ n : ℕ, mod (n + 1) ⟶ restrictScalars (trans n) (mod n)
  /-- The comparison `P_{n+1} ⊗_{A_{n+1}} Y|_{A_{n+1}} ⟶ P_n ⊗_{A_n} Y` of the plain tensor
  functors, natural in the differential graded `A_n`-module `Y`. -/
  plainCmp : ∀ n : ℕ,
    restrictScalarsFunctor (trans n) ⋙ tensorCompFunctor (bimod (n + 1)) ⟶
      tensorCompFunctor (bimod n)
  /-- Each module is orthogonal on the left to the acyclic modules, so that its derived tensor
  product with `P_n` is computed by the plain one. -/
  leftOrthogonal : ∀ n : ℕ,
    (acyclic' (alg n)).leftOrthogonal ((toHomotopyCategory (alg n)).obj (mod n))

namespace DerivedTensorTower

variable {B : DifferentialGradedAlgebra.{u, u} R} (T : DerivedTensorTower B)

/-- The `n`-th term `P_n ⊗_{A_n}^𝐋 X_n` of the derived tower. -/
abbrev obj (n : ℕ) : derivedCategory' B :=
  (derivedTensorFunctor (T.bimod n)).obj
    ((quasiIsomorphisms' (T.alg n)).Q.obj ((toHomotopyCategory (T.alg n)).obj (T.mod n)))

/-- The `n`-th term `P_n ⊗_{A_n} X_n` of the plain tower, a differential graded `B`-module. -/
abbrev plainObj (n : ℕ) : DifferentialGradedModule.{u, u, u} B :=
  tensorObj (T.bimod n) (T.mod n)

/-- The transition homomorphism `P_{n+1} ⊗_{A_{n+1}} X_{n+1} ⟶ P_n ⊗_{A_n} X_n` of the plain
tower: tensor the transition homomorphism of the modules, then compare the plain tensor
functors. -/
def plainMap (n : ℕ) : T.plainObj (n + 1) ⟶ T.plainObj n :=
  (tensorCompFunctor (T.bimod (n + 1))).map (T.modTrans n) ≫ (T.plainCmp n).app (T.mod n)

/-- The transition map `P_{n+1} ⊗_{A_{n+1}}^𝐋 X_{n+1} ⟶ P_n ⊗_{A_n}^𝐋 X_n` of the derived tower:
the derived tensor product of the transition homomorphism of the modules, then the comparison
`DifferentialGraded.Bimodule.derivedTensorRestrictTrans` of the derived tensor functors. -/
def towerMap (n : ℕ) : T.obj (n + 1) ⟶ T.obj n :=
  (derivedTensorFunctor (T.bimod (n + 1))).map (derivedTrans (T.trans n) (T.modTrans n)) ≫
    (derivedTensorRestrictTrans (T.trans n) (T.bimod (n + 1)) (T.bimod n) (T.plainCmp n)).app
      ((quasiIsomorphisms' (T.alg n)).Q.obj ((toHomotopyCategory (T.alg n)).obj (T.mod n)))

/-- **The derived tower** `n ↦ P_n ⊗_{A_n}^𝐋 X_n`, an inverse system in `D(B, d)`. -/
def tower : ℕᵒᵖ ⥤ derivedCategory' B := Functor.ofOpSequence T.towerMap

/-- The terms of the derived tower are the derived tensor products. -/
@[simp] theorem tower_obj (n : ℕ) : T.tower.obj (op n) = T.obj n := rfl

/-- The one-step transition map of the derived tower is
`DifferentialGraded.Bimodule.DerivedTensorTower.towerMap`. -/
@[simp] theorem tower_map_succ (n : ℕ) :
    T.tower.map (homOfLE (Nat.le_add_right n 1)).op = T.towerMap n :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- The identification of the `n`-th term of the derived tower with the `n`-th term of the plain
tower, which is `DifferentialGraded.Bimodule.derivedTensorObjIsoPlain` at the module `X_n`. -/
def objIsoPlain (n : ℕ) :
    T.obj n ≅ (quasiIsomorphisms' B).Q.obj ((toHomotopyCategory B).obj (T.plainObj n)) :=
  derivedTensorObjIsoPlain (T.bimod n) (T.mod n) (T.leftOrthogonal n)

/-- **The transition map of the derived tower is the transition homomorphism of the plain
tower.** -/
theorem towerMap_objIsoPlain (n : ℕ) :
    T.towerMap n ≫ (T.objIsoPlain n).hom =
      (T.objIsoPlain (n + 1)).hom ≫
        (quasiIsomorphisms' B).Q.map ((toHomotopyCategory B).map (T.plainMap n)) :=
  derivedTensorRestrictTrans_towerMap (T.trans n) (T.bimod (n + 1)) (T.bimod n) (T.plainCmp n)
    (T.modTrans n) _ rfl (T.leftOrthogonal (n + 1)) (T.leftOrthogonal n)

/-! ### Two towers with isomorphic plain towers -/

variable (T₁ T₂ : DerivedTensorTower B) (e : ∀ n : ℕ, T₁.plainObj n ≅ T₂.plainObj n)
  (he : ∀ n : ℕ, T₁.plainMap n ≫ (e n).hom = (e (n + 1)).hom ≫ T₂.plainMap n)

/-- The isomorphism `P_n ⊗_{A_n}^𝐋 X_n ≅ P'_n ⊗_{A'_n}^𝐋 X'_n` of the `n`-th terms of two derived
towers induced by an isomorphism of the `n`-th terms of their plain towers. -/
def objIso (n : ℕ) : T₁.obj n ≅ T₂.obj n :=
  derivedTensorObjIsoOfTensorIso (T₁.bimod n) (T₂.bimod n) (T₁.mod n) (T₂.mod n)
    (T₁.leftOrthogonal n) (T₂.leftOrthogonal n) (e n)

/-- The map of the two derived towers induced by an isomorphism of the plain towers. Its
naturality is `DifferentialGraded.Bimodule.derivedTensorObjIsoOfTensorIso_naturality`, and this is
where the commuting ladder of homomorphisms of differential graded `B`-modules is used. -/
def towerNatTrans : T₁.tower ⟶ T₂.tower :=
  NatTrans.ofOpSequence (fun n => (objIso T₁ T₂ e n).hom) fun n => by
    rw [tower_map_succ, tower_map_succ]
    exact derivedTensorObjIsoOfTensorIso_naturality (T₁.trans n) (T₂.trans n)
      (T₁.bimod (n + 1)) (T₁.bimod n) (T₂.bimod (n + 1)) (T₂.bimod n)
      (T₁.plainCmp n) (T₂.plainCmp n) (T₁.modTrans n) (T₂.modTrans n) _ rfl _ rfl
      (T₁.leftOrthogonal (n + 1)) (T₁.leftOrthogonal n) (T₂.leftOrthogonal (n + 1))
      (T₂.leftOrthogonal n) (e (n + 1)) (e n) (he n)

/-- The components of the map of the two derived towers are the isomorphisms
`DifferentialGraded.Bimodule.DerivedTensorTower.objIso`. -/
@[simp] theorem towerNatTrans_app (n : ℕ) :
    (towerNatTrans T₁ T₂ e he).app (op n) = (objIso T₁ T₂ e n).hom :=
  rfl

/-- **An isomorphism of the plain towers gives an isomorphism of the derived towers.** This is the
naturality that an objectwise isomorphism of derived tensor products does not provide: the two
towers are isomorphic as functors `ℕᵒᵖ ⥤ D(B, d)`, not merely termwise. -/
def towerNatIso : T₁.tower ≅ T₂.tower := by
  have h : ∀ X : ℕᵒᵖ, IsIso ((towerNatTrans T₁ T₂ e he).app X) := fun X => by
    change IsIso (objIso T₁ T₂ e X.unop).hom
    infer_instance
  have := NatIso.isIso_of_isIso_app (towerNatTrans T₁ T₂ e he)
  exact asIso (towerNatTrans T₁ T₂ e he)

/-- **The two derived towers are pro-isomorphic**, with both reindexings the identity. -/
def towerProIso : InverseSequence.ProIso T₁.tower T₂.tower :=
  InverseSequence.ProIso.ofNatIso (towerNatIso T₁ T₂ e he)

include e he in
/-- **The derived limits of the two derived towers are isomorphic.** This is Tag 0H9L applied to
the pro-isomorphism of `DifferentialGraded.Bimodule.DerivedTensorTower.towerProIso`; the
isomorphism is not canonical, so the conclusion is stated for any two derived limits. -/
theorem nonempty_iso_of_isDerivedLimit [HasProduct fun n : ℕ => T₁.tower.obj (op n)]
    [HasProduct fun n : ℕ => T₂.tower.obj (op n)] (K K' : derivedCategory' B)
    (hK : Pretriangulated.IsDerivedLimit T₁.tower K)
    (hK' : Pretriangulated.IsDerivedLimit T₂.tower K') :
    Nonempty (K ≅ K') :=
  Rlim.Pro.nonempty_iso_of_isDerivedLimit_of_pro_isomorphism _ _ K K' hK hK'
    (towerProIso T₁ T₂ e he)

end DerivedTensorTower

end DifferentialGraded.Bimodule

end
