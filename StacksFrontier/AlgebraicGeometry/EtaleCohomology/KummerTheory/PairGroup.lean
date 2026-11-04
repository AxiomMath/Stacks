module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.Basic
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.LocalKernelPresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerTransport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TensorOfPairs
public import Mathlib.Tactic.CategoryTheory.Coherence
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# The group of pairs on a scheme

A pair on a scheme `S` consists of an invertible sheaf together with a trivialization of its
`n`-th tensor power, and the isomorphism classes of such pairs are what Tag 040Q identifies with
a Kummer-theoretic cohomology group. This file builds the algebra of those classes that does not
mention abelian groups: the tensor product of two pairs, the fact that `PairIso` is an
equivalence relation, the quotient type of isomorphism classes, the compatibility of the tensor
product with isomorphism — which is what makes the tensor product descend to the quotient — the
two unit laws, that the unit pair is a right unit and that the tensor product of two unit pairs
is the unit pair of the product of the two units, and the twist of a pair by a global unit, which
is what tensoring with a unit pair does to it.

## Main definitions

* `AlgebraicGeometry.tensorPair` is the tensor product of two pairs: the tensor product of the
  two invertible sheaves, with the trivialization
  `Stacks.Cohomology.Torsors.Generators.tensorTriv` of its `n`-th tensor power.
* `AlgebraicGeometry.pairSetoid` is the setoid of isomorphism of pairs,
  `AlgebraicGeometry.PairClasses` its quotient, `AlgebraicGeometry.pairClass` the class of a
  pair, and `AlgebraicGeometry.tensorPairClass` the tensor product read on classes.
* `AlgebraicGeometry.twistPair` is a pair with its trivialization scaled by a global unit, the
  invertible sheaf and its invertibility left untouched.

## Main results

* `AlgebraicGeometry.pairIsoRefl`, `AlgebraicGeometry.pairIsoSymm` and
  `AlgebraicGeometry.pairIsoTrans`: **isomorphism of pairs is an equivalence relation.** They
  rest on `AlgebraicGeometry.tensorPowerMap_refl`, `AlgebraicGeometry.tensorPowerMap_trans_eq` and
  `AlgebraicGeometry.tensorPowerMap_symm`, the functoriality of the tensor power of an
  isomorphism.
* `AlgebraicGeometry.pairIsoTensorPair`: **the tensor product of two pairs respects isomorphism
  in both arguments**, and `AlgebraicGeometry.pairClass_tensorPair_congr` is the resulting
  congruence on isomorphism classes. The square it needs is
  `AlgebraicGeometry.tensorTriv_congr`, which is the naturality of the tensor-power comparison
  read on trivializations.
* `AlgebraicGeometry.pairIsoTensorPairUnit`: **the unit pair is a right unit for the tensor
  product of pairs up to isomorphism.** Its content is
  `AlgebraicGeometry.tpowTensorIso_unit_rightUnitor`, the right unit law for the tensor-power
  comparison, proved by induction out of the symmetric monoidal coherences
  `AlgebraicGeometry.tensorMu_unit_rightUnitor` and
  `AlgebraicGeometry.tensorMu_rightUnitor_step`.
* `AlgebraicGeometry.pairIsoTensorPairUnitPair`: **the tensor product of two unit pairs is the
  unit pair of the product of the two units.** The scalars are collected by
  `AlgebraicGeometry.tensorTriv_scalar`.
* `AlgebraicGeometry.pairIsoTensorPairUnitTwist`: **tensoring a pair with a unit pair twists it
  by that unit**, which interpolates between the two unit laws above, and
  `AlgebraicGeometry.trivializationRatio_twistPair`: **the global unit comparing the twisted
  trivialization with the original one is the twisting unit itself.**

## Implementation notes

The trivialization of the tensor product is not rebuilt here: it is
`Stacks.Cohomology.Torsors.Generators.tensorTriv`, which lives over an arbitrary ringed site, and
a scheme is fed to it as `Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite`. That
ringed site has `(schemeRingedSite S).O.obj = S.presheaf` and
`Stacks.SheafOfModules.Tensor.ringSheaf (schemeRingedSite S).O = ringSheaf S` by `rfl`, so the
tensor powers of the two
developments are the same object; what is *not* transported automatically is the invertibility
instance, whose arguments are then spelled through projections of the ringed site that instance
resolution does not unfold. `AlgebraicGeometry.isInvertible_schemeRingedSite` retypes it, and is
inserted by `letI` wherever a ringed-site construction is applied to a scheme.

`AlgebraicGeometry.tensorPowerMap` of Tag 01CU associates its three constituents to the *right*,
while `Stacks.Cohomology.Torsors.Generators.powerMap` — the same recursion over a ringed site,
and the one the naturality of the tensor-power comparison is stated for — associates them to the
left. The two are therefore not definitionally equal, and
`AlgebraicGeometry.tensorPowerMap_eq_powerMap` identifies them by induction.

Composites of isomorphisms of sheaves of modules mixing the index `ringSheaf S` with the index
`Stacks.SheafOfModules.TensorSheafification.structureSheaf S.presheaf (ringSheafCond S)` are
type-correct only at default transparency, which blocks `rw` and `simp`; every composite below is
written at one index and the crossings are made by `exact` or `congrArg`. The same applies to the
two spellings of the structure sheaf as a module over itself,
`SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)` and the monoidal unit `𝟙_`: a
`rw` whose replacement changes one into the other leaves a goal that is not type-correct at
`implicit` transparency and the next `rw` fails. The two inductions over the exponent therefore fix
one of the two spellings and reassociate in term mode.

The monoidal and symmetric structures are not redeclared: the `local instance`s of
`StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TensorPowerOfATensorProduct` are re-enabled
with `attribute [local instance]`, so that `rw` with that file's lemmas meets the instance they
were stated at. The monoidal coherences of the two unit laws are isolated as statements of an
abstract symmetric monoidal category, where no object carries a projection of a ringed site and
`rw` works; they are applied to sheaves of modules by `exact`.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 040P](https://stacks.math.columbia.edu/tag/040P)
* [Stacks Project, Tag 040Q](https://stacks.math.columbia.edu/tag/040Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules (schemeRingedSite)
open Stacks.Cohomology.Torsors.Generators
open Stacks.SheafOfModules (IsInvertible terminalSectionToEnd)
open Stacks.SheafOfModules.Invertible (tensorPower tensorPowerSuccIso tensorProductIso
  tensorProductBifunctor tensorProductRightUnitor)

universe u v w

namespace AlgebraicGeometry

-- The tensor product sheaf of Tag 01CA and its symmetry constraint, as a monoidal and a
-- symmetric structure on the modules of a ringed site.  Both instances are `local` where they
-- are declared, so the attribute is re-enabled here rather than the declarations repeated; using
-- the very same instances is what lets `rw` fire on the lemmas of
-- `StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TensorPowerOfATensorProduct`.
attribute [local instance] ringedSiteModulesMonoidal ringedSiteModulesSymmetric

/-- The monoidal tensor product of two invertible modules of a ringed site is invertible. This is
`Stacks.SheafOfModules.isInvertible_tensorSheaf` again, at the spelling `L ⊗ M` rather than
`Stacks.Cohomology.Torsors.Generators.tensorSheafOfModules`, which instance resolution treats as
a different term. -/
local instance isInvertible_tensorObj (X : RingedSite.{u, u, u})
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify X.J AddCommGrpCat.{u}]
    (L M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L]
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 M] :
    IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2
      ((L ⊗ M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
  Stacks.SheafOfModules.isInvertible_tensorSheaf X.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L M

/-- The structure sheaf of a ringed site is invertible as a module over itself. -/
local instance isInvertible_unitRingedSite (X : RingedSite.{u, u, u})
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify X.J AddCommGrpCat.{u}] :
    IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  Stacks.SheafOfModules.isInvertible_unit X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2

/-- The monoidal unit of the modules of a ringed site is invertible: the same statement as
`AlgebraicGeometry.isInvertible_unitRingedSite` at the spelling `𝟙_`. -/
local instance isInvertible_tensorUnitRingedSite (X : RingedSite.{u, u, u})
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify X.J AddCommGrpCat.{u}] :
    IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2
      (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
  Stacks.SheafOfModules.isInvertible_unit X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2

/-- The invertibility of a sheaf of modules on a scheme, retyped for the ringed site of the
scheme. The two statements are the same proposition, because `(schemeRingedSite S).O.obj` is
`S.presheaf` and `(Stacks.SheafOfModules.Tensor.ringSheaf (schemeRingedSite S).O).2` is
`ringSheafCond S` by `rfl`; what the
retyping buys is that instance resolution, which does not unfold the projections of the ringed
site, can find it. -/
local instance isInvertible_schemeRingedSite (S : Scheme.{u})
    (L : SheafOfModules.{u} (ringSheaf S)) [h : IsInvertible S.presheaf (ringSheafCond S) L] :
    IsInvertible (schemeRingedSite S).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (schemeRingedSite S).O).2 L :=
  h

/-- **The tensor product of two pairs**: the tensor product of the two invertible sheaves,
trivialized by `Stacks.Cohomology.Torsors.Generators.tensorTriv`, whose value on a tensor
product of sections is the product of the two trivialization values. -/
def tensorPair (S : Scheme.{u}) (n : ℕ) (P Q : TrivializedPower S n) :
    TrivializedPower S n :=
  letI := P.invertible
  letI := Q.invertible
  { sheaf := tensorSheafOfModules (schemeRingedSite S) P.sheaf Q.sheaf
    invertible := Stacks.SheafOfModules.isInvertible_tensorSheaf S.presheaf (ringSheafCond S)
      P.sheaf Q.sheaf
    trivialization := tensorTriv (schemeRingedSite S) P.sheaf Q.sheaf n
      P.trivialization Q.trivialization }

/-- The invertible sheaf of a tensor product of two pairs is the tensor product sheaf. -/
theorem tensorPair_sheaf (S : Scheme.{u}) (n : ℕ) (P Q : TrivializedPower S n) :
    (tensorPair S n P Q).sheaf =
      tensorSheafOfModules (schemeRingedSite S) P.sheaf Q.sheaf := rfl

/-- The trivialization of a tensor product of two pairs is the tensor product of the two
trivializations. -/
theorem tensorPair_trivialization (S : Scheme.{u}) (n : ℕ) (P Q : TrivializedPower S n) :
    letI := P.invertible
    letI := Q.invertible
    (tensorPair S n P Q).trivialization =
      tensorTriv (schemeRingedSite S) P.sheaf Q.sheaf n
        P.trivialization Q.trivialization := rfl

/-! ### The tensor power of an isomorphism is functorial -/

/-- The tensor product of two identity isomorphisms is the identity: it is the tensor product
bifunctor applied to an identity. -/
theorem tensorProductIso_refl (S : Scheme.{u}) (L M : SheafOfModules.{u} (ringSheaf S)) :
    tensorProductIso S.presheaf (ringSheafCond S) (Iso.refl L) (Iso.refl M) =
      Iso.refl _ := by
  let B := tensorProductBifunctor S.presheaf (ringSheafCond S)
  have hp : (Iso.refl L).prod (Iso.refl M) = Iso.refl (L, M) := by ext <;> simp
  show B.mapIso ((Iso.refl L).prod (Iso.refl M)) = Iso.refl _
  exact (congrArg B.mapIso hp).trans (Functor.mapIso_refl B (L, M))

attribute [local implicit_reducible] Stacks.SheafOfModules.TensorSheafification.structureSheaf
  Stacks.SheafOfModules.Tensor.ringSheaf in
/-- **The tensor power of the identity isomorphism is the identity.** The successor comparison is
stated over `Stacks.SheafOfModules.Tensor.ringSheaf` while the tensor powers are stated over
`Stacks.SheafOfModules.TensorSheafification.structureSheaf`; the two rings are the same sheaf but
both names are plain `def`s, so the agreement is invisible at `implicit` transparency and the
`Iso.refl` cancellation below has no pattern to match until they are made reducible. -/
theorem tensorPowerMap_refl (S : Scheme.{u}) (L : SheafOfModules.{u} (ringSheaf S))
    [IsInvertible S.presheaf (ringSheafCond S) L] (n : ℕ) :
    tensorPowerMap S (Iso.refl L) n =
      Iso.refl (tensorPower S.presheaf (ringSheafCond S) L (n : ℤ)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [tensorPowerMap, ih, tensorProductIso_refl, Iso.refl_trans, Iso.symm_self_id]

/-- **The tensor power of an inverse isomorphism is the inverse of the tensor power.** -/
theorem tensorPowerMap_symm (S : Scheme.{u}) {L M : SheafOfModules.{u} (ringSheaf S)}
    [IsInvertible S.presheaf (ringSheafCond S) L]
    [IsInvertible S.presheaf (ringSheafCond S) M]
    (e : L ≅ M) (n : ℕ) :
    tensorPowerMap S e.symm n = (tensorPowerMap S e n).symm := by
  have h : tensorPowerMap S e n ≪≫ tensorPowerMap S e.symm n =
      Iso.refl (tensorPower S.presheaf (ringSheafCond S) L (n : ℤ)) := by
    rw [← tensorPowerMap_trans_eq, Iso.self_symm_id, tensorPowerMap_refl]
  calc tensorPowerMap S e.symm n
      = Iso.refl _ ≪≫ tensorPowerMap S e.symm n := (Iso.refl_trans _).symm
    _ = ((tensorPowerMap S e n).symm ≪≫ tensorPowerMap S e n) ≪≫
          tensorPowerMap S e.symm n := by rw [Iso.symm_self_id]
    _ = (tensorPowerMap S e n).symm ≪≫
          (tensorPowerMap S e n ≪≫ tensorPowerMap S e.symm n) := Iso.trans_assoc _ _ _
    _ = (tensorPowerMap S e n).symm ≪≫ Iso.refl _ := by rw [h]
    _ = (tensorPowerMap S e n).symm := Iso.trans_refl _

/-! ### Isomorphism of pairs is an equivalence relation -/

/-- **Isomorphism of pairs is reflexive**: the identity isomorphism of the invertible sheaf is
compatible with the trivialization, because its tensor power is the identity. -/
def pairIsoRefl {S : Scheme.{u}} {n : ℕ} (P : TrivializedPower S n) : PairIso P P where
  sheafIso := Iso.refl P.sheaf
  compatible :=
    letI := P.invertible
    (congrArg (fun z => z ≪≫ P.trivialization)
      (tensorPowerMap_refl S P.sheaf n)).trans (Iso.refl_trans P.trivialization)

/-- **Isomorphism of pairs is symmetric**: the inverse isomorphism of the invertible sheaf is
compatible with the trivializations, because the tensor power of an inverse is an inverse. -/
def pairIsoSymm {S : Scheme.{u}} {n : ℕ} {P Q : TrivializedPower S n} (φ : PairIso P Q) :
    PairIso Q P where
  sheafIso := φ.sheafIso.symm
  compatible := by
    let := P.invertible
    let := Q.invertible
    rw [tensorPowerMap_symm, ← φ.compatible, ← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans]

/-- **Isomorphism of pairs is transitive**: a composite of isomorphisms of the invertible sheaves
is compatible with the trivializations, because the tensor power of a composite is a
composite. -/
def pairIsoTrans {S : Scheme.{u}} {n : ℕ} {P Q R : TrivializedPower S n}
    (φ : PairIso P Q) (ψ : PairIso Q R) : PairIso P R where
  sheafIso := φ.sheafIso ≪≫ ψ.sheafIso
  compatible := by
    let := P.invertible
    let := Q.invertible
    let := R.invertible
    rw [tensorPowerMap_trans_eq, Iso.trans_assoc, ψ.compatible, φ.compatible]

/-! ### The isomorphism classes of pairs -/

/-- **The setoid of isomorphism of pairs**: two pairs are equivalent when an isomorphism of pairs
between them exists. -/
def pairSetoid (S : Scheme.{u}) (n : ℕ) : Setoid (TrivializedPower S n) where
  r P Q := Nonempty (PairIso P Q)
  iseqv :=
    { refl := fun P => ⟨pairIsoRefl P⟩
      symm := fun ⟨φ⟩ => ⟨pairIsoSymm φ⟩
      trans := fun ⟨φ⟩ ⟨ψ⟩ => ⟨pairIsoTrans φ ψ⟩ }

/-- **The isomorphism classes of pairs** on a scheme: the set that Tag 040Q identifies with a
Kummer-theoretic cohomology group. -/
def PairClasses (S : Scheme.{u}) (n : ℕ) : Type (u + 1) :=
  Quotient (pairSetoid S n)

/-- The isomorphism class of a pair. -/
def pairClass {S : Scheme.{u}} {n : ℕ} (P : TrivializedPower S n) : PairClasses S n :=
  Quotient.mk (pairSetoid S n) P

/-- Two pairs have the same class exactly when they are isomorphic. -/
theorem pairClass_eq_iff {S : Scheme.{u}} {n : ℕ} (P Q : TrivializedPower S n) :
    pairClass P = pairClass Q ↔ Nonempty (PairIso P Q) :=
  Quotient.eq (r := pairSetoid S n)

/-! ### The tensor product of pairs respects isomorphism -/

/-- The two recursions for the tensor power of an isomorphism agree: `tensorPowerMap` associates
its three constituents to the right and `Stacks.Cohomology.Torsors.Generators.powerMap` to the
left, so they are not definitionally equal, but one reassociation per step identifies them. -/
theorem tensorPowerMap_eq_powerMap (S : Scheme.{u}) {L M : SheafOfModules.{u} (ringSheaf S)}
    [IsInvertible S.presheaf (ringSheafCond S) L]
    [IsInvertible S.presheaf (ringSheafCond S) M]
    (e : L ≅ M) (n : ℕ) :
    tensorPowerMap S e n = powerMap (schemeRingedSite S) e n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (tensorPowerSuccIso S.presheaf (ringSheafCond S) L (n : ℤ)).symm ≪≫
        tensorProductIso S.presheaf (ringSheafCond S) (tensorPowerMap S e n) e ≪≫
        tensorPowerSuccIso S.presheaf (ringSheafCond S) M (n : ℤ) =
      ((tensorPowerSuccIso S.presheaf (ringSheafCond S) L (n : ℤ)).symm ≪≫
          tensorProductIso S.presheaf (ringSheafCond S)
            (powerMap (schemeRingedSite S) e n) e) ≪≫
        tensorPowerSuccIso S.presheaf (ringSheafCond S) M (n : ℤ)
    refine Eq.trans (congrArg (fun z =>
      (tensorPowerSuccIso S.presheaf (ringSheafCond S) L (n : ℤ)).symm ≪≫
        tensorProductIso S.presheaf (ringSheafCond S) z e ≪≫
        tensorPowerSuccIso S.presheaf (ringSheafCond S) M (n : ℤ)) ih) ?_
    exact (Iso.trans_assoc _ _ _).symm

/-- **The trivialization of a tensor product of pairs is compatible with isomorphisms of the two
factors.** The square for the tensor-power comparison is
`Stacks.Cohomology.Torsors.Generators.tpowTensorIso_naturality`; the two trivializations are then
moved across it by functoriality of the tensor product of isomorphisms. -/
theorem tensorTriv_congr (X : RingedSite.{u, u, u})
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify X.J AddCommGrpCat.{u}]
    (L L' M M' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L]
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L']
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 M]
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 M'] (n : ℕ)
    (al : tpow X L n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (al' : tpow X L' n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (bl : tpow X M n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (bl' : tpow X M' n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (e : L ≅ L') (f : M ≅ M')
    (he : powerMap X e n ≪≫ al' = al) (hf : powerMap X f n ≪≫ bl' = bl) :
    powerMap X (tensorIsoOfModules X e f) n ≪≫ tensorTriv X L' M' n al' bl' =
      tensorTriv X L M n al bl := by
  have he' : (powerMap X e n).hom ≫ al'.hom = al.hom := congrArg Iso.hom he
  have hf' : (powerMap X f n).hom ≫ bl'.hom = bl.hom := congrArg Iso.hom hf
  have hnat : (powerMap X (tensorIsoOfModules X e f) n).hom ≫ (tpowTensorIso X L' M' n).hom =
      (tpowTensorIso X L M n).hom ≫ ((powerMap X e n).hom ⊗ₘ (powerMap X f n).hom) :=
    tpowTensorIso_naturality X e f n
  have hmul : ((powerMap X e n).hom ⊗ₘ (powerMap X f n).hom) ≫ (al'.hom ⊗ₘ bl'.hom) =
      al.hom ⊗ₘ bl.hom := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, he', hf']
  apply Iso.ext
  show (powerMap X (tensorIsoOfModules X e f) n).hom ≫
      (((tpowTensorIso X L' M' n).hom ≫ (al'.hom ⊗ₘ bl'.hom)) ≫
        (ρ_ (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom) =
    ((tpowTensorIso X L M n).hom ≫ (al.hom ⊗ₘ bl.hom)) ≫
      (ρ_ (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom
  calc (powerMap X (tensorIsoOfModules X e f) n).hom ≫
        (((tpowTensorIso X L' M' n).hom ≫ (al'.hom ⊗ₘ bl'.hom)) ≫
          (ρ_ (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom)
      = ((powerMap X (tensorIsoOfModules X e f) n).hom ≫
          ((tpowTensorIso X L' M' n).hom ≫ (al'.hom ⊗ₘ bl'.hom))) ≫
          (ρ_ (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom :=
        (Category.assoc _ _ _).symm
    _ = (((powerMap X (tensorIsoOfModules X e f) n).hom ≫ (tpowTensorIso X L' M' n).hom) ≫
          (al'.hom ⊗ₘ bl'.hom)) ≫
          (ρ_ (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom :=
        congrArg
          (fun z => z ≫ (ρ_ (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom)
          (Category.assoc _ _ _).symm
    _ = (((tpowTensorIso X L M n).hom ≫
            ((powerMap X e n).hom ⊗ₘ (powerMap X f n).hom)) ≫
          (al'.hom ⊗ₘ bl'.hom)) ≫
          (ρ_ (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom := by
        rw [hnat]
    _ = ((tpowTensorIso X L M n).hom ≫
            (((powerMap X e n).hom ⊗ₘ (powerMap X f n).hom) ≫
              (al'.hom ⊗ₘ bl'.hom))) ≫
          (ρ_ (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom :=
        congrArg
          (fun z => z ≫ (ρ_ (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom)
          (Category.assoc _ _ _)
    _ = ((tpowTensorIso X L M n).hom ≫ (al.hom ⊗ₘ bl.hom)) ≫
          (ρ_ (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom := by
        rw [hmul]

/-- **The tensor product of two pairs respects isomorphism in both arguments.** -/
def pairIsoTensorPair {S : Scheme.{u}} {n : ℕ} {P P' Q Q' : TrivializedPower S n}
    (φ : PairIso P P') (ψ : PairIso Q Q') :
    PairIso (tensorPair S n P Q) (tensorPair S n P' Q') where
  sheafIso := tensorIsoOfModules (schemeRingedSite S) φ.sheafIso ψ.sheafIso
  compatible := by
    let := P.invertible
    let := Q.invertible
    let := P'.invertible
    let := Q'.invertible
    let : IsInvertible S.presheaf (ringSheafCond S)
        (tensorSheafOfModules (schemeRingedSite S) P.sheaf Q.sheaf) :=
      (tensorPair S n P Q).invertible
    let : IsInvertible S.presheaf (ringSheafCond S)
        (tensorSheafOfModules (schemeRingedSite S) P'.sheaf Q'.sheaf) :=
      (tensorPair S n P' Q').invertible
    have he : powerMap (schemeRingedSite S) φ.sheafIso n ≪≫ P'.trivialization =
        P.trivialization :=
      (congrArg (fun z => z ≪≫ P'.trivialization)
        (tensorPowerMap_eq_powerMap S φ.sheafIso n)).symm.trans φ.compatible
    have hf : powerMap (schemeRingedSite S) ψ.sheafIso n ≪≫ Q'.trivialization =
        Q.trivialization :=
      (congrArg (fun z => z ≪≫ Q'.trivialization)
        (tensorPowerMap_eq_powerMap S ψ.sheafIso n)).symm.trans ψ.compatible
    change tensorPowerMap S (tensorIsoOfModules (schemeRingedSite S) φ.sheafIso ψ.sheafIso) n ≪≫
        tensorTriv (schemeRingedSite S) P'.sheaf Q'.sheaf n P'.trivialization
          Q'.trivialization =
      tensorTriv (schemeRingedSite S) P.sheaf Q.sheaf n P.trivialization Q.trivialization
    refine Eq.trans (congrArg (fun z => z ≪≫
      tensorTriv (schemeRingedSite S) P'.sheaf Q'.sheaf n P'.trivialization Q'.trivialization)
      (tensorPowerMap_eq_powerMap S
        (tensorIsoOfModules (schemeRingedSite S) φ.sheafIso ψ.sheafIso) n)) ?_
    exact tensorTriv_congr (schemeRingedSite S) P.sheaf P'.sheaf Q.sheaf Q'.sheaf n
      P.trivialization P'.trivialization Q.trivialization Q'.trivialization
      φ.sheafIso ψ.sheafIso he hf

/-- **The class of a tensor product of pairs depends only on the two classes.** -/
theorem pairClass_tensorPair_congr {S : Scheme.{u}} {n : ℕ} {P P' Q Q' : TrivializedPower S n}
    (hP : pairClass P = pairClass P') (hQ : pairClass Q = pairClass Q') :
    pairClass (tensorPair S n P Q) = pairClass (tensorPair S n P' Q') := by
  obtain ⟨φ⟩ := (pairClass_eq_iff P P').1 hP
  obtain ⟨ψ⟩ := (pairClass_eq_iff Q Q').1 hQ
  exact (pairClass_eq_iff _ _).2 ⟨pairIsoTensorPair φ ψ⟩

/-- **The tensor product of pairs, as an operation on isomorphism classes.** -/
def tensorPairClass (S : Scheme.{u}) (n : ℕ) :
    PairClasses S n → PairClasses S n → PairClasses S n :=
  Quotient.map₂ (tensorPair S n) (by
    intro P P' hP Q Q' hQ
    obtain ⟨φ⟩ := hP
    obtain ⟨ψ⟩ := hQ
    exact ⟨pairIsoTensorPair φ ψ⟩)

/-- The operation on classes is the class of the tensor product. -/
theorem tensorPairClass_pairClass (S : Scheme.{u}) (n : ℕ) (P Q : TrivializedPower S n) :
    tensorPairClass S n (pairClass P) (pairClass Q) = pairClass (tensorPair S n P Q) := rfl

/-! ### The monoidal coherences behind the unit pair

The three statements of this section hold in any symmetric monoidal category, where no object
carries a projection of a ringed site and `rw` therefore works on the monoidal lemmas; they are
applied to sheaves of modules by `exact`, exactly as
`Stacks.Cohomology.Torsors.Generators.tensorMu_naturality_step` is.
-/

/-- The two unit constraints agree on the unit object, read on their inverses. -/
theorem unitorsInvEqual {D : Type w} [Category.{v} D] [MonoidalCategory D] :
    (λ_ (𝟙_ D)).inv = (ρ_ (𝟙_ D)).inv :=
  unitors_inv_equal

/-- At the unit object the inverse middle-four interchange is the interchange with the two
middle factors exchanged: the two differ only in which of the two inverse braidings of the
symmetry they use. -/
theorem tensorDelta_unit_eq {D : Type w} [Category.{v} D] [MonoidalCategory D]
    [SymmetricCategory D] (P Q : D) :
    tensorδ P (𝟙_ D) Q (𝟙_ D) = tensorμ P Q (𝟙_ D) (𝟙_ D) := by
  simp only [tensorδ, tensorμ]
  rw [SymmetricCategory.braiding_swap_eq_inv_braiding (𝟙_ D) Q]

/-- **The middle-four interchange at two unit factors is the tensor product of the two right
unit constraints**, once the unit factor of the target has been cancelled. This is the right
unitality of the interchange, `CategoryTheory.MonoidalCategory.tensor_right_unitality`, with the
one cancellation it needs carried out. -/
theorem tensorMu_unit_rightUnitor {D : Type w} [Category.{v} D] [MonoidalCategory D]
    [SymmetricCategory D] (P Q : D) :
    tensorμ P (𝟙_ D) Q (𝟙_ D) ≫ ((P ⊗ Q) ◁ (ρ_ (𝟙_ D)).hom) ≫ (ρ_ (P ⊗ Q)).hom =
      (ρ_ P).hom ⊗ₘ (ρ_ Q).hom := by
  have key : (ρ_ (P ⊗ Q)).hom =
      ((P ⊗ Q) ◁ (ρ_ (𝟙_ D)).inv) ≫ tensorδ P (𝟙_ D) Q (𝟙_ D) ≫
        ((ρ_ P).hom ⊗ₘ (ρ_ Q).hom) := by
    rw [tensorDelta_unit_eq, ← unitorsInvEqual]
    exact tensor_right_unitality P Q
  rw [key, ← MonoidalCategory.whiskerLeft_comp_assoc, Iso.hom_inv_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp, ← Category.assoc,
    tensorμ_tensorδ, Category.id_comp]

/-- **The inductive step of the right unit law for tensor powers**, isolated as an identity of a
symmetric monoidal category: the middle-four interchange, followed by whiskering with a map to
the unit object and the right unit constraint, is the tensor product of that whiskering with the
right unit constraint of the other factor. It is the naturality of the interchange in its second
argument, `CategoryTheory.MonoidalCategory.tensorμ_natural`, followed by
`AlgebraicGeometry.tensorMu_unit_rightUnitor`. -/
theorem tensorMu_rightUnitor_step {D : Type w} [Category.{v} D] [MonoidalCategory D]
    [SymmetricCategory D] (P Q : D) {A : D} (b : A ⟶ 𝟙_ D) :
    tensorμ P A Q (𝟙_ D) ≫ ((P ⊗ Q) ◁ ((b ⊗ₘ 𝟙 (𝟙_ D)) ≫ (ρ_ (𝟙_ D)).hom)) ≫
        (ρ_ (P ⊗ Q)).hom =
      ((P ◁ b) ≫ (ρ_ P).hom) ⊗ₘ (ρ_ Q).hom := by
  have hn : ((𝟙 P ⊗ₘ b) ⊗ₘ (𝟙 Q ⊗ₘ 𝟙 (𝟙_ D))) ≫ tensorμ P (𝟙_ D) Q (𝟙_ D) =
      tensorμ P A Q (𝟙_ D) ≫ ((𝟙 P ⊗ₘ 𝟙 Q) ⊗ₘ (b ⊗ₘ 𝟙 (𝟙_ D))) :=
    tensorμ_natural (𝟙 P) b (𝟙 Q) (𝟙 (𝟙_ D))
  calc tensorμ P A Q (𝟙_ D) ≫ ((P ⊗ Q) ◁ ((b ⊗ₘ 𝟙 (𝟙_ D)) ≫ (ρ_ (𝟙_ D)).hom)) ≫
        (ρ_ (P ⊗ Q)).hom
      = tensorμ P A Q (𝟙_ D) ≫ ((𝟙 P ⊗ₘ 𝟙 Q) ⊗ₘ (b ⊗ₘ 𝟙 (𝟙_ D))) ≫
          ((P ⊗ Q) ◁ (ρ_ (𝟙_ D)).hom) ≫ (ρ_ (P ⊗ Q)).hom := by
        rw [MonoidalCategory.whiskerLeft_comp, MonoidalCategory.id_tensorHom_id,
          MonoidalCategory.id_tensorHom, Category.assoc]
    _ = (((𝟙 P ⊗ₘ b) ⊗ₘ (𝟙 Q ⊗ₘ 𝟙 (𝟙_ D))) ≫ tensorμ P (𝟙_ D) Q (𝟙_ D)) ≫
          ((P ⊗ Q) ◁ (ρ_ (𝟙_ D)).hom) ≫ (ρ_ (P ⊗ Q)).hom := by
        rw [hn, Category.assoc]
    _ = ((𝟙 P ⊗ₘ b) ⊗ₘ (𝟙 Q ⊗ₘ 𝟙 (𝟙_ D))) ≫ ((ρ_ P).hom ⊗ₘ (ρ_ Q).hom) := by
        rw [Category.assoc, tensorMu_unit_rightUnitor]
    _ = ((P ◁ b) ≫ (ρ_ P).hom) ⊗ₘ (ρ_ Q).hom := by
        rw [MonoidalCategory.tensorHom_comp_tensorHom, MonoidalCategory.id_tensorHom_id,
          MonoidalCategory.id_tensorHom, Category.id_comp]

/-! ### The unit pair is a right unit -/

/-- The tensor product of two morphisms followed by whiskering the target of the first absorbs
the whiskering into the second factor. -/
theorem tensorHom_comp_whiskerLeft {D : Type w} [Category.{v} D] [MonoidalCategory D]
    {A A' B B' B'' : D} (f : A ⟶ A') (g : B ⟶ B') (h : B' ⟶ B'') :
    (f ⊗ₘ g) ≫ (A' ◁ h) = f ⊗ₘ (g ≫ h) := by
  rw [← MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom,
    Category.comp_id]

/-- A tensor product whose second factor lands in the unit object, followed by the right unit
constraint, is the whiskering of the second factor followed by the right unit constraint and the
first factor. -/
theorem tensorHom_whiskerLeft_rightUnitor {D : Type w} [Category.{v} D] [MonoidalCategory D]
    {A A' B : D} (f : A ⟶ A') (g : B ⟶ 𝟙_ D) :
    (f ⊗ₘ g) ≫ (ρ_ A').hom = (A ◁ g) ≫ (ρ_ A).hom ≫ f := by
  rw [MonoidalCategory.tensorHom_def', Category.assoc,
    MonoidalCategory.rightUnitor_naturality]

/-- **The inductive step of the right unit law, in the shape the recursion leaves it in.** The
successor comparison of the unit factor is cancelled against its inverse, the right unit
constraint is moved across the first factor, and
`AlgebraicGeometry.tensorMu_rightUnitor_step` finishes. -/
theorem tensorMu_rightUnitor_whisker_step {D : Type w} [Category.{v} D] [MonoidalCategory D]
    [SymmetricCategory D] {P A Q P' A' : D} (sl : P ⊗ Q ⟶ P') (su : A ⊗ 𝟙_ D ⟶ A')
    (suinv : A' ⟶ A ⊗ 𝟙_ D) (c : A ⟶ 𝟙_ D) (hs : su ≫ suinv = 𝟙 (A ⊗ 𝟙_ D)) :
    tensorμ P A Q (𝟙_ D) ≫ (sl ⊗ₘ su) ≫
        (P' ◁ (suinv ≫ ((c ⊗ₘ 𝟙 (𝟙_ D)) ≫ (ρ_ (𝟙_ D)).hom))) ≫ (ρ_ P').hom =
      (((P ◁ c) ≫ (ρ_ P).hom) ⊗ₘ (ρ_ Q).hom) ≫ sl := by
  have h1 : (sl ⊗ₘ su) ≫ (P' ◁ (suinv ≫ ((c ⊗ₘ 𝟙 (𝟙_ D)) ≫ (ρ_ (𝟙_ D)).hom))) =
      sl ⊗ₘ ((c ⊗ₘ 𝟙 (𝟙_ D)) ≫ (ρ_ (𝟙_ D)).hom) := by
    rw [tensorHom_comp_whiskerLeft, ← Category.assoc, hs, Category.id_comp]
  calc tensorμ P A Q (𝟙_ D) ≫ (sl ⊗ₘ su) ≫
        (P' ◁ (suinv ≫ ((c ⊗ₘ 𝟙 (𝟙_ D)) ≫ (ρ_ (𝟙_ D)).hom))) ≫ (ρ_ P').hom
      = tensorμ P A Q (𝟙_ D) ≫ ((sl ⊗ₘ su) ≫
          (P' ◁ (suinv ≫ ((c ⊗ₘ 𝟙 (𝟙_ D)) ≫ (ρ_ (𝟙_ D)).hom)))) ≫ (ρ_ P').hom :=
        congrArg (fun z => tensorμ P A Q (𝟙_ D) ≫ z) (Category.assoc _ _ _).symm
    _ = tensorμ P A Q (𝟙_ D) ≫
          (sl ⊗ₘ ((c ⊗ₘ 𝟙 (𝟙_ D)) ≫ (ρ_ (𝟙_ D)).hom)) ≫ (ρ_ P').hom := by rw [h1]
    _ = tensorμ P A Q (𝟙_ D) ≫
          ((P ⊗ Q) ◁ ((c ⊗ₘ 𝟙 (𝟙_ D)) ≫ (ρ_ (𝟙_ D)).hom)) ≫
            (ρ_ (P ⊗ Q)).hom ≫ sl := by rw [tensorHom_whiskerLeft_rightUnitor]
    _ = (tensorμ P A Q (𝟙_ D) ≫
          ((P ⊗ Q) ◁ ((c ⊗ₘ 𝟙 (𝟙_ D)) ≫ (ρ_ (𝟙_ D)).hom)) ≫
            (ρ_ (P ⊗ Q)).hom) ≫ sl := by simp only [Category.assoc]
    _ = (((P ◁ c) ≫ (ρ_ P).hom) ⊗ₘ (ρ_ Q).hom) ≫ sl :=
        congrArg (fun z => z ≫ sl) (tensorMu_rightUnitor_step P Q c)

/-- The tensor-power comparison at a successor exponent, read on underlying morphisms. -/
theorem tpowTensorIso_succ_hom (X : RingedSite.{u, u, u})
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify X.J AddCommGrpCat.{u}]
    (L M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L]
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 M] (k : ℕ) :
    (tpowTensorIso X L M (k + 1)).hom =
      (((tpowSuccIso X (tensorSheafOfModules X L M) k).inv ≫
            ((tpowTensorIso X L M k).hom ⊗ₘ 𝟙 (tensorSheafOfModules X L M))) ≫
          tensorμ (tpow X L k) (tpow X M k) L M) ≫
        ((tpowSuccIso X L k).hom ⊗ₘ (tpowSuccIso X M k).hom) := rfl

/-- The tensor-power comparison at the zero exponent, read on underlying morphisms. -/
theorem tpowTensorIso_zero_hom (X : RingedSite.{u, u, u})
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify X.J AddCommGrpCat.{u}]
    (L M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L]
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 M] :
    (tpowTensorIso X L M 0).hom =
      (ρ_ (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).inv := rfl

/-- The tensor power of an isomorphism at a successor exponent, read on underlying
morphisms. -/
theorem powerMap_succ_hom (X : RingedSite.{u, u, u})
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify X.J AddCommGrpCat.{u}]
    {L M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L]
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 M]
    (e : L ≅ M) (k : ℕ) :
    (powerMap X e (k + 1)).hom =
      ((tpowSuccIso X L k).inv ≫ ((powerMap X e k).hom ⊗ₘ e.hom)) ≫
        (tpowSuccIso X M k).hom := rfl

/-- **The right unit law for the tensor-power comparison.** Comparing the `n`-th power of
`L ⊗ O` with `L^{⊗ n} ⊗ O^{⊗ n}`, trivializing the second factor and cancelling it against the
right unit constraint gives the `n`-th power of the right unit constraint of `L`. The
trivialization of the powers of the structure sheaf enters only through its recursion, which is
why it is taken as the family `γ` together with the two equations it satisfies. -/
theorem tpowTensorIso_unit_rightUnitor (X : RingedSite.{u, u, u})
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify X.J AddCommGrpCat.{u}]
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L]
    (γ : (k : ℕ) → tpow X (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) k ≅
      𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hγ0 : (γ 0).hom = 𝟙 (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hγs : ∀ k : ℕ, (γ (k + 1)).hom =
      (tpowSuccIso X (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) k).inv ≫
        (((γ k).hom ⊗ₘ 𝟙 (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) ≫
          (ρ_ (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).hom))
    (n : ℕ) :
    (tpowTensorIso X L (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
      n).hom ≫
        (tpow X L n ◁ (γ n).hom) ≫ (ρ_ (tpow X L n)).hom =
      (powerMap X (ρ_ L) n).hom := by
  induction n with
  | zero =>
    have h0 : (tpowTensorIso X L
          (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).hom ≫
          (tpow X L 0 ◁ (γ 0).hom) ≫ (ρ_ (tpow X L 0)).hom =
        (ρ_ (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).inv ≫
          ((𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ◁
            (𝟙 (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))) ≫
          (ρ_ (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).hom :=
      congrArg (fun z =>
        (ρ_ (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).inv ≫
        ((𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ◁ z) ≫
        (ρ_ (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).hom) hγ0
    refine h0.trans ?_
    show (ρ_ (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).inv ≫
        ((𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ◁
          (𝟙 (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))) ≫
        (ρ_ (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).hom =
      𝟙 (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    rw [MonoidalCategory.whiskerLeft_id, Category.id_comp, Iso.inv_hom_id]
  | succ k ih =>
    rw [tpowTensorIso_succ_hom, powerMap_succ_hom, hγs k]
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg
      (fun z => ((tpowSuccIso X
            (tensorSheafOfModules X L
              (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) k).inv ≫
          ((tpowTensorIso X L
              (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) k).hom ⊗ₘ
            𝟙 (tensorSheafOfModules X L
              (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))))) ≫ z)
      (tensorMu_rightUnitor_whisker_step (tpowSuccIso X L k).hom
        (tpowSuccIso X (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) k).hom
        (tpowSuccIso X (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) k).inv
        (γ k).hom
        (Iso.hom_inv_id _))) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine congrArg (fun z => z ≫ (tpowSuccIso X L k).hom) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine congrArg (fun z =>
      (tpowSuccIso X (tensorSheafOfModules X L
        (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) k).inv ≫ z) ?_
    refine Eq.trans (MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _) ?_
    rw [Category.id_comp, ih]

/-- **The right unit law for the trivialization of a tensor product of pairs**: tensoring with
the structure sheaf carrying its canonical trivialization gives back the trivialization of the
original pair, transported along the right unit constraint. -/
theorem tensorTriv_unit (X : RingedSite.{u, u, u})
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify X.J AddCommGrpCat.{u}]
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L]
    (γ : (k : ℕ) → tpow X (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) k ≅
      𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hγ0 : (γ 0).hom = 𝟙 (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hγs : ∀ k : ℕ, (γ (k + 1)).hom =
      (tpowSuccIso X (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) k).inv ≫
        (((γ k).hom ⊗ₘ 𝟙 (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) ≫
          (ρ_ (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).hom))
    (n : ℕ)
    (al : tpow X L n ≅ 𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    powerMap X (ρ_ L) n ≪≫ al =
      tensorTriv X L (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) n al
        (γ n) := by
  apply Iso.ext
  refine Eq.trans (congrArg (fun z => z ≫ al.hom)
    (tpowTensorIso_unit_rightUnitor X L γ hγ0 hγs n).symm) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg
    (fun z => (tpowTensorIso X L
      (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) n).hom ≫ z)
    (Category.assoc _ _ _)) ?_
  refine Eq.trans (congrArg
    (fun z => (tpowTensorIso X L
      (𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) n).hom ≫ z)
    (tensorHom_whiskerLeft_rightUnitor al.hom (γ n).hom).symm) ?_
  exact (Category.assoc _ _ _).symm

/-- Multiplication by two global units, composed, is multiplication by their product. -/
theorem scalarIso_trans_mul (S : Scheme.{u}) (f g : (Scheme.Γ.obj (Opposite.op S))ˣ)
    (M : SheafOfModules (ringSheaf S)) :
    scalarIso S g M ≪≫ scalarIso S f M = scalarIso S (f * g) M :=
  Iso.ext (by
    rw [Iso.trans_hom, scalarIso_hom, scalarIso_hom, scalarIso_hom]
    ext U x
    let ρ := ((ringSheaf S).obj.map (Limits.isTerminalTop.from U.unop).op).hom
    show ρ f.val • (ρ g.val • x) = ρ (f * g).val • x
    rw [smul_smul, Units.val_mul]
    exact congrArg (fun r => r • x) (map_mul ρ f.val g.val).symm)

/-- The trivialization of the unit pair at the unit of the global units is the canonical
trivialization of the tensor powers of the structure sheaf. -/
theorem unitPair_one_trivialization (S : Scheme.{u}) (n : ℕ) :
    (unitPair S n 1).trivialization = structureSheafTensorPowerIso S n :=
  have hone : scalarIso S 1 (SheafOfModules.unit (ringSheaf S)) = Iso.refl _ := by
    have h := scalarIso_trans_mul S 1 1 (SheafOfModules.unit (ringSheaf S))
    rw [mul_one] at h
    calc scalarIso S 1 _ = (scalarIso S 1 _ ≪≫ scalarIso S 1 _) ≪≫ (scalarIso S 1 _).symm := by
          rw [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]
      _ = Iso.refl _ := by rw [h, Iso.self_symm_id]
  (unitPair_trivialization S n 1).trans
    ((congrArg (fun z => structureSheafTensorPowerIso S n ≪≫ z) hone).trans
      (Iso.trans_refl _))

/-- **The unit pair is a right unit for the tensor product of pairs**, up to isomorphism of
pairs: the isomorphism of invertible sheaves is the right unit constraint, and its compatibility
with the trivializations is `AlgebraicGeometry.tensorTriv_unit`. -/
def pairIsoTensorPairUnit {S : Scheme.{u}} {n : ℕ} (P : TrivializedPower S n) :
    PairIso (tensorPair S n P (unitPair S n 1)) P where
  sheafIso := tensorProductRightUnitor S.presheaf (ringSheafCond S) P.sheaf
  compatible := by
    let := P.invertible
    let : IsInvertible S.presheaf (ringSheafCond S)
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ S.presheaf (forget₂ CommRingCat RingCat)
            (ringSheafCond S)⟩).obj P.sheaf).obj (SheafOfModules.unit (ringSheaf S)))) :=
      (tensorPair S n P (unitPair S n 1)).invertible
    refine Eq.trans (congrArg (fun z => z ≪≫ P.trivialization)
      (tensorPowerMap_eq_powerMap S
        (tensorProductRightUnitor S.presheaf (ringSheafCond S) P.sheaf) n)) ?_
    refine Eq.trans (tensorTriv_unit (schemeRingedSite S) P.sheaf
      (structureSheafTensorPowerIso S) rfl (fun k => Category.id_comp _) n
      P.trivialization) ?_
    exact congrArg (fun z => tensorTriv (schemeRingedSite S) P.sheaf
      (SheafOfModules.unit (ringSheaf S)) n P.trivialization z)
      (unitPair_one_trivialization S n).symm

/-! ### The tensor product of two unit pairs -/

/-- **Two endomorphisms of the unit object, tensored and followed by the right unit
constraint**, compose into their product. The second factor is moved past the right unit
constraint by its left-unit naturality, which applies because the two unit constraints agree on
the unit object. -/
theorem tensorHom_unitEnd_rightUnitor {D : Type w} [Category.{v} D] [MonoidalCategory D]
    (a b : 𝟙_ D ⟶ 𝟙_ D) :
    (a ⊗ₘ b) ≫ (ρ_ (𝟙_ D)).hom = (ρ_ (𝟙_ D)).hom ≫ b ≫ a := by
  have hb : ((𝟙_ D) ◁ b) ≫ (ρ_ (𝟙_ D)).hom = (ρ_ (𝟙_ D)).hom ≫ b := by
    rw [← unitors_equal]
    exact MonoidalCategory.leftUnitor_naturality b
  rw [tensorHom_whiskerLeft_rightUnitor, ← Category.assoc, hb, Category.assoc]

/-- The same statement with the two factors preceded by arbitrary maps to the unit object, which
is the shape in which a trivialization scaled by a global unit occurs. -/
theorem tensorHom_comp_unitEnd_rightUnitor {D : Type w} [Category.{v} D] [MonoidalCategory D]
    {A B : D} (p : A ⟶ 𝟙_ D) (q : B ⟶ 𝟙_ D) (a b : 𝟙_ D ⟶ 𝟙_ D) :
    ((p ≫ a) ⊗ₘ (q ≫ b)) ≫ (ρ_ (𝟙_ D)).hom =
      ((p ⊗ₘ q) ≫ (ρ_ (𝟙_ D)).hom) ≫ (b ≫ a) := by
  rw [← MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc,
    tensorHom_unitEnd_rightUnitor, Category.assoc]

/-- **Scaling the two trivializations of a tensor product of pairs scales the trivialization of
the tensor product by the product of the two scalars.** -/
theorem tensorTriv_scalar (X : RingedSite.{u, u, u})
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify X.J AddCommGrpCat.{u}]
    (L M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L]
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 M] (n : ℕ)
    (al : tpow X L n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (bl : tpow X M n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (a b : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    tensorTriv X L M n (al ≪≫ a) (bl ≪≫ b) =
      tensorTriv X L M n al bl ≪≫ (b ≪≫ a) := by
  apply Iso.ext
  show ((tpowTensorIso X L M n).hom ≫ ((al.hom ≫ a.hom) ⊗ₘ (bl.hom ≫ b.hom))) ≫
      (ρ_ (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom =
    (((tpowTensorIso X L M n).hom ≫ (al.hom ⊗ₘ bl.hom)) ≫
      (ρ_ (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom) ≫ (b.hom ≫ a.hom)
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun z => (tpowTensorIso X L M n).hom ≫ z)
    (tensorHom_comp_unitEnd_rightUnitor al.hom bl.hom a.hom b.hom)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact congrArg (fun z => z ≫ (b.hom ≫ a.hom)) (Category.assoc _ _ _).symm

/-- **The tensor product of two unit pairs is the unit pair of the product of the two units.**
The isomorphism of invertible sheaves is the right unit constraint of the structure sheaf; the
compatibility is `AlgebraicGeometry.tensorTriv_unit` followed by
`AlgebraicGeometry.tensorTriv_scalar`, which turns the two trivializing units into their
product. -/
def pairIsoTensorPairUnitPair {S : Scheme.{u}} {n : ℕ}
    (f g : (Scheme.Γ.obj (Opposite.op S))ˣ) :
    PairIso (tensorPair S n (unitPair S n f) (unitPair S n g)) (unitPair S n (f * g)) where
  sheafIso := tensorProductRightUnitor S.presheaf (ringSheafCond S)
    (SheafOfModules.unit (ringSheaf S))
  compatible := by
    let : IsInvertible S.presheaf (ringSheafCond S)
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ S.presheaf (forget₂ CommRingCat RingCat)
            (ringSheafCond S)⟩).obj (SheafOfModules.unit (ringSheaf S))).obj
              (SheafOfModules.unit (ringSheaf S)))) :=
      (tensorPair S n (unitPair S n f) (unitPair S n g)).invertible
    refine Eq.trans (congrArg (fun z => z ≪≫ (unitPair S n (f * g)).trivialization)
      (tensorPowerMap_eq_powerMap S (tensorProductRightUnitor S.presheaf (ringSheafCond S)
        (SheafOfModules.unit (ringSheaf S))) n)) ?_
    refine Eq.trans (tensorTriv_unit (schemeRingedSite S)
      (SheafOfModules.unit (ringSheaf S)) (structureSheafTensorPowerIso S) rfl
      (fun k => Category.id_comp _) n (unitPair S n (f * g)).trivialization) ?_
    refine Eq.trans (congrArg₂
      (fun z w => tensorTriv (schemeRingedSite S) (SheafOfModules.unit (ringSheaf S))
        (SheafOfModules.unit (ringSheaf S)) n z w)
      (unitPair_trivialization S n (f * g))
      (Iso.trans_refl (structureSheafTensorPowerIso S n)).symm) ?_
    refine Eq.trans (tensorTriv_scalar (schemeRingedSite S)
      (SheafOfModules.unit (ringSheaf S)) (SheafOfModules.unit (ringSheaf S)) n
      (structureSheafTensorPowerIso S n) (structureSheafTensorPowerIso S n)
      (scalarIso S (f * g) (SheafOfModules.unit (ringSheaf S)))
      (Iso.refl (SheafOfModules.unit (ringSheaf S)))) ?_
    refine Eq.trans (congrArg (fun z => tensorTriv (schemeRingedSite S)
        (SheafOfModules.unit (ringSheaf S)) (SheafOfModules.unit (ringSheaf S)) n
        (structureSheafTensorPowerIso S n) (structureSheafTensorPowerIso S n) ≪≫ z)
      ((Iso.refl_trans (scalarIso S (f * g) (SheafOfModules.unit (ringSheaf S)))).trans
        (scalarIso_trans_mul S f g (SheafOfModules.unit (ringSheaf S))).symm)) ?_
    refine Eq.trans (tensorTriv_scalar (schemeRingedSite S)
      (SheafOfModules.unit (ringSheaf S)) (SheafOfModules.unit (ringSheaf S)) n
      (structureSheafTensorPowerIso S n) (structureSheafTensorPowerIso S n)
      (scalarIso S f (SheafOfModules.unit (ringSheaf S)))
      (scalarIso S g (SheafOfModules.unit (ringSheaf S)))).symm ?_
    exact congrArg₂
      (fun z w => tensorTriv (schemeRingedSite S) (SheafOfModules.unit (ringSheaf S))
        (SheafOfModules.unit (ringSheaf S)) n z w)
      (unitPair_trivialization S n f).symm (unitPair_trivialization S n g).symm

/-! ### Twisting a pair by a global unit -/

/-- **A pair twisted by a global unit**: the same invertible sheaf with the same invertibility,
and the trivialization multiplied by the unit. The scaling is composed on the *right* of the
trivialization: a trivialization is an isomorphism onto the structure sheaf and
`AlgebraicGeometry.scalarIso` is an automorphism of the structure sheaf, so this is the only one
of the two orders that type-checks. -/
def twistPair (S : Scheme.{u}) (n : ℕ) (P : TrivializedPower S n)
    (g : (Scheme.Γ.obj (Opposite.op S))ˣ) : TrivializedPower S n where
  sheaf := P.sheaf
  invertible := P.invertible
  trivialization :=
    P.trivialization ≪≫ scalarIso S g (SheafOfModules.unit (ringSheaf S))

/-- The invertible sheaf of a twisted pair is the invertible sheaf of the original pair. -/
theorem twistPair_sheaf (S : Scheme.{u}) (n : ℕ) (P : TrivializedPower S n)
    (g : (Scheme.Γ.obj (Opposite.op S))ˣ) :
    (twistPair S n P g).sheaf = P.sheaf := rfl

/-- The trivialization of a twisted pair is the original trivialization scaled by the unit. -/
theorem twistPair_trivialization (S : Scheme.{u}) (n : ℕ) (P : TrivializedPower S n)
    (g : (Scheme.Γ.obj (Opposite.op S))ˣ) :
    (twistPair S n P g).trivialization =
      P.trivialization ≪≫ scalarIso S g (SheafOfModules.unit (ringSheaf S)) := rfl

/-- **Tensoring a pair with a unit pair twists it by that unit.** The isomorphism of invertible
sheaves is again the right unit constraint, as in
`AlgebraicGeometry.pairIsoTensorPairUnit`, and the compatibility is
`AlgebraicGeometry.tensorTriv_unit` followed by `AlgebraicGeometry.tensorTriv_scalar` used twice:
once to move the scaling out of the first factor, where `tensorTriv_unit` has put it, and once to
move it back into the second factor, where the trivialization of the unit pair carries it. This
interpolates between `AlgebraicGeometry.pairIsoTensorPairUnit`, which is the case `g = 1`, and
`AlgebraicGeometry.pairIsoTensorPairUnitPair`, which is the case of a unit pair in the first
factor as well. -/
def pairIsoTensorPairUnitTwist {S : Scheme.{u}} {n : ℕ} (P : TrivializedPower S n)
    (g : (Scheme.Γ.obj (Opposite.op S))ˣ) :
    PairIso (tensorPair S n P (unitPair S n g)) (twistPair S n P g) where
  sheafIso := tensorProductRightUnitor S.presheaf (ringSheafCond S) P.sheaf
  compatible := by
    let := P.invertible
    let : IsInvertible S.presheaf (ringSheafCond S)
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ S.presheaf (forget₂ CommRingCat RingCat)
            (ringSheafCond S)⟩).obj P.sheaf).obj (SheafOfModules.unit (ringSheaf S)))) :=
      (tensorPair S n P (unitPair S n g)).invertible
    refine Eq.trans (congrArg (fun z => z ≪≫ (twistPair S n P g).trivialization)
      (tensorPowerMap_eq_powerMap S
        (tensorProductRightUnitor S.presheaf (ringSheafCond S) P.sheaf) n)) ?_
    refine Eq.trans (tensorTriv_unit (schemeRingedSite S) P.sheaf
      (structureSheafTensorPowerIso S) rfl (fun k => Category.id_comp _) n
      (twistPair S n P g).trivialization) ?_
    refine Eq.trans (congrArg₂
      (fun z w => tensorTriv (schemeRingedSite S) P.sheaf
        (SheafOfModules.unit (ringSheaf S)) n z w)
      (twistPair_trivialization S n P g)
      (Iso.trans_refl (structureSheafTensorPowerIso S n)).symm) ?_
    refine Eq.trans (tensorTriv_scalar (schemeRingedSite S) P.sheaf
      (SheafOfModules.unit (ringSheaf S)) n P.trivialization
      (structureSheafTensorPowerIso S n)
      (scalarIso S g (SheafOfModules.unit (ringSheaf S)))
      (Iso.refl (SheafOfModules.unit (ringSheaf S)))) ?_
    refine Eq.trans (congrArg (fun z => tensorTriv (schemeRingedSite S) P.sheaf
        (SheafOfModules.unit (ringSheaf S)) n P.trivialization
        (structureSheafTensorPowerIso S n) ≪≫ z)
      ((Iso.refl_trans (scalarIso S g (SheafOfModules.unit (ringSheaf S)))).trans
        (Iso.trans_refl (scalarIso S g (SheafOfModules.unit (ringSheaf S)))).symm)) ?_
    refine Eq.trans (tensorTriv_scalar (schemeRingedSite S) P.sheaf
      (SheafOfModules.unit (ringSheaf S)) n P.trivialization
      (structureSheafTensorPowerIso S n)
      (Iso.refl (SheafOfModules.unit (ringSheaf S)))
      (scalarIso S g (SheafOfModules.unit (ringSheaf S)))).symm ?_
    exact congrArg₂
      (fun z w => tensorTriv (schemeRingedSite S) P.sheaf
        (SheafOfModules.unit (ringSheaf S)) n z w)
      (Iso.trans_refl P.trivialization) (unitPair_trivialization S n g).symm

/-- **The unit comparing a twisted trivialization with the original one is the twisting unit
itself.** `AlgebraicGeometry.trivializationRatio S n α β` is defined by
`scalarIso (ratio) = β⁻¹ ∘ α`, so the twisted trivialization has to be taken as the *first*
argument: then the original trivialization cancels and exactly the scaling is left. In the other
order the ratio is `g⁻¹`. -/
theorem trivializationRatio_twistPair {S : Scheme.{u}} {n : ℕ} (P : TrivializedPower S n)
    (g : (Scheme.Γ.obj (Opposite.op S))ˣ) :
    letI := P.invertible
    trivializationRatio S n (L := P.sheaf) (twistPair S n P g).trivialization
      P.trivialization = g := by
  let := P.invertible
  have key : scalarIso S (trivializationRatio S n (L := P.sheaf)
        (twistPair S n P g).trivialization P.trivialization)
      (SheafOfModules.unit (ringSheaf S)) =
      scalarIso S g (SheafOfModules.unit (ringSheaf S)) := by
    refine (scalarIso_trivializationRatio S n (L := P.sheaf)
      (twistPair S n P g).trivialization P.trivialization).trans ?_
    refine Eq.trans (congrArg (fun z => P.trivialization.symm ≪≫ z)
      (twistPair_trivialization S n P g)) ?_
    refine Eq.trans (Iso.trans_assoc P.trivialization.symm P.trivialization
      (scalarIso S g (SheafOfModules.unit (ringSheaf S)))).symm ?_
    refine Eq.trans (congrArg
      (fun z => z ≪≫ scalarIso S g (SheafOfModules.unit (ringSheaf S)))
      (Iso.symm_self_id P.trivialization)) ?_
    exact Iso.refl_trans (scalarIso S g (SheafOfModules.unit (ringSheaf S)))
  exact Units.ext (scalarEnd_unit_injective S (congrArg Iso.hom key))

end AlgebraicGeometry

end
