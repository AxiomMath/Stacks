module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDeRhamUnit
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedFormsUnitZero
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CosimplicialDeRhamDoubleComplex
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.EnvelopeForms

/-!
# The structure pair `D̂(•)` and its de Rham double complex

Let `D(•)` be a cosimplicial divided power algebra with completions `D̂(•)`. The cosimplicial
module `M(b) = D̂(b)`, with the connection `∇ x = 1 ⊗ d x` of [Stacks, Tag 07JC] given in each
cosimplicial degree by the universal differential, is a `Crystalline.CosimplicialCompletedPair`.
Its double complex is

`K^{a,b} = D̂(b) ⊗̂_{D(b)} Ω^a_{D(b)}`,

the double complex of [Stacks, Proposition 60.21.3, Tag 07LG] for the coefficient sheaf
`𝒪_{X/S}`. At the cosimplicial envelope `D(*)` of [Stacks, Equation 60.17.3, Tag 07JF], through
`Crystalline.envelopeDPAlgebra`, it is the de Rham double complex `Ω^a_{D(b)}` of the crystalline
cohomology of the structure sheaf.

## Main definitions

* `Crystalline.CosimplicialDPAlgebra.structureModule`: the cosimplicial module `b ↦ D̂(b)`, as a
  `Crystalline.CosimplicialCompletedModule`.
* `Crystalline.CosimplicialDPAlgebra.structureNabla`: the connection `∇ x = 1 ⊗ d x` in each
  cosimplicial degree.
* `Crystalline.CosimplicialDPAlgebra.structurePair`: the `Crystalline.CosimplicialCompletedPair`
  formed by `b ↦ D̂(b)` and these connections.
* `Crystalline.CosimplicialDPAlgebra.structureDoubleComplex`: the double complex `K` of
  `Crystalline.CosimplicialDPAlgebra.structurePair`.
* `Crystalline.envelopeStructurePair`, `Crystalline.envelopeStructureDoubleComplex`: the pair and
  the double complex at the cosimplicial envelope `D(*)`.

## Main results

* `Crystalline.CosimplicialDPAlgebra.formsMap_differential`: the universal differential commutes
  with the cosimplicial transition maps.
* `Crystalline.CosimplicialDPAlgebra.structureIsSquareZero`: the de Rham differentials of each
  cosimplicial degree compose to zero.
* `Crystalline.CosimplicialDPAlgebra.structureDoubleComplex_X`,
  `Crystalline.CosimplicialDPAlgebra.structureDoubleComplex_d`: the degree-`a` column of `K` and
  its differential.

## Implementation notes

Only the coefficient sheaf `𝒪_{X/S}` is treated. For a general crystal the connection in each
cosimplicial degree is the one of [Stacks, Tag 07JC] attached to a
`Crystalline.FirstOrderComparison` for `M(b)`, which the library has for `M = D` only
(`Crystalline.structureComparison`); the general case is blocked by
`Crystalline.GlobalCrystallineSituation.FirstOrderIdealBaseChange`, constructed at the single
coefficient sheaf `𝒪_{X/S}` in
`Crystalline.GlobalCrystallineSituation.firstOrderIdealBaseChangeUnit` and not a consequence of
the sheaf-level crystal condition.

## What this does and does not do to [Stacks, Tag 07LG]

**No `@[stacks 07LG]` attribute is placed.** [Stacks, Tag 07LG] is
`...SmallSite.crystalPairDeRhamComplex_computesCohomology` of
`SmallSite/CrystalDeRhamComputesCohomology.lean`. What falls here of the hypothesis list of
`...SmallSite.computes07LG_of_doubleComplex` is the data `K` itself, for the structure sheaf;
its five other hypotheses (`hcolumns`, `hrows`, `hrow0`, `hcolumn0` and `hker`) are untouched.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Equation 60.17.3, Tag 07JF](https://stacks.math.columbia.edu/tag/07JF)
* [Stacks Project, Tag 07JC](https://stacks.math.columbia.edu/tag/07JC)
-/

@[expose] public noncomputable section

open CategoryTheory
open DividedPowers
open scoped TensorProduct

universe u v w uC

namespace Crystalline

/-- The composite of two semilinear maps, semilinear over the composite of the ring maps. -/
def semilinearComp {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] {σ : R →+* S}
    {τ : S →+* T} {P Q V : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module S Q]
    [AddCommGroup V] [Module T V] (k : Q →ₛₗ[τ] V) (l : P →ₛₗ[σ] Q) : P →ₛₗ[τ.comp σ] V where
  toFun y := k (l y)
  map_add' x y := by rw [map_add, map_add]
  map_smul' r y := by rw [map_smulₛₗ, map_smulₛₗ]; rfl

/-- The composite of two semilinear maps, as a formula. -/
@[simp] theorem semilinearComp_apply {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    {σ : R →+* S} {τ : S →+* T} {P Q V : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q]
    [Module S Q] [AddCommGroup V] [Module T V] (k : Q →ₛₗ[τ] V) (l : P →ₛₗ[σ] Q) (y : P) :
    semilinearComp k l y = k (l y) :=
  rfl

namespace CosimplicialDPAlgebra

variable {A : Type u} [CommRing A] (E : CosimplicialDPAlgebra.{u, v} A) (p : ℕ)

/-! ### The universal differential of a cosimplicial degree -/

/-- **The unit zero-form `1 ∈ Ω^0_{D(b)}`** of the cosimplicial degree `b`. -/
def unitZeroForm (b : ℕ) : E.forms p 0 b :=
  completedUnitZeroForm p A (E.dividedPowers b)

/-- **In exterior degree zero the de Rham differential of the cosimplicial forms is the universal
differential**, read through the unit zero-form. -/
theorem deRham_zero_smul_unitZeroForm (b : ℕ) (f : E.completedRing p b) :
    E.deRham p b 0 (f • E.unitZeroForm p b) = E.differential p b f :=
  completedDividedPowerDeRham_smul_completedUnitZeroForm p A (E.dividedPowers b) f

/-- The universal differential of a cosimplicial degree is additive. -/
theorem differential_add (b : ℕ) (x y : E.completedRing p b) :
    E.differential p b (x + y) = E.differential p b x + E.differential p b y :=
  completedFormsDifferential_add p A (E.dividedPowers b) x y

/-- **The product rule for the universal differential of a cosimplicial degree.** -/
theorem differential_mul (b : ℕ) (x y : E.completedRing p b) :
    E.differential p b (x * y) =
      x • E.differential p b y + y • E.differential p b x :=
  completedFormsDifferential_mul p A (E.dividedPowers b) x y

/-- The universal differential of a cosimplicial degree kills `1`. -/
@[simp] theorem differential_one (b : ℕ) :
    E.differential p b (1 : E.completedRing p b) = 0 :=
  completedFormsDifferential_one p A (E.dividedPowers b)

/-- **An exact one-form of a cosimplicial degree is closed.** -/
@[simp] theorem deRham_differential (b : ℕ) (x : E.completedRing p b) :
    E.deRham p b 1 (E.differential p b x) = 0 :=
  deRham_completedFormsDifferential p A (E.dividedPowers b) x

/-- **The transition maps of the forms carry the unit zero-form to the unit zero-form.** -/
@[simp] theorem formsMap_unitZeroForm {m n : SimplexCategory} (φ : m ⟶ n) :
    E.formsMap p φ 0 (E.unitZeroForm p m.len) = E.unitZeroForm p n.len :=
  completedMapDifferentialForms_completedUnitZeroForm p A (E.dividedPowers m.len)
    (E.dividedPowers n.len) (E.map φ) (E.map_isDPMorphism φ)

/-- **The universal differential commutes with the cosimplicial transition maps**: for
`φ : m ⟶ n` and `x ∈ D̂(m)`, the transition map `Ω^1_{D(m)} → Ω^1_{D(n)}` sends `d x` to
`d (φ x)`. -/
theorem formsMap_differential {m n : SimplexCategory} (φ : m ⟶ n) (x : E.completedRing p m.len) :
    E.formsMap p φ 1 (E.differential p m.len x) =
      E.differential p n.len (E.completedRingMap p φ x) := by
  have hsmul : E.formsMap p φ 0 (x • E.unitZeroForm p m.len) =
      E.completedRingMap p φ x • E.unitZeroForm p n.len :=
    (map_smulₛₗ (E.formsMapCompleted p φ 0) x (E.unitZeroForm p m.len)).trans
      (congrArg (fun z => E.completedRingMap p φ x • z) (E.formsMap_unitZeroForm p φ))
  have hd := E.formsMap_deRham p φ 0 (x • E.unitZeroForm p m.len)
  rw [E.deRham_zero_smul_unitZeroForm p m.len x] at hd
  rw [hd, hsmul, E.deRham_zero_smul_unitZeroForm p n.len]

/-! ### The cosimplicial module `b ↦ D̂(b)` -/

/-- **The cosimplicial module `b ↦ D̂(b)`**: in each cosimplicial degree the completed divided
power ring of that degree, as a module over itself, with the transition ring maps as its
semilinear transitions. -/
def structureModule : CosimplicialCompletedModule.{u, v, v} E p where
  carrier b := E.completedRing p b
  map φ :=
    { toFun := E.completedRingMap p φ
      map_add' := map_add _
      map_smul' := fun r x => by
        rw [smul_eq_mul, map_mul, smul_eq_mul] }
  map_id_apply n x := E.completedRingMap_id p n x
  map_comp_apply φ ψ x := E.completedRingMap_comp p φ ψ x

/-- The module of `Crystalline.CosimplicialDPAlgebra.structureModule` in degree `b` is `D̂(b)`. -/
@[simp] theorem structureModule_carrier (b : ℕ) :
    (E.structureModule p).carrier b = E.completedRing p b := rfl

/-- The transitions of `Crystalline.CosimplicialDPAlgebra.structureModule` are the transition
ring maps. -/
@[simp] theorem structureModule_map_apply {m n : SimplexCategory} (φ : m ⟶ n)
    (x : E.completedRing p m.len) :
    (E.structureModule p).map φ x = E.completedRingMap p φ x := rfl

/-! ### The connection of each cosimplicial degree, and the pair -/

/-- **The connection `∇ x = 1 ⊗ d x` of the cosimplicial degree `b`**, item (07JC) of
[Stacks, Tag 07JG] for the coefficient sheaf `𝒪_{X/S}`. -/
def structureNabla (b : ℕ) :
    CompletedConnection p (E.completedRing p b) (E.forms p 1 b) (E.differential p b)
      (E.completedRing p b) :=
  CompletedDeRham.unitConnection p (E.completedRing p b) (E.forms p 1 b) (E.differential p b)
    (E.differential_add p b) (E.differential_mul p b)

/-- The connection `Crystalline.CosimplicialDPAlgebra.structureNabla` sends `x` to `1 ⊗ d x`. -/
@[simp] theorem structureNabla_apply (b : ℕ) (x : E.completedRing p b) :
    E.structureNabla p b x =
      toCompletedTensor p (E.completedRing p b) (E.forms p 1 b) (E.completedRing p b)
        ((1 : E.completedRing p b) ⊗ₜ[E.completedRing p b] E.differential p b x) := rfl

/-- **The connections of the cosimplicial degrees are compatible with the cosimplicial
transition maps**: for `φ : m ⟶ n`, `∇ (φ x)` is the image of `∇ x` under the transition map
`D̂(m) ⊗̂ Ω^1_{D(m)} → D̂(n) ⊗̂ Ω^1_{D(n)}`. -/
theorem structureNabla_tensorMap {m n : SimplexCategory} (φ : m ⟶ n)
    (x : E.completedRing p m.len) :
    E.structureNabla p n.len ((E.structureModule p).map φ x) =
      (E.structureModule p).tensorMap φ 1 (E.structureNabla p m.len x) := by
  have key : (1 : E.completedRing p n.len) ⊗ₜ[E.completedRing p n.len]
        E.differential p n.len (E.completedRingMap p φ x) =
      E.completedRingMap p φ 1 ⊗ₜ[E.completedRing p n.len]
        E.formsMap p φ 1 (E.differential p m.len x) := by
    rw [map_one, E.formsMap_differential p φ x]
  exact (congrArg (toCompletedTensor p (E.completedRing p n.len) (E.forms p 1 n.len)
      (E.completedRing p n.len)) key).trans
    (CosimplicialCompletedModule.tensorMap_of_tmul (E.structureModule p) φ 1
      (1 : E.completedRing p m.len) (E.differential p m.len x)).symm

/-- **In each cosimplicial degree the de Rham differentials of the connection
`Crystalline.CosimplicialDPAlgebra.structureNabla` compose to zero.** -/
theorem structureIsSquareZero (b : ℕ) :
    CompletedDeRham.IsSquareZero p (E.completedRing p b) (fun a => E.forms p a b) (E.wedge p b)
      (E.deRham p b) (E.completedRing p b) (E.structureNabla p b) (E.isGradedLeibniz p b) :=
  CompletedDeRham.isSquareZero_unitConnection p (E.completedRing p b) (fun a => E.forms p a b)
    (E.wedge p b) (E.deRham p b) (E.differential p b) (E.differential_add p b)
    (E.differential_mul p b) (E.isGradedLeibniz p b) (E.isGradedExterior p b)
    (E.differential_one p b) (E.deRham_differential p b)

/-- **The cosimplicial module `b ↦ D̂(b)` with the connection `∇ x = 1 ⊗ d x` in each
cosimplicial degree**, as a `Crystalline.CosimplicialCompletedPair`. -/
def structurePair : CosimplicialCompletedPair.{u, v, v} E p where
  toCosimplicialCompletedModule := E.structureModule p
  nabla := E.structureNabla p
  nabla_tensorMap φ x := E.structureNabla_tensorMap p φ x
  isSquareZero := E.structureIsSquareZero p

/-- The cosimplicial module of `Crystalline.CosimplicialDPAlgebra.structurePair` is
`Crystalline.CosimplicialDPAlgebra.structureModule`. -/
@[simp] theorem structurePair_toCosimplicialCompletedModule :
    (E.structurePair p).toCosimplicialCompletedModule = E.structureModule p := rfl

/-- The connection of `Crystalline.CosimplicialDPAlgebra.structurePair` in degree `b` is
`Crystalline.CosimplicialDPAlgebra.structureNabla`. -/
@[simp] theorem structurePair_nabla (b : ℕ) :
    (E.structurePair p).nabla b = E.structureNabla p b := rfl

/-- **The double complex `K^{a,b} = Ω^a_{D(b)}` of [Stacks, Proposition 60.21.3, Tag 07LG] for
the structure sheaf**, as a cochain complex of cosimplicial abelian groups. -/
def structureDoubleComplex : CochainComplex (CosimplicialObject AddCommGrpCat.{v}) ℕ :=
  (E.structurePair p).doubleComplex

/-- The exterior degree `a` of `K` is the column `b ↦ D̂(b) ⊗̂_{D(b)} Ω^a_{D(b)}`. -/
theorem structureDoubleComplex_X (a : ℕ) :
    (E.structureDoubleComplex p).X a = (E.structureModule p).column a := rfl

/-- The differential of `K` is the de Rham differential of the connections. -/
theorem structureDoubleComplex_d (a : ℕ) :
    (E.structureDoubleComplex p).d a (a + 1) = (E.structurePair p).columnDifferential a :=
  (E.structurePair p).doubleComplex_d a

end CosimplicialDPAlgebra

/-! ### The pair of the actual cosimplicial envelope `D(*)` -/

section Envelope

variable (s : AffineCrystallineSituation.{u, uC}) {ι : Type w}
  (f : MvPolynomial ι s.A →ₐ[s.A] s.C)

/-- **The cosimplicial envelope `D(*)` of [Stacks, Equation 60.17.3, Tag 07JF] with the
connection of [Stacks, Tag 07JC] in each cosimplicial degree**, as a
`Crystalline.CosimplicialCompletedPair`: `Crystalline.CosimplicialDPAlgebra.structurePair` at
`Crystalline.envelopeDPAlgebra`. -/
def envelopeStructurePair :
    CosimplicialCompletedPair.{u, max u w, max u w} (envelopeDPAlgebra s f) s.p :=
  (envelopeDPAlgebra s f).structurePair s.p

/-- **The double complex `K^{a,b} = Ω^a_{D(b)}` of [Stacks, Proposition 60.21.3, Tag 07LG] for
the actual cosimplicial envelope and the structure sheaf.**  Its `a` direction is the completed
de Rham complex of `D(b)` and its `b` direction is the cosimplicial one. -/
def envelopeStructureDoubleComplex :
    CochainComplex (CosimplicialObject AddCommGrpCat.{max u w}) ℕ :=
  (envelopeDPAlgebra s f).structureDoubleComplex s.p

/-- The exterior degree `a` of `K` is the column `b ↦ D̂(b) ⊗̂_{D(b)} Ω^a_{D(b)}`. -/
theorem envelopeStructureDoubleComplex_X (a : ℕ) :
    (envelopeStructureDoubleComplex s f).X a =
      ((envelopeDPAlgebra s f).structureModule s.p).column a := rfl

/-- The differential of `K` is the de Rham differential of the connections. -/
theorem envelopeStructureDoubleComplex_d (a : ℕ) :
    (envelopeStructureDoubleComplex s f).d a (a + 1) =
      (envelopeStructurePair s f).columnDifferential a :=
  (envelopeDPAlgebra s f).structureDoubleComplex_d s.p a

end Envelope

end Crystalline

end
