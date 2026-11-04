module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerBridge
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.Basic

/-!
# Relative Proj as a functor: quadruples and the sets `F_d(T)`

Let `S` be a scheme and `𝒜` a graded `𝒪_S`-algebra (Situation 01NN), and fix an integer `d`.
Section 01NS introduces, for a scheme `T`, the *quadruples* `(d, f : T → S, L, ψ)` over `T`: a
morphism of schemes `f : T → S`, an invertible `𝒪_T`-module `L`, and a homomorphism of graded
`𝒪_T`-algebras `ψ : f^*𝒜^{(d)} → ⨁_{n ≥ 0} L^{⊗ n}` whose degree-one component
`f^*𝒜_d → L` is surjective. Two quadruples over the same `f` are *strictly equivalent* when an
isomorphism `β : L → L'` carries `ψ` to `ψ'`, and `F_d(T)` is the set of strict equivalence
classes.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple`: **a quadruple over a test
  scheme**, the invertible module `L` together with the map `ψ` and the surjectivity of its
  degree-one component.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.oneIso`: the identification
  `L^{⊗ 1} = L` through which the degree-one component of `ψ` is read.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.StrictlyEquivalent`: **strict
  equivalence of quadruples**, and `Quadruple.setoid` the setoid it defines.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd`: **the set `F_d(T)`** of strict
  equivalence classes of quadruples over `T`, fibred over the morphisms `T ⟶ S`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.strictlyEquivalent_equivalence`:
  **strict equivalence of quadruples is an equivalence relation.**
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.strictlyEquivalent_iff_exists_hom`:
  an isomorphism of Laurent algebras carrying `ψ` to `ψ'` is already enough; the degree-one
  isomorphism `β` of the source is its degree-one component.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.mk_eq_mk_iff`: two quadruples over the same
  morphism have the same class in `F_d(T)` exactly when they are strictly equivalent.

## Implementation notes

The map `ψ` of a quadruple is `RelativeProjQcohSheaf.Twisting`, which is how Tag 01O6 already
spells it: a multiplicative, unit-preserving family `f^*𝒜_{id} ⟶ L^{⊗ i}` into the Laurent
algebra of `L`. Tag 01O6's construction does not use the surjectivity of the degree-one
component, so `Twisting` does not assume it; it is a field of `Quadruple`, where Section 01NS
does require it.

Strict equivalence is recorded as an isomorphism `β : L ≅ L'` **together with** the isomorphism
`γ` of Laurent algebras it induces, rather than as `β` alone. The source writes the condition as
`β ∘ ψ = ψ'`, where `β ∘ -` means the map induced by `β` on all integral tensor powers; that
induced map is exactly a homomorphism of graded algebras whose degree-one component is `β`, and
such a homomorphism is uniquely determined by its degree-one component, because multiplication
by the degree-one piece generates the Laurent algebra. So the two formulations describe the same
relation, and the second is the one that does not require the functoriality of the Laurent
algebra in `L` to be stated. The degree-one component is compared with `β` through
`Quadruple.oneIso`, the identification `L^{⊗ 1} = L` of Tag 01CU.

The invertibility of `L` is a field of `Quadruple` rather than an instance argument, since
`F_d(T)` quantifies over `L`; `Quadruple.instIsInvertible` feeds it back to instance resolution,
which is what lets the Laurent algebra of `P.L` be written without a `letI` at every use.
`Quadruple.oneIso` is an `abbrev` because its source `(laurent P.L).piece 1` is only
definitionally the first tensor power of `P.L`. `Quadruple.instIsEquivalenceTensorRight` is
stated as well, even though it is an instance of
`Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible` applied to the previous
one: that general instance is found by neither `infer_instance` nor the elaborator at the
spelling of the tensor-power functor used here, while the same instance applied is accepted.

## Not done here

The functoriality of `F_d` is not set up in this module, but it is available downstream and is
not conditional on anything. The pullback of a quadruple along a morphism `g : T' ⟶ T` of test
schemes is `...RelativeProjQcohSheaf.QuadruplePullback.Quadruple.pullback`; it respects strict
equivalence by `...RelativeProjQcohSheaf.UnionPullback.Quadruple.StrictlyEquivalent.pullback`, so
it descends to the map `F_d(T) → F_d(T')` of `...UnionPullback.Fd.pullback`; and the two functor
laws for that map, `...RelativeProjQcohSheaf.UnionFunctor.Fd.pullback_id` and
`...UnionFunctor.Fd.pullback_comp`, assemble it into the functor `...UnionFunctor.Fd.functor`.

The inputs that construction needed, recorded here while they were still missing, are the
comparison `g^*(L^{⊗ n}) ≅ (g^*L)^{⊗ n}` of the integral tensor powers of an invertible module
with pullback (`...RelativeProjQcohSheaf.LaurentPullback.pieceIso`, with its compatibility
`...LaurentPullback.pieceIso_mul` with the coherent multiplication of Tag 01CU in every integral
bidegree, its composition law `...LaurentComposition.pieceIso_comp` and its identity law
`...LaurentIdentity.pieceIso_id`), the degreewise comparison `M^{⊗ i} ≅ M'^{⊗ i}` induced by an
isomorphism `M ≅ M'` of invertible modules (`...LaurentCongr.congrIso`), which is what lets a
strict equivalence absorb the residual isomorphism `(𝟙_T)^*L ≅ L` or `g'^*g^*L ≅ (g' ≫ g)^*L`,
and the identification `...LaurentPullback.mulSheaf_laurent` of the multiplication
`SheafOfModules.GradedAlgebra.mulSheaf (laurent L)` that `Twisting.app_mul` is stated against
with the `Stacks.SheafOfModules.TensorPower.coherentMulIso` that `pieceIso_mul` is stated for.

What is still carried, in
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.Representable`, where Tag 01NV — the
representability of `F_d` by a scheme — is stated, is the Zariski sheaf property of `F_d`, the
smallness of its values, and the representability over an affine base (Tag 01NU). The
restriction maps are not among them.

## References

* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01O6](https://stacks.math.columbia.edu/tag/01O6)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

open AlgebraicGeometry Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.SheafOfModules.TensorPower

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {T S : Scheme.{u}}

/-- **Stacks Project, Section 01NS.** A quadruple `(d, f : T → S, L, ψ)` over the test scheme
`T`: an invertible `𝒪_T`-module `L`, a homomorphism `ψ` of graded `𝒪_T`-algebras from the
pullback of the `d`-th Veronese regrading of `𝒜` to the Laurent algebra of `L`, and the
requirement that the degree-one component `f^*𝒜_d ⟶ L` of `ψ` be surjective.

The integer `d` and the morphism `f` are parameters; the pair `(L, ψ)` is the data. -/
@[stacks 01NS "quadruples over a test scheme"]
structure Quadruple (f : T ⟶ S)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) (d : ℤ) where
  /-- The invertible module on the test scheme. -/
  L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)
  /-- `L` is invertible. -/
  isInvertible : Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L
  /-- The map `ψ : f^*𝒜^{(d)} ⟶ ⨁_{n ∈ ℤ} L^{⊗ n}`. -/
  twisting :
    letI : Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L :=
      isInvertible
    Twisting f A d L
  /-- The degree-one component `f^*𝒜_d ⟶ L^{⊗ 1}` of `ψ` is surjective. -/
  epi_app_one :
    letI : Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L :=
      isInvertible
    Epi (twisting.app 1)

namespace Quadruple

variable {f : T ⟶ S}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}

/-- The invertible module of a quadruple is invertible, as an instance. -/
instance instIsInvertible (P : Quadruple f A d) :
    Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) P.L :=
  P.isInvertible

/-- The invertible module of a quadruple is invertible in the spelling the integral tensor
powers of Tag 01CU are indexed by. -/
instance instIsInvertibleAlgebraicGeometry (P : Quadruple f A d) :
    AlgebraicGeometry.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T)
      P.L :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ P.isInvertible

/-- Tensoring on the right by the invertible module of a quadruple is an autoequivalence of the
sheaves of modules on the test scheme, which is the datum the integral tensor powers are indexed
by. -/
instance instIsEquivalenceTensorRight (P : Quadruple f A d) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨T.toRingedSpace.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ T.toRingedSpace.presheaf
          (forget₂ CommRingCat RingCat) (isSheafStruct T)⟩).flip.obj P.L).IsEquivalence :=
  Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible _ _ _

/-- The identification `L^{⊗ 1} = L` of Tag 01CU, through which the degree-one component of `ψ`
is compared with an isomorphism of the invertible modules. -/
abbrev oneIso (P : Quadruple f A d) : (laurent P.L).piece 1 ≅ P.L :=
  tensorPowerOneIso T.toRingedSpace.presheaf (isSheafStruct T) P.L

/-- The isomorphism `L^{⊗ 1} ≅ (L')^{⊗ 1}` of degree-one pieces determined by an isomorphism
`β : L ≅ L'` of the invertible modules of two quadruples. -/
abbrev pieceOneIso {P Q : Quadruple f A d} (β : P.L ≅ Q.L) :
    (laurent P.L).piece 1 ≅ (laurent Q.L).piece 1 :=
  P.oneIso ≪≫ β ≪≫ Q.oneIso.symm

/-- **Stacks Project, Section 01NS.** Two quadruples over the same morphism `f` are *strictly
equivalent* when there is an isomorphism `β : L ≅ L'` of their invertible modules with
`β ∘ ψ = ψ'`.

The composite `β ∘ ψ` is spelled through the isomorphism `γ` of Laurent algebras induced by `β`:
the condition is that `γ` be an isomorphism of sheaves of graded algebras whose degree-one
component is `β` and which carries `ψ` to `ψ'` in every degree. -/
@[stacks 01NS "strict equivalence of quadruples"]
def StrictlyEquivalent (P Q : Quadruple f A d) : Prop :=
  ∃ (β : P.L ≅ Q.L) (γ : laurent P.L ≅ laurent Q.L),
    γ.hom.app 1 = (pieceOneIso β).hom ∧
      ∀ n : ℤ, P.twisting.app n ≫ γ.hom.app n = Q.twisting.app n

/-- The homogeneous components of an isomorphism of sheaves of graded algebras are
isomorphisms. -/
private theorem hom_app_inv_app
    {R : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf T.toRingedSpace)}
    {R' : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf T.toRingedSpace)}
    (γ : R ≅ R') (n : ℤ) : γ.hom.app n ≫ γ.inv.app n = 𝟙 _ :=
  congrArg (fun φ : R ⟶ R => φ.app n) γ.hom_inv_id

/-- A homogeneous component of the inverse of an isomorphism of sheaves of graded algebras is
the inverse of the corresponding component of the isomorphism. -/
private theorem inv_app_eq
    {R : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf T.toRingedSpace)}
    {R' : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf T.toRingedSpace)}
    (γ : R ≅ R') (n : ℤ) {e : R.piece n ≅ R'.piece n} (h : γ.hom.app n = e.hom) :
    γ.inv.app n = e.inv := by
  rw [← Category.id_comp (γ.inv.app n), ← e.inv_hom_id, Category.assoc, ← h,
    hom_app_inv_app γ n, Category.comp_id]

/-- **Strict equivalence of quadruples is an equivalence relation.** -/
@[stacks 01NS "strict equivalence of quadruples"]
theorem strictlyEquivalent_equivalence :
    Equivalence (StrictlyEquivalent (f := f) (A := A) (d := d)) where
  refl P := ⟨Iso.refl P.L, Iso.refl (laurent P.L), by simp, by simp⟩
  symm := by
    rintro P Q ⟨β, γ, h1, hψ⟩
    refine ⟨β.symm, γ.symm, ?_, fun n => ?_⟩
    · change γ.inv.app 1 = (pieceOneIso β.symm).hom
      rw [inv_app_eq γ 1 h1]
      simp
    · change Q.twisting.app n ≫ γ.inv.app n = P.twisting.app n
      rw [← hψ n, Category.assoc, hom_app_inv_app γ n, Category.comp_id]
  trans := by
    rintro P Q R ⟨β, γ, h1, hψ⟩ ⟨β', γ', h1', hψ'⟩
    refine ⟨β ≪≫ β', γ ≪≫ γ', ?_, fun n => ?_⟩
    · change γ.hom.app 1 ≫ γ'.hom.app 1 = (pieceOneIso (β ≪≫ β')).hom
      rw [h1, h1']
      simp
    · change P.twisting.app n ≫ γ.hom.app n ≫ γ'.hom.app n = R.twisting.app n
      rw [← Category.assoc, hψ n, hψ' n]

/-- The degree-`n` component of an isomorphism of the Laurent algebras, as an isomorphism. -/
private def appIso {P Q : Quadruple f A d} (γ : laurent P.L ≅ laurent Q.L) (n : ℤ) :
    (laurent P.L).piece n ≅ (laurent Q.L).piece n where
  hom := γ.hom.app n
  inv := γ.inv.app n
  hom_inv_id := hom_app_inv_app γ n
  inv_hom_id := hom_app_inv_app γ.symm n

/-- An isomorphism of the Laurent algebras carrying `ψ` to `ψ'` already witnesses strict
equivalence: its degree-one component is the isomorphism `β` of the source. -/
theorem strictlyEquivalent_iff_exists_hom (P Q : Quadruple f A d) :
    StrictlyEquivalent P Q ↔
      ∃ γ : laurent P.L ≅ laurent Q.L,
        ∀ n : ℤ, P.twisting.app n ≫ γ.hom.app n = Q.twisting.app n := by
  refine ⟨fun ⟨_, γ, _, hψ⟩ => ⟨γ, hψ⟩, fun ⟨γ, hψ⟩ => ?_⟩
  refine ⟨P.oneIso.symm ≪≫ appIso γ 1 ≪≫ Q.oneIso, γ, ?_, hψ⟩
  simp [appIso]

/-- The setoid of strict equivalence of quadruples over a fixed morphism `f : T ⟶ S`. -/
def setoid (f : T ⟶ S)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) (d : ℤ) :
    Setoid (Quadruple f A d) where
  r := StrictlyEquivalent
  iseqv := strictlyEquivalent_equivalence

end Quadruple

/-- **Stacks Project, Section 01NS.** The set `F_d(T)` of strict equivalence classes of
quadruples `(d, f : T → S, L, ψ)` over the test scheme `T`.

Strict equivalence relates only quadruples over the same morphism `f : T ⟶ S`, so the set of
classes is fibred over the morphisms `T ⟶ S`, which is the morphism recorded by a quadruple. -/
@[stacks 01NS "the set of strict equivalence classes of quadruples over a test scheme"]
def Fd (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) (d : ℤ)
    (T : Scheme.{u}) : Type (u + 1) :=
  Σ f : T ⟶ S, Quotient (Quadruple.setoid f A d)

/-- The class in `F_d(T)` of a quadruple over `f : T ⟶ S`. -/
def Fd.mk {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}
    (f : T ⟶ S) (P : Quadruple f A d) : Fd A d T :=
  ⟨f, Quotient.mk _ P⟩

/-- Two quadruples over the same morphism have the same class in `F_d(T)` exactly when they are
strictly equivalent. -/
theorem Fd.mk_eq_mk_iff
    {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}
    {f : T ⟶ S} (P Q : Quadruple f A d) :
    Fd.mk f P = Fd.mk f Q ↔ Quadruple.StrictlyEquivalent P Q := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h2 : (Quotient.mk (Quadruple.setoid f A d) P) = Quotient.mk _ Q :=
      eq_of_heq (Sigma.mk.injEq .. ▸ h).2
    exact Quotient.exact h2
  · exact congrArg (fun q => (⟨f, q⟩ : Fd A d T)) (Quotient.sound h)

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
