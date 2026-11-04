module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.QuadruplePullback

/-!
# The pullback of a quadruple respects the identifications, and the map `F(T) → F(T')`

Let `S` be a scheme and `𝒜` a graded `𝒪_S`-algebra (Situation 01NN). Section 01NS attaches to each
`d ≥ 1` the quadruples `(d, f : T → S, L, ψ)` over a test scheme `T`, the display 01NX assembles
their classes into `F(T) = ⋃_{d ≥ 1} F_d(T)`, and Tag 01NY asserts that `F` is representable by a
scheme.

`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.QuadruplePullback` constructs the pullback
`Quadruple.pullback` of a quadruple along a morphism `g : T' ⟶ T` of test schemes. That is not yet
a map `F(T) → F(T')`: the display 01NX makes two identifications — strict equivalence inside one
degree (`Quadruple.StrictlyEquivalent`) and equivalence across degrees (`Quadruple.Equivalent`) —
and the pullback has to carry each to one of the same kind. This file proves that it does, and
descends it to the union.

## The route taken, and the one avoided

Both identifications are stated through an isomorphism of the Laurent algebras of the invertible
modules of the two quadruples. The sibling modules record the missing input as the **functoriality
of `Stacks.SheafOfModules.TensorPower.laurentAlgebra` in the invertible module** together with the
naturality of `Stacks.TensorPowerPullback.pullbackIntPowIso` in that variable: from `φ : L ≅ L'`
one would build `⨁_n L^{⊗ n} ≅ ⨁_n (L')^{⊗ n}` and transport the witness along it.

That is **not** what is done here, and it is not needed. The witness is transported along the
comparison of the integral tensor powers with pullback instead: writing `c_i` for the comparison
`g^*(L^{⊗ i}) ≅ (g^*L)^{⊗ i}` of
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.laurentPullback`, a component
`θ : L^{⊗ p} ⟶ (L')^{⊗ q}` of the witness is carried to

`c_p⁻¹ ≫ g^*θ ≫ c'_q : (g^*L)^{⊗ p} ⟶ (g^*L')^{⊗ q}`,

which is `laurentTransport` below. Multiplicativity of the transported witness is then the
multiplicativity `laurentPullback_mul` of `c`, which is already proved, together with the
naturality of the comparison of Tag 01CD; and the compatibility with `ψ` is immediate, because the
copy of `c` inside `Twisting.pullbackApp` cancels against the `c_p⁻¹` of the transport. No
functoriality of the Laurent algebra in the invertible module occurs anywhere below.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.laurentTransport`: **the transport of a morphism
  between homogeneous pieces of two Laurent algebras along a morphism `g : T' ⟶ T` of test
  schemes.**
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.laurentTransportIso`: the same for an
  isomorphism.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.laurentPullbackHom` and `laurentPullbackIso`:
  **the Laurent algebra of an invertible module is functorial under pullback**: a homomorphism
  (resp. isomorphism) `⨁_n L^{⊗ n} ⟶ ⨁_n (L')^{⊗ n}` of sheaves of graded algebras is carried to
  one `⨁_n (g^*L)^{⊗ n} ⟶ ⨁_n (g^*L')^{⊗ n}`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.pullback`: **the map `F_d(T) → F_d(T')`** at
  a fixed degree, induced by a morphism `g : T' ⟶ T` of test schemes.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.F.pullback`: **the map `F(T) → F(T')`** induced
  by a morphism `g : T' ⟶ T` of test schemes.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.laurentTransport_mulSheaf`: **the transport
  carries a multiplicativity relation between two Laurent algebras on `T` to one between their
  pullbacks**, which is the engine of everything below.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.pullbackApp_comp_laurentTransport`: the
  transport is compatible with the pullback of the map `ψ` of a quadruple.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.StrictlyEquivalent.pullback`:
  **the pullback of a quadruple respects strict equivalence.**
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.CompatibleAt.pullback` and
  `Quadruple.Equivalent.pullback`: **the pullback of a quadruple respects a comparison at a common
  multiple of the degrees, hence equivalence of quadruples of different degrees.**
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.F.pullback_mk`: the induced map sends the point
  of a quadruple to the point of its pullback.

## Implementation notes

`mulSheaf_comp_app` and `map_mul_of_mulSheaf_comp` are the two directions of the dictionary between
the `map_mul` field of `SheafOfModules.GradedAlgebra.Hom`, which is a statement about local
sections, and the equation between morphisms out of the tensor product sheaf that the
multiplicativity of the comparisons is stated by. They are the ringed-space instance of
`SheafOfModules.GradedAlgebra.mulSheaf_comp_eq_iff`, stated at the spelling
`Stacks.RingedSpace.structureRingSheaf` in which the Laurent algebra of this directory lives; the
general form is indexed by `SheafOfModules.toRingCat`, and the two spellings are equal by `rfl`
without being syntactically equal, so a goal mixing them is not type-correct at `implicit`
transparency.

The unit clause is the cheapest of the three. The global unit of a Laurent algebra is the identity
of the structure sheaf (`oneHom_laurent`), so a unit-preserving component in degree zero *is* the
identity; and in degree zero the comparison `c_0` is the structure-sheaf comparison of Tag 01CD
(`laurentPullback_zero`) for every invertible module at once, so the transport of the identity is
the identity.

## Not done here

* **Neither `F` nor `F_d` is made a functor here.** What is built is the map `F(T) → F(T')`, and
  its fixed-degree analogue `F_d(T) → F_d(T')`, of a morphism of test schemes; the comparison of
  `F.pullback (𝟙 T)` with the identity and of
  `F.pullback (g' ≫ g)` with the composite, and the same for `Fd.pullback`, is
  `StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.UnionFunctor`. The first needs the
  identity law `(𝟙 Z)^* ≅ 𝟭` for the pullback of sheaves of modules over a ringed space, which
  is `Stacks.PullbackTensorCoherence.pullbackIdIso`, together with the unit coherence relating it
  to `Stacks.PullbackCompMonoidal.comparison`; the second needs the associativity coherence of
  that comparison. Both coherences are proved in that module, from the pseudofunctoriality of the
  pullback.
* The representability of `F` by a scheme is not stated here, and neither is a functor-of-points
  comparison with the relative `Proj` of `𝒜`.
* **The functoriality of the Laurent algebra in the invertible module is still not available**, and
  neither is the naturality of `Stacks.TensorPowerPullback.pullbackIntPowIso` in that variable.
  What is proved here is functoriality under *pullback* (`laurentPullbackHom`), which is a
  different statement: the two Laurent algebras compared live on different schemes. Nothing below
  compares two Laurent algebras on one scheme.
* The inverse limit over the quasi-compact opens, by which the display 01NX extends `F` from a
  quasi-compact test scheme to an arbitrary one, is not constructed *here*. It is
  `...RelativeProjQcohSheaf.F.limFunctor` of
  `StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.UnionRepresentable`, built out of the map
  below, and `...RelativeProjQcohSheaf.F.limEquiv_naturality` of
  `...RelativeProjQcohSheaf.UnionLimitExtension` says that its identification with the union at a
  quasi-compact test scheme commutes with this map, so the two cases of the source's definition
  of `F` are two cases of one functor.

## References

* [Stacks Project, Tag 01NY](https://stacks.math.columbia.edu/tag/01NY)
* [Stacks Project, Tag 01NX](https://stacks.math.columbia.edu/tag/01NX)
* [Stacks Project, Tag 01NW](https://stacks.math.columbia.edu/tag/01NW)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory TopologicalSpace

open AlgebraicGeometry Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.SheafOfModules.TensorPower

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

universe v₁ v₂ u₁ u₂ u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

/-! ### The transport of a multiplicativity relation, in an abstract monoidal setting -/

section Abstract

variable {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D]
  {E : Type u₂} [Category.{v₂} E] [MonoidalCategory E] (G : D ⥤ E)

/-- **A multiplicativity relation is carried by a comparison of a monoidal functor, in every
degree.** Let `G` be a functor between monoidal categories, let `tA` and `tB` be comparisons
`G(X ⊗ Y) ⟶ G X ⊗ G Y` compatible with two multiplications `m` and `n` upstairs through
isomorphisms `c` and morphisms `d`, and let `u`, `u'`, `w` satisfy the multiplicativity relation
of a homomorphism of graded objects for `m` and `n`. Then the conjugates of `u`, `u'` and `w` by
`c` and `d` satisfy it for the two multiplications downstairs.

This is stated abstractly, with the three compatibilities as hypotheses rather than as the
naturality and monoidality of a comparison, because that is what makes it usable: instantiated at
the pullback of sheaves of modules it is `laurentTransport_mulSheaf`, whose goal mixes the two
spellings of the structure sheaf of a scheme and is therefore not type-correct at `implicit`
transparency, so `rw` and `simp only [Category.assoc]` refuse it. Here nothing is mixed and the
rewriting goes through; the crossing happens once, in the instantiation. -/
theorem mul_transport_of_comparison {Ap Ap' App Bq Bq' Bqq : D}
    {A'p A'p' A'pp B'q B'q' B'qq : E}
    (cp : G.obj Ap ⟶ A'p) [IsIso cp] (cp' : G.obj Ap' ⟶ A'p') [IsIso cp']
    (cpp : G.obj App ⟶ A'pp) [IsIso cpp]
    (dq : G.obj Bq ⟶ B'q) (dq' : G.obj Bq' ⟶ B'q') (dqq : G.obj Bqq ⟶ B'qq)
    (tA : G.obj (Ap ⊗ Ap') ⟶ G.obj Ap ⊗ G.obj Ap') [IsIso tA]
    (tB : G.obj (Bq ⊗ Bq') ⟶ G.obj Bq ⊗ G.obj Bq')
    (m : Ap ⊗ Ap' ⟶ App) (m' : A'p ⊗ A'p' ⟶ A'pp)
    (n : Bq ⊗ Bq' ⟶ Bqq) (n' : B'q ⊗ B'q' ⟶ B'qq)
    (u : Ap ⟶ Bq) (u' : Ap' ⟶ Bq') (w : App ⟶ Bqq)
    (hm : tA ≫ (cp ⊗ₘ cp') ≫ m' = G.map m ≫ cpp)
    (hn : tB ≫ (dq ⊗ₘ dq') ≫ n' = G.map n ≫ dqq)
    (hnat : G.map (u ⊗ₘ u') ≫ tB = tA ≫ (G.map u ⊗ₘ G.map u'))
    (h : m ≫ w = (u ⊗ₘ u') ≫ n) :
    m' ≫ inv cpp ≫ G.map w ≫ dqq =
      ((inv cp ≫ G.map u ≫ dq) ⊗ₘ (inv cp' ≫ G.map u' ≫ dq')) ≫ n' := by
  have hcu : (cp ⊗ₘ cp') ≫
        ((inv cp ≫ G.map u ≫ dq) ⊗ₘ (inv cp' ≫ G.map u' ≫ dq')) =
      (G.map u ⊗ₘ G.map u') ≫ (dq ⊗ₘ dq') := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [IsIso.hom_inv_id_assoc]
    rw [← MonoidalCategory.tensorHom_comp_tensorHom]
  have hmw : G.map m ≫ G.map w = G.map (u ⊗ₘ u') ≫ G.map n :=
    (G.map_comp m w).symm.trans ((congrArg G.map h).trans (G.map_comp (u ⊗ₘ u') n))
  have hLHS : tA ≫ (cp ⊗ₘ cp') ≫ m' ≫ inv cpp ≫ G.map w ≫ dqq =
      G.map (u ⊗ₘ u') ≫ G.map n ≫ dqq := by
    rw [← Category.assoc (cp ⊗ₘ cp'), ← Category.assoc tA, hm, Category.assoc,
      IsIso.hom_inv_id_assoc, ← Category.assoc, hmw, Category.assoc]
  have hRHS : tA ≫ (cp ⊗ₘ cp') ≫
        ((inv cp ≫ G.map u ≫ dq) ⊗ₘ (inv cp' ≫ G.map u' ≫ dq')) ≫ n' =
      G.map (u ⊗ₘ u') ≫ G.map n ≫ dqq := by
    rw [← Category.assoc (cp ⊗ₘ cp'), hcu, Category.assoc, ← Category.assoc tA, ← hnat,
      Category.assoc, hn]
  refine (cancel_epi (tA ≫ (cp ⊗ₘ cp'))).mp ?_
  simp only [Category.assoc]
  exact hLHS.trans hRHS.symm

end Abstract

variable {T' T S : Scheme.{u}}

/-! ### Homomorphisms of sheaves of graded algebras, degreewise and through `mulSheaf` -/

section GradedAlgebraHom

variable {Z : RingedSpace.{u, u}}
  (A B : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Z))

/-- **A homomorphism of sheaves of graded algebras commutes with the morphism-level
multiplications.** This is one direction of `SheafOfModules.GradedAlgebra.mulSheaf_comp_eq_iff`,
at the spelling `Stacks.RingedSpace.structureRingSheaf` of the structure sheaf of a ringed
space. -/
theorem mulSheaf_comp_app (φ : A ⟶ B) (i j : ℤ) :
    A.mulSheaf i j ≫ φ.app (i + j) = (φ.app i ⊗ₘ φ.app j) ≫ B.mulSheaf i j :=
  tensor_hom_ext fun U x y =>
    (congrArg ((φ.app (i + j)).val.app U)
        (SheafOfModules.GradedAlgebra.mulSheaf_unit A i j U x y)).trans
      ((φ.map_mul i j U x y).trans
        ((SheafOfModules.GradedAlgebra.mulSheaf_unit B i j U
              ((φ.app i).val.app U x) ((φ.app j).val.app U y)).symm.trans
          (congrArg ((B.mulSheaf i j).val.app U)
            (tensorHom_tmul (φ.app i) (φ.app j) U x y).symm)))

/-- **A degreewise family of morphisms commuting with the morphism-level multiplications preserves
products of homogeneous local sections**, which is the `map_mul` field of
`SheafOfModules.GradedAlgebra.Hom`. This is the other direction of
`SheafOfModules.GradedAlgebra.mulSheaf_comp_eq_iff`. -/
theorem map_mul_of_mulSheaf_comp (φ : ∀ n : ℤ, A.piece n ⟶ B.piece n)
    (h : ∀ i j : ℤ, A.mulSheaf i j ≫ φ (i + j) = (φ i ⊗ₘ φ j) ≫ B.mulSheaf i j)
    (i j : ℤ) (U : (Opens Z.carrier)ᵒᵖ)
    (x : (A.piece i).val.obj U) (y : (A.piece j).val.obj U) :
    (φ (i + j)).val.app U ((A.mul i j).app U x y) =
      (B.mul i j).app U ((φ i).val.app U x) ((φ j).val.app U y) :=
  (((congrArg ((φ (i + j)).val.app U)
            (SheafOfModules.GradedAlgebra.mulSheaf_unit A i j U x y)).symm.trans
        (congrArg (fun ψ => ψ.val.app U (tmul Z (A.piece i) (A.piece j) U x y)) (h i j))).trans
      (congrArg ((B.mulSheaf i j).val.app U)
        (tensorHom_tmul (φ i) (φ j) U x y))).trans
    (SheafOfModules.GradedAlgebra.mulSheaf_unit B i j U
      ((φ i).val.app U x) ((φ j).val.app U y))

/-- **A degreewise family of morphisms commuting with the morphism-level multiplications is a
homomorphism of sheaves of graded algebras.** -/
def homOfMulSheaf (φ : ∀ n : ℤ, A.piece n ⟶ B.piece n)
    (h : ∀ i j : ℤ, A.mulSheaf i j ≫ φ (i + j) = (φ i ⊗ₘ φ j) ≫ B.mulSheaf i j) : A ⟶ B :=
  { app := φ
    map_mul := map_mul_of_mulSheaf_comp A B φ h }

/-- The degree-`n` component of `homOfMulSheaf A B φ h` is `φ n`. -/
@[simp] theorem homOfMulSheaf_app (φ : ∀ n : ℤ, A.piece n ⟶ B.piece n)
    (h : ∀ i j : ℤ, A.mulSheaf i j ≫ φ (i + j) = (φ i ⊗ₘ φ j) ≫ B.mulSheaf i j) (n : ℤ) :
    (homOfMulSheaf A B φ h).app n = φ n := rfl

end GradedAlgebraHom

/-! ### Transporting a morphism of homogeneous pieces along a morphism of test schemes -/

section Transport

variable (g : T' ⟶ T) (L L' : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L']

/-- **The transport of a morphism `L^{⊗ p} ⟶ (L')^{⊗ q}` along a morphism `g : T' ⟶ T` of test
schemes**: pull it back and cancel the comparison `g^*(L^{⊗ i}) ≅ (g^*L)^{⊗ i}` of the integral
tensor powers of Tag 01CU on either side. -/
def laurentTransport (p q : ℤ) (u : (laurent L).piece p ⟶ (laurent L').piece q) :
    (laurent ((pullbackFunctor (ringedSpaceHom g)).obj L)).piece p ⟶
      (laurent ((pullbackFunctor (ringedSpaceHom g)).obj L')).piece q :=
  inv (laurentPullback g L p) ≫
    (pullbackFunctor (ringedSpaceHom g)).map u ≫ laurentPullback g L' q

/-- The transport of an isomorphism of homogeneous pieces, as an isomorphism. -/
def laurentTransportIso (p q : ℤ) (e : (laurent L).piece p ≅ (laurent L').piece q) :
    (laurent ((pullbackFunctor (ringedSpaceHom g)).obj L)).piece p ≅
      (laurent ((pullbackFunctor (ringedSpaceHom g)).obj L')).piece q :=
  (asIso (laurentPullback g L p)).symm ≪≫
    (pullbackFunctor (ringedSpaceHom g)).mapIso e ≪≫ asIso (laurentPullback g L' q)

/-- The forward morphism of `laurentTransportIso g L L' p q e` is the transport of `e.hom`. -/
@[simp] theorem laurentTransportIso_hom (p q : ℤ)
    (e : (laurent L).piece p ≅ (laurent L').piece q) :
    (laurentTransportIso g L L' p q e).hom = laurentTransport g L L' p q e.hom := rfl

/-- The transport of a composite is the composite of the transports: the two inner copies of the
comparison of the integral tensor powers cancel. -/
theorem laurentTransport_comp
    (L'' : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L'']
    (p q r : ℤ) (u : (laurent L).piece p ⟶ (laurent L').piece q)
    (v : (laurent L').piece q ⟶ (laurent L'').piece r) :
    laurentTransport g L L'' p r (u ≫ v) =
      laurentTransport g L L' p q u ≫ laurentTransport g L' L'' q r v := by
  simp only [laurentTransport, CategoryTheory.Functor.map_comp, Category.assoc,
    IsIso.hom_inv_id_assoc]

/-- The transport of an identity is an identity. -/
theorem laurentTransport_id (p : ℤ) :
    laurentTransport g L L p p (CategoryStruct.id ((laurent L).piece p)) =
      CategoryStruct.id ((laurent ((pullbackFunctor (ringedSpaceHom g)).obj L)).piece p) := by
  simp only [laurentTransport, CategoryTheory.Functor.map_id, Category.id_comp, IsIso.inv_hom_id]

/-- **The multiplication of the Laurent algebra of a pullback, read through the comparison of the
integral tensor powers.** This is `laurentPullback_mul` solved for the multiplication downstairs;
it is the form in which the transport consumes it. -/
theorem laurentMul_pullback_eq (i j : ℤ) :
    laurentMul ((pullbackFunctor (ringedSpaceHom g)).obj L) i j =
      (inv (laurentPullback g L i) ⊗ₘ inv (laurentPullback g L j)) ≫
        inv (pullbackTensorComparison (ringedSpaceHom g) ((laurent L).piece i)
            ((laurent L).piece j)) ≫
          (pullbackFunctor (ringedSpaceHom g)).map (laurentMul L i j) ≫
            laurentPullback g L (i + j) := by
  have hcancel : (inv (laurentPullback g L i) ⊗ₘ inv (laurentPullback g L j)) ≫
      (laurentPullback g L i ⊗ₘ laurentPullback g L j) = CategoryStruct.id _ := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, IsIso.inv_hom_id, IsIso.inv_hom_id]
    simp
  have h2 : (laurentPullback g L i ⊗ₘ laurentPullback g L j) ≫
        laurentMul ((pullbackFunctor (ringedSpaceHom g)).obj L) i j =
      inv (pullbackTensorComparison (ringedSpaceHom g) ((laurent L).piece i)
          ((laurent L).piece j)) ≫
        (pullbackFunctor (ringedSpaceHom g)).map (laurentMul L i j) ≫
          laurentPullback g L (i + j) := by
    rw [IsIso.eq_inv_comp]
    exact laurentPullback_mul g L i j
  calc laurentMul ((pullbackFunctor (ringedSpaceHom g)).obj L) i j
      = CategoryStruct.id _ ≫ laurentMul ((pullbackFunctor (ringedSpaceHom g)).obj L) i j :=
        (Category.id_comp _).symm
    _ = ((inv (laurentPullback g L i) ⊗ₘ inv (laurentPullback g L j)) ≫
          (laurentPullback g L i ⊗ₘ laurentPullback g L j)) ≫
            laurentMul ((pullbackFunctor (ringedSpaceHom g)).obj L) i j := by rw [hcancel]
    _ = (inv (laurentPullback g L i) ⊗ₘ inv (laurentPullback g L j)) ≫
          ((laurentPullback g L i ⊗ₘ laurentPullback g L j) ≫
            laurentMul ((pullbackFunctor (ringedSpaceHom g)).obj L) i j) := Category.assoc _ _ _
    _ = _ := by rw [h2]

/-- **The transport carries a multiplicativity relation to a multiplicativity relation.** If the
morphisms `u`, `u'` and `w` between homogeneous pieces of the Laurent algebras of `L` and of `L'`
satisfy the multiplicativity relation of a homomorphism of graded algebras, then so do their
transports along `g`.

The proof is the composite of three facts: the multiplicativity `laurentPullback_mul` of the
comparison of the integral tensor powers of Tag 01CU, in the form `laurentMul_pullback_eq`, the
naturality `pullbackTensorComparison_naturality_tensorHom` of the comparison of Tag 01CD, and the
given relation. -/
theorem laurentTransport_mulSheaf (p q p' q' : ℤ)
    (u : (laurent L).piece p ⟶ (laurent L').piece q)
    (u' : (laurent L).piece p' ⟶ (laurent L').piece q')
    (w : (laurent L).piece (p + p') ⟶ (laurent L').piece (q + q'))
    (h : (laurent L).mulSheaf p p' ≫ w = (u ⊗ₘ u') ≫ (laurent L').mulSheaf q q') :
    (laurent ((pullbackFunctor (ringedSpaceHom g)).obj L)).mulSheaf p p' ≫
        laurentTransport g L L' (p + p') (q + q') w =
      (laurentTransport g L L' p q u ⊗ₘ laurentTransport g L L' p' q' u') ≫
        (laurent ((pullbackFunctor (ringedSpaceHom g)).obj L')).mulSheaf q q' := by
  rw [laurent_mulSheaf_eq, laurent_mulSheaf_eq] at h
  rw [laurent_mulSheaf_eq, laurent_mulSheaf_eq]
  exact mul_transport_of_comparison (pullbackFunctor (ringedSpaceHom g))
    (laurentPullback g L p) (laurentPullback g L p') (laurentPullback g L (p + p'))
    (laurentPullback g L' q) (laurentPullback g L' q') (laurentPullback g L' (q + q'))
    (pullbackTensorComparison (ringedSpaceHom g) ((laurent L).piece p) ((laurent L).piece p'))
    (pullbackTensorComparison (ringedSpaceHom g) ((laurent L').piece q) ((laurent L').piece q'))
    (laurentMul L p p') (laurentMul ((pullbackFunctor (ringedSpaceHom g)).obj L) p p')
    (laurentMul L' q q') (laurentMul ((pullbackFunctor (ringedSpaceHom g)).obj L') q q')
    u u' w (laurentPullback_mul g L p p') (laurentPullback_mul g L' q q')
    (pullbackTensorComparison_naturality_tensorHom (ringedSpaceHom g) u u') h

/-- **The transport of a unit-preserving degree-zero component is unit-preserving.** The global
unit of a Laurent algebra is the identity of the structure sheaf, so the hypothesis says the
component is the identity, and in degree zero the comparison of the integral tensor powers is the
structure-sheaf comparison of Tag 01CD for `L` and for `L'` alike. -/
theorem laurentTransport_oneHom (u : (laurent L).piece 0 ⟶ (laurent L').piece 0)
    (h : SheafOfModules.GradedAlgebra.oneHom (laurent L) ≫ u =
      SheafOfModules.GradedAlgebra.oneHom (laurent L')) :
    SheafOfModules.GradedAlgebra.oneHom
          (laurent ((pullbackFunctor (ringedSpaceHom g)).obj L)) ≫
        laurentTransport g L L' 0 0 u =
      SheafOfModules.GradedAlgebra.oneHom
        (laurent ((pullbackFunctor (ringedSpaceHom g)).obj L')) := by
  have hu : u = CategoryStruct.id
      (𝟙_ (SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))) :=
    (Category.id_comp u).symm.trans
      (((congrArg (fun z => z ≫ u) (oneHom_laurent L)).symm.trans h).trans (oneHom_laurent L'))
  have hmapu : (pullbackFunctor (ringedSpaceHom g)).map u =
      CategoryStruct.id ((pullbackFunctor (ringedSpaceHom g)).obj
        (𝟙_ (SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)))) :=
    (congrArg (fun z => (pullbackFunctor (ringedSpaceHom g)).map z) hu).trans
      (CategoryTheory.Functor.map_id (pullbackFunctor (ringedSpaceHom g)) _)
  have hmid : (pullbackFunctor (ringedSpaceHom g)).map u ≫ laurentPullback g L' 0 =
      laurentPullback g L 0 :=
    (congrArg (fun z => z ≫ laurentPullback g L' 0) hmapu).trans
      ((Category.id_comp (laurentPullback g L' 0)).trans
        ((laurentPullback_zero g L').trans (laurentPullback_zero g L).symm))
  have hT : laurentTransport g L L' 0 0 u =
      CategoryStruct.id
        ((laurent ((pullbackFunctor (ringedSpaceHom g)).obj L)).piece 0) :=
    (congrArg (fun z => inv (laurentPullback g L 0) ≫ z) hmid).trans
      (IsIso.inv_hom_id (laurentPullback g L 0))
  refine Eq.trans (congrArg (fun z => SheafOfModules.GradedAlgebra.oneHom
    (laurent ((pullbackFunctor (ringedSpaceHom g)).obj L)) ≫ z) hT) ?_
  refine Eq.trans (Category.comp_id _) ?_
  exact (oneHom_laurent ((pullbackFunctor (ringedSpaceHom g)).obj L)).trans
    (oneHom_laurent ((pullbackFunctor (ringedSpaceHom g)).obj L')).symm

end Transport

/-! ### Functoriality of the Laurent algebra under pullback -/

section Functorial

variable (g : T' ⟶ T) {L L' : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L']

/-- **The Laurent algebra of an invertible module is functorial under pullback**: a homomorphism
of sheaves of graded algebras `⨁_n L^{⊗ n} ⟶ ⨁_n (L')^{⊗ n}` is carried to one
`⨁_n (g^*L)^{⊗ n} ⟶ ⨁_n (g^*L')^{⊗ n}`, degreewise by `laurentTransport`. -/
def laurentPullbackHom (φ : laurent L ⟶ laurent L') :
    laurent ((pullbackFunctor (ringedSpaceHom g)).obj L) ⟶
      laurent ((pullbackFunctor (ringedSpaceHom g)).obj L') :=
  homOfMulSheaf _ _ (fun n => laurentTransport g L L' n n (φ.app n))
    fun i j => laurentTransport_mulSheaf g L L' i i j j (φ.app i) (φ.app j) (φ.app (i + j))
      (mulSheaf_comp_app (laurent L) (laurent L') φ i j)

/-- The degree-`n` component of `laurentPullbackHom g φ` is the transport of the degree-`n`
component of `φ`. -/
@[simp] theorem laurentPullbackHom_app (φ : laurent L ⟶ laurent L') (n : ℤ) :
    (laurentPullbackHom g φ).app n = laurentTransport g L L' n n (φ.app n) := rfl

/-- `laurentPullbackHom g` carries the identity of `laurent L` to the identity. -/
theorem laurentPullbackHom_id :
    laurentPullbackHom g (CategoryStruct.id (laurent L)) =
      CategoryStruct.id (laurent ((pullbackFunctor (ringedSpaceHom g)).obj L)) :=
  SheafOfModules.GradedAlgebra.Hom.ext fun n => laurentTransport_id g L n

/-- `laurentPullbackHom g` carries a composite to the composite of the images. -/
theorem laurentPullbackHom_comp
    {L'' : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L'']
    (φ : laurent L ⟶ laurent L') (φ' : laurent L' ⟶ laurent L'') :
    laurentPullbackHom g (φ ≫ φ') = laurentPullbackHom g φ ≫ laurentPullbackHom g φ' :=
  SheafOfModules.GradedAlgebra.Hom.ext fun n =>
    laurentTransport_comp g L L' L'' n n n (φ.app n) (φ'.app n)

/-- **An isomorphism of the Laurent algebras of two invertible modules is carried to one of the
Laurent algebras of their pullbacks.** This is the input the two identifications of the display
01NX need in order to be respected by the pullback of a quadruple. -/
def laurentPullbackIso (γ : laurent L ≅ laurent L') :
    laurent ((pullbackFunctor (ringedSpaceHom g)).obj L) ≅
      laurent ((pullbackFunctor (ringedSpaceHom g)).obj L') where
  hom := laurentPullbackHom g γ.hom
  inv := laurentPullbackHom g γ.inv
  hom_inv_id := (laurentPullbackHom_comp g γ.hom γ.inv).symm.trans
    ((congrArg (laurentPullbackHom g) γ.hom_inv_id).trans (laurentPullbackHom_id g))
  inv_hom_id := (laurentPullbackHom_comp g γ.inv γ.hom).symm.trans
    ((congrArg (laurentPullbackHom g) γ.inv_hom_id).trans (laurentPullbackHom_id g))

/-- The degree-`n` component of the forward morphism of `laurentPullbackIso g γ` is the transport
of the degree-`n` component of `γ.hom`. -/
@[simp] theorem laurentPullbackIso_hom_app (γ : laurent L ≅ laurent L') (n : ℤ) :
    (laurentPullbackIso g γ).hom.app n = laurentTransport g L L' n n (γ.hom.app n) := rfl

end Functorial

/-! ### Compatibility with the pullback of the map `ψ` of a quadruple -/

namespace Twisting

variable {f : T ⟶ S}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d d' : ℤ}
  {L L' : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L']

/-- **The transport is compatible with the pullback of the map `ψ` of a quadruple.** If a morphism
`u : L^{⊗ p} ⟶ (L')^{⊗ q}` carries the degree-`p` component of `ψ` to the degree-`q` component of
`ψ'`, up to the reindexing `φ` of the algebra, then its transport carries the degree-`p` component
of `g^*ψ` to the degree-`q` component of `g^*ψ'`, up to the pullback of `φ` along `g ∘ f`.

The copy of the comparison of the integral tensor powers inside `Twisting.pullbackApp` cancels
against the one inside `laurentTransport`, and what is left is the naturality
`compComparison_naturality` of the comparison of an iterated pullback. -/
theorem pullbackApp_comp_laurentTransport (ψ : Twisting f A d L) (ψ' : Twisting f A d' L')
    (g : T' ⟶ T) (p q : ℤ) (u : (laurent L).piece p ⟶ (laurent L').piece q)
    (φ : A.piece (p * d) ⟶ A.piece (q * d'))
    (h : ψ.app p ≫ u = (pullbackFunctor (ringedSpaceHom f)).map φ ≫ ψ'.app q) :
    ψ.pullbackApp g p ≫ laurentTransport g L L' p q u =
      (pullbackFunctor (ringedSpaceHom (g ≫ f))).map φ ≫ ψ'.pullbackApp g q := by
  simp only [pullbackApp, laurentTransport, Category.assoc, IsIso.hom_inv_id_assoc]
  slice_lhs 2 3 => rw [← CategoryTheory.Functor.map_comp]
  rw [h, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  slice_lhs 1 2 => rw [compComparison_naturality g f φ]
  simp only [Category.assoc]

/-- The equal-degree case of `pullbackApp_comp_laurentTransport`, with no reindexing of the
algebra: this is the clause a strict equivalence of quadruples carries. -/
theorem pullbackApp_comp_laurentTransport_of_app (ψ : Twisting f A d L) (ψ' : Twisting f A d L')
    (g : T' ⟶ T) (n : ℤ) (u : (laurent L).piece n ⟶ (laurent L').piece n)
    (h : ψ.app n ≫ u = ψ'.app n) :
    ψ.pullbackApp g n ≫ laurentTransport g L L' n n u = ψ'.pullbackApp g n := by
  refine Eq.trans (pullbackApp_comp_laurentTransport ψ ψ' g n n u
    (CategoryStruct.id (A.piece (n * d)))
    (h.trans ((Category.id_comp (ψ'.app n)).symm.trans
      (congrArg (fun z => z ≫ ψ'.app n)
        (CategoryTheory.Functor.map_id (pullbackFunctor (ringedSpaceHom f))
          (A.piece (n * d))).symm)))) ?_
  exact (congrArg (fun z => z ≫ ψ'.pullbackApp g n)
      (CategoryTheory.Functor.map_id (pullbackFunctor (ringedSpaceHom (g ≫ f)))
        (A.piece (n * d)))).trans (Category.id_comp _)

end Twisting

/-! ### The pullback of a quadruple respects the two identifications -/

namespace Quadruple

variable {f : T ⟶ S}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d d' : ℤ}

/-- **Stacks Project, Section 01NS: the pullback of a quadruple respects strict equivalence.**
Strict equivalence is witnessed by an isomorphism of the Laurent algebras carrying `ψ` to `ψ'`;
`laurentPullbackIso` carries that witness to one for the pullbacks, and
`Twisting.pullbackApp_comp_laurentTransport_of_app` is the compatibility with `ψ`. -/
@[stacks 01NS "the pullback of a quadruple along a morphism of test schemes respects strict \
equivalence"]
theorem StrictlyEquivalent.pullback {P Q : Quadruple f A d} (h : StrictlyEquivalent P Q)
    (g : T' ⟶ T) : StrictlyEquivalent (P.pullback g) (Q.pullback g) := by
  obtain ⟨γ, hψ⟩ := (strictlyEquivalent_iff_exists_hom P Q).mp h
  refine (strictlyEquivalent_iff_exists_hom _ _).mpr ⟨laurentPullbackIso g γ, fun n => ?_⟩
  exact Twisting.pullbackApp_comp_laurentTransport_of_app P.twisting Q.twisting g n
    (γ.hom.app n) (hψ n)

/-- **Stacks Project, Tag 01NW: the pullback of a quadruple respects a comparison at a common
multiple of the degrees.** The components of the comparison are transported by
`laurentTransportIso`; its multiplicativity is `laurentTransport_mulSheaf`, its unit clause is
`laurentTransport_oneHom`, and its compatibility with `ψ` is
`Twisting.pullbackApp_comp_laurentTransport`. The two degrees, and hence the common multiple, are
unchanged. -/
theorem CompatibleAt.pullback {P : Quadruple f A d} {Q : Quadruple f A d'} {a a' : ℤ}
    (h : CompatibleAt P Q a a') (g : T' ⟶ T) :
    CompatibleAt (P.pullback g) (Q.pullback g) a a' := by
  obtain ⟨hm, γ, hmul, hone, hψ⟩ := h
  refine ⟨hm, fun p q hpq => laurentTransportIso g P.L Q.L p q (γ p q hpq), ?_, ?_, ?_⟩
  · intro p q p' q' hpq hpq'
    exact (laurentTransport_mulSheaf g P.L Q.L p q p' q' (γ p q hpq).hom (γ p' q' hpq').hom
      (γ (p + p') (q + q') (hpq.add hpq')).hom (hmul p q p' q' hpq hpq').symm).symm
  · exact laurentTransport_oneHom g P.L Q.L (γ 0 0 (IsScaledPair.zero a a')).hom hone
  · intro p q hpq
    exact Twisting.pullbackApp_comp_laurentTransport P.twisting Q.twisting g p q
      (γ p q hpq).hom (eqToHom (congrArg A.piece (hpq.degree_eq hm))) (hψ p q hpq)

/-- **Stacks Project, Section 01NS: the pullback of a quadruple respects equivalence of quadruples
of possibly different degrees.** Equivalence is the comparison at the common multiple `d d'` of the
two degrees, and the pullback leaves both degrees unchanged. -/
@[stacks 01NS "the pullback of a quadruple along a morphism of test schemes respects equivalence \
of quadruples of possibly different degrees"]
theorem Equivalent.pullback {P : Quadruple f A d} {Q : Quadruple f A d'} (h : Equivalent P Q)
    (g : T' ⟶ T) : Equivalent (P.pullback g) (Q.pullback g) :=
  CompatibleAt.pullback h g

end Quadruple

/-! ### The induced map at a fixed degree, and on the union -/

/-- **Stacks Project, Section 01NS: the map `F_d(T) → F_d(T')` of a morphism `g : T' ⟶ T` of test
schemes**, at a fixed degree `d`. A point of `F_d(T)` over `f : T ⟶ S` is a quadruple of degree
`d` over `f` taken modulo strict equivalence; its image is the pullback of that quadruple, again
of degree `d`, over `g ≫ f`. This is well defined because the pullback respects strict
equivalence (`Quadruple.StrictlyEquivalent.pullback`), and no identification across degrees is
involved. -/
@[stacks 01NS "the map F_d(T) → F_d(T') of a morphism of test schemes at a fixed degree d, the \
pullback of a quadruple descended to the strict equivalence classes"]
def Fd.pullback {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)}
    {d : ℤ} (g : T' ⟶ T) (ξ : Fd A d T) : Fd A d T' :=
  ⟨g ≫ ξ.1,
    Quotient.map (sa := Quadruple.setoid ξ.1 A d) (sb := Quadruple.setoid (g ≫ ξ.1) A d)
      (fun P => P.pullback g) (fun _ _ h => Quadruple.StrictlyEquivalent.pullback h g) ξ.2⟩

/-- The map at a fixed degree sends the class of a quadruple to the class of its pullback. -/
@[simp] theorem Fd.pullback_mk
    {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}
    (g : T' ⟶ T) (f : T ⟶ S) (P : Quadruple f A d) :
    Fd.pullback g (Fd.mk f P) = Fd.mk (g ≫ f) (P.pullback g) := rfl

/-- The morphism to `S` recorded by the image of a class in `F_d(T)` is the composite. -/
@[simp] theorem Fd.pullback_fst
    {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}
    (g : T' ⟶ T) (ξ : Fd A d T) : (Fd.pullback g ξ).1 = g ≫ ξ.1 := rfl


/-- **Stacks Project, Tag 01NY, the functoriality of the display 01NX in the test scheme: the map
`F(T) → F(T')` of a morphism `g : T' ⟶ T` of test schemes.** A point of `F(T)` over `f : T ⟶ S` is
a quadruple of some positive degree over `f`, taken modulo strict equivalence inside a degree and
equivalence across degrees; its image is the pullback of that quadruple, of the same degree, over
`g ≫ f`. This is well defined because the pullback respects both identifications
(`Quadruple.StrictlyEquivalent.pullback` and `Quadruple.Equivalent.pullback`).

This is the map on morphisms only. Its two functor laws, and the functor
`F : Sch^{opp} ⟶ Sets` of the display 01NX that they assemble into, are
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.UnionFunctor`. It is **not** a clause of
Tag 01NY, whose content is the representability of `F` by a scheme: this makes `F` a functor,
which is what Tag 01NY's statement is *about*. -/
-- [Stacks, Tag 01NX] is registered on UnionRepresentable (`UnionRepresentable.lean:125`), which
-- carries the functor F of the display for every test scheme. This lemma proves only the map
-- F(T) → F(T') of a morphism of test schemes, which is the functoriality of the display on
-- morphisms: the pullback of a quadruple respects both identifications of 01NX, so it descends to
-- the union. The two functor laws for this map, and the functor they assemble into, are proved in
-- StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.UnionFunctor; they need the unit and
-- associativity coherences of Stacks.PullbackCompMonoidal.comparison, which are proved there.
-- Nothing is carried as a hypothesis. Making F a functor is part of defining the display's F,
-- which is 01NX, and is not a clause of Tag 01NY, whose content is the representability of F by a
-- scheme; representability is neither proved nor assumed here, so this lemma carries no tag.
def F.pullback {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)}
    (g : T' ⟶ T) (ξ : F A T) : F A T' :=
  ⟨g ≫ ξ.1,
    Quot.lift
      (fun P : PositiveQuadruple ξ.1 A =>
        Quot.mk (UnionRel (f := g ≫ ξ.1) (A := A)) ⟨P.1, P.2.pullback g⟩)
      (fun _ _ hrel => by
        cases hrel with
        | strict hs => exact Quot.sound (UnionRel.strict (hs.pullback g))
        | equivalent he => exact Quot.sound (UnionRel.equivalent (he.pullback g)))
      ξ.2⟩

/-- The induced map sends the point of a quadruple to the point of its pullback, of the same
degree. -/
@[simp] theorem F.pullback_mk
    {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)}
    (g : T' ⟶ T) (f : T ⟶ S) {d : ℤ} (hd : 0 < d) (P : Quadruple f A d) :
    F.pullback g (F.mk f hd P) = F.mk (g ≫ f) hd (P.pullback g) := rfl

/-- The morphism to `S` recorded by the image of a point of `F(T)` is the composite. -/
@[simp] theorem F.pullback_fst
    {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)}
    (g : T' ⟶ T) (ξ : F A T) : (F.pullback g ξ).1 = g ≫ ξ.1 := rfl

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
