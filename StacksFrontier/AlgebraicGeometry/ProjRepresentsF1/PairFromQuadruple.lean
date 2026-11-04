module

public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.QuadrupleClassInjective
public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.BilinearZero
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.TripleComparison
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.UnionPullback

/-!
# The pair of Tag 01O4 a quadruple of Section 01NS determines, and the bijection of Tag 01O4

Let `𝒜` be a graded `𝒪_S`-algebra as in Situation 01NN and `f : T ⟶ S` a morphism of schemes.
`StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.QuadrupleFromPair` built from a pair of
Tag 01O4 a quadruple of Section 01NS at `d = 1`; this file builds the pair from the quadruple,
and with it the bijection Tag 01O4 asserts.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjRepresentsF1.quadruplePsi`: **the graded map `𝒜_n ⟶ f_*T(L)_n` a
  quadruple determines**, in every integral degree. This is
  `Stacks.AlgebraicGeometry.ProjRepresentsF1.quadrupleTensorPsi` extended from `ℕ` to `ℤ`: in a
  nonnegative degree it is the quadruple's own map transposed across the pullback–pushforward
  adjunction and read back through the comparison `Tⁿ(L) ≅ L^{⊗ n}`; in a negative degree, where
  the tensor algebra vanishes, it is zero.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.quadruplePair`: **the pair of Tag 01O4 a quadruple
  determines**, with all four of its fields.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.pairClassifyingEquiv`: the bijection of Tag 01O4,
  as an equivalence of types.

## Main results

* `Stacks.AlgebraicGeometry.ProjRepresentsF1.quadruplePsi_map_mul` and `quadruplePsi_map_one`:
  **the multiplicativity and unit clauses of a pair, for the graded map a quadruple
  determines**, and `epi_quadruplePsi_one`: its degree-one surjectivity clause.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.strictlyEquivalent_quadruple_quadruplePair`: **the
  quadruple of the pair of a quadruple is strictly equivalent to that quadruple** — the two
  constructions are mutually inverse on classes.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.quadrupleClass_surjective` and
  `quadrupleClass_bijective`: **Tag 01O4's functor `F_1` and Section 01NS's `F_d` at `d = 1` are
  the same set**, the injectivity half being `quadrupleClass_injective`.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.pairClassifyingHom_bijective`: **Tag 01O4.** For
  `𝒜` generated in degree one the classifying map from strict isomorphism classes of invertible
  degree-one quotients of `f^*𝒜` to the morphisms `T ⟶ Proj_S(𝒜)` over `S` is a bijection.

## Implementation notes

**The degree identification `n * 1 = n` is confined to one morphism-level lemma.** A quadruple's
family is indexed so that its degree-`n` component has source `f^*𝒜_{n·1}`, while a homomorphism
of sheaves of graded algebras out of `f^*𝒜` has source `f^*𝒜_n`; the two differ by an `eqToHom`,
and `n * 1 = n` is not `rfl` for an integer. `mulSheaf_comp_eqToHom_comp` takes the three source
degrees as variables together with the equalities identifying them, so that `subst` removes
every `eqToHom` at once. Everything downstream — in particular all three clauses of the pair —
is then stated and proved with no `eqToHom` at the level of local sections at all.

**No statement names the inverse of the comparison with the Laurent algebra, and every `IsIso`
argument is passed by hand.** The comparison `T(L) ⟶ ⨁_n L^{⊗ n}` is invertible only in the
nonnegative degrees, so its invertibility is a hypothesis rather than an instance, and at the
spellings below instance search does not find it even where it is in scope. The graded map is
therefore characterised by `quadruplePsi_comp_tensorToLaurent`, which mentions only the
comparison itself, and the clauses are checked after applying it, using
`section_injective_of_isIso`. Where an inverse is unavoidable it is written `@inv` with the
invertibility supplied explicitly.

**`rw` and `simp` are unusable in these goals.** The goals mix
`AlgebraicGeometry.Scheme.Modules` with `SheafOfModules (structureRingSheaf _)` and are not
type-correct at the transparency the rewriting tactics check their motives at, so a rewrite
reports a missing pattern that the error message prints character-for-character identically to
the goal. Every proof below is an `Eq.trans` chain of `congrArg`s, and the manipulations that do
need a rewrite — cancelling two `eqToHom`s, transporting epimorphy along an equality of
morphisms, composing an epimorphism with isomorphisms — are stated in an arbitrary category with
every object and morphism free, where the rewrite does fire, and applied with `exact`.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)

## Not done here

The universal pair of Tag 01O4 — the pair over relative `Proj` itself whose class the bijection
sends to the identity — is not built, so `F1Bundle` and `F1Representation` remain uninhabited:
what is proved here is the bijectivity of the classifying map `pairClassifyingHom`, which is the
map those structures would carry, not the structures themselves. The naturality of the bijection
in the test scheme and the pullback of a pair along a morphism of test schemes are not here
either.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory CategoryTheory.Limits AlgebraicGeometry Opposite
open TopologicalSpace
open Stacks.RingedSpace Stacks.PullbackTensorCoherence RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace Stacks.AlgebraicGeometry.ProjRepresentsF1

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
attribute [local instance] Stacks.PullbackGradedAlgebra.pullbackStrictMonoidal
attribute [local instance] Stacks.PushforwardGradedAlgebra.pushforwardFunctorLaxMonoidal

/-! ### Free facts about sheaves of modules and sheaves of graded algebras -/

/-- A sheaf of graded algebras kills a zero section in its first variable. -/
public theorem gradedMul_app_zero_left {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    (D : SheafOfModules.GradedAlgebra.{u, u} R) (i j : ℤ) (U : Cᵒᵖ)
    (y : (D.piece j).val.obj U) : (D.mul i j).app U 0 y = 0 := by
  rw [map_zero]
  rfl

/-- A sheaf of graded algebras kills a zero section in its second variable. -/
public theorem gradedMul_app_zero_right {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    (D : SheafOfModules.GradedAlgebra.{u, u} R) (i j : ℤ) (U : Cᵒᵖ)
    (x : (D.piece i).val.obj U) : (D.mul i j).app U x 0 = 0 :=
  map_zero ((D.mul i j).app U x)

/-- **A morphism of objects identified by an equality is an isomorphism.** Instance search does
not find this, and every `IsIso` argument below is therefore supplied by hand. -/
public theorem isIso_eqToHom {C : Type*} [Category C] {X Y : C} (h : X = Y) :
    IsIso (eqToHom h) :=
  (eqToIso h).isIso_hom

/-- **An isomorphism of sheaves of modules is injective on local sections.** Every object and
every morphism is free, so the statement is applied with `exact` and the `Category` instance is
taken from the goal; the invertibility is an explicit argument, because at the spellings below
instance search does not find it. -/
public theorem section_injective_of_isIso {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R}
    (θ : M ⟶ N) (hθ : IsIso θ) (U : Cᵒᵖ) {x y : M.val.obj U}
    (h : θ.val.app U x = θ.val.app U y) : x = y := by
  have := hθ
  have hx : (inv θ).val.app U (θ.val.app U x) = x :=
    SheafOfModules.hom_congr_app_apply (IsIso.hom_inv_id θ) U x
  have hy : (inv θ).val.app U (θ.val.app U y) = y :=
    SheafOfModules.hom_congr_app_apply (IsIso.hom_inv_id θ) U y
  exact hx.symm.trans ((congrArg ((inv θ).val.app U) h).trans hy)

/-- **Two `eqToHom`s in opposite directions cancel**, in an arbitrary category with every
object and morphism free. -/
public theorem eqToHom_comp_eqToHom_comp {C : Type*} [Category C] {X Y Z : C} (h : X = Y)
    (h' : Y = X) (g : X ⟶ Z) : eqToHom h ≫ eqToHom h' ≫ g = g := by
  subst h
  simp

/-! ### Epimorphy through isomorphisms -/

/-- **Epimorphy transported along an equality of morphisms**, in an arbitrary category with
every object and morphism free: at the sheaf-of-modules spelling the rewrite fails, the goal not
being type-correct at the transparency the rewriting tactics check their motives at. -/
public theorem epi_of_eq {C : Type*} [Category C] {X Y : C} {a b : X ⟶ Y} (h : a = b)
    (hb : Epi b) : Epi a := by
  rw [h]
  exact hb

/-- **An epimorphism with an isomorphism composed on the left is an epimorphism**, in an
arbitrary category with every object and morphism free. -/
public theorem epi_isoComp {C : Type*} [Category C] {V W X : C} (a : V ⟶ W) (b : W ⟶ X)
    (ha : IsIso a) (hb : Epi b) : Epi (a ≫ b) := by
  have := ha
  have := hb
  infer_instance

/-- **An epimorphism with two isomorphisms composed on the right is an epimorphism**, in an
arbitrary category with every object and morphism free. -/
public theorem epi_compIso {C : Type*} [Category C] {V W X Y : C} (a : V ⟶ W) (b : W ⟶ X)
    (c : X ⟶ Y) (ha : Epi a) (hb : IsIso b) (hc : IsIso c) : Epi (a ≫ b ≫ c) := by
  have := ha
  have := hb
  have := hc
  infer_instance

variable {S T : Scheme.{u}} (A : SheafGradedAlgebra.{u} S) (TA : TensorAlgebras.{u})
  (f : T ⟶ S)

/-! ### Degree bookkeeping, with the degrees free -/

/-- The pullback of the `eqToHom` identifying two homogeneous pieces is the `eqToHom`
identifying their pullbacks. -/
public theorem map_eqToHom_piece
    (B : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace))
    {m n : ℤ} (e : m = n) :
    (pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg B.piece e)) =
      eqToHom (congrArg
        (fun k : ℤ => (pullbackFunctor (ringedSpaceHom f)).obj (B.piece k)) e) := by
  subst e
  simp

/-- **The multiplicativity clause of `Twisting`, with the three source degrees taken as
variables**, read as the commuting square of morphism-level multiplications a homomorphism of
sheaves of graded algebras out of `f^*𝒜` has to satisfy.

Substituting the equalities leaves the multiplicativity axiom itself; the degree identification
`n * 1 = n` cannot be rewritten inside the dependent types, since it is not `rfl` for an
integer. After the substitution every `eqToHom` is definitionally an identity — the proof it
carries is a proof of a reflexive equality, and `Prop`s are definitionally irrelevant — so the
whole chain below is an `Eq.trans` of unit laws, with no rewriting: in this goal context `rw`
and `simp` both fail on the `Scheme.Modules`-versus-`SheafOfModules` spelling of the sheaf of
rings. -/
public theorem mulSheaf_comp_eqToHom_comp
    (B : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace))
    (D : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf T.toRingedSpace))
    (i j i' j' k' : ℤ) (hi : i' = i) (hj : j' = j) (hk : k' = i + j) (h : i' + j' = k')
    (ai : (pullbackFunctor (ringedSpaceHom f)).obj (B.piece i') ⟶ D.piece i)
    (aj : (pullbackFunctor (ringedSpaceHom f)).obj (B.piece j') ⟶ D.piece j)
    (ak : (pullbackFunctor (ringedSpaceHom f)).obj (B.piece k') ⟶ D.piece (i + j))
    (happ : MonoidalCategoryStruct.tensorHom ai aj ≫ D.mulSheaf i j =
      inv (pullbackTensorComparison (ringedSpaceHom f) (B.piece i') (B.piece j')) ≫
        (pullbackFunctor (ringedSpaceHom f)).map
          (B.mulSheaf i' j' ≫ eqToHom (congrArg B.piece h)) ≫ ak) :
    (Stacks.PullbackGradedAlgebra.pullbackGradedAlgebra (ringedSpaceHom f) B
          (isSheafStruct S)).mulSheaf i j ≫
        (eqToHom (congrArg
          (fun k : ℤ => (pullbackFunctor (ringedSpaceHom f)).obj (B.piece k)) hk.symm) ≫ ak) =
      MonoidalCategoryStruct.tensorHom
          (eqToHom (congrArg
            (fun k : ℤ => (pullbackFunctor (ringedSpaceHom f)).obj (B.piece k)) hi.symm) ≫ ai)
          (eqToHom (congrArg
            (fun k : ℤ => (pullbackFunctor (ringedSpaceHom f)).obj (B.piece k)) hj.symm) ≫ aj) ≫
        D.mulSheaf i j := by
  subst hi
  subst hj
  subst hk
  refine Eq.trans (congrArg
    (fun z => (Stacks.PullbackGradedAlgebra.pullbackGradedAlgebra (ringedSpaceHom f) B
      (isSheafStruct S)).mulSheaf i' j' ≫ z) (Category.id_comp ak)) ?_
  refine Eq.trans (congrArg (fun z => z ≫ ak) (mulSheaf_pullbackGradedAlgebra f B i' j')) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg
    (fun z => inv (pullbackTensorComparison (ringedSpaceHom f) (B.piece i') (B.piece j')) ≫
      z ≫ ak)
    (congrArg (pullbackFunctor (ringedSpaceHom f)).map
      (Category.comp_id (B.mulSheaf i' j'))).symm) ?_
  refine Eq.trans happ.symm ?_
  refine congrArg (fun z => z ≫ D.mulSheaf i' j') ?_
  refine Eq.trans (congrArg (fun z => MonoidalCategoryStruct.tensorHom z aj)
    (Category.id_comp ai).symm) ?_
  exact congrArg
    (fun z => MonoidalCategoryStruct.tensorHom (𝟙 _ ≫ ai) z) (Category.id_comp aj).symm

/-! ### The graded map a quadruple carries, with its degrees aligned -/

/-- **The degreewise map `f^*𝒜_n ⟶ L^{⊗ n}` a quadruple at `d = 1` carries**, with the degree
identification `n * 1 = n` absorbed, so that it has the shape of a homomorphism of sheaves of
graded algebras out of `f^*𝒜`. -/
public def quadrupleTwistingApp (Q : Quadruple f (situationAlgebra A) 1) (n : ℤ) :
    letI := Q.isInvertible
    (Stacks.PullbackGradedAlgebra.pullbackGradedAlgebra (ringedSpaceHom f) (situationAlgebra A)
        (isSheafStruct S)).piece n ⟶ (laurent Q.L).piece n :=
  letI := Q.isInvertible
  eqToHom (congrArg (fun k : ℤ =>
      (pullbackFunctor (ringedSpaceHom f)).obj ((situationAlgebra A).piece k))
    (mul_one n).symm) ≫ Q.twisting.app n

/-- **The aligned family is multiplicative at the level of morphisms.** -/
public theorem quadrupleTwistingApp_mulSheaf (Q : Quadruple f (situationAlgebra A) 1) (i j : ℤ) :
    letI := Q.isInvertible
    (Stacks.PullbackGradedAlgebra.pullbackGradedAlgebra (ringedSpaceHom f) (situationAlgebra A)
          (isSheafStruct S)).mulSheaf i j ≫ quadrupleTwistingApp A f Q (i + j) =
      MonoidalCategoryStruct.tensorHom (quadrupleTwistingApp A f Q i)
          (quadrupleTwistingApp A f Q j) ≫ (laurent Q.L).mulSheaf i j :=
  let := Q.isInvertible
  mulSheaf_comp_eqToHom_comp f (situationAlgebra A) (laurent Q.L) i j (i * 1) (j * 1)
    ((i + j) * 1) (mul_one i) (mul_one j) (mul_one (i + j)) (by ring)
    (Q.twisting.app i) (Q.twisting.app j) (Q.twisting.app (i + j)) (Q.twisting.app_mul i j)

/-- **The homomorphism of sheaves of graded algebras `f^*𝒜 ⟶ ⨁_{n ∈ ℤ} L^{⊗ n}` a quadruple
carries.** -/
public def quadrupleTwistingHom (Q : Quadruple f (situationAlgebra A) 1) :
    letI := Q.isInvertible
    Stacks.PullbackGradedAlgebra.pullbackGradedAlgebra (ringedSpaceHom f) (situationAlgebra A)
        (isSheafStruct S) ⟶ laurent Q.L :=
  letI := Q.isInvertible
  homOfMulSheaf _ _ (quadrupleTwistingApp A f Q) (quadrupleTwistingApp_mulSheaf A f Q)

/-- **The homomorphism of sheaves of graded algebras `𝒜 ⟶ f_*(⨁_{n ∈ ℤ} L^{⊗ n})` a quadruple
carries**: the adjoint transpose of `quadrupleTwistingHom` across the correspondence of
Tag 0FQX. -/
public def quadruplePsiHom (Q : Quadruple f (situationAlgebra A) 1) :
    letI := Q.isInvertible
    situationAlgebra A ⟶ Stacks.PushforwardGradedAlgebra.pushforwardGradedAlgebra
      (ringedSpaceHom f) (laurent Q.L) :=
  letI := Q.isInvertible
  SheafOfModules.GradedAlgebra.transportHomForward (pullbackAdjunction (ringedSpaceHom f))
    (isSheafStruct T) (isSheafStruct S) (quadrupleTwistingHom A f Q)

/-- The components of `quadruplePsiHom` are the adjoint transposes of the aligned family. -/
public theorem quadruplePsiHom_app (Q : Quadruple f (situationAlgebra A) 1) (n : ℤ) :
    letI := Q.isInvertible
    (quadruplePsiHom A f Q).app n =
      (pullbackAdjunction (ringedSpaceHom f)).homEquiv _ _ (quadrupleTwistingApp A f Q n) :=
  rfl

/-! ### The graded map of the pair -/

/-- **The family of morphisms `𝒜_n ⟶ f_*T(L)_n` determined by a quadruple of Section 01NS**, in
every integral degree: the quadruple's `ψ` transposed across the pullback–pushforward adjunction
and read back through the comparison `Tⁿ(L) ≅ L^{⊗ n}`, which is an isomorphism exactly in the
nonnegative degrees. In a negative degree both `𝒜_n` and `Tⁿ(L)` vanish and the map is zero.

This is `Stacks.AlgebraicGeometry.ProjRepresentsF1.quadrupleTensorPsi` extended from `ℕ`
to `ℤ`. -/
public def quadruplePsi (Q : Quadruple f (situationAlgebra A) 1) (n : ℤ) :
    A.piece n ⟶ (Scheme.Modules.pushforward f).obj ((TA T Q.L).tensor.piece n) :=
  letI := Q.isInvertible
  if hn : 0 ≤ n then
    (quadruplePsiHom A f Q).app n ≫
      (Scheme.Modules.pushforward f).map
        (@inv _ _ _ _ ((tensorToLaurent Q.L (TA T Q.L)).app n)
          (isIso_tensorToLaurent_app Q.L (TA T Q.L) n hn))
  else 0

/-- In a negative degree the graded map is zero. -/
public theorem quadruplePsi_of_neg (Q : Quadruple f (situationAlgebra A) 1) {n : ℤ}
    (hn : n < 0) : quadruplePsi A TA f Q n = 0 :=
  dite_eq_right (not_le.mpr hn)

/-- In a nonnegative degree the graded map is the transposed homomorphism followed by the inverse
of the comparison with the Laurent algebra. -/
private theorem quadruplePsi_eq_of_nonneg (Q : Quadruple f (situationAlgebra A) 1) {n : ℤ}
    (hn : 0 ≤ n) :
    letI := Q.isInvertible
    quadruplePsi A TA f Q n =
      (quadruplePsiHom A f Q).app n ≫
        (Scheme.Modules.pushforward f).map
          (@inv _ _ _ _ ((tensorToLaurent Q.L (TA T Q.L)).app n)
            (isIso_tensorToLaurent_app Q.L (TA T Q.L) n hn)) :=
  dite_eq_left hn

/-- **The graded map of the pair is characterised by the comparison with the Laurent algebra**:
followed by the direct image of that comparison it is the transposed homomorphism of sheaves of
graded algebras. This is the form in which the graded map is used, so that no statement below
has to name the inverse of a morphism whose invertibility is a hypothesis. -/
public theorem quadruplePsi_comp_tensorToLaurent (Q : Quadruple f (situationAlgebra A) 1)
    {n : ℤ} (hn : 0 ≤ n) :
    letI := Q.isInvertible
    quadruplePsi A TA f Q n ≫
        (Scheme.Modules.pushforward f).map ((tensorToLaurent Q.L (TA T Q.L)).app n) =
      (quadruplePsiHom A f Q).app n := by
  let := Q.isInvertible
  have hdef := quadruplePsi_eq_of_nonneg A TA f Q hn
  refine Eq.trans (congrArg (fun z => z ≫ (Scheme.Modules.pushforward f).map
    ((tensorToLaurent Q.L (TA T Q.L)).app n)) hdef) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun z => (quadruplePsiHom A f Q).app n ≫ z)
    ((Scheme.Modules.pushforward f).map_comp
      (@inv _ _ _ _ ((tensorToLaurent Q.L (TA T Q.L)).app n)
        (isIso_tensorToLaurent_app Q.L (TA T Q.L) n hn))
      ((tensorToLaurent Q.L (TA T Q.L)).app n)).symm) ?_
  refine Eq.trans (congrArg (fun z => (quadruplePsiHom A f Q).app n ≫
    (Scheme.Modules.pushforward f).map z)
    (@IsIso.inv_hom_id _ _ _ _ ((tensorToLaurent Q.L (TA T Q.L)).app n)
      (isIso_tensorToLaurent_app Q.L (TA T Q.L) n hn))) ?_
  refine Eq.trans (congrArg (fun z => (quadruplePsiHom A f Q).app n ≫ z)
    ((Scheme.Modules.pushforward f).map_id _)) ?_
  exact Category.comp_id _

/-- The characterisation of the graded map, on local sections. -/
public theorem quadruplePsi_val_app (Q : Quadruple f (situationAlgebra A) 1) {n : ℤ}
    (hn : 0 ≤ n) (U : S.Opens) (c : Γ(A.piece n, U)) :
    letI := Q.isInvertible
    ((tensorToLaurent Q.L (TA T Q.L)).app n).val.app (op (f ⁻¹ᵁ U))
        ((quadruplePsi A TA f Q n).val.app (op U) c) =
      ((quadruplePsiHom A f Q).app n).val.app (op U) c :=
  let := Q.isInvertible
  SheafOfModules.hom_congr_app_apply (quadruplePsi_comp_tensorToLaurent A TA f Q hn) (op U) c

/-! ### The multiplicativity clause of the pair -/

/-- **The graded map of the pair a quadruple determines preserves products of homogeneous local
sections.**

In a bidegree with both indices nonnegative this is the multiplicativity of the transposed
homomorphism of sheaves of graded algebras, read over `f⁻¹U` by
`pushforwardGradedAlgebra_mul_app` and compared on the other side by the multiplicativity of
the comparison with the Laurent algebra; the comparison is injective on sections there, which
is what lets the clause be checked after it. In a bidegree with a negative index — including the
mixed ones, where the sum is nonnegative and neither map is zero — the homogeneous piece in that
degree is a zero object, so the section there is zero and both sides vanish by the zero-argument
laws. -/
public theorem quadruplePsi_map_mul (Q : Quadruple f (situationAlgebra A) 1) (i j : ℤ)
    (U : S.Opens) (a : Γ(A.piece i, U)) (b : Γ(A.piece j, U)) :
    (quadruplePsi A TA f Q (i + j)).val.app (op U) ((A.mul i j).app U a b) =
      ((TA T Q.L).tensor.mul i j).app (op (f ⁻¹ᵁ U))
        ((quadruplePsi A TA f Q i).val.app (op U) a)
        ((quadruplePsi A TA f Q j).val.app (op U) b) := by
  let := Q.isInvertible
  rcases lt_or_ge i 0 with hi | hi
  · obtain rfl : a = 0 :=
      Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.section_eq_zero_of_isZero
        (A.negative_isZero i hi) U a
    refine Eq.trans (Eq.trans (congrArg ((quadruplePsi A TA f Q (i + j)).val.app (op U))
      (SheafBilinearMap.app_zero_left (A.mul i j) U b)) (map_zero _)) ?_
    refine Eq.trans (gradedMul_app_zero_left (TA T Q.L).tensor i j (op (f ⁻¹ᵁ U))
      ((quadruplePsi A TA f Q j).val.app (op U) b)).symm ?_
    exact congrArg (fun z => ((TA T Q.L).tensor.mul i j).app (op (f ⁻¹ᵁ U)) z
      ((quadruplePsi A TA f Q j).val.app (op U) b)) (map_zero _).symm
  rcases lt_or_ge j 0 with hj | hj
  · obtain rfl : b = 0 :=
      Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.section_eq_zero_of_isZero
        (A.negative_isZero j hj) U b
    refine Eq.trans (Eq.trans (congrArg ((quadruplePsi A TA f Q (i + j)).val.app (op U))
      (SheafBilinearMap.app_zero_right (A.mul i j) U a)) (map_zero _)) ?_
    refine Eq.trans (gradedMul_app_zero_right (TA T Q.L).tensor i j (op (f ⁻¹ᵁ U))
      ((quadruplePsi A TA f Q i).val.app (op U) a)).symm ?_
    exact congrArg (fun z => ((TA T Q.L).tensor.mul i j).app (op (f ⁻¹ᵁ U))
      ((quadruplePsi A TA f Q i).val.app (op U) a) z) (map_zero _).symm
  refine section_injective_of_isIso ((tensorToLaurent Q.L (TA T Q.L)).app (i + j))
    (isIso_tensorToLaurent_app Q.L (TA T Q.L) (i + j) (add_nonneg hi hj)) (op (f ⁻¹ᵁ U)) ?_
  refine Eq.trans (quadruplePsi_val_app A TA f Q (add_nonneg hi hj) U
    ((A.mul i j).app U a b)) ?_
  refine Eq.trans ((quadruplePsiHom A f Q).map_mul i j (op U) a b) ?_
  refine Eq.trans (pushforwardGradedAlgebra_mul_app f (laurent Q.L) i j U
    (((quadruplePsiHom A f Q).app i).val.app (op U) a)
    (((quadruplePsiHom A f Q).app j).val.app (op U) b)) ?_
  refine Eq.trans ?_ ((tensorToLaurent Q.L (TA T Q.L)).map_mul i j (op (f ⁻¹ᵁ U))
    ((quadruplePsi A TA f Q i).val.app (op U) a)
    ((quadruplePsi A TA f Q j).val.app (op U) b)).symm
  refine Eq.trans (congrArg (fun z => ((laurent Q.L).mul i j).app (op (f ⁻¹ᵁ U)) z
    (((quadruplePsiHom A f Q).app j).val.app (op U) b))
    (quadruplePsi_val_app A TA f Q hi U a).symm) ?_
  exact congrArg (fun z => ((laurent Q.L).mul i j).app (op (f ⁻¹ᵁ U))
    (((tensorToLaurent Q.L (TA T Q.L)).app i).val.app (op (f ⁻¹ᵁ U))
      ((quadruplePsi A TA f Q i).val.app (op U) a)) z)
    (quadruplePsi_val_app A TA f Q hj U b).symm

/-! ### The unit clause of the pair -/

/-- **The transposed homomorphism carries the unit of `𝒜` to the unit of the Laurent algebra**,
on sections over an arbitrary open of the base. This is `Twisting.sectionHom_one`, read through
the adjoint transpose and the degree identification `0 * 1 = 0`. -/
public theorem quadruplePsiHom_app_zero_one (Q : Quadruple f (situationAlgebra A) 1)
    (U : S.Opens) :
    letI := Q.isInvertible
    ((quadruplePsiHom A f Q).app 0).val.app (op U) ((situationAlgebra A).one.eval (op U)) =
      (laurent Q.L).one.eval (op (f ⁻¹ᵁ U)) := by
  let := Q.isInvertible
  refine Eq.trans (Stacks.RingedSpace.homEquiv_val_app (ringedSpaceHom f)
    ((situationAlgebra A).piece 0) ((laurent Q.L).piece 0) (quadrupleTwistingApp A f Q 0)
    (op U) ((situationAlgebra A).one.eval (op U))) ?_
  refine Eq.trans (congrArg (fun z => (Q.twisting.app 0).val.app
    ((opensMap (ringedSpaceHom f)).op.obj (op U)) z) ?_)
    (Q.twisting.sectionHom_one (op U))
  refine Eq.trans (congrArg (fun z => z.val.app ((opensMap (ringedSpaceHom f)).op.obj (op U))
    (pullbackUnit (ringedSpaceHom f) ((situationAlgebra A).piece 0) (op U)
      ((situationAlgebra A).one.eval (op U))))
    (map_eqToHom_piece f (situationAlgebra A) (mul_one (0 : ℤ)).symm).symm) ?_
  exact pullbackUnit_naturality (ringedSpaceHom f)
    (eqToHom (congrArg (situationAlgebra A).piece (mul_one (0 : ℤ)).symm)) (op U)
    ((situationAlgebra A).one.eval (op U))

/-- **The graded map of the pair a quadruple determines is unital.** -/
public theorem quadruplePsi_map_one (Q : Quadruple f (situationAlgebra A) 1) (U : S.Opens) :
    (quadruplePsi A TA f Q 0).val.app (op U) (A.one U) =
      (TA T Q.L).tensor.one.eval (op (f ⁻¹ᵁ U)) := by
  let := Q.isInvertible
  refine section_injective_of_isIso ((tensorToLaurent Q.L (TA T Q.L)).app 0)
    (isIso_tensorToLaurent_app Q.L (TA T Q.L) 0 le_rfl) (op (f ⁻¹ᵁ U)) ?_
  refine Eq.trans (quadruplePsi_val_app A TA f Q le_rfl U (A.one U)) ?_
  refine Eq.trans (quadruplePsiHom_app_zero_one A f Q U) ?_
  exact ((tensorToLaurent Q.L (TA T Q.L)).map_one (op (f ⁻¹ᵁ U))).symm

/-! ### The surjectivity clause of the pair -/

/-- The adjoint transpose of the graded map, followed by the comparison with the Laurent
algebra, is the aligned family the quadruple carries. -/
public theorem homEquiv_symm_quadruplePsi_comp (Q : Quadruple f (situationAlgebra A) 1)
    {n : ℤ} (hn : 0 ≤ n) :
    letI := Q.isInvertible
    ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
          (quadruplePsi A TA f Q n) ≫ (tensorToLaurent Q.L (TA T Q.L)).app n =
      quadrupleTwistingApp A f Q n := by
  let := Q.isInvertible
  have hdef := quadruplePsi_eq_of_nonneg A TA f Q hn
  have hsymm : ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
      (quadruplePsi A TA f Q n) =
        quadrupleTwistingApp A f Q n ≫
          @inv _ _ _ _ ((tensorToLaurent Q.L (TA T Q.L)).app n)
            (isIso_tensorToLaurent_app Q.L (TA T Q.L) n hn) := by
    refine Eq.trans (congrArg
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm hdef) ?_
    refine Eq.trans ((pullbackAdjunction (ringedSpaceHom f)).homEquiv_naturality_right_symm
      ((quadruplePsiHom A f Q).app n)
      (@inv _ _ _ _ ((tensorToLaurent Q.L (TA T Q.L)).app n)
        (isIso_tensorToLaurent_app Q.L (TA T Q.L) n hn))) ?_
    exact congrArg (fun z => z ≫ @inv _ _ _ _ ((tensorToLaurent Q.L (TA T Q.L)).app n)
        (isIso_tensorToLaurent_app Q.L (TA T Q.L) n hn))
      (((pullbackAdjunction (ringedSpaceHom f)).homEquiv _ _).symm_apply_apply
        (quadrupleTwistingApp A f Q n))
  refine Eq.trans (congrArg (fun z => z ≫ (tensorToLaurent Q.L (TA T Q.L)).app n) hsymm) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun z => quadrupleTwistingApp A f Q n ≫ z)
    (@IsIso.inv_hom_id _ _ _ _ ((tensorToLaurent Q.L (TA T Q.L)).app n)
      (isIso_tensorToLaurent_app Q.L (TA T Q.L) n hn))) ?_
  exact Category.comp_id _

/-- The aligned family is epimorphic wherever the quadruple's own family is: the two differ by
the degree identification `n * 1 = n`, which is an isomorphism. -/
public theorem epi_quadrupleTwistingApp (Q : Quadruple f (situationAlgebra A) 1) {n : ℤ}
    (h : letI := Q.isInvertible; Epi (Q.twisting.app n)) :
    letI := Q.isInvertible
    Epi (quadrupleTwistingApp A f Q n) :=
  let := Q.isInvertible
  epi_isoComp _ (Q.twisting.app n) (isIso_eqToHom _) h

/-- **The degree-one surjectivity clause of Tag 01O4's pair, for the pair a quadruple
determines.** -/
public theorem epi_quadruplePsi_one (Q : Quadruple f (situationAlgebra A) 1) :
    letI := Q.isInvertible
    Epi (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
          (quadruplePsi A TA f Q 1) ≫
        ((TA T Q.L).tensorPieceIso 1).hom ≫
        eqToHom (by rfl : SheafOfModules.tensorPower (Opens.grothendieckTopology ↥T) Q.L 1
          = Q.L)) := by
  let := Q.isInvertible
  have hepi0 : Epi (quadrupleTwistingApp A f Q 1) :=
    epi_quadrupleTwistingApp A f Q Q.epi_app_one
  have hepi : Epi (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
      (quadruplePsi A TA f Q 1)) := by
    refine epi_of_epi_comp_isoHom _
      (@asIso _ _ _ _ ((tensorToLaurent Q.L (TA T Q.L)).app 1)
        (isIso_tensorToLaurent_app Q.L (TA T Q.L) 1 Int.one_nonneg)) ?_
    have hc : ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
          (quadruplePsi A TA f Q 1) ≫
            (@asIso _ _ _ _ ((tensorToLaurent Q.L (TA T Q.L)).app 1)
              (isIso_tensorToLaurent_app Q.L (TA T Q.L) 1 Int.one_nonneg)).hom =
        quadrupleTwistingApp A f Q 1 :=
      homEquiv_symm_quadruplePsi_comp A TA f Q Int.one_nonneg
    exact epi_of_eq hc hepi0
  exact epi_compIso _ _ _ hepi ((TA T Q.L).tensorPieceIso 1).isIso_hom (isIso_eqToHom _)

/-! ### The pair -/

/-- **The pair of Tag 01O4 a quadruple of Section 01NS at `d = 1` determines.** -/
public def quadruplePair (Q : Quadruple f (situationAlgebra A) 1) : F1Pair A TA f where
  L := Q.L
  invertible := Q.isInvertible
  ψ := quadruplePsi A TA f Q
  map_mul := quadruplePsi_map_mul A TA f Q
  map_one := quadruplePsi_map_one A TA f Q
  degreeOneSurjective := epi_quadruplePsi_one A TA f Q

/-! ### The two constructions are mutually inverse, up to strict equivalence -/

/-- **The family the pair a quadruple determines gives back is the quadruple's own family.**

In a nonnegative degree this is `homEquiv_symm_quadruplePsi_comp` with the two degree
identifications `n * 1 = n` cancelled; in a negative degree the common source is a zero object,
so there is nothing to check. -/
public theorem laurentApp_quadruplePair (Q : Quadruple f (situationAlgebra A) 1) (n : ℤ) :
    letI := Q.isInvertible
    (quadruplePair A TA f Q).laurentApp A TA f n = Q.twisting.app n := by
  let := Q.isInvertible
  rcases lt_or_ge n 0 with hn | hn
  · exact (isZero_pullbackPiece_of_neg A f (by rw [mul_one]; exact hn : n * 1 < 0)).eq_of_src _ _
  refine Eq.trans (congrArg (fun z => eqToHom (congrArg
      (fun k : ℤ => (pullbackFunctor (ringedSpaceHom f)).obj ((situationAlgebra A).piece k))
      (mul_one n)) ≫ z) (homEquiv_symm_quadruplePsi_comp A TA f Q hn)) ?_
  exact eqToHom_comp_eqToHom_comp _ _ (Q.twisting.app n)

/-- **The quadruple of the pair of a quadruple is strictly equivalent to that quadruple.** The
invertible module is the same one, and the witnessing isomorphism of Laurent algebras is the
identity: by `laurentApp_quadruplePair` the two maps `ψ` agree on the nose. -/
public theorem strictlyEquivalent_quadruple_quadruplePair
    (Q : Quadruple f (situationAlgebra A) 1) :
    Quadruple.StrictlyEquivalent ((quadruplePair A TA f Q).quadruple A TA f) Q := by
  let := Q.isInvertible
  refine (Quadruple.strictlyEquivalent_iff_exists_hom _ _).2
    ⟨Iso.refl (laurent Q.L), fun n => ?_⟩
  exact Eq.trans (Category.comp_id _) (laurentApp_quadruplePair A TA f Q n)

/-! ### Surjectivity, and the bijection of Tag 01O4 -/

/-- **The map from Tag 01O4's functor `F_1` to Section 01NS's `F_d` at `d = 1` is
surjective**: every quadruple is strictly equivalent to the quadruple of a pair. -/
public theorem quadrupleClass_surjective : Function.Surjective (quadrupleClass A TA f) :=
  Quotient.ind fun Q =>
    ⟨Quot.mk _ (quadruplePair A TA f Q),
      Quotient.sound (strictlyEquivalent_quadruple_quadruplePair A TA f Q)⟩

/-- **The two functors agree**: Tag 01O4's set of strict isomorphism classes of invertible
degree-one quotients of `f^*𝒜` and Section 01NS's set `F_1(T)` of strict equivalence classes of
quadruples are in bijection. -/
public theorem quadrupleClass_bijective : Function.Bijective (quadrupleClass A TA f) :=
  ⟨quadrupleClass_injective A TA f, quadrupleClass_surjective A TA f⟩

variable (X : Stacks.AlgebraicGeometry.RelativeProj.RelativeProjData A)

/-- **Tag 01O4.** For a quasi-coherent graded `𝒪_S`-algebra generated in degree one, the strict
isomorphism classes of invertible degree-one quotients of `f^*𝒜` are in bijection with the
morphisms `T ⟶ Proj_S(𝒜)` over `S`: relative `Proj` represents the functor `F_1` of Tag 01O4.

The map is `Stacks.AlgebraicGeometry.ProjRepresentsF1.pairClassifyingHom`, whose two factors are
`quadrupleClass` and the relative universal property `quadrupleClassEquiv`; no
representability is assumed and no bijection is taken as an argument. Injectivity is
`pairClassifyingHom_injective` and surjectivity comes from `quadrupleClass_surjective`, which is
the pair a quadruple determines. -/
public theorem pairClassifyingHom_bijective (hgen : IsGeneratedInDegreeOne A) :
    Function.Bijective (pairClassifyingHom A TA f X hgen) :=
  Function.Bijective.comp (quadrupleClassEquiv A X hgen f).bijective
    (quadrupleClass_bijective A TA f)

/-- **Tag 01O4.** The bijection of Tag 01O4, as an equivalence of types. -/
public def pairClassifyingEquiv (hgen : IsGeneratedInDegreeOne A) :
    F1 A TA f ≃ {g : T ⟶ X.scheme // g ≫ X.toBase = f} :=
  Equiv.ofBijective _ (pairClassifyingHom_bijective A TA f X hgen)

end Stacks.AlgebraicGeometry.ProjRepresentsF1

end
