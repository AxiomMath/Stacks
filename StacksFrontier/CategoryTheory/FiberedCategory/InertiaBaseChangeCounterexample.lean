module

public import Mathlib.CategoryTheory.SingleObj
public import StacksFrontier.CategoryTheory.FiberedCategory.InertiaBaseChange

/-!
# The base-change comparison for the relative inertia needs `F` to be over the base

`CategoryTheory.RelativeInertia.isEquivalenceOver_toBaseChangeFibreProduct` proves the left
square of Stacks 06PQ — that the canonical comparison
`Θ : I_{X'/Y'} ⥤ I_{X/Y} ×_X X'` is an equivalence over the base, where `X' = X ×_Y Y'` —
under the hypothesis `hF : F ⋙ pY = pX`, i.e. that `F` is a 1-morphism of categories over
`C`. The naive reading of Tag 06PQ states the same conclusion with **no** hypothesis
relating `F` to the structure functors. This file shows that that statement is false.

`CategoryTheory.RelativeInertia.BaseChangeComparisonStatement` is that naive conclusion,
verbatim, as a predicate on `(pX, pY', pY, F, G)`;
`CategoryTheory.RelativeInertia.baseChangeComparisonStatement_of_comp_eq` records that the
proved theorem gives it whenever `hF` holds; and
`CategoryTheory.RelativeInertia.not_baseChangeComparisonStatement` refutes it for an
explicit choice of data in which `hF` fails and `G ⋙ pY = pY'` still holds.

## The counterexample

Let `M` be a nontrivial group, here `Multiplicative ℤ`, and let `σ ≠ 1` in `M`. Take

* `C = X = SingleObj M` with `pX = 𝟭`;
* `Y = Y' = SingleObj Unit`, the terminal category, with `G = 𝟭` and `pY = pY'` the functor
  induced by the trivial monoid homomorphism — so `G ⋙ pY = pY'` holds;
* `F : X ⥤ Y` induced by the trivial monoid homomorphism `M →* Unit`.

Then `F ⋙ pY ≠ pX`, since `(F ⋙ pY) σ = 1` while `pX σ = σ`.

The object `x' = (⋆, ⋆, ⋆, id)` of `X ×_Y Y'` carries only the identity automorphism: the
`Y'`-component of an automorphism is an identity, which forces the common base morphism to
be an identity, which — as `pX = 𝟭` — forces the `X`-component to be an identity. So every
object `(x', α')` of `I_{X'/Y'}` has trivial `X`-component, and the comparison `Θ`, whose
action is pinned by the clauses of the statement, sends it to an object of `I_{X/Y} ×_X X'` whose
`I_{X/Y}`-component is `(⋆, id)`.

But `(⋆, σ)` is also an object of `I_{X/Y}` — the condition `F σ = id` is vacuous, `Y`
being terminal — so `P = (⋆, (⋆, σ), x', id)` is an object of `I_{X/Y} ×_X X'`, and a
morphism `Θ (x', α') ⟶ P` is in particular a morphism `(⋆, id) ⟶ (⋆, σ)` of `I_{X/Y}`,
i.e. an element `c` of `M` with `σ c = c`, forcing `σ = 1`. An equivalence is essentially
surjective, so no such `Θ` can be one.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

namespace RelativeInertia

universe uC vC uX vX uY' vY' uY vY

/-! ## The naive statement as a predicate -/

section Statement

variable {C : Type uC} [Category.{vC} C]
variable {X : Type uX} [Category.{vX} X]
variable {Y' : Type uY'} [Category.{vY'} Y']
variable {Y : Type uY} [Category.{vY} Y]

/-- The conclusion of the naive reading of Tag 06PQ, verbatim, as a predicate on the data
`(pX, pY', pY, F, G)`: there is a comparison 1-morphism from `I_{X'/Y'}` to
`I_{X/Y} ×_X X'` whose action on objects, automorphisms, gluing datum and morphisms is the
canonical one, and which is an equivalence over `C`. The naive reading asserts this for arbitrary
data; `baseChangeComparisonStatement_of_comp_eq` proves it when `F` is a 1-morphism over
`C`, and `not_baseChangeComparisonStatement` refutes it in general. -/
def BaseChangeComparisonStatement (pX : X ⥤ C) (pY' : Y' ⥤ C) (pY : Y ⥤ C) (F : X ⥤ Y)
    (G : Y' ⥤ Y) : Prop :=
  ∃ Θ : RelativeInertia (TwoFibreProductOver.snd pX pY' pY F G) ⥤
      BaseChangeFibreProduct pX pY' pY F G,
    (∀ A : RelativeInertia (TwoFibreProductOver.snd pX pY' pY F G),
      (Θ.obj A).x.obj = A.obj.x ∧
      HEq (Θ.obj A).x.auto.asIso.hom A.auto.asIso.hom.a ∧
      (Θ.obj A).y = A.obj ∧
      HEq (Θ.obj A).iso.hom (𝟙 A.obj.x)) ∧
    (∀ {A B : RelativeInertia (TwoFibreProductOver.snd pX pY' pY F G)} (φ : A ⟶ B),
      HEq (Θ.map φ).a.hom φ.hom.a ∧
      HEq (Θ.map φ).b φ.hom) ∧
    Nonempty (IsEquivalenceOver
      (RelativeInertia.π (TwoFibreProductOver.snd pX pY' pY F G) ⋙
        TwoFibreProductOver.structureFunctor pX pY' pY F G)
      (TwoFibreProductOver.structureFunctor (RelativeInertia.π F ⋙ pX)
        (TwoFibreProductOver.structureFunctor pX pY' pY F G) pX
        (RelativeInertia.π F) (TwoFibreProductOver.fst pX pY' pY F G)) Θ)

/-- Stacks 06PQ gives the naive statement as soon as `F` is a 1-morphism of categories over
`C`. -/
theorem baseChangeComparisonStatement_of_comp_eq (pX : X ⥤ C) (pY' : Y' ⥤ C) (pY : Y ⥤ C)
    (F : X ⥤ Y) (G : Y' ⥤ Y) (hF : F ⋙ pY = pX) :
    BaseChangeComparisonStatement pX pY' pY F G :=
  exists_baseChangeComparison pX pY' pY F G hF

end Statement

/-! ## The counterexample -/

section Counterexample

/-- The nontrivial group of the counterexample. -/
abbrev CexM : Type := Multiplicative ℤ

/-- The base category and the source of `F`: the single-object category of `CexM`. -/
abbrev CexBase : Type := SingleObj CexM

/-- The target of `F`, and the second factor of the base change: the terminal category,
realised as the single-object category of the trivial monoid. -/
abbrev CexTerminal : Type := SingleObj Unit

/-- The underlying element of `CexM` of a morphism of `SingleObj CexM`. The hom-types of a
single-object category are the monoid itself, but not syntactically so, which blocks
instance synthesis for the monoid operations; this makes the identification explicit. -/
def cexVal {x y : CexBase} (f : x ⟶ y) : CexM := f

/-- Composition in `SingleObj CexM` is multiplication, in the other order. -/
lemma cexVal_comp {x y z : CexBase} (f : x ⟶ y) (g : y ⟶ z) :
    cexVal (f ≫ g) = cexVal g * cexVal f := rfl

/-- The identity of `SingleObj CexM` is the unit. -/
lemma cexVal_id (x : CexBase) : cexVal (𝟙 x) = 1 := rfl

/-- Every transport isomorphism of `CexBase` is the unit of `CexM`: its source and target
are the unique object. -/
lemma cexVal_eqToHom {x y : CexBase} (h : x = y) : cexVal (eqToHom h) = 1 := rfl

/-- For a functor into `CexBase` from a single-object category, `IsHomLift f g` says
exactly that `g` maps to `f`: the transports in the definition are units. -/
lemma cex_map_eq_of_isHomLift {M : Type} [Monoid M] (p : SingleObj M ⥤ CexBase)
    {R S : CexBase} (f : R ⟶ S) {a b : SingleObj M} (g : a ⟶ b) [p.IsHomLift f g] :
    cexVal (p.map g) = cexVal f := by
  rw [IsHomLift.fac' p f g, cexVal_comp, cexVal_comp, cexVal_eqToHom, mul_one, one_mul]

/-- The nontrivial element `σ` of `CexM`, as a morphism of `CexBase`. -/
def cexSigma : SingleObj.star CexM ⟶ SingleObj.star CexM :=
  ((Multiplicative.ofAdd (1 : ℤ)) : CexM)

/-- Its inverse. -/
def cexSigmaInv : SingleObj.star CexM ⟶ SingleObj.star CexM :=
  (((Multiplicative.ofAdd (1 : ℤ))⁻¹) : CexM)

/-- The underlying element of `σ`. -/
lemma cexVal_cexSigma : cexVal cexSigma = Multiplicative.ofAdd (1 : ℤ) := rfl

/-- `σ` is not the identity. -/
lemma cexVal_cexSigma_ne_one : cexVal cexSigma ≠ 1 := by
  rw [cexVal_cexSigma]
  intro h
  have h0 : (1 : ℤ) = 0 := by simpa using congrArg Multiplicative.toAdd h
  exact absurd h0 (by decide)

/-- The trivial monoid homomorphism to the trivial monoid. -/
def cexToUnitHom : CexM →* Unit where
  toFun _ := ()
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The trivial monoid homomorphism from the trivial monoid. -/
def cexFromUnitHom : Unit →* CexM where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (one_mul 1).symm

/-- The structure functor of `X = C`: the identity. It is *not* compatible with `F`. -/
abbrev cexPX : CexBase ⥤ CexBase := 𝟭 CexBase

/-- The structure functor of `Y` (and of `Y'`), induced by the trivial homomorphism. -/
abbrev cexPY : CexTerminal ⥤ CexBase := SingleObj.mapHom Unit CexM cexFromUnitHom

/-- `F : X ⥤ Y`, induced by the trivial homomorphism. -/
abbrev cexF : CexBase ⥤ CexTerminal := SingleObj.mapHom CexM Unit cexToUnitHom

/-- `G : Y' ⥤ Y`: the identity, so that `G ⋙ pY = pY'` holds. -/
abbrev cexG : CexTerminal ⥤ CexTerminal := 𝟭 CexTerminal

/-- `G` *is* a 1-morphism over the base, so the counterexample isolates the failure of the
hypothesis on `F`. -/
lemma cex_comp_eq_G : cexG ⋙ cexPY = cexPY := rfl

/-- `F` is not a 1-morphism over the base: it kills `σ`, which `pX` does not. -/
lemma cex_not_comp_eq_F : cexF ⋙ cexPY ≠ cexPX := by
  intro h
  have h1 : cexVal ((cexF ⋙ cexPY).map cexSigma) = 1 := rfl
  have h2 := congrArg cexVal (Functor.congr_hom h cexSigma)
  rw [h1, cexVal_comp, cexVal_comp, cexVal_eqToHom, mul_one, one_mul, Functor.id_map] at h2
  exact cexVal_cexSigma_ne_one h2.symm

/-- The unique object of the base change `X ×_Y Y'`. -/
def cexBaseChangeObj : TwoFibreProductOver cexPX cexPY cexPY cexF cexG where
  base := SingleObj.star CexM
  x := SingleObj.star CexM
  y := SingleObj.star Unit
  hx := rfl
  hy := rfl
  iso := Iso.refl _
  vertical := IsHomLift.id rfl

/-- The automorphism of the unique object of `X` given by `σ`. -/
def cexSigmaAuto : Aut (SingleObj.star CexM) where
  asIso :=
    { hom := cexSigma
      inv := cexSigmaInv
      hom_inv_id := inv_mul_cancel (Multiplicative.ofAdd (1 : ℤ))
      inv_hom_id := mul_inv_cancel (Multiplicative.ofAdd (1 : ℤ)) }

/-- The object `(⋆, σ)` of `I_{X/Y}`: the condition `F σ = id` is vacuous since `Y` is
terminal. -/
def cexSigmaInertia : RelativeInertia cexF where
  obj := SingleObj.star CexM
  auto := cexSigmaAuto
  cond := rfl

/-- The object `(⋆, (⋆, σ), x', id)` of `I_{X/Y} ×_X X'`, which is not in the image of the
comparison 1-morphism. -/
def cexBadObj : BaseChangeFibreProduct cexPX cexPY cexPY cexF cexG where
  base := SingleObj.star CexM
  x := cexSigmaInertia
  y := cexBaseChangeObj
  hx := rfl
  hy := rfl
  iso := Iso.refl _
  vertical := IsHomLift.id rfl

/-- Every automorphism of an object of `X ×_Y Y'` has trivial `X`-component here: its
`Y'`-component is an identity, which forces the common base morphism to be an identity,
which forces the `X`-component to be an identity because `pX` is the identity functor. -/
lemma cex_auto_a_eq_one (A : RelativeInertia (TwoFibreProductOver.snd cexPX cexPY cexPY
    cexF cexG)) : cexVal A.auto.asIso.hom.a = 1 := by
  have hbase : cexVal A.auto.asIso.hom.hbase = 1 := by
    have := A.auto.asIso.hom.hb
    exact (cex_map_eq_of_isHomLift cexPY A.auto.asIso.hom.hbase A.auto.asIso.hom.b).symm
  have := A.auto.asIso.hom.ha
  exact (cex_map_eq_of_isHomLift cexPX A.auto.asIso.hom.hbase A.auto.asIso.hom.a).trans hbase

/-- **The naive reading of Tag 06PQ is false.** Without a hypothesis relating `F`
to the structure functors there is no comparison 1-morphism with the prescribed action which
is an equivalence over the base, even when `G` is a 1-morphism over the base.

Essential surjectivity of such a `Θ` gives an object `(x', α')` of `I_{X'/Y'}` and an
isomorphism `Θ (x', α') ≅ (⋆, (⋆, σ), x', id)`. Its `I_{X/Y}`-component is a morphism
`(⋆, α) ⟶ (⋆, σ)` with `α = id` by `cex_auto_a_eq_one` together with the statement's own clause
pinning the automorphism of `Θ (x', α')`, so its commuting-square condition reads `σ c = c`
for some `c` in the group `CexM`, forcing `σ = 1`. -/
theorem not_baseChangeComparisonStatement :
    ¬ BaseChangeComparisonStatement cexPX cexPY cexPY cexF cexG := by
  rintro ⟨Θ, hobj, -, ⟨E⟩⟩
  have hEq : Θ.IsEquivalence := E.isEquivalence
  obtain ⟨A, ⟨u⟩⟩ : ∃ A, Nonempty (Θ.obj A ⟶ cexBadObj) :=
    ⟨Θ.objPreimage cexBadObj, ⟨(Θ.objObjPreimageIso cexBadObj).hom⟩⟩
  -- The automorphism of the `I_{X/Y}`-component of `Θ A` is the identity.
  have hauto : cexVal (Θ.obj A).x.auto.asIso.hom = 1 :=
    (congrArg cexVal (eq_of_heq (hobj A).2.1)).trans (cex_auto_a_eq_one A)
  -- The commuting square of the `I_{X/Y}`-component of `u` reads `σ c = c`.
  have hcomm := congrArg cexVal u.a.comm
  rw [cexVal_comp, cexVal_comp, hauto, mul_one] at hcomm
  exact cexVal_cexSigma_ne_one (mul_right_cancel (b := cexVal u.a.hom)
    (hcomm.trans (one_mul _).symm))

end Counterexample

end RelativeInertia

end CategoryTheory

end
