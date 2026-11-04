module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraBridge
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.BaseChangeFunctor
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.QuadruplePullback
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.SituationRestrict
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.UnionPullback

/-!
# Transporting quadruples along an isomorphism of the graded algebra on the base

Let `X` be a scheme and `𝒜`, `ℬ` two sheaves of graded `𝒪_X`-algebras. A quadruple
`(d, f : T → X, L, ψ)` of Section 01NS depends on the algebra **only** through the family
`ψ : f^*𝒜_{id} ⟶ L^{⊗ i}` and its two conditions, multiplicativity and the preservation of the
degree-zero unit. So a homomorphism of sheaves of graded algebras `Φ : 𝒜 ⟶ ℬ` preserving the
unit — a `SheafOfModules.GradedAlgebra.UnitalHom` — carries a quadruple for `ℬ` to a quadruple
for `𝒜` by precomposition, and when every component of `Φ` is an isomorphism the two
constructions are inverse bijections. Precomposition does not disturb the surjectivity of the
degree-one component either, for the same reason.

This file carries that out, at the level of the map `ψ`
(`...RelativeProjQcohSheaf.Twisting.algebraTransport`), of quadruples
(`...RelativeProjQcohSheaf.Quadruple.algebraTransport`) and of the sets `F_d(T)` of strict
equivalence classes (`...RelativeProjQcohSheaf.Fd.algebraTransportEquiv`), and records that the
bijection commutes with the pullback along a morphism of test schemes.

## The instance it is built for

The chart-wise argument of Tags 01NY and 01NZ needs exactly one instance of it. The functor
`F_d` of Section 01NS is written with the inverse image `...RelativeProjQcohSheaf.baseAlgebra`
of Tag 01NT, and the base change `F'_d ≅ h_{S'} ×_{h_S} F_d` of that tag —
`...RelativeProjQcohSheaf.Fd.baseFibreEquiv` — produces an `F_d` for `baseAlgebra`; the
identification of the projective spectrum of an affine chart with the chart, on the other hand,
is stated for the **restriction** `...RelativeProjBridge.SheafGradedAlgebra.restrict`, whose
sections over `V` are by definition the sections over `f ''ᵁ V`. The two spellings are not
equal, but `...RelativeProjQcohSheaf.restrictPullbackUnitalHom` is a homomorphism of sheaves of
graded algebras from the first to the second, and
`...RelativeProjQcohSheaf.isIso_restrictPullbackUnitalHom_app` says each of its components is an
isomorphism. `Fd.restrictPullbackEquiv` below is the resulting bijection

`F_d(T) for the restriction  ≃  F_d(T) for the inverse image`

along an open immersion of base schemes, and `Fd.restrictPullbackEquiv_pullback` its naturality
in `T`.

## Main definitions

* `...RelativeProjQcohSheaf.unitalHomInverse`: the inverse of a unital homomorphism all of whose
  components are isomorphisms, again a unital homomorphism.
* `...RelativeProjQcohSheaf.Twisting.algebraTransport`: **the map `ψ` of a quadruple for `ℬ`,
  read as a map `ψ` for `𝒜`** along a unital homomorphism `𝒜 ⟶ ℬ`.
* `...RelativeProjQcohSheaf.Quadruple.algebraTransportEquiv`: **the bijection of quadruples** a
  degreewise-invertible unital homomorphism induces.
* `...RelativeProjQcohSheaf.Fd.algebraTransportEquiv`: **the bijection of the sets `F_d(T)`** of
  strict equivalence classes.
* `...RelativeProjQcohSheaf.Fd.restrictPullbackEquiv`: the instance the chart-wise argument
  needs, comparing the restriction spelling with the inverse-image spelling of the algebra on an
  open subscheme of the base.

## Main results

* `...RelativeProjQcohSheaf.Twisting.algebraTransport_pullback`,
  `...RelativeProjQcohSheaf.Quadruple.algebraTransport_pullback` and
  `...RelativeProjQcohSheaf.Fd.algebraTransport_pullback`: **the transport commutes with the
  pullback along a morphism of test schemes**, so the bijection is natural in `T`. The only
  input is the naturality `...RelativeProjQcohSheaf.compComparison_naturality` of the
  contraction of an iterated pullback.
* `...RelativeProjQcohSheaf.Quadruple.strictlyEquivalent_algebraTransport_iff`: the transport
  matches strict equivalence on the two sides, which is what makes it descend to the classes.

## Implementation notes

The multiplicativity of the transported `ψ` is `Twisting.algebraTransport_key`: the naturality
of the comparison `f^*(M ⊗ N) ≅ f^*M ⊗ f^*N` of Tag 01CD
(`...RelativeProjQcohSheaf.pullbackTensorComparison_naturality_tensorHom`) composed with the
morphism-level multiplicativity of `Φ` (`...RelativeProjQcohSheaf.mulSheaf_comp_app`) and the
commutation `unitalHom_app_eqToHom` of a homomorphism with the degree bookkeeping
`i d + j d = (i + j) d`. That last commutation is stated with the two degrees as **free
variables**, so that `subst` can discharge it; at the compound degrees it is used at, where
neither side is a variable, no tactic can perform the substitution.

The unit normalisation is `Twisting.pullbackOne_comp_map_app_zero`, which reduces to
`oneHom_comp_app_zero` — that a unital homomorphism carries the global unit to the global unit,
which is `SheafOfModules.GradedAlgebra.UnitalHom.sectionsMap_one` read through
`SheafOfModules.unitHomEquiv_symm_comp` — together with
`Stacks.PullbackStrictUnit.pullbackOne_eq`, the formula for the global unit of a pullback.

**Why the two conditions are proved outside the structure instance.** Inside the definition of a
`Twisting` the target of `app i` is `(laurent L).piece i` with `L` the field being defined, and
a goal mentioning it is not type-correct at the `implicit` transparency `rw` checks its motives
at; both `Category.assoc` and the naturality rewrites then report a missing pattern rather than
the cause. `Twisting.algebraTransport_app_mul` and `Twisting.algebraTransport_app_one` take the
degreewise family and the invertible module as ordinary arguments, where the same rewrites fire,
and the structure instance applies them.

`unitalHomInverse` is built degreewise, as the inverse of each component, and its two conditions
are the conditions for `Φ` applied to the preimages. The section-level round trip
`val_app_roundtrip` is stated for an arbitrary pair of morphisms composing to the identity
rather than for `inv`, so that the instance argument never has to be found by unification: at
the use sites the witness is `@CategoryTheory.IsIso.hom_inv_id` with the invertibility supplied
by hand.

## No tag is claimed

Nothing here states a clause of a tag. The file transports the data of a quadruple along an
isomorphism of the graded algebra on the base; it says nothing about representability, and on
its own it is not a step of any tag's proof.

## References

* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NT](https://stacks.math.columbia.edu/tag/01NT)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite

open AlgebraicGeometry Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.SheafOfModules.TensorPower
open Stacks.AlgebraicGeometry.RelativeProjBridge

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {T T' X S : Scheme.{u}}

/-! ### Generalities about homomorphisms of sheaves of graded algebras -/

section Generalities

variable {A B : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X.toRingedSpace)}

/-- **A homomorphism of sheaves of graded algebras commutes with the transport of a degree along
an equality of degrees.** The two degrees are free variables, which is what lets the equality be
substituted; at the compound degrees this is applied to, no tactic can perform the
substitution. -/
theorem unitalHom_app_eqToHom (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B) {p q : ℤ}
    (h : p = q) :
    Φ.app p ≫ eqToHom (congrArg B.piece h) = eqToHom (congrArg A.piece h) ≫ Φ.app q := by
  subst h
  simp

/-- **A unital homomorphism of sheaves of graded algebras commutes with the morphism-level
multiplications.** This is `...RelativeProjQcohSheaf.mulSheaf_comp_app` for the underlying
homomorphism. -/
theorem unitalHom_mulSheaf_comp (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B) (i j : ℤ) :
    A.mulSheaf i j ≫ Φ.app (i + j) = (Φ.app i ⊗ₘ Φ.app j) ≫ B.mulSheaf i j :=
  mulSheaf_comp_app A B Φ.toHom i j

/-- **A unital homomorphism of sheaves of graded algebras carries the global unit to the global
unit**, as an equality of morphisms out of the unit object. This is
`SheafOfModules.GradedAlgebra.UnitalHom.sectionsMap_one`, the same statement at the level of
global sections, read through the bijection `(𝟙_ ⟶ M) ≃ Γ(M)` of
`SheafOfModules.unitHomEquiv`. -/
theorem oneHom_comp_app_zero (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B) :
    SheafOfModules.GradedAlgebra.oneHom A ≫ Φ.app 0 =
      SheafOfModules.GradedAlgebra.oneHom B :=
  (SheafOfModules.unitHomEquiv_symm_comp A.one (Φ.app 0)).trans
    (congrArg (B.piece 0).unitHomEquiv.symm Φ.sectionsMap_one)

/-- **Two morphisms of sheaves of modules composing to the identity compose to the identity on
local sections.** Stated for an arbitrary pair rather than for a morphism and its inverse, so
that no instance has to be found by unification at the use sites. -/
theorem val_app_roundtrip
    {M N : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace)} (a : M ⟶ N) (b : N ⟶ M)
    (hab : a ≫ b = 𝟙 M)
    (U : (TopologicalSpace.Opens X.toRingedSpace.carrier)ᵒᵖ) (z : M.val.obj U) :
    b.val.app U (a.val.app U z) = z := by
  rw [← SheafOfModules.comp_val_app_apply, hab]
  rfl

/-- **The inverse of a unital homomorphism of sheaves of graded algebras all of whose components
are isomorphisms**, again a unital homomorphism. Its two conditions are the two conditions for
`Φ`, applied to the preimages of the given local sections. -/
def unitalHomInverse (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B)
    (h : ∀ n : ℤ, IsIso (Φ.app n)) : SheafOfModules.GradedAlgebra.UnitalHom B A where
  app n := @inv _ _ _ _ (Φ.app n) (h n)
  map_mul i j U x y := by
    have hfwd : ∀ (n : ℤ) (z : (B.piece n).val.obj U),
        (Φ.app n).val.app U ((@inv _ _ _ _ (Φ.app n) (h n)).val.app U z) = z := fun n z =>
      val_app_roundtrip (@inv _ _ _ _ (Φ.app n) (h n)) (Φ.app n)
        (@IsIso.inv_hom_id _ _ _ _ (Φ.app n) (h n)) U z
    have key := Φ.map_mul i j U ((@inv _ _ _ _ (Φ.app i) (h i)).val.app U x)
      ((@inv _ _ _ _ (Φ.app j) (h j)).val.app U y)
    rw [hfwd i x, hfwd j y] at key
    rw [← key, val_app_roundtrip (Φ.app (i + j)) (@inv _ _ _ _ (Φ.app (i + j)) (h (i + j)))
      (@IsIso.hom_inv_id _ _ _ _ (Φ.app (i + j)) (h (i + j)))]
  map_one U := by
    rw [← Φ.map_one U, val_app_roundtrip (Φ.app 0) (@inv _ _ _ _ (Φ.app 0) (h 0))
      (@IsIso.hom_inv_id _ _ _ _ (Φ.app 0) (h 0))]

/-- The components of the inverse unital homomorphism are the inverses of the components. -/
@[simp] theorem unitalHomInverse_app (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B)
    (h : ∀ n : ℤ, IsIso (Φ.app n)) (n : ℤ) :
    (unitalHomInverse Φ h).app n = @inv _ _ _ _ (Φ.app n) (h n) := rfl

/-- The inverse of a degreewise-invertible unital homomorphism is degreewise invertible. -/
theorem isIso_unitalHomInverse_app (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B)
    (h : ∀ n : ℤ, IsIso (Φ.app n)) (n : ℤ) : IsIso ((unitalHomInverse Φ h).app n) :=
  @IsIso.inv_isIso _ _ _ _ (Φ.app n) (h n)

end Generalities

/-! ### The map `ψ` of a quadruple, transported along a unital homomorphism -/

namespace Twisting

variable {A B : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X.toRingedSpace)}

/-- **The global unit of `f^*𝒜` carried through `Φ` is the global unit of `f^*ℬ`.** This is
`oneHom_comp_app_zero` pulled back along `f`, through the formula
`Stacks.PullbackStrictUnit.pullbackOne_eq` for the global unit of a pullback. -/
theorem pullbackOne_comp_map_app_zero (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B)
    (f : T ⟶ X) :
    Stacks.PullbackGradedAlgebra.pullbackOne (ringedSpaceHom f) A ≫
        (pullbackFunctor (ringedSpaceHom f)).map (Φ.app 0) =
      Stacks.PullbackGradedAlgebra.pullbackOne (ringedSpaceHom f) B := by
  rw [Stacks.PullbackStrictUnit.pullbackOne_eq, Stacks.PullbackStrictUnit.pullbackOne_eq,
    Category.assoc, ← CategoryTheory.Functor.map_comp, oneHom_comp_app_zero Φ]

/-- **The multiplication of `𝒜^{(d)}`, pulled back and read through `Φ`, is the multiplication of
`ℬ^{(d)}` pulled back.** This is the whole content of the multiplicativity of a transported `ψ`:
the naturality of the comparison `f^*(M ⊗ N) ≅ f^*M ⊗ f^*N` of Tag 01CD, the morphism-level
multiplicativity of `Φ`, and the commutation of `Φ` with the degree bookkeeping
`i d + j d = (i + j) d`. -/
theorem algebraTransport_key (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B) (f : T ⟶ X)
    (d i j : ℤ) :
    pullbackTensorComparison (ringedSpaceHom f) (A.piece (i * d)) (A.piece (j * d)) ≫
        ((pullbackFunctor (ringedSpaceHom f)).map (Φ.app (i * d)) ⊗ₘ
            (pullbackFunctor (ringedSpaceHom f)).map (Φ.app (j * d))) ≫
          inv (pullbackTensorComparison (ringedSpaceHom f) (B.piece (i * d))
              (B.piece (j * d))) ≫
            (pullbackFunctor (ringedSpaceHom f)).map
              (B.mulSheaf (i * d) (j * d) ≫
                eqToHom (congrArg B.piece (by ring : i * d + j * d = (i + j) * d))) =
      (pullbackFunctor (ringedSpaceHom f)).map
          (A.mulSheaf (i * d) (j * d) ≫
            eqToHom (congrArg A.piece (by ring : i * d + j * d = (i + j) * d))) ≫
        (pullbackFunctor (ringedSpaceHom f)).map (Φ.app ((i + j) * d)) := by
  have halg : (Φ.app (i * d) ⊗ₘ Φ.app (j * d)) ≫ B.mulSheaf (i * d) (j * d) ≫
        eqToHom (congrArg B.piece (by ring : i * d + j * d = (i + j) * d)) =
      (A.mulSheaf (i * d) (j * d) ≫
          eqToHom (congrArg A.piece (by ring : i * d + j * d = (i + j) * d))) ≫
        Φ.app ((i + j) * d) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg
            (fun z => z ≫ eqToHom (congrArg B.piece
              (by ring : i * d + j * d = (i + j) * d)))
            (unitalHom_mulSheaf_comp Φ (i * d) (j * d)).symm).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun z => A.mulSheaf (i * d) (j * d) ≫ z)
              (unitalHom_app_eqToHom Φ
                (show i * d + j * d = (i + j) * d by ring))).trans
            (Category.assoc _ _ _).symm)))
  rw [← Category.assoc, ← pullbackTensorComparison_naturality_tensorHom (ringedSpaceHom f)
      (Φ.app (i * d)) (Φ.app (j * d)), Category.assoc, IsIso.hom_inv_id_assoc,
    ← CategoryTheory.Functor.map_comp]
  exact (congrArg (fun z => (pullbackFunctor (ringedSpaceHom f)).map z) halg).trans
    ((pullbackFunctor (ringedSpaceHom f)).map_comp
      (A.mulSheaf (i * d) (j * d) ≫
        eqToHom (congrArg A.piece (by ring : i * d + j * d = (i + j) * d)))
      (Φ.app ((i + j) * d)))

variable {d : ℤ} {f : T ⟶ X} {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]

/-- **Multiplicativity is carried across the transport.** A degreewise family of maps out of
`f^*ℬ^{(d)}` into the Laurent algebra of `L` which is multiplicative in bidegree `(i, j)` stays
multiplicative after precomposition with the pullback of `Φ`.

The family and the invertible module are ordinary arguments rather than fields of a structure
being defined, which is what lets the rewrites below fire. -/
theorem algebraTransport_app_mul (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B)
    (b : ∀ n : ℤ, (pullbackFunctor (ringedSpaceHom f)).obj (B.piece (n * d)) ⟶
      (laurent L).piece n) (i j : ℤ)
    (hb : (b i ⊗ₘ b j) ≫ (laurent L).mulSheaf i j =
      inv (pullbackTensorComparison (ringedSpaceHom f) (B.piece (i * d)) (B.piece (j * d))) ≫
        (pullbackFunctor (ringedSpaceHom f)).map
            (B.mulSheaf (i * d) (j * d) ≫
              eqToHom (congrArg B.piece (by ring : i * d + j * d = (i + j) * d))) ≫
          b (i + j)) :
    (((pullbackFunctor (ringedSpaceHom f)).map (Φ.app (i * d)) ≫ b i) ⊗ₘ
          ((pullbackFunctor (ringedSpaceHom f)).map (Φ.app (j * d)) ≫ b j)) ≫
        (laurent L).mulSheaf i j =
      inv (pullbackTensorComparison (ringedSpaceHom f) (A.piece (i * d)) (A.piece (j * d))) ≫
        (pullbackFunctor (ringedSpaceHom f)).map
            (A.mulSheaf (i * d) (j * d) ≫
              eqToHom (congrArg A.piece (by ring : i * d + j * d = (i + j) * d))) ≫
          (pullbackFunctor (ringedSpaceHom f)).map (Φ.app ((i + j) * d)) ≫ b (i + j) := by
  have hRHS : ((pullbackFunctor (ringedSpaceHom f)).map (Φ.app (i * d)) ⊗ₘ
          (pullbackFunctor (ringedSpaceHom f)).map (Φ.app (j * d))) ≫
        inv (pullbackTensorComparison (ringedSpaceHom f) (B.piece (i * d))
            (B.piece (j * d))) ≫
          (pullbackFunctor (ringedSpaceHom f)).map
            (B.mulSheaf (i * d) (j * d) ≫
              eqToHom (congrArg B.piece (by ring : i * d + j * d = (i + j) * d))) =
      inv (pullbackTensorComparison (ringedSpaceHom f) (A.piece (i * d)) (A.piece (j * d))) ≫
        (pullbackFunctor (ringedSpaceHom f)).map
            (A.mulSheaf (i * d) (j * d) ≫
              eqToHom (congrArg A.piece (by ring : i * d + j * d = (i + j) * d))) ≫
          (pullbackFunctor (ringedSpaceHom f)).map (Φ.app ((i + j) * d)) := by
    rw [IsIso.eq_inv_comp]
    exact algebraTransport_key Φ f d i j
  refine Eq.trans (congrArg (fun z => z ≫ (laurent L).mulSheaf i j)
    (MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _).symm) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg
    (fun z => ((pullbackFunctor (ringedSpaceHom f)).map (Φ.app (i * d)) ⊗ₘ
      (pullbackFunctor (ringedSpaceHom f)).map (Φ.app (j * d))) ≫ z) hb) ?_
  exact (reassoc_of% hRHS) (b (i + j))

/-- **The unit normalisation is carried across the transport.** -/
theorem algebraTransport_app_one (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B)
    (b : ∀ n : ℤ, (pullbackFunctor (ringedSpaceHom f)).obj (B.piece (n * d)) ⟶
      (laurent L).piece n)
    (hb : Stacks.PullbackGradedAlgebra.pullbackOne (ringedSpaceHom f) B ≫
        (pullbackFunctor (ringedSpaceHom f)).map
          (eqToHom (congrArg B.piece (by ring : (0 : ℤ) = 0 * d))) ≫ b 0 =
      SheafOfModules.GradedAlgebra.oneHom (laurent L)) :
    Stacks.PullbackGradedAlgebra.pullbackOne (ringedSpaceHom f) A ≫
        (pullbackFunctor (ringedSpaceHom f)).map
            (eqToHom (congrArg A.piece (by ring : (0 : ℤ) = 0 * d))) ≫
          (pullbackFunctor (ringedSpaceHom f)).map (Φ.app (0 * d)) ≫ b 0 =
      SheafOfModules.GradedAlgebra.oneHom (laurent L) := by
  have hpre : (Stacks.PullbackGradedAlgebra.pullbackOne (ringedSpaceHom f) A ≫
        (pullbackFunctor (ringedSpaceHom f)).map
          (eqToHom (congrArg A.piece (by ring : (0 : ℤ) = 0 * d)))) ≫
      (pullbackFunctor (ringedSpaceHom f)).map (Φ.app (0 * d)) =
      Stacks.PullbackGradedAlgebra.pullbackOne (ringedSpaceHom f) B ≫
        (pullbackFunctor (ringedSpaceHom f)).map
          (eqToHom (congrArg B.piece (by ring : (0 : ℤ) = 0 * d))) := by
    rw [Category.assoc, ← CategoryTheory.Functor.map_comp,
      ← unitalHom_app_eqToHom Φ (show (0 : ℤ) = 0 * d by ring),
      CategoryTheory.Functor.map_comp, ← Category.assoc,
      pullbackOne_comp_map_app_zero Φ f]
  rwa [← Category.assoc, ← Category.assoc, hpre, Category.assoc]

/-- **The map `ψ` of a quadruple for `ℬ`, read as a map `ψ` for `𝒜`** along a unital
homomorphism `Φ : 𝒜 ⟶ ℬ`: in degree `i` it is the pullback of `Φ` in degree `i d`, followed by
the given component.

Both conditions are carried across: multiplicativity by `algebraTransport_app_mul` and the unit
normalisation by `algebraTransport_app_one`. No invertibility of `Φ` is used. -/
def algebraTransport (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B) (χ : Twisting f B d L) :
    Twisting f A d L where
  app i := (pullbackFunctor (ringedSpaceHom f)).map (Φ.app (i * d)) ≫ χ.app i
  app_mul i j := algebraTransport_app_mul Φ χ.app i j (χ.app_mul i j)
  app_one := algebraTransport_app_one Φ χ.app χ.app_one

/-- The components of the transported map. -/
@[simp] theorem algebraTransport_app (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B)
    (χ : Twisting f B d L) (i : ℤ) :
    (algebraTransport Φ χ).app i =
      (pullbackFunctor (ringedSpaceHom f)).map (Φ.app (i * d)) ≫ χ.app i := rfl

/-- The transported family, read over a member of the pullback along a morphism of test schemes.
This is the naturality `compComparison_naturality` of the contraction of an iterated pullback,
with the two associativity rearrangements it needs. -/
theorem algebraTransport_pullbackApp_eq (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B)
    (χ : Twisting f B d L) (g : T' ⟶ T) (i : ℤ) :
    compComparison g f (A.piece (i * d)) ≫
        (pullbackFunctor (ringedSpaceHom g)).map
            ((pullbackFunctor (ringedSpaceHom f)).map (Φ.app (i * d)) ≫ χ.app i) ≫
          laurentPullback g L i =
      (pullbackFunctor (ringedSpaceHom (g ≫ f))).map (Φ.app (i * d)) ≫
        compComparison g f (B.piece (i * d)) ≫
          (pullbackFunctor (ringedSpaceHom g)).map (χ.app i) ≫ laurentPullback g L i := by
  rw [CategoryTheory.Functor.map_comp, ← Category.assoc, ← Category.assoc,
    compComparison_naturality g f (Φ.app (i * d)), Category.assoc, Category.assoc]

/-- **The transport along `Φ` commutes with the pullback along a morphism of test schemes.** -/
theorem algebraTransport_pullback (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B)
    (χ : Twisting f B d L) (g : T' ⟶ T) :
    (algebraTransport Φ χ).pullback g = algebraTransport Φ (χ.pullback g) :=
  Twisting.ext fun i => algebraTransport_pullbackApp_eq Φ χ g i

end Twisting

/-! ### Quadruples, transported -/

namespace Quadruple

variable {A B : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X.toRingedSpace)}
  {d : ℤ} {f : T ⟶ X}

/-- **A quadruple for `ℬ`, read as a quadruple for `𝒜`** along a unital homomorphism
`Φ : 𝒜 ⟶ ℬ` all of whose components are isomorphisms. The invertible module is unchanged — it
lives on the test scheme, which the algebra on the base does not touch — and `ψ` is carried
across by `Twisting.algebraTransport`. The surjectivity of the degree-one component survives
because the component of `Φ` precomposed with it is an isomorphism. -/
def algebraTransport (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B)
    (h : ∀ n : ℤ, IsIso (Φ.app n)) (P : Quadruple f B d) : Quadruple f A d where
  L := P.L
  isInvertible := P.isInvertible
  twisting := Twisting.algebraTransport Φ P.twisting
  epi_app_one := by
    have := h (1 * d)
    have := P.epi_app_one
    exact epi_comp _ _

/-- The transport leaves the invertible module of a quadruple unchanged. -/
@[simp] theorem algebraTransport_L (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B)
    (h : ∀ n : ℤ, IsIso (Φ.app n)) (P : Quadruple f B d) :
    (algebraTransport Φ h P).L = P.L := rfl

/-- The components of the map of the transported quadruple. -/
@[simp] theorem algebraTransport_twisting_app (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B)
    (h : ∀ n : ℤ, IsIso (Φ.app n)) (P : Quadruple f B d) (i : ℤ) :
    (algebraTransport Φ h P).twisting.app i =
      (pullbackFunctor (ringedSpaceHom f)).map (Φ.app (i * d)) ≫ P.twisting.app i := rfl

/-- Transporting along `Φ` and then along `Ψ` is the identity when `Ψ` is degreewise a left
inverse of `Φ`. -/
private theorem algebraTransport_algebraTransport_of_comp_eq_id
    (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B) (h : ∀ n : ℤ, IsIso (Φ.app n))
    (Ψ : SheafOfModules.GradedAlgebra.UnitalHom B A) (h' : ∀ n : ℤ, IsIso (Ψ.app n))
    (hΨΦ : ∀ n, Ψ.app n ≫ Φ.app n = 𝟙 _) (P : Quadruple f B d) :
    algebraTransport Ψ h' (algebraTransport Φ h P) = P :=
  Quadruple.ext rfl fun i => heq_of_eq (by
    simp [← Functor.map_comp_assoc, hΨΦ])

/-- The transport along `Φ` and the transport along its inverse are inverse, in one
direction. -/
theorem algebraTransport_inverse_algebraTransport
    (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B) (h : ∀ n : ℤ, IsIso (Φ.app n))
    (P : Quadruple f B d) :
    algebraTransport (unitalHomInverse Φ h) (isIso_unitalHomInverse_app Φ h)
        (algebraTransport Φ h P) = P :=
  algebraTransport_algebraTransport_of_comp_eq_id Φ h _ (isIso_unitalHomInverse_app Φ h)
    (fun n => @IsIso.inv_hom_id _ _ _ _ (Φ.app n) (h n)) P

/-- The transport along `Φ` and the transport along its inverse are inverse, in the other
direction. -/
theorem algebraTransport_algebraTransport_inverse
    (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B) (h : ∀ n : ℤ, IsIso (Φ.app n))
    (P : Quadruple f A d) :
    algebraTransport Φ h
        (algebraTransport (unitalHomInverse Φ h) (isIso_unitalHomInverse_app Φ h) P) = P :=
  algebraTransport_algebraTransport_of_comp_eq_id _ (isIso_unitalHomInverse_app Φ h) Φ h
    (fun n => @IsIso.hom_inv_id _ _ _ _ (Φ.app n) (h n)) P

/-- **The quadruples for `𝒜` and for `ℬ` over a fixed morphism correspond bijectively** along a
unital homomorphism `Φ : 𝒜 ⟶ ℬ` all of whose components are isomorphisms. -/
def algebraTransportEquiv (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B)
    (h : ∀ n : ℤ, IsIso (Φ.app n)) : Quadruple f B d ≃ Quadruple f A d where
  toFun P := algebraTransport Φ h P
  invFun P := algebraTransport (unitalHomInverse Φ h) (isIso_unitalHomInverse_app Φ h) P
  left_inv P := algebraTransport_inverse_algebraTransport Φ h P
  right_inv P := algebraTransport_algebraTransport_inverse Φ h P

/-- **The transport matches strict equivalence on the two sides.** An isomorphism of the Laurent
algebras carries one `ψ` to another exactly when it carries the transported maps to one another,
because the two differ by precomposition with an isomorphism. -/
theorem strictlyEquivalent_algebraTransport_iff (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B)
    (h : ∀ n : ℤ, IsIso (Φ.app n)) {P Q : Quadruple f B d} :
    StrictlyEquivalent (algebraTransport Φ h P) (algebraTransport Φ h Q) ↔
      StrictlyEquivalent P Q := by
  rw [strictlyEquivalent_iff_exists_hom, strictlyEquivalent_iff_exists_hom]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, fun n => ?_⟩
    let : IsIso (Φ.app (n * d)) := h (n * d)
    refine (cancel_epi ((pullbackFunctor (ringedSpaceHom f)).map (Φ.app (n * d)))).mp ?_
    exact (Category.assoc _ _ _).symm.trans (hc n)
  · rintro ⟨c, hc⟩
    refine ⟨c, fun n => ?_⟩
    exact (Category.assoc _ _ _).trans
      (congrArg (fun z => (pullbackFunctor (ringedSpaceHom f)).map (Φ.app (n * d)) ≫ z) (hc n))

/-- The transport of a quadruple commutes with the pullback along a morphism of test
schemes. -/
theorem algebraTransport_pullback (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B)
    (h : ∀ n : ℤ, IsIso (Φ.app n)) (P : Quadruple f B d) (g : T' ⟶ T) :
    (algebraTransport Φ h P).pullback g = algebraTransport Φ h (P.pullback g) :=
  Quadruple.ext rfl fun i => heq_of_eq
    (Twisting.algebraTransport_pullbackApp_eq Φ P.twisting g i)

end Quadruple

/-! ### The sets `F_d(T)`, transported -/

namespace Fd

variable {A B : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X.toRingedSpace)}
  (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B) (h : ∀ n : ℤ, IsIso (Φ.app n)) (d : ℤ)

/-- **The map `F_d(T)` for `ℬ` to `F_d(T)` for `𝒜`** along a unital homomorphism: the class of a
quadruple is sent to the class of its transport, which is well defined because the transport
matches strict equivalence (`Quadruple.strictlyEquivalent_algebraTransport_iff`). -/
def algebraTransport {T : Scheme.{u}} (ξ : Fd B d T) : Fd A d T :=
  ⟨ξ.1,
    Quotient.map (fun P : Quadruple ξ.1 B d => Quadruple.algebraTransport Φ h P)
      (fun _ _ hPQ => (Quadruple.strictlyEquivalent_algebraTransport_iff Φ h).mpr hPQ) ξ.2⟩

/-- The morphism to the base recorded by a class is unchanged by the transport. -/
@[simp] theorem algebraTransport_fst {T : Scheme.{u}} (ξ : Fd B d T) :
    (algebraTransport Φ h d ξ).1 = ξ.1 := rfl

/-- The transport sends the class of a quadruple to the class of its transport. -/
@[simp] theorem algebraTransport_mk {T : Scheme.{u}} (f : T ⟶ X) (P : Quadruple f B d) :
    algebraTransport Φ h d (Fd.mk f P) = Fd.mk f (Quadruple.algebraTransport Φ h P) := rfl

/-- **The sets `F_d(T)` for `𝒜` and for `ℬ` correspond bijectively** along a unital homomorphism
`Φ : 𝒜 ⟶ ℬ` all of whose components are isomorphisms. -/
def algebraTransportEquiv (T : Scheme.{u}) : Fd B d T ≃ Fd A d T where
  toFun ξ := algebraTransport Φ h d ξ
  invFun ξ :=
    algebraTransport (unitalHomInverse Φ h) (isIso_unitalHomInverse_app Φ h) d ξ
  left_inv ξ := by
    obtain ⟨f, q⟩ := ξ
    induction q using Quotient.ind with
    | _ P =>
      exact congrArg (Fd.mk f)
        (Quadruple.algebraTransport_inverse_algebraTransport Φ h P)
  right_inv ξ := by
    obtain ⟨f, q⟩ := ξ
    induction q using Quotient.ind with
    | _ P =>
      exact congrArg (Fd.mk f)
        (Quadruple.algebraTransport_algebraTransport_inverse Φ h P)

/-- The bijection is `Fd.algebraTransport` on an element. -/
@[simp] theorem algebraTransportEquiv_apply (T : Scheme.{u}) (ξ : Fd B d T) :
    algebraTransportEquiv Φ h d T ξ = algebraTransport Φ h d ξ := rfl

/-- **The bijection of the sets `F_d(T)` commutes with the pullback along a morphism of test
schemes**, so it is natural in the test scheme. -/
theorem algebraTransport_pullback {T T' : Scheme.{u}} (g : T' ⟶ T) (ξ : Fd B d T) :
    algebraTransport Φ h d (Fd.pullback g ξ) = Fd.pullback g (algebraTransport Φ h d ξ) := by
  obtain ⟨f, q⟩ := ξ
  induction q using Quotient.ind with
  | _ P => exact (congrArg (Fd.mk (g ≫ f))
      (Quadruple.algebraTransport_pullback Φ h P g)).symm

end Fd

/-! ### The instance the chart-wise argument needs -/

section RestrictPullback

variable (A : SheafGradedAlgebra S) (f : X ⟶ S) [IsOpenImmersion f] (d : ℤ)

/-- Every component of the comparison of the two spellings of the restriction is an isomorphism,
as a family. This is `...RelativeProjQcohSheaf.isIso_restrictPullbackUnitalHom_app`. -/
theorem isIso_restrictPullbackUnitalHom_app_forall (n : ℤ) :
    IsIso ((restrictPullbackUnitalHom A f).app n) :=
  isIso_restrictPullbackUnitalHom_app A f n

/-- **The bijection between the two spellings of `F_d(T)` over an open subscheme of the base**:
the set of strict equivalence classes of quadruples for the *restriction* `A|_X` is in bijection
with the set of classes for the *inverse image* `f^*A`, which is the spelling the base change of
Tag 01NT produces.

The two spellings of the algebra are isomorphic as sheaves of graded algebras — each component
of `...RelativeProjQcohSheaf.restrictPullbackUnitalHom` is an isomorphism, and it carries the
multiplication to the multiplication and the unit to the unit — and a quadruple depends on the
algebra only through `ψ` and its two conditions. -/
def Fd.restrictPullbackEquiv (T : Scheme.{u}) :
    Fd (situationAlgebra (A.restrict f)) d T ≃ Fd (baseAlgebra f (situationAlgebra A)) d T :=
  Fd.algebraTransportEquiv (restrictPullbackUnitalHom A f)
    (isIso_restrictPullbackUnitalHom_app_forall A f) d T

/-- The bijection between the two spellings of `F_d(T)` is natural in the test scheme. -/
theorem Fd.restrictPullbackEquiv_pullback {T T' : Scheme.{u}} (g : T' ⟶ T)
    (ξ : Fd (situationAlgebra (A.restrict f)) d T) :
    Fd.restrictPullbackEquiv A f d T' (Fd.pullback g ξ) =
      Fd.pullback g (Fd.restrictPullbackEquiv A f d T ξ) :=
  Fd.algebraTransport_pullback (restrictPullbackUnitalHom A f)
    (isIso_restrictPullbackUnitalHom_app_forall A f) d g ξ

/-- The same bijection with the inverse-image spelling as its source, which is the direction the
base change of Tag 01NT hands over: a point of `F_d(T)` for `f^*A` is a point of `F_d(T)` for
`A|_X`, whose projective spectrum is the chart. -/
def Fd.pullbackRestrictEquiv (T : Scheme.{u}) :
    Fd (baseAlgebra f (situationAlgebra A)) d T ≃ Fd (situationAlgebra (A.restrict f)) d T :=
  (Fd.restrictPullbackEquiv A f d T).symm

end RestrictPullback

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
