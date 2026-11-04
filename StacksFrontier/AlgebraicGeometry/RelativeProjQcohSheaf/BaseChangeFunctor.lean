module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStrictUnit
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.BaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.OverBase

/-!
# Base change for the relative Proj functor: the isomorphism `F'_d ≅ h_{S'} ×_{h_S} F_d`

Let `S` be a scheme and `𝒜` a graded `𝒪_S`-algebra (Situation 01NN), fix an integer `d`, and let
`F_d : Sch^{opp} ⟶ Sets` be the functor of strict equivalence classes of quadruples of
Section 01NS. For a morphism of base schemes `g : S' ⟶ S` put `𝒜' = g^*𝒜`
(`...RelativeProjQcohSheaf.baseAlgebra`) and let `F'_d` be the functor of `(S', 𝒜')`. Tag 01NT
asserts a canonical isomorphism

`F'_d ≅ h_{S'} ×_{h_S} F_d`

of functors on `Sch^{opp}`. This file constructs it, in the form: the functor `F'_d`, together
with its projection to the functor of points of `S'` and the canonical map `F'_d ⟹ F_d`, is a
**limit** of the cospan `h_{S'} ⟶ h_S ⟵ F_d`.

The mathematical content is a bijection between quadruples. A quadruple
`(d, f' : T → S', L, ψ')` for `(S', 𝒜')` and a quadruple `(d, g ∘ f', L, ψ)` for `(S, 𝒜)` carry
the same data, because the invertible module `L` and its Laurent algebra live on the test scheme
`T`, which base change does not move, and because

`(f')^*(𝒜')^{(d)} = (f')^*g^*(𝒜^{(d)}) = f^*𝒜^{(d)}`,   `f = g ∘ f'`,

which is the canonical identification `...RelativeProjQcohSheaf.veroneseBaseChangeIso` of
`...RelativeProjQcohSheaf.BaseChange`. Carrying `ψ` across that identification preserves
multiplicativity and the unit normalisation — `Quadruple.baseChangeEquiv` below — and strict
equivalence, so the bijection descends to the sets `F_d(T)`. Recording a quadruple for `(S, 𝒜)`
over `T` *together with* a factorization of its structure morphism through `S'` is exactly a
point of `h_{S'} ×_{h_S} F_d`, which is what makes the bijection the asserted isomorphism.

Two identifications of the multiplication and unit of `𝒜' = g^*𝒜` are what the construction
needed and what the implementation notes of `...RelativeProjQcohSheaf.BaseChange` recorded as
missing: `baseMul_eq` and `baseOne_eq` below.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.baseChangeEquiv`: **the bijection
  between the quadruples over `f' : T ⟶ S'` for `(S', 𝒜')` and the quadruples over `g ∘ f'` for
  `(S, 𝒜)`**, together with its two halves `Quadruple.baseChangeUp` and
  `Quadruple.baseChangeDown`, and the corresponding bijection `Twisting.baseChangeEquiv` of the
  maps `ψ` alone.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.baseChangeNat`: **the canonical natural
  transformation `F'_d ⟹ F_d`**, the map of functors over `g`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.yonedaBaseMap`: the map `h_{S'} ⟹ h_S` of
  functors of points induced by `g`, lifted to `Type (u+1)` as the projections of `F_d` are.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.baseFibre`: the fibre product
  `h_{S'} ×_{h_S} F_d` written out, as the functor sending a test scheme `T` to the pairs
  `(f' : T ⟶ S', ξ ∈ F_d(T))` with `g ∘ f'` the structure morphism of `ξ`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.baseChangePullbackIso`: **the canonical
  isomorphism `F'_d ≅ h_{S'} ×_{h_S} F_d` of Tag 01NT**, at the categorical pullback.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.isLimitBaseChangeCone`: **`F'_d`, with its
  projection to `h_{S'}` and the canonical map to `F_d`, is a limit of the cospan
  `h_{S'} ⟶ h_S ⟵ F_d`** — i.e. `F'_d` *is* the fibre product `h_{S'} ×_{h_S} F_d`, the
  comparison being the canonical one.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.baseChangePullbackIso_hom_fst` and
  `..._hom_snd`: the isomorphism is compatible with both projections, so it is the canonical one
  and not merely some isomorphism.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.baseMul_eq` and `baseOne_eq`: **the
  multiplication and the unit of `𝒜' = g^*𝒜` are the pullbacks of those of `𝒜`, read through the
  comparison of Tag 01CD** and through the structure-sheaf comparison.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.baseChangeUp_pullback`: the bijection
  on quadruples **commutes with the pullback along a morphism of test schemes**, which is the
  naturality of the isomorphism in the test scheme.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.strictlyEquivalent_baseChangeUp_iff`:
  the bijection on quadruples matches strict equivalence on the two sides exactly.

## Implementation notes

The degree `d` is an arbitrary integer, as everywhere in this directory; the source takes
`d ≥ 1`, and nothing below uses positivity.

`𝒜' = g^*𝒜` is taken literally, as `baseAlgebra g 𝒜`: no comparison of `𝒜'` with `g^*𝒜` is
assumed anywhere, and no quasi-coherence of `𝒜` is used.

The identification of the degreewise components of `ψ` is written with
`...RelativeProjQcohSheaf.compComparison`, the ascribed spelling of the contraction of an
iterated pullback, rather than with `veroneseBaseChangeIso` itself; the two are the same morphism
(`veroneseBaseChangeIso_hom`), and the ascribed spelling is the one the existing naturality,
associativity, tensor and unit coherences of that contraction are stated at, so that `rw` applies
to a goal containing it.

The value of `Fd.baseFibre` is the **subtype** of a product rather than a dependent sum over the
morphisms `T ⟶ S'`; with the subtype the universal property of the fibre product needs no
transport of a quotient along an equality of morphisms of schemes, and the one transport the
comparison does need is confined to `Fd.baseFibreEquiv`.

The projections of `F_d` land in `yoneda.obj S ⋙ CategoryTheory.uliftFunctor`, not in
`yoneda.obj S`, because the sets `F_d(T)` live one universe above `Hom(T, S)`; the lift is the
identity on elements, as recorded at `...RelativeProjQcohSheaf.Fd.toBase`, and `yonedaBaseMap`
is the map of base schemes lifted the same way.

## Not done here

* The source's `F = ⋃_{d ≥ 1} F_d` is not treated: Tag 01NT is a statement about `F_d` at a
  fixed degree, and the corresponding statement for `F` would need the base-change bijection to
  respect the identifications across degrees as well.
* Representability of `F_d` by a scheme (Tag 01NV) is not proved, so this is a statement about
  functors and not about a fibre product of schemes.

## References

* [Stacks Project, Tag 01NT](https://stacks.math.columbia.edu/tag/01NT)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite

open AlgebraicGeometry Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.SheafOfModules.TensorPower

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {S S' T T₂ : Scheme.{u}}

/-! ### Extensionality for the map `ψ` and for a quadruple -/

/-- **Two maps `ψ` of quadruples with the same homogeneous components are equal.** The remaining
two fields of `...RelativeProjQcohSheaf.Twisting` are propositions. -/
theorem Twisting.ext {f : T ⟶ S}
    {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}
    {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
    {ψ χ : Twisting f A d L} (h : ∀ i : ℤ, ψ.app i = χ.app i) : ψ = χ := by
  have hfun : ψ.app = χ.app := funext h
  obtain ⟨a, ma, oa⟩ := ψ
  obtain ⟨b, mb, ob⟩ := χ
  subst hfun
  rfl

/-- **Two quadruples with the same invertible module and the same homogeneous components of `ψ`
are equal.** The invertibility of the module and the surjectivity of the degree-one component are
propositions; the components of `ψ` are compared by `HEq` because their type depends on the
invertible module. -/
theorem Quadruple.ext {f : T ⟶ S}
    {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}
    {P Q : Quadruple f A d} (hL : P.L = Q.L)
    (h : ∀ i : ℤ, HEq (P.twisting.app i) (Q.twisting.app i)) : P = Q := by
  obtain ⟨L, hiP, ψ, heP⟩ := P
  obtain ⟨L', hiQ, χ, heQ⟩ := Q
  obtain rfl : L = L' := hL
  obtain rfl : ψ = χ := Twisting.ext fun i => eq_of_heq (h i)
  rfl

/-! ### The multiplication and the unit of the base-changed algebra -/

/-- The multiplication of `𝒜' = g^*𝒜` in degrees `i` and `j`, as a morphism out of the tensor
product of the two pulled-back pieces. This is
`SheafOfModules.GradedAlgebra.mulSheaf (baseAlgebra g 𝒜) i j` with its source and target ascribed
at the pullback spelling. -/
def baseMul (g : S' ⟶ S)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) (i j : ℤ) :
    (pullbackFunctor (ringedSpaceHom g)).obj (A.piece i) ⊗
        (pullbackFunctor (ringedSpaceHom g)).obj (A.piece j) ⟶
      (pullbackFunctor (ringedSpaceHom g)).obj (A.piece (i + j)) :=
  (baseAlgebra g A).mulSheaf i j

/-- The global unit of `𝒜' = g^*𝒜`, as a morphism out of the unit object. This is
`SheafOfModules.GradedAlgebra.oneHom (baseAlgebra g 𝒜)` with its target ascribed at the pullback
spelling. -/
def baseOne (g : S' ⟶ S)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) :
    𝟙_ (SheafOfModules.{u} (structureRingSheaf S'.toRingedSpace)) ⟶
      (pullbackFunctor (ringedSpaceHom g)).obj (A.piece 0) :=
  SheafOfModules.GradedAlgebra.oneHom (baseAlgebra g A)

/-- **The multiplication of `𝒜' = g^*𝒜` is the pullback of the multiplication of `𝒜`, read
through the comparison of Tag 01CD.** Both sides are morphisms out of the pullback of a tensor
product, hence determined by their values on the pullback-unit images of the local pure tensors,
where the left side is the pulled-back multiplication of
`Stacks.RingedSpace.pullbackGradedAlgebra_mul_pullbackUnit` and the right side the pullback-unit
image of the product. -/
theorem baseMul_eq (g : S' ⟶ S)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) (i j : ℤ) :
    pullbackTensorComparison (ringedSpaceHom g) (A.piece i) (A.piece j) ≫ baseMul g A i j =
      (pullbackFunctor (ringedSpaceHom g)).map
        (SheafOfModules.GradedAlgebra.mulSheaf A i j) := by
  refine pullback_tensor_hom_ext (ringedSpaceHom g) fun U a b => ?_
  have e1 := pullbackTensorComparison_pullbackUnit (ringedSpaceHom g) (A.piece i) (A.piece j) U a b
  have e2 := mulHom_tmul (baseAlgebra g A) i j
    ((RingedSpaceModuleAdjunction.opensMap (ringedSpaceHom g)).op.obj U)
    (pullbackUnit (ringedSpaceHom g) (A.piece i) U a)
    (pullbackUnit (ringedSpaceHom g) (A.piece j) U b)
  have e3 := pullbackBilinear_pullbackUnit (ringedSpaceHom g) (A.mul i j) U a b
  have e4 := mulHom_tmul A i j U a b
  have e5 := pullbackUnit_naturality (ringedSpaceHom g) (A.mulSheaf i j) U
    (tmul S.toRingedSpace (A.piece i) (A.piece j) U a b)
  exact ((congrArg ((baseMul g A i j).val.app
        ((RingedSpaceModuleAdjunction.opensMap (ringedSpaceHom g)).op.obj U)) e1).trans
      (e2.trans e3)).trans
    ((congrArg (pullbackUnit (ringedSpaceHom g) (A.piece (i + j)) U) e4).symm.trans e5.symm)

/-- **The unit of `𝒜' = g^*𝒜` is the pullback of the unit of `𝒜`, read through the
structure-sheaf comparison of Tag 01CD.** Both sides are morphisms out of a pullback, hence
determined on the pullback-unit images of the local sections of the structure sheaf, where the
semilinearity `Stacks.RingedSpace.pullbackUnit_smul` of the pullback unit matches the two
scalars. -/
theorem baseOne_eq (g : S' ⟶ S)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) :
    pullbackUnitComparison (ringedSpaceHom g) ≫ baseOne g A =
      (pullbackFunctor (ringedSpaceHom g)).map
        (SheafOfModules.GradedAlgebra.oneHom A) := by
  refine pullback_hom_ext (ringedSpaceHom g) fun U r => ?_
  obtain ⟨V⟩ := U
  have e1 := pullbackUnitComparison_pullbackUnit (ringedSpaceHom g) (op V) r
  have e2 := SheafOfModules.GradedAlgebra.oneHom_val_app (baseAlgebra g A)
    ((RingedSpaceModuleAdjunction.opensMap (ringedSpaceHom g)).op.obj (op V))
    (sharp (ringedSpaceHom g) (op V) r)
  have e3 := pullbackGradedAlgebra_one_eval (ringedSpaceHom g) A V
  have e4 := pullbackUnit_naturality (ringedSpaceHom g)
    (SheafOfModules.GradedAlgebra.oneHom A) (op V) r
  have e5 := SheafOfModules.GradedAlgebra.oneHom_val_app A (op V) r
  have e6 := pullbackUnit_smul (ringedSpaceHom g) (A.piece 0) (op V) r (A.one.eval (op V))
  exact ((congrArg ((baseOne g A).val.app
        ((RingedSpaceModuleAdjunction.opensMap (ringedSpaceHom g)).op.obj (op V))) e1).trans
      (e2.trans (congrArg (fun z => sharp (ringedSpaceHom g) (op V) r • z) e3))).trans
    ((e6.symm.trans (congrArg (pullbackUnit (ringedSpaceHom g) (A.piece 0) (op V)) e5.symm)).trans
      e4.symm)

/-! ### The canonical identification at the ascribed spelling -/

/-- The canonical identification `f^*𝒜^{(d)}_n ≅ (f')^*(𝒜')^{(d)}_n` of Tag 01NT is the
contraction of the iterated pullback, at the ascribed spelling at which its naturality and its
tensor, unit and associativity coherences are stated. -/
theorem veroneseBaseChangeIso_hom (g : S' ⟶ S) (f' : T ⟶ S')
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) (d n : ℤ) :
    (veroneseBaseChangeIso g f' A d n).hom = compComparison f' g (A.piece (n * d)) := rfl

/-- The inverse of the canonical identification of Tag 01NT, at the ascribed spelling. -/
theorem veroneseBaseChangeIso_inv (g : S' ⟶ S) (f' : T ⟶ S')
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) (d n : ℤ) :
    (veroneseBaseChangeIso g f' A d n).inv = inv (compComparison f' g (A.piece (n * d))) := rfl

/-! ### Base change of the map `ψ` of a quadruple -/

section Twist

variable (g : S' ⟶ S) (f' : T ⟶ S')
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) (d : ℤ)
  {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]

/-- **The canonical identification of Tag 01NT carries the multiplication of
`(f')^*(𝒜')^{(d)}` to the multiplication of `f^*𝒜^{(d)}`**, where `f = g ∘ f'`. The
multiplication of `(f')^*(𝒜')^{(d)}` enters as an arbitrary morphism `m` subject to the
hypothesis that it be the pullback along `g` of the multiplication of `𝒜^{(d)}`, which is what
`baseMul_eq` supplies.

The proof composes the compatibility `compComparison_tensor` of the contraction with the
comparison of Tag 01CD with the naturality `compComparison_naturality` of the contraction. -/
theorem baseChange_key (i j : ℤ)
    (m : (pullbackFunctor (ringedSpaceHom g)).obj (A.piece (i * d)) ⊗
          (pullbackFunctor (ringedSpaceHom g)).obj (A.piece (j * d)) ⟶
        (pullbackFunctor (ringedSpaceHom g)).obj (A.piece ((i + j) * d)))
    (hm : pullbackTensorComparison (ringedSpaceHom g) (A.piece (i * d)) (A.piece (j * d)) ≫ m =
      (pullbackFunctor (ringedSpaceHom g)).map
        (A.mulSheaf (i * d) (j * d) ≫
          eqToHom (congrArg A.piece (by ring : i * d + j * d = (i + j) * d)))) :
    pullbackTensorComparison (ringedSpaceHom (f' ≫ g)) (A.piece (i * d)) (A.piece (j * d)) ≫
        (compComparison f' g (A.piece (i * d)) ⊗ₘ compComparison f' g (A.piece (j * d))) ≫
          inv (pullbackTensorComparison (ringedSpaceHom f')
              ((pullbackFunctor (ringedSpaceHom g)).obj (A.piece (i * d)))
              ((pullbackFunctor (ringedSpaceHom g)).obj (A.piece (j * d)))) ≫
            (pullbackFunctor (ringedSpaceHom f')).map m =
      (pullbackFunctor (ringedSpaceHom (f' ≫ g))).map
          (A.mulSheaf (i * d) (j * d) ≫
            eqToHom (congrArg A.piece (by ring : i * d + j * d = (i + j) * d))) ≫
        compComparison f' g (A.piece ((i + j) * d)) := by
  slice_lhs 1 2 => rw [← compComparison_tensor f' g (A.piece (i * d)) (A.piece (j * d))]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  slice_lhs 2 3 => rw [← CategoryTheory.Functor.map_comp]
  rw [hm]
  exact compComparison_naturality f' g _

/-- **Multiplicativity in bidegree `(i, j)` is the same condition on the two sides of the base
change.** A degreewise family `b` of maps out of `(f')^*(𝒜')^{(d)}` into the Laurent algebra of
`L` is multiplicative for `(S', 𝒜')` exactly when the family obtained from it by precomposing
with the canonical identification of Tag 01NT is multiplicative for `(S, 𝒜)` over `g ∘ f'`.

Both equations have the same left-hand side up to composition with the isomorphism
`θ_i ⊗ θ_j` of the identifications, and `baseChange_key` says their right-hand sides differ by
the same isomorphism. -/
theorem baseChange_app_mul_iff (i j : ℤ)
    (m : (pullbackFunctor (ringedSpaceHom g)).obj (A.piece (i * d)) ⊗
          (pullbackFunctor (ringedSpaceHom g)).obj (A.piece (j * d)) ⟶
        (pullbackFunctor (ringedSpaceHom g)).obj (A.piece ((i + j) * d)))
    (hm : pullbackTensorComparison (ringedSpaceHom g) (A.piece (i * d)) (A.piece (j * d)) ≫ m =
      (pullbackFunctor (ringedSpaceHom g)).map
        (A.mulSheaf (i * d) (j * d) ≫
          eqToHom (congrArg A.piece (by ring : i * d + j * d = (i + j) * d))))
    (b : ∀ n : ℤ, (pullbackFunctor (ringedSpaceHom f')).obj
        ((pullbackFunctor (ringedSpaceHom g)).obj (A.piece (n * d))) ⟶ (laurent L).piece n) :
    ((b i ⊗ₘ b j) ≫ laurentMul L i j =
        inv (pullbackTensorComparison (ringedSpaceHom f')
            ((pullbackFunctor (ringedSpaceHom g)).obj (A.piece (i * d)))
            ((pullbackFunctor (ringedSpaceHom g)).obj (A.piece (j * d)))) ≫
          (pullbackFunctor (ringedSpaceHom f')).map m ≫ b (i + j)) ↔
      (((compComparison f' g (A.piece (i * d)) ≫ b i) ⊗ₘ
            (compComparison f' g (A.piece (j * d)) ≫ b j)) ≫ laurentMul L i j =
        inv (pullbackTensorComparison (ringedSpaceHom (f' ≫ g)) (A.piece (i * d))
            (A.piece (j * d))) ≫
          (pullbackFunctor (ringedSpaceHom (f' ≫ g))).map
              (A.mulSheaf (i * d) (j * d) ≫
                eqToHom (congrArg A.piece (by ring : i * d + j * d = (i + j) * d))) ≫
            compComparison f' g (A.piece ((i + j) * d)) ≫ b (i + j)) := by
  have hRHS : (compComparison f' g (A.piece (i * d)) ⊗ₘ compComparison f' g (A.piece (j * d))) ≫
        inv (pullbackTensorComparison (ringedSpaceHom f')
            ((pullbackFunctor (ringedSpaceHom g)).obj (A.piece (i * d)))
            ((pullbackFunctor (ringedSpaceHom g)).obj (A.piece (j * d)))) ≫
          (pullbackFunctor (ringedSpaceHom f')).map m =
      inv (pullbackTensorComparison (ringedSpaceHom (f' ≫ g)) (A.piece (i * d))
          (A.piece (j * d))) ≫
        (pullbackFunctor (ringedSpaceHom (f' ≫ g))).map
            (A.mulSheaf (i * d) (j * d) ≫
              eqToHom (congrArg A.piece (by ring : i * d + j * d = (i + j) * d))) ≫
          compComparison f' g (A.piece ((i + j) * d)) := by
    rw [IsIso.eq_inv_comp]
    exact baseChange_key g f' A d i j m hm
  rw [← MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Category.assoc]
  rw [← reassoc_of% hRHS]
  exact (Iso.cancel_iso_hom_left
    (tensorIso (asIso (compComparison f' g (A.piece (i * d))))
      (asIso (compComparison f' g (A.piece (j * d))))) _ _).symm

/-- A functor carries `u ≫ eqToHom e` to a composite through any factorization of `F.map u`. -/
private theorem map_comp_eqToHom_of_map_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y Z : C} (u : X ⟶ Y) (e : Y = Z) {V : D} {c : F.obj X ⟶ V} {w : V ⟶ F.obj Y}
    (h : F.map u = c ≫ w) : F.map (u ≫ eqToHom e) = c ≫ w ≫ F.map (eqToHom e) := by
  rw [F.map_comp, h, Category.assoc]

/-- **The unit of `𝒜'` in the degree the unit normalisation of a map `ψ` uses**: the pullback
along `g` of the unit of `𝒜^{(d)}` in degree zero is the structure-sheaf comparison followed by
the unit of `(𝒜')^{(d)}`. This is `baseOne_eq` with the degree bookkeeping `0 = 0 · d` carried
across the pullback. -/
theorem baseChange_oneHom_gamma :
    (pullbackFunctor (ringedSpaceHom g)).map
        (SheafOfModules.GradedAlgebra.oneHom A ≫
          eqToHom (congrArg A.piece (by ring : (0 : ℤ) = 0 * d))) =
      pullbackUnitComparison (ringedSpaceHom g) ≫
        (SheafOfModules.GradedAlgebra.oneHom (baseAlgebra g A) ≫
          eqToHom (congrArg (baseAlgebra g A).piece (by ring : (0 : ℤ) = 0 * d))) := by
  rw [map_comp_eqToHom_of_map_eq _ _ _ (baseOne_eq g A).symm, eqToHom_map]
  rfl

/-- **The canonical identification of Tag 01NT carries the unit normalisation of a map `ψ` for
`(S, 𝒜)` to the unit normalisation for `(S', 𝒜')`**: the global unit of `f^*𝒜^{(d)}` in degree
zero, followed by the identification, is the global unit of `(f')^*(𝒜')^{(d)}` in degree zero.

The proof cancels the structure-sheaf comparison of `g ∘ f'`, which is an isomorphism, and then
composes the formula `Stacks.PullbackStrictUnit.pullbackUnitComparison_comp_pullbackOne` for the
global unit of a pulled-back algebra with the naturality and the unit coherence
`compComparison_unit` of the contraction of an iterated pullback, together with
`baseChange_oneHom_gamma`. -/
theorem baseChange_pullbackOne :
    Stacks.PullbackGradedAlgebra.pullbackOne (ringedSpaceHom (f' ≫ g)) A ≫
        (pullbackFunctor (ringedSpaceHom (f' ≫ g))).map
            (eqToHom (congrArg A.piece (by ring : (0 : ℤ) = 0 * d))) ≫
          compComparison f' g (A.piece (0 * d)) =
      Stacks.PullbackGradedAlgebra.pullbackOne (ringedSpaceHom f') (baseAlgebra g A) ≫
        (pullbackFunctor (ringedSpaceHom f')).map
          (eqToHom (congrArg (baseAlgebra g A).piece (by ring : (0 : ℤ) = 0 * d))) := by
  refine (cancel_epi (pullbackUnitComparison (ringedSpaceHom (f' ≫ g)))).mp ?_
  have hinner2 : (pullbackFunctor (ringedSpaceHom f')).map
        (SheafOfModules.GradedAlgebra.oneHom (baseAlgebra g A) ≫
          eqToHom (congrArg (baseAlgebra g A).piece (by ring : (0 : ℤ) = 0 * d))) =
      pullbackUnitComparison (ringedSpaceHom f') ≫
        (Stacks.PullbackGradedAlgebra.pullbackOne (ringedSpaceHom f') (baseAlgebra g A) ≫
          (pullbackFunctor (ringedSpaceHom f')).map
            (eqToHom (congrArg (baseAlgebra g A).piece (by ring : (0 : ℤ) = 0 * d)))) :=
    map_comp_eqToHom_of_map_eq _ _ _
      (Stacks.PullbackStrictUnit.pullbackUnitComparison_comp_pullbackOne
        (ringedSpaceHom f') (baseAlgebra g A)).symm
  refine (Category.assoc _ _ _).symm.trans ?_
  refine Eq.trans (congrArg (fun z => z ≫ ((pullbackFunctor (ringedSpaceHom (f' ≫ g))).map
      (eqToHom (congrArg A.piece (by ring : (0 : ℤ) = 0 * d))) ≫
        compComparison f' g (A.piece (0 * d))))
    (Stacks.PullbackStrictUnit.pullbackUnitComparison_comp_pullbackOne
      (ringedSpaceHom (f' ≫ g)) A)) ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine Eq.trans (congrArg (fun z => z ≫ compComparison f' g (A.piece (0 * d)))
    (CategoryTheory.Functor.map_comp (pullbackFunctor (ringedSpaceHom (f' ≫ g)))
      (SheafOfModules.GradedAlgebra.oneHom A)
      (eqToHom (congrArg A.piece (by ring : (0 : ℤ) = 0 * d)))).symm) ?_
  refine Eq.trans (compComparison_naturality f' g
    (SheafOfModules.GradedAlgebra.oneHom A ≫
      eqToHom (congrArg A.piece (by ring : (0 : ℤ) = 0 * d)))).symm ?_
  refine Eq.trans (congrArg (fun z => compComparison f' g
      (𝟙_ (SheafOfModules.{u} (structureRingSheaf S.toRingedSpace))) ≫
    (pullbackFunctor (ringedSpaceHom f')).map z) (baseChange_oneHom_gamma g A d)) ?_
  refine Eq.trans (congrArg (fun z => compComparison f' g
      (𝟙_ (SheafOfModules.{u} (structureRingSheaf S.toRingedSpace))) ≫ z)
    (CategoryTheory.Functor.map_comp (pullbackFunctor (ringedSpaceHom f'))
      (pullbackUnitComparison (ringedSpaceHom g))
      (SheafOfModules.GradedAlgebra.oneHom (baseAlgebra g A) ≫
        eqToHom (congrArg (baseAlgebra g A).piece (by ring : (0 : ℤ) = 0 * d))))) ?_
  refine Eq.trans (congrArg (fun z => compComparison f' g
      (𝟙_ (SheafOfModules.{u} (structureRingSheaf S.toRingedSpace))) ≫
    (pullbackFunctor (ringedSpaceHom f')).map (pullbackUnitComparison (ringedSpaceHom g)) ≫ z)
    hinner2) ?_
  refine Eq.trans ?_ (congrArg (fun z => z ≫
      (Stacks.PullbackGradedAlgebra.pullbackOne (ringedSpaceHom f') (baseAlgebra g A) ≫
        (pullbackFunctor (ringedSpaceHom f')).map
          (eqToHom (congrArg (baseAlgebra g A).piece (by ring : (0 : ℤ) = 0 * d)))))
    (compComparison_unit f' g))
  exact ((Category.assoc _ _ _).trans (congrArg (fun z => compComparison f' g
      (𝟙_ (SheafOfModules.{u} (structureRingSheaf S.toRingedSpace))) ≫ z)
    (Category.assoc _ _ _))).symm

namespace Twisting

/-- The degree-`i` component of the map `ψ` for `(S, 𝒜)` over `g ∘ f'` obtained from a map `ψ'`
for `(S', 𝒜')` over `f'`: precomposition with the canonical identification of Tag 01NT. -/
def baseChangeUpApp (χ : Twisting f' (baseAlgebra g A) d L) (i : ℤ) :
    (pullbackFunctor (ringedSpaceHom (f' ≫ g))).obj (A.piece (i * d)) ⟶ (laurent L).piece i :=
  compComparison f' g (A.piece (i * d)) ≫ χ.app i

/-- The degree-`i` component of the map `ψ'` for `(S', 𝒜')` over `f'` obtained from a map `ψ` for
`(S, 𝒜)` over `g ∘ f'`: precomposition with the inverse of the canonical identification of
Tag 01NT. -/
def baseChangeDownApp (ψ : Twisting (f' ≫ g) A d L) (i : ℤ) :
    (pullbackFunctor (ringedSpaceHom f')).obj
        ((pullbackFunctor (ringedSpaceHom g)).obj (A.piece (i * d))) ⟶ (laurent L).piece i :=
  inv (compComparison f' g (A.piece (i * d))) ≫ ψ.app i

/-- **The map `ψ'` of a quadruple for the base-changed situation `(S', 𝒜')`, read as a map `ψ`
for `(S, 𝒜)` over the composite `g ∘ f'`.** The components are carried across the canonical
identification of Tag 01NT; multiplicativity is `baseChange_app_mul_iff` and the unit
normalisation is `baseChange_pullbackOne`. -/
def baseChangeUp (χ : Twisting f' (baseAlgebra g A) d L) :
    Twisting (f' ≫ g) A d L where
  app i := baseChangeUpApp g f' A d χ i
  app_mul i j := by
    rw [laurent_mulSheaf_eq]
    refine (baseChange_app_mul_iff g f' A d i j
      (baseMul g A (i * d) (j * d) ≫
        eqToHom (congrArg (baseAlgebra g A).piece
          (by ring : i * d + j * d = (i + j) * d))) ?_ (fun n => χ.app n)).mp ?_
    · rw [← Category.assoc, baseMul_eq]
      exact (((pullbackFunctor (ringedSpaceHom g)).map_comp
            (A.mulSheaf (i * d) (j * d))
            (eqToHom (congrArg A.piece (by ring : i * d + j * d = (i + j) * d)))).trans
          (congrArg (fun z => (pullbackFunctor (ringedSpaceHom g)).map
                (A.mulSheaf (i * d) (j * d)) ≫ z)
            (eqToHom_map (pullbackFunctor (ringedSpaceHom g))
              (congrArg A.piece (by ring : i * d + j * d = (i + j) * d))))).symm
    · have h := χ.app_mul i j
      rw [laurent_mulSheaf_eq] at h
      exact h
  app_one :=
    (congrArg (fun z => Stacks.PullbackGradedAlgebra.pullbackOne (ringedSpaceHom (f' ≫ g)) A ≫ z)
        (Category.assoc _ _ _).symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ χ.app 0) (baseChange_pullbackOne g f' A d)).trans
          ((Category.assoc _ _ _).trans χ.app_one)))

/-- The components of the base-changed map are precomposition with the canonical identification
of Tag 01NT. -/
@[simp] theorem baseChangeUp_app (χ : Twisting f' (baseAlgebra g A) d L) (i : ℤ) :
    (χ.baseChangeUp g f' A d).app i = compComparison f' g (A.piece (i * d)) ≫ χ.app i := rfl

/-- **The map `ψ` of a quadruple for `(S, 𝒜)` over a morphism factoring through `S'`, read as a
map `ψ'` for the base-changed situation `(S', 𝒜')`.** This is the inverse construction to
`Twisting.baseChangeUp`. -/
def baseChangeDown (ψ : Twisting (f' ≫ g) A d L) :
    Twisting f' (baseAlgebra g A) d L where
  app i := baseChangeDownApp g f' A d ψ i
  app_mul i j := by
    rw [laurent_mulSheaf_eq]
    refine (baseChange_app_mul_iff g f' A d i j
      (baseMul g A (i * d) (j * d) ≫
        eqToHom (congrArg (baseAlgebra g A).piece
          (by ring : i * d + j * d = (i + j) * d))) ?_
      (fun n => baseChangeDownApp g f' A d ψ n)).mpr ?_
    · rw [← Category.assoc, baseMul_eq]
      exact (((pullbackFunctor (ringedSpaceHom g)).map_comp
            (A.mulSheaf (i * d) (j * d))
            (eqToHom (congrArg A.piece (by ring : i * d + j * d = (i + j) * d)))).trans
          (congrArg (fun z => (pullbackFunctor (ringedSpaceHom g)).map
                (A.mulSheaf (i * d) (j * d)) ≫ z)
            (eqToHom_map (pullbackFunctor (ringedSpaceHom g))
              (congrArg A.piece (by ring : i * d + j * d = (i + j) * d))))).symm
    · have h := ψ.app_mul i j
      rw [laurent_mulSheaf_eq] at h
      simp only [baseChangeDownApp, IsIso.hom_inv_id_assoc]
      exact h
  app_one :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ baseChangeDownApp g f' A d ψ 0)
          (baseChange_pullbackOne g f' A d).symm).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun z => Stacks.PullbackGradedAlgebra.pullbackOne
                (ringedSpaceHom (f' ≫ g)) A ≫ z)
              ((Category.assoc _ _ _).trans
                (congrArg (fun z => (pullbackFunctor (ringedSpaceHom (f' ≫ g))).map
                    (eqToHom (congrArg A.piece (by ring : (0 : ℤ) = 0 * d))) ≫ z)
                  (IsIso.hom_inv_id_assoc (compComparison f' g (A.piece (0 * d)))
                    (ψ.app 0))))).trans
            ψ.app_one)))

/-- The components of the base-changed map are precomposition with the inverse of the canonical
identification of Tag 01NT. -/
@[simp] theorem baseChangeDown_app (ψ : Twisting (f' ≫ g) A d L) (i : ℤ) :
    (ψ.baseChangeDown g f' A d).app i =
      inv (compComparison f' g (A.piece (i * d))) ≫ ψ.app i := rfl

/-- **Stacks Project, Tag 01NT: the maps `ψ` on the two sides of the base change correspond
bijectively.** For a fixed invertible module `L` on the test scheme, the maps
`(f')^*(𝒜')^{(d)} ⟶ ⨁_n L^{⊗ n}` of a quadruple for `(S', 𝒜')` are in bijection with the maps
`f^*𝒜^{(d)} ⟶ ⨁_n L^{⊗ n}` for `(S, 𝒜)` over the composite `f = g ∘ f'`; this is the source's
`ψ = ψ'`, with both multiplicativity and the unit normalisation carried across. -/
def baseChangeEquiv :
    Twisting f' (baseAlgebra g A) d L ≃ Twisting (f' ≫ g) A d L where
  toFun χ := χ.baseChangeUp g f' A d
  invFun ψ := ψ.baseChangeDown g f' A d
  left_inv χ := Twisting.ext fun i => by
    simp only [baseChangeDown_app, baseChangeUp_app]
    exact IsIso.inv_hom_id_assoc (compComparison f' g (A.piece (i * d))) (χ.app i)
  right_inv ψ := Twisting.ext fun i => by
    simp only [baseChangeUp_app, baseChangeDown_app]
    exact IsIso.hom_inv_id_assoc (compComparison f' g (A.piece (i * d))) (ψ.app i)

end Twisting

/-! ### Base change of a quadruple -/

namespace Quadruple

/-- **A quadruple for the base-changed situation `(S', 𝒜')` over `f' : T ⟶ S'`, read as a
quadruple for `(S, 𝒜)` over the composite `g ∘ f'`.** The invertible module is unchanged — it
lives on the test scheme, which base change does not move — and the map `ψ` is carried across the
canonical identification of Tag 01NT by `Twisting.baseChangeUp`. The surjectivity of the
degree-one component survives because the identification is an isomorphism. -/
def baseChangeUp (P : Quadruple f' (baseAlgebra g A) d) :
    Quadruple (f' ≫ g) A d where
  L := P.L
  isInvertible := P.isInvertible
  twisting := P.twisting.baseChangeUp g f' A d
  epi_app_one :=
    @epi_comp _ _ _ _ _ (compComparison f' g (A.piece (1 * d))) inferInstance
      (P.twisting.app 1) P.epi_app_one

/-- Base change leaves the invertible module of a quadruple unchanged. -/
@[simp] theorem baseChangeUp_L (P : Quadruple f' (baseAlgebra g A) d) :
    (P.baseChangeUp g f' A d).L = P.L := rfl

/-- The components of the map of the base-changed quadruple. -/
@[simp] theorem baseChangeUp_twisting_app (P : Quadruple f' (baseAlgebra g A) d) (i : ℤ) :
    (P.baseChangeUp g f' A d).twisting.app i =
      compComparison f' g (A.piece (i * d)) ≫ P.twisting.app i := rfl

/-- **A quadruple for `(S, 𝒜)` over a morphism factoring as `g ∘ f'`, read as a quadruple for the
base-changed situation `(S', 𝒜')` over `f'`.** This is the inverse construction to
`Quadruple.baseChangeUp`. -/
def baseChangeDown (P : Quadruple (f' ≫ g) A d) :
    Quadruple f' (baseAlgebra g A) d where
  L := P.L
  isInvertible := P.isInvertible
  twisting := P.twisting.baseChangeDown g f' A d
  epi_app_one :=
    @epi_comp _ _ _ _ _ (inv (compComparison f' g (A.piece (1 * d)))) inferInstance
      (P.twisting.app 1) P.epi_app_one

/-- Base change in the other direction also leaves the invertible module unchanged. -/
@[simp] theorem baseChangeDown_L (P : Quadruple (f' ≫ g) A d) :
    (P.baseChangeDown g f' A d).L = P.L := rfl

/-- The components of the map of the quadruple read on the base-changed side. -/
@[simp] theorem baseChangeDown_twisting_app (P : Quadruple (f' ≫ g) A d) (i : ℤ) :
    (P.baseChangeDown g f' A d).twisting.app i =
      inv (compComparison f' g (A.piece (i * d))) ≫ P.twisting.app i := rfl

/-- The two base-change constructions on quadruples are inverse, in one direction. -/
theorem baseChangeDown_baseChangeUp (P : Quadruple f' (baseAlgebra g A) d) :
    (P.baseChangeUp g f' A d).baseChangeDown g f' A d = P :=
  Quadruple.ext rfl fun i => heq_of_eq (by
    simp only [baseChangeDown_twisting_app, baseChangeUp_twisting_app]
    exact IsIso.inv_hom_id_assoc (compComparison f' g (A.piece (i * d))) (P.twisting.app i))

/-- The two base-change constructions on quadruples are inverse, in the other direction. -/
theorem baseChangeUp_baseChangeDown (P : Quadruple (f' ≫ g) A d) :
    (P.baseChangeDown g f' A d).baseChangeUp g f' A d = P :=
  Quadruple.ext rfl fun i => heq_of_eq (by
    simp only [baseChangeDown_twisting_app, baseChangeUp_twisting_app]
    exact IsIso.hom_inv_id_assoc (compComparison f' g (A.piece (i * d))) (P.twisting.app i))

/-- **Stacks Project, Tag 01NT: the quadruples on the two sides of the base change correspond
bijectively.** The quadruples `(d, f' : T → S', L, ψ')` for the base-changed situation
`(S', 𝒜')` are in bijection with the quadruples `(d, g ∘ f', L, ψ)` for `(S, 𝒜)` whose structure
morphism is the composite; the invertible module is unchanged and the map `ψ` is carried across
the canonical identification `(f')^*(𝒜')^{(d)} = f^*𝒜^{(d)}` of Tag 01NT.

This is the whole of the source's proof. The passage to the classes and to the functors is
`Fd.isLimitBaseChangeCone`. -/
def baseChangeEquiv :
    Quadruple f' (baseAlgebra g A) d ≃ Quadruple (f' ≫ g) A d where
  toFun P := P.baseChangeUp g f' A d
  invFun P := P.baseChangeDown g f' A d
  left_inv := baseChangeDown_baseChangeUp g f' A d
  right_inv := baseChangeUp_baseChangeDown g f' A d

/-- **The bijection on quadruples matches strict equivalence on the two sides.** An isomorphism
of the Laurent algebras carries `ψ'` to `ψ''` exactly when it carries the base-changed maps to
one another, because the two differ by precomposition with an isomorphism. -/
theorem strictlyEquivalent_baseChangeUp_iff {P Q : Quadruple f' (baseAlgebra g A) d} :
    StrictlyEquivalent (P.baseChangeUp g f' A d) (Q.baseChangeUp g f' A d) ↔
      StrictlyEquivalent P Q := by
  rw [strictlyEquivalent_iff_exists_hom, strictlyEquivalent_iff_exists_hom]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, fun n => ?_⟩
    refine (cancel_epi (compComparison f' g (A.piece (n * d)))).mp ?_
    exact (Category.assoc _ _ _).symm.trans (hc n)
  · rintro ⟨c, hc⟩
    refine ⟨c, fun n => ?_⟩
    exact (Category.assoc _ _ _).trans
      (congrArg (fun z => compComparison f' g (A.piece (n * d)) ≫ z) (hc n))

/-- Base change in the other direction respects strict equivalence. -/
theorem strictlyEquivalent_baseChangeDown {P Q : Quadruple (f' ≫ g) A d}
    (h : StrictlyEquivalent P Q) :
    StrictlyEquivalent (P.baseChangeDown g f' A d) (Q.baseChangeDown g f' A d) := by
  refine (strictlyEquivalent_baseChangeUp_iff g f' A d).mp ?_
  rw [baseChangeUp_baseChangeDown, baseChangeUp_baseChangeDown]
  exact h

/-- **The bijection on quadruples commutes with the pullback along a morphism of test schemes.**
This is the naturality in the test scheme of the isomorphism of Tag 01NT, at the level of
quadruples; the only input is the associativity coherence `compComparison_assoc` of the
contraction of an iterated pullback. -/
theorem baseChangeUp_pullback (P : Quadruple f' (baseAlgebra g A) d) (k : T₂ ⟶ T) :
    (P.baseChangeUp g f' A d).pullback k = (P.pullback k).baseChangeUp g (k ≫ f') A d :=
  Quadruple.ext rfl fun i => heq_of_eq (by
    simp only [Quadruple.pullback_twisting_app, Twisting.pullbackApp,
      Quadruple.baseChangeUp_twisting_app]
    refine Eq.trans (congrArg (fun z => compComparison k (f' ≫ g) (A.piece (i * d)) ≫
      z ≫ laurentPullback k P.L i)
      (CategoryTheory.Functor.map_comp (pullbackFunctor (ringedSpaceHom k))
        (compComparison f' g (A.piece (i * d))) (P.twisting.app i))) ?_
    refine Eq.trans (congrArg (fun z => compComparison k (f' ≫ g) (A.piece (i * d)) ≫ z)
      (Category.assoc _ _ _)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun z => z ≫ ((pullbackFunctor (ringedSpaceHom k)).map
        (P.twisting.app i) ≫ laurentPullback k P.L i))
      (compComparison_assoc k f' g (A.piece (i * d))).symm) ?_
    exact Category.assoc _ _ _)

end Quadruple

end Twist

/-! ### The base-change map on `F_d`, and the fibre product -/

section FdLevel

open CategoryTheory.Limits

variable (g : S' ⟶ S)
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) (d : ℤ)

/-- A natural transformation of functors into sets, read on an element: the naturality square
evaluated at a point. -/
theorem natTrans_app_map {F G : Scheme.{u}ᵒᵖ ⥤ Type (u + 1)} (α : F ⟶ G)
    {X Y : Scheme.{u}ᵒᵖ} (φ : X ⟶ Y) (w : F.obj X) :
    α.app Y (F.map φ w) = G.map φ (α.app X w) :=
  ConcreteCategory.congr_hom (α.naturality φ) w

/-- **The map `F'_d(T) → F_d(T)` of Tag 01NT**: the class of a quadruple for the base-changed
situation `(S', 𝒜')` over `f' : T ⟶ S'` is sent to the class of the corresponding quadruple for
`(S, 𝒜)` over `g ∘ f'`. It is well defined because the bijection on quadruples matches strict
equivalence (`Quadruple.strictlyEquivalent_baseChangeUp_iff`). -/
def Fd.baseChangeUp {T : Scheme.{u}} (ξ : Fd (baseAlgebra g A) d T) : Fd A d T :=
  ⟨ξ.1 ≫ g,
    Quotient.map (fun P : Quadruple ξ.1 (baseAlgebra g A) d => P.baseChangeUp g ξ.1 A d)
      (fun _ _ h => (Quadruple.strictlyEquivalent_baseChangeUp_iff g ξ.1 A d).mpr h) ξ.2⟩

/-- The morphism to `S` recorded by the image of a class in `F'_d(T)` is the composite with
`g`. -/
@[simp] theorem Fd.baseChangeUp_fst {T : Scheme.{u}} (ξ : Fd (baseAlgebra g A) d T) :
    (Fd.baseChangeUp g A d ξ).1 = ξ.1 ≫ g := rfl

/-- The map sends the class of a quadruple to the class of the corresponding quadruple. -/
@[simp] theorem Fd.baseChangeUp_mk {T : Scheme.{u}} (f' : T ⟶ S')
    (P : Quadruple f' (baseAlgebra g A) d) :
    Fd.baseChangeUp g A d (Fd.mk f' P) = Fd.mk (f' ≫ g) (P.baseChangeUp g f' A d) := rfl

/-- **The inverse map, on the classes of quadruples over a fixed factorization**: a class of
quadruples for `(S, 𝒜)` over `g ∘ f'` gives a point of `F'_d(T)` over `f'`. -/
def Fd.baseChangeDownQ {T : Scheme.{u}} (f' : T ⟶ S')
    (q : Quotient (Quadruple.setoid (f' ≫ g) A d)) : Fd (baseAlgebra g A) d T :=
  ⟨f', Quotient.map (fun P : Quadruple (f' ≫ g) A d => P.baseChangeDown g f' A d)
      (fun _ _ h => Quadruple.strictlyEquivalent_baseChangeDown g f' A d h) q⟩

/-- The morphism to `S'` recorded by the inverse map is the chosen factorization. -/
@[simp] theorem Fd.baseChangeDownQ_fst {T : Scheme.{u}} (f' : T ⟶ S')
    (q : Quotient (Quadruple.setoid (f' ≫ g) A d)) :
    (Fd.baseChangeDownQ g A d f' q).1 = f' := rfl

/-- The two maps on classes are inverse, in one direction. -/
theorem Fd.baseChangeUp_baseChangeDownQ {T : Scheme.{u}} (f' : T ⟶ S')
    (q : Quotient (Quadruple.setoid (f' ≫ g) A d)) :
    Fd.baseChangeUp g A d (Fd.baseChangeDownQ g A d f' q) = ⟨f' ≫ g, q⟩ := by
  induction q using Quotient.ind with
  | _ P => exact congrArg (Fd.mk (f' ≫ g)) (Quadruple.baseChangeUp_baseChangeDown g f' A d P)

/-- The two maps on classes are inverse, in the other direction. -/
theorem Fd.baseChangeDownQ_baseChangeUp {T : Scheme.{u}} (ξ : Fd (baseAlgebra g A) d T) :
    Fd.baseChangeDownQ g A d ξ.1 (Fd.baseChangeUp g A d ξ).2 = ξ := by
  obtain ⟨f', q⟩ := ξ
  induction q using Quotient.ind with
  | _ P => exact congrArg (Fd.mk f') (Quadruple.baseChangeDown_baseChangeUp g f' A d P)

/-- **The map `F'_d(T) → F_d(T)` commutes with the pullback along a morphism of test schemes.**
This is `Quadruple.baseChangeUp_pullback` descended to the classes. -/
theorem Fd.baseChangeUp_pullback {T T₃ : Scheme.{u}} (k : T₃ ⟶ T)
    (ξ : Fd (baseAlgebra g A) d T) :
    Fd.baseChangeUp g A d (Fd.pullback k ξ) = Fd.pullback k (Fd.baseChangeUp g A d ξ) := by
  obtain ⟨f', q⟩ := ξ
  induction q using Quotient.ind with
  | _ P => exact (congrArg (Fd.mk ((k ≫ f') ≫ g))
      (Quadruple.baseChangeUp_pullback g f' A d P k)).symm

/-- **The canonical natural transformation `F'_d ⟹ F_d` of Tag 01NT**, the map of functors over
`g`: on a test scheme it is `Fd.baseChangeUp`, and naturality is
`Fd.baseChangeUp_pullback`. -/
def Fd.baseChangeNat :
    Fd.functor (baseAlgebra g A) d ⟶ Fd.functor A d where
  app _T := TypeCat.ofHom (Fd.baseChangeUp g A d)
  naturality _ _ φ := TypeCat.homEquiv.injective (funext fun ξ =>
    Fd.baseChangeUp_pullback g A d φ.unop ξ)

/-- The components of the canonical natural transformation. -/
@[simp] theorem Fd.baseChangeNat_app (T : Scheme.{u}ᵒᵖ) (ξ : Fd (baseAlgebra g A) d T.unop) :
    (Fd.baseChangeNat g A d).app T ξ = Fd.baseChangeUp g A d ξ := rfl

/-- The map `h_{S'} ⟹ h_S` of functors of points induced by `g : S' ⟶ S`, lifted to the universe
the sets `F_d(T)` live in, so that it can be compared with the projections
`...RelativeProjQcohSheaf.Fd.toBase`. -/
def yonedaBaseMap :
    yoneda.obj S' ⋙ uliftFunctor.{u + 1, u} ⟶ yoneda.obj S ⋙ uliftFunctor.{u + 1, u} :=
  CategoryTheory.Functor.whiskerRight (yoneda.map g) uliftFunctor.{u + 1, u}

/-- The map `h_{S'} ⟹ h_S` is composition with `g`. -/
@[simp] theorem yonedaBaseMap_app (T : Scheme.{u}ᵒᵖ) (h : T.unop ⟶ S') :
    (yonedaBaseMap g).app T (ULift.up h) = ULift.up (h ≫ g) := rfl

/-- **The square defining the comparison of Tag 01NT commutes**: the structure morphism recorded
by a class in `F'_d(T)`, composed with `g`, is the structure morphism recorded by its image in
`F_d(T)`. -/
theorem Fd.toBase_comp_yonedaBaseMap :
    Fd.toBase (baseAlgebra g A) d ≫ yonedaBaseMap g =
      Fd.baseChangeNat g A d ≫ Fd.toBase A d :=
  NatTrans.ext (funext fun _T => TypeCat.homEquiv.injective (funext fun _ξ => rfl))

/-- **The fibre product `h_{S'} ×_{h_S} F_d` written out.** Its value on a test scheme `T` is
the set of pairs consisting of a morphism `f' : T ⟶ S'` and a point of `F_d(T)` whose structure
morphism is `g ∘ f'`, and a morphism of test schemes acts by composition and by the pullback of
a class. -/
def Fd.baseFibre : Scheme.{u}ᵒᵖ ⥤ Type (u + 1) where
  obj T := {p : ULift.{u + 1, u} (T.unop ⟶ S') × Fd A d T.unop // p.1.down ≫ g = p.2.1}
  map {X Y} φ := TypeCat.ofHom fun p =>
    ⟨(ULift.up (φ.unop ≫ p.1.1.down), Fd.pullback φ.unop p.1.2), by
      rw [Fd.pullback_fst, Category.assoc, p.2]⟩
  map_id _ := TypeCat.homEquiv.injective (funext fun p =>
    Subtype.ext (Prod.ext (congrArg ULift.up (Category.id_comp p.1.1.down))
      (Fd.pullback_id p.1.2)))
  map_comp φ χ := TypeCat.homEquiv.injective (funext fun p =>
    Subtype.ext (Prod.ext (congrArg ULift.up (Category.assoc χ.unop φ.unop p.1.1.down))
      (Fd.pullback_comp φ.unop χ.unop p.1.2)))

/-- The projection of the fibre product to the functor of points of the new base. -/
def Fd.baseFibreFst :
    Fd.baseFibre g A d ⟶ yoneda.obj S' ⋙ uliftFunctor.{u + 1, u} where
  app _T := TypeCat.ofHom fun p => p.1.1
  naturality _ _ _ := TypeCat.homEquiv.injective (funext fun _p => rfl)

/-- The projection of the fibre product to `F_d`. -/
def Fd.baseFibreSnd : Fd.baseFibre g A d ⟶ Fd.functor A d where
  app _T := TypeCat.ofHom fun p => p.1.2
  naturality _ _ _ := TypeCat.homEquiv.injective (funext fun _p => rfl)

/-- The two projections of the fibre product agree over `h_S`. -/
theorem Fd.baseFibre_condition :
    Fd.baseFibreFst g A d ≫ yonedaBaseMap g = Fd.baseFibreSnd g A d ≫ Fd.toBase A d :=
  NatTrans.ext (funext fun _T => TypeCat.homEquiv.injective (funext fun p =>
    congrArg ULift.up p.2))

/-- The commutativity condition of a cone over the cospan `h_{S'} ⟶ h_S ⟵ F_d`, read on an
element of the vertex. -/
theorem Fd.baseFibre_cone_condition
    (s : PullbackCone (yonedaBaseMap g) (Fd.toBase A d)) (T : Scheme.{u}ᵒᵖ) (w : s.pt.obj T) :
    (s.fst.app T w).down ≫ g = (s.snd.app T w).1 := by
  have h : (yonedaBaseMap g).app T (s.fst.app T w) = (Fd.toBase A d).app T (s.snd.app T w) :=
    ConcreteCategory.congr_hom
      (congrArg (fun α : s.pt ⟶ yoneda.obj S ⋙ uliftFunctor.{u + 1, u} => α.app T)
        s.condition) w
  exact congrArg ULift.down h

/-- The morphism into the fibre product determined by a cone over the cospan
`h_{S'} ⟶ h_S ⟵ F_d`: on an element of the vertex it is the pair of its two images. -/
def Fd.baseFibreLift (s : PullbackCone (yonedaBaseMap g) (Fd.toBase A d)) :
    s.pt ⟶ Fd.baseFibre g A d where
  app T := TypeCat.ofHom fun w =>
    ⟨(s.fst.app T w, s.snd.app T w), Fd.baseFibre_cone_condition g A d s T w⟩
  naturality _ _ φ := TypeCat.homEquiv.injective (funext fun w =>
    Subtype.ext (Prod.ext (natTrans_app_map s.fst φ w) (natTrans_app_map s.snd φ w)))

/-- **`Fd.baseFibre` with its two projections is the fibre product `h_{S'} ×_{h_S} F_d`.** The
limit is checked directly: a cone over the cospan is a pair of compatible maps, which is a map
into the set of compatible pairs. -/
def Fd.isLimitBaseFibre :
    IsLimit (PullbackCone.mk (Fd.baseFibreFst g A d) (Fd.baseFibreSnd g A d)
      (Fd.baseFibre_condition g A d)) :=
  PullbackCone.IsLimit.mk _ (fun s => Fd.baseFibreLift g A d s)
    (fun _ => NatTrans.ext (funext fun _T =>
      TypeCat.homEquiv.injective (funext fun _w => rfl)))
    (fun _ => NatTrans.ext (funext fun _T =>
      TypeCat.homEquiv.injective (funext fun _w => rfl)))
    (fun _ m h1 h2 => NatTrans.ext (funext fun T =>
      TypeCat.homEquiv.injective (funext fun w => by
        refine Subtype.ext (Prod.ext ?_ ?_)
        · exact ConcreteCategory.congr_hom
            (congrArg (fun α : _ ⟶ yoneda.obj S' ⋙ uliftFunctor.{u + 1, u} => α.app T) h1) w
        · exact ConcreteCategory.congr_hom
            (congrArg (fun α : _ ⟶ Fd.functor A d => α.app T) h2) w)))

/-- The inverse map on classes, applied to a point of `F_d(T)` whose structure morphism factors
through `S'`, returns that point. The class is transported along the factorization, which is the
only transport the comparison needs. -/
theorem Fd.baseChangeUp_baseChangeDownQ_cast {T : Scheme.{u}} (f' : T ⟶ S') (ξ : Fd A d T)
    (h : f' ≫ g = ξ.1) :
    Fd.baseChangeUp g A d (Fd.baseChangeDownQ g A d f'
        (cast (congrArg (fun f => Quotient (Quadruple.setoid f A d)) h.symm) ξ.2)) = ξ := by
  obtain ⟨f, q⟩ := ξ
  obtain rfl : f' ≫ g = f := h
  exact Fd.baseChangeUp_baseChangeDownQ g A d f' q

/-- **Stacks Project, Tag 01NT, on a single test scheme: `F'_d(T)` is the fibre product of the
morphisms `T ⟶ S'` with `F_d(T)` over the morphisms `T ⟶ S`.** A point of `F'_d(T)` is a
morphism `f' : T ⟶ S'` together with a class of quadruples over `f'` for `(S', 𝒜')`, and the
bijection on quadruples turns the latter into a class of quadruples over `g ∘ f'` for
`(S, 𝒜)`. -/
def Fd.baseFibreEquiv (T : Scheme.{u}) :
    Fd (baseAlgebra g A) d T ≃
      {p : ULift.{u + 1, u} (T ⟶ S') × Fd A d T // p.1.down ≫ g = p.2.1} where
  toFun ξ := ⟨(ULift.up ξ.1, Fd.baseChangeUp g A d ξ), rfl⟩
  invFun p := Fd.baseChangeDownQ g A d p.1.1.down
    (cast (congrArg (fun f => Quotient (Quadruple.setoid f A d)) p.2.symm) p.1.2.2)
  left_inv ξ := Fd.baseChangeDownQ_baseChangeUp g A d ξ
  right_inv p := Subtype.ext (Prod.ext rfl
    (Fd.baseChangeUp_baseChangeDownQ_cast g A d p.1.1.down p.1.2 p.2))

/-- The comparison `F'_d ⟹ h_{S'} ×_{h_S} F_d`, assembled from the bijections
`Fd.baseFibreEquiv` on the test schemes. -/
def Fd.baseChangeFibreNat :
    Fd.functor (baseAlgebra g A) d ⟶ Fd.baseFibre g A d where
  app T := TypeCat.ofHom (Fd.baseFibreEquiv g A d T.unop)
  naturality _ _ φ := TypeCat.homEquiv.injective (funext fun ξ =>
    Subtype.ext (Prod.ext rfl (Fd.baseChangeUp_pullback g A d φ.unop ξ)))

/-- The comparison is an isomorphism, its components being bijections. -/
instance Fd.isIso_baseChangeFibreNat : IsIso (Fd.baseChangeFibreNat g A d) := by
  have : ∀ T : Scheme.{u}ᵒᵖ, IsIso ((Fd.baseChangeFibreNat g A d).app T) := fun T =>
    (isIso_iff_bijective _).mpr (Fd.baseFibreEquiv g A d T.unop).bijective
  exact NatIso.isIso_of_isIso_app _

/-- The comparison is compatible with the projection to the functor of points of the new base. -/
theorem Fd.baseChangeFibreNat_comp_fst :
    Fd.baseChangeFibreNat g A d ≫ Fd.baseFibreFst g A d = Fd.toBase (baseAlgebra g A) d :=
  NatTrans.ext (funext fun _T => TypeCat.homEquiv.injective (funext fun _ξ => rfl))

/-- The comparison is compatible with the projection to `F_d`. -/
theorem Fd.baseChangeFibreNat_comp_snd :
    Fd.baseChangeFibreNat g A d ≫ Fd.baseFibreSnd g A d = Fd.baseChangeNat g A d :=
  NatTrans.ext (funext fun _T => TypeCat.homEquiv.injective (funext fun _ξ => rfl))

/-- The comparison `F'_d ≅ h_{S'} ×_{h_S} F_d`, at the explicit fibre product
`Fd.baseFibre`. -/
def Fd.baseChangeFibreIso :
    Fd.functor (baseAlgebra g A) d ≅ Fd.baseFibre g A d :=
  asIso (Fd.baseChangeFibreNat g A d)

/-- **Stacks Project, Tag 01NT.** *In Situation 01NN. Let `d` be an integer. Let `F_d` be the
functor associated to `(S, 𝒜)`. Let `g : S' ⟶ S` be a morphism of schemes. Set `𝒜' = g^*𝒜`. Let
`F'_d` be the functor associated to `(S', 𝒜')`. Then there is a canonical isomorphism
`F'_d ≅ h_{S'} ×_{h_S} F_d` of functors.*

The isomorphism is produced in its universal form: `F'_d`, together with its projection
`Fd.toBase` to the functor of points of `S'` and the canonical map `Fd.baseChangeNat` to `F_d`,
**is a limit of the cospan `h_{S'} ⟶ h_S ⟵ F_d`**. So the comparison is the canonical one, and
`Fd.baseChangePullbackIso` reads it off as an isomorphism with the categorical fibre product.

The source takes `d ≥ 1`; positivity is not used. -/
-- Beyond what this declaration proves, recorded here rather than in the attribute:
--   The analogue for the union F of the display 01NX is not proved
def Fd.isLimitBaseChangeCone :
    IsLimit (PullbackCone.mk (Fd.toBase (baseAlgebra g A) d) (Fd.baseChangeNat g A d)
      (Fd.toBase_comp_yonedaBaseMap g A d)) :=
  IsLimit.ofIsoLimit (Fd.isLimitBaseFibre g A d)
    (PullbackCone.ext (Fd.baseChangeFibreIso g A d).symm
      ((IsIso.inv_hom_id_assoc (Fd.baseChangeFibreNat g A d)
          (Fd.baseFibreFst g A d)).symm.trans
        (congrArg (fun z => inv (Fd.baseChangeFibreNat g A d) ≫ z)
          (Fd.baseChangeFibreNat_comp_fst g A d)))
      ((IsIso.inv_hom_id_assoc (Fd.baseChangeFibreNat g A d)
          (Fd.baseFibreSnd g A d)).symm.trans
        (congrArg (fun z => inv (Fd.baseChangeFibreNat g A d) ≫ z)
          (Fd.baseChangeFibreNat_comp_snd g A d))))

/-- **Stacks Project, Tag 01NT: the canonical isomorphism `F'_d ≅ h_{S'} ×_{h_S} F_d`**, with the
right-hand side the categorical fibre product of the cospan `h_{S'} ⟶ h_S ⟵ F_d` in the functor
category. It is canonical: `Fd.baseChangePullbackIso_hom_fst` and `..._hom_snd` identify its
composites with the two projections as the projection of `F'_d` to the functor of points of `S'`
and the canonical map `F'_d ⟹ F_d`. -/
@[stacks 01NT "the canonical isomorphism F'_d = h_{S'} x_{h_S} F_d of functors on Sch^opp read \
off at the categorical fibre product, with its compatibility with both projections \
(baseChangePullbackIso_hom_fst and _hom_snd), so that it is the canonical isomorphism and not \
merely some isomorphism. Stated for every integer d"]
def Fd.baseChangePullbackIso :
    Fd.functor (baseAlgebra g A) d ≅
      Limits.pullback (yonedaBaseMap g) (Fd.toBase A d) :=
  IsLimit.conePointUniqueUpToIso (Fd.isLimitBaseChangeCone g A d) (limit.isLimit _)

/-- The canonical isomorphism of Tag 01NT, followed by the projection to the functor of points of
the new base, is the projection of `F'_d` to that functor of points. -/
theorem Fd.baseChangePullbackIso_hom_fst :
    (Fd.baseChangePullbackIso g A d).hom ≫ Limits.pullback.fst (yonedaBaseMap g)
        (Fd.toBase A d) =
      Fd.toBase (baseAlgebra g A) d :=
  IsLimit.conePointUniqueUpToIso_hom_comp (Fd.isLimitBaseChangeCone g A d)
    (limit.isLimit _) WalkingCospan.left

/-- The canonical isomorphism of Tag 01NT, followed by the projection to `F_d`, is the canonical
map `F'_d ⟹ F_d`. -/
theorem Fd.baseChangePullbackIso_hom_snd :
    (Fd.baseChangePullbackIso g A d).hom ≫ Limits.pullback.snd (yonedaBaseMap g)
        (Fd.toBase A d) =
      Fd.baseChangeNat g A d :=
  IsLimit.conePointUniqueUpToIso_hom_comp (Fd.isLimitBaseChangeCone g A d)
    (limit.isLimit _) WalkingCospan.right

end FdLevel

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
