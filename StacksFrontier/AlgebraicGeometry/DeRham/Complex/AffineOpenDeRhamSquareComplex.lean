module

public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.AffineOpenDeRhamSquare
public import StacksFrontier.AlgebraicGeometry.DeRham.Functoriality

/-!
# The canonical map of de Rham complexes of a square, on an affine open, as a complex

Let

```
X' --f--> X
|         |
p'        p
v         v
S' --g--> S
```

be a commutative square of schemes. `StacksDraft.AlgebraicGeometry.DeRham.Complex`
`.AffineOpenDeRhamComplexIso` reads the relative de Rham complex of a morphism on sections over
an open as a cochain complex of abelian groups, `Γ(Ω^•_{X/S}, W)`, and identifies it over an
affine open with the algebraic de Rham complex of its sections. **This file makes that reading
functorial in the square:** the canonical map `Ω^•_{X/S} ⟶ f_*Ω^•_{X'/S'}` of
[Stacks, Tag 07HX] becomes a map of complexes of abelian groups

`Γ(Ω^•_{X/S}, W) ⟶ Γ(Ω^•_{X'/S'}, f^{-1}W)`

for every open `W ⊆ X`, and over affine opens a map of *algebraic* de Rham complexes

`Ω^•_{Γ(X,U)/Γ(S,V)} ⟶ Ω^•_{Γ(X',f^{-1}U)/Γ(S',V')}`,

whose value on the generators `a₀ · (d a₁ ∧ ⋯ ∧ d a_n)` is computed, and which those values
determine.

## Main definitions

* `Stacks.AlgebraicGeometry.AffineOpenDeRham.deRhamSectionsAbSquareMap`: **the complex of
  sections of the relative de Rham complex is functorial in the square**, over every open `W`.
* `Stacks.AlgebraicGeometry.AffineOpenDeRham.ringDeRhamAbSquareMap`: **the same map read through
  the affine-open comparison at both ends**, as a map of algebraic de Rham complexes of abelian
  groups.

## Main results

* `Stacks.AlgebraicGeometry.AffineOpenDeRham.deRhamSectionsAbSquareMap_f_apply`: the degreewise
  component of the functorial map is the canonical map of [Stacks, Tag 07HX] read on sections, so
  it is that map and not a second one.
* `Stacks.AlgebraicGeometry.AffineOpenDeRham.sectionsAbTermMap_inv_apply`: the inverse of the
  degreewise affine-open comparison of abelian groups is the degreewise comparison of
  `Γ(X, U)`-modules in the other direction.
* `Stacks.AlgebraicGeometry.AffineOpenDeRham.ringDeRhamAbSquareMap_f_ιMulti_d` and
  `ringDeRhamAbSquareMap_f_smul_ιMulti_d`: **the conjugated map on the generators.** It carries
  `d a₁ ∧ ⋯ ∧ d a_n` to `d (f^♯ a₁) ∧ ⋯ ∧ d (f^♯ a_n)` and
  `a₀ · (d a₁ ∧ ⋯ ∧ d a_n)` to `f^♯ a₀ · (d (f^♯ a₁) ∧ ⋯ ∧ d (f^♯ a_n))`, where
  `f^♯ : Γ(X, U) ⟶ Γ(X', f^{-1}U)`.
* `Stacks.AlgebraicGeometry.AffineOpenDeRham.ringDeRhamAb_hom_ext`: **those values determine the
  map.** An additive map out of the degree-`n` term of `Ω^•_{Γ(X,U)/Γ(S,V)}` is determined by its
  values on `a₀ · (d a₁ ∧ ⋯ ∧ d a_n)`, these spanning the term over `ℤ`.

## What this is for, and what it is not

Nothing here carries a `@[stacks]` attribute. [Stacks, Tag 07HX] is the canonical map itself,
which is `AlgebraicGeometry.Scheme.Hom.deRhamFormsPushforwardHom`, and that is where the
attribute sits. [Stacks, Tag 0FUI] asserts that for the projection from the total space of a line
bundle the canonical map is a quasi-isomorphism over a base on which `ℚ` acts, and that is not
proved here: what is here is the chart-wise reading of the map, which is one of that assertion's
inputs.

The module docstrings of
`StacksFrontier.AlgebraicGeometry.DeRham.Complex.AffineOpenDeRhamSquare` and
`StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceAffineModel` recorded functoriality of
`Stacks.AlgebraicGeometry.AffineOpenDeRham.deRhamSectionsAbComplex` in the square as missing, and
it is `deRhamSectionsAbSquareMap` below: the canonical map of abelian sheaves
`AlgebraicGeometry.Scheme.Hom.deRhamAbelianPushforwardMap` already exists, the complex of
sections is by definition the sections functor applied to the complex of abelian sheaves, and
sections over `U` of a direct image along `f` are sections over `f^{-1}U`, so the map is the
image of the former under `Functor.mapHomologicalComplex` of the sections functor and both
identifications hold by `rfl`. No hypothesis beyond the commutativity of the square is used, and
in particular `W` is an arbitrary open: affineness is needed only for the comparison with the
algebraic complex.

**What remains between this and the ring-level map.** The two computations below pin the
conjugated map on generators, and `ringDeRhamAb_hom_ext` says the generators determine it. What
is still not available is a *name* for the ring-level map whose values those are — for a general
bottom edge `g` it is a `KaehlerDifferential.mapBaseChange` followed by a
`CommRingCat.KaehlerDifferential.map` of the square of rings, carried to exterior powers, and
that composite is not named in the development. Until it is, the identification has to be made
against whatever candidate a consumer has in hand, which is what `ringDeRhamAb_hom_ext` is for.

## Implementation notes

**Two `rfl` bridges before each `ModuleCat`-level input.** The degreewise component of
`ringDeRhamAbSquareMap` is a composite in `AddCommGrpCat` and the computations it is matched
against are stated in `ModuleCat`; a single `isDefEq` across both exhausts the recursion depth,
as it already did for the differential square of
`Stacks.AlgebraicGeometry.AffineOpenDeRham.sectionsAbTermMap_comm`. Each proof below therefore
unfolds the `AddCommGrpCat` composite by an explicit `show … from rfl` first, and only then
applies the `ModuleCat`-level statement. The crossing that makes the single step fail is between
`↥(CommRingCat.KaehlerDifferential (p.appLE V U e))`, which the affine-open comparison is stated
over, and `Ω[↑Γ(X, U)⁄↑Γ(S, V)]`, which the term of
`Stacks.AlgebraicGeometry.AffineDifferentialsIso.ringDeRhamComplex` is built from.

**Why the generator computations are stated on elements and not as semilinearity of the map.**
`(ringDeRhamAbComplex p e).X n` is an object of `AddCommGrpCat`, and instance search finds no
`HSMul ↑Γ(X, U) ↑((ringDeRhamAbComplex p e).X n)`: the `Γ(X, U)`-module structure is not visible
through it. So a statement quantified over an element `x` of that type cannot mention `b • x` at
all. Written on a concrete `b 0 • exteriorPower.ιMulti …` the scalar multiplication is
elaborated at the exterior power and the result unified with the opaque type afterwards, which is
why `ringDeRhamAbSquareMap_f_smul_ιMulti_d` and the hypothesis of `ringDeRhamAb_hom_ext` can be
written. The same asymmetry is why `sectionsAbTermMap_comm` runs its spanning argument in
`AddCommGrpCat`.

## References

* [Stacks Project, Tag 07HX](https://stacks.math.columbia.edu/tag/07HX), the canonical map
* [Stacks Project, Tag 0FUI](https://stacks.math.columbia.edu/tag/0FUI), the consumer
* [Stacks Project, Tag 0FLW](https://stacks.math.columbia.edu/tag/0FLW), the affine comparison
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.AffineOpenDeRham

section Inverse

variable {Y Z : Scheme.{u}} (q : Y ⟶ Z) {W : Y.Opens} {T : Z.Opens}
  (hW : IsAffineOpen W) (hT : IsAffineOpen T) (eqT : W ≤ q ⁻¹ᵁ T)

include hW hT in
/-- **The inverse of the degreewise affine-open comparison of abelian groups** is the degreewise
comparison of `Γ(Y, W)`-modules read in the other direction:
`Stacks.AlgebraicGeometry.AffineOpenDeRham.sectionsAbTermMap` is
`Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso` turned around and its module
structure forgotten, so inverting it undoes the turning. -/
theorem sectionsAbTermMap_inv_apply (n : ℕ) (y : (deRhamSectionsAbComplex q W).X n) :
    (CategoryTheory.inv (sectionsAbTermMap q hW hT eqT n)).hom y =
      (formsSectionsIso q hW hT eqT n).hom y := by
  have h1 := ConcreteCategory.congr_hom
    (CategoryTheory.IsIso.inv_hom_id (sectionsAbTermMap q hW hT eqT n)) y
  rw [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at h1
  have h1' : (formsSectionsIso q hW hT eqT n).inv
      ((CategoryTheory.inv (sectionsAbTermMap q hW hT eqT n)).hom y) = y := h1
  have hinj : Function.Injective (formsSectionsIso q hW hT eqT n).inv.hom :=
    (formsSectionsIso q hW hT eqT n).symm.toLinearEquiv.injective
  refine hinj (h1'.trans ?_)
  exact ((formsSectionsIso q hW hT eqT n).toLinearEquiv.symm_apply_apply y).symm

end Inverse

variable {X' X S' S : Scheme.{u}} (f : X' ⟶ X) (p : X ⟶ S) (p' : X' ⟶ S') (g : S' ⟶ S)
  {U : X.Opens} {V : S.Opens} {V' : S'.Opens}
  (hU : IsAffineOpen U) (hU' : IsAffineOpen (f ⁻¹ᵁ U))
  (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
  (e : U ≤ p ⁻¹ᵁ V) (e' : f ⁻¹ᵁ U ≤ p' ⁻¹ᵁ V')

/-! ### Functoriality of the complex of sections -/

/-- **The complex of sections of the relative de Rham complex is functorial in a commutative
square of schemes**: for an arbitrary open `W ⊆ X` the canonical map of [Stacks, Tag 07HX] gives
a map of cochain complexes of abelian groups
`Γ(Ω^•_{X/S}, W) ⟶ Γ(Ω^•_{X'/S'}, f^{-1}W)`.

It is the sections functor applied to the canonical map of complexes of abelian sheaves
`AlgebraicGeometry.Scheme.Hom.deRhamAbelianPushforwardMap`: the complex of sections is by
definition that functor applied degreewise to the complex of abelian sheaves, and sections over
`W` of a direct image along `f` are sections over `f^{-1}W`, so both ends of the composite are
the complexes named here. -/
def deRhamSectionsAbSquareMap (hcomm : f ≫ p = p' ≫ g) (W : X.Opens) :
    deRhamSectionsAbComplex p W ⟶ deRhamSectionsAbComplex p' (f ⁻¹ᵁ W) :=
  ((Stacks.Cohomology.LerayLowDegree.abelianSections.{u, u} X.carrier W).mapHomologicalComplex
      (ComplexShape.up ℕ)).map
    (Scheme.Hom.deRhamAbelianPushforwardMap f p p' g hcomm)

/-- **In each degree the functorial map is the canonical map of [Stacks, Tag 07HX] read on
sections**, so it is that map and not a second one. -/
theorem deRhamSectionsAbSquareMap_f_apply (hcomm : f ≫ p = p' ≫ g) (W : X.Opens) (n : ℕ)
    (x : (deRhamSectionsAbComplex p W).X n) :
    ((deRhamSectionsAbSquareMap f p p' g hcomm W).f n).hom x =
      ((Scheme.Hom.deRhamFormsPushforwardHom f p p' g hcomm).app (n : ℤ)).val.app (op W) x :=
  rfl

/-! ### The map of algebraic de Rham complexes over a pair of affine charts -/

include hU hU' hV hV' in
/-- **The canonical map of the square as a map of algebraic de Rham complexes.** Over affine
opens `U ⊆ X` with `f^{-1}U` affine, lying over affine opens `V ⊆ S` and `V' ⊆ S'`, the
affine-open comparison `Stacks.AlgebraicGeometry.AffineOpenDeRham.deRhamSectionsAbComplexIso` at
each end turns `Stacks.AlgebraicGeometry.AffineOpenDeRham.deRhamSectionsAbSquareMap` into a map
of cochain complexes of abelian groups

`Ω^•_{Γ(X,U)/Γ(S,V)} ⟶ Ω^•_{Γ(X',f^{-1}U)/Γ(S',V')}`. -/
def ringDeRhamAbSquareMap (hcomm : f ≫ p = p' ≫ g) :
    ringDeRhamAbComplex p e ⟶ ringDeRhamAbComplex p' e' :=
  (deRhamSectionsAbComplexIso p hU hV e).hom ≫
    deRhamSectionsAbSquareMap f p p' g hcomm U ≫
      (deRhamSectionsAbComplexIso p' hU' hV' e').inv

include hU hU' hV hV' in
/-- The degreewise component of the conjugated map, with the comparison at `f^{-1}U` still
inverted. This is the `rfl` bridge that unfolds the `AddCommGrpCat` composite before a
`ModuleCat`-level statement is applied to it. -/
theorem ringDeRhamAbSquareMap_f_apply_inv (hcomm : f ≫ p = p' ≫ g) (n : ℕ)
    (x : (ringDeRhamAbComplex p e).X n) :
    ((ringDeRhamAbSquareMap f p p' g hU hU' hV hV' e e' hcomm).f n).hom x =
      (CategoryTheory.inv (sectionsAbTermMap p' hU' hV' e' n)).hom
        (((Scheme.Hom.deRhamFormsPushforwardHom f p p' g hcomm).app (n : ℤ)).val.app (op U)
          ((formsSectionsIso p hU hV e n).inv x)) :=
  rfl

include hU hU' hV hV' in
/-- **The degreewise component of the conjugated map**: the canonical map of the square read on
sections over `U`, with the degreewise comparison of `Γ(X, U)`-modules on the source and the one
at `f^{-1}U` on the target. -/
theorem ringDeRhamAbSquareMap_f_apply (hcomm : f ≫ p = p' ≫ g) (n : ℕ)
    (x : (ringDeRhamAbComplex p e).X n) :
    ((ringDeRhamAbSquareMap f p p' g hU hU' hV hV' e e' hcomm).f n).hom x =
      (formsSectionsIso p' hU' hV' e' n).hom
        (((Scheme.Hom.deRhamFormsPushforwardHom f p p' g hcomm).app (n : ℤ)).val.app (op U)
          ((formsSectionsIso p hU hV e n).inv x)) :=
  (ringDeRhamAbSquareMap_f_apply_inv f p p' g hU hU' hV hV' e e' hcomm n x).trans
    (sectionsAbTermMap_inv_apply p' hU' hV' e' n _)

/-! ### The conjugated map on the generators -/

/-- The degreewise component of the conjugated map at `ω` equals `y` as soon as the comparison at
`f^{-1}U` of the canonical map applied to the comparison at `U` of `ω` does. -/
private theorem ringDeRhamAbSquareMap_f_eq_of (hcomm : f ≫ p = p' ≫ g) (n : ℕ)
    (ω : ↥(ModuleCat.of Γ(X, U)
      (⋀[Γ(X, U)]^n ↥(CommRingCat.KaehlerDifferential (p.appLE V U e))))) {y}
    (h : (formsSectionsIso p' hU' hV' e' n).hom
        (((Scheme.Hom.deRhamFormsPushforwardHom f p p' g hcomm).app (n : ℤ)).val.app (op U)
          ((formsSectionsIso p hU hV e n).inv ω)) = y) :
    ((ringDeRhamAbSquareMap f p p' g hU hU' hV hV' e e' hcomm).f n).hom ω = y :=
  (ringDeRhamAbSquareMap_f_apply f p p' g hU hU' hV hV' e e' hcomm n ω).trans h

include hU hU' hV hV' in
/-- **The conjugated map on a wedge of universal differentials**: it carries
`d a₁ ∧ ⋯ ∧ d a_n` to `d (f^♯ a₁) ∧ ⋯ ∧ d (f^♯ a_n)`, where
`f^♯ : Γ(X, U) ⟶ Γ(X', f^{-1}U)` is the map `f` induces on sections. This is
`Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso_hom_deRhamFormsPushforwardHom_ιMulti_d`
seated on the map of algebraic de Rham complexes. -/
theorem ringDeRhamAbSquareMap_f_ιMulti_d (hcomm : f ≫ p = p' ≫ g) (n : ℕ)
    (a : Fin n → Γ(X, U)) :
    ((ringDeRhamAbSquareMap f p p' g hU hU' hV hV' e e' hcomm).f n).hom
        (exteriorPower.ιMulti Γ(X, U) n fun i ↦ CommRingCat.KaehlerDifferential.d (a i)) =
      exteriorPower.ιMulti Γ(X', f ⁻¹ᵁ U) n fun i ↦
        CommRingCat.KaehlerDifferential.d ((f.app U).hom (a i)) := by
  have := formsSectionsIso_hom_deRhamFormsPushforwardHom_ιMulti_d f p p' g hU hU' hV hV' e e'
    hcomm n a
  refine ringDeRhamAbSquareMap_f_eq_of f p p' g hU hU' hV hV' e e' hcomm n
    (exteriorPower.ιMulti Γ(X, U) n fun i ↦ CommRingCat.KaehlerDifferential.d (a i)) ?_
  exact formsSectionsIso_hom_deRhamFormsPushforwardHom_ιMulti_d f p p' g hU hU' hV hV' e e'
    hcomm n a

include hU hU' hV hV' in
/-- **The conjugated map on a generator `a₀ · (d a₁ ∧ ⋯ ∧ d a_n)`**: it carries it to
`f^♯ a₀ · (d (f^♯ a₁) ∧ ⋯ ∧ d (f^♯ a_n))`. Together with
`Stacks.AlgebraicGeometry.AffineOpenDeRham.ringDeRhamAb_hom_ext` this pins the map down, the
generators spanning each term over `ℤ`.

The scalar and the differentiated functions are packaged into one family `b` indexed by
`Fin (n + 1)`, with `b 0` the scalar, because that is the shape of the spanning family of
`Crystalline.span_range_smul_ιMulti_eq_top`. -/
theorem ringDeRhamAbSquareMap_f_smul_ιMulti_d (hcomm : f ≫ p = p' ≫ g) (n : ℕ)
    (b : Fin (n + 1) → Γ(X, U)) :
    ((ringDeRhamAbSquareMap f p p' g hU hU' hV hV' e e' hcomm).f n).hom
        (b 0 • exteriorPower.ιMulti Γ(X, U) n fun i ↦
          CommRingCat.KaehlerDifferential.d (b i.succ)) =
      (f.app U).hom (b 0) • exteriorPower.ιMulti Γ(X', f ⁻¹ᵁ U) n fun i ↦
        CommRingCat.KaehlerDifferential.d ((f.app U).hom (b i.succ)) := by
  refine ringDeRhamAbSquareMap_f_eq_of f p p' g hU hU' hV hV' e e' hcomm n
    (b 0 • exteriorPower.ιMulti Γ(X, U) n fun i ↦
      CommRingCat.KaehlerDifferential.d (b i.succ)) ?_
  refine Eq.trans (formsSectionsIso_hom_pushforwardSections_smul f p p' g hU hU' hV hV' e e'
    hcomm n (b 0) (exteriorPower.ιMulti Γ(X, U) n fun i ↦
      CommRingCat.KaehlerDifferential.d (b i.succ))) ?_
  exact congrArg (fun z ↦ (f.app U).hom (b 0) • z)
    (formsSectionsIso_hom_deRhamFormsPushforwardHom_ιMulti_d f p p' g hU hU' hV hV' e e'
      hcomm n fun i ↦ b i.succ)

omit hU hV in
/-- **An additive map out of a term of `Ω^•_{Γ(X,U)/Γ(S,V)}` is determined by its values on the
generators `a₀ · (d a₁ ∧ ⋯ ∧ d a_n)`**, these spanning the degree-`n` term over `ℤ` by
`Crystalline.span_range_smul_ιMulti_eq_top` together with
`KaehlerDifferential.span_range_derivation`.

Spanning over `ℤ` rather than over `Γ(S, V)` is what makes an *additive* extensionality step
enough: the spanning family is closed under multiplication by `Γ(X, U)`, so a `Γ(S, V)`-span of
the whole term is already a `ℤ`-span of it. -/
theorem ringDeRhamAb_hom_ext {M : AddCommGrpCat.{u}} (n : ℕ)
    {φ ψ : (ringDeRhamAbComplex p e).X n ⟶ M}
    (h : ∀ b : Fin (n + 1) → Γ(X, U),
      φ.hom (b 0 • exteriorPower.ιMulti Γ(X, U) n fun i ↦
          CommRingCat.KaehlerDifferential.d (b i.succ)) =
        ψ.hom (b 0 • exteriorPower.ιMulti Γ(X, U) n fun i ↦
          CommRingCat.KaehlerDifferential.d (b i.succ))) :
    φ = ψ := by
  let _ := (p.appLE V U e).hom.toAlgebra
  refine AddCommGrpCat.hom_ext (addMonoidHom_ext_of_span_int_eq_top
    (Crystalline.span_range_smul_ιMulti_eq_top (R := ℤ)
      (KaehlerDifferential.D ↑Γ(S, V) ↑Γ(X, U))
      (KaehlerDifferential.span_range_derivation ↑Γ(S, V) ↑Γ(X, U)) n) ?_)
  rintro _ ⟨b, rfl⟩
  beta_reduce
  exact h b

end Stacks.AlgebraicGeometry.AffineOpenDeRham

end
