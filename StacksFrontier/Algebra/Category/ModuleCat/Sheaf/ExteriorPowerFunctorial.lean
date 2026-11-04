module

public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialForms
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Functoriality of the exterior power of a sheaf of modules in its module argument

Let `(C, J)` be a site, `O♯` a sheaf of commutative rings on it and `F`, `F'` sheaves of modules
over the underlying sheaf of rings. A morphism `f : F ⟶ F'` induces a morphism
`⋀ⁿ f : ⋀ⁿ F ⟶ ⋀ⁿ F'` on exterior powers, compatibly with identities and composition; for a
fixed degree this makes the exterior power a functor on sheaves of modules.

The map is produced by the universal property of the exterior algebra and nothing else. Writing
`ι : F ⟶ ⋀¹F` and `κ : F' ⟶ ⋀¹F'` for the two degree-one generators, the composite `f ≫ κ` is a
degree-one generator of `⋀(F')` indexed by `F`, and it is square-zero because `κ` is
(`SheafOfModules.GradedAlgebra.SquareZero.comp`). So the universal property of `⋀(F)` produces a
unique unital homomorphism of sheaves of graded algebras `⋀(F) ⟶ ⋀(F')` extending `f`, and its
degree-`n` component is the induced map on exterior powers. Functoriality is then uniqueness: the
identity of `⋀(F)` and the composite of two induced homomorphisms both extend the generator they
have to extend, so they are the homomorphisms the universal property names.

Nothing here constructs an exterior algebra. The universal property
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra` is a hypothesis throughout the site-level part,
so the statements apply to any exterior algebra of `F` and in particular to the one carried by a
`SheafOfModules.TensorExteriorSymmetricAlgebras` package; the scheme-level part specializes to
the chosen package `SheafOfModules.algebras`, which is the one
`AlgebraicGeometry.Scheme.Modules.exteriorPower` is defined from, and bundles the result as a
functor.

## Main definitions

* `SheafOfModules.GradedAlgebra.IsExteriorAlgebra.map`: the unital homomorphism of sheaves of
  graded algebras `⋀(F) ⟶ ⋀(F')` induced by a morphism `F ⟶ F'`, and
  `IsExteriorAlgebra.pieceMap` its degree-`n` component.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorPowerMap`: the induced map on the
  degree-`n` exterior powers of two `TensorExteriorSymmetricAlgebras` packages.
* `AlgebraicGeometry.Scheme.Modules.exteriorPowerMap`: the induced map
  `⋀ⁿ F ⟶ ⋀ⁿ F'` for sheaves of modules on a scheme.
* `AlgebraicGeometry.Scheme.Modules.exteriorPowerFunctor`: the degree-`n` exterior power as a
  functor `X.Modules ⥤ X.Modules`.

## Main results

* `SheafOfModules.GradedAlgebra.IsExteriorAlgebra.map_app_one`: the induced homomorphism extends
  `f`, which is the equation that characterizes it.
* `SheafOfModules.GradedAlgebra.IsExteriorAlgebra.map_id` and `map_comp`, and their degreewise
  forms `pieceMap_id` and `pieceMap_comp`: **functoriality**.
* `SheafOfModules.GradedAlgebra.IsExteriorAlgebra.isIso_pieceMap`: the map induced by an
  isomorphism of sheaves of modules is an isomorphism in every degree.
* `AlgebraicGeometry.Scheme.Modules.exteriorPowerMap_id` and `exteriorPowerMap_comp`: the
  scheme-level functoriality.

## Implementation notes

**Why the universal property and not the sectionwise model.** There are two spellings of the
exterior power of a sheaf of modules in this development: the graded piece
`(SheafOfModules.algebras J F).exterior.piece n`, which the statements about ranks, finiteness
and invertibility are written against, and `PresheafOfModules.extPow n` applied to the underlying
presheaf of modules, which is already functorial in the module argument
(`PresheafOfModules.extPowMap`). The two are identified by
`SheafOfModules.exteriorPowerSheafifyIso`, so an alternative route to the map below is to
transport `extPowMap` across that isomorphism. That route needs more than is available: the
isomorphism is built from `TensorExteriorSymmetricAlgebras.exteriorAlgebraIso`, a comparison of
two packages over a *fixed* sheaf of modules, so it carries no naturality in `F`, and without
naturality the transported map is not known to be the one the universal property determines —
indeed the transport would have to be proved functorial from scratch. The universal property
gives the map and both functoriality laws directly, and it also gives them for an arbitrary
exterior algebra rather than only for the sheafified sectionwise one. For the same reason no
statement below compares `exteriorPowerMap` with `PresheafOfModules.extPowMap`; that comparison
is the naturality of `exteriorPowerSheafifyIso`, proved separately in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerSheafifyNaturality` and not used
here.

**Proof irrelevance carries the square-zero side conditions.** `IsExteriorAlgebra.desc` takes a
proof that the target generator is square-zero as an argument, so `map` does too, through
`SquareZero.comp`. The functoriality proofs compare terms whose side conditions are produced in
different ways — `SquareZero.comp` applied to `f ≫ f'` against `SquareZero.comp` applied twice —
and those are equal by proof irrelevance alone, so no compatibility lemma for the side conditions
is needed.

**The degree is an integer.** The homogeneous pieces of a `SheafOfModules.GradedAlgebra` are
indexed by `ℤ`, and `AlgebraicGeometry.Scheme.Modules.exteriorPower` takes an integer degree, so
the maps below are stated for `n : ℤ`. In a negative degree both exterior algebras vanish and the
induced map is the zero map; no statement below separates the two cases.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/


@[expose] public section

open CategoryTheory

universe t a v₁ u₁ v u w

/-! ### The map induced by a morphism of sheaves of modules -/

namespace SheafOfModules.GradedAlgebra

section Site

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {M N P : SheafOfModules.{a} R} {A B D : GradedAlgebra.{t, a} R} {ι : M ⟶ A.piece 1}
  {κ : N ⟶ B.piece 1} {lam : P ⟶ D.piece 1}

namespace IsExteriorAlgebra

/-- **The homomorphism of exterior algebras induced by a morphism of sheaves of modules.** Given
exterior algebras `A` of `M` and `B` of `N`, a morphism `f : M ⟶ N` composes with the generator
of `B` to a square-zero degree-one generator of `B` indexed by `M`, and the universal property
of `A` turns that into a unital homomorphism `A ⟶ B` of sheaves of graded algebras. -/
@[ega "0 4.1.5" "partial"]
noncomputable def map (hA : IsExteriorAlgebra A ι) (hB : IsExteriorAlgebra B κ) (f : M ⟶ N) :
    UnitalHom A B :=
  hA.desc B (f ≫ κ) (hB.1.comp f)

/-- The induced homomorphism extends the given morphism of sheaves of modules: in degree one it
carries the generator of `A` to the image under `f` of the generator of `B`. -/
theorem map_app_one (hA : IsExteriorAlgebra A ι) (hB : IsExteriorAlgebra B κ) (f : M ⟶ N) :
    ι ≫ (hA.map hB f).app 1 = f ≫ κ :=
  hA.desc_extends B (f ≫ κ) (hB.1.comp f)

/-- The homomorphism induced by the identity is the identity. -/
theorem map_id (hA : IsExteriorAlgebra A ι) : hA.map hA (𝟙 M) = UnitalHom.id A :=
  hA.eq_id (by rw [map_app_one, Category.id_comp])

/-- The homomorphism induced by a composite is the composite of the induced homomorphisms. -/
theorem map_comp (hA : IsExteriorAlgebra A ι) (hB : IsExteriorAlgebra B κ)
    (hD : IsExteriorAlgebra D lam) (f : M ⟶ N) (f' : N ⟶ P) :
    hA.map hD (f ≫ f') = (hA.map hB f).comp (hB.map hD f') := by
  refine (hA.desc_unique D ((f ≫ f') ≫ lam) (hD.1.comp (f ≫ f')) ?_).symm
  rw [UnitalHom.comp_app, ← Category.assoc, map_app_one, Category.assoc, map_app_one,
    Category.assoc]

/-- **The map on degree-`n` exterior powers induced by a morphism of sheaves of modules**: the
degree-`n` component of `IsExteriorAlgebra.map`. -/
@[ega "0 4.1.5" "morphism action ∧^p f"]
noncomputable def pieceMap (hA : IsExteriorAlgebra A ι) (hB : IsExteriorAlgebra B κ)
    (f : M ⟶ N) (n : ℤ) : A.piece n ⟶ B.piece n :=
  (hA.map hB f).app n

/-- The map on degree-`n` exterior powers induced by the identity is the identity. -/
@[simp] theorem pieceMap_id (hA : IsExteriorAlgebra A ι) (n : ℤ) :
    hA.pieceMap hA (𝟙 M) n = 𝟙 (A.piece n) :=
  congrArg (fun g : UnitalHom A A => g.app n) hA.map_id

/-- The map on degree-`n` exterior powers induced by a composite is the composite of the induced
maps. -/
theorem pieceMap_comp (hA : IsExteriorAlgebra A ι) (hB : IsExteriorAlgebra B κ)
    (hD : IsExteriorAlgebra D lam) (f : M ⟶ N) (f' : N ⟶ P) (n : ℤ) :
    hA.pieceMap hD (f ≫ f') n = hA.pieceMap hB f n ≫ hB.pieceMap hD f' n :=
  congrArg (fun g : UnitalHom A D => g.app n) (hA.map_comp hB hD f f')

/-- The map on degree-`n` exterior powers induced by an isomorphism of sheaves of modules is an
isomorphism. -/
theorem isIso_pieceMap (hA : IsExteriorAlgebra A ι) (hB : IsExteriorAlgebra B κ) (f : M ⟶ N)
    (hf : IsIso f) (n : ℤ) : IsIso (hA.pieceMap hB f n) :=
  hA.isIso_desc_app hB f hf (hB.1.comp f) n

end IsExteriorAlgebra

end Site

end SheafOfModules.GradedAlgebra

/-! ### The induced map for a package of tensor, exterior and symmetric algebras -/

namespace SheafOfModules.TensorExteriorSymmetricAlgebras

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {F F' F'' : SheafOfModules.{w} (Sheaf.toRingCat J Osharp)}

/-- **The map on degree-`n` exterior powers induced by a morphism of sheaves of modules**, for
the exterior algebras carried by two `TensorExteriorSymmetricAlgebras` packages. -/
@[ega "0 4.1.5" "morphism action ∧^n f"]
noncomputable def exteriorPowerMap (A : TensorExteriorSymmetricAlgebras J F)
    (A' : TensorExteriorSymmetricAlgebras J F') (f : F ⟶ F') (n : ℤ) :
    A.exterior.piece n ⟶ A'.exterior.piece n :=
  A.exterior_isExteriorAlgebra.pieceMap A'.exterior_isExteriorAlgebra f n

/-- The map on degree-`n` exterior powers induced by the identity is the identity. -/
@[simp] theorem exteriorPowerMap_id (A : TensorExteriorSymmetricAlgebras J F) (n : ℤ) :
    A.exteriorPowerMap A (𝟙 F) n = 𝟙 (A.exterior.piece n) :=
  A.exterior_isExteriorAlgebra.pieceMap_id n

/-- The map on degree-`n` exterior powers induced by a composite is the composite of the induced
maps. -/
theorem exteriorPowerMap_comp (A : TensorExteriorSymmetricAlgebras J F)
    (A' : TensorExteriorSymmetricAlgebras J F') (A'' : TensorExteriorSymmetricAlgebras J F'')
    (f : F ⟶ F') (f' : F' ⟶ F'') (n : ℤ) :
    A.exteriorPowerMap A'' (f ≫ f') n =
      A.exteriorPowerMap A' f n ≫ A'.exteriorPowerMap A'' f' n :=
  A.exterior_isExteriorAlgebra.pieceMap_comp A'.exterior_isExteriorAlgebra
    A''.exterior_isExteriorAlgebra f f' n

end SheafOfModules.TensorExteriorSymmetricAlgebras

/-! ### The exterior power functor on a scheme -/

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {F F' F'' : X.Modules}

/-- **The map `⋀ⁿ F ⟶ ⋀ⁿ F'` induced by a morphism `F ⟶ F'` of sheaves of modules on a
scheme**, by the universal property of the exterior algebra. -/
@[ega "0 4.1.5" "partial"]
noncomputable def exteriorPowerMap (f : F ⟶ F') (n : ℤ) :
    exteriorPower F n ⟶ exteriorPower F' n :=
  (isExteriorAlgebra_exteriorAlgebra F).pieceMap (isExteriorAlgebra_exteriorAlgebra F') f n

/-- The exterior power of the identity is the identity. -/
@[simp] theorem exteriorPowerMap_id (F : X.Modules) (n : ℤ) :
    exteriorPowerMap (𝟙 F) n = 𝟙 (exteriorPower F n) :=
  (isExteriorAlgebra_exteriorAlgebra F).pieceMap_id n

/-- The exterior power of a composite is the composite of the exterior powers. -/
@[simp] theorem exteriorPowerMap_comp (f : F ⟶ F') (f' : F' ⟶ F'') (n : ℤ) :
    exteriorPowerMap (f ≫ f') n = exteriorPowerMap f n ≫ exteriorPowerMap f' n :=
  (isExteriorAlgebra_exteriorAlgebra F).pieceMap_comp (isExteriorAlgebra_exteriorAlgebra F')
    (isExteriorAlgebra_exteriorAlgebra F'') f f' n

/-- The exterior power of an isomorphism is an isomorphism. -/
instance isIso_exteriorPowerMap (f : F ⟶ F') [hf : IsIso f] (n : ℤ) :
    IsIso (exteriorPowerMap f n) :=
  (isExteriorAlgebra_exteriorAlgebra F).isIso_pieceMap (isExteriorAlgebra_exteriorAlgebra F') f
    hf n

/-- The degree-`n` exterior power as a functor on sheaves of modules on a scheme. -/
@[ega "0 4.1.5" "special case",
  sga "6 X 5.1" "special case",
  sga "6 X 6.1" "partial",
  sga "6 X 6.2" "special case"]
noncomputable def exteriorPowerFunctor (X : Scheme.{u}) (n : ℤ) : X.Modules ⥤ X.Modules where
  obj F := exteriorPower F n
  map f := exteriorPowerMap f n
  map_id F := exteriorPowerMap_id F n
  map_comp f f' := exteriorPowerMap_comp f f' n

/-- The degree-`n` exterior power functor sends `F` to `exteriorPower F n`. -/
@[simp] theorem exteriorPowerFunctor_obj (X : Scheme.{u}) (n : ℤ) (F : X.Modules) :
    (exteriorPowerFunctor X n).obj F = exteriorPower F n :=
  rfl

/-- The degree-`n` exterior power functor sends `f` to `exteriorPowerMap f n`. -/
@[simp] theorem exteriorPowerFunctor_map (n : ℤ) (f : F ⟶ F') :
    (exteriorPowerFunctor X n).map f = exteriorPowerMap f n :=
  rfl

end AlgebraicGeometry.Scheme.Modules

end
