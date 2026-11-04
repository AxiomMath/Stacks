module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraDescent
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulExtDescent
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulQuotientStructureStalk
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulSelfExtSquareZero

/-!
# The self-Ext algebra of a Koszul-regular quotient over the quotient, and the comparison map

Let `O♯` be a sheaf of commutative rings on a space, let `φ : (O♯)ʳ ⟶ O♯` generate a sheaf of
ideals `𝓘`, write `O_X = O♯/𝓘`, and let `K` be a Koszul complex resolving the quotient. The
self-Ext sheaves `Ext^n_{O♯}(O_X, O_X)` form a sheaf of graded `O♯`-algebras under composition
(`Stacks.SheafOfModules.homologyGradedAlgebra`), and every piece of it is annihilated by `𝓘`. It
therefore descends to a sheaf of graded **`O_X`**-algebras, and the degree-one generator still has
square zero, so the universal property of the exterior algebra over `O_X` produces the comparison
map of Stacks 0BQY in every degree,

`⋀ⁱ_{O_X}(Ext^1_{O♯}(O_X, O_X)) ⟶ Ext^i_{O♯}(O_X, O_X)`,

the map induced by composition: its value on a wedge of degree-one classes is their composition
product, which is what `IsExteriorAlgebra.desc` extends the generator to.

## Main definitions

* `Stacks.RegularSequence.KoszulChainData.homIso`: the `n`-th piece of the self-Ext algebra,
  identified with an internal Hom sheaf into the quotient.
* `Stacks.RegularSequence.KoszulChainData.extSelfAlgebra`: the self-Ext algebra over `O_X`.
* `Stacks.RegularSequence.KoszulChainData.extSelfExteriorAlgebra`: the exterior algebra over
  `O_X` of its degree-one piece.
* `Stacks.RegularSequence.KoszulChainData.extComparison`: the comparison map of Stacks 0BQY.

## Main statements

* `Stacks.RegularSequence.KoszulChainData.smul_homologyPiece_eq_zero`: every piece of the
  self-Ext algebra is annihilated by the sheaf of ideals.
* `Stacks.RegularSequence.KoszulChainData.squareZero_extSelfAlgebra`: the degree-one generator of
  the descended algebra has square zero.

## Implementation notes

**The annihilation holds in every integer degree, with no vanishing statement.** One might expect
negative degrees to need `Ext^n = 0` for `n < 0`, which this library does not have. They do not:
the `n`-th piece is isomorphic to `SheafHom_{O♯}(Kₙ, O_X)` for every `n : ℤ` by
`extIsoInternalHom`, and a homomorphism into a sheaf annihilated by `𝓘` is annihilated by `𝓘`
*whatever its source* — `smulHom_eq_zero_of_mem_idealOfHom` assumes nothing about the source. So
one statement covers all degrees, and in the degrees where the source happens to vanish it is
simply vacuous rather than requiring a separate argument.

**Two Ext sheaves have to be compared, not one.** `extIsoInternalHom` lands in
`Ext^n(O_X, Q(single 0 (O_X)))` while the graded algebra's pieces are the cohomology of
`SheafHom(K, K)`, which is `Ext^n(O_X, Q(cochain K))` — a *different* second argument. The two are
bridged by the augmentation of the Koszul cochain complex, which is a quasi-isomorphism, so its
image under the localisation functor is invertible; `derivedSheafExtMapIso` transports along it in
the second variable, and `quotientSingleIso` reconciles the two single complexes.

**The square-zero statement needs no transport.** The descended algebra has the same sections and
the same multiplication on them as the original — `GradedAlgebra.descend_mul_app` is `rfl` — so
the square-zero statement for the descended degree-one generator *is* the one already proved for
the original, applied unchanged. This is the payoff of descending with the underlying presheaves
untouched rather than by a construction that moves them.

**What this does not yet contain, and how it is reduced.** That `extComparison` is an
isomorphism is not proved here. It is *reduced*, by `isIso_extComparison`, to the single statement
that the self-Ext algebra is itself an exterior algebra on its degree-one piece — in every degree
at once, degree zero included, since both sides are formed over the same ring and no exterior-power
comparison across two rings arises.
The stalkwise material it needs is in place — the stalk of the source is an exterior power over
the stalk of `O_X`, the stalk of the target is the dual of one, and the duality pairing between
them is bijective — but identifying the *stalk map of this comparison* with that pairing is a
germ-level computation about the composition product on wedges, and is not done.

## References

* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace
open AlgebraicGeometry HomologicalComplex Stacks.ChainComplex

universe u

namespace Stacks.RegularSequence.KoszulChainData

open Stacks.Sites Stacks.SheafOfModules Stacks.RegularSequence

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology ↥X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (Opens.grothendieckTopology ↥X) CommRingCat.{u}]
  {r : ℕ}
  {A : SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X)
    (koszulFreeSheaf Rc r)}
  {φ : koszulFreeSheaf Rc r ⟶
    SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X) Rc)}
  (K : KoszulChainData.{u, u, u} A φ) [QuasiIso K.augmentation]

omit [HasSheafify (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology ↥X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (Opens.grothendieckTopology ↥X) CommRingCat.{u}] in
/-- **Annihilation transfers along an isomorphism of sheaves of modules.** -/
theorem smul_eq_zero_of_iso {M N : SheafOfModules.{u} (structureSheaf Rc)} (e : M ≅ N)
    {Y : (Opens ↥X)ᵒᵖ} {a : (structureSheaf Rc).obj.obj Y}
    (h : ∀ n : N.val.obj Y, a • n = 0) (m : M.val.obj Y) : a • m = 0 := by
  have hrt : e.inv.val.app Y (e.hom.val.app Y m) = m :=
    congrFun (congrArg (fun g => ⇑(ConcreteCategory.hom
      ((SheafOfModules.Hom.val g).app Y))) e.hom_inv_id) m
  calc a • m = e.inv.val.app Y (a • e.hom.val.app Y m) := by rw [map_smul, hrt]
    _ = 0 := by rw [h, map_zero]

/-- **The pieces of the self-Ext algebra are internal Hom sheaves into the quotient.** The `n`-th
cohomology of `SheafHom(K, K)` is `Ext^n(O_X, O_X)`, which is `SheafHom(Kₙ, O_X)`.

The augmentation of the Koszul cochain complex is a quasi-isomorphism, so it becomes invertible in
the derived category; that is what reconciles the second argument of the two Ext sheaves. -/
def homIso (n : ℤ) :=
  (derivedSheafExtIsoHomologyCochain Rc K (cochain Rc K) n).symm ≪≫
    derivedSheafExtMapIso Rc n (Iso.refl _)
      (asIso (DerivedCategory.Q.map (cochainAugmentation Rc K)) ≪≫
        DerivedCategory.Q.mapIso (quotientSingleIso Rc (φ := φ))) ≪≫
    extIsoInternalHom Rc K n

/-- **Every piece of the self-Ext algebra is annihilated by the sheaf of ideals**, in every
integer degree. No vanishing statement is needed: the piece is a sheaf of homomorphisms into the
quotient, and the sheaf of ideals annihilates every homomorphism into anything it annihilates,
with no hypothesis on the source. -/
theorem smul_homologyPiece_eq_zero (n : ℤ) (Y : (Opens ↥X)ᵒᵖ)
    (a : (structureSheaf Rc).obj.obj Y)
    (ha : a ∈ RingHom.ker ((quotientRingHom (quotientIdeal Rc φ)).hom.app Y).hom)
    (m : ((homologyGradedAlgebra Rc (cochain Rc K)).piece n).val.obj Y) : a • m = 0 :=
  smul_eq_zero_of_iso Rc (homIso Rc K n)
    (fun t => smulHom_eq_zero_of_mem_idealOfHom φ (K.chain.X n) (quotient Rc (φ := φ))
      (smul_koszulQuotient_eq_zero_of_mem_idealOfHom φ) Y.unop a
      (mem_idealOfHom_of_mem_ker φ Y a ha) t) m

/-- **The self-Ext algebra of a Koszul-regular quotient, as a sheaf of graded `O_X`-algebras.**
Its pieces are the self-Ext sheaves read as `O_X`-modules and its multiplication is composition. -/
def extSelfAlgebra :=
  haveI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology ↥X)
      (quotientRingHom (quotientIdeal Rc φ)).hom :=
    isLocallySurjective_quotientRingHom_idealOfHom φ
  SheafOfModules.GradedAlgebra.descend (quotientRingHom (quotientIdeal Rc φ))
    (homologyGradedAlgebra Rc (cochain Rc K)) (smul_homologyPiece_eq_zero Rc K)

/-- **The degree-one generator of the descended algebra has square zero.** The descended algebra
has the same sections and the same multiplication on them as the original, so this is the
square-zero statement already proved for the original, applied unchanged. -/
theorem squareZero_extSelfAlgebra :
    SheafOfModules.GradedAlgebra.SquareZero
      (A := extSelfAlgebra Rc K) (𝟙 ((extSelfAlgebra Rc K).piece 1)) :=
  squareZero_id_homologyGradedAlgebra Rc K

/-- **The exterior algebra over `O_X` of the first self-Ext sheaf.** -/
def extSelfExteriorAlgebra :=
  SheafOfModules.algebras (Opens.grothendieckTopology ↥X) ((extSelfAlgebra Rc K).piece 1)

/-- **The comparison map of Stacks 0BQY**, in every degree:

`⋀ⁱ_{O_X}(Ext^1_{O♯}(O_X, O_X)) ⟶ Ext^i_{O♯}(O_X, O_X)`.

It is the map induced by composition. The universal property of the exterior algebra over `O_X`
extends the identity of the degree-one piece, which has square zero, to a homomorphism of graded
algebras; its degree-`i` component carries a wedge of degree-one classes to their composition
product. -/
def extComparison (i : ℤ) :=
  ((extSelfExteriorAlgebra Rc K).exterior_isExteriorAlgebra.desc (extSelfAlgebra Rc K)
    (𝟙 ((extSelfAlgebra Rc K).piece 1)) (squareZero_extSelfAlgebra Rc K)).app i

/-- **The comparison of Stacks 0BQY is an isomorphism in every degree as soon as the self-Ext
algebra is itself an exterior algebra on its degree-one piece.**

Two graded algebras universal for the same property are isomorphic in every degree, and the
comparison between them *is* the map `desc` produces — `IsUniversal.pieceIso_hom` is `rfl`. So
the whole of Stacks 0BQY reduces to the hypothesis below, with no separate argument in any
degree: the conclusion is for all `i : ℤ`, so degree zero is covered by the same statement rather
than needing its own, there being no change of ring between the two sides here.

The hypothesis is the remaining mathematical content of the tag and is **not** proved here, which
is why nothing in this development carries the `0BQY` attribute. Proving it means showing that
the self-Ext algebra satisfies the universal property of the exterior algebra on
`Ext^1_{O♯}(O_X, O_X)`, which at a stalk is the statement that the duality pairing between an
exterior power of a finite free module and the exterior power of its dual is bijective. -/
theorem isIso_extComparison
    (h : SheafOfModules.GradedAlgebra.IsExteriorAlgebra (extSelfAlgebra Rc K)
      (𝟙 ((extSelfAlgebra Rc K).piece 1))) (i : ℤ) :
    IsIso (extComparison Rc K i) :=
  ((extSelfExteriorAlgebra Rc K).exterior_isExteriorAlgebra.isUniversal.pieceIso
    h.isUniversal i).isIso_hom

end Stacks.RegularSequence.KoszulChainData

end
