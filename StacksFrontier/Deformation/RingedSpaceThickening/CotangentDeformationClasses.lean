module

public import StacksFrontier.Cotangent.SheavesOfRings.RingedSpaceExtTruncation
public import StacksFrontier.Cotangent.SheavesOfRings.RingedSpaceFundamentalTriangle
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentTriangleObstruction
public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionTorsor
public import StacksFrontier.Deformation.ToposThickening.FlatLiftTorsors
public import StacksFrontier.Homology.Injectives.FilteredComplex.HomComplex

/-!
# The deformation problem of a ringed space read on the full cotangent complex (Stacks 08UZ)

Let `t : (S, 𝒪_S) ⟶ (S', 𝒪_{S'})` be a first order thickening of ringed spaces with ideal `𝒥`,
let `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` be a morphism of ringed spaces, let `𝒢` be an `𝒪_X`-module and let
`c : f^*t^*𝒥 ⟶ 𝒢` be the prescribed map on ideals.  **Stacks 08UZ** describes the solutions of
the resulting deformation problem (**Stacks 08UY**) by the groups
`Ext^i_{𝒪_X}(L_{X/S}, 𝒢)` for `i = 2, 1, 0`:

1. a canonical `ξ ∈ Ext²_{𝒪_X}(L_{X/S}, 𝒢)` whose vanishing is necessary and sufficient for a
   solution to exist;
2. if a solution exists, the isomorphism classes of solutions are principal homogeneous under
   `Ext¹_{𝒪_X}(L_{X/S}, 𝒢)`;
3. the automorphisms of a solution are `Ext⁰_{𝒪_X}(L_{X/S}, 𝒢)`.

Clause (3) is `AlgebraicGeometry.RingedSpaceThickening.DeformationSolution`
`.solutionHomEquivCotangentExt` in
`StacksFrontier/Deformation/RingedSpaceThickening/SolutionAutomorphisms.lean`.  This file does
clauses (1) and (2).

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.extOneCotangentAddEquivOfTruncIso`: the degree-one
  transport.  An object of `D(𝒪_X)` identified with `τ_{≥ -1}L_{X/S}` — which is what
  **Stacks 08UW** says the naive cotangent complex `𝖭𝖫_{X/S}` is — has the same `Ext¹` into `𝒢`
  as `L_{X/S}` itself.
* `AlgebraicGeometry.RingedSpaceThickening.cotangentObstructionClass`: the Yoneda product of a
  class in `Ext¹_{𝒪_X}(A, 𝒢)` with a connecting morphism `L_{X/S} ⟶ A[1]`, an element of
  `Ext²_{𝒪_X}(L_{X/S}, 𝒢)`.  This is the element `ξ` of clause (1), `A` being the first vertex
  of the fundamental triangle of `X ⟶ S ⟶ S'`.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.cotangentObstructionClass_eq_zero_iff`: the closing
  step of **clause (1)** from its two inputs — the obstruction class vanishes exactly when a
  solution exists. Clause (1) itself is
  `AlgebraicGeometry.RingedSpaceThickening.cotangentObstruction_eq_zero_iff`.
* `AlgebraicGeometry.RingedSpaceThickening.nonempty_addTorsor_cotangentExtOne`: **clause (2)**
  transported from torsor data `T` — the isomorphism classes of solutions are a principal
  homogeneous space under `Ext¹_{𝒪_X}(L_{X/S}, 𝒢)`, as Mathlib's `AddTorsor`. Clause (2) itself
  is `AlgebraicGeometry.RingedSpaceThickening.solutionClassesCotangentAddTorsor`.

## The transport of this tag, and what each clause rests on

The source's proof of clauses (2) and (3) is: "Via the identifications
`𝖭𝖫_{X/S} = τ_{≥ -1}L_{X/S}` (**Stacks 08UW**) and `H⁰(L_{X/S}) = Ω_{X/S}` (**Stacks 08UV**) we
have seen parts (2) and (3) in Deformation Theory, Lemmas **08U8** and **08UC**."  In degree `0`
the identification is `Stacks.Sheaves.RingedSpaceCotangent.extZeroCotangentAddEquiv`, which is
what clause (3) consumes.  In degree `1` it is `extOneCotangentAddEquivOfTruncIso` below, built
from the two pieces

* `Stacks.Sheaves.RingedSpaceCotangent.extTruncGECotangentAddEquiv`, which identifies
  `Ext^i_{𝒪_X}(τ_{≥ -1}L_{X/S}, 𝒢)` with `Ext^i_{𝒪_X}(L_{X/S}, 𝒢)` for every `i ≤ 1`, and is
  a statement about the t-structure alone, and
* the identification of the object `𝖭𝖫_{X/S}` with the truncation `τ_{≥ -1}L_{X/S}`, which is
  the second assertion of **Stacks 08UW**.

That second assertion is `CategoryTheory.Sheaf.naiveComparison_isIso_homologyMap_unconditional`
for a homomorphism of sheaves of rings, read for a morphism of ringed spaces in
`StacksFrontier.Cotangent.SheavesOfRings.RingedSpaceNaiveTruncation`.  In this module the
identification is the argument `hN` of the declarations below, and the `Ext¹` transport they
build on top of it is the whole of the degree-one half of the source's "Via the
identifications".

The torsor data `T` of clause (2) is the content of **Stacks 08UC** for the acting group
`Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)`: a difference class of two solutions and an action realizing every
class as a difference, bundled as
`AlgebraicGeometry.RingedSpaceThickening.SolutionObstruction`.  Its own torsor formalism — that
these two make the isomorphism classes a principal homogeneous space, the isomorphism relation
being the vanishing of the difference class, which by clause (1) of **Stacks 08U8** is the
existence of a morphism of solutions — is proved in
`StacksFrontier/Deformation/RingedSpaceThickening/SolutionTorsor.lean`; the separation half of
**Stacks 08UC** is `AlgebraicGeometry.RingedSpaceThickening.isomorphic_iff_nonempty_solutionHom`.
The source's proof of the remaining half ends "A calculation (omitted) shows that
`o(X', X'_ξ) = ξ` as desired."

Clause (1) rests on the two inputs the source's own proof names: the parametrization of the
solutions by a fibre of a map of `Ext¹` groups, **Stacks 0GQ3**, and the fundamental triangle of
`X ⟶ S ⟶ S'`, **Stacks 08T4**.  The library's **Stacks 08T4** for ringed spaces,
`Stacks.Sheaves.RingedSpaceCotangent.exists_distTriang_degreewisePullback_of_shortExact`, proves
distinguishedness under the short exact sequence that **Stacks 08SZ** carries, and identifies
its first vertex with the degreewise rather than the derived pullback; the triangle is therefore
the arguments `u`, `w` and `htri` here, and the first vertex is left as the object `A` it is,
with no identification of it asserted.  What is proved here, from those two inputs, is the
source's closing step — "Hence taking `ξ` the image of `ξ'` works" — namely that the Yoneda
product with the connecting morphism of the triangle vanishes exactly on the classes restricted
from `Ext¹_{𝒪_X}(L_{X/S'}, 𝒢)`, so that the image of `ξ'` is the obstruction asserted by the
clause.

## Implementation notes

`Ext` is `CategoryTheory.DerivedCategory.Ext`, i.e. `CategoryTheory.ShiftedHom` in the derived
category, and the model of the derived category is `HasDerivedCategory.standard` as a local
instance, as in `StacksFrontier/Cotangent/SheavesOfRings/RingedSpaceExt.lean`.  The Yoneda product
`Ext¹ × Ext¹ ⟶ Ext²` is `CategoryTheory.ShiftedHom.comp`, as in
`AlgebraicGeometry.RingedSpaceThickening.obstructionExtClass`, which is the same construction
for the naive cotangent complex.

The exactness used for clause (1) is
`AlgebraicGeometry.RingedSpaceThickening.exists_comp_eq_iff_shiftedHom_comp_eq_zero'` of
`StacksFrontier/Deformation/RingedSpaceThickening/NaiveCotangentTriangleObstruction.lean`, stated
there for an arbitrary distinguished triangle in an arbitrary pretriangulated category; it is
not restated here.

The transport of the principal homogeneous structure across the degree-one identification is
`Deformation.ToposThickening.addTorsorCongr`, and the identification of the two `Ext¹` groups
along an isomorphism of their sources is `Stacks.Injectives.homCongrAddEquiv`.

## References

* [Stacks Project, Tag 08UZ](https://stacks.math.columbia.edu/tag/08UZ), this tag
* [Stacks Project, Tag 08UY](https://stacks.math.columbia.edu/tag/08UY), the deformation problem
* [Stacks Project, Tag 08UW](https://stacks.math.columbia.edu/tag/08UW),
  `𝖭𝖫_{X/S} = τ_{≥ -1}L_{X/S}`
* [Stacks Project, Tag 08UC](https://stacks.math.columbia.edu/tag/08UC), the torsor of solutions
  for the naive cotangent complex
* [Stacks Project, Tag 08T4](https://stacks.math.columbia.edu/tag/08T4), the fundamental triangle
* [Stacks Project, Tag 0GQ3](https://stacks.math.columbia.edu/tag/0GQ3), the solutions as a fibre
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open RingedSpaceModuleAdjunction
open Stacks.Sheaves.RingedSpaceCotangent

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

attribute [local instance] HasDerivedCategory.standard

variable {X S S' : RingedSpace.{u, u}} {t : S ⟶ S'} {ht : IsFirstOrderThickening t} {f : X ⟶ S}
  {G : SheafOfModules.{u} (structureSheafRing X)}
  {c : (modulePullback f).obj
    ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ G}

/-! ### The degree-one transport -/

/-- **The degree-one identification of Stacks 08UZ.** An object `N` of `D(𝒪_X)` identified with
the truncation `τ_{≥ -1}L_{X/S}` has the same first extension group into `𝒢` as `L_{X/S}` itself:

`Ext¹_{𝒪_X}(N, 𝒢) ≃+ Ext¹_{𝒪_X}(L_{X/S}, 𝒢)`.

The second assertion of **Stacks 08UW** is that the naive cotangent complex `𝖭𝖫_{X/S}` is such
an `N`, so this is the identification `Ext¹(𝖭𝖫_{X/S}, 𝒢) = Ext¹(L_{X/S}, 𝒢)` along which the
proof of **Stacks 08UZ** reads clauses (1) and (2) of its source lemmas on the full cotangent
complex.  It is the composite of the identification of `Ext¹` along `hN` with
`Stacks.Sheaves.RingedSpaceCotangent.extTruncGECotangentAddEquiv` in degree `1`, which is
restriction along the truncation projection `L_{X/S} ⟶ τ_{≥ -1}L_{X/S}`. -/
def extOneCotangentAddEquivOfTruncIso (f : X ⟶ S)
    (G : SheafOfModules.{u} (structureSheafRing X))
    {N : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (hN : N ≅ truncCotangentComplexDerived f) :
    DerivedCategory.Ext N
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj G) 1 ≃+
      cotangentExt f G 1 :=
  (Stacks.Injectives.homCongrAddEquiv hN (Iso.refl _)).trans
    (extTruncGECotangentAddEquiv f G (le_refl (1 : ℤ)))

/-! ### Clause (2): the isomorphism classes of solutions -/

/-- **Stacks 08UZ, clause (2), transported from torsor data.** If there exists a solution of the
deformation problem of **Stacks 08UY**, then the set of isomorphism classes of solutions is
principal homogeneous under `Ext¹_{𝒪_X}(L_{X/S}, 𝒢)`, as Mathlib's `AddTorsor`. Clause (2)
itself is `AlgebraicGeometry.RingedSpaceThickening.solutionClassesCotangentAddTorsor`.

`hN` identifies the object `N` carrying the acting group of **Stacks 08UC** with the truncation
`τ_{≥ -1}L_{X/S}`; for `N` the naive cotangent complex `𝖭𝖫_{X/S}` that is the second assertion
of **Stacks 08UW**.  `T` is the obstruction data of **Stacks 08UC**, whose isomorphism classes
`T.IsomorphismClasses` are the classes of solutions under the vanishing of the difference class,
which by clause (1) of **Stacks 08U8** is the existence of a morphism of solutions
(`AlgebraicGeometry.RingedSpaceThickening.setoid_iff_nonempty_lift`).  `hne` is the source's
"if there exists a solution".

The content of this declaration is the transport: the principal homogeneous structure under
`Ext¹_{𝒪_X}(N, 𝒢)` is carried across the degree-one identification of
`extOneCotangentAddEquivOfTruncIso` to one under `Ext¹_{𝒪_X}(L_{X/S}, 𝒢)`, which is the acting
group the clause names. -/
theorem nonempty_addTorsor_cotangentExtOne
    {N : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (hN : N ≅ truncCotangentComplexDerived f)
    (T : SolutionObstruction (DeformationSolution t ht f G c)
      (DerivedCategory.Ext N
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj G) 1))
    (hne : Nonempty (DeformationSolution t ht f G c)) :
    Nonempty (AddTorsor (cotangentExt f G 1) T.IsomorphismClasses) :=
  let := hne
  ⟨Deformation.ToposThickening.addTorsorCongr
    (extOneCotangentAddEquivOfTruncIso f G hN).symm (Equiv.refl _)⟩

/-! ### Clause (1): the obstruction class -/

/-- The obstruction class of **Stacks 08UZ**, clause (1): the Yoneda product of a class
`ξ' ∈ Ext¹_{𝒪_X}(A, 𝒢)` with a connecting morphism `w : L_{X/S} ⟶ A[1]`, an element of
`Ext²_{𝒪_X}(L_{X/S}, 𝒢)`.

For `A` the first vertex of the fundamental triangle of `X ⟶ S ⟶ S'` (**Stacks 08T4**) and `ξ'`
the class of **Stacks 0GQ3**, this is the "image of `ξ'`" that the source's proof takes for
`ξ`. -/
def cotangentObstructionClass (f : X ⟶ S)
    {G : SheafOfModules.{u} (structureSheafRing X)}
    {A : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (w : cotangentComplexDerived.{u, u + 1} f ⟶ A⟦(1 : ℤ)⟧)
    (xi : DerivedCategory.Ext A
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj G) 1) :
    cotangentExt f G 2 :=
  ShiftedHom.comp w xi (show (1 : ℤ) + 1 = 2 by omega)

/-- **The closing step of the proof of Stacks 08UZ, clause (1), from its two inputs.** The class
`ξ = cotangentObstructionClass f w ξ' ∈ Ext²_{𝒪_X}(L_{X/S}, 𝒢)` vanishes exactly when the
deformation problem of **Stacks 08UY** has a solution, given the triangle and the
parametrization below. Clause (1) itself, with the canonical class constructed and no inputs, is
`AlgebraicGeometry.RingedSpaceThickening.cotangentObstruction_eq_zero_iff`.

The two inputs are the two the source's proof names.  `u`, `w` and `htri` are the fundamental
triangle `A ⟶ L_{X/S'} ⟶ L_{X/S} ⟶ A[1]` of the tower `X ⟶ S ⟶ S'` (**Stacks 08T4**), its
second arrow being the canonical change-of-base map `L_{X/S'} ⟶ L_{X/S}`; the first vertex `A`
is left as the object it is, no identification of it with `Lf^*L_{S/S'}` being asserted.  `hsol`
is the parametrization of the solutions of **Stacks 0GQ3**, read on the full cotangent complex:
a solution exists exactly when the class `ξ'` is restricted along the first arrow from
`Ext¹_{𝒪_X}(L_{X/S'}, 𝒢)`.  The source's own statement of **Stacks 0GQ3** has
`Ext¹_{𝒪_X}(𝖭𝖫_{X/S'}, 𝒢)` and `Ext¹_{𝒪_X}(Lf^*𝖭𝖫_{S/S'}, 𝒢)` in those two places, and passes
to the displayed groups by the degree-one identification of
`extOneCotangentAddEquivOfTruncIso` above for `X ⟶ S'` and by the identification of the first
vertex `A`; `hsol` is that reading, so it absorbs both.  The library's **Stacks 0GQ3** is
`AlgebraicGeometry.RingedSpaceThickening.solutionsEquivDerivedExtFibre`.

What is proved is the source's closing step, "Hence taking `ξ` the image of `ξ'` works": by the
contravariant Yoneda exactness of the triangle, the Yoneda product of `ξ'` with the connecting
morphism `w` vanishes exactly on the classes so restricted. -/
theorem cotangentObstructionClass_eq_zero_iff
    {A : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (u : A ⟶ cotangentComplexDerived.{u, u + 1} (f ≫ t))
    (w : cotangentComplexDerived.{u, u + 1} f ⟶ A⟦(1 : ℤ)⟧)
    (htri : Triangle.mk u
        (DerivedCategory.Q.map (cotangentChangeOfBase f t)) w ∈
      distTriang (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))))
    (xi : DerivedCategory.Ext A
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj G) 1)
    (hsol : Nonempty (DeformationSolution t ht f G c) ↔
      ∃ z : cotangentExt (f ≫ t) G 1, xi = u ≫ z) :
    cotangentObstructionClass f w xi = 0 ↔ Nonempty (DeformationSolution t ht f G c) := by
  rw [hsol, cotangentObstructionClass]
  exact (exists_comp_eq_iff_shiftedHom_comp_eq_zero'
    (Triangle.mk u (DerivedCategory.Q.map (cotangentChangeOfBase f t)) w) htri xi).symm

end AlgebraicGeometry.RingedSpaceThickening

end
