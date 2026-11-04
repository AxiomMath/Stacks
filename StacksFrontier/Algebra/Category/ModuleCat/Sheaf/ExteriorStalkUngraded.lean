module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AlgebraStalkUngraded
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerStalk
public import StacksCore.Tactic.StacksAttribute

/-!
# Tag 01CH, ungraded exterior assertion: the stalk of the exterior algebra of a sheaf of modules

Let `X` be a topological space, `O♯` a sheaf of commutative rings on it, `M` a sheaf of
`O♯`-modules and `A` an exterior algebra of `M` in the sense of Stacks Section 17.21. Stacks Tag
01CH asserts canonical isomorphisms of `O_x`-modules between the stalk at `x` of each of `T(M)`,
`Sym(M)`, `⋀(M)` and the corresponding construction applied to the stalk `M_x`. Those three
*ungraded* isomorphisms are the whole of what the source asserts. This file proves the **exterior
one**:

`⋀(M)_x ≅ ⋀_{O_x}(M_x)`,

together with the formula that pins the isomorphism down: for every `n`, it carries the germ at
`x` of the degree-`n` local section `s₀ ∧ ⋯ ∧ s_{n-1}` of `⋀(M)` to the wedge of the germs of the
`sᵢ`.

Here `⋀(M)` is the sheaf of modules underlying the exterior algebra, that is the coproduct
`∐ n, ⋀ⁿ M` of its homogeneous pieces, as in
`SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorAlgebraSheaf`.

The proof has two halves, and only the second is new.

* The graded→ungraded passage is `SheafOfModules.natStalkCoprodEquiv` in
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AlgebraStalkUngraded` — the stalk of a coproduct
  of sheaves of modules is the direct sum of the stalks, which is Tag 01AH — together with
  Mathlib's `ExteriorAlgebra.gradedAlgebra`, which reassembles `⨁ n, ⋀ⁿ(M_x)` into `⋀(M_x)`
  through `DirectSum.decomposeLinearEquiv`. This is exactly the step the exterior clause was
  waiting on, and `SheafOfModules.symmetricAlgebra_stalk` is the worked symmetric precedent.
* In each graded degree the stalk of `⋀ⁿ M` is `⋀ⁿ(M_x)`. The point-local content of that is
  `PresheafOfModules.extPowStalkEquivOfStalkIso` with its germ formula
  `PresheafOfModules.extPowStalkEquivOfStalkIso_germ_ιMulti`, in
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerStalk`, which is stated for a
  *presheaf* of modules together with a morphism out of the sectionwise exterior powers which is
  a stalk isomorphism. `SheafOfModules.exteriorPowerStalkEquiv` below instantiates it at the
  comparison morphism `SheafOfModules.GradedAlgebra.extPowCmp` of Tag 01CG, which
  `SheafOfModules.extPowCmp_eq_sheafifyUnit_comp` exhibits as a sheafification unit followed by
  an isomorphism and hence as a stalk isomorphism; that bundled form is what the coproduct step
  and `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPresentationExact` consume.

## Main definitions

* `SheafOfModules.exteriorPowerStalkEquiv` : the comparison isomorphism
  `(⋀ⁿ M)_x ≅ ⋀ⁿ_{O_x}(M_x)` for a sheaf of graded algebras `A` with a degree-one generator
  `gen : M ⟶ A.piece 1` satisfying the exterior-algebra universal property. This is the bundled
  form of the degreewise exterior clause.
* `SheafOfModules.exteriorAlgebraStalkEquiv` : **the comparison isomorphism of the ungraded
  exterior assertion of Tag 01CH**, `(∐ n, ⋀ⁿ M)_x ≅ ⋀_{O_x}(M_x)`.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorPowerStalkEquiv` and
  `SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorAlgebraStalkEquiv` : the same two
  comparisons for the exterior algebra supplied by a package of the three algebras of Section
  17.21.
* `SheafOfModules.ringedSpaceExteriorAlgebraStalkEquiv` : the ungraded comparison for the chosen
  package on a ringed space, which is the form Section 17.21 states its lemmas in. See the
  implementation note on its missing type ascription.

## Main results

* `SheafOfModules.isIso_stalkFunctor_map_extPowCmp` : the comparison morphism of Tag 01CG for
  exterior powers is an isomorphism on every stalk.
* `SheafOfModules.exteriorPowerStalkEquiv_germ_homogeneousProd` : **the degreewise comparison on
  a wedge of local sections.** The germ of the ordered product in `A` of the images of
  `s₀, …, s_{n-1}` under the degree-one generator goes to the wedge of the germs of the `sᵢ`.
* `SheafOfModules.exteriorAlgebraStalkEquiv_germ_homogeneousProd` : the same formula for the
  ungraded comparison, in every degree, after the degree-`n` coproduct injection.
* `SheafOfModules.exteriorAlgebra_stalk` : **Tag 01CH, ungraded exterior assertion** — the
  isomorphism and that formula assembled into the single assertion that a comparison isomorphism
  with that behaviour on germs of wedges exists. This is the declaration carrying the tag.

## Implementation notes

**Which clause of Tag 01CH is proved, and which is not.** The source asserts three ungraded
isomorphisms. The symmetric one is `SheafOfModules.symmetricAlgebra_stalk` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AlgebraStalkUngraded`; the exterior one is
`SheafOfModules.exteriorAlgebra_stalk` below. The tensor one, `T(M)_x ≅ T(M_x)`, is **not** proved
here: it belongs with the stalk of the sectionwise tensor powers. The degreewise statements this
library also carries
(`SheafOfModules.symmetricPower_stalk`, `PresheafOfModules.extPowStalkEquivOfStalkIso`,
`SheafOfModules.exteriorPowerStalkEquiv` below) are its own clause convention and not assertions
of the source; they are strictly stronger inputs, not substitutes.

**Explicit universe levels on `PresheafOfModules.extPow`.** `isIso_stalkFunctor_map_extPowCmp`
writes `PresheafOfModules.extPow.{u, u, u, u}`. This is forced, and it is the only place in the
file where a universe is written by hand. `extPow` is stated for a presheaf of modules in
`PresheafOfModules.{max w a}` over a presheaf of rings in universe `w`, so handing it to
`isIso_stalkFunctor_map_sheafifyUnit`, whose argument is pinned at `PresheafOfModules.{u}`,
produces the universe constraint `max ?w ?a =?= u` with *both* sides metavariables, on which the
unifier gives up with "stuck at solving universe constraint". When one of the two is already
known the constraint is solvable — which is why `A.extPowCmp` itself needs no annotation, `A`
being a `GradedAlgebra.{u, u}` — but here neither is. Lean solves `max u ?a =?= u`; it does not
solve `max ?w ?a =?= u`.

**`rw` cannot push `Functor.map_comp` through the factorization of Tag 01CG.** The right-hand
side of `SheafOfModules.extPowCmp_eq_sheafifyUnit_comp` composes a morphism of
`PresheafOfModules (O♯.obj ⋙ forget₂ CommRingCat RingCat)` with the image under
`SheafOfModules.forget` of a morphism of sheaves of modules. The two ambient categories are
definitionally equal and not syntactically equal, so after rewriting with the factorization the
goal is not type-correct at `implicit` transparency and `rw [Functor.map_comp]` fails with a
message naming a pattern. The remedy is the usual one for this situation: the equation of
morphisms is proved at the term level with `congrArg` and two applications of
`CategoryTheory.Functor.map_comp`, and the two halves are then combined with
`CategoryTheory.IsIso.comp_isIso'`, whose arguments are explicit. The second half must be
produced by a `have` with its *ascribed* type: left to `inferInstance` against the rewritten
goal, instance search walks into `IsIso (sheafifyUnit …)`, which is false, and fails.

**`ringedSpaceExteriorAlgebraStalkEquiv` has no ascribed type.** With the type written out —
`… ≃ₗ[↑(TopCat.Presheaf.stalk Y.sheaf.obj x)] ExteriorAlgebra ↑(TopCat.Presheaf.stalk Y.sheaf.obj
x) ↑(TopCat.Presheaf.stalk G.val.presheaf x)` — synthesizing
`AddCommMonoid (ExteriorAlgebra ↑(TopCat.Presheaf.stalk Y.sheaf.obj x) …)` exhausts the default
`synthInstance` heartbeat budget, because reaching `CommRing` of the stalk of the ring sheaf of a
ringed space unfolds `AlgebraicGeometry.SheafedSpace.sheaf`. The same type with `Osharp` a
variable, which is the package-level `TensorExteriorSymmetricAlgebras.exteriorAlgebraStalkEquiv`
just above, synthesizes immediately; and `ExteriorAlgebra` is what makes the difference, since the
symmetric counterpart `SheafOfModules.ringedSpaceSymmetricAlgebraStalkEquiv` is stated with its
type in full. Raising the limit is not available here, so the declaration is given by its body
alone — the type is then obtained by substitution into an already-elaborated statement and no
search is performed.

**Every degree is a variable.** No statement below instantiates a numeral degree.
`ExteriorAlgebra R N` is a `CliffordAlgebra` quotient of `TensorAlgebra R N`, so with a numeral
degree `whnf` unfolds the exterior power through `Submodule.mul` and `Submodule.span` into that
quotient, which is fatal while elaborating a *statement* and not only in a proof. The one numeral
that appears, in `gen : M ⟶ A.piece 1`, is the degree of a piece of an *abstract* sheaf of graded
algebras, where there is nothing to unfold.

**Wedges, not products.** `ExteriorAlgebra R N` is not commutative, so there is no `Finset.prod`
and the spanning family is the ordered product `ExteriorAlgebra.ιMulti R n`. The degreewise
statements are phrased with its subtype-valued companion `exteriorPower.ιMulti R n`, so that they
are equations *in* the exterior power; the ungraded ones are phrased with
`ExteriorAlgebra.ιMulti`, the two being related by `exteriorPower.ιMulti_apply_coe`. The ordering
matches `Stacks.GradedAlgebra.homogeneousProd`, which also multiplies on the right, so no
reordering appears anywhere.

**Universes.** The space, the ring and the module universe are all `u`. That is forced, not
chosen: Mathlib's instance `Module (R.stalk x) ↑(TopCat.Presheaf.stalk F.presheaf x)` in
`Mathlib/Algebra/Category/ModuleCat/Stalk.lean` exists at no other combination,
`AlgebraicGeometry.SheafOfModules.stalkFunctor` is stated for `X : TopCat.{u}` and a sheaf of
`RingCat.{u}`-valued rings, and `SheafOfModules.sectionwiseExteriorAlgebra` — the exterior algebra
the comparison of Tag 01CG is built against — exists only at `GradedAlgebra.{u, u}`. Independently,
`SheafOfModules.stalkCoprodEquiv` fixes the index universe; see the implementation notes of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AlgebraStalkUngraded`, which record the two more
general forms that were tried and why neither is available. Tag 01CH is stated in the
equal-universe case and nothing the source says is narrowed.

## References

* [Stacks Project, Tag 01CH](https://stacks.math.columbia.edu/tag/01CH)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace CategoryTheory.Sheaf
open DirectSum

universe u

namespace SheafOfModules

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {M : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (A : GradedAlgebra.{u, u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp))
  (gen : M ⟶ A.piece 1) (hA : GradedAlgebra.IsExteriorAlgebra A gen)

/-! ### The stalk of an exterior power of a sheaf of modules -/

/-- **The comparison morphism of Tag 01CG for exterior powers is a stalk isomorphism.** It
factors as the sheafification unit of the presheaf of sectionwise exterior powers followed by a
degreewise isomorphism (`SheafOfModules.extPowCmp_eq_sheafifyUnit_comp`), and each of those is a
stalk isomorphism. -/
theorem isIso_stalkFunctor_map_extPowCmp (n : ℕ) (x : ↥X) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf _).map
        (A.extPowCmp (hO := (toRingCat (Opens.grothendieckTopology ↥X) Osharp).property)
          gen hA.1 n))) := by
  have key : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf _).map
          (A.extPowCmp (hO := (toRingCat (Opens.grothendieckTopology ↥X) Osharp).property)
            gen hA.1 n)) =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          ((PresheafOfModules.toPresheaf _).map
            (PresheafOfModules.sheafifyUnit
              (toRingCatMap (Opens.grothendieckTopology ↥X) (𝟙 Osharp.obj))
              (PresheafOfModules.extPow.{u, u, u, u} n M.val))) ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          ((PresheafOfModules.toPresheaf _).map
            ((SheafOfModules.forget (toRingCat (Opens.grothendieckTopology ↥X) Osharp)).map
              (exteriorPieceIso M A gen hA (n : ℤ)).hom)) := by
    refine Eq.trans (congrArg
      (fun f => (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf _).map f))
      (extPowCmp_eq_sheafifyUnit_comp M A gen hA.1 hA n)) ?_
    exact Eq.trans (congrArg (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf _).map_comp _ _))
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map_comp _ _)
  have h2 : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf _).map
        ((SheafOfModules.forget (toRingCat (Opens.grothendieckTopology ↥X) Osharp)).map
          (exteriorPieceIso M A gen hA (n : ℤ)).hom))) := inferInstance
  rw [key]
  exact IsIso.comp_isIso'
    (isIso_stalkFunctor_map_sheafifyUnit (PresheafOfModules.extPow.{u, u, u, u} n M.val) x) h2

/-- **The comparison isomorphism of the exterior assertion of Tag 01CH in graded degree `n`**,
for a *sheaf* of graded algebras: for an exterior algebra `A` of a sheaf of modules `M`, the
stalk at `x` of the degree-`n` exterior power `A.piece n` is `⋀ⁿ` of the stalk `M_x` over the
stalk ring `O_x`.

This is `PresheafOfModules.extPowStalkEquivOfStalkIso` at the comparison morphism
`SheafOfModules.GradedAlgebra.extPowCmp` of Tag 01CG, which `isIso_stalkFunctor_map_extPowCmp`
shows is a stalk isomorphism. -/
@[ega "0 4.1.5"]
noncomputable def exteriorPowerStalkEquiv (n : ℕ) (x : ↥X) :
    ↑(TopCat.Presheaf.stalk (A.piece (n : ℤ)).val.presheaf x)
        ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      ⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^n ↑(TopCat.Presheaf.stalk M.val.presheaf x) :=
  PresheafOfModules.extPowStalkEquivOfStalkIso M.val x n
    (A.extPowCmp (hO := (toRingCat (Opens.grothendieckTopology ↥X) Osharp).property) gen hA.1 n)
    (isIso_stalkFunctor_map_extPowCmp A gen hA n x)

/-- **The comparison isomorphism on a wedge of local sections.** The germ at `x` of the local
section `s₀ ∧ ⋯ ∧ s_{n-1}` of `⋀ⁿ M` — written with the data of `A` alone, as the ordered product
in `A` of the images of the `sᵢ` under its degree-one generator — goes to the wedge of the germs
of the `sᵢ`.

Such wedges span `⋀ⁿ(M_x)` (`ExteriorAlgebra.ιMulti_span_fixedDegree`), so this formula
determines `exteriorPowerStalkEquiv` and is what makes it the *canonical* isomorphism of
Tag 01CH rather than merely one. -/
theorem exteriorPowerStalkEquiv_germ_homogeneousProd (n : ℕ) (x : ↥X) (U : Opens ↥X)
    (hx : x ∈ U) (s : Fin n → M.val.obj (op U)) :
    exteriorPowerStalkEquiv A gen hA n x
        (TopCat.Presheaf.germ (A.piece (n : ℤ)).val.presheaf U x hx
          (A.toPresheafGradedAlgebra.homogeneousProd (op U) n
            fun i => gen.val.app (op U) (s i))) =
      exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) n
        fun i => TopCat.Presheaf.germ M.val.presheaf U x hx (s i) := by
  have hcmp : PresheafOfModules.Hom.app
        (A.extPowCmp (hO := (toRingCat (Opens.grothendieckTopology ↥X) Osharp).property)
          gen hA.1 n) (op U)
        (exteriorPower.ιMulti
          ((Osharp.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) n s) =
      A.toPresheafGradedAlgebra.homogeneousProd (op U) n
        fun i => gen.val.app (op U) (s i) :=
    Stacks.GradedAlgebra.extCmpSections_ιMulti A.toPresheafGradedAlgebra gen.val
      (fun Y y => hA.1 Y y) n (op U) s
  refine Eq.trans (congrArg (fun z => exteriorPowerStalkEquiv A gen hA n x
    (TopCat.Presheaf.germ (A.piece (n : ℤ)).val.presheaf U x hx z)) hcmp.symm) ?_
  exact PresheafOfModules.extPowStalkEquivOfStalkIso_germ_ιMulti M.val x n _ _ U hx s

/-! ### Tag 01CH for the ungraded exterior algebra of a sheaf of modules -/

/-- **The comparison isomorphism of the ungraded exterior assertion of Tag 01CH**: for an
exterior algebra `A` of a sheaf of modules `M`, the stalk at `x` of the sheaf of modules
`∐ n, ⋀ⁿ M` underlying `⋀(M)` is the exterior algebra of the stalk `M_x` over the stalk ring
`O_x`.

It is the composition of three identifications: the stalk of the coproduct is the direct sum of
the stalks (`SheafOfModules.natStalkCoprodEquiv`); in each degree the stalk of `⋀ⁿ M` is
`⋀ⁿ(M_x)` (`exteriorPowerStalkEquiv`, which is Tag 01CH in degree `n`); and `⋀(M_x)` is the
direct sum of its exterior powers, which is Mathlib's `ExteriorAlgebra.gradedAlgebra` read
through `DirectSum.decomposeLinearEquiv`. -/
noncomputable def exteriorAlgebraStalkEquiv (x : ↥X) :
    ↑(TopCat.Presheaf.stalk (∐ fun n : ℕ => A.piece (n : ℤ)).val.presheaf x)
        ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      ExteriorAlgebra ↑(TopCat.Presheaf.stalk Osharp.obj x)
        ↑(TopCat.Presheaf.stalk M.val.presheaf x) :=
  ((natStalkCoprodEquiv (fun n : ℕ => A.piece (n : ℤ)) x).symm.trans
      (DirectSum.congrLinearEquiv fun n : ℕ => exteriorPowerStalkEquiv A gen hA n x)).trans
    (DirectSum.decomposeLinearEquiv
      (fun n : ℕ => ⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^n
        ↑(TopCat.Presheaf.stalk M.val.presheaf x))).symm

/-- **The comparison isomorphism on a wedge of local sections.** The germ at `x` of the image
under the degree-`n` coproduct injection of the ordered product, in `A`, of the images of
`s₀, …, s_{n-1}` under the degree-one generator goes to the wedge of the germs of the `sᵢ`.

Wedges of vectors span each exterior power (`ExteriorAlgebra.ιMulti_span_fixedDegree`) and the
exterior powers span the exterior algebra (`ExteriorAlgebra.gradedAlgebra`), so this formula
determines `exteriorAlgebraStalkEquiv` and is what makes it the *canonical* isomorphism of
Tag 01CH rather than merely one. -/
theorem exteriorAlgebraStalkEquiv_germ_homogeneousProd (x : ↥X) (n : ℕ) (U : Opens ↥X)
    (hx : x ∈ U) (s : Fin n → M.val.obj (op U)) :
    exteriorAlgebraStalkEquiv A gen hA x
        (TopCat.Presheaf.germ (∐ fun m : ℕ => A.piece (m : ℤ)).val.presheaf U x hx
          ((Sigma.ι (fun m : ℕ => A.piece (m : ℤ)) n).val.app (op U)
            (A.toPresheafGradedAlgebra.homogeneousProd (op U) n
              fun i => gen.val.app (op U) (s i)))) =
      ExteriorAlgebra.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) n
        fun i => TopCat.Presheaf.germ M.val.presheaf U x hx (s i) := by
  have h1 : TopCat.Presheaf.germ (∐ fun m : ℕ => A.piece (m : ℤ)).val.presheaf U x hx
        ((Sigma.ι (fun m : ℕ => A.piece (m : ℤ)) n).val.app (op U)
          (A.toPresheafGradedAlgebra.homogeneousProd (op U) n
            fun i => gen.val.app (op U) (s i))) =
      natStalkCoprodEquiv (fun m : ℕ => A.piece (m : ℤ)) x (DirectSum.of _ n
        (TopCat.Presheaf.germ (A.piece (n : ℤ)).val.presheaf U x hx
          (A.toPresheafGradedAlgebra.homogeneousProd (op U) n
            fun i => gen.val.app (op U) (s i)))) := by
    rw [natStalkCoprodEquiv_of]
    exact (PresheafOfModules.stalkMapL_germ x
      (Sigma.ι (fun m : ℕ => A.piece (m : ℤ)) n).val U hx _).symm
  rw [h1]
  simp only [exteriorAlgebraStalkEquiv, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, DirectSum.coe_congrLinearEquiv,
    ← DirectSum.lof_eq_of ↑(TopCat.Presheaf.stalk Osharp.obj x), DirectSum.lmap_lof,
    LinearEquiv.coe_coe, DirectSum.decomposeLinearEquiv_symm_lof]
  exact Eq.trans
    (congrArg Subtype.val (exteriorPowerStalkEquiv_germ_homogeneousProd A gen hA n x U hx s))
    (exteriorPower.ιMulti_apply_coe ↑(TopCat.Presheaf.stalk Osharp.obj x) n _)

include hA in
/-- **Tag 01CH, ungraded exterior assertion.** For a sheaf of modules `M` on a topological space
with a sheaf of commutative rings `O♯`, an exterior algebra `A` of `M` in the sense of Section
17.21, and a point `x`, there is a canonical isomorphism of `O_x`-modules

`⋀(M)_x ≅ ⋀_{O_x}(M_x)`,

where `⋀(M)` is the coproduct `∐ n, ⋀ⁿ M` of the homogeneous pieces of `A`.

It is canonical in the sense Tag 01CH means: its value is prescribed on the germ of every local
section of the form `s₀ ∧ ⋯ ∧ s_{n-1}`, in every degree `n`, namely the wedge of the germs of the
`sᵢ`; such wedges span each exterior power of the stalk
(`ExteriorAlgebra.ιMulti_span_fixedDegree`) and the exterior powers span `⋀(M_x)`
(`ExteriorAlgebra.gradedAlgebra`), so no other linear map has that behaviour.

The exterior algebra is a hypothesis rather than a chosen term because Section 17.21 pins it only
up to canonical isomorphism; `SheafOfModules.isExteriorAlgebra_sectionwiseExteriorAlgebra_val`
shows the hypothesis is satisfiable for every `M`, and
`SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorAlgebraStalkEquiv` discharges it from a
package of the three algebras of Section 17.21. -/
@[stacks 01CH "the ungraded exterior assertion `⋀(M)ₓ ≅ ⋀(Mₓ)` — one of the three isomorphisms \
the source asserts — with the isomorphism pinned down by its values on germs of wedges of local \
sections in every degree. The ungraded symmetric assertion `Sym(M)ₓ ≅ Sym(Mₓ)` is \
`SheafOfModules.symmetricAlgebra_stalk`. The ungraded tensor assertion `T(M)ₓ ≅ T(Mₓ)` is not \
covered here. The degreewise clauses, which are this \
library's convention and not assertions of the source, are \
`SheafOfModules.symmetricPower_stalk` and `PresheafOfModules.extPowStalkEquivOfStalkIso`."]
theorem exteriorAlgebra_stalk (x : ↥X) :
    ∃ cmp : ↑(TopCat.Presheaf.stalk (∐ fun n : ℕ => A.piece (n : ℤ)).val.presheaf x)
        ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
        ExteriorAlgebra ↑(TopCat.Presheaf.stalk Osharp.obj x)
          ↑(TopCat.Presheaf.stalk M.val.presheaf x),
      ∀ (n : ℕ) (U : Opens ↥X) (hx : x ∈ U) (s : Fin n → M.val.obj (op U)),
        cmp (TopCat.Presheaf.germ (∐ fun m : ℕ => A.piece (m : ℤ)).val.presheaf U x hx
            ((Sigma.ι (fun m : ℕ => A.piece (m : ℤ)) n).val.app (op U)
              (A.toPresheafGradedAlgebra.homogeneousProd (op U) n
                fun i => gen.val.app (op U) (s i)))) =
          ExteriorAlgebra.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) n
            fun i => TopCat.Presheaf.germ M.val.presheaf U x hx (s i) :=
  ⟨exteriorAlgebraStalkEquiv A gen hA x,
    fun n U hx s => exteriorAlgebraStalkEquiv_germ_homogeneousProd A gen hA x n U hx s⟩

end SheafOfModules

/-! ### The comparison for a package of the three algebras, and on a ringed space -/

namespace SheafOfModules.TensorExteriorSymmetricAlgebras

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {G : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

/-- **Tag 01CH, exterior assertion in degree `n`, for a package of the three algebras of Section
17.21.** The stalk of the degree-`n` exterior power `⋀ⁿ G` supplied by the package is `⋀ⁿ` of the
stalk of `G`. -/
noncomputable def exteriorPowerStalkEquiv
    (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) G) (n : ℕ) (x : ↥X) :
    ↑(TopCat.Presheaf.stalk (A.exteriorPower n).val.presheaf x)
        ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      ⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^n ↑(TopCat.Presheaf.stalk G.val.presheaf x) :=
  SheafOfModules.exteriorPowerStalkEquiv A.exterior A.exteriorGenerator
    A.exterior_isExteriorAlgebra n x

/-- **Tag 01CH, ungraded exterior assertion, for a package of the three algebras of Section
17.21.** The stalk of the sheaf of modules `exteriorAlgebraSheaf` underlying `⋀(G)` is the
exterior algebra of the stalk of `G`. -/
noncomputable def exteriorAlgebraStalkEquiv
    (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) G) (x : ↥X) :
    ↑(TopCat.Presheaf.stalk A.exteriorAlgebraSheaf.val.presheaf x)
        ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      ExteriorAlgebra ↑(TopCat.Presheaf.stalk Osharp.obj x)
        ↑(TopCat.Presheaf.stalk G.val.presheaf x) :=
  SheafOfModules.exteriorAlgebraStalkEquiv A.exterior A.exteriorGenerator
    A.exterior_isExteriorAlgebra x

end SheafOfModules.TensorExteriorSymmetricAlgebras

namespace SheafOfModules

open AlgebraicGeometry RingedSpaceModuleAdjunction

/-- **Tag 01CH, ungraded exterior assertion, on a ringed space**, for the chosen package
`SheafOfModules.ringedSpaceAlgebras` of the three algebras of Section 17.21: the stalk of the
exterior algebra of a sheaf of modules on a ringed space is the exterior algebra of the stalk.
This is the form Section 17.21 states its lemmas in. -/
noncomputable def ringedSpaceExteriorAlgebraStalkEquiv (Y : RingedSpace.{u, u})
    (G : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥Y.carrier) Y.sheaf))
    (x : ↥Y.carrier) :=
  TensorExteriorSymmetricAlgebras.exteriorAlgebraStalkEquiv (ringedSpaceAlgebras Y G) x

end SheafOfModules

end
