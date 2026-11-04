module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorStalkUngraded
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.HomogeneousProdLeft
public import StacksCore.Tactic.StacksAttribute

/-!
# The exterior basis of a finite free sheaf of modules, and its germs

Let `O♯` be a sheaf of commutative rings on a topological space `X`, let `F = O♯ʳ` be the
finite free sheaf of `O♯`-modules on `r` generators, and let `A` be a package of the tensor,
exterior and symmetric algebras of `F` in the sense of Stacks Section 17.21. For an open set
`U` and an `n`-tuple `i : Fin n → Fin r` of indices, the ordered product

`e_{i₀} ∧ e_{i₁} ∧ ⋯ ∧ e_{i_{n-1}}`

of the images under the degree-one generator of `A` of the tautological sections of `F` is a
section of `⋀ⁿ F` over `U`. This file defines it and computes its germ: under the comparison
isomorphism `(⋀ⁿ F)_x ≅ ⋀ⁿ_{O_x}(F_x)` of Stacks Tag 01CH in degree `n`, the germ of that
product is the wedge of the germs of the tautological sections.

The ordered product recurses on the **left**, `e_{i₀} · (e_{i₁} ⋯ e_{i_{n-1}})`, which is the
form the Koszul complex of Stacks Tag 062K is written in. Its degree is therefore
`1 + (n : ℤ)`, only propositionally `((n + 1 : ℕ) : ℤ)`, so a degree transport is part of the
definition; `Stacks.GradedAlgebra.homogeneousProdLeft` is that product and
`Stacks.GradedAlgebra.homogeneousProdLeft_eq_homogeneousProd` is what lets the transport-free
germ formula of Tag 01CH be applied to it.

Everything here is stated for an **arbitrary** package `A`, taken as a hypothesis. No
particular construction of the exterior algebra of `F` is presupposed, and in particular
nothing here depends on a chosen inhabitant of the package.

## Main definitions

* `Stacks.RegularSequence.koszulFreeSheaf`: the finite free sheaf of modules `O♯ʳ`, with its
  generators indexed by `ULift (Fin r)` so that the index type lies in the universe
  `SheafOfModules.free` requires.
* `Stacks.RegularSequence.exteriorBasisSection`: the ordered exterior product over `U` of the
  tautological generators indexed by `i : Fin n → Fin r`, as a section of `⋀ⁿ (O♯ʳ)`. The empty
  product is the unit of the exterior algebra in degree zero.

## Main results

* `Stacks.RegularSequence.exteriorBasisSection_zero` and
  `Stacks.RegularSequence.exteriorBasisSection_succ`: the two defining clauses, the second
  exhibiting the left-handed recursion together with its degree transport.
* `Stacks.RegularSequence.map_exteriorBasisSection`: the exterior products commute with
  restriction, so they are restrictions of the ones over `⊤`.
* `Stacks.RegularSequence.exteriorPowerStalkEquiv_germ_exteriorBasisSection`: **the germ of an
  exterior product of tautological generators is the wedge of the germs of those generators.**

## Implementation notes

What is forced and what is chosen.

* The single universe `u` carrying the space, the sections of `O♯` and the sections of every
  module is the one `SheafOfModules.exteriorPowerStalkEquiv` is stated at, and that in turn is
  forced by `TopCat.Presheaf.stalk`: a `CommRingCat.{u}`-valued presheaf on `X` has stalks only
  for `X : TopCat.{u}`. Nothing is narrowed here.
* The index type of the free sheaf is `ULift.{u} (Fin r)` rather than `Fin r` because
  `SheafOfModules.free` takes its index type in the module universe. The tuples `i` that index
  the exterior products are nevertheless `Fin n → Fin r`, with `ULift.up` applied at the one
  place a generator is named: an exterior product is indexed by a tuple of *indices*, and
  wrapping those in `ULift` would propagate into every consumer.
* `exteriorBasisSection` is defined through `Stacks.GradedAlgebra.homogeneousProdLeft` rather
  than by its own recursion, so that `homogeneousProdLeft_eq_homogeneousProd` is available and
  the germ formula reduces to the transport-free
  `SheafOfModules.exteriorPowerStalkEquiv_germ_homogeneousProd`. Writing the recursion out
  would make the degree transport of each step a separate obligation in the germ computation.
* `map_exteriorBasisSection` is a statement about `(⋀ⁿ F).val.map`, not about the sheaf
  morphism: the tautological sections of `SheafOfModules.free` are global sections, and
  `PresheafOfModules.sections_property` is the compatibility with restriction they carry, so no
  sheaf condition and no naturality square is used.
* No `@[stacks]` attribute. The germ formula below is the degree-`n` exterior clause of Tag
  01CH specialized to a free sheaf of modules and to products of its tautological generators;
  the tag itself is carried by `SheafOfModules.exteriorAlgebra_stalk`
  (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ExteriorStalkUngraded.lean`), and this file
  asserts nothing the tag states that is not already proved there.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01CH](https://stacks.math.columbia.edu/tag/01CH)
* [Stacks Project, Tag 062K](https://stacks.math.columbia.edu/tag/062K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace

universe u

namespace Stacks.RegularSequence

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}

/-- The finite free sheaf of `O♯`-modules on `r` generators. The generators are indexed by
`ULift (Fin r)` because `SheafOfModules.free` takes its index type in the module universe. -/
noncomputable abbrev koszulFreeSheaf (Osharp : Sheaf (Opens.grothendieckTopology ↥X)
    CommRingCat.{u}) (r : ℕ) :
    SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp) :=
  SheafOfModules.free (ULift.{u} (Fin r))

variable {r : ℕ}
  (A : SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X)
    (koszulFreeSheaf Osharp r))

/-- The tautological generator of `O♯ʳ` indexed by `k : Fin r`, read over the open set `U` as a
degree-one section of the exterior algebra. -/
noncomputable def exteriorGen (U : Opens ↥X) (k : Fin r) : (A.exterior.piece 1).val.obj (op U) :=
  A.exteriorGenerator.val.app (op U)
    ((SheafOfModules.freeSection (ULift.up k)).val (op U))

/-- **The ordered exterior product of the tautological generators indexed by `i`, over `U`.**
The product recurses on the left, and the empty product is the unit of the exterior algebra in
degree zero. -/
noncomputable def exteriorBasisSection (U : Opens ↥X) (n : ℕ) (i : Fin n → Fin r) :
    (A.exteriorPower n).val.obj (op U) :=
  A.exterior.toPresheafGradedAlgebra.homogeneousProdLeft (op U) n fun j => exteriorGen A U (i j)

/-- The empty exterior product is the unit of the exterior algebra. -/
theorem exteriorBasisSection_zero (U : Opens ↥X) (i : Fin 0 → Fin r) :
    exteriorBasisSection A U 0 i = A.exterior.one.eval (op U) :=
  rfl

/-- The defining recursion: the exterior product of `n + 1` generators is the first generator
times the product of the remaining `n`, transported from degree `1 + (n : ℤ)` to degree
`((n + 1 : ℕ) : ℤ)`. -/
theorem exteriorBasisSection_succ (U : Opens ↥X) (n : ℕ) (i : Fin (n + 1) → Fin r) :
    exteriorBasisSection A U (n + 1) i =
      Stacks.degCast (F := fun k : ℤ => ((A.exterior.piece k).val.obj (op U) : Type u))
        (show (1 : ℤ) + (n : ℤ) = ((n + 1 : ℕ) : ℤ) by omega)
        ((A.exterior.mul 1 (n : ℤ)).app (op U) (exteriorGen A U (i 0))
          (exteriorBasisSection A U n fun j => i j.succ)) :=
  rfl

/-- The tautological generators commute with restriction. -/
theorem map_exteriorGen {U V : Opens ↥X} (h : op U ⟶ op V) (k : Fin r) :
    (A.exterior.piece 1).val.map h (exteriorGen A U k) = exteriorGen A V k :=
  Eq.trans
    (PresheafOfModules.naturality_apply A.exteriorGenerator.val h
      ((SheafOfModules.freeSection (ULift.up k)).val (op U))).symm
    (congrArg (PresheafOfModules.Hom.app A.exteriorGenerator.val (op V))
      (PresheafOfModules.sections_property (SheafOfModules.freeSection (ULift.up k)) h))

/-- **The exterior products of tautological generators commute with restriction**, so each of
them is the restriction of the one over the whole space. -/
theorem map_exteriorBasisSection {U V : Opens ↥X} (h : op U ⟶ op V) (n : ℕ)
    (i : Fin n → Fin r) :
    (A.exteriorPower n).val.map h (exteriorBasisSection A U n i) =
      exteriorBasisSection A V n i := by
  rw [exteriorBasisSection, exteriorBasisSection,
    A.exterior.toPresheafGradedAlgebra.homogeneousProdLeft_naturality h n]
  exact congrArg (A.exterior.toPresheafGradedAlgebra.homogeneousProdLeft (op V) n)
    (funext fun j => map_exteriorGen A h (i j))

/-- **The germ of an exterior product of tautological generators is the wedge of their germs.**
This is the degree-`n` exterior clause of Stacks Tag 01CH, read on the sections that index the
Koszul complex of Tag 062K. -/
theorem exteriorPowerStalkEquiv_germ_exteriorBasisSection (n : ℕ) (x : ↥X) (U : Opens ↥X)
    (hx : x ∈ U) (i : Fin n → Fin r) :
    A.exteriorPowerStalkEquiv n x
        (TopCat.Presheaf.germ (A.exteriorPower n).val.presheaf U x hx
          (exteriorBasisSection A U n i)) =
      exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) n
        fun j => TopCat.Presheaf.germ (koszulFreeSheaf Osharp r).val.presheaf U x hx
          ((SheafOfModules.freeSection (ULift.up (i j))).val (op U)) := by
  refine Eq.trans (congrArg (fun z => A.exteriorPowerStalkEquiv n x
    (TopCat.Presheaf.germ (A.exteriorPower n).val.presheaf U x hx z))
    (A.exterior.toPresheafGradedAlgebra.homogeneousProdLeft_eq_homogeneousProd (op U) n
      fun j => exteriorGen A U (i j))) ?_
  exact SheafOfModules.exteriorPowerStalkEquiv_germ_homogeneousProd A.exterior
    A.exteriorGenerator A.exterior_isExteriorAlgebra n x U hx
    fun j => (SheafOfModules.freeSection (ULift.up (i j))).val (op U)

end Stacks.RegularSequence

end
