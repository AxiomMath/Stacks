module

public import StacksFrontier.AlgebraicGeometry.NormInvertible.Cocycle

/-!
# Reindexing a unit transition cocycle

A unit transition cocycle is indexed by a family of opens `U : ι → Opens X`. Renaming the
indices along an equivalence `e : ι' ≃ ι` produces a cocycle for the family `U ∘ e`, and the two
cocycles glue to isomorphic sheaves of modules: a compatible family of local coordinates for one
is a compatible family for the other, read at the renamed index, and that renaming is already
`𝒪_X(W)`-linear and already commutes with restriction.

[Stacks, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY) omits the verification that the norm
construction is well defined, and this is one part of it, needed together with
`Stacks.SheafOfModules.UnitTransitionCocycle.glueIsoOfCoboundaryTwist` and for the same reason.
`Stacks.Divisors.normTransitionCocycle f N L` is indexed by `Stacks.Divisors.NormChart f L`, the
subtype of target opens over which `L` becomes trivial upstairs — so the index *type* depends on
`L`. For two isomorphic modules `L ≅ M` the two index types are different types carrying the same
opens, and the chart trivializations are independently chosen with `Classical.choice`. Comparing
`normInvertible f N L` with `normInvertible f N M` therefore needs both halves: the reindexing here
moves `M`'s cocycle onto `L`'s index type over the literally equal family of opens, and the
coboundary twist then absorbs the difference between the two choices of trivialization.

## Main definitions

* `Stacks.SheafOfModules.UnitTransitionCocycle.reindex`: the cocycle for `U ∘ e`.
* `Stacks.SheafOfModules.UnitTransitionCocycle.reindexPullHom` and
  `Stacks.SheafOfModules.UnitTransitionCocycle.reindexSectionsEquiv`: renaming the coordinates of
  a compatible family, as a linear map and as a linear equivalence.

## Main results

* `Stacks.SheafOfModules.UnitTransitionCocycle.reindex_cover`: the reindexed family covers
  whatever the original family covers.
* `Stacks.SheafOfModules.UnitTransitionCocycle.reindexSectionsEquiv_sectionsMap`: the renaming
  commutes with restriction.
* `Stacks.SheafOfModules.UnitTransitionCocycle.glueReindexIso`: **a cocycle and its reindexing
  glue to isomorphic sheaves of modules.**
* `Stacks.SheafOfModules.UnitTransitionCocycle.chartLinearEquiv_glueReindexIso`: the isomorphism
  carries the `e i'`-th chart coordinate to the `i'`-th, which is what pins it down.

## Implementation notes

No `@[stacks]` attribute is placed. Tag 0BCY asserts the whole norm construction including the
Picard-group homomorphism, and this file is one ingredient of its well-definedness clause.

The reindexed cocycle is stated for the family `U ∘ e` rather than for an arbitrary family `U'`
together with a hypothesis `∀ i', U' (e i') = U i`. The second shape would make the family appear
in the type only up to a propositional equality of opens, and every statement about sections
would then have to be transported along `X.presheaf.map (eqToHom _)`. With `U ∘ e` the
index-level equation `(U ∘ e) i' = U (e i')` holds by `rfl`, so the whole file needs no transport
at all: both `reindexPullHom`'s membership proof and `chartLinearEquiv_glueReindexIso` are the
original facts read at the renamed index. A caller whose two families are not literally composite
— `Subtype.val` on two subtypes of `Opens X` with equivalent predicates, which is the case of the
norm construction — gets them identified by `funext`, the pointwise equality holding by `rfl`.

Only the inverse of the renaming needs a transport, because `e (e.symm i)` is not `i`: it is
`Equiv.piCongrLeft`, and `reindexSectionsEquiv` is built by `LinearEquiv.ofBijective` so that the
*forward* map stays the plain renaming and the transport never appears in a consumer.

## References

* [Stacks Project, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.SheafOfModules.UnitTransitionCocycle

attribute [local instance] sectionsProductModule

variable {X : RingedSpace.{u, u}} {ι ι' : Type u} {U : ι → Opens X.carrier}

/-! ### The reindexed cocycle -/

/-- Renaming the indices of a unit transition cocycle along an equivalence `e : ι' ≃ ι`. All four
laws are the original laws at the renamed indices. -/
def reindex (D : UnitTransitionCocycle X U) (e : ι' ≃ ι) :
    UnitTransitionCocycle X (U ∘ e) where
  transition i j V hi hj := D.transition (e i) (e j) V hi hj
  restrict hi hj h := D.restrict hi hj h
  symm i j V hi hj := D.symm (e i) (e j) V hi hj
  cocycle i j k V hi hj hk := D.cocycle (e i) (e j) (e k) V hi hj hk

/-- The transition units of the reindexed cocycle are the original ones at the renamed indices. -/
@[simp]
theorem reindex_transition (D : UnitTransitionCocycle X U) (e : ι' ≃ ι) (i j : ι')
    (V : Opens X.carrier) (hi : V ≤ (U ∘ e) i) (hj : V ≤ (U ∘ e) j) :
    (D.reindex e).transition i j V hi hj = D.transition (e i) (e j) V hi hj :=
  rfl

/-- The reindexed family covers whatever the original family covers. -/
theorem reindex_cover (e : ι' ≃ ι) {V : Opens X.carrier} (hU : V ≤ ⨆ i, U i) :
    V ≤ ⨆ i, (U ∘ e) i :=
  hU.trans e.iSup_comp.ge

/-! ### Renaming the coordinates of a compatible family -/

section

variable (D : UnitTransitionCocycle X U) (e : ι' ≃ ι)

/-- Renaming the coordinates of a compatible family of local coordinates, as a linear map. The
`i'`-th coordinate of the renamed family is the `e i'`-th coordinate of the original, and the
compatibility condition at `(i', j')` is the original condition at `(e i', e j')`. -/
def reindexPullHom (W : Opens X.carrier) :
    D.sectionsSubmodule W →ₗ[X.presheaf.obj (op W)] (D.reindex e).sectionsSubmodule W where
  toFun s := ⟨fun i => s.val (e i), fun i j => s.property (e i) (e j)⟩
  map_add' _ _ := Subtype.ext (funext fun _ => rfl)
  map_smul' _ _ := Subtype.ext (funext fun _ => rfl)

/-- The `i'`-th coordinate of the renamed family is the `e i'`-th coordinate of the original. -/
@[simp]
theorem reindexPullHom_val (W : Opens X.carrier) (s : D.sectionsSubmodule W) (i : ι') :
    (D.reindexPullHom e W s).val i = s.val (e i) :=
  rfl

/-- Renaming the coordinates of a compatible family is injective. -/
theorem reindexPullHom_injective (W : Opens X.carrier) :
    Function.Injective (D.reindexPullHom e W) := fun _ _ h =>
  Subtype.ext (funext (e.surjective.forall.mpr fun i => congrFun (congrArg Subtype.val h) i))

/-- Renaming the coordinates of a compatible family is surjective: the preimage of a family is
its transport along `Equiv.piCongrLeft`. -/
theorem reindexPullHom_surjective (W : Opens X.carrier) :
    Function.Surjective (D.reindexPullHom e W) := by
  intro t
  set s : ∀ i, X.presheaf.obj (op (W ⊓ U i)) :=
    Equiv.piCongrLeft (fun i => X.presheaf.obj (op (W ⊓ U i))) e t.val with hs
  have hval : ∀ i : ι', s (e i) = t.val i := fun i =>
    Equiv.piCongrLeft_apply_apply (fun i => X.presheaf.obj (op (W ⊓ U i))) e t.val i
  have hmem : s ∈ D.sectionsSubmodule W := by
    refine e.surjective.forall.mpr fun i => e.surjective.forall.mpr fun j => ?_
    have := t.property i j
    rw [← hval i, ← hval j] at this
    exact this
  exact ⟨⟨s, hmem⟩, Subtype.ext (funext fun i => hval i)⟩

/-- Renaming the coordinates of a compatible family of local coordinates, as a linear
equivalence. -/
noncomputable def reindexSectionsEquiv (W : Opens X.carrier) :
    D.sectionsSubmodule W ≃ₗ[X.presheaf.obj (op W)] (D.reindex e).sectionsSubmodule W :=
  LinearEquiv.ofBijective (D.reindexPullHom e W)
    ⟨D.reindexPullHom_injective e W, D.reindexPullHom_surjective e W⟩

/-- The `i'`-th coordinate of the renamed family is the `e i'`-th coordinate of the original. -/
@[simp]
theorem reindexSectionsEquiv_val (W : Opens X.carrier) (s : D.sectionsSubmodule W) (i : ι') :
    (D.reindexSectionsEquiv e W s).val i = s.val (e i) :=
  rfl

/-- The renaming commutes with restriction of compatible families. -/
theorem reindexSectionsEquiv_sectionsMap {W W' : Opens X.carrier} (k : W' ≤ W)
    (s : D.sectionsSubmodule W) :
    D.reindexSectionsEquiv e W' (D.sectionsMap k s) =
      (D.reindex e).sectionsMap k (D.reindexSectionsEquiv e W s) := by
  refine Subtype.ext (funext fun i => ?_)
  rw [reindexSectionsEquiv_val, sectionsMap_val, sectionsMap_val, reindexSectionsEquiv_val]

/-- **A unit cocycle and its reindexing glue to isomorphic sheaves of modules.** -/
noncomputable def glueReindexIso : D.glue ≅ (D.reindex e).glue :=
  (_root_.SheafOfModules.fullyFaithfulForget (structureSheaf X.sheaf)).preimageIso <|
    PresheafOfModules.isoMk (fun V => (D.reindexSectionsEquiv e V.unop).toModuleIso)
      fun _ _ g => ModuleCat.hom_ext <| LinearMap.ext fun s =>
        D.reindexSectionsEquiv_sectionsMap e g.unop.le s

/-- The gluing isomorphism carries the `e i'`-th chart coordinate to the `i'`-th. Together with
`chartLinearEquiv` this pins the isomorphism down. -/
theorem chartLinearEquiv_glueReindexIso (i : ι') {V : Opens X.carrier} (hV : V ≤ U (e i))
    (s : D.sectionsSubmodule V) :
    (D.reindex e).chartLinearEquiv i hV ((D.glueReindexIso e).hom.val.app (op V) s) =
      D.chartLinearEquiv (e i) hV s :=
  rfl

end

end Stacks.SheafOfModules.UnitTransitionCocycle

end
