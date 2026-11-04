module

public import StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic
public import StacksFrontier.Topology.Sheaves.Modules.StalkTensor
public import StacksFrontier.Algebra.Homology.KFlat
public import StacksFrontier.Homology.KFlat.Bifunctor
public import StacksFrontier.Topology.Sheaves.RingedSpace.OfSheaf

/-!
# The stalk criterion for K-flatness: its statement

Let `X` be a topological space and `R` a sheaf of commutative rings on the site of open
subsets of `X`. The stalk criterion for K-flatness (Stacks 06YB) says that a cochain complex
`K` of sheaves of `R`-modules is K-flat exactly when, for every `x : X`, the complex `K_x` of
modules over the stalk ring `R_x` is K-flat in the sense of Stacks 06XZ.

This file makes that biconditional *writable* and supplies the two identifications its two
sides need. Each of the three declarations removes a definite obstruction:

* **Universes.** `Stacks.SheafOfModules.Tensor.ringSheaf` and
  `Stacks.SheafOfModules.Tensor.sheafTensor` take the universe
  of their sheaf of commutative rings in the shape `max (max u₁ u₂) u₃`, where `u₁` and `u₂`
  are the object and morphism universes of the site. Applying either to a sheaf on
  `Opens X` for `X : TopCat.{u}` therefore asks the elaborator to solve
  `max (max u₁ u₂) u₃ =?= u` with all three unknown, which is *stuck* rather than failing:
  neither side can make progress and elaboration aborts. `stalkComplex` and
  `KFlatStalkwise` below pin all three to `u`, which is the unique solution up to the
  normalisation `max u u = u`, and with that pinning both sides of the criterion elaborate.

* **The ring of scalars on the right.** The stalk ring that
  `AlgebraicGeometry.SheafOfModules.stalkFunctor` takes its modules over is the
  `RingCat`-valued stalk, which carries only a `Ring` instance, while `CochainComplex.KFlat`
  requires a commutative one. `StacksDraft.StalkTensor.commRing_stalk_ringSheaf` supplies it,
  and `stalkComplex` is stated so that it is the instance found.

* **The tensor product on the right.** `CochainComplex.KFlat` is phrased with the monoidal
  product of complexes of modules, whereas the stalk of a total tensor complex is produced by
  the bifunctor machinery of `CochainComplex.KFlatBifunctor`. `kFlat_iff_kFlatBifunctor`
  identifies the two; it is `Iff.rfl`, the monoidal product of complexes being by definition
  the bifunctor total complex of the curried tensor.

* **The tensor product on the left.** Stacks 01CB — the stalk of a tensor product of sheaves
  of modules is the tensor product of the stalks — is proved in
    `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso`
  over a `AlgebraicGeometry.RingedSpace`, whose structure sheaf has type
  `TopCat.Sheaf CommRingCat`, while the criterion is phrased over a sheaf on
  `Opens.grothendieckTopology X`. `ringedSpaceOfSheaf` passes between the two, and
  `structureSheafRing_ringedSpaceOfSheaf` records that the passage is the identity on the
  underlying sheaf of rings.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.ringedSpaceOfSheaf`: the ringed space whose structure
  sheaf is a given sheaf of commutative rings on the site of opens.
* `AlgebraicGeometry.SheafOfModules.stalkComplex`: the complex of modules over the stalk ring
  obtained by taking stalks at a point in each degree.
* `AlgebraicGeometry.SheafOfModules.KFlatStalkwise`: the right-hand side of the stalk
  criterion.

## Main results

* `AlgebraicGeometry.SheafOfModules.structureSheafRing_ringedSpaceOfSheaf`: the two
  developments' sheaves of rings agree definitionally.
* `CochainComplex.kFlat_iff_kFlatBifunctor`: K-flatness of a complex of modules over a
  commutative ring is bifunctor-relative K-flatness at the curried tensor product.

## Implementation notes

`ringedSpaceOfSheaf` is a `def` and not an `abbrev`: `AlgebraicGeometry.RingedSpace` is a
structure, and the only thing wanted of it is that its three projections are the given data,
which they are by `rfl` and which `structureSheafRing_ringedSpaceOfSheaf` records. Making it
reducible would expose `TopCat.Sheaf`, a `def` over `CategoryTheory.Sheaf` whose universes are
`max`-shaped, to instance search at the site spelling, and a class keyed on one of the two
spellings gets stuck on `max ?u ?v =?= u` rather than failing when the other is wanted — which
aborts synthesis for both.

`stalkComplex` is the ordinary topological stalk complex, formed by
`AlgebraicGeometry.SheafOfModules.stalkFunctor` degreewise. That shape is dictated by its
consumers: `acyclic_iff_forall_stalk_acyclic`, which tests acyclicity of a complex of sheaves
of modules stalkwise over the stalk ring, and `stalkTotalComplexIso`, which carries a total
complex through the stalk functor, are both stated with
`(stalkFunctor _ x).mapHomologicalComplex (ComplexShape.up ℤ)`, and both directions of the
criterion are consumed through those two. Applying the stalk functor degreewise at all needs
it to be additive, which is `stalkFunctor_additive` and is not synthesizable.

## References

* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 06XZ](https://stacks.math.columbia.edu/tag/06XZ)
* [Stacks Project, Tag 06YB](https://stacks.math.columbia.edu/tag/06YB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

noncomputable section

namespace CochainComplex

variable {R : Type u} [CommRing R]

/-- **K-flatness of a complex of modules is bifunctor-relative K-flatness at the tensor
product.** `CochainComplex.KFlat` (Stacks 06XZ) asks that `Tot(M ⊗_R K)` be acyclic for every
acyclic `M`, with `⊗` the monoidal product of complexes of `R`-modules;
`CochainComplex.KFlatBifunctor.KFlat` asks the same of the total complex of a bifunctor. The
two agree at the curried tensor product, by definition: the monoidal product of complexes
*is* the bifunctor total complex of the curried tensor, with the same Koszul signs.

This is what lets the right-hand side of the stalk criterion for K-flatness (Stacks 06YB),
which speaks of `CochainComplex.KFlat` over the stalk ring, be fed to the bifunctor machinery
through which the stalk of a total tensor complex is computed. -/
theorem kFlat_iff_kFlatBifunctor (K : CochainComplex (ModuleCat.{max u v} R) ℤ) :
    letI := ModuleCat.liftedModuleMonoidalStruct.{u, v} (R := R)
    letI := ModuleCat.liftedModuleMonoidal.{u, v} (R := R)
    KFlat.{u, v} K ↔
      KFlatBifunctor.KFlat (MonoidalCategory.curriedTensor (ModuleCat.{max u v} R)) K :=
  Iff.rfl

end CochainComplex

namespace AlgebraicGeometry.SheafOfModules

variable {X : TopCat.{u}}
  (R : CategoryTheory.Sheaf.{u, u, u, u + 1} (Opens.grothendieckTopology X) CommRingCat.{u})


/-- The sheaf of rings of the ringed space `ringedSpaceOfSheaf R`, as named by the Stacks 01CB
development, is the sheaf of rings of the ringed site `(Opens X, R)`, as named by the
Stacks 06YM development.

Consequently `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso` — the canonical
  isomorphism
`(F ⊗_R G)_x ≅ F_x ⊗_{R_x} G_x` of Stacks 01CB, natural in both variables by
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso_natural` — is already a statement
  about sheaves of modules over
`Stacks.SheafOfModules.Tensor.ringSheaf R`, hence about the tensor product
`Stacks.SheafOfModules.Tensor.sheafTensor R` over which K-flatness is defined. -/
theorem structureSheafRing_ringedSpaceOfSheaf :
    structureSheafRing (ringedSpaceOfSheaf R) =
      Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R :=
  rfl

/-- **The stalk complex of a complex of sheaves of modules.** Taking stalks at `x` in each
degree carries a cochain complex of sheaves of `R`-modules to a cochain complex of modules
over the stalk ring `R_x`. This is `K_x^•` in the statement of the stalk criterion for
K-flatness (Stacks 06YB).

The stalk ring here is the `RingCat`-valued stalk of the underlying sheaf of rings, which is
the ring `AlgebraicGeometry.SheafOfModules.stalkFunctor` takes its modules over; it is
commutative by `StacksDraft.StalkTensor.commRing_stalk_ringSheaf`. -/
def stalkComplex (x : X)
    (K : CochainComplex (SheafOfModules.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
      u} R)) ℤ) :
    CochainComplex (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u})
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R).obj x)) ℤ := by
  letI : (stalkFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).Additive :=
    stalkFunctor_additive (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
  exact
    ((stalkFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K

/-- **The right-hand side of the stalk criterion for K-flatness (Stacks 06YB):** at every
point of `X`, the complex of modules over the stalk ring obtained by taking stalks degreewise
is K-flat in the sense of Stacks 06XZ. -/
def KFlatStalkwise
    (K : CochainComplex (SheafOfModules.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
      u} R)) ℤ) :
    Prop :=
  ∀ x : X, CochainComplex.KFlat.{u, u} (stalkComplex R x K)

end AlgebraicGeometry.SheafOfModules

end

end
