module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.FactorizationThroughAnAuxiliaryTopos
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExistenceOnARingedSite

/-!
# The derived tensor product over the inverse image of a structure sheaf

Let `f : (Sh(C), O) ⟶ (Sh(C'), O')` be a morphism of ringed topoi.  The inverse image
`f⁻¹O'` of the target structure sheaf is a sheaf of commutative rings on the site of the
source, so the pair `(C, f⁻¹O')` is a ringed site like any other and the derived tensor
product of sheaves of `f⁻¹O'`-modules is an instance of the derived tensor product on a
ringed site.  No new derived bifunctor is needed in order to write `- ⊗^L_{f⁻¹O'} -`.

The same remark applies to the two halves of the factorization

`X --h--> X' --g--> Y`,  `X' = (C, f⁻¹O')`,

of `StacksPullbackFactorization`: `g^*` is the inverse image of modules with no change of
rings, so it is the functor written `f⁻¹` on modules, and `h^*` and `h_*` are extension and
restriction of scalars along `f⁻¹O' ⟶ O`.  Both of those identifications hold by `rfl`.

## Main definitions

* `Stacks.Cohomology.MixedDerivedTensor.structureMapOfInvRing`: the structure map in its
  inverse-image form `f⁻¹O' ⟶ O`, read on the sheaves of rings over which the sheaves of
  modules are indexed.
* `Stacks.Cohomology.MixedDerivedTensor.restrictToInvRing`: an `O`-module read as an
  `f⁻¹O'`-module.
* `Stacks.Cohomology.MixedDerivedTensor.inverseImageModules`: `f⁻¹` on sheaves of modules,
  from `O'`-modules to `f⁻¹O'`-modules.
* `Stacks.Cohomology.MixedDerivedTensor.derivedTensorInvRing`: the derived tensor product of
  sheaves of `f⁻¹O'`-modules, with its K-flat comparisons and exactness in both variables.
* `Stacks.Cohomology.MixedDerivedTensor.derivedTensorInvRingFunctor`: its bifunctor
  `D(f⁻¹O') ⥤ D(f⁻¹O') ⥤ D(f⁻¹O')`, which is what `- ⊗^L_{f⁻¹O'} -` denotes.

## Main results

* `Stacks.Cohomology.MixedDerivedTensor.ringSheaf_auxTopos`: the sheaf of rings over which
  the modules of the auxiliary ringed topos are indexed is the one over which the derived
  tensor product on the ringed site `(C, f⁻¹O')` is indexed, by `rfl`.  This is what makes
  the derived tensor product of the ringed site and the modules of the factorization speak
  about the same category.
* `Stacks.Cohomology.MixedDerivedTensor.pushforwardTopos_auxHomH`: `h_*` is restriction of
  scalars along `f⁻¹O' ⟶ O`, by `rfl`.
* `Stacks.Cohomology.MixedDerivedTensor.extendRestrictAdjunctionOfInvRing`: consequently the
  adjunction `h^* ⊣ h_*` of the factorization *is* the change-of-rings adjunction
  `extendScalars ⊣ restrictScalars` along `f⁻¹O' ⟶ O`.

## Implementation notes

The existence of the derived tensor product over `f⁻¹O'` costs nothing beyond instantiating
`Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct` at the sheaf of rings
`f⁻¹O'`: that existence statement is unconditional in the sheaf of commutative rings, and the
site of `X'` is the site of `X`, so every hypothesis on the site is the one already present
for `X`.  The three instance arguments on the ordinary tensor product of sheaves of modules
and the choice of a derived category are carried as hypotheses, exactly as they are carried by
the existence statement itself.

`Stacks.SheafOfModules.Tensor.ringSheaf` supplies its own `HasSheafCompose` instance by a
`letI`, while `AlgebraicGeometry.RingedTopos.ringSheaf` takes one from the context.  The two
resulting sheaves of rings have the same underlying presheaf and their sheaf conditions are
proofs of one proposition, so `ringSheaf_auxTopos` is `rfl` and nothing has to be transported
between the two spellings.

**Universes.**  Everything is at `AlgebraicGeometry.RingedTopos.{u, u, u}`, with the site
small in the universe of the sections of the structure sheaves.  This narrowing is inherited
rather than chosen here: it is forced both by `StacksPullbackFactorization` and by
`Stacks.DerivedTensor.RingedSite.exists_derivedTensorProduct`, whose own implementation notes
record that the existence of K-flat resolutions pins the ring universe to the hom universe of
the site.  The hom universe of the derived category stays independent, as
`HasDerivedCategory.{d}`.

**No tag is placed in this file.**  The derived tensor product constructed here is the one of
Stacks 06YU, tagged where it is built, read at a particular sheaf of rings; the
identifications of the two halves of the factorization are those of
`StacksPullbackFactorization`.  Nothing here asserts a statement of the source that is not
already asserted elsewhere.

## References

* [The Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [The Stacks Project, Tag 08I6](https://stacks.math.columbia.edu/tag/08I6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u d

namespace Stacks.Cohomology.MixedDerivedTensor

open StacksPullbackFactorization

attribute [local instance]
  AlgebraicGeometry.SheafOfModules.isRightAdjoint_sheafPushforwardContinuous_commRingCat

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The sheaf of rings over which the sheaves of modules of the auxiliary ringed topos
`X' = (C, f⁻¹O')` are indexed is the sheaf of rings over which the derived tensor product on
the ringed site `(C, f⁻¹O')` is indexed.

Both are the image of `f⁻¹O'` under `CategoryTheory.sheafCompose` along
`forget₂ CommRingCat RingCat`; they differ only in where the instance witnessing that the
composition is again a sheaf comes from, and the sheaf condition is a proposition. -/
theorem ringSheaf_auxTopos (f : AlgebraicGeometry.RingedToposSiteHom X Y) :
    (Stacks.SheafOfModules.Tensor.ringSheaf (auxTopos f).O) =
      Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (invRing f) :=
  rfl

/-- The structure map of `f` in its inverse-image form `f⁻¹O' ⟶ O`, read as a morphism of the
sheaves of rings over which the sheaves of modules are indexed.  This is the structure map of
the ring-theoretic half `h` of the factorization; pushforward along the identity functor of
the site is the identity on the nose, so no comparison isomorphism intervenes. -/
def structureMapOfInvRing (f : AlgebraicGeometry.RingedToposSiteHom X Y) :
    (Stacks.SheafOfModules.Tensor.ringSheaf (auxTopos f).O) ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  (auxHomH f).fSharpRing

/-- An `O`-module read as an `f⁻¹O'`-module, by restriction of scalars along `f⁻¹O' ⟶ O`.
This is the functor under which the left-hand factor of Stacks 08I6 is read on the right-hand
side of that tag. -/
abbrev restrictToInvRing (f : AlgebraicGeometry.RingedToposSiteHom X Y) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (auxTopos f).O) :=
  SheafOfModules.restrictScalars.{u} (structureMapOfInvRing f)

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **`h_*` is restriction of scalars along `f⁻¹O' ⟶ O`.**  The underlying continuous functor
of `h` is the identity, and pushforward of sheaves of modules along the identity functor is
restriction of scalars, so this is `rfl`. -/
theorem pushforwardTopos_auxHomH (f : AlgebraicGeometry.RingedToposSiteHom X Y) :
    (auxHomH f).pushforwardTopos = restrictToInvRing f :=
  rfl

/-- **The adjunction `h^* ⊣ h_*` of the factorization is the change-of-rings adjunction.**
Its left adjoint is extension of scalars along `f⁻¹O' ⟶ O`
(`StacksPullbackFactorization.pullbackTopos_auxHomH`) and its right adjoint is restriction of
scalars along the same morphism (`pushforwardTopos_auxHomH`). -/
def extendRestrictAdjunctionOfInvRing (f : AlgebraicGeometry.RingedToposSiteHom X Y) :
    Stacks.Sheaves.ModuleAdjunction.extendScalars.{u} (structureMapOfInvRing f) ⊣
      restrictToInvRing f :=
  Stacks.Sheaves.ModuleAdjunction.extendRestrictScalarsAdjunction.{u} (structureMapOfInvRing f)

/-- **`f⁻¹` on sheaves of modules**, from `O'`-modules to `f⁻¹O'`-modules: the geometric half
`g^*` of the factorization, which changes no rings.  Composed with extension of scalars along
`f⁻¹O' ⟶ O` it is `f^*`, which is
`StacksPullbackFactorization.pullbackFactorIso`. -/
abbrev inverseImageModules (f : AlgebraicGeometry.RingedToposSiteHom X Y) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (auxTopos f).O) :=
  (auxHomG f).pullbackTopos

section DerivedTensor

variable (f : AlgebraicGeometry.RingedToposSiteHom X Y)
  [HasDerivedCategory.{d} (Stacks.DerivedTensor.RingedSite.Modules (invRing f))]
  [(Stacks.SheafOfModules.Tensor.sheafTensor (invRing f)).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor (invRing f)).obj M).Additive]
  [∀ (K L : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules (invRing f)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (invRing f)) (ComplexShape.up ℤ)]

/-- **The derived tensor product of sheaves of `f⁻¹O'`-modules**, with its canonical map to
the ordinary total tensor product, its one-sided K-flat comparisons, and exactness in both
variables.

This is Stacks 06YU at the ringed site `(C, f⁻¹O')`.  Nothing is constructed here: the
inverse image of the structure sheaf of the target is a sheaf of commutative rings on the
site of the source, and the existence of the derived tensor product on a ringed site is
unconditional in that sheaf. -/
def derivedTensorInvRing : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct (invRing f) :=
  Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct (invRing f)

/-- The bifunctor `- ⊗^L_{f⁻¹O'} -` on the unbounded derived category of sheaves of
`f⁻¹O'`-modules. -/
abbrev derivedTensorInvRingFunctor := (derivedTensorInvRing f).tensor

end DerivedTensor

end Stacks.Cohomology.MixedDerivedTensor

end
