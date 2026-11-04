module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalPresentationOfPresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafifiedDirectSum
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafUnderlyingModule
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.MultiplicativeTorsor
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionToAlgebraicSpaceInjectives

/-!
# Quasi-coherence of the Laurent algebra of an invertible sheaf on a good algebraic space

In Situation 0EDT let `X/B` be good and let `ℒ` be an invertible `𝒪_X`-module which is trivial on
an étale covering of `X`.  The module underlying the Laurent algebra `⨁_{n ∈ ℤ} ℒ^{⊗ n}` is the
coproduct of the integer tensor powers of `ℒ`, and one covering trivializing `ℒ` trivializes all
of them at once; the Laurent algebra is therefore quasi-coherent, which is the datum its relative
spectrum requires.

## Main definitions

* `AlgebraicGeometry.Space.laurentDirectSumIsoUnderlyingModule`: the module underlying the
  Laurent algebra sheaf of `ℒ` is the sheafification of the objectwise direct sum of the integer
  tensor powers of `ℒ`.
* `AlgebraicGeometry.Space.laurentCoprodIsoUnderlyingModule`: **the module underlying the Laurent
  algebra sheaf of `ℒ` is `⨁_{n ∈ ℤ} ℒ^{⊗ n}`.**

## Main results

* `AlgebraicGeometry.Space.isQuasicoherent_coprod_laurentGradedAlgebra_piece`: **the direct sum
  `⨁_{n ∈ ℤ} ℒ^{⊗ n}` is quasi-coherent.**
* `AlgebraicGeometry.Space.isQuasicoherent_laurentAlgebraSheaf_of_isLocallyTrivial`: **the Laurent
  algebra sheaf of `ℒ` is quasi-coherent.**

## Implementation notes

The identification of the underlying module is assembled from two pieces available for an
arbitrary site: `Stacks.GradedAlgebra.directSumIsoUnderlyingModule`, which presents the module
underlying an ungraded realization as the sheafification of the objectwise direct sum of the
homogeneous pieces, and `Stacks.sheafifyDirectSumIso`, which identifies that sheafification with
the coproduct.  The first produces the module in the spelling
`SheafOfModules.restrictScalars σ (SheafOfModules.unit T)`, and
`AlgebraicGeometry.Space.AlgebraSheaf.underlyingModule_eq_restrictScalars` is what turns that
into `AlgebraicGeometry.Space.AlgebraSheaf.underlyingModule`.

Local injectivity and local surjectivity of the sheafification unit are proved first at the
level of presheaves of commutative rings, for `AlgebraicGeometry.Space.laurentCommUnit`, and
then transported to the presheaves of possibly noncommutative rings that the graded apparatus
consumes: forgetting commutativity changes neither the sections nor therefore the equalizer and
image sieves, so the two `RingCat`-level statements are the `CommRingCat`-level ones verbatim.

Both steps name their instances instead of leaving them to be searched for.  At the
`CommRingCat` level the universe of the sections of the coefficient category is supplied as the
explicit argument `CA` of `CategoryTheory.GrothendieckTopology.W.isLocallyInjective`; left
implicit it is a metavariable, and a candidate instance for
`CategoryTheory.Presheaf.IsLocallyInjective` whose section universe has the form `max u v w`,
with `u` and `v` the universes of the objects and the morphisms of the site and `w` free, then
produces an unsolvable universe constraint, the small étale site of an algebraic space having
its objects one universe above its morphisms and its sections.  At the `RingCat` level the two
local-bijectivity instances are passed positionally to
`CategoryTheory.Presheaf.equalizerSieve_mem` and `CategoryTheory.Presheaf.imageSieve_mem`, so
that no instance in scope can be selected in their place.

Local triviality of `ℒ` is an explicit hypothesis here; it is what Tag 01CL needs, namely one
covering family presenting every summand at once.  It is discharged from invertibility alone in
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.MultiplicativeTorsorOfInvertible`, where the local
ringedness of the small étale site is available.

## References

* [Stacks Project, Tag 0EQG](https://stacks.math.columbia.edu/tag/0EQG)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 01CL](https://stacks.math.columbia.edu/tag/01CL)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1)
    (hL : IsInvertibleSheaf D p hp L)

/-! ### The module underlying the Laurent algebra sheaf -/

/-- The sheafification unit of the ungraded realization of the Laurent algebra of `ℒ`, as a
morphism of presheaves of commutative rings on the small étale site of `X`. -/
def laurentCommUnit :
    laurentCommPresheaf D p hp L hL ⟶
      CategoryTheory.sheafify (SmallEtale.topology D.site D.base D.base_mem X)
        (laurentCommPresheaf D p hp L hL) :=
  CategoryTheory.toSheafify (SmallEtale.topology D.site D.base D.base_mem X)
    (laurentCommPresheaf D p hp L hL)

/-- The sheafification unit of the ungraded realization of the Laurent algebra is locally
injective as a morphism of presheaves of commutative rings: on the small étale site the local
equivalences of presheaves of commutative rings are exactly the locally bijective morphisms. -/
theorem isLocallyInjective_laurentCommUnit :
    Presheaf.IsLocallyInjective (SmallEtale.topology D.site D.base D.base_mem X)
      (laurentCommUnit D p hp L hL) :=
  GrothendieckTopology.W.isLocallyInjective (CA := fun R : CommRingCat.{u} => ToType R)
    ((SmallEtale.topology D.site D.base D.base_mem X).W_toSheafify
      (laurentCommPresheaf D p hp L hL))

/-- The sheafification unit of the ungraded realization of the Laurent algebra is locally
surjective as a morphism of presheaves of commutative rings: on the small étale site the local
equivalences of presheaves of commutative rings are exactly the locally bijective morphisms. -/
theorem isLocallySurjective_laurentCommUnit :
    Presheaf.IsLocallySurjective (SmallEtale.topology D.site D.base D.base_mem X)
      (laurentCommUnit D p hp L hL) :=
  GrothendieckTopology.W.isLocallySurjective (CA := fun R : CommRingCat.{u} => ToType R)
    ((SmallEtale.topology D.site D.base D.base_mem X).W_toSheafify
      (laurentCommPresheaf D p hp L hL))

/-- The sheafification unit of the ungraded realization of the Laurent algebra of `ℒ`, read as a
morphism of presheaves of possibly noncommutative rings into the sections of its algebra
sheaf. -/
def laurentRingUnit :
    (laurentGradedAlgebra D p hp L hL).toPresheafGradedAlgebra.totalPresheaf ⟶
      (AlgebraSheaf.ringSheafOfSite (laurentAlgebraSheaf D p hp L hL)).obj :=
  Functor.whiskerRight (laurentCommUnit D p hp L hL) (forget₂ CommRingCat.{u} RingCat.{u})

/-- The sheafification unit of the ungraded realization of the Laurent algebra is compatible
with the structure map of the graded algebra and the structure morphism of its algebra sheaf. -/
theorem structureHom_comp_laurentRingUnit :
    (laurentGradedAlgebra D p hp L hL).toPresheafGradedAlgebra.structureHom ≫
        laurentRingUnit D p hp L hL =
      (AlgebraSheaf.structureMapOfSite (laurentAlgebraSheaf D p hp L hL)).hom :=
  rfl

/-- The sheafification unit of the ungraded realization of the Laurent algebra is locally
injective. -/
theorem isLocallyInjective_laurentRingUnit :
    Presheaf.IsLocallyInjective (SmallEtale.topology D.site D.base D.base_mem X)
      (laurentRingUnit D p hp L hL) where
  equalizerSieve_mem x y h :=
    @Presheaf.equalizerSieve_mem _ _ _ _ _ _ _ _
      (SmallEtale.topology D.site D.base D.base_mem X) _ _ (laurentCommUnit D p hp L hL)
      (isLocallyInjective_laurentCommUnit D p hp L hL) _ x y h

/-- The sheafification unit of the ungraded realization of the Laurent algebra is locally
surjective. -/
theorem isLocallySurjective_laurentRingUnit :
    Presheaf.IsLocallySurjective (SmallEtale.topology D.site D.base D.base_mem X)
      (laurentRingUnit D p hp L hL) where
  imageSieve_mem s :=
    @Presheaf.imageSieve_mem _ _ (SmallEtale.topology D.site D.base D.base_mem X)
      _ _ _ _ _ _ _ _ (laurentCommUnit D p hp L hL)
      (isLocallySurjective_laurentCommUnit D p hp L hL) _ s

/-- The module underlying the Laurent algebra sheaf of `ℒ` is the sheafification of the
objectwise direct sum of the integer tensor powers of `ℒ`. -/
def laurentDirectSumIsoUnderlyingModule :
    ((PresheafOfModules.sheafification (𝟙 (tensorStructureSheaf D p hp).obj) :
          PresheafOfModules.{u} (tensorStructureSheaf D p hp).obj ⥤
            SheafOfModules.{u} (tensorStructureSheaf D p hp)).obj
        (Stacks.directSum fun n : ℤ => ((laurentGradedAlgebra D p hp L hL).piece n).val)) ≅
      AlgebraSheaf.underlyingModule (laurentAlgebraSheaf D p hp L hL) :=
  Stacks.GradedAlgebra.directSumIsoUnderlyingModule
      (laurentGradedAlgebra D p hp L hL).toPresheafGradedAlgebra
      (AlgebraSheaf.structureMapOfSite (laurentAlgebraSheaf D p hp L hL))
      (laurentRingUnit D p hp L hL) (structureHom_comp_laurentRingUnit D p hp L hL)
      (isLocallyInjective_laurentRingUnit D p hp L hL)
      (isLocallySurjective_laurentRingUnit D p hp L hL) ≪≫
    eqToIso (AlgebraSheaf.underlyingModule_eq_restrictScalars
      (laurentAlgebraSheaf D p hp L hL)).symm

/-- **The module underlying the Laurent algebra sheaf of `ℒ` is `⨁_{n ∈ ℤ} ℒ^{⊗ n}`**, the
coproduct of the integer tensor powers of `ℒ`. -/
def laurentCoprodIsoUnderlyingModule :
    (∐ fun n : ℤ => (laurentGradedAlgebra D p hp L hL).piece n) ≅
      AlgebraSheaf.underlyingModule (laurentAlgebraSheaf D p hp L hL) :=
  (Stacks.sheafifyDirectSumIso fun n : ℤ => (laurentGradedAlgebra D p hp L hL).piece n).symm ≪≫
    laurentDirectSumIsoUnderlyingModule D p hp L hL

/-! ### Quasi-coherence -/

variable (hLT : Stacks.SheafOfModules.Invertible.IsLocallyTrivial
  (R := tensorStructureSheaf D p hp) L)

include hLT in
/-- **The direct sum `⨁_{n ∈ ℤ} ℒ^{⊗ n}` of the integer tensor powers of an invertible
`𝒪_X`-module trivial on an étale covering of `X` is quasi-coherent**: a chart trivializing `ℒ`
trivializes every tensor power of `ℒ` at once, which is the uniformity of the covering family
that Tag 01CL requires. -/
theorem isQuasicoherent_coprod_laurentGradedAlgebra_piece :
    (∐ fun n : ℤ => (laurentGradedAlgebra D p hp L hL).piece n).IsQuasicoherent := by
  have : HasBinaryProducts (SmallEtale D.site D.base D.base_mem X) :=
    SmallEtale.instHasBinaryProducts D.site D.base D.base_mem X
  have : Stacks.SheafOfModules.IsInvertible (tensorStructureRingPresheaf D p hp)
      (isSheaf_tensorStructureRingPresheaf D p hp) L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hL
  have := hLT
  exact Stacks.SheafOfModules.TensorPower.isQuasicoherent_coprod_tensorPower
    (tensorStructureRingPresheaf D p hp) (isSheaf_tensorStructureRingPresheaf D p hp) L

include hLT in
/-- **The Laurent algebra sheaf of an invertible `𝒪_X`-module trivial on an étale covering of `X`
is quasi-coherent**, its underlying module being `⨁_{n ∈ ℤ} ℒ^{⊗ n}`. -/
theorem isQuasicoherent_laurentAlgebraSheaf_of_isLocallyTrivial :
    AlgebraSheaf.IsQuasicoherent (laurentAlgebraSheaf D p hp L hL) :=
  have : (AlgebraSheaf.underlyingModule (laurentAlgebraSheaf D p hp L hL)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (tensorStructureSheaf D p hp)).prop_of_iso
      (laurentCoprodIsoUnderlyingModule D p hp L hL)
      (isQuasicoherent_coprod_laurentGradedAlgebra_piece D p hp L hL hLT)
  SheafOfModules.IsQuasicoherentOnSite.of_isQuasicoherent _

end AlgebraicGeometry.Space

end
