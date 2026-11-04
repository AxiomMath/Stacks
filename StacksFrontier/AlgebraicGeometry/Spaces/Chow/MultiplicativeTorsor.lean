module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LaurentAlgebra
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EffectiveCartierIntersection
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecDirectImage

/-!
# The multiplicative torsor of an invertible sheaf on a good algebraic space

In Situation 0EDT let `X/B` be good and let `ℒ` be an invertible `𝒪_X`-module.  The integer
tensor powers of `ℒ` assemble into the `ℤ`-graded Laurent algebra `⨁_{n ∈ ℤ} ℒ^{⊗ n}`, whose
relative spectrum `q : T ⟶ X` is the punctured total space of `ℒ`: étale-locally where `ℒ` is
trivial it is the projection `𝐆_m × U ⟶ U`.  This file builds that algebra on the small étale
site of `X`, forms `T` and `q` as its relative spectrum, and records the base change of a
relative spectrum as an algebraic space affine over the new base.

## Main definitions

* `AlgebraicGeometry.Space.relativeSpecBaseChangeAffineIso`:
  `Y ×_X \underline{Spec}_X(A) ≅ \underline{Spec}_Y(g^* A)` as algebraic spaces affine over `Y`.
* `AlgebraicGeometry.Space.laurentGradedAlgebra`: the `ℤ`-graded Laurent algebra
  `⨁_{n ∈ ℤ} ℒ^{⊗ n}` of an invertible sheaf on the small étale site of `X`.
* `AlgebraicGeometry.Space.laurentAlgebraSheaf`: its ungraded realization, as a sheaf of
  commutative `𝒪_X`-algebras.
* `AlgebraicGeometry.Space.multiplicativeTorsor`: **the algebraic space
  `T = \underline{Spec}_X(⨁_{n ∈ ℤ} ℒ^{⊗ n})`, affine over `X`**, and
  `AlgebraicGeometry.Space.multiplicativeTorsorProjection` its structure morphism `q : T ⟶ X`.

## Main results

* `AlgebraicGeometry.Space.laurentGradedAlgebra_mul_comm`: homogeneous multiplication in the
  Laurent algebra commutes, which is what makes its ungraded realization a sheaf of commutative
  rings and hence the algebra of a relative spectrum.

## Implementation notes

The Laurent algebra is `Stacks.SheafOfModules.TensorPower.laurentAlgebra` of Tag 01CU,
instantiated at the structure sheaf of `X`.  Its base is given by the pair consisting of
`(AlgebraicGeometry.Space.smallEtaleRingedSite …).O.obj` and the sheaf condition
`(AlgebraicGeometry.Space.structureRingSheaf …).property`, which is the pair
`AlgebraicGeometry.Space.IsInvertibleSheaf` is stated at; sheaf conditions are propositions, so
that pair determines the sheaf of rings over which `ℒ` is a module on the nose.

Invertibility of a sheaf of modules is formalized twice in this library, as
`Stacks.SheafOfModules.IsInvertible` and as `AlgebraicGeometry.SheafOfModules.IsInvertible`;
`Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry` passes between them, and the hypothesis
carried here is the Chow chapter's own `AlgebraicGeometry.Space.IsInvertibleSheaf`, which is the
second of the two.

The ungraded realization uses the site-level apparatus of
`StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpace`:
`Stacks.GradedAlgebra.totalCommPresheaf` is the presheaf of commutative rings whose sections are
the direct sum of the homogeneous pieces, and `Stacks.GradedAlgebra.totalCommStructureMap` the
map `r ↦ r · 1` out of the structure sheaf.  Both are stated for an arbitrary site; only their
sheafification was written for schemes, and that step is redone here.

The anti-equivalence of Tag 081V and its base-change clause are carried as the explicit
parameters `E` and `C`, as `AlgebraicGeometry.Space.relativeSpec` carries them, and
quasi-coherence of `⨁_{n ∈ ℤ} ℒ^{⊗ n}` is carried as `hqc` in this file; the latter is
discharged in `StacksFrontier.AlgebraicGeometry.Spaces.Chow.LaurentAlgebraQuasicoherence`.

**`T` and `q` as formed here cannot be formed from the hypotheses of Situation 0EDT**, and
carrying `E` is not forced.  `AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence` is Tag 081V
with the tag's unrestricted target, and it is **empty** over any site one of whose algebraic
spaces has an affine étale chart whose ring of functions is not the zero ring, by
`AlgebraicGeometry.Space.not_nonempty_affineAlgebraAntiEquivalence_of_hasNonzeroAffineChart`: an
affine morphism has fewer than `B.cutoff` sections over a chart (Tag 03G8) while a quasi-coherent
algebra is under no such bound.  Tag 081W does hold with no parameter — for every quasi-coherent
algebra over the enlargement of the site that Tag 03FO supplies
(`AlgebraicGeometry.Space.relativeSpectrum`), and inside the site for every algebra satisfying
the size condition of the corrected Tag 081V
(`AlgebraicGeometry.Space.boundedRelativeSpec`) — and
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.MultiplicativeTorsorSpectrum` forms `T` and `q` both
of those ways, with no parameter.  The definitions here are kept as they stand and are
superseded by those.

## References

* [Stacks Project, Tag 0EQG](https://stacks.math.columbia.edu/tag/0EQG)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### The relative spectrum of a base-changed algebra -/

section BaseChange

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (E : AffineAlgebraAntiEquivalence B S hS) (C : BaseChangeCompatibility B S hS E)
    {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X)

/-- `Y ×_X \underline{Spec}_X(A) ≅ \underline{Spec}_Y(g^* A)`, as algebraic spaces affine over
`Y`: the base-change isomorphism of quasi-coherent algebras, carried across the
anti-equivalence of Stacks 081V over `Y`. -/
def relativeSpecBaseChangeAffineIso (A : QuasicoherentAlgebra B S hS X) :
    relativeSpec B S hS E ((qcAlgebraPullback B S hS E C g).obj A) ≅
      (C.affineBaseChange g).obj (relativeSpec B S hS E A) :=
  (((E.equivalence Y).inverse.mapIso (relativeSpecBaseChangeIso B S hS E C g A)) ≪≫
    ((E.equivalence Y).unitIso.app
      (op ((C.affineBaseChange g).obj (relativeSpec B S hS E A)))).symm).unop.symm

end BaseChange

/-! ### The Laurent algebra on the small étale site of a good algebraic space -/

section Good

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1)

/-- The structure sheaf of `X`, as a presheaf of commutative rings on its small étale site:
the base over which the tensor-power apparatus of Tag 01CU is stated. -/
abbrev tensorStructureRingPresheaf :
    (SmallEtale D.site D.base D.base_mem X)ᵒᵖ ⥤ CommRingCat.{u} :=
  (smallEtaleRingedSite D.site D.base D.base_mem X hp.1).O.obj

/-- The structure sheaf of `X` satisfies the sheaf condition for the small étale topology, in
the form the tensor-power apparatus of Tag 01CU consumes. -/
theorem isSheaf_tensorStructureRingPresheaf :
    Presheaf.IsSheaf (SmallEtale.topology D.site D.base D.base_mem X)
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
        (tensorStructureRingPresheaf D p hp)) :=
  (structureRingSheaf D.site D.base D.base_mem ⟨X, hp.1⟩).property

/-- The structure sheaf of `X`, as the sheaf of rings indexing its modules, in the spelling in
which the tensor-power apparatus of Tag 01CU takes its base. -/
abbrev tensorStructureSheaf :
    Sheaf (SmallEtale.topology D.site D.base D.base_mem X) RingCat.{u} :=
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
    (tensorStructureRingPresheaf D p hp) (isSheaf_tensorStructureRingPresheaf D p hp)

variable (hL : IsInvertibleSheaf D p hp L)

/-- **The `ℤ`-graded Laurent algebra `⨁_{n ∈ ℤ} ℒ^{⊗ n}` of an invertible `𝒪_X`-module**: the
homogeneous piece in degree `n` is the `n`th integer tensor power of `ℒ`, with the coherent
multiplication of Tag 01CU. -/
def laurentGradedAlgebra :
    SheafOfModules.GradedAlgebra.{u, u} (tensorStructureSheaf D p hp) := by
  have : Stacks.SheafOfModules.IsInvertible (tensorStructureRingPresheaf D p hp)
      (isSheaf_tensorStructureRingPresheaf D p hp) L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hL
  exact Stacks.SheafOfModules.TensorPower.laurentAlgebra
    (tensorStructureRingPresheaf D p hp) (isSheaf_tensorStructureRingPresheaf D p hp) L

/-- **Homogeneous multiplication in the Laurent algebra of `ℒ` commutes**, in every pair of
degrees.  This is what makes its ungraded realization a sheaf of commutative rings. -/
theorem laurentGradedAlgebra_mul_comm (n m : ℤ)
    (U : (SmallEtale D.site D.base D.base_mem X)ᵒᵖ)
    (x : ((laurentGradedAlgebra D p hp L hL).piece n).val.obj U)
    (y : ((laurentGradedAlgebra D p hp L hL).piece m).val.obj U) :
    HEq (((laurentGradedAlgebra D p hp L hL).mul n m).app U x y)
      (((laurentGradedAlgebra D p hp L hL).mul m n).app U y x) := by
  have : Stacks.SheafOfModules.IsInvertible (tensorStructureRingPresheaf D p hp)
      (isSheaf_tensorStructureRingPresheaf D p hp) L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hL
  exact Stacks.SheafOfModules.TensorPower.laurentAlgebra_mul_comm
    (tensorStructureRingPresheaf D p hp) (isSheaf_tensorStructureRingPresheaf D p hp) L n m U x y

/-! ### The ungraded realization -/

/-- The ungraded realization of `⨁_{n ∈ ℤ} ℒ^{⊗ n}` as a presheaf of commutative rings on the
small étale site: its sections over a chart are the direct sum of the homogeneous pieces. -/
def laurentCommPresheaf : (SmallEtale D.site D.base D.base_mem X)ᵒᵖ ⥤ CommRingCat.{u} :=
  (laurentGradedAlgebra D p hp L hL).toPresheafGradedAlgebra.totalCommPresheaf
    (laurentGradedAlgebra_mul_comm D p hp L hL)

/-- The structure map `r ↦ r · 1` of the ungraded realization, as a morphism of presheaves of
commutative rings out of the structure sheaf of `X`. -/
def laurentCommStructureMap :
    (structureSheaf D.site D.base D.base_mem X hp.1).obj ⟶ laurentCommPresheaf D p hp L hL :=
  Stacks.GradedAlgebra.totalCommStructureMap
    (O := tensorStructureRingPresheaf D p hp)
    (laurentGradedAlgebra D p hp L hL).toPresheafGradedAlgebra
    (laurentGradedAlgebra_mul_comm D p hp L hL)

/-- **The Laurent algebra sheaf of `ℒ`**: the ungraded realization of `⨁_{n ∈ ℤ} ℒ^{⊗ n}`, as a
sheaf of commutative `𝒪_X`-algebras on the small étale site of `X`. -/
def laurentAlgebraSheaf : AlgebraSheaf.{u, u} D.site D.base D.base_mem X hp.1 :=
  AlgebraSheaf.ofHom
    (R := (presheafToSheaf (SmallEtale.topology D.site D.base D.base_mem X) CommRingCat.{u}).obj
      (laurentCommPresheaf D p hp L hL))
    { hom := laurentCommStructureMap D p hp L hL ≫
        (sheafificationAdjunction (SmallEtale.topology D.site D.base D.base_mem X)
          CommRingCat.{u}).unit.app (laurentCommPresheaf D p hp L hL) }

/-- The Laurent algebra sheaf of `ℒ` as a quasi-coherent `𝒪_X`-algebra, granted its
quasi-coherence. -/
def laurentQuasicoherentAlgebra
    (hqc : AlgebraSheaf.IsQuasicoherent (laurentAlgebraSheaf D p hp L hL)) :
    QuasicoherentAlgebra D.site D.base D.base_mem ⟨X, hp.1⟩ :=
  ⟨laurentAlgebraSheaf D p hp L hL, hqc⟩

/-! ### The torsor and its projection -/

variable (E : AffineAlgebraAntiEquivalence D.site D.base D.base_mem)
    (hqc : AlgebraSheaf.IsQuasicoherent (laurentAlgebraSheaf D p hp L hL))

/-- **The multiplicative torsor `T = \underline{Spec}_X(⨁_{n ∈ ℤ} ℒ^{⊗ n})` of an invertible
`𝒪_X`-module**, as an algebraic space affine over `X`: the relative spectrum of Stacks 081W of
its Laurent algebra. -/
def multiplicativeTorsor : AffineOver D.site D.base D.base_mem ⟨X, hp.1⟩ :=
  relativeSpec D.site D.base D.base_mem E (laurentQuasicoherentAlgebra D p hp L hL hqc)

/-- The algebraic space `T` underlying the multiplicative torsor of `ℒ`. -/
abbrev multiplicativeTorsorSpace : AlgebraicSpaces D.site D.base D.base_mem :=
  (multiplicativeTorsor D p hp L hL E hqc).obj.left

/-- **The projection `q : T ⟶ X`** of the multiplicative torsor of `ℒ`, that is, the structure
morphism of the relative spectrum of `⨁_{n ∈ ℤ} ℒ^{⊗ n}`. -/
abbrev multiplicativeTorsorProjection :
    multiplicativeTorsorSpace D p hp L hL E hqc ⟶ ⟨X, hp.1⟩ :=
  (multiplicativeTorsor D p hp L hL E hqc).obj.hom

end Good

end AlgebraicGeometry.Space

end
