module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsEpiFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.MixedTensorQuasicoherent

/-!
# Tensor products of quasi-coherent modules on an algebraic space

The tensor product of two quasi-coherent `𝒪_F`-modules on an algebraic space `F` is
quasi-coherent.  At the universe of the schemes this is the tensor-product clause of
Stacks 03M1.

The tensor product of `𝒪_F`-modules is formed as on any ringed site: the objectwise tensor
product of the two presheaves of sections, with the universe of its sections raised to contain
the universe of the coefficient rings, sheafified.  Its universal property is Stacks 06WN(2).

## Main definitions

* `AlgebraicGeometry.Space.tensorModule` is the tensor product of two `𝒪_F`-modules, with the
  sections of the two factors in independent universes.

## Main results

* `AlgebraicGeometry.Space.isSheaf_structureRingPresheaf` and
  `AlgebraicGeometry.Space.isSheaf_structureRingPresheaf_forget`: the structure sheaf of `F`,
  read as a presheaf of rings and as a presheaf of sets, is a sheaf on the small étale site.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_tensorModule`: the tensor product of two
  quasi-coherent `𝒪_F`-modules is quasi-coherent.  At the universe of the schemes this is
  clause (5) of Stacks 03M1,
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_tensorModule_schemeUniverse`.

## Implementation notes

The small étale site of an algebraic space over `Scheme.{u}` has its objects in
`Type (u + 1)`, its morphisms in `Type u` and a `CommRingCat.{u}`-valued structure sheaf, so the
universe of the coefficient rings does *not* contain the universe of the site.  The
single-universe tensor theory, `Stacks.SheafOfModules.isQuasicoherentOnSite_tensorSheaf`, is
therefore unavailable here: it needs the coefficient rings in the universe containing the site
and the sections at once, which over an algebraic space would ask for `u = u + 1`.  What applies
instead is `Stacks.Modules.isQuasicoherentOnSite_sheafificationTensorObjUlift`, which carries
out the universe bookkeeping and whose only hypotheses beyond the sheaf condition for the
coefficient rings are the sheaf condition for their *sets* of sections and sheafification of
abelian presheaves at the universe of the sections of the tensor product.

The sheaf condition for the sets of sections is not obtainable from the sheaf condition in
`CommRingCat.{u}` by `CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget`, which would require
the forgetful functor to preserve limits of size `Type (u + 1)`; on the small étale site that
unfolds to the unsatisfiable `u + 1 =?= u`, the obstruction recorded in
`StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleQuasicoherentSections`.  It holds all the
same, because `CategoryTheory.forget RingCat.{u}` is corepresented by the free ring on one
generator, which makes the statement one instance of the definition of a sheaf; that is
`Stacks.NoncommChangeOfRings.Silver.isSheaf_forget_of_isSheaf`, and it needs no size condition.

The two sheafification facts are carried as hypotheses rather than fixing the module universes,
exactly as in `AlgebraicGeometry.Space.quasicoherentSheaves_abelian_of_closure`: they are
instances at the universe `u` of the schemes, where they come from essential smallness of the
small étale site, and they hold in every universe at least `u + 1` by
`AlgebraicGeometry.Space.hasSheafify_smallEtaleRingedSite_addCommGrpCat` and
`AlgebraicGeometry.Space.wEqualsLocallyBijective_smallEtaleRingedSite_addCommGrpCat`.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 03G6](https://stacks.math.columbia.edu/tag/03G6)
-/

@[expose] public section

open CategoryTheory

universe u m n

namespace AlgebraicGeometry.Space

open Stacks.SheafOfModules.TensorSheafification (structureRingPresheaf)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- The structure sheaf of the algebraic space `F`, read as a presheaf of (not necessarily
commutative) rings, is a sheaf on the small étale site: the forgetful functor
`forget₂ CommRingCat RingCat` creates limits, so it preserves the sheaf condition.  This is the
sheaf condition already carried by `AlgebraicGeometry.RingedSite.ringSheaf`. -/
theorem isSheaf_structureRingPresheaf :
    Presheaf.IsSheaf (smallEtaleRingedSite B S hS F hF).J
      (structureRingPresheaf (structurePresheaf B S hS F)) :=
  (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).property

/-- The structure sheaf of the algebraic space `F`, read as a presheaf of *sets*, is a sheaf on
the small étale site.  The forgetful functor of `RingCat.{u}` is corepresented by the free ring
on one generator, so this is one instance of the sheaf condition of
`AlgebraicGeometry.Space.isSheaf_structureRingPresheaf`, with no condition relating the universe
of the rings to the universe of the site. -/
theorem isSheaf_structureRingPresheaf_forget :
    Presheaf.IsSheaf (smallEtaleRingedSite B S hS F hF).J
      (structureRingPresheaf (structurePresheaf B S hS F) ⋙ forget RingCat.{u}) :=
  Stacks.NoncommChangeOfRings.Silver.isSheaf_forget_of_isSheaf _
    (isSheaf_structureRingPresheaf B S hS F hF)

section Tensor

variable
  [((smallEtaleRingedSite B S hS F hF).J).WEqualsLocallyBijective
    AddCommGrpCat.{max u m n}]
  [HasWeakSheafify ((smallEtaleRingedSite B S hS F hF).J) AddCommGrpCat.{max u m n}]

/-- The tensor product `M ⊗_{𝒪_F} N` of two `𝒪_F`-modules on an algebraic space: the objectwise
tensor product of their presheaves of sections, with the universe of its sections raised to
contain the universe `u` of the coefficient rings, sheafified.  The sections of the two factors
lie in independent universes `m` and `n`, and those of the tensor product in `max u m n`.

Its universal property is Stacks 06WN(2):
`Stacks.Modules.existsUnique_hom_ulift` factors every bilinear map through it. -/
noncomputable def tensorModule (M : Modules.{u, m} B S hS F hF)
    (N : Modules.{u, n} B S hS F hF) : Modules.{u, max u m n} B S hS F hF :=
  letI := SheafOfModules.isLocallyInjective_id_structure
    (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
  letI := SheafOfModules.isLocallySurjective_id_structure
    (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
  (PresheafOfModules.sheafification
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).obj)).obj
    ((PresheafOfModules.tensorObj M.val N.val).uliftSections.{u})

/-- **Stacks 03M1, tensor products.**  The tensor product of two quasi-coherent `𝒪_F`-modules on
an algebraic space is quasi-coherent.

The tensor product is `AlgebraicGeometry.Space.tensorModule`, formed on the small étale ringed
site of `F`; the sections of the two factors may lie in independent universes. -/
@[stacks 03M1 "(5) tensor products"]
theorem isQuasicoherentOnSite_tensorModule (M : Modules.{u, m} B S hS F hF)
    (N : Modules.{u, n} B S hS F hF) (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) :
    (tensorModule B S hS F hF M N).IsQuasicoherentOnSite :=
  Stacks.Modules.isQuasicoherentOnSite_sheafificationTensorObjUlift
    (isSheaf_structureRingPresheaf B S hS F hF)
    (isSheaf_structureRingPresheaf_forget B S hS F hF) M N hM hN

end Tensor

end AlgebraicGeometry.Space

end
