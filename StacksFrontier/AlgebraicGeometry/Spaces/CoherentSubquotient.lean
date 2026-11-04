module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Topologies.CoherentKernelOnSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceCokernels

/-!
# Submodules and quotient modules of a coherent module on an algebraic space

Let `F` be an algebraic space over a scheme `S` and let `M` be a coherent `𝒪_F`-module, that is
a module which is quasi-coherent and coherent on the small étale ringed site of `F`, as in
Stacks 07UA.  Stacks 07UD asserts, for `F` locally Noetherian, that a quasi-coherent submodule
of `M` and a quasi-coherent quotient module of `M` are again coherent.

This file proves both assertions in the form in which they need no local Noetherianity: a
submodule of `M` is coherent as soon as it is of finite type, and a quotient of `M` is coherent
as soon as the submodule it is taken by is of finite type.  A submodule is a monomorphism
`ι : N ⟶ M` of `𝒪_F`-modules and a quotient is an epimorphism `p : M ⟶ Q`, and finite type is
the sectionwise condition `PresheafOfModules.IsFiniteType` of Stacks 03DL(7), the one appearing
in the coherence predicate itself.

## Main results

* `AlgebraicGeometry.Space.isCoherentOnSite_of_mono_of_isFiniteType`: **a submodule of finite
  type of a coherent module is coherent.**  The relations among a finite family of sections of
  the submodule are the relations among their images, because a monomorphism is injective on
  sections, so the relations clause of coherence is inherited verbatim from the ambient module.
* `AlgebraicGeometry.Space.isFiniteType_of_mono_of_isCoherentOnSite_cokernel`: a submodule of a
  coherent module is of finite type as soon as the quotient by it is coherent, the submodule
  being the kernel of the projection onto that quotient.
* `AlgebraicGeometry.Space.isCoherentOnSite_of_mono_of_isCoherentOnSite_cokernel` and
  `AlgebraicGeometry.Space.isCoherent_of_mono_of_isCoherent_cokernel`: the two combined, on the
  small étale ringed site and for `AlgebraicGeometry.Space.IsCoherent`.
* `AlgebraicGeometry.Space.isCoherentOnSite_of_epi_of_isFiniteType_kernel` and
  `AlgebraicGeometry.Space.isCoherent_of_epi_of_isFiniteType_kernel`: **a quotient of a coherent
  module by a submodule of finite type is coherent.**  Such a submodule is itself coherent by
  the first result, and the quotient is the cokernel of its inclusion, so the cokernel clause of
  Stacks 01BY on a site applies.

## Implementation notes

**Local Noetherianity is a hypothesis of no statement here, and `@[stacks 07UD]` is therefore
not carried; this is not a weakening of the source but a factorization of it.**  Both assertions
of Stacks 07UD are false without local Noetherianity: over the spectrum of a valuation ring of
rank one which is not discrete the structure sheaf is coherent, finitely generated ideals being
principal, while its maximal ideal is a quasi-coherent submodule which is not of finite type and
the residue field is a quasi-coherent quotient module which is not coherent.  What local
Noetherianity is needed for is exactly the assertion

  *a quasi-coherent submodule of a coherent module on a locally Noetherian algebraic space is of
  finite type*,

and the results below reduce both assertions of Stacks 07UD to that one: the submodule clause is
`AlgebraicGeometry.Space.isCoherentOnSite_of_mono_of_isFiniteType` and the quotient clause is
`AlgebraicGeometry.Space.isCoherentOnSite_of_epi_of_isFiniteType_kernel`, applied to the kernel
of the projection.  Over and above local Noetherianity that assertion needs the identification
of the sections of a quasi-coherent module over an affine étale chart with a module over the
ring of the chart, which is Descent, Proposition 03DX(2); in this tree that identification is
the hypothesis `AlgebraicGeometry.Space.IsCartesianOnAffineCharts` carried throughout
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentNoetherian`, and it is not available.

The module universe is the universe `u` of the schemes.  That is the universe in which the
category of `𝒪_F`-modules is abelian, by `StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian`,
hence the universe in which a monomorphism is the kernel of its cokernel and an epimorphism is
the cokernel of its kernel; it is also the universe in which the quasi-coherence clause of
`AlgebraicGeometry.Space.IsCoherent` follows from its coherence clause, by
`AlgebraicGeometry.Space.isCoherent_of_isCoherentOnSite`, so that the statements about
`AlgebraicGeometry.Space.IsCoherent` cost no more than the statements on the site.  Neither
module is assumed quasi-coherent anywhere below: coherence on the site implies it.

Nothing here is specific to the small étale site of an algebraic space.  The four inputs
`Stacks.SheafOfModules.isCoherentOnSite_of_injective`,
`Stacks.SheafOfModules.isFiniteType_kernel_of_isCoherentOnSite`,
`Stacks.SheafOfModules.injective_val_of_mono` and
`Stacks.SheafOfModules.isCoherentOnSite_cokernel` are proved for sheaves of modules over a sheaf
of rings on an arbitrary site, and all that is asked of this site is that its category of
modules be abelian.

## References

* [Stacks Project, Tag 07UD](https://stacks.math.columbia.edu/tag/07UD)
* [Stacks Project, Tag 07UA](https://stacks.math.columbia.edu/tag/07UA)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 01Y1](https://stacks.math.columbia.edu/tag/01Y1)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **A submodule of finite type of a coherent module on an algebraic space is coherent.**  The
submodule is given by a monomorphism `ι : N ⟶ M` of `𝒪_F`-modules, and coherence is coherence on
the small étale ringed site of `F`, which is Stacks 03DL(8).

A monomorphism of sheaves of modules is injective on the sections over every étale chart, so the
relations among a finite family of sections of `N` are *equal*, as a submodule of a finite
product of copies of `𝒪_F`, to the relations among their images in `M`; the relations clause of
coherence is inherited from `M` along that equality, and the finite-type clause is the
hypothesis `hN`.  Neither local Noetherianity of `F` nor quasi-coherence of `N` is used. -/
theorem isCoherentOnSite_of_mono_of_isFiniteType {M N : Modules.{u, u} B S hS F hF}
    (ι : N ⟶ M) [Mono ι]
    (hN : PresheafOfModules.IsFiniteType (smallEtaleRingedSite B S hS F hF).J N.val)
    (hM : SheafOfModules.IsCoherentOnSite M) :
    SheafOfModules.IsCoherentOnSite N :=
  Stacks.SheafOfModules.isCoherentOnSite_of_injective ι
    (Stacks.SheafOfModules.injective_val_of_mono ι) hN hM

/-- **A submodule of a coherent module on an algebraic space whose quotient is coherent is of
finite type.**

The category of `𝒪_F`-modules is abelian, so the monomorphism `ι` identifies `N` with the kernel
of the projection of `M` onto the quotient `M / N`, by
`CategoryTheory.Abelian.isIso_factorThruImage`.  The kernel of a morphism from a module of
finite type to a module coherent on the small étale ringed site is of finite type; the source
`M` of the projection is of finite type because it is coherent, and its target `M / N` is
coherent by hypothesis.  Local Noetherianity of `F` is not used. -/
theorem isFiniteType_of_mono_of_isCoherentOnSite_cokernel {M N : Modules.{u, u} B S hS F hF}
    (ι : N ⟶ M) [Mono ι] (hM : SheafOfModules.IsCoherentOnSite M)
    (hQ : SheafOfModules.IsCoherentOnSite (cokernel ι)) :
    PresheafOfModules.IsFiniteType (smallEtaleRingedSite B S hS F hF).J N.val :=
  Stacks.SheafOfModules.presheaf_isFiniteType_of_iso
    ((SheafOfModules.forget _).mapIso (asIso (Abelian.factorThruImage ι)).symm)
    (Stacks.SheafOfModules.isFiniteType_kernel_of_isCoherentOnSite hM.isFiniteType hQ
      (cokernel.π ι))

/-- **A submodule of a coherent module on an algebraic space whose quotient is coherent is
coherent**, for coherence on the small étale ringed site.

The submodule is of finite type by
`AlgebraicGeometry.Space.isFiniteType_of_mono_of_isCoherentOnSite_cokernel`, and a submodule of
finite type of a coherent module is coherent by
`AlgebraicGeometry.Space.isCoherentOnSite_of_mono_of_isFiniteType`.  Local Noetherianity of `F`
is not used. -/
theorem isCoherentOnSite_of_mono_of_isCoherentOnSite_cokernel
    {M N : Modules.{u, u} B S hS F hF} (ι : N ⟶ M) [Mono ι]
    (hM : SheafOfModules.IsCoherentOnSite M)
    (hQ : SheafOfModules.IsCoherentOnSite (cokernel ι)) :
    SheafOfModules.IsCoherentOnSite N :=
  isCoherentOnSite_of_mono_of_isFiniteType B S hS F hF ι
    (isFiniteType_of_mono_of_isCoherentOnSite_cokernel B S hS F hF ι hM hQ) hM

/-- **A submodule of a coherent module on an algebraic space whose quotient is coherent is
coherent**, for the predicate `AlgebraicGeometry.Space.IsCoherent` of Stacks 07UA.

Only the coherence-on-the-site clause of the two hypotheses is used, and the quasi-coherence
clause of the conclusion is free at this module universe by
`AlgebraicGeometry.Space.isCoherent_of_isCoherentOnSite`, coherence on a site implying
quasi-coherence on it.  Local Noetherianity of `F` is not used. -/
theorem isCoherent_of_mono_of_isCoherent_cokernel {M N : Modules.{u, u} B S hS F hF}
    (ι : N ⟶ M) [Mono ι] (hM : IsCoherent B S hS F hF M)
    (hQ : IsCoherent B S hS F hF (cokernel ι)) :
    IsCoherent B S hS F hF N :=
  let : SheafOfModules.IsCoherentOnSite N :=
    isCoherentOnSite_of_mono_of_isCoherentOnSite_cokernel B S hS F hF ι
      hM.toIsCoherentOnSite hQ.toIsCoherentOnSite
  isCoherent_of_isCoherentOnSite B S hS F hF N

/-- **A quotient of a coherent module on an algebraic space by a submodule of finite type is
coherent**, for coherence on the small étale ringed site.  The quotient is given by an
epimorphism `p : M ⟶ Q` of `𝒪_F`-modules and the submodule it is taken by is the kernel of `p`.

The kernel of `p` is coherent by
`AlgebraicGeometry.Space.isCoherentOnSite_of_mono_of_isFiniteType`, being a submodule of finite
type of the coherent module `M`; and `Q` is the cokernel of its inclusion, by
`CategoryTheory.Abelian.isIso_factorThruCoimage`, so the cokernel clause of Stacks 01BY on a
site applies to it.  Local Noetherianity of `F` is not used.

Finite type of the kernel is where local Noetherianity is needed in the source's own argument;
what makes it indispensable is that the relations among a finite family of sections of `Q` are
computed from a finite generating family of the kernel together with the relations among lifts
of the family to `M`. -/
theorem isCoherentOnSite_of_epi_of_isFiniteType_kernel {M Q : Modules.{u, u} B S hS F hF}
    (p : M ⟶ Q) [Epi p] (hM : SheafOfModules.IsCoherentOnSite M)
    (hK : PresheafOfModules.IsFiniteType (smallEtaleRingedSite B S hS F hF).J (kernel p).val) :
    SheafOfModules.IsCoherentOnSite Q :=
  Stacks.SheafOfModules.isCoherentOnSite_of_iso (asIso (Abelian.factorThruCoimage p))
    (Stacks.SheafOfModules.isCoherentOnSite_cokernel (kernel.ι p)
      (isCoherentOnSite_of_mono_of_isFiniteType B S hS F hF (kernel.ι p) hK hM) hM)

/-- **A quotient of a coherent module on an algebraic space by a submodule of finite type is
coherent**, for the predicate `AlgebraicGeometry.Space.IsCoherent` of Stacks 07UA.

Only the coherence-on-the-site clause of the hypothesis on `M` is used, and the quasi-coherence
clause of the conclusion is free at this module universe by
`AlgebraicGeometry.Space.isCoherent_of_isCoherentOnSite`.  Local Noetherianity of `F` is not
used. -/
theorem isCoherent_of_epi_of_isFiniteType_kernel {M Q : Modules.{u, u} B S hS F hF}
    (p : M ⟶ Q) [Epi p] (hM : IsCoherent B S hS F hF M)
    (hK : PresheafOfModules.IsFiniteType (smallEtaleRingedSite B S hS F hF).J (kernel p).val) :
    IsCoherent B S hS F hF Q :=
  let : SheafOfModules.IsCoherentOnSite Q :=
    isCoherentOnSite_of_epi_of_isFiniteType_kernel B S hS F hF p hM.toIsCoherentOnSite hK
  isCoherent_of_isCoherentOnSite B S hS F hF Q

end AlgebraicGeometry.Space

end
