module

public import StacksFrontier.AlgebraicGeometry.ProjCoherentModule.Basic
public import StacksFrontier.AlgebraicGeometry.ProjSerreCorrespondence.QuotientFunctor
public import StacksFrontier.AlgebraicGeometry.ProjTwistFunctor.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `M ↦ M̃` as a functor `Mod^fg_A / Mod^fg_{A, torsion} ⟶ Coh(𝒪_X)`

Let `A` be a graded ring which is Noetherian and of finite type over `A₀`, and let `X = Proj(A)`.
The arrow of Stacks 0BXD has the quotient category `Mod^fg_A / Mod^fg_{A, torsion}` for its source
and the category `Coh(𝒪_X)` of **coherent** `𝒪_X`-modules for its target. The functor induced by
`M ↦ M̃` out of that quotient is built in
`StacksFrontier/AlgebraicGeometry/ProjSerreCorrespondence/IrrelevantQuotientFunctor.lean`, but with
all sheaves of `𝒪_X`-modules as its target, because the coherence of `M̃` was not available. It is
now (`StacksFrontier/AlgebraicGeometry/ProjCoherentModule/Basic.lean`), and this
file corestricts the functor to `Coh(𝒪_X)` and records that the corestriction is still faithful.

It also records the one step that turns an isomorphism of associated sheaves back into an
isomorphism in the quotient category, which is how the essential surjectivity of the quasi-inverse
is proved: a morphism of finitely generated graded modules whose associated sheaf morphism is an
isomorphism is an isomorphism modulo the torsion subcategory, so the quotient functor sends it to
an isomorphism.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.finiteCoherentSheafFunctor`: the restriction
  of `M ↦ M̃` to `Mod^fg_A`, corestricted to `Coh(𝒪_X)`.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.coherentQuotientFunctor`: **the arrow of
  Stacks 0BXD**, the functor `Mod^fg_A / Mod^fg_{A, torsion} ⟶ Coh(𝒪_X)` induced by `M ↦ M̃`.

## Main results

* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.coherentQuotientFunctorFac`: the induced
  functor composed with the quotient functor is `M ↦ M̃` again.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.coherentQuotientFunctorCompι`: the induced
  functor, read in all sheaves of `𝒪_X`-modules, is the functor of
  `IrrelevantQuotientFunctor.lean` — so corestricting changed nothing.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.faithful_coherentQuotientFunctor`: **the
  corestricted functor is faithful**, for `A` generated in degree one.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.isoModSerre_of_isIso_map` and
  `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.isIso_toIrrelevantQuotient_map`: a morphism of
  finitely generated graded modules inducing an isomorphism of associated sheaves becomes an
  isomorphism in the quotient category.

## Implementation notes

The corestriction is `CategoryTheory.ObjectProperty.lift`, whose composite with the inclusion is
`Iso.refl`; so `finiteCoherentSheafFunctor ⋙ ι` and `finiteAssociatedSheafFunctor` are the same
functor, and every property of the corestriction is read off the inclusion being fully faithful
rather than proved again. In particular it inverts the isomorphisms modulo the torsion
subcategory because the inclusion reflects isomorphisms, and the two lifts through the
localization are isomorphic by `CategoryTheory.Localization.liftNatIso`, which is what identifies
the corestricted functor with the one already built.

No abelian structure on `Coh(𝒪_X)` is used. The faithfulness of the corestriction is deduced from
the faithfulness of `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.irrelevantQuotientFunctor`
through `CategoryTheory.Functor.Faithful.of_comp_iso`, not by rerunning the criterion of Stacks
06XK.

`isoModSerre_of_isIso_map` is the converse direction of the first paragraph of Stacks 0BXD. Its
proof does not compute the kernel and the cokernel of the morphism: the restriction of `M ↦ M̃` to
`Mod^fg_A` preserves finite limits and finite colimits, so it carries them to the kernel and
cokernel of an isomorphism, which are zero objects, and
`Stacks.AlgebraicGeometry.ProjSerreCorrespondence.isIrrelevant_of_isZero_associatedModuleSheaf`
turns that into irrelevance.

**No `stacks` attribute.** The arrow of Stacks 0BXD is not the proposition; the proposition
asserts that it is an equivalence with a named quasi-inverse, and that is stated elsewhere.

## References

* [Stacks Project, Tag 0BXD](https://stacks.math.columbia.edu/tag/0BXD)
* [Stacks Project, Tag 06XK](https://stacks.math.columbia.edu/tag/06XK)
* [Stacks Project, Tag 02MS](https://stacks.math.columbia.edu/tag/02MS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality
open Stacks.AlgebraicGeometry.ProjTwistFunctor (projRingSheaf)

namespace Stacks.AlgebraicGeometry.ProjSerreCorrespondence

universe u w

variable {A : Type u} {σ : Type w} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] [IsNoetherianRing A]

/-! ### An isomorphism of associated sheaves is an isomorphism modulo torsion -/

/-- **The converse half of the first paragraph of Stacks 0BXD, for a morphism.** Over a Noetherian
graded ring generated in degree one, a morphism of finitely generated graded modules whose
associated sheaf morphism is an isomorphism has irrelevant kernel and irrelevant cokernel, that is,
it is an isomorphism modulo the torsion subcategory.

The kernel and the cokernel are not computed: `M ↦ M̃` preserves finite limits and finite colimits
on `Mod^fg_A`, so it sends them to the kernel and the cokernel of an isomorphism, which are zero
objects, and the kernel of `M ↦ M̃` consists of irrelevant modules. -/
theorem isoModSerre_of_isIso_map
    (hgen : Algebra.adjoin (𝒜 0) ((𝒜 1 : Set A)) = ⊤)
    {X Y : FiniteGradedModules.{u, u, w} 𝒜} (f : X ⟶ Y)
    (hf : IsIso ((finiteAssociatedSheafFunctor.{u, w} 𝒜).map f)) :
    haveI := isSerreClass_irrelevantModules.{u, u, w} 𝒜 Nat.one_pos
    (ObjectProperty.isoModSerre (irrelevantModules.{u, u, w} 𝒜 1)) f := by
  have := isSerreClass_irrelevantModules.{u, u, w} 𝒜 Nat.one_pos
  have := preservesFiniteLimits_finiteAssociatedSheafFunctor.{u, w} 𝒜
  have := preservesFiniteColimits_finiteAssociatedSheafFunctor.{u, w} 𝒜
  have := hf
  have key {Z : FiniteGradedModules.{u, u, w} 𝒜} :=
    isIrrelevant_of_isZero_associatedModuleSheaf (M := Z.obj) 𝒜 hgen
      (Ideal.fg_of_isNoetherianRing _)
  exact ⟨key (IsZero.of_iso (isZero_kernel_of_mono _)
      (PreservesKernel.iso (finiteAssociatedSheafFunctor.{u, w} 𝒜) f)),
    key (IsZero.of_iso (isZero_cokernel_of_epi _)
      (PreservesCokernel.iso (finiteAssociatedSheafFunctor.{u, w} 𝒜) f))⟩

/-- **A morphism of finitely generated graded modules inducing an isomorphism of associated
sheaves becomes an isomorphism in the quotient category** `Mod^fg_A / Mod^fg_{A, torsion}`: by
`isoModSerre_of_isIso_map` it is an isomorphism modulo the torsion subcategory, and the quotient
functor inverts those by construction. -/
theorem isIso_toIrrelevantQuotient_map
    (hgen : Algebra.adjoin (𝒜 0) ((𝒜 1 : Set A)) = ⊤)
    {X Y : FiniteGradedModules.{u, u, w} 𝒜} (f : X ⟶ Y)
    (hf : IsIso ((finiteAssociatedSheafFunctor.{u, w} 𝒜).map f)) :
    IsIso ((toIrrelevantQuotient.{u, u, w} 𝒜 Nat.one_pos).map f) := by
  have := isSerreClass_irrelevantModules.{u, u, w} 𝒜 Nat.one_pos
  exact Localization.inverts (toIrrelevantQuotient.{u, u, w} 𝒜 Nat.one_pos)
    (ObjectProperty.isoModSerre (irrelevantModules.{u, u, w} 𝒜 1)) f
    (isoModSerre_of_isIso_map 𝒜 hgen f hf)

/-! ### The corestriction to the coherent sheaves -/

/-- **The restriction of `M ↦ M̃` to `Mod^fg_A`, corestricted to `Coh(𝒪_X)`.** A finitely
generated graded module over a Noetherian graded ring has coherent associated sheaf, by
`AlgebraicGeometry.ProjectiveSpectrum.Proj.stacksIsCoherent_associatedModuleSheafFunctor_obj`. -/
@[ega "II 3.4.3" "(i)"]
def finiteCoherentSheafFunctor :
    FiniteGradedModules.{u, u, w} 𝒜 ⥤ Stacks.SheafOfModules.CoherentModules (projRingSheaf 𝒜) :=
  ObjectProperty.lift (Stacks.SheafOfModules.coherentModules (projRingSheaf 𝒜))
    (finiteAssociatedSheafFunctor.{u, w} 𝒜)
    fun M => haveI := M.property
      AlgebraicGeometry.ProjectiveSpectrum.Proj.stacksIsCoherent_associatedModuleSheafFunctor_obj
        𝒜 M.obj

/-- Corestricting changes nothing: composing with the inclusion of the coherent sheaves gives
back `M ↦ M̃` on `Mod^fg_A`. -/
def finiteCoherentSheafFunctorCompι :
    finiteCoherentSheafFunctor.{u, w} 𝒜 ⋙
        (Stacks.SheafOfModules.coherentModules (projRingSheaf 𝒜)).ι ≅
      finiteAssociatedSheafFunctor.{u, w} 𝒜 :=
  ObjectProperty.liftCompιIso _ _ _

/-- **The corestricted functor inverts the isomorphisms modulo the torsion subcategory**: its
composite with the inclusion does, and the inclusion of a full subcategory reflects
isomorphisms. -/
theorem isInvertedBy_isoModSerre_finiteCoherentSheafFunctor :
    haveI := isSerreClass_irrelevantModules.{u, u, w} 𝒜 Nat.one_pos
    (ObjectProperty.isoModSerre (irrelevantModules.{u, u, w} 𝒜 1)).IsInvertedBy
      (finiteCoherentSheafFunctor.{u, w} 𝒜) := by
  have := isSerreClass_irrelevantModules.{u, u, w} 𝒜 Nat.one_pos
  intro M N f hf
  have h1 : IsIso ((finiteAssociatedSheafFunctor.{u, w} 𝒜).map f) :=
    isInvertedBy_isoModSerre_irrelevantModules 𝒜 Nat.one_pos f hf
  have : IsIso (((Stacks.SheafOfModules.coherentModules (projRingSheaf 𝒜)).ι).map
      ((finiteCoherentSheafFunctor.{u, w} 𝒜).map f)) := h1
  exact isIso_of_reflects_iso _ (Stacks.SheafOfModules.coherentModules (projRingSheaf 𝒜)).ι

/-- **The arrow of Stacks 0BXD**: the functor

`Mod^fg_A / Mod^fg_{A, torsion} ⟶ Coh(𝒪_X)`

induced by `M ↦ M̃`, obtained by factoring the corestricted functor through the localization at the
isomorphisms modulo the torsion subcategory. -/
def coherentQuotientFunctor :
    IrrelevantQuotient.{u, u, w} 𝒜 (d := 1) Nat.one_pos ⥤
      Stacks.SheafOfModules.CoherentModules (projRingSheaf 𝒜) :=
  haveI := isSerreClass_irrelevantModules.{u, u, w} 𝒜 Nat.one_pos
  Localization.lift (finiteCoherentSheafFunctor.{u, w} 𝒜)
    (isInvertedBy_isoModSerre_finiteCoherentSheafFunctor.{u, w} 𝒜)
    (toIrrelevantQuotient.{u, u, w} 𝒜 Nat.one_pos)

/-- The induced functor composed with the quotient functor is `M ↦ M̃` again. -/
def coherentQuotientFunctorFac :
    toIrrelevantQuotient.{u, u, w} 𝒜 Nat.one_pos ⋙ coherentQuotientFunctor.{u, w} 𝒜 ≅
      finiteCoherentSheafFunctor.{u, w} 𝒜 :=
  haveI := isSerreClass_irrelevantModules.{u, u, w} 𝒜 Nat.one_pos
  Localization.fac (finiteCoherentSheafFunctor.{u, w} 𝒜)
    (isInvertedBy_isoModSerre_finiteCoherentSheafFunctor.{u, w} 𝒜)
    (toIrrelevantQuotient.{u, u, w} 𝒜 Nat.one_pos)

/-- **The corestricted functor, read in all sheaves of `𝒪_X`-modules, is the functor already
built.** Both are lifts through the localization of the same functor `M ↦ M̃`, so they are
isomorphic by the uniqueness of such a lift. -/
def coherentQuotientFunctorCompι :
    coherentQuotientFunctor.{u, w} 𝒜 ⋙
        (Stacks.SheafOfModules.coherentModules (projRingSheaf 𝒜)).ι ≅
      irrelevantQuotientFunctor.{u, w} 𝒜 (d := 1) Nat.one_pos :=
  haveI := isSerreClass_irrelevantModules.{u, u, w} 𝒜 Nat.one_pos
  letI : Localization.Lifting (toIrrelevantQuotient.{u, u, w} 𝒜 Nat.one_pos)
      (ObjectProperty.isoModSerre (irrelevantModules.{u, u, w} 𝒜 1))
      (finiteCoherentSheafFunctor.{u, w} 𝒜) (coherentQuotientFunctor.{u, w} 𝒜) :=
    ⟨coherentQuotientFunctorFac.{u, w} 𝒜⟩
  letI : Localization.Lifting (toIrrelevantQuotient.{u, u, w} 𝒜 Nat.one_pos)
      (ObjectProperty.isoModSerre (irrelevantModules.{u, u, w} 𝒜 1))
      (finiteAssociatedSheafFunctor.{u, w} 𝒜)
      (irrelevantQuotientFunctor.{u, w} 𝒜 (d := 1) Nat.one_pos) :=
    ⟨irrelevantQuotientFunctorFac.{u, w} 𝒜 Nat.one_pos⟩
  Localization.liftNatIso (toIrrelevantQuotient.{u, u, w} 𝒜 Nat.one_pos)
    (ObjectProperty.isoModSerre (irrelevantModules.{u, u, w} 𝒜 1))
    (finiteCoherentSheafFunctor.{u, w} 𝒜 ⋙
      (Stacks.SheafOfModules.coherentModules (projRingSheaf 𝒜)).ι)
    (finiteAssociatedSheafFunctor.{u, w} 𝒜)
    (coherentQuotientFunctor.{u, w} 𝒜 ⋙
      (Stacks.SheafOfModules.coherentModules (projRingSheaf 𝒜)).ι)
    (irrelevantQuotientFunctor.{u, w} 𝒜 Nat.one_pos)
    (finiteCoherentSheafFunctorCompι.{u, w} 𝒜)

/-- **The arrow of Stacks 0BXD is faithful**, for `A` generated in degree one: its composite with
the inclusion of the coherent sheaves is the faithful functor of
`Stacks.AlgebraicGeometry.ProjSerreCorrespondence.faithful_irrelevantQuotientFunctor_one`. -/
theorem faithful_coherentQuotientFunctor
    (hgen : Algebra.adjoin (𝒜 0) ((𝒜 1 : Set A)) = ⊤) :
    (coherentQuotientFunctor.{u, w} 𝒜).Faithful :=
  have := faithful_irrelevantQuotientFunctor_one.{u, w} 𝒜 hgen
  Functor.Faithful.of_comp_iso (coherentQuotientFunctorCompι.{u, w} 𝒜)

end Stacks.AlgebraicGeometry.ProjSerreCorrespondence

end
