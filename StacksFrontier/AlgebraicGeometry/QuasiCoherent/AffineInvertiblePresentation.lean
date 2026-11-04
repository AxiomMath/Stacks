module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackInvertible.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparison
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneModule.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleTrivialization.Sheaf
public import StacksFrontier.AlgebraicGeometry.PicardUFD.Affine
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge

/-!
# An invertible sheaf on an affine scheme comes from an invertible module

Let `W` be an affine scheme and `N` an invertible sheaf of `𝒪_W`-modules in the sense of
[Stacks, Tag 01CS].  This file produces an invertible `Γ(W, ⊤)`-module `M` together with an
isomorphism

`N ≅ (W.isoSpec.hom)^* (M^~)`,

that is, it puts an abstract invertible sheaf on an affine scheme into the presentation "inverse
image along `W ≅ Spec Γ(W, ⊤)` of the sheaf associated to a module".

The presentation is the one in which `AlgebraicGeometry.eq_of_iso_pullbackTensorFunctor` and
`AlgebraicGeometry.eq_of_iso_pullbackTensorFunctor_of_range_subset` state their invertible
sheaves, because it is the form in which the affine Gabriel–Rosenberg reconstruction
(`AlgebraicGeometry.exists_schemeIso_invertibleSheaf_of_quasicoherentEquivalence`) produces
them.  What those statements could not do before is accept an invertible sheaf that arrives in
*any other* way — in particular the restriction `k^*N` of an invertible sheaf along a morphism
`k : W' ⟶ W` of affine schemes, which is what the gluing step of [Stacks, Tag 0GPJ] has to feed
them after shrinking the source.  Both forms are supplied below.

## Main results

* `AlgebraicGeometry.exists_module_invertible_iso_tilde`: on `Spec R` itself, an invertible sheaf
  of modules is `M^~` for an invertible `R`-module `M`.
* `AlgebraicGeometry.exists_module_invertible_iso_pullback_tilde`: on an affine scheme `W`, an
  invertible sheaf is the inverse image along `W.isoSpec.hom` of `M^~` for an invertible
  `Γ(W, ⊤)`-module `M`.
* `AlgebraicGeometry.exists_module_invertible_iso_pullback_tilde_of_hom`: the same for the
  inverse image `k^*N` of an invertible sheaf along a morphism `k : W' ⟶ W` with `W'` affine;
  `W` itself need not be affine.

## The route

Everything is assembled from existing statements; no new mathematics is involved.

* An invertible sheaf of modules on a scheme is quasi-coherent
  (`Stacks.SheafOfModules.Scheme.isQuasicoherent_of_isInvertible`), so on `Spec R` the counit
  `Γ(F)^~ ⟶ F` of the tilde–Γ adjunction is an isomorphism by Mathlib's
  `AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent`.  This already gives the
  module, namely `AlgebraicGeometry.moduleSpecΓFunctor.obj F`, and the isomorphism.
* That the module is *invertible* is the converse direction of [Stacks, Tag 0B8M]
  (`Stacks.SheafOfModules.Scheme.isInvertible_iff_isFiniteLocallyFreeOfRank_one`), followed by
  [Stacks, Tag 05JM] (`tilde_isFiniteLocallyFreeOfRank_iff`) and [Stacks, Tag 0B8I]
  (`Module.invertible_of_isFiniteLocallyFreeOfRank_one`): invertible is finite locally free of
  rank one, which descends through the tilde dictionary to the module and is there the same thing
  as invertibility.  The two spellings of "finite locally free of rank one" for a sheaf of
  modules that meet in the middle of that chain are reconciled by
  `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_of_sheafOfModules`.
* The passage from `Spec Γ(W, ⊤)` to an abstract affine `W` is inverse image along
  `AlgebraicGeometry.Scheme.isoSpec`, with invertibility transported by [Stacks, Tag 0B8L]
  (`Stacks.RingedSpace.modulePullback_isInvertible`) and the two inverse images cancelled by
  `AlgebraicGeometry.Scheme.Modules.pullbackComp`, `pullbackCongr` and `pullbackId`.

The restriction statement is immediate from the affine one: `k^*N` is invertible on `W'` by Tag
0B8L again, so the affine statement applies to it directly, and no comparison of the two base
changes is needed.  Consequently the module it produces is only asserted to exist; it is *not*
identified with the base change `Γ(W', ⊤) ⊗_{Γ(W, ⊤)} M` of the module belonging to `N`.  That
identification would be `Stacks.AlgebraicGeometry.AffineTilde.tildeOfPullbackIso` and is not
proved here, because no consumer needs it: the rigidity statements quantify over the module.

## Implementation notes

**Why the invertible module is not read off as `Γ(N, ⊤)`.**
`Stacks.Discriminant.isInvertible_iff_forall_module_invertible` gives `Module.Invertible Γ(W, V)
Γ(N, V)` for every affine open `V`, and in particular for `V = ⊤`.  Using it would still leave
the isomorphism to be built, and the comparison of `Γ(N, ⊤)` with the module that the counit of
the tilde–Γ adjunction actually produces is available only as a `private` declaration
(`moduleSpecΓPullbackLinearEquiv` in
`StacksFrontier/AlgebraicGeometry/Morphisms/EtaleNeighbourhood/AffineApproximationModule.lean`).
Taking the module from the counit instead makes the isomorphism free and moves the whole cost to
the invertibility, where the rank-one chain above discharges it.

**The transparency block.**  The structure sheaf of a scheme is named both as
`AlgebraicGeometry.Scheme.ringCatSheaf` and as
`Stacks.SheafOfModules.TensorSheafification.structureSheaf` of its structure presheaf, and
instance search, which runs at `reducible` transparency, sees through neither chain.  The same
`implicit_reducible` list is declared in
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/AffineReconstruction.lean` and
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/ReconstructionGlobalIso.lean` for the same reason,
and the statements below are the ones those files consume.

**No `stacks` attribute.**  Nothing here is an assertion of the source: Tags 0B8M, 05JM, 0B8I and
0B8L are consumed and are claimed where they are proved, and Tag 0GPJ is claimed in
`AffineReconstruction.lean` for the affine case only.

## References

* [Stacks Project, Definition 17.23.1 (Tag 01CS)](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Lemma 17.23.2 (Tag 0B8M)](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Lemma 10.78.2 (Tag 0B8I)](https://stacks.math.columbia.edu/tag/0B8I)
* [Stacks Project, Lemma 17.23.3 (Tag 0B8L)](https://stacks.math.columbia.edu/tag/0B8L)
* [Stacks Project, Lemma 29.4.1 (Tag 05JM)](https://stacks.math.columbia.edu/tag/05JM)
* [Stacks Project, Proposition 56.6.6 (Tag 0GPJ)](https://stacks.math.columbia.edu/tag/0GPJ)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/- One object is named through two chains of definitions — the structure sheaf of a scheme as
`AlgebraicGeometry.Scheme.ringCatSheaf` and as
`Stacks.SheafOfModules.TensorSheafification.structureSheaf` of its structure presheaf — and
instance search, which works at `reducible` transparency, sees through neither.  The same list is
declared in `StacksFrontier/AlgebraicGeometry/QuasiCoherent/AffineReconstruction.lean` and
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/ReconstructionGlobalIso.lean`. -/
attribute [local implicit_reducible] Stacks.SheafOfModules.TensorSheafification.structureSheaf
  AlgebraicGeometry.SheafedSpace.sheaf AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules.Hom AlgebraicGeometry.Scheme.Modules.instCategory
  CategoryTheory.sheafCompose TopCat.Sheaf

/-- **An invertible sheaf of modules on `Spec R` is the sheaf associated to an invertible
`R`-module.**

The module is the one the tilde–Γ adjunction supplies, `AlgebraicGeometry.moduleSpecΓFunctor.obj
F`: an invertible sheaf is quasi-coherent, so the counit `Γ(F)^~ ⟶ F` is an isomorphism.  Its
invertibility is the chain Tag 0B8M (invertible is finite locally free of rank one), Tag 05JM
(finite local freeness of rank one passes through the tilde dictionary) and Tag 0B8I (a module
finite locally free of rank one is invertible). -/
theorem exists_module_invertible_iso_tilde (R : CommRingCat.{u}) (F : (Spec R).Modules)
    (hF : Stacks.SheafOfModules.IsInvertible (Spec R).presheaf (Spec R).ringCatSheaf.2 F) :
    ∃ M : ModuleCat.{u} R, Module.Invertible R M ∧ Nonempty (tilde M ≅ F) := by
  have hF' := hF
  have hqc : F.IsQuasicoherent :=
    Stacks.SheafOfModules.Scheme.isQuasicoherent_of_isInvertible _ F
  have hiso : IsIso (Scheme.Modules.fromTildeΓ F) :=
    @Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent _ F hqc
  set M : ModuleCat.{u} R := moduleSpecΓFunctor.obj F with hM
  have e : tilde M ≅ F := @asIso _ _ _ _ (Scheme.Modules.fromTildeΓ F) hiso
  have hL : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F 1 :=
    (Stacks.SheafOfModules.Scheme.isInvertible_iff_isFiniteLocallyFreeOfRank_one _ F).1 hF'
  have hpt : Scheme.Modules.IsFiniteLocallyFreeOfRank (tilde M) 1 := by
    intro x
    obtain ⟨U, hxU, ⟨φ⟩⟩ :=
      Scheme.Modules.isFiniteLocallyFreeOfRank_of_sheafOfModules F 1 hL x
    exact ⟨U, hxU, ⟨(Scheme.Modules.restrictFunctor (Scheme.Opens.ι U)).mapIso e ≪≫ φ⟩⟩
  have hmod : Module.IsFiniteLocallyFreeOfRank R M 1 :=
    (tilde_isFiniteLocallyFreeOfRank_iff (R : Type u) (M : Type u) 1).mp hpt
  exact ⟨M, Module.invertible_of_isFiniteLocallyFreeOfRank_one hmod, ⟨e⟩⟩

/-- **An invertible sheaf of modules on an affine scheme is the inverse image along
`W ≅ Spec Γ(W, ⊤)` of the sheaf associated to an invertible `Γ(W, ⊤)`-module.**

This is the presentation in which `AlgebraicGeometry.eq_of_iso_pullbackTensorFunctor` and
`AlgebraicGeometry.eq_of_iso_pullbackTensorFunctor_of_range_subset` state their invertible
sheaves.  Transporting `N` to `Spec Γ(W, ⊤)` along `W.isoSpec.inv` keeps it invertible by Tag
0B8L, `AlgebraicGeometry.exists_module_invertible_iso_tilde` applies there, and the two inverse
images cancel. -/
theorem exists_module_invertible_iso_pullback_tilde (W : Scheme.{u}) [IsAffine W]
    (N : SheafOfModules.{u} W.ringCatSheaf)
    (hN : Stacks.SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 N) :
    ∃ M : ModuleCat.{u} Γ(W, ⊤), Module.Invertible Γ(W, ⊤) M ∧
      Nonempty (N ≅ (Stacks.RingedSpace.pullbackFunctor
        W.isoSpec.hom.toLRSHom.toShHom).obj (tilde M)) := by
  have hF : Stacks.SheafOfModules.IsInvertible (Spec Γ(W, ⊤)).presheaf
      (Spec Γ(W, ⊤)).ringCatSheaf.2 ((Scheme.Modules.pullback W.isoSpec.inv).obj N) :=
    @Stacks.RingedSpace.modulePullback_isInvertible _ _ W.isoSpec.inv.toLRSHom.toShHom N hN
  obtain ⟨M, hM, ⟨e⟩⟩ := exists_module_invertible_iso_tilde Γ(W, ⊤) _ hF
  refine ⟨M, hM, ⟨?_⟩⟩
  refine (((Scheme.Modules.pullbackComp W.isoSpec.hom W.isoSpec.inv).app N ≪≫
      (Scheme.Modules.pullbackCongr W.isoSpec.hom_inv_id).app N ≪≫
      (Scheme.Modules.pullbackId W).app N).symm ≪≫ ?_)
  exact (Scheme.Modules.pullback W.isoSpec.hom).mapIso e.symm

/-- **The inverse image of an invertible sheaf along a morphism with affine source is again of
that form.**  For `k : W' ⟶ W` with `W'` affine and `N` invertible on `W` — which need not be
affine — the sheaf `k^*N` is the inverse image along `W' ≅ Spec Γ(W', ⊤)` of the sheaf associated
to an invertible `Γ(W', ⊤)`-module.

This is what puts a restricted invertible sheaf back into the presentation that the rigidity
statements of `StacksFrontier/AlgebraicGeometry/QuasiCoherent/ReconstructionGlobalIso.lean` ask for.
The module is not identified with a base change of the module belonging to `N`; see the
implementation notes of this file. -/
theorem exists_module_invertible_iso_pullback_tilde_of_hom {W W' : Scheme.{u}} [IsAffine W']
    (k : W' ⟶ W) (N : SheafOfModules.{u} W.ringCatSheaf)
    (hN : Stacks.SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 N) :
    ∃ M : ModuleCat.{u} Γ(W', ⊤), Module.Invertible Γ(W', ⊤) M ∧
      Nonempty ((Scheme.Modules.pullback k).obj N ≅ (Stacks.RingedSpace.pullbackFunctor
        W'.isoSpec.hom.toLRSHom.toShHom).obj (tilde M)) :=
  exists_module_invertible_iso_pullback_tilde W' _
    (@Stacks.RingedSpace.modulePullback_isInvertible _ _ k.toLRSHom.toShHom N hN)

end AlgebraicGeometry

end
