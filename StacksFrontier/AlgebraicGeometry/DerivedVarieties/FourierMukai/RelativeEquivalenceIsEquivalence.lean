module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeUnitSingle
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.DiagonalKernelIdentity
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.PerfectPreservationCriteria
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.ProjectionFormulaDischarged
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.RelativeEquivalence
public import StacksFrontier.AlgebraicGeometry.Duality.IdentityFourierMukaiKernel
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Affine
public import StacksFrontier.AlgebraicGeometry.Perfect.TorIndependence
import StacksCore.Tactic.StacksAttribute

/-!
# The Fourier-Mukai functors of a relative equivalence are equivalences

Let `S` be a scheme, let `f : X ⟶ S` and `g : Y ⟶ S` be smooth and proper, and let `K` be the
Fourier-Mukai kernel of a relative equivalence from `X` to `Y` over `S` in the sense of
[Stacks, Tag 0G0I] (`AlgebraicGeometry.IsRelativeEquivalenceKernel`). Then both Fourier-Mukai
functors attached to `K`,

`Φ_K : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` of [Stacks, Tag 0FYR] and
`Φ_K : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` of [Stacks, Tag 0FYT],

are equivalences. This is [Stacks, Tag 0G0J].

The argument is the source's. The definition of a relative equivalence supplies a perfect `K'`
on `Y ×_S X` whose two convolutions with `K` are the diagonal kernels of
[Stacks, Tag 0FYV]. Composition of Fourier-Mukai functors, [Stacks, Tag 0FYS]
(`AlgebraicGeometry.quasiCoherentFourierMukaiComp`), turns `Φ_{K'} ∘ Φ_K` into the Fourier-Mukai
functor of that convolution; the convolution isomorphism rewrites the kernel as `𝒪_Δ`; and the
clause of [Stacks, Tag 0FYV] identifying `Φ_{𝒪_Δ}` with the identity finishes both composites.
A functor with an inverse up to isomorphism on both sides is an equivalence.

## Main definitions

* `AlgebraicGeometry.DiagonalFourierMukaiIsIdentity` — the clause of [Stacks, Tag 0FYV] that
  `Φ_{𝒪_Δ}` is the identity functor of `D(𝒪_X)`, as a proposition in one variable-free shape.
* `AlgebraicGeometry.FourierMukaiPreservesPerfect` — clause (3) of [Stacks, Tag 0FYT], likewise.
* `AlgebraicGeometry.perfectFourierMukai` — the restriction `Φ_K : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)`.

## Main results

* `AlgebraicGeometry.isEquivalence_quasiCoherentFourierMukai` — **[Stacks, Tag 0G0J]**, the
  clause for `D_QCoh`.
* `AlgebraicGeometry.isEquivalence_perfectFourierMukai` — **[Stacks, Tag 0G0J]**, the clause for
  `D_perf`.

## Implementation notes

*The two clauses are separate carriers.* The source states one lemma with two conclusions, one
about `D_QCoh` and one about `D_perf`. The two live in different categories and the second needs
an input the first does not, so each is a theorem of its own and each carries the tag.

*Nothing is assumed.* Both theorems take exactly the source's hypotheses — `f` and `g` smooth and
proper, `K` a relative-equivalence kernel — and nothing else. Four auxiliary Stacks results enter
the proof, and each is a theorem of this library, used here directly:

* [Stacks, Tag 08IB] and [Stacks, Tag 08EU], the two inputs that this library's form of
  [Stacks, Tag 0FYS] requires (see the module documentation of
  `StacksFrontier/AlgebraicGeometry/DerivedVarieties/FourierMukai/Composition.lean`), are
  `AlgebraicGeometry.derivedBaseChangeIsIsoOnQuasicoherent` and
  `AlgebraicGeometry.projectionFormulaIsIsoOnQuasicoherent`.
* The closing assertion of [Stacks, Tag 0FYV], that `Φ_{𝒪_Δ}` is the identity for a separated
  `f`, is `AlgebraicGeometry.fourierMukaiDiagonalKernelIso`; `f` and `g` are proper, hence
  separated.
* Clause (3) of [Stacks, Tag 0FYT], that `Φ_K` carries perfect objects to perfect objects for a
  perfect `K` and a proper flat `X ⟶ S` of finite presentation, is
  `AlgebraicGeometry.isPerfect_fourierMukai_of_isPerfect_kernel_of_properFlatFinitePresentation`.
  It is what makes the functor `Φ_K : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` exist, so
  `AlgebraicGeometry.perfectFourierMukai` appeals to it; it is applied to both `K` and `K'`, the
  latter produced inside the definition of a relative equivalence.

The propositions `AlgebraicGeometry.DiagonalFourierMukaiIsIdentity` and
`AlgebraicGeometry.FourierMukaiPreservesPerfect` state the last two of those results in a shape
with no free variables; they are kept because other modules read them, not because anything here
is conditional on them.

Nothing about the class of objects the tag speaks of is narrowed: both theorems are stated for an
arbitrary relative-equivalence kernel over arbitrary smooth proper `f` and `g`.

*Everything else is proved here*: that a perfect kernel has quasi-coherent cohomology, that an
isomorphism of kernels induces an isomorphism of Fourier-Mukai functors, that `X` and `X` are tor
independent over `S` when `f` is flat (needed to apply 0FYS at the triple `(X, Y, X)`), the
descent of the two composite isomorphisms from `D_QCoh` to `D_perf` along the fully faithful
inclusion, and the passage from a two-sided inverse up to isomorphism to an equivalence.

*The perfect case runs through the quasi-coherent one.* [Stacks, Tag 0FYS] is available in this
library only after restricting to `D_QCoh`, as the source states it. Since a perfect complex has
quasi-coherent cohomology, `D_perf(𝒪_X)` sits inside `D_QCoh(𝒪_X)`, and the composite
isomorphisms on `D_perf` are obtained from those on `D_QCoh` by whiskering with that inclusion
and cancelling the fully faithful inclusion of `D_perf` into `D(𝒪_X)`.

## References

* [Stacks Project, Tag 0G0J](https://stacks.math.columbia.edu/tag/0G0J)
* [Stacks Project, Tag 0G0I](https://stacks.math.columbia.edu/tag/0G0I)
* [Stacks Project, Tag 0FYQ](https://stacks.math.columbia.edu/tag/0FYQ)
* [Stacks Project, Tag 0FYR](https://stacks.math.columbia.edu/tag/0FYR)
* [Stacks Project, Tag 0FYS](https://stacks.math.columbia.edu/tag/0FYS)
* [Stacks Project, Tag 0FYT](https://stacks.math.columbia.edu/tag/0FYT)
* [Stacks Project, Tag 0FYV](https://stacks.math.columbia.edu/tag/0FYV)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 0B55](https://stacks.math.columbia.edu/tag/0B55)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.PerfectComplexes (IsPerfect)
open Stacks.DerivedTensor.RingedSite

universe u

namespace AlgebraicGeometry

-- The priority selects the standard model of the derived categories, the one the Fourier-Mukai
-- functor, the convolution kernel and the diagonal kernel are all read at, over the locally
-- small model arriving with the imports.
attribute [local instance 100000] HasDerivedCategory.standard

/-! ### Two Stacks results in variable-free shape -/

/-- **The fourth assertion of [Stacks, Tag 0FYV]**: for a separated morphism `f : X ⟶ S`, the
Fourier-Mukai functor of the diagonal kernel `𝒪_Δ = RΔ_{X/S,*}𝒪_X` is the identity functor of
`D(𝒪_X)`.

The source's proof is the chain
`R pr_{2,*}(L pr_1^*M ⊗^𝐋 RΔ_*𝒪_X) = R pr_{2,*}RΔ_*(LΔ^*L pr_1^*M) = M`, whose middle equality
is the general projection formula [Stacks, Tag 0B55]; this library proves the assertion instead
through the computation of `Φ_{Rs_*𝒪_Z}` at a section `s`, as
`AlgebraicGeometry.fourierMukaiDiagonalKernelIso`. This is that statement in a shape with no free
variables, for modules that want it as a single proposition. -/
abbrev DiagonalFourierMukaiIsIdentity : Prop :=
  ∀ {S X : Scheme.{u}} (f : X ⟶ S), IsSeparated f →
    Nonempty (fourierMukai f f (diagonalKernel f) ≅ 𝟭 (DerivedCategory X.Modules))

/-- **[Stacks, Tag 0FYT], clause (3)**: if `X ⟶ S` is proper, flat and of finite presentation and
`K` is a perfect object of `D(𝒪_{X ×_S Y})`, then the Fourier-Mukai functor `Φ_K` carries every
perfect object of `D(𝒪_X)` to a perfect object of `D(𝒪_Y)`.

The clause is proved in the source's own form as
`AlgebraicGeometry.isPerfect_fourierMukai_of_isPerfect_kernel_of_properFlatFinitePresentation`.
This is that statement in a shape with no free variables, for modules that want it as a single
proposition. -/
abbrev FourierMukaiPreservesPerfect : Prop :=
  ∀ {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S), IsProper f → Flat f →
    LocallyOfFinitePresentation f →
      ∀ K : DerivedCategory (Limits.pullback f g).Modules,
        IsPerfect (X := (Limits.pullback f g).toRingedSpace) K →
          ∀ M : DerivedCategory X.Modules, IsPerfect (X := X.toRingedSpace) M →
            IsPerfect (X := Y.toRingedSpace) ((fourierMukai f g K).obj M)

/-! ### Isomorphic kernels give isomorphic Fourier-Mukai functors -/

section Kernels

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- An isomorphism of kernels induces an isomorphism of the Fourier-Mukai functors they define:
`Φ_K` depends on `K` only through the functor `- ⊗^𝐋_{𝒪_{X ×_S Y}} K`, which is functorial in
`K`. -/
private def fourierMukaiIsoOfKernelIso
    {K K' : DerivedCategory (Limits.pullback f g).Modules} (e : K ≅ K') :
    fourierMukai f g K ≅ fourierMukai f g K' :=
  Functor.isoWhiskerLeft (fourierMukaiPullback f g)
    (Functor.isoWhiskerRight
      ((derivedTensorProductFunctor (Limits.pullback f g).toRingedSpace.sheaf).flip.mapIso e)
      (fourierMukaiPushforward f g))

/-- The isomorphism of Fourier-Mukai functors induced by an isomorphism of kernels, read on the
quasi-coherent derived categories. -/
private def quasiCoherentFourierMukaiIsoOfKernelIso [QuasiCompact f] [QuasiSeparated f]
    {K K' : DerivedCategory (Limits.pullback f g).Modules} (hK : IsQCohAll K)
    (hK' : IsQCohAll K') (e : K ≅ K') :
    quasiCoherentFourierMukai f g K hK ≅ quasiCoherentFourierMukai f g K' hK' := by
  refine NatIso.ofComponents
    (fun M => ObjectProperty.isoMk _ ((fourierMukaiIsoOfKernelIso f g e).app M.obj)) ?_
  intro M N v
  apply ObjectProperty.hom_ext
  exact (fourierMukaiIsoOfKernelIso f g e).hom.naturality v.hom

end Kernels

/-! ### The quasi-coherent composite isomorphism -/

section Composite

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- The Fourier-Mukai functor of the diagonal kernel is the identity of `D_QCoh(𝒪_X)`, given the
carried assertion of [Stacks, Tag 0FYV] that it is the identity of `D(𝒪_X)`: the two functors
agree on underlying objects, so the isomorphism restricts componentwise. -/
private def quasiCoherentFourierMukaiDiagonalIso [IsSeparated f] [QuasiCompact f]
    [QuasiSeparated f]
    (ediag : fourierMukai f f (diagonalKernel f) ≅ 𝟭 (DerivedCategory X.Modules)) :
    quasiCoherentFourierMukai f f (diagonalKernel f)
        (isQuasicoherent_homology_diagonalKernel f) ≅
      𝟭 (QuasicoherentDerivedCategory X) := by
  refine NatIso.ofComponents (fun M => ObjectProperty.isoMk _ (ediag.app M.obj)) ?_
  intro M N v
  apply ObjectProperty.hom_ext
  exact ediag.hom.naturality v.hom

/-- **The composite of the two Fourier-Mukai functors of a relative equivalence is the identity
of `D_QCoh(𝒪_X)`.** Composition of Fourier-Mukai functors, [Stacks, Tag 0FYS] at the triple
`(X, Y, X)`, identifies `Φ_{K'} ∘ Φ_K` with the Fourier-Mukai functor of the convolution of `K`
and `K'`; the isomorphism `eX` of [Stacks, Tag 0G0I] rewrites that kernel as the diagonal kernel
`𝒪_Δ`; and `ediag` identifies `Φ_{𝒪_Δ}` with the identity.

`X` and `X` are tor independent over `S` because `f` is flat, which is what lets
[Stacks, Tag 0FYS] be applied at `(X, Y, X)`. -/
private def quasiCoherentFourierMukaiCompIso
    (h08IB : DerivedBaseChangeIsIsoOnQuasicoherent.{u})
    (h08EU : ProjectionFormulaIsIsoOnQuasicoherent.{u}) [Flat f] [Flat g] [IsSeparated f]
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
    {K : DerivedCategory (Limits.pullback f g).Modules} (hK : IsQCohAll K)
    {K' : DerivedCategory (Limits.pullback g f).Modules} (hK' : IsQCohAll K')
    (ediag : fourierMukai f f (diagonalKernel f) ≅ 𝟭 (DerivedCategory X.Modules))
    (e : diagonalKernel f ≅ fourierMukaiConvolution f g f K K') :
    quasiCoherentFourierMukai f g K hK ⋙ quasiCoherentFourierMukai g f K' hK' ≅
      𝟭 (QuasicoherentDerivedCategory X) :=
  quasiCoherentFourierMukaiComp f g f h08IB h08EU (torIndependent_of_flat_left f f) hK hK' ≪≫
    (quasiCoherentFourierMukaiIsoOfKernelIso f f (isQuasicoherent_homology_diagonalKernel f)
      (isQuasicoherent_homology_fourierMukaiConvolution f g f hK hK') e).symm ≪≫
    quasiCoherentFourierMukaiDiagonalIso f ediag

end Composite

/-! ### The two equivalences -/

section Main

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- **The Fourier-Mukai kernel of a relative equivalence has quasi-coherent cohomology
sheaves**, being perfect by the first clause of [Stacks, Tag 0G0I]. -/
theorem isQuasicoherent_homology_of_isRelativeEquivalenceKernel
    {K : DerivedCategory (Limits.pullback f g).Modules}
    (hK : IsRelativeEquivalenceKernel f g K) (j : ℤ) :
    ((DerivedCategory.homologyFunctor (Limits.pullback f g).Modules j).obj
      K).IsQuasicoherent :=
  PerfectApproximation.isQuasicoherent_homology_of_isPerfect _ K hK.1 j

/-- **The Fourier-Mukai functor on the perfect derived categories**, the restriction
`Φ_K : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` named in [Stacks, Tag 0FYQ]. It exists for a perfect `K` and a
proper flat `X ⟶ S` of finite presentation by clause (3) of [Stacks, Tag 0FYT],
`AlgebraicGeometry.isPerfect_fourierMukai_of_isPerfect_kernel_of_properFlatFinitePresentation`. -/
def perfectFourierMukai [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f] (K : DerivedCategory (Limits.pullback f g).Modules)
    (hK : IsPerfect (X := (Limits.pullback f g).toRingedSpace) K) :
    (Stacks.Duality.perfectDerivedObjects X).FullSubcategory ⥤
      (Stacks.Duality.perfectDerivedObjects Y).FullSubcategory :=
  fourierMukaiOn f g K _ _ fun M =>
    isPerfect_fourierMukai_of_isPerfect_kernel_of_properFlatFinitePresentation f g K hK M.obj
      M.property

/-- A perfect complex has quasi-coherent cohomology, so `D_perf(𝒪_X)` maps to `D_QCoh(𝒪_X)`. -/
private def perfectToQuasicoherent (X : Scheme.{u}) :
    (Stacks.Duality.perfectDerivedObjects X).FullSubcategory ⥤ QuasicoherentDerivedCategory X :=
  (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf)).lift
    (Stacks.Duality.perfectDerivedObjects X).ι fun M =>
    PerfectApproximation.isQuasicoherent_homology_of_isPerfect _ M.obj M.property

/-- An isomorphism `F ⋙ G ≅ 𝟭` of functors on `D_QCoh` descends to `D_perf` along the fully
faithful inclusions, once the functors on `D_perf` are compatible with those on `D_QCoh`. -/
private def perfectCompIsoOfQuasiCoherent {X Y : Scheme.{u}}
    {F : (Stacks.Duality.perfectDerivedObjects X).FullSubcategory ⥤
      (Stacks.Duality.perfectDerivedObjects Y).FullSubcategory}
    {G : (Stacks.Duality.perfectDerivedObjects Y).FullSubcategory ⥤
      (Stacks.Duality.perfectDerivedObjects X).FullSubcategory}
    {Fq : QuasicoherentDerivedCategory X ⥤ QuasicoherentDerivedCategory Y}
    {Gq : QuasicoherentDerivedCategory Y ⥤ QuasicoherentDerivedCategory X}
    (h : (perfectToQuasicoherent X ⋙ Fq ⋙ Gq) ⋙
      (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι =
      (F ⋙ G) ⋙ (Stacks.Duality.perfectDerivedObjects X).ι)
    (e : Fq ⋙ Gq ≅ 𝟭 _) : F ⋙ G ≅ 𝟭 _ :=
  Functor.fullyFaithfulCancelRight (Stacks.Duality.perfectDerivedObjects X).ι
    ((eqToIso h).symm ≪≫ Functor.isoWhiskerRight (Functor.isoWhiskerLeft _ e) _ ≪≫
      eqToIso rfl)

/-- **[Stacks, Tag 0G0J], the clause for `D_QCoh`.** Let `f : X ⟶ S` and `g : Y ⟶ S` be smooth
and proper and let `K` be the Fourier-Mukai kernel of a relative equivalence from `X` to `Y` over
`S`, [Stacks, Tag 0G0I]. Then the Fourier-Mukai functor
`Φ_K : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` of [Stacks, Tag 0FYR] is an equivalence.

The inverse is `Φ_{K'}` for the kernel `K'` the definition of a relative equivalence supplies:
its two composites with `Φ_K` are, by [Stacks, Tag 0FYS], the Fourier-Mukai functors of the two
convolutions, which the definition identifies with the diagonal kernels, whose Fourier-Mukai
functors are the identities. [Stacks, Tag 0FYS] is used through
`AlgebraicGeometry.quasiCoherentFourierMukaiComp`, whose two inputs [Stacks, Tag 08IB] and
[Stacks, Tag 08EU] are the theorems `AlgebraicGeometry.derivedBaseChangeIsIsoOnQuasicoherent` and
`AlgebraicGeometry.projectionFormulaIsIsoOnQuasicoherent`; the clause of [Stacks, Tag 0FYV] that
`Φ_{𝒪_Δ}` is the identity is `AlgebraicGeometry.fourierMukaiDiagonalKernelIso`. -/
@[stacks 0G0J "Phi_K : D_QCoh(O_X) -> D_QCoh(O_Y) is an equivalence"]
theorem isEquivalence_quasiCoherentFourierMukai
    [Smooth f] [Smooth g] [IsProper f] [IsProper g]
    {K : DerivedCategory (Limits.pullback f g).Modules}
    (hK : IsRelativeEquivalenceKernel f g K) :
    (quasiCoherentFourierMukai f g K
      (isQuasicoherent_homology_of_isRelativeEquivalenceKernel f g hK)).IsEquivalence := by
  obtain ⟨hKperf, K', hK'perf, ⟨eX⟩, ⟨eY⟩⟩ := id hK
  have hKq : IsQCohAll K := isQuasicoherent_homology_of_isRelativeEquivalenceKernel f g hK
  have hK'q : IsQCohAll K' := fun j =>
    PerfectApproximation.isQuasicoherent_homology_of_isPerfect _ K' hK'perf j
  exact Functor.IsEquivalence.mk' (quasiCoherentFourierMukai g f K' hK'q)
    (quasiCoherentFourierMukaiCompIso f g derivedBaseChangeIsIsoOnQuasicoherent
      projectionFormulaIsIsoOnQuasicoherent hKq hK'q (fourierMukaiDiagonalKernelIso f) eX).symm
    (quasiCoherentFourierMukaiCompIso g f derivedBaseChangeIsIsoOnQuasicoherent
      projectionFormulaIsIsoOnQuasicoherent hK'q hKq (fourierMukaiDiagonalKernelIso g) eY)

/-- **[Stacks, Tag 0G0J], the clause for `D_perf`.** Let `f : X ⟶ S` and `g : Y ⟶ S` be smooth
and proper and let `K` be the Fourier-Mukai kernel of a relative equivalence from `X` to `Y` over
`S`, [Stacks, Tag 0G0I]. Then the Fourier-Mukai functor
`Φ_K : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` of [Stacks, Tag 0FYT] is an equivalence.

A perfect complex has quasi-coherent cohomology, so `D_perf(𝒪_X)` is a full subcategory of
`D_QCoh(𝒪_X)` on which the two functors agree with their quasi-coherent counterparts. The two
composite isomorphisms of the quasi-coherent clause therefore whisker down to `D_perf`, and the
fully faithful inclusion of `D_perf(𝒪_X)` into `D(𝒪_X)` may be cancelled. What makes the two
functors on `D_perf` exist at all is clause (3) of [Stacks, Tag 0FYT], the theorem
`AlgebraicGeometry.isPerfect_fourierMukai_of_isPerfect_kernel_of_properFlatFinitePresentation`,
appealed to inside `AlgebraicGeometry.perfectFourierMukai`. -/
@[stacks 0G0J "Phi_K : D_perf(O_X) -> D_perf(O_Y) is an equivalence"]
theorem isEquivalence_perfectFourierMukai
    [Smooth f] [Smooth g] [IsProper f] [IsProper g]
    {K : DerivedCategory (Limits.pullback f g).Modules}
    (hK : IsRelativeEquivalenceKernel f g K) :
    (perfectFourierMukai f g K hK.1).IsEquivalence := by
  obtain ⟨hKperf, K', hK'perf, ⟨eX⟩, ⟨eY⟩⟩ := id hK
  have hKq : IsQCohAll K := isQuasicoherent_homology_of_isRelativeEquivalenceKernel f g hK
  have hK'q : IsQCohAll K' := fun j =>
    PerfectApproximation.isQuasicoherent_homology_of_isPerfect _ K' hK'perf j
  exact Functor.IsEquivalence.mk' (perfectFourierMukai g f K' hK'perf)
    (perfectCompIsoOfQuasiCoherent rfl
      (quasiCoherentFourierMukaiCompIso f g derivedBaseChangeIsIsoOnQuasicoherent
        projectionFormulaIsIsoOnQuasicoherent hKq hK'q (fourierMukaiDiagonalKernelIso f) eX)).symm
    (perfectCompIsoOfQuasiCoherent rfl
      (quasiCoherentFourierMukaiCompIso g f derivedBaseChangeIsIsoOnQuasicoherent
        projectionFormulaIsIsoOnQuasicoherent hK'q hKq (fourierMukaiDiagonalKernelIso g) eY))

end Main

end AlgebraicGeometry

end
