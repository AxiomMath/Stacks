module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.ClosedImmersionKernel
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.DiagonalKernel
import StacksCore.Tactic.StacksAttribute

/-!
# The diagonal kernel is the kernel of the identity

Let `f : X ⟶ S` be a separated morphism of schemes, with diagonal
`Δ = Δ_{X/S} : X ⟶ X ×_S X`, and let

`𝒪_Δ = RΔ_*𝒪_X ∈ D(𝒪_{X ×_S X})`

be the diagonal kernel of `AlgebraicGeometry.diagonalKernel`.  The Fourier-Mukai functor
`Φ_{𝒪_Δ}` of [Stacks, Tag 0FYQ] is the identity functor of `D(𝒪_X)`.  This is the conclusion of
Example [Stacks, Tag 0FYV].

## Main results

* `AlgebraicGeometry.fourierMukaiPullbackTensorDiagonalKernelIso` — the chain
  [Stacks, Tag 0FYV] displays: `L pr_1^*(-) ⊗^𝐋 𝒪_Δ ≅ RΔ_*(-)`.
* `AlgebraicGeometry.fourierMukaiDiagonalKernelIso` — **the closing assertion of
  [Stacks, Tag 0FYV]**: `Φ_{𝒪_Δ} ≅ 𝟭` for `f` separated.
* `AlgebraicGeometry.isFourierMukaiKernel_diagonalKernel` — `𝒪_Δ` is a Fourier-Mukai kernel for
  the identity functor, in the sense of `AlgebraicGeometry.IsFourierMukaiKernel`.

## Implementation notes

*The source's chain is run once, and in general.*  For `M ∈ D(𝒪_X)` the source computes

`L pr_1^*M ⊗^𝐋 𝒪_Δ = L pr_1^*M ⊗^𝐋 RΔ_*𝒪_X = RΔ_*(LΔ^*L pr_1^*M ⊗^𝐋 𝒪_X) = RΔ_*M`

and then applies `R pr_{2,*}`.  That chain is carried out for an *arbitrary* closed immersion
`s : Z ⟶ X ×_S Y` in
`StacksFrontier/AlgebraicGeometry/DerivedVarieties/FourierMukai/ClosedImmersionKernel.lean`, as an
isomorphism of functors at each step, giving
`AlgebraicGeometry.fourierMukaiDerivedPushforwardUnitIso`:

`Φ_{Rs_*𝒪_Z} ≅ L(s ∘ pr_1)^* ⋙ R(s ∘ pr_2)_*`.

No step of it is proved again here: both declarations below only specialise those general
isomorphisms to `s = Δ`, the first stopping before `R pr_{2,*}` so that the source's displayed
chain is itself a statement, the second running on to `Φ_{𝒪_Δ} ≅ 𝟭`.

The diagonal of a separated `f` is a closed immersion and is a section of the second projection,
`Δ ≫ pr_2 = 𝟙_X`, so that general isomorphism in the form
`AlgebraicGeometry.fourierMukaiIsoDerivedPullback_of_comp_snd_eq_id` — where the closed immersion
hypothesis is discharged from separatedness of `f` — already reads `Φ_{𝒪_Δ} ≅ L(Δ ≫ pr_1)^*`.
The remaining identity `Δ ≫ pr_1 = 𝟙_X` and `AlgebraicGeometry.dpullIdIso` turn the right-hand
side into the identity functor.

*The kernel is the same object.*  `AlgebraicGeometry.diagonalKernel` is `RΔ_*` of `𝒪_X` in degree
zero, which is the kernel `Rs_*𝒪_Z` of the general statement at `s = Δ`; the two spellings agree
definitionally, so no comparison isomorphism is needed.

*No hypothesis beyond separatedness.*  The source's Example 0FYV hypothesises only that
`f : X ⟶ S` be separated, and that is the only hypothesis here.  In particular nothing is
assumed on the cohomology sheaves of `M`: the general chain uses [Stacks, Tag 0B55] in the form
`Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_of_isClosedEmbedding`,
valid for arbitrary complexes, rather than in the quasi-coherent form that
`AlgebraicGeometry.ProjectionFormulaIsIsoOnQuasicoherent` carries as a hypothesis.

*The model of the derived categories.*  As in
`StacksFrontier/AlgebraicGeometry/DerivedVarieties/FourierMukai/Basic.lean`, everything is read at
`CategoryTheory.HasDerivedCategory.standard`, given a raised local instance priority so that the
locally small model arriving with the imports does not compete.

## References

* [Stacks Project, Tag 0FYV](https://stacks.math.columbia.edu/tag/0FYV)
* [Stacks Project, Tag 0FYQ](https://stacks.math.columbia.edu/tag/0FYQ)
* [Stacks Project, Tag 0B55](https://stacks.math.columbia.edu/tag/0B55)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

-- The priority selects the standard model of the derived categories, the one the Fourier-Mukai
-- functor of [Stacks, Tag 0FYQ] and the diagonal kernel of [Stacks, Tag 0FYV] are read at, over
-- the locally small model arriving with the imports.
attribute [local instance 100000] HasDerivedCategory.standard

variable {S X : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]

/-- **The chain [Stacks, Tag 0FYV] displays.**  For a separated morphism of schemes `f : X ⟶ S`
and any `M ∈ D(𝒪_X)`,

`L pr_1^*M ⊗^𝐋_{𝒪_{X ×_S X}} 𝒪_Δ = RΔ_*(LΔ^*L pr_1^*M ⊗^𝐋_{𝒪_X} 𝒪_X) = RΔ_*M`,

read as an isomorphism of functors `D(𝒪_X) ⥤ D(𝒪_{X ×_S X})`, hence natural in `M`.

The first equality is `AlgebraicGeometry.dtenDerivedPushforwardUnitIso` at the closed immersion
`Δ`: the projection formula [Stacks, Tag 0B55], which is the source's own justification for it,
with the factor `𝒪_X` absorbed by the unitor.  The second is the composition isomorphism of
[Stacks, Tag 0D5S], `AlgebraicGeometry.dpullCompFstIso`, followed by `pr_1 ∘ Δ = 𝟙_X`, again as
in the source.  Pushing this forward along `pr_2` is the source's closing sentence and gives
`AlgebraicGeometry.fourierMukaiDiagonalKernelIso` below. -/
@[stacks 0FYV "the chain the example displays, `L pr_1^*(-) ⊗^𝐋 𝒪_Δ ≅ RΔ_*(-)`, as an \
isomorphism of functors, for `f` separated"]
def fourierMukaiPullbackTensorDiagonalKernelIso :
    fourierMukaiPullback f f ⋙ fourierMukaiTensor f f (diagonalKernel f) ≅
      dpush (Limits.pullback.diagonal f) :=
  Functor.isoWhiskerLeft (dpull (Limits.pullback.fst f f))
      (dtenDerivedPushforwardUnitIso f f (Limits.pullback.diagonal f)) ≪≫
    Functor.isoWhiskerRight (dpullCompFstIso f f (Limits.pullback.diagonal f))
      (dpush (Limits.pullback.diagonal f)) ≪≫
    Functor.isoWhiskerRight
      (eqToIso (congrArg dpull (Limits.pullback.diagonal_fst f)) ≪≫ dpullIdIso X)
      (dpush (Limits.pullback.diagonal f)) ≪≫
    (dpush (Limits.pullback.diagonal f)).leftUnitor

/-- **The closing assertion of [Stacks, Tag 0FYV].**  For a separated morphism of schemes
`f : X ⟶ S` the Fourier-Mukai functor of the diagonal kernel `𝒪_Δ = RΔ_{X/S,*}𝒪_X` is the
identity functor of `D(𝒪_X)`:

`Φ_{𝒪_Δ} = R pr_{2,*}(L pr_1^*(-) ⊗^𝐋_{𝒪_{X ×_S X}} 𝒪_Δ) ≅ 𝟭`.

The diagonal is a closed immersion and a section of the second projection, so
`AlgebraicGeometry.fourierMukaiIsoDerivedPullback_of_comp_snd_eq_id` — the general computation of
`Φ_{Rs_*𝒪_Z}` at a closed immersion `s` into the product, specialised to a section — gives
`Φ_{𝒪_Δ} ≅ L(Δ ≫ pr_1)^*`; and `Δ ≫ pr_1 = 𝟙_X`, whose derived pullback is the identity by
`AlgebraicGeometry.dpullIdIso`. -/
@[stacks 0FYV "the Fourier-Mukai functor of the diagonal kernel is the identity, for `f` \
separated"]
def fourierMukaiDiagonalKernelIso :
    fourierMukai f f (diagonalKernel f) ≅ 𝟭 (DerivedCategory X.Modules) :=
  fourierMukaiIsoDerivedPullback_of_comp_snd_eq_id f f (Limits.pullback.diagonal f)
      (Limits.pullback.diagonal_snd f) ≪≫
    eqToIso (congrArg dpull (Limits.pullback.diagonal_fst f)) ≪≫ dpullIdIso X

/-- **`𝒪_Δ` is a Fourier-Mukai kernel for the identity functor**, in the sense of
`AlgebraicGeometry.IsFourierMukaiKernel`; this is [Stacks, Tag 0FYV] read through the
vocabulary of [Stacks, Tag 0FYQ]. -/
@[stacks 0FYV "the diagonal kernel is a Fourier-Mukai kernel for the identity functor"]
theorem isFourierMukaiKernel_diagonalKernel :
    IsFourierMukaiKernel f f (𝟭 (DerivedCategory X.Modules)) (diagonalKernel f) :=
  ⟨(fourierMukaiDiagonalKernelIso f).symm⟩

end AlgebraicGeometry

end
