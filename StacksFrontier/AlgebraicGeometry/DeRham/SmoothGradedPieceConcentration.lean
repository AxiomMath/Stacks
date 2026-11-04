module

public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothSpectralSequenceFiltered
public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.DerivedFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AbelianOfSmallSite
public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.DerivedFunctor
public import StacksFrontier.AlgebraicGeometry.DeRham.WedgeFiltrationDegreewise

/-!
# Where the filtration of Section 0FMK and its graded pieces live

Let `f : X ⟶ Y` be a morphism of schemes over a base `S`. `Ω^•_{X/S}` is filtered by the forms
pulled back from `Y` (`Stacks.DeRhamSmooth.deRhamSmoothFiltration`). This file locates the
`p`-th step of that filtration and the `p`-th graded piece in the degrees `≤ p`:

* **both vanish in degrees `< p`**, and
* **in degree exactly `p` the graded piece is the step**, `gr^pΩ^p_{X/S} = F^pΩ^p_{X/S}` —
  because the next step `F^{p+1}Ω^•_{X/S}` has already vanished in degree `p`, so the cokernel
  defining the graded piece is taken of a morphism out of a zero object.

These are the two facts about the left-hand side of Section 0FMK's identification

`gr^kΩ^•_{X/S}  ≅  f^{-1}Ω^k_{Y/S}[-k] ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y}`

that `Stacks.DeRhamSmooth.gradedPieceXIsoGradedTargetX` does not supply. That identification is
assembled degree by degree, and its degrees come in two kinds: the degrees `n = k + 1 + m` with
`m : ℕ`, where `gradedPieceXIsoGradedTargetX` is the comparison, and the degrees it does not
reach — the degrees `< k`, where `CochainComplex.isoOfGE` needs both sides to vanish
(`Stacks.DeRhamSmooth.isZero_gradedPiece_X` here and
`Stacks.DeRhamSmooth.isZero_gradedTargetComplex_X` for the target), and the degree `k` itself,
where the comparison has to be built separately and where
`Stacks.DeRhamSmooth.gradedPieceXIsoFiltrationX` reduces the task to the single sheaf
`F^kΩ^k_{X/S}`, the image of `⋀^k(f^*Ω_{Y/S}) ⟶ Ω^k_{X/S}`.

Nothing is assumed of `f`: these are statements about the filtration, not about the graded
pieces being computable.

## Main definitions

* `Stacks.DeRhamSmooth.gradedPieceXIsoFiltrationX`: **in a degree `n ≤ p` the `p`-th graded
  piece is the `p`-th step**, `(gr^pΩ^•_{X/S})^n ≅ (F^pΩ^•_{X/S})^n`.

## Main results

* `Stacks.DeRhamSmooth.isZero_deRhamSmoothFiltration_obj_X`: **the `p`-th step of the
  filtration vanishes in degrees `< p`**, for every `p : ℤ`.
* `Stacks.DeRhamSmooth.isZero_gradedPiece_X`: **the `p`-th graded piece vanishes in degrees
  `< p`**, for every `p : ℤ`.
* `Stacks.DeRhamSmooth.gradedPieceXIsoFiltrationX_inv`: **in a degree `n ≤ p` the inverse of
  that comparison is the projection onto the graded piece**, and hence
  `Stacks.DeRhamSmooth.gradedPieceXIsoFiltrationX_inv_d`, its square against the differentials.

## Implementation notes

`AlgebraicGeometry.SheafOfModules.isZero_wedgeFiltered_filtration_obj_X` already gives the
vanishing of the step, but only for `0 < p`: it reads the step as the image of the wedge map out
of `Tot(f^{-1}σ^{≥p}Ω^•_{Y/S} ⊗ Ω^•_{X/S})`, and that description of the step is the one the
construction of the filtration gives for `p ≥ 1`. The remaining case `p ≤ 0` is not a
degeneration but a different argument: there the step is the whole complex
(`AlgebraicGeometry.SheafOfModules.isIso_wedgeFiltered_ι_of_nonpos`), and the vanishing in
degrees `< p ≤ 0` is the vanishing of the relative de Rham complex in negative degrees. The
statement below is uniform in `p` because the consumer — a cut `k : ℕ` of the identification,
whose vanishing is needed in every degree `< k`, so at `k = 0` in every negative degree — needs
it at `p = 0` as well as at `p ≥ 1`.

The graded piece is reached through `CategoryTheory.Limits.PreservesCokernel.iso` at evaluation
in degree `n`, which presents its degree-`n` term as the cokernel of the degree-`n` component of
`F^{p+1} ⟶ F^p`, cokernels of cochain complexes being computed degreewise. Both results below go
through that one identification: the vanishing is not proved from the epimorphy of a morphism
into a zero object but as a corollary of the isomorphism with the step, which holds in every
degree `n ≤ p` and therefore in every degree `n < p`. That keeps the `Epi` instance out of the
proof; pinned by `haveI` at these binders it was not found again by the instance search inside
`CategoryTheory.Limits.isZero_cokernel_of_epi`.

## References

* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.Cohomology.FilteredComplex Stacks.DeRhamDirectImage

attribute [local instance 2000] HasDerivedCategory.standard

universe u

namespace Stacks.DeRhamSmooth

/-! Sheaves of modules on a ringed space form an abelian category. Pinned rather than restated,
for the same reason `StacksFrontier.AlgebraicGeometry.DeRham.SmoothSpectralSequenceFiltered` pins
it: at this import surface the search from `SheafOfModules.instAbelian` exceeds the default
instance-synthesis budget, and `Stacks.SheafOfModules.abelianOfSmallSite` is that instance with
the budget already spent. -/
attribute [local instance] Stacks.SheafOfModules.abelianOfSmallSite

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **The `p`-th step of the filtration of `Ω^•_{X/S}` by the forms pulled back from `Y`
vanishes in degrees `< p`**, for every `p : ℤ`.

For `p ≥ 1` this is `AlgebraicGeometry.SheafOfModules.isZero_wedgeFiltered_filtration_obj_X`:
the step is the image of the wedge map out of `Tot(f^{-1}σ^{≥p}Ω^•_{Y/S} ⊗ Ω^•_{X/S})`, whose
total degree `< p` terms all have a vanishing left-hand factor. For `p ≤ 0` the step is the
whole of `Ω^•_{X/S}` (`AlgebraicGeometry.SheafOfModules.isIso_wedgeFiltered_ι_of_nonpos`), and a
degree `< p ≤ 0` is a negative degree, where the relative de Rham complex vanishes.

Costs 1,938 heartbeats against the default budget of 200,000. -/
theorem isZero_deRhamSmoothFiltration_obj_X (p n : ℤ) (hn : n < p) :
    IsZero (((deRhamSmoothFiltration f g).filtration.obj (op p)).X n) := by
  rcases le_or_gt p 0 with hp | hp
  · have := AlgebraicGeometry.SheafOfModules.isIso_wedgeFiltered_ι_of_nonpos
      (Scheme.Hom.deRhamAlgebras (f ≫ g))
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g)))
      (pulledBackDeRhamComplex f g) (Stacks.DeRhamPullback.deRhamPullbackChain f g) p hp
    exact IsZero.of_iso
      (CochainComplex.isZero_of_isStrictlyGE (deRhamCochainComplex (f ≫ g)) 0 n (by omega))
      ((HomologicalComplex.eval _ (ComplexShape.up ℤ) n).mapIso (@asIso _ _ _ _ _ this))
  · exact AlgebraicGeometry.SheafOfModules.isZero_wedgeFiltered_filtration_obj_X
      _ _ _ _ p hp n hn

/-- **In a degree `n ≤ p` the `p`-th graded piece of the filtration of `Ω^•_{X/S}` is the `p`-th
step**: `(gr^pΩ^•_{X/S})^n ≅ (F^pΩ^•_{X/S})^n`.

The graded piece is degreewise the cokernel of `(F^{p+1})^n ⟶ (F^p)^n`
(`CategoryTheory.Limits.PreservesCokernel.iso` at evaluation in degree `n`), and for `n ≤ p` the
source of that morphism has already vanished — the next step is concentrated in degrees
`≥ p + 1`. A cokernel of a morphism out of a zero object is its target.

In degree exactly `n = p` this is the content Section 0FMK needs at the cut, where the
decomposition `n = k + 1 + m` with `m : ℕ` of
`Stacks.DeRhamSmooth.gradedPieceXIsoGradedTargetX` does not reach: it reduces the degree-`p`
term of the graded piece to the single sheaf `F^pΩ^p_{X/S}`, the image of
`⋀^p(f^*Ω_{Y/S}) ⟶ Ω^p_{X/S}`.

Costs 8,066 heartbeats against the default budget of 200,000. -/
def gradedPieceXIsoFiltrationX (p n : ℤ) (hn : n ≤ p) :
    (gradedPiece (inverseImageBase (f ≫ g)) p (deRhamSmoothFiltration f g)).X n ≅
      ((deRhamSmoothFiltration f g).filtration.obj (op p)).X n :=
  have G : ∀ (𝒜 : Type (u + 1)) [Category.{u} 𝒜] [Abelian 𝒜]
        (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ),
        ((FilteredObject.gr p).obj K).X n ≅
          cokernel ((HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n).map
            (K.filtration.diagram.map (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op)) :=
      fun 𝒜 _ _ K => PreservesCokernel.iso (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n)
        (K.filtration.diagram.map (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op)
  G _ (deRhamSmoothFiltration f g) ≪≫
    cokernelIsoOfEq
      ((isZero_deRhamSmoothFiltration_obj_X f g (p + 1) n (by omega)).eq_of_src _ 0) ≪≫
    cokernelZeroIsoTarget

/-- **In a degree `n ≤ p` the inverse of that comparison is the projection onto the graded
piece.** Both of the last two steps of the comparison are cokernel comparisons, and a cokernel
projection composed with either is again a cokernel projection
(`CategoryTheory.Limits.cokernelZeroIsoTarget_inv` and
`CategoryTheory.Limits.π_comp_cokernelIsoOfEq_inv`), while the first step carries the projection
onto the graded piece to the cokernel projection
(`CategoryTheory.Limits.PreservesCokernel.π_iso_hom`).

This is what makes `Stacks.DeRhamSmooth.gradedPieceXIsoFiltrationX` usable against the
differentials: the projection onto the graded piece is a morphism of complexes, so naming the
inverse as that projection turns every square against the differential of the graded piece into
the chain-map square of the projection
(`Stacks.DeRhamSmooth.gradedPieceXIsoFiltrationX_inv_d`).

Costs 22,831 heartbeats against the default budget of 200,000. -/
theorem gradedPieceXIsoFiltrationX_inv (p n : ℤ) (hn : n ≤ p) :
    (gradedPieceXIsoFiltrationX f g p n hn).inv =
      (FilteredObject.grMapπ (FilteredObject.succHom p) (deRhamSmoothFiltration f g)).f n := by
  let G : ∀ (𝒜 : Type (u + 1)) [Category.{u} 𝒜] [Abelian 𝒜]
        (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ),
        ((FilteredObject.gr p).obj K).X n ≅
          cokernel ((HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n).map
            (K.filtration.diagram.map (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op)) :=
    fun 𝒜 _ _ K => PreservesCokernel.iso (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n)
      (K.filtration.diagram.map (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op)
  have Gπ : ∀ (𝒜 : Type (u + 1)) [Category.{u} 𝒜] [Abelian 𝒜]
      (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ),
      (FilteredObject.grMapπ (FilteredObject.succHom p) K).f n ≫ (G 𝒜 K).hom =
        cokernel.π ((HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n).map
          (K.filtration.diagram.map (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op)) :=
    fun 𝒜 _ _ K => PreservesCokernel.π_iso_hom (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n)
      (K.filtration.diagram.map (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op)
  have key : (gradedPieceXIsoFiltrationX f g p n hn).inv =
      (cokernel.π 0 ≫ (cokernelIsoOfEq
          ((isZero_deRhamSmoothFiltration_obj_X f g (p + 1) n (by omega)).eq_of_src _ 0)).inv) ≫
        (G _ (deRhamSmoothFiltration f g)).inv := rfl
  refine key.trans (Eq.trans (Category.assoc _ _ _) ?_)
  refine Eq.trans (π_comp_cokernelIsoOfEq_inv_assoc _ _) ?_
  exact (Iso.comp_inv_eq _).2 (Gπ _ (deRhamSmoothFiltration f g)).symm

/-- **The square of `Stacks.DeRhamSmooth.gradedPieceXIsoFiltrationX` against the differentials.**
In a degree `n ≤ p` the comparison with the step carries the differential of the graded piece to
the differential of the step, followed by the projection in the target degree — which is no
longer `Stacks.DeRhamSmooth.gradedPieceXIsoFiltrationX` once the target degree has passed `p`,
as it has at the cut of Section 0FMK.

Nothing is proved here that the chain-map square of the projection does not already say: the
content is `Stacks.DeRhamSmooth.gradedPieceXIsoFiltrationX_inv`, and this is that identification
substituted into `CategoryTheory.FilteredObject.grMapπ`'s own `HomologicalComplex.Hom.comm`.

Costs 6,535 heartbeats against the default budget of 200,000. -/
theorem gradedPieceXIsoFiltrationX_inv_d (p n m : ℤ) (hn : n ≤ p) :
    (gradedPieceXIsoFiltrationX f g p n hn).inv ≫
        (gradedPiece (inverseImageBase (f ≫ g)) p (deRhamSmoothFiltration f g)).d n m =
      ((deRhamSmoothFiltration f g).filtration.obj (op p)).d n m ≫
        (FilteredObject.grMapπ (FilteredObject.succHom p) (deRhamSmoothFiltration f g)).f m :=
  Eq.trans
    (congrArg (fun u => u ≫ (gradedPiece (inverseImageBase (f ≫ g)) p
        (deRhamSmoothFiltration f g)).d n m)
      (gradedPieceXIsoFiltrationX_inv f g p n hn))
    ((FilteredObject.grMapπ (FilteredObject.succHom p) (deRhamSmoothFiltration f g)).comm n m)

/-- **The `p`-th graded piece of the filtration of `Ω^•_{X/S}` vanishes in degrees `< p`**, for
every `p : ℤ`: in those degrees it is the `p`-th step
(`Stacks.DeRhamSmooth.gradedPieceXIsoFiltrationX`), which has vanished
(`Stacks.DeRhamSmooth.isZero_deRhamSmoothFiltration_obj_X`).

With `Stacks.DeRhamSmooth.isZero_gradedTargetComplex_X` for the right-hand side, this is the
hypothesis `CochainComplex.isoOfGE` asks of both sides of Section 0FMK's identification below
the cut.

Costs 533 heartbeats against the default budget of 200,000. -/
theorem isZero_gradedPiece_X (p n : ℤ) (hn : n < p) :
    IsZero ((gradedPiece (inverseImageBase (f ≫ g)) p (deRhamSmoothFiltration f g)).X n) :=
  IsZero.of_iso (isZero_deRhamSmoothFiltration_obj_X f g p n hn)
    (gradedPieceXIsoFiltrationX f g p n hn.le)

end Stacks.DeRhamSmooth

end
