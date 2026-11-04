module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeChart
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjStructureRestriction

/-!
# The punctured cone projection on an affine chart

Let `A` and `B` be nonnegatively graded rings, `c : ConeData 𝒜 ℬ` cone data, `π : L = Proj B ⟶ P`
the cone projection and `U ⊆ L` the punctured cone. For `f` homogeneous of positive degree the
part of `U` lying over the standard open `D₊(f)` of `P` is the standard open
`D₊(σ f · ψ f)` of `L` (`Stacks.AlgebraicGeometry.ProjAndSpec.openUInL_inf_basicOpen`), which is
affine, so the functions on it are the degree-zero localization `B_{(σ f · ψ f)}`.

**On those charts `π|_U` is the map `A_{(f)} ⟶ B_{(σ f · ψ f)}` of degree-zero localizations**
given by `HomogeneousLocalization.Away.map ψ f` followed by the restriction map attached to
`D₊(σ f · ψ f) ⊆ D₊(ψ f)`. This is the punctured analogue of
`Stacks.AlgebraicGeometry.ProjAndSpec.awayToSection_comp_pi_appLE`, and it is what says which
`A_{(f)}`-algebra the functions on the part of `U` over `D₊(f)` form — hence what the scalar
multiplication is in any comparison of `(π|_U)_* 𝒪_U` with a sheaf of `𝒪_P`-modules over a
standard open.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjAndSpec.puncturedAwayMap`: the map
  `A_{(f)} ⟶ B_{(σ f · ψ f)}` of degree-zero localizations.

## Main results

* `Stacks.AlgebraicGeometry.ProjAndSpec.awayToSection_comp_pi_appLE_sigmaMulPsi`: **on functions
  over `D₊(f)`, read on the standard open `D₊(σ f · ψ f)` of `L`, the cone projection is
  `puncturedAwayMap`.**
* `Stacks.AlgebraicGeometry.ProjAndSpec.awayToSection_comp_puncturedPi_appLE`: the same statement
  for the restricted projection `π|_U : U ⟶ P` itself, the chart of `U` being the inverse image
  of that standard open under the open immersion of `U`.

## Implementation notes

The statement follows from `Stacks.AlgebraicGeometry.ProjAndSpec.awayToSection_comp_pi_appLE`
together with `ProjectiveSpectrum.basicOpenIsoAway_restrict`: shrinking the target open from
`D₊(ψ f)` to `D₊(σ f · ψ f)` composes the chart description with a restriction map of `𝒪_L`,
and that restriction map is the degree-zero restriction map of `B` under the identifications
`B_{(ψ f)} = Γ(L, D₊(ψ f))` and `B_{(σ f · ψ f)} = Γ(L, D₊(σ f · ψ f))` of [Stacks, Tag 01M6].
The remaining steps are `AlgebraicGeometry.Scheme.Hom.appLE_map`, which absorbs the
restriction into `appLE`, and `AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE`, which splits the
composite `U ⟶ L ⟶ P` off the chart.

No statement here names the sections of `𝒪_U`: the chart of `U` over `D₊(f)` is written as the
inverse image of `D₊(σ f · ψ f)` under the open immersion, so that both displayed identities are
equalities of maps out of `A_{(f)}` and nothing has to be transported along
`Γ(U, U.ι ⁻¹ᵁ V) = Γ(L, U ⊓ V)`.

## References

* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
* [Stacks Project, Tag 01M4](https://stacks.math.columbia.edu/tag/01M4)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory HomogeneousLocalization

universe u

namespace Stacks.AlgebraicGeometry.ProjAndSpec

variable {A B : Type u} {σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (c : ConeData 𝒜 ℬ) {d : ℕ} {f : A}

/-- `σ f · ψ f` is homogeneous of the same degree as `f`, the element `σ f` having degree zero. -/
theorem sigmaMulPsi_mem (hf : f ∈ 𝒜 d) : (c.sigma f : B) * c.psi f ∈ ℬ d := by
  simpa using SetLike.mul_mem_graded (c.sigma f).2 (c.psi.map_mem hf)

/-- The part of `U` over `D₊(f)` sits inside the part of `L` over `D₊(f)`: the standard open
`D₊(σ f · ψ f)` is contained in `D₊(ψ f)`. -/
theorem basicOpen_sigmaMulPsi_le : Proj.basicOpen ℬ ((c.sigma f : B) * c.psi f) ≤
    Proj.basicOpen ℬ (c.psi f) :=
  ProjectiveSpectrum.basicOpen_mul_le_right ℬ _ _

/-- The part of `U` over `D₊(f)` lies over `D₊(f)`. -/
theorem basicOpen_sigmaMulPsi_le_pi_preimage (hd : 0 < d) (hf : f ∈ 𝒜 d) :
    Proj.basicOpen ℬ ((c.sigma f : B) * c.psi f) ≤ pi c ⁻¹ᵁ Proj.basicOpen 𝒜 f := by
  rw [pi_preimage_basicOpen c f d hf hd]
  exact basicOpen_sigmaMulPsi_le c

/-- **The map `A_{(f)} ⟶ B_{(σ f · ψ f)}` of degree-zero localizations** attached to a
positive-degree homogeneous `f`: the map of degree-zero localizations of `ψ`, followed by the
restriction map of [Stacks, Tag 01M4] for `D₊(σ f · ψ f) ⊆ D₊(ψ f)`. -/
def puncturedAwayMap (hd : 0 < d) (hf : f ∈ 𝒜 d) :
    Away 𝒜 f →+* Away ℬ ((c.sigma f : B) * c.psi f) :=
  (ProjectiveSpectrum.degreeZeroRingMap ℬ (c.psi f) ((c.sigma f : B) * c.psi f)
      ⟨d, hd, c.psi.map_mem hf⟩ ⟨d, hd, sigmaMulPsi_mem c hf⟩
      (basicOpen_sigmaMulPsi_le c)).toRingHom.comp
    (Away.map c.psi f)

/-- **On the chart `D₊(σ f · ψ f)` of the punctured cone the projection acts on functions by the
map `A_{(f)} ⟶ B_{(σ f · ψ f)}` of degree-zero localizations.** Through the identifications
`A_{(f)} = Γ(P, D₊(f))` and `B_{(σ f · ψ f)} = Γ(L, D₊(σ f · ψ f))` of [Stacks, Tag 01M6], the
pullback of functions along `π` to the part of `U` over `D₊(f)` is `puncturedAwayMap`. -/
@[stacks 0EKG "the punctured cone projection on functions over a standard open is the map of \
degree-zero localizations A_(f) to B_(sigma f * psi f)"]
theorem awayToSection_comp_pi_appLE_sigmaMulPsi (hd : 0 < d) (hf : f ∈ 𝒜 d) :
    Proj.awayToSection 𝒜 f ≫ (pi c).appLE (Proj.basicOpen 𝒜 f)
        (Proj.basicOpen ℬ ((c.sigma f : B) * c.psi f))
        (basicOpen_sigmaMulPsi_le_pi_preimage c hd hf) =
      CommRingCat.ofHom (puncturedAwayMap c hd hf) ≫
        Proj.awayToSection ℬ ((c.sigma f : B) * c.psi f) := by
  have hsplit : (pi c).appLE (Proj.basicOpen 𝒜 f) (Proj.basicOpen ℬ (c.psi f))
        (pi_preimage_basicOpen c f d hf hd).ge ≫
      (AlgebraicGeometry.Proj ℬ).presheaf.map (homOfLE (basicOpen_sigmaMulPsi_le c)).op =
      (pi c).appLE (Proj.basicOpen 𝒜 f) (Proj.basicOpen ℬ ((c.sigma f : B) * c.psi f))
        (basicOpen_sigmaMulPsi_le_pi_preimage c hd hf) :=
    Scheme.Hom.appLE_map _ _ _
  have hres : CommRingCat.ofHom (ProjectiveSpectrum.degreeZeroRingMap ℬ (c.psi f)
        ((c.sigma f : B) * c.psi f) ⟨d, hd, c.psi.map_mem hf⟩ ⟨d, hd, sigmaMulPsi_mem c hf⟩
        (basicOpen_sigmaMulPsi_le c)).toRingHom ≫
      Proj.awayToSection ℬ ((c.sigma f : B) * c.psi f) =
      Proj.awayToSection ℬ (c.psi f) ≫
        (AlgebraicGeometry.Proj ℬ).presheaf.map (homOfLE (basicOpen_sigmaMulPsi_le c)).op := by
    have h := ProjectiveSpectrum.basicOpenIsoAway_restrict ℬ (c.psi f)
      ((c.sigma f : B) * c.psi f) d d (c.psi.map_mem hf) hd (sigmaMulPsi_mem c hf) hd
      (basicOpen_sigmaMulPsi_le c)
    rwa [AlgebraicGeometry.Proj.basicOpenIsoAway_hom,
      AlgebraicGeometry.Proj.basicOpenIsoAway_hom] at h
  rw [← hsplit, ← Category.assoc, awayToSection_comp_pi_appLE c hd hf, Category.assoc, ← hres,
    puncturedAwayMap, ← Category.assoc, CommRingCat.ofHom_comp]

/-- **The same statement for the restricted projection `π|_U : U ⟶ P`**, whose chart over
`D₊(f)` is the inverse image of `D₊(σ f · ψ f)` under the open immersion of `U`: there too the
pullback of functions is `puncturedAwayMap`, followed by restriction along that open
immersion. -/
@[stacks 0EKG "the restricted projection pi|_U on functions over a standard open, on the chart \
given by the inverse image of D+(sigma f * psi f)"]
theorem awayToSection_comp_puncturedPi_appLE (hd : 0 < d) (hf : f ∈ 𝒜 d) :
    Proj.awayToSection 𝒜 f ≫ ((openUInL c).ι ≫ pi c).appLE (Proj.basicOpen 𝒜 f)
        ((openUInL c).ι ⁻¹ᵁ Proj.basicOpen ℬ ((c.sigma f : B) * c.psi f))
        (((TopologicalSpace.Opens.map (openUInL c).ι.base).map
          (homOfLE (basicOpen_sigmaMulPsi_le_pi_preimage c hd hf))).le) =
      CommRingCat.ofHom (puncturedAwayMap c hd hf) ≫
        Proj.awayToSection ℬ ((c.sigma f : B) * c.psi f) ≫
          (openUInL c).ι.appLE (Proj.basicOpen ℬ ((c.sigma f : B) * c.psi f))
            ((openUInL c).ι ⁻¹ᵁ Proj.basicOpen ℬ ((c.sigma f : B) * c.psi f)) le_rfl := by
  rw [← Scheme.Hom.appLE_comp_appLE (openUInL c).ι (pi c) _ _ _
      (basicOpen_sigmaMulPsi_le_pi_preimage c hd hf) le_rfl,
    ← Category.assoc, awayToSection_comp_pi_appLE_sigmaMulPsi c hd hf, Category.assoc]

end Stacks.AlgebraicGeometry.ProjAndSpec

end
