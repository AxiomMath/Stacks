module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationConormalTrack
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationSheafAction
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDerivationActionGlobalComposition

/-!
# The modified lift of the global track is the modified lift of the derivation track

The repository carries two constructions of the lift `θ ⬝ a'` of [Stacks Project, Tag 0CK1] for a
morphism of thickenings `(a, a') : (X ⊂ X') ⟶ (Y ⊂ Y')` over `S`, differing in how the datum
`θ` is presented.

* `Stacks.Thickenings.derivationActionGlobal` takes `θ` out of
  `Stacks.Smooth.pullbackCotangentSheaf (j ≫ q) a`, the module pullback of the ringed-space
  sheaf of differentials, and perturbs the comorphism of `a'` by
  `Stacks.Thickenings.derivationSection`.
* `Stacks.Thickenings.derivationActionSheaf` takes `θ` out of
  `(Scheme.Modules.pullback a).obj (Scheme.Hom.relativeDifferentials (j ≫ q))`, the module
  pullback of the corepresenting sheaf of differentials, and perturbs by
  `Stacks.Thickenings.derivationSectionι`.

The two data correspond under
`Stacks.Thickenings.derivationDatumEquiv`, and this file proves that the two lifts then agree.
With that, the characterisation `Stacks.Thickenings.IsDerivationAction` of the derivation track —
and in particular the unrestricted [Stacks Project, Tag 04FG], which produces a datum from a
*pair* of lifts — becomes available for `Stacks.Thickenings.derivationActionGlobal`.

`StacksFrontier/AlgebraicGeometry/MoreMorphisms/InfinitesimalDeformationSheafHomTransitivity.lean`
proves the corresponding statement for the third construction,
`Stacks.Thickenings.homSectionAct`, over an open of `X'`; the two proofs have the same shape, and
the present one is shorter because over the whole space the two opens of `X` on which the datum is
evaluated are *equal* — `i⁻¹(a')⁻¹W` and `a⁻¹j⁻¹W` — rather than one being contained in the image
of the other.

## Main results

* `Stacks.Thickenings.derivationSection_eq_derivationSectionι`: the two perturbations agree on
  sections, over the open `(a')⁻¹W` of `X'`.
* `Stacks.Thickenings.derivationActionGlobal_eq_derivationActionSheaf`: **the two modified lifts
  agree.**

## Implementation notes

The perturbations are both `θ` applied to the pulled-back universal differential and included
into `𝒪_{X'}` along `Stacks.Thickenings.firstOrderImmersionConormalSheafι`; the inclusion is the
same in both, so the content is that the two readings of the differential agree. They differ in
two ways, each absorbed by one lemma.

* The derivation track evaluates `θ` over `a⁻¹j⁻¹W` and then transports along the equality of
  opens `Stacks.Thickenings.preimage_square`, while the global track evaluates it over
  `i⁻¹(a')⁻¹W` directly. Naturality of `θ` moves the transport from after `θ` to before it.
* `Stacks.Smooth.pullbackD` is then taken over the two opens, and
  `Stacks.Smooth.map_pullbackD` identifies the two — stated for a `homOfLE`, which is the
  `eqToHom` of the equality of opens because the opens of a scheme form a thin category, so
  `Subsingleton.elim` converts one to the other.

At the level of morphisms the two lifts have the same underlying map and the same preimages of
opens, both by `rfl`, so `AlgebraicGeometry.Scheme.Hom.ext` reduces the statement to the
comorphisms over an arbitrary open, which is the sections statement above.

## References

* [Stacks Project, Tag 02H5](https://stacks.math.columbia.edu/tag/02H5)
* [Stacks Project, Tag 04BV](https://stacks.math.columbia.edu/tag/04BV)
* [Stacks Project, Tag 04FG](https://stacks.math.columbia.edu/tag/04FG)
* [Stacks Project, Tag 0CK1](https://stacks.math.columbia.edu/tag/0CK1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Thickenings

variable {S X X' Y Y' : Scheme.{u}} {i : X ⟶ X'} {j : Y ⟶ Y'} {a : X ⟶ Y} {a' : X' ⟶ Y'}

/-- **The two perturbations agree on sections.** Over the open `(a')⁻¹W` of `X'`, the
perturbation `Stacks.Thickenings.derivationSection` of the global track at `θ` is the
perturbation `Stacks.Thickenings.derivationSectionι` of the derivation track at the datum
`Stacks.Thickenings.derivationDatumOfCotangent θ` that corresponds to it.

Both are `θ` applied to the pulled-back universal differential of the section, included into
`𝒪_{X'}`; the two readings of the differential are identified by naturality of `θ` along the
equality of opens `i⁻¹(a')⁻¹W = a⁻¹j⁻¹W` together with `Stacks.Smooth.map_pullbackD`. -/
theorem derivationSection_eq_derivationSectionι [IsClosedImmersion i] [IsImmersion j]
    (hsq : i.ker ^ 2 = ⊥) (q : Y' ⟶ S) (comm_a : i ≫ a' = a ≫ j)
    (θ : Stacks.Smooth.pullbackCotangentSheaf (j ≫ q) a ⟶ conormalModules i)
    (W : Y'.Opens) (g : Γ(Y', W)) :
    derivationSection hsq θ W (a' ⁻¹ᵁ W) (preimage_le_of_comm comm_a le_rfl) g
      = derivationSectionι hsq q comm_a (derivationDatumOfCotangent θ) W
          ((j.app W).hom g) := by
  have hpre : i ⁻¹ᵁ (a' ⁻¹ᵁ W) = a ⁻¹ᵁ (j ⁻¹ᵁ W) := preimage_square comm_a W
  -- naturality of `θ` along the equality of the two opens
  have hθ := (Scheme.Modules.Hom.mapPresheaf θ).naturality (eqToHom hpre).op
  have hθ' := congrArg (fun z : Γ(Stacks.Smooth.pullbackCotangentSheaf (j ≫ q) a,
        a ⁻¹ᵁ (j ⁻¹ᵁ W)) ⟶ Γ(conormalModules i, i ⁻¹ᵁ (a' ⁻¹ᵁ W)) => z.hom
      (Stacks.Smooth.pullbackD (j ≫ q) a (j ⁻¹ᵁ W) le_rfl ((j.app W).hom g))) hθ
  -- the pulled-back universal differential over the two equal opens
  have hmpd : (Stacks.Smooth.pullbackCotangentSheaf (j ≫ q) a).val.map (eqToHom hpre).op
        (Stacks.Smooth.pullbackD (j ≫ q) a (j ⁻¹ᵁ W) le_rfl ((j.app W).hom g))
      = Stacks.Smooth.pullbackD (j ≫ q) a (j ⁻¹ᵁ W)
          (preimage_le_of_comm comm_a (le_refl (a' ⁻¹ᵁ W))) ((j.app W).hom g) :=
    (congrArg (fun z : (i ⁻¹ᵁ (a' ⁻¹ᵁ W) : X.Opens) ⟶ (a ⁻¹ᵁ (j ⁻¹ᵁ W) : X.Opens) =>
        (Stacks.Smooth.pullbackCotangentSheaf (j ≫ q) a).val.map z.op
          (Stacks.Smooth.pullbackD (j ≫ q) a (j ⁻¹ᵁ W) le_rfl ((j.app W).hom g)))
      (Subsingleton.elim (eqToHom hpre) (homOfLE hpre.le))).trans
      (Stacks.Smooth.map_pullbackD (j ≫ q) a (j ⁻¹ᵁ W) le_rfl
        (preimage_le_of_comm comm_a (le_refl (a' ⁻¹ᵁ W))) hpre.le ((j.app W).hom g))
  rw [derivationSectionι_derivationDatumOfCotangent hsq q comm_a θ W ((j.app W).hom g)]
  exact congrArg (conormalSection hsq (a' ⁻¹ᵁ W))
    ((congrArg (Scheme.Modules.Hom.app θ (i ⁻¹ᵁ (a' ⁻¹ᵁ W)) |>.hom) hmpd).symm.trans hθ')

/-- **The modified lift of the global track is the modified lift of the derivation track.** For a
datum `θ : a^*Ω_{Y/S} ⟶ 𝒞_{X/X'}` out of the ringed-space sheaf of differentials, the lift
`θ ⬝ a'` of `Stacks.Thickenings.derivationActionGlobal` is the lift `θ ⬝ a'` of
`Stacks.Thickenings.derivationActionSheaf` at the corresponding datum out of the corepresenting
sheaf of differentials.

Both lifts have the underlying map of `a'`, and their comorphisms over an open `W` of `Y'` are
`(a')^♯` perturbed by the two perturbations, which agree by
`Stacks.Thickenings.derivationSection_eq_derivationSectionι`. -/
theorem derivationActionGlobal_eq_derivationActionSheaf [IsClosedImmersion i] [IsImmersion j]
    (hsq : i.ker ^ 2 = ⊥) (q : Y' ⟶ S) (comm_a : i ≫ a' = a ≫ j)
    (θ : Stacks.Smooth.pullbackCotangentSheaf (j ≫ q) a ⟶ conormalModules i) :
    derivationActionGlobal hsq θ comm_a
      = derivationActionSheaf hsq q comm_a (derivationDatumOfCotangent θ) := by
  refine Scheme.Hom.ext rfl (fun W ↦ CommRingCat.hom_ext (RingHom.ext fun s ↦ ?_))
  refine (CommRingCat.comp_apply _ _ s).trans ((presheaf_map_self _ _).trans ?_)
  rw [derivationActionGlobal_app, derivationActionSheaf_app,
    derivationSection_eq_derivationSectionι hsq q comm_a θ W s]

end Stacks.Thickenings

end
