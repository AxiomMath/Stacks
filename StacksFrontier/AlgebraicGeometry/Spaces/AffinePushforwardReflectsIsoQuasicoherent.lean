module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealPowerFactorIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceQuotientQuasicoherent

/-!
# Direct image along an affine morphism reflects isomorphisms of quasi-coherent modules

Let `f : Y ⟶ X` be an affine morphism of algebraic spaces over `S`.  A morphism `g : M ⟶ N` of
quasi-coherent `𝒪_Y`-modules whose direct image `f_*g` is an isomorphism of `𝒪_X`-modules is an
isomorphism.  This is the conservativity half of Stacks 08AI: `F ↦ f_*F` is an equivalence from
quasi-coherent `𝒪_Y`-modules onto quasi-coherent `f_*𝒪_Y`-modules
(`AlgebraicGeometry.Space.isEquivalence_affineQuasicoherentDirectImage`), and the direct image as
`𝒪_X`-modules differs from the one as `f_*𝒪_Y`-modules only by restriction of scalars, which does
not change the underlying maps of sections.

## Main results

* `AlgebraicGeometry.Space.isIso_of_isIso_modulePushforward_map_of_isAffineHom`.

## References

* [Stacks Project, Tag 08AI](https://stacks.math.columbia.edu/tag/08AI)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Direct image along an affine morphism reflects isomorphisms of quasi-coherent modules**
(the conservativity of the equivalence of Stacks 08AI). -/
theorem isIso_of_isIso_modulePushforward_map_of_isAffineHom {X Y : AlgebraicSpaces B S hS}
    (f : Y ⟶ X) (hf : IsAffineHom B S hS f.hom) {M N : Modules.{u, u} B S hS Y.1 Y.2}
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) (g : M ⟶ N)
    (hg : IsIso ((modulePushforward B S hS f).map g)) : IsIso g := by
  have h1 : IsIso ((moduleDirectImage B S hS f).map g) :=
    Stacks.SheafOfModules.isIso_of_bijective_val_app _
      (bijective_val_app_of_isIso_module ((modulePushforward B S hS f).map g) hg)
  let F := affineQuasicoherentDirectImage B S hS f hf
  have := isEquivalence_affineQuasicoherentDirectImage B S hS f hf
  let g' : (⟨M, hM⟩ : QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2) ⟶ ⟨N, hN⟩ :=
    ObjectProperty.homMk g
  have h2 : IsIso ((ObjectProperty.ι _).map (F.map g')) := h1
  have : IsIso (F.map g') := isIso_of_reflects_iso _ (ObjectProperty.ι _)
  have : IsIso g' := isIso_of_reflects_iso g' F
  exact (inferInstance : IsIso ((ObjectProperty.ι _).map g'))

end AlgebraicGeometry.Space

end
