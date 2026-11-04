module

public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.RelativeFinitePresentation.Affine
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeFinitePresentation.Transport

/-!
# Relative finite presentation from the restrictions to affine charts

Relative finite presentation of a quasi-coherent module is a condition on the modules of
sections over the affine opens of the source lying over affine opens of the base, by
`AlgebraicGeometry.isFinitelyPresentedRelative_iff_affine`. Each such pair of affine opens
`W ≤ f ⁻¹ᵁ V` carries a morphism of affine schemes `f.resLE V W : W ⟶ V`, and the condition at
that pair is exactly relative finite presentation of `M|_W` over `f.resLE V W`. So a statement
proved for morphisms of affine schemes globalises: a quasi-coherent module is finitely presented
relative to the base as soon as each of these restrictions is.

## Main results

* `AlgebraicGeometry.finitePresentationRel_sections_of_resLE` reads the module of sections over
  an affine open off relative finite presentation of the restricted morphism.
* `AlgebraicGeometry.isFinitelyPresentedRelative_of_resLE` is the globalisation.

## Implementation notes

For `W : X.Opens` the ring `Γ(W.toScheme, ⊤)` is `Γ(X, W.ι ''ᵁ ⊤)` by definition, and the
sections of `M.restrict W.ι` over `⊤` are the sections of `M` over `W.ι ''ᵁ ⊤`
(`AlgebraicGeometry.Scheme.Modules.restrictAppIso` is the identity isomorphism). What the two
statements below have to supply is therefore only bookkeeping: the equality of opens
`W.ι ''ᵁ ⊤ = W`, which is substituted through a helper so that no `Eq.mpr` is left in the term,
the comparison of the two algebra maps, which is
`AlgebraicGeometry.Scheme.Hom.resLE_appLE`, and the comparison of the module structures, which
differ by `(W.ι.appIso ⊤).inv` and so are identified by
`AlgebraicGeometry.Scheme.Opens.ι_appIso`.

## References

* [Stacks Project, Tag 09T7](https://stacks.math.columbia.edu/tag/09T7)
* [Stacks Project, Tag 05H1](https://stacks.math.columbia.edu/tag/05H1)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Relative finite presentation of a module of sections transports along an equality of the
two opens involved and an equality of the algebra map. -/
private theorem finitePresentationRel_congr {Y S : Scheme.{u}} (g : Y ⟶ S) (G : Y.Modules)
    {V V' : S.Opens} {W W' : Y.Opens} (hV : V' = V) (hW : W' = W)
    (e : W' ≤ g ⁻¹ᵁ V') (e' : W ≤ g ⁻¹ᵁ V) (φ : Γ(S, V') ⟶ Γ(Y, W'))
    (hφ : φ = g.appLE V' W' e)
    (h : letI : Algebra Γ(S, V') Γ(Y, W') := φ.hom.toAlgebra
         Module.FinitePresentationRel Γ(S, V') Γ(Y, W') Γ(G, W')) :
    letI : Algebra Γ(S, V) Γ(Y, W) := (g.appLE V W e').hom.toAlgebra
    Module.FinitePresentationRel Γ(S, V) Γ(Y, W) Γ(G, W) := by
  subst hφ hV hW
  exact h

/-- If the restriction of `G` to an affine open `W` of the source is finitely presented relative
to an affine open `V` of the base containing the image of `W`, then the sections of `G` over `W`
are finitely presented relative to the sections of the base over `V`. -/
theorem finitePresentationRel_sections_of_resLE
    {Y S : Scheme.{u}} (g : Y ⟶ S) [LocallyOfFiniteType g] (G : Y.Modules) [G.IsQuasicoherent]
    {W : Y.Opens} (hW : IsAffineOpen W) {V : S.Opens} (hV : IsAffineOpen V) (hWV : W ≤ g ⁻¹ᵁ V)
    (h : IsFinitelyPresentedRelative (g.resLE V W hWV) (G.restrict W.ι)) :
    letI : Algebra Γ(S, V) Γ(Y, W) := (g.appLE V W hWV).hom.toAlgebra
    Module.FinitePresentationRel Γ(S, V) Γ(Y, W) Γ(G, W) := by
  have _ : IsAffine W.toScheme := hW
  have _ : IsAffine V.toScheme := hV
  have htop : (⊤ : W.toScheme.Opens) ≤ (g.resLE V W hWV) ⁻¹ᵁ ⊤ := by simp
  have key := (isFinitelyPresentedRelative_iff_affine (g.resLE V W hWV) (G.restrict W.ι)).mp h
    ⊤ (isAffineOpen_top W.toScheme) ⊤ (isAffineOpen_top V.toScheme) htop
  let _ : Algebra Γ(S, V.ι ''ᵁ ⊤) Γ(Y, W.ι ''ᵁ ⊤) :=
    ((g.resLE V W hWV).appLE ⊤ ⊤ htop).hom.toAlgebra
  let _ : Module Γ(Y, W.ι ''ᵁ ⊤) Γ(G.restrict W.ι, (⊤ : W.toScheme.Opens)) := by
    show Module Γ(W.toScheme, (⊤ : W.toScheme.Opens)) Γ(G.restrict W.ι, ⊤)
    infer_instance
  let e : Γ(G.restrict W.ι, (⊤ : W.toScheme.Opens)) ≃ₗ[Γ(Y, W.ι ''ᵁ ⊤)] Γ(G, W.ι ''ᵁ ⊤) :=
    { (G.restrictAppIso W.ι ⊤).addCommGroupIsoToAddEquiv with
      map_smul' := fun r m => by
        show (G.restrictAppIso W.ι ⊤).hom (r • m) = r • (G.restrictAppIso W.ι ⊤).hom m
        have hr : (W.ι.appIso ⊤).inv r = r := by
          rw [Scheme.Opens.ι_appIso]
          exact CategoryTheory.id_apply r
        have h0 := Scheme.Modules.smul_restrictAppIso_hom_apply W.ι G ⊤ r m
        rwa [hr] at h0 }
  exact finitePresentationRel_congr g G (Scheme.Opens.ι_image_top V)
    (Scheme.Opens.ι_image_top W) _ hWV _ (Scheme.Hom.resLE_appLE g hWV ⊤ ⊤ htop)
    (Module.FinitePresentationRel.of_linearEquiv e key)

/-- A quasi-coherent module is finitely presented relative to the base as soon as its
restriction to every affine open of the source is finitely presented relative to every affine
open of the base containing the image of that open. -/
theorem isFinitelyPresentedRelative_of_resLE
    {Y S : Scheme.{u}} (g : Y ⟶ S) [LocallyOfFiniteType g] (G : Y.Modules) [G.IsQuasicoherent]
    (h : ∀ (V : S.Opens) (_ : IsAffineOpen V) (W : Y.Opens) (_ : IsAffineOpen W)
      (hWV : W ≤ g ⁻¹ᵁ V), IsFinitelyPresentedRelative (g.resLE V W hWV) (G.restrict W.ι)) :
    IsFinitelyPresentedRelative g G :=
  (isFinitelyPresentedRelative_iff_affine g G).2 fun W hW V hV hWV =>
    finitePresentationRel_sections_of_resLE g G hW hV hWV (h V hV W hW hWV)

end AlgebraicGeometry

end
