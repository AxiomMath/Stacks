module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.SchemeRepresentation
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.SiteRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.InfiniteFibreContractedPiece

/-!
# The Hilbert space of `ℙⁿ_ℤ/ℤ` has a Noetherian space of points

The proof of Stacks 0E96 covers the subset `T ⊆ |𝒫olarized|` it is about by the image of the
space of points of
`H = Hilb^{P, 𝒪(1)}_{ℙⁿ_ℤ/ℤ}`,
and uses of the properness of `H` over `Spec(ℤ)` (Stacks 0DPH) only that `|H|` is quasi-compact.
This file produces that `H` over the big fppf site of a terminal base scheme, with the stronger
conclusion that `|H|` is a *Noetherian* topological space — which is what makes the algebraicity
of `𝒫olarized` (Quot, Theorem 0D4X) unnecessary in
`StacksFrontier/AlgebraicGeometry/Quot/PolarizedHilbertBoundedImage.lean`.

The scheme-level input is Stacks 0DPA at `r = 1`: `Quot^P_{𝒪/ℙⁿ_ℤ/ℤ}`, which is `Hilb^P` of
`ℙⁿ_ℤ/ℤ`, is represented by a scheme `X` proper over `Spec(ℤ)`
(`AlgebraicGeometry.ProjectiveQuot.exists_isProper_iso_hilbertFunctor`). Such an `X` lies in every
big fppf site, is a Noetherian topological space, and the presheaf it represents on the site over
a terminal base is the restriction of the presheaf it represents on all schemes; the space of
points of a represented presheaf is homeomorphic to the representing scheme by clause (1) of
Stacks 03BX.

## Main definitions

* `AlgebraicGeometry.terminalSiteObject`: a scheme of the site, read as an object of the site over
  a terminal base — the structure morphism being the unique one.
* `AlgebraicGeometry.yonedaTerminalSiteObjectIso`: the presheaf represented on the site by such an
  object is the restriction of the presheaf represented on all schemes.

## Main results

* `AlgebraicGeometry.noetherianSpace_of_isProper_terminal_from`: a scheme proper over the terminal
  scheme is a Noetherian topological space.
* `AlgebraicGeometry.exists_noetherianSpace_points_yoneda_iso_hilbertFunctor`: **the Hilbert space
  of the proof of Stacks 0E96** — an object of the site over a terminal base whose represented
  presheaf is `Hilb^P_{ℙⁿ_ℤ/ℤ}` and whose space of points is Noetherian.

## References

* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 0DPA](https://stacks.math.columbia.edu/tag/0DPA)
* [Stacks Project, Tag 0DPH](https://stacks.math.columbia.edu/tag/0DPH)
* [Stacks Project, Tag 0E96](https://stacks.math.columbia.edu/tag/0E96)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- **A scheme proper over the terminal scheme is a Noetherian topological space.** Properness
over `Spec(ℤ)` gives both halves of `AlgebraicGeometry.IsNoetherian`: local finite type over the
Noetherian ring `ULift ℤ` makes the scheme locally Noetherian, and quasi-compactness over the
affine `Spec(ℤ)` makes it compact. -/
theorem noetherianSpace_of_isProper_terminal_from {X : Scheme.{u}}
    (hX : IsProper (terminal.from X)) : NoetherianSpace X := by
  have : IsNoetherianRing (ULift.{u} ℤ) := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  have := ProjectiveQuot.isProper_of_isProper_terminal_from hX
    (specULiftZIsTerminal.from X)
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (specULiftZIsTerminal.from X)
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (specULiftZIsTerminal.from X)
  have : IsNoetherian X := ⟨⟩
  infer_instance

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)

/-- A scheme of the big fppf site, read as an object of the site over a terminal base scheme:
the structure morphism is the unique morphism to the base. -/
def terminalSiteObject (hT : IsTerminal (B.obj hS)) {X : Scheme.{u}} (hX : B.Contains X) :
    BigFppfOver B S hS :=
  Over.mk (hT.from (B.obj hX))

/-- The underlying scheme of `AlgebraicGeometry.terminalSiteObject` at `X` is `X`. -/
@[simp]
theorem toScheme_obj_terminalSiteObject (hT : IsTerminal (B.obj hS)) {X : Scheme.{u}}
    (hX : B.Contains X) :
    (BigFppfOver.toScheme B S hS).obj (terminalSiteObject B hS hT hX) = X :=
  rfl

/-- The morphisms of the big fppf site over a terminal base from an object `T` to a scheme `X` of
the site are the morphisms of schemes from the underlying scheme of `T` to `X`: the compatibility
with the structure morphisms is automatic. -/
def homTerminalSiteObjectEquiv (hT : IsTerminal (B.obj hS)) {X : Scheme.{u}}
    (hX : B.Contains X) (T : BigFppfOver B S hS) :
    (T ⟶ terminalSiteObject B hS hT hX) ≃
      ((BigFppfOver.toScheme B S hS).obj T ⟶ X) where
  toFun f := (BigFppfOver.toScheme B S hS).map f
  invFun g := Over.homMk (ObjectProperty.homMk g) (hT.hom_ext _ _)
  left_inv _ := (BigFppfOver.toScheme B S hS).map_injective rfl
  right_inv _ := rfl

/-- **The presheaf represented on the site by a scheme of the site, over a terminal base.** It is
the restriction to the site of the presheaf represented by that scheme on all schemes. -/
def yonedaTerminalSiteObjectIso (hT : IsTerminal (B.obj hS)) {X : Scheme.{u}}
    (hX : B.Contains X) :
    yoneda.obj (terminalSiteObject B hS hT hX) ≅
      (BigFppfOver.toScheme B S hS).op ⋙ yoneda.obj X :=
  NatIso.ofComponents (fun T ↦ (homTerminalSiteObjectEquiv B hS hT hX T.unop).toIso) fun f ↦ by
    ext x
    exact (BigFppfOver.toScheme B S hS).map_comp f.unop x

/-- **The Hilbert space of the proof of Stacks 0E96.** For `n ∈ ℕ` and `P ∈ ℚ[t]` there is an
object `U₀` of the big fppf site over a terminal base scheme whose space of points is a
Noetherian topological space and whose represented presheaf is the restriction to the site of
`Hilb^P_{ℙⁿ_ℤ/ℤ} = Quot^P_{𝒪/ℙⁿ_ℤ/ℤ}`.

By Stacks 0DPA at `r = 1` the functor `Quot^P_{𝒪/ℙⁿ_ℤ/ℤ}` on schemes is represented by a scheme
`X` proper over `Spec(ℤ)` (`AlgebraicGeometry.ProjectiveQuot.exists_isProper_iso_hilbertFunctor`).
Being proper over the terminal scheme, `X` lies in every big fppf site and is a Noetherian space
(`AlgebraicGeometry.noetherianSpace_of_isProper_terminal_from`), and the presheaf it represents on
the site is the restriction of the one it represents on all schemes
(`AlgebraicGeometry.yonedaTerminalSiteObjectIso`), whose space of points is homeomorphic to `X` by
clause (1) of Stacks 03BX.

This is `H` of the source's proof, with the properness of Stacks 0DPH used through the stronger
consequence that `|H|` is Noetherian rather than merely quasi-compact. -/
theorem exists_noetherianSpace_points_yoneda_iso_hilbertFunctor (hT : IsTerminal (B.obj hS))
    (n : ℕ) (P : Polynomial ℚ) :
    ∃ U₀ : BigFppfOver B S hS,
      @NoetherianSpace (Space.points B S hS (yoneda.obj U₀))
        (Space.pointTopology B S hS (yoneda.obj U₀)) ∧
      Nonempty (yoneda.obj U₀ ⋙ uliftFunctor.{u + 1} ≅
        (BigFppfOver.toScheme B S hS).op ⋙ ProjectiveQuot.hilbertFunctor.{u} n 1 P) := by
  obtain ⟨X, hX, ⟨hF⟩⟩ := ProjectiveQuot.exists_isProper_iso_hilbertFunctor.{u} n 1 le_rfl P
  have hXB : B.Contains X := ProjectiveQuot.contains_of_isProper_terminal_from B hX
  refine ⟨terminalSiteObject B hS hT hXB,
    Space.noetherianSpace_points_yoneda B S hS _ (noetherianSpace_of_isProper_terminal_from hX),
    ⟨?_⟩⟩
  exact Functor.isoWhiskerRight (yonedaTerminalSiteObjectIso B hS hT hXB)
      uliftFunctor.{u + 1} ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (BigFppfOver.toScheme B S hS).op hF.symm

end AlgebraicGeometry

end
