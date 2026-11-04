module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Restrict
public import StacksFrontier.RingTheory.LocalCohomology.Deps.PuncturedSpectrumAffine
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation

/-!
# Coherent triples on the punctured spectrum and the closed fibre

Let `A` be a local ring and `f ∈ A`. A *coherent triple* for the pair `(A, f)` consists of a
coherent module `F` on the punctured spectrum `Spec A ∖ {𝔪}` on which multiplication by `f` is
injective, a coherent module `F₀` on the closed fibre `Spec (A / fA)`, and an identification of
the two over the punctured closed fibre. Such a triple is the datum from which the Euler
characteristic attached to `(A, f)` is computed.

This file sets up that datum: the three schemes involved, the action of `f` on the sections of a
module over the punctured spectrum, the torsion-freeness condition, and the triple itself.

## Main definitions

* `Stacks.Algebraization.baseScheme`, `Stacks.Algebraization.closedFibre` and
  `Stacks.Algebraization.closedImmersion`: the spectrum of `A`, the spectrum of `A / fA` and the
  closed immersion between them.
* `Stacks.Algebraization.puncturedClosedFibre`: the part of the closed fibre lying over the
  punctured spectrum.
* `Stacks.Algebraization.scalarOnOpen`: the image of `f` in the functions on an open of the
  punctured spectrum.
* `Stacks.Algebraization.IsFTorsionFree`: multiplication by `f` is injective on every module of
  sections.
* `Stacks.Algebraization.CoherentTriple`: the coherent triple itself.

## Main results

* `Stacks.Algebraization.regular_of_mono_pushforward`: a module on `Spec A` admitting a
  monomorphism into the direct image of an `f`-torsion-free module has `f` acting regularly on
  all of its sections.

## Implementation notes

The punctured spectrum is `Stacks.Divisors.puncturedSpectrum`, the complement of the closed
point, and the punctured closed fibre is its preimage under the closed immersion rather than the
punctured spectrum of `A / fA`; the two agree when `f` lies in the maximal ideal, which is not
assumed here.

The compatibility datum of a triple is an isomorphism of pullbacks along the two routes around
the square

```
Spec(A/fA) ∖ {𝔪}  ⟶  Spec A ∖ {𝔪}
       |                   |
       v                   v
   Spec(A/fA)        ⟶   Spec A
```

phrased with `AlgebraicGeometry.morphismRestrict` for the top horizontal arrow, so that no
choice of pullback has to be made.

Multiplication by `f` is recorded as `IsSMulRegular` on the sections over each open rather than
as injectivity of a morphism of sheaves, because that is the form in which the length
computations downstream consume it.

## References

* [Stacks Project, Tag 0F23](https://stacks.math.columbia.edu/tag/0F23)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

/-- The spectrum of the base ring. -/
public noncomputable abbrev baseScheme (A : Type u) [CommRing A] : Scheme.{u} :=
  Spec (.of A)

/-- The closed fibre of the base scheme at `f`, the spectrum of `A / fA`. -/
public noncomputable abbrev closedFibre (A : Type u) [CommRing A] (f : A) : Scheme.{u} :=
  Spec (.of (A ⧸ Ideal.span {f}))

/-- The closed immersion of the closed fibre into the base scheme. -/
public noncomputable abbrev closedImmersion (A : Type u) [CommRing A] (f : A) :
    closedFibre A f ⟶ baseScheme A :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))

/-- The part of the closed fibre lying over the punctured spectrum of `A`. -/
public noncomputable abbrev puncturedClosedFibre (A : Type u) [CommRing A] [IsLocalRing A]
    (f : A) : (closedFibre A f).Opens :=
  closedImmersion A f ⁻¹ᵁ Stacks.Divisors.puncturedSpectrum A

/-- The image of `f` in the functions on an open of the punctured spectrum of `A`. -/
public noncomputable def scalarOnOpen (A : Type u) [CommRing A] [IsLocalRing A]
    (f : A) (V : (Stacks.Divisors.puncturedSpectrum A).toScheme.Opens) :
    Γ((Stacks.Divisors.puncturedSpectrum A).toScheme, V) :=
  ((Stacks.Divisors.puncturedSpectrum A).toScheme.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op)
    ((Stacks.Divisors.puncturedSpectrum A).ι.appTop
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f))

/-- A module on the punctured spectrum of `A` is `f`-torsion-free when multiplication by the
image of `f` is injective on its sections over every open. -/
public def IsFTorsionFree (A : Type u) [CommRing A] [IsLocalRing A]
    (f : A) (F : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules) : Prop :=
  ∀ V : (Stacks.Divisors.puncturedSpectrum A).toScheme.Opens,
    IsSMulRegular Γ(F, V) (scalarOnOpen A f V)

/-- **A coherent triple for a local ring `A` and an element `f`.** It consists of an
`f`-torsion-free coherent module on the punctured spectrum, a coherent module on the closed
fibre, and an identification of the two over the punctured closed fibre. -/
public structure CoherentTriple (A : Type u) [CommRing A] [IsLocalRing A] (f : A) where
  /-- The coherent module on the punctured spectrum. -/
  F : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules
  /-- The coherent module on the closed fibre. -/
  F₀ : (closedFibre A f).Modules
  /-- `F` is coherent. -/
  coherent_F : _root_.SheafOfModules.IsCoherent F
  /-- `F₀` is coherent. -/
  coherent_F₀ : _root_.SheafOfModules.IsCoherent F₀
  /-- Multiplication by `f` is injective on the sections of `F`. -/
  torsionFree : IsFTorsionFree A f F
  /-- The identification of `F` and `F₀` over the punctured closed fibre. -/
  alpha : (Scheme.Modules.pullback
      (morphismRestrict (closedImmersion A f) (Stacks.Divisors.puncturedSpectrum A))).obj F ≅
    (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj F₀

/-- Multiplying a section of the direct image of `F` along the inclusion of the punctured
spectrum by the restriction of `f` is multiplying the corresponding section of `F` by the image
of `f` there. -/
public theorem pushforward_scalarOnOpen
    (A : Type u) [CommRing A] [IsLocalRing A] (f : A)
    (F : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules)
    (V : (baseScheme A).Opens)
    (s : Γ((Scheme.Modules.pushforward
      (Stacks.Divisors.puncturedSpectrum A).ι).obj F, V)) :
    ((baseScheme A).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)) • s =
    scalarOnOpen A f ((Stacks.Divisors.puncturedSpectrum A).ι ⁻¹ᵁ V) •
      (show Γ(F, (Stacks.Divisors.puncturedSpectrum A).ι ⁻¹ᵁ V) from s) := by
  show ((Stacks.Divisors.puncturedSpectrum A).ι.app V
      ((baseScheme A).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f))) •
    (show Γ(F, (Stacks.Divisors.puncturedSpectrum A).ι ⁻¹ᵁ V) from s) = _
  congr 1

/-- **`f`-torsion-freeness passes to a submodule of a direct image.** If `F` on the punctured
spectrum is `f`-torsion-free and `G` on `Spec A` admits a monomorphism into the direct image of
`F`, then multiplication by `f` is injective on the sections of `G` over every open. -/
public theorem regular_of_mono_pushforward
    (A : Type u) [CommRing A] [IsLocalRing A] (f : A)
    (F : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules)
    (hF : IsFTorsionFree A f F) (G : (baseScheme A).Modules)
    (g : G ⟶ (Scheme.Modules.pushforward (Stacks.Divisors.puncturedSpectrum A).ι).obj F)
    [Mono g] : ∀ V : (baseScheme A).Opens,
      IsSMulRegular Γ(G, V)
        ((baseScheme A).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f)) := by
  intro V x y hxy
  have hmono : Mono (C := SheafOfModules (baseScheme A).ringCatSheaf) g := inferInstanceAs (Mono g)
  have : Mono g.val := (SheafOfModules.forget _).map_mono g
  apply PresheafOfModules.injective_of_mono g.val (.op V)
  apply hF ((Stacks.Divisors.puncturedSpectrum A).ι ⁻¹ᵁ V)
  have h := congrArg (g.app V) hxy
  rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, pushforward_scalarOnOpen,
    pushforward_scalarOnOpen] at h
  exact h

end Stacks.Algebraization

end
