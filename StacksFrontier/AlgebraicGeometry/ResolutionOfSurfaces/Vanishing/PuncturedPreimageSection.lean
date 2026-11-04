module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomSlice
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.TorsionInFirstCohomology

/-!
# A section killed by the maximal ideal dies over the punctured spectrum

Let `A` be a local ring with maximal ideal `𝔪` and let `f : X ⟶ Spec A` be a scheme over it. A
global section of a sheaf of `𝒪_X`-modules annihilated by every element of `𝔪` — acting through
`A ⟶ Γ(X, 𝒪_X)` — restricts to zero on the preimage of any open of `Spec A` missing the closed
point, in particular on `f⁻¹(U)` for `U` the punctured spectrum.

The reason is that `𝔪` generates the unit ideal away from the closed point: every prime of a
local ring is contained in `𝔪`, so a prime other than `𝔪` omits some element of it, and the
preimages of the basic opens `D(r)` for `r ∈ 𝔪` therefore cover `f⁻¹(U)`. On `f⁻¹(D(r))` the
pullback of `r` is invertible, so a section it annihilates vanishes there; and a section
vanishing near every point of an open vanishes on that open.

This is the step that makes the unit section of `𝒪_X/a𝒪_X` in the proof of [Stacks, Tag 0AXC]
die on `f⁻¹(U)`, which is what feeds [Stacks, Tag 0AXB].

## Main results

* `AlgebraicGeometry.res_preimage_eq_zero_of_maximalIdeal_smul_eq_zero`: the vanishing.

## Implementation notes

The three ingredients are `Stacks.SheafOfModules.eq_zero_of_locally_zero'`, which reduces the
claim to a neighbourhood of each point; `AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen`,
which makes the pullback of `r` invertible on its basic open, together with
`AlgebraicGeometry.Scheme.preimage_basicOpen_top` and
`AlgebraicGeometry.basicOpen_eq_of_affine` identifying that basic open with `f⁻¹(D(r))`; and
`Stacks.SheafOfModules.res_smul`, the semilinearity of the restriction maps, which is what
turns `r • s = 0` over `⊤` into `(r|_V) • (s|_V) = 0`.

The neighbourhood produced at a point is `X.basicOpen (baseSection X f r) ⊓ f⁻¹(W)` rather than
`X.basicOpen (baseSection X f r)` alone, since it has to be an open *of* `f⁻¹(W)` for
`eq_zero_of_locally_zero'`; the intersection costs nothing.

*Which spelling the scalar is in.* The ring of sections is written
`X.ringCatSheaf.obj.obj (op U)` and not the notationally identical `Γ(X, U)`: as the
implementation notes of
`StacksFrontier/AlgebraicGeometry/ResolutionOfSurfaces/Boundedness/TorsionInFirstCohomology.lean`
record, the two have the same elements but the module structure on the sections of a sheaf of
modules is found by unification on the first spelling only, so `•` does not elaborate at the
second. `AlgebraicGeometry.Scheme.commRingRingCatSheafObj` is reactivated here for the same
reason. `AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen` is stated in the `Γ(X, U)`
spelling, so the invertibility crosses into the other one by passing a term, which defeq at
default transparency accepts. The restricted scalar is named with
`Stacks.SheafOfModules.resR` rather than written out, because `res_smul` is stated with it and
a rewrite will not see through the definition otherwise; the `.op` it hides is why the
composite of the two restrictions has to be assembled before that name is introduced, with
`show` crossing the two descriptions.

## References

* [Stacks Project, Tag 0AXC](https://stacks.math.columbia.edu/tag/0AXC)
* [Stacks Project, Tag 0AXK](https://stacks.math.columbia.edu/tag/0AXK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

attribute [local instance] Scheme.commRingRingCatSheafObj

variable {A : Type u} [CommRing A] [IsLocalRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A))

/-- Away from the closed point of a local ring some element of the maximal ideal is invertible:
a prime other than the maximal ideal omits one, every prime being contained in it. -/
private lemma exists_mem_maximalIdeal_notMem_asIdeal
    (p : (Spec (CommRingCat.of A)).carrier) (hp : p ≠ IsLocalRing.closedPoint A) :
    ∃ r ∈ IsLocalRing.maximalIdeal A, r ∉ p.asIdeal := by
  have : p.asIdeal.IsPrime := p.isPrime
  have hle : p.asIdeal ≤ IsLocalRing.maximalIdeal A :=
    IsLocalRing.le_maximalIdeal_of_isPrime p.asIdeal
  have hne : p.asIdeal ≠ IsLocalRing.maximalIdeal A := fun h => hp (PrimeSpectrum.ext h)
  by_contra hcon
  refine hne (le_antisymm hle fun x hx => ?_)
  by_contra hxp
  exact hcon ⟨x, hx, hxp⟩

omit [IsLocalRing A] in
/-- The basic open of the image in `Γ(X, 𝒪_X)` of an element of the base ring is the preimage of
its basic open in the spectrum. -/
private lemma basicOpen_baseSection (r : A) :
    X.basicOpen (baseSection X f r) =
      f ⁻¹ᵁ ((Spec (CommRingCat.of A)).basicOpen
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv r)) := by
  rw [Scheme.preimage_basicOpen_top]
  rfl

/-- **A global section annihilated by the maximal ideal of the base restricts to zero over any
open missing the closed point.** In particular it dies on the preimage of the punctured
spectrum, which is how the unit section of `𝒪_X/a𝒪_X` in the proof of [Stacks, Tag 0AXC] comes
to vanish there. -/
theorem res_preimage_eq_zero_of_maximalIdeal_smul_eq_zero
    (M : SheafOfModules.{u} X.ringCatSheaf) (s : ToType (M.val.obj (op ⊤)))
    (hs : ∀ r ∈ IsLocalRing.maximalIdeal A, baseSection X f r • s = 0)
    (W : (Spec (CommRingCat.of A)).Opens) (hW : IsLocalRing.closedPoint A ∉ W) :
    Stacks.SheafOfModules.res M (homOfLE (le_top : f ⁻¹ᵁ W ≤ ⊤)) s = 0 := by
  refine Stacks.SheafOfModules.eq_zero_of_locally_zero' M _ fun y hy => ?_
  obtain ⟨r, hrm, hry⟩ :=
    exists_mem_maximalIdeal_notMem_asIdeal (f.base y) (fun h => hW (h ▸ hy))
  have hyb : y ∈ X.basicOpen (baseSection X f r) := by
    rw [basicOpen_baseSection f r]
    show f.base y ∈ (Spec (CommRingCat.of A)).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv r)
    rw [basicOpen_eq_of_affine (R := CommRingCat.of A) r]
    exact (PrimeSpectrum.mem_basicOpen r (f.base y)).2 hry
  refine ⟨X.basicOpen (baseSection X f r) ⊓ f ⁻¹ᵁ W, homOfLE inf_le_right, ⟨hyb, hy⟩, ?_⟩
  rw [Stacks.SheafOfModules.res_res, homOfLE_comp]
  have hunit : IsUnit (Stacks.SheafOfModules.resR X.ringCatSheaf
      (homOfLE (show X.basicOpen (baseSection X f r) ⊓ f ⁻¹ᵁ W ≤ ⊤ from le_top))
      (baseSection X f r)) := by
    have h1 : IsUnit (X.ringCatSheaf.obj.map
        (homOfLE (X.basicOpen_le (baseSection X f r))).op (baseSection X f r)) :=
      RingedSpace.isUnit_res_basicOpen (X := X.toRingedSpace) (baseSection X f r)
    have h2 := h1.map (ConcreteCategory.hom (X.ringCatSheaf.obj.map (homOfLE (show
        X.basicOpen (baseSection X f r) ⊓ f ⁻¹ᵁ W ≤ X.basicOpen (baseSection X f r)
        from inf_le_left)).op))
    have hmor : (homOfLE (show X.basicOpen (baseSection X f r) ⊓ f ⁻¹ᵁ W ≤ ⊤ from le_top)).op
        = (homOfLE (X.basicOpen_le (baseSection X f r))).op ≫
          (homOfLE (show X.basicOpen (baseSection X f r) ⊓ f ⁻¹ᵁ W ≤
            X.basicOpen (baseSection X f r) from inf_le_left)).op :=
      Subsingleton.elim _ _
    show IsUnit (X.ringCatSheaf.obj.map
      (homOfLE (show X.basicOpen (baseSection X f r) ⊓ f ⁻¹ᵁ W ≤ ⊤ from le_top)).op
      (baseSection X f r))
    rw [hmor, X.ringCatSheaf.obj.map_comp_apply]
    exact h2
  refine (hunit.smul_eq_zero).1 ?_
  rw [← Stacks.SheafOfModules.res_smul, hs r hrm, Stacks.SheafOfModules.res_zero]

end AlgebraicGeometry

end
