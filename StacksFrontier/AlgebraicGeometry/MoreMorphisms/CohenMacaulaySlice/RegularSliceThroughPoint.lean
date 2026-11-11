module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.ConditionalStatements
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.QuasiFiniteSlice
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularIdealSheaf.Spreading
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeRegularImmersion.Chart
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.RegularSequenceSlice
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Immersion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Slicing a flat morphism by a regular sequence, and quasi-finite Cohen–Macaulay slices

Let `f : X ⟶ S` be locally of finite presentation and flat at `x : X`, and let `h₁, …, h_r` be
elements of the local ring `𝒪_{X, x}` whose images in the local ring of the fibre `X_{f x}` at
`x` form a regular sequence.  Then the `h_i` are the germs of global sections `a₁, …, a_r` of an
affine open neighbourhood `U` of `x`, and the zero scheme `V(a)` is a regular immersion into
`U`, contains `x`, is flat and locally of finite presentation over `S`, and stays a regular
immersion after any base change.  This is Stacks tag 06LI.

Feeding that into the Cohen–Macaulay slicing argument gives Stacks tag 0570: a point at which
`f` is Cohen–Macaulay and which is closed in its fibre lies on a regularly immersed subscheme of
`X` that is flat, locally of finite presentation and locally quasi-finite over `S`, and whose
fibre over `f x` is the single point `x`.

## Main results

All four live in the `Stacks.AlgebraicGeometry` namespace.

* `exists_affineOpen_regularImmersion_flat_of_isRegular_fiber`: Stacks tag 06LI.
* `relativeRegularSliceStatement`: the same result in the shape
  `Stacks.AlgebraicGeometry.RelativeRegularSliceStatement` in which the argument for tag 0570
  consumes it.
* `exists_regularImmersion_flat_locallyQuasiFinite_singleton_fiber_of_isCohenMacaulayAt`:
  Stacks tag 0570.
* `statement0570`: the same result in the shape `AlgebraicGeometry.Statement0570` in which the
  Stacks 057K chain consumes it.

## Implementation notes

Nothing is proved here.  The two theorems are assembled from results that already exist in the
library:  `Stacks.AlgebraicGeometry.exists_affineOpen_regularImmersion_of_isRegular_fiber` takes
the statements of Stacks tags 063I and 063W as explicit hypotheses, and those are discharged by
`Stacks.AlgebraicGeometry.statement063I` and `Stacks.AlgebraicGeometry.statement063W`;
`Stacks.AlgebraicGeometry.exists_regularImmersion_flat_locallyQuasiFinite_singleton_fiber` takes
the statement of Stacks tag 06LI as an explicit hypothesis, which is discharged by
`Stacks.AlgebraicGeometry.relativeRegularSliceStatement`.  The statements of the two tags are
therefore stated here unconditionally, and this is where the two tag attributes are placed.

## References

* [Stacks Project, Lemma 37.23.2 (Tag 06LI)](https://stacks.math.columbia.edu/tag/06LI)
* [Stacks Project, Lemma 37.23.4 (Tag 0570)](https://stacks.math.columbia.edu/tag/0570)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

open Stacks.AlgebraicGeometry.RegularIdealSheaf

namespace Stacks.AlgebraicGeometry

universe u

/-- **Stacks Project, Lemma 37.23.2 (Tag 06LI).**  Let `f : X ⟶ S` be locally of finite
presentation and flat at `x : X`, and let `h : Fin r → 𝒪_{X, x}` be a family whose image in the
local ring of the fibre `X_{f x}` at `x` is a regular sequence.  Then there is an affine open `U`
containing `x` and global sections `a : Fin r → Γ(U, ⊤)` whose germs at `x` are the `h i`, such
that `x` lies on the zero scheme `V(a)`, the closed immersion of `V(a)` into `U` is a regular
immersion, `V(a)` is flat and locally of finite presentation over `S`, and the base change of
the immersion along any `S' ⟶ S` is again a regular immersion. -/
@[stacks 06LI, ega "IV 11.3.8" "c) ⇒ b') for F = O_X"]
theorem exists_affineOpen_regularImmersion_flat_of_isRegular_fiber
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) {r : ℕ}
    (h : Fin r → X.presheaf.stalk x) [LocallyOfFinitePresentation f]
    (hflat : IsFlatAt f.toLRSHom.toShHom x)
    (hregular : RingTheory.Sequence.IsRegular
      ((f.fiber (f x)).presheaf.stalk (f.asFiber x))
      (List.ofFn fun i : Fin r =>
        ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom ((f.fiberι_asFiber x).symm ▸ h i))) :
    ∃ (U : X.affineOpens) (hx : x ∈ U.1) (a : Fin r → Γ(U.1.toScheme, ⊤)),
      let y : U.1.toScheme := ⟨x, hx⟩
      let I : U.1.toScheme.IdealSheafData :=
        Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn a))
      (∀ i : Fin r, (U.1.ι.stalkMap y).hom ((show U.1.ι y = x by rfl).symm ▸ h i) =
          U.1.toScheme.presheaf.germ ⊤ y (by trivial) (a i)) ∧
      y ∈ I.support ∧
      IsRegularImmersion I.subschemeι ∧
      Flat (I.subschemeι ≫ U.1.ι ≫ f) ∧
      LocallyOfFinitePresentation (I.subschemeι ≫ U.1.ι ≫ f) ∧
      ∀ (S' : Scheme.{u}) (g : S' ⟶ S),
        IsRegularImmersion (pullback.snd I.subschemeι (pullback.fst (U.1.ι ≫ f) g)) :=
  exists_affineOpen_regularImmersion_of_isRegular_fiber statement063I statement063W f x h hflat
    hregular

/-- **The statement of Stacks tag 06LI**, in the shape
`Stacks.AlgebraicGeometry.RelativeRegularSliceStatement` in which the proof of Stacks tag 0570
consumes it. -/
theorem relativeRegularSliceStatement : RelativeRegularSliceStatement.{u} := by
  intro X S f x r h _ hflat hregular
  exact exists_affineOpen_regularImmersion_flat_of_isRegular_fiber f x h hflat hregular

/-- **Stacks Project, Lemma 37.23.4 (Tag 0570).**  Let `f : X ⟶ S` be locally of finite
presentation, let `x : X` be a point at which `f` is Cohen–Macaulay, and assume `x` is closed in
its fibre `X_{f x}`.  Then there is a regular immersion `i : Z ⟶ X` through `x` such that `Z` is
flat, locally of finite presentation and locally quasi-finite over `S`, and such that the fibre
of `Z` over `f x` is set-theoretically the single point of `Z` above `x`. -/
@[stacks 0570, ega "IV 19.2.9" "x closed in fibre", ega "IV 17.16.1"]
theorem exists_regularImmersion_flat_locallyQuasiFinite_singleton_fiber_of_isCohenMacaulayAt
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] (x : X)
    (hCM : ∃ hf : ∀ y : S, IsLocallyNoetherian (f.fiber y),
      Scheme.Hom.IsCohenMacaulayAt f hf x)
    (hclosed : IsClosed ({f.asFiber x} : Set (f.fiber (f x)))) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ X) (z : Z) (hi : IsImmersion i),
      letI := hi
      i z = x ∧ IsRegularImmersion i ∧
        Flat (i ≫ f) ∧ LocallyOfFinitePresentation (i ≫ f) ∧
        LocallyQuasiFinite (i ≫ f) ∧
        {z' : Z | (i ≫ f) z' = f x} = {z} :=
  exists_regularImmersion_flat_locallyQuasiFinite_singleton_fiber f x hCM hclosed
    relativeRegularSliceStatement

/-- **The statement of Stacks tag 0570**, in the shape `AlgebraicGeometry.Statement0570` in which
the Stacks 057K chain consumes it. -/
theorem statement0570 : Statement0570.{u} := by
  intro X S f _ x hCM hclosed
  exact exists_regularImmersion_flat_locallyQuasiFinite_singleton_fiber_of_isCohenMacaulayAt
    f x hCM hclosed

end Stacks.AlgebraicGeometry

end
