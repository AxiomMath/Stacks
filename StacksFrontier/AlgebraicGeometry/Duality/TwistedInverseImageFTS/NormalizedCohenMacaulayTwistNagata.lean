module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NagataFormalism
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NormalizedCohenMacaulay

/-!
# Normalized dualizing complexes along a Cohen–Macaulay morphism, for Nagata compactifications

Let `S` be Noetherian with a dualizing complex `ω_S^•`, and `f : X ⟶ Y` a separated
Cohen–Macaulay morphism of relative dimension `d` between schemes of finite type over `S`, not
necessarily separated over `S`. For the upper shriek functors of Nagata compactifications
(`Stacks.Duality.UpperShriek.nagata`), with `ω_X^•`, `ω_Y^•` dualizing complexes normalized
relative to `ω_S^•` (for instance `Stacks.Duality.normalizedDualizingComplex`) and
`ω_{X/Y} = H^{-d}(f^! 𝒪_Y)`: `ω_X^• ≅ Lf^* ω_Y^• ⊗ᴸ ω_{X/Y}[d]`, and if `Y` is connected and
Cohen–Macaulay, `ω_X = f^* ω_Y ⊗ ω_{X/Y}` for the unique nonzero cohomology sheaves. This is the
last sentence of [Stacks, Tag 0C10].

## Main results

* `Stacks.Duality.NormalizedOnOpens.nonempty_iso_pullback_tensor_shift_nagata`
* `Stacks.Duality.NormalizedOnOpens.exists_homology_iso_pullback_tensor_nagata`

## References

* [Stacks Project, Tag 0C10](https://stacks.math.columbia.edu/tag/0C10)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

namespace NormalizedOnOpens

variable {X Y S : Scheme.{u}} {f : X ⟶ Y} {q : Y ⟶ S} {p : X ⟶ S} (hpe : f ≫ q = p)
  {hp : IsFiniteTypeOverNoetherian p} {hq : IsFiniteTypeOverNoetherian q}
  {ωS : quasiCoherentDerivedCategoryPlusOfModel S}

include hpe in
/-- **[Stacks, Tag 0C10], last sentence, the complexes.** Let `S` be Noetherian with a dualizing
complex `ω_S^•` and `f : X ⟶ Y` a separated Cohen–Macaulay morphism of relative dimension `d`
between schemes of finite type over `S`, not necessarily separated over `S`. For dualizing
complexes `ω_X^•`, `ω_Y^•` normalized relative to `ω_S^•` and `ω_{X/Y} = H^{-d}(f^! 𝒪_Y)`,
`ω_X^• ≅ Lf^* ω_Y^• ⊗ᴸ ω_{X/Y}[d]`. -/
@[stacks 0C10 "Similar results hold for X and Y of finite type over S, not necessarily \
separated, with complexes normalized relative to omega_S: omega_X = Lf^* omega_Y (x) \
omega_{X/Y}[d]"]
theorem nonempty_iso_pullback_tensor_shift_nagata
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) (hf : IsShriekable f)
    (𝒦X : NormalizedOnOpens UpperShriek.nagata hp ωS)
    (𝒦Y : NormalizedOnOpens UpperShriek.nagata hq ωS)
    (hCM : haveI := hf.target_noetherian
      (ftsHomOf f hf.separatedFiniteType (isSeparatedFiniteType_id Y)
        (Category.comp_id f)).left.IsCohenMacaulay (isLocallyNoetherian_fiber_left _))
    (d : ℕ) (hd : ∀ x : X, topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) =
      (d : WithBot ℕ∞)) :
    haveI := hf.target_noetherian
    Nonempty (𝒦X.complex.obj ≅ ((quasiCoherentDerivedTensor X).obj
        ((quasiCoherentDerivedPullback' f).obj 𝒦Y.complex.obj)).obj
          (relativeDualizingSheafShift (ftsHomOf f hf.separatedFiniteType
            (isSeparatedFiniteType_id Y) (Category.comp_id f)) (nagataCompactification f hf)
            hCM d hd)) :=
  nonempty_iso_pullback_tensor_shift_ofCompactifications nagataCompactification hpe hωS hf
    𝒦X 𝒦Y hCM d hd

include hpe in
/-- **[Stacks, Tag 0C10], last sentence, the dualizing modules.** In the situation of
`nonempty_iso_pullback_tensor_shift_nagata`, if moreover `Y` is connected and Cohen–Macaulay, the
normalized complexes `ω_Y^•` and `ω_X^•` are concentrated in single degrees `m` and `m - d`, and
their cohomology sheaves `ω_Y`, `ω_X` there satisfy `ω_X ≅ f^* ω_Y ⊗ ω_{X/Y}`. -/
@[stacks 0C10 "Similar results hold for X and Y of finite type over S, not necessarily \
separated, with complexes normalized relative to omega_S: omega_X = f^* omega_Y (x) omega_{X/Y} \
for connected Cohen-Macaulay schemes"]
theorem exists_homology_iso_pullback_tensor_nagata
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) (hf : IsShriekable f)
    (𝒦X : NormalizedOnOpens UpperShriek.nagata hp ωS)
    (𝒦Y : NormalizedOnOpens UpperShriek.nagata hq ωS)
    (hCM : haveI := hf.target_noetherian
      (ftsHomOf f hf.separatedFiniteType (isSeparatedFiniteType_id Y)
        (Category.comp_id f)).left.IsCohenMacaulay (isLocallyNoetherian_fiber_left _))
    (d : ℕ) (hd : ∀ x : X, topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) =
      (d : WithBot ℕ∞))
    [ConnectedSpace Y] (hY : AlgebraicGeometry.IsCohenMacaulay Y) :
    haveI := hf.target_noetherian
    ∃ m : ℤ,
      (∀ i : ℤ, i ≠ m → IsZero ((DerivedCategory.homologyFunctor Y.Modules i).obj
        𝒦Y.complex.obj.obj)) ∧
      (∀ i : ℤ, i ≠ m - d → IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj
        𝒦X.complex.obj.obj)) ∧
      Nonempty ((DerivedCategory.homologyFunctor X.Modules (m - d)).obj 𝒦X.complex.obj.obj ≅
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj
          ((Scheme.Modules.pullback f).obj
            ((DerivedCategory.homologyFunctor Y.Modules m).obj 𝒦Y.complex.obj.obj))).obj
          (relativeDualizingSheaf (ftsHomOf f hf.separatedFiniteType
            (isSeparatedFiniteType_id Y) (Category.comp_id f)) (nagataCompactification f hf)
            d)) :=
  exists_homology_iso_pullback_tensor_ofCompactifications nagataCompactification hpe hωS hf
    𝒦X 𝒦Y hCM d hd hY

end NormalizedOnOpens

end Stacks.Duality
