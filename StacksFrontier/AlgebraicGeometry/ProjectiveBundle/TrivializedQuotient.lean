module

public import StacksFrontier.AlgebraicGeometry.ProjF1Dehomogenization.Trivialization
public import StacksFrontier.AlgebraicGeometry.ProjInvertibleLocus.Restriction

/-!
# A quotient trivialized on an open, read as a map into the direct image of the structure sheaf

Let `X` be a scheme, `q : F ⟶ L` a surjection of `𝒪_X`-modules and `U ⊆ X` an open on which `L`
is trivial. **This file turns that data into a morphism**

`κ : F ⟶ (U.ι)_*𝒪_U`

which is the shape `Stacks.SymmetricDehomogenize.dehomogenize` consumes: the dehomogenization of
`Sym F` over `U` at a trivialized quotient is built from exactly such a `κ`, and the morphism
into the chart of `𝐏(F)` over `U` is built from the dehomogenization.

## Main definitions

* `Stacks.RelativeProj.trivializedQuotientHom`: **`κ`**, the transpose across the
  restriction/pushforward adjunction of `q` restricted to `U` and followed by the
  trivialization.

## Main results

* `Stacks.RelativeProj.trivializedQuotientHom_app`: `κ` on sections over an open, as the three
  factors it is built from. True by `rfl`, since every factor of the adjunction's unit is.
* `Stacks.RelativeProj.exists_app_trivializedQuotientHom_eq_one`: **a section of `F` over `U`
  whose image under `κ` is the unit section.** This is what the chart construction needs: by
  `Stacks.SymmetricDehomogenize.dehomogenize_of_one` the degree-one coefficient of the
  dehomogenization at that section is then `φ 1`, hence a unit, which is the hypothesis of
  `Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.fromOfIsUnit`.

## Implementation notes

**Why the adjunction rather than a direct construction.** `(U.ι)_*𝒪_U` has `Γ(U.ι ⁻¹ᵁ V, 𝒪_U)` for
its sections over `V`, so a morphism into it out of `F` is by definition a compatible family of
maps `Γ(F, V) ⟶ Γ(𝒪_U, U.ι ⁻¹ᵁ V)`; assembling that family by hand means checking naturality and
semilinearity over every inclusion of opens. The transpose across
`AlgebraicGeometry.Scheme.Modules.restrictAdjunction` — restriction is left adjoint to
pushforward along an open immersion — produces it from a single morphism on `U`, and the
adjunction's unit is an explicit presheaf restriction map
(`AlgebraicGeometry.Scheme.Modules.restrictAdjunction_unit_app_app`), which is why
`trivializedQuotientHom_app` below is `rfl`.

**Two spellings of "trivial on `U`" are crossed, once.** The trivializations this repository
produces — `Stacks.LineBundle.Situation.exists_trivializing_affineOpen`, through
`Stacks.RelativeProj.exists_affineOpen_trivializing_surjective` — are isomorphisms
`L.over U ≅ 𝒪` on the *restricted site* `Over U`, while the adjunction wants an isomorphism of
modules on the open *subscheme* `U.toScheme`. The comparison is Mathlib's
`AlgebraicGeometry.Scheme.Modules.overFunctorEquiv`, and this file does not re-derive it: the
existing wrapper `Stacks.AlgebraicGeometry.ProjInvertibleLocus.restrictIsoUnitOfOverIsoUnit`
is the single crossing.

**Why the conclusion is `= 1` and not `IsUnit`.** The chart only needs a unit, but the stronger
statement is no harder — the trivialization is an isomorphism, so the unit section has a preimage
— and it is what a later comparison of the classified morphism with the quotient it came from
will want. `IsUnit` follows by `isUnit_one`.

The surjectivity of `q` on sections over `U` is a hypothesis rather than derived from `Epi q`,
because it is false for a general open and the statement that supplies it,
`Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen`, needs `U` affine and both modules
quasi-coherent. `Stacks.RelativeProj.exists_affineOpen_trivializing_surjective` produces it
together with the trivialization, which is the form the consumer has.

No `@[stacks]` attribute is attached. Tag 0B3V is the bijection between sections and invertible
quotients; transposing one morphism across an adjunction asserts no part of it.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.ProjF1Dehomogenization
open Stacks.AlgebraicGeometry.ProjInvertibleLocus

universe u

namespace Stacks.RelativeProj

variable {X : Scheme.{u}} {F L : X.Modules} (U : X.Opens) (q : F ⟶ L)
  (e : L.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))

/-- **A quotient trivialized on `U`, read as a morphism into `(U.ι)_*𝒪_U`.** The restriction of
`q` to the open subscheme `U`, followed by the trivialization of `L` there, transposed across the
adjunction between restriction and pushforward along the inclusion of `U`.

This is the `κ` that `Stacks.SymmetricDehomogenize.gradedHom` and
`Stacks.SymmetricDehomogenize.dehomogenize` consume. -/
public def trivializedQuotientHom : F ⟶ pushforwardUnit U.ι :=
  (Scheme.Modules.restrictAdjunction U.ι).homEquiv F
      (SheafOfModules.unit U.toScheme.ringCatSheaf)
    ((Scheme.Modules.restrictFunctor U.ι).map q ≫ (restrictIsoUnitOfOverIsoUnit U L e).hom)

/-- **`κ` on sections over an open `V`**: restrict from `V` to the part of `V` inside `U`, then
apply `q` and the trivialization there. Every factor of the adjunction's unit is a presheaf
restriction map, so this holds by `rfl`. -/
public theorem trivializedQuotientHom_app (V : X.Opens) :
    (trivializedQuotientHom U q e).app V =
      F.presheaf.map (homOfLE (U.ι.image_preimage_le V)).op ≫
        ((Scheme.Modules.restrictFunctor U.ι).map q ≫
          (restrictIsoUnitOfOverIsoUnit U L e).hom).app (U.ι ⁻¹ᵁ V) :=
  rfl

/-- **`κ` on a section over `U` itself, read in the ring of functions of the open subscheme.**
The three factors are the restriction from `U` to the image of its own preimage, `q` there, and
the trivialization. True by `rfl`; it is stated because the composite is the only form in which
the invertibility hypothesis of the chart can be checked. -/
public theorem ofPushforwardUnit_trivializedQuotientHom_app (m : Γ(F, U)) :
    ofPushforwardUnit U.ι ((trivializedQuotientHom U q e).val.app (op U) m) =
      ofPushforwardUnit U.ι (W := op U)
        ((restrictIsoUnitOfOverIsoUnit U L e).hom.val.app (op (U.ι ⁻¹ᵁ U))
          (q.val.app (op (U.ι ''ᵁ (U.ι ⁻¹ᵁ U)))
            (F.presheaf.map (homOfLE (U.ι.image_preimage_le U)).op m))) :=
  rfl

/-- **A section of `F` over `U` that `κ` carries to the unit section.** The trivialization is an
isomorphism, so the unit section of `𝒪_U` has a preimage in the restriction of `L`; by the
hypothesis that `q` is surjective on sections over `U` that preimage is the image of a section of
`F`; and the restriction map `κ` precomposes with is an isomorphism, `U` being the image of its
own preimage under the inclusion.

This supplies the invertibility hypothesis of
`Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.fromOfIsUnit` through
`Stacks.SymmetricDehomogenize.dehomogenize_of_one`: that lemma computes the degree-one
coefficient of the dehomogenization at `m` as `φ` of this section, which is then `φ 1`. -/
public theorem exists_app_trivializedQuotientHom_eq_one
    (hq : Function.Surjective (q.val.app (op U))) :
    ∃ m : Γ(F, U), ofPushforwardUnit U.ι
      ((trivializedQuotientHom U q e).val.app (op U) m) = 1 := by
  have heq : U.ι ''ᵁ (U.ι ⁻¹ᵁ U) = U := by simp
  -- The unit section of `𝒪_U` has a preimage under the trivialization, …
  let one : Γ(SheafOfModules.unit U.toScheme.ringCatSheaf, U.ι ⁻¹ᵁ U) :=
    (1 : U.toScheme.ringCatSheaf.obj.obj (op (U.ι ⁻¹ᵁ U)))
  obtain ⟨y, hy⟩ : ∃ y, (restrictIsoUnitOfOverIsoUnit U L e).hom.val.app (op (U.ι ⁻¹ᵁ U)) y =
      one :=
    ⟨(restrictIsoUnitOfOverIsoUnit U L e).inv.val.app (op (U.ι ⁻¹ᵁ U)) one,
      congrArg (fun φ : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
          SheafOfModules.unit U.toScheme.ringCatSheaf => φ.val.app (op (U.ι ⁻¹ᵁ U)) one)
        (restrictIsoUnitOfOverIsoUnit U L e).inv_hom_id⟩
  -- … that preimage is the image of a section of `F`, …
  have hq' : Function.Surjective (q.val.app (op (U.ι ''ᵁ (U.ι ⁻¹ᵁ U)))) := by
    rw [heq]; exact hq
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : Γ(F, U.ι ''ᵁ (U.ι ⁻¹ᵁ U)),
      q.val.app (op (U.ι ''ᵁ (U.ι ⁻¹ᵁ U))) m₀ = y := hq' y
  -- … and that section comes from one over `U`, the two opens being equal.
  refine ⟨F.presheaf.map (homOfLE heq.ge).op m₀, ?_⟩
  have hres : F.presheaf.map (homOfLE (U.ι.image_preimage_le U)).op
      (F.presheaf.map (homOfLE heq.ge).op m₀) = m₀ := by
    rw [← ConcreteCategory.comp_apply, ← F.presheaf.map_comp,
      show ((homOfLE heq.ge).op ≫ (homOfLE (U.ι.image_preimage_le U)).op) =
        𝟙 (op (U.ι ''ᵁ (U.ι ⁻¹ᵁ U))) from Subsingleton.elim _ _,
      F.presheaf.map_id, ConcreteCategory.id_apply]
  rw [ofPushforwardUnit_trivializedQuotientHom_app, hres, hm₀, hy]
  rfl

end Stacks.RelativeProj

end
