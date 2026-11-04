module

public import Mathlib.AlgebraicGeometry.FunctionField
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.StalkwiseRegular
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierStalk.Stalkwise
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk

/-!
# The open subscheme on which an ideal sheaf is principal

An ideal sheaf `𝓘` on a scheme `X` need not be locally principal, but the points at which it is
has an open neighbourhood on which the ideal is principal, so those points form an open
subscheme: `AlgebraicGeometry.IdealSheafData.principalOpen`, the union of the affine opens on
which the ideal of `𝓘` is principal.  A point lies in it exactly when the ideal `𝓘` induces in
the local ring there is principal, by [Stacks, Tag 0AG8].

On that open subscheme the inverse image of `𝓘` is an effective Cartier divisor, provided `X` is
integral and `𝓘` is the unit ideal at the generic point: principality is what Tag 0AG8 needs,
and the generator is a nonzerodivisor because the local rings of an integral scheme are domains
and the generator is nonzero.

This is the construction `𝒪_X(D)` needs on a merely *normal* scheme.  On a scheme with factorial
local rings the ideal sheaf `AlgebraicGeometry.positiveWeilIdeal` of the positive part of a Weil
divisor is an effective Cartier divisor on all of `X`, by
`AlgebraicGeometry.positiveWeilIdeal_isEffectiveCartierDivisor`; over a normal scheme that fails,
and the open subscheme constructed here is the largest one on which it holds.

## Main definitions

* `AlgebraicGeometry.IdealSheafData.principalOpen` — the open subscheme on which an ideal sheaf
  is principal.

## Main results

* `AlgebraicGeometry.IdealSheafData.mem_principalOpen_iff_stalk_isPrincipal` — a point lies in it
  exactly when the induced ideal of the local ring is principal.
* `AlgebraicGeometry.IdealSheafData.isEffectiveCartierDivisor_comap_of_le_principalOpen` — the
  inverse image of the ideal sheaf on an open subscheme of the principal locus is an effective
  Cartier divisor.

## References

* [Stacks Project, Tag 0AG8](https://stacks.math.columbia.edu/tag/0AG8)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.IdealSheafData

variable {X : Scheme.{u}}

/-! ### The principal locus -/

/-- **The open subscheme on which an ideal sheaf is principal**: the union of the affine opens
on which its ideal is a principal ideal. -/
def principalOpen (I : X.IdealSheafData) : X.Opens :=
  ⨆ (U : X.affineOpens) (_ : (I.ideal U).IsPrincipal), U.1

/-- An affine open on which the ideal of an ideal sheaf is principal is contained in the
principal locus. -/
theorem le_principalOpen (I : X.IdealSheafData) (U : X.affineOpens)
    (hU : (I.ideal U).IsPrincipal) : U.1 ≤ principalOpen I :=
  le_iSup_of_le U (le_iSup (fun _ : (I.ideal U).IsPrincipal => U.1) hU)

/-- At a point of the principal locus the ideal an ideal sheaf induces in the local ring is
principal: it is the image of a principal ideal under a germ map. -/
theorem stalk_isPrincipal_of_mem_principalOpen (I : X.IdealSheafData) {x : X}
    (hx : x ∈ principalOpen I) : (stalk I x).IsPrincipal := by
  obtain ⟨U, hU⟩ := Opens.mem_iSup.mp hx
  obtain ⟨hprincipal, hxU⟩ := Opens.mem_iSup.mp hU
  rw [stalk_eq_map_germ I x U hxU]
  exact hprincipal.map_ringHom _

/-- **A point at which an ideal sheaf induces a principal ideal of the local ring lies in the
principal locus**, by [Stacks, Tag 0AG8]: principality spreads from the local ring to an affine
neighbourhood. -/
theorem mem_principalOpen_of_stalk_isPrincipal [IsLocallyNoetherian X] (I : X.IdealSheafData)
    {x : X} (hx : (stalk I x).IsPrincipal) : x ∈ principalOpen I := by
  obtain ⟨U, hxU, hU⟩ :=
    Stacks.Divisors.exists_affineOpens_isPrincipal_of_stalk_isPrincipal I x hx
  exact le_principalOpen I U hU hxU

/-- **The principal locus is exactly the set of points at which the ideal sheaf induces a
principal ideal of the local ring.** -/
theorem mem_principalOpen_iff_stalk_isPrincipal [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (x : X) : x ∈ principalOpen I ↔ (stalk I x).IsPrincipal :=
  ⟨stalk_isPrincipal_of_mem_principalOpen I, mem_principalOpen_of_stalk_isPrincipal I⟩

/-! ### An effective Cartier divisor on the principal locus -/

/-- **An ideal sheaf which is the unit ideal at the generic point of an integral scheme is
nonzero in every local ring.**  Were its ideal on an affine open to vanish, it would vanish in
the local ring at the generic point too, because germ maps on an integral scheme are
injective. -/
theorem stalk_ne_bot_of_stalk_genericPoint_eq_top [IsIntegral X] (I : X.IdealSheafData)
    (hI : stalk I (genericPoint X) = ⊤) (x : X) : stalk I x ≠ ⊥ := by
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ x)
  have hηV : genericPoint X ∈ V :=
    ((genericPoint_spec X).specializes trivial).mem_open V.isOpen hxV
  intro hx
  have hbot : I.ideal ⟨V, hV⟩ = ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (germ_injective_of_isIntegral X x hxV)).mp
      ((stalk_eq_map_germ I x ⟨V, hV⟩ hxV).symm.trans hx)
  refine top_ne_bot (hI.symm.trans ?_)
  rw [stalk_eq_map_germ I (genericPoint X) ⟨V, hV⟩ hηV, hbot, Ideal.map_bot]

/-- The map of local rings induced by the inclusion of an open subscheme is injective: it is the
inverse of `AlgebraicGeometry.Scheme.Opens.stalkIso`. -/
theorem injective_stalkMap_opensι (U : X.Opens) (y : U.toScheme) :
    Function.Injective (U.ι.stalkMap y).hom := by
  rw [← U.stalkIso_inv y]
  exact (U.stalkIso y).symm.commRingCatIsoToRingEquiv.injective

/-- The map of local rings induced by the inclusion of an open subscheme carries the maximal
ideal onto the maximal ideal: it is an isomorphism of local rings. -/
theorem map_stalkMap_opensι_maximalIdeal (U : X.Opens) (y : U.toScheme) :
    Ideal.map (U.ι.stalkMap y).hom
        (IsLocalRing.maximalIdeal (X.presheaf.stalk (U.ι.base y))) =
      IsLocalRing.maximalIdeal (U.toScheme.presheaf.stalk y) := by
  rw [← U.stalkIso_inv y]
  exact IsLocalRing.map_ringEquiv_maximalIdeal
    (U.stalkIso y).symm.commRingCatIsoToRingEquiv

/-- The ideal the inverse image of an ideal sheaf induces in a local ring of an open subscheme is
the image of the ideal upstairs under the induced map of local rings. -/
theorem stalk_comap_opensι (I : X.IdealSheafData) (U : X.Opens) (y : U.toScheme) :
    stalk (I.comap U.ι) y = Ideal.map (U.ι.stalkMap y).hom (stalk I (U.ι.base y)) :=
  stalk_comap I U.ι y

/-- The ideal the inverse image of an ideal sheaf induces in a local ring of an open subscheme is
generated by the image of a generator of the ideal upstairs. -/
theorem stalk_comap_opensι_eq_span (I : X.IdealSheafData) (U : X.Opens) (y : U.toScheme)
    {c : X.presheaf.stalk (U.ι.base y)} (hc : stalk I (U.ι.base y) = Ideal.span {c}) :
    stalk (I.comap U.ι) y = Ideal.span {(U.ι.stalkMap y).hom c} := by
  rw [stalk_comap_opensι I U y, hc, Ideal.map_span, Set.image_singleton]

/-- **The inverse image of an ideal sheaf on an open subscheme induces the corresponding power of
the maximal ideal** wherever the ideal sheaf does upstairs. -/
theorem stalk_comap_opensι_eq_maximalIdeal_pow (I : X.IdealSheafData) (U : X.Opens)
    (y : U.toScheme) (n : ℕ)
    (hy : stalk I (U.ι.base y) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (U.ι.base y)) ^ n) :
    stalk (I.comap U.ι) y =
      IsLocalRing.maximalIdeal (U.toScheme.presheaf.stalk y) ^ n := by
  rw [stalk_comap_opensι I U y, hy, Ideal.map_pow, map_stalkMap_opensι_maximalIdeal]

/-- **The inverse image of an ideal sheaf on an open subscheme of its principal locus is an
effective Cartier divisor.**  Its ideal is principal in every local ring of the open subscheme,
and a generator is a nonzerodivisor: the local rings of an integral scheme are domains, and the
generator is nonzero because the ideal sheaf is the unit ideal at the generic point. -/
theorem isEffectiveCartierDivisor_comap_of_le_principalOpen [IsIntegral X]
    [IsLocallyNoetherian X] (I : X.IdealSheafData) (hI : stalk I (genericPoint X) = ⊤)
    (U : X.Opens) [IsIntegral U.toScheme] (hU : U ≤ principalOpen I) :
    Stacks.Divisors.IsEffectiveCartierDivisor (I.comap U.ι) := by
  have : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  refine isEffectiveCartierDivisor_of_stalk_regular_principal _ fun y _ => ?_
  obtain ⟨c, hc⟩ :=
    stalk_isPrincipal_of_mem_principalOpen I (x := U.ι.base y) (hU y.2)
  have hc0 : c ≠ 0 := fun h =>
    stalk_ne_bot_of_stalk_genericPoint_eq_top I hI _
      (hc.trans (Submodule.span_singleton_eq_bot.mpr h))
  refine ⟨(U.ι.stalkMap y).hom c, isRegular_iff_ne_zero.mpr fun h =>
    hc0 (injective_stalkMap_opensι U y (h.trans (map_zero _).symm)),
    stalk_comap_opensι_eq_span I U y hc⟩

end AlgebraicGeometry.IdealSheafData

end
