module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.BoundedAbove
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.BoundedAboveCohomology
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.BoundedComplex
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentLocal
public import StacksCore.Tactic.StacksAttribute

/-!
# Pseudo-coherence of a locally bounded above object from its cohomology sheaves

Let `X` be a ringed space, let `m : ℤ` and let `E` be an object of the derived category of
`𝒪_X`-modules which is locally bounded above. If the cohomology sheaf `Hⁱ(E)` is
`(m - i)`-pseudo-coherent for every `i`, then `E` is `m`-pseudo-coherent.

The hypothesis on the cohomology sheaves is phrased, as the source phrases it, as
`(m - i)`-pseudo-coherence of `Hⁱ(E)` placed in degree zero of the derived category.

## Main definitions

* `AlgebraicGeometry.RingedSpace.IsLocallyBoundedAbove`: every point has an open neighbourhood
  on which the cohomology of the object vanishes in all large enough degrees.

## Main results

* `DerivedCategory.isLE_truncGE_obj`: truncating below preserves an upper bound.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_isLE_homology`: the globally bounded
  above case.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_homology`: Stacks 09V8 itself.

## Implementation notes

The content is an induction, on one fixed ringed space and with no restriction functor involved,
over the number of degrees in which the object has cohomology above `m`. One step splits `E` into
the distinguished triangle `τ^{<d}E ⟶ E ⟶ τ^{≥d}E` of the canonical t-structure for
`d` the top such degree: the third term is concentrated in degree `d`, where it has the
cohomology of `E`, so it is `m`-pseudo-coherent by the hypothesis on `Hᵈ(E)`; the first term has
the same cohomology as `E` below `d` and none from `d` on, so the inductive hypothesis applies to
it; and Stacks 08CD part (2) assembles the two. The base case is an object whose cohomology
vanishes from `m` on, which is `m`-pseudo-coherent for the trivial reason that the zero complex
approximates it.

The passage from a global bound to a local one is
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_local_restrict`, which needs the
hypothesis on the cohomology sheaves carried to the open subspace. Restriction to an open
subspace is exact, so it commutes with the cohomology of the derived category
(`CategoryTheory.Functor.mapDerivedCategoryHomologyIso`) and with placing a module in a single
degree (`AlgebraicGeometry.RingedSpace.derivedRestrictSingleFunctorIso`); the two isomorphisms
turn the restriction of `Hⁱ(E)` into `Hⁱ(E|_U)`, and
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_derivedRestrictModules` transports the
pseudo-coherence.

The truncation fact in the `DerivedCategory` namespace below is stated for an arbitrary
abelian category rather than for `𝒪_X`-modules, because that is the generality in which it is
true and in which the rest of this library repeatedly needs it.

## References

* [Stacks Project, Tag 09V8](https://stacks.math.columbia.edu/tag/09V8)
* [Stacks Project, Tag 08CD](https://stacks.math.columbia.edu/tag/08CD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace StrictlyPerfect

universe d d' u v₁ u₁

namespace DerivedCategory

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{d} C]

/-- **Truncating below preserves an upper bound.** If the cohomology of `E` vanishes above `n`
then so does that of `τ^{≥n}E`, the two agreeing in those degrees by
`DerivedCategory.isIso_homologyFunctor_map_truncGEπ`. -/
theorem isLE_truncGE_obj (n : ℤ) (E : DerivedCategory C) [E.IsLE n] :
    ((TStructure.t.truncGE n).obj E).IsLE n := by
  rw [isLE_iff]
  intro i hi
  have : IsIso ((homologyFunctor C i).map ((TStructure.t.truncGEπ n).app E)) :=
    isIso_homologyFunctor_map_truncGEπ n i (by omega) E
  exact (isZero_of_isLE E n i hi).of_iso
    (asIso ((homologyFunctor C i).map ((TStructure.t.truncGEπ n).app E))).symm

end DerivedCategory

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u, u}} [HasDerivedCategory.{d} (OXMod.{u, u} X)]

/-! ### The globally bounded above case -/

/-- The truncation `τ^{≥d}E` of an object bounded above by `d` is `m`-pseudo-coherent as soon as
`Hᵈ(E)` is `(m - d)`-pseudo-coherent. -/
private theorem isPseudoCoherentFrom_truncGE_obj (E : DerivedCategory (OXMod.{u, u} X))
    (d m : ℤ) [E.IsLE d]
    (h : IsPseudoCoherentFrom ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) d).obj E)) (m - d)) :
    IsPseudoCoherentFrom ((DerivedCategory.TStructure.t.truncGE d).obj E) m := by
  have : ((DerivedCategory.TStructure.t.truncGE d).obj E).IsLE d :=
    DerivedCategory.isLE_truncGE_obj d E
  have : IsIso ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) d).map
      ((DerivedCategory.TStructure.t.truncGEπ d).app E)) :=
    DerivedCategory.isIso_homologyFunctor_map_truncGEπ d d le_rfl E
  exact isPseudoCoherentFrom_of_isGE_of_isLE _ d m
    (h.ofIso ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).mapIso
      (asIso ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) d).map
        ((DerivedCategory.TStructure.t.truncGEπ d).app E)))))

/-- The induction behind `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_isLE_homology`,
with the number of degrees above `m` in which the object may have cohomology as the induction
variable. -/
private theorem isPseudoCoherentFrom_of_isLE_homology_aux (m : ℤ) :
    ∀ (n : ℕ) (E : DerivedCategory (OXMod.{u, u} X)), E.IsLE (m + n) →
      (∀ i : ℤ, m ≤ i → IsPseudoCoherentFrom
        ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj
          ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj E)) (m - i)) →
      IsPseudoCoherentFrom E m := by
  intro n
  induction n with
  | zero =>
    intro E hLE hcoh
    have hE : E.IsLE m := by simpa using hLE
    refine isPseudoCoherentFrom_obj₂_of_distinguished m _
      (DerivedCategory.TStructure.t.triangleLTGE_distinguished m E) ?_ ?_
    · change IsPseudoCoherentFrom ((DerivedCategory.TStructure.t.truncLT m).obj E) m
      have : ((DerivedCategory.TStructure.t.truncLT m).obj E).IsLE (m - 1) :=
        DerivedCategory.TStructure.t.isLE_truncLT_obj E m (m - 1) (by omega)
      exact isPseudoCoherentFrom_of_isZero_homology_ge _ m fun j hj =>
        DerivedCategory.isZero_of_isLE _ (m - 1) j (by omega)
    · exact isPseudoCoherentFrom_truncGE_obj E m m (hcoh m le_rfl)
  | succ n ih =>
    intro E hLE hcoh
    have hEb : E.IsLE (m + (n : ℤ) + 1) :=
      DerivedCategory.TStructure.t.isLE_of_le E (m + ((n + 1 : ℕ) : ℤ)) _ (by push_cast; omega)
    refine isPseudoCoherentFrom_obj₂_of_distinguished m _
      (DerivedCategory.TStructure.t.triangleLTGE_distinguished (m + (n : ℤ) + 1) E) ?_ ?_
    · change IsPseudoCoherentFrom
        ((DerivedCategory.TStructure.t.truncLT (m + (n : ℤ) + 1)).obj E) m
      have hlt :
          ((DerivedCategory.TStructure.t.truncLT (m + (n : ℤ) + 1)).obj E).IsLE (m + (n : ℤ)) :=
        DerivedCategory.TStructure.t.isLE_truncLT_obj E (m + (n : ℤ) + 1) (m + (n : ℤ))
          (by omega)
      refine ih _ hlt fun i hi => ?_
      by_cases hib : i < m + (n : ℤ) + 1
      · have := DerivedCategory.isIso_homologyFunctor_map_truncLTι (m + (n : ℤ) + 1) i hib E
        exact (hcoh i hi).ofIso ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).mapIso
          (asIso ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).map
            ((DerivedCategory.TStructure.t.truncLTι (m + (n : ℤ) + 1)).app E))).symm)
      · exact (isPseudoCoherent_of_isZero
          ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).map_isZero
            (DerivedCategory.isZero_of_isLE _ (m + (n : ℤ)) i (by omega)))).isPseudoCoherentFrom _
    · exact isPseudoCoherentFrom_truncGE_obj E (m + (n : ℤ) + 1) m (hcoh _ (by omega))

/-- **A bounded above object of `D(𝒪_X)` whose cohomology sheaves are pseudo-coherent in the
corresponding degrees is pseudo-coherent**: the globally bounded above case of Stacks 09V8.

Only the cohomology in degrees at least `m` is constrained, the lower degrees being irrelevant
to `m`-pseudo-coherence. -/
theorem isPseudoCoherentFrom_of_isLE_homology (E : DerivedCategory (OXMod.{u, u} X)) (m b : ℤ)
    (hLE : E.IsLE b)
    (hcoh : ∀ i : ℤ, m ≤ i → IsPseudoCoherentFrom
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj
        ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj E)) (m - i)) :
    IsPseudoCoherentFrom E m := by
  have hbm : m ≤ max b m := le_max_right b m
  have hbb : b ≤ max b m := le_max_left b m
  have hcast : ((max b m - m).toNat : ℤ) = max b m - m := Int.toNat_of_nonneg (by omega)
  have := hLE
  have hE : E.IsLE (m + ((max b m - m).toNat : ℤ)) :=
    DerivedCategory.TStructure.t.isLE_of_le E b _ (by rw [hcast]; omega)
  exact isPseudoCoherentFrom_of_isLE_homology_aux m ((max b m - m).toNat) E hE hcoh

/-! ### The locally bounded above case -/

variable [∀ U : Opens X.carrier,
  HasDerivedCategory.{d'} (OXMod.{u, u} (X.restrict U.isOpenEmbedding))]

/-- **An object of `D(𝒪_X)` is locally bounded above** when every point has an open
neighbourhood `U` such that the cohomology of `E|_U` vanishes in all degrees above some bound
depending on `U`.

This is the hypothesis of Stacks 09V8. It is weaker than a global bound, and it is what
`AlgebraicGeometry.RingedSpace.exists_isZero_homology_gt_derivedRestrict` produces from
`m`-pseudo-coherence, so the conclusion of Stacks 09V8 feeds back into its hypothesis. -/
abbrev IsLocallyBoundedAbove (E : DerivedCategory (OXMod.{u, u} X)) : Prop :=
  ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧ ∃ b : ℤ, ∀ j : ℤ, b < j →
    IsZero ((DerivedCategory.homologyFunctor
      (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) j).obj ((derivedRestrictModules X U).obj E))

/-- Restriction to an open subspace commutes with the cohomology of the derived category:
`Hⁱ(E|_U) ≅ Hⁱ(E)|_U`. Restriction is exact
(`AlgebraicGeometry.RingedSpace.exactFunctor_restrictModules`), which is all this needs. -/
def derivedRestrictHomologyIso (U : Opens X.carrier) (i : ℤ)
    (E : DerivedCategory (OXMod.{u, u} X)) :
    (DerivedCategory.homologyFunctor (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) i).obj
        ((derivedRestrictModules X U).obj E) ≅
      (restrictModules X U).obj
        ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj E) :=
  ((restrictModules X U).mapDerivedCategoryHomologyIso i).app E

/-- **Stacks Project, Tag 09V8.** Let `X` be a ringed space, `m : ℤ` and `E` an object of the
derived category of `𝒪_X`-modules which is locally bounded above. If the cohomology sheaf `Hⁱ(E)`
is `(m - i)`-pseudo-coherent for every `i`, then `E` is `m`-pseudo-coherent. -/
@[stacks 09V8]
theorem isPseudoCoherentFrom_of_homology (E : DerivedCategory (OXMod.{u, u} X)) (m : ℤ)
    (hbdd : IsLocallyBoundedAbove E)
    (hcoh : ∀ i : ℤ, IsPseudoCoherentFrom
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj
        ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj E)) (m - i)) :
    IsPseudoCoherentFrom E m := by
  refine isPseudoCoherentFrom_of_local_restrict E m fun x => ?_
  obtain ⟨U, hxU, b, hb⟩ := hbdd x
  refine ⟨U, hxU, isPseudoCoherentFrom_of_isLE_homology _ m b ?_ fun i _ => ?_⟩
  · rw [DerivedCategory.isLE_iff]
    exact fun j hj => hb j hj
  · exact ((isPseudoCoherentFrom_derivedRestrictModules _ (m - i) (hcoh i) U).ofIso
      (derivedRestrictSingleFunctorIso U 0 _)).ofIso
      ((DerivedCategory.singleFunctor (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) 0).mapIso
        (derivedRestrictHomologyIso U i E).symm)

end AlgebraicGeometry.RingedSpace

end
