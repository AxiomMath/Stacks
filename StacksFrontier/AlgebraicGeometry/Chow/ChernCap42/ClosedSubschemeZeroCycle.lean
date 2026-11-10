module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCap42.DivisorOfSectionCycle
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.InvertibleChernSpecialization
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.IntersectionInvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionCorrespondence
public import StacksFrontier.AlgebraicGeometry.Modules.FreeSections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Intersecting with an invertible sheaf: the cycle of the zero scheme of a section

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `L` be an invertible `𝒪_X`-module, let `i : Y ⟶ X` be a closed
subscheme and let `s` be a global section of `L|_Y`, with zero scheme `Z(s) ⊆ Y`. Assume

* `dim_δ(Y) ≤ k + 1`,
* `dim_δ(Z(s)) ≤ k`, and
* multiplication by `s` is injective on the stalk at the generic point of every irreducible
  component of `Z(s)` of `δ`-dimension `k`.

Then `c₁(L) ∩ [Y]_{k + 1} = [Z(s)]_k` in `A_k(X)`, which is
[Stacks, Tag 02SQ](https://stacks.math.columbia.edu/tag/02SQ).

The proof is the source's. Write `[Y]_{k + 1} = ∑ nᵢ [Yᵢ]` over the irreducible components `Yᵢ`
of `Y` of `δ`-dimension `k + 1`. The cap product of Stacks 02SO is computed on that presentation
by `Stacks.Chow.firstChernClassCapOfInvertible_finsum`: it is the class of the cycle whose
coefficients are `∑ nᵢ c₁(L) ∩ [Yᵢ]`. On each `Yᵢ` the restriction `sᵢ` of `s` is nonzero — were
it zero, `Yᵢ` would sit inside `Z(s)`, whose `δ`-dimension is at most `k` — so Stacks 02SK
identifies the divisor cycle of `sᵢ` with `[Z(sᵢ)]_k`, and the cycle the component rule actually
chose differs from it by the principal divisor of the ratio of the two meromorphic sections.
Finally Stacks 0EPI, `Stacks.Chow.zeroCycle_eq_sum_components`, gives
`[Z(s)]_k = ∑ nᵢ [Z(sᵢ)]_k` as cycles. The two sides therefore differ by a locally finite sum of
principal divisors on the `Yᵢ`, which is exactly a rational equivalence.

## Main definitions

* `Stacks.ChernCap42.topComponents` — the irreducible components of `Y` of `δ`-dimension
  `k + 1`, the index set of the presentation of `[Y]_{k + 1}`.
* `Stacks.ChernCap42.topComponentSubscheme` — such a component, with its reduced induced
  structure, as an integral closed subscheme of `X`.
* `Stacks.ChernCap42.principalCycleAt` — the principal divisor of a rational function on an
  integral closed subscheme of `δ`-dimension `k + 1`, graded as a `k`-cycle.

## Main results

* `Stacks.ChernCap42.firstChernClassCapOfInvertible_closedSubscheme_eq_zeroScheme` —
  **Stacks 02SQ.**
* `Stacks.ChernCap42.cycleAssociatedToClosedSubscheme_apply_eq_finsum` — the fundamental cycle of
  a closed subscheme is the weighted sum of the fundamental cycles of its top-dimensional
  components.
* `Stacks.ChernCap42.exists_restrictedSection` — the restriction of `s` to a top-dimensional
  component is a nonzero section whose zero cycle is the cycle of the scheme-theoretic
  intersection of that component with `Z(s)`.
* `Stacks.ChernCap42.exists_firstChernComponentCycleRule_coe_eq` — the cycle the component rule
  of Stacks 02SO chooses differs from the zero cycle of a nonzero section by a principal divisor.
* `Stacks.ChernCap42.cycleAssociatedToZeroScheme_apply_eq_finsum` — Stacks 0EPI transported to
  cycles on the ambient scheme `X`.

## Implementation notes

A top-dimensional component is handled through `Stacks.Chow.integralComponentAt`, the reduced
induced structure on the closure of a point, rather than through a bespoke device: the component
of `Y` through `ξ` is `integralComponentAt ξ` on `Y` and `integralComponentAt (i ξ)` on `X`, and
`Stacks.ChernCap42.exists_restrictionMorphism` produces the isomorphism between the two together
with the morphism `W ⟶ Y` presenting the component as a closed subscheme of `Y`. The
scheme-theoretic intersection of that component with `Z(s)` is the supremum of the two ideal
sheaves, and `Stacks.ChernCap42.exists_iso_comap_sup` identifies it with the inverse image of
`Z(s)` along that morphism, which is where Stacks 0B6Y
(`Stacks.Divisors.zeroScheme_pullback`) enters.

The index set of the presentation of `[Y]_{k + 1}` is chosen to be the index set that Stacks
0EPI already uses — the irreducible components of `Y` of `δ`-dimension `k + 1` — so that the two
locally finite sums are indexed by the same type and no reindexing is needed.

The correction term is a principal divisor on each component separately, not a single principal
divisor on `X`, so the rational equivalence is witnessed by the locally finite family
`Stacks.Chow.IsRationallyEquivalentToZero` asks for, with the `nᵢ`-th power of the ratio on the
`i`-th component; `Stacks.ChernCap42.principalDivisorPushforward_zpow` is what turns the
multiplicity `nᵢ` into that power.

## References

* [Stacks Project, Tag 02SQ](https://stacks.math.columbia.edu/tag/02SQ)
* [Stacks Project, Tag 0EPI](https://stacks.math.columbia.edu/tag/0EPI)
* [Stacks Project, Tag 02SK](https://stacks.math.columbia.edu/tag/02SK)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules (sectionsLinearMap sectionsLinearMap_apply)

universe u

namespace Stacks.ChernCap42

open Stacks.Chow Stacks.Divisors

variable (C : Chow.ChowSituation.{u}) {X Y : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  (i : Y ⟶ X) [IsClosedImmersion i] (k : ℤ)

/-- The irreducible components of `Y` of delta-dimension `k + 1`. -/
def topComponents : Type u :=
  {W : irreducibleComponents Y //
    deltaDimension C (i ≫ p) ⟨W.1, W.2.1, isClosed_of_mem_irreducibleComponents W.1 W.2⟩ = k + 1}

/-- The generic point of a top-dimensional component. -/
def topComponentPoint (j : topComponents C p i k) : genericPoints Y :=
  genericPoints.ofComponent j.1

/-- The relative dimension over the base of the generic point of a top-dimensional component,
computed on `Y`, is `k + 1`. -/
theorem relativeDimension_topComponentPoint (j : topComponents C p i k) :
    relativeDimension C.dimensionFunction (i ≫ p) (topComponentPoint C p i k j).1 = k + 1 := by
  rw [topComponentPoint, ← deltaDimension_eq_of_isGenericPoint C (i ≫ p)
    ⟨j.1.1, j.1.2.1, isClosed_of_mem_irreducibleComponents j.1.1 j.1.2⟩ _
    (genericPoints.isGenericPoint_ofComponent j.1)]
  exact j.2

/-- The relative dimension over the base of the image in `X` of the generic point of a
top-dimensional component is `k + 1`. -/
theorem relativeDimension_image_topComponentPoint (j : topComponents C p i k) :
    relativeDimension C.dimensionFunction p (i (topComponentPoint C p i k j).1) = k + 1 := by
  rw [← relativeDimension_comp_closedImmersion C.dimensionFunction i p]
  exact relativeDimension_topComponentPoint C p i k j

/-- The integral closed subscheme of `X` cut out by a top-dimensional component of `Y`. -/
def topComponentSubscheme (j : topComponents C p i k) : X.IdealSheafData :=
  integralComponentAt (i (topComponentPoint C p i k j).1)

/-- A top-dimensional component, read as a closed subscheme of `X`, is integral. -/
theorem isIntegral_topComponentSubscheme (j : topComponents C p i k) :
    IsIntegral (topComponentSubscheme C p i k j).subscheme :=
  isIntegral_integralComponentAt _

/-- A top-dimensional component has delta-dimension `k + 1` over the base. -/
theorem schemeDeltaDimension_topComponentSubscheme (j : topComponents C p i k) :
    schemeDeltaDimension C ((topComponentSubscheme C p i k j).subschemeι ≫ p) =
      ((k + 1 : ℤ) : EInt) := by
  rw [topComponentSubscheme, schemeDeltaDimension_integralComponentAt,
    relativeDimension_image_topComponentPoint]

/-- The generic point of a top-dimensional component, read in `X`, is the image of its generic
point in `Y`. -/
theorem genericPointOf_topComponentSubscheme (j : topComponents C p i k) :
    genericPointOf (topComponentSubscheme C p i k j) (isIntegral_topComponentSubscheme C p i k j) =
      i (topComponentPoint C p i k j).1 :=
  genericPointOf_integralComponentAt _

/-- The support in `X` of a top-dimensional component is the image of that component of `Y`. -/
theorem coe_support_topComponentSubscheme (j : topComponents C p i k) :
    ((topComponentSubscheme C p i k j).support : Set X) = i '' (j.1.1 : Set Y) := by
  rw [topComponentSubscheme, coe_support_integralComponentAt, ← Set.image_singleton,
    i.isClosedEmbedding.closure_image_eq]
  exact congrArg (fun S : Set Y => i '' S) (genericPoints.isGenericPoint_ofComponent j.1)

/-- The top-dimensional components form a locally finite family of closed subsets of `X`: the
images of the irreducible components of a closed subscheme of a locally Noetherian scheme are
locally finite. -/
theorem locallyFinite_topComponentSubscheme :
    LocallyFinite fun j : topComponents C p i k =>
      ((topComponentSubscheme C p i k j).support : Set X) := by
  have _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have hinj : Function.Injective fun j : topComponents C p i k => j.1 :=
    fun _ _ h => Subtype.ext h
  have h := (locallyFinite_irreducibleComponents_image i).comp_injective hinj
  refine h.subset fun j => ?_
  rw [coe_support_topComponentSubscheme]
  exact subset_rfl

/-! ### Stage 2 -/

/-- The fundamental cycle of a top-dimensional component has coefficient one at its generic
point. -/
theorem cycleAssociatedToClosedSubscheme_topComponentSubscheme_self (j : topComponents C p i k) :
    (cycleAssociatedToClosedSubscheme C p (topComponentSubscheme C p i k j).subschemeι
        (k + 1)).1 (i (topComponentPoint C p i k j).1) = 1 := by
  rw [← genericPointOf_topComponentSubscheme C p i k j]
  exact cycleAssociatedToClosedSubscheme_integral_apply C p _
    (isIntegral_topComponentSubscheme C p i k j)
    (schemeDeltaDimension_topComponentSubscheme C p i k j)

/-- The fundamental cycle of a top-dimensional component vanishes away from its generic point. -/
theorem cycleAssociatedToClosedSubscheme_topComponentSubscheme_of_ne
    (j : topComponents C p i k) {x : X} (hx : x ≠ i (topComponentPoint C p i k j).1) :
    (cycleAssociatedToClosedSubscheme C p (topComponentSubscheme C p i k j).subschemeι
        (k + 1)).1 x = 0 :=
  cycleAssociatedToClosedSubscheme_integral_apply_of_ne C p _
    (isIntegral_topComponentSubscheme C p i k j) (k + 1)
    (by rwa [genericPointOf_topComponentSubscheme C p i k j])

/-- The top-dimensional component of `Y` through a generic point of relative dimension
`k + 1`. -/
def topComponentOfPoint (ξ : genericPoints Y)
    (hξ : relativeDimension C.dimensionFunction p (i ξ.1) = k + 1) : topComponents C p i k :=
  ⟨genericPoints.component ξ, by
    rw [deltaDimension_eq_of_isGenericPoint C (i ≫ p) _ ξ.1 (genericPoints.isGenericPoint ξ),
      relativeDimension_comp_closedImmersion C.dimensionFunction i p]
    exact hξ⟩

/-- The generic point of the component through a generic point is that point. -/
theorem topComponentPoint_topComponentOfPoint (ξ : genericPoints Y)
    (hξ : relativeDimension C.dimensionFunction p (i ξ.1) = k + 1) :
    topComponentPoint C p i k (topComponentOfPoint C p i k ξ hξ) = ξ :=
  genericPoints.ofComponent_component ξ

/-- Two top-dimensional components whose generic points have the same image in `X` are equal. -/
theorem topComponents_eq_of_point_eq {j j' : topComponents C p i k}
    (h : i (topComponentPoint C p i k j).1 = i (topComponentPoint C p i k j').1) : j = j' := by
  refine Subtype.ext ?_
  calc j.1 = genericPoints.component (topComponentPoint C p i k j) :=
        (genericPoints.component_ofComponent j.1).symm
    _ = genericPoints.component (topComponentPoint C p i k j') :=
        congrArg genericPoints.component (Subtype.ext (i.isClosedEmbedding.injective h))
    _ = j'.1 := genericPoints.component_ofComponent j'.1

/-- **The fundamental cycle of a closed subscheme is the weighted sum of the fundamental cycles
of its top-dimensional components.** -/
theorem cycleAssociatedToClosedSubscheme_apply_eq_finsum (x : X) :
    (cycleAssociatedToClosedSubscheme C p i (k + 1)).1 x =
      ∑ᶠ j : topComponents C p i k,
        componentMultiplicity i (topComponentPoint C p i k j) *
          (cycleAssociatedToClosedSubscheme C p
            (topComponentSubscheme C p i k j).subschemeι (k + 1)).1 x := by
  by_cases hx : ∃ ξ : genericPoints Y,
      i ξ.1 = x ∧ relativeDimension C.dimensionFunction p x = k + 1
  · obtain ⟨ξ, hξx, hdim⟩ := hx
    have hξ : relativeDimension C.dimensionFunction p (i ξ.1) = k + 1 := by rwa [hξx]
    have hpt : topComponentPoint C p i k (topComponentOfPoint C p i k ξ hξ) = ξ :=
      topComponentPoint_topComponentOfPoint C p i k ξ hξ
    rw [← hξx, cycleAssociatedToClosedSubscheme_apply C p i (k + 1) ξ hξ,
      finsum_eq_single _ (topComponentOfPoint C p i k ξ hξ) ?_]
    · have hself := cycleAssociatedToClosedSubscheme_topComponentSubscheme_self C p i k
        (topComponentOfPoint C p i k ξ hξ)
      rw [hpt] at hself
      rw [hself, hpt, mul_one]
    · intro j hj
      refine mul_eq_zero_of_right _
        (cycleAssociatedToClosedSubscheme_topComponentSubscheme_of_ne C p i k j fun heq => ?_)
      exact hj (topComponents_eq_of_point_eq C p i k
        (show i (topComponentPoint C p i k j).1 =
          i (topComponentPoint C p i k (topComponentOfPoint C p i k ξ hξ)).1 by
          rw [hpt]; exact heq.symm))
  · rw [cycleAssociatedToClosedSubscheme_apply_eq_zero C p i (k + 1) x hx]
    refine (finsum_eq_zero_of_forall_eq_zero fun j => ?_).symm
    rw [cycleAssociatedToClosedSubscheme_topComponentSubscheme_of_ne C p i k j
      (fun heq => hx ⟨topComponentPoint C p i k j, heq.symm, by
        rw [heq]; exact relativeDimension_image_topComponentPoint C p i k j⟩), mul_zero]

/-! ### Stage 3: the component as a closed subscheme of `Y` -/

section Lift

variable {Z : Scheme.{u}}

/-- The integral closed subscheme of `X` through the image of a point of a closed subscheme `Y`
is the image of the integral closed subscheme of `Y` through that point. -/
theorem integralComponentAt_comp (y : Y) :
    integralComponentAt (i y) = (integralComponentAt y).map i := by
  rw [integralComponentAt, integralComponentAt, Scheme.IdealSheafData.map_vanishingIdeal]
  refine congrArg Scheme.IdealSheafData.vanishingIdeal (Closeds.ext ?_)
  change closure ({i y} : Set X) = closure (i '' closure ({y} : Set Y))
  rw [← Set.image_singleton, i.isClosedEmbedding.closure_image_eq]
  exact ((i.isClosedEmbedding.isClosedMap _ isClosed_closure).closure_eq).symm

/-- The integral closed subscheme of `Y` through a point and the integral closed subscheme of
`X` through its image are isomorphic over `X`. -/
theorem exists_iso_integralComponentAt (y : Y) :
    ∃ e : (integralComponentAt y).subscheme ≅ (integralComponentAt (i y)).subscheme,
      e.hom ≫ (integralComponentAt (i y)).subschemeι =
        (integralComponentAt y).subschemeι ≫ i := by
  have hker : Scheme.Hom.ker (integralComponentAt (i y)).subschemeι =
      Scheme.Hom.ker ((integralComponentAt y).subschemeι ≫ i) := by
    rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι,
      Scheme.IdealSheafData.ker_subschemeι, ← integralComponentAt_comp]
  have he := IsClosedImmersion.lift_fac _ _ hker.le
  have := IsClosedImmersion.isIso_of_ker_eq _ _ _ he hker.symm
  exact ⟨asIso (IsClosedImmersion.lift _ _ hker.le), he⟩

/-- The integral closed subscheme of `X` through the image of a point of `Y` is presented, as a
closed subscheme of `Y`, by the integral closed subscheme of `Y` through that point. -/
theorem exists_restrictionMorphism (y : Y) :
    ∃ g : (integralComponentAt (i y)).subscheme ⟶ Y, IsClosedImmersion g ∧
      g ≫ i = (integralComponentAt (i y)).subschemeι ∧
      ∃ e : (integralComponentAt y).subscheme ≅ (integralComponentAt (i y)).subscheme,
        e.inv ≫ (integralComponentAt y).subschemeι = g := by
  obtain ⟨e, he⟩ := exists_iso_integralComponentAt i y
  refine ⟨e.inv ≫ (integralComponentAt y).subschemeι, inferInstance, ?_, e, rfl⟩
  rw [Category.assoc, ← he, Iso.inv_hom_id_assoc]

/-- **The scheme-theoretic intersection as an inverse image.** Let `T`, `D` be closed subschemes
of `Y` and let `g : Z ⟶ Y` present `T`. Then the inverse image of `D` along `g` is the
scheme-theoretic intersection `T ⊔ D`, compatibly with the immersions into `Y`. -/
@[ega "I 4.4.3" "special case"]
theorem exists_iso_comap_sup (T D : Y.IdealSheafData) (g : Z ⟶ Y) [IsClosedImmersion g]
    (e : T.subscheme ≅ Z) (he : e.inv ≫ T.subschemeι = g) :
    ∃ e' : (D.comap g).subscheme ≅ (T ⊔ D).subscheme,
      e'.hom ≫ (T ⊔ D).subschemeι = (D.comap g).subschemeι ≫ g := by
  set K : Y.IdealSheafData := T ⊔ D with hK
  set F : Z.IdealSheafData := D.comap g with hF
  let aT : K.subscheme ⟶ T.subscheme :=
    IsClosedImmersion.lift T.subschemeι K.subschemeι (by
      rw [T.ker_subschemeι, K.ker_subschemeι, hK]; exact le_sup_left)
  have haT : aT ≫ T.subschemeι = K.subschemeι := IsClosedImmersion.lift_fac _ _ _
  let aD : K.subscheme ⟶ D.subscheme :=
    IsClosedImmersion.lift D.subschemeι K.subschemeι (by
      rw [D.ker_subschemeι, K.ker_subschemeι, hK]; exact le_sup_right)
  have haD : aD ≫ D.subschemeι = K.subschemeι := IsClosedImmersion.lift_fac _ _ _
  let aV : K.subscheme ⟶ Z := aT ≫ e.hom
  have haV : aV ≫ g = K.subschemeι := by
    change (aT ≫ e.hom) ≫ g = K.subschemeι
    rw [Category.assoc, ← he, Iso.hom_inv_id_assoc, haT]
  let a : K.subscheme ⟶ F.subscheme :=
    Limits.pullback.lift aV aD (by rw [haV, haD]) ≫ (D.comapIso g).inv
  have haa : a ≫ F.subschemeι = aV := by
    change (Limits.pullback.lift aV aD _ ≫ (D.comapIso g).inv) ≫ F.subschemeι = aV
    rw [Category.assoc, Scheme.IdealSheafData.comapIso_inv_subschemeι, Limits.pullback.lift_fst]
  have hTle : T ≤ Scheme.Hom.ker (F.subschemeι ≫ g) := by
    calc T = Scheme.Hom.ker T.subschemeι := T.ker_subschemeι.symm
      _ ≤ Scheme.Hom.ker (F.subschemeι ≫ e.inv ≫ T.subschemeι) := by
          simpa only [Category.assoc] using
            (F.subschemeι ≫ e.inv).le_ker_comp T.subschemeι
      _ = Scheme.Hom.ker (F.subschemeι ≫ g) := by rw [he]
  have hDle : D ≤ Scheme.Hom.ker (F.subschemeι ≫ g) := by
    rw [← D.ker_subschemeι]
    have hfactor : F.subschemeι ≫ g =
        (D.comapIso g).hom ≫ Limits.pullback.snd g D.subschemeι ≫ D.subschemeι := by
      calc F.subschemeι ≫ g
            = F.subschemeMap D g (D.le_map_comap g) ≫ D.subschemeι :=
              (Scheme.IdealSheafData.subschemeMap_subschemeι F D g (D.le_map_comap g)).symm
        _ = ((D.comapIso g).hom ≫ Limits.pullback.snd g D.subschemeι) ≫ D.subschemeι := by
              rw [Scheme.IdealSheafData.comapIso_hom_snd]
        _ = _ := by rw [Category.assoc]
    rw [hfactor]
    exact ((D.comapIso g).hom ≫ Limits.pullback.snd g D.subschemeι).le_ker_comp D.subschemeι
  let b : F.subscheme ⟶ K.subscheme :=
    IsClosedImmersion.lift K.subschemeι (F.subschemeι ≫ g) (by
      rw [K.ker_subschemeι, hK]; exact sup_le hTle hDle)
  have hb : b ≫ K.subschemeι = F.subschemeι ≫ g := IsClosedImmersion.lift_fac _ _ _
  refine ⟨⟨b, a, ?_, ?_⟩, hb⟩
  · refine (cancel_mono F.subschemeι).1 ?_
    rw [Category.assoc, haa, Category.id_comp]
    refine (cancel_mono g).1 ?_
    rw [Category.assoc, haV, hb]
  · refine (cancel_mono K.subschemeι).1 ?_
    rw [Category.assoc, hb, ← Category.assoc, haa, haV, Category.id_comp]

end Lift

/-! ### Stage 4: restricting the section to a component -/

section Restriction

variable (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

omit [IsClosedImmersion i] in
/-- **The zero scheme of a restricted section is the inverse image of the zero scheme.** Let `s`
be a global section of `L|_Y` and let `g : W ⟶ Y` present a closed subscheme `W ⊆ X` as a closed
subscheme of `Y`. Then `s` restricts to a global section `t` of `L|_W`, nonzero whenever its
pullback along `g` is, whose zero scheme is the inverse image along `g` of the zero scheme
of `s`. -/
theorem exists_pullbackSection (s : Γ((Scheme.Modules.pullback i).obj L, ⊤))
    (W : X.IdealSheafData) (g : W.subscheme ⟶ Y) [IsClosedImmersion g]
    (hgi : g ≫ i = W.subschemeι) :
    ∃ t : Γ((Scheme.Modules.pullback W.subschemeι).obj L, ⊤),
      ((ConcreteCategory.hom (AlgebraicGeometry.pullbackGlobalSections g
          ((Scheme.Modules.pullback i).obj L))) s ≠ 0 → t ≠ 0) ∧
      Stacks.Divisors.zeroScheme W.subscheme
          ((Scheme.Modules.pullback W.subschemeι).obj L) t =
        (Stacks.Divisors.zeroScheme Y ((Scheme.Modules.pullback i).obj L) s).comap g := by
  have _ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property
      ((Scheme.Modules.pullback i).obj L) := isInvertible_sheafObj_modulePullback L i
  have _ : AlgebraicGeometry.SheafOfModules.IsInvertible W.subscheme.sheaf.obj
      W.subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback i).obj L)) :=
    isInvertible_sheafObj_modulePullback ((Scheme.Modules.pullback i).obj L) g
  have _ : AlgebraicGeometry.SheafOfModules.IsInvertible W.subscheme.sheaf.obj
      W.subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback i ⋙ Scheme.Modules.pullback g).obj L) :=
    isInvertible_sheafObj_modulePullback ((Scheme.Modules.pullback i).obj L) g
  have _ : AlgebraicGeometry.SheafOfModules.IsInvertible W.subscheme.sheaf.obj
      W.subscheme.ringCatSheaf.property ((Scheme.Modules.pullback (g ≫ i)).obj L) :=
    isInvertible_sheafObj_modulePullback L (g ≫ i)
  have _ : AlgebraicGeometry.SheafOfModules.IsInvertible W.subscheme.sheaf.obj
      W.subscheme.ringCatSheaf.property ((Scheme.Modules.pullback W.subschemeι).obj L) :=
    isInvertible_sheafObj_modulePullback L W.subschemeι
  refine ⟨Scheme.Modules.Hom.app ((Scheme.Modules.pullbackCongr hgi).app L).hom ⊤
    (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp g i).app L).hom ⊤
      ((ConcreteCategory.hom (AlgebraicGeometry.pullbackGlobalSections g
        ((Scheme.Modules.pullback i).obj L))) s)), ?_, ?_⟩
  · intro h0 hcontra
    refine h0 ?_
    have h1 := Scheme.Modules.app_inv_app ((Scheme.Modules.pullbackComp g i).app L) ⊤
      ((ConcreteCategory.hom (AlgebraicGeometry.pullbackGlobalSections g
        ((Scheme.Modules.pullback i).obj L))) s)
    have h2 := Scheme.Modules.app_inv_app ((Scheme.Modules.pullbackCongr hgi).app L) ⊤
      (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp g i).app L).hom ⊤
        ((ConcreteCategory.hom (AlgebraicGeometry.pullbackGlobalSections g
          ((Scheme.Modules.pullback i).obj L))) s))
    rw [hcontra] at h2
    rw [← h1, ← h2, ← sectionsLinearMap_apply,
      ← sectionsLinearMap_apply, map_zero, map_zero]
  · refine Eq.trans ?_ (Stacks.Divisors.zeroScheme_pullback g
      ((Scheme.Modules.pullback i).obj L) s)
    exact (AlgebraicGeometry.zeroScheme_eq_of_iso
        ((Scheme.Modules.pullbackCongr hgi).app L) rfl).symm.trans
      (AlgebraicGeometry.zeroScheme_eq_of_iso
        ((Scheme.Modules.pullbackComp g i).app L) rfl).symm

/-- The top-dimensional component, presented as a closed subscheme of `Y`. -/
theorem exists_topComponentMorphism (j : topComponents C p i k) :
    ∃ g : (topComponentSubscheme C p i k j).subscheme ⟶ Y, IsClosedImmersion g ∧
      g ≫ i = (topComponentSubscheme C p i k j).subschemeι ∧
      ∃ e : (integralComponentAt (topComponentPoint C p i k j).1).subscheme ≅
          (topComponentSubscheme C p i k j).subscheme,
        e.inv ≫ (integralComponentAt (topComponentPoint C p i k j).1).subschemeι = g :=
  exists_restrictionMorphism i (topComponentPoint C p i k j).1

/-- **A section vanishing on a top-dimensional component would raise the dimension of its zero
scheme.** If the zero scheme of `s` has delta-dimension at most `k`, the restriction of `s` to a
component of delta-dimension `k + 1` is nonzero. -/
theorem pullbackSection_topComponent_ne_zero (j : topComponents C p i k)
    (s : Γ((Scheme.Modules.pullback i).obj L, ⊤))
    (hD : schemeDeltaDimension C
      ((Stacks.Divisors.zeroScheme Y ((Scheme.Modules.pullback i).obj L) s).subschemeι ≫
        (i ≫ p)) ≤ (k : EInt))
    (g : (topComponentSubscheme C p i k j).subscheme ⟶ Y) [IsClosedImmersion g]
    (hgi : g ≫ i = (topComponentSubscheme C p i k j).subschemeι) :
    (ConcreteCategory.hom (AlgebraicGeometry.pullbackGlobalSections g
      ((Scheme.Modules.pullback i).obj L))) s ≠ 0 := by
  have _ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property
      ((Scheme.Modules.pullback i).obj L) := isInvertible_sheafObj_modulePullback L i
  have _ : IsIntegral (topComponentSubscheme C p i k j).subscheme :=
    isIntegral_topComponentSubscheme C p i k j
  intro h0
  obtain ⟨q, hq⟩ := (Stacks.Divisors.pullbackSection_eq_zero_iff_factorsThrough_zeroScheme Y
    ((Scheme.Modules.pullback i).obj L) s g).mp h0
  set z := genericPoint (topComponentSubscheme C p i k j).subscheme with hz
  have himg : i (g z) = i (topComponentPoint C p i k j).1 := by
    change (g ≫ i) z = _
    rw [hgi]
    exact genericPointOf_topComponentSubscheme C p i k j
  have hgz : g z = (topComponentPoint C p i k j).1 := i.isClosedEmbedding.injective himg
  have hpt : (Stacks.Divisors.zeroScheme Y ((Scheme.Modules.pullback i).obj L) s).subschemeι
      (q z) = (topComponentPoint C p i k j).1 := by
    rw [← hgz]
    exact congrArg (fun f : (topComponentSubscheme C p i k j).subscheme ⟶ Y => f z) hq
  have hle := relativeDimension_le_of_schemeDeltaDimension_le C (i ≫ p)
    (Stacks.Divisors.zeroScheme Y ((Scheme.Modules.pullback i).obj L) s).subschemeι hD (q z)
  rw [hpt, relativeDimension_topComponentPoint C p i k j] at hle
  omega

/-- **The zero cycle of the restricted section.** Under the hypotheses of Stacks 02SQ the
restriction of `s` to a top-dimensional component `W` of `Y` is a nonzero global section of
`L|_W` whose zero cycle, read on `X`, is the cycle of the scheme-theoretic intersection of `W`
with the zero scheme of `s`. -/
theorem exists_restrictedSection (j : topComponents C p i k)
    (s : Γ((Scheme.Modules.pullback i).obj L, ⊤))
    (hD : schemeDeltaDimension C
      ((Stacks.Divisors.zeroScheme Y ((Scheme.Modules.pullback i).obj L) s).subschemeι ≫
        (i ≫ p)) ≤ (k : EInt)) :
    ∃ t : Γ((Scheme.Modules.pullback (topComponentSubscheme C p i k j).subschemeι).obj L, ⊤),
      t ≠ 0 ∧
      cycleAssociatedToClosedSubscheme C p
          ((Stacks.Divisors.zeroScheme (topComponentSubscheme C p i k j).subscheme
            ((Scheme.Modules.pullback
              (topComponentSubscheme C p i k j).subschemeι).obj L) t).subschemeι ≫
            (topComponentSubscheme C p i k j).subschemeι) k =
        cycleAssociatedToClosedSubscheme C p
          ((integralComponentAt (topComponentPoint C p i k j).1 ⊔
            Stacks.Divisors.zeroScheme Y ((Scheme.Modules.pullback i).obj L) s).subschemeι ≫ i)
          k := by
  obtain ⟨g, hgci, hgi, e, he⟩ := exists_topComponentMorphism C p i k j
  have _ : IsClosedImmersion g := hgci
  obtain ⟨t, ht0, hzero⟩ := exists_pullbackSection i L s
    (topComponentSubscheme C p i k j) g hgi
  obtain ⟨e', he'⟩ := exists_iso_comap_sup (integralComponentAt (topComponentPoint C p i k j).1)
    (Stacks.Divisors.zeroScheme Y ((Scheme.Modules.pullback i).obj L) s) g e he
  refine ⟨t, ht0 (pullbackSection_topComponent_ne_zero C p i k L j s hD g hgi), ?_⟩
  rw [hzero]
  refine cycleAssociatedToClosedSubscheme_eq_of_iso C p _ _ e' ?_ k
  rw [← Category.assoc, he', Category.assoc, hgi]

end Restriction

/-! ### Stage 5: the component rule against the zero cycle -/

section ComponentRule

variable (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- **Stacks 02SK at a fixed grading.** On an integral scheme of delta-dimension `k + 1` the
divisor cycle of the meromorphic image of a nonzero global section `t` of an invertible module
is the cycle of the zero scheme of `t`. -/
theorem chernComponentCycle_coe_eq_cycleAssociatedToZeroScheme {V : Scheme.{u}} (q : V ⟶ C.S)
    [LocallyOfFiniteType q] [IsIntegral V] (N : V.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj V.ringCatSheaf.property N]
    [IsLocallyNoetherian V]
    (hq : schemeDeltaDimension C q = ((k + 1 : ℤ) : EInt)) (t : Γ(N, ⊤)) (ht : t ≠ 0)
    (hL : ∀ x : V, Stacks.Divisors.IsTrivializedNear N x) :
    Stacks.Chow.weilDivisorAlgebraicCycle (Stacks.Divisors.weilDivisorOfMeromorphicSection hL
        (Stacks.Divisors.genericValue N (meromorphicSectionOfSection N t))) =
      ((cycleAssociatedToClosedSubscheme C q
        (Stacks.Divisors.zeroScheme V N t).subschemeι k : CycleGroup C q k) :
          AlgebraicCycle V ℤ) := by
  obtain ⟨n, hn, rfl⟩ : ∃ n : ℤ, schemeDeltaDimension C q = (n : EInt) ∧ n - 1 = k :=
    ⟨k + 1, hq, by ring⟩
  exact congrArg (fun c : CycleGroup C q (n - 1) => (c : AlgebraicCycle V ℤ))
    (divisorOfMeromorphicSectionCycle_eq_cycleAssociatedToZeroScheme C q n hn N t ht)

/-- **The component rule of Stacks 02SO against the zero cycle of a section.** On an integral
closed subscheme `W ⊆ X` of delta-dimension `k + 1`, the cycle the component rule of `L` chooses
differs from the cycle of the zero scheme of a nonzero global section `t` of `L|_W` by the
principal divisor of a nonzero rational function on `W`. -/
theorem exists_firstChernComponentCycleRule_coe_eq (W : X.IdealSheafData)
    [IsIntegral W.subscheme] [IsLocallyNoetherian W.subscheme]
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (t : Γ((Scheme.Modules.pullback W.subschemeι).obj L, ⊤)) (ht : t ≠ 0) :
    ∃ f : W.subscheme.functionField, f ≠ 0 ∧
      ((firstChernComponentCycleRule C p k L W inferInstance hDim :
            CycleGroup C (W.subschemeι ≫ p) k) : AlgebraicCycle W.subscheme ℤ) =
        ((cycleAssociatedToClosedSubscheme C (W.subschemeι ≫ p)
            (Stacks.Divisors.zeroScheme W.subscheme
              ((Scheme.Modules.pullback W.subschemeι).obj L) t).subschemeι k :
            CycleGroup C (W.subschemeι ≫ p) k) : AlgebraicCycle W.subscheme ℤ) +
          principalCycle W.subscheme f := by
  have _ : AlgebraicGeometry.SheafOfModules.IsInvertible W.subscheme.presheaf
      W.subscheme.ringCatSheaf.2 ((Scheme.Modules.pullback W.subschemeι).obj L) :=
    isInvertible_presheaf_modulePullback L W.subschemeι
  have _ : AlgebraicGeometry.SheafOfModules.IsInvertible W.subscheme.sheaf.obj
      W.subscheme.ringCatSheaf.property ((Scheme.Modules.pullback W.subschemeι).obj L) :=
    isInvertible_sheafObj_modulePullback L W.subschemeι
  have hτ : Stacks.Divisors.genericValue ((Scheme.Modules.pullback W.subschemeι).obj L)
      (meromorphicSectionOfSection _ t) ≠ 0 := by
    rw [Stacks.Divisors.genericValue_meromorphicSectionOfSection]
    exact germ_ne_zero_of_ne_zero _ t ht _
  obtain ⟨σ, hσ, hrule⟩ : ∃ σ : ((Scheme.Modules.pullback W.subschemeι).obj L).presheaf.stalk
        (genericPoint W.subscheme), σ ≠ 0 ∧
      ((firstChernComponentCycleRule C p k L W inferInstance hDim :
            CycleGroup C (W.subschemeι ≫ p) k) : AlgebraicCycle W.subscheme ℤ) =
        Stacks.Chow.weilDivisorAlgebraicCycle (Stacks.Divisors.weilDivisorOfMeromorphicSection
          (Stacks.Divisors.isTrivializedNear_of_isInvertible
            ((Scheme.Modules.pullback W.subschemeι).obj L)) σ) :=
    ⟨_, (Stacks.Divisors.exists_ne_zero_genericStalk
      (Stacks.Divisors.isTrivializedNear_of_isInvertible
        ((Scheme.Modules.pullback W.subschemeι).obj L) (genericPoint W.subscheme))).choose_spec,
      rfl⟩
  obtain ⟨f, hsf, -⟩ := Stacks.Divisors.existsUnique_smul_eq (s := σ)
    (Stacks.Divisors.isTrivializedNear_of_isInvertible
      ((Scheme.Modules.pullback W.subschemeι).obj L) (genericPoint W.subscheme)) hτ
  have hf : f ≠ 0 := fun h => hσ (by rw [hsf, h]; exact zero_smul _ _)
  refine ⟨f, hf, ?_⟩
  rw [hrule, Stacks.Chow.weilDivisorAlgebraicCycle_meromorphic_eq_add _ hτ hf hsf,
    chernComponentCycle_coe_eq_cycleAssociatedToZeroScheme C k (W.subschemeι ≫ p)
      ((Scheme.Modules.pullback W.subschemeι).obj L) hDim t ht]

end ComponentRule

/-! ### Stage 6: principal divisors of powers, and pushforward along a closed immersion -/

section Principal

/-- The order of vanishing of an integer power of a nonzero rational function is that multiple of
its order of vanishing. -/
private theorem ord_zpow {V : Scheme.{u}} [IsIntegral V] [IsLocallyNoetherian V] (x : V)
    (f : V.functionFieldˣ) (n : ℤ) :
    Scheme.ord (↑(f ^ n) : V.functionField) x = n * Scheme.ord (↑f : V.functionField) x := by
  have hone : Scheme.ord (1 : V.functionField) x = 0 := by
    have h := Scheme.ord_mul (x := x) (one_ne_zero (α := V.functionField))
      (one_ne_zero (α := V.functionField))
    rw [one_mul] at h
    omega
  have hinv : ∀ g : V.functionFieldˣ,
      Scheme.ord (↑g⁻¹ : V.functionField) x = -Scheme.ord (↑g : V.functionField) x := by
    intro g
    have h := Scheme.ord_mul (x := x) (Units.ne_zero g) (Units.ne_zero g⁻¹)
    rw [show (↑g : V.functionField) * ↑g⁻¹ = 1 from congrArg Units.val (mul_inv_cancel g),
      hone] at h
    omega
  have hpow : ∀ m : ℕ, Scheme.ord (↑(f ^ m) : V.functionField) x =
      (m : ℤ) * Scheme.ord (↑f : V.functionField) x := by
    intro m
    induction m with
    | zero => simpa using hone
    | succ m ih =>
        rw [pow_succ, show (↑(f ^ m * f) : V.functionField) = ↑(f ^ m) * ↑f from rfl,
          Scheme.ord_mul (x := x) (Units.ne_zero (f ^ m)) (Units.ne_zero f), ih]
        push_cast
        ring
  cases n with
  | ofNat m => simpa using hpow m
  | negSucc m =>
      rw [zpow_negSucc, hinv, hpow, Int.negSucc_eq]
      push_cast
      ring

/-- The principal divisor of a rational function on an integral closed subscheme of
delta-dimension `k + 1`, as a `k`-cycle on that subscheme. -/
def principalCycleAt (V : X.IdealSheafData) [IsIntegral V.subscheme]
    [IsLocallyNoetherian V.subscheme]
    (hDim : schemeDeltaDimension C (V.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (f : V.subscheme.functionField) : CycleGroup C (V.subschemeι ≫ p) k :=
  ⟨principalCycle V.subscheme f, by
    have h := principalCycle_mem_cyclesOfDimension C (V.subschemeι ≫ p) hDim f
    rwa [add_sub_cancel_right] at h⟩

/-- Proper pushforward of the principal divisor cycle along the immersion of an integral closed
subscheme is the pushforward cycle of `Stacks.Chow.principalDivisorPushforward`. -/
theorem properPushforward_principalCycleAt (V : X.IdealSheafData) [IsIntegral V.subscheme]
    [IsLocallyNoetherian V.subscheme]
    (hDim : schemeDeltaDimension C (V.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (g : (rationalFunctions V.subscheme)ˣ) :
    ((properPushforward C (V.subschemeι ≫ p) p V.subschemeι rfl k
          (principalCycleAt C p k V hDim ((rationalFunctionsEquivFunctionField V.subscheme).1
            (g : rationalFunctions V.subscheme)))).1 : AlgebraicCycle X ℤ) =
      principalDivisorPushforward C p V inferInstance g := rfl

/-- **The principal divisor of an integer power.** -/
theorem principalDivisorPushforward_zpow (V : X.IdealSheafData) [IsIntegral V.subscheme]
    [IsLocallyNoetherian V.subscheme]
    (hDim : schemeDeltaDimension C (V.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (g : (rationalFunctions V.subscheme)ˣ) (n : ℤ) (x : X) :
    principalDivisorPushforward C p V inferInstance (g ^ n) x =
      n * principalDivisorPushforward C p V inferInstance g x := by
  set e := (rationalFunctionsEquivFunctionField V.subscheme).1 with he
  set gu : V.subscheme.functionFieldˣ := Units.map e.toRingHom.toMonoidHom g with hgu
  have hval : ∀ m : ℤ, e ((g ^ m : (rationalFunctions V.subscheme)ˣ) :
      rationalFunctions V.subscheme) = ((gu ^ m : V.subscheme.functionFieldˣ) :
      V.subscheme.functionField) := by
    intro m
    rw [hgu, ← map_zpow (Units.map e.toRingHom.toMonoidHom) g m]
    rfl
  rw [← properPushforward_principalCycleAt C p k V hDim, ←
    properPushforward_principalCycleAt C p k V hDim]
  change (properPushforward C (V.subschemeι ≫ p) p V.subschemeι rfl k
      (principalCycleAt C p k V hDim (e _))).1 x = _
  have hz : ∀ z : V.subscheme,
      (principalCycleAt C p k V hDim (e ((g ^ n : (rationalFunctions V.subscheme)ˣ) :
          rationalFunctions V.subscheme)) : AlgebraicCycle V.subscheme ℤ) z =
        n * (principalCycleAt C p k V hDim (e (g : rationalFunctions V.subscheme)) :
          AlgebraicCycle V.subscheme ℤ) z := by
    intro z
    change (principalCycle V.subscheme _) z = n * (principalCycle V.subscheme _) z
    rw [principalCycle_apply, principalCycle_apply, hval n]
    exact ord_zpow z gu n
  rw [properPushforward_apply, properPushforward_apply]
  refine Eq.trans (finsum_mem_congr rfl fun z _ => ?_) (mul_finsum_mem _ n).symm
  rw [hz z, mul_assoc]

end Principal

section Pushforward

/-- The coefficient of a proper pushforward along a closed immersion at a point of the image is
the coefficient upstairs. -/
theorem properPushforward_apply_image {Z : Scheme.{u}} (f : Z ⟶ C.S) [LocallyOfFiniteType f]
    (ι : Z ⟶ X) [IsClosedImmersion ι] (hι : ι ≫ p = f) (c : CycleGroup C f k) (z : Z) :
    (properPushforward C f p ι hι k c).1 (ι z) = c.1 z := by
  rw [properPushforward_apply]
  have hfib : ι.base ⁻¹' {ι.base z} = {z} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h => ι.isClosedEmbedding.injective h, fun h => congrArg ι.base h⟩
  rw [hfib, finsum_mem_singleton]
  have hdim : relativeDimension C.dimensionFunction f z =
      relativeDimension C.dimensionFunction p (ι.base z) := by
    rw [← hι, relativeDimension_comp_closedImmersion]
  simp [hdim, residueDegree_eq_one_of_isClosedImmersion]

end Pushforward

/-! ### Stage 7: Stacks 02SQ -/

section Main

variable (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property
    ((Scheme.Modules.pullback i).obj L)]

/-- The integral closed subscheme of `Y` cut out by a top-dimensional component is the reduced
induced structure on that component. -/
theorem integralComponentAt_topComponentPoint (j : topComponents C p i k) :
    integralComponentAt (topComponentPoint C p i k j).1 =
      Scheme.IdealSheafData.vanishingIdeal
        ⟨j.1.1, isClosed_of_mem_irreducibleComponents j.1.1 j.1.2⟩ :=
  congrArg Scheme.IdealSheafData.vanishingIdeal
    (Closeds.ext (genericPoints.isGenericPoint_ofComponent j.1))

/-- The multiplicity of a top-dimensional component in the fundamental cycle of `Y`, read as the
coefficient appearing in Stacks 0EPI. -/
theorem componentMultiplicity_eq_cycleAssociatedToClosedSubscheme_id
    (j : topComponents C p i k) :
    componentMultiplicity i (topComponentPoint C p i k j) =
      (cycleAssociatedToClosedSubscheme C (i ≫ p) (𝟙 Y) (k + 1)).1 j.1.2.1.genericPoint := by
  have hdim : relativeDimension C.dimensionFunction (i ≫ p)
      ((𝟙 Y : Y ⟶ Y) (topComponentPoint C p i k j).1) = k + 1 :=
    relativeDimension_topComponentPoint C p i k j
  rw [show j.1.2.1.genericPoint = (𝟙 Y : Y ⟶ Y) (topComponentPoint C p i k j).1 from rfl,
    cycleAssociatedToClosedSubscheme_apply C (i ≫ p) (𝟙 Y) (k + 1)
      (topComponentPoint C p i k j) hdim,
    componentMultiplicity_eq_length_stalk i (topComponentPoint C p i k j),
    ← componentMultiplicity_eq_length_stalk (𝟙 Y) (topComponentPoint C p i k j)]

omit [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] in
/-- **Stacks 0EPI, read on the ambient scheme.** The cycle of the zero scheme of `s`, as a cycle
on `X`, is the weighted sum over the top-dimensional components `W` of `Y` of the cycles of the
scheme-theoretic intersections of `W` with the zero scheme. -/
theorem cycleAssociatedToZeroScheme_apply_eq_finsum
    (s : ((Scheme.Modules.pullback i).obj L).sections)
    (hY : schemeDeltaDimension C (i ≫ p) ≤ (k + 1 : EInt))
    (hD : schemeDeltaDimension C
      ((Stacks.Divisors.zeroScheme Y ((Scheme.Modules.pullback i).obj L)
        (s.eval (op ⊤))).subschemeι ≫ (i ≫ p)) ≤ (k : EInt))
    (hs : ∀ ξ : genericPoints (Stacks.Divisors.zeroScheme Y
        ((Scheme.Modules.pullback i).obj L) (s.eval (op ⊤))).subscheme,
      relativeDimension C.dimensionFunction (i ≫ p)
        ((Stacks.Divisors.zeroScheme Y ((Scheme.Modules.pullback i).obj L)
          (s.eval (op ⊤))).subschemeι ξ.1) = k →
      Function.Injective (ConcreteCategory.hom
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
          ((Stacks.Divisors.zeroScheme Y ((Scheme.Modules.pullback i).obj L)
            (s.eval (op ⊤))).subschemeι ξ.1)).map
          ((Scheme.Modules.toPresheaf Y).map
            (((Scheme.Modules.pullback i).obj L).unitHomEquiv.symm s))))) (x : X) :
    (cycleAssociatedToClosedSubscheme C p
        ((Stacks.Divisors.zeroScheme Y ((Scheme.Modules.pullback i).obj L)
          (s.eval (op ⊤))).subschemeι ≫ i) k).1 x =
      ∑ᶠ j : topComponents C p i k,
        componentMultiplicity i (topComponentPoint C p i k j) *
          (cycleAssociatedToClosedSubscheme C p
            ((integralComponentAt (topComponentPoint C p i k j).1 ⊔
              Stacks.Divisors.zeroScheme Y ((Scheme.Modules.pullback i).obj L)
                (s.eval (op ⊤))).subschemeι ≫ i) k).1 x := by
  have hzero := zeroCycle_eq_sum_components C (i ≫ p) ((Scheme.Modules.pullback i).obj L) s k
    hY hD hs
  have hpush : ∀ (Z : Y.IdealSheafData) (y : Y),
      (cycleAssociatedToClosedSubscheme C p (Z.subschemeι ≫ i) k).1 (i y) =
        (cycleAssociatedToClosedSubscheme C (i ≫ p) Z.subschemeι k).1 y := fun Z y => by
    rw [← properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp C (i ≫ p)
      p i rfl Z.subschemeι k, properPushforward_apply_image C p k (i ≫ p) i rfl _ y]
  by_cases hx : x ∈ Set.range i.base
  · obtain ⟨y, rfl⟩ := hx
    rw [hpush, hzero y]
    refine finsum_congr fun j => ?_
    rw [← componentMultiplicity_eq_cycleAssociatedToClosedSubscheme_id C p i k j, hpush,
      integralComponentAt_topComponentPoint C p i k j]
  · have hzero0 : ∀ Z : Y.IdealSheafData,
        (cycleAssociatedToClosedSubscheme C p (Z.subschemeι ≫ i) k).1 x = 0 := fun Z =>
      cycleAssociatedToClosedSubscheme_apply_eq_zero_of_notMem_range C p _ k
        fun ⟨z, hz⟩ => hx ⟨Z.subschemeι z, hz⟩
    rw [hzero0]
    exact (finsum_eq_zero_of_forall_eq_zero fun j => by rw [hzero0, mul_zero]).symm

/-- **The component rule against the zero cycle, on a top-dimensional component.** -/
theorem exists_firstChernComponentCycle_apply_eq (j : topComponents C p i k)
    (s : Γ((Scheme.Modules.pullback i).obj L, ⊤))
    (hD : schemeDeltaDimension C
      ((Stacks.Divisors.zeroScheme Y ((Scheme.Modules.pullback i).obj L) s).subschemeι ≫
        (i ≫ p)) ≤ (k : EInt)) :
    ∃ g : (rationalFunctions (topComponentSubscheme C p i k j).subscheme)ˣ, ∀ x : X,
      (firstChernComponentCycle C p k (firstChernComponentCycleRule C p k L)
          (topComponentSubscheme C p i k j) (isIntegral_topComponentSubscheme C p i k j)
          (schemeDeltaDimension_topComponentSubscheme C p i k j)).1 x =
        (cycleAssociatedToClosedSubscheme C p
            ((integralComponentAt (topComponentPoint C p i k j).1 ⊔
              Stacks.Divisors.zeroScheme Y ((Scheme.Modules.pullback i).obj L) s).subschemeι ≫
              i) k).1 x +
          principalDivisorPushforward C p (topComponentSubscheme C p i k j)
            (isIntegral_topComponentSubscheme C p i k j) g x := by
  have _ : IsIntegral (topComponentSubscheme C p i k j).subscheme :=
    isIntegral_topComponentSubscheme C p i k j
  have _ : IsLocallyNoetherian (topComponentSubscheme C p i k j).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian
      ((topComponentSubscheme C p i k j).subschemeι ≫ p)
  obtain ⟨t, ht, hcyc⟩ := exists_restrictedSection C p i k L j s hD
  obtain ⟨f, hf, heq⟩ := exists_firstChernComponentCycleRule_coe_eq C p k L
    (topComponentSubscheme C p i k j) (schemeDeltaDimension_topComponentSubscheme C p i k j) t ht
  set e := (rationalFunctionsEquivFunctionField
    (topComponentSubscheme C p i k j).subscheme).1 with he
  obtain ⟨g, hef⟩ : ∃ g : (rationalFunctions (topComponentSubscheme C p i k j).subscheme)ˣ,
      e (g : rationalFunctions (topComponentSubscheme C p i k j).subscheme) = f :=
    ⟨Units.mk0 (e.symm f) (fun h => hf (by rw [← e.apply_symm_apply f, h, map_zero])),
      e.apply_symm_apply f⟩
  refine ⟨g, ?_⟩
  have hsplit : firstChernComponentCycleRule C p k L (topComponentSubscheme C p i k j)
        (isIntegral_topComponentSubscheme C p i k j)
        (schemeDeltaDimension_topComponentSubscheme C p i k j) =
      cycleAssociatedToClosedSubscheme C ((topComponentSubscheme C p i k j).subschemeι ≫ p)
          (Stacks.Divisors.zeroScheme (topComponentSubscheme C p i k j).subscheme
            ((Scheme.Modules.pullback
              (topComponentSubscheme C p i k j).subschemeι).obj L) t).subschemeι k +
        principalCycleAt C p k (topComponentSubscheme C p i k j)
          (schemeDeltaDimension_topComponentSubscheme C p i k j) f := Subtype.ext heq
  intro x
  have hpush : firstChernComponentCycle C p k (firstChernComponentCycleRule C p k L)
        (topComponentSubscheme C p i k j) (isIntegral_topComponentSubscheme C p i k j)
        (schemeDeltaDimension_topComponentSubscheme C p i k j) =
      properPushforward C ((topComponentSubscheme C p i k j).subschemeι ≫ p) p
          (topComponentSubscheme C p i k j).subschemeι rfl k
          (cycleAssociatedToClosedSubscheme C
            ((topComponentSubscheme C p i k j).subschemeι ≫ p)
            (Stacks.Divisors.zeroScheme (topComponentSubscheme C p i k j).subscheme
              ((Scheme.Modules.pullback
                (topComponentSubscheme C p i k j).subschemeι).obj L) t).subschemeι k) +
        properPushforward C ((topComponentSubscheme C p i k j).subschemeι ≫ p) p
          (topComponentSubscheme C p i k j).subschemeι rfl k
          (principalCycleAt C p k (topComponentSubscheme C p i k j)
            (schemeDeltaDimension_topComponentSubscheme C p i k j) f) := by
    rw [show firstChernComponentCycle C p k (firstChernComponentCycleRule C p k L)
          (topComponentSubscheme C p i k j) (isIntegral_topComponentSubscheme C p i k j)
          (schemeDeltaDimension_topComponentSubscheme C p i k j) =
        properPushforward C ((topComponentSubscheme C p i k j).subschemeι ≫ p) p
          (topComponentSubscheme C p i k j).subschemeι rfl k
          (firstChernComponentCycleRule C p k L (topComponentSubscheme C p i k j)
            (isIntegral_topComponentSubscheme C p i k j)
            (schemeDeltaDimension_topComponentSubscheme C p i k j)) from rfl,
      hsplit, properPushforward_add]
  rw [properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp C
      ((topComponentSubscheme C p i k j).subschemeι ≫ p) p
      (topComponentSubscheme C p i k j).subschemeι rfl _ k, hcyc] at hpush
  rw [hpush, cycleGroup_add_apply]
  refine congrArg (fun z : ℤ => _ + z) ?_
  rw [← hef]
  exact congrFun (congrArg (fun c : AlgebraicCycle X ℤ => (c : X → ℤ))
    (properPushforward_principalCycleAt C p k (topComponentSubscheme C p i k j)
      (schemeDeltaDimension_topComponentSubscheme C p i k j) _)) x

/-- The coefficients of a difference of cycles are the differences of the coefficients. -/
private theorem cycleGroup_sub_apply {Z : Scheme.{u}} (f : Z ⟶ C.S) [LocallyOfFiniteType f]
    (a b : CycleGroup C f k) (z : Z) : (a - b).1 z = a.1 z - b.1 z := rfl

/-- A family of integers indexed by a locally finite family of sets, each member vanishing when
the point misses its set, has finite support at that point. -/
private theorem finite_support_of_vanishing {J : Type u} (E : J → Set X) (hE : LocallyFinite E)
    (c : J → ℤ) (x : X) (hc : ∀ j, x ∉ E j → c j = 0) : (Function.support c).Finite := by
  refine (hE.point_finite x).subset fun j hj => ?_
  by_contra h
  exact hj (hc j h)

/-- **Stacks 02SQ.** Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let
`X` be locally of finite type over `S`, let `L` be an invertible `𝒪_X`-module, let `Y ⊆ X` be a
closed subscheme and let `s` be a global section of `L|_Y`. Assume `dim_δ(Y) ≤ k + 1`, that
`dim_δ(Z(s)) ≤ k`, and that multiplication by `s` is injective on the local ring at the generic
point of every component of `Z(s)` of `δ`-dimension `k`. Then

`c₁(L) ∩ [Y]_{k + 1} = [Z(s)]_k`  in  `A_k(X)`.

The cycle `[Z(s)]_k` is read on `X` through the composite of the closed immersion of `Z(s)` into
`Y` with that of `Y` into `X`. -/
@[stacks 02SQ]
theorem firstChernClassCapOfInvertible_closedSubscheme_eq_zeroScheme
    (s : ((Scheme.Modules.pullback i).obj L).sections)
    (hY : schemeDeltaDimension C (i ≫ p) ≤ (k + 1 : EInt))
    (hD : schemeDeltaDimension C
      ((Stacks.Divisors.zeroScheme Y ((Scheme.Modules.pullback i).obj L)
        (s.eval (op ⊤))).subschemeι ≫ (i ≫ p)) ≤ (k : EInt))
    (hs : ∀ ξ : genericPoints (Stacks.Divisors.zeroScheme Y
        ((Scheme.Modules.pullback i).obj L) (s.eval (op ⊤))).subscheme,
      relativeDimension C.dimensionFunction (i ≫ p)
        ((Stacks.Divisors.zeroScheme Y ((Scheme.Modules.pullback i).obj L)
          (s.eval (op ⊤))).subschemeι ξ.1) = k →
      Function.Injective (ConcreteCategory.hom
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
          ((Stacks.Divisors.zeroScheme Y ((Scheme.Modules.pullback i).obj L)
            (s.eval (op ⊤))).subschemeι ξ.1)).map
          ((Scheme.Modules.toPresheaf Y).map
            (((Scheme.Modules.pullback i).obj L).unitHomEquiv.symm s))))) :
    firstChernClassCapOfInvertible C p k L (cycleAssociatedToClosedSubscheme C p i (k + 1)) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme C p
        ((Stacks.Divisors.zeroScheme Y ((Scheme.Modules.pullback i).obj L)
          (s.eval (op ⊤))).subschemeι ≫ i) k) := by
  classical
  obtain ⟨β, hcap, hβ⟩ := firstChernClassCapOfInvertible_finsum C p k L
    (topComponentSubscheme C p i k) (isIntegral_topComponentSubscheme C p i k)
    (schemeDeltaDimension_topComponentSubscheme C p i k)
    (locallyFinite_topComponentSubscheme C p i k)
    (fun j => componentMultiplicity i (topComponentPoint C p i k j))
    (cycleAssociatedToClosedSubscheme C p i (k + 1))
    (cycleAssociatedToClosedSubscheme_apply_eq_finsum C p i k)
  choose g hg using fun j : topComponents C p i k =>
    exists_firstChernComponentCycle_apply_eq C p i k L j (s.eval (op ⊤)) hD
  rw [hcap]
  refine QuotientAddGroup.eq_iff_sub_mem.mpr
    ⟨topComponents C p i k, topComponentSubscheme C p i k,
      isIntegral_topComponentSubscheme C p i k,
      schemeDeltaDimension_topComponentSubscheme C p i k,
      locallyFinite_topComponentSubscheme C p i k,
      fun j => g j ^ componentMultiplicity i (topComponentPoint C p i k j), fun x => ?_⟩
  have hcompzero : ∀ j : topComponents C p i k, x ∉ ((topComponentSubscheme C p i k j).support :
      Set X) → (firstChernComponentCycle C p k (firstChernComponentCycleRule C p k L)
        (topComponentSubscheme C p i k j) (isIntegral_topComponentSubscheme C p i k j)
        (schemeDeltaDimension_topComponentSubscheme C p i k j)).1 x = 0 := by
    intro j hj
    by_contra hne
    exact hj (support_firstChernComponentCycle_subset C p k (firstChernComponentCycleRule C p k L)
      (topComponentSubscheme C p i k j) (isIntegral_topComponentSubscheme C p i k j)
      (schemeDeltaDimension_topComponentSubscheme C p i k j) hne)
  have hprinzero : ∀ j : topComponents C p i k, x ∉ ((topComponentSubscheme C p i k j).support :
      Set X) → principalDivisorPushforward C p (topComponentSubscheme C p i k j)
        (isIntegral_topComponentSubscheme C p i k j) (g j) x = 0 := by
    intro j hj
    by_contra hne
    exact hj (support_principalDivisorPushforward_subset C p (topComponentSubscheme C p i k j)
      (isIntegral_topComponentSubscheme C p i k j) (g j) hne)
  have hzerozero : ∀ j : topComponents C p i k, x ∉ ((topComponentSubscheme C p i k j).support :
      Set X) → (cycleAssociatedToClosedSubscheme C p
        ((integralComponentAt (topComponentPoint C p i k j).1 ⊔
          Stacks.Divisors.zeroScheme Y ((Scheme.Modules.pullback i).obj L)
            (s.eval (op ⊤))).subschemeι ≫ i) k).1 x = 0 := by
    intro j hj
    have h := hg j x
    rw [hcompzero j hj, hprinzero j hj, add_zero] at h
    exact h.symm
  have hfin : ∀ c : topComponents C p i k → ℤ,
      (∀ j, x ∉ ((topComponentSubscheme C p i k j).support : Set X) → c j = 0) →
      (Function.support fun j => componentMultiplicity i (topComponentPoint C p i k j) *
        c j).Finite := fun c hc =>
    finite_support_of_vanishing _ (locallyFinite_topComponentSubscheme C p i k) _ x
      fun j hj => by rw [hc j hj, mul_zero]
  rw [cycleGroup_sub_apply, hβ,
    cycleAssociatedToZeroScheme_apply_eq_finsum C p i k L s hY hD hs x,
    ← finsum_sub_distrib (hfin _ hcompzero) (hfin _ hzerozero)]
  change _ = ∑ᶠ j : topComponents C p i k, principalDivisorPushforward C p
    (topComponentSubscheme C p i k j) (isIntegral_topComponentSubscheme C p i k j)
    (g j ^ componentMultiplicity i (topComponentPoint C p i k j)) x
  refine finsum_congr fun j => ?_
  have _ : IsIntegral (topComponentSubscheme C p i k j).subscheme :=
    isIntegral_topComponentSubscheme C p i k j
  have _ : IsLocallyNoetherian (topComponentSubscheme C p i k j).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian
      ((topComponentSubscheme C p i k j).subschemeι ≫ p)
  rw [principalDivisorPushforward_zpow C p k (topComponentSubscheme C p i k j)
      (schemeDeltaDimension_topComponentSubscheme C p i k j) (g j) _ x, hg j x]
  ring

end Main

end Stacks.ChernCap42

end
