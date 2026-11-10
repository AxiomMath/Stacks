module

public import StacksFrontier.AlgebraicGeometry.Intersection.RationalEquivalence.SectionLocalIdentity
public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToDiagonal.TorFormulaWhole
public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToDiagonal.TorFormulaBaseCase
public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToDiagonal.Whole
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.FibreCycleClosedPointPair
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.TripleProductCycleAssociativity
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.CoherentComponentDecomposition
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbolComparison.Arrows
public import StacksFrontier.RingTheory.Length.SemilinearTransfer
public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToDiagonal.SubvarietyProductAssociativity
public import StacksFrontier.AlgebraicGeometry.Intersection.ExteriorProductIntersection
public import StacksFrontier.AlgebraicGeometry.Curves.NodeStalkCharacterization
import StacksCore.Tactic.StacksAttribute

/-!
# Tag 0B60: the intersection product with the fibres of a family over `ℙ¹`

Let `X` be a nonsingular variety over an algebraically closed field, let `W ⊆ X × ℙ¹` be a closed
subvariety of dimension `s + 1` dominating `ℙ¹`, let `W_a`, `W_b` be its fibres over closed points
`a`, `b` of `ℙ¹`, and let `V ⊆ X` be a closed subvariety of dimension `r` meeting both fibres
properly. Then `[V] · [W_a]_s ∼_rat [V] · [W_b]_s`. This is Tag 0B60,
`Stacks.Intersection.RationalEquivalence.rationallyEquivalent_intersectionProduct_fibreCycle`.

## The proof

Write `n = r + s - dim X`. The source replaces the intersection product of `V × ℙ¹` and `W`, whose
components need not have the expected dimension, by the cycle `γ = ∑_Z e_Z [Z]` over the
components `Z` of `(V × ℙ¹) ∩ W` of dimension `n + 1` meeting neither fibre in a component of its
own, with `e_Z = ∑ⱼ (-1)ʲ length Torⱼ(𝒪_{V × ℙ¹}, 𝒪_W)_Z`, and shows

`[V] · [W_c]_s = pr_*(γ · X × c) = ∑_Z e_Z [Z_c]_n`  (`c = a, b`),

after which the two right-hand sides differ by a cycle rationally equivalent to zero, one integral
`Z` at a time (part (2) of Tag 0B07). The identity is proved here coefficient by coefficient. At a
point `x` of `V ∩ W_c` of dimension `n`, Tag 0B0W turns the left-hand coefficient into the
alternating sum of the lengths of `Torᵢ^{𝒪_{X,x}}(𝒪_{V,x}, 𝒪_{W_c,x})`; the flat local homomorphism
`𝒪_{X,x} → 𝒪_{X × ℙ¹, σ x}` and its retraction move it to the local ring at `σ x`, where the local
form of the associativity of Tag 0B1L and the length formula of Tag 02QF produce the sum over the
components `Z` through `σ x` of `e_Z` times the colength of `(t) + 𝔭_Z`, `t` a local equation of
`X × c`; that colength is the coefficient of `[Z_c]_n` at `x`. The components through `σ x` are
read off the primes of the local ring with `Scheme.fromSpecStalk`.

The source's argument restricts to the open complement in `X × ℙ¹` of the fibres containing the
components of `(V × ℙ¹) ∩ W` of excess dimension and invokes the projection formula of Tag 0B10
there; working one point of `X × c` at a time needs neither, since such components do not pass
through `X × c`.

## Main results

* `Stacks.Intersection.RationalEquivalence.torFormulaCycleIntersectionProduct_fibre_eq` — the
  identity `[V] · [W_σ]_s = ∑_Z e_Z [Z_σ]_n` along a section `σ` of the projection whose image is
  an effective Cartier divisor.
* `Stacks.Intersection.RationalEquivalence.relativeDimension_genericPoints_comap_eq` — the fibre
  `W_σ` is pure of dimension `s` (Tag 02RK).
* `Stacks.Intersection.RationalEquivalence.rationallyEquivalent_intersectionProduct_fibreCycle` —
  **Tag 0B60**, with the fibre cycles `[W_a]_s`.
* `rationallyEquivalent_intersectionProduct_fibreCycle_dimension_r`, in the same namespace —
  **Tag 0B60** as printed, with `[W_a]_r`.

## Implementation notes

The source writes `[W_a]_r` for the cycle of the fibre. The fibre has dimension `s`, and the cycle
the proof and Tag 0B1V use is `[W_a]_s`; both readings are registered, the printed one following
from the other because the fibres are pure of dimension `s`, so `[W_a]_r = 0` for `r ≠ s`.
Closed subvarieties are the reduced closures of points, as in
Tag 0B1L, and `W_a` is the scheme-theoretic fibre `W.comap σ_a` of Tag 0B07. Proper intersection
of `V` with the `s`-dimensional fibre is the bound `dim (V ∩ W_a) ≤ r + s - dim X` of Tag 0AZQ,
written additively; the empty intersection has dimension `⊥` and satisfies it. The expected
dimension `r + s - dim X` is an integer.

## References

* [Stacks Project, Tag 0B60](https://stacks.math.columbia.edu/tag/0B60)
* [Stacks Project, Tag 0B07](https://stacks.math.columbia.edu/tag/0B07)
* [Stacks Project, Tag 0B0W](https://stacks.math.columbia.edu/tag/0B0W)
* [Stacks Project, Tag 0B1L](https://stacks.math.columbia.edu/tag/0B1L)
* [Stacks Project, Tag 02QF](https://stacks.math.columbia.edu/tag/02QF)
-/
@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Chow AlgebraicGeometry.TorFormula Stacks.Intersection.ReductionToDiagonal
open Stacks.Intersection.ExteriorProductProjections

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Intersection.RationalEquivalence

variable (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsVariety k f]

/-! ### The left-hand side at a point -/

section LeftSide

variable [DecidableEq X] (hX : IsRegular X) (r s n : ℤ) (dX : ℕ)
  (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞)) (hrs : r + s = (dX : ℤ) + n) (v : X)
  (hv : relativeDimension (fieldChowSituation k).dimensionFunction f v = r)
  (Z : X.IdealSheafData)
  (hZ : ∀ w ∈ (Z.support : Set X),
    relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ s)
  (hn : ∀ w ∈ closure ({v} : Set X) ∩ (Z.support : Set X),
    relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ n)

omit [IsAlgClosed k] [DecidableEq X] in
include hv in
/-- The support of `𝒪_V` has dimension at most that of `V`. -/
theorem relativeDimension_le_of_mem_supp_structureSheafAt :
    ∀ w ∈ SheafOfModules.supp (structureSheafAt v),
      relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ r := by
  intro w hw
  rw [supp_structureSheafAt] at hw
  rw [← hv]
  exact relativeDimension_le_of_specializes (fieldChowSituation k) f
    (specializes_iff_mem_closure.mpr hw)

omit [IsAlgClosed k] [IsVariety k f] [DecidableEq X] in
include hn in
/-- The bound on `V ∩ Z`, read on the supports of the two structure sheaves. -/
theorem relativeDimension_le_of_mem_supp_inter :
    ∀ w ∈ SheafOfModules.supp (structureSheafAt v) ∩
      SheafOfModules.supp (subschemeStructureSheaf Z),
      relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ n := by
  intro w hw
  rw [supp_structureSheafAt, supp_subschemeStructureSheaf] at hw
  exact hn w hw

omit [IsAlgClosed k] [IsVariety k f] [DecidableEq X] in
include hZ in
/-- The bound on `Z`, read on the support of its structure sheaf. -/
theorem relativeDimension_le_of_mem_supp_subschemeStructureSheaf :
    ∀ w ∈ SheafOfModules.supp (subschemeStructureSheaf Z),
      relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ s := by
  intro w hw
  rw [supp_subschemeStructureSheaf] at hw
  exact hZ w hw

include hdX hrs hv hZ hn in
/-- **`[V] · [Z]_s` is the alternating sum of the cycles of the `Tor` sheaves**, by the Tor formula
of Tag 0B0W. -/
theorem torFormulaCycleIntersectionProduct_single_eq :
    letI : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
    torFormulaCycleIntersectionProduct (fieldChowSituation k) f hX n
        (Function.locallyFinsuppWithin.single v 1)
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f Z.subschemeι s).1 =
      intersectionProductCycle (fieldChowSituation k) f hX (structureSheafAt v)
        (subschemeStructureSheaf Z) (isCoherent_structureSheafAt v)
        (isCoherent_subschemeStructureSheaf Z) n
        (torSheafDeltaDimension_le_of_forall_mem_inter (fieldChowSituation k) f hX
          (structureSheafAt v) (subschemeStructureSheaf Z) (isCoherent_structureSheafAt v)
          (isCoherent_subschemeStructureSheaf Z) n
          (relativeDimension_le_of_mem_supp_inter k f n v Z hn)) := by
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
  have hr := relativeDimension_le_of_mem_supp_structureSheafAt k f r v hv
  have hs := relativeDimension_le_of_mem_supp_subschemeStructureSheaf k f s Z hZ
  have hTF := Stacks.Intersection.ReductionToDiagonal.torFormula_coherent k f hX r s n dX hdX hrs
    (structureSheafAt v) (isCoherent_structureSheafAt v) hr (subschemeStructureSheaf Z)
    (isCoherent_subschemeStructureSheaf Z) hs (relativeDimension_le_of_mem_supp_inter k f n v Z hn)
  have hV : coherentSheafCycle (fieldChowSituation k) f (structureSheafAt v) r
      (schemeDeltaDimension_reducedSupport_le (fieldChowSituation k) f _ hr) =
      Function.locallyFinsuppWithin.single v 1 :=
    Stacks.Intersection.ReductionToDiagonal.coherentSheafCycle_structureSheafAt
      (fieldChowSituation k) f v r
      (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq (fieldChowSituation k) f
        v hv) _
  have hZb : schemeDeltaDimension (fieldChowSituation k) (Z.subschemeι ≫ f) ≤ (s : EInt) :=
    schemeDeltaDimension_le_of_forall_relativeDimension_le (fieldChowSituation k) f Z.subschemeι
      fun w => hZ _ (by rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨w, rfl⟩)
  have h02 := cycleAssociatedToClosedSubscheme_eq_cycleAssociatedToCoherentSheaf
      (fieldChowSituation k) f Z.subschemeι s hZb
  have hZs : (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f Z.subschemeι s).1 =
      coherentSheafCycle (fieldChowSituation k) f (subschemeStructureSheaf Z) s
        (schemeDeltaDimension_reducedSupport_le (fieldChowSituation k) f _ hs) :=
    congrArg Subtype.val h02
  rw [← hV, hZs, hTF]

include hdX hrs hv hZ hn in
/-- **The coefficient of `[V] · [Z]_s` at a point of `V ∩ Z`** is the alternating sum of the
lengths of the `Tor` modules of the two local rings. -/
theorem torFormulaCycleIntersectionProduct_single_apply (d : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) {x : X}
    (hx : relativeDimension (fieldChowSituation k).dimensionFunction f x = n)
    (hxv : x ∈ closure ({v} : Set X)) (hxZ : x ∈ (Z.support : Set X)) :
    letI : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
    torFormulaCycleIntersectionProduct (fieldChowSituation k) f hX n
        (Function.locallyFinsuppWithin.single v 1)
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f Z.subschemeι s).1 x =
      ∑ i ∈ Finset.range (d + 2), (-1 : ℤ) ^ i * ((Module.length (X.presheaf.stalk x)
        (((Tor (ModuleCat.{u} (X.presheaf.stalk x)) i).obj
          (ModuleCat.of (X.presheaf.stalk x)
            (X.presheaf.stalk x ⧸ IdealSheafData.stalk (integralComponentAt v) x))).obj
          (ModuleCat.of (X.presheaf.stalk x)
            (X.presheaf.stalk x ⧸ IdealSheafData.stalk Z x)))).toNat : ℤ) := by
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
  rw [torFormulaCycleIntersectionProduct_single_eq k f hX r s n dX hdX hrs v hv Z hZ hn]
  have hreg : ∀ y : X, IsRegularLocalRing (X.presheaf.stalk y) :=
    ((isRegular_iff_regular_stalks X).1 hX).2
  rw [intersectionProductCycle_apply (fieldChowSituation k) f hX _ _ _ _ n _ hreg d hd x]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have := isCoherent_torSheaf_of_isRegular X hX (structureSheafAt v) (subschemeStructureSheaf Z)
    (isCoherent_structureSheafAt v) (isCoherent_subschemeStructureSheaf Z) i
  have hb := torSheafDeltaDimension_le_of_forall_mem_inter (fieldChowSituation k) f hX
    (structureSheafAt v) (subschemeStructureSheaf Z) (isCoherent_structureSheafAt v)
    (isCoherent_subschemeStructureSheaf Z) n (relativeDimension_le_of_mem_supp_inter k f n v Z hn) i
  refine (cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_eq (fieldChowSituation k) f
    _ n hb hx).trans ?_
  exact sheafMultiplicity_torSheaf_subschemeStructureSheaf (integralComponentAt v) Z i x
    (by rw [← SetLike.mem_coe, coe_support_integralComponentAt]; exact hxv) hxZ

include hdX hrs hv hZ hn in
/-- **Off `V ∩ Z` the coefficient of `[V] · [Z]_s` vanishes.** -/
theorem torFormulaCycleIntersectionProduct_single_apply_eq_zero {x : X}
    (hx : x ∉ closure ({v} : Set X) ∩ (Z.support : Set X)) :
    letI : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
    torFormulaCycleIntersectionProduct (fieldChowSituation k) f hX n
        (Function.locallyFinsuppWithin.single v 1)
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f Z.subschemeι s).1 x = 0 := by
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
  rw [torFormulaCycleIntersectionProduct_single_eq k f hX r s n dX hdX hrs v hv Z hZ hn]
  have hreg : ∀ y : X, IsRegularLocalRing (X.presheaf.stalk y) :=
    ((isRegular_iff_regular_stalks X).1 hX).2
  rw [intersectionProductCycle_apply (fieldChowSituation k) f hX _ _ _ _ n _ hreg dX hdX.le x]
  refine Finset.sum_eq_zero fun i _ => ?_
  have := isCoherent_torSheaf_of_isRegular X hX (structureSheafAt v) (subschemeStructureSheaf Z)
    (isCoherent_structureSheafAt v) (isCoherent_subschemeStructureSheaf Z) i
  have hxT : x ∉ SheafOfModules.supp (torSheaf X (structureSheafAt v)
      (subschemeStructureSheaf Z) i) := by
    intro hmem
    apply hx
    have := supp_torSheaf_subset_inter X (structureSheafAt v) (subschemeStructureSheaf Z) i hmem
    rwa [supp_structureSheafAt, supp_subschemeStructureSheaf] at this
  rw [sheafCycleCoeff, ite_eq_right (fun h => hxT h.1), mul_zero]

end LeftSide

/-! ### The local rings along a section of a retraction -/

section SectionStalk

variable {Y P : Scheme.{u}} (σ : Y ⟶ P) (pr : P ⟶ Y) (hσ : σ ≫ pr = 𝟙 Y) (x : Y)

include hσ in
/-- A section of a retraction lands over the point it starts from. -/
theorem retraction_apply_section : pr.base (σ.base x) = x := by
  rw [← Scheme.Hom.comp_apply, hσ]
  rfl

/-- The stalk of an ideal sheaf is transported along an equality of points. -/
theorem idealStalk_eq_map_stalkCongr (I : Y.IdealSheafData) {a b : Y} (h : a = b) :
    IdealSheafData.stalk I b =
      Ideal.map (Y.presheaf.stalkCongr (.of_eq h)).hom.hom (IdealSheafData.stalk I a) := by
  subst h
  rw [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl]
  exact (Ideal.map_id _).symm

/-- The local homomorphism `𝒪_{Y, x} → 𝒪_{P, σ x}` induced by the retraction. -/
def retractionStalkMap : Y.presheaf.stalk x ⟶ P.presheaf.stalk (σ.base x) :=
  (Y.presheaf.stalkCongr (.of_eq (retraction_apply_section σ pr hσ x).symm)).hom ≫
    pr.stalkMap (σ.base x)

/-- The stalk map `𝒪_{Y, x} → 𝒪_{P, σ x}` induced by the retraction is a local homomorphism. -/
instance isLocalHom_retractionStalkMap : IsLocalHom (retractionStalkMap σ pr hσ x).hom := by
  rw [retractionStalkMap, CommRingCat.hom_comp]
  infer_instance

omit hσ in
/-- Transport to the image under an endomorphism equal to the identity, followed by its stalk
map, is the identity. -/
theorem stalkCongr_comp_stalkMap_of_eq_id (g : Y ⟶ Y) (hg : g = 𝟙 Y)
    (h : Inseparable x (g.base x)) :
    (Y.presheaf.stalkCongr h).hom ≫ g.stalkMap x = 𝟙 _ := by
  subst hg
  simp only [Scheme.Hom.stalkMap_id]
  exact Y.presheaf.stalkSpecializes_refl x

/-- The stalk map of the section is a retraction of the stalk map of the retraction. -/
theorem retractionStalkMap_comp_stalkMap :
    retractionStalkMap σ pr hσ x ≫ σ.stalkMap x = 𝟙 _ := by
  rw [retractionStalkMap, Category.assoc, ← Scheme.Hom.stalkMap_comp]
  exact stalkCongr_comp_stalkMap_of_eq_id x (σ ≫ pr) hσ _

/-- The stalk of the inverse image of an ideal sheaf along the retraction, at a point of the
section, is the extension of the stalk of the ideal sheaf. -/
theorem idealStalk_comap_retraction (I : Y.IdealSheafData) :
    IdealSheafData.stalk (I.comap pr) (σ.base x) =
      Ideal.map (retractionStalkMap σ pr hσ x).hom (IdealSheafData.stalk I x) := by
  rw [IdealSheafData.stalk_comap, idealStalk_eq_map_stalkCongr I
    (retraction_apply_section σ pr hσ x).symm, Ideal.map_map, retractionStalkMap,
    CommRingCat.hom_comp]

/-- The local homomorphism induced by a flat retraction is flat. -/
theorem flat_retractionStalkMap [Flat pr] : (retractionStalkMap σ pr hσ x).hom.Flat := by
  rw [retractionStalkMap, CommRingCat.hom_comp]
  refine RingHom.Flat.comp ?_ (Flat.stalkMap pr (σ.base x))
  exact RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)

end SectionStalk

/-! ### Local lengths -/

/-- The order of vanishing of `t` along a prime `Q` is the colength of `(t) + Q`. -/
theorem ord_quotient_eq_length {B : Type u} [CommRing B] (Q : Ideal B) (t : B) :
    Ring.ord (B ⧸ Q) (Ideal.Quotient.mk Q t) = Module.length B (B ⧸ (Ideal.span {t} ⊔ Q)) := by
  have hspan : Ideal.span {Ideal.Quotient.mk Q t} = (Ideal.span {t}).map (Ideal.Quotient.mk Q) := by
    rw [Ideal.map_span, Set.image_singleton]
  let e : (B ⧸ Q) ⧸ Ideal.span {Ideal.Quotient.mk Q t} ≃+* B ⧸ (Ideal.span {t} ⊔ Q) :=
    (Ideal.quotEquivOfEq hspan).trans
      ((DoubleQuot.quotQuotEquivQuotSup Q (Ideal.span {t})).trans
        (Ideal.quotEquivOfEq (sup_comm _ _)))
  refine (Module.length_eq_of_surjective_of_addEquiv (Ideal.Quotient.mk Q)
    Ideal.Quotient.mk_surjective e.toAddEquiv fun b x => ?_).symm
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  rfl

/-- A linear equivalence of modules gives localizations of equal length. -/
theorem length_localizedModule_eq_of_linearEquiv {B : Type u} [CommRing B] (Q : Ideal B)
    [Q.IsPrime] {M N : Type u} [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    (e : M ≃ₗ[B] N) :
    Module.length (Localization.AtPrime Q) (LocalizedModule Q.primeCompl M) =
      Module.length (Localization.AtPrime Q) (LocalizedModule Q.primeCompl N) :=
  (IsLocalizedModule.mapEquiv Q.primeCompl (LocalizedModule.mkLinearMap Q.primeCompl M)
    (LocalizedModule.mkLinearMap Q.primeCompl N) (Localization.AtPrime Q) e).length_eq

/-! ### The weight of a component of `(V × ℙ¹) ∩ W` -/

/-- The inverse image `V × ℙ¹` of the closure `V` of a point `v` of `X`. -/
def cylinderIdeal (v : X) : (projectiveLineProduct f).IdealSheafData :=
  (integralComponentAt v).comap
    (pullback.fst f (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)))

/-- The alternating sum `∑ⱼ (-1)ʲ length Torⱼ(𝒪_{V × ℙ¹}, 𝒪_W)` at a point `z` of `X × ℙ¹`: at the
generic point of a component `Z` of `(V × ℙ¹) ∩ W` this is the coefficient `e_Z` of the source. -/
def componentWeight (v : X) (W : (projectiveLineProduct f).IdealSheafData) (d : ℕ)
    (z : projectiveLineProduct f) : ℤ :=
  ∑ j ∈ Finset.range (d + 2), (-1 : ℤ) ^ j *
    sheafMultiplicity (torSheaf (projectiveLineProduct f)
      (subschemeStructureSheaf (cylinderIdeal k f v)) (subschemeStructureSheaf W) j) z

omit [IsAlgClosed k] [IsVariety k f] in
/-- The weight at a generalization of a point `y`, read in the local ring at `y`. -/
theorem componentWeight_fromSpecStalk (hP : IsRegular (projectiveLineProduct f)) (v : X)
    (W : (projectiveLineProduct f).IdealSheafData) (d : ℕ) {y : projectiveLineProduct f}
    (hyV : y ∈ (cylinderIdeal k f v).support) (hyW : y ∈ W.support)
    (Q : PrimeSpectrum ((projectiveLineProduct f).presheaf.stalk y)) :
    componentWeight k f v W d ((projectiveLineProduct f).fromSpecStalk y Q) =
      ∑ j ∈ Finset.range (d + 2), (-1 : ℤ) ^ j *
        ((Module.length (Localization.AtPrime Q.asIdeal)
          (LocalizedModule Q.asIdeal.primeCompl
            (((Tor (ModuleCat.{u} ((projectiveLineProduct f).presheaf.stalk y)) j).obj
              (ModuleCat.of ((projectiveLineProduct f).presheaf.stalk y)
                ((projectiveLineProduct f).presheaf.stalk y ⧸
                  IdealSheafData.stalk (cylinderIdeal k f v) y))).obj
              (ModuleCat.of ((projectiveLineProduct f).presheaf.stalk y)
                ((projectiveLineProduct f).presheaf.stalk y ⧸
                  IdealSheafData.stalk W y))))).toNat : ℤ) := by
  have : IsLocallyNoetherian (projectiveLineProduct f) := isLocallyNoetherian_of_isRegular hP
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have := isCoherent_torSheaf_of_isRegular _ hP (subschemeStructureSheaf (cylinderIdeal k f v))
    (subschemeStructureSheaf W) (isCoherent_subschemeStructureSheaf _)
    (isCoherent_subschemeStructureSheaf W) j
  have := isQuasicoherent_of_isCoherent (torSheaf (projectiveLineProduct f)
    (subschemeStructureSheaf (cylinderIdeal k f v)) (subschemeStructureSheaf W) j)
  rw [← length_localizedModule_stalk_eq_sheafMultiplicity]
  congr 2
  refine length_localizedModule_eq_of_linearEquiv Q.asIdeal ?_
  exact (stalkTorModuleCatIso _ _ _ j y ≪≫
    ((Tor _ j).mapIso (stalkSubschemeStructureSheafIso _ y hyV)).app _ ≪≫
    ((Tor _ j).obj _).mapIso (stalkSubschemeStructureSheafIso W y hyW)).toLinearEquiv

/-! ### Points of `Spec 𝒪_{P,y}` -/

section SpecStalk

variable {P : Scheme.{u}} (y : P)

/-- A prime of a local ring of `P` contains the stalk of an ideal sheaf exactly when the point
it defines lies on the support. -/
theorem mem_support_quotient_idealStalk_iff (J : P.IdealSheafData)
    (Q : PrimeSpectrum (P.presheaf.stalk y)) :
    Q ∈ Module.support (P.presheaf.stalk y) (P.presheaf.stalk y ⧸ IdealSheafData.stalk J y) ↔
      P.fromSpecStalk y Q ∈ (J.support : Set P) := by
  rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient, PrimeSpectrum.mem_zeroLocus,
    SetLike.coe_subset_coe]
  exact le_iff_fromSpecStalk_mem_support J y Q

/-- The canonical morphism `Spec 𝒪_{P,y} → P` is injective on underlying points. -/
theorem fromSpecStalk_injective : Function.Injective ⇑(P.fromSpecStalk y) :=
  (P.fromSpecStalk y).isEmbedding.injective

/-- Under `Spec 𝒪_{P,y} → P`, the image of `Q` specializes to the image of `Q'` exactly when
`Q ≤ Q'`. -/
theorem fromSpecStalk_specializes_iff (Q Q' : PrimeSpectrum (P.presheaf.stalk y)) :
    P.fromSpecStalk y Q ⤳ P.fromSpecStalk y Q' ↔ Q.asIdeal ≤ Q'.asIdeal :=
  (P.fromSpecStalk y).isEmbedding.isInducing.specializes_iff.trans
    (PrimeSpectrum.le_iff_specializes Q Q').symm

/-- The image of every point under `Spec 𝒪_{P,y} → P` specializes to `y`. -/
theorem fromSpecStalk_specializes (Q : PrimeSpectrum (P.presheaf.stalk y)) :
    P.fromSpecStalk y Q ⤳ y := by
  have h : P.fromSpecStalk y Q ∈ Set.range ⇑(P.fromSpecStalk y) := ⟨Q, rfl⟩
  rwa [Scheme.range_fromSpecStalk] at h

/-- Every generization of `y` is the image of a point under `Spec 𝒪_{P,y} → P`. -/
theorem exists_fromSpecStalk_eq_of_specializes {z : P} (hz : z ⤳ y) :
    ∃ Q : PrimeSpectrum (P.presheaf.stalk y), P.fromSpecStalk y Q = z := by
  have h : z ∈ Set.range ⇑(P.fromSpecStalk y) := by rw [Scheme.range_fromSpecStalk]; exact hz
  exact h

omit [IsAlgClosed k] in
/-- A prime lies in the support of a cyclic module exactly when it contains the ideal. -/
theorem mem_support_quotient_iff_le {R : Type u} [CommRing R] (I : Ideal R)
    (Q : PrimeSpectrum R) : Q ∈ Module.support R (R ⧸ I) ↔ I ≤ Q.asIdeal := by
  rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient, PrimeSpectrum.mem_zeroLocus,
    SetLike.coe_subset_coe]

/-- If `Q` is minimal in the support of `𝒪_{P,y} ⧸ (I₁ ⊔ I₂)`, then every point of
`V(J₁ ⊔ J₂)` specializing to the point of `Q` is that point. -/
theorem eq_of_specializes_of_minimal_support_quotient_sup (J₁ J₂ : P.IdealSheafData)
    {Q : PrimeSpectrum (P.presheaf.stalk y)}
    (hQ : Minimal (· ∈ Module.support (P.presheaf.stalk y)
      (P.presheaf.stalk y ⧸ (IdealSheafData.stalk J₁ y ⊔ IdealSheafData.stalk J₂ y))) Q)
    {z : P} (hz : z ∈ ((J₁ ⊔ J₂).support : Set P)) (hzQ : z ⤳ P.fromSpecStalk y Q) :
    z = P.fromSpecStalk y Q := by
  obtain ⟨Q', rfl⟩ := exists_fromSpecStalk_eq_of_specializes y
    (hzQ.trans (fromSpecStalk_specializes y Q))
  rw [fromSpecStalk_specializes_iff] at hzQ
  have hz' : P.fromSpecStalk y Q' ∈ (J₁.support : Set P) ∧
      P.fromSpecStalk y Q' ∈ (J₂.support : Set P) := by
    rw [Scheme.IdealSheafData.support_sup] at hz
    exact hz
  have hQ' : Q' ∈ Module.support (P.presheaf.stalk y)
      (P.presheaf.stalk y ⧸ (IdealSheafData.stalk J₁ y ⊔ IdealSheafData.stalk J₂ y)) := by
    rw [mem_support_quotient_iff_le, sup_le_iff]
    exact ⟨(le_iff_fromSpecStalk_mem_support _ y Q').mpr hz'.1,
      (le_iff_fromSpecStalk_mem_support _ y Q').mpr hz'.2⟩
  rw [PrimeSpectrum.ext (le_antisymm hzQ (hQ.2 hQ' hzQ))]

omit [IsAlgClosed k] in
/-- If `B ⧸ I` and `B ⧸ J` meet `V(t)` only at the closed point, then `B ⧸ K` has support
dimension at most one for every `K ≥ I ⊔ J`. -/
theorem supportDim_quotient_le_one_of_sup_le {B : Type u} [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] {I J K : Ideal B} (t : B) (htm : t ∈ IsLocalRing.maximalIdeal B)
    (hsupp : Module.support B (B ⧸ I) ∩ Module.support B (B ⧸ J) ∩
      PrimeSpectrum.zeroLocus {t} ⊆ {IsLocalRing.closedPoint B}) (hK : I ⊔ J ≤ K) :
    Module.supportDim B (B ⧸ K) ≤ 1 :=
  Stacks.Intersection.PrincipalQuotientTor.supportDim_le_one_of_support_inter_subset t htm
    fun Q hQ => hsupp ⟨⟨(mem_support_quotient_iff_le _ Q).mpr
        ((le_sup_left.trans hK).trans ((mem_support_quotient_iff_le _ Q).mp hQ.1)),
      (mem_support_quotient_iff_le _ Q).mpr
        ((le_sup_right.trans hK).trans ((mem_support_quotient_iff_le _ Q).mp hQ.1))⟩, hQ.2⟩

omit [IsAlgClosed k] in
/-- If `B ⧸ I` and `B ⧸ J` meet `V(t)` only at the closed point, every non-maximal prime
`Q ≥ I ⊔ J` has `dim B ⧸ Q = 1`. -/
theorem ringKrullDim_quotient_eq_one_of_sup_le {B : Type u} [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] {I J : Ideal B} (t : B) (htm : t ∈ IsLocalRing.maximalIdeal B)
    (hsupp : Module.support B (B ⧸ I) ∩ Module.support B (B ⧸ J) ∩
      PrimeSpectrum.zeroLocus {t} ⊆ {IsLocalRing.closedPoint B}) {Q : PrimeSpectrum B}
    (hQ : I ⊔ J ≤ Q.asIdeal) (hQm : Q ≠ IsLocalRing.closedPoint B) :
    ringKrullDim (B ⧸ Q.asIdeal) = 1 := by
  rw [← Module.supportDim_quotient_eq_ringKrullDim]
  refine le_antisymm (supportDim_quotient_le_one_of_sup_le t htm hsupp hQ) ?_
  have hle : Q ≤ IsLocalRing.closedPoint B := IsLocalRing.le_maximalIdeal Q.isPrime.ne_top
  exact Order.one_le_krullDim_iff.mpr
    ⟨⟨Q, (mem_support_quotient_iff_le _ Q).mpr le_rfl⟩,
      ⟨_, (mem_support_quotient_iff_le _ _).mpr hle⟩,
      lt_of_le_of_ne hle fun h => hQm (congrArg Subtype.val h)⟩

/-- For an integral closed subscheme `W`, the prime of `𝒪_{P,y}` given by the stalk of its ideal
sheaf defines the generic point of `W`. -/
theorem isGenericPoint_fromSpecStalk_idealStalk (W : P.IdealSheafData) [IsIntegral W.subscheme]
    (hprime : (IdealSheafData.stalk W y).IsPrime) :
    IsGenericPoint (P.fromSpecStalk y ⟨IdealSheafData.stalk W y, hprime⟩) (W.support : Set P) := by
  let Qw : PrimeSpectrum (P.presheaf.stalk y) := ⟨IdealSheafData.stalk W y, hprime⟩
  have hirr : IsIrreducible (W.support : Set P) := by
    rw [← Scheme.IdealSheafData.range_subschemeι, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ W.subscheme).image _
      W.subschemeι.continuous.continuousOn
  have hη := hirr.isGenericPoint_genericPoint_closure
  rw [W.support.isClosed.closure_eq] at hη
  have hηz : hirr.genericPoint ⤳ P.fromSpecStalk y Qw :=
    hη.specializes ((le_iff_fromSpecStalk_mem_support W y Qw).mp le_rfl)
  obtain ⟨Qη, hQη⟩ := exists_fromSpecStalk_eq_of_specializes y
    (hηz.trans (fromSpecStalk_specializes y Qw))
  have h1 : IdealSheafData.stalk W y ≤ Qη.asIdeal :=
    (le_iff_fromSpecStalk_mem_support W y Qη).mpr (hQη ▸ hη.mem)
  have h2 : Qη.asIdeal ≤ Qw.asIdeal := by
    rw [← fromSpecStalk_specializes_iff, hQη]
    exact hηz
  change IsGenericPoint (P.fromSpecStalk y Qw) _
  rwa [← PrimeSpectrum.ext (le_antisymm h2 h1), hQη]

/-- If an integral `W` through `y` is not contained in the closed set `T` and `t` lies only in
primes of `𝒪_{P,y}` over `T`, then `t` is a nonzerodivisor on `𝒪_{P,y} ⧸ I_W`. -/
theorem isSMulRegular_quotient_idealStalk_of_not_range_subset (W : P.IdealSheafData)
    [IsIntegral W.subscheme] (hyW : y ∈ (W.support : Set P)) {T : Set P} (hT : IsClosed T)
    (hWT : ¬ Set.range W.subschemeι ⊆ T) {t : P.presheaf.stalk y}
    (htT : ∀ Q : PrimeSpectrum (P.presheaf.stalk y), t ∈ Q.asIdeal → P.fromSpecStalk y Q ∈ T) :
    IsSMulRegular (P.presheaf.stalk y ⧸ IdealSheafData.stalk W y) t := by
  have := isDomain_quotient_idealStalk W hyW
  have hprime : (IdealSheafData.stalk W y).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
  have hne : Ideal.Quotient.mk (IdealSheafData.stalk W y) t ≠ 0 := by
    intro h0
    rw [Ideal.Quotient.eq_zero_iff_mem] at h0
    apply hWT
    rw [Scheme.IdealSheafData.range_subschemeι,
      ← (isGenericPoint_fromSpecStalk_idealStalk y W hprime).def]
    exact closure_minimal (Set.singleton_subset_iff.mpr (htT ⟨_, hprime⟩ h0)) hT
  intro a b hab
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact mul_left_cancel₀ hne hab

end SpecStalk

/-- The support of the inverse image of an ideal sheaf is the preimage of its support. -/
private theorem mem_support_comap_iff {Y P : Scheme.{u}} (σ : Y ⟶ P) (W : P.IdealSheafData)
    (x : Y) : x ∈ ((W.comap σ).support : Set Y) ↔ σ.base x ∈ (W.support : Set P) := by
  rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage]
  rfl

/-- Along a section of the projection, the relative dimension over the base of a point of the
section is that of the point below. -/
private theorem relativeDimension_section_eq (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsVariety k f] (σ : X ⟶ projectiveLineProduct f) [IsClosedImmersion σ]
    (hσ : σ ≫ pullback.fst f (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) = 𝟙 X)
    (x : X) :
    relativeDimension (fieldChowSituation k).dimensionFunction
      (pullback.fst f (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) ≫ f) (σ.base x) =
      relativeDimension (fieldChowSituation k).dimensionFunction f x :=
  relativeDimension_apply_of_section (fieldChowSituation k) f σ
    (by rw [← Category.assoc, hσ, Category.id_comp]) x

/-- A prime of the local ring at `y` contains a generator `t` of the stalk of the kernel of a
closed immersion `σ` exactly when the point it defines lies in the image of `σ`. -/
private theorem mem_asIdeal_iff_fromSpecStalk_mem_range {Y P : Scheme.{u}} (σ : Y ⟶ P)
    [IsClosedImmersion σ] (y : P) {t : P.presheaf.stalk y}
    (ht : IdealSheafData.stalk σ.ker y = Ideal.span {t}) (Q : PrimeSpectrum (P.presheaf.stalk y)) :
    t ∈ Q.asIdeal ↔ P.fromSpecStalk y Q ∈ Set.range σ := by
  have hrange : (σ.ker.support : Set P) = Set.range σ := by
    rw [Scheme.Hom.support_ker, σ.isClosedEmbedding.isClosed_range.closure_eq]
  rw [← hrange, ← le_iff_fromSpecStalk_mem_support σ.ker y Q, ht,
    Ideal.span_singleton_le_iff_mem]

/-- A generator of the stalk of the kernel of a closed immersion `σ` at a point `σ x` lies in the
maximal ideal. -/
private theorem mem_maximalIdeal_of_stalk_ker_eq_span {Y P : Scheme.{u}} (σ : Y ⟶ P)
    [IsClosedImmersion σ] (x : Y) {t : P.presheaf.stalk (σ.base x)}
    (ht : IdealSheafData.stalk σ.ker (σ.base x) = Ideal.span {t}) :
    t ∈ IsLocalRing.maximalIdeal (P.presheaf.stalk (σ.base x)) :=
  (mem_asIdeal_iff_fromSpecStalk_mem_range σ _ ht (IsLocalRing.closedPoint _)).mpr
    ⟨x, Scheme.fromSpecStalk_closedPoint.symm⟩

/-- If a prime `Q` of the local ring at `σ x` defines a point `σ x'`, and `x'` is forced to be `x`
when it specializes to `x`, then `Q` is the closed point. -/
private theorem eq_closedPoint_of_section_eq {Y P : Scheme.{u}} (σ : Y ⟶ P) (pr : P ⟶ Y)
    (hσ : σ ≫ pr = 𝟙 Y) (x x' : Y) (Q : PrimeSpectrum (P.presheaf.stalk (σ.base x)))
    (hx' : σ.base x' = P.fromSpecStalk _ Q) (h : x' ⤳ x → x' = x) :
    Q = IsLocalRing.closedPoint _ := by
  have hspec : x' ⤳ x := by
    have := (fromSpecStalk_specializes _ Q).map pr.continuous
    rwa [← hx', retraction_apply_section σ pr hσ, retraction_apply_section σ pr hσ] at this
  apply fromSpecStalk_injective (σ.base x)
  rw [Scheme.fromSpecStalk_closedPoint, ← hx', h hspec]

/-! ### The identity at one point -/

section Key

variable [DecidableEq X] (hX : IsRegular X)
  (σ : X ⟶ projectiveLineProduct f) [IsClosedImmersion σ]
  (hσ : σ ≫ pullback.fst f (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) = 𝟙 X)
  (hD : Stacks.Divisors.IsEffectiveCartierDivisor σ.ker)
  (r s n : ℤ) (dX : ℕ) (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞))
  (hrs : r + s = (dX : ℤ) + n) (v : X)
  (hv : relativeDimension (fieldChowSituation k).dimensionFunction f v = r)
  (W : (projectiveLineProduct f).IdealSheafData) [IsIntegral W.subscheme]
  (hWσ : ¬ Set.range W.subschemeι ⊆ Set.range σ)
  (hWs : ∀ w ∈ ((W.comap σ).support : Set X),
    relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ s)
  (hn : ∀ w ∈ closure ({v} : Set X) ∩ ((W.comap σ).support : Set X),
    relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ n)
  (d : ℕ) (hd : topologicalKrullDim (projectiveLineProduct f) ≤ (d : WithBot ℕ∞))
  (hdX' : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
  (Zf : Finset (projectiveLineProduct f))
  (hZ₁ : ∀ z ∈ Zf, z ∈ ((cylinderIdeal k f v ⊔ W).support : Set (projectiveLineProduct f)))
  (hZ₂ : ∀ z ∈ Zf, z ∉ Set.range σ)
  (hZ₃ : ∀ z : projectiveLineProduct f,
    z ∈ ((cylinderIdeal k f v ⊔ W).support : Set (projectiveLineProduct f)) →
    (∀ z' ∈ ((cylinderIdeal k f v ⊔ W).support : Set (projectiveLineProduct f)),
      z' ⤳ z → z' = z) →
    relativeDimension (fieldChowSituation k).dimensionFunction
      (pullback.fst f (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) ≫ f) z = n + 1 →
    z ∉ Set.range σ → (∃ x : X, z ⤳ σ x) → z ∈ Zf)

include hσ hD hdX hrs hv hWσ hWs hn hd hdX' hZ₁ hZ₂ hZ₃ in
/-- **The identity behind Tag 0B60, at one point.** At a point `x` of `X` of delta-dimension `n`,
the coefficient of `[V] · [W_σ]_s` is the sum over the components `Z` of `(V × ℙ¹) ∩ W` of
`e_Z` times the coefficient of `[Z_σ]_n`. -/
theorem torFormulaCycleIntersectionProduct_fibre_apply (x : X)
    (hx : relativeDimension (fieldChowSituation k).dimensionFunction f x = n) :
    letI : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
    torFormulaCycleIntersectionProduct (fieldChowSituation k) f hX n
        (Function.locallyFinsuppWithin.single v 1)
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f (W.comap σ).subschemeι s).1 x =
      ∑ z ∈ Zf, componentWeight k f v W d z *
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f
          ((integralComponentAt z).comap σ).subschemeι n).1 x := by
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
  classical
  set pr := pullback.fst f (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) with hpr
  have hP : IsRegular (projectiveLineProduct f) := isRegular_projectiveLineProduct_of_eq f rfl hX
  have : IsLocallyNoetherian (projectiveLineProduct f) := isLocallyNoetherian_of_isRegular hP
  have hprσ : ∀ x' : X, pr.base (σ.base x') = x' := retraction_apply_section σ pr hσ
  have hcyl : ∀ z : projectiveLineProduct f, z ∈ ((cylinderIdeal k f v).support :
      Set (projectiveLineProduct f)) ↔ pr.base z ∈ closure ({v} : Set X) := by
    intro z
    rw [cylinderIdeal, Scheme.IdealSheafData.support_comap, Closeds.coe_preimage,
      Set.mem_preimage, ← coe_support_integralComponentAt]
  have hJ0 : ∀ z : projectiveLineProduct f,
      z ∈ ((cylinderIdeal k f v ⊔ W).support : Set (projectiveLineProduct f)) ↔
        z ∈ ((cylinderIdeal k f v).support : Set (projectiveLineProduct f)) ∧
          z ∈ (W.support : Set (projectiveLineProduct f)) := by
    intro z
    rw [Scheme.IdealSheafData.support_sup]
    rfl
  -- the points of `X` over which the cylinder meets `W` along the section
  have hpt : ∀ x' : X, σ.base x' ∈ ((cylinderIdeal k f v ⊔ W).support :
      Set (projectiveLineProduct f)) →
        x' ∈ closure ({v} : Set X) ∩ ((W.comap σ).support : Set X) := by
    intro x' hx'
    rw [hJ0, hcyl, hprσ] at hx'
    exact ⟨hx'.1, (mem_support_comap_iff σ W x').mpr hx'.2⟩
  -- the coefficient of `[Z_σ]_n` vanishes off `σ⁻¹(Z)`
  have hcoeff0 : ∀ z ∈ Zf, ¬ σ.base x ∈ closure ({z} : Set (projectiveLineProduct f)) →
      (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f
        ((integralComponentAt z).comap σ).subschemeι n).1 x = 0 := by
    intro z _ hxz
    refine cycleAssociatedToClosedSubscheme_apply_eq_zero_of_notMem_range (fieldChowSituation k) f
      _ n ?_
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap,
      Closeds.coe_preimage, coe_support_integralComponentAt]
    exact hxz
  by_cases hxin : x ∈ closure ({v} : Set X) ∩ ((W.comap σ).support : Set X)
  swap
  · rw [torFormulaCycleIntersectionProduct_single_apply_eq_zero k f hX r s n dX hdX hrs v hv
      (W.comap σ) hWs hn hxin]
    refine (Finset.sum_eq_zero fun z hz => ?_).symm
    rw [hcoeff0 z hz, mul_zero]
    intro hxz
    exact hxin (hpt x (closure_minimal (Set.singleton_subset_iff.mpr (hZ₁ z hz))
      (cylinderIdeal k f v ⊔ W).support.isClosed hxz))
  -- the local rings at `x` and at `y = σ x`
  set y := σ.base x with hy
  have hyV : y ∈ ((cylinderIdeal k f v).support : Set (projectiveLineProduct f)) := by
    rw [hcyl, hprσ]; exact hxin.1
  have hyW : y ∈ (W.support : Set (projectiveLineProduct f)) :=
    (mem_support_comap_iff σ W x).mp hxin.2
  have hyδ : relativeDimension (fieldChowSituation k).dimensionFunction (pr ≫ f) y = n := by
    rw [relativeDimension_section_eq k f σ hσ, hx]
  let : Algebra (X.presheaf.stalk x) ((projectiveLineProduct f).presheaf.stalk y) :=
    (retractionStalkMap σ pr hσ x).hom.toAlgebra
  have : IsLocalHom (algebraMap (X.presheaf.stalk x)
      ((projectiveLineProduct f).presheaf.stalk y)) :=
    isLocalHom_retractionStalkMap σ pr hσ x
  have : IsRegularLocalRing ((projectiveLineProduct f).presheaf.stalk y) :=
    ((isRegular_iff_regular_stalks _).1 hP).2 y
  have hflat : (algebraMap (X.presheaf.stalk x)
      ((projectiveLineProduct f).presheaf.stalk y)).Flat :=
    flat_retractionStalkMap σ pr hσ x
  have hret : (σ.stalkMap x).hom.comp (algebraMap (X.presheaf.stalk x)
      ((projectiveLineProduct f).presheaf.stalk y)) = RingHom.id _ := by
    have h := congrArg CommRingCat.Hom.hom (retractionStalkMap_comp_stalkMap σ pr hσ x)
    rwa [CommRingCat.hom_comp, CommRingCat.hom_id] at h
  obtain ⟨t, htreg, ht⟩ :=
    Stacks.Divisors.exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor σ.ker hD y
  have hker : RingHom.ker (σ.stalkMap x).hom = Ideal.span {t} :=
    (ker_stalkMap_eq_idealStalk_ker σ x).trans ht
  have htB : IsSMulRegular ((projectiveLineProduct f).presheaf.stalk y) t := htreg.left
  have hdimB : ringKrullDim ((projectiveLineProduct f).presheaf.stalk y) ≤ (d : WithBot ℕ∞) :=
    (ringKrullDim_stalk_le_topologicalKrullDim y).trans hd
  have hIB : (IdealSheafData.stalk (integralComponentAt v) x).map
      (algebraMap (X.presheaf.stalk x) ((projectiveLineProduct f).presheaf.stalk y)) =
      IdealSheafData.stalk (cylinderIdeal k f v) y :=
    (idealStalk_comap_retraction σ pr hσ x _).symm
  have hJA : (IdealSheafData.stalk W y).map (σ.stalkMap x).hom =
      IdealSheafData.stalk (W.comap σ) x :=
    (IdealSheafData.stalk_comap W σ x).symm
  have htQ := mem_asIdeal_iff_fromSpecStalk_mem_range σ y ht
  -- `V × ℙ¹`, `W` and the section meet near `y` only at `y`
  have hsupp : Module.support ((projectiveLineProduct f).presheaf.stalk y)
        ((projectiveLineProduct f).presheaf.stalk y ⧸
          (IdealSheafData.stalk (integralComponentAt v) x).map
            (algebraMap (X.presheaf.stalk x) ((projectiveLineProduct f).presheaf.stalk y))) ∩
      Module.support ((projectiveLineProduct f).presheaf.stalk y)
        ((projectiveLineProduct f).presheaf.stalk y ⧸ IdealSheafData.stalk W y) ∩
      PrimeSpectrum.zeroLocus {t} ⊆
        {IsLocalRing.closedPoint ((projectiveLineProduct f).presheaf.stalk y)} := by
    rintro Q ⟨⟨h1, h2⟩, h3⟩
    rw [hIB, mem_support_quotient_idealStalk_iff] at h1
    rw [mem_support_quotient_idealStalk_iff] at h2
    have h3' : t ∈ Q.asIdeal := by
      rwa [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff] at h3
    obtain ⟨x', hx'⟩ := (htQ Q).mp h3'
    have hx'in : x' ∈ closure ({v} : Set X) ∩ ((W.comap σ).support : Set X) :=
      hpt x' (by rw [hx', hJ0]; exact ⟨h1, h2⟩)
    rw [Set.mem_singleton_iff]
    refine eq_closedPoint_of_section_eq σ pr hσ x x' Q hx' fun hspec => ?_
    by_contra hne
    have hlt := relativeDimension_lt_of_specializes (fieldChowSituation k) f hspec hne
    have hle := hn x' hx'in
    omega
  -- `t` is a nonzerodivisor on the local ring of `W`
  have htJ := isSMulRegular_quotient_idealStalk_of_not_range_subset y W hyW
    σ.isClosedEmbedding.isClosed_range hWσ fun Q => (htQ Q).mp
  have htm := mem_maximalIdeal_of_stalk_ker_eq_span σ x ht
  -- the left-hand side as the local alternating sum, and the local identity
  rw [torFormulaCycleIntersectionProduct_single_apply k f hX r s n dX hdX hrs v hv (W.comap σ)
    hWs hn d hdX' hx hxin.1 hxin.2, ← hJA,
    Stacks.Intersection.SectionLocalIdentity.sum_length_tor_section_eq hflat (σ.stalkMap x).hom
      hret t hker htB d hdimB _ _ htJ hsupp, hIB]
  -- the nonclosed points of `V(cylinder) ∩ V(W)` near `y`
  set Iset := {Q : PrimeSpectrum ((projectiveLineProduct f).presheaf.stalk y) |
    Q ∈ Module.support ((projectiveLineProduct f).presheaf.stalk y)
        ((projectiveLineProduct f).presheaf.stalk y ⧸
          IdealSheafData.stalk (cylinderIdeal k f v) y) ∩
      Module.support ((projectiveLineProduct f).presheaf.stalk y)
        ((projectiveLineProduct f).presheaf.stalk y ⧸ IdealSheafData.stalk W y) ∧
    Q ≠ IsLocalRing.closedPoint _} with hIset
  have hsupp' : Module.support ((projectiveLineProduct f).presheaf.stalk y)
        ((projectiveLineProduct f).presheaf.stalk y ⧸
          IdealSheafData.stalk (cylinderIdeal k f v) y) ∩
      Module.support ((projectiveLineProduct f).presheaf.stalk y)
        ((projectiveLineProduct f).presheaf.stalk y ⧸ IdealSheafData.stalk W y) ∩
      PrimeSpectrum.zeroLocus {t} ⊆
        {IsLocalRing.closedPoint ((projectiveLineProduct f).presheaf.stalk y)} := by
    rw [← hIB]; exact hsupp
  have hX0 : Module.supportDim ((projectiveLineProduct f).presheaf.stalk y)
      ((projectiveLineProduct f).presheaf.stalk y ⧸
        (IdealSheafData.stalk (cylinderIdeal k f v) y ⊔ IdealSheafData.stalk W y)) ≤ 1 :=
    supportDim_quotient_le_one_of_sup_le t htm hsupp' le_rfl
  -- for `Q ∈ Iset` the corresponding point is a component of `(V × ℙ¹) ∩ W` in `Zf`
  have hIZ : ∀ Q ∈ Iset, (projectiveLineProduct f).fromSpecStalk y Q ∈ Zf := by
    intro Q hQ
    have hQ1 := (mem_support_quotient_iff_le _ Q).mp hQ.1.1
    have hQ2 := (mem_support_quotient_iff_le _ Q).mp hQ.1.2
    have hzJ : (projectiveLineProduct f).fromSpecStalk y Q ∈
        ((cylinderIdeal k f v ⊔ W).support : Set (projectiveLineProduct f)) := by
      rw [hJ0]
      exact ⟨(le_iff_fromSpecStalk_mem_support _ y Q).mp hQ1,
        (le_iff_fromSpecStalk_mem_support _ y Q).mp hQ2⟩
    have hQX0 : Q ∈ Module.support ((projectiveLineProduct f).presheaf.stalk y)
        ((projectiveLineProduct f).presheaf.stalk y ⧸
          (IdealSheafData.stalk (cylinderIdeal k f v) y ⊔ IdealSheafData.stalk W y)) := by
      rw [mem_support_quotient_iff_le, sup_le_iff]; exact ⟨hQ1, hQ2⟩
    have hQmin := Stacks.Intersection.PrincipalQuotientTor.minimal_support_of_supportDim_le_one
      hX0 hQX0 hQ.2
    have hdimQ := ringKrullDim_quotient_eq_one_of_sup_le t htm hsupp' (sup_le hQ1 hQ2) hQ.2
    refine hZ₃ _ hzJ ?_ ?_ ?_ ⟨x, fromSpecStalk_specializes y Q⟩
    · exact fun z' hz' hz'z =>
        eq_of_specializes_of_minimal_support_quotient_sup y _ _ hQmin hz' hz'z
    · have hyz : y ∈ ((integralComponentAt ((projectiveLineProduct f).fromSpecStalk y Q)).support :
          Set (projectiveLineProduct f)) := by
        rw [coe_support_integralComponentAt]
        exact (fromSpecStalk_specializes y Q).mem_closure
      have h := ringKrullDim_quotient_idealStalk_integralComponentAt (fieldChowSituation k)
        (pr ≫ f) hyz
      rw [idealStalk_integralComponentAt_fromSpecStalk, hdimQ, hyδ] at h
      have h' : (relativeDimension (fieldChowSituation k).dimensionFunction (pr ≫ f)
          ((projectiveLineProduct f).fromSpecStalk y Q) - n).toNat = 1 := by
        exact_mod_cast h.symm
      omega
    · intro hzσ
      exact hQ.2 (Set.mem_singleton_iff.mp (hsupp' ⟨hQ.1, by
        rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]; exact (htQ Q).mpr hzσ⟩))
  -- each summand
  have hterm : ∀ Q ∈ Iset, componentWeight k f v W d ((projectiveLineProduct f).fromSpecStalk y Q) *
      (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f
        ((integralComponentAt ((projectiveLineProduct f).fromSpecStalk y Q)).comap
          σ).subschemeι n).1 x =
      ((Ring.ord ((projectiveLineProduct f).presheaf.stalk y ⧸ Q.asIdeal)
          (Ideal.Quotient.mk Q.asIdeal t)).toNat : ℤ) *
        ∑ j ∈ Finset.range (d + 2), (-1 : ℤ) ^ j *
          ((Module.length (Localization.AtPrime Q.asIdeal)
            (LocalizedModule Q.asIdeal.primeCompl
              (((Tor (ModuleCat.{u} ((projectiveLineProduct f).presheaf.stalk y)) j).obj
                (ModuleCat.of ((projectiveLineProduct f).presheaf.stalk y)
                  ((projectiveLineProduct f).presheaf.stalk y ⧸
                    IdealSheafData.stalk (cylinderIdeal k f v) y))).obj
                (ModuleCat.of ((projectiveLineProduct f).presheaf.stalk y)
                  ((projectiveLineProduct f).presheaf.stalk y ⧸
                    IdealSheafData.stalk W y))))).toNat : ℤ) := by
    intro Q hQ
    have hzJ := hZ₁ _ (hIZ Q hQ)
    have hWz : schemeDeltaDimension (fieldChowSituation k)
        (((integralComponentAt ((projectiveLineProduct f).fromSpecStalk y Q)).comap
          σ).subschemeι ≫ f) ≤ (n : EInt) := by
      refine schemeDeltaDimension_le_of_forall_relativeDimension_le (fieldChowSituation k) f _
        fun w => hn _ (hpt _ ?_)
      have hw : ((integralComponentAt ((projectiveLineProduct f).fromSpecStalk y Q)).comap
          σ).subschemeι w ∈ (((integralComponentAt ((projectiveLineProduct f).fromSpecStalk y
            Q)).comap σ).support : Set X) := by
        rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨w, rfl⟩
      rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, Set.mem_preimage,
        coe_support_integralComponentAt] at hw
      exact closure_minimal (Set.singleton_subset_iff.mpr hzJ)
        (cylinderIdeal k f v ⊔ W).support.isClosed hw
    have hxz : σ.base x ∈ ((integralComponentAt ((projectiveLineProduct f).fromSpecStalk y
        Q)).support : Set (projectiveLineProduct f)) := by
      rw [coe_support_integralComponentAt]
      exact (fromSpecStalk_specializes y Q).mem_closure
    rw [componentWeight_fromSpecStalk k f hP v W d hyV hyW Q,
      cycleAssociatedToComap_apply_eq_length_of_mem_support (fieldChowSituation k) f n σ
        (integralComponentAt ((projectiveLineProduct f).fromSpecStalk y Q)) hWz hx hxz,
      idealStalk_integralComponentAt_fromSpecStalk, hker, ← ord_quotient_eq_length]
    ring
  -- the reindexing
  have hbij : Set.BijOn ⇑((projectiveLineProduct f).fromSpecStalk y) Iset
      {z | z ∈ Zf ∧ z ⤳ y} := by
    refine ⟨fun Q hQ => ⟨hIZ Q hQ, fromSpecStalk_specializes y Q⟩,
      (fromSpecStalk_injective y).injOn, fun z hz => ?_⟩
    obtain ⟨Q, rfl⟩ := exists_fromSpecStalk_eq_of_specializes y hz.2
    have hzJ := (hJ0 _).mp (hZ₁ _ hz.1)
    refine ⟨Q, ⟨⟨(mem_support_quotient_idealStalk_iff y _ Q).mpr hzJ.1,
      (mem_support_quotient_idealStalk_iff y _ Q).mpr hzJ.2⟩, fun hQm => ?_⟩, rfl⟩
    apply hZ₂ _ hz.1
    rw [hQm, Scheme.fromSpecStalk_closedPoint]
    exact ⟨x, rfl⟩
  rw [← finsum_mem_coe_finset]
  symm
  calc (∑ᶠ z ∈ (Zf : Set (projectiveLineProduct f)), componentWeight k f v W d z *
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f
          ((integralComponentAt z).comap σ).subschemeι n).1 x)
      = ∑ᶠ z ∈ {z | z ∈ Zf ∧ z ⤳ y}, componentWeight k f v W d z *
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f
          ((integralComponentAt z).comap σ).subschemeι n).1 x := by
        refine finsum_mem_inter_support_eq' _ _ _ fun z hz => ⟨fun hzZ => ⟨hzZ, ?_⟩,
          fun h => h.1⟩
        by_contra hzy
        apply hz
        change componentWeight k f v W d z * _ = 0
        rw [hcoeff0 z hzZ (fun h => hzy (specializes_iff_mem_closure.mpr h)), mul_zero]
    _ = _ := (finsum_mem_eq_of_bijOn _ hbij fun Q hQ => (hterm Q hQ).symm).symm


include hσ hD hdX hrs hv hWσ hWs hn hd hdX' hZ₁ hZ₂ hZ₃ in
/-- **The identity behind Tag 0B60, as cycles.** `[V] · [W_σ]_s = ∑_Z e_Z [Z_σ]_n`. -/
theorem torFormulaCycleIntersectionProduct_fibre_eq :
    letI : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
    torFormulaCycleIntersectionProduct (fieldChowSituation k) f hX n
        (Function.locallyFinsuppWithin.single v 1)
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f (W.comap σ).subschemeι s).1 =
      ∑ z ∈ Zf, componentWeight k f v W d z •
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f
          ((integralComponentAt z).comap σ).subschemeι n).1 := by
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
  apply Function.locallyFinsuppWithin.ext
  intro x
  rw [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
  simp only [Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply, smul_eq_mul]
  by_cases hx : relativeDimension (fieldChowSituation k).dimensionFunction f x = n
  · exact torFormulaCycleIntersectionProduct_fibre_apply k f hX σ hσ hD r s n dX hdX hrs v hv W
      hWσ hWs hn d hd hdX' Zf hZ₁ hZ₂ hZ₃ x hx
  · have hzero : ∀ c ∈ cyclesOfDimension (fieldChowSituation k) f n, c x = 0 := fun c hc => by
      by_contra hne
      exact hx ((mem_cyclesOfDimension_iff_forall_point (fieldChowSituation k) f n _).mp hc x hne)
    rw [hzero _ (torFormulaCycleIntersectionProduct_mem_cyclesOfDimension
      (fieldChowSituation k) f hX n _ _)]
    refine (Finset.sum_eq_zero fun z _ => ?_).symm
    rw [hzero _ (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f _ n).2, mul_zero]

end Key

/-! ### The section of the family at a closed point -/

section ClosedPointSection

variable (c : relativeProjectiveLine (Spec (.of k))) (hc : IsClosed {c})

omit [IsVariety k f] in
/-- The section at a closed point is presented as a point of the affine chart or as the point at
infinity. -/
theorem isPresentedSection_closedPointSection :
    IsPresentedSection (fieldChowSituation k) f (closedPointSection k rfl c hc f) :=
  exists_closedPointSection_eq_pointSection_or_eq_infinitySection k rfl c hc f

omit [IsVariety k f] in
/-- The section at a closed point is a closed immersion. -/
theorem isClosedImmersion_closedPointSection :
    IsClosedImmersion (closedPointSection k rfl c hc f) := by
  rcases isPresentedSection_closedPointSection k f c hc with ⟨t, ht⟩ | ht <;> rw [ht] <;>
    infer_instance

omit [IsVariety k f] in
/-- The image of the section at a closed point is an effective Cartier divisor. -/
theorem isEffectiveCartierDivisor_ker_closedPointSection :
    Stacks.Divisors.IsEffectiveCartierDivisor (closedPointSection k rfl c hc f).ker := by
  rcases isPresentedSection_closedPointSection k f c hc with ⟨t, ht⟩ | ht <;> rw [ht]
  · exact isEffectiveCartierDivisor_ker_pointSection f t
  · exact isEffectiveCartierDivisor_ker_infinitySection f

omit [IsVariety k f] in
/-- The section at `c` lies over `c`. -/
theorem snd_closedPointSection_apply (x : X) :
    (pullback.snd f (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k))).base
      ((closedPointSection k rfl c hc f).base x) = c := by
  rw [← Scheme.Hom.comp_apply, closedPointSection_comp_snd, Scheme.Hom.comp_apply,
    closedPointLineSection_apply]

end ClosedPointSection

/-! ### The fibre of `W` along a section is pure -/

section Purity

variable (σ : X ⟶ projectiveLineProduct f) [IsClosedImmersion σ]
  (hσ : σ ≫ pullback.fst f (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) = 𝟙 X)
  (hD : Stacks.Divisors.IsEffectiveCartierDivisor σ.ker)
  (W : (projectiveLineProduct f).IdealSheafData) [IsIntegral W.subscheme] (s : ℤ)
  (hηδ : relativeDimension (fieldChowSituation k).dimensionFunction
    (pullback.fst f (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) ≫ f)
    (W.subschemeι.base (genericPoint W.subscheme)) = s + 1)
  (hWs : ∀ w ∈ ((W.comap σ).support : Set X),
    relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ s)

omit [IsAlgClosed k] in
include hσ hD hηδ hWs in
/-- **Every component of the fibre `W_σ` has dimension `s`.** At the generic point `x` of a
component, the image of the section meets `W` near `σ x` only at `σ x`, so by Krull's principal
ideal theorem the local ring of `W` at `σ x` has dimension at most one (Tag 02RK). -/
theorem relativeDimension_genericPoints_comap_eq
    (ξ : genericPoints (W.comap σ).subscheme) :
    relativeDimension (fieldChowSituation k).dimensionFunction f
      ((W.comap σ).subschemeι.base ξ.1) = s := by
  classical
  set pr := pullback.fst f (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) with hpr
  set x := (W.comap σ).subschemeι.base ξ.1 with hxdef
  set η := W.subschemeι.base (genericPoint W.subscheme) with hη
  have hprσ : ∀ x' : X, pr.base (σ.base x') = x' := retraction_apply_section σ pr hσ
  have hxW : x ∈ ((W.comap σ).support : Set X) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨ξ.1, rfl⟩
  -- `x` is a maximal point of the support of `W_σ`
  have hxmax : ∀ x' ∈ ((W.comap σ).support : Set X), x' ⤳ x → x' = x := by
    intro x' hx' hx'x
    rw [← Scheme.IdealSheafData.range_subschemeι] at hx'
    obtain ⟨w', rfl⟩ := hx'
    have hw' : w' ⤳ ξ.1 :=
      ((W.comap σ).subschemeι.isClosedEmbedding.isInducing.specializes_iff).mp hx'x
    have hcomp : closure ({ξ.1} : Set (W.comap σ).subscheme) ∈
        irreducibleComponents (W.comap σ).subscheme := ξ.2
    have hsub : closure ({ξ.1} : Set (W.comap σ).subscheme) ⊆ closure {w'} :=
      closure_minimal (Set.singleton_subset_iff.mpr hw'.mem_closure) isClosed_closure
    have heq := hcomp.2 isIrreducible_singleton.closure hsub
    have hξw : ξ.1 ⤳ w' := specializes_iff_mem_closure.mpr (heq (subset_closure rfl))
    exact congrArg _ (hw'.antisymm hξw).eq
  set y := σ.base x with hy
  have hyW : y ∈ (W.support : Set (projectiveLineProduct f)) := (mem_support_comap_iff σ W x).mp hxW
  obtain ⟨t, -, ht⟩ :=
    Stacks.Divisors.exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor σ.ker hD y
  have htQ := mem_asIdeal_iff_fromSpecStalk_mem_range σ y ht
  have htm := mem_maximalIdeal_of_stalk_ker_eq_span σ x ht
  -- near `y`, the section meets `W` only at `y`
  have hsuppJ : Module.support ((projectiveLineProduct f).presheaf.stalk y)
      ((projectiveLineProduct f).presheaf.stalk y ⧸ IdealSheafData.stalk W y) ∩
        PrimeSpectrum.zeroLocus {t} ⊆
      {IsLocalRing.closedPoint ((projectiveLineProduct f).presheaf.stalk y)} := by
    rintro Q ⟨h1, h2⟩
    rw [mem_support_quotient_idealStalk_iff] at h1
    rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff] at h2
    obtain ⟨x', hx'⟩ := (htQ Q).mp h2
    have hx'W : x' ∈ ((W.comap σ).support : Set X) := (mem_support_comap_iff σ W x').mpr (hx' ▸ h1)
    exact eq_closedPoint_of_section_eq σ pr hσ x x' Q hx' (hxmax x' hx'W)
  have hdim := Stacks.Intersection.PrincipalQuotientTor.supportDim_le_one_of_support_inter_subset
    t htm hsuppJ
  rw [Module.supportDim_quotient_eq_ringKrullDim] at hdim
  have hyη : y ∈ ((integralComponentAt η).support : Set (projectiveLineProduct f)) := by
    rw [integralComponentAt_subschemeι_genericPoint W]; exact hyW
  have h := ringKrullDim_quotient_idealStalk_integralComponentAt (fieldChowSituation k)
    (pr ≫ f) hyη
  rw [integralComponentAt_subschemeι_genericPoint W] at h
  rw [h] at hdim
  have h' : (relativeDimension (fieldChowSituation k).dimensionFunction (pr ≫ f) η -
      relativeDimension (fieldChowSituation k).dimensionFunction (pr ≫ f) y).toNat ≤ 1 := by
    exact_mod_cast hdim
  have hle := hWs x hxW
  have hδσ : relativeDimension (fieldChowSituation k).dimensionFunction (pr ≫ f) y =
      relativeDimension (fieldChowSituation k).dimensionFunction f x :=
    relativeDimension_section_eq k f σ hσ x
  omega

omit [IsAlgClosed k] in
include hσ hD hηδ hWs in
/-- Off the dimension `s` of its components, the cycle of the fibre `W_σ` vanishes. -/
theorem cycleAssociatedToClosedSubscheme_comap_eq_zero {r : ℤ} (hrs : r ≠ s) :
    (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f (W.comap σ).subschemeι r).1 =
      0 := by
  apply Function.locallyFinsuppWithin.ext
  intro x
  change closedSubschemeCycleCoeff (fieldChowSituation k) f _ r x = 0
  unfold closedSubschemeCycleCoeff
  rw [dite_eq_right]
  rintro ⟨ξ, hξ, hδ⟩
  apply hrs
  rw [← hδ, ← hξ]
  exact relativeDimension_genericPoints_comap_eq k f σ hσ hD W s hηδ hWs ξ

end Purity

/-! ### The fibres of `W` over closed points -/

omit [IsVariety k f] in
/-- If `W` dominates `ℙ¹` and `ℙ¹` has two distinct points, then `W` is not contained in the
image of the section at a closed point. -/
theorem not_range_subschemeι_subset_range_closedPointSection
    (W : (projectiveLineProduct f).IdealSheafData)
    [IsDominant (W.subschemeι ≫
      pullback.snd f (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)))]
    {a b : relativeProjectiveLine (Spec (.of k))} (hab : a ≠ b)
    (c : relativeProjectiveLine (Spec (.of k))) (hc : IsClosed {c}) :
    ¬ Set.range W.subschemeι ⊆ Set.range (closedPointSection k rfl c hc f) := by
  intro hsub
  set q := pullback.snd f (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) with hq
  have hrange : Set.range (W.subschemeι ≫ q).base ⊆ {c} := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨x', hx'⟩ := hsub ⟨w, rfl⟩
    rw [Scheme.Hom.comp_apply, ← hx']
    exact snd_closedPointSection_apply k f c hc x'
  have huniv : (Set.univ : Set (relativeProjectiveLine (Spec (.of k)))) ⊆ {c} := by
    rw [← (W.subschemeι ≫ q).denseRange.closure_range]
    exact closure_minimal hrange hc
  exact hab ((huniv (Set.mem_univ a)).trans (huniv (Set.mem_univ b)).symm)

/-- If the generic point of `W` has relative dimension `s + 1` and `W` is not contained in the
section at `c`, every point of the fibre `W_c` has relative dimension at most `s`. -/
theorem relativeDimension_le_of_mem_support_comap_closedPointSection
    (W : (projectiveLineProduct f).IdealSheafData) [IsIntegral W.subscheme] (s : ℤ)
    (hηδ : relativeDimension (fieldChowSituation k).dimensionFunction
      (pullback.fst f (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) ≫ f)
      (W.subschemeι.base (genericPoint W.subscheme)) = s + 1)
    (c : relativeProjectiveLine (Spec (.of k))) (hc : IsClosed {c})
    (hWσ : ¬ Set.range W.subschemeι ⊆ Set.range (closedPointSection k rfl c hc f)) :
    ∀ w ∈ ((W.comap (closedPointSection k rfl c hc f)).support : Set X),
      relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ s := by
  intro w hw
  set pr := pullback.fst f (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) with hpr
  set η := W.subschemeι.base (genericPoint W.subscheme) with hη
  have hηcl : closure ({η} : Set (projectiveLineProduct f)) = W.support :=
    closure_singleton_subschemeι_genericPoint W
  have := isClosedImmersion_closedPointSection k f c hc
  rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, Set.mem_preimage, ← hηcl] at hw
  have hne : η ≠ (closedPointSection k rfl c hc f).base w := by
    intro h
    apply hWσ
    rw [Scheme.IdealSheafData.range_subschemeι, ← hηcl]
    exact closure_minimal (Set.singleton_subset_iff.mpr ⟨w, h.symm⟩)
      (closedPointSection k rfl c hc f).isClosedEmbedding.isClosed_range
  have hlt := relativeDimension_lt_of_specializes (fieldChowSituation k) (pr ≫ f)
    (specializes_iff_mem_closure.mpr hw) hne
  have hσf : closedPointSection k rfl c hc f ≫ pr ≫ f = f := by
    rw [← Category.assoc, closedPointSection_comp_fst, Category.id_comp]
  have h1 : relativeDimension (fieldChowSituation k).dimensionFunction (pr ≫ f)
      ((closedPointSection k rfl c hc f).base w) =
      relativeDimension (fieldChowSituation k).dimensionFunction f w :=
    relativeDimension_apply_of_section (fieldChowSituation k) f _ hσf w
  omega

omit [IsVariety k f] in
/-- A point specializing into the fibre over `c` does not lie on the section over `c' ≠ c`. -/
theorem notMem_range_closedPointSection_of_specializes
    {c c' : relativeProjectiveLine (Spec (.of k))} (hc : IsClosed {c}) (hc' : IsClosed {c'})
    (hcc' : c ≠ c') {z : projectiveLineProduct f} {x : X}
    (hzx : z ⤳ (closedPointSection k rfl c hc f).base x) :
    z ∉ Set.range (closedPointSection k rfl c' hc' f) := by
  rintro ⟨x', rfl⟩
  have := hzx.map
    (pullback.snd f (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k))).continuous
  rw [snd_closedPointSection_apply k f c' hc' x', snd_closedPointSection_apply k f c hc x] at this
  exact hcc' ((hc'.closure_eq ▸ this.mem_closure : c ∈ ({c'} : Set _)))

omit [IsAlgClosed k] in
/-- If `W` has dimension `s + 1`, its generic point has relative dimension `s + 1`. -/
theorem relativeDimension_genericPoint_eq_of_topologicalKrullDim
    (W : (projectiveLineProduct f).IdealSheafData) [IsIntegral W.subscheme] (s : ℕ)
    (hW : topologicalKrullDim (W.support : Set (projectiveLineProduct f)) =
      ((s + 1 : ℕ) : WithBot ℕ∞)) :
    relativeDimension (fieldChowSituation k).dimensionFunction
      (pullback.fst f (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) ≫ f)
      (W.subschemeι.base (genericPoint W.subscheme)) = (s : ℤ) + 1 := by
  have h := relativeDimension_eq_of_topologicalKrullDim_closure k
    (pullback.fst f (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) ≫ f)
    (W.subschemeι.base (genericPoint W.subscheme)) (s + 1)
    (by rw [closure_singleton_subschemeι_genericPoint W]; exact hW)
  rw [h]
  push_cast
  ring

omit [IsAlgClosed k] in
/-- If `V ∩ T` has dimension `≤ r + s - dX`, every point of it has relative dimension
`≤ r + s - dX`. -/
theorem relativeDimension_le_of_topologicalKrullDim_closure_inter_add_le (v : X) (r s dX : ℕ)
    {T : Set X} (hT : IsClosed T)
    (hVT : topologicalKrullDim (↥(closure ({v} : Set X) ∩ T)) + (dX : WithBot ℕ∞) ≤
      ((r + s : ℕ) : WithBot ℕ∞)) :
    ∀ w ∈ closure ({v} : Set X) ∩ T,
      relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ (r : ℤ) + s - dX := by
  intro w hw
  have h : relativeDimension (fieldChowSituation k).dimensionFunction f w + (dX : ℤ) ≤
      ((r + s : ℕ) : ℤ) :=
    relativeDimension_add_le_of_topologicalKrullDim_add_le k f (isClosed_closure.inter hT) hVT hw
  rw [Nat.cast_add] at h
  omega

omit [IsAlgClosed k] in
/-- A closed subscheme of `X × ℙ¹` has only finitely many generic points of its support. -/
theorem finite_setOf_generic_mem_support (J : (projectiveLineProduct f).IdealSheafData) :
    {z | z ∈ (J.support : Set (projectiveLineProduct f)) ∧
      ∀ z' ∈ (J.support : Set (projectiveLineProduct f)), z' ⤳ z → z' = z}.Finite := by
  set pr := pullback.fst f (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k))
  have : IsVariety k (f ≫ eqToHom (rfl : (fieldChowSituation k).S = Spec (.of k))) := by
    rw [eqToHom_refl, Category.comp_id]
    infer_instance
  have : CompactSpace (projectiveLineProduct f) :=
    compactSpace_projectiveLineProduct k (fieldChowSituation k) rfl f
  have : LocallyOfFiniteType (J.subschemeι ≫ pr ≫ f) := inferInstance
  have : IsLocallyNoetherian J.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (J.subschemeι ≫ pr ≫ f)
  have : CompactSpace J.subscheme := J.subschemeι.isClosedEmbedding.compactSpace
  have : IsNoetherian J.subscheme := ⟨⟩
  have hgen : (genericPoints J.subscheme).Finite :=
    genericPoints.finite (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents)
  refine (hgen.image J.subschemeι.base).subset fun z hz => ?_
  obtain ⟨w, hw⟩ := exists_genericPoints_subschemeι_eq_of_mem_componentGenericPointsThrough
    (fieldChowSituation k) f J (ξ := z) ⟨hz.1, specializes_refl z, hz.2⟩
  exact ⟨w.1, w.2, hw⟩

/-! ### Tag 0B60 -/

/-- **Stacks Project, Tag 0B60.** Let `X` be a nonsingular variety over an algebraically closed
field, of dimension `dX`. Let `W ⊆ X × ℙ¹` be a closed subvariety of dimension `s + 1` dominating
`ℙ¹`, let `a`, `b` be closed points of `ℙ¹` and let `W_a`, `W_b` be the fibres of `W` over them,
viewed as closed subschemes of `X`. Let `V ⊆ X` be the closure of a point `v`, of dimension `r`,
meeting `W_a` and `W_b` properly. Then `[V] · [W_a]_s ∼_rat [V] · [W_b]_s`. -/
@[stacks 0B60 "the whole lemma with the fibre cycles in their dimension `s`, as the proof and \
Tag 0B1V use it, at the source's own data: `X` a nonsingular variety over an \
algebraically closed field (the chapter's convention, Tag 0AZ8) of dimension `dX`, `W ⊆ X × P^1` \
an integral closed subscheme of dimension `s + 1` dominating `P^1`, `a`, `b` closed points of \
`P^1` with fibres `W_a`, `W_b` read in `X` as in Tag 0B07, and `V` the closure of a point of \
dimension `r` with `dim (V ∩ W_a)` and `dim (V ∩ W_b)` at most `r + s - dX`, the proper \
intersection of Tag 0AZQ written additively. The conclusion is that `[V] · [W_a]_s` and \
`[V] · [W_b]_s` are rationally equivalent (Tag 02RW), the products being those of Tag 0B08 in the \
integer expected dimension `r + s - dX`. The source prints `[W_a]_r`; the fibre has dimension \
`s`, and the statement as printed is \
`rationallyEquivalent_intersectionProduct_fibreCycle_dimension_r`."]
theorem rationallyEquivalent_intersectionProduct_fibreCycle [DecidableEq X] (hX : IsRegular X)
    (dX r s : ℕ) (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞))
    (W : (projectiveLineProduct f).IdealSheafData) [IsIntegral W.subscheme]
    (hW : topologicalKrullDim (W.support : Set (projectiveLineProduct f)) =
      ((s + 1 : ℕ) : WithBot ℕ∞))
    [IsDominant (W.subschemeι ≫
      pullback.snd f (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)))]
    (a b : relativeProjectiveLine (Spec (.of k))) (ha : IsClosed {a}) (hb : IsClosed {b})
    (v : X) (hv : topologicalKrullDim (closure ({v} : Set X)) = (r : WithBot ℕ∞))
    (hVa : topologicalKrullDim (↥(closure ({v} : Set X) ∩
        Set.range (W.comap (closedPointSection k rfl a ha f)).subschemeι)) +
        (dX : WithBot ℕ∞) ≤ ((r + s : ℕ) : WithBot ℕ∞))
    (hVb : topologicalKrullDim (↥(closure ({v} : Set X) ∩
        Set.range (W.comap (closedPointSection k rfl b hb f)).subschemeι)) +
        (dX : WithBot ℕ∞) ≤ ((r + s : ℕ) : WithBot ℕ∞)) :
    letI : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
    RationallyEquivalent (fieldChowSituation k) f ((r : ℤ) + s - dX)
      ⟨torFormulaCycleIntersectionProduct (fieldChowSituation k) f hX ((r : ℤ) + s - dX)
          (Function.locallyFinsuppWithin.single v 1)
          (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f
            (W.comap (closedPointSection k rfl a ha f)).subschemeι s).1,
        torFormulaCycleIntersectionProduct_mem_cyclesOfDimension
          (fieldChowSituation k) f hX _ _ _⟩
      ⟨torFormulaCycleIntersectionProduct (fieldChowSituation k) f hX ((r : ℤ) + s - dX)
          (Function.locallyFinsuppWithin.single v 1)
          (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f
            (W.comap (closedPointSection k rfl b hb f)).subschemeι s).1,
        torFormulaCycleIntersectionProduct_mem_cyclesOfDimension
          (fieldChowSituation k) f hX _ _ _⟩ := by
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
  classical
  -- the two sections
  set σa := closedPointSection k rfl a ha f with hσa
  set σb := closedPointSection k rfl b hb f with hσb
  by_cases hab : a = b
  · subst hab
    rw [RationallyEquivalent, sub_self]
    exact AddSubgroup.zero_mem _
  set pr := pullback.fst f (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) with hpr
  have : IsClosedImmersion σa := isClosedImmersion_closedPointSection k f a ha
  have : IsClosedImmersion σb := isClosedImmersion_closedPointSection k f b hb
  have hσaf : σa ≫ pr = 𝟙 X := closedPointSection_comp_fst k rfl a ha f
  have hσbf : σb ≫ pr = 𝟙 X := closedPointSection_comp_fst k rfl b hb f
  have hP : IsRegular (projectiveLineProduct f) := isRegular_projectiveLineProduct_of_eq f rfl hX
  have : IsLocallyNoetherian (projectiveLineProduct f) := isLocallyNoetherian_of_isRegular hP
  have : IsVariety k (f ≫ eqToHom (rfl : (fieldChowSituation k).S = Spec (.of k))) := by
    rw [eqToHom_refl, Category.comp_id]
    infer_instance
  -- the expected dimension
  set n : ℤ := (r : ℤ) + s - dX with hn
  have hrs : (r : ℤ) + s = (dX : ℤ) + n := by omega
  have hvδ : relativeDimension (fieldChowSituation k).dimensionFunction f v = r :=
    relativeDimension_eq_of_topologicalKrullDim_closure k f v r hv
  -- the generic point of `W`
  have hηδ := relativeDimension_genericPoint_eq_of_topologicalKrullDim k f W s hW
  -- `W` is not contained in a fibre
  have hWσ := not_range_subschemeι_subset_range_closedPointSection k f W hab
  -- `W_c` has dimension at most `s`
  have hWs := fun (c : relativeProjectiveLine (Spec (.of k))) (hc : IsClosed {c}) =>
    relativeDimension_le_of_mem_support_comap_closedPointSection k f W s hηδ c hc (hWσ c hc)
  -- `V ∩ W_c` has dimension at most `n`
  have hnc : ∀ (c : relativeProjectiveLine (Spec (.of k))) (hc : IsClosed {c}),
      topologicalKrullDim (↥(closure ({v} : Set X) ∩
        Set.range (W.comap (closedPointSection k rfl c hc f)).subschemeι)) +
        (dX : WithBot ℕ∞) ≤ ((r + s : ℕ) : WithBot ℕ∞) →
      ∀ w ∈ closure ({v} : Set X) ∩ ((W.comap (closedPointSection k rfl c hc f)).support : Set X),
        relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ n :=
      fun c hc hVc => relativeDimension_le_of_topologicalKrullDim_closure_inter_add_le k f v r s dX
        (W.comap (closedPointSection k rfl c hc f)).support.isClosed
        (by rwa [Scheme.IdealSheafData.range_subschemeι] at hVc)
  -- a bound for the dimensions
  obtain ⟨d₀, hd₀⟩ := exists_topologicalKrullDim_projectiveLineProduct_le k (fieldChowSituation k)
    rfl f
  set d := max d₀ dX with hd
  have hdP : topologicalKrullDim (projectiveLineProduct f) ≤ (d : WithBot ℕ∞) :=
    hd₀.trans (by exact_mod_cast le_max_left d₀ dX)
  have hdX' : topologicalKrullDim X ≤ (d : WithBot ℕ∞) :=
    hdX.le.trans (by exact_mod_cast le_max_right d₀ dX)
  -- the components of `(V × ℙ¹) ∩ W` entering the cycle `γ` of the source
  set J₀ := cylinderIdeal k f v ⊔ W with hJ₀
  set M : Set (projectiveLineProduct f) := {z | z ∈ (J₀.support : Set (projectiveLineProduct f)) ∧
    (∀ z' ∈ (J₀.support : Set (projectiveLineProduct f)), z' ⤳ z → z' = z) ∧
    relativeDimension (fieldChowSituation k).dimensionFunction (pr ≫ f) z = n + 1 ∧
    z ∉ Set.range σa ∧ z ∉ Set.range σb} with hM
  have hMfin : M.Finite :=
    (finite_setOf_generic_mem_support k f J₀).subset fun z hz => ⟨hz.1, hz.2.1⟩
  set Zf := hMfin.toFinset with hZf
  have hmemZf : ∀ z, z ∈ Zf ↔ z ∈ M := fun z => Set.Finite.mem_toFinset hMfin
  -- a point specializing into one fibre does not lie on the other
  have hZ₁ : ∀ z ∈ Zf, z ∈ (J₀.support : Set (projectiveLineProduct f)) :=
    fun z hz => ((hmemZf z).mp hz).1
  have hZa : ∀ z ∈ Zf, z ∉ Set.range σa := fun z hz => ((hmemZf z).mp hz).2.2.2.1
  have hZb : ∀ z ∈ Zf, z ∉ Set.range σb := fun z hz => ((hmemZf z).mp hz).2.2.2.2
  have hZδ : ∀ z ∈ Zf,
      relativeDimension (fieldChowSituation k).dimensionFunction (pr ≫ f) z = n + 1 :=
    fun z hz => ((hmemZf z).mp hz).2.2.1
  have hZ₃a : ∀ z : projectiveLineProduct f, z ∈ (J₀.support : Set (projectiveLineProduct f)) →
      (∀ z' ∈ (J₀.support : Set (projectiveLineProduct f)), z' ⤳ z → z' = z) →
      relativeDimension (fieldChowSituation k).dimensionFunction (pr ≫ f) z = n + 1 →
      z ∉ Set.range σa → (∃ x : X, z ⤳ σa x) → z ∈ Zf := by
    rintro z h1 h2 h3 h4 ⟨x, hzx⟩
    exact (hmemZf z).mpr
      ⟨h1, h2, h3, h4, notMem_range_closedPointSection_of_specializes k f ha hb hab hzx⟩
  have hZ₃b : ∀ z : projectiveLineProduct f, z ∈ (J₀.support : Set (projectiveLineProduct f)) →
      (∀ z' ∈ (J₀.support : Set (projectiveLineProduct f)), z' ⤳ z → z' = z) →
      relativeDimension (fieldChowSituation k).dimensionFunction (pr ≫ f) z = n + 1 →
      z ∉ Set.range σb → (∃ x : X, z ⤳ σb x) → z ∈ Zf := by
    rintro z h1 h2 h3 h4 ⟨x, hzx⟩
    exact (hmemZf z).mpr
      ⟨h1, h2, h3, notMem_range_closedPointSection_of_specializes k f hb ha (Ne.symm hab) hzx, h4⟩
  -- the identity behind the tag at each of the two fibres
  have hKa := torFormulaCycleIntersectionProduct_fibre_eq k f hX σa hσaf
    (isEffectiveCartierDivisor_ker_closedPointSection k f a ha) r s n dX hdX hrs v hvδ W
    (hWσ a ha) (hWs a ha) (hnc a ha hVa) d hdP hdX' Zf hZ₁ hZa hZ₃a
  have hKb := torFormulaCycleIntersectionProduct_fibre_eq k f hX σb hσbf
    (isEffectiveCartierDivisor_ker_closedPointSection k f b hb) r s n dX hdX hrs v hvδ W
    (hWσ b hb) (hWs b hb) (hnc b hb hVb) d hdP hdX' Zf hZ₁ hZb hZ₃b
  -- the difference is a finite sum of differences of fibre cycles of the components
  rw [RationallyEquivalent]
  have hdiff : (⟨torFormulaCycleIntersectionProduct (fieldChowSituation k) f hX n
          (Function.locallyFinsuppWithin.single v 1)
          (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f (W.comap σa).subschemeι s).1,
        torFormulaCycleIntersectionProduct_mem_cyclesOfDimension
          (fieldChowSituation k) f hX _ _ _⟩ - ⟨torFormulaCycleIntersectionProduct
          (fieldChowSituation k) f hX n (Function.locallyFinsuppWithin.single v 1)
          (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f (W.comap σb).subschemeι s).1,
        torFormulaCycleIntersectionProduct_mem_cyclesOfDimension
          (fieldChowSituation k) f hX _ _ _⟩ : CycleGroup (fieldChowSituation k) f n) =
      ∑ z ∈ Zf, componentWeight k f v W d z •
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f
            ((integralComponentAt z).comap σa).subschemeι n -
          cycleAssociatedToClosedSubscheme (fieldChowSituation k) f
            ((integralComponentAt z).comap σb).subschemeι n) := by
    apply Subtype.ext
    rw [AddSubgroup.coe_sub, AddSubgroup.val_finsetSum]
    change torFormulaCycleIntersectionProduct (fieldChowSituation k) f hX n
          (Function.locallyFinsuppWithin.single v 1)
          (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f (W.comap σa).subschemeι s).1 -
        torFormulaCycleIntersectionProduct (fieldChowSituation k) f hX n
          (Function.locallyFinsuppWithin.single v 1)
          (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f
            (W.comap σb).subschemeι s).1 = _
    rw [hKa, hKb, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [AddSubgroup.coe_zsmul, AddSubgroup.coe_sub, smul_sub]
  rw [hdiff]
  refine AddSubgroup.sum_mem _ fun z hz => AddSubgroup.zsmul_mem _ ?_ _
  have : IsIntegral (integralComponentAt z).subscheme := isIntegral_integralComponentAt z
  have hzr : z ∈ Set.range (integralComponentAt z).subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι, coe_support_integralComponentAt]
    exact subset_closure rfl
  exact sub_cycleAssociatedToClosedSubscheme_comap_mem_rationalEquivalences (fieldChowSituation k)
    f n (isPresentedSection_closedPointSection k f a ha)
    (isPresentedSection_closedPointSection k f b hb) (integralComponentAt z)
    (relativeDimension_familyBase_integralComponentAt_genericPoints (fieldChowSituation k) f z
      (hZδ z hz))
    (fun hsub => hZa z hz (hsub hzr)) (fun hsub => hZb z hz (hsub hzr))

/-- **Stacks Project, Tag 0B60, as printed.** The statement with the fibre cycles `[W_a]_r` and
`[W_b]_r` in the dimension `r` of `V`, as the source writes it. The fibres are pure of dimension
`s` (Tag 02RK), so for `r ≠ s` both cycles vanish, and for `r = s` this is
`Stacks.Intersection.RationalEquivalence.rationallyEquivalent_intersectionProduct_fibreCycle`. -/
@[stacks 0B60 "as printed, with `[W_a]_r` and `[W_b]_r`, the fibre cycles in the dimension `r` \
of `V`, the products being those of Tag 0B08 in the integer expected dimension `r + r - dX`; \
the data are those of `rationallyEquivalent_intersectionProduct_fibreCycle`, the fibres \
being pure of dimension `s` by Tag 02RK."]
theorem rationallyEquivalent_intersectionProduct_fibreCycle_dimension_r [DecidableEq X]
    (hX : IsRegular X)
    (dX r s : ℕ) (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞))
    (W : (projectiveLineProduct f).IdealSheafData) [IsIntegral W.subscheme]
    (hW : topologicalKrullDim (W.support : Set (projectiveLineProduct f)) =
      ((s + 1 : ℕ) : WithBot ℕ∞))
    [IsDominant (W.subschemeι ≫
      pullback.snd f (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)))]
    (a b : relativeProjectiveLine (Spec (.of k))) (ha : IsClosed {a}) (hb : IsClosed {b})
    (v : X) (hv : topologicalKrullDim (closure ({v} : Set X)) = (r : WithBot ℕ∞))
    (hVa : topologicalKrullDim (↥(closure ({v} : Set X) ∩
        Set.range (W.comap (closedPointSection k rfl a ha f)).subschemeι)) +
        (dX : WithBot ℕ∞) ≤ ((r + s : ℕ) : WithBot ℕ∞))
    (hVb : topologicalKrullDim (↥(closure ({v} : Set X) ∩
        Set.range (W.comap (closedPointSection k rfl b hb f)).subschemeι)) +
        (dX : WithBot ℕ∞) ≤ ((r + s : ℕ) : WithBot ℕ∞)) :
    letI : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
    RationallyEquivalent (fieldChowSituation k) f ((r : ℤ) + r - dX)
      ⟨torFormulaCycleIntersectionProduct (fieldChowSituation k) f hX ((r : ℤ) + r - dX)
          (Function.locallyFinsuppWithin.single v 1)
          (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f
            (W.comap (closedPointSection k rfl a ha f)).subschemeι r).1,
        torFormulaCycleIntersectionProduct_mem_cyclesOfDimension
          (fieldChowSituation k) f hX _ _ _⟩
      ⟨torFormulaCycleIntersectionProduct (fieldChowSituation k) f hX ((r : ℤ) + r - dX)
          (Function.locallyFinsuppWithin.single v 1)
          (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f
            (W.comap (closedPointSection k rfl b hb f)).subschemeι r).1,
        torFormulaCycleIntersectionProduct_mem_cyclesOfDimension
          (fieldChowSituation k) f hX _ _ _⟩ := by
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
  by_cases hrs : r = s
  · subst hrs
    exact rationallyEquivalent_intersectionProduct_fibreCycle k f hX dX r r hdX W hW a b ha hb v
      hv hVa hVb
  by_cases hab : a = b
  · subst hab
    rw [RationallyEquivalent, sub_self]
    exact AddSubgroup.zero_mem _
  have hηδ := relativeDimension_genericPoint_eq_of_topologicalKrullDim k f W s hW
  have hWσ := not_range_subschemeι_subset_range_closedPointSection k f W hab
  have hWs := fun (c : relativeProjectiveLine (Spec (.of k))) (hc : IsClosed {c}) =>
    relativeDimension_le_of_mem_support_comap_closedPointSection k f W s hηδ c hc (hWσ c hc)
  have hzero : ∀ (c : relativeProjectiveLine (Spec (.of k))) (hc : IsClosed {c}),
      (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f
        (W.comap (closedPointSection k rfl c hc f)).subschemeι r).1 = 0 := by
    intro c hc
    have := isClosedImmersion_closedPointSection k f c hc
    exact cycleAssociatedToClosedSubscheme_comap_eq_zero k f _
      (closedPointSection_comp_fst k rfl c hc f)
      (isEffectiveCartierDivisor_ker_closedPointSection k f c hc) W s hηδ (hWs c hc)
      (by exact_mod_cast hrs)
  have heq : (⟨torFormulaCycleIntersectionProduct (fieldChowSituation k) f hX ((r : ℤ) + r - dX)
          (Function.locallyFinsuppWithin.single v 1)
          (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f
            (W.comap (closedPointSection k rfl a ha f)).subschemeι r).1,
        torFormulaCycleIntersectionProduct_mem_cyclesOfDimension
          (fieldChowSituation k) f hX _ _ _⟩ : CycleGroup (fieldChowSituation k) f _) =
      ⟨torFormulaCycleIntersectionProduct (fieldChowSituation k) f hX ((r : ℤ) + r - dX)
          (Function.locallyFinsuppWithin.single v 1)
          (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f
            (W.comap (closedPointSection k rfl b hb f)).subschemeι r).1,
        torFormulaCycleIntersectionProduct_mem_cyclesOfDimension
          (fieldChowSituation k) f hX _ _ _⟩ := by
    apply Subtype.ext
    change torFormulaCycleIntersectionProduct (fieldChowSituation k) f hX ((r : ℤ) + r - dX)
          (Function.locallyFinsuppWithin.single v 1)
          (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f
            (W.comap (closedPointSection k rfl a ha f)).subschemeι r).1 =
        torFormulaCycleIntersectionProduct (fieldChowSituation k) f hX ((r : ℤ) + r - dX)
          (Function.locallyFinsuppWithin.single v 1)
          (cycleAssociatedToClosedSubscheme (fieldChowSituation k) f
            (W.comap (closedPointSection k rfl b hb f)).subschemeι r).1
    rw [hzero a ha, hzero b hb]
  rw [RationallyEquivalent, heq, sub_self]
  exact AddSubgroup.zero_mem _

end Stacks.Intersection.RationalEquivalence

end
