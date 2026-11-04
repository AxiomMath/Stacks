module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.PointClassDegree
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# Rational points of a geometrically irreducible scheme induce the same map on `H^0`

Let `W` be data (D0)–(D3) satisfying (A), (B), (C) (`Stacks.WeilCohomology.WeilData`), let
`L/k` be a finite separable extension and `Y` a geometrically irreducible smooth projective
scheme over `L`, viewed over `k`. This file proves the step of the source's proof of Stacks 0FI0
which says that, once the points are `L`-rational, "by axiom (A)(b) all the maps
`H^0(Y) → H^0(yᵢ)` are the same":

* by the rational-point step of Stacks 0FHV
  (`Stacks.WeilCohomology.WeilData.cycleClass_rationalPointClass_eq_of_relativeDimension`) two
  `L`-rational points `y, y'` of `Y` have `γ([y]) = γ([y'])` in `H^{2d}(Y)(d)`;
* by Stacks 0FHG and 0FHQ (4)
  (`Stacks.WeilCohomology.WeilData.h0Pairing_cycleClass_closedSubschemeClass`)
  `∫_Y a ∪ γ([y]) = Tr_{H^0(Spec L)/F}(y^* a)` for `a ∈ H^0(Y)`;
* applying this to `a ∪ q^* c` for `c ∈ H^0(Spec L)`, `q : Y ⟶ Spec L` the structure morphism,
  gives `Tr(y^* a ∪ c) = Tr(y'^* a ∪ c)` for all `c`, whence `y^* a = y'^* a` by Poincaré duality
  (A)(b) on `Spec L` (`Stacks.WeilCohomology.WeilData.eq_of_traceZero_mul_eq`).

Consequently, if the pullbacks to finitely many `L`-rational points are jointly injective on
`H^0(Y)`, then `q^* : H^0(Spec L) → H^0(Y)` is an isomorphism
(`Stacks.WeilCohomology.WeilData.bijective_pullHom_toSpec_of_injective`).

## Main results

* `Stacks.WeilCohomology.WeilData.pullHom_ofOverFieldSection_eq`.
* `Stacks.WeilCohomology.WeilData.bijective_pullHom_toSpec_of_injective`.

## References

* [Stacks Project, Tag 0FI0](https://stacks.math.columbia.edu/tag/0FI0)
* [Stacks Project, Tag 0FHV](https://stacks.math.columbia.edu/tag/0FHV)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Chow

universe u w

namespace Stacks.WeilCohomology

open SmoothProjectiveScheme

variable {k : Type u} [Field k]

section OverExtension

variable {L : Type u} [Field L] [Algebra k L] [FiniteDimensional k L] [Algebra.IsSeparable k L]
  {Y : Scheme.{u}} (q : Y ⟶ (fieldChowSituation L).S) [Smooth q] (hq : IsProjectiveMorphism q)

/-- **An `L`-rational point `y` of `Y`**, a section of `q : Y ⟶ Spec L`, as a morphism
`Spec L ⟶ Y` of smooth projective `k`-schemes. -/
def ofOverFieldSection (y : (fieldChowSituation L).S ⟶ Y) (hy : y ≫ q = 𝟙 _) :
    specField (k := k) L ⟶ ofOverField (k := k) q hq :=
  specFieldHom y (by
    change y ≫ q ≫ specStructure k L = specStructure k L
    rw [← Category.assoc, hy, Category.id_comp])

/-- The underlying scheme morphism of `ofOverFieldSection q hq y hy` is `y`. -/
@[simp]
theorem ofOverFieldSection_left (y : (fieldChowSituation L).S ⟶ Y) (hy : y ≫ q = 𝟙 _) :
    (ofOverFieldSection (k := k) q hq y hy).hom.left = y :=
  rfl

/-- **The structure morphism `q : Y ⟶ Spec L`**, as a morphism of smooth projective `k`-schemes. -/
abbrev ofOverFieldToSpec : ofOverField (k := k) q hq ⟶ specField (k := k) L :=
  haveI := etale_of_isSeparable (k := k) L
  toSpec k q hq

/-- The morphism `ofOverFieldSection q hq y hy` is a section of `ofOverFieldToSpec q hq`. -/
theorem ofOverFieldSection_comp_toSpec (y : (fieldChowSituation L).S ⟶ Y) (hy : y ≫ q = 𝟙 _) :
    ofOverFieldSection (k := k) q hq y hy ≫ ofOverFieldToSpec q hq = 𝟙 _ :=
  hom_ext_left hy

end OverExtension

namespace WeilData

variable {F : Type w} [Field F] {W : WeilData k F}
variable {L : Type u} [Field L] [Algebra k L] [FiniteDimensional k L] [Algebra.IsSeparable k L]

/-- The pullback along a rational point followed by the pullback along `q` is the identity. -/
private theorem pullHom_section_comp_pullHom_toSpec {Y : Scheme.{u}}
    (q : Y ⟶ (fieldChowSituation L).S) [Smooth q] (hq : IsProjectiveMorphism q)
    (z : (fieldChowSituation L).S ⟶ Y) (hz : z ≫ q = 𝟙 _) :
    (H0.pullHom W (ofOverFieldSection (k := k) q hq z hz)).comp
      (H0.pullHom W (ofOverFieldToSpec (k := k) q hq)) = AlgHom.id F _ :=
  W.pullHom_comp_pullHom_of_comp_eq_id _ _ (ofOverFieldSection_comp_toSpec q hq z hz)

/-- The total space of a geometrically irreducible scheme over `Spec L` is irreducible. -/
private theorem irreducibleSpace_of_geometricallyIrreducible {Y : Scheme.{u}}
    (q : Y ⟶ (fieldChowSituation L).S) [GeometricallyIrreducible q] : IrreducibleSpace Y :=
  haveI : Subsingleton (Spec (.of L)) := inferInstanceAs (Subsingleton (PrimeSpectrum L))
  GeometricallyIrreducible.irreducibleSpace_of_subsingleton q

/-- **The pullbacks along two `L`-rational points agree on `H^0`** for a geometrically irreducible
smooth projective scheme `Y` over a finite separable extension `L/k`. -/
theorem pullHom_ofOverFieldSection_eq [CharZero F] (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing) {Y : Scheme.{u}} (q : Y ⟶ (fieldChowSituation L).S)
    [Smooth q] [GeometricallyIrreducible q] (hq : IsProjectiveMorphism q)
    (y y' : (fieldChowSituation L).S ⟶ Y) (hy : y ≫ q = 𝟙 _) (hy' : y' ≫ q = 𝟙 _) :
    H0.pullHom W (ofOverFieldSection (k := k) q hq y hy) =
      H0.pullHom W (ofOverFieldSection (k := k) q hq y' hy') := by
  have := irreducibleSpace_of_geometricallyIrreducible (L := L) q
  obtain ⟨d, hd⟩ := exists_relativeDimension_of_irreducibleSpace q
  have : Nonempty Y := ⟨y (genericPoint (Spec (.of L)))⟩
  have hYd := isNonemptyEquidimensional_ofOverField (k := k) q hq hd
  have hZ := isNonemptyEquidimensional_specField (k := k) L
  have htr : ∀ c : W.H0 (specField (k := k) L),
      W.trace _ 0 hZ (W.h0TwEquiv _ c) = Algebra.trace F _ c := fun c ↦
    traceZero_eq_trace hA hB hC (topologicalKrullDim_eq_zero_of_isNonemptyEquidimensional hZ) c
  have hγ := W.cycleClass_rationalPointClass_eq_of_relativeDimension hA hB hC q hq hd y y' hy hy'
  have key : ∀ (z : (fieldChowSituation L).S ⟶ Y) (hz : z ≫ q = 𝟙 _)
      (a : W.H0 (ofOverField (k := k) q hq)),
      W.h0Pairing _ d hYd a (W.cycleClass _ d (rationalPointClass (k := k) q hq z hz d)) =
        Algebra.trace F _ (H0.pullHom W (ofOverFieldSection (k := k) q hq z hz) a) := by
    intro z hz a
    have : IsClosedImmersion (ofOverFieldSection (k := k) q hq z hz).hom.left :=
      isClosedImmersion_of_comp_eq_id q z hz
    exact W.h0Pairing_cycleClass_closedSubschemeClass hA hB hC
      (ofOverFieldSection (k := k) q hq z hz) hYd hZ htr a
  ext a
  set u := H0.pullHom W (ofOverFieldSection (k := k) q hq y hy) a
  set u' := H0.pullHom W (ofOverFieldSection (k := k) q hq y' hy') a
  have hmul : ∀ c, Algebra.trace F _ (u * c) = Algebra.trace F _ (u' * c) := by
    intro c
    have e : ∀ (z : (fieldChowSituation L).S ⟶ Y) (hz : z ≫ q = 𝟙 _),
        H0.pullHom W (ofOverFieldSection (k := k) q hq z hz) a * c =
          H0.pullHom W (ofOverFieldSection (k := k) q hq z hz)
            (a * H0.pullHom W (ofOverFieldToSpec (k := k) q hq) c) := fun z hz ↦ by
      rw [map_mul, ← AlgHom.comp_apply, pullHom_section_comp_pullHom_toSpec, AlgHom.id_apply]
    rw [e y hy, e y' hy', ← key, ← key, hγ]
  have huu : (u : W.H _) = u' := eq_of_traceZero_mul_eq hA.perfectPairing hZ u.2 u'.2
    (fun c hc ↦ by
      have h1 := htr ⟨c * u, mul_mem_grade_zero hc u.2⟩
      have h2 := htr ⟨c * u', mul_mem_grade_zero hc u'.2⟩
      have h3 := hmul ⟨c, hc⟩
      rw [mul_comm u, mul_comm u'] at h3
      exact h1.trans (h3.trans h2.symm))
  exact congrArg Subtype.val (Subtype.ext huu)

/-- **If the pullbacks to finitely many `L`-rational points are jointly injective on `H^0(Y)`,
then `H^0(Spec L) → H^0(Y)` is an isomorphism**, for `Y` geometrically irreducible smooth
projective over `L`. -/
theorem bijective_pullHom_toSpec_of_injective [CharZero F] (hA : W.PoincareDuality)
    (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing) {Y : Scheme.{u}}
    (q : Y ⟶ (fieldChowSituation L).S) [Smooth q] [GeometricallyIrreducible q]
    (hq : IsProjectiveMorphism q) {ι : Type*} (y : ι → ((fieldChowSituation L).S ⟶ Y))
    (hy : ∀ i, y i ≫ q = 𝟙 _)
    (hinj : Function.Injective fun a : W.H0 (ofOverField (k := k) q hq) ↦
      fun i ↦ H0.pullHom W (ofOverFieldSection (k := k) q hq (y i) (hy i)) a) :
    Function.Bijective (H0.pullHom W (ofOverFieldToSpec (k := k) q hq)) := by
  have hsec := fun i ↦ pullHom_section_comp_pullHom_toSpec (W := W) (k := k) q hq (y i) (hy i)
  have hall : ∀ i j, H0.pullHom W (ofOverFieldSection (k := k) q hq (y i) (hy i)) =
      H0.pullHom W (ofOverFieldSection (k := k) q hq (y j) (hy j)) := fun i j ↦
    pullHom_ofOverFieldSection_eq hA hB hC q hq (y i) (y j) (hy i) (hy j)
  by_cases hι : Nonempty ι
  swap
  · exfalso
    rw [not_nonempty_iff] at hι
    have h1 : (1 : W.H0 (ofOverField (k := k) q hq)) = 0 :=
      hinj (funext fun i ↦ (IsEmpty.false i).elim)
    have := irreducibleSpace_of_geometricallyIrreducible (L := L) q
    have : Nonempty (ofOverField (k := k) q hq).obj.left := IrreducibleSpace.toNonempty (X := Y)
    have := nontrivial_of_nonempty hA hB hC (ofOverField (k := k) q hq)
    exact one_ne_zero (congrArg Subtype.val h1)
  obtain ⟨i⟩ := hι
  refine ⟨fun c c' hcc ↦ ?_, fun a ↦ ?_⟩
  · have := congrArg (H0.pullHom W (ofOverFieldSection (k := k) q hq (y i) (hy i))) hcc
    rwa [← AlgHom.comp_apply, hsec i, ← AlgHom.comp_apply, hsec i] at this
  · refine ⟨H0.pullHom W (ofOverFieldSection (k := k) q hq (y i) (hy i)) a,
      hinj (funext fun j ↦ ?_)⟩
    show (H0.pullHom W (ofOverFieldSection (k := k) q hq (y j) (hy j))).comp
        (H0.pullHom W (ofOverFieldToSpec (k := k) q hq))
        (H0.pullHom W (ofOverFieldSection (k := k) q hq (y i) (hy i)) a) = _
    rw [hsec j, AlgHom.id_apply, hall i j]

end WeilData

end Stacks.WeilCohomology
