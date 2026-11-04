module

public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.ComplexFunctoriality
public import StacksFrontier.RingTheory.DeRham.LogPolesComplex

/-!
# The descent datum of the de Rham complex of log poles

Let `A → R` be a ring map and let `t ∈ R` cut out an effective Cartier divisor `Y ⊆ X = Spec R`.
`Stacks.LogPoles.logComplex` builds the complex `Ω^•_{X/S}(log Y)` from the *chosen equation* `t`,
and the proof of Stacks Tag 0FMW glues those local complexes into a complex of sheaves. Gluing
needs three pieces of data, and two of them are constructed elsewhere:

* **restriction maps** along a tower `R → R'` carrying `t` to its image,
  `Stacks.LogPoles.logComplexTowerMap`;
* **transition isomorphisms** between the complexes of two equations `s = u · t` of one divisor,
  `Stacks.LogPoles.logComplexUnitIso`.

Neither alone is a presheaf: on a smaller affine open the *chosen* equation `t'` is not the image
of `t`, only a unit multiple of it, so the restriction map of the glued object is the composite

`Ω^•(log Y)(t) → Ω^•(log Y)(t|_{R'}) → Ω^•(log Y)(t')`

of a tower map with a transition isomorphism. This file supplies that composite, and the
**cocycle law** for it, which is the third piece: the composite restriction maps of a tower
`R → R' → R''` compose to the composite restriction map of `R → R''`. With it the descent datum
of Stacks Tag 0FMW is complete at the level of rings.

Nothing here is a sheaf: see the implementation notes for what still blocks the globalization.

## Main definitions

* `Stacks.LogPoles.logComplexRestrict`: **the restriction map of the descent datum**, for a tower
  `R → R'` of `A`-algebras and equations `t ∈ R`, `t' ∈ R'` of the same divisor, related by
  `t' = w · t|_{R'}` with `w` a unit of `R'`.

## Main results

* `Stacks.LogPoles.logComplexRestrict_comp`: **the cocycle law** — the restriction maps compose
  along a tower, with the unit of the composite the product of the two units. This is the
  presheaf law that neither `logComplexTowerMap_comp` (which fixes the equation) nor
  `logComplexUnitIso` (which fixes the ring) states.
* `Stacks.LogPoles.logComplexUnitHom_comp_logComplexTowerMap`: the compatibility square of the
  two given pieces of data, that a tower map commutes with the change of equation. This is what
  makes the cocycle law hold.
* `Stacks.LogPoles.exists_unit_mul_of_span_singleton_eq`: two generators of one principal ideal
  whose generator is a nonzerodivisor differ by a unit, so the unit `w` above exists and is
  determined by the two equations.
* `Stacks.LogPoles.exists_logComplexRestrict`: consequently a restriction map exists for any two
  local equations of one divisor, compatibly with the inclusion of the forms with no pole.
* `Stacks.LogPoles.logIncl_comp_logComplexRestrict` and
  `Stacks.LogPoles.injective_logIncl_comp_logComplexRestrict_f`: the restriction map carries the
  forms with no pole to the forms with no pole, injectively whenever the maps of relative forms
  are injective — as they are for a localization. So neither the datum nor its terms has
  collapsed.

## Implementation notes

The unit of the composite is `Units.map (algebraMap R' R'') w' * w''` and not `w' * w''`: the
first unit lives in `R'` and has to be pushed to `R''` before the two can be multiplied. That is
the only arithmetic in the cocycle law; everything else is the pair-model computation

`(ω, η) ↦ (ω + dlog u ∧ η, η)`,

whose own composition law is `Stacks.LogPoles.logPairUnit_mul`, deduced from
`dlog (u v) = dlog u + dlog v`.

### What still blocks the globalization

With the datum complete, the route through Stacks Tags 009T and 009U — restriction of module
sheaves to a basis is an equivalence, `Stacks.BasisRestriction.isEquivalence_restrictModuleSheaf`
— is still not available, for two reasons that are about the *interface* and not about the datum.

1. The basis datum that `Stacks.BasisRestriction.extModuleSheaf` consumes is a bundled
   `SheafOfModules` over the restriction of the sheaf of rings to the basis, so its terms are
   modules over `(f^{-1}𝒪_S)|_B`. The complex here is a complex in `ModuleCat.{u} A` for one
   fixed base ring `A`. Converting one into the other needs the sections of `Ω^p_{X/S}` over an
   affine open `U = Spec R` lying over an affine open `V = Spec A` to be identified with
   `⋀[R]^p (Ω[R⁄A])`. That identification is Stacks Tag 0FLW, which the library has only for a
   morphism that is globally `Spec φ`, only degreewise, and with no transport of the differential
   above degree zero — as `StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.DeRhamSections`
   records of itself.
2. The hypotheses the datum needs on each affine open are
   `∀ p, IsSMulRegular (⋀[R]^p (Ω[R⁄A])) t` and a retraction of `g ↦ g · dt`. Stacks Tag 0FMV,
   `AlgebraicGeometry.Scheme.Hom.HasLogPolesDeRhamComplex`, asserts both only at the *stalks* of
   the points of the divisor, and the only sheaf-to-ring crossing in the tree,
   `AlgebraicGeometry.Scheme.Hom.hasLogPolesDeRhamComplex_of_smooth`, also lands in stalks and
   derives the ring hypotheses from smoothness rather than from the predicate. A local-to-global
   step from stalk regularity to regularity on the sections of an affine open has no precedent
   here.

## References

* [Stacks Project, Tag 0FMW](https://stacks.math.columbia.edu/tag/0FMW), whose proof glues the
  complexes of the local equations; this file is its gluing datum, in the ring-level form
* [Stacks Project, Tag 0FMV](https://stacks.math.columbia.edu/tag/0FMV), the hypothesis under
  which the complex of log poles is defined
* [Stacks Project, Tag 0FUA](https://stacks.math.columbia.edu/tag/0FUA), the complex itself
* [Stacks Project, Tag 009T](https://stacks.math.columbia.edu/tag/009T) and
  [Stacks Project, Tag 009U](https://stacks.math.columbia.edu/tag/009U), the descent of module
  sheaves along a basis
* [Stacks Project, Tag 0FLW](https://stacks.math.columbia.edu/tag/0FLW), the affine local
  description of the de Rham complex, which the globalization of this datum still needs
-/

@[expose] public noncomputable section

open CategoryTheory KaehlerDifferential

universe u

namespace Stacks.LogPoles

/-- Two maps of complexes of log poles agree if they agree in degree zero and on the classes of
pairs in positive degrees. -/
private theorem logComplex_hom_ext {A R R' : Type u} [CommRing A] [CommRing R] [CommRing R']
    [Algebra A R] [Algebra A R'] {t : R} {t' : R'}
    {ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t}
    {ht' : ∀ p : ℕ, IsSMulRegular (↥(⋀[R']^p (Ω[R'⁄A]))) t'}
    {f g : logComplex ht ⟶ logComplex ht'}
    (h0 : ∀ ω, (f.f 0).hom ω = (g.f 0).hom ω)
    (hsucc : ∀ (q : ℕ) (x : ⋀[R]^(q + 1) (Ω[R⁄A]) × ⋀[R]^q (Ω[R⁄A])),
      (f.f (q + 1)).hom
          (Submodule.Quotient.mk (p := Submodule.restrictScalars A (logRel A t q)) x) =
        (g.f (q + 1)).hom
          (Submodule.Quotient.mk (p := Submodule.restrictScalars A (logRel A t q)) x)) :
    f = g := by
  ext p : 1
  cases p with
  | zero => exact ModuleCat.hom_ext (LinearMap.ext h0)
  | succ q =>
      ext z
      obtain ⟨z, rfl⟩ : ∃ y : (⋀[R]^(q + 1) (Ω[R⁄A]) × ⋀[R]^q (Ω[R⁄A])) ⧸
          Submodule.restrictScalars A (logRel A t q), y = z := ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      exact hsucc q x

/-! ### Two equations of one principal divisor -/

section Generators

variable {R : Type u} [CommRing R]

/-- **Two equations of one effective Cartier divisor differ by a unit.**  If `(s) = (t)` as ideals
and `t` is a nonzerodivisor then `s = u · t` for a unit `u`: writing `s = x t` and `t = y s` gives
`t = y x t`, so `y x = 1`.  This is what makes the unit appearing in the restriction map of the
descent datum below exist, and determines it. -/
theorem exists_unit_mul_of_span_singleton_eq {t s : R} (ht : IsSMulRegular R t)
    (h : Ideal.span {s} = Ideal.span {t}) : ∃ u : Rˣ, s = (u : R) * t := by
  obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.mp (h ▸ Ideal.mem_span_singleton_self s)
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp (h.symm ▸ Ideal.mem_span_singleton_self t)
  have hyx : y * x = 1 := by
    refine ht ?_
    show t • (y * x) = t • (1 : R)
    rw [smul_eq_mul, smul_eq_mul, mul_one]
    calc t * (y * x) = y * (x * t) := by ring
      _ = y * s := by rw [hx]
      _ = t := hy
  exact ⟨⟨x, y, by rw [mul_comm]; exact hyx, hyx⟩, hx.symm⟩

end Generators

/-! ### The change of equation is multiplicative in the unit -/

section Unit

variable {A R : Type u} [CommRing A] [CommRing R] [Algebra A R]

/-- **`dlog` is multiplicative**: `dlog (u v) = dlog u + dlog v` for units `u`, `v` of `R`.  This
is the Leibniz rule `d(u v) = u dv + v du` divided by `u v`. -/
theorem dlogUnit_mul (u v : Rˣ) :
    dlogUnit A (u * v) = dlogUnit A u + dlogUnit A v := by
  have key : ∀ a b : Rˣ, (↑(a * b)⁻¹ : R) * (a : R) = (↑b⁻¹ : R) := by
    intro a b; rw [← Units.val_mul]; congr 1; group
  have h1 := key u v
  have h2 : (↑(u * v)⁻¹ : R) * (v : R) = (↑u⁻¹ : R) := by
    rw [mul_comm u v]; exact key v u
  have hl := (KaehlerDifferential.D A R).leibniz (u : R) (v : R)
  rw [dlogUnit, dlogUnit, dlogUnit, Units.val_mul, hl, smul_add, smul_smul, smul_smul, h1, h2]
  exact add_comm _ _

/-- **The changes of equation compose**: changing the equation by `u` and then by `v` is changing
it by `u v`, because `dlog` is multiplicative. -/
theorem logPairUnit_mul (u v : Rˣ) (p : ℕ)
    (x : ⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])) :
    logPairUnit A v p (logPairUnit A u p x) = logPairUnit A (u * v) p x := by
  rw [logPairUnit_apply, logPairUnit_apply, logPairUnit_apply]
  refine Prod.ext ?_ rfl
  rw [dlogUnit_mul, exteriorPower.wedgeLeft_add, LinearMap.add_apply, add_assoc]

/-- **The comparisons of the complexes of log poles for a change of equation compose.**  For
equations `w = v · s` and `s = u · t` of one divisor the two comparisons compose to the
comparison for `w = (u v) · t`. -/
theorem logComplexUnitHom_comp {t s w : R} (u v : Rˣ) (hs : s = (u : R) * t)
    (hw : w = (v : R) * s)
    (hw' : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) w)
    (hs' : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) s)
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t) :
    logComplexUnitHom v hw hw' hs' ≫ logComplexUnitHom u hs hs' ht =
      logComplexUnitHom (u * v)
        (show w = (↑(u * v) : R) * t by rw [hw, hs, Units.val_mul]; ring) hw' ht := by
  refine logComplex_hom_ext (fun _ => rfl) fun q x => ?_
  show Submodule.Quotient.mk (p := Submodule.restrictScalars A (logRel A t q))
      (logPairUnit A u q (logPairUnit A v q x)) =
    Submodule.Quotient.mk (p := Submodule.restrictScalars A (logRel A t q))
      (logPairUnit A (u * v) q x)
  rw [logPairUnit_mul, mul_comm v u]

end Unit

/-! ### The restriction map of the descent datum -/

section Restrict

variable {A R R' : Type u} [CommRing A] [CommRing R] [CommRing R']
  [Algebra A R] [Algebra A R'] [Algebra R R'] [IsScalarTower A R R']

/-- **A tower map commutes with a change of equation.**  The pair-model comparison for a unit `u`
of `R` is carried by the map of relative forms to the comparison for the image unit, because the
map of relative forms carries `dlog u` to `dlog (u|_{R'})`.  This is the compatibility of the two
given pieces of the descent datum, and the ingredient the cocycle law needs. -/
theorem logPairTowerMap_logPairUnit (u : Rˣ) (p : ℕ)
    (x : ⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])) :
    logPairTowerMap A R R' p (logPairUnit A u p x) =
      logPairUnit A (Units.map (algebraMap R R' : R →* R') u) p
        (logPairTowerMap A R R' p x) := by
  have hmap : ∀ (v : Rˣ) (q : ℕ) (η : ⋀[R]^q (Ω[R⁄A])),
      mapExteriorPower A R R' (q + 1) (exteriorPower.wedgeLeft (dlogUnit A v) q η) =
        exteriorPower.wedgeLeft (dlogUnit A (Units.map (algebraMap R R' : R →* R') v)) q
          (mapExteriorPower A R R' q η) := by
    intro v q η
    rw [mapExteriorPower_wedgeLeft]
    congr 1
    rw [dlogUnit, dlogUnit, map_smul, KaehlerDifferential.map_D, Units.coe_map_inv, Units.coe_map]
    simp only [MonoidHom.coe_coe]
    rw [algebraMap_smul]
  rw [logPairUnit_apply, logPairTowerMap_apply, logPairTowerMap_apply, logPairUnit_apply]
  refine Prod.ext ?_ rfl
  rw [map_add, hmap]

omit [Algebra A R] [IsScalarTower A R R'] in
/-- The image of `t` is the chosen equation `t'` divided by the unit relating them. -/
theorem algebraMap_eq_inv_unit_mul {t : R} {t' : R'} (w : R'ˣ)
    (hw : t' = (w : R') * algebraMap R R' t) :
    algebraMap R R' t = (↑w⁻¹ : R') * t' := by
  rw [hw, ← mul_assoc, Units.inv_mul, one_mul]

omit [Algebra A R] [IsScalarTower A R R'] in
/-- Torsion freeness for the chosen equation gives it for the image equation, the two differing
by a unit. -/
theorem isSMulRegular_algebraMap_of_unit_mul {t : R} {t' : R'} (w : R'ˣ)
    (hw : t' = (w : R') * algebraMap R R' t)
    (ht' : ∀ p : ℕ, IsSMulRegular (↥(⋀[R']^p (Ω[R'⁄A]))) t') (p : ℕ) :
    IsSMulRegular (↥(⋀[R']^p (Ω[R'⁄A]))) (algebraMap R R' t) := by
  rw [algebraMap_eq_inv_unit_mul w hw, isSMulRegular_unit_mul_iff]
  exact ht' p

/-- **The compatibility square of the two given pieces of the descent datum**, at the level of
complexes: the comparison of the complexes of two equations `s = u · t` of one divisor, followed
by the tower map of `R → R'`, is the tower map followed by the comparison for the image unit. -/
theorem logComplexUnitHom_comp_logComplexTowerMap {t s : R} (u : Rˣ) (hs : s = (u : R) * t)
    (hs' : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) s)
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (hφs : ∀ p : ℕ, IsSMulRegular (↥(⋀[R']^p (Ω[R'⁄A]))) (algebraMap R R' s))
    (hφt : ∀ p : ℕ, IsSMulRegular (↥(⋀[R']^p (Ω[R'⁄A]))) (algebraMap R R' t)) :
    logComplexUnitHom u hs hs' ht ≫ logComplexTowerMap rfl ht hφt =
      logComplexTowerMap rfl hs' hφs ≫
        logComplexUnitHom (Units.map (algebraMap R R' : R →* R') u)
          (show algebraMap R R' s =
              (↑(Units.map (algebraMap R R' : R →* R') u) : R') * algebraMap R R' t by
            rw [hs, map_mul, Units.coe_map]; rfl) hφs hφt := by
  refine logComplex_hom_ext (fun _ => rfl) fun q x => ?_
  show Submodule.Quotient.mk
      (p := Submodule.restrictScalars A (logRel A (algebraMap R R' t) q))
      (logPairTowerMap A R R' q (logPairUnit A u q x)) =
    Submodule.Quotient.mk
      (p := Submodule.restrictScalars A (logRel A (algebraMap R R' t) q))
      (logPairUnit A (Units.map (algebraMap R R' : R →* R') u) q
        (logPairTowerMap A R R' q x))
  rw [logPairTowerMap_logPairUnit]

/-- **The restriction map of the descent datum of Stacks Tag 0FMW.**  For a tower `R → R'` of
`A`-algebras and equations `t ∈ R` and `t' ∈ R'` of the same divisor, related by `t' = w · t|_{R'}`
with `w` a unit of `R'`, the map `Ω^•(log Y)(t) → Ω^•(log Y')(t')` restricting a form with a
logarithmic pole and then rewriting it in the chosen equation of the smaller ring.  It is the
tower map of `Stacks.LogPoles.logComplexTowerMap` followed by the change of equation of
`Stacks.LogPoles.logComplexUnitIso`; neither alone is a presheaf. -/
def logComplexRestrict {t : R} {t' : R'} (w : R'ˣ)
    (hw : t' = (w : R') * algebraMap R R' t)
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (ht' : ∀ p : ℕ, IsSMulRegular (↥(⋀[R']^p (Ω[R'⁄A]))) t') :
    logComplex ht ⟶ logComplex ht' :=
  logComplexTowerMap rfl ht (isSMulRegular_algebraMap_of_unit_mul w hw ht') ≫
    logComplexUnitHom w⁻¹ (algebraMap_eq_inv_unit_mul w hw)
      (isSMulRegular_algebraMap_of_unit_mul w hw ht') ht'

/-- In degree zero the restriction map is the map of relative forms. -/
@[simp]
theorem logComplexRestrict_zero_apply {t : R} {t' : R'} (w : R'ˣ)
    (hw : t' = (w : R') * algebraMap R R' t)
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (ht' : ∀ p : ℕ, IsSMulRegular (↥(⋀[R']^p (Ω[R'⁄A]))) t')
    (ω : ⋀[R]^0 (Ω[R⁄A])) :
    ((logComplexRestrict w hw ht ht').f 0).hom ω = mapExteriorPower A R R' 0 ω := rfl

/-- In degree `p + 1` the restriction map carries the pair `(ω, η)` to
`(ω|_{R'} + dlog w⁻¹ ∧ η|_{R'}, η|_{R'})`. -/
@[simp]
theorem logComplexRestrict_succ_apply {t : R} {t' : R'} (w : R'ˣ)
    (hw : t' = (w : R') * algebraMap R R' t)
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (ht' : ∀ p : ℕ, IsSMulRegular (↥(⋀[R']^p (Ω[R'⁄A]))) t')
    (p : ℕ) (x : ⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])) :
    ((logComplexRestrict w hw ht ht').f (p + 1)).hom
        (Submodule.Quotient.mk (p := Submodule.restrictScalars A (logRel A t p)) x) =
      Submodule.Quotient.mk (p := Submodule.restrictScalars A (logRel A t' p))
        (logPairUnit A w⁻¹ p (logPairTowerMap A R R' p x)) := rfl

/-- **The restriction map of the descent datum restricts to the standard map of de Rham complexes
on the forms with no pole.**  A form with no pole is the pair `(ω, 0)`, which both the tower map
and the change of equation fix, so the restriction map is a map of the two residue sequences of
Stacks Tag 0FMW on their left-hand terms. -/
theorem logIncl_comp_logComplexRestrict {t : R} {t' : R'} (w : R'ˣ)
    (hw : t' = (w : R') * algebraMap R R' t)
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (ht' : ∀ p : ℕ, IsSMulRegular (↥(⋀[R']^p (Ω[R'⁄A]))) t') :
    logIncl ht ≫ logComplexRestrict w hw ht ht' =
      KaehlerDifferential.deRhamComplexMap A R R' ≫ logIncl ht' := by
  rw [logComplexRestrict, ← Category.assoc, logIncl_comp_logComplexTowerMap,
    Category.assoc, logIncl_comp_logComplexUnitHom]

/-- **The restriction map of the descent datum is not degenerate.**  Whenever the maps of relative
forms are injective — as they are for a localization, where they are the localization maps — the
restriction map is injective on the forms with no pole, in every degree.  So neither the datum nor
the complexes it relates has collapsed. -/
theorem injective_logIncl_comp_logComplexRestrict_f {t : R} {t' : R'} (w : R'ˣ)
    (hw : t' = (w : R') * algebraMap R R' t)
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (ht' : ∀ p : ℕ, IsSMulRegular (↥(⋀[R']^p (Ω[R'⁄A]))) t')
    (hinj : ∀ p : ℕ, Function.Injective (mapExteriorPower A R R' p)) (p : ℕ) :
    Function.Injective ((logIncl ht ≫ logComplexRestrict w hw ht ht').f p).hom := by
  rw [logIncl_comp_logComplexRestrict]
  intro x y hxy
  exact hinj p (injective_logIncl_f ht' p hxy)

/-- **A restriction map exists for any two local equations of one divisor**, with no unit given in
advance: the two equations generate the same ideal, so they differ by a unit, and that unit builds
the restriction map.  It is compatible with the inclusion of the forms with no pole. -/
theorem exists_logComplexRestrict {t : R} {t' : R'}
    (hreg : IsSMulRegular R' (algebraMap R R' t))
    (hspan : Ideal.span {t'} = Ideal.span {algebraMap R R' t})
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (ht' : ∀ p : ℕ, IsSMulRegular (↥(⋀[R']^p (Ω[R'⁄A]))) t') :
    ∃ Φ : logComplex ht ⟶ logComplex ht',
      logIncl ht ≫ Φ = KaehlerDifferential.deRhamComplexMap A R R' ≫ logIncl ht' := by
  obtain ⟨w, hw⟩ := exists_unit_mul_of_span_singleton_eq hreg hspan
  exact ⟨logComplexRestrict w hw ht ht', logIncl_comp_logComplexRestrict w hw ht ht'⟩

end Restrict

/-! ### The cocycle law -/

section Cocycle

variable {A R R' R'' : Type u} [CommRing A] [CommRing R] [CommRing R'] [CommRing R'']
  [Algebra A R] [Algebra A R'] [Algebra A R''] [Algebra R R'] [Algebra R R''] [Algebra R' R'']
  [IsScalarTower A R R'] [IsScalarTower A R R''] [IsScalarTower A R' R'']
  [IsScalarTower R R' R'']

omit [Algebra A R] [Algebra A R'] [Algebra A R''] [IsScalarTower A R R']
  [IsScalarTower A R R''] [IsScalarTower A R' R''] in
/-- The unit relating the equations at the two ends of a tower is the product of the two units
relating them stepwise, the first pushed along `R' → R''`. -/
theorem unit_mul_algebraMap_of_tower {t : R} {t' : R'} {t'' : R''} (w' : R'ˣ) (w'' : R''ˣ)
    (hw' : t' = (w' : R') * algebraMap R R' t)
    (hw'' : t'' = (w'' : R'') * algebraMap R' R'' t') :
    t'' = (↑(Units.map (algebraMap R' R'' : R' →* R'') w' * w'') : R'') *
      algebraMap R R'' t := by
  rw [hw'', hw', map_mul, Units.val_mul, Units.coe_map,
    IsScalarTower.algebraMap_apply R R' R'' t]
  simp only [MonoidHom.coe_coe]
  ring

/-- **The cocycle law of the descent datum of Stacks Tag 0FMW.**  The restriction maps compose
along a tower `R → R' → R''` of `A`-algebras with chosen equations `t`, `t'`, `t''` of one
divisor: restricting to `R'` and then to `R''` is restricting to `R''`.  This is the presheaf law
that the glued complex of sheaves `Ω^•_{X/S}(log Y)` needs, and that neither
`Stacks.LogPoles.logComplexTowerMap_comp`, which holds the equation fixed, nor
`Stacks.LogPoles.logComplexUnitIso`, which holds the ring fixed, states.  It rests on the
compatibility square `Stacks.LogPoles.logPairTowerMap_logPairUnit` and on the multiplicativity of
`dlog`. -/
theorem logComplexRestrict_comp {t : R} {t' : R'} {t'' : R''} (w' : R'ˣ) (w'' : R''ˣ)
    (hw' : t' = (w' : R') * algebraMap R R' t)
    (hw'' : t'' = (w'' : R'') * algebraMap R' R'' t')
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (ht' : ∀ p : ℕ, IsSMulRegular (↥(⋀[R']^p (Ω[R'⁄A]))) t')
    (ht'' : ∀ p : ℕ, IsSMulRegular (↥(⋀[R'']^p (Ω[R''⁄A]))) t'') :
    logComplexRestrict w' hw' ht ht' ≫ logComplexRestrict w'' hw'' ht' ht'' =
      logComplexRestrict (Units.map (algebraMap R' R'' : R' →* R'') w' * w'')
        (unit_mul_algebraMap_of_tower w' w'' hw' hw'') ht ht'' := by
  have hu : Units.map (algebraMap R' R'' : R' →* R'') w'⁻¹ * w''⁻¹ =
      (Units.map (algebraMap R' R'' : R' →* R'') w' * w'')⁻¹ := by
    rw [mul_inv_rev, map_inv, mul_comm]
  refine logComplex_hom_ext (fun ω => ?_) fun q x => ?_
  · exact mapExteriorPower_mapExteriorPower A R R' R'' 0 ω
  · show Submodule.Quotient.mk (p := Submodule.restrictScalars A (logRel A t'' q))
        (logPairUnit A w''⁻¹ q (logPairTowerMap A R' R'' q
          (logPairUnit A w'⁻¹ q (logPairTowerMap A R R' q x)))) =
      Submodule.Quotient.mk (p := Submodule.restrictScalars A (logRel A t'' q))
        (logPairUnit A (Units.map (algebraMap R' R'' : R' →* R'') w' * w'')⁻¹ q
          (logPairTowerMap A R R'' q x))
    rw [logPairTowerMap_logPairUnit, logPairTowerMap_logPairTowerMap, logPairUnit_mul, hu]

end Cocycle

end Stacks.LogPoles

end
