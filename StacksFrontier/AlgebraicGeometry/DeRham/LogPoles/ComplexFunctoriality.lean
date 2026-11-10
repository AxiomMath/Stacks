module

public import StacksFrontier.RingTheory.DeRham.LogPolesSequence
public import StacksFrontier.RingTheory.DeRham.PolynomialQuasiIso
public import StacksFrontier.RingTheory.DeRham.WeightComparison

/-!
# The de Rham complex of log poles is functorial in the ring

Let `A → R` be a ring map, let `t ∈ R` cut out a divisor, and let `R → R'` be a further map of
`A`-algebras carrying `t` to an equation `s` of the pulled-back divisor. This file constructs
the induced map of the residue sequences of
`StacksFrontier.RingTheory.DeRham.LogPolesSequence`,

`Ω^•_{X/S}(log Y) ⟶ Ω^•_{X'/S}(log Y')`,

shows it restricts on the forms with no pole to the standard map of de Rham complexes, and
proves that it composes along a tower. These are the restriction maps of the presheaf
`U ↦ Ω^•(log Y)(U)`, and so they are one of the two pieces of data from which the sheaf
`Ω^•_{X/S}(log Y)` of Stacks Tag 0FMW is glued; the other is the comparison between two local
equations of the same divisor, which is the content of
`StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.LocalEquationIndependence`.

## Main definitions

* `Stacks.LogPoles.logPairTowerMap`: the pair model `Ω^{p+1} × Ω^p` mapped along a tower.
* `Stacks.LogPoles.logFormsTowerMap`: the degreewise map of the forms with a logarithmic pole.
* `Stacks.LogPoles.logComplexTowerMap`: **the induced map of complexes**
  `Ω^•_{X/S}(log Y) ⟶ Ω^•_{X'/S}(log Y')`.

## Main results

* `Stacks.LogPoles.logPairTowerMap_mem_logRel`: the relations of the pair model are carried into
  the relations for the image equation, which is what makes the map well defined.
* `Stacks.LogPoles.logIncl_comp_logComplexTowerMap`: **the map agrees with the standard map of de
  Rham complexes on the forms with no pole**, so it is a map of the two residue sequences on
  their left-hand terms. With the injectivity of the inclusion this pins the map down on
  `Ω^•_{X/S}` and shows it is not a degenerate one.
* `Stacks.LogPoles.injective_logIncl_comp_logComplexTowerMap_f`: the map is not degenerate —
  on the forms with no pole it is injective whenever the maps of relative forms are.
* `Stacks.LogPoles.logPairTowerMap_logPairTowerMap` and
  `Stacks.LogPoles.logComplexTowerMap_comp`: **functoriality**, that the maps compose along a
  tower `R → R' → R''`. This is the presheaf law.

## Implementation notes

The equation on `R'` is carried as an element `s` together with the hypothesis
`s = algebraMap R R' t` rather than being written as `algebraMap R R' t` outright. The two spell
the same divisor, but the hypothesis form is what lets the composite along a tower be stated: the
equation reached by composing is `algebraMap R' R'' (algebraMap R R' t)`, which is only
propositionally the equation `algebraMap R R'' t` reached directly, so with the outright spelling
the two sides of the composition law would not even have the same type. This is the same device
by which `Stacks.LogPoles.logComplexUnitIso` carries a second equation of one divisor.

Both torsion-freeness hypotheses are carried: `t`-torsion freeness of the forms on `R` and
`s`-torsion freeness of the forms on `R'`. Neither follows from the other — the first is a
hypothesis of the source complex and the second of the target complex, and the second is a
condition of Stacks Tag 0FMV for the pulled-back divisor, not a consequence of the first. The
splitting, the other condition of Tag 0FMV, is not needed: it enters only with the residue.

The underlying maps of modules are `KaehlerDifferential.mapExteriorPower`, the maps of relative
forms induced by a tower, and the two facts used about them are that they commute with the de
Rham differential and with wedging by a one-form. Nothing about `R → R'` is assumed beyond its
being a map of `A`-algebras: in particular it need not be flat, a localization or surjective, so
the same maps serve both the restriction of the presheaf to a smaller open and the restriction of
forms to the divisor.

## References

* [Stacks Project, Tag 0FMW](https://stacks.math.columbia.edu/tag/0FMW), whose proof glues the
  local complexes, for which these restriction maps are the presheaf datum
* [Stacks Project, Tag 0FMV](https://stacks.math.columbia.edu/tag/0FMV), the hypothesis
-/

@[expose] public noncomputable section

open CategoryTheory KaehlerDifferential

universe u

namespace Stacks.LogPoles

section Tower

variable {A R R' : Type u} [CommRing A] [CommRing R] [CommRing R']
  [Algebra A R] [Algebra A R'] [Algebra R R'] [IsScalarTower A R R']

/-! ### The pair model along a tower -/

/-- The pair model of the forms with a logarithmic pole, mapped along a tower `R → R'` of
`A`-algebras: `(ω, η) ↦ (ω|_{R'}, η|_{R'})`. -/
def logPairTowerMap (A R R' : Type u) [CommRing A] [CommRing R] [CommRing R'] [Algebra A R]
    [Algebra A R'] [Algebra R R'] [IsScalarTower A R R'] (p : ℕ) :
    (⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])) →ₗ[A]
      (⋀[R']^(p + 1) (Ω[R'⁄A]) × ⋀[R']^p (Ω[R'⁄A])) :=
  ((mapExteriorPower A R R' (p + 1)).restrictScalars A).prodMap
    ((mapExteriorPower A R R' p).restrictScalars A)

/-- The map of the pair model along `R → R'` applies the maps of relative forms in each
component. -/
@[simp]
theorem logPairTowerMap_apply (p : ℕ) (x : ⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])) :
    logPairTowerMap A R R' p x =
      (mapExteriorPower A R R' (p + 1) x.1, mapExteriorPower A R R' p x.2) := rfl

/-- The map of relative forms carries the map `(ω, η) ↦ t ω + dt ∧ η` of the pair model to the
same map for the image equation. -/
theorem mapExteriorPower_logPairMap {t : R} {s : R'} (hs : s = algebraMap R R' t) (p : ℕ)
    (x : ⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])) :
    mapExteriorPower A R R' (p + 1) (logPairMap A t p x) =
      logPairMap A s p (logPairTowerMap A R R' p x) := by
  have hx : logPairMap A t p x =
      t • x.1 + exteriorPower.wedgeLeft (KaehlerDifferential.D A R t) p x.2 := rfl
  have hy : logPairMap A s p (logPairTowerMap A R R' p x) =
      s • mapExteriorPower A R R' (p + 1) x.1 +
        exteriorPower.wedgeLeft (KaehlerDifferential.D A R' s) p
          (mapExteriorPower A R R' p x.2) := rfl
  rw [hx, hy, hs, map_add, map_smul, mapExteriorPower_wedgeLeft, KaehlerDifferential.map_D,
    algebraMap_smul]

/-- **The relations of the pair model are carried into the relations for the image equation.**
If `t ω + dt ∧ η = 0` then `s ω|_{R'} + ds ∧ η|_{R'} = 0`, because the maps of relative forms
commute with multiplication by a scalar and with wedging by `dt`. This is what makes the induced
map of the forms with a logarithmic pole well defined. -/
theorem logPairTowerMap_mem_logRel {t : R} {s : R'} (hs : s = algebraMap R R' t) (p : ℕ)
    {x : ⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])} (hx : x ∈ logRel A t p) :
    logPairTowerMap A R R' p x ∈ logRel A s p := by
  have h : mapExteriorPower A R R' (p + 1) (logPairMap A t p x) = 0 := by
    rw [show logPairMap A t p x = 0 from hx, map_zero]
  rw [mapExteriorPower_logPairMap hs p x] at h
  exact h

/-- The map of relative forms commutes with the differential `(ω, η) ↦ (dω, -dη)` of the pair
model. -/
theorem logPairTowerMap_logPairD (p : ℕ) (x : ⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])) :
    logPairTowerMap A R R' (p + 1) (logPairD A p x) =
      logPairD A p (logPairTowerMap A R R' p x) := by
  rw [logPairD_apply, logPairTowerMap_apply, logPairTowerMap_apply, logPairD_apply]
  rw [Prod.mk.injEq]
  refine ⟨mapExteriorPower_deRhamDifferential A R R' (p + 1) x.1, ?_⟩
  rw [map_neg, mapExteriorPower_deRhamDifferential A R R' p x.2]

/-! ### The induced map of the complexes of log poles -/

/-- The relations of the pair model are carried into the relations for the image equation, in
the form the quotient consumes: the composite of the map of the pair model with the projection
onto the forms with a logarithmic pole for `s` kills the relations for `t`. -/
theorem logPairTowerMap_mkQ_eq_zero {t : R} {s : R'} (hs : s = algebraMap R R' t) (p : ℕ)
    {x : ⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])}
    (hx : x ∈ Submodule.restrictScalars A (logRel A t p)) :
    Submodule.Quotient.mk (p := Submodule.restrictScalars A (logRel A s p))
      (logPairTowerMap A R R' p x) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr
    (Submodule.restrictScalars_mem A _ _ |>.mpr
      (logPairTowerMap_mem_logRel hs p (Submodule.restrictScalars_mem A _ _ |>.mp hx)))

/-- The degreewise map of the forms with a logarithmic pole induced by a tower `R → R'`. -/
def logFormsTowerMap {t : R} {s : R'} (hs : s = algebraMap R R' t)
    (_ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (_hs' : ∀ p : ℕ, IsSMulRegular (↥(⋀[R']^p (Ω[R'⁄A]))) s) :
    (p : ℕ) → (logFormsX A t p ⟶ logFormsX A s p)
  | 0 => ModuleCat.ofHom ((mapExteriorPower A R R' 0).restrictScalars A)
  | p + 1 => ModuleCat.ofHom
      (Submodule.liftQ _
        ((Submodule.restrictScalars A (logRel A s p)).mkQ.comp (logPairTowerMap A R R' p))
        fun _ hx ↦ logPairTowerMap_mkQ_eq_zero hs p hx)

/-- In degree `0` the map of the forms with a logarithmic pole is the map of relative forms. -/
@[simp]
theorem logFormsTowerMap_zero_apply {t : R} {s : R'} (hs : s = algebraMap R R' t)
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (hs' : ∀ p : ℕ, IsSMulRegular (↥(⋀[R']^p (Ω[R'⁄A]))) s) (ω : ⋀[R]^0 (Ω[R⁄A])) :
    (logFormsTowerMap hs ht hs' 0).hom ω = mapExteriorPower A R R' 0 ω := rfl

/-- In degree `p + 1` the map of the forms with a logarithmic pole sends the class of a pair
`(ω, η)` to the class of `(ω|_{R'}, η|_{R'})`. -/
@[simp]
theorem logFormsTowerMap_succ_apply {t : R} {s : R'} (hs : s = algebraMap R R' t)
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (hs' : ∀ p : ℕ, IsSMulRegular (↥(⋀[R']^p (Ω[R'⁄A]))) s) (p : ℕ)
    (x : ⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])) :
    (logFormsTowerMap hs ht hs' (p + 1)).hom
        (Submodule.Quotient.mk (p := Submodule.restrictScalars A (logRel A t p)) x) =
      Submodule.Quotient.mk (p := Submodule.restrictScalars A (logRel A s p))
        (logPairTowerMap A R R' p x) := rfl

/-- **The map of the de Rham complexes of log poles** induced by a tower `R → R'` of
`A`-algebras carrying the equation `t` of the divisor to the equation `s`: degreewise
`(ω, η) ↦ (ω|_{R'}, η|_{R'})`. It commutes with the differential `(ω, η) ↦ (dω, -dη)` because
the maps of relative forms commute with the de Rham differential. -/
def logComplexTowerMap {t : R} {s : R'} (hs : s = algebraMap R R' t)
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (hs' : ∀ p : ℕ, IsSMulRegular (↥(⋀[R']^p (Ω[R'⁄A]))) s) :
    logComplex ht ⟶ logComplex hs' :=
  CochainComplex.ofHom (logFormsTowerMap hs ht hs') fun p ↦ by
    cases p with
    | zero =>
        ext ω
        obtain ⟨ω, rfl⟩ : ∃ y : ⋀[R]^0 (Ω[R⁄A]), y = ω := ⟨ω, rfl⟩
        change ((logComplex hs').d 0 1).hom ((logFormsTowerMap hs ht hs' 0).hom ω) =
          (logFormsTowerMap hs ht hs' 1).hom (((logComplex ht).d 0 1).hom ω)
        simp only [logComplex_d, logFormsTowerMap_zero_apply]
        refine congrArg (Submodule.Quotient.mk
          (p := Submodule.restrictScalars A (logRel A s 0))) ?_
        rw [logPairTowerMap_apply, Prod.mk.injEq]
        exact ⟨(mapExteriorPower_deRhamDifferential A R R' 0 ω).symm, (map_zero _).symm⟩
    | succ q =>
        ext z
        obtain ⟨z, rfl⟩ : ∃ y : (⋀[R]^(q + 1) (Ω[R⁄A]) × ⋀[R]^q (Ω[R⁄A])) ⧸
            Submodule.restrictScalars A (logRel A t q), y = z := ⟨z, rfl⟩
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
        change ((logComplex hs').d (q + 1) (q + 1 + 1)).hom
              ((logFormsTowerMap hs ht hs' (q + 1)).hom
                (Submodule.Quotient.mk (p := Submodule.restrictScalars A (logRel A t q)) x)) =
            (logFormsTowerMap hs ht hs' (q + 1 + 1)).hom
              (((logComplex ht).d (q + 1) (q + 1 + 1)).hom
                (Submodule.Quotient.mk (p := Submodule.restrictScalars A (logRel A t q)) x))
        simp only [logComplex_d, logFormsTowerMap_succ_apply]
        exact congrArg (Submodule.Quotient.mk
          (p := Submodule.restrictScalars A (logRel A s (q + 1))))
          (logPairTowerMap_logPairD q x).symm

/-- In degree `p` the map of complexes of log poles is `Stacks.LogPoles.logFormsTowerMap`. -/
@[simp]
theorem logComplexTowerMap_f {t : R} {s : R'} (hs : s = algebraMap R R' t)
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (hs' : ∀ p : ℕ, IsSMulRegular (↥(⋀[R']^p (Ω[R'⁄A]))) s) (p : ℕ) :
    (logComplexTowerMap hs ht hs').f p = logFormsTowerMap hs ht hs' p := rfl

/-- **The induced map restricts to the standard map of de Rham complexes on the forms with no
pole.** A form with no pole is the pair `(ω, 0)`, and the map sends it to `(ω|_{R'}, 0)`, which
is the form with no pole `ω|_{R'}`. So the induced map is a map of the two residue sequences of
Stacks Tag 0FMW on their left-hand terms. -/
theorem logIncl_comp_logComplexTowerMap {t : R} {s : R'} (hs : s = algebraMap R R' t)
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (hs' : ∀ p : ℕ, IsSMulRegular (↥(⋀[R']^p (Ω[R'⁄A]))) s) :
    logIncl ht ≫ logComplexTowerMap hs ht hs' =
      KaehlerDifferential.deRhamComplexMap A R R' ≫ logIncl hs' := by
  ext p : 1
  cases p with
  | zero => rfl
  | succ q =>
      ext ω
      obtain ⟨ω, rfl⟩ : ∃ y : ⋀[R]^(q + 1) (Ω[R⁄A]), y = ω := ⟨ω, rfl⟩
      change (logFormsTowerMap hs ht hs' (q + 1)).hom ((logInclF ht (q + 1)).hom ω) =
        (logInclF hs' (q + 1)).hom
          (((KaehlerDifferential.deRhamComplexMap A R R').f (q + 1)).hom ω)
      rw [logInclF_succ_apply, logFormsTowerMap_succ_apply,
        KaehlerDifferential.deRhamComplexMap_f]
      refine congrArg (Submodule.Quotient.mk
        (p := Submodule.restrictScalars A (logRel A s q))) ?_
      rw [logPairTowerMap_apply, Prod.mk.injEq]
      exact ⟨rfl, map_zero _⟩

/-- **The induced map is not degenerate.** Whenever the maps of relative forms are injective —
as they are for a localization, where they are the localization maps — the induced map of the
complexes of log poles is injective on the forms with no pole, in every degree. So neither the
map nor the complexes it compares has collapsed: the composite is the inclusion of
`Ω^•_{X'/S}` into `Ω^•_{X'/S}(log Y')`, which is injective by
`Stacks.LogPoles.injective_logIncl_f`. -/
theorem injective_logIncl_comp_logComplexTowerMap_f {t : R} {s : R'}
    (hs : s = algebraMap R R' t)
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (hs' : ∀ p : ℕ, IsSMulRegular (↥(⋀[R']^p (Ω[R'⁄A]))) s)
    (hinj : ∀ p : ℕ, Function.Injective (mapExteriorPower A R R' p)) (p : ℕ) :
    Function.Injective ((logIncl ht ≫ logComplexTowerMap hs ht hs').f p).hom := by
  rw [logIncl_comp_logComplexTowerMap hs ht hs']
  intro x y hxy
  exact hinj p (injective_logIncl_f hs' p hxy)

end Tower

/-! ### Functoriality -/

section Comp

variable {A R R' R'' : Type u} [CommRing A] [CommRing R] [CommRing R'] [CommRing R'']
  [Algebra A R] [Algebra A R'] [Algebra A R''] [Algebra R R'] [Algebra R R''] [Algebra R' R'']
  [IsScalarTower A R R'] [IsScalarTower A R R''] [IsScalarTower A R' R'']
  [IsScalarTower R R' R'']

/-- The equation of the divisor reached by composing a tower is the equation reached directly:
if `s` is the image of `t` in `R'` and `w` the image of `s` in `R''`, then `w` is the image of
`t` in `R''`. -/
theorem eq_algebraMap_of_tower {t : R} {s : R'} {w : R''} (hs : s = algebraMap R R' t)
    (hw : w = algebraMap R' R'' s) : w = algebraMap R R'' t := by
  rw [hw, hs, ← IsScalarTower.algebraMap_apply]

/-- **The pair model is functorial**: the maps induced by `R → R'` and by `R' → R''` compose to
the map induced by `R → R''`. -/
theorem logPairTowerMap_logPairTowerMap (p : ℕ)
    (x : ⋀[R]^(p + 1) (Ω[R⁄A]) × ⋀[R]^p (Ω[R⁄A])) :
    logPairTowerMap A R' R'' p (logPairTowerMap A R R' p x) =
      logPairTowerMap A R R'' p x := by
  rw [logPairTowerMap_apply, logPairTowerMap_apply, logPairTowerMap_apply, Prod.mk.injEq]
  exact ⟨mapExteriorPower_mapExteriorPower A R R' R'' (p + 1) x.1,
    mapExteriorPower_mapExteriorPower A R R' R'' p x.2⟩

/-- **The induced maps of the complexes of log poles compose along a tower.** This is the
presheaf law for the restriction maps of `Ω^•_{X/S}(log Y)`. -/
theorem logComplexTowerMap_comp {t : R} {s : R'} {w : R''} (hs : s = algebraMap R R' t)
    (hw : w = algebraMap R' R'' s)
    (ht : ∀ p : ℕ, IsSMulRegular (↥(⋀[R]^p (Ω[R⁄A]))) t)
    (hs' : ∀ p : ℕ, IsSMulRegular (↥(⋀[R']^p (Ω[R'⁄A]))) s)
    (hw' : ∀ p : ℕ, IsSMulRegular (↥(⋀[R'']^p (Ω[R''⁄A]))) w) :
    logComplexTowerMap hs ht hs' ≫ logComplexTowerMap hw hs' hw' =
      logComplexTowerMap (eq_algebraMap_of_tower hs hw) ht hw' := by
  ext p : 1
  cases p with
  | zero =>
      ext ω
      obtain ⟨ω, rfl⟩ : ∃ y : ⋀[R]^0 (Ω[R⁄A]), y = ω := ⟨ω, rfl⟩
      change (logFormsTowerMap hw hs' hw' 0).hom
            ((logFormsTowerMap hs ht hs' 0).hom ω) =
          (logFormsTowerMap (eq_algebraMap_of_tower hs hw) ht hw' 0).hom ω
      rw [logFormsTowerMap_zero_apply, logFormsTowerMap_zero_apply,
        logFormsTowerMap_zero_apply]
      exact mapExteriorPower_mapExteriorPower A R R' R'' 0 ω
  | succ q =>
      ext z
      obtain ⟨z, rfl⟩ : ∃ y : (⋀[R]^(q + 1) (Ω[R⁄A]) × ⋀[R]^q (Ω[R⁄A])) ⧸
          Submodule.restrictScalars A (logRel A t q), y = z := ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      change (logFormsTowerMap hw hs' hw' (q + 1)).hom
            ((logFormsTowerMap hs ht hs' (q + 1)).hom
              (Submodule.Quotient.mk (p := Submodule.restrictScalars A (logRel A t q)) x)) =
          (logFormsTowerMap (eq_algebraMap_of_tower hs hw) ht hw' (q + 1)).hom
            (Submodule.Quotient.mk (p := Submodule.restrictScalars A (logRel A t q)) x)
      rw [logFormsTowerMap_succ_apply, logFormsTowerMap_succ_apply,
        logFormsTowerMap_succ_apply]
      exact congrArg (Submodule.Quotient.mk
        (p := Submodule.restrictScalars A (logRel A w q)))
        (logPairTowerMap_logPairTowerMap q x)

end Comp

end Stacks.LogPoles

end
