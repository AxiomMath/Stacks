module

public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ClosedSubschemeComposition
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.DvrCycleClasses
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.FlatCycleClasses
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ModuleGeneralBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Relative
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecializationRestriction
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.ResidueField
public import StacksFrontier.AlgebraicGeometry.NormalizationFieldExtension.Basic
public import StacksFrontier.RingTheory.DiscreteValuationRing.Solution
public import StacksCore.Tactic.StacksAttribute

/-!
# Specialization of cycles and extensions of discrete valuation rings

Let `R'/R` be an extension of discrete valuation rings, inducing a fraction field extension
`K'/K` and a residue field extension `κ'/κ`, let `X` be locally of finite type over `R` and
write `X' = X_{R'}`. For `r ≥ 0` the square
```
  Z_r(X_K)  ---- sp_{X/R} ---->  Z_r(X_κ)
     |                              |
     ↓                              ↓
  Z_r(X'_{K'}) - sp_{X'/R'} ->  Z_r(X'_{κ'})
```
commutes, the vertical arrows being the base change maps of Section 0H4E.

## Main definitions

* `Stacks.Chow.baseChangeFiberCycleOfEq` — the base change map `Z_r(X_s) ⟶ Z_r(X'_t)` of
  Section 0H4E at a point `t` of the new base whose image is a prescribed point `s`.
* `Stacks.Chow.SpecializationCompatibleWithBaseChange` — the identity of Stacks 0H4K on the
  fundamental cycle of a single integral closed subscheme of the generic fibre.

## Main results

* `AlgebraicGeometry.specMapAlgebraMap_genericPoint`,
  `AlgebraicGeometry.specMapAlgebraMap_closedPoint` — an extension of discrete valuation rings
  carries the generic point to the generic point and the closed point to the closed point, so the
  two horizontal edges of the square are the specialization maps of the two bases.
* `Stacks.Chow.comap_specializationClosure_fiberι` — the generic fibre of the scheme-theoretic
  image in `X` of an integral closed subscheme of `X_K` is that subscheme again.
* `Stacks.Chow.specializationCycle_familyAssociatedToClosedSubscheme_genericPoint` —
  **Stacks 0H4J** in the form used here: for a closed subscheme flat over `R` whose fibres have
  dimension at most `r`, the member of `[Z/X/Spec R]_r` over the generic point specializes to its
  member over the closed point.
* `Stacks.Chow.specializationCompatibleWithBaseChange` — the integral-subscheme case of
  Stacks 0H4K, which is the whole of the source's proof.
* `Stacks.Chow.baseChangeFiberCycleOfEq_comp_specializationCycleHom` — **Stacks 0H4K**: the
  square commutes.

## Implementation notes

An extension of discrete valuation rings in the sense of Tag 09E4 is an injective local algebra
map `R → R'`, that is `IsDiscreteValuationRing.IsExtension R R'`; the morphism of bases is
`AlgebraicGeometry.specMapAlgebraMap R R'` and `X' = X_{R'}` is the pullback of `f : X ⟶ Spec R`
along it, with structure morphism `pullback.snd f (specMapAlgebraMap R R')`. Injectivity gives
`g(η') = η` on generic points and locality gives `g(κ') = κ` on closed points, which is the
identification `X'_{K'} = X_{K'}` with which the source's proof begins: the fraction fields and
the residue fields of `R` and `R'` are the residue fields of `Spec R` and `Spec R'` at those two
pairs of points, so `Z_r(X_K)`, `Z_r(X_κ)`, `Z_r(X'_{K'})` and `Z_r(X'_{κ'})` are the fibrewise
cycle groups `Stacks.Chow.FiberCycleGroup` there and need no further identification.

The base change map of Section 0H4E on the cycles of a single fibre is
`Stacks.Chow.baseChangeFiberCycle f g t r : Z_r(X_{g t}) ⟶ Z_r(X'_t)`. Its source is the cycle
group of the fibre over `g t`, while the specialization maps live over the generic and the
closed point of `Spec R`; the two are the same group, but only after the equalities above.
Rather than transport the cycles pointwise, `Stacks.Chow.baseChangeFiberCycleOfEq` substitutes
the equality `g t = s` once, in the definition of the vertical arrow, so that the square below
is a plain equality of two homomorphisms `Z_r(X_K) ⟶ Z_r(X'_{κ'})` with no casts in it.

### The integral-subscheme case

`Stacks.Chow.SpecializationCompatibleWithBaseChange` says that the square commutes on the
fundamental cycle `[Z]` of a single integral closed subscheme `Z ⊆ X_K` of dimension `r`, and
`Stacks.Chow.specializationCompatibleWithBaseChange` proves it. The argument is organized around
the family of cycles on fibres `[\overline{Z}/X/Spec R]_r` of the scheme-theoretic image
`\overline{Z} ⊆ X` of `Z`, rather than around the four corners of the square separately.

That image is `Stacks.Chow.specializationClosure`, the integral closed subscheme of `X` with the
same generic point as `Z`. Its generic fibre is `Z` again — the inclusion `X_K ⟶ X` is an open
immersion, `Spec K` being the complement of the closed point of `Spec R`, and the inverse image
of a reduced closure along an open immersion is a reduced closure
(`Stacks.Chow.comap_specializationClosure_fiberι`) — so the member of
`[\overline{Z}/X/Spec R]_r` over the generic point is `[Z]`. It dominates `Spec R`, hence is flat
over it (`Stacks.Chow.flat_subschemeι_specializationClosure_comp`), and its generic fibre has
dimension `r`, so Stacks 0H4J makes its member over the closed point `sp_{X/R}([Z])`.

Both vertical arrows of the square are therefore values of the base change of that one family,
read at the generic and at the closed point of `Spec R'`
(`Stacks.Chow.baseChangeFiberCycleOfEq_family`), and the claim is Stacks 0H4J over the new base.
Its hypotheses are supplied by Stacks 0H4R
(`Stacks.Chow.familyAssociatedToModule_baseChange_general`), which identifies the base change of
`[\overline{Z}/X/Spec R]_r` with the family of the base-changed closed subscheme
`\overline{Z}_{R'} ⊆ X'`, together with the flatness of `\overline{Z}_{R'}` over `R'` as a base
change of a flat morphism. No comparison of the two routes around the square is needed: they are
the two members of a single base-changed family.

### From a generator to an arbitrary cycle

`Stacks.Chow.baseChangeFiberCycleOfEq_comp_specializationCycleHom_of_generator` passes from the
integral-subscheme case to every cycle, and that passage is not formal: a cycle on `X_K` is only
locally finite, both specialization maps are coefficientwise locally finite sums over the points
of a generic fibre, and the two index sets are related by the map of fibres `X'_{K'} ⟶ X_K`, so
the sum over `X'_{K'}` has to be regrouped along its fibres and each group summed separately.

Mathlib's category of schemes lives in a single universe and `Spec` of a ring in `Type u` lands
in `Scheme.{u}`, so `R`, `R'` and `X` share the universe variable `u`. Local Noetherianity of
`Spec R` and of `Spec R'` is automatic and is not assumed.

## References

* [Stacks Project, Tag 0H4K](https://stacks.math.columbia.edu/tag/0H4K)
* [Stacks Project, Tag 09E4](https://stacks.math.columbia.edu/tag/09E4)
* [Stacks Project, Section 0H4E](https://stacks.math.columbia.edu/tag/0H4E)
* [Stacks Project, Section 0H4H](https://stacks.math.columbia.edu/tag/0H4H)
* [Stacks Project, Tag 0H4I](https://stacks.math.columbia.edu/tag/0H4I)
* [Stacks Project, Tag 0H4J](https://stacks.math.columbia.edu/tag/0H4J)
* [Stacks Project, Tag 0H4R](https://stacks.math.columbia.edu/tag/0H4R)
* [Stacks Project, Tag 0H4S](https://stacks.math.columbia.edu/tag/0H4S)
* [Stacks Project, Tag 0FVI](https://stacks.math.columbia.edu/tag/0FVI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### The morphism of bases of a ring extension

The morphism of bases along which the base change `X' = X_{R'}` is formed is
`AlgebraicGeometry.specMapAlgebraMap R R'`. -/

/-- An injective algebra map of domains carries the generic point of the spectrum of the target
to the generic point of the spectrum of the source: the fraction field `K'` of `R'` is an
extension of the fraction field `K` of `R`. -/
theorem specMapAlgebraMap_genericPoint (R R' : Type u) [CommRing R] [IsDomain R] [CommRing R']
    [IsDomain R'] [Algebra R R'] [FaithfulSMul R R'] :
    specMapAlgebraMap R R' (genericPoint (Spec (.of R'))) = genericPoint (Spec (.of R)) := by
  rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
  exact PrimeSpectrum.ext
    (Ideal.comap_bot_of_injective (algebraMap R R') (FaithfulSMul.algebraMap_injective R R'))

/-- A local algebra map of local rings carries the closed point of the spectrum of the target to
the closed point of the spectrum of the source: the residue field `κ'` of `R'` is an extension of
the residue field `κ` of `R`. -/
theorem specMapAlgebraMap_closedPoint (R R' : Type u) [CommRing R] [IsLocalRing R] [CommRing R']
    [IsLocalRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')] :
    specMapAlgebraMap R R' (IsLocalRing.closedPoint R') = IsLocalRing.closedPoint R :=
  AlgebraicGeometry.Spec_closedPoint (f := CommRingCat.ofHom (algebraMap R R'))

end AlgebraicGeometry

namespace Stacks.Chow

/-! ### The base change map on the cycles of a fibre over a prescribed point -/

/-- The base change map `Z_r(X_s) ⟶ Z_r(X'_t)` of Section 0H4E on the cycles of a single fibre,
read at a point `t` of the new base whose image is the prescribed point `s` of the old base. It
is `Stacks.Chow.baseChangeFiberCycle` with the equality `g t = s` substituted once, so that no
cast between the cycle groups of the fibres over `s` and over `g t` survives. -/
def baseChangeFiberCycleOfEq {X S S' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) {t : S'} {s : S} (hst : g t = s) (r : ℕ) :
    FiberCycleGroup f s r →+ FiberCycleGroup (pullback.snd f g) t r :=
  hst ▸ baseChangeFiberCycle f g t r

/-- At the tautological equality the base change map over a prescribed point is the base change
map of Section 0H4E. -/
@[simp]
theorem baseChangeFiberCycleOfEq_rfl {X S S' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (t : S') (r : ℕ) :
    baseChangeFiberCycleOfEq f g (rfl : g t = g t) r = baseChangeFiberCycle f g t r :=
  rfl

/-- The base change map over a prescribed point computes the base change of a family of cycles:
the member of `g^*α` over a point `t` of the new base is the base change of the member of `α`
over the prescribed image `s` of `t`. -/
theorem baseChangeFiberCycleOfEq_family {X S S' : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (g : S' ⟶ S) {t : S'} {s : S} (hst : g t = s) (r : ℕ)
    (α : FamilyOfCycles f r) :
    baseChangeFiberCycleOfEq f g hst r (α s) = baseChangeFamily f g r α t := by
  subst hst
  exact (baseChangeFamily_eq_baseChangeFiberCycle f g r α t).symm

/-- The base change map on the cycles of a fibre multiplies coefficients by a weight read through
a map of fibres: there are a map `q : X'_t ⟶ X_s` on points and a weight function `m` on `X'_t`,
both independent of the cycle, with `(g^*z)(x) = z(q x) * m x`.

Through the canonical identification `X'_t = X_s ×_{κ(s)} κ(t)` the map `q` is the projection to
`X_s` and `m x` is the multiplicity with which `x` enters the inverse image of the reduced closure
of `q x`; this existence statement is the form in which the two are used. -/
theorem exists_coeff_baseChangeFiberCycleOfEq {X S S' : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (g : S' ⟶ S) {t : S'} {s : S} (hst : g t = s) (r : ℕ) :
    ∃ q : (pullback.snd f g).fiber t → f.fiber s, ∃ m : (pullback.snd f g).fiber t → ℤ,
      ∀ (z : FiberCycleGroup f s r) (x : (pullback.snd f g).fiber t),
        (baseChangeFiberCycleOfEq f g hst r z).1 x = z.1 (q x) * m x := by
  subst hst
  refine ⟨fun x ↦ restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g
      pullback.condition t x,
    fun x ↦ flatPullbackWeight (fieldChowSituation (S'.residueField t))
      (pullback.snd (f.fiberToSpecResidueField (g t)) (residueFieldBaseChangeSituation g t).g)
      (pullback.fst (f.fiberToSpecResidueField (g t)) (residueFieldBaseChangeSituation g t).g)
      (r : ℤ) ((fibreBaseChangeIso f g t).hom x), ?_⟩
  intro z x
  exact baseChangeFiberCycle_apply f g t r z x

/-! ### Coefficients of fundamental cycles on a generic fibre -/

/-- The fundamental cycle `[Z]` of the integral closed subscheme of the generic fibre with
generic point `ξ` has coefficient one at `ξ`, provided `ξ` has dimension `r`. -/
theorem integralGenericCycle_apply_self {R : Type u} [CommRing R] [IsDomain R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f] (r : ℕ)
    (ξ : f.fiber (genericPoint (Spec (.of R))))
    (hξ : fiberPointDimension f (genericPoint (Spec (.of R))) ξ = (r : ℤ)) :
    (integralGenericCycle f r ξ).1 ξ = 1 :=
  fiberSubschemeCycle_integralComponentAt_self f _ r ξ hξ

/-- Every other coefficient of the fundamental cycle `[Z]` of the integral closed subscheme of
the generic fibre with generic point `ξ` vanishes: at a point other than `ξ`, and at `ξ` itself
when `ξ` does not have dimension `r`. -/
theorem integralGenericCycle_apply_eq_zero {R : Type u} [CommRing R] [IsDomain R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f] (r : ℕ)
    (ξ ζ : f.fiber (genericPoint (Spec (.of R))))
    (h : ζ ≠ ξ ∨ fiberPointDimension f (genericPoint (Spec (.of R))) ξ ≠ (r : ℤ)) :
    (integralGenericCycle f r ξ).1 ζ = 0 := by
  by_cases hζ : ζ = ξ
  · subst hζ
    refine fiberSubschemeCycle_apply_eq_zero f _ r _ ζ ?_
    rintro ⟨-, -, hζdim⟩
    exact (h.resolve_left (fun hne ↦ hne rfl)) hζdim
  · exact fiberSubschemeCycle_integralComponentAt_of_ne f _ r ξ ζ hζ

/-- A point of a fibre at which an `r`-cycle has a nonzero coefficient has dimension `r`. -/
theorem fiberPointDimension_of_coeff_ne_zero {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (s : S) (r : ℕ) (c : FiberCycleGroup f s r) (y : f.fiber s)
    (hy : c.1 y ≠ 0) : fiberPointDimension f s y = (r : ℤ) := by
  have : LocallyOfFiniteType (f.fiberToSpecResidueField s) := by
    change LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField s))
    infer_instance
  exact (mem_cyclesOfDimension_iff_forall_point (fieldChowSituation (S.residueField s))
    (f.fiberToSpecResidueField s) (r : ℤ) c.1).mp c.2 y hy

/-- The locally finite sum defining the specialization map, taken over *all* points of the
generic fibre rather than over the points of dimension `r`: a point of another dimension carries
the coefficient zero in an `r`-cycle, so it contributes nothing. -/
theorem hasSum_specializationCycle_of_forall {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f]
    (r : ℕ) (c : FiberCycleGroup f (genericPoint (Spec (.of R))) r)
    (x : f.fiber (IsLocalRing.closedPoint R)) :
    HasSum (fun ξ : f.fiber (genericPoint (Spec (.of R))) ↦
        c.1 ξ * (specializationCycle f r (integralGenericCycle f r ξ)).1 x)
      ((specializationCycle f r c).1 x) := by
  refine (hasSum_subtype_iff_of_support_subset (s := {ξ |
    fiberPointDimension f (genericPoint (Spec (.of R))) ξ = (r : ℤ)}) ?_).1
      (hasSum_specializationCycle f r c x)
  intro ξ hξ
  exact fiberPointDimension_of_coeff_ne_zero f _ r c ξ (left_ne_zero_of_mul hξ)

/-! ### The schematic closure of an integral subscheme of the generic fibre, as a cycle -/

section Closure

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f] (r : ℕ)

/-- Transporting a closed immersion along an equality of the ideal sheaves cutting it out. -/
private alias eqToHom_subscheme_comp_subschemeι := AlgebraicGeometry.Scheme.eqToHom_comp_subschemeι

/-- The generic fibre of the scheme-theoretic image `\overline{Z} ⊆ X` of the integral closed
subscheme of `X_K` with generic point `ξ` is that subscheme again. The inclusion of the generic
fibre is an open immersion, `Spec K` being the complement of the closed point of `Spec R`, and
the inverse image of a reduced closure along an open immersion is a reduced closure. -/
@[sga "3 VIII 7.1" "partial"]
theorem comap_specializationClosure_fiberι (ξ : f.fiber (genericPoint (Spec (.of R)))) :
    (specializationClosure f ξ).comap (f.fiberι (genericPoint (Spec (.of R)))) =
      integralComponentAt ξ := by
  have := isOpenImmersion_fiberι_genericPoint f
  rw [specializationClosure_eq_integralComponentAt,
    comap_integralComponentAt_of_isOpenImmersion]

/-- The identification of the integral closed subscheme `Z ⊆ X_K` with generic point `ξ` with the
inverse image in `X_K` of the scheme-theoretic image `\overline{Z} ⊆ X`. -/
private def specializationClosureFibreIso (ξ : f.fiber (genericPoint (Spec (.of R)))) :
    (integralComponentAt ξ).subscheme ≅
      pullback (specializationClosure f ξ).subschemeι
        (f.fiberι (genericPoint (Spec (.of R)))) :=
  eqToIso (congrArg Scheme.IdealSheafData.subscheme
      (comap_specializationClosure_fiberι f ξ).symm) ≪≫
    (specializationClosure f ξ).comapIso (f.fiberι (genericPoint (Spec (.of R)))) ≪≫
    pullbackSymmetry _ _

/-- The identification of `Stacks.Chow.specializationClosureFibreIso` lies over `X_K`. -/
private theorem specializationClosureFibreIso_hom_comp
    (ξ : f.fiber (genericPoint (Spec (.of R)))) :
    (specializationClosureFibreIso f ξ).hom ≫
        fiberClosedImmersion f (specializationClosure f ξ).subschemeι
          (genericPoint (Spec (.of R))) =
      (integralComponentAt ξ).subschemeι := by
  rw [specializationClosureFibreIso, fiberClosedImmersion]
  simp only [Iso.trans_hom, eqToIso.hom, Category.assoc, pullbackSymmetry_hom_comp_snd,
    Scheme.IdealSheafData.comapIso_hom_fst]
  exact eqToHom_subscheme_comp_subschemeι (comap_specializationClosure_fiberι f ξ).symm

/-- The member over the generic point of the family of cycles `[\overline{Z}/X/Spec R]_r` of the
scheme-theoretic image is the fundamental cycle `[Z]` of the integral closed subscheme of the
generic fibre: the inverse image of `\overline{Z}` in `X_K` is `Z`. -/
theorem familyAssociatedToClosedSubscheme_specializationClosure_genericPoint
    (ξ : f.fiber (genericPoint (Spec (.of R)))) :
    familyAssociatedToClosedSubscheme f (specializationClosure f ξ).subschemeι r
        (genericPoint (Spec (.of R))) =
      integralGenericCycle f r ξ := by
  rw [familyAssociatedToClosedSubscheme_apply, integralGenericCycle, fiberSubschemeCycle]
  exact (cycleAssociatedToClosedSubscheme_eq_of_iso _ _ _ _
    (specializationClosureFibreIso f ξ) (specializationClosureFibreIso_hom_comp f ξ) _).symm

/-- The generic fibre of the scheme-theoretic image of the integral closed subscheme of `X_K`
with generic point `ξ` has dimension `r` when `ξ` has relative dimension `r`: that fibre is the
reduced closure of `ξ` in `X_K`, whose dimension is the relative dimension at its generic
point. -/
theorem topologicalKrullDim_pullback_specializationClosure
    (ξ : f.fiber (genericPoint (Spec (.of R))))
    (hd : fiberPointDimension f (genericPoint (Spec (.of R))) ξ = (r : ℤ)) :
    topologicalKrullDim (pullback (specializationClosure f ξ).subschemeι
        (f.fiberι (genericPoint (Spec (.of R)))) : Scheme.{u}) = (r : WithBot ℕ∞) := by
  have : IsIntegral (integralComponentAt ξ).subscheme := isIntegral_integralComponentAt ξ
  have : JacobsonSpace (fieldChowSituation ((Spec (.of R)).residueField
      (genericPoint (Spec (.of R))))).S :=
    inferInstanceAs (JacobsonSpace (Spec (CommRingCat.of ((Spec (.of R)).residueField
      (genericPoint (Spec (.of R)))))))
  have hgen : (integralComponentAt ξ).subschemeι.base
      (genericPoint (integralComponentAt ξ).subscheme) = ξ := by
    simpa [genericPointOf] using genericPointOf_integralComponentAt ξ
  have hd' : relativeDimension (fieldChowSituation ((Spec (.of R)).residueField
        (genericPoint (Spec (.of R))))).dimensionFunction
      (f.fiberToSpecResidueField (genericPoint (Spec (.of R)))) ξ = (r : ℤ) := hd
  rw [← IsHomeomorph.topologicalKrullDim_eq _
      (Scheme.homeoOfIso (specializationClosureFibreIso f ξ)).isHomeomorph,
    topologicalKrullDim_eq_relativeDimension_toNat
      (fieldChowSituation ((Spec (.of R)).residueField (genericPoint (Spec (.of R)))))
      (fun _ _ ↦ rfl) (f.fiberToSpecResidueField (genericPoint (Spec (.of R))))
      (integralComponentAt ξ).subschemeι (genericPoint (integralComponentAt ξ).subscheme)
      (genericPoint_spec (integralComponentAt ξ).subscheme),
    hgen, hd']
  simp

/-- The dimension of the fibres of the scheme-theoretic image of the integral closed subscheme of
`X_K` with generic point `ξ` is at most `r` over *every* point of `Spec R`: the bound holds over
the generic point, and the schematic closure is flat over `R`, so Tag 0H4I carries the bound to
every fibre. -/
@[sga "6 X 7.14" "partial", sga "6 X 7.4" "special case"]
theorem topologicalKrullDim_pullback_specializationClosure_le
    (ξ : f.fiber (genericPoint (Spec (.of R))))
    (hd : fiberPointDimension f (genericPoint (Spec (.of R))) ξ = (r : ℤ))
    (s : Spec (.of R)) :
    topologicalKrullDim (pullback (specializationClosure f ξ).subschemeι (f.fiberι s) :
      Scheme.{u}) ≤ (r : WithBot ℕ∞) := by
  have : Flat ((specializationClosure f ξ).subschemeι ≫ f) :=
    flat_subschemeι_specializationClosure_comp f ξ
  exact topologicalKrullDim_pullback_fiberι_le_of_genericFibre f
    (specializationClosure f ξ).subschemeι
    (le_of_eq (topologicalKrullDim_pullback_specializationClosure f r ξ hd)) s

end Closure

/-! ### Tag 0H4J for a closed subscheme flat over the base -/

/-- **Stacks Project, Lemma 0H4J** in the form used below: for a closed subscheme `Z ⊆ X` flat
over the discrete valuation ring `R` whose fibres have dimension at most `r`, the specialization
map carries the member of `[Z/X/Spec R]_r` over the generic point to its member over the closed
point.

This is `Stacks.Chow.specializationCycle_familyAssociatedToClosedSubscheme_of_genericFibre`,
whose hypothesis is the bound on the generic fibre alone. -/
theorem specializationCycle_familyAssociatedToClosedSubscheme_genericPoint {R : Type u}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f] (i : Z ⟶ X) [IsClosedImmersion i]
    [Flat (i ≫ f)] (r : ℕ)
    (hZ : ∀ s : Spec (.of R),
      topologicalKrullDim (pullback i (f.fiberι s) : Scheme.{u}) ≤ (r : WithBot ℕ∞)) :
    specializationCycle f r
        (familyAssociatedToClosedSubscheme f i r (genericPoint (Spec (.of R)))) =
      familyAssociatedToClosedSubscheme f i r (IsLocalRing.closedPoint R) :=
  specializationCycle_familyAssociatedToClosedSubscheme_of_genericFibre f i
    (hZ (genericPoint (Spec (.of R))))

/-! ### Specialization commutes with base change along an extension of discrete valuation rings -/

section Extension

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (R' : Type u)
  [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
  [IsDiscreteValuationRing.IsExtension R R'] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
  [LocallyOfFiniteType f] (r : ℕ)

/-- The base change map `Z_r(X_K) ⟶ Z_r(X'_{K'})` on the cycles of the generic fibres: the map
of Section 0H4E at the generic point of `Spec R'`, whose image is the generic point of
`Spec R`. -/
abbrev baseChangeGenericFibreCycle :
    FiberCycleGroup f (genericPoint (Spec (.of R))) r →+
      FiberCycleGroup (pullback.snd f (specMapAlgebraMap R R')) (genericPoint (Spec (.of R'))) r :=
  baseChangeFiberCycleOfEq f (specMapAlgebraMap R R') (specMapAlgebraMap_genericPoint R R') r

/-- The base change map `Z_r(X_κ) ⟶ Z_r(X'_{κ'})` on the cycles of the special fibres: the map
of Section 0H4E at the closed point of `Spec R'`, whose image is the closed point of
`Spec R`. -/
abbrev baseChangeSpecialFibreCycle :
    FiberCycleGroup f (IsLocalRing.closedPoint R) r →+
      FiberCycleGroup (pullback.snd f (specMapAlgebraMap R R')) (IsLocalRing.closedPoint R') r :=
  baseChangeFiberCycleOfEq f (specMapAlgebraMap R R') (specMapAlgebraMap_closedPoint R R') r

/-- **The integral-subscheme case of Stacks 0H4K.** The square of Stacks 0H4K commutes on the
fundamental cycle `[Z]` of a single integral closed subscheme `Z ⊆ X_K` of dimension `r`: the
specialization of the base change of `[Z]` to `X'_{K'}` is the base change to `X'_{κ'}` of the
specialization of `[Z]`.

This is the whole of the source's proof, and it is
`Stacks.Chow.specializationCompatibleWithBaseChange`. Both routes around the square compute the
`r`-cycle of `(\overline{Z}_{R'})_{κ'}`, the special fibre of the base change to `R'` of the
scheme-theoretic image `\overline{Z} ⊆ X` of `Z`, which is flat over `R`. -/
def SpecializationCompatibleWithBaseChange : Prop :=
  ∀ ξ : f.fiber (genericPoint (Spec (.of R))),
    fiberPointDimension f (genericPoint (Spec (.of R))) ξ = (r : ℤ) →
      specializationCycle (pullback.snd f (specMapAlgebraMap R R')) r
          (baseChangeGenericFibreCycle R' f r (integralGenericCycle f r ξ)) =
        baseChangeSpecialFibreCycle R' f r
          (specializationCycle f r (integralGenericCycle f r ξ))

/-- An extension of discrete valuation rings induces a flat morphism of spectra: the larger ring
is a torsion-free module over the smaller one, because the algebra map of an extension is
injective, and a torsion-free module over a discrete valuation ring is flat. -/
@[ega "0 6.3.4" "special case"]
theorem flat_specMapAlgebraMap_of_isExtension : Flat (specMapAlgebraMap R R') := by
  have : Module.IsTorsionFree R R' :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (FaithfulSMul.algebraMap_injective R R')
  rw [Flat.SpecMap_iff]
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

/-- **Stacks Project, Lemma 0H4J on the base change.** Let `Z ⊆ X` be a closed subscheme flat
over `R` whose fibres have dimension at most `r`. The base change of the family
`[Z/X/Spec R]_r` along the extension `R'/R` satisfies the specialization identity over `Spec R'`:
its member over the generic point of `Spec R'` specializes to its member over the closed point.

The base change of `[Z/X/Spec R]_r` is the family of the base-changed closed subscheme
`Z_{R'} ⊆ X'`: by Stacks 0H4R the base change of the family of a module is the family of the
pulled-back module (Stacks 0FVI on each fibre), and the pullback of `i_* 𝒪_Z` to `X'` is the
direct image of the structure sheaf of `Z_{R'} = Z ×_X X'`. That subscheme is flat over `R'`,
being a base change of `Z ⟶ Spec R` along `Spec R' ⟶ Spec R`, so Stacks 0H4J applies to it over
the new base. -/
theorem specializationCycle_baseChangeFamily_familyAssociatedToClosedSubscheme {Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [Flat (i ≫ f)]
    (hZ : ∀ s : Spec (.of R),
      topologicalKrullDim (pullback i (f.fiberι s) : Scheme.{u}) ≤ (r : WithBot ℕ∞)) :
    specializationCycle (pullback.snd f (specMapAlgebraMap R R')) r
        (baseChangeFamily f (specMapAlgebraMap R R') r
          (familyAssociatedToClosedSubscheme f i r) (genericPoint (Spec (.of R')))) =
      baseChangeFamily f (specMapAlgebraMap R R') r
        (familyAssociatedToClosedSubscheme f i r) (IsLocalRing.closedPoint R') := by
  have : Flat (specMapAlgebraMap R R') := flat_specMapAlgebraMap_of_isExtension R'
  have : Flat (pullback.snd i (pullback.fst f (specMapAlgebraMap R R')) ≫
      pullback.snd f (specMapAlgebraMap R R')) :=
    MorphismProperty.of_isPullback ((IsPullback.of_hasPullback i
        (pullback.fst f (specMapAlgebraMap R R'))).paste_vert
      (IsPullback.of_hasPullback f (specMapAlgebraMap R R'))) (P := @Flat) inferInstance
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : (structureSheafPushforward i).IsQuasicoherent :=
    isQuasicoherent_of_isCoherent (structureSheafPushforward i)
  let : (structureSheafPushforward (pullback.snd i
      (pullback.fst f (specMapAlgebraMap R R')))).IsQuasicoherent :=
    isQuasicoherent_of_isCoherent _
  set e := pullbackPushforwardStructureSheafIso
    (IsPullback.of_hasPullback i (pullback.fst f (specMapAlgebraMap R R'))) with he
  have hs := topologicalKrullDim_supp_pullback_fiberι_le i f hZ
  have hsd := supportDimension_le_of_baseChange_general f (specMapAlgebraMap R R')
    (structureSheafPushforward i) r hs
  have hbc := familyAssociatedToModule_baseChange_general f (specMapAlgebraMap R R')
    (structureSheafPushforward i) r hs
  have hmod' : ∀ t : Spec (.of R'), topologicalKrullDim (SheafOfModules.supp
      ((Scheme.Modules.pullback ((pullback.snd f (specMapAlgebraMap R R')).fiberι t)).obj
        (structureSheafPushforward (pullback.snd i
          (pullback.fst f (specMapAlgebraMap R R')))))) ≤ (r : WithBot ℕ∞) := fun t => by
    rw [← SheafOfModules.supp_eq_of_iso
      ((Scheme.Modules.pullback ((pullback.snd f (specMapAlgebraMap R R')).fiberι t)).mapIso e)]
    exact hsd t
  have hiso := familyAssociatedToModule_eq_of_iso (pullback.snd f (specMapAlgebraMap R R')) e r
    hsd hmod'
  have key : baseChangeFamily f (specMapAlgebraMap R R') r
        (familyAssociatedToClosedSubscheme f i r) =
      familyAssociatedToModule (pullback.snd f (specMapAlgebraMap R R'))
        (structureSheafPushforward (pullback.snd i
          (pullback.fst f (specMapAlgebraMap R R')))) r hmod' :=
    ((congrArg (baseChangeFamily f (specMapAlgebraMap R R') r)
      (familyAssociatedToClosedSubscheme_eq_familyAssociatedToModule f i r hZ)).trans
        hbc).trans hiso
  rw [key]
  exact specializationCycle_familyAssociatedToClosedSubscheme
    (pullback.snd f (specMapAlgebraMap R R'))
    (pullback.snd i (pullback.fst f (specMapAlgebraMap R R')))
    (hmod' (genericPoint (Spec (.of R'))))

/-- **The integral-subscheme case of Stacks 0H4K**, which is the whole of the source's proof.
For an integral closed subscheme `Z ⊆ X_K` of dimension `r`, the specialization of the base
change of `[Z]` to `X'_{K'}` is the base change to `X'_{κ'}` of `sp_{X/R}([Z])`.

Let `\overline{Z} ⊆ X` be the scheme-theoretic image of `Z` in `X`, that is, the integral closed
subscheme of `X` with the same generic point as `Z`. Its generic fibre is `Z` again
(`Stacks.Chow.comap_specializationClosure_fiberι`), so the member over the generic point of the
family `[\overline{Z}/X/Spec R]_r` is `[Z]`, and `\overline{Z}` dominates `Spec R`, hence is flat
over it. Both routes around the square are therefore values of the base change of
`[\overline{Z}/X/Spec R]_r`, read over the two points of `Spec R'`:
`sp_{X/R}([Z])` is the member of `[\overline{Z}/X/Spec R]_r` over the closed point by
Stacks 0H4J, and the two vertical arrows are the base change of that family at the generic and at
the closed point of `Spec R'`. The claim is then Stacks 0H4J over the new base, applied to the
base-changed closed subscheme `\overline{Z}_{R'} ⊆ X'`. -/
theorem specializationCompatibleWithBaseChange :
    SpecializationCompatibleWithBaseChange R' f r := by
  intro ξ hd
  have : Flat ((specializationClosure f ξ).subschemeι ≫ f) :=
    flat_subschemeι_specializationClosure_comp f ξ
  have hZ := topologicalKrullDim_pullback_specializationClosure_le f r ξ hd
  have hgen := familyAssociatedToClosedSubscheme_specializationClosure_genericPoint f r ξ
  calc specializationCycle (pullback.snd f (specMapAlgebraMap R R')) r
          (baseChangeGenericFibreCycle R' f r (integralGenericCycle f r ξ))
      = specializationCycle (pullback.snd f (specMapAlgebraMap R R')) r
          (baseChangeFamily f (specMapAlgebraMap R R') r
            (familyAssociatedToClosedSubscheme f (specializationClosure f ξ).subschemeι r)
            (genericPoint (Spec (.of R')))) := by
        rw [← hgen, baseChangeFiberCycleOfEq_family]
    _ = baseChangeFamily f (specMapAlgebraMap R R') r
          (familyAssociatedToClosedSubscheme f (specializationClosure f ξ).subschemeι r)
          (IsLocalRing.closedPoint R') :=
        specializationCycle_baseChangeFamily_familyAssociatedToClosedSubscheme R' f r _ hZ
    _ = baseChangeSpecialFibreCycle R' f r
          (specializationCycle f r (integralGenericCycle f r ξ)) := by
        rw [← hgen, specializationCycle_familyAssociatedToClosedSubscheme_genericPoint f
          (specializationClosure f ξ).subschemeι r hZ]
        exact (baseChangeFiberCycleOfEq_family f (specMapAlgebraMap R R')
          (specMapAlgebraMap_closedPoint R R') r
          (familyAssociatedToClosedSubscheme f (specializationClosure f ξ).subschemeι r)).symm

/-- **Stacks Project, Tag 0H4K** reduced to its integral-subscheme case. The content of this
step is the passage from the fundamental cycle of a single integral closed subscheme of `X_K` to
an arbitrary `r`-cycle on `X_K`: the coefficient of `sp_{X'/R'}` of a base change is a locally
finite sum over the points of `X'_{K'}`, which is regrouped along the fibres of `X'_{K'} ⟶ X_K`
and each group identified with the corresponding term of the base change of `sp_{X/R}`.

The hypothesis is `Stacks.Chow.specializationCompatibleWithBaseChange`, so the square commutes
unconditionally: that is
`Stacks.Chow.baseChangeFiberCycleOfEq_comp_specializationCycleHom`. -/
theorem baseChangeFiberCycleOfEq_comp_specializationCycleHom_of_generator
    (hgen : SpecializationCompatibleWithBaseChange R' f r) :
    (baseChangeSpecialFibreCycle R' f r).comp (specializationCycleHom f r) =
      (specializationCycleHom (pullback.snd f (specMapAlgebraMap R R')) r).comp
        (baseChangeGenericFibreCycle R' f r) := by
  classical
  apply AddMonoidHom.ext
  intro c
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x
  obtain ⟨q, m, hm⟩ := exists_coeff_baseChangeFiberCycleOfEq f (specMapAlgebraMap R R')
    (specMapAlgebraMap_genericPoint R R') r
  obtain ⟨q₀, m₀, hm₀⟩ := exists_coeff_baseChangeFiberCycleOfEq f (specMapAlgebraMap R R')
    (specMapAlgebraMap_closedPoint R R') r
  have hm' : ∀ (z : FiberCycleGroup f (genericPoint (Spec (.of R))) r)
      (y : (pullback.snd f (specMapAlgebraMap R R')).fiber (genericPoint (Spec (.of R')))),
      (baseChangeGenericFibreCycle R' f r z).1 y = z.1 (q y) * m y := hm
  have hm₀' : ∀ (z : FiberCycleGroup f (IsLocalRing.closedPoint R) r)
      (y : (pullback.snd f (specMapAlgebraMap R R')).fiber (IsLocalRing.closedPoint R')),
      (baseChangeSpecialFibreCycle R' f r z).1 y = z.1 (q₀ y) * m₀ y := hm₀
  have hgroup : ∀ ξ : f.fiber (genericPoint (Spec (.of R))),
      (∑' z : q ⁻¹' {ξ}, (baseChangeGenericFibreCycle R' f r c).1 z.1 *
          (specializationCycle (pullback.snd f (specMapAlgebraMap R R')) r
            (integralGenericCycle (pullback.snd f (specMapAlgebraMap R R')) r z.1)).1 x) =
        c.1 ξ * (baseChangeSpecialFibreCycle R' f r
          (specializationCycle f r (integralGenericCycle f r ξ))).1 x := by
    intro ξ
    by_cases hd : fiberPointDimension f (genericPoint (Spec (.of R))) ξ = (r : ℤ)
    · have hsupp : Function.support (fun z ↦
          (baseChangeGenericFibreCycle R' f r (integralGenericCycle f r ξ)).1 z *
            (specializationCycle (pullback.snd f (specMapAlgebraMap R R')) r
              (integralGenericCycle (pullback.snd f (specMapAlgebraMap R R')) r z)).1 x) ⊆
          q ⁻¹' {ξ} := by
        intro z hz
        by_contra hne
        have h0 : (baseChangeGenericFibreCycle R' f r (integralGenericCycle f r ξ)).1 z = 0 := by
          rw [hm' (integralGenericCycle f r ξ) z,
            integralGenericCycle_apply_eq_zero f r ξ (q z) (Or.inl hne), zero_mul]
        exact hz (by simp only [h0, zero_mul])
      have hA := (hasSum_subtype_iff_of_support_subset hsupp).2
        (hasSum_specializationCycle_of_forall (pullback.snd f (specMapAlgebraMap R R')) r
          (baseChangeGenericFibreCycle R' f r (integralGenericCycle f r ξ)) x)
      have hB : HasSum (fun z : q ⁻¹' {ξ} ↦
          (baseChangeGenericFibreCycle R' f r c).1 z.1 *
            (specializationCycle (pullback.snd f (specMapAlgebraMap R R')) r
              (integralGenericCycle (pullback.snd f (specMapAlgebraMap R R')) r z.1)).1 x)
          (c.1 ξ * (specializationCycle (pullback.snd f (specMapAlgebraMap R R')) r
            (baseChangeGenericFibreCycle R' f r (integralGenericCycle f r ξ))).1 x) := by
        refine (hA.mul_left (c.1 ξ)).congr_fun ?_
        intro z
        have hz : q z.1 = ξ := z.2
        simp only [Function.comp_apply]
        rw [hm' c z.1, hm' (integralGenericCycle f r ξ) z.1, hz,
          integralGenericCycle_apply_self f r ξ hd, one_mul, mul_assoc]
      rw [hB.tsum_eq, hgen ξ hd]
    · have hc : c.1 ξ = 0 := by
        by_contra hne
        exact hd (fiberPointDimension_of_coeff_ne_zero f _ r c ξ hne)
      rw [hc, zero_mul, ← tsum_zero]
      refine tsum_congr fun z ↦ ?_
      have hz : q z.1 = ξ := z.2
      rw [hm' c z.1, hz, hc, zero_mul, zero_mul]
  have hleft : HasSum (fun ξ : f.fiber (genericPoint (Spec (.of R))) ↦
      c.1 ξ * (baseChangeSpecialFibreCycle R' f r
        (specializationCycle f r (integralGenericCycle f r ξ))).1 x)
      ((specializationCycle (pullback.snd f (specMapAlgebraMap R R')) r
        (baseChangeGenericFibreCycle R' f r c)).1 x) :=
    ((hasSum_specializationCycle_of_forall (pullback.snd f (specMapAlgebraMap R R')) r
      (baseChangeGenericFibreCycle R' f r c) x).tsum_fiberwise q).congr_fun
      fun ξ ↦ (hgroup ξ).symm
  have hright : HasSum (fun ξ : f.fiber (genericPoint (Spec (.of R))) ↦
      c.1 ξ * (baseChangeSpecialFibreCycle R' f r
        (specializationCycle f r (integralGenericCycle f r ξ))).1 x)
      ((baseChangeSpecialFibreCycle R' f r (specializationCycle f r c)).1 x) := by
    rw [hm₀' (specializationCycle f r c) x]
    refine ((hasSum_specializationCycle_of_forall f r c (q₀ x)).mul_right (m₀ x)).congr_fun ?_
    intro ξ
    rw [hm₀' (specializationCycle f r (integralGenericCycle f r ξ)) x, mul_assoc]
  exact hright.unique hleft

/-- **Stacks Project, Tag 0H4K.** Let `R'/R` be an extension of discrete valuation rings,
inducing a fraction field extension `K'/K` and a residue field extension `κ'/κ`, let `X` be
locally of finite type over `R` and let `X' = X_{R'}`. For `r ≥ 0` the square formed by the
specialization homomorphisms `sp_{X/R} : Z_r(X_K) ⟶ Z_r(X_κ)` and
`sp_{X'/R'} : Z_r(X'_{K'}) ⟶ Z_r(X'_{κ'})` of Section 0H4H and the base change maps of
Section 0H4E commutes.

The integral-subscheme case is
`Stacks.Chow.specializationCompatibleWithBaseChange` and the passage from it to an arbitrary
cycle is `Stacks.Chow.baseChangeFiberCycleOfEq_comp_specializationCycleHom_of_generator`. -/
@[stacks 0H4K]
theorem baseChangeFiberCycleOfEq_comp_specializationCycleHom :
    (baseChangeSpecialFibreCycle R' f r).comp (specializationCycleHom f r) =
      (specializationCycleHom (pullback.snd f (specMapAlgebraMap R R')) r).comp
        (baseChangeGenericFibreCycle R' f r) :=
  baseChangeFiberCycleOfEq_comp_specializationCycleHom_of_generator R' f r
    (specializationCompatibleWithBaseChange R' f r)

end Extension

end Stacks.Chow

end
