module

public import StacksFrontier.Cotangent.LichtenbaumSchlessingerComparisonCanonical
public import StacksFrontier.Cotangent.LichtenbaumSchlessingerFunctoriality

/-!
# The map of Lichtenbaum–Schlessinger complexes attached to a square

For a commutative square of rings `A → A'`, `B → B'` and compatible presentations `P → P'` with
`f'_t` the image of `f_t` ([Stacks, Tag 09D7]), the three vertical arrows of
`StacksFrontier.Cotangent.LichtenbaumSchlessingerFunctoriality` form a map of complexes
`L → L'`, `B`-linear when `L'` is read over `B` through `B → B'`.

## Main definitions

* `Algebra.Presentation.LichtenbaumSchlessingerHom.freeQuotientMap`: `F/TrivRel → F'/TrivRel'`.
* `Algebra.Presentation.LichtenbaumSchlessingerHom.relationTensorMap`: the vertical arrow
  `Rel/TrivRel ⊗_P B → Rel'/TrivRel' ⊗_{P'} B'`.
* `Algebra.Presentation.LichtenbaumSchlessingerHom.complexMap`: the map of complexes `L → L'`.

## References

* [Stacks Project, Tag 09D7](https://stacks.math.columbia.edu/tag/09D7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct KaehlerDifferential

universe u u' v w

noncomputable section

namespace Algebra.Presentation

/-- The identity of an `S`-module `M`, as an `R`-linear map into `M` with the scalars restricted
along `R → S`, for an `R`-module structure on `M` compatible with the `S`-module structure. -/
def toRestrictScalarsₗ {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (M : Type*)
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M] :
    M →ₗ[R] (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S M) where
  toFun m := m
  map_add' _ _ := rfl
  map_smul' r m := (algebraMap_smul S r m).symm

variable {A : Type u} {A' : Type u'} {B B' : Type (max u u' v)}
  [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
  [Algebra A B] [Algebra A' B'] [Algebra A A'] [Algebra B B']
  {X X' T S : Type w}

namespace LichtenbaumSchlessingerHom

variable {P : Presentation A B X T} {P' : Presentation A' B' X' (T ⊕ S)}
  (f : LichtenbaumSchlessingerHom P P')

/-- The map `F → F'` sends the trivial relations of `P` into the trivial relations of `P'`. -/
theorem trivialRelationsFree_le_comap :
    trivialRelationsFree P ≤ (trivialRelationsFree P').comap f.freeMap := by
  rw [trivialRelationsFree, Submodule.span_le]
  rintro x ⟨⟨s, t⟩, rfl⟩
  refine Submodule.mem_comap.2 ?_
  rw [f.freeMap_trivialRelation]
  exact Submodule.subset_span ⟨(Sum.inl s, Sum.inl t), rfl⟩

/-- The map `F/TrivRel → F'/TrivRel'` induced by `F → F'`. -/
def freeQuotientMap : freeQuotient P →ₛₗ[f.ringHom] freeQuotient P' :=
  Submodule.mapQ _ _ f.freeMap f.trivialRelationsFree_le_comap

/-- `freeQuotientMap` sends the class of `x` to the class of its image under `F → F'`. -/
@[simp]
theorem freeQuotientMap_mk (x : T →₀ P.Ring) :
    f.freeQuotientMap (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f.freeMap x) := rfl

/-- The maps `F/TrivRel → P` and `F'/TrivRel' → P'` commute with `freeQuotientMap` and the ring
map `P → P'`. -/
theorem freeQuotientRelationMap_freeQuotientMap (m : freeQuotient P) :
    freeQuotientRelationMap P' (f.freeQuotientMap m) = f.ringHom (freeQuotientRelationMap P m) := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ m
  exact f.relationMap_freeMap x

/-- The inclusions `Rel/TrivRel → F/TrivRel` and `Rel'/TrivRel' → F'/TrivRel'` commute with
`relationQuotientMap` and `freeQuotientMap`. -/
theorem relationQuotientToFree_relationQuotientMap (q : relationQuotient P) :
    relationQuotientToFree P' (f.relationQuotientMap q) =
      f.freeQuotientMap (relationQuotientToFree P q) := by
  obtain ⟨r, rfl⟩ := Submodule.mkQ_surjective _ q
  rfl

section Square

variable [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B']

/-- The maps `F/TrivRel → F ⊗_P B` and `F'/TrivRel' → F' ⊗_{P'} B'` commute with
`freeQuotientMap` and `freeTensorMap`. -/
theorem freeTensorMap_freeQuotientToTensor (m : freeQuotient P) :
    f.freeTensorMap (freeQuotientToTensor P m) = freeQuotientToTensor P' (f.freeQuotientMap m) := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ m
  rw [Submodule.mkQ_apply, freeQuotientToTensor_mk, f.freeTensorMap_tmul, map_one]
  rfl

/-- The map `Rel/TrivRel ⊗_P B → Rel'/TrivRel' ⊗_{P'} B'` induced by `Rel/TrivRel → Rel'/TrivRel'`
and `B → B'`. -/
def relationTensorMap :
    (B ⊗[P.Ring] relationQuotient P) →ₗ[B] B' ⊗[P'.Ring] relationQuotient P' := by
  letI := ((algebraMap B B').comp (algebraMap P.Ring B)).toAlgebra
  haveI : IsScalarTower P.Ring B B' := IsScalarTower.of_algebraMap_eq' rfl
  letI := f.toHom.toAlgHom.toAlgebra
  haveI : IsScalarTower P.Ring P'.Ring B' :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (f.algebraMap_ringHom x).symm
  refine LinearMap.liftBaseChange B ?_
  refine (TensorProduct.mk P'.Ring B' (relationQuotient P') 1).restrictScalars P.Ring ∘ₗ ?_
  exact { toFun := f.relationQuotientMap
          map_add' := f.relationQuotientMap.map_add
          map_smul' := fun p x ↦ f.relationQuotientMap.map_smulₛₗ p x }

/-- `relationTensorMap` sends `b ⊗ q` to `b' ⊗ q'`, the images of `b` in `B'` and of `q` in
`Rel'/TrivRel'`. -/
@[simp]
theorem relationTensorMap_tmul (b : B) (q : relationQuotient P) :
    f.relationTensorMap (b ⊗ₜ[P.Ring] q) =
      algebraMap B B' b ⊗ₜ[P'.Ring] f.relationQuotientMap q := by
  rw [relationTensorMap, LinearMap.liftBaseChange_tmul, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.restrictScalars_apply, TensorProduct.mk_apply, TensorProduct.smul_tmul',
    Algebra.smul_def, mul_one]
  rfl

/-- The square in degrees `-2`, `-1`, for the boundary map of `L` on `Rel/TrivRel ⊗_P B`. -/
theorem freeTensorMap_relationBoundary (s : B ⊗[P.Ring] relationQuotient P) :
    letI := relationModule P
    letI := relationModule P'
    f.freeTensorMap (relationBoundary P s) = relationBoundary P' (f.relationTensorMap s) := by
  let := relationModule P
  let := relationModule P'
  induction s using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul b q =>
    rw [show b ⊗ₜ[P.Ring] q = b • ((1 : B) ⊗ₜ[P.Ring] q) by rw [smul_tmul', smul_eq_mul, mul_one],
      map_smul, map_smul, map_smul, relationBoundary_tmul_one, f.relationTensorMap_tmul, map_one,
      ← algebraMap_smul B' b ((1 : B') ⊗ₜ[P'.Ring] f.relationQuotientMap q), map_smul,
      relationBoundary_tmul_one, freeTensorMap_freeQuotientToTensor,
      relationQuotientToFree_relationQuotientMap]
    exact (algebraMap_smul B' b _).symm

/-! ### The map of complexes -/

/-- Restriction of scalars along `B → B'`. -/
local notation "𝓡" => ModuleCat.restrictScalars (algebraMap B B')

/-- The map `L → L'` in degree `0`. -/
def complexMapZero : (lichtenbaumSchlessingerComplex P).complex.X 0 ⟶
    (𝓡).obj ((lichtenbaumSchlessingerComplex P').complex.X 0) :=
  (lichtenbaumSchlessingerComplex P).differentialIso.hom ≫
    ConcreteCategory.ofHom (C := ModuleCat B)
      (Y := (𝓡).obj (ModuleCat.of B' (B' ⊗[P'.Ring] Ω[P'.Ring⁄A'])))
      (toRestrictScalarsₗ (B' ⊗[P'.Ring] Ω[P'.Ring⁄A']) ∘ₗ f.differentialTensorMap) ≫
    (𝓡).map (lichtenbaumSchlessingerComplex P').differentialIso.inv

/-- The map `L → L'` in degree `-1`. -/
def complexMapOne : (lichtenbaumSchlessingerComplex P).complex.X (-1) ⟶
    (𝓡).obj ((lichtenbaumSchlessingerComplex P').complex.X (-1)) :=
  (lichtenbaumSchlessingerComplex P).freeIso.hom ≫
    ConcreteCategory.ofHom (C := ModuleCat B)
      (Y := (𝓡).obj (ModuleCat.of B' (B' ⊗[P'.Ring] ((T ⊕ S) →₀ P'.Ring))))
      (toRestrictScalarsₗ (B' ⊗[P'.Ring] ((T ⊕ S) →₀ P'.Ring)) ∘ₗ f.freeTensorMap) ≫
    (𝓡).map (lichtenbaumSchlessingerComplex P').freeIso.inv

/-- The map `L → L'` in degree `-2`. -/
def complexMapTwo : (lichtenbaumSchlessingerComplex P).complex.X (-2) ⟶
    (𝓡).obj ((lichtenbaumSchlessingerComplex P').complex.X (-2)) :=
  (lichtenbaumSchlessingerComplex P).relationIso.hom ≫
    ConcreteCategory.ofHom (C := ModuleCat B)
      (Y := (𝓡).obj (ModuleCat.of B' (B' ⊗[P'.Ring] relationQuotient P')))
      (toRestrictScalarsₗ (B' ⊗[P'.Ring] relationQuotient P') ∘ₗ f.relationTensorMap) ≫
    (𝓡).map (lichtenbaumSchlessingerComplex P').relationIso.inv

/-- Under the identifications of the degree `0` terms with `Ω_{P/A} ⊗_P B` and
`Ω_{P'/A'} ⊗_{P'} B'`, `complexMapZero` is `differentialTensorMap`. -/
theorem complexMapZero_apply (z : (lichtenbaumSchlessingerComplex P).complex.X 0) :
    (lichtenbaumSchlessingerComplex P').differentialIso.hom (f.complexMapZero z) =
      f.differentialTensorMap ((lichtenbaumSchlessingerComplex P).differentialIso.hom z) :=
  Iso.inv_hom_id_apply _ _

/-- Under the identifications of the degree `-1` terms with `F ⊗_P B` and `F' ⊗_{P'} B'`,
`complexMapOne` is `freeTensorMap`. -/
theorem complexMapOne_apply (z : (lichtenbaumSchlessingerComplex P).complex.X (-1)) :
    (lichtenbaumSchlessingerComplex P').freeIso.hom (f.complexMapOne z) =
      f.freeTensorMap ((lichtenbaumSchlessingerComplex P).freeIso.hom z) :=
  Iso.inv_hom_id_apply _ _

/-- Under the identifications of the degree `-2` terms with `Rel/TrivRel ⊗_P B` and
`Rel'/TrivRel' ⊗_{P'} B'`, `complexMapTwo` is `relationTensorMap`. -/
theorem complexMapTwo_apply (z : (lichtenbaumSchlessingerComplex P).complex.X (-2)) :
    (lichtenbaumSchlessingerComplex P').relationIso.hom (f.complexMapTwo z) =
      f.relationTensorMap ((lichtenbaumSchlessingerComplex P).relationIso.hom z) :=
  Iso.inv_hom_id_apply _ _

/-- The square formed by `complexMapOne`, `complexMapZero` and the differentials of `L` and `L'`
in degrees `-1 → 0` commutes. -/
theorem complexMap_square_zero :
    f.complexMapOne ≫ (𝓡).map ((lichtenbaumSchlessingerComplex P').complex.d (-1) 0) =
      (lichtenbaumSchlessingerComplex P).complex.d (-1) 0 ≫ f.complexMapZero := by
  refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
  apply (ModuleCat.mono_iff_injective
    (lichtenbaumSchlessingerComplex P').differentialIso.hom).1 inferInstance
  show (lichtenbaumSchlessingerComplex P').differentialIso.hom
      ((lichtenbaumSchlessingerComplex P').complex.d (-1) 0
        ((lichtenbaumSchlessingerComplex P').freeIso.inv
          (f.freeTensorMap ((lichtenbaumSchlessingerComplex P).freeIso.hom z)))) =
    (lichtenbaumSchlessingerComplex P').differentialIso.hom
      ((lichtenbaumSchlessingerComplex P').differentialIso.inv
        (f.differentialTensorMap ((lichtenbaumSchlessingerComplex P).differentialIso.hom
          ((lichtenbaumSchlessingerComplex P).complex.d (-1) 0 z))))
  rw [lsComplex_d_negOne_inv_apply, Iso.inv_hom_id_apply,
    ← f.differentialTensorMap_relationDifferentialB,
    ← lsComplex_d_negOne_inv_apply P ((lichtenbaumSchlessingerComplex P).freeIso.hom z),
    Iso.hom_inv_id_apply]

/-- The square formed by `complexMapTwo`, `complexMapOne` and the differentials of `L` and `L'`
in degrees `-2 → -1` commutes. -/
theorem complexMap_square_one :
    f.complexMapTwo ≫ (𝓡).map ((lichtenbaumSchlessingerComplex P').complex.d (-2) (-1)) =
      (lichtenbaumSchlessingerComplex P).complex.d (-2) (-1) ≫ f.complexMapOne := by
  let := relationModule P
  let := relationModule P'
  refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
  apply (ModuleCat.mono_iff_injective
    (lichtenbaumSchlessingerComplex P').freeIso.hom).1 inferInstance
  show (lichtenbaumSchlessingerComplex P').freeIso.hom
      ((lichtenbaumSchlessingerComplex P').complex.d (-2) (-1)
        ((lichtenbaumSchlessingerComplex P').relationIso.inv
          (f.relationTensorMap ((lichtenbaumSchlessingerComplex P).relationIso.hom z)))) =
    (lichtenbaumSchlessingerComplex P').freeIso.hom
      ((lichtenbaumSchlessingerComplex P').freeIso.inv
        (f.freeTensorMap ((lichtenbaumSchlessingerComplex P).freeIso.hom
          ((lichtenbaumSchlessingerComplex P).complex.d (-2) (-1) z))))
  rw [lsComplex_d_negTwo_inv_apply, Iso.inv_hom_id_apply, ← f.freeTensorMap_relationBoundary,
    ← lsComplex_d_negTwo_inv_apply P ((lichtenbaumSchlessingerComplex P).relationIso.hom z),
    Iso.hom_inv_id_apply]

/-- The component of `L → L'` in degree `i`. -/
def complexMapComponent (i : ℤ) : (lichtenbaumSchlessingerComplex P).complex.X i ⟶
    (𝓡).obj ((lichtenbaumSchlessingerComplex P').complex.X i) :=
  if h0 : i = 0 then eqToHom (by rw [h0]) ≫ f.complexMapZero ≫ eqToHom (by rw [h0])
  else if h1 : i = -1 then eqToHom (by rw [h1]) ≫ f.complexMapOne ≫ eqToHom (by rw [h1])
  else if h2 : i = -2 then eqToHom (by rw [h2]) ≫ f.complexMapTwo ≫ eqToHom (by rw [h2])
  else 0

/-- The degree `0` component of `L → L'` is `complexMapZero`. -/
theorem complexMapComponent_zero : f.complexMapComponent 0 = f.complexMapZero := by
  simp [complexMapComponent]

/-- The degree `-1` component of `L → L'` is `complexMapOne`. -/
theorem complexMapComponent_negOne : f.complexMapComponent (-1) = f.complexMapOne := by
  simp [complexMapComponent]

/-- The degree `-2` component of `L → L'` is `complexMapTwo`. -/
theorem complexMapComponent_negTwo : f.complexMapComponent (-2) = f.complexMapTwo := by
  simp [complexMapComponent]

/-- The component of `L → L'` in a degree `i ∉ {0, -1, -2}` is zero. -/
theorem complexMapComponent_eq_zero (i : ℤ) (h0 : i ≠ 0) (h1 : i ≠ -1) (h2 : i ≠ -2) :
    f.complexMapComponent i = 0 := by
  rw [complexMapComponent, dif_neg h0, dif_neg h1, dif_neg h2]

/-- The canonical map of Lichtenbaum–Schlessinger complexes `L → L'` attached to compatible
presentations of a commutative square of rings: the arrows `Rel/TrivRel → Rel'/TrivRel'`,
`F ⊗_P B → F' ⊗_{P'} B'`, `Ω_{P/A} ⊗_P B → Ω_{P'/A'} ⊗_{P'} B'` (tensored up to `B'`), which
commute with the differentials. It is `B`-linear, `L'` being read over `B` along `B → B'`. -/
@[stacks 09D7 "the first commutative diagram: the canonical map of Lichtenbaum–Schlessinger
complexes L → L' with vertical arrows Rel/TrivRel → Rel'/TrivRel', F ⊗_P B → F' ⊗_{P'} B',
Ω_{P/A} ⊗_P B → Ω_{P'/A'} ⊗_{P'} B'"]
def complexMap : (lichtenbaumSchlessingerComplex P).complex ⟶
    ((𝓡).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (lichtenbaumSchlessingerComplex P').complex where
  f := f.complexMapComponent
  comm' i j hij := by
    have hij' : i + 1 = j := hij
    change f.complexMapComponent i ≫ (𝓡).map ((lichtenbaumSchlessingerComplex P').complex.d i j) =
      (lichtenbaumSchlessingerComplex P).complex.d i j ≫ f.complexMapComponent j
    by_cases e1 : i = -1
    · subst e1
      obtain rfl : j = 0 := by omega
      rw [complexMapComponent_negOne, complexMapComponent_zero, complexMap_square_zero]
    by_cases e2 : i = -2
    · subst e2
      obtain rfl : j = -1 := by omega
      rw [complexMapComponent_negTwo, complexMapComponent_negOne, complexMap_square_one]
    by_cases e3 : i = -3
    · subst e3
      obtain rfl : j = -2 := by omega
      exact ((lichtenbaumSchlessingerComplex P).isZero_X (-3) (by decide) (by decide)
        (by decide)).eq_of_src _ _
    by_cases e0 : i = 0
    · subst e0
      obtain rfl : j = 1 := by omega
      exact (((lichtenbaumSchlessingerComplex P').isZero_X 1 (by decide) (by decide)
        (by decide)).of_iso (Iso.refl _) |> fun h => (Functor.map_isZero (𝓡) h)).eq_of_tgt _ _
    rw [complexMapComponent_eq_zero f i e0 e1 e2,
      complexMapComponent_eq_zero f j (by omega) (by omega) (by omega), Limits.zero_comp,
      Limits.comp_zero]

/-- The component of `complexMap` in degree `i` is `complexMapComponent i`. -/
theorem complexMap_f (i : ℤ) : f.complexMap.f i = f.complexMapComponent i := rfl

end Square

end LichtenbaumSchlessingerHom

end Algebra.Presentation

end
