module

public import StacksFrontier.CategoryTheory.Triangulated.CompactObjects
public import StacksFrontier.CategoryTheory.Triangulated.GeneratorAdjunction

/-!
# Compact generation travels along the left adjoint of a fully faithful right adjoint

Let `L ⊣ R` be an adjunction of additive functors with `L` commuting with the shift. If `R` is
fully faithful — equivalently, if the counit of the adjunction is invertible — and if `R`
commutes with the direct sums being tested, then the image under `L` of a compact weak generator
is a compact weak generator:

* *compactness*, because `Hom(L K, ∐ A i) = Hom(K, R (∐ A i)) = Hom(K, ∐ R (A i))` is
  `⨁ Hom(K, R (A i)) = ⨁ Hom(L K, A i)`;
* *generation*, because an object `E` right orthogonal to the shifts of `L Q` has `R E` right
  orthogonal to the shifts of `Q`, by the adjunction bijection and the commutation of `L` with
  the shift, so `R E = 0` and then `E ≅ L (R E) = 0` by the counit.

Neither half needs `L` to be fully faithful, and neither needs the categories to be
pretriangulated: the first is the universal property of a direct sum and the second is
orthogonality bookkeeping.

The geometric instance this is written for is restriction along a quasi-compact open immersion
`j : U ⟶ X` of schemes. There `L = j^*` and `R = Rj_*` on the quasi-coherent derived categories,
the counit is invertible because `j` is an open immersion, and `Rj_*` commutes with direct sums by
[Stacks, Tag 08DZ]; so a compact generator of `D_QCoh(𝒪_X)` restricts to one of `D_QCoh(𝒪_U)`.
This is how [Stacks, Tag 09IS] passes from an affine scheme to a quasi-affine one — see
`StacksFrontier/AlgebraicGeometry/Duality/CompactGeneration/QuasiAffineQuasiCoherent.lean`.

## Main results

* `CategoryTheory.isCompactObject_map_of_adjunction` — compactness travels along `L` when `R`
  commutes with the direct sums tested.
* `CategoryTheory.ObjectProperty.rightOrthogonal_shiftClosure_ofObj_map_of_adjunction` — right
  orthogonality to the shifts of the family `L ∘ Q` at `E` gives right orthogonality to the shifts
  of `Q` at `R E`.
* `CategoryTheory.ObjectProperty.isWeakTriangulatedGenerator_ofObj_map_of_reflects_isZero` and
  its singleton companion — generation travels along `L` when `R` reflects zero objects.
* `CategoryTheory.ObjectProperty.isWeakTriangulatedGenerator_ofObj_map_of_isIso_counit` and
  `CategoryTheory.ObjectProperty.isWeakTriangulatedGenerator_singleton_map_of_isIso_counit` —
  the same when the counit is invertible.
* `CategoryTheory.Pretriangulated.isCompactlyGenerated_of_reflects_isZero` and
  `CategoryTheory.Pretriangulated.isCompactlyGenerated_of_isIso_counit` — the two halves
  combined: the target of a left adjoint whose right adjoint is fully faithful and commutes with
  direct sums is compactly generated as soon as the source is.

## Implementation notes

The orthogonality transfer is the counterpart of
`CategoryTheory.ObjectProperty.rightOrthogonal_shiftClosure_singleton_map_of_isIso_unit`, which
moves an object *forward* along `L` and therefore needs the unit at that object to be invertible.
Moving the object *backward* along `R` needs nothing: it is the adjunction bijection and the
commutation isomorphism of `L` with the shift, so it is stated with no hypothesis beyond
`L.CommShift ℤ`.

Compactness is stated with the coproduct-preservation of `R` as an instance argument over all
`I : Type w`, which is the shape in which [Stacks, Tag 08DZ] is stated. The proof is the commutative
square of `CategoryTheory.bijective_cofanMap_of_adjunction` read in the opposite direction: that
lemma deduces bijectivity for `K` against the family `R.map (j i)` from compactness of `L.obj K`,
whereas here compactness of `K` against that family — which is genuine compactness because `R`
preserves the direct sum — gives bijectivity for `L.obj K` against `j`.

## References

* [Stacks Project, Tag 07LS](https://stacks.math.columbia.edu/tag/07LS)
* [Stacks Project, Tag 09SQ](https://stacks.math.columbia.edu/tag/09SQ)
* [Stacks Project, Tag 09IS](https://stacks.math.columbia.edu/tag/09IS)
* [Stacks Project, Tag 08DZ](https://stacks.math.columbia.edu/tag/08DZ)
-/

@[expose] public noncomputable section

open CategoryTheory.Limits CategoryTheory.ObjectProperty CategoryTheory.Pretriangulated

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

/-! ### Compactness -/

section Compactness

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D]

/-- **Compactness travels along the left adjoint of a coproduct-preserving right adjoint.** Let
`L ⊣ R` be an adjunction of additive functors and suppose `R` commutes with direct sums indexed by
`Type w`. If `K` is a compact object of the source, then `L.obj K` is a compact object of the
target.

A morphism `L K ⟶ ∐ A` is a morphism `K ⟶ R (∐ A)`, and `R (∐ A)` is the direct sum of the
`R (A i)`, so compactness of `K` makes the group of such morphisms the direct sum of the
`K ⟶ R (A i)`, which are the `L K ⟶ A i`. -/
lemma isCompactObject_map_of_adjunction {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    (adj : L ⊣ R) [∀ I : Type w, PreservesColimitsOfShape (Discrete I) R]
    {K : C} (hK : IsCompactObject.{w} K) : IsCompactObject.{w} (L.obj K) := by
  classical
  refine ⟨fun {I} _ A _ => ?_⟩
  have hc : IsColimit (Cofan.mk (R.obj (∐ A)) fun i => R.map (Limits.Sigma.ι A i)) :=
    (isColimitMapCoconeCofanMkEquiv R A (Limits.Sigma.ι A))
      (isColimitOfPreserves R (coproductIsCoproduct A))
  have hKR : Function.Bijective (cofanMap K fun i => R.map (Limits.Sigma.ι A i)) :=
    bijective_cofanMap K hK _ hc
  have hEq : (cofanMap K fun i => R.map (Limits.Sigma.ι A i)).comp
        (DirectSum.map fun i => (adj.homAddEquiv K (A i)).toAddMonoidHom) =
      (adj.homAddEquiv K (∐ A)).toAddMonoidHom.comp (cofanMap (L.obj K) (Limits.Sigma.ι A)) := by
    refine DirectSum.addHom_ext fun i f => ?_
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, DirectSum.map_of,
      AddEquiv.coe_toAddMonoidHom, cofanMap_of, Adjunction.homAddEquiv_apply]
    exact (adj.homEquiv_naturality_right f (Limits.Sigma.ι A i)).symm
  show Function.Bijective (cofanMap (L.obj K) (Limits.Sigma.ι A))
  refine (Function.Bijective.of_comp_iff' (adj.homAddEquiv K (∐ A)).bijective _).mp ?_
  have hcomp : (adj.homAddEquiv K (∐ A)) ∘ (cofanMap (L.obj K) (Limits.Sigma.ι A)) =
      (cofanMap K fun i => R.map (Limits.Sigma.ι A i)) ∘
        (DirectSum.map fun i => (adj.homAddEquiv K (A i)).toAddMonoidHom) :=
    funext fun x => (DFunLike.congr_fun hEq x).symm
  rw [hcomp]
  exact hKR.comp (bijective_directSumMap _ fun i => (adj.homAddEquiv K (A i)).bijective)

end Compactness

/-! ### Generation -/

namespace ObjectProperty

section Generation

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasShift C ℤ]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasShift D ℤ]

/-- **Right orthogonality transports backward along the right adjoint.** Let `L ⊣ R` with `L`
commuting with the shift and let `Q : ι → C` be a family. If `E` is right orthogonal to all shifts
of all the `L (Q i)`, then `R E` is right orthogonal to all shifts of all the `Q i`.

A morphism `f : (Q i)⟦a⟧ ⟶ R E` is the adjunct of a morphism `L ((Q i)⟦a⟧) ⟶ E`, which after the
commutation isomorphism `L ((Q i)⟦a⟧) ≅ (L (Q i))⟦a⟧` is a morphism out of a shift of `L (Q i)`
and therefore vanishes; the adjunction bijection is injective, so `f` vanishes.

This is the counterpart of
`CategoryTheory.ObjectProperty.rightOrthogonal_shiftClosure_singleton_map_of_isIso_unit`, which
transports an object forward along `L` and needs the unit there to be invertible. Backwards no
hypothesis is needed. -/
theorem rightOrthogonal_shiftClosure_ofObj_map_of_adjunction {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) [L.Additive] [L.CommShift ℤ] {ι : Type*} (Q : ι → C) {E : D}
    (hE : ((ofObj fun i => L.obj (Q i)).shiftClosure ℤ).rightOrthogonal E) :
    ((ofObj Q).shiftClosure ℤ).rightOrthogonal (R.obj E) := by
  have : R.Additive := adj.right_adjoint_additive
  rw [rightOrthogonal_shiftClosure_ofObj_iff] at hE ⊢
  intro i a f
  set g := (adj.homEquiv ((shiftFunctor C a).obj (Q i)) E).symm f with hg
  set e := (L.commShiftIso (A := ℤ) a).app (Q i) with he
  have hzero : e.inv ≫ g = 0 := hE i a _
  have hg0 : g = 0 := by
    rw [show g = e.hom ≫ e.inv ≫ g by rw [Iso.hom_inv_id_assoc], hzero, comp_zero]
  rw [show f = adj.homEquiv ((shiftFunctor C a).obj (Q i)) E g by
      rw [hg, Equiv.apply_symm_apply], hg0, adj.homEquiv_unit, Functor.map_zero, comp_zero]

/-- **Generation travels along the left adjoint of a right adjoint that reflects zero objects.**
Let `L ⊣ R` with `L` additive and commuting with the shift, and suppose an object `E` of the
target with `R E = 0` is itself zero. If the family `Q : ι → C` is a weak generator of `C`, then
the family `L ∘ Q` is a weak generator of `D`.

An object `E` right orthogonal to the shifts of the `L (Q i)` has `R E` right orthogonal to the
shifts of the `Q i`, hence `R E = 0`, hence `E = 0`.

The hypothesis on `R` is the weakest form of "`R` is conservative" the argument uses; it holds in
particular when the counit of the adjunction is invertible, which is
`CategoryTheory.ObjectProperty.isWeakTriangulatedGenerator_ofObj_map_of_isIso_counit`. -/
theorem isWeakTriangulatedGenerator_ofObj_map_of_reflects_isZero {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) [L.Additive] [L.CommShift ℤ] (hR : ∀ E : D, IsZero (R.obj E) → IsZero E)
    {ι : Type*} (Q : ι → C) (hQ : (ofObj Q).IsWeakTriangulatedGenerator) :
    (ofObj fun i => L.obj (Q i)).IsWeakTriangulatedGenerator := fun E hE =>
  hR E (hQ _ (rightOrthogonal_shiftClosure_ofObj_map_of_adjunction adj Q hE))

omit [HasShift C ℤ] [HasShift D ℤ] in
/-- **An invertible counit makes the right adjoint reflect zero objects**: if `E ≅ L (R E)` and
`R E = 0` then `E = 0`, since `L` is additive. -/
theorem isZero_of_isZero_obj_of_isIso_counit {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [L.Additive]
    (hcounit : ∀ E : D, IsIso (adj.counit.app E)) (E : D) (h : IsZero (R.obj E)) : IsZero E :=
  have : IsIso (adj.counit.app E) := hcounit E
  (L.map_isZero h).of_iso (asIso (adj.counit.app E)).symm

/-- **Generation travels along the left adjoint of a fully faithful right adjoint.** Let `L ⊣ R`
with `L` additive and commuting with the shift and with the counit of the adjunction invertible —
that is, with `R` fully faithful. If the family `Q : ι → C` is a weak generator of `C`, then the
family `L ∘ Q` is a weak generator of `D`.

An object `E` right orthogonal to the shifts of the `L (Q i)` has `R E` right orthogonal to the
shifts of the `Q i`, hence `R E = 0`; the counit then identifies `E` with `L (R E)`, which is
zero. -/
theorem isWeakTriangulatedGenerator_ofObj_map_of_isIso_counit {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) [L.Additive] [L.CommShift ℤ] (hcounit : ∀ E : D, IsIso (adj.counit.app E))
    {ι : Type*} (Q : ι → C) (hQ : (ofObj Q).IsWeakTriangulatedGenerator) :
    (ofObj fun i => L.obj (Q i)).IsWeakTriangulatedGenerator :=
  isWeakTriangulatedGenerator_ofObj_map_of_reflects_isZero adj
    (isZero_of_isZero_obj_of_isIso_counit adj hcounit) Q hQ

/-- **Generation by a single object travels along the left adjoint of a fully faithful right
adjoint**: the one-member-family case of
`CategoryTheory.ObjectProperty.isWeakTriangulatedGenerator_ofObj_map_of_isIso_counit`, read
through `CategoryTheory.ObjectProperty.singleton`, which is by definition `ofObj` of the constant
family on `Unit`. -/
theorem isWeakTriangulatedGenerator_singleton_map_of_isIso_counit {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) [L.Additive] [L.CommShift ℤ] (hcounit : ∀ E : D, IsIso (adj.counit.app E))
    {P : C} (hP : (singleton P).IsWeakTriangulatedGenerator) :
    (singleton (L.obj P)).IsWeakTriangulatedGenerator :=
  isWeakTriangulatedGenerator_ofObj_map_of_isIso_counit adj hcounit (fun _ : Unit => P) hP

/-- **Generation by a single object travels along the left adjoint of a right adjoint that
reflects zero objects**: the one-member-family case of
`CategoryTheory.ObjectProperty.isWeakTriangulatedGenerator_ofObj_map_of_reflects_isZero`. -/
theorem isWeakTriangulatedGenerator_singleton_map_of_reflects_isZero {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) [L.Additive] [L.CommShift ℤ] (hR : ∀ E : D, IsZero (R.obj E) → IsZero E)
    {P : C} (hP : (singleton P).IsWeakTriangulatedGenerator) :
    (singleton (L.obj P)).IsWeakTriangulatedGenerator :=
  isWeakTriangulatedGenerator_ofObj_map_of_reflects_isZero adj hR (fun _ : Unit => P) hP

end Generation

end ObjectProperty

/-! ### The two halves combined -/

namespace Pretriangulated

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasShift C ℤ]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasShift D ℤ]

/-- **Compact generation travels along the left adjoint of a fully faithful, coproduct-preserving
right adjoint.** Let `L ⊣ R` be an adjunction with `L` additive and commuting with the shift,
with `R` commuting with direct sums indexed by `Type w`, and with the counit invertible. If `C` is
compactly generated in the sense of [Stacks, Tag 09SQ], then so is `D`: the image under `L` of a
compact generating family is one.

This is `CategoryTheory.isCompactObject_map_of_adjunction` together with
`CategoryTheory.ObjectProperty.isWeakTriangulatedGenerator_ofObj_map_of_isIso_counit`. -/
theorem isCompactlyGenerated_of_reflects_isZero {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    [L.Additive] [L.CommShift ℤ] [∀ I : Type w, PreservesColimitsOfShape (Discrete I) R]
    (hR : ∀ E : D, IsZero (R.obj E) → IsZero E)
    (hC : IsCompactlyGenerated.{w} C) : IsCompactlyGenerated.{w} D := by
  have : R.Additive := adj.right_adjoint_additive
  obtain ⟨ι, Q, hcompact, hgen⟩ := hC
  exact ⟨ι, fun i => L.obj (Q i),
    fun i => isCompactObject_map_of_adjunction adj (hcompact i),
    ObjectProperty.isWeakTriangulatedGenerator_ofObj_map_of_reflects_isZero adj hR Q hgen⟩

/-- `CategoryTheory.Pretriangulated.isCompactlyGenerated_of_reflects_isZero` with the hypothesis
on `R` in the form "the counit is invertible", i.e. "`R` is fully faithful". -/
theorem isCompactlyGenerated_of_isIso_counit {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    [L.Additive] [L.CommShift ℤ] [∀ I : Type w, PreservesColimitsOfShape (Discrete I) R]
    (hcounit : ∀ E : D, IsIso (adj.counit.app E))
    (hC : IsCompactlyGenerated.{w} C) : IsCompactlyGenerated.{w} D :=
  isCompactlyGenerated_of_reflects_isZero adj
    (ObjectProperty.isZero_of_isZero_obj_of_isIso_counit adj hcounit) hC

end Pretriangulated

end CategoryTheory

end
