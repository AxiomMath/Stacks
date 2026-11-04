module

public import Mathlib.CategoryTheory.Center.Preadditive
public import Mathlib.CategoryTheory.Retract
public import StacksFrontier.CategoryTheory.Center.Shift

/-!
# Where two central elements agree, and what a dévissage can and cannot see

Let `C` be a category and let `z, w : CatCenter C` be two central elements, that is, two
endomorphisms of the identity functor. The *agreement locus* of `z` and `w` is the class of
objects `X` with `z.app X = w.app X`. This file collects its closure properties and uses them to
reduce the surjectivity of `ModuleCat.centerToShiftCenterDerived` — the one input that
[Stacks, Tag 09SD](https://stacks.math.columbia.edu/tag/09SD) defers to Rickard, and the one
input `StacksFrontier/RingTheory/DerivedEquivalenceCenter.lean` assumes — to a statement about
complexes concentrated in a single degree.

The agreement locus is closed under isomorphisms and under composition with arbitrary morphisms
(both are naturality), under retracts and under coproducts (the inclusions are jointly
epimorphic), and, for shift-compatible elements, under shifting and unshifting. What it is
**not** closed under is
two-out-of-three in a distinguished triangle, and that is not a gap in the argument below but a
fact about triangulated categories:

## The two-out-of-three step is false, so the dévissage of Tag 0FQE does not apply

`DifferentialGradedModule.General.property_of_coproducts_of_two_out_of_three_of_shifts`
([Stacks, Tag 0FQE]) and `StacksDraft.CompactDevissage.isIso_app_of_isCompactlyGenerated`
([Stacks, Tag 09SN]) both reduce a property of all objects of a derived category to the shifts of
a generator, and both require the property to propagate along a distinguished triangle. For
*invertibility* of a morphism of functors that propagation is the five lemma, which is why the
second of those dévissages is stated for invertibility. For *agreement* of two central elements
it fails. What naturality gives is only nilpotence, and that is exactly what
`CategoryTheory.CatCenter.app_comp_app_eq_zero_obj₃` and
`CategoryTheory.CatCenter.app_comp_app_eq_zero_obj₂` below prove: if a central element `δ`
vanishes at two vertices of a distinguished triangle then its component at the third vertex
squares to zero. It need not vanish.

Nor is the deficit an artefact of the proof. If a shift-compatible central element of a
compactly generated triangulated category were determined by its component at a compact
generator, then the following would be true, and it is false. Let `k` be a field, let
`Λ = k[x]/(x⁴)`, and let `StMod Λ` be the stable module category, a compactly generated
triangulated category whose compact objects are the finite-dimensional modules; the simple module
`k` is a compact generator, since every finite-dimensional `Λ`-module is a finite iterated
extension of copies of `k`. The central element `x` of `Λ` acts on every module, compatibly with
the syzygy functor, hence is a shift-compatible central element of `StMod Λ`. It acts as zero on
`k`, and it does not act as zero on `k[x]/(x²)`: multiplication by `x` on `k[x]/(x²)` has image
`(x)/(x²) ≠ 0`, while every map `k[x]/(x²) ⟶ Λ` lands in `(x²)` and so every endomorphism of
`k[x]/(x²)` factoring through a projective is zero. (Krause and Ye compute the whole degree-zero
centre of this stable category: `Z⁰(stmod k[x]/(xⁿ)) ≅ k[x]/(x^⌊n/2⌋)`.)

So surjectivity of `ModuleCat.centerToShiftCenterDerived` cannot be proved from naturality,
additivity, coproducts, compatibility with the shift and distinguished triangles alone: such an
argument would prove the false statement above. It needs an input special to the derived category
of a ring. This file isolates that input.

## Nor does representability of a derived equivalence by a bimodule remove it

[Stacks, Tag 09SA] is available in this library, as
`DifferentialGraded.Bimodule.exists_bimodule_of_derivedEquivalence`: an additive, `R`-linear,
shift-commuting equivalence `F : D(A, d) ≌ D(B, d)` with `A = H^0(A)` and `B` K-flat over `R`
comes with a differential graded `(A, B)`-bimodule `N` whose derived tensor functor
`G = - ⊗_A^𝐋 N` is an equivalence and whose class in `D(B, d)` is isomorphic to `F(A)`. That is
representability of the *value at the regular module*, not of the functor: an isomorphism
`G ≅ F` of functors is not part of the conclusion, and [Stacks, Tag 09SB] opens by declining to
assert one. The formalization of that remark reaches a natural isomorphism of `G` with `F` over
the retracts of direct sums of shifts of `A` (`DifferentialGraded.Bimodule.retractNatIso`) and no
further, and its implementation notes explain why it cannot be pushed to all graded projective
modules: that class contains a model of every object of `D(A, d)`, so the extension would be the
isomorphism of functors the source declines.

What the extension principle below would need is a statement one level lower, about natural
transformations rather than about functors: that every shift-compatible endomorphism of the
identity of `D(A)` is `- ⊗_A^𝐋 φ` for an endomorphism `φ` of the diagonal bimodule, that is, that
the comparison `HH^0(A) = End_{D(A^{opp} ⊗_R A, d)}(A) → Z_shift(D(A))` is surjective. A natural
endomorphism of the identity is not a functor, so 09SA does not apply to it; the only equivalence
there is to feed it here is the identity, whose bimodule is the regular one and which says
nothing about the endomorphism.

## The identification of `HH^0` with the centre is available and is not what is missing

`DifferentialGraded.Bimodule.centerAlgEquivDiagonalDerivedEnd` proves that for a differential
graded algebra concentrated in degree zero left multiplication is an isomorphism of `R`-algebras
`Z(A) ≅ End_{D(A^{opp} ⊗_R A, d)}(A)`, which is the source's `HH^0(A, d) = Z(A)` of
[Stacks, Tag 09ST]. That is the *left*-hand end of the chain
`Z(A) ≅ HH^0(A) → Z_shift(D(A))`, and the composite is the map
`ModuleCat.centerToShiftCenterDerived` whose surjectivity is owed here. So the two statements are
equivalent given the identification, and the identification therefore cannot supply the
surjectivity: what remains is exactly that every shift-compatible central element of `D(A)` comes
from an endomorphism of the diagonal bimodule, which is Rickard's Proposition 9.2.

## What is proved here

For a shift-compatible central element `z` of `D(A)` there is a central element
`ModuleCat.derivedCenterValue R A z` of `A` whose degreewise action agrees with `z` at
*every* module in *every* degree — not merely at the regular module, which is all a dévissage
along the generator would give. Consequently `z` and that degreewise action agree after
composition with any morphism out of a complex concentrated in a single degree. What remains is
the extension principle `ModuleCat.centerToShiftCenterDerived_surjective_of_ext_single`: a
shift-compatible central element of `D(A)` is determined by its components at the single
complexes. It holds whenever every object of `D(A)` is a coproduct of shifts of modules, by
`ModuleCat.centerToShiftCenterDerived_surjective_of_isoCoproductSingle` — as happens over a
hereditary ring — and in general it is the degree-zero case of the identification of the graded
centre of `D(A)` with Hochschild cohomology.

## Main definitions

* `CategoryTheory.CatCenter.ofFull` and `CategoryTheory.CatCenter.ofFullAlgHom`: a central element
  of `D` pulled back along a fully faithful functor `C ⥤ D`, and that pullback as a morphism of
  `R`-algebras when the functor is additive and `R`-linear.
* `ModuleCat.derivedCenterValue` and `ModuleCat.derivedCenterValueAlgHom`: the central element of
  `A` attached to a central element of `D(ModuleCat A)` by its components at complexes
  concentrated in degree zero, and that assignment as a morphism of `R`-algebras.

## Main results

* `CategoryTheory.CatCenter.app_eq_of_iso`, `CategoryTheory.CatCenter.comp_app_eq_of_app_eq`,
  `CategoryTheory.CatCenter.app_eq_of_retract`,
  `CategoryTheory.CatCenter.app_eq_of_coproduct`,
  `CategoryTheory.CatCenter.app_shift_eq_of_app_eq`,
  `CategoryTheory.CatCenter.app_eq_of_app_shift_eq`: the closure properties of the agreement
  locus.
* `CategoryTheory.CatCenter.app_comp_app_eq_zero_obj₃` and
  `CategoryTheory.CatCenter.app_comp_app_eq_zero_obj₂`: the obstruction — vanishing at two
  vertices of a distinguished triangle makes the third component square-zero, and no more.
* `ModuleCat.app_single_derivedCenterValue`: a shift-compatible central element of `D(A)` agrees
  with the degreewise action of a central element of `A` at every module in every degree.
* `ModuleCat.derivedCenterValue_centerToCatCenterDerived` and
  `ModuleCat.derivedCenterValueAlgHom_comp_centerToShiftCenterDerived`: reading off the central
  element of `A` retracts its degreewise action, so the centre of `A` is a direct factor of the
  shift-compatible centre of `D(A)` as an `R`-algebra.
* `ModuleCat.centerToShiftCenterDerived_surjective_iff_eq_zero`: the input owed by Tag 09SD in its
  sharpest form — the degreewise action is surjective precisely when a shift-compatible central
  element of `D(A)` vanishing at every module placed in degree zero is zero. Neither the centre of
  `A` nor the map occurs on the right, so this is the form to compare with Rickard's Proposition
  9.2.
* `ModuleCat.centerToShiftCenterDerived_surjective_of_ext_single`,
  `ModuleCat.centerToShiftCenterDerived_surjective_of_retractCoproductSingle` and
  `ModuleCat.centerToShiftCenterDerived_surjective_of_isoCoproductSingle`: the surjectivity owed
  by Tag 09SD, reduced to an extension principle for the single complexes, and that principle
  discharged when the objects of `D(A)` are retracts of coproducts of shifts of modules — in
  particular when they split as such coproducts.

## References

* [Stacks Project, Tag 09SD](https://stacks.math.columbia.edu/tag/09SD)
* [Stacks Project, Tag 0FQE](https://stacks.math.columbia.edu/tag/0FQE)
* [Stacks Project, Tag 09SN](https://stacks.math.columbia.edu/tag/09SN)
* H. Krause and Y. Ye, *On the center of a triangulated category*, Proposition 6.1.
* J. Rickard, *Derived equivalences as derived functors*, Proposition 9.2.
-/

@[expose] public section

namespace CategoryTheory

open Category Limits Pretriangulated

universe t s w v₁ v₂ u₁ u₂ u

namespace CatCenter

section Naturality

variable {C : Type u₁} [Category.{v₁} C] {z w : CatCenter C}

/-- Two central elements that agree at an object agree at every isomorphic object. -/
lemma app_eq_of_iso {X Y : C} (e : X ≅ Y) (h : z.app X = w.app X) : z.app Y = w.app Y := by
  rw [← cancel_epi e.hom, naturality z e.hom, h, ← naturality w e.hom]

/-- Two central elements that agree at `X` agree after composition with any morphism out of
`X`: both composites are the common component at `X` followed by that morphism. This is the
sense in which the difference of two central elements agreeing on a class of objects is a
*phantom*: it is killed by every morphism out of that class. -/
lemma comp_app_eq_of_app_eq {X Y : C} (h : z.app X = w.app X) (f : X ⟶ Y) :
    f ≫ z.app Y = f ≫ w.app Y := by
  rw [naturality z f, h, ← naturality w f]

/-- Two central elements that agree at `Y` agree after composition with any morphism into
`Y`. -/
lemma app_comp_eq_of_app_eq {X Y : C} (h : z.app Y = w.app Y) (f : X ⟶ Y) :
    z.app X ≫ f = w.app X ≫ f := by
  rw [← naturality z f, h, naturality w f]

/-- The agreement locus is closed under retracts: writing `𝟙 X` as `h.i ≫ h.r` and moving the
common component at `Y` across `h.r` by naturality expresses the component at `X` through the
component at `Y`. This is the closure property the comparison of
[Stacks, Tag 09SB] also stops at; see the discussion at the top of this file. -/
lemma app_eq_of_retract {X Y : C} (h : Retract X Y) (hY : z.app Y = w.app Y) :
    z.app X = w.app X := by
  rw [← id_comp (z.app X), ← h.retract, assoc, naturality z h.r, hY, ← naturality w h.r,
    ← assoc, h.retract, id_comp]

/-- The agreement locus is closed under coproducts: the inclusions of a coproduct are jointly
epimorphic, and agreement at the summands propagates along them by naturality. -/
lemma app_eq_of_coproduct {ι : Type*} {X : ι → C} [HasCoproduct X]
    (h : ∀ i, z.app (X i) = w.app (X i)) : z.app (∐ X) = w.app (∐ X) :=
  Sigma.hom_ext _ _ fun i => comp_app_eq_of_app_eq (h i) _

end Naturality

section Shift

variable {C : Type u₁} [Category.{v₁} C] {z w : CatCenter C}

/-- The agreement locus of two shift-compatible central elements is closed under shifting. -/
lemma app_shift_eq_of_app_eq {A : Type s} [AddMonoid A] [HasShift C A]
    (hz : NatTrans.CommShift z A) (hw : NatTrans.CommShift w A) {X : C}
    (h : z.app X = w.app X) (a : A) : z.app (X⟦a⟧) = w.app (X⟦a⟧) := by
  rw [← (commShift_iff_app z).1 hz a X, ← (commShift_iff_app w).1 hw a X, h]

/-- The agreement locus of two shift-compatible central elements is closed under unshifting: for
a shift by an additive group the shift functors are equivalences, hence faithful. -/
lemma app_eq_of_app_shift_eq {A : Type s} [AddGroup A] [HasShift C A]
    (hz : NatTrans.CommShift z A) (hw : NatTrans.CommShift w A) {X : C} (a : A)
    (h : z.app (X⟦a⟧) = w.app (X⟦a⟧)) : z.app X = w.app X :=
  (shiftFunctor C a).map_injective <| by
    rw [(commShift_iff_app z).1 hz a X, (commShift_iff_app w).1 hw a X, h]

end Shift

section Triangulated

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] {δ : CatCenter C}
  (hδ : NatTrans.CommShift δ ℤ) (T : Triangle C) (hT : T ∈ distTriang C)

include hδ hT

/-- **The two-out-of-three step for vanishing of a central element, and all of it that is true.**
Let `δ` be a shift-compatible central element vanishing at the first two vertices of a
distinguished triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧`. Then its component at `Z` *squares to zero*; it need
not vanish.

Indeed `δ.app Z` is killed by `Y ⟶ Z` by naturality, so it factors as `Z ⟶ X⟦1⟧ ⟶ Z` through the
third morphism of the triangle; and the second factor is killed by `δ.app Z` by naturality and
the vanishing at `X`, which is where compatibility with the shift is spent. The composite of the
two observations is the square.

This is why the dévissage of [Stacks, Tag 0FQE] cannot be run on the property `δ.app X = 0`, and
why `StacksDraft.CompactDevissage.isIso_app_of_isCompactlyGenerated` is stated for invertibility,
where the same step is the five lemma. See the discussion at the top of this file. -/
lemma app_comp_app_eq_zero_obj₃ (h₁ : δ.app T.obj₁ = 0) (h₂ : δ.app T.obj₂ = 0) :
    δ.app T.obj₃ ≫ δ.app T.obj₃ = 0 := by
  obtain ⟨v, hv⟩ := T.yoneda_exact₃ hT (δ.app T.obj₃)
    (by rw [naturality δ T.mor₂, h₂, zero_comp])
  have hv' : v ≫ δ.app T.obj₃ = 0 := by
    rw [naturality δ v, ← (commShift_iff_app δ).1 hδ 1 T.obj₁, h₁, Functor.map_zero, zero_comp]
  nth_rewrite 1 [hv]
  rw [assoc, hv', comp_zero]

omit hδ in
/-- The two-out-of-three step in the middle position, with the same conclusion and for the same
reason as `CategoryTheory.CatCenter.app_comp_app_eq_zero_obj₃`: a shift-compatible central
element vanishing at the outer two vertices of a distinguished triangle has square-zero
component at the middle vertex. Here the shift is not needed; the factorisation runs through
`Y ⟶ Z ⟶ Y`. -/
lemma app_comp_app_eq_zero_obj₂ (h₁ : δ.app T.obj₁ = 0) (h₃ : δ.app T.obj₃ = 0) :
    δ.app T.obj₂ ≫ δ.app T.obj₂ = 0 := by
  obtain ⟨v, hv⟩ := T.yoneda_exact₂ hT (δ.app T.obj₂)
    (by rw [naturality δ T.mor₁, h₁, zero_comp])
  have hv' : v ≫ δ.app T.obj₂ = 0 := by rw [naturality δ v, h₃, zero_comp]
  nth_rewrite 1 [hv]
  rw [assoc, hv', comp_zero]

end Triangulated

section OfFull

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- **A central element pulled back along a fully faithful functor.** If `F : C ⥤ D` is fully
faithful, the components at the objects of the image of `F` of a central element of `D` are the
images of a unique family of endomorphisms in `C`, and that family is natural because `F` is
faithful. -/
noncomputable def ofFull (F : C ⥤ D) [F.Full] [F.Faithful] (w : CatCenter D) : CatCenter C where
  app X := F.preimage (w.app (F.obj X))
  naturality _ _ f := F.map_injective <| by
    simp only [Functor.id_obj, Functor.id_map, Functor.map_comp, Functor.map_preimage]
    exact w.naturality (F.map f)

/-- Applying `F` to a component of `CategoryTheory.CatCenter.ofFull F w` recovers the component
of `w` at the image object. -/
@[simp]
lemma map_app_ofFull (F : C ⥤ D) [F.Full] [F.Faithful] (w : CatCenter D) (X : C) :
    F.map ((ofFull F w).app X) = w.app (F.obj X) :=
  F.map_preimage _

section Algebra

variable (R : Type t) [CommRing R] [Preadditive C] [Preadditive D] [Linear R C] [Linear R D]

/-- **Pullback of central elements along a fully faithful functor, as a morphism of algebras.**
For `F : C ⥤ D` fully faithful, additive and `R`-linear, `CategoryTheory.CatCenter.ofFull F` is a
morphism of `R`-algebras: each identity is checked after applying `F`, where
`CategoryTheory.CatCenter.map_app_ofFull` turns it into the corresponding identity in
`CatCenter D`. -/
noncomputable def ofFullAlgHom (F : C ⥤ D) [F.Full] [F.Faithful] [F.Additive] [F.Linear R] :
    CatCenter D →ₐ[R] CatCenter C where
  toFun := ofFull F
  map_one' := CatCenter.ext _ _ fun X => F.map_injective (by simp [End.one_def])
  map_mul' _ _ := CatCenter.ext _ _ fun X => F.map_injective (by
    simp [Functor.map_comp])
  map_zero' := CatCenter.ext _ _ fun X => F.map_injective (by simp)
  map_add' _ _ := CatCenter.ext _ _ fun X => F.map_injective (by simp [app_add])
  commutes' r := CatCenter.ext _ _ fun X => F.map_injective (by
    rw [map_app_ofFull, algebraMap_app, algebraMap_app, Functor.map_smul, Functor.map_id])

/-- The underlying function of `CategoryTheory.CatCenter.ofFullAlgHom R F` is
`CategoryTheory.CatCenter.ofFull F`. -/
@[simp]
lemma ofFullAlgHom_apply (F : C ⥤ D) [F.Full] [F.Faithful] [F.Additive] [F.Linear R]
    (w : CatCenter D) : ofFullAlgHom R F w = ofFull F w := rfl

end Algebra

end OfFull

end CatCenter

end CategoryTheory

namespace ModuleCat

open CategoryTheory Limits DerivedCategory

open scoped ModuleCat.Algebra

universe w u t

variable (R : Type t) [CommRing R] (A : Type u) [Ring A] [Algebra R A]
  [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- The degreewise action of a central element of `A` on the derived category commutes with the
shift. This is the membership in `CategoryTheory.CatCenter.shiftSubalgebra` that
`ModuleCat.centerToShiftCenterDerived` establishes, read as compatibility with the shift. -/
lemma commShift_centerToCatCenterDerived (a : Subalgebra.center R A) :
    NatTrans.CommShift (centerToCatCenterDerived R A a) ℤ :=
  (CatCenter.mem_shiftSubalgebra_iff_commShift _).1 (centerToShiftCenterDerived R A a).2

/-- **The central element of `A` attached to a central element of `D(A)`.** The functor placing a
module in degree zero is fully faithful, so the components of a central element of the derived
category at those complexes are the degreewise action of a central element of the category of
modules, hence of a central element of `A` by `ModuleCat.centerAlgEquiv`.

No compatibility with the shift is needed to *define* this element; it is needed to show that it
accounts for the components at the modules placed in the other degrees, which is
`ModuleCat.app_single_derivedCenterValue`. -/
noncomputable def derivedCenterValue (z : CatCenter (DerivedCategory (ModuleCat.{u} A))) :
    Subalgebra.center R A :=
  (centerAlgEquiv R A).symm (CatCenter.ofFull (singleFunctor (ModuleCat.{u} A) 0) z)

/-- The element of the centre of `A` attached to a central element of the derived category acts
on modules by the pullback of that element along the degree-zero single-complex functor. -/
lemma centerToCatCenter_derivedCenterValue (z : CatCenter (DerivedCategory (ModuleCat.{u} A))) :
    centerToCatCenter R A (derivedCenterValue R A z) =
      CatCenter.ofFull (singleFunctor (ModuleCat.{u} A) 0) z := by
  rw [← centerAlgEquiv_apply]
  exact (centerAlgEquiv R A).apply_symm_apply _

/-- The degreewise action of `ModuleCat.derivedCenterValue R A z` agrees with `z` at every module
placed in degree zero. This is the defining property of that element. -/
lemma app_single_zero_derivedCenterValue (z : CatCenter (DerivedCategory (ModuleCat.{u} A)))
    (M : ModuleCat.{u} A) :
    (centerToCatCenterDerived R A (derivedCenterValue R A z)).app
        ((singleFunctor (ModuleCat.{u} A) 0).obj M) =
      z.app ((singleFunctor (ModuleCat.{u} A) 0).obj M) := by
  rw [centerToCatCenterDerived_app_single, centerToCatCenter_derivedCenterValue,
    CatCenter.map_app_ofFull]

/-- **`ModuleCat.derivedCenterValue` as a morphism of `R`-algebras.** Reading the components of a
central element of `D(A)` at the modules placed in degree zero is `R`-algebra valued: it is the
pullback along the degree-zero single-complex functor, which is fully faithful, additive and
`R`-linear, followed by the identification of `CatCenter (ModuleCat A)` with the centre of `A`. -/
noncomputable def derivedCenterValueAlgHom :
    CatCenter (DerivedCategory (ModuleCat.{u} A)) →ₐ[R] Subalgebra.center R A :=
  (ModuleCat.centerAlgEquiv R A).symm.toAlgHom.comp
    (CatCenter.ofFullAlgHom R (singleFunctor (ModuleCat.{u} A) 0))

/-- The underlying function of `ModuleCat.derivedCenterValueAlgHom R A` is
`ModuleCat.derivedCenterValue R A`. -/
@[simp]
lemma derivedCenterValueAlgHom_apply (z : CatCenter (DerivedCategory (ModuleCat.{u} A))) :
    derivedCenterValueAlgHom R A z = derivedCenterValue R A z := rfl

/-- **`ModuleCat.derivedCenterValue` is a retraction of the canonical map.** The central element
of `A` read off from the degreewise action of a central element `a` of `A` is `a` again. -/
@[simp]
lemma derivedCenterValue_centerToCatCenterDerived (a : Subalgebra.center R A) :
    derivedCenterValue R A (centerToCatCenterDerived R A a) = a := by
  have h : CatCenter.ofFull (singleFunctor (ModuleCat.{u} A) 0)
      (centerToCatCenterDerived R A a) = centerToCatCenter R A a :=
    CatCenter.ext _ _ fun M => (singleFunctor (ModuleCat.{u} A) 0).map_injective (by
      rw [CatCenter.map_app_ofFull, centerToCatCenterDerived_app_single])
  show (ModuleCat.centerAlgEquiv R A).symm (CatCenter.ofFull _ _) = a
  rw [h, ← centerAlgEquiv_apply, AlgEquiv.symm_apply_apply]

/-- **The centre of `A` is a direct factor of the shift-compatible centre of `D(A)`.** The
degreewise action `ModuleCat.centerToShiftCenterDerived` is a split monomorphism of `R`-algebras,
split by `ModuleCat.derivedCenterValueAlgHom`. Its injectivity,
`ModuleCat.centerToShiftCenterDerived_injective`, is a consequence; what the splitting does not
give is surjectivity, which is the input owed by Tag 09SD and is equivalent to the vanishing of
the kernel of the retraction, by
`ModuleCat.centerToShiftCenterDerived_surjective_iff_eq_zero`. -/
theorem derivedCenterValueAlgHom_comp_centerToShiftCenterDerived :
    (derivedCenterValueAlgHom R A).comp
        ((CatCenter.shiftSubalgebra R (DerivedCategory (ModuleCat.{u} A)) ℤ).val.comp
          (centerToShiftCenterDerived R A)) =
      AlgHom.id R (Subalgebra.center R A) :=
  AlgHom.ext fun a => by simp

/-- A central element of `D(A)` vanishing at every module placed in degree zero has zero
`ModuleCat.derivedCenterValue`: that element is read off from exactly those components. -/
lemma derivedCenterValue_eq_zero (z : CatCenter (DerivedCategory (ModuleCat.{u} A)))
    (hz : ∀ M : ModuleCat.{u} A, z.app ((singleFunctor (ModuleCat.{u} A) 0).obj M) = 0) :
    derivedCenterValue R A z = 0 := by
  have h : CatCenter.ofFull (singleFunctor (ModuleCat.{u} A) 0) z = 0 :=
    CatCenter.ext _ _ fun M =>
      (singleFunctor (ModuleCat.{u} A) 0).map_injective (by simp [hz M])
  show (ModuleCat.centerAlgEquiv R A).symm (CatCenter.ofFull _ _) = 0
  rw [h, map_zero]

/-- **A shift-compatible central element of `D(A)` is the degreewise action of a central element
of `A` at every module in every degree.** The complexes concentrated in degree `n` are the shifts
of those concentrated in degree `0`, and both `z` and the degreewise action of
`ModuleCat.derivedCenterValue R A z` are compatible with the shift, so the agreement of
`ModuleCat.app_single_zero_derivedCenterValue` propagates from degree `0` to every degree.

This is strictly more than a dévissage along the regular module could give: the agreement is at
*all* modules, not just at `A` itself. What it is not is agreement at all objects of `D(A)`; see
the discussion at the top of this file. -/
lemma app_single_derivedCenterValue (z : CatCenter (DerivedCategory (ModuleCat.{u} A)))
    (hz : NatTrans.CommShift z ℤ) (n : ℤ) (M : ModuleCat.{u} A) :
    (centerToCatCenterDerived R A (derivedCenterValue R A z)).app
        ((singleFunctor (ModuleCat.{u} A) n).obj M) =
      z.app ((singleFunctor (ModuleCat.{u} A) n).obj M) :=
  CatCenter.app_eq_of_app_shift_eq
    (commShift_centerToCatCenterDerived R A (derivedCenterValue R A z)) hz n
    (CatCenter.app_eq_of_iso
      (((singleFunctors (ModuleCat.{u} A)).shiftIso n 0 n (add_zero n)).app M).symm
      (app_single_zero_derivedCenterValue R A z M))

/-- **The difference is a phantom on the single complexes.** A shift-compatible central element
of `D(A)` and the degreewise action of `ModuleCat.derivedCenterValue R A z` agree after
composition with any morphism out of a module placed in any degree. Since those complexes include
the shifts of the regular module, which generate `D(A)`, the difference of the two is killed by
every morphism from a compact generator: it is a phantom, and phantoms need not vanish. -/
lemma comp_app_eq_of_single (z : CatCenter (DerivedCategory (ModuleCat.{u} A)))
    (hz : NatTrans.CommShift z ℤ) (n : ℤ) (M : ModuleCat.{u} A)
    (X : DerivedCategory (ModuleCat.{u} A)) (f : (singleFunctor (ModuleCat.{u} A) n).obj M ⟶ X) :
    f ≫ (centerToCatCenterDerived R A (derivedCenterValue R A z)).app X = f ≫ z.app X :=
  CatCenter.comp_app_eq_of_app_eq (app_single_derivedCenterValue R A z hz n M) f

/-- **Every shift-compatible central element of `D(A)` is accounted for on the single complexes by
a central element of `A`.** This is the half of the surjectivity of
`ModuleCat.centerToShiftCenterDerived` that holds unconditionally. -/
theorem exists_app_single_eq
    (z : CatCenter.shiftSubalgebra R (DerivedCategory (ModuleCat.{u} A)) ℤ) :
    ∃ a : Subalgebra.center R A, ∀ (n : ℤ) (M : ModuleCat.{u} A),
      (centerToCatCenterDerived R A a).app ((singleFunctor (ModuleCat.{u} A) n).obj M) =
        (z : CatCenter (DerivedCategory (ModuleCat.{u} A))).app
          ((singleFunctor (ModuleCat.{u} A) n).obj M) :=
  ⟨derivedCenterValue R A z.1, fun n M => app_single_derivedCenterValue R A z.1
    ((CatCenter.mem_shiftSubalgebra_iff_commShift _).1 z.2) n M⟩

/-- **The surjectivity owed by Tag 09SD, reduced to an extension principle.** If a
shift-compatible central element of `D(A)` is determined by its components at the complexes
concentrated in a single degree, then `ModuleCat.centerToShiftCenterDerived` is surjective, hence
— being injective by `ModuleCat.centerToShiftCenterDerived_injective` — an isomorphism of
`R`-algebras onto the shift-compatible centre of `D(A)`.

The hypothesis mentions neither the centre of `A` nor the map; it is a statement about the
derived category alone, and it is what Rickard's Proposition 9.2 supplies through Hochschild
cohomology. It cannot be obtained from the dévissage along the shifts of the regular module; see
the discussion at the top of this file. -/
theorem centerToShiftCenterDerived_surjective_of_ext_single
    (hext : ∀ z w : CatCenter (DerivedCategory (ModuleCat.{u} A)),
      NatTrans.CommShift z ℤ → NatTrans.CommShift w ℤ →
      (∀ (n : ℤ) (M : ModuleCat.{u} A),
        z.app ((singleFunctor (ModuleCat.{u} A) n).obj M) =
          w.app ((singleFunctor (ModuleCat.{u} A) n).obj M)) → z = w) :
    Function.Surjective (centerToShiftCenterDerived R A) := by
  intro z
  refine ⟨derivedCenterValue R A z.1, Subtype.ext ?_⟩
  rw [centerToShiftCenterDerived_coe]
  exact hext _ _ (commShift_centerToCatCenterDerived R A _)
    ((CatCenter.mem_shiftSubalgebra_iff_commShift _).1 z.2)
    (app_single_derivedCenterValue R A z.1
      ((CatCenter.mem_shiftSubalgebra_iff_commShift _).1 z.2))

/-- **The input owed by Tag 09SD, in its sharpest form: a shift-compatible central element of
`D(A)` vanishing on the modules is zero.** The degreewise action
`ModuleCat.centerToShiftCenterDerived` is surjective — hence, being injective, an isomorphism of
`R`-algebras onto the shift-compatible centre of `D(A)` — exactly when every shift-compatible
central element of `D(A)` whose component at each module placed in degree zero vanishes is zero.

Neither the centre of `A` nor the map occurs in the right-hand side: it is a statement about the
derived category alone, and it is what Rickard's Proposition 9.2 supplies. It is the form to
compare with the literature, and the form a citation would take.

Both directions use `ModuleCat.derivedCenterValue`. Surjectivity makes such a `z` the degreewise
action of a central element of `A`, which the retraction
`ModuleCat.derivedCenterValue_centerToCatCenterDerived` recovers and
`ModuleCat.derivedCenterValue_eq_zero` shows to be zero. Conversely the difference of a
shift-compatible central element and the degreewise action of its
`ModuleCat.derivedCenterValue` vanishes at every module in every degree, by
`ModuleCat.app_single_derivedCenterValue`, and is again shift-compatible, the shift-compatible
elements forming a subalgebra; so the right-hand side makes it zero. -/
theorem centerToShiftCenterDerived_surjective_iff_eq_zero :
    Function.Surjective (centerToShiftCenterDerived R A) ↔
      ∀ z : CatCenter (DerivedCategory (ModuleCat.{u} A)), NatTrans.CommShift z ℤ →
        (∀ M : ModuleCat.{u} A, z.app ((singleFunctor (ModuleCat.{u} A) 0).obj M) = 0) →
        z = 0 := by
  refine ⟨fun hsurj z hz hzero => ?_, fun hvan => ?_⟩
  · obtain ⟨a, ha⟩ := hsurj ⟨z, (CatCenter.mem_shiftSubalgebra_iff_commShift z).2 hz⟩
    have ha' : centerToCatCenterDerived R A a = z := by simpa using Subtype.ext_iff.1 ha
    have ha0 : a = 0 := by
      rw [← derivedCenterValue_centerToCatCenterDerived R A a, ha']
      exact derivedCenterValue_eq_zero R A z hzero
    rw [← ha', ha0, map_zero]
  · refine centerToShiftCenterDerived_surjective_of_ext_single R A fun z w hz hw h => ?_
    have hmem : z - w ∈ CatCenter.shiftSubalgebra R (DerivedCategory (ModuleCat.{u} A)) ℤ :=
      sub_mem ((CatCenter.mem_shiftSubalgebra_iff_commShift z).2 hz)
        ((CatCenter.mem_shiftSubalgebra_iff_commShift w).2 hw)
    refine sub_eq_zero.1 (hvan (z - w)
      ((CatCenter.mem_shiftSubalgebra_iff_commShift _).1 hmem) fun M => ?_)
    rw [CatCenter.app_sub, h 0 M, sub_self]

/-- **The surjectivity owed by Tag 09SD, when the objects of `D(A)` are retracts of split
objects.** If every object of `D(A)` is a retract of a coproduct of modules placed in single
degrees then `ModuleCat.centerToShiftCenterDerived` is surjective: the agreement locus of two
shift-compatible central elements is closed under coproducts and retracts, so agreement at the
single complexes is agreement everywhere.

The retracts of coproducts of single complexes are exactly as far as the closure properties of
the agreement locus reach, and they are the class over which the comparison of
[Stacks, Tag 09SB] is natural; the discussion at the top of this file explains why neither can be
pushed further without an input special to the derived category of a ring. -/
theorem centerToShiftCenterDerived_surjective_of_retractCoproductSingle
    [HasCoproducts.{w} (DerivedCategory (ModuleCat.{u} A))]
    (hsplit : ∀ X : DerivedCategory (ModuleCat.{u} A), ∃ (ι : Type w) (n : ι → ℤ)
      (M : ι → ModuleCat.{u} A),
      Nonempty (Retract X (∐ fun i => (singleFunctor (ModuleCat.{u} A) (n i)).obj (M i)))) :
    Function.Surjective (centerToShiftCenterDerived R A) := by
  refine centerToShiftCenterDerived_surjective_of_ext_single R A
    fun z w _ _ h => CatCenter.ext _ _ fun X => ?_
  obtain ⟨ι, n, M, ⟨e⟩⟩ := hsplit X
  exact CatCenter.app_eq_of_retract e (CatCenter.app_eq_of_coproduct fun i => h (n i) (M i))

/-- **The surjectivity owed by Tag 09SD, when the objects of `D(A)` split.** If every object of
`D(A)` is isomorphic to a coproduct of modules placed in single degrees — as happens over a
hereditary ring, where every complex is the direct sum of its shifted cohomology modules — then
`ModuleCat.centerToShiftCenterDerived` is surjective, an isomorphism being in particular a
retract. -/
theorem centerToShiftCenterDerived_surjective_of_isoCoproductSingle
    [HasCoproducts.{w} (DerivedCategory (ModuleCat.{u} A))]
    (hsplit : ∀ X : DerivedCategory (ModuleCat.{u} A), ∃ (ι : Type w) (n : ι → ℤ)
      (M : ι → ModuleCat.{u} A),
      Nonempty (X ≅ ∐ fun i => (singleFunctor (ModuleCat.{u} A) (n i)).obj (M i))) :
    Function.Surjective (centerToShiftCenterDerived R A) :=
  centerToShiftCenterDerived_surjective_of_retractCoproductSingle R A fun X => by
    obtain ⟨ι, n, M, ⟨e⟩⟩ := hsplit X
    exact ⟨ι, n, M, ⟨⟨e.hom, e.inv, e.hom_inv_id⟩⟩⟩

end ModuleCat

end
