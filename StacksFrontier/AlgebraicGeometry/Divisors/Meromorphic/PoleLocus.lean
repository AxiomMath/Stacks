module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.Denominators
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.WeilDivisors
public import StacksFrontier.AlgebraicGeometry.Divisors.OrderOfVanishingMeromorphic
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.GenericPoint

/-!
# The poles of a regular meromorphic section

Let `X` be a locally Noetherian integral scheme and let `L` be an invertible sheaf of
`𝒪_X`-modules. A regular meromorphic section `s` of `L` is an ordinary section of `L` over some
neighbourhood of all but a locally finite collection of prime divisors, and has nonzero order of
vanishing along all but a locally finite collection of prime divisors, so that its orders of
vanishing are the coefficients of a Weil divisor `div_L(s)`.

## Main definitions

* `AlgebraicGeometry.IsRepresentedAt`: the meromorphic section `s` is an ordinary section of `L`
  on a neighbourhood of `x`.
* `AlgebraicGeometry.weilDivisorOfMeromorphicSection`: the Weil divisor whose coefficient at a
  prime divisor is the order of vanishing of `s` there.

## Main results

* `AlgebraicGeometry.isRepresentedAt_genericPoint`: a meromorphic section of a quasi-coherent
  module on an integral scheme is an ordinary section near the generic point.
* `AlgebraicGeometry.locallyFinite_primeDivisors_not_representedAt`: the prime divisors at whose
  generic point `s` is not an ordinary section form a locally finite collection.
* `AlgebraicGeometry.locallyFinite_primeDivisors_orderOfVanishingMeromorphic_ne_zero`: the prime
  divisors along which `s` has nonzero order form a locally finite collection.

## References

* [Stacks Project, Tag 02SG](https://stacks.math.columbia.edu/tag/02SG)
* [Stacks Project, Tag 01X5](https://stacks.math.columbia.edu/tag/01X5)
* [Stacks Project, Tag 02SF](https://stacks.math.columbia.edu/tag/02SF)
* [Stacks Project, Tag 0BE1](https://stacks.math.columbia.edu/tag/0BE1)
* [Stacks Project, Tag 0BE2](https://stacks.math.columbia.edu/tag/0BE2)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

section Represented

variable {X : Scheme.{u}}

/-! ### Where a meromorphic section is an ordinary section -/

/-- A meromorphic section `s` of `L` is *represented at* `x` when it is the
canonical image of an ordinary section of `L` over some neighbourhood of `x`; equivalently, when
`s` lies in the image of `L_x` in the stalk of the sheaf of meromorphic sections. The canonical
map is `AlgebraicGeometry.toMeromorphicSectionSheafAsModule`, the unit of extension of scalars
to the sheaf of total quotient rings. -/
def IsRepresentedAt (L : X.Modules) (s : MeromorphicSection X.sheaf L) (x : X) : Prop :=
  ∃ (U : X.Opens) (e : L.val.obj (op U)), x ∈ U ∧
    (toMeromorphicSectionSheafAsModule X L).val.app (op U) e = s.val (op U)

/-- The sections of an isomorphism of sheaves of modules over a fixed open set are injective. -/
theorem injective_iso_hom_val_app {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
    {F G : SheafOfModules.{u} R} (e : F ≅ G) (U : (Opens X)ᵒᵖ) :
    Function.Injective (e.hom.val.app U) := by
  have : IsIso e.hom.val := Functor.map_isIso (SheafOfModules.forget R) e.hom
  have : IsIso (e.hom.val.app U) :=
    Functor.map_isIso (PresheafOfModules.evaluation R.obj U) e.hom.val
  exact (ConcreteCategory.bijective_of_isIso (e.hom.val.app U)).1

/-- On an integral scheme a meromorphic section of a quasi-coherent module is an ordinary
section on a neighbourhood of the generic point. -/
theorem isRepresentedAt_genericPoint [IsIntegral X] (L : X.Modules) [L.IsQuasicoherent]
    (s : MeromorphicSection X.sheaf L) : IsRepresentedAt L s (genericPoint X) := by
  obtain ⟨e, he⟩ := meromorphicSectionSheafIsoConstant X L
  obtain ⟨v, hv, -⟩ := exists_unique_eq_constantGenericStalkModuleSection X L
    (e.hom.val.app (op (⊤ : X.Opens)) (s.val (op ⊤)))
  obtain ⟨U, hU, d, hd⟩ := TopCat.Presheaf.exists_germ_eq L.presheaf v
  refine ⟨U, d, hU, injective_iso_hom_val_app e (op U) ?_⟩
  have h1 : e.hom.val.app (op U) ((toMeromorphicSectionSheafAsModule X L).val.app (op U) d) =
      constantGenericStalkModuleSection X L U v := by
    rw [← hd]; exact he U d hU
  have h2 : e.hom.val.app (op U) (s.val (op U)) =
      constantGenericStalkModuleSection X L U v := by
    have key := PresheafOfModules.sections_property s (homOfLE (le_top (a := U))).op
    have hnat := PresheafOfModules.naturality_apply e.hom.val
      (homOfLE (le_top (a := U))).op (s.val (op ⊤))
    have hcn := constantGenericStalkModuleSection_naturality X L (homOfLE (le_top (a := U))) v
    rw [← key]
    exact hnat.trans (by rw [hv]; exact hcn.symm)
  exact h1.trans h2.symm

/-! ### The prime divisors at whose generic point the section is not an ordinary section -/

/-- Distinct prime divisors have distinct supports. -/
theorem PrimeDivisor.eq_of_support_eq {Z W : PrimeDivisor X} (h : Z.support = W.support) :
    Z = W := by
  refine PrimeDivisor.genericPoint_injective (Inseparable.eq ?_)
  rwa [inseparable_iff_closure_eq, ← Z.support_eq_closure, ← W.support_eq_closure]

/-- On an integral scheme, a closed irreducible subset of the complement of a nonempty open set
that contains the generic point of a prime divisor is the support of that prime divisor. -/
theorem PrimeDivisor.eq_support_of_isIrreducible [IsIntegral X] (Z : PrimeDivisor X)
    {U : X.Opens} (hU : (U : Set X).Nonempty) {S : Set X} (hSclosed : IsClosed S)
    (hSirred : IsIrreducible S) (hSsub : S ⊆ (U : Set X)ᶜ)
    (hZS : Z.genericPoint ∈ S) : S = Z.support := by
  set A : IrreducibleCloseds X := IrreducibleCloseds.closureSingleton Z.genericPoint with hA
  set B : IrreducibleCloseds X := ⟨S, hSirred, hSclosed⟩ with hB
  set T : IrreducibleCloseds X :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩ with hT
  have hABle : A ≤ B := closure_minimal (Set.singleton_subset_iff.mpr hZS) hSclosed
  have hBT : B < T := lt_of_le_of_ne (Set.subset_univ _) fun he => by
    obtain ⟨y, hy⟩ := hU
    exact hSsub (show y ∈ S from
      (congrArg (fun Q : IrreducibleCloseds X => (Q : Set X)) he).ge (Set.mem_univ y)) hy
  have hABeq : A = B := by
    by_contra hne
    have htwo : (2 : ℕ∞) ≤ codimension A := by
      refine (codimension_iff_exists_chain A 2).2 ⟨(RelSeries.singleton _ T).cons B
        (by simpa using hBT) |>.cons A (by simpa using lt_of_le_of_ne hABle hne), by simp, by
          simp⟩
    rw [Z.codimension_closureSingleton_genericPoint] at htwo
    norm_num at htwo
  have hSA : S = closure ({Z.genericPoint} : Set X) :=
    congrArg (fun Q : IrreducibleCloseds X => (Q : Set X)) hABeq.symm
  rw [hSA, Z.support_eq_closure]

/-- The support of a prime divisor whose generic point avoids a nonempty open set is the image
of an irreducible component of the reduced closed subscheme on the complement. -/
theorem PrimeDivisor.exists_irreducibleComponents_image_eq_support [IsIntegral X]
    (Z : PrimeDivisor X) (U : X.Opens) (hU : (U : Set X).Nonempty)
    (hZU : Z.genericPoint ∉ (U : Set X)) :
    ∃ C : irreducibleComponents
        (Scheme.IdealSheafData.vanishingIdeal
          (⟨(U : Set X)ᶜ, U.2.isClosed_compl⟩ : Closeds X)).subscheme,
      (Scheme.IdealSheafData.vanishingIdeal
          (⟨(U : Set X)ᶜ, U.2.isClosed_compl⟩ : Closeds X)).subschemeι '' (C : Set _) =
        Z.support := by
  set I := Scheme.IdealSheafData.vanishingIdeal
    (⟨(U : Set X)ᶜ, U.2.isClosed_compl⟩ : Closeds X) with hI
  have hIsupp : (I.support : Set X) = (U : Set X)ᶜ := by
    rw [hI, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  obtain ⟨y, hy⟩ : Z.genericPoint ∈ Set.range I.subschemeι := by
    rwa [Scheme.IdealSheafData.range_subschemeι, hIsupp]
  obtain ⟨C, hC, hyC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({y} : Set I.subscheme)) (isIrreducible_iff_closure.mpr isIrreducible_singleton)
  refine ⟨⟨C, hC⟩, Z.eq_support_of_isIrreducible hU
    (I.subschemeι.isClosedEmbedding.isClosedMap _ (isClosed_of_mem_irreducibleComponents _ hC))
    (hC.1.image _ I.subschemeι.continuous.continuousOn) ?_
    ⟨y, hyC (subset_closure rfl), hy⟩⟩
  rintro x ⟨z, -, rfl⟩
  rw [← hIsupp, ← Scheme.IdealSheafData.range_subschemeι]
  exact ⟨z, rfl⟩

/-- The prime divisors at whose generic point a meromorphic section of a quasi-coherent module
on a locally Noetherian integral scheme is not an ordinary section form a locally finite
collection of closed subsets. -/
@[stacks 02SG "nonintegral_stalk_locus"]
theorem locallyFinite_primeDivisors_not_representedAt [IsLocallyNoetherian X] [IsIntegral X]
    (L : X.Modules)
    [L.IsQuasicoherent] (s : MeromorphicSection X.sheaf L) :
    LocallyFinite
      (fun Z : { Z : PrimeDivisor X // ¬ IsRepresentedAt L s Z.genericPoint } => Z.1.support) := by
  classical
  obtain ⟨U, e, hηU, hEq⟩ := isRepresentedAt_genericPoint L s
  have hU : (U : Set X).Nonempty := ⟨genericPoint X, hηU⟩
  set I := Scheme.IdealSheafData.vanishingIdeal
    (⟨(U : Set X)ᶜ, U.2.isClosed_compl⟩ : Closeds X) with hI
  have hex : ∀ Z : { Z : PrimeDivisor X // ¬ IsRepresentedAt L s Z.genericPoint },
      ∃ C : irreducibleComponents I.subscheme, I.subschemeι '' (C : Set I.subscheme) =
        Z.1.support := fun Z =>
    Z.1.exists_irreducibleComponents_image_eq_support U hU fun hZ => Z.2 ⟨U, e, hZ, hEq⟩
  choose c hcspec using hex
  have hinj : Function.Injective c := fun Z W hZW => Subtype.ext
    (PrimeDivisor.eq_of_support_eq
      ((hcspec Z).symm.trans ((congrArg (fun C : irreducibleComponents I.subscheme =>
        I.subschemeι '' (C : Set I.subscheme)) hZW).trans (hcspec W))))
  exact ((locallyFinite_irreducibleComponents_image I.subschemeι).comp_injective
    hinj).subset fun Z => (hcspec Z).ge

end Represented

/-! ### The prime divisors along which the section has nonzero order -/

variable (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X] (L : X.Modules)
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : MeromorphicSection X.sheaf L) (hs : IsRegularMeromorphicSection X.sheaf L s)

/-- The prime divisors along which a regular meromorphic section of an invertible module on a
locally Noetherian integral scheme has nonzero order of vanishing form a locally finite
collection of closed subsets; equivalently, the orders are the coefficients of a Weil divisor. -/
@[stacks 02SG "nonzero_order_locus"]
theorem locallyFinite_primeDivisors_orderOfVanishingMeromorphic_ne_zero :
    LocallyFinite (fun Z : PrimeDivisor X =>
      if orderOfVanishingMeromorphic X L s hs Z = 0 then ∅ else Z.support) := by
  classical
  have hqc : L.IsQuasicoherent := isQuasicoherent_of_isInvertible L
  have hL : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).2 ‹_›
  show (fun Z => orderOfVanishingMeromorphic X L s hs Z) ∈ WeilDivisor X
  refine mem_weilDivisor_of_forall_exists_open fun x => ?_
  obtain ⟨W, hxW, t, ht⟩ :=
    Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible (X := X.toRingedSpace) L x
  have hηW : genericPoint X ∈ W :=
    ((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr ⟨x, trivial, hxW⟩
  have hspan := span_germ_eq_top_of_surjective_smul X L W t fun V hV => (ht V hV).surjective
  obtain ⟨v, hv, -⟩ := exists_unique_eq_constantGenericStalkModuleSection X L
    ((meromorphicSectionSheafIsoConstant X L).val.hom.val.app (op (⊤ : X.Opens))
      (s.val (op ⊤)))
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1
    (Submodule.eq_top_iff'.1 (hspan (genericPoint X) hηW) v)
  have hgerm : ∀ (Z : PrimeDivisor X) (hZW : Z.genericPoint ∈ W),
      (L.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial))
          (L.presheaf.germ W Z.genericPoint hZW t) =
        L.presheaf.germ W (genericPoint X) hηW t :=
    fun _ _ => TopCat.Presheaf.germ_stalkSpecializes_apply ..
  have hcoord : ∀ Z : PrimeDivisor X, Z.genericPoint ∈ W →
      orderOfVanishingMeromorphic X L s hs Z = X.ord a Z.genericPoint := by
    intro Z hZW
    refine (orderOfVanishingMeromorphicData X L s hs Z).2.2
      (L.presheaf.germ W Z.genericPoint hZW t) (hspan _ hZW) a ?_
    exact hv.trans (congrArg (constantGenericStalkModuleSection X L ⊤)
      (by rw [hgerm Z hZW]; exact ha.symm))
  obtain ⟨V, hV, hfin⟩ := Stacks.Chow.locallyFiniteSupport_ord X a x
  refine ⟨(W : Set X) ∩ interior V, W.isOpen.inter isOpen_interior,
    ⟨hxW, mem_interior_iff_mem_nhds.mpr hV⟩, ?_⟩
  refine Set.Finite.of_finite_image (f := PrimeDivisor.genericPoint) (hfin.subset ?_)
    PrimeDivisor.genericPoint_injective.injOn
  rintro - ⟨Z, ⟨hZW, hZne⟩, rfl⟩
  exact ⟨interior_subset hZW.2, by rwa [Function.mem_support, ← hcoord Z hZW.1]⟩

/-- The Weil divisor `div_L(s) = ∑_Z ord_{Z, L}(s) [Z]` of a regular meromorphic section of an
invertible module on a locally Noetherian integral scheme. -/
@[stacks 0BE6 "part (1): divisor of a meromorphic section"]
def weilDivisorOfMeromorphicSection : WeilDivisor X :=
  ⟨fun Z => orderOfVanishingMeromorphic X L s hs Z,
    locallyFinite_primeDivisors_orderOfVanishingMeromorphic_ne_zero X L s hs⟩

/-- The coefficient of `div_L(s)` at a prime divisor is the order of vanishing of `s` there. -/
@[simp]
theorem weilDivisorOfMeromorphicSection_apply (Z : PrimeDivisor X) :
    (weilDivisorOfMeromorphicSection X L s hs).val Z =
      orderOfVanishingMeromorphic X L s hs Z :=
  rfl

end AlgebraicGeometry

end
