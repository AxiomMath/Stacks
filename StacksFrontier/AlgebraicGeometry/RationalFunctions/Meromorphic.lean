module

public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import StacksFrontier.AlgebraicGeometry.MeromorphicGenericPointDecomposition.Globalization
public import StacksFrontier.AlgebraicGeometry.Meromorphic.NonZeroDivisorNowhereDense
public import StacksFrontier.AlgebraicGeometry.Meromorphic.TotalQuotientSheafSections
public import StacksFrontier.AlgebraicGeometry.RationalFunctions.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Rational functions are the global meromorphic functions

Let `X` be a scheme whose weakly associated points are generic points of irreducible components
and whose quasi-compact opens have only finitely many irreducible components. Part (6) of
[Stacks, Tag 0EMF] asserts that the ring of rational functions of `X` is the ring of meromorphic
functions on `X`, that is `R(X) = Γ(X, K_X)`. Specialized to a reduced scheme this is part (6) of
[Stacks, Tag 02OW], and specialized to a locally Noetherian scheme without embedded points it is
the last clause of [Stacks, Tag 0EMH].

The source deduces part (6) from the generic-point decomposition and
[Stacks, Tag 01RV] when there are finitely many irreducible components, and omits the general
case. The proof here is uniform in the number of components, and is the following three
statements about the sheaf `K_X` of total quotient rings.

*Restriction to a dense open set is bijective on `K_X`.* The decomposition of `K_X` as a sheaf of
*rings* over the generic points is available as
`AlgebraicGeometry.isIso_toGenericPointStalkProduct`, sections of a product of sheaves of rings
are the families of sections, and restriction along an inclusion containing every generic point
is an isomorphism on each factor because the factor is a pushforward from the spectrum of a local
ring at a generic point, whose preimage is the whole space. The hypothesis that the open set
contain every generic point is supplied by
`AlgebraicGeometry.mem_of_dense_of_mem_genericPoints`, which is where the local finiteness of the
irreducible components enters: on a space with infinitely many components a dense open set can
miss a generic point.

*The structure sheaf injects into `K_X`.* On an affine open set this is
`AlgebraicGeometry.isLocalization_totalQuotientSheaf_obj` together with
`IsLocalization.injective`; on an arbitrary open set it follows by comparing germs.

*Every global section of `K_X` restricts to a section of the structure sheaf on a dense open
set.* A section of `K_X` is locally a fraction `a / b` with `b` a nonzerodivisor
(`AlgebraicGeometry.Scheme.exists_isAffineOpen_nhds_isFraction_totalQuotientSheaf`); on the basic
open set of `b` the fraction is an honest section, those basic open sets cover a dense open set by
`AlgebraicGeometry.inf_basicOpen_ne_bot_of_mem_nonZeroDivisors`, and the sections glue because the
structure sheaf injects into `K_X`.

## Main results

* `AlgebraicGeometry.bijective_totalQuotientSheaf_presheaf_map_of_genericPoints_mem`,
  `AlgebraicGeometry.injective_toTotalQuotientSheaf_app` and
  `AlgebraicGeometry.exists_dense_section_toTotalQuotientSheaf_app_eq`: the three statements
  above.
* `AlgebraicGeometry.exists_equiv_totalQuotientSheaf_top`: the resulting bijection between
  the global sections of `K_X` and any set receiving the sections on dense open sets in the way
  the ring of rational functions does.
* `AlgebraicGeometry.nonempty_ringEquiv_totalQuotientSheaf_top`: the ring form of that
  bijection.
* `AlgebraicGeometry.nonempty_rationalFunctions_ringEquiv_totalQuotientSheaf_top`: part (6)
  of [Stacks, Tag 0EMF], for a commutative ring structure on the rational functions carried as a
  hypothesis and characterized as in [Stacks, Tag 01RU].
* `AlgebraicGeometry.exists_commRing_rationalFunctions_ringEquiv_totalQuotientSheaf_top`:
  the same with that ring structure constructed rather than assumed, and its two specializations
  `..._of_isReduced` and `..._of_hasNoEmbeddedPoints`, which are part (6) of
  [Stacks, Tag 02OW] and the last clause of [Stacks, Tag 0EMH].

## Implementation notes

`AlgebraicGeometry.mem_of_dense_of_closure_singleton_mem_irreducibleComponents` is the purely
topological core of the first step and is stated for an arbitrary topological space: if the
irreducible components are finitely many then a dense open set contains the generic point of each
of them, because otherwise the union of the other components is a closed set containing the dense
set, hence everything.

The ring structure on the rational functions is not constructed in
`StacksDraft.AlgebraicGeometry.F3b.RationalFunctions.Basic`, so the comparison is proved first
with that structure as a hypothesis — which is the form a consumer of [Stacks, Tag 01RU] wants —
and the structure is then obtained by transporting the one on `Γ(X, K_X)` along the bijection,
which is what makes the two specializations unconditional.

## References

* [Stacks Project, Tag 02OW](https://stacks.math.columbia.edu/tag/02OW)
* [Stacks Project, Tag 0EMF](https://stacks.math.columbia.edu/tag/0EMF)
* [Stacks Project, Tag 0EMH](https://stacks.math.columbia.edu/tag/0EMH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry

/-! ### A dense open set contains every generic point -/

/-- In a topological space with finitely many irreducible components, a dense open set contains
the generic point of every irreducible component: otherwise the union of the other components is
a closed set containing the dense set, hence the whole space, and so contains that generic point,
whose component is then contained in another one. -/
theorem mem_of_dense_of_closure_singleton_mem_irreducibleComponents
    {α : Type*} [TopologicalSpace α] (hfin : (irreducibleComponents α).Finite)
    {S : Set α} (hSo : IsOpen S) (hS : Dense S) {x : α}
    (hx : closure {x} ∈ irreducibleComponents α) : x ∈ S := by
  by_contra hxS
  set Z : Set α := closure {x} with hZ
  set T : Set (Set α) := irreducibleComponents α \ {Z} with hT
  have hTclosed : IsClosed (⋃₀ T) :=
    (hfin.subset Set.sdiff_subset).isClosed_sUnion fun t ht =>
      isClosed_of_mem_irreducibleComponents t ht.1
  have hZcompl : Z ⊆ Sᶜ := closure_minimal (by simpa using hxS) hSo.isClosed_compl
  have hSsub : S ⊆ ⋃₀ T := by
    intro y hyS
    obtain ⟨W, hW, hyW⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {y}
      isIrreducible_singleton
    refine ⟨W, ⟨hW, ?_⟩, hyW rfl⟩
    intro hWZ
    exact hZcompl (hWZ ▸ hyW rfl) hyS
  obtain ⟨W, hWT, hxW⟩ : x ∈ ⋃₀ T := by
    have h : (Set.univ : Set α) ⊆ ⋃₀ T := hS.closure_eq ▸ closure_minimal hSsub hTclosed
    exact h (Set.mem_univ x)
  have hZW : Z ⊆ W := closure_minimal (by simpa using hxW)
    (isClosed_of_mem_irreducibleComponents W hWT.1)
  exact hWT.2 (le_antisymm (hx.2 hWT.1.1 hZW) hZW)

variable {X : Scheme.{u}}

/-- Restricting a section of the structure sheaf in two steps. -/
lemma presheaf_map_res_res {A B C : X.Opens} (hAB : A ≤ B) (hBC : B ≤ C) (g : Γ(X, C)) :
    (X.presheaf.map (homOfLE hAB).op).hom ((X.presheaf.map (homOfLE hBC).op).hom g) =
      (X.presheaf.map (homOfLE (hAB.trans hBC)).op).hom g := by
  rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
  congr 1

/-- On a scheme whose quasi-compact opens have finitely many irreducible components, every dense
open set contains every generic point of an irreducible component. -/
theorem mem_of_dense_of_mem_genericPoints
    (hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    {U : X.Opens} (hU : Dense (U : Set X)) (η : genericPoints X) : η.1 ∈ U := by
  obtain ⟨V, hVaff, hηV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := (⊤ : X.Opens)) (x := η.1) trivial
  have hcomp : closure {(⟨η.1, hηV⟩ : (V : Set X))} ∈ irreducibleComponents (V : Set X) := by
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, Set.image_singleton]
    exact preimage_mem_irreducibleComponents η.2 V.isOpen.isOpenEmbedding_subtypeVal
      ⟨η.1, subset_closure (Set.mem_singleton _), ⟨⟨η.1, hηV⟩, rfl⟩⟩
  have hmem : (⟨η.1, hηV⟩ : (V : Set X)) ∈ (Subtype.val ⁻¹' (U : Set X) : Set (V : Set X)) :=
    mem_of_dense_of_closure_singleton_mem_irreducibleComponents
      (hfinite V hVaff.isCompact) (U.isOpen.preimage continuous_subtype_val)
      (hU.preimage V.isOpen.isOpenMap_subtype_val) hcomp
  exact hmem

/-! ### Restriction to a dense open set is bijective on the sheaf of total quotient rings -/

/-- If a square of maps commutes and three sides are bijective, so is the fourth. -/
private lemma bijective_of_comp_eq {α β γ δ : Type*} {f : α → β} {g : α → γ} {h : β → δ}
    {k : γ → δ} (hsq : ∀ x, h (f x) = k (g x)) (hg : Function.Bijective g)
    (hh : Function.Bijective h) (hk : Function.Bijective k) : Function.Bijective f :=
  (hh.of_comp_iff' f).mp (by rw [show h ∘ f = k ∘ g from funext hsq]; exact hk.comp hg)

/-- Restriction on a product of sheaves of rings is computed componentwise. -/
lemma ringSheafSectionsPiEquiv_naturality {ι : Type u} (L : ι → TopCat.Sheaf CommRingCat.{u} X)
    {V W : X.Opens} (h : V ≤ W)
    (x : ToType ((ringSheafSectionsFunctor X W).obj (∏ᶜ L))) (i : ι) :
    ringSheafSectionsPiEquiv L V (((∏ᶜ L).presheaf.map (homOfLE h).op).hom x) i =
      ((L i).presheaf.map (homOfLE h).op).hom (ringSheafSectionsPiEquiv L W x i) := by
  have key : ∀ (U : X.Opens) (y : (∏ᶜ L).presheaf.obj (op U)),
      ringSheafSectionsPiEquiv L U y i = ((Pi.π L i).hom.app (op U)).hom y :=
    fun U y => ringSheafSectionsPiEquiv_apply L U y i
  refine (key V _).trans ?_
  refine Eq.trans ?_ (congrArg (((L i).presheaf.map (homOfLE h).op).hom) (key W x)).symm
  exact NatTrans.naturality_apply (Pi.π L i).hom (homOfLE h).op x

/-- A restriction map of a product of sheaves of rings is bijective as soon as it is bijective on
every factor. -/
lemma bijective_pi_presheaf_map {ι : Type u} (L : ι → TopCat.Sheaf CommRingCat.{u} X)
    {V W : X.Opens} (h : V ≤ W)
    (hcomp : ∀ i, Function.Bijective ((L i).presheaf.map (homOfLE h).op).hom) :
    Function.Bijective (((∏ᶜ L).presheaf.map (homOfLE h).op).hom) := by
  classical
  set eV := ringSheafSectionsPiEquiv L V with heV
  set eW := ringSheafSectionsPiEquiv L W with heW
  set F : (∀ i, ToType ((ringSheafSectionsFunctor X W).obj (L i))) →
      (∀ i, ToType ((ringSheafSectionsFunctor X V).obj (L i))) :=
    fun f i => ((L i).presheaf.map (homOfLE h).op).hom (f i) with hF
  have hFbij : Function.Bijective F := by
    refine ⟨fun a b hab => funext fun i => (hcomp i).1 (congrFun hab i), fun g => ?_⟩
    choose a ha using fun i => (hcomp i).2 (g i)
    exact ⟨a, funext ha⟩
  have hsq : ∀ x : ToType ((ringSheafSectionsFunctor X W).obj (∏ᶜ L)),
      eV (((∏ᶜ L).presheaf.map (homOfLE h).op).hom x) = F (eW x) :=
    fun x => funext fun i => ringSheafSectionsPiEquiv_naturality L h x i
  exact bijective_of_comp_eq hsq eW.bijective eV.bijective hFbij

/-- On an open set containing a generic point, restriction from the whole space is an isomorphism
on the pushforward of the structure sheaf of the spectrum of the local ring at that point: the
preimage of both open sets is the whole of that spectrum. -/
lemma isIso_stalkSpecPushforward_presheaf_map (η : genericPoints X) {V : X.Opens} (hη : η.1 ∈ V) :
    IsIso ((stalkSpecPushforward X η.1).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op) := by
  have h1 : X.fromSpecStalk η.1 ⁻¹ᵁ V = ⊤ := fromSpecStalk_preimage_eq_top η.2 hη
  have h2 : X.fromSpecStalk η.1 ⁻¹ᵁ (⊤ : X.Opens) = ⊤ :=
    fromSpecStalk_preimage_eq_top η.2 trivial
  have heq : X.fromSpecStalk η.1 ⁻¹ᵁ V = X.fromSpecStalk η.1 ⁻¹ᵁ (⊤ : X.Opens) := by
    rw [h1, h2]
  change IsIso ((Spec (X.presheaf.stalk η.1)).presheaf.map
    ((Opens.map (X.fromSpecStalk η.1).base).map (homOfLE (le_top : V ≤ ⊤))).op)
  rw [show (Opens.map (X.fromSpecStalk η.1).base).map (homOfLE (le_top : V ≤ ⊤)) =
      eqToHom heq from Subsingleton.elim _ _]
  infer_instance

/-- **Restriction to an open set containing every generic point is bijective on the sheaf of
total quotient rings.** The sheaf of total quotient rings is the product, over the generic points,
of the pushforwards from the spectra of the local rings there, and on each factor the restriction
map is an isomorphism. -/
theorem bijective_totalQuotientSheaf_presheaf_map_of_genericPoints_mem
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    {V : X.Opens} (hVgen : ∀ η : genericPoints X, η.1 ∈ V) :
    Function.Bijective
      (X.totalQuotientSheaf.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom := by
  have hiso : IsIso (toGenericPointStalkProduct X) := isIso_toGenericPointStalkProduct hass hfinite
  have hhom : IsIso (toGenericPointStalkProduct X).hom :=
    Functor.map_isIso (TopCat.Sheaf.forget CommRingCat.{u} X) (toGenericPointStalkProduct X)
  have happ : ∀ U : X.Opens,
      Function.Bijective (((toGenericPointStalkProduct X).hom.app (op U)).hom) := by
    intro U
    rw [← ConcreteCategory.isIso_iff_bijective]
    infer_instance
  have hprod : Function.Bijective
      (((genericPointStalkProduct X).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom) :=
    bijective_pi_presheaf_map _ _ fun η => by
      rw [← ConcreteCategory.isIso_iff_bijective]
      exact isIso_stalkSpecPushforward_presheaf_map η (hVgen η)
  have hsq : ∀ x : X.totalQuotientSheaf.presheaf.obj (op ⊤),
      ((toGenericPointStalkProduct X).hom.app (op V)).hom
          ((X.totalQuotientSheaf.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom x) =
        ((genericPointStalkProduct X).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom
          (((toGenericPointStalkProduct X).hom.app (op ⊤)).hom x) :=
    fun x => NatTrans.naturality_apply (toGenericPointStalkProduct X).hom
      (homOfLE (le_top : V ≤ ⊤)).op x
  exact bijective_of_comp_eq hsq (happ ⊤) (happ V) hprod

/-! ### The structure sheaf injects into the sheaf of total quotient rings -/

/-- On an affine open set the structure sheaf injects into the sheaf of total quotient rings,
because the latter is the localization of the former at its nonzerodivisors. -/
theorem injective_toTotalQuotientSheaf_app_of_isAffineOpen
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Injective (X.toTotalQuotientSheaf.hom.app (op U)).hom := by
  let _ : Algebra Γ(X, U) (X.totalQuotientSheaf.obj.obj (op U)) :=
    (X.toTotalQuotientSheaf.hom.app (op U)).hom.toAlgebra
  have h : IsLocalization (nonZeroDivisors Γ(X, U)) (X.totalQuotientSheaf.obj.obj (op U)) :=
    isLocalization_totalQuotientSheaf_obj hass hfinite hU
  exact IsLocalization.injective (M := nonZeroDivisors Γ(X, U))
    (X.totalQuotientSheaf.obj.obj (op U)) le_rfl

/-- The map from the structure sheaf to the sheaf of total quotient rings commutes with
restriction. -/
private lemma toTotalQuotientSheaf_app_res {P Q : X.Opens} (hQP : Q ≤ P) (g : Γ(X, P)) :
    (X.toTotalQuotientSheaf.hom.app (op Q)).hom ((X.presheaf.map (homOfLE hQP).op).hom g) =
      (X.totalQuotientSheaf.presheaf.map (homOfLE hQP).op).hom
        ((X.toTotalQuotientSheaf.hom.app (op P)).hom g) :=
  NatTrans.naturality_apply X.toTotalQuotientSheaf.hom (homOfLE hQP).op g

/-- **The structure sheaf injects into the sheaf of total quotient rings**, over every open
set. -/
theorem injective_toTotalQuotientSheaf_app
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    (U : X.Opens) : Function.Injective (X.toTotalQuotientSheaf.hom.app (op U)).hom := by
  intro a b hab
  refine TopCat.Presheaf.section_ext X.sheaf U a b fun y hy => ?_
  obtain ⟨V, hVaff, hyV, hVU⟩ := exists_isAffineOpen_mem_and_subset hy
  have hres : (X.presheaf.map (homOfLE hVU).op) a = (X.presheaf.map (homOfLE hVU).op) b := by
    refine injective_toTotalQuotientSheaf_app_of_isAffineOpen hass hfinite hVaff ?_
    exact (toTotalQuotientSheaf_app_res hVU a).trans
      ((congrArg (X.totalQuotientSheaf.presheaf.map (homOfLE hVU).op).hom hab).trans
        (toTotalQuotientSheaf_app_res hVU b).symm)
  exact (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hVU) y hyV a).symm.trans
    ((congrArg (X.presheaf.germ V y hyV).hom hres).trans
      (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hVU) y hyV b))

/-! ### A global meromorphic function is a section on a dense open set -/

/-- The restriction of a global section of the sheaf of total quotient rings — a global
meromorphic function — to an open set. -/
noncomputable abbrev resTotalQuotientSheaf (t : X.totalQuotientSheaf.presheaf.obj (op ⊤))
    (P : X.Opens) : X.totalQuotientSheaf.presheaf.obj (op P) :=
  (X.totalQuotientSheaf.presheaf.map (homOfLE (le_top : P ≤ ⊤)).op).hom t

lemma resTotalQuotientSheaf_res (t : X.totalQuotientSheaf.presheaf.obj (op ⊤)) {P Q : X.Opens}
    (hPQ : P ≤ Q) :
    (X.totalQuotientSheaf.presheaf.map (homOfLE hPQ).op).hom (resTotalQuotientSheaf t Q) =
      resTotalQuotientSheaf t P := by
  refine Eq.trans ?_ (congrArg (fun m => (X.totalQuotientSheaf.presheaf.map m).hom t)
    (Subsingleton.elim ((homOfLE (le_top : Q ≤ ⊤) : Q ⟶ ⊤).op ≫ (homOfLE hPQ : P ⟶ Q).op)
      ((homOfLE (le_top : P ≤ ⊤) : P ⟶ ⊤).op)))
  rw [X.totalQuotientSheaf.presheaf.map_comp, ConcreteCategory.comp_apply]

lemma resTotalQuotientSheaf_top (t : X.totalQuotientSheaf.presheaf.obj (op ⊤)) :
    resTotalQuotientSheaf t ⊤ = t := by
  change (X.totalQuotientSheaf.presheaf.map
    (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op).hom t = t
  rw [show (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤) : (⊤ : X.Opens) ⟶ ⊤).op = 𝟙 _ from
    Subsingleton.elim _ _, X.totalQuotientSheaf.presheaf.map_id]
  rfl

/-- On the basic open set of a denominator, a fraction description of a section of the sheaf of
total quotient rings is the image of an honest section of the structure sheaf: the denominator is
invertible there. -/
lemma exists_section_toTotalQuotientSheaf_app_eq_on_basicOpen (X : Scheme.{u}) {U : X.Opens}
    (t : X.totalQuotientSheaf.presheaf.obj (op U)) {V : X.Opens} (hVU : V ≤ U) (a b : Γ(X, V))
    (heq : (X.totalQuotientSheaf.presheaf.map (homOfLE hVU).op).hom t *
        (X.toTotalQuotientSheaf.hom.app (op V)).hom b =
      (X.toTotalQuotientSheaf.hom.app (op V)).hom a) :
    ∃ s : Γ(X, X.basicOpen b),
      (X.toTotalQuotientSheaf.hom.app (op (X.basicOpen b))).hom s =
        (X.totalQuotientSheaf.presheaf.map
          (homOfLE ((X.basicOpen_le b).trans hVU)).op).hom t := by
  set W : X.Opens := X.basicOpen b with hW
  set ra : Γ(X, W) := (X.presheaf.map (homOfLE (X.basicOpen_le b)).op).hom a with hra
  set rb : Γ(X, W) := (X.presheaf.map (homOfLE (X.basicOpen_le b)).op).hom b with hrb
  have hu : IsUnit rb := X.toRingedSpace.isUnit_res_basicOpen b
  obtain ⟨c, hc⟩ : ∃ c : Γ(X, W), rb * c = 1 := by
    obtain ⟨v, hv⟩ := hu
    exact ⟨↑v⁻¹, by rw [← hv]; exact v.mul_inv⟩
  have hsrb : rb * (c * ra) = ra := by rw [← mul_assoc, hc, one_mul]
  have hres : (X.totalQuotientSheaf.presheaf.map
        (homOfLE ((X.basicOpen_le b).trans hVU)).op).hom t *
      (X.toTotalQuotientSheaf.hom.app (op W)).hom rb =
      (X.toTotalQuotientSheaf.hom.app (op W)).hom ra := by
    have h := mul_toTotalQuotientSheaf_eq_of_le X.sheaf (X.basicOpen_le b) heq
    rw [show (homOfLE ((X.basicOpen_le b).trans hVU) : W ⟶ U).op =
        (homOfLE hVU : V ⟶ U).op ≫ (homOfLE (X.basicOpen_le b) : W ⟶ V).op from rfl,
      X.totalQuotientSheaf.presheaf.map_comp, ConcreteCategory.comp_apply]
    exact h
  have hunit : IsUnit ((X.toTotalQuotientSheaf.hom.app (op W)).hom rb) :=
    hu.map (X.toTotalQuotientSheaf.hom.app (op W)).hom
  refine ⟨c * ra, hunit.mul_left_cancel ?_⟩
  calc (X.toTotalQuotientSheaf.hom.app (op W)).hom rb *
        (X.toTotalQuotientSheaf.hom.app (op W)).hom (c * ra)
      = (X.toTotalQuotientSheaf.hom.app (op W)).hom ra :=
        (map_mul (X.toTotalQuotientSheaf.hom.app (op W)).hom rb (c * ra)).symm.trans
          (congrArg (X.toTotalQuotientSheaf.hom.app (op W)).hom hsrb)
    _ = (X.totalQuotientSheaf.presheaf.map
          (homOfLE ((X.basicOpen_le b).trans hVU)).op).hom t *
        (X.toTotalQuotientSheaf.hom.app (op W)).hom rb := hres.symm
    _ = (X.toTotalQuotientSheaf.hom.app (op W)).hom rb *
        (X.totalQuotientSheaf.presheaf.map
          (homOfLE ((X.basicOpen_le b).trans hVU)).op).hom t := mul_comm _ _

/-- **A global section of the sheaf of total quotient rings is a section of the structure sheaf
on a dense open set.** Around each point the section is a fraction `a / b` with `b` a
nonzerodivisor on an affine open set; on the basic open set of `b` it is an honest section, those
basic open sets cover a dense open set, and the sections glue because the structure sheaf injects
into the sheaf of total quotient rings. -/
theorem exists_dense_section_toTotalQuotientSheaf_app_eq
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    (t : X.totalQuotientSheaf.presheaf.obj (op ⊤)) :
    ∃ U : X.Opens, Dense (U : Set X) ∧ ∃ s : Γ(X, U),
      (X.toTotalQuotientSheaf.hom.app (op U)).hom s = resTotalQuotientSheaf t U := by
  classical
  choose V hVU hVaff hxV a b hb hbu heq using
    fun x : X => X.exists_isAffineOpen_nhds_isFraction_totalQuotientSheaf (U := ⊤) t
      (x := x) trivial
  choose s hs using fun x : X =>
    exists_section_toTotalQuotientSheaf_app_eq_on_basicOpen X t (hVU x) (a x) (b x) (heq x)
  set W : X → X.Opens := fun x => X.basicOpen (b x) with hWdef
  have hsT : ∀ x, (X.toTotalQuotientSheaf.hom.app (op (W x))).hom (s x) =
      resTotalQuotientSheaf t (W x) := hs
  set U : X.Opens := ⨆ x, W x with hUdef
  have hWU : ∀ x, W x ≤ U := fun x => le_iSup W x
  have hdense : Dense (U : Set X) := by
    rw [dense_iff_inter_open]
    intro O hO hOne
    obtain ⟨y, hyO⟩ := hOne
    have hO'ne : (⟨O, hO⟩ ⊓ V y : X.Opens) ≠ ⊥ :=
      (TopologicalSpace.Opens.ne_bot_iff_nonempty _).mpr ⟨y, hyO, hxV y⟩
    obtain ⟨z, hz⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp
      (inf_basicOpen_ne_bot_of_mem_nonZeroDivisors (hVaff y) (hb y) inf_le_right hO'ne)
    exact ⟨z, hz.1.1, hWU y hz.2⟩
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf W s := by
    intro x y
    refine injective_toTotalQuotientSheaf_app hass hfinite (W x ⊓ W y) ?_
    have key : ∀ (z : X) (m : W x ⊓ W y ⟶ W z) (hz : W x ⊓ W y ≤ W z),
        (X.toTotalQuotientSheaf.hom.app (op (W x ⊓ W y))).hom
          ((X.presheaf.map m.op).hom (s z)) = resTotalQuotientSheaf t (W x ⊓ W y) := by
      intro z m hz
      rw [show m = homOfLE hz from Subsingleton.elim _ _]
      rw [toTotalQuotientSheaf_app_res, hsT z, resTotalQuotientSheaf_res]
    rw [key x _ inf_le_left, key y _ inf_le_right]
  obtain ⟨g, hg, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf W U
    (fun x => homOfLE (hWU x)) le_rfl s hcompat
  refine ⟨U, hdense, g, ?_⟩
  refine TopCat.Presheaf.section_ext X.totalQuotientSheaf U _ _ fun y hy => ?_
  obtain ⟨x, hxW⟩ : ∃ x, y ∈ W x := by
    have hyU : y ∈ ⨆ x, W x := hUdef ▸ hy
    exact Opens.mem_iSup.mp hyU
  have e1 := TopCat.Presheaf.germ_res_apply X.totalQuotientSheaf.presheaf (homOfLE (hWU x)) y hxW
    ((X.toTotalQuotientSheaf.hom.app (op U)).hom g)
  have e2 := TopCat.Presheaf.germ_res_apply X.totalQuotientSheaf.presheaf (homOfLE (hWU x)) y hxW
    (resTotalQuotientSheaf t U)
  refine e1.symm.trans (Eq.trans ?_ e2)
  refine congrArg (X.totalQuotientSheaf.presheaf.germ (W x) y hxW).hom ?_
  refine (toTotalQuotientSheaf_app_res (hWU x) g).symm.trans
    ((congrArg (X.toTotalQuotientSheaf.hom.app (op (W x))).hom (hg x)).trans ?_)
  rw [hsT x, resTotalQuotientSheaf_res]

/-! ### The comparison -/

/-- **The global meromorphic functions are the ring of rational functions, as a bijection.** Any
type receiving the sections of the structure sheaf on dense open sets compatibly with restriction,
surjectively, and separating sections only up to a smaller dense open set, is in bijection with
the global sections of the sheaf of total quotient rings; the bijection sends a global section to
the value of any section of the structure sheaf representing it on a dense open set. -/
theorem exists_equiv_totalQuotientSheaf_top
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    (R : Type u) (σ : ∀ P : X.Opens, Dense (P : Set X) → Γ(X, P) → R)
    (hres : ∀ (P Q : X.Opens) (hP : Dense (P : Set X)) (hQ : Dense (Q : Set X)) (hQP : Q ≤ P)
      (f : Γ(X, P)), σ Q hQ ((X.presheaf.map (homOfLE hQP).op).hom f) = σ P hP f)
    (hsurj : ∀ r : R, ∃ (P : X.Opens) (hP : Dense (P : Set X)) (f : Γ(X, P)), σ P hP f = r)
    (hsep : ∀ (P : X.Opens) (hP : Dense (P : Set X)) (f f' : Γ(X, P)),
      σ P hP f = σ P hP f' → ∃ (Q : X.Opens) (_ : Dense (Q : Set X)) (hQP : Q ≤ P),
        (X.presheaf.map (homOfLE hQP).op).hom f = (X.presheaf.map (homOfLE hQP).op).hom f') :
    ∃ e : X.totalQuotientSheaf.presheaf.obj (op ⊤) ≃ R,
      ∀ (t : X.totalQuotientSheaf.presheaf.obj (op ⊤)) (P : X.Opens) (hP : Dense (P : Set X))
        (f : Γ(X, P)), (X.toTotalQuotientSheaf.hom.app (op P)).hom f = resTotalQuotientSheaf t P →
        e t = σ P hP f := by
  classical
  choose D hD sec hsec using
    fun t => exists_dense_section_toTotalQuotientSheaf_app_eq hass hfinite t
  set Θ : X.totalQuotientSheaf.presheaf.obj (op ⊤) → R := fun t => σ (D t) (hD t) (sec t) with hΘ
  have hwd : ∀ (t : X.totalQuotientSheaf.presheaf.obj (op ⊤)) (P : X.Opens)
      (hP : Dense (P : Set X)) (f : Γ(X, P)),
      (X.toTotalQuotientSheaf.hom.app (op P)).hom f = resTotalQuotientSheaf t P →
        Θ t = σ P hP f := by
    intro t P hP f hf
    have hQ : Dense (((D t ⊓ P : X.Opens)) : Set X) :=
      (hD t).inter_of_isOpen_left hP (D t).isOpen
    have h1 : (X.presheaf.map (homOfLE (inf_le_left : D t ⊓ P ≤ D t)).op).hom (sec t) =
        (X.presheaf.map (homOfLE (inf_le_right : D t ⊓ P ≤ P)).op).hom f := by
      refine injective_toTotalQuotientSheaf_app hass hfinite (D t ⊓ P) ?_
      rw [toTotalQuotientSheaf_app_res, toTotalQuotientSheaf_app_res, hsec t, hf,
        resTotalQuotientSheaf_res, resTotalQuotientSheaf_res]
    calc Θ t = σ (D t ⊓ P) hQ
          ((X.presheaf.map (homOfLE (inf_le_left : D t ⊓ P ≤ D t)).op).hom (sec t)) :=
          (hres (D t) (D t ⊓ P) (hD t) hQ inf_le_left (sec t)).symm
      _ = σ (D t ⊓ P) hQ ((X.presheaf.map (homOfLE (inf_le_right : D t ⊓ P ≤ P)).op).hom f) := by
          rw [h1]
      _ = σ P hP f := hres P (D t ⊓ P) hP hQ inf_le_right f
  have hinj : Function.Injective Θ := by
    intro t t' htt
    have hQ : Dense (((D t ⊓ D t' : X.Opens)) : Set X) :=
      (hD t).inter_of_isOpen_left (hD t') (D t).isOpen
    have h1 : σ (D t ⊓ D t') hQ
          ((X.presheaf.map (homOfLE (inf_le_left : D t ⊓ D t' ≤ D t)).op).hom (sec t)) =
        σ (D t ⊓ D t') hQ
          ((X.presheaf.map (homOfLE (inf_le_right : D t ⊓ D t' ≤ D t')).op).hom (sec t')) := by
      rw [hres (D t) (D t ⊓ D t') (hD t) hQ inf_le_left (sec t),
        hres (D t') (D t ⊓ D t') (hD t') hQ inf_le_right (sec t')]
      exact htt
    obtain ⟨Q, hQd, hQP, he⟩ := hsep (D t ⊓ D t') hQ _ _ h1
    have e1 : (X.toTotalQuotientSheaf.hom.app (op Q)).hom
          ((X.presheaf.map
            (homOfLE (hQP.trans (inf_le_left : D t ⊓ D t' ≤ D t))).op).hom (sec t)) =
        resTotalQuotientSheaf t Q := by
      rw [toTotalQuotientSheaf_app_res, hsec t, resTotalQuotientSheaf_res]
    have e2 : (X.toTotalQuotientSheaf.hom.app (op Q)).hom
          ((X.presheaf.map
            (homOfLE (hQP.trans (inf_le_right : D t ⊓ D t' ≤ D t'))).op).hom (sec t')) =
        resTotalQuotientSheaf t' Q := by
      rw [toTotalQuotientSheaf_app_res, hsec t', resTotalQuotientSheaf_res]
    have hrQ : resTotalQuotientSheaf t Q = resTotalQuotientSheaf t' Q := by
      rw [← e1, ← e2]
      refine congrArg (X.toTotalQuotientSheaf.hom.app (op Q)).hom ?_
      rw [← presheaf_map_res_res hQP (inf_le_left : D t ⊓ D t' ≤ D t) (sec t),
        ← presheaf_map_res_res hQP (inf_le_right : D t ⊓ D t' ≤ D t') (sec t'), he]
    exact (bijective_totalQuotientSheaf_presheaf_map_of_genericPoints_mem hass hfinite
      (mem_of_dense_of_mem_genericPoints hfinite hQd)).1 hrQ
  have hsur : Function.Surjective Θ := by
    intro r
    obtain ⟨P, hP, f, hf⟩ := hsurj r
    obtain ⟨t, ht⟩ := (bijective_totalQuotientSheaf_presheaf_map_of_genericPoints_mem hass hfinite
      (mem_of_dense_of_mem_genericPoints hfinite hP)).2
      ((X.toTotalQuotientSheaf.hom.app (op P)).hom f)
    exact ⟨t, (hwd t P hP f ht.symm).trans hf⟩
  exact ⟨Equiv.ofBijective Θ ⟨hinj, hsur⟩, hwd⟩

/-- **The global meromorphic functions are the ring of rational functions.** A commutative ring
receiving the sections of the structure sheaf on dense open sets as ring homomorphisms,
compatibly with restriction, surjectively, and separating sections only up to a smaller dense open
set, is isomorphic as a ring to the global sections of the sheaf of total quotient rings. -/
theorem nonempty_ringEquiv_totalQuotientSheaf_top
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    (R : Type u) [CommRing R] (φ : ∀ P : X.Opens, Dense (P : Set X) → Γ(X, P) →+* R)
    (hres : ∀ (P Q : X.Opens) (hP : Dense (P : Set X)) (hQ : Dense (Q : Set X)) (hQP : Q ≤ P)
      (f : Γ(X, P)), φ Q hQ ((X.presheaf.map (homOfLE hQP).op).hom f) = φ P hP f)
    (hsurj : ∀ r : R, ∃ (P : X.Opens) (hP : Dense (P : Set X)) (f : Γ(X, P)), φ P hP f = r)
    (hsep : ∀ (P : X.Opens) (hP : Dense (P : Set X)) (f f' : Γ(X, P)),
      φ P hP f = φ P hP f' → ∃ (Q : X.Opens) (_ : Dense (Q : Set X)) (hQP : Q ≤ P),
        (X.presheaf.map (homOfLE hQP).op).hom f = (X.presheaf.map (homOfLE hQP).op).hom f') :
    Nonempty (R ≃+* X.totalQuotientSheaf.presheaf.obj (op ⊤)) := by
  have htopdense : Dense (((⊤ : X.Opens)) : Set X) := by simp
  obtain ⟨e, he⟩ := exists_equiv_totalQuotientSheaf_top hass hfinite R
    (fun P hP f => φ P hP f) hres hsurj hsep
  have happ_add : ∀ (Q : X.Opens) (x y : Γ(X, Q)),
      (X.toTotalQuotientSheaf.hom.app (op Q)).hom (x + y) =
        (X.toTotalQuotientSheaf.hom.app (op Q)).hom x +
          (X.toTotalQuotientSheaf.hom.app (op Q)).hom y := fun Q x y => map_add _ x y
  have happ_mul : ∀ (Q : X.Opens) (x y : Γ(X, Q)),
      (X.toTotalQuotientSheaf.hom.app (op Q)).hom (x * y) =
        (X.toTotalQuotientSheaf.hom.app (op Q)).hom x *
          (X.toTotalQuotientSheaf.hom.app (op Q)).hom y := fun Q x y => map_mul _ x y
  have happ_one : ∀ Q : X.Opens,
      (X.toTotalQuotientSheaf.hom.app (op Q)).hom 1 = 1 := fun Q => map_one _
  have hres_add : ∀ (t t' : X.totalQuotientSheaf.presheaf.obj (op ⊤)) (Q : X.Opens),
      resTotalQuotientSheaf (t + t') Q =
        resTotalQuotientSheaf t Q + resTotalQuotientSheaf t' Q := fun t t' Q => map_add _ t t'
  have hres_mul : ∀ (t t' : X.totalQuotientSheaf.presheaf.obj (op ⊤)) (Q : X.Opens),
      resTotalQuotientSheaf (t * t') Q =
        resTotalQuotientSheaf t Q * resTotalQuotientSheaf t' Q := fun t t' Q => map_mul _ t t'
  have hone : e 1 = 1 := by
    rw [he 1 ⊤ htopdense 1 ((happ_one ⊤).trans (resTotalQuotientSheaf_top (1 : _)).symm)]
    exact map_one _
  have hbin : ∀ (t t' : X.totalQuotientSheaf.presheaf.obj (op ⊤))
      (P : X.Opens) (hP : Dense (P : Set X)) (f f' : Γ(X, P)),
      (X.toTotalQuotientSheaf.hom.app (op P)).hom f = resTotalQuotientSheaf t P →
      (X.toTotalQuotientSheaf.hom.app (op P)).hom f' = resTotalQuotientSheaf t' P →
      e t = φ P hP f ∧ e t' = φ P hP f' :=
    fun t t' P hP f f' h h' => ⟨he t P hP f h, he t' P hP f' h'⟩
  have hdata : ∀ t t' : X.totalQuotientSheaf.presheaf.obj (op ⊤),
      ∃ (P : X.Opens) (hP : Dense (P : Set X)) (f f' : Γ(X, P)),
        (X.toTotalQuotientSheaf.hom.app (op P)).hom f = resTotalQuotientSheaf t P ∧
        (X.toTotalQuotientSheaf.hom.app (op P)).hom f' = resTotalQuotientSheaf t' P := by
    intro t t'
    obtain ⟨U, hU, s, hs⟩ := exists_dense_section_toTotalQuotientSheaf_app_eq hass hfinite t
    obtain ⟨U', hU', s', hs'⟩ := exists_dense_section_toTotalQuotientSheaf_app_eq hass hfinite t'
    refine ⟨U ⊓ U', hU.inter_of_isOpen_left hU' U.isOpen,
      (X.presheaf.map (homOfLE (inf_le_left : U ⊓ U' ≤ U)).op).hom s,
      (X.presheaf.map (homOfLE (inf_le_right : U ⊓ U' ≤ U')).op).hom s', ?_, ?_⟩
    · rw [toTotalQuotientSheaf_app_res, hs, resTotalQuotientSheaf_res]
    · rw [toTotalQuotientSheaf_app_res, hs', resTotalQuotientSheaf_res]
  have hadd : ∀ t t', e (t + t') = e t + e t' := by
    intro t t'
    obtain ⟨P, hP, f, f', hf, hf'⟩ := hdata t t'
    obtain ⟨h1, h2⟩ := hbin t t' P hP f f' hf hf'
    rw [h1, h2, ← map_add]
    refine he (t + t') P hP (f + f') ?_
    rw [happ_add, hf, hf', hres_add]
  have hmul : ∀ t t', e (t * t') = e t * e t' := by
    intro t t'
    obtain ⟨P, hP, f, f', hf, hf'⟩ := hdata t t'
    obtain ⟨h1, h2⟩ := hbin t t' P hP f f' hf hf'
    rw [h1, h2, ← map_mul]
    refine he (t * t') P hP (f * f') ?_
    rw [happ_mul, hf, hf', hres_mul]
  have hzero : e 0 = 0 := by
    have h0 := hadd 0 0
    rw [add_zero] at h0
    refine add_left_cancel (a := e 0) ?_
    rw [add_zero]
    exact h0.symm
  exact ⟨(RingEquiv.ofBijective
    ({ toFun := e, map_one' := hone, map_mul' := hmul, map_zero' := hzero,
        map_add' := hadd } : X.totalQuotientSheaf.presheaf.obj (op ⊤) →+* R)
    e.bijective).symm⟩

/-! ### Part (6) for the rational functions -/

/-- **Part (6) of [Stacks, Tag 0EMF].** The ring of rational functions of `X` is the ring of
global meromorphic functions, for a scheme whose weakly associated points are generic points of
irreducible components and whose quasi-compact opens have finitely many irreducible components.
The commutative ring structure on the rational functions is carried as a hypothesis, characterized
exactly as in [Stacks, Tag 01RU]: every section on a dense open set is a ring homomorphism to
it. -/
theorem nonempty_rationalFunctions_ringEquiv_totalQuotientSheaf_top (X : Scheme.{u})
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    [CommRing X.rationalFunctions]
    (hofSection : ∀ (U : X.Opens) (hU : Dense (U : Set X)),
      ∃ ψ : Γ(X, U) →+* X.rationalFunctions,
        ∀ s, ψ s = X.rationalFunctionOfSection U hU s) :
    Nonempty (X.rationalFunctions ≃+* X.totalQuotientSheaf.presheaf.obj (op ⊤)) := by
  classical
  choose ψ hψ using hofSection
  refine nonempty_ringEquiv_totalQuotientSheaf_top hass hfinite X.rationalFunctions ψ
    ?_ ?_ ?_
  · intro P Q hP hQ hQP f
    rw [hψ, hψ, X.rationalFunctionOfSection_res hP hQ hQP]
  · intro r
    obtain ⟨U, hU, s, hs⟩ := X.exists_rationalFunctionOfSection_eq r
    exact ⟨U, hU, s, (hψ U hU s).trans hs⟩
  · intro P hP f f' hff
    rw [hψ, hψ] at hff
    exact X.exists_dense_res_eq_of_rationalFunctionOfSection_eq hP f f' hff

/-- **Part (6) of [Stacks, Tag 0EMF]**, with the commutative ring structure on the rational
functions constructed rather than assumed: it is transported from the global sections of the sheaf
of total quotient rings along the bijection, and every section on a dense open set is a ring
homomorphism to it, which is the characterization of [Stacks, Tag 01RU]. -/
@[stacks 0EMF "part (6)", ega "I 7.1.3" "special case"]
theorem exists_commRing_rationalFunctions_ringEquiv_totalQuotientSheaf_top (X : Scheme.{u})
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite) :
    ∃ _ : CommRing X.rationalFunctions,
      (∀ (U : X.Opens) (hU : Dense (U : Set X)),
          ∃ ψ : Γ(X, U) →+* X.rationalFunctions,
            ∀ s, ψ s = X.rationalFunctionOfSection U hU s) ∧
        Nonempty (X.rationalFunctions ≃+* X.totalQuotientSheaf.presheaf.obj (op ⊤)) := by
  classical
  obtain ⟨e, he⟩ := exists_equiv_totalQuotientSheaf_top hass hfinite X.rationalFunctions
    (fun P hP f => X.rationalFunctionOfSection P hP f)
    (fun P Q hP hQ hQP f => X.rationalFunctionOfSection_res hP hQ hQP f)
    (fun r => X.exists_rationalFunctionOfSection_eq r)
    (fun P hP f f' h => X.exists_dense_res_eq_of_rationalFunctionOfSection_eq hP f f' h)
  let _ : CommRing X.rationalFunctions := Equiv.commRing e.symm
  let hring : X.rationalFunctions ≃+* X.totalQuotientSheaf.presheaf.obj (op ⊤) :=
    e.symm.ringEquiv
  refine ⟨inferInstance, fun U hU => ?_, ⟨hring⟩⟩
  have hbij := bijective_totalQuotientSheaf_presheaf_map_of_genericPoints_mem hass hfinite
    (mem_of_dense_of_mem_genericPoints hfinite hU)
  let ρ : X.totalQuotientSheaf.presheaf.obj (op ⊤) ≃+*
      X.totalQuotientSheaf.presheaf.obj (op U) :=
    RingEquiv.ofBijective
      (X.totalQuotientSheaf.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom hbij
  refine ⟨(hring.symm.toRingHom.comp ρ.symm.toRingHom).comp
    (X.toTotalQuotientSheaf.hom.app (op U)).hom, fun s => ?_⟩
  have hrs : resTotalQuotientSheaf (ρ.symm ((X.toTotalQuotientSheaf.hom.app (op U)).hom s)) U =
      (X.toTotalQuotientSheaf.hom.app (op U)).hom s :=
    ρ.apply_symm_apply _
  change hring.symm (ρ.symm ((X.toTotalQuotientSheaf.hom.app (op U)).hom s)) = _
  rw [RingEquiv.symm_apply_eq]
  change ρ.symm ((X.toTotalQuotientSheaf.hom.app (op U)).hom s) =
    e.symm (X.rationalFunctionOfSection U hU s)
  exact (Equiv.eq_symm_apply e).mpr (he _ U hU s hrs.symm)

/-- **Part (6) of [Stacks, Tag 02OW].** On a reduced scheme whose quasi-compact opens have
finitely many irreducible components, the ring of rational functions is the ring of global
meromorphic functions. -/
@[stacks 02OW "part (6)", ega "IV 20.2.13" "(ii) global sections", ega "I 7.1.3" "special case"]
theorem exists_commRing_rationalFunctions_ringEquiv_totalQuotientSheaf_top_of_isReduced
    (X : Scheme.{u}) [IsReduced X]
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    ∃ _ : CommRing X.rationalFunctions,
      (∀ (U : X.Opens) (hU : Dense (U : Set X)),
          ∃ ψ : Γ(X, U) →+* X.rationalFunctions,
            ∀ s, ψ s = X.rationalFunctionOfSection U hU s) ∧
        Nonempty (X.rationalFunctions ≃+* X.totalQuotientSheaf.presheaf.obj (op ⊤)) :=
  exists_commRing_rationalFunctions_ringEquiv_totalQuotientSheaf_top X
    (weaklyAssociatedPointsOfScheme_eq_genericPoints X).subset hfinite

/-- **[Stacks, Tag 0EMH]**: on a locally Noetherian scheme without embedded points, the ring of
rational functions is the ring of global meromorphic functions.
One clause of [Stacks, Tag 0EMH]; the complete statement is
`AlgebraicGeometry.genericPointDecomposition_of_hasNoEmbeddedPoints`. -/
@[ega "I 7.1.3" "special case"]
theorem exists_commRing_rationalFunctions_ringEquiv_totalQuotientSheaf_top_of_hasNoEmbeddedPoints
    (X : Scheme.{u}) [IsLocallyNoetherian X] (hX : HasNoEmbeddedPoints X) :
    ∃ _ : CommRing X.rationalFunctions,
      (∀ (U : X.Opens) (hU : Dense (U : Set X)),
          ∃ ψ : Γ(X, U) →+* X.rationalFunctions,
            ∀ s, ψ s = X.rationalFunctionOfSection U hU s) ∧
        Nonempty (X.rationalFunctions ≃+* X.totalQuotientSheaf.presheaf.obj (op ⊤)) :=
  exists_commRing_rationalFunctions_ringEquiv_totalQuotientSheaf_top X
    (schemeWeaklyAssociatedPoints_eq_genericPoints_of_hasNoEmbeddedPoints X hX).le
    (finite_irreducibleComponents_of_isCompact X)

/-- **Part (6) of [Stacks, Tag 02OW]**, for a ring structure on the rational functions supplied by
the caller. -/
theorem nonempty_rationalFunctions_ringEquiv_totalQuotientSheaf_top_of_isReduced
    (X : Scheme.{u}) [IsReduced X]
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    [CommRing X.rationalFunctions]
    (hofSection : ∀ (U : X.Opens) (hU : Dense (U : Set X)),
      ∃ ψ : Γ(X, U) →+* X.rationalFunctions,
        ∀ s, ψ s = X.rationalFunctionOfSection U hU s) :
    Nonempty (X.rationalFunctions ≃+* X.totalQuotientSheaf.presheaf.obj (op ⊤)) :=
  nonempty_rationalFunctions_ringEquiv_totalQuotientSheaf_top X
    (weaklyAssociatedPointsOfScheme_eq_genericPoints X).subset hfinite hofSection

/-- **[Stacks, Tag 0EMH]**, for a ring structure on the rational functions supplied by the
caller. -/
theorem nonempty_rationalFunctions_ringEquiv_totalQuotientSheaf_top_of_hasNoEmbeddedPoints
    (X : Scheme.{u}) [IsLocallyNoetherian X] (hX : HasNoEmbeddedPoints X)
    [CommRing X.rationalFunctions]
    (hofSection : ∀ (U : X.Opens) (hU : Dense (U : Set X)),
      ∃ ψ : Γ(X, U) →+* X.rationalFunctions,
        ∀ s, ψ s = X.rationalFunctionOfSection U hU s) :
    Nonempty (X.rationalFunctions ≃+* X.totalQuotientSheaf.presheaf.obj (op ⊤)) :=
  nonempty_rationalFunctions_ringEquiv_totalQuotientSheaf_top X
    (schemeWeaklyAssociatedPoints_eq_genericPoints_of_hasNoEmbeddedPoints X hX).le
    (finite_irreducibleComponents_of_isCompact X) hofSection

end AlgebraicGeometry
