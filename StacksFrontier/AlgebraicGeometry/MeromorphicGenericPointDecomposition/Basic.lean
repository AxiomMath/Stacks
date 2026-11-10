module

public import Mathlib.Topology.Sheaves.Sheafify
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MeromorphicGenericPointDecomposition.Comparison

/-!
# Meromorphic functions from the generic points

Let `X` be a scheme such that every weakly associated point of `X` is a generic point of an
irreducible component, and such that every quasi-compact open has only finitely many
irreducible components. Then the sheaf of meromorphic functions on `X` is the product, over
the generic points `η` of the irreducible components, of the pushforwards
`j_{η, *} 𝒪_{Spec 𝒪_{X, η}}` along the canonical morphisms `j_η : Spec 𝒪_{X, η} ⟶ X`.

The proof is the one in the source. On an affine open `U = Spec A` the regular sections are
exactly the nonzerodivisors of `A`, the zerodivisors of `A` are the union of its minimal primes,
and `A` has finitely many minimal primes; so the total ring of fractions of `A` is the product
of the localizations of `A` at its minimal primes, which are the local rings at the generic
points lying in `U`. That identifies the *presheaf* of meromorphic functions with the product
on affine opens, hence on stalks, hence identifies the sheaf of meromorphic functions with the
product.

## Main definitions

* `AlgebraicGeometry.genericPointStalkProduct`: the product of the pushforwards, as a sheaf of
  rings.
* `AlgebraicGeometry.toGenericPointStalkProduct`,
  `AlgebraicGeometry.toGenericPointStalkModulePi`: the comparison maps to the product of the
  generic-point contributions, as sheaves of rings and as `𝒪_X`-modules.
* `AlgebraicGeometry.specStalkSectionsAlgEquiv`: on an open containing a generic point, the
  sections of the pushforward there are the local ring at that point.

## Main results

* `AlgebraicGeometry.isLocalization_pi_specStalkSections`: the affine computation.
* `AlgebraicGeometry.isIso_toGenericPointStalkProduct`: the comparison map of sheaves of rings
  is an isomorphism.
* `AlgebraicGeometry.meromorphicFunctions_iso_product_genericPointStalks`: the decomposition of
  the sheaf of meromorphic functions, as `𝒪_X`-modules.

## Implementation notes

The comparison is first shown to be an isomorphism of sheaves of *rings*, where the
sheafification machinery is available: the map out of the objectwise localization is bijective
on affine opens, hence bijective on stalks, and the sheafification unit is an isomorphism on
stalks. The statement for `𝒪_X`-modules is then read off, because the two comparison maps have
the same underlying maps on sections; the sections of either product are the families of
sections of the factors.

The affine computation itself is in
`StacksDraft.AlgebraicGeometry.F3b.GenericPointDecomposition.Local`, which also records that a
nonzerodivisor in the local ring at a generic point is a unit; that is what makes the
comparison map exist at all, and it is the dimension-zero statement of the source.

## References

* [Stacks Project, Tag 0EMF](https://stacks.math.columbia.edu/tag/0EMF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace ConcreteCategory

universe u

noncomputable section

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### The sections of the pushforward on an open -/

/-- The sections over `U` of the pushforward at a point form an algebra over the sections of
`X` over `U`, through the map on sections induced by the canonical morphism. -/
instance specStalkSectionsAlgebra (x : X) (U : X.Opens) :
    Algebra Γ(X, U) Γ(Spec (X.presheaf.stalk x), X.fromSpecStalk x ⁻¹ᵁ U) :=
  ((X.fromSpecStalk x).app U).hom.toAlgebra

/-- The algebra map from the sections of `X` over `U` to the sections over `U` of the pushforward
at `x` is the map on sections induced by the canonical morphism `Spec 𝒪_{X, x} ⟶ X`. -/
lemma algebraMap_specStalkSections (x : X) (U : X.Opens) (a : Γ(X, U)) :
    algebraMap Γ(X, U) Γ(Spec (X.presheaf.stalk x), X.fromSpecStalk x ⁻¹ᵁ U) a =
      ((X.fromSpecStalk x).app U).hom a := rfl

/-- The pushforward at a generic point has no sections over an open set avoiding that point. -/
lemma subsingleton_specStalkSections (η : genericPoints X) {U : X.Opens} (h : η.1 ∉ U) :
    Subsingleton Γ(Spec (X.presheaf.stalk η.1), X.fromSpecStalk η.1 ⁻¹ᵁ U) := by
  rw [fromSpecStalk_preimage_eq_bot η.2 h]
  infer_instance

/-- On an open containing a generic point, the sections of the pushforward at that point are
the local ring there. -/
def specStalkSectionsAlgEquiv (η : genericPoints X) {U : X.Opens} (hηU : η.1 ∈ U) :
    letI : Algebra Γ(X, U) (X.presheaf.stalk η.1) :=
      X.presheaf.algebra_section_stalk ⟨η.1, hηU⟩
    Γ(Spec (X.presheaf.stalk η.1), X.fromSpecStalk η.1 ⁻¹ᵁ U) ≃ₐ[Γ(X, U)]
      X.presheaf.stalk η.1 := by
  letI : Algebra Γ(X, U) (X.presheaf.stalk η.1) :=
    X.presheaf.algebra_section_stalk ⟨η.1, hηU⟩
  have htop : X.fromSpecStalk η.1 ⁻¹ᵁ U = ⊤ := fromSpecStalk_preimage_eq_top η.2 hηU
  have hiso : IsIso ((Spec (X.presheaf.stalk η.1)).presheaf.map
      (homOfLE htop.ge : (⊤ : (Spec (X.presheaf.stalk η.1)).Opens) ⟶
        X.fromSpecStalk η.1 ⁻¹ᵁ U).op) := by
    rw [show (homOfLE htop.ge : (⊤ : (Spec (X.presheaf.stalk η.1)).Opens) ⟶
      X.fromSpecStalk η.1 ⁻¹ᵁ U) = eqToHom htop.symm from Subsingleton.elim _ _]
    infer_instance
  let θ : Γ(Spec (X.presheaf.stalk η.1), X.fromSpecStalk η.1 ⁻¹ᵁ U) ≅
      X.presheaf.stalk η.1 :=
    (@asIso _ _ _ _ _ hiso) ≪≫ Scheme.ΓSpecIso (X.presheaf.stalk η.1)
  have hcomm : (X.fromSpecStalk η.1).app U ≫ θ.hom = X.presheaf.germ U η.1 hηU := by
    rw [← fromSpecStalk_appLE_germ X U η.1 hηU htop.ge]
    rfl
  exact AlgEquiv.ofRingEquiv (f := θ.commRingCatIsoToRingEquiv)
    fun a ↦ ConcreteCategory.congr_hom hcomm a

/-! ### The affine computation -/

/-- **The affine case of Stacks 0EMF.** On an affine open, the product over all the generic
points of the sections of the pushforwards is the total ring of fractions of the ring of
sections: the factors at generic points outside the open set vanish, and the remaining ones are
the localizations at the minimal primes. -/
lemma isLocalization_pi_specStalkSections
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    {U : X.Opens} (hU : IsAffineOpen U) :
    IsLocalization (nonZeroDivisors Γ(X, U))
      (∀ η : genericPoints X, Γ(Spec (X.presheaf.stalk η.1), X.fromSpecStalk η.1 ⁻¹ᵁ U)) := by
  let _ : ∀ η : {η : genericPoints X // η.1 ∈ U},
      Algebra Γ(X, U) (X.presheaf.stalk η.1.1) :=
    fun η ↦ X.presheaf.algebra_section_stalk ⟨η.1.1, η.2⟩
  have h0 : IsLocalization (nonZeroDivisors Γ(X, U))
      (∀ η : {η : genericPoints X // η.1 ∈ U}, X.presheaf.stalk η.1.1) :=
    isLocalization_pi_stalk_genericPoints hass hfinite hU
  let e2 : (∀ η : {η : genericPoints X // η.1 ∈ U},
      Γ(Spec (X.presheaf.stalk η.1.1), X.fromSpecStalk η.1.1 ⁻¹ᵁ U)) ≃ₐ[Γ(X, U)]
      (∀ η : {η : genericPoints X // η.1 ∈ U}, X.presheaf.stalk η.1.1) :=
    AlgEquiv.piCongrRight fun η ↦ specStalkSectionsAlgEquiv η.1 η.2
  let e1 := piSubtypeAlgEquivOfSubsingleton (A := Γ(X, U))
    (fun η : genericPoints X ↦ η.1 ∈ U)
    (fun η : genericPoints X ↦ Γ(Spec (X.presheaf.stalk η.1), X.fromSpecStalk η.1 ⁻¹ᵁ U))
    fun η h ↦ subsingleton_specStalkSections η h
  exact IsLocalization.isLocalization_of_algEquiv _ (e1.trans e2).symm

/-- The comparison map on an open, as a ring hom into the product. -/
def piToStalkSpecPushforwardAppHom (X : Scheme.{u}) (U : X.Opens) :
    ((regularSubmonoidPresheaf X).localizationPresheaf.obj (Opposite.op U) : Type u) →+*
      (∀ η : genericPoints X, Γ(Spec (X.presheaf.stalk η.1), X.fromSpecStalk η.1 ⁻¹ᵁ U)) :=
  RingHom.pi fun η ↦ toStalkSpecPushforwardAppHom η (Opposite.op U)

/-- On an affine open the comparison map into the product is bijective: both sides are total
rings of fractions of the ring of sections, and the map is one of algebras over it. -/
lemma bijective_piToStalkSpecPushforwardAppHom
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Bijective (piToStalkSpecPushforwardAppHom X U) := by
  have hS : (regularSubmonoidPresheaf X).obj (Opposite.op U) = nonZeroDivisors Γ(X, U) :=
    submonoidPresheafOfStalk_obj_eq_nonZeroDivisors X U hU
  have hsrc : IsLocalization (nonZeroDivisors Γ(X, U))
      ((regularSubmonoidPresheaf X).localizationPresheaf.obj (Opposite.op U)) := by
    rw [← hS]; infer_instance
  have htgt := isLocalization_pi_specStalkSections hass hfinite hU
  let e := IsLocalization.algEquiv (nonZeroDivisors Γ(X, U))
    ((regularSubmonoidPresheaf X).localizationPresheaf.obj (Opposite.op U) : Type u)
    (∀ η : genericPoints X, Γ(Spec (X.presheaf.stalk η.1), X.fromSpecStalk η.1 ⁻¹ᵁ U))
  have hΦ : piToStalkSpecPushforwardAppHom X U = e.toRingHom := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors Γ(X, U)) ?_
    apply RingHom.ext
    intro a
    change piToStalkSpecPushforwardAppHom X U (algebraMap _ _ a) = e (algebraMap _ _ a)
    rw [e.commutes]
    funext η
    change toStalkSpecPushforwardAppHom η (Opposite.op U) (algebraMap _ _ a) = _
    rw [toStalkSpecPushforwardAppHom, IsLocalization.lift_eq]
    rfl
  rw [hΦ]
  exact e.bijective

/-! ### The comparison with the product -/

/-- The product over the generic points of the pushforwards of the structure sheaves of the
spectra of the local rings, as a sheaf of rings on `X`. -/
abbrev genericPointStalkProduct (X : Scheme.{u}) : TopCat.Sheaf CommRingCat.{u} X :=
  ∏ᶜ fun η : genericPoints X ↦ stalkSpecPushforward X η.1

/-- The comparison map from the sheaf of meromorphic functions to that product. -/
def toGenericPointStalkProduct (X : Scheme.{u}) :
    X.totalQuotientSheaf ⟶ genericPointStalkProduct X :=
  Pi.lift fun η ↦ toStalkSpecPushforwardSheaf η

/-- The presheaf-level comparison map to the product. -/
abbrev toGenericPointStalkProductPresheaf (X : Scheme.{u}) :
    X.presheaf.totalQuotientPresheaf ⟶ (genericPointStalkProduct X).presheaf :=
  CategoryTheory.toSheafify (Opens.grothendieckTopology X) X.presheaf.totalQuotientPresheaf ≫
    (toGenericPointStalkProduct X).hom

/-- The component at a generic point `η` of the presheaf-level comparison map to the product is
the presheaf-level comparison map to the pushforward at `η`. -/
lemma toGenericPointStalkProductPresheaf_comp_π (η : genericPoints X) :
    toGenericPointStalkProductPresheaf X ≫
        (Pi.π (fun η : genericPoints X ↦ stalkSpecPushforward X η.1) η).hom =
      toStalkSpecPushforwardPresheaf η := by
  have h1 : (toGenericPointStalkProduct X).hom ≫
      (Pi.π (fun η : genericPoints X ↦ stalkSpecPushforward X η.1) η).hom =
      (toStalkSpecPushforwardSheaf η).hom :=
    congrArg (fun t : X.totalQuotientSheaf ⟶ stalkSpecPushforward X η.1 ↦ t.hom)
      (Pi.lift_comp_π (fun η ↦ toStalkSpecPushforwardSheaf η) η)
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun t ↦ CategoryTheory.toSheafify (Opens.grothendieckTopology X)
    X.presheaf.totalQuotientPresheaf ≫ t) h1).trans ?_
  exact toSheafify_comp_toStalkSpecPushforwardSheaf_hom η

/-- On sections over `U`, read as families of sections of the factors, the presheaf-level
comparison map to the product is `piToStalkSpecPushforwardAppHom X U`. -/
lemma ringSheafSectionsPiEquiv_toGenericPointStalkProductPresheaf (U : X.Opens)
    (x : X.presheaf.totalQuotientPresheaf.obj (Opposite.op U)) :
    ringSheafSectionsPiEquiv (fun η : genericPoints X ↦ stalkSpecPushforward X η.1) U
        (((toGenericPointStalkProductPresheaf X).app (Opposite.op U)).hom x) =
      piToStalkSpecPushforwardAppHom X U x := by
  funext η
  refine (ringSheafSectionsPiEquiv_apply _ _ _ η).trans ?_
  exact ConcreteCategory.congr_hom
    (congrArg (fun t : X.presheaf.totalQuotientPresheaf ⟶
        (stalkSpecPushforward X η.1).presheaf ↦ t.app (Opposite.op U))
      (toGenericPointStalkProductPresheaf_comp_π η)) x

/-- A map is bijective if its composite with an equivalence is a bijective map. -/
private theorem bijective_of_equiv_comp_eq {α β γ : Type*} (e : β ≃ γ) {f : α → β} {g : α → γ}
    (hfg : ∀ x, e (f x) = g x) (hg : Function.Bijective g) : Function.Bijective f :=
  Function.Bijective.of_comp_left (f := e) (by rwa [show e ∘ f = g from funext hfg]) e.injective

/-- On an affine open, the presheaf-level comparison map to the product is bijective on
sections. -/
lemma bijective_toGenericPointStalkProductPresheaf_app
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Bijective
      ((toGenericPointStalkProductPresheaf X).app (Opposite.op U)).hom := by
  exact bijective_of_equiv_comp_eq
    (ringSheafSectionsPiEquiv (fun η : genericPoints X ↦ stalkSpecPushforward X η.1) U)
    (ringSheafSectionsPiEquiv_toGenericPointStalkProductPresheaf U)
    (bijective_piToStalkSpecPushforwardAppHom hass hfinite hU)

/-- The presheaf-level comparison map to the product is an isomorphism on every stalk. -/
lemma isIso_stalkFunctor_map_toGenericPointStalkProductPresheaf
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    (x : X) :
    IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
      (toGenericPointStalkProductPresheaf X)) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis X.isBasis_affineOpens
    (fun V hV ↦ (bijective_toGenericPointStalkProductPresheaf_app hass hfinite hV).1) x, ?_⟩
  intro t
  obtain ⟨V, hxV, hVB, s, hs⟩ := TopCat.Presheaf.exists_mem_germ_eq_of_isBasis
    X.isBasis_affineOpens (genericPointStalkProduct X).presheaf x t
  obtain ⟨y, hy⟩ := (bijective_toGenericPointStalkProductPresheaf_app hass hfinite hVB).2 s
  refine ⟨(X.presheaf.totalQuotientPresheaf.germ V x hxV).hom y, ?_⟩
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, hy, hs]

/-- The comparison map of sheaves of rings is an isomorphism: it is so on stalks, because the
presheaf-level comparison is bijective on the affine opens and the sheafification unit is an
isomorphism on stalks. -/
@[stacks 0EMF "generic_point_decomposition"]
lemma isIso_toGenericPointStalkProduct
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite) :
    IsIso (toGenericPointStalkProduct X) := by
  have hst : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
      (toGenericPointStalkProduct X).hom) := by
    intro x
    have h1 : IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
          X.presheaf.totalQuotientPresheaf)) :=
      TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x CommRingCat.{u} _
    have h2 : IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
        (toGenericPointStalkProductPresheaf X)) :=
      isIso_stalkFunctor_map_toGenericPointStalkProductPresheaf hass hfinite x
    exact IsIso.of_isIso_fac_left (f := (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
          X.presheaf.totalQuotientPresheaf))
      (g := (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
        (toGenericPointStalkProduct X).hom)
      (h := (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
        (toGenericPointStalkProductPresheaf X))
      (Functor.map_comp _ _ _).symm
  exact TopCat.Presheaf.isIso_of_stalkFunctor_map_iso _

/-! ### The decomposition of the module of meromorphic functions -/

/-- Applying the `η`-th projection to the image of `x` under a lifted map to a product, on
sections, gives the image of `x` under the `η`-th component. -/
private theorem map_π_map_lift_apply {C D : Type*} [Category C] [Category D] {FD : D → D → Type*}
    {CD : D → Type*} [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory D FD]
    (F : C ⥤ D) {ι : Type*} {Y : ι → C} [HasProduct Y] {Z : C} (f : ∀ i, Z ⟶ Y i) (η : ι)
    (x : ToType (F.obj Z)) :
    F.map (Pi.π Y η) (F.map (Pi.lift f) x) = F.map (f η) x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, Pi.lift_comp_π]

/-- The comparison map from meromorphic functions to the product of the generic-point
contributions, as `𝒪_X`-modules. -/
def toGenericPointStalkModulePi (X : Scheme.{u}) :
    meromorphicFunctions X ⟶ ∏ᶜ fun η : genericPoints X ↦ genericPointStalkModule X η :=
  Pi.lift fun η ↦ toGenericPointStalkModule η

/-- The component at a generic point `η` of the sections over `U` of the comparison map of
`𝒪_X`-modules is the map on sections of the comparison map to the pushforward at `η`. -/
lemma modulesSectionsPiEquiv_toGenericPointStalkModulePi (U : X.Opens)
    (x : ToType ((modulesSectionsFunctor X U).obj (meromorphicFunctions X)))
    (η : genericPoints X) :
    modulesSectionsPiEquiv (fun η : genericPoints X ↦ genericPointStalkModule X η) U
        (((toGenericPointStalkModulePi X).app U) x) η =
      ((toStalkSpecPushforwardSheaf η).hom.app (Opposite.op U)).hom x := by
  refine (modulesSectionsPiEquiv_apply _ _ _ η).trans ?_
  exact map_π_map_lift_apply (modulesSectionsFunctor X U) _ η x

/-- The component at a generic point `η` of the sections over `U` of the comparison map of
sheaves of rings is the map on sections of the comparison map to the pushforward at `η`. -/
lemma ringSheafSectionsPiEquiv_toGenericPointStalkProduct (U : X.Opens)
    (x : ToType ((ringSheafSectionsFunctor X U).obj X.totalQuotientSheaf))
    (η : genericPoints X) :
    ringSheafSectionsPiEquiv (fun η : genericPoints X ↦ stalkSpecPushforward X η.1) U
        (((toGenericPointStalkProduct X).hom.app (Opposite.op U)).hom x) η =
      ((toStalkSpecPushforwardSheaf η).hom.app (Opposite.op U)).hom x := by
  refine (ringSheafSectionsPiEquiv_apply _ _ _ η).trans ?_
  exact map_π_map_lift_apply (ringSheafSectionsFunctor X U) _ η x

/-- The comparison map of `𝒪_X`-modules is an isomorphism. -/
lemma isIso_toGenericPointStalkModulePi
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite) :
    IsIso (toGenericPointStalkModulePi X) := by
  have hring : IsIso (toGenericPointStalkProduct X) :=
    isIso_toGenericPointStalkProduct hass hfinite
  have hhom : IsIso (toGenericPointStalkProduct X).hom :=
    Functor.map_isIso (TopCat.Sheaf.forget CommRingCat.{u} X) (toGenericPointStalkProduct X)
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro U
  rw [ConcreteCategory.isIso_iff_bijective]
  have hR : Function.Bijective
      (((toGenericPointStalkProduct X).hom.app (Opposite.op U)).hom) := by
    rw [← ConcreteCategory.isIso_iff_bijective]
    infer_instance
  have hG : Function.Bijective (fun x ↦
      ringSheafSectionsPiEquiv (fun η : genericPoints X ↦ stalkSpecPushforward X η.1) U
        (((toGenericPointStalkProduct X).hom.app (Opposite.op U)).hom x)) :=
    (ringSheafSectionsPiEquiv (fun η : genericPoints X ↦ stalkSpecPushforward X η.1)
      U).bijective.comp hR
  exact bijective_of_equiv_comp_eq
    (modulesSectionsPiEquiv (fun η : genericPoints X ↦ genericPointStalkModule X η) U)
    (fun x ↦ funext fun η ↦
      (modulesSectionsPiEquiv_toGenericPointStalkModulePi U x η).trans
        (ringSheafSectionsPiEquiv_toGenericPointStalkProduct U x η).symm) hG

/-- **Stacks 0EMF.** The `𝒪_X`-module of meromorphic functions is the product of the
pushed-forward structure sheaves of the local schemes at the generic points of the irreducible
components, for a scheme whose weakly associated points are generic points of irreducible
components and whose quasi-compact opens have finitely many irreducible components. -/
@[stacks 0EMF "generic_point_decomposition"]
theorem meromorphicFunctions_iso_product_genericPointStalks
    (X : Scheme.{u})
    (hassoc : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) →
      (irreducibleComponents U).Finite) :
    Nonempty (meromorphicFunctions X ≅
      ∏ᶜ fun η : genericPoints X ↦ genericPointStalkModule X η) :=
  ⟨@asIso _ _ _ _ _ (isIso_toGenericPointStalkModulePi hassoc hfinite)⟩

end AlgebraicGeometry
