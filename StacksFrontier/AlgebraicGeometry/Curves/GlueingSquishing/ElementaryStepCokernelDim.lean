module

public import StacksFrontier.AlgebraicGeometry.Cohomology.ZeroDimensionalSupport.Vanishing
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.BadPointsLength
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.GlueingTwoPoints
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.PushforwardMono
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.AsymptoticRiemannRoch

/-!
# The one-dimensionality of `H⁰(X, f_*𝒪_{X'}/𝒪_X)` across an elementary step

Let `f : X' ⟶ X` be a morphism of algebraic `k`-schemes which is an isomorphism over the
complement of a single point `x`, and let `Q = f_*𝒪_{X'}/𝒪_X` be the cokernel of the unit
`𝒪_X ⟶ f_*𝒪_{X'}` in `X.Modules`. This file proves

`dim_k H⁰(X, Q) = 1`

from a germ-local description of the quotient: a rule `D` assigning to a section of `𝒪_{X'}`
over `f⁻¹U`, for `U` a neighbourhood of `x`, a scalar, which is additive, compatible with
restriction, kills the sections pulled back from `X`, is `k`-homogeneous for the constants, is
somewhere nonzero, and whose vanishing forces the section to come from `X` near `x`.

That is exactly what the two elementary steps of [Stacks, Tag 0C1L] supply: for a glueing of
two rational points `a` and `b` the rule is `s ↦ s(a) - s(b)`, and for a squishing of a tangent
vector `θ` it is the coefficient of `ε` in the restriction of `s` along `θ`.

## The route

The only `k`-linear identification of `H⁰` available is
`AlgebraicGeometry.finrank_globalSectionsOverField`, which replaces `H⁰(X, Q)` by the global
sections `Γ(Q, ⊤)` carrying the `k`-action restricted along the structure morphism. Those global
sections are then identified with the stalk `Q_x`: the germ map at `x` is bijective, because `Q`
has no sections on an open missing `x` and because `⊤` is covered by any neighbourhood of `x`
together with `{x}ᶜ`. On the stalk the cokernel is computed by the exactness of the stalk
functor, and the germ-local rule `D` exhibits `Q_x` as the `k`-span of a single nonzero vector.

The `k`-linearity that the source reads off an isomorphism of `Q` with the skyscraper `k_x` is
here carried by two germ-semilinearity facts, `PresheafOfModules.germ_smul` for `Q` and for
`f_*𝒪_{X'}`, and by `AlgebraicGeometry.sectionAt_constHom`-style homogeneity of `D`: no
identification of `Q` with a skyscraper sheaf of modules is constructed.

## Main results

* `Stacks.GlueSquishFactor.eq_zero_of_notMem_of_supp_subset_singleton` — a module supported in
  one point has no sections off that point.
* `Stacks.GlueSquishFactor.bijective_germ_of_supp_subset_singleton` — for such a module the germ
  map `Γ(F, ⊤) ⟶ F_x` is bijective.
* `Stacks.GlueSquishFactor.constHom_res` and `Stacks.GlueSquishFactor.app_constHom` — constant
  sections restrict and pull back to constant sections.
* `Stacks.GlueSquishFactor.finrank_cohomologyOverField_zero_cokernel_eq_one` — the evaluation
  `dim_k H⁰(X, f_*𝒪_{X'}/𝒪_X) = 1` from the germ-local data `D`.

## References

* [Stacks Project, Tag 0C1L](https://stacks.math.columbia.edu/tag/0C1L)
* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.GlueSquishFactor

/-! ### Sections and germs of a module supported in a single point -/

/-- **A module supported in the single point `x` has only the zero section over an open set
missing `x`**: such an open set meets the support not at all. -/
theorem eq_zero_of_notMem_of_supp_subset_singleton {X : Scheme.{u}} (F : X.Modules) {x : X}
    (hsupp : SheafOfModules.supp F ⊆ ({x} : Set X)) (V : X.Opens) (hx : x ∉ V) (s : Γ(F, V)) :
    s = 0 := by
  refine AlgebraicGeometry.eq_zero_of_inter_supp_eq_empty F V ?_ s
  exact Set.eq_empty_iff_forall_notMem.mpr fun y hy => hx (hsupp hy.2 ▸ hy.1)

/-- The germ map at `x` on global sections is injective for a module whose support is contained
in `{x}`. -/
theorem injective_germ_of_supp_subset_singleton {X : Scheme.{u}} (F : X.Modules) {x : X}
    (hsupp : SheafOfModules.supp F ⊆ ({x} : Set X)) :
    Function.Injective fun s : Γ(F, ⊤) => F.presheaf.germ ⊤ x (Opens.mem_top x) s := by
  intro s t hst
  refine TopCat.Presheaf.section_ext (⟨F.presheaf, F.isSheaf⟩ : TopCat.Sheaf Ab.{u} X) ⊤ s t ?_
  intro y _
  by_cases hy : y = x
  · subst hy
    exact hst
  · exact (AlgebraicGeometry.subsingleton_stalk_of_notMem_supp F
      (fun h => hy (hsupp h))).elim _ _

/-- The germ map at `x` on global sections is surjective for a module whose support is contained
in `{x}`, provided `{x}ᶜ` is open. -/
theorem surjective_germ_of_supp_subset_singleton {X : Scheme.{u}} (F : X.Modules) {x : X}
    {W : X.Opens} (hW : (W : Set X) = ({x} : Set X)ᶜ)
    (hsupp : SheafOfModules.supp F ⊆ ({x} : Set X)) :
    Function.Surjective fun s : Γ(F, ⊤) => F.presheaf.germ ⊤ x (Opens.mem_top x) s := by
  have hxW : x ∉ W := by
    intro h
    have : x ∈ (W : Set X) := h
    rw [hW] at this
    exact this rfl
  intro z
  obtain ⟨V, hxV, s, hs⟩ := F.presheaf.exists_germ_eq z
  set O : Bool → X.Opens := fun c => cond c V W
  have hOle : ∀ c, O c ≤ (⊤ : X.Opens) := fun _ => le_top
  set sf : (c : Bool) → Γ(F, O c) := fun c => match c with | true => s | false => 0
  have hcover : (⊤ : X.Opens) ≤ ⨆ c, O c := by
    intro y _
    rw [Opens.mem_iSup]
    by_cases hy : y = x
    · exact ⟨true, hy ▸ hxV⟩
    · refine ⟨false, ?_⟩
      show y ∈ (W : Set X)
      rw [hW]
      exact hy
  have hcompat : TopCat.Presheaf.IsCompatible F.presheaf O sf := by
    intro c d
    rcases eq_or_ne c d with rfl | hcd
    · rfl
    · have hxcd : x ∉ O c ⊓ O d := by
        match c, d with
        | true, true => exact absurd rfl hcd
        | false, false => exact absurd rfl hcd
        | true, false => exact fun hm => hxW hm.2
        | false, true => exact fun hm => hxW hm.1
      have h0 := eq_zero_of_notMem_of_supp_subset_singleton F hsupp (O c ⊓ O d) hxcd
      exact (h0 _).trans (h0 _).symm
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨F.presheaf, F.isSheaf⟩ : TopCat.Sheaf Ab.{u} X) O ⊤ (fun c => homOfLE (hOle c))
    hcover sf hcompat
  refine ⟨t, ?_⟩
  have h1 : F.presheaf.map (homOfLE (hOle true)).op t = s := ht true
  have h2 := TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE (hOle true)) x hxV t
  rw [h1] at h2
  exact h2.symm.trans hs

/-- **The germ map at `x` on global sections is bijective** for a module whose support is
contained in `{x}`, provided `{x}ᶜ` is open.

Injectivity: two global sections with the same germ at `x` have the same germ everywhere, the
stalks off the support being trivial. Surjectivity: a germ is represented by a section on some
neighbourhood `V` of `x`, and that section glues with the zero section on `{x}ᶜ`, the overlap
missing the support and therefore carrying no nonzero section. -/
theorem bijective_germ_of_supp_subset_singleton {X : Scheme.{u}} (F : X.Modules) {x : X}
    {W : X.Opens} (hW : (W : Set X) = ({x} : Set X)ᶜ)
    (hsupp : SheafOfModules.supp F ⊆ ({x} : Set X)) :
    Function.Bijective fun s : Γ(F, ⊤) => F.presheaf.germ ⊤ x (Opens.mem_top x) s :=
  ⟨injective_germ_of_supp_subset_singleton F hsupp,
    surjective_germ_of_supp_subset_singleton F hW hsupp⟩

/-! ### Constant sections and the unit map on sections -/

/-- Restricting a constant section to a smaller open set gives the constant section there. -/
theorem constHom_res {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    {U V : X.Opens} (hVU : V ≤ U) (hU : U ≤ (X ↘ Spec (.of k)) ⁻¹ᵁ ⊤)
    (hV : V ≤ (X ↘ Spec (.of k)) ⁻¹ᵁ ⊤) (c : k) :
    (X.presheaf.map (homOfLE hVU).op).hom (constHom X U hU c) = constHom X V hV c := by
  have h2 : ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appLE ⊤ U hU) ≫
      X.presheaf.map (homOfLE hVU).op =
      (Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appLE ⊤ V hV := by
    rw [Category.assoc, (X ↘ Spec (.of k)).appLE_map hU (homOfLE hVU).op]
  exact congrArg (fun m : CommRingCat.of k ⟶ Γ(X, V) => m.hom c) h2

/-- The constant sections over the whole space are the image of `k` under the structure
morphism on global sections. -/
theorem constHom_top {k : Type u} [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    (hU : (⊤ : X.Opens) ≤ (X ↘ Spec (.of k)) ⁻¹ᵁ ⊤) (c : k) :
    constHom X ⊤ hU c = ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop).hom c := by
  have h : (X ↘ Spec (.of k)).appLE ⊤ ⊤ hU = (X ↘ Spec (.of k)).appTop :=
    Scheme.Hom.appLE_eq_app (f := X ↘ Spec (.of k)) (U := ⊤)
  exact congrArg (fun m : CommRingCat.of k ⟶ Γ(X, ⊤) => m.hom c)
    (congrArg (fun m => (Scheme.ΓSpecIso (.of k)).inv ≫ m) h)

/-- **Constant sections pull back to constant sections** along a morphism of schemes over
`k`: the structure morphism of the source is the composite of `f` with that of the target. -/
theorem app_constHom {k : Type u} [Field k] {X' X : Scheme.{u}} [X.Over (Spec (.of k))]
    [X'.Over (Spec (.of k))] (f : X' ⟶ X) (hf : f.IsOver (Spec (.of k))) (U : X.Opens)
    (hU : U ≤ (X ↘ Spec (.of k)) ⁻¹ᵁ ⊤)
    (hU' : f ⁻¹ᵁ U ≤ (X' ↘ Spec (.of k)) ⁻¹ᵁ ⊤) (c : k) :
    (f.app U).hom (constHom X U hU c) = constHom X' (f ⁻¹ᵁ U) hU' c := by
  have hover : f ≫ (X ↘ Spec (.of k)) = X' ↘ Spec (.of k) := by
    simpa only [Scheme.Hom.isOver_iff] using hf
  have h : (X ↘ Spec (.of k)).appLE ⊤ U hU ≫ f.app U =
      (X' ↘ Spec (.of k)).appLE ⊤ (f ⁻¹ᵁ U) hU' := by
    rw [← f.appLE_eq_app (U := U), Scheme.Hom.appLE_comp_appLE, hover]
  have h2 : (Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appLE ⊤ U hU ≫ f.app U =
      (Scheme.ΓSpecIso (.of k)).inv ≫ (X' ↘ Spec (.of k)).appLE ⊤ (f ⁻¹ᵁ U) hU' := by
    rw [h]
  exact congrArg (fun m : CommRingCat.of k ⟶ Γ(X', f ⁻¹ᵁ U) => m.hom c) h2

/-- The unit map `𝒪_X ⟶ f_*𝒪_{X'}` of `Stacks.GlueSquishFactor.structureUnitHom` acts on
sections as `f.app`. -/
theorem structureUnitHom_val_app {X' X : Scheme.{u}} (f : X' ⟶ X) (U : X.Opens)
    (t : (unitModule X).presheaf.obj (op U)) :
    (structureUnitHom f).val.app (op U) t = (f.app U).hom t :=
  Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit_val_app
    (AlgebraSheaf.structureMap (pushforwardAlgebra f)) (op U) t

/-- Restriction in `f_*𝒪_{X'}`, read as an `𝒪_X`-module, is restriction in `𝒪_{X'}` along the
preimage. -/
theorem pushforwardModule_map {X' X : Scheme.{u}} (f : X' ⟶ X) {U V : X.Opens} (hVU : V ≤ U)
    (s : Γ(X', f ⁻¹ᵁ U)) :
    (AlgebraSheaf.underlyingModule (pushforwardAlgebra f) : X.Modules).presheaf.map
        (homOfLE hVU).op s = (X'.presheaf.map (homOfLE (f.preimage_mono hVU)).op).hom s := rfl

/-- The germ in `f_*𝒪_{X'}` of a restricted section is the germ of the section. -/
private theorem germ_pushforwardModule_res {X' X : Scheme.{u}} (f : X' ⟶ X) {U V : X.Opens}
    (hVU : V ≤ U) {x : X} (hxV : x ∈ V) (s : Γ(X', f ⁻¹ᵁ U)) :
    (AlgebraSheaf.underlyingModule (pushforwardAlgebra f) : X.Modules).presheaf.germ V x hxV
        ((X'.presheaf.map (homOfLE (f.preimage_mono hVU)).op).hom s) =
      (AlgebraSheaf.underlyingModule (pushforwardAlgebra f) : X.Modules).presheaf.germ U x
        (hVU hxV) s := by
  rw [← pushforwardModule_map f hVU s]
  exact TopCat.Presheaf.germ_res_apply
    (AlgebraSheaf.underlyingModule (pushforwardAlgebra f) : X.Modules).presheaf
    (homOfLE hVU) x hxV s

/-- The stalk map of the unit `𝒪_X ⟶ f_*𝒪_{X'}` carries the germ of a section of `𝒪_X` to the
germ of its pullback. -/
theorem stalkLinearMap_structureUnitHom_germ {X' X : Scheme.{u}} (f : X' ⟶ X) (U : X.Opens)
    (x : X) (hx : x ∈ U) (t : (unitModule X).presheaf.obj (op U)) :
    AlgebraicGeometry.stalkLinearMap (unitModule X)
        (AlgebraSheaf.underlyingModule (pushforwardAlgebra f) : X.Modules)
        (structureUnitHom f) x ((unitModule X).presheaf.germ U x hx t)
      = (AlgebraSheaf.underlyingModule (pushforwardAlgebra f) : X.Modules).presheaf.germ U x hx
          ((f.app U).hom t) := by
  rw [AlgebraicGeometry.stalkLinearMap_germ, structureUnitHom_val_app]

/-- **A module in `ModuleCat k` which is the `k`-span of a single nonzero vector has dimension
one.** This is `finrank_eq_one_iff_of_nonzero'` read on a bundled object, where the module
structure is the object's own and is therefore not unfolded away by instance search. -/
theorem finrank_eq_one_of_span_singleton {k : Type u} [Field k] (M : ModuleCat.{u} k) (v : M)
    (hv : v ≠ 0) (hspan : ∀ w : M, ∃ c : k, c • v = w) : Module.finrank k M = 1 :=
  (finrank_eq_one_iff_of_nonzero' v hv).mpr hspan

/-! ### Stalks of a cokernel -/

/-- The stalk of the projection onto a cokernel, followed by the comparison isomorphism, is the
projection onto the cokernel of the stalk map. -/
theorem stalkLinearMap_cokernel_π_apply {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) (x : X)
    (z : N.presheaf.stalk x) :
    (PreservesCokernel.iso (Scheme.Modules.stalkFunctor X x) φ).hom
        (AlgebraicGeometry.stalkLinearMap N (cokernel φ) (cokernel.π φ) x z) =
      cokernel.π ((Scheme.Modules.stalkFunctor X x).map φ) z := by
  show ConcreteCategory.hom ((Scheme.Modules.stalkFunctor X x).map (cokernel.π φ) ≫
    (PreservesCokernel.iso (Scheme.Modules.stalkFunctor X x) φ).hom) z = _
  exact congrArg (fun m : (Scheme.Modules.stalkFunctor X x).obj N ⟶
      cokernel ((Scheme.Modules.stalkFunctor X x).map φ) => ConcreteCategory.hom m z)
    (PreservesCokernel.π_iso_hom (Scheme.Modules.stalkFunctor X x) φ)

/-- The stalk of the projection onto a cokernel is surjective. -/
theorem surjective_stalkLinearMap_cokernel_π {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    (x : X) :
    Function.Surjective (AlgebraicGeometry.stalkLinearMap N (cokernel φ) (cokernel.π φ) x) := by
  intro q
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective
    (cokernel.π ((Scheme.Modules.stalkFunctor X x).map φ))).mp inferInstance
    ((PreservesCokernel.iso (Scheme.Modules.stalkFunctor X x) φ).hom q)
  exact ⟨z, (ConcreteCategory.bijective_of_isIso
    (PreservesCokernel.iso (Scheme.Modules.stalkFunctor X x) φ).hom).1
    ((stalkLinearMap_cokernel_π_apply φ x z).trans hz)⟩

/-- An element of the stalk killed by the projection onto the cokernel comes from the source. -/
theorem exists_stalkLinearMap_eq_of_stalkLinearMap_cokernel_π_eq_zero {X : Scheme.{u}}
    {M N : X.Modules} (φ : M ⟶ N) (x : X) (z : N.presheaf.stalk x)
    (hz : AlgebraicGeometry.stalkLinearMap N (cokernel φ) (cokernel.π φ) x z = 0) :
    ∃ w, AlgebraicGeometry.stalkLinearMap M N φ x w = z := by
  have h0 : cokernel.π ((Scheme.Modules.stalkFunctor X x).map φ) z = 0 := by
    rw [← stalkLinearMap_cokernel_π_apply φ x z, hz]
    exact map_zero _
  have hce := ShortComplex.cokernelSequence_exact ((Scheme.Modules.stalkFunctor X x).map φ)
  rw [ShortComplex.moduleCat_exact_iff] at hce
  exact hce z h0

/-- The stalk of the projection onto a cokernel kills the image of the stalk map. -/
theorem stalkLinearMap_cokernel_π_stalkLinearMap {X : Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N) (x : X) (w : M.presheaf.stalk x) :
    AlgebraicGeometry.stalkLinearMap N (cokernel φ) (cokernel.π φ) x
      (AlgebraicGeometry.stalkLinearMap M N φ x w) = 0 := by
  have h : cokernel.π ((Scheme.Modules.stalkFunctor X x).map φ)
      (AlgebraicGeometry.stalkLinearMap M N φ x w) = 0 := by
    show ConcreteCategory.hom ((Scheme.Modules.stalkFunctor X x).map φ ≫
      cokernel.π ((Scheme.Modules.stalkFunctor X x).map φ)) w = 0
    rw [cokernel.condition]
    rfl
  refine (ConcreteCategory.bijective_of_isIso
    (PreservesCokernel.iso (Scheme.Modules.stalkFunctor X x) φ).hom).1 ?_
  rw [stalkLinearMap_cokernel_π_apply, h]
  exact (map_zero _).symm

/-! ### Germs in the quotient `f_*𝒪_{X'}/𝒪_X` -/

/-- A section of `f_*𝒪_{X'}` which comes from `X` near `x` has germ killed in the quotient. -/
theorem stalkLinearMap_cokernel_π_germ_eq_zero_of_map_eq_app {X' X : Scheme.{u}} (f : X' ⟶ X)
    {x : X} {U V : X.Opens} (hU : x ∈ U) (hVU : V ≤ U) (hxV : x ∈ V) (s : Γ(X', f ⁻¹ᵁ U))
    (t : Γ(X, V))
    (hst : (X'.presheaf.map (homOfLE (f.preimage_mono hVU)).op).hom s = (f.app V).hom t) :
    AlgebraicGeometry.stalkLinearMap _ (cokernel (structureUnitHom f))
        (cokernel.π (structureUnitHom f)) x
        ((AlgebraSheaf.underlyingModule (pushforwardAlgebra f) : X.Modules).presheaf.germ
          U x hU s) = 0 := by
  have hres : (AlgebraSheaf.underlyingModule (pushforwardAlgebra f) : X.Modules).presheaf.germ
      V x hxV ((f.app V).hom t) =
      (AlgebraSheaf.underlyingModule (pushforwardAlgebra f) : X.Modules).presheaf.germ
        U x hU s := by
    rw [← hst]
    exact germ_pushforwardModule_res f hVU hxV s
  rw [← hres, ← stalkLinearMap_structureUnitHom_germ f V x hxV t]
  exact stalkLinearMap_cokernel_π_stalkLinearMap _ x _

/-- A section of `f_*𝒪_{X'}` whose germ is killed in the quotient comes from `X` near `x`. -/
theorem exists_map_eq_app_of_stalkLinearMap_cokernel_π_germ_eq_zero {X' X : Scheme.{u}}
    (f : X' ⟶ X) {x : X} {U : X.Opens} (hU : x ∈ U) (s : Γ(X', f ⁻¹ᵁ U))
    (hs : AlgebraicGeometry.stalkLinearMap _ (cokernel (structureUnitHom f))
      (cokernel.π (structureUnitHom f)) x
      ((AlgebraSheaf.underlyingModule (pushforwardAlgebra f) : X.Modules).presheaf.germ
        U x hU s) = 0) :
    ∃ (V : X.Opens) (hVU : V ≤ U) (_ : x ∈ V) (t : Γ(X, V)),
      (X'.presheaf.map (homOfLE (f.preimage_mono hVU)).op).hom s = (f.app V).hom t := by
  obtain ⟨w, hw⟩ :=
    exists_stalkLinearMap_eq_of_stalkLinearMap_cokernel_π_eq_zero (structureUnitHom f) x _ hs
  obtain ⟨V, hxV, t₀, ht⟩ := (unitModule X).presheaf.exists_germ_eq w
  rw [← ht, stalkLinearMap_structureUnitHom_germ f V x hxV t₀] at hw
  obtain ⟨V', hxV', iV, iU, heq⟩ :=
    (AlgebraSheaf.underlyingModule (pushforwardAlgebra f) : X.Modules).presheaf.germ_eq
      x hxV hU _ _ hw
  have hVle : V' ≤ V := iV.le
  have hUle : V' ≤ U := iU.le
  have heq' : (X'.presheaf.map (homOfLE (f.preimage_mono hVle)).op).hom
        ((f.app V).hom (t₀ : Γ(X, V))) =
      (X'.presheaf.map (homOfLE (f.preimage_mono hUle)).op).hom s := by
    rw [← pushforwardModule_map f hVle ((f.app V).hom (t₀ : Γ(X, V))),
      ← pushforwardModule_map f hUle s]
    exact heq
  have hnat := congrArg (fun m : Γ(X, V) ⟶ Γ(X', f ⁻¹ᵁ V') => m.hom (t₀ : Γ(X, V)))
    (map_comp_app f hVle)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hnat
  exact ⟨V', hUle, hxV', _, heq'.symm.trans hnat.symm⟩

/-- In the quotient, the germ of `a - c • b` is the germ of `a` minus the constant `c` times the
germ of `b`. -/
theorem stalkLinearMap_cokernel_π_germ_sub_constHom_mul {k : Type u} [Field k]
    {X' X : Scheme.{u}} [X.Over (Spec (.of k))] (f : X' ⟶ X) {x : X} {V : X.Opens}
    (hxV : x ∈ V) (c : k) (a b : Γ(X', f ⁻¹ᵁ V)) :
    AlgebraicGeometry.stalkLinearMap _ (cokernel (structureUnitHom f))
        (cokernel.π (structureUnitHom f)) x
        ((AlgebraSheaf.underlyingModule (pushforwardAlgebra f) : X.Modules).presheaf.germ V x hxV
          (a - (f.app V).hom (constHom X V (by simp) c) * b)) =
      AlgebraicGeometry.stalkLinearMap _ (cokernel (structureUnitHom f))
          (cokernel.π (structureUnitHom f)) x
          ((AlgebraSheaf.underlyingModule (pushforwardAlgebra f) : X.Modules).presheaf.germ V x
            hxV a) -
        X.presheaf.germ ⊤ x (Opens.mem_top x) (constHom X ⊤ (by simp) c) •
          AlgebraicGeometry.stalkLinearMap _ (cokernel (structureUnitHom f))
            (cokernel.π (structureUnitHom f)) x
            ((AlgebraSheaf.underlyingModule (pushforwardAlgebra f) : X.Modules).presheaf.germ V x
              hxV b) := by
  have hsmul : (AlgebraSheaf.underlyingModule (pushforwardAlgebra f) : X.Modules).presheaf.germ
      V x hxV ((f.app V).hom (constHom X V (by simp) c) * b) =
      X.presheaf.germ V x hxV (constHom X V (by simp) c) •
        (AlgebraSheaf.underlyingModule (pushforwardAlgebra f) : X.Modules).presheaf.germ
          V x hxV b :=
    PresheafOfModules.germ_smul
      (M := (AlgebraSheaf.underlyingModule (pushforwardAlgebra f) : X.Modules).val) x V hxV
      (constHom X V (by simp) c) b
  have hdiff : (AlgebraSheaf.underlyingModule (pushforwardAlgebra f) : X.Modules).presheaf.germ
      V x hxV (a - (f.app V).hom (constHom X V (by simp) c) * b) =
      (AlgebraSheaf.underlyingModule (pushforwardAlgebra f) : X.Modules).presheaf.germ V x hxV a -
        X.presheaf.germ V x hxV (constHom X V (by simp) c) •
          (AlgebraSheaf.underlyingModule (pushforwardAlgebra f) : X.Modules).presheaf.germ
            V x hxV b := by
    rw [← hsmul]
    exact map_sub _ _ _
  have hconst : X.presheaf.germ V x hxV (constHom X V (by simp) c) =
      X.presheaf.germ ⊤ x (Opens.mem_top x) (constHom X ⊤ (by simp) c) := by
    rw [← constHom_res (le_top : V ≤ ⊤) (by simp) (by simp) c]
    exact TopCat.Presheaf.germ_res_apply _ (homOfLE (le_top : V ≤ ⊤)) x hxV _
  rw [hdiff, map_sub, map_smul, hconst]

/-- **The stalk of the quotient at `x` is spanned by one germ** `s₀` with `D s₀ ≠ 0`, the scalars
acting through the constant sections. -/
theorem exists_constHom_smul_eq_of_stalk_cokernel {k : Type u} [Field k]
    {X' X : Scheme.{u}} [X.Over (Spec (.of k))] (f : X' ⟶ X) {x : X}
    (D : ∀ U : X.Opens, x ∈ U → Γ(X', f ⁻¹ᵁ U) → k)
    (hDadd : ∀ (U : X.Opens) (hU : x ∈ U) (s t : Γ(X', f ⁻¹ᵁ U)),
      D U hU (s + t) = D U hU s + D U hU t)
    (hDres : ∀ (U V : X.Opens) (hVU : V ≤ U) (hV : x ∈ V) (s : Γ(X', f ⁻¹ᵁ U)),
      D V hV ((X'.presheaf.map (homOfLE (f.preimage_mono hVU)).op).hom s) = D U (hVU hV) s)
    (hDconst : ∀ (U : X.Opens) (hU : x ∈ U) (c : k) (s : Γ(X', f ⁻¹ᵁ U)),
      D U hU ((f.app U).hom (constHom X U (by simp) c) * s) = c * D U hU s)
    (hDker : ∀ (U : X.Opens) (hU : x ∈ U) (s : Γ(X', f ⁻¹ᵁ U)), D U hU s = 0 →
      ∃ (V : X.Opens) (hVU : V ≤ U) (_ : x ∈ V) (t : Γ(X, V)),
        (X'.presheaf.map (homOfLE (f.preimage_mono hVU)).op).hom s = (f.app V).hom t)
    {U₀ : X.Opens} (hxU₀ : x ∈ U₀) (s₀ : Γ(X', f ⁻¹ᵁ U₀)) (hs₀ : D U₀ hxU₀ s₀ ≠ 0)
    (q : (cokernel (structureUnitHom f)).presheaf.stalk x) :
    ∃ c : k, X.presheaf.germ ⊤ x (Opens.mem_top x) (constHom X ⊤ (by simp) c) •
      AlgebraicGeometry.stalkLinearMap _ (cokernel (structureUnitHom f))
        (cokernel.π (structureUnitHom f)) x
        ((AlgebraSheaf.underlyingModule (pushforwardAlgebra f) : X.Modules).presheaf.germ
          U₀ x hxU₀ s₀) = q := by
  obtain ⟨z, rfl⟩ := surjective_stalkLinearMap_cokernel_π (structureUnitHom f) x q
  obtain ⟨U₁, hxU₁, s₁, rfl⟩ :=
    (AlgebraSheaf.underlyingModule (pushforwardAlgebra f) : X.Modules).presheaf.exists_germ_eq z
  have hxU : x ∈ U₁ ⊓ U₀ := ⟨hxU₁, hxU₀⟩
  set c : k := D U₁ hxU₁ s₁ / D U₀ hxU₀ s₀ with hc
  refine ⟨c, ?_⟩
  have hDsub : ∀ (U : X.Opens) (hU : x ∈ U) (s t : Γ(X', f ⁻¹ᵁ U)),
      D U hU (s - t) = D U hU s - D U hU t := fun U hU s t =>
    eq_sub_of_add_eq (by rw [← hDadd, sub_add_cancel])
  set s₁' : Γ(X', f ⁻¹ᵁ (U₁ ⊓ U₀)) :=
    (X'.presheaf.map (homOfLE (f.preimage_mono (inf_le_left : U₁ ⊓ U₀ ≤ U₁))).op).hom s₁
    with hs₁'
  set s₀' : Γ(X', f ⁻¹ᵁ (U₁ ⊓ U₀)) :=
    (X'.presheaf.map (homOfLE (f.preimage_mono (inf_le_right : U₁ ⊓ U₀ ≤ U₀))).op).hom s₀
    with hs₀'
  have hDd : D (U₁ ⊓ U₀) hxU (s₁' - (f.app (U₁ ⊓ U₀)).hom
      (constHom X (U₁ ⊓ U₀) (by simp) c) * s₀') = 0 := by
    rw [hDsub, hDconst, hs₁', hs₀', hDres U₁ (U₁ ⊓ U₀) inf_le_left hxU s₁,
      hDres U₀ (U₁ ⊓ U₀) inf_le_right hxU s₀, hc, div_mul_cancel₀ _ hs₀, sub_self]
  obtain ⟨V, hVU, hxV, t, hst⟩ := hDker _ hxU _ hDd
  have hgd := stalkLinearMap_cokernel_π_germ_eq_zero_of_map_eq_app f hxU hVU hxV _ t hst
  have hg₁ := germ_pushforwardModule_res f (inf_le_left : U₁ ⊓ U₀ ≤ U₁) hxU s₁
  have hg₀ := germ_pushforwardModule_res f (inf_le_right : U₁ ⊓ U₀ ≤ U₀) hxU s₀
  rw [stalkLinearMap_cokernel_π_germ_sub_constHom_mul, hg₁, hg₀, sub_eq_zero] at hgd
  exact hgd.symm

/-! ### The evaluation `dim_k H⁰(X, f_*𝒪_{X'}/𝒪_X) = 1` -/

/-- **`dim_k H⁰(X, f_*𝒪_{X'}/𝒪_X) = 1` from a germ-local description of the quotient.**

Let `f : X' ⟶ X` be a morphism of schemes over `k` which is an isomorphism over the complement
`W` of a single point `x`, and let `D` assign to a section of `𝒪_{X'}` over `f⁻¹U`, for each
neighbourhood `U` of `x`, a scalar, subject to: additivity, compatibility with restriction,
`k`-homogeneity against the constants, vanishing on the sections pulled back from `X`, being
somewhere nonzero, and the property that a section with `D s = 0` comes from `X` near `x`.

Then the cokernel `Q` of the unit `𝒪_X ⟶ f_*𝒪_{X'}` in `X.Modules` has
`dim_k H⁰(X, Q) = 1`.

This is the evaluation the Euler-characteristic bookkeeping of
`Stacks.GlueSquishFactor.eulerCharacteristic_unit_eq_add_finrank` is missing. Both elementary
steps of [Stacks, Tag 0C1L] supply such a `D`: the difference of the values at the two glued
points, and the coefficient of `ε` along the squished tangent vector. -/
theorem finrank_cohomologyOverField_zero_cokernel_eq_one {k : Type u} [Field k]
    {X' X : Scheme.{u}} [X.Over (Spec (.of k))] (f : X' ⟶ X)
    {x : X} {W : X.Opens} (hW : (W : Set X) = ({x} : Set X)ᶜ) [IsIso (f ∣_ W)]
    (D : ∀ U : X.Opens, x ∈ U → Γ(X', f ⁻¹ᵁ U) → k)
    (hDadd : ∀ (U : X.Opens) (hU : x ∈ U) (s t : Γ(X', f ⁻¹ᵁ U)),
      D U hU (s + t) = D U hU s + D U hU t)
    (hDres : ∀ (U V : X.Opens) (hVU : V ≤ U) (hV : x ∈ V) (s : Γ(X', f ⁻¹ᵁ U)),
      D V hV ((X'.presheaf.map (homOfLE (f.preimage_mono hVU)).op).hom s) = D U (hVU hV) s)
    (hDconst : ∀ (U : X.Opens) (hU : x ∈ U) (c : k) (s : Γ(X', f ⁻¹ᵁ U)),
      D U hU ((f.app U).hom (constHom X U (by simp) c) * s) = c * D U hU s)
    (hDapp : ∀ (U : X.Opens) (hU : x ∈ U) (t : Γ(X, U)), D U hU ((f.app U).hom t) = 0)
    (hDne : ∃ (U : X.Opens) (hU : x ∈ U) (s : Γ(X', f ⁻¹ᵁ U)), D U hU s ≠ 0)
    (hDker : ∀ (U : X.Opens) (hU : x ∈ U) (s : Γ(X', f ⁻¹ᵁ U)), D U hU s = 0 →
      ∃ (V : X.Opens) (hVU : V ≤ U) (_ : x ∈ V) (t : Γ(X, V)),
        (X'.presheaf.map (homOfLE (f.preimage_mono hVU)).op).hom s = (f.app V).hom t) :
    Module.finrank k (cohomologyOverField k (X ↘ Spec (.of k))
      (cokernel (structureUnitHom f)) 0) = 1 := by
  classical
  rw [← finrank_globalSectionsOverField]
  have hsupp : SheafOfModules.supp (cokernel (structureUnitHom f)) ⊆ ({x} : Set X) := by
    have h := supp_subset_compl_cokernel_structureUnitHom f W
    rwa [hW, compl_compl] at h
  have hbij := bijective_germ_of_supp_subset_singleton (cokernel (structureUnitHom f)) hW hsupp
  obtain ⟨U₀, hxU₀, s₀, hs₀⟩ := hDne
  obtain ⟨v, hv⟩ := hbij.2 (AlgebraicGeometry.stalkLinearMap _ (cokernel (structureUnitHom f))
    (cokernel.π (structureUnitHom f)) x
    ((AlgebraSheaf.underlyingModule (pushforwardAlgebra f) : X.Modules).presheaf.germ
      U₀ x hxU₀ s₀))
  have hv' : (cokernel (structureUnitHom f)).presheaf.germ ⊤ x (Opens.mem_top x) v =
      AlgebraicGeometry.stalkLinearMap _ (cokernel (structureUnitHom f))
        (cokernel.π (structureUnitHom f)) x
        ((AlgebraSheaf.underlyingModule (pushforwardAlgebra f) : X.Modules).presheaf.germ
          U₀ x hxU₀ s₀) := hv
  have hvne : v ≠ 0 := by
    rintro rfl
    obtain ⟨V, hVU, hxV, t, hst⟩ := exists_map_eq_app_of_stalkLinearMap_cokernel_π_germ_eq_zero
      f hxU₀ s₀ (hv'.symm.trans (map_zero _))
    exact hs₀ (by rw [← hDres U₀ V hVU hxV s₀, hst, hDapp V hxV])
  refine finrank_eq_one_of_span_singleton (globalSectionsOverField k (X ↘ Spec (.of k))
    (cokernel (structureUnitHom f))) v hvne fun w => ?_
  obtain ⟨c, hc⟩ := exists_constHom_smul_eq_of_stalk_cokernel f D hDadd hDres hDconst hDker
    hxU₀ s₀ hs₀ ((cokernel (structureUnitHom f)).presheaf.germ ⊤ x (Opens.mem_top x) w)
  have hsm : (cokernel (structureUnitHom f)).presheaf.germ ⊤ x (Opens.mem_top x)
      (constHom X ⊤ (by simp) c • v) =
      X.presheaf.germ ⊤ x (Opens.mem_top x) (constHom X ⊤ (by simp) c) •
        (cokernel (structureUnitHom f)).presheaf.germ ⊤ x (Opens.mem_top x) v :=
    PresheafOfModules.germ_smul (M := (cokernel (structureUnitHom f)).val) x ⊤
      (Opens.mem_top x) (constHom X ⊤ (by simp) c) v
  have hfin : (cokernel (structureUnitHom f)).presheaf.germ ⊤ x (Opens.mem_top x)
      (constHom X ⊤ (by simp) c • v) =
      (cokernel (structureUnitHom f)).presheaf.germ ⊤ x (Opens.mem_top x) w := by
    rw [hsm, hv']
    exact hc
  have hcw := hbij.1 hfin
  exact ⟨c, hcw⟩

end Stacks.GlueSquishFactor

end
