module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Triangulated.Generators
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleLength
public import StacksFrontier.CategoryTheory.Triangulated.OperationsOnFullSubcategories

/-!
# The derived category of the spectrum of a field

Let `k` be a field. Every `𝒪_{Spec k}`-module is the module associated to its global sections,
so `Mod(𝒪_{Spec k})` is equivalent to the category of `k`-vector spaces; in particular every
object of it is projective and all higher `Ext` groups vanish. Consequently a bounded object
`V` of `D(𝒪_{Spec k})` is the direct sum `⨁ᵢ H^i(V)[-i]` of its cohomology sheaves, and when
those are coherent, that is finite dimensional, `V` is a finite direct sum of shifts of
`𝒪_{Spec k}`:

`V ∈ smd(add(𝒪_{Spec k}[a, b]))`

whenever `H^i(V)` is coherent for all `i` and vanishes outside `[a, b]`, in the notation of
Derived Categories, Section 13.35 ([Stacks, Tag 0FX0]). This is the step of the proof of
[Stacks, Tag 0FZ6] that reads "each `H^i(X, K)` is finite dimensional. We conclude that the
right hand side is contained in `smd(add(𝒢[-m + a, m + b])^{⋆ n})`".

## Main results

* `AlgebraicGeometry.SpecFieldDerived.isIso_of_bijective_app_top_of_subsingleton`: on a scheme
  with at most one point a morphism of modules is an isomorphism once it is bijective on global
  sections.
* `AlgebraicGeometry.SpecFieldDerived.isIso_tildeAdjunction_counit_of_subsingleton`: on a
  one-point spectrum every module is the module associated to its global sections.
* `AlgebraicGeometry.SpecFieldDerived.projective_of_field`: every `𝒪_{Spec k}`-module is
  projective.
* `AlgebraicGeometry.SpecFieldDerived.nonempty_iso_biproduct_homology`: a bounded object of
  `D(𝒪_{Spec k})` is the direct sum of its shifted cohomology sheaves.
* `AlgebraicGeometry.SpecFieldDerived.exists_iso_biproduct_unit_of_isCoherent`: a coherent
  `𝒪_{Spec k}`-module is a finite direct sum of copies of `𝒪_{Spec k}`.
* `AlgebraicGeometry.SpecFieldDerived.mem_window_of_isCoherent_homology`: the membership
  `V ∈ smd(add(𝒪_{Spec k}[a, b]))` above.

## Implementation notes

The shifted family `P[a, b]` is spelled `⨆ i ∈ Set.Icc a b, P.isoClosure.shift i`, as in
`StacksFrontier/CategoryTheory/Triangulated/Generators.lean`; with Mathlib's convention for
`ObjectProperty.shift`, an object `𝒪[-i]` concentrated in cohomological degree `i` lies in
`P.shift i` for `P = {𝒪[0]}`, so the window `[a, b]` is the window of cohomological degrees.

## References

* [Stacks Project, Tag 0FX0](https://stacks.math.columbia.edu/tag/0FX0)
* [Stacks Project, Tag 0FZ6](https://stacks.math.columbia.edu/tag/0FZ6)
* [Stacks Project, Tag 0EWX](https://stacks.math.columbia.edu/tag/0EWX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped ZeroObject

universe u

namespace AlgebraicGeometry.SpecFieldDerived

/-! ### Modules on a one-point scheme -/

/-- **On a scheme with at most one point, a morphism of modules which is bijective on global
sections is an isomorphism.** The only other open is the empty one, over which both modules
vanish, their scalars there being the zero ring. -/
theorem isIso_of_bijective_app_top_of_subsingleton {X : Scheme.{u}} [Subsingleton X]
    {M N : X.Modules} (φ : M ⟶ N) (h : Function.Bijective (φ.app ⊤)) : IsIso φ := by
  have hU : ∀ U : X.Opens, Function.Bijective (φ.app U) := by
    intro U
    by_cases hne : (U : Set X).Nonempty
    · obtain ⟨y, hy⟩ := hne
      obtain rfl : U = ⊤ := by
        ext x
        simp only [Opens.coe_top, Set.mem_univ, iff_true]
        exact Subsingleton.elim y x ▸ hy
      exact h
    · obtain rfl : U = ⊥ := by
        ext x
        simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
        exact fun hx => hne ⟨x, hx⟩
      have : Subsingleton Γ(M, ⊥) := Module.subsingleton Γ(X, ⊥) _
      have : Subsingleton Γ(N, ⊥) := Module.subsingleton Γ(X, ⊥) _
      exact ⟨fun a b _ => Subsingleton.elim a b, fun b => ⟨0, Subsingleton.elim _ _⟩⟩
  have : IsIso ((Scheme.Modules.toPresheaf X).map φ) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro U
    exact (ConcreteCategory.isIso_iff_bijective _).2 (hU U.unop)
  exact isIso_of_reflects_iso φ (Scheme.Modules.toPresheaf X)

variable {R : CommRingCat.{u}} [Subsingleton (Spec R)]

/-- **On a one-point spectrum every module is the module associated to its global sections**:
the counit `~Γ(M) ⟶ M` of the adjunction `~ ⊣ Γ` is an isomorphism. -/
instance isIso_tildeAdjunction_counit_of_subsingleton :
    IsIso (tilde.adjunction (R := R)).counit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have : IsIso ((tilde.adjunction (R := R)).unit.app (moduleSpecΓFunctor.obj M) ≫
      (moduleSpecΓFunctor (R := R)).map ((tilde.adjunction (R := R)).counit.app M)) := by
    rw [(tilde.adjunction (R := R)).right_triangle_components M]
    infer_instance
  have h1 : IsIso ((moduleSpecΓFunctor (R := R)).map ((tilde.adjunction (R := R)).counit.app M)) :=
    IsIso.of_isIso_comp_left ((tilde.adjunction (R := R)).unit.app _) _
  have hb := (ConcreteCategory.isIso_iff_bijective _).1 h1
  exact isIso_of_bijective_app_top_of_subsingleton _ hb

/-- **`R`-modules and `𝒪_{Spec R}`-modules are equivalent when `Spec R` is a point**, through the
module associated to an `R`-module and global sections. -/
def tildeEquivalenceOfSubsingleton : ModuleCat.{u} R ≌ (Spec R).Modules :=
  (tilde.adjunction (R := R)).toEquivalence

/-! ### Modules on the spectrum of a field -/


variable (k : Type u) [Field k]

/-- The spectrum of a field has at most one point. -/
instance subsingleton_spec_field : Subsingleton (Spec (.of k)) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum k))

/-- **Every `𝒪_{Spec k}`-module is projective.** -/
theorem projective_of_field (M : (Spec (.of k)).Modules) : Projective M := by
  let e := tildeEquivalenceOfSubsingleton (R := .of k)
  let : Field (CommRingCat.of k) := inferInstanceAs (Field k)
  exact Projective.of_iso (e.counitIso.app M) ((e.map_projective_iff _).2
    (ModuleCat.projective_of_free
      (Module.Basis.ofVectorSpace (CommRingCat.of k) (e.inverse.obj M))))

/-! ### Objects of the derived category -/

attribute [local instance 100000] HasDerivedCategory.standard

/-- **A bounded object of `D(𝒪_{Spec k})` is the direct sum of its shifted cohomology sheaves.** -/
theorem nonempty_iso_biproduct_homology (V : DerivedCategory (Spec (.of k)).Modules) (a b : ℤ)
    [V.IsGE a] [V.IsLE b] :
    Nonempty (V ≅ ⨁ fun i : Finset.Icc a b =>
      (DerivedCategory.singleFunctor _ i.1).obj
        ((DerivedCategory.homologyFunctor _ i.1).obj V)) := by
  let := HasExt.standard (Spec (.of k)).Modules
  exact DerivedCategory.nonempty_iso_biproduct_singleFunctor_obj_homology_of_forall_ext_two_eq_zero
    V a b fun _ B e => by
      have := projective_of_field k B
      exact Abelian.Ext.eq_zero_of_projective e

/-- The module associated to `Rⁿ`, placed in degree `i`, is the direct sum of `n` copies of
`𝒪_{Spec R}[-i]`. -/
def singleTildeBiproductIso (R : CommRingCat.{u}) (n : ℕ) (i : ℤ) :
    (tilde.functor R ⋙ DerivedCategory.singleFunctor (Spec R).Modules i).obj
        (⨁ fun _ : Fin n => ModuleCat.of R R) ≅
      ⨁ fun _ : Fin n => (DerivedCategory.singleFunctor (Spec R).Modules i).obj
        (SheafOfModules.unit (Spec R).ringCatSheaf) :=
  (tilde.functor R ⋙ DerivedCategory.singleFunctor (Spec R).Modules i).mapBiproduct _ ≪≫
    biproduct.mapIso fun _ => (DerivedCategory.singleFunctor (Spec R).Modules i).mapIso tildeSelf

/-- **A coherent `𝒪_{Spec k}`-module placed in degree `i` is a finite direct sum of copies of
`𝒪_{Spec k}[-i]`**: its global sections are a finite dimensional `k`-vector space, hence `kⁿ`,
and the module is the module associated to them. -/
theorem exists_iso_biproduct_single_unit_of_isCoherent (H : (Spec (.of k)).Modules)
    (hH : SheafOfModules.IsCoherent H) (i : ℤ) :
    ∃ n : ℕ, Nonempty ((DerivedCategory.singleFunctor _ i).obj H ≅
      ⨁ fun _ : Fin n => (DerivedCategory.singleFunctor (Spec (.of k)).Modules i).obj
        (SheafOfModules.unit (Spec (.of k)).ringCatSheaf)) := by
  let : Field (CommRingCat.of k) := inferInstanceAs (Field k)
  have hfin : Module.Finite (CommRingCat.of k) (moduleSpecΓFunctor.obj H) :=
    Stacks.Algebraization.finite_globalSections_of_isCoherent H hH
  let bV := Module.finBasis (CommRingCat.of k) (moduleSpecΓFunctor.obj H)
  let eV : moduleSpecΓFunctor.obj H ≅
      ⨁ fun _ : Fin _ => ModuleCat.of (CommRingCat.of k) (CommRingCat.of k) :=
    bV.equivFun.toModuleIso ≪≫
      (ModuleCat.biproductIsoPi fun _ => ModuleCat.of (CommRingCat.of k) (CommRingCat.of k)).symm
  exact ⟨_, ⟨(DerivedCategory.singleFunctor _ i).mapIso
      (asIso ((tilde.adjunction (R := .of k)).counit.app H)).symm ≪≫
    (tilde.functor _ ⋙ DerivedCategory.singleFunctor _ i).mapIso eV ≪≫
      singleTildeBiproductIso _ _ i⟩⟩

/-! ### The window `smd(add(𝒪[a, b]))` -/

/-- **A finite direct sum of objects of `smd(add(P))` lies in `smd(add(P))`**, as soon as `P` has
an object: the zero object is then a retract of it, and `smd(add(P))` is closed under binary
products ([Stacks, Tag 0FX3] (2)). -/
theorem prop_biproduct_retractClosure_binaryProductsClosure {D : Type*} [Category D]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D] (P : ObjectProperty D) {X₀ : D} (hX₀ : P X₀)
    {J : Type} [Finite J] (f : J → D)
    (h : ∀ j, P.binaryProductsClosure.retractClosure (f j)) :
    P.binaryProductsClosure.retractClosure (⨁ f) := by
  have : P.binaryProductsClosure.retractClosure.IsClosedUnderBinaryProducts :=
    ObjectProperty.isClosedUnderBinaryProducts_retractClosure _
  have : P.binaryProductsClosure.retractClosure.ContainsZero :=
    ⟨⟨0, isZero_zero D, X₀, ObjectProperty.le_limitsClosure _ _ _ hX₀,
      ⟨⟨0, 0, (isZero_zero D).eq_of_src _ _⟩⟩⟩⟩
  have : P.binaryProductsClosure.retractClosure.IsClosedUnderFiniteProducts := .mk'
  exact ObjectProperty.prop_of_isLimit_fan _ (biproduct.isLimit f) h

/-- **A bounded object of `D(𝒪_{Spec k})` with coherent cohomology in degrees `[a, b]` lies in
`smd(add(𝒪_{Spec k}[a, b]))`.** By `nonempty_iso_biproduct_homology` it is the direct sum of its
shifted cohomology sheaves `H^i(V)[-i]`, `a ≤ i ≤ b`, and each of these is a finite direct sum of
copies of `𝒪_{Spec k}[-i]` by `exists_iso_biproduct_single_unit_of_isCoherent`. This is the
step "each `H^i(X, K)` is finite dimensional" of the proof of [Stacks, Tag 0FZ6]. -/
theorem mem_window_of_isCoherent_homology (V : DerivedCategory (Spec (.of k)).Modules)
    (a b : ℤ) (hle : a ≤ b)
    (hcoh : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor (Spec (.of k)).Modules i).obj V).IsCoherent)
    (hab : ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor (Spec (.of k)).Modules i).obj V)) :
    ((⨆ i ∈ Set.Icc a b, (ObjectProperty.singleton
        ((DerivedCategory.singleFunctor (Spec (.of k)).Modules 0).obj
          (SheafOfModules.unit (Spec (.of k)).ringCatSheaf))).isoClosure.shift i
      ).binaryProductsClosure).retractClosure V := by
  set P := ⨆ i ∈ Set.Icc a b, (ObjectProperty.singleton
    ((DerivedCategory.singleFunctor (Spec (.of k)).Modules 0).obj
      (SheafOfModules.unit (Spec (.of k)).ringCatSheaf))).isoClosure.shift i with hP
  have hGE : V.IsGE a := (DerivedCategory.isGE_iff V a).2 fun i hi => hab i (Or.inl hi)
  have hLE : V.IsLE b := (DerivedCategory.isLE_iff V b).2 fun i hi => hab i (Or.inr hi)
  have hsingle : ∀ i ∈ Set.Icc a b, P ((DerivedCategory.singleFunctor (Spec (.of k)).Modules i).obj
      (SheafOfModules.unit (Spec (.of k)).ringCatSheaf)) := fun i hi => by
    rw [hP, ObjectProperty.prop_iSup_iff]
    refine ⟨i, ?_⟩
    rw [ObjectProperty.prop_iSup_iff]
    exact ⟨hi, _, (ObjectProperty.singleton_iff _ _).2 rfl,
      ⟨((DerivedCategory.singleFunctors (Spec (.of k)).Modules).shiftIso i 0 i (by omega)).app _⟩⟩
  have hR : ∀ i ∈ Set.Icc a b, P.binaryProductsClosure.retractClosure
      ((DerivedCategory.singleFunctor (Spec (.of k)).Modules i).obj
        ((DerivedCategory.homologyFunctor (Spec (.of k)).Modules i).obj V)) := by
    intro i hi
    obtain ⟨n, ⟨e⟩⟩ := exists_iso_biproduct_single_unit_of_isCoherent k _ (hcoh i) i
    exact ObjectProperty.prop_of_iso _ e.symm
      (prop_biproduct_retractClosure_binaryProductsClosure P (hsingle a ⟨le_rfl, hle⟩) _
        fun _ => ObjectProperty.le_retractClosure _ _
          (ObjectProperty.le_limitsClosure _ _ _ (hsingle i hi)))
  obtain ⟨e⟩ := nonempty_iso_biproduct_homology k V a b
  exact ObjectProperty.prop_of_iso _ e.symm
    (prop_biproduct_retractClosure_binaryProductsClosure P (hsingle a ⟨le_rfl, hle⟩) _
      fun i => hR i.1 (Finset.mem_Icc.1 i.2))

end AlgebraicGeometry.SpecFieldDerived

end
