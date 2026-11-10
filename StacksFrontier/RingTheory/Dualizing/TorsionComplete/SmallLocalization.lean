module

public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.Coreflection

/-!
# Localization of modules in a fixed universe, and torsion

Let `A` be a commutative ring and `S ⊆ A` a submonoid which is small relative to a universe `v`.
The localization `S⁻¹M` of a module `M` in universe `v` is then again small relative to `v`, so
shrinking it produces an endofunctor of `ModuleCat.{v} A` with a unit from the identity. This is
the model of localization needed when the module universe is independent of the ring universe,
where `LocalizedModule S M` itself lives in `max u v`.

The functor is exact, and the unit is invertible on its image, both as a functor on modules and
on the derived category. Vanishing of all the localizations at the powers of a finite generating
family of an ideal `I` is exactly `I`-power torsion; on the derived category it is exactly the
condition that all cohomology modules are `I`-power torsion. These are the localizations whose
common kernel is the torsion subcategory, the input to the coreflection of
`Dualizing.Coreflection.exists_finite_localization_coreflection`.

## Main definitions

* `Dualizing.smallLocalization` — the localization `S⁻¹M`, shrunk into the universe of `M`.
* `Dualizing.smallLocalizationMk` — its canonical map from `M`.
* `Dualizing.smallLocalizationFunctor` — the resulting exact endofunctor of `ModuleCat.{v} A`.
* `Dualizing.smallLocalizationUnit` — the unit `𝟭 ⟶ smallLocalizationFunctor S`.

## Main results

* `Dualizing.isIso_smallLocalizationUnit_app_obj`,
  `Dualizing.smallLocalizationFunctor_map_smallLocalizationUnit_app` and
  `Dualizing.isIso_smallLocalizationFunctor_map_smallLocalizationUnit_app` — the unit is
  invertible on the image of the functor, in the forms required of an abstract localization
  functor.
* `Dualizing.isIPowerTorsion_iff_isZero_smallLocalization` — `I`-power torsion is the vanishing of
  the localizations at the powers of a generating family.
* `Dualizing.derivedPowerTorsionProperty_iff_isZero_mapDerivedCategory` — the derived form.
* `Dualizing.isIso_smul_mapDerivedCategory_smallLocalization` — the inverted element acts
  invertibly on a derived localization.

## References

* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
* [Stacks Project, Tag 0A6W](https://stacks.math.columbia.edu/tag/0A6W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace Dualizing

section Modules

variable {A : Type u} [CommRing A]

/-- A localization of a module at a small submonoid is small: it is a quotient of `M × S`. -/
theorem small_localizedModule (S : Submonoid A) [Small.{v} S] (M : ModuleCat.{v} A) :
    Small.{v} (LocalizedModule S M) :=
  small_of_surjective.{v} (IsLocalizedModule.mk'_surjective S (LocalizedModule.mkLinearMap S M))

/-- The localization `S⁻¹M`, shrunk into the universe of `M`. -/
def smallLocalization (S : Submonoid A) [Small.{v} S] (M : ModuleCat.{v} A) : ModuleCat.{v} A :=
  letI := small_localizedModule S M
  ModuleCat.of A (Shrink.{v} (LocalizedModule S M))

/-- The canonical map `M ⟶ S⁻¹M` into the shrunk localization. -/
def smallLocalizationMk (S : Submonoid A) [Small.{v} S] (M : ModuleCat.{v} A) :
    M →ₗ[A] smallLocalization S M :=
  letI := small_localizedModule S M
  (Shrink.linearEquiv A (LocalizedModule S M)).symm.toLinearMap.comp
    (LocalizedModule.mkLinearMap S M)

/-- The canonical map `M ⟶ smallLocalization S M` exhibits its target as the localization of `M`
at `S`. -/
instance isLocalizedModule_smallLocalizationMk (S : Submonoid A) [Small.{v} S]
    (M : ModuleCat.{v} A) : IsLocalizedModule S (smallLocalizationMk S M) := by
  let := small_localizedModule S M
  exact IsLocalizedModule.of_linearEquiv S (LocalizedModule.mkLinearMap S M)
    (Shrink.linearEquiv A (LocalizedModule S M)).symm

/-- Localization at `S`, shrunk into the universe of the modules, as an endofunctor of
`ModuleCat.{v} A`. -/
def smallLocalizationFunctor (S : Submonoid A) [Small.{v} S] :
    ModuleCat.{v} A ⥤ ModuleCat.{v} A where
  obj := smallLocalization S
  map {M N} f := ModuleCat.ofHom
    (IsLocalizedModule.map S (smallLocalizationMk S M) (smallLocalizationMk S N) f.hom)
  map_id _ := ModuleCat.hom_ext (IsLocalizedModule.map_id S _)
  map_comp f g := ModuleCat.hom_ext (IsLocalizedModule.map_comp' S _ _ _ f.hom g.hom)

/-- The localization functor at `S` is additive. -/
instance smallLocalizationFunctor_additive (S : Submonoid A) [Small.{v} S] :
    (smallLocalizationFunctor.{u, v} S).Additive where
  map_add {M N} f g := ModuleCat.hom_ext
    (map_add (IsLocalizedModule.map S (smallLocalizationMk S M) (smallLocalizationMk S N))
      f.hom g.hom)

/-- Localization is exact. -/
theorem smallLocalizationFunctor_map_exact (S : Submonoid A) [Small.{v} S]
    (T : ShortComplex (ModuleCat.{v} A)) (hT : T.Exact) :
    (T.map (smallLocalizationFunctor S)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hT ⊢
  change Function.Exact
    (IsLocalizedModule.map S (smallLocalizationMk S T.X₁) (smallLocalizationMk S T.X₂) T.f.hom)
    (IsLocalizedModule.map S (smallLocalizationMk S T.X₂) (smallLocalizationMk S T.X₃) T.g.hom)
  exact IsLocalizedModule.map_exact S _ _ _ T.f.hom T.g.hom hT

/-- The localization functor at `S` preserves finite limits and finite colimits. -/
theorem smallLocalizationFunctor_preservesFinite (S : Submonoid A) [Small.{v} S] :
    PreservesFiniteLimits (smallLocalizationFunctor.{u, v} S) ∧
      PreservesFiniteColimits (smallLocalizationFunctor.{u, v} S) :=
  ((Functor.exact_tfae (smallLocalizationFunctor.{u, v} S)).out 2 4).mp
    (smallLocalizationFunctor_map_exact S)

/-- The localization functor at `S` preserves finite limits. -/
instance smallLocalizationFunctor_preservesFiniteLimits (S : Submonoid A) [Small.{v} S] :
    PreservesFiniteLimits (smallLocalizationFunctor.{u, v} S) :=
  (smallLocalizationFunctor_preservesFinite S).1

/-- The localization functor at `S` preserves finite colimits. -/
instance smallLocalizationFunctor_preservesFiniteColimits (S : Submonoid A) [Small.{v} S] :
    PreservesFiniteColimits (smallLocalizationFunctor.{u, v} S) :=
  (smallLocalizationFunctor_preservesFinite S).2

/-- The unit of localization, as a natural transformation of endofunctors of
`ModuleCat.{v} A`. -/
def smallLocalizationUnit (S : Submonoid A) [Small.{v} S] :
    𝟭 (ModuleCat.{v} A) ⟶ smallLocalizationFunctor S where
  app M := ModuleCat.ofHom (smallLocalizationMk S M)
  naturality {M N} f := ModuleCat.hom_ext
    (IsLocalizedModule.map_comp S (smallLocalizationMk S M) (smallLocalizationMk S N) f.hom).symm

/-- If every element of `S` already acts invertibly on `M`, then `M` is its own localization. -/
theorem bijective_smallLocalizationMk (S : Submonoid A) [Small.{v} S] (M : ModuleCat.{v} A)
    (h : ∀ s : S, IsUnit (algebraMap A (Module.End A M) s)) :
    Function.Bijective (smallLocalizationMk S M) := by
  let : IsLocalizedModule S (LinearMap.id : M →ₗ[A] M) :=
    { map_units := h
      surj x := ⟨⟨x, 1⟩, by simp⟩
      exists_of_eq h := ⟨1, by simpa using h⟩ }
  have he : (IsLocalizedModule.linearEquiv S (LinearMap.id : M →ₗ[A] M)
      (smallLocalizationMk S M)).toLinearMap = smallLocalizationMk S M := by
    ext x
    exact IsLocalizedModule.linearEquiv_apply S _ _ x
  rw [← he]
  exact (IsLocalizedModule.linearEquiv S _ _).bijective

/-- The unit is invertible on the image of the localization functor. -/
theorem isIso_smallLocalizationUnit_app_obj (S : Submonoid A) [Small.{v} S]
    (M : ModuleCat.{v} A) :
    IsIso ((smallLocalizationUnit S).app ((smallLocalizationFunctor S).obj M)) :=
  (ConcreteCategory.isIso_iff_bijective _).2 <|
    bijective_smallLocalizationMk S (smallLocalization S M)
      (IsLocalizedModule.map_units (smallLocalizationMk S M))

/-- The localization functor takes the unit at `M` to the unit at `S⁻¹M`; in particular it takes
the unit to an isomorphism. -/
theorem smallLocalizationFunctor_map_smallLocalizationUnit_app (S : Submonoid A) [Small.{v} S]
    (M : ModuleCat.{v} A) :
    (smallLocalizationFunctor S).map ((smallLocalizationUnit S).app M) =
      (smallLocalizationUnit S).app ((smallLocalizationFunctor S).obj M) := by
  apply ModuleCat.hom_ext
  apply IsLocalizedModule.ext S (smallLocalizationMk S M)
    (IsLocalizedModule.map_units (smallLocalizationMk S (smallLocalization S M)))
  exact IsLocalizedModule.map_comp S (smallLocalizationMk S M)
    (smallLocalizationMk S (smallLocalization S M)) (smallLocalizationMk S M)

/-- The localization functor inverts the unit: it carries the unit at `M` to the unit at `S⁻¹M`,
which is an isomorphism. -/
theorem isIso_smallLocalizationFunctor_map_smallLocalizationUnit_app (S : Submonoid A)
    [Small.{v} S] (M : ModuleCat.{v} A) :
    IsIso ((smallLocalizationFunctor S).map ((smallLocalizationUnit S).app M)) := by
  rw [smallLocalizationFunctor_map_smallLocalizationUnit_app]
  exact isIso_smallLocalizationUnit_app_obj S M

/-- A localization vanishes exactly when every element of the module is killed by some element
of the submonoid. -/
theorem isZero_smallLocalization_iff (S : Submonoid A) [Small.{v} S] (M : ModuleCat.{v} A) :
    IsZero (smallLocalization S M) ↔ ∀ m : M, ∃ s : S, s • m = 0 := by
  rw [ModuleCat.isZero_iff_subsingleton,
    IsLocalizedModule.subsingleton_iff S (smallLocalizationMk S M)]
  exact ⟨fun h m => by obtain ⟨r, hr, hm⟩ := h m; exact ⟨⟨r, hr⟩, hm⟩,
    fun h m => by obtain ⟨r, hr⟩ := h m; exact ⟨r, r.property, hr⟩⟩

/-- Localizing at `S` kills `T⁻¹M` as soon as it kills `M`. -/
theorem isZero_smallLocalization_smallLocalization (S T : Submonoid A) [Small.{v} S]
    [Small.{v} T] (M : ModuleCat.{v} A) (h : IsZero (smallLocalization S M)) :
    IsZero (smallLocalization S (smallLocalization T M)) := by
  rw [isZero_smallLocalization_iff] at h ⊢
  intro x
  obtain ⟨⟨m, t⟩, rfl⟩ := IsLocalizedModule.mk'_surjective T (smallLocalizationMk T M) x
  obtain ⟨s, hs⟩ := h m
  refine ⟨s, ?_⟩
  change (s : A) • IsLocalizedModule.mk' (smallLocalizationMk T M) m t = 0
  change (s : A) • m = 0 at hs
  rw [← IsLocalizedModule.mk'_smul, hs, IsLocalizedModule.mk'_zero]

/-- The powers of an element form a small submonoid: they are the image of `ℕ`. -/
instance small_submonoidPowers {M : Type u} [Monoid M] (f : M) :
    Small.{v} (Submonoid.powers f) := by
  apply small_of_surjective.{v} (f := fun n : ℕ =>
    (⟨f ^ n, Submonoid.pow_mem _ (Submonoid.mem_powers f) n⟩ : Submonoid.powers f))
  rintro ⟨x, hx⟩
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp hx
  exact ⟨n, Subtype.ext hn⟩

/-- **A module is `I`-power torsion exactly when it dies under localization at the powers of
each generator of `I`.** -/
theorem isIPowerTorsion_iff_isZero_smallLocalization (s : Finset A) (M : ModuleCat.{v} A) :
    IsIPowerTorsion A M (Ideal.span (s : Set A)) ↔
      ∀ f ∈ s, IsZero (smallLocalization (Submonoid.powers f) M) := by
  constructor
  · intro h f hf
    rw [isZero_smallLocalization_iff]
    intro m
    obtain ⟨n, _, hn⟩ := h m
    exact ⟨⟨f ^ n, (Submonoid.mem_powers_iff _ _).2 ⟨n, rfl⟩⟩,
      hn _ (Ideal.pow_mem_pow (Ideal.subset_span hf) n)⟩
  · intro h m
    have hle : Ideal.span (s : Set A) ≤ (A ∙ m).annihilator.radical := by
      rw [Ideal.span_le]
      intro f hf
      obtain ⟨t, ht⟩ := (isZero_smallLocalization_iff _ M).mp (h f hf) m
      obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp t.property
      refine ⟨n, ?_⟩
      apply (Submodule.mem_annihilator_span_singleton m _).2
      simpa only [Submonoid.smul_def, hn] using ht
    obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hle
      (Submodule.fg_span s.finite_toSet)
    refine ⟨n + 1, Nat.succ_pos _, fun a ha => ?_⟩
    exact (Submodule.mem_annihilator_span_singleton m a).1
      (hn (Ideal.pow_le_pow_right n.le_succ ha))

end Modules

section Derived

attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A]

/-- A derived localization vanishes exactly when it vanishes on every cohomology module. -/
theorem isZero_mapDerivedCategory_smallLocalization_iff (S : Submonoid A) [Small.{v} S]
    (X : DerivedCategory (ModuleCat.{v} A)) :
    IsZero ((smallLocalizationFunctor S).mapDerivedCategory.obj X) ↔
      ∀ i, IsZero (smallLocalization S ((DerivedCategory.homologyFunctor _ i).obj X)) := by
  rw [Coreflection.isZero_iff_homology]
  exact forall_congr' fun i =>
    ((mapDerivedCategoryHomologyIso (smallLocalizationFunctor S) i).app X).isZero_iff

/-- Derived localization at `S` kills the derived localization at `T` of any object it kills. -/
theorem isZero_mapDerivedCategory_smallLocalization_comp (S T : Submonoid A) [Small.{v} S]
    [Small.{v} T] (X : DerivedCategory (ModuleCat.{v} A))
    (h : IsZero ((smallLocalizationFunctor S).mapDerivedCategory.obj X)) :
    IsZero ((smallLocalizationFunctor S).mapDerivedCategory.obj
      ((smallLocalizationFunctor T).mapDerivedCategory.obj X)) := by
  rw [isZero_mapDerivedCategory_smallLocalization_iff] at h ⊢
  intro i
  exact (isZero_smallLocalization_smallLocalization S T _ (h i)).of_iso
    ((smallLocalizationFunctor S).mapIso
      ((mapDerivedCategoryHomologyIso (smallLocalizationFunctor T) i).app X))

/-- **An object of `D(A)` has `I`-power-torsion cohomology exactly when it dies under derived
localization at the powers of each generator of `I`.** -/
theorem derivedPowerTorsionProperty_iff_isZero_mapDerivedCategory (I : Ideal A) (hI : I.FG)
    (s : Finset A) (hs : Ideal.span (s : Set A) = I) (X : DerivedCategory (ModuleCat.{v} A)) :
    derivedPowerTorsionProperty A I hI X ↔
      ∀ f ∈ s,
        IsZero ((smallLocalizationFunctor (Submonoid.powers f)).mapDerivedCategory.obj X) := by
  change (∀ i, IsIPowerTorsion A
    ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj X) I) ↔ _
  simp only [← hs, isIPowerTorsion_iff_isZero_smallLocalization,
    isZero_mapDerivedCategory_smallLocalization_iff]
  exact ⟨fun h f hf i => h i f hf, fun h i f hf => h f hf i⟩

/-- The element inverted by a derived localization acts invertibly on its values: this already
holds degreewise, on a representing complex. -/
theorem isIso_smul_mapDerivedCategory_smallLocalization (x : A)
    (K : DerivedCategory (ModuleCat.{v} A)) :
    IsIso (x • 𝟙 ((smallLocalizationFunctor (Submonoid.powers x)).mapDerivedCategory.obj K)) := by
  let F := smallLocalizationFunctor.{u, v} (Submonoid.powers x)
  let L := DerivedCategory.Q.objPreimage K
  let M := (F.mapHomologicalComplex (.up ℤ)).obj L
  have hM : IsIso (x • 𝟙 M) := by
    have : ∀ i, IsIso ((x • 𝟙 M).f i) := by
      intro i
      exact (ConcreteCategory.isIso_iff_bijective _).2 <| (Module.End.isUnit_iff _).mp
        (IsLocalizedModule.map_units (smallLocalizationMk (Submonoid.powers x) (L.X i))
          ⟨x, Submonoid.mem_powers x⟩)
    exact HomologicalComplex.Hom.isIso_of_components _
  have hQ : IsIso (x • 𝟙 (DerivedCategory.Q.obj M)) := by
    simpa only [Functor.Linear.map_smul, CategoryTheory.Functor.map_id] using
      (show IsIso (DerivedCategory.Q.map (x • 𝟙 M)) from inferInstance)
  let e : F.mapDerivedCategory.obj K ≅ DerivedCategory.Q.obj M :=
    (F.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso K)).symm ≪≫
      F.mapDerivedCategoryFactors.app L
  have he : x • 𝟙 (F.mapDerivedCategory.obj K) =
      e.hom ≫ (x • 𝟙 (DerivedCategory.Q.obj M)) ≫ e.inv := by
    simp [Linear.comp_smul, Linear.smul_comp]
  rw [he]
  infer_instance

end Derived

end Dualizing

end
