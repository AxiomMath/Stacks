module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingComplex

/-!
# The category of module glueing data

For a ring map `R → S` and a finite family `f = (f₁, …, f_t)` in `R`, this file packages systems
consisting of an `S`-module, modules over the rings `R[1 / fᵢ]`, comparison isomorphisms on the
overlaps, and their compatibility and cocycle conditions. This is the category
`Glue(R → S, f₁, …, f_t)`. It also records the canonical glueing-data functor `Can` from
`R`-modules, the functor `H⁰` of compatible global sections, the adjunction `Can ⊣ H⁰`, and — when
`R → S` is flat — the fact that the category of glueing data is abelian and that `Can` is exact
and preserves arbitrary colimits.

The adjunction is in `FormalGlueingCategory.Adjunction`, the left exactness of `H⁰` in
`FormalGlueingCategory.Exactness`, and the abelian structure in `FormalGlueingCategory.Abelian`.

## Main definitions

* `FormalGlueing.LocalizationComparisons`: canonical comparison of iterated and simultaneous
  localization.
* `FormalGlueing.ModuleGlueingDatum`: a system of modules and overlap isomorphisms.
* `FormalGlueing.ModuleGlueingMap`: a compatible family of maps between two systems.
* `FormalGlueing.compatibleSections`: the `R`-module of compatible tuples.
* `FormalGlueing.canonicalSectionsUnit`: the natural map from a module to its compatible
  sections.

## Implementation notes

The source identifies iterated localizations with localization at the product without notation.
Here that identification is explicit and characterized on fractions with denominator one. The
generic scalar extension is represented as `S ⊗[R] M`, canonically isomorphic to the source's
`M ⊗[R] S`; likewise, `Mᵢ ⊗[R] S` is written `S ⊗[R] Mᵢ`, so that the comparison isomorphism is
genuinely `S`-linear. The localization `(M')_{fᵢ}` is taken over `S` at the image of `fᵢ`, rather
than by forgetting to an `R`-module. The compatibility and cocycle fields compare composites
constructed from the given overlap isomorphisms; they are not additional freely chosen path maps.
Equality of maps out of a localized module is expressed on its original module, using the
localization universal property.
-/

/-! ### The category of module glueing data -/

@[expose] public section

namespace FormalGlueing

universe u v w

open CategoryTheory Cech TensorProduct

variable {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
variable {r : ℕ} (f : Fin r → R)

attribute [local instance] LocalizedModule.moduleOfIsLocalization

/-- The underlying `R`-module of an `S`-module. -/
public noncomputable abbrev restrictFromTarget (M : ModuleCat.{w} S) : ModuleCat.{w} R :=
  (ModuleCat.restrictScalars (algebraMap R S)).obj M

/-- The underlying `R`-module of a module over `R[1 / fᵢ]`. -/
public noncomputable abbrev restrictFromAway (i : Fin r)
    (M : ModuleCat.{w} (Localization.Away (f i))) : ModuleCat.{w} R :=
  (ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i)))).obj M

/-- Regard an equivalence over `R[1 / fᵢ]` as an `R`-linear equivalence, using the canonical
restricted scalar structure on its source. -/
public noncomputable def restrictAwayLinearEquiv (i : Fin r)
    {M : ModuleCat.{w} (Localization.Away (f i))} {N : Type*}
    [AddCommGroup N] [Module R N] [Module (Localization.Away (f i)) N]
    [IsScalarTower R (Localization.Away (f i)) N]
    (e : M ≃ₗ[Localization.Away (f i)] N) :
    letI : Module R M := Module.compHom M (algebraMap R (Localization.Away (f i)))
    M ≃ₗ[R] N :=
  by
    letI : Module R M := Module.compHom M (algebraMap R (Localization.Away (f i)))
    letI : IsScalarTower R (Localization.Away (f i)) M :=
      ⟨fun r a m ↦ by
        rw [Algebra.smul_def, mul_smul]
        change _ = (algebraMap R (Localization.Away (f i)) r) • (a • m)
        rfl⟩
    exact e.restrictScalars R

/-- Localization of an `R`-linear map, viewed again as an `R`-linear map. -/
public noncomputable def localizedMap {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (s : Finset (Fin r)) (g : M →ₗ[R] N) :
    cechMod f M s →ₗ[R] cechMod f N s :=
  (LocalizedModule.map (cechSub f s) g).restrictScalars R

/-- Reindex a Čech localization along an equality of indexing sets. -/
public def cechModCongr {M : Type*} [AddCommGroup M] [Module R M]
    {s t : Finset (Fin r)} (h : s = t) : cechMod f M s ≃ₗ[R] cechMod f M t :=
  LinearEquiv.cast (M := fun q : Finset (Fin r) ↦ cechMod f M q) h

/-- Localization at `s` followed by localization at `t` is canonically simultaneous
localization at `s ∪ t`. The equation on denominator-one fractions uniquely specifies it. -/
public structure LocalizationComparisons where
  /-- The identification of `(M_s)_t` with `M_{s ∪ t}`. -/
  iterated : ∀ (M : Type w) [AddCommGroup M] [Module R M] (s t : Finset (Fin r)),
    cechMod f (cechMod f M s) t ≃ₗ[R] cechMod f M (s ∪ t)
  /-- The identification `iterated` sends the iterated fraction `m / 1 / 1` to `m / 1`. -/
  iterated_mk : ∀ (M : Type w) [AddCommGroup M] [Module R M]
      (s t : Finset (Fin r)) (m : M),
    iterated M s t
        (LocalizedModule.mkLinearMap (cechSub f t) _
          (LocalizedModule.mkLinearMap (cechSub f s) _ m)) =
      LocalizedModule.mkLinearMap (cechSub f (s ∪ t)) _ m

/-- Localization does not destroy an invertible scalar action. -/
theorem localized_isUnit (T : Submonoid R) (M : Type*)
    [AddCommGroup M] [Module R M] (a : R)
    (h : IsUnit (algebraMap R (Module.End R M) a)) :
    IsUnit (algebraMap R (Module.End R (LocalizedModule T M)) a) := by
  rw [Module.End.isUnit_iff] at h ⊢
  have he : (LocalizedModule.map T (algebraMap R (Module.End R M) a)).restrictScalars R =
      algebraMap R (Module.End R (LocalizedModule T M)) a := by
    ext x
    induction x using LocalizedModule.induction_on with
    | h m s => simp [LocalizedModule.map_mk, LocalizedModule.smul'_mk]
  rw [← he]
  exact ⟨LocalizedModule.map_injective _ _ h.1, LocalizedModule.map_surjective _ _ h.2⟩

/-- A product of an element generated by the `fᵢ`, `i ∈ s`, and a power of `∏ i ∈ t, fᵢ`
is generated by the `fᵢ`, `i ∈ s ∪ t`. -/
private theorem mul_mem_closure_union (s t : Finset (Fin r)) {a b : R}
    (ha : a ∈ Submonoid.closure (f '' (↑s : Set (Fin r)))) (hb : b ∈ cechSub f t) :
    a * b ∈ Submonoid.closure (f '' (↑(s ∪ t) : Set (Fin r))) :=
  Submonoid.mul_mem _ (closure_mono_of_subset f Finset.subset_union_left ha)
    (cechSub_le_closure f Finset.subset_union_right hb)

/-- Two successive localizations invert the union of the two sets of denominators. -/
theorem localize_isLocalized_union {M L : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup L] [Module R L] (s t : Finset (Fin r))
    (l : M →ₗ[R] L) [IsLocalizedModule (Submonoid.closure (f '' (↑s : Set (Fin r)))) l] :
    IsLocalizedModule (Submonoid.closure (f '' (↑(s ∪ t) : Set (Fin r))))
      ((LocalizedModule.mkLinearMap (cechSub f t) _).comp
        l) where
  map_units x := by
    obtain ⟨x, hx⟩ := x
    induction hx using Submonoid.closure_induction with
    | one => simp
    | mul a b _ _ ha hb => simpa only [map_mul] using ha.mul hb
    | mem a ha =>
      obtain ⟨i, hi, rfl⟩ := ha
      rcases Finset.mem_union.mp hi with hi | hi
      · exact localized_isUnit _ _ _ (IsLocalizedModule.map_units
          (S := Submonoid.closure (f '' (↑s : Set (Fin r)))) l
          ⟨_, Submonoid.subset_closure ⟨i, hi, rfl⟩⟩)
      · exact IsLocalizedModule.map_units (S := Submonoid.closure (f '' (↑t : Set (Fin r))))
          (LocalizedModule.mkLinearMap (cechSub f t) _) ⟨_, Submonoid.subset_closure ⟨i, hi, rfl⟩⟩
  surj x := by
    obtain ⟨⟨y, b⟩, hb⟩ := IsLocalizedModule.surj (cechSub f t)
      (LocalizedModule.mkLinearMap (cechSub f t) _) x
    obtain ⟨⟨m, a⟩, ha⟩ := IsLocalizedModule.surj (Submonoid.closure (f '' (↑s : Set (Fin r)))) l y
    refine ⟨⟨m, ⟨a * b, mul_mem_closure_union f s t a.2 b.2⟩⟩, ?_⟩
    change ((a : R) * b) • x = _
    rw [mul_smul]
    change (a : R) • (b • x) = _
    rw [hb, ← map_smul]
    exact congrArg (LocalizedModule.mkLinearMap (cechSub f t) _) ha
  exists_of_eq h := by
    obtain ⟨b, hb⟩ := IsLocalizedModule.exists_of_eq (S := cechSub f t)
      (f := LocalizedModule.mkLinearMap (cechSub f t) _) h
    obtain ⟨a, ha⟩ := IsLocalizedModule.exists_of_eq
      (S := Submonoid.closure (f '' (↑s : Set (Fin r))))
      (show l (b • _) =
        l (b • _) by
        simpa only [Submonoid.smul_def, map_smul] using hb)
    refine ⟨⟨a * b, mul_mem_closure_union f s t a.2 b.2⟩, ?_⟩
    simpa only [Submonoid.smul_def, mul_smul] using ha

/-- The composite of the localization maps at `s` and then at `t` is a localization at the
submonoid generated by the `fᵢ` with `i ∈ s ∪ t`. -/
theorem iterated_isLocalized (M : Type*) [AddCommGroup M] [Module R M]
    (s t : Finset (Fin r)) :
    IsLocalizedModule (Submonoid.closure (f '' (↑(s ∪ t) : Set (Fin r))))
      ((LocalizedModule.mkLinearMap (cechSub f t) _).comp
        (LocalizedModule.mkLinearMap (cechSub f s) M)) :=
  localize_isLocalized_union f s t (LocalizedModule.mkLinearMap (cechSub f s) M)

/-- The canonical identifications between iterated and simultaneous localization. -/
public noncomputable def localizationComparisons : LocalizationComparisons f where
  iterated M _ _ s t := by
    letI := iterated_isLocalized f M s t
    exact IsLocalizedModule.linearEquiv (Submonoid.closure (f '' (↑(s ∪ t) : Set (Fin r))))
      ((LocalizedModule.mkLinearMap (cechSub f t) _).comp
        (LocalizedModule.mkLinearMap (cechSub f s) M))
      (LocalizedModule.mkLinearMap (cechSub f (s ∪ t)) M)
  iterated_mk M _ _ s t m := by
    let := iterated_isLocalized f M s t
    exact IsLocalizedModule.linearEquiv_apply _ _ _ m

/-- A system of module glueing data. Its laws are the actual compatibility and cocycle diagrams
formed from `alpha` and `alphaIJ`. -/
public structure ModuleGlueingDatum (comparison : LocalizationComparisons f) where
  /-- The `S`-module `M'`. -/
  generic : ModuleCat.{max u v w} S
  /-- The module `Mᵢ` over `R[1 / fᵢ]`. -/
  localPiece : ∀ i, ModuleCat.{max u v w} (Localization.Away (f i))
  /-- The `S`-linear isomorphism `(M')_{fᵢ} ≅ S ⊗[R] Mᵢ`. -/
  alpha : ∀ i,
    LocalizedModule.Away (algebraMap R S (f i)) generic ≃ₗ[S]
      TensorProduct R S (restrictFromAway (R := R) f i (localPiece i))
  /-- The overlap isomorphism `(Mᵢ)_{fⱼ} ≅ (Mⱼ)_{fᵢ}`. -/
  alphaIJ : ∀ i j,
    cechMod f (restrictFromAway (R := R) f i (localPiece i)) {j} ≃ₗ[R]
      cechMod f (restrictFromAway (R := R) f j (localPiece j)) {i}
  /-- For `m : M'`, the images of `m` under `alpha i` and `alpha j`, localized further at `fⱼ`
  and `fᵢ` respectively, correspond under `S ⊗[R] alphaIJ i j`. -/
  alpha_compatibility : ∀ i j (m : generic),
    TensorProduct.map LinearMap.id (alphaIJ i j).toLinearMap
        (TensorProduct.map LinearMap.id
          (LocalizedModule.mkLinearMap (cechSub f {j}) _)
          (alpha i (LocalizedModule.mkLinearMap
            (Submonoid.powers (algebraMap R S (f i))) _ m))) =
      TensorProduct.map LinearMap.id
        (LocalizedModule.mkLinearMap (cechSub f {i}) _)
        (alpha j (LocalizedModule.mkLinearMap
          (Submonoid.powers (algebraMap R S (f j))) _ m))
  /-- The cocycle condition: on the triple overlap, `alphaIJ j k` after `alphaIJ i j` agrees with
  `alphaIJ i k`, all three being identified via `comparison` with maps of localizations of `Mᵢ`,
  `Mⱼ`, `Mₖ` at the product of two of `fᵢ`, `fⱼ`, `fₖ`. -/
  cocycle : ∀ i j k,
    (comparison.iterated _ {j} {i}).toLinearMap.comp
        ((localizedMap f {i} (alphaIJ j k).toLinearMap).comp
          ((comparison.iterated _ {k} {i}).symm.toLinearMap.comp
            ((cechModCongr f
              (show {i} ∪ {k} = {k} ∪ {i} by simp [Finset.union_comm])).toLinearMap.comp
              ((comparison.iterated _ {i} {k}).toLinearMap.comp
                ((localizedMap f {k} (alphaIJ i j).toLinearMap).comp
                  (comparison.iterated _ {j} {k}).symm.toLinearMap))))) =
      (cechModCongr f (show {i} ∪ {j} = {j} ∪ {i} by simp [Finset.union_comm])).toLinearMap.comp
        ((comparison.iterated _ {i} {j}).toLinearMap.comp
          ((localizedMap f {j} (alphaIJ i k).toLinearMap).comp
            ((comparison.iterated _ {k} {j}).symm.toLinearMap.comp
              (cechModCongr f
                (show {j} ∪ {k} = {k} ∪ {j} by simp [Finset.union_comm])).toLinearMap)))

/-- A morphism of module glueing data: maps on all modules compatible with both families of
comparison isomorphisms. -/
public structure ModuleGlueingMap (comparison : LocalizationComparisons f)
    (X Y : ModuleGlueingDatum S f comparison) where
  /-- The `S`-linear map of generic modules. -/
  generic : X.generic ⟶ Y.generic
  /-- The `R[1 / fᵢ]`-linear map of local modules. -/
  localPiece : ∀ i, X.localPiece i ⟶ Y.localPiece i
  /-- The localization of `generic` at `fᵢ` corresponds to `S ⊗[R] localPiece i` under `alpha`. -/
  alpha_compatibility : ∀ i (m : restrictFromTarget (R := R) S X.generic),
    Y.alpha i
        (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S (f i))) _ (generic m)) =
      TensorProduct.map LinearMap.id
        (((ModuleCat.restrictScalars
          (algebraMap R (Localization.Away (f i)))).map (localPiece i)).hom)
        (X.alpha i
          (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S (f i))) _ m))
  /-- The localizations of `localPiece i` at `fⱼ` and of `localPiece j` at `fᵢ` correspond
  under `alphaIJ i j`. -/
  alphaIJ_compatibility : ∀ i j
      (m : restrictFromAway (R := R) f i (X.localPiece i)),
    Y.alphaIJ i j
        (LocalizedModule.mkLinearMap (cechSub f {j}) _ (localPiece i m)) =
      localizedMap f {i}
        (((ModuleCat.restrictScalars
          (algebraMap R (Localization.Away (f j)))).map (localPiece j)).hom)
        (X.alphaIJ i j (LocalizedModule.mkLinearMap (cechSub f {j}) _ m))

/-- The `R`-module of tuples satisfying the generic/local and overlap compatibility equations. -/
public def compatibleSections (comparison : LocalizationComparisons f)
    (X : ModuleGlueingDatum S f comparison) :
    Submodule R (restrictFromTarget (R := R) S X.generic ×
      ∀ i, restrictFromAway (R := R) f i (X.localPiece i)) where
  carrier := {x | (∀ i,
      X.alpha i
          (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S (f i))) _ x.1) =
        (TensorProduct.mk R S _) 1 (x.2 i)) ∧
      ∀ i j, X.alphaIJ i j (LocalizedModule.mkLinearMap (cechSub f {j}) _ (x.2 i)) =
        LocalizedModule.mkLinearMap (cechSub f {i}) _ (x.2 j)}
  zero_mem' := by
    constructor
    · intro i
      change X.alpha i (LocalizedModule.mkLinearMap
          (Submonoid.powers (algebraMap R S (f i))) _ 0) =
        (TensorProduct.mk R S _) 1 0
      simp
    · intro i j
      simp
  add_mem' := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨hxi, hxij⟩ ⟨hyi, hyij⟩
    constructor
    · intro i
      let m : X.generic := x
      let n : X.generic := y
      change X.alpha i (LocalizedModule.mkLinearMap
          (Submonoid.powers (algebraMap R S (f i))) _
            (m + n)) =
        (TensorProduct.mk R S _) 1 (hx i + hy i)
      rw [map_add, map_add, hxi, hyi, map_add]
    · intro i j
      change X.alphaIJ i j (LocalizedModule.mkLinearMap (cechSub f {j}) _ (hx i + hy i)) =
        LocalizedModule.mkLinearMap (cechSub f {i}) _ (hx j + hy j)
      rw [map_add, map_add, hxij, hyij, map_add]
  smul_mem' := by
    rintro a ⟨x, hx⟩ ⟨hxi, hxij⟩
    constructor
    · intro i
      let m : X.generic := x
      change X.alpha i (LocalizedModule.mkLinearMap
          (Submonoid.powers (algebraMap R S (f i))) _
            ((algebraMap R S a) • m)) =
        (TensorProduct.mk R S _) 1 (a • hx i)
      rw [map_smul, map_smul, hxi, map_smul]
      exact IsScalarTower.algebraMap_smul S a _
    · intro i j
      change X.alphaIJ i j (LocalizedModule.mkLinearMap (cechSub f {j}) _ (a • hx i)) =
        LocalizedModule.mkLinearMap (cechSub f {i}) _ (a • hx j)
      rw [map_smul, map_smul, hxij, map_smul]

/-- The localization of `g` sends `m / 1` to `g m / 1`. -/
@[simp] theorem localizedMap_mk {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (s : Finset (Fin r)) (g : M →ₗ[R] N) (m : M) :
    localizedMap f s g (LocalizedModule.mkLinearMap (cechSub f s) M m) =
      LocalizedModule.mkLinearMap (cechSub f s) N (g m) :=
  LocalizedModule.map_mk _ _ _ _

/-- Localization of the identity map is the identity. -/
@[simp] theorem localizedMap_id (M : Type*) [AddCommGroup M] [Module R M]
    (s : Finset (Fin r)) : localizedMap f s (LinearMap.id (M := M)) = LinearMap.id := by
  ext x
  induction x using LocalizedModule.induction_on with
  | h m a => simp [localizedMap]

/-- Localization of a composite is the composite of the localizations. -/
@[simp] theorem localizedMap_comp {M N P : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (s : Finset (Fin r)) (g : M →ₗ[R] N) (h : N →ₗ[R] P) :
    localizedMap f s (h.comp g) = (localizedMap f s h).comp (localizedMap f s g) := by
  ext x
  induction x using LocalizedModule.induction_on with
  | h m a => simp [localizedMap, LocalizedModule.map_mk]

namespace ModuleGlueingMap

variable {S f} {comparison : LocalizationComparisons.{u, max u v w} f}
  {X Y Z : ModuleGlueingDatum.{u, v, w} S f comparison}

/-- Two morphisms of glueing data are equal when their generic and local components are. -/
@[ext] theorem ext {g h : ModuleGlueingMap S f comparison X Y}
    (hg : g.generic = h.generic) (hl : g.localPiece = h.localPiece) : g = h := by
  cases g
  cases h
  cases hg
  cases hl
  rfl

/-- Identity maps on the generic and local modules. -/
noncomputable def id (X : ModuleGlueingDatum S f comparison) :
    ModuleGlueingMap S f comparison X X where
  generic := 𝟙 X.generic
  localPiece i := 𝟙 (X.localPiece i)
  alpha_compatibility i m := by
    simp [LocalizedModule.mkLinearMap]
    rfl
  alphaIJ_compatibility i j m := by
    simp [LocalizedModule.mkLinearMap]
    rfl

/-- Componentwise composition of morphisms of glueing data. -/
noncomputable def comp (g : ModuleGlueingMap S f comparison X Y)
    (h : ModuleGlueingMap S f comparison Y Z) : ModuleGlueingMap S f comparison X Z where
  generic := g.generic ≫ h.generic
  localPiece i := g.localPiece i ≫ h.localPiece i
  alpha_compatibility i m := by
    change Z.alpha i (LocalizedModule.mkLinearMap _ _ (h.generic (g.generic m))) = _
    erw [h.alpha_compatibility, g.alpha_compatibility]
    rw [TensorProduct.map_map]
    rfl
  alphaIJ_compatibility i j m := by
    change Z.alphaIJ i j (LocalizedModule.mkLinearMap _ _ (h.localPiece i (g.localPiece i m))) = _
    erw [h.alphaIJ_compatibility, g.alphaIJ_compatibility]
    change ((localizedMap f {i} _).comp (localizedMap f {i} _)) _ = _
    rw [← localizedMap_comp]
    rfl

end ModuleGlueingMap

/-- The category whose arrows are the compatible componentwise linear maps. -/
@[instance_reducible]
public noncomputable def moduleGlueingCategory
    (comparison : LocalizationComparisons.{u, max u v w} f) :
    Category.{max u v w} (ModuleGlueingDatum.{u, v, w} S f comparison) where
  Hom X Y := ModuleGlueingMap S f comparison X Y
  id := ModuleGlueingMap.id
  comp := ModuleGlueingMap.comp
  id_comp g := by apply ModuleGlueingMap.ext <;> rfl
  comp_id g := by apply ModuleGlueingMap.ext <;> rfl
  assoc g h k := by apply ModuleGlueingMap.ext <;> rfl

/-- Apply a compatible family of maps to a tuple of compatible sections. -/
public noncomputable def compatibleSectionsMap
    {comparison : LocalizationComparisons.{u, max u v w} f}
    {X Y : ModuleGlueingDatum.{u, v, w} S f comparison}
    (g : ModuleGlueingMap S f comparison X Y) :
    compatibleSections S f comparison X →ₗ[R] compatibleSections S f comparison Y where
  toFun x := ⟨⟨g.generic x.1.1, fun i ↦ g.localPiece i (x.1.2 i)⟩, by
    constructor
    · intro i
      rw [g.alpha_compatibility, x.2.1]
      rfl
    · intro i j
      rw [g.alphaIJ_compatibility, x.2.2, localizedMap_mk]
      rfl⟩
  map_add' x y := Subtype.ext (Prod.ext (map_add _ _ _) (funext fun i ↦ map_add _ _ _))
  map_smul' a x := Subtype.ext (Prod.ext
    (((ModuleCat.restrictScalars (algebraMap R S)).map g.generic).hom.map_smul a _)
    (funext fun i ↦ ((ModuleCat.restrictScalars
      (algebraMap R (Localization.Away (f i)))).map (g.localPiece i)).hom.map_smul a _))

/-- The functor of compatible sections, with its componentwise action on arrows. -/
public noncomputable def compatibleSectionsFunctor
    (comparison : LocalizationComparisons.{u, max u v w} f) :
    letI := moduleGlueingCategory S f comparison
    ModuleGlueingDatum.{u, v, w} S f comparison ⥤ ModuleCat.{max u v w} R := by
  letI := moduleGlueingCategory S f comparison
  exact
    { obj X := ModuleCat.of R (compatibleSections S f comparison X)
      map g := ModuleCat.ofHom (compatibleSectionsMap S f g)
      map_id X := rfl
      map_comp g h := rfl }

/-- The local component of a canonical datum. -/
noncomputable def canonicalLocalPiece (M : ModuleCat.{w} R) (i : Fin r) :
    ModuleCat.{max u w} (Localization.Away (f i)) :=
  ModuleCat.of _ (LocalizedModule.Away (f i) M)

/-- Restricting a scalar extension recovers the specified smaller scalar action. -/
noncomputable def restrictModuleOfEquiv (A : Type*) [CommRing A] [Algebra R A]
    (M : Type*) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] :
    (ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A M) ≃ₗ[R] M where
  toFun m := m
  invFun m := m
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a m := by
    change (algebraMap R A a) • (show M from m) = a • (show M from m)
    exact IsScalarTower.algebraMap_smul (M := M) A a m

/-- The restriction of the canonical local component has the usual localized scalar action. -/
noncomputable def canonicalLocalRestriction (M : ModuleCat.{w} R) (i : Fin r) :
    restrictFromAway f i (canonicalLocalPiece f M i) ≃ₗ[R] LocalizedModule.Away (f i) M :=
  restrictModuleOfEquiv (Localization.Away (f i)) (LocalizedModule.Away (f i) M)

/-- The denominator-one map into the canonical local component. -/
noncomputable def canonicalLocalMk (M : ModuleCat.{w} R) (i : Fin r) :
    M →ₗ[R] restrictFromAway f i (canonicalLocalPiece f M i) :=
  (canonicalLocalRestriction f M i).symm.toLinearMap.comp
    (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M)

/-- The map `canonicalLocalMk` is a localization at the powers of `fᵢ`. -/
instance canonicalLocalMk_isLocalized (M : ModuleCat.{w} R) (i : Fin r) :
    IsLocalizedModule (Submonoid.powers (f i)) (canonicalLocalMk f M i) :=
  IsLocalizedModule.of_linearEquiv _ _ _

/-- The map `canonicalLocalMk` is a localization at the submonoid generated by `fᵢ`. -/
instance canonicalLocalMk_isLocalized_closure (M : ModuleCat.{w} R) (i : Fin r) :
    IsLocalizedModule (Submonoid.closure (f '' (↑({i} : Finset (Fin r)) : Set (Fin r))))
      (canonicalLocalMk f M i) := by
  simpa [Submonoid.powers_eq_closure] using canonicalLocalMk_isLocalized f M i

/-- Tensoring on the left preserves a module localization. -/
theorem isLocalized_lTensor {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (T : Submonoid R) (l : M →ₗ[R] N)
    [IsLocalizedModule T l] : IsLocalizedModule T (l.lTensor S) := by
  have h : IsLocalizedModule T (AlgebraTensorModule.rTensor R S l) := inferInstance
  have h' := IsLocalizedModule.of_linearEquiv_right T (AlgebraTensorModule.rTensor R S l)
    (TensorProduct.comm R S M)
  have h'' := IsLocalizedModule.of_linearEquiv T
    ((AlgebraTensorModule.rTensor R S l).comp (TensorProduct.comm R S M).toLinearMap)
    (TensorProduct.comm R N S)
  convert h'' using 1
  ext s m
  rfl

/-- The base change `S ⊗[R] M → S ⊗[R] M_{fᵢ}` of `canonicalLocalMk` is a localization at the
powers of the image of `fᵢ` in `S`. -/
instance canonicalTensor_isLocalized (M : ModuleCat.{w} R) (i : Fin r) :
    IsLocalizedModule (Submonoid.powers (algebraMap R S (f i)))
      (AlgebraTensorModule.lTensor S S (canonicalLocalMk f M i)) := by
  have : IsLocalizedModule (Submonoid.powers (f i))
      ((AlgebraTensorModule.lTensor S S (canonicalLocalMk f M i)).restrictScalars R) :=
    isLocalized_lTensor S _ _
  simpa only [Algebra.algebraMapSubmonoid_powers] using
    IsLocalizedModule.of_restrictScalars (Submonoid.powers (f i))
      (AlgebraTensorModule.lTensor S S (canonicalLocalMk f M i))

/-- The localization comparison for scalar extension of a canonical module. -/
noncomputable def canonicalAlpha (M : ModuleCat.{w} R) (i : Fin r) :
    LocalizedModule.Away (algebraMap R S (f i)) (TensorProduct R S M) ≃ₗ[S]
      TensorProduct R S (restrictFromAway f i (canonicalLocalPiece f M i)) :=
  IsLocalizedModule.iso _ (AlgebraTensorModule.lTensor S S (canonicalLocalMk f M i))

/-- The map `canonicalAlpha` sends `(s ⊗ m) / 1` to `s ⊗ (m / 1)`. -/
@[simp] theorem canonicalAlpha_mk (M : ModuleCat.{w} R) (i : Fin r) (s : S) (m : M) :
    canonicalAlpha S f M i
      (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S (f i))) _ (s ⊗ₜ[R] m)) =
      s ⊗ₜ[R] canonicalLocalMk f M i m :=
  IsLocalizedModule.iso_mk_one _ _ _

/-- Localizing `M_{fᵢ}` further at the `fⱼ` with `j ∈ s` is a localization of `M` at the
submonoid generated by the `fⱼ` with `j ∈ {i} ∪ s`. -/
instance canonicalOverlap_isLocalized (M : ModuleCat.{w} R) (i : Fin r)
    (s : Finset (Fin r)) :
    IsLocalizedModule (Submonoid.closure (f '' (↑({i} ∪ s) : Set (Fin r))))
      ((LocalizedModule.mkLinearMap (cechSub f s) _).comp (canonicalLocalMk f M i)) :=
  localize_isLocalized_union f {i} s (canonicalLocalMk f M i)

/-- The canonical identification on a pairwise overlap. -/
noncomputable def canonicalAlphaIJ (M : ModuleCat.{w} R) (i j : Fin r) :
    cechMod f (restrictFromAway f i (canonicalLocalPiece f M i)) {j} ≃ₗ[R]
      cechMod f (restrictFromAway f j (canonicalLocalPiece f M j)) {i} := by
  letI := localize_isLocalized_union f {i} {j} (canonicalLocalMk f M i)
  haveI : IsLocalizedModule
      (Submonoid.closure (f '' (↑(({i} : Finset (Fin r)) ∪ {j}) : Set (Fin r))))
      ((LocalizedModule.mkLinearMap (cechSub f {i}) _).comp (canonicalLocalMk f M j)) := by
    simpa only [Finset.union_comm] using
      localize_isLocalized_union f {j} {i} (canonicalLocalMk f M j)
  exact IsLocalizedModule.linearEquiv
    (Submonoid.closure (f '' (↑(({i} : Finset (Fin r)) ∪ {j}) : Set (Fin r))))
    ((LocalizedModule.mkLinearMap (cechSub f {j}) _).comp (canonicalLocalMk f M i))
    ((LocalizedModule.mkLinearMap (cechSub f {i}) _).comp (canonicalLocalMk f M j))

/-- The map `canonicalAlphaIJ` sends `m / 1 / 1` in `(M_{fᵢ})_{fⱼ}` to `m / 1 / 1` in
`(M_{fⱼ})_{fᵢ}`. -/
@[simp] theorem canonicalAlphaIJ_mk (M : ModuleCat.{w} R) (i j : Fin r) (m : M) :
    canonicalAlphaIJ f M i j
      (LocalizedModule.mkLinearMap (cechSub f {j}) _ (canonicalLocalMk f M i m)) =
      LocalizedModule.mkLinearMap (cechSub f {i}) _ (canonicalLocalMk f M j m) := by
  have : IsLocalizedModule
      (Submonoid.closure (f '' (↑(({i} : Finset (Fin r)) ∪ {j}) : Set (Fin r))))
      ((LocalizedModule.mkLinearMap (cechSub f {i}) _).comp (canonicalLocalMk f M j)) := by
    simpa only [Finset.union_comm] using canonicalOverlap_isLocalized f M j {i}
  exact IsLocalizedModule.linearEquiv_apply _ _ _ m

/-- Any comparison of iterated localizations sends `m / 1 / 1` to `m / 1`. -/
@[simp] theorem iterated_mk (comparison : LocalizationComparisons f)
    (M : Type w) [AddCommGroup M] [Module R M] (s t : Finset (Fin r)) (m : M) :
    comparison.iterated M s t (LocalizedModule.mkLinearMap (cechSub f t) _
      (LocalizedModule.mkLinearMap (cechSub f s) _ m)) =
      LocalizedModule.mkLinearMap (cechSub f (s ∪ t)) _ m := comparison.iterated_mk _ _ _ _

/-- The inverse of a comparison of iterated localizations sends `m / 1` to `m / 1 / 1`. -/
@[simp] theorem iterated_symm_mk (comparison : LocalizationComparisons f)
    (M : Type w) [AddCommGroup M] [Module R M] (s t : Finset (Fin r)) (m : M) :
    (comparison.iterated M s t).symm (LocalizedModule.mkLinearMap (cechSub f (s ∪ t)) _ m) =
      LocalizedModule.mkLinearMap (cechSub f t) _
        (LocalizedModule.mkLinearMap (cechSub f s) _ m) := by
  rw [LinearEquiv.symm_apply_eq, iterated_mk]

/-- Reindexing along `s = t` sends `m / 1` to `m / 1`. -/
@[simp] theorem cechModCongr_mk (M : Type*) [AddCommGroup M] [Module R M]
    {s t : Finset (Fin r)} (h : s = t) (m : M) :
    cechModCongr f h (LocalizedModule.mkLinearMap (cechSub f s) M m) =
      LocalizedModule.mkLinearMap (cechSub f t) M m := by subst t; rfl

/-- The canonical datum associated to an `R`-module. -/
public noncomputable def canonicalDatum (M : ModuleCat.{max u v w} R) :
    ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f) where
  generic := ModuleCat.of S (TensorProduct R S M)
  localPiece := canonicalLocalPiece f M
  alpha := canonicalAlpha S f M
  alphaIJ := canonicalAlphaIJ f M
  alpha_compatibility i j m := by
    change TensorProduct.map _ _ (TensorProduct.map _ _ (canonicalAlpha S f M i _)) =
      TensorProduct.map _ _ (canonicalAlpha S f M j _)
    induction m using TensorProduct.inductionOn with
    | tmul s m => simp only [canonicalAlpha_mk, TensorProduct.map_tmul,
        LinearMap.id_apply, LinearEquiv.coe_coe, canonicalAlphaIJ_mk]
    | add x y hx hy => simp_all only [map_add]
  cocycle i j k := by
    let := localize_isLocalized_union f {k} ({j} ∪ {i}) (canonicalLocalMk f M k)
    have hu : ∀ a : cechSub f ({j} ∪ {k}),
        IsUnit (algebraMap R
          (Module.End R (cechMod f (restrictFromAway f k (canonicalLocalPiece f M k))
            ({j} ∪ {i}))) a) := fun a ↦
      IsLocalizedModule.map_units
        ((LocalizedModule.mkLinearMap (cechSub f ({j} ∪ {i})) _).comp
          (canonicalLocalMk f M k))
        ⟨a, cechSub_le_closure f (t := {k} ∪ ({j} ∪ {i})) (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_singleton] at *
          tauto) a.2⟩
    apply IsLocalizedModule.ext (cechSub f ({j} ∪ {k}))
      (LocalizedModule.mkLinearMap (cechSub f ({j} ∪ {k})) _) hu
    have hi : ∀ a : Submonoid.powers (f i),
        IsUnit (algebraMap R
          (Module.End R (cechMod f (restrictFromAway f k (canonicalLocalPiece f M k))
            ({j} ∪ {i}))) a) := by
      intro a
      apply IsLocalizedModule.map_units (S := Submonoid.closure
        (f '' (↑(({k} : Finset (Fin r)) ∪ ({j} ∪ {i})) : Set (Fin r))))
        ((LocalizedModule.mkLinearMap (cechSub f ({j} ∪ {i})) _).comp
          (canonicalLocalMk f M k))
        ⟨a, ?_⟩
      apply cechSub_le_closure f (s := {i}) (t := {k} ∪ ({j} ∪ {i})) (by simp)
      simpa only [cechSub, Finset.prod_singleton] using a.2
    apply IsLocalizedModule.ext (Submonoid.powers (f i)) (canonicalLocalMk f M i) hi
    ext m
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, iterated_symm_mk,
      localizedMap_mk, canonicalAlphaIJ_mk, iterated_mk, cechModCongr_mk]

/-- The map of local components induced by a linear map of original modules. -/
noncomputable def canonicalLocalMap {M N : ModuleCat.{w} R} (g : M ⟶ N) (i : Fin r) :
    canonicalLocalPiece f M i ⟶ canonicalLocalPiece f N i :=
  ModuleCat.ofHom (LocalizedModule.map (Submonoid.powers (f i)) g.hom)

/-- The map `canonicalLocalMap` sends `m / 1` to `g m / 1`. -/
@[simp] theorem canonicalLocalMap_mk {M N : ModuleCat.{w} R} (g : M ⟶ N) (i : Fin r) (m : M) :
    canonicalLocalMap f g i (canonicalLocalMk f M i m) = canonicalLocalMk f N i (g m) :=
  LocalizedModule.map_mk _ _ _ _

/-- The compatible family of maps induced by a linear map of modules. -/
public noncomputable def canonicalDatumMap {M N : ModuleCat.{max u v w} R} (g : M ⟶ N) :
    ModuleGlueingMap S f (localizationComparisons f)
      (canonicalDatum S f M) (canonicalDatum S f N) where
  generic := ModuleCat.ofHom (AlgebraTensorModule.lTensor S S g.hom)
  localPiece := canonicalLocalMap f g
  alpha_compatibility i m := by
    dsimp only [canonicalDatum] at m ⊢
    change canonicalAlpha S f N i (LocalizedModule.mkLinearMap _ _
      (AlgebraTensorModule.lTensor S S g.hom m)) =
      TensorProduct.map LinearMap.id
        (((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i)))).map
          (canonicalLocalMap f g i)).hom)
        (canonicalAlpha S f M i (LocalizedModule.mkLinearMap _ (TensorProduct R S M) m))
    induction m using TensorProduct.inductionOn with
    | tmul s m =>
      change canonicalAlpha S f N i (LocalizedModule.mkLinearMap _ _ (s ⊗ₜ[R] g m)) = _
      rw [canonicalAlpha_mk]
      change _ = TensorProduct.map _ _ (canonicalAlpha S f M i _)
      rw [canonicalAlpha_mk, TensorProduct.map_tmul]
      exact congrArg (TensorProduct.mk R S _ s) (canonicalLocalMap_mk f g i m).symm
    | add x y hx hy => simp_all only [map_add]
  alphaIJ_compatibility i j m := by
    let h : restrictFromAway f i (canonicalLocalPiece f M i) →ₗ[R]
        restrictFromAway f i (canonicalLocalPiece f N i) :=
      ((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i)))).map
        (canonicalLocalMap f g i)).hom
    let h' : restrictFromAway f j (canonicalLocalPiece f M j) →ₗ[R]
        restrictFromAway f j (canonicalLocalPiece f N j) :=
      ((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f j)))).map
        (canonicalLocalMap f g j)).hom
    suffices (canonicalAlphaIJ f N i j).toLinearMap.comp
        ((LocalizedModule.mkLinearMap (cechSub f {j}) _).comp h) =
        (localizedMap f {i} h').comp ((canonicalAlphaIJ f M i j).toLinearMap.comp
          (LocalizedModule.mkLinearMap (cechSub f {j}) _)) from
      DFunLike.congr_fun this m
    apply IsLocalizedModule.ext (Submonoid.powers (f i)) (canonicalLocalMk f M i)
      (fun a ↦ IsLocalizedModule.map_units (S := cechSub f {i})
        (LocalizedModule.mkLinearMap (cechSub f {i}) _)
        ⟨a, by simpa only [cechSub, Finset.prod_singleton] using a.2⟩)
    ext m
    change canonicalAlphaIJ f N i j (LocalizedModule.mkLinearMap _ _
      (canonicalLocalMap f g i (canonicalLocalMk f M i m))) = _
    rw [canonicalLocalMap_mk, canonicalAlphaIJ_mk]
    change _ = localizedMap f {i} h'
      (canonicalAlphaIJ f M i j (LocalizedModule.mkLinearMap _ _ (canonicalLocalMk f M i m)))
    rw [canonicalAlphaIJ_mk, localizedMap_mk]
    exact congrArg (LocalizedModule.mkLinearMap (cechSub f {i}) _)
      (canonicalLocalMap_mk f g j m).symm

/-- The canonical glueing functor. -/
public noncomputable def canonicalFunctor :
    letI := moduleGlueingCategory S f (localizationComparisons f)
    ModuleCat.{max u v w} R ⥤ ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f) := by
  letI := moduleGlueingCategory S f (localizationComparisons f)
  exact
    { obj := canonicalDatum S f
      map := canonicalDatumMap S f
      map_id M := by
        apply ModuleGlueingMap.ext
        · apply ModuleCat.hom_ext
          change AlgebraTensorModule.lTensor S S (LinearMap.id (M := M)) = LinearMap.id
          exact AlgebraTensorModule.lTensor_id
        · funext i
          apply ModuleCat.hom_ext
          exact LocalizedModule.map_id _
      map_comp g h := by
        apply ModuleGlueingMap.ext
        · apply ModuleCat.hom_ext
          change AlgebraTensorModule.lTensor S S (h.hom.comp g.hom) =
            (AlgebraTensorModule.lTensor S S h.hom).comp (AlgebraTensorModule.lTensor S S g.hom)
          exact AlgebraTensorModule.lTensor_comp _ _
        · funext i
          ext x
          induction x using LocalizedModule.induction_on with
          | h m a =>
            change LocalizedModule.map _ (h.hom.comp g.hom) (LocalizedModule.mk m a) =
              LocalizedModule.map _ h.hom (LocalizedModule.map _ g.hom (LocalizedModule.mk m a))
            simp only [LocalizedModule.map_mk, LinearMap.comp_apply] }

/-- The canonical compatible tuple attached to an element of a module. -/
public noncomputable def canonicalToCompatibleSections (M : ModuleCat.{max u v w} R) :
    M →ₗ[R] compatibleSections S f (localizationComparisons f) (canonicalDatum S f M) where
  toFun m := ⟨⟨1 ⊗ₜ[R] m, fun i ↦ canonicalLocalMk f M i m⟩, by
    constructor
    · intro i
      exact canonicalAlpha_mk S f M i 1 m
    · intro i j
      exact canonicalAlphaIJ_mk f M i j m⟩
  map_add' x y := by
    apply Subtype.ext
    exact Prod.ext (TensorProduct.tmul_add _ _ _) (funext fun i ↦ map_add _ _ _)
  map_smul' a x := by
    apply Subtype.ext
    apply Prod.ext
    · change (1 : S) ⊗ₜ[R] (a • x) = (algebraMap R S a) • ((1 : S) ⊗ₜ[R] x)
      rw [TensorProduct.tmul_smul, ← IsScalarTower.algebraMap_smul S a]
    · exact funext fun i ↦ (canonicalLocalMk f M i).map_smul a x

/-- The natural map from a module to the sections of its canonical datum. -/
public noncomputable def canonicalSectionsUnit :
    letI := moduleGlueingCategory S f (localizationComparisons f)
    𝟭 (ModuleCat.{max u v w} R) ⟶
      canonicalFunctor S f ⋙ compatibleSectionsFunctor S f (localizationComparisons f) := by
  letI := moduleGlueingCategory S f (localizationComparisons f)
  exact
    { app M := ModuleCat.ofHom (canonicalToCompatibleSections S f M)
      naturality {M N} g := by
        ext m
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · exact funext fun i ↦ (canonicalLocalMap_mk f g i m).symm }

end FormalGlueing

end
