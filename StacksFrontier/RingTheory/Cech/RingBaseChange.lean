module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import StacksFrontier.RingTheory.Cech.BaseChange
public import StacksFrontier.RingTheory.Cech.Shrink
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Change of rings for the extended alternating Čech complex

Let `φ : A → B` be a homomorphism of commutative rings, let `f₁, …, f_r ∈ A` and write
`g_i = φ(f_i)`.  The family `g₁, …, g_r` generates the extension `I B` of the ideal
`I = (f₁, …, f_r) ⊆ A`, so the extended alternating Čech complexes
$$ C^\bullet(f_1, \ldots, f_r; A), \qquad C^\bullet(g_1, \ldots, g_r; B) $$
are the Čech models of `RΓ_{V(I)}(A)` and of `RΓ_{V(IB)}(B)`.  This file constructs the map
between them.

In each degree the comparison is built one localization at a time: `φ` carries
`f_{i_0} \cdots f_{i_{p-1}}` to `g_{i_0} \cdots g_{i_{p-1}}`, which is invertible in
`B_{g_{i_0} \cdots g_{i_{p-1}}}`, so there is exactly one `A`-linear map
`A_{f_{i_0} \cdots f_{i_{p-1}}} → B_{g_{i_0} \cdots g_{i_{p-1}}}` extending `φ`.  Uniqueness is
what makes the construction strictly functorial: a composite of two such maps extends the
composite ring map, hence *is* the map attached to it, and the transition maps of the Čech
complexes are compatible for the same reason.

## Main definitions

* `Stacks.CechRingBaseChange.modMap` — the `A`-linear map `A_{f_s} → B_{g_s}` extending `φ`.
* `Stacks.CechRingBaseChange.termMap` — its degreewise assembly `C^p(f; A) → C^p(g; B)`.
* `Stacks.CechRingBaseChange.complexMap` — **the map of complexes of `A`-modules**
  `C^•(f₁, …, f_r; A) → C^•(g₁, …, g_r; B)`.  This is item (3) of tag 099D for the Čech model;
  its item (1), the complex, is `Cech.cechComplex`, and its item (2), the augmentation onto the
  ring, is `Stacks.LocalCohomology.extendedCechAugmentation`.

## Main results

* `Stacks.CechRingBaseChange.complexMap_comp` — the maps compose on the nose: for
  `A → B → C` the composite of the maps for `φ` and for `ψ` is the map for `ψ ∘ φ`.
* `Stacks.CechRingBaseChange.cechModEmptyEquiv_modMap`,
  `Stacks.CechRingBaseChange.termMap_zero` — in degree zero the map is `φ`, under the canonical
  identification of the degree-zero term with the ring; this is the commutativity of the square
  formed by the two augmentations and `φ`.

## Implementation notes

The target is a complex of `A`-modules, obtained from the complex of `B`-modules by restriction
of scalars along `φ`.  It is spelled with `ModuleCat.restrictScalars`, so the `A`-module
structures appearing here are the ones that functor puts on the terms — the convention of
`CochainComplex.restrictScalars` and of the change-of-rings functors used elsewhere in the
library — rather than a locally pinned copy of them.

Both rings are taken in a single universe.  Restriction of scalars acts on module categories at
a fixed module universe, and the module here is the ring itself, so the two module universes are
the two ring universes.

Tag 099D asserts more than what is proved here.  There the complex is attached to the pair
`(A, I)` of a ring and a finitely generated ideal, not to a chosen finite generating family of
`I`, and the map of its item (3) is given for *every* ring map `A → B`; the map built here is
attached to a ring map together with the generating family it transports.  So what this file
settles is tag 099D for pairs carrying a chosen finite generating family, with the Čech complex
as the complex: its items (1) and (2), the complex and its augmentation onto the ring, are
`Cech.cechComplex` and `Stacks.LocalCohomology.extendedCechAugmentation`, already in the
library, and item (3) and conditions (a) and (b) are what is added here.  Condition (c), the
derived one, is
`Stacks.CechRingBaseChange.isIso_derivedBaseChange_extendedComplexMap` of
`StacksFrontier/RingTheory/Cech/RingBaseChangeDerived.lean`: the Čech complex of the ring is K-flat
(`Cech.kFlat_extend_cechComplex`), so the derived base-change map of
`Stacks.LocalCohomology.derivedBaseChange` is computed by the extension-of-scalars transpose of
`complexMap` (`Stacks.LocalCohomology.isIso_derivedBaseChange_of_kFlat`), and that transpose is
degreewise the base-change isomorphism `B ⊗_A C^p(f; A) ≅ C^p(g; B)`.  Condition (d) holds for the
Čech model, by `Stacks.LocalCohomology.exists_extendedCechObject_iso_of_span_eq`.  The construction
for a pair `(A, I)` — the content of 099D, whose proof in the source strictifies a functorial
injective resolution on a site with the chaotic topology — is not proved anywhere in this library.

## References

* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
* [Stacks Project, Tag 0G6I](https://stacks.math.columbia.edu/tag/0G6I)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Stacks.CechRingBaseChange

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] {r : ℕ}

/-! ### The image family -/

/-- The image under a ring map of a finite family of elements. -/
abbrev mapFamily (φ : A →+* B) (f : Fin r → A) : Fin r → B := fun i => φ (f i)

/-- The product of an image family is the image of the product, so `φ` carries the localizing
submonoid of `s` for `f` into the one for the image family. -/
theorem mem_cechSub_mapFamily (φ : A →+* B) (f : Fin r → A) {s : Finset (Fin r)} {x : A}
    (hx : x ∈ Cech.cechSub f s) : φ x ∈ Cech.cechSub (mapFamily φ f) s := by
  obtain ⟨n, hn⟩ := hx
  exact ⟨n, by rw [← hn, map_pow, map_prod]⟩

/-! ### The target modules -/

/-- The localization `B_{g_{i_0} \cdots g_{i_{p-1}}}` of `B` at the image family, read as an
`A`-module along `φ`. -/
abbrev restrictedMod (φ : A →+* B) (f : Fin r → A) (s : Finset (Fin r)) : ModuleCat.{u} A :=
  (ModuleCat.restrictScalars φ).obj (ModuleCat.of B (Cech.cechMod (mapFamily φ f) B s))

/-- The degree-`p` term `C^p(g₁, …, g_r; B)` of the Čech complex of the image family, read as an
`A`-module along `φ`. -/
abbrev restrictedTerm (φ : A →+* B) (f : Fin r → A) (p : ℕ) : ModuleCat.{u} A :=
  (ModuleCat.restrictScalars φ).obj (ModuleCat.of B (Cech.cechTerm (mapFamily φ f) B p))

/-- A `B`-linear map, read as an `A`-linear map along `φ`. -/
def restrictHom (φ : A →+* B) {X Y : ModuleCat.{u} B} (l : X ⟶ Y) :
    ↑((ModuleCat.restrictScalars φ).obj X) →ₗ[A] ↑((ModuleCat.restrictScalars φ).obj Y) :=
  ((ModuleCat.restrictScalars φ).map l).hom

/-- `restrictHom φ l` acts on elements as `l` does. -/
@[simp]
theorem restrictHom_apply (φ : A →+* B) {X Y : ModuleCat.{u} B} (l : X ⟶ Y) (x : X) :
    restrictHom φ l x = l.hom x :=
  rfl

/-- Every element of `Cech.cechSub f s` acts invertibly on `B_{g_{j_0} \cdots g_{j_{q-1}}}` for
`s ⊆ t`: its image under `φ` is a power of `g_{i_0} \cdots g_{i_{p-1}}`, and all of those have
been inverted there. -/
theorem isUnit_algebraMap_restrictedMod (φ : A →+* B) (f : Fin r → A) {s t : Finset (Fin r)}
    (h : s ⊆ t) (x : Cech.cechSub f s) :
    IsUnit (algebraMap A (Module.End A ↑(restrictedMod φ f t)) (x : A)) := by
  have hB := Cech.isUnit_algebraMap (mapFamily φ f) B h
    (LocalizedModule.mkLinearMap (Cech.cechSub (mapFamily φ f) t) B)
    (⟨φ (x : A), mem_cechSub_mapFamily φ f x.2⟩ : Cech.cechSub (mapFamily φ f) s)
  rw [Module.End.isUnit_iff] at hB ⊢
  exact hB

/-! ### The map on a single localization -/

/-- A ring map `φ : A → B`, as an `A`-linear map from `A` to `B` restricted along `φ`. -/
def ofRingHom (φ : A →+* B) :
    A →ₗ[A] ↑((ModuleCat.restrictScalars φ).obj (ModuleCat.of B B)) where
  toFun := φ
  map_add' := φ.map_add
  map_smul' a x := φ.map_mul a x

/-- The composite `A → B → B_{g_{i_0} \cdots g_{i_{p-1}}}`, as an `A`-linear map. -/
def seed (φ : A →+* B) (f : Fin r → A) (s : Finset (Fin r)) :
    A →ₗ[A] ↑(restrictedMod φ f s) :=
  (restrictHom φ (ModuleCat.ofHom
    (LocalizedModule.mkLinearMap (Cech.cechSub (mapFamily φ f) s) B))).comp (ofRingHom φ)

/-- `ofRingHom φ` sends `a` to `φ a`. -/
@[simp]
theorem ofRingHom_apply (φ : A →+* B) (a : A) : ofRingHom φ a = φ a :=
  rfl

/-- `seed φ f s` sends `a` to the class of `φ a` in `B_{g_{i_0} \cdots g_{i_{p-1}}}`. -/
@[simp]
theorem seed_apply (φ : A →+* B) (f : Fin r → A) (s : Finset (Fin r)) (a : A) :
    seed φ f s a =
      LocalizedModule.mkLinearMap (Cech.cechSub (mapFamily φ f) s) B (φ a) :=
  rfl

/-- **Change of rings on a single localization.** The unique `A`-linear map
`A_{f_{i_0} \cdots f_{i_{p-1}}} → B_{g_{i_0} \cdots g_{i_{p-1}}}` extending `φ`. -/
def modMap (φ : A →+* B) (f : Fin r → A) (s : Finset (Fin r)) :
    Cech.cechMod f A s →ₗ[A] ↑(restrictedMod φ f s) :=
  IsLocalizedModule.lift (Cech.cechSub f s) (LocalizedModule.mkLinearMap (Cech.cechSub f s) A)
    (seed φ f s) (isUnit_algebraMap_restrictedMod φ f (le_refl s))

/-- `modMap φ f s` sends the class of `a` in `A_{f_{i_0} \cdots f_{i_{p-1}}}` to the class of `φ a`
in `B_{g_{i_0} \cdots g_{i_{p-1}}}`. -/
@[simp]
theorem modMap_mkLinearMap (φ : A →+* B) (f : Fin r → A) (s : Finset (Fin r)) (a : A) :
    modMap φ f s (LocalizedModule.mkLinearMap (Cech.cechSub f s) A a) =
      LocalizedModule.mkLinearMap (Cech.cechSub (mapFamily φ f) s) B (φ a) :=
  LinearMap.congr_fun (IsLocalizedModule.lift_comp (Cech.cechSub f s)
    (LocalizedModule.mkLinearMap (Cech.cechSub f s) A) (seed φ f s)
    (isUnit_algebraMap_restrictedMod φ f (le_refl s))) a

/-- Two `A`-linear maps out of `A_{f_s}` into a module on which `cechSub f s` acts invertibly are
equal when they agree on the image of `A`. -/
private theorem cechMod_linearMap_ext (f : Fin r → A) (s : Finset (Fin r)) {M : Type*}
    [AddCommGroup M] [Module A M]
    (hM : ∀ y : Cech.cechSub f s, IsUnit (algebraMap A (Module.End A M) (y : A)))
    {g h : Cech.cechMod f A s →ₗ[A] M}
    (H : ∀ a, g (LocalizedModule.mkLinearMap (Cech.cechSub f s) A a) =
      h (LocalizedModule.mkLinearMap (Cech.cechSub f s) A a)) : g = h :=
  IsLocalizedModule.ext (Cech.cechSub f s) (LocalizedModule.mkLinearMap (Cech.cechSub f s) A) hM
    (LinearMap.ext H)

/-- Change of rings is compatible with the transition maps of the Čech complexes: both composites
are `A`-linear maps out of a localization extending `φ`, and such a map is unique. -/
@[ega "0 1.5.6" "special case"]
theorem modMap_cechι (φ : A →+* B) (f : Fin r → A) {s t : Finset (Fin r)} (h : s ⊆ t)
    (x : Cech.cechMod f A s) :
    modMap φ f t (Cech.cechι f A h x) =
      Cech.cechι (mapFamily φ f) B h (modMap φ f s x) := by
  have key : (modMap φ f t).comp (Cech.cechι f A h) =
      (restrictHom φ (ModuleCat.ofHom (Cech.cechι (mapFamily φ f) B h))).comp
        (modMap φ f s) := by
    refine cechMod_linearMap_ext f s (isUnit_algebraMap_restrictedMod φ f h) fun a => ?_
    change modMap φ f t (Cech.cechι f A h
        (LocalizedModule.mkLinearMap (Cech.cechSub f s) A a)) =
      Cech.cechι (mapFamily φ f) B h
        (modMap φ f s (LocalizedModule.mkLinearMap (Cech.cechSub f s) A a))
    rw [Cech.cechι_mk, modMap_mkLinearMap, modMap_mkLinearMap, Cech.cechι_mk]
  exact LinearMap.congr_fun key x

/-- **Change of rings composes on the nose.** For `A → B → C` the composite of the maps on a
single localization is the map attached to the composite ring map. -/
theorem modMap_modMap (φ : A →+* B) (ψ : B →+* C) (f : Fin r → A) (s : Finset (Fin r))
    (x : Cech.cechMod f A s) :
    modMap ψ (mapFamily φ f) s (modMap φ f s x) = modMap (ψ.comp φ) f s x := by
  have key : (restrictHom φ (ModuleCat.ofHom (modMap ψ (mapFamily φ f) s))).comp
      (modMap φ f s) = modMap (ψ.comp φ) f s := by
    refine cechMod_linearMap_ext f s
      (isUnit_algebraMap_restrictedMod (ψ.comp φ) f (le_refl s)) fun a => ?_
    change modMap ψ (mapFamily φ f) s
        (modMap φ f s (LocalizedModule.mkLinearMap (Cech.cechSub f s) A a)) =
      modMap (ψ.comp φ) f s (LocalizedModule.mkLinearMap (Cech.cechSub f s) A a)
    rw [modMap_mkLinearMap, modMap_mkLinearMap, modMap_mkLinearMap]
    rfl
  exact LinearMap.congr_fun key x

/-- **The augmentation square of tag 099D, condition (a).** In degree zero the change-of-rings
map is `φ` itself: the degree-zero localization inverts nothing, and the identification of it
with the ring carries the map onto `φ`.  The augmentations of the two Čech complexes are their
degree-zero identifications with the rings, so this is the commutativity of the square they form
with `φ`. -/
@[stacks 099D "condition (a) for a pair with a chosen finite generating family"]
theorem cechModEmptyEquiv_modMap (φ : A →+* B) (f : Fin r → A)
    (x : Cech.cechMod f A (∅ : Finset (Fin r))) :
    Stacks.CechBaseChange.cechModEmptyEquiv (mapFamily φ f) B (modMap φ f ∅ x) =
      φ (Stacks.CechBaseChange.cechModEmptyEquiv f A x) := by
  have hunit : ∀ y : Cech.cechSub f (∅ : Finset (Fin r)),
      IsUnit (algebraMap A
        (Module.End A ↑((ModuleCat.restrictScalars φ).obj (ModuleCat.of B B))) (y : A)) := by
    intro y
    have hmem : (y : A) ∈ (⊥ : Submonoid A) := by
      rw [← Stacks.CechBaseChange.cechSub_empty f]
      exact y.2
    rw [Submonoid.mem_bot.mp hmem, map_one]
    exact isUnit_one
  have key : (restrictHom φ (ModuleCat.ofHom
        (Stacks.CechBaseChange.cechModEmptyEquiv (mapFamily φ f) B).toLinearMap)).comp
        (modMap φ f ∅) =
      (ofRingHom φ).comp (Stacks.CechBaseChange.cechModEmptyEquiv f A).toLinearMap := by
    refine cechMod_linearMap_ext f ∅ hunit fun a => ?_
    change Stacks.CechBaseChange.cechModEmptyEquiv (mapFamily φ f) B
        (modMap φ f ∅ (LocalizedModule.mkLinearMap
          (Cech.cechSub f (∅ : Finset (Fin r))) A a)) =
      φ (Stacks.CechBaseChange.cechModEmptyEquiv f A
        (LocalizedModule.mkLinearMap (Cech.cechSub f (∅ : Finset (Fin r))) A a))
    rw [modMap_mkLinearMap, Stacks.CechBaseChange.cechModEmptyEquiv_mk,
      Stacks.CechBaseChange.cechModEmptyEquiv_mk]
  exact LinearMap.congr_fun key x

/-! ### The map on the terms of the complex -/

/-- **Change of rings on the degree-`p` term** of the extended alternating Čech complex. -/
def termMap (φ : A →+* B) (f : Fin r → A) (p : ℕ) :
    Cech.cechTerm f A p →ₗ[A] ↑(restrictedTerm φ f p) :=
  DirectSum.toModule A _ _ fun s =>
    (restrictHom φ (ModuleCat.ofHom (DirectSum.lof B {t : Finset (Fin r) // t.card = p}
      (fun t => Cech.cechMod (mapFamily φ f) B t.1) s))).comp (modMap φ f s.1)

/-- On the summand indexed by `s`, `termMap φ f p` is `modMap φ f s` followed by the inclusion of
the summand indexed by `s`. -/
theorem termMap_lof (φ : A →+* B) (f : Fin r → A) (p : ℕ)
    (s : {s : Finset (Fin r) // s.card = p}) (x : Cech.cechMod f A s.1) :
    termMap φ f p (DirectSum.lof A {t : Finset (Fin r) // t.card = p}
        (fun t => Cech.cechMod f A t.1) s x) =
      DirectSum.lof B {t : Finset (Fin r) // t.card = p}
        (fun t => Cech.cechMod (mapFamily φ f) B t.1) s (modMap φ f s.1 x) := by
  rw [termMap, DirectSum.toModule_lof]
  rfl

/-- **Condition (a) on the degree-zero term of the complex.**  The empty set is the only index
of cardinality zero, so the degree-zero term of the Čech complex is the summand it indexes, and
there the change-of-rings map is `φ`. -/
@[stacks 099D "condition (a) for a pair with a chosen finite generating family"]
theorem termMap_zero (φ : A →+* B) (f : Fin r → A) (a : A) :
    termMap φ f 0 (DirectSum.lof A {t : Finset (Fin r) // t.card = 0}
        (fun t => Cech.cechMod f A t.1) ⟨∅, Finset.card_empty⟩
        (LocalizedModule.mkLinearMap (Cech.cechSub f (∅ : Finset (Fin r))) A a)) =
      DirectSum.lof B {t : Finset (Fin r) // t.card = 0}
        (fun t => Cech.cechMod (mapFamily φ f) B t.1) ⟨∅, Finset.card_empty⟩
        (LocalizedModule.mkLinearMap
          (Cech.cechSub (mapFamily φ f) (∅ : Finset (Fin r))) B (φ a)) := by
  rw [termMap_lof, modMap_mkLinearMap]

/-- Change of rings commutes with the Čech differentials: on the summand indexed by `s` both
sides are the alternating sum, over the indices outside `s`, of the transition map into the
summand indexed by `insert i s`. -/
theorem termMap_comp_cechD (φ : A →+* B) (f : Fin r → A) (p : ℕ) :
    (termMap φ f (p + 1)).comp (Cech.cechD f A p) =
      (restrictHom φ (ModuleCat.ofHom (Cech.cechD (mapFamily φ f) B p))).comp
        (termMap φ f p) := by
  refine DirectSum.linearMap_ext A fun s => LinearMap.ext fun x => ?_
  change termMap φ f (p + 1) (Cech.cechD f A p (DirectSum.lof A _ _ s x)) =
    Cech.cechD (mapFamily φ f) B p (termMap φ f p (DirectSum.lof A _ _ s x))
  have hrhs := Cech.cechD_lof (mapFamily φ f) B p s (modMap φ f s.1 x)
  rw [Cech.cechD_lof, map_sum, termMap_lof, hrhs]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, termMap_lof, modMap_cechι]
  rfl

/-! ### The map of complexes -/

/-- **Change of rings for the extended alternating Čech complex, tag 099D items (1)–(3) for a
pair with a chosen finite generating family.** The complex is `C^•(f₁, …, f_r; A)`, the
augmentation onto `A` is its degree-zero projection, and this is the map of complexes of
`A`-modules onto `C^•(g₁, …, g_r; B)` for `g_i = φ(f_i)`. -/
@[stacks 099D "item (3) for a pair with a chosen finite generating family"]
def complexMap (φ : A →+* B) (f : Fin r → A) :
    Cech.cechComplex f A ⟶
      ((ModuleCat.restrictScalars φ).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (Cech.cechComplex (mapFamily φ f) B) where
  f p := ConcreteCategory.ofHom (C := ModuleCat.{u} A) (termMap φ f p)
  comm' p q hpq := by
    obtain rfl : p + 1 = q := hpq
    rw [Cech.cechComplex_d, Functor.mapHomologicalComplex_obj_d, Cech.cechComplex_d]
    exact ConcreteCategory.ext (termMap_comp_cechD φ f p).symm

/-- In degree `p`, `complexMap φ f` is `termMap φ f p`. -/
@[simp]
theorem complexMap_f_hom (φ : A →+* B) (f : Fin r → A) (p : ℕ) :
    ((complexMap φ f).f p).hom = termMap φ f p :=
  rfl

/-- Change of rings on the terms composes on the nose. -/
theorem termMap_comp_termMap (φ : A →+* B) (ψ : B →+* C) (f : Fin r → A) (p : ℕ) :
    (restrictHom φ (ModuleCat.ofHom (termMap ψ (mapFamily φ f) p))).comp (termMap φ f p) =
      termMap (ψ.comp φ) f p := by
  refine DirectSum.linearMap_ext A fun s => LinearMap.ext fun x => ?_
  have hmid := termMap_lof ψ (mapFamily φ f) p s (modMap φ f s.1 x)
  change termMap ψ (mapFamily φ f) p (termMap φ f p (DirectSum.lof A _ _ s x)) =
    termMap (ψ.comp φ) f p (DirectSum.lof A _ _ s x)
  rw [termMap_lof, hmid, termMap_lof, modMap_modMap]
  rfl

/-- **Tag 099D, condition (b).** For `A → B → C` the composite of the change-of-rings maps for
`φ : A → B` and `ψ : B → C` is the change-of-rings map for `ψ ∘ φ`. -/
@[stacks 099D "condition (b) for a pair with a chosen finite generating family"]
theorem complexMap_comp (φ : A →+* B) (ψ : B →+* C) (f : Fin r → A) :
    complexMap φ f ≫
        ((ModuleCat.restrictScalars φ).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (complexMap ψ (mapFamily φ f)) =
      complexMap (ψ.comp φ) f := by
  refine HomologicalComplex.hom_ext _ _ fun p => ConcreteCategory.ext ?_
  exact termMap_comp_termMap φ ψ f p

end Stacks.CechRingBaseChange

end
