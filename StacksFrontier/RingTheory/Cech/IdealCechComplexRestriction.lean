module

public import StacksFrontier.RingTheory.Cech.Reindex
public import StacksFrontier.RingTheory.LocalCohomology.CechGeneratorIndependence
public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.Augmentation
public import StacksFrontier.Algebra.Homology.Embedding.UpNatZero

/-!
# The extended alternating Čech complex is attached to the ideal, canonically

Let `R` be a commutative ring, let `M` be an `R`-module and let `f₁, …, f_r` and `g₁, …, g_s` be
two finite families of elements of `R` spanning the same ideal `I`. The extended alternating Čech
complexes
$$ M \to \bigoplus_i M_{f_i} \to \cdots \to M_{f_1 \cdots f_r}, \qquad
   M \to \bigoplus_j M_{g_j} \to \cdots \to M_{g_1 \cdots g_s} $$
are isomorphic in `D(R)` over `M`.  That much is
`Stacks.LocalCohomology.exists_extendedCechObject_iso_of_span_eq`, which produces the
isomorphism from the uniqueness of a coreflection and therefore only as an existential.  This
file replaces the existential by a **named morphism** and proves the two properties that make it
usable as a comparison system, and it identifies that morphism, when one family is an ordered
subfamily of the other, with the restriction map of complexes `Cech.cechRestrict`.

The universal property of the augmentation,
`Stacks.LocalCohomology.bijective_comp_extendedCechAugmentationHom`, says that composing with the
augmentation identifies the morphisms into the Čech object from an object with `I`-power-torsion
cohomology with the morphisms into `M`.  Since the Čech object of a family spanning `I` is such an
object (`Stacks.LocalCohomology.derivedPowerTorsionProperty_extendedCechObject`), there is exactly
one morphism over `M` between the Čech objects of two families spanning `I`.  Naming it makes the
whole comparison system canonical: uniqueness forces it to be the identity on a single family and
to compose, so the Čech objects of the families spanning a fixed finitely generated ideal form a
transitive system of isomorphisms over `M`, with no coherence left to check.

## Main definitions

* `Stacks.IdealCechComplex.canonicalHom` — **the** morphism over `M` between the Čech objects of
  two families spanning the same ideal.
* `Stacks.IdealCechComplex.canonicalIso` — it is an isomorphism.
* `Stacks.IdealCechComplex.restrictObjHom` — the restriction map of
  `Cech.cechRestrict f M g e he` read in `D(R)`, for `f` an ordered subfamily of `g`.

## Main results

* `Stacks.IdealCechComplex.existsUnique_hom_over_augmentation` — there is exactly one morphism
  over `M` between the two Čech objects.
* `Stacks.IdealCechComplex.eq_canonicalHom` — **uniqueness**: every morphism over `M` between the
  two Čech objects is the canonical one.
* `Stacks.IdealCechComplex.canonicalHom_self`,
  `Stacks.IdealCechComplex.canonicalHom_comp` — **coherence**: the canonical comparisons are the
  identity on a single family and compose.
* `Stacks.IdealCechComplex.extendMap_cechRestrict_comp_augmentation` — restriction to a subfamily
  is compatible with the augmentations onto `M`, for every module `M`.
* `Stacks.IdealCechComplex.isIso_restrictObjHom_of_span_eq` — **restriction to a subfamily
  spanning the same ideal is a quasi-isomorphism.** This is exactly what the implementation notes
  of `StacksFrontier/RingTheory/LocalCohomology/CechGeneratorIndependence.lean` record as missing:
  "at the level of complexes there is a canonical candidate when one family is an ordered
  subfamily of the other, namely `Cech.cechRestrict`; it is not shown here to be a
  quasi-isomorphism".
* `Stacks.IdealCechComplex.restrictObjHom_comp_canonicalHom` — for two arbitrary families
  spanning the same ideal, the canonical comparison is the **explicit zig-zag** of maps of
  complexes through the concatenated family `f₁, …, f_r, g₁, …, g_s`, whose two restrictions are
  quasi-isomorphisms by `isIso_restrictObjHom_castAdd` and `isIso_restrictObjHom_natAdd`.

## Implementation notes

No `@[stacks]` attribute is attached, and the reason is a genuine gap rather than bookkeeping.
The relevant tag is [Stacks, Tag 099D], which asserts the existence of a complex `K(A, I)`
attached to a pair of a ring and a finitely generated ideal, *strictly* functorial in ring maps,
identified in `D(A)` with the extended Čech complex of any finite generating family of `I`.  The
interface for that datum is `Stacks.LocalCohomology.FunctorialCechData` in
`StacksFrontier/RingTheory/DerivedCompletion/FunctorialCechComplex.lean`, and no term of it is
constructed anywhere in the library.  What is proved here is strictly weaker in two ways: the
comparison lives in `D(R)` rather than between complexes, and there is no statement relating it
to change of rings.  It is, however, exactly the "independence of the chosen finite generating
set" that [Stacks, Tag 099E] quotes from 099D — except that 099E needs that independence as an
*equality of presheaf complexes* in order to sheafify and glue, which a comparison in `D(R)`
cannot supply.

The augmentation compatibility `extendMap_cechRestrict_comp_augmentation` generalizes
`Stacks.LocalCohomology.cechRestrict_augmentation` of
`StacksFrontier/RingTheory/LocalCohomology/DerivationAction.lean`, which states the same square for
the module `M = A` only; the generality is free, because every lemma its proof uses is stated for
an arbitrary module.

## References

* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
* [Stacks Project, Tag 099E](https://stacks.math.columbia.edu/tag/099E)
* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
* [Stacks Project, Tag 0G6K](https://stacks.math.columbia.edu/tag/0G6K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.IdealCechComplex

open Stacks.LocalCohomology

/-! ### The canonical comparison attached to the ideal -/

section Canonical

variable {R : Type u} [CommRing R] {r s t : ℕ} (f : Fin r → R) (g : Fin s → R) (h : Fin t → R)
  (M : ModuleCat.{max u v} R)

/-- **There is exactly one morphism over `M`** between the Čech objects of two families spanning
the same ideal: the source has `I`-power-torsion cohomology and the augmentation of the target is
universal among morphisms from such objects. -/
theorem existsUnique_hom_over_augmentation
    (hfg : Ideal.span (Set.range f) = Ideal.span (Set.range g)) :
    ∃! φ : extendedCechObject f M ⟶ extendedCechObject g M,
      φ ≫ extendedCechAugmentationHom g M = extendedCechAugmentationHom f M := by
  have hI : (Ideal.span (Set.range f)).FG := Submodule.fg_span (Set.finite_range f)
  have hPf := derivedPowerTorsionProperty_extendedCechObject f M _ hI rfl
  have hbij := bijective_comp_extendedCechAugmentationHom g M _ hI hfg.symm
    (extendedCechObject f M) hPf
  obtain ⟨φ, hφ⟩ := hbij.2 (extendedCechAugmentationHom f M)
  exact ⟨φ, hφ, fun ψ hψ => hbij.1 (hψ.trans hφ.symm)⟩

/-- **The canonical comparison of the Čech objects of two families spanning the same ideal.**
Unlike `Stacks.LocalCohomology.exists_extendedCechObject_iso_of_span_eq`, which only asserts that
an isomorphism over `M` exists, this is a named morphism: the unique one over `M`. -/
def canonicalHom (hfg : Ideal.span (Set.range f) = Ideal.span (Set.range g)) :
    extendedCechObject f M ⟶ extendedCechObject g M :=
  (existsUnique_hom_over_augmentation f g M hfg).choose

/-- The canonical comparison is a morphism over `M`. -/
theorem canonicalHom_comp_augmentationHom
    (hfg : Ideal.span (Set.range f) = Ideal.span (Set.range g)) :
    canonicalHom f g M hfg ≫ extendedCechAugmentationHom g M =
      extendedCechAugmentationHom f M :=
  (existsUnique_hom_over_augmentation f g M hfg).choose_spec.1

/-- **Uniqueness.** Every morphism over `M` between the two Čech objects is the canonical one. -/
theorem eq_canonicalHom (hfg : Ideal.span (Set.range f) = Ideal.span (Set.range g))
    (φ : extendedCechObject f M ⟶ extendedCechObject g M)
    (hφ : φ ≫ extendedCechAugmentationHom g M = extendedCechAugmentationHom f M) :
    φ = canonicalHom f g M hfg :=
  (existsUnique_hom_over_augmentation f g M hfg).choose_spec.2 φ hφ

/-- The canonical comparison of a family with itself is the identity. -/
theorem canonicalHom_self (hff : Ideal.span (Set.range f) = Ideal.span (Set.range f)) :
    canonicalHom f f M hff = 𝟙 (extendedCechObject f M) :=
  (eq_canonicalHom f f M hff _ (Category.id_comp _)).symm

/-- **Coherence.** The canonical comparisons compose, so they form a transitive system over the
families spanning a fixed ideal. -/
theorem canonicalHom_comp (h₁ : Ideal.span (Set.range f) = Ideal.span (Set.range g))
    (h₂ : Ideal.span (Set.range g) = Ideal.span (Set.range h)) :
    canonicalHom f g M h₁ ≫ canonicalHom g h M h₂ = canonicalHom f h M (h₁.trans h₂) :=
  eq_canonicalHom f h M (h₁.trans h₂) _
    (by rw [Category.assoc, canonicalHom_comp_augmentationHom,
      canonicalHom_comp_augmentationHom])

/-- **The extended alternating Čech object depends only on the ideal, canonically.** For two
finite families spanning the same ideal the canonical comparison is an isomorphism of `D(R)`
over `M`, and it is the only morphism over `M`. -/
def canonicalIso (hfg : Ideal.span (Set.range f) = Ideal.span (Set.range g)) :
    extendedCechObject f M ≅ extendedCechObject g M where
  hom := canonicalHom f g M hfg
  inv := canonicalHom g f M hfg.symm
  hom_inv_id := by rw [canonicalHom_comp, canonicalHom_self]
  inv_hom_id := by rw [canonicalHom_comp, canonicalHom_self]

/-- The forward map of `canonicalIso` is `canonicalHom`. -/
@[simp]
theorem canonicalIso_hom (hfg : Ideal.span (Set.range f) = Ideal.span (Set.range g)) :
    (canonicalIso f g M hfg).hom = canonicalHom f g M hfg :=
  rfl

/-- The canonical comparison `canonicalHom` is an isomorphism. -/
instance isIso_canonicalHom (hfg : Ideal.span (Set.range f) = Ideal.span (Set.range g)) :
    IsIso (canonicalHom f g M hfg) :=
  (inferInstanceAs (IsIso (canonicalIso f g M hfg).hom))

end Canonical

/-! ### Restriction to a subfamily -/

section Zero

variable {R : Type u} [CommRing R] (M : ModuleCat.{max u v} R)

/-- The degree-zero component of the augmentation, split into the reindexing isomorphism, the
identification of the degree-zero Čech term with the module, and the identification of the
degree-zero term of the target. -/
private theorem augmentation_f_zero_eq {n : ℕ} (u : Fin n → R) :
    (extendedCechAugmentation u M).f 0 =
      (HomologicalComplex.extendXIso (Cech.cechComplex u M) ComplexShape.embeddingUpNat
          ComplexShape.embeddingUpNat_f_zero).hom ≫ (cechZeroIso u M).hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).inv := by
  rw [extendedCechAugmentation_f_zero]
  show ((HomologicalComplex.extendXIso (Cech.cechComplex u M) ComplexShape.embeddingUpNat
    ComplexShape.embeddingUpNat_f_zero).hom ≫ (cechZeroIso u M).hom) ≫ _ = _
  rw [Category.assoc]

end Zero

section Restriction

variable {R : Type u} [CommRing R] {r s : ℕ} (f : Fin r → R) (g : Fin s → R)
  (e : Fin r ↪o Fin s) (he : ∀ i, g (e i) = f i) (M : ModuleCat.{max u v} R)

include he

/-- **In degree zero the restriction map is the identity.** Both degree-zero terms are the single
summand indexed by the empty set, on which the restriction map is the identity of `M`. -/
theorem cechZeroIso_cechRestrict :
    (Cech.cechRestrict f M g e he).f 0 ≫ (cechZeroIso f M).hom = (cechZeroIso g M).hom := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  show cechTermZeroEquiv f M (Cech.cechTermRestrict f M g e he 0 x) =
    cechTermZeroEquiv g M x
  have key : (cechTermZeroEquiv f M).toLinearMap.comp (Cech.cechTermRestrict f M g e he 0) =
      (cechTermZeroEquiv g M).toLinearMap := by
    refine DirectSum.linearMap_ext R fun S => LinearMap.ext fun y => ?_
    obtain rfl : S = default := Subsingleton.elim _ _
    obtain ⟨m, rfl⟩ : ∃ m, y = LocalizedModule.mkLinearMap (Cech.cechSub g ∅) M m :=
      ⟨Stacks.CechBaseChange.cechModEmptyEquiv g M y, by
        rw [← Stacks.CechBaseChange.cechModEmptyEquiv_symm_apply, LinearEquiv.symm_apply_apply]⟩
    show cechTermZeroEquiv f M (Cech.cechTermRestrict f M g e he 0
        (DirectSum.lof R (ExtendedAlternatingCech.Idx s 0)
          (fun S => Cech.cechMod g (M : Type (max u v)) S.1) default
          (LocalizedModule.mkLinearMap (Cech.cechSub g ∅) (M : Type (max u v)) m))) =
      cechTermZeroEquiv g M (DirectSum.lof R (ExtendedAlternatingCech.Idx s 0)
        (fun S => Cech.cechMod g (M : Type (max u v)) S.1) default
        (LocalizedModule.mkLinearMap (Cech.cechSub g ∅) (M : Type (max u v)) m))
    rw [Cech.cechTermRestrict_lof_zero, cechTermZeroEquiv_lof, cechTermZeroEquiv_lof,
      Stacks.CechBaseChange.cechModEmptyEquiv_mk, Stacks.CechBaseChange.cechModEmptyEquiv_mk]
  exact LinearMap.congr_fun key x

/-- **Restriction to a subfamily is compatible with the augmentations onto the module.** -/
theorem extendMap_cechRestrict_comp_augmentation :
    HomologicalComplex.extendMap (Cech.cechRestrict f M g e he) ComplexShape.embeddingUpNat ≫
        extendedCechAugmentation f M = extendedCechAugmentation g M := by
  refine HomologicalComplex.to_single_hom_ext ?_
  rw [HomologicalComplex.comp_f,
    HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat ComplexShape.embeddingUpNat_f_zero,
    augmentation_f_zero_eq M f, augmentation_f_zero_eq M g]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc ((Cech.cechRestrict f M g e he).f 0), cechZeroIso_cechRestrict f g e he M]

/-- **The restriction map on derived objects** `C^•(g; M) ⟶ C^•(f; M)` for a subfamily
`f = g ∘ e`. -/
def restrictObjHom : extendedCechObject g M ⟶ extendedCechObject f M :=
  DerivedCategory.Q.map (HomologicalComplex.extendMap (Cech.cechRestrict f M g e he)
    ComplexShape.embeddingUpNat)

/-- The restriction map on derived objects is a morphism over `M`. -/
theorem restrictObjHom_comp_augmentationHom :
    restrictObjHom f g e he M ≫ extendedCechAugmentationHom f M =
      extendedCechAugmentationHom g M := by
  show DerivedCategory.Q.map (HomologicalComplex.extendMap (Cech.cechRestrict f M g e he)
      ComplexShape.embeddingUpNat) ≫
      (DerivedCategory.Q.map (extendedCechAugmentation f M) ≫
        ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max u v} R) 0).app M).inv) =
    DerivedCategory.Q.map (extendedCechAugmentation g M) ≫
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max u v} R) 0).app M).inv
  rw [← Category.assoc, ← Functor.map_comp, extendMap_cechRestrict_comp_augmentation]

/-- **The restriction map realizes the canonical comparison.** When the subfamily spans the same
ideal, `Cech.cechRestrict` is a map of complexes inducing the canonical comparison of the two
Čech objects. -/
theorem restrictObjHom_eq_canonicalHom
    (hgf : Ideal.span (Set.range g) = Ideal.span (Set.range f)) :
    restrictObjHom f g e he M = canonicalHom g f M hgf :=
  eq_canonicalHom g f M hgf _ (restrictObjHom_comp_augmentationHom f g e he M)

/-- **Restriction to a subfamily spanning the same ideal is a quasi-isomorphism.** This is the
statement flagged as missing in the implementation notes of
`StacksFrontier/RingTheory/LocalCohomology/CechGeneratorIndependence.lean`. -/
theorem isIso_restrictObjHom_of_span_eq
    (hgf : Ideal.span (Set.range g) = Ideal.span (Set.range f)) :
    IsIso (restrictObjHom f g e he M) := by
  rw [restrictObjHom_eq_canonicalHom f g e he M hgf]
  infer_instance

end Restriction

/-! ### The zig-zag through the concatenated family -/

section Append

variable {R : Type u} [CommRing R] {r s : ℕ} (f : Fin r → R) (g : Fin s → R)
  (M : ModuleCat.{max u v} R)

omit [CommRing R] in
/-- The concatenated family contains the first block. -/
theorem append_castAddOrderEmb (i : Fin r) :
    Fin.append f g (Fin.castAddOrderEmb s i) = f i :=
  Fin.append_left f g i

omit [CommRing R] in
/-- The concatenated family contains the second block. -/
theorem append_natAddOrderEmb (j : Fin s) :
    Fin.append f g (Fin.natAddOrderEmb r j) = g j :=
  Fin.append_right f g j

/-- The concatenated family spans the sum of the two ideals, hence the common ideal when the two
families span the same one. -/
theorem span_range_append_eq (hfg : Ideal.span (Set.range f) = Ideal.span (Set.range g)) :
    Ideal.span (Set.range (Fin.append f g)) = Ideal.span (Set.range f) := by
  refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.span_mono ?_)
  · rintro x ⟨i, rfl⟩
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · rw [Fin.append_left]
      exact Ideal.subset_span ⟨i, rfl⟩
    · rw [Fin.append_right, hfg]
      exact Ideal.subset_span ⟨j, rfl⟩
  · rintro x ⟨i, rfl⟩
    exact ⟨Fin.castAdd s i, Fin.append_left f g i⟩

/-- The restriction of the concatenated family onto its first block is an isomorphism in `D(R)`
when the two families span the same ideal. -/
theorem isIso_restrictObjHom_castAdd
    (hfg : Ideal.span (Set.range f) = Ideal.span (Set.range g)) :
    IsIso (restrictObjHom f (Fin.append f g) (Fin.castAddOrderEmb s)
      (append_castAddOrderEmb f g) M) :=
  isIso_restrictObjHom_of_span_eq f (Fin.append f g) (Fin.castAddOrderEmb s)
    (append_castAddOrderEmb f g) M (span_range_append_eq f g hfg)

/-- The restriction of the concatenated family onto its second block is an isomorphism in `D(R)`
when the two families span the same ideal. -/
theorem isIso_restrictObjHom_natAdd
    (hfg : Ideal.span (Set.range f) = Ideal.span (Set.range g)) :
    IsIso (restrictObjHom g (Fin.append f g) (Fin.natAddOrderEmb r)
      (append_natAddOrderEmb f g) M) :=
  isIso_restrictObjHom_of_span_eq g (Fin.append f g) (Fin.natAddOrderEmb r)
    (append_natAddOrderEmb f g) M ((span_range_append_eq f g hfg).trans hfg)

/-- **The canonical comparison is the explicit zig-zag through the concatenated family.** The two
restrictions of `C^•(f₁, …, f_r, g₁, …, g_s; M)` onto its two blocks are maps of complexes, both
quasi-isomorphisms by `isIso_restrictObjHom_castAdd` and `isIso_restrictObjHom_natAdd`, and the
canonical comparison is the unique morphism making the triangle they form commute. -/
theorem restrictObjHom_comp_canonicalHom
    (hfg : Ideal.span (Set.range f) = Ideal.span (Set.range g)) :
    restrictObjHom f (Fin.append f g) (Fin.castAddOrderEmb s)
          (append_castAddOrderEmb f g) M ≫ canonicalHom f g M hfg =
      restrictObjHom g (Fin.append f g) (Fin.natAddOrderEmb r)
        (append_natAddOrderEmb f g) M := by
  have hag : Ideal.span (Set.range (Fin.append f g)) = Ideal.span (Set.range g) :=
    (span_range_append_eq f g hfg).trans hfg
  refine (eq_canonicalHom (Fin.append f g) g M hag _ ?_).trans
    (eq_canonicalHom (Fin.append f g) g M hag _ ?_).symm
  · rw [Category.assoc, canonicalHom_comp_augmentationHom,
      restrictObjHom_comp_augmentationHom]
  · rw [restrictObjHom_comp_augmentationHom]

end Append

end Stacks.IdealCechComplex

end
