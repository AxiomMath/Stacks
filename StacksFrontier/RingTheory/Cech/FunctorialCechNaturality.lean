module

public import StacksFrontier.RingTheory.Cech.FunctorialCechDatumExists

/-!
# The Čech identification of [Stacks, Tag 099D] is natural in the ring

Condition (d) of [Stacks, Tag 099D] says that for a finite family `f₁, …, f_r` generating a
finitely generated ideal `I ⊆ A` the complex `K(A, I)` of a functorial Čech datum is isomorphic,
in `D(A)` and over the augmentations onto `A`, to the extended alternating Čech complex
`C^•(f₁, …, f_r; A)`. As a field of `Stacks.LocalCohomology.FunctorialCechData` it is an
existential statement *for each ring separately*: it asserts nothing about how the
identifications at `A` and at `B` are related along a ring map `φ : A → B`.

**This file proves that they are automatically related.** For every ring map `φ : A → B`, every
finitely generated `I ⊆ A` with `J = IB`, every finite family `f` generating `I` and *every*
choice of identifications `e₁` at `(A, f)` and `e₂` at `(B, φ ∘ f)`, the square

```
C^•(f; A) ⊗^𝐋_A B ────────▸ C^•(φ ∘ f; B)
      │                           │
      │ e₁ ⊗^𝐋 B                  │ e₂
      ▼                           ▼
   K(A, I) ⊗^𝐋_A B ──────────▸ K(B, J)
```

commutes in `D(B)`, the horizontal arrows being the base-change comparisons of condition (c) for
the two models. Equivalently — and this is the form a presheaf of complexes consumes — the square

```
C^•(f; A) ──────▸ K(A, I)
    │                │
    ▼                ▼
C^•(φ ∘ f; B)|_A ▸ K(B, J)|_A
```

commutes in `D(A)`, the vertical arrows being the images of the maps of complexes of `A`-modules
of item (3) of the tag. So the Čech identification of a functorial Čech datum is a natural
transformation on the category of pairs with a chosen finite generating family, with no choices
to coordinate.

The proof is the universal property of the augmentation of the Čech complex. The source of both
composites is `C^•(f; A) ⊗^𝐋_A B`, which is isomorphic to `C^•(φ ∘ f; B)` by condition (c) for
the Čech model and therefore has `J`-power-torsion cohomology; the target `K(B, J)` is, by
condition (d) at `(B, φ ∘ f)`, a complex whose augmentation onto `B` is universal among maps out
of `J`-power-torsion objects. Hence a morphism out of `C^•(f; A) ⊗^𝐋_A B` into `K(B, J)` is
*determined* by its composite with the augmentation, and both composites in the square have the
same one: conditions (a) for the two models turn each of them into the comparison
`B ⊗^𝐋_A A[0] → B[0]` preceded by the image of the augmentation upstairs.

## Main definitions

* `Stacks.LocalCohomology.derivedBaseChangeAdjoint` — the comparison of condition (c) read
  through the adjunction, as a morphism `K → L|_A` of `D(A)`; this is the form in which the
  naturality square lives over `A`.
* `Stacks.LocalCohomology.NaturalCechData` — a functorial Čech datum together with a *chosen*
  Čech identification which is natural in the ring.

## Main results

* `Stacks.LocalCohomology.FunctorialCechData.cechIso_natural` — **the naturality square in
  `D(B)`, for any choices of the two identifications.**
* `Stacks.LocalCohomology.FunctorialCechData.cechIso_natural_restrict` — the same square over
  `A`.
* `Stacks.LocalCohomology.FunctorialCechData.cechIso_natural_of_map` — the same square for an
  arbitrary comparison of the two Čech models, so for a generating family of `IB` which need not
  be the image of the one upstairs.
* `Stacks.LocalCohomology.FunctorialCechData.cechIso_eq_comp` and
  `Stacks.LocalCohomology.FunctorialCechData.cechIso_unique` — the identification is independent
  of the generating family, and for a given family there is exactly one.
* `Stacks.LocalCohomology.FunctorialCechData.hom_ext_derivedAugmentation` — a morphism of `D(B)`
  from a `J`-power-torsion object into `K(B, J)` is determined by its composite with the
  augmentation.
* `Stacks.LocalCohomology.FunctorialCechData.toNaturalCechData` and
  `Stacks.LocalCohomology.nonempty_naturalCechData` — every functorial Čech datum upgrades to a
  natural one, so a datum with a natural Čech identification exists.

## Implementation notes

No `@[stacks 099D]` attribute is attached here. The tag's condition (d) is the existential
statement, and it is registered in full on
`Stacks.LocalCohomology.nonempty_functorialCechData`; what this file adds is strictly stronger
than the tag asks for, and a second unclaused registration would claim no new part of it.

The two named naturality squares are stated for the transported family `φ ∘ f`, which is the
shape a presheaf of complexes on a site needs — a family generating `ℐ|_U` restricts to a family
generating `ℐ|_V` along `V → U` — and the shape in which the left-hand vertical arrow is the
change-of-rings map of the Čech complexes,
`Stacks.CechRingBaseChange.extendedComplexMap`. The underlying statement
`Stacks.LocalCohomology.FunctorialCechData.cechIso_natural_of_map` asks only for *some* map of
complexes between the two Čech models satisfying conditions (a) and (c), so it covers an
arbitrary generating family of `IB` as well, and — at `φ` the identity — the independence of the
identification from the generating family.

Every square here is stated for *arbitrary* choices of `e₁` and `e₂` satisfying condition (d).
That is stronger than producing one compatible system, and there is in fact nothing to choose:
`Stacks.LocalCohomology.FunctorialCechData.cechIso_unique` says the identification at a given
family is unique.

## References

* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
* [Stacks Project, Tag 099E](https://stacks.math.columbia.edu/tag/099E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

open CochainComplex.DerivedExtensionScalars

section Comparison

variable {A B : Type u} [CommRing A] [CommRing B]

/-- **The comparison of condition (c), read over `A`.** A map `u : K → L|_A` of complexes of
`A`-modules into the restriction of a complex of `B`-modules becomes, in the derived categories,
a morphism `K → L|_A` of `D(A)`. It is the image of `Stacks.LocalCohomology.derivedBaseChange`
under the adjunction between derived extension and derived restriction of scalars
(`Stacks.LocalCohomology.homEquiv_derivedBaseChange`), so the two carry the same information;
this is the spelling in which naturality squares live over `A`. -/
def derivedBaseChangeAdjoint (φ : A →+* B) {K : CochainComplex (ModuleCat.{u} A) ℤ}
    {L : CochainComplex (ModuleCat.{u} B) ℤ}
    (u : K ⟶ (CochainComplex.restrictScalars φ).obj L) :
    DerivedCategory.Q.obj K ⟶
      (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory.obj (DerivedCategory.Q.obj L) :=
  DerivedCategory.Q.map u ≫
    (ModuleCat.restrictScalars.{u} φ).mapDerivedCategoryFactors.inv.app L

/-- The comparison of condition (c) and its reading over `A` correspond under the adjunction. -/
theorem homEquiv_derivedBaseChange (φ : A →+* B) {K : CochainComplex (ModuleCat.{u} A) ℤ}
    {L : CochainComplex (ModuleCat.{u} B) ℤ}
    (u : K ⟶ (CochainComplex.restrictScalars φ).obj L) :
    (derivedExtensionRestrictAdjunction.{u, u, u} φ).homEquiv _ _
        (derivedBaseChange φ u) =
      derivedBaseChangeAdjoint φ u :=
  Equiv.apply_symm_apply _ _

/-- **Condition (a) turns the comparison of condition (c) into the comparison of the ring map.**
If `u : K → L|_A` carries an augmentation `a : K → A[0]` onto an augmentation `b : L → B[0]` over
`φ`, then the base-change comparison of `u` followed by `b` is the base-change comparison of
`φ` itself, preceded by the image of `a`.

This is the calculation that `Stacks.LocalCohomology.exists_iso_of_augmentation_squares` performs
on each of its two models, isolated so that it can be applied to a model whose identification is
not being constructed but compared. -/
theorem derivedBaseChange_comp_augmentation (φ : A →+* B)
    {K : CochainComplex (ModuleCat.{u} A) ℤ} {L : CochainComplex (ModuleCat.{u} B) ℤ}
    (u : K ⟶ (CochainComplex.restrictScalars φ).obj L)
    (a : K ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))
    (b : L ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B))
    (h : u ≫ (CochainComplex.restrictScalars φ).map b = a ≫ singleRingHom φ) :
    derivedBaseChange φ u ≫ DerivedCategory.Q.map b =
      (derivedExtensionScalarsGeneral.{u, u, u} φ).functor.map (DerivedCategory.Q.map a) ≫
        derivedBaseChange φ (singleRingHom φ) := by
  rw [← derivedBaseChange_comp_right φ u b, h, derivedBaseChange_comp_left]

/-- The image of a finite generating family of `I` generates `IB`. -/
theorem span_range_mapFamily (φ : A →+* B) {r : ℕ} (f : Fin r → A) {I : Ideal A} {J : Ideal B}
    (hf : Ideal.span (Set.range f) = I) (hφ : J = I.map φ) :
    Ideal.span (Set.range (CechRingBaseChange.mapFamily φ f)) = J := by
  rw [hφ, ← hf, Ideal.map_span]
  exact congrArg Ideal.span (Set.range_comp (φ : A → B) f)

/-- Having `I`-power-torsion cohomology is invariant under isomorphism in `D(A)`. -/
theorem derivedPowerTorsion_of_iso {I : Ideal A} (hI : I.FG)
    {X Y : DerivedCategory (ModuleCat.{u} A)} (e : X ≅ Y)
    (hX : Dualizing.derivedPowerTorsionProperty A I hI X) :
    Dualizing.derivedPowerTorsionProperty A I hI Y := fun i =>
  (Dualizing.powerTorsionModuleProperty A I hI).prop_of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso e) (hX i)

end Comparison

namespace FunctorialCechData

variable (D : FunctorialCechData.{u})

/-- Condition (d) with the comparison between the two models of the single complex divided out:
an identification of condition (d) carries the Čech augmentation onto the datum's own
augmentation, as maps of `D(A)` into `A` placed in degree zero *as a complex*. -/
theorem cechIso_comp_Q_augmentation {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A)
    (I : Ideal A) (hI : I.FG)
    (e : extendedCechObject f (ModuleCat.of A A) ≅ DerivedCategory.Q.obj (D.complex A I hI))
    (he : e.hom ≫ D.derivedAugmentation A I hI =
      extendedCechAugmentationHom f (ModuleCat.of A A)) :
    e.hom ≫ DerivedCategory.Q.map (D.augmentation A I hI) =
      DerivedCategory.Q.map (extendedCechAugmentation f (ModuleCat.of A A)) :=
  comp_eq_of_comp_iso_inv _ _
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app (ModuleCat.of A A)) _ he

/-- **A map into `K(B, J)` out of a torsion object is determined by its augmentation.** By
condition (d) the complex `K(B, J)` is isomorphic over `B` to the extended alternating Čech
complex on a finite generating family of `J`, whose augmentation is universal among morphisms out
of objects with `J`-power-torsion cohomology
(`Stacks.LocalCohomology.bijective_comp_extendedCechAugmentationHom`). So two morphisms into
`K(B, J)` from such an object which have the same composite with the augmentation are equal. -/
theorem hom_ext_derivedAugmentation {B : Type u} [CommRing B] {r : ℕ} (g : Fin r → B)
    (J : Ideal B) (hJ : J.FG) (hg : Ideal.span (Set.range g) = J)
    (e : extendedCechObject g (ModuleCat.of B B) ≅ DerivedCategory.Q.obj (D.complex B J hJ))
    (he : e.hom ≫ D.derivedAugmentation B J hJ =
      extendedCechAugmentationHom g (ModuleCat.of B B))
    (W : DerivedCategory (ModuleCat.{u} B))
    (hW : Dualizing.derivedPowerTorsionProperty B J hJ W)
    (p q : W ⟶ DerivedCategory.Q.obj (D.complex B J hJ))
    (hpq : p ≫ D.derivedAugmentation B J hJ = q ≫ D.derivedAugmentation B J hJ) : p = q := by
  have hbij := bijective_comp_extendedCechAugmentationHom g (ModuleCat.of B B) J hJ hg W hW
  have key : (p ≫ e.inv) ≫ extendedCechAugmentationHom g (ModuleCat.of B B) =
      (q ≫ e.inv) ≫ extendedCechAugmentationHom g (ModuleCat.of B B) := by
    rw [← he]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hpq
  exact (cancel_mono e.inv).1 (hbij.injective key)

/-- **The Čech identification of a functorial Čech datum is natural, for every choice.** Let
`φ : A → B` be a ring map, `I ⊆ A` a finitely generated ideal and `J = IB`. Let `f₁, …, f_r ∈ A`
and let `g₁, …, g_s` generate `J`, and let `u : C^•(f; A) → C^•(g; B)|_A` be a map of complexes of
`A`-modules compatible with the augmentations and `φ` — condition (a) for the Čech model — whose
base-change comparison is invertible — condition (c) for the Čech model. Let `e₁` be *any*
identification of condition (d) at `(A, f)` and `e₂` *any* identification of condition (d) at
`(B, g)`. Then the square formed by `e₁`, `e₂`, the base-change comparison of `u` and the
base-change comparison of the datum's own map `K(A, I) → K(B, J)` commutes in `D(B)`.

So there is nothing to coordinate: the identifications of condition (d) are compatible with
every comparison of the Čech models, for every choice of the identifications.

The source of both composites is `C^•(f; A) ⊗^𝐋_A B`, which is isomorphic to `C^•(g; B)` and
hence has `J`-power-torsion cohomology, and
`Stacks.LocalCohomology.FunctorialCechData.hom_ext_derivedAugmentation` reduces the claim to the
equality of the two composites with the augmentation of `K(B, J)`. Each of those is computed by
`Stacks.LocalCohomology.derivedBaseChange_comp_augmentation` from condition (a) of the
corresponding model — `hu` for the Čech complexes and
`Stacks.LocalCohomology.FunctorialCechData.map_augmentation` for the datum — and the two results
agree because `e₁` carries one augmentation onto the other. -/
theorem cechIso_natural_of_map {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (I : Ideal A) (hI : I.FG) (J : Ideal B) (hJ : J.FG) (hφ : J = I.map φ) {r s : ℕ}
    (f : Fin r → A) (g : Fin s → B) (hg : Ideal.span (Set.range g) = J)
    (u : extendedCechComplex f (ModuleCat.of A A) ⟶
      (CochainComplex.restrictScalars φ).obj (extendedCechComplex g (ModuleCat.of B B)))
    (hu : u ≫ (CochainComplex.restrictScalars φ).map
          (extendedCechAugmentation g (ModuleCat.of B B)) =
      extendedCechAugmentation f (ModuleCat.of A A) ≫ singleRingHom φ)
    (hiso : IsIso (derivedBaseChange φ u))
    (e₁ : extendedCechObject f (ModuleCat.of A A) ≅ DerivedCategory.Q.obj (D.complex A I hI))
    (h₁ : e₁.hom ≫ D.derivedAugmentation A I hI =
      extendedCechAugmentationHom f (ModuleCat.of A A))
    (e₂ : extendedCechObject g (ModuleCat.of B B) ≅ DerivedCategory.Q.obj (D.complex B J hJ))
    (h₂ : e₂.hom ≫ D.derivedAugmentation B J hJ =
      extendedCechAugmentationHom g (ModuleCat.of B B)) :
    derivedBaseChange φ u ≫ e₂.hom =
      (derivedExtensionScalarsGeneral.{u, u, u} φ).functor.map e₁.hom ≫
        derivedBaseChange φ (D.map φ I hI J hJ hφ) := by
  have := hiso
  have hW : Dualizing.derivedPowerTorsionProperty B J hJ
      ((derivedExtensionScalarsGeneral.{u, u, u} φ).functor.obj
        (extendedCechObject f (ModuleCat.of A A))) :=
    derivedPowerTorsion_of_iso hJ (asIso (derivedBaseChange φ u)).symm
      (derivedPowerTorsionProperty_extendedCechObject g (ModuleCat.of B B) J hJ hg)
  refine D.hom_ext_derivedAugmentation g J hJ hg e₂ h₂ _ hW _ _ ?_
  have hcech := derivedBaseChange_comp_augmentation φ u _ _ hu
  have hdat := derivedBaseChange_comp_augmentation φ (D.map φ I hI J hJ hφ) _ _
    (D.map_augmentation φ I hI J hJ hφ)
  simp only [derivedAugmentation, ← Category.assoc, cancel_mono]
  rw [Category.assoc, D.cechIso_comp_Q_augmentation g J hJ e₂ h₂, hcech, Category.assoc, hdat,
    ← Category.assoc, ← Functor.map_comp, D.cechIso_comp_Q_augmentation f I hI e₁ h₁]

/-- **The Čech identification of a functorial Čech datum is natural in the ring.** For a ring map
`φ : A → B`, a finitely generated ideal `I ⊆ A` with `J = IB` and a finite family `f₁, …, f_r`
generating `I`, the identifications of condition (d) at `(A, f)` and at `(B, φ ∘ f)` — *any* two
of them — are carried onto one another by the base-change comparisons of the change-of-rings map
of the Čech complexes and of the datum's own map `K(A, I) → K(B, J)`.

This is `Stacks.LocalCohomology.FunctorialCechData.cechIso_natural_of_map` applied to the
change-of-rings map `Stacks.CechRingBaseChange.extendedComplexMap`, whose compatibility with the
augmentations is `Stacks.CechRingBaseChange.extendedComplexMap_augmentation` and whose base
change is invertible by
`Stacks.CechRingBaseChange.isIso_derivedBaseChange_extendedComplexMap`. -/
theorem cechIso_natural {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A)
    (hI : I.FG) (J : Ideal B) (hJ : J.FG) (hφ : J = I.map φ) {r : ℕ} (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = I)
    (e₁ : extendedCechObject f (ModuleCat.of A A) ≅ DerivedCategory.Q.obj (D.complex A I hI))
    (h₁ : e₁.hom ≫ D.derivedAugmentation A I hI =
      extendedCechAugmentationHom f (ModuleCat.of A A))
    (e₂ : extendedCechObject (CechRingBaseChange.mapFamily φ f) (ModuleCat.of B B) ≅
      DerivedCategory.Q.obj (D.complex B J hJ))
    (h₂ : e₂.hom ≫ D.derivedAugmentation B J hJ =
      extendedCechAugmentationHom (CechRingBaseChange.mapFamily φ f) (ModuleCat.of B B)) :
    derivedBaseChange φ (CechRingBaseChange.extendedComplexMap φ f) ≫ e₂.hom =
      (derivedExtensionScalarsGeneral.{u, u, u} φ).functor.map e₁.hom ≫
        derivedBaseChange φ (D.map φ I hI J hJ hφ) :=
  D.cechIso_natural_of_map φ I hI J hJ hφ f (CechRingBaseChange.mapFamily φ f)
    (span_range_mapFamily φ f hf hφ) (CechRingBaseChange.extendedComplexMap φ f)
    (CechRingBaseChange.extendedComplexMap_augmentation φ f)
    (CechRingBaseChange.isIso_derivedBaseChange_extendedComplexMap φ f) e₁ h₁ e₂ h₂

/-- **The Čech identification does not depend on the generating family.** Let `f` and `g` be two
finite families generating the same finitely generated ideal `I ⊆ A`, and let
`v : C^•(f; A) → C^•(g; A)` be a morphism of `D(A)` over the augmentations onto `A` — there is
exactly one, the two complexes being two models of `RΓ_{V(I)}(A)`. Then any identification of
condition (d) at `(A, f)` is the composite of `v` with any identification at `(A, g)`. -/
theorem cechIso_eq_comp {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG) {r s : ℕ}
    (f : Fin r → A) (g : Fin s → A) (hf : Ideal.span (Set.range f) = I)
    (hg : Ideal.span (Set.range g) = I)
    (v : extendedCechObject f (ModuleCat.of A A) ⟶ extendedCechObject g (ModuleCat.of A A))
    (hv : v ≫ extendedCechAugmentationHom g (ModuleCat.of A A) =
      extendedCechAugmentationHom f (ModuleCat.of A A))
    (e₁ : extendedCechObject f (ModuleCat.of A A) ≅ DerivedCategory.Q.obj (D.complex A I hI))
    (h₁ : e₁.hom ≫ D.derivedAugmentation A I hI =
      extendedCechAugmentationHom f (ModuleCat.of A A))
    (e₂ : extendedCechObject g (ModuleCat.of A A) ≅ DerivedCategory.Q.obj (D.complex A I hI))
    (h₂ : e₂.hom ≫ D.derivedAugmentation A I hI =
      extendedCechAugmentationHom g (ModuleCat.of A A)) :
    e₁.hom = v ≫ e₂.hom := by
  refine D.hom_ext_derivedAugmentation g I hI hg e₂ h₂ _
    (derivedPowerTorsionProperty_extendedCechObject f (ModuleCat.of A A) I hI hf) _ _ ?_
  rw [h₁, Category.assoc, h₂, hv]

/-- **The identification of condition (d) is unique.** Two identifications of condition (d) at
the same pair and the same generating family are equal, so there is no choice being made in
`Stacks.LocalCohomology.FunctorialCechData.toNaturalCechData`. -/
theorem cechIso_unique {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG) {r : ℕ}
    (f : Fin r → A) (hf : Ideal.span (Set.range f) = I)
    (e₁ e₂ : extendedCechObject f (ModuleCat.of A A) ≅ DerivedCategory.Q.obj (D.complex A I hI))
    (h₁ : e₁.hom ≫ D.derivedAugmentation A I hI =
      extendedCechAugmentationHom f (ModuleCat.of A A))
    (h₂ : e₂.hom ≫ D.derivedAugmentation A I hI =
      extendedCechAugmentationHom f (ModuleCat.of A A)) : e₁ = e₂ :=
  Iso.ext (by
    simpa only [Category.id_comp] using
      D.cechIso_eq_comp I hI f f hf hf (𝟙 _) (Category.id_comp _) e₁ h₁ e₂ h₂)

/-- **The naturality square of the Čech identification, over `A`.** The same statement as
`Stacks.LocalCohomology.FunctorialCechData.cechIso_natural`, with the two vertical arrows read as
morphisms of `D(A)` into the restriction of scalars rather than as base-change comparisons over
`B`. This is the form that says the Čech identification is a morphism of presheaves of complexes
on a category of rings: over a morphism of the index category the identification at the source
composed with the restriction map is the restriction map composed with the identification at the
target. -/
theorem cechIso_natural_restrict {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (I : Ideal A) (hI : I.FG) (J : Ideal B) (hJ : J.FG) (hφ : J = I.map φ) {r : ℕ}
    (f : Fin r → A) (hf : Ideal.span (Set.range f) = I)
    (e₁ : extendedCechObject f (ModuleCat.of A A) ≅ DerivedCategory.Q.obj (D.complex A I hI))
    (h₁ : e₁.hom ≫ D.derivedAugmentation A I hI =
      extendedCechAugmentationHom f (ModuleCat.of A A))
    (e₂ : extendedCechObject (CechRingBaseChange.mapFamily φ f) (ModuleCat.of B B) ≅
      DerivedCategory.Q.obj (D.complex B J hJ))
    (h₂ : e₂.hom ≫ D.derivedAugmentation B J hJ =
      extendedCechAugmentationHom (CechRingBaseChange.mapFamily φ f) (ModuleCat.of B B)) :
    derivedBaseChangeAdjoint φ (CechRingBaseChange.extendedComplexMap φ f) ≫
        (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory.map e₂.hom =
      e₁.hom ≫ derivedBaseChangeAdjoint φ (D.map φ I hI J hJ hφ) := by
  have hsq := D.cechIso_natural φ I hI J hJ hφ f hf e₁ h₁ e₂ h₂
  have hL : (derivedExtensionRestrictAdjunction.{u, u, u} φ).homEquiv _ _
        (derivedBaseChange φ (CechRingBaseChange.extendedComplexMap φ f) ≫ e₂.hom) =
      derivedBaseChangeAdjoint φ (CechRingBaseChange.extendedComplexMap φ f) ≫
        (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory.map e₂.hom :=
    (Adjunction.homEquiv_naturality_right _ _ _).trans
      (congrArg (fun t => t ≫ (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory.map e₂.hom)
        (homEquiv_derivedBaseChange φ (CechRingBaseChange.extendedComplexMap φ f)))
  have hR : (derivedExtensionRestrictAdjunction.{u, u, u} φ).homEquiv _ _
        ((derivedExtensionScalarsGeneral.{u, u, u} φ).functor.map e₁.hom ≫
          derivedBaseChange φ (D.map φ I hI J hJ hφ)) =
      e₁.hom ≫ derivedBaseChangeAdjoint φ (D.map φ I hI J hJ hφ) :=
    (Adjunction.homEquiv_naturality_left _ _ _).trans
      (congrArg (fun t => e₁.hom ≫ t)
        (homEquiv_derivedBaseChange φ (D.map φ I hI J hJ hφ)))
  exact hL.symm.trans
    ((congrArg ((derivedExtensionRestrictAdjunction.{u, u, u} φ).homEquiv _ _) hsq).trans hR)

end FunctorialCechData

/-- **A functorial Čech datum whose Čech identification is natural in the ring.** The data and
the four conditions of [Stacks, Tag 099D], with condition (d) strengthened: instead of the mere
existence of an isomorphism `C^•(f; A) ≅ K(A, I)` of `D(A)` over `A` for each ring separately, a
*chosen* such isomorphism for every ring and every finite generating family, compatible with
every ring map `A → B` in the sense of `FunctorialCechData.cechIso_natural`.

Every functorial Čech datum is one, by
`Stacks.LocalCohomology.FunctorialCechData.toNaturalCechData`: the naturality is automatic. The
structure exists because a consumer — the construction of the complex of [Stacks, Tag 099E] on a
ringed site — needs the identifications as data and their compatibility as an equation, not as a
family of unrelated existence statements. -/
structure NaturalCechData extends FunctorialCechData.{u} where
  /-- (d), with the isomorphism of condition (d) chosen. -/
  cechIso (A : Type u) [CommRing A] {r : ℕ} (f : Fin r → A) (I : Ideal A) (hI : I.FG)
    (hf : Ideal.span (Set.range f) = I) :
    extendedCechObject f (ModuleCat.of A A) ≅ DerivedCategory.Q.obj (complex A I hI)
  /-- The chosen isomorphism carries the Čech augmentation onto the datum's augmentation. -/
  cechIso_augmentation (A : Type u) [CommRing A] {r : ℕ} (f : Fin r → A) (I : Ideal A)
      (hI : I.FG) (hf : Ideal.span (Set.range f) = I) :
    (cechIso A f I hI hf).hom ≫ DerivedCategory.Q.map (augmentation A I hI) ≫
        ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app
          (ModuleCat.of A A)).inv =
      extendedCechAugmentationHom f (ModuleCat.of A A)
  /-- **The chosen isomorphisms are natural in the ring.** For a ring map `φ : A → B` with
  `J = IB` the identification at `(B, φ ∘ f)` is the identification at `(A, f)`, base changed
  along `φ`, read through the comparisons of condition (c) for the two models. -/
  cechIso_natural {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A)
      (hI : I.FG) (J : Ideal B) (hJ : J.FG) (hφ : J = I.map φ) {r : ℕ} (f : Fin r → A)
      (hf : Ideal.span (Set.range f) = I) :
    derivedBaseChange φ (CechRingBaseChange.extendedComplexMap φ f) ≫
        (cechIso B (CechRingBaseChange.mapFamily φ f) J hJ
          (span_range_mapFamily φ f hf hφ)).hom =
      (derivedExtensionScalarsGeneral.{u, u, u} φ).functor.map (cechIso A f I hI hf).hom ≫
        derivedBaseChange φ (map φ I hI J hJ hφ)

namespace FunctorialCechData

/-- **Every functorial Čech datum has a natural Čech identification.** Choose, for each ring and
each finite generating family, an isomorphism of condition (d); the naturality is then automatic
by `Stacks.LocalCohomology.FunctorialCechData.cechIso_natural`, which holds for any choices. -/
def toNaturalCechData (D : FunctorialCechData.{u}) : NaturalCechData.{u} where
  toFunctorialCechData := D
  cechIso A _ _ f I hI hf := (D.exists_cech_iso A f I hI hf).choose
  cechIso_augmentation A _ _ f I hI hf := (D.exists_cech_iso A f I hI hf).choose_spec
  cechIso_natural φ I hI J hJ hφ _ f hf :=
    D.cechIso_natural φ I hI J hJ hφ f hf _
      (D.exists_cech_iso _ f I hI hf).choose_spec _
      (D.exists_cech_iso _ (CechRingBaseChange.mapFamily φ f) J hJ
        (span_range_mapFamily φ f hf hφ)).choose_spec

end FunctorialCechData

/-- **[Stacks, Tag 099D] with condition (d) natural in the ring.** There is a functorial Čech
datum together with a choice, for every ring `A`, every finitely generated ideal `I ⊆ A` and
every finite family `f₁, …, f_r` generating `I`, of an isomorphism
`C^•(f₁, …, f_r; A) ≅ K(A, I)` in `D(A)` over the augmentations onto `A`, such that these
isomorphisms are compatible with every ring map `A → B`.

No `@[stacks 099D]` attribute is attached: the tag's condition (d) is the existential statement,
which `Stacks.LocalCohomology.nonempty_functorialCechData` registers in full; this is a
strengthening of it. -/
theorem nonempty_naturalCechData : Nonempty NaturalCechData.{u} :=
  ⟨nonempty_functorialCechData.{u}.some.toNaturalCechData⟩

end Stacks.LocalCohomology

end
