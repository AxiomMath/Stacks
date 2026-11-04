module

public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.RingTheory.MilnorPatching.ProjectiveModules

/-!
# Patching complexes of finite projective modules over a fibre product of rings

Let `B' = B ×_A A'` be a fibre product of rings in which `A' → A` is surjective. A complex `E` of
finite projective `B`-modules and a complex `P` of finite projective `A'`-modules, together with
an isomorphism of complexes `E ⊗_B A ≅ P ⊗_{A'} A`, come from a complex `L` of finite projective
`B'`-modules: `L ⊗_{B'} B ≅ E` and `L ⊗_{B'} A' ≅ P` compatibly with the given isomorphism.

## Main definitions

* `MilnorPatching.patchedComplex`: the complex `L` of finite projective `B'`-modules.
* `MilnorPatching.patchedComplexExtendScalarsFstIso` and
  `MilnorPatching.patchedComplexExtendScalarsSndIso`: the isomorphisms of complexes
  `L ⊗_{B'} B ≅ E` and `L ⊗_{B'} A' ≅ P`.

## Main results

* `MilnorPatching.patchedComplex_finite_projective`: the terms of `L` are finite projective.
* `MilnorPatching.patchedComplexExtendScalarsIso_compatible`: the two isomorphisms are
  compatible with `φ`.
* `MilnorPatching.isZero_patchedComplex_X`: `L` vanishes in every degree in which `E` and `P`
  vanish, so `L` is bounded above when `E` and `P` are.

## Implementation notes

The complex `L` is obtained by applying, degree by degree, the inverse of the equivalence of
Stacks Tag 0D2J between finite projective `B'`-modules and compatible pairs of finite projective
modules. That equivalence is not additive as stated (the category of compatible pairs carries no
preadditive structure here), so the vanishing of `d ∘ d` and of the differentials off the
complex shape are read off through extension of scalars, which is faithful on finite projective
modules because it is identified with the equivalence followed by a fully faithful inclusion.

This is the complex-level step in the proof of Stacks Tag 0DL7, where it is applied with
`B' → B` surjective with locally nilpotent kernel to a lift provided by Stacks Tag 0BCE.

## References

* [Stacks Project, Tag 0D2J](https://stacks.math.columbia.edu/tag/0D2J)
* [Stacks Project, Tag 0DL7](https://stacks.math.columbia.edu/tag/0DL7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ModuleGlueing

universe u

namespace MilnorPatching

variable {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
  {toBase : B →+* A} {surjection : A' →+* A}

section PatchObjects

variable (E : CochainComplex (ModuleCat.{u} B) ℤ) (P : CochainComplex (ModuleCat.{u} A') ℤ)
  (φ : ((ModuleCat.extendScalars.{u, u, u} toBase).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E ≅
    ((ModuleCat.extendScalars.{u, u, u} surjection).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P)

/-- The compatible pair formed by the degree `n` terms of two complexes identified after
extension of scalars. -/
def complexPatchObj (n : ℤ) :
    CategoricalPullback (ModuleCat.extendScalars.{u, u, u} toBase)
      (ModuleCat.extendScalars.{u, u, u} surjection) where
  fst := E.X n
  snd := P.X n
  iso := (HomologicalComplex.eval _ _ n).mapIso φ

/-- The morphism of compatible pairs formed by the differentials of two complexes identified
after extension of scalars. -/
def complexPatchD (i j : ℤ) : complexPatchObj E P φ i ⟶ complexPatchObj E P φ j where
  fst := E.d i j
  snd := P.d i j
  w := by simpa [complexPatchObj] using (φ.hom.comm i j).symm

end PatchObjects

section Equivalence

omit [CommRing A] [CommRing A'] [CommRing B] in
private lemma extendScalars_map_zero {R T : Type u} [CommRing R] [CommRing T] (f : R →+* T)
    (M N : ModuleCat.{u} R) :
    (ModuleCat.extendScalars.{u, u, u} f).map (0 : M ⟶ N) = 0 :=
  Functor.map_zero _ _ _

variable (I : Ideal A') (s : RingFibreProduct.Situation toBase surjection I)

/-- Extension of scalars from `B' = B ×_A A'` into compatible pairs. -/
abbrev fibreProductExtension :
    ModuleCat.{u} s.fibreProduct ⥤ CategoricalPullback
      (ModuleCat.extendScalars.{u, u, u} toBase) (ModuleCat.extendScalars.{u, u, u} surjection) :=
  extensionOfScalarsToPullback.{u, u, u, u, u} s.pullbackCone.fst.hom s.pullbackCone.snd.hom
    toBase surjection (congrArg CommRingCat.Hom.hom s.pullbackCone.condition)

/-- Finite projective `B'`-modules. -/
abbrev finiteProjectiveFibreProductModule : ObjectProperty (ModuleCat.{u} s.fibreProduct) :=
  fun L ↦ Module.Finite s.fibreProduct L ∧ Module.Projective s.fibreProduct L

/-- Compatible pairs whose two components are finite projective. -/
abbrev finiteProjectiveCompatiblePair (toBase : B →+* A) (surjection : A' →+* A) :
    ObjectProperty (CategoricalPullback
    (ModuleCat.extendScalars.{u, u, u} toBase) (ModuleCat.extendScalars.{u, u, u} surjection)) :=
  fun X ↦ (Module.Finite B X.fst ∧ Module.Projective B X.fst) ∧
    (Module.Finite A' X.snd ∧ Module.Projective A' X.snd)

/-- Stacks Tag 0D2J, with the source and target subcategories named. -/
theorem exists_finiteProjectivePatchingEquivalence :
    ∃ q : ObjectProperty.FullSubcategory (finiteProjectiveFibreProductModule I s) ≌
        ObjectProperty.FullSubcategory (finiteProjectiveCompatiblePair toBase surjection),
      Nonempty (ObjectProperty.ι (finiteProjectiveFibreProductModule I s) ⋙
          fibreProductExtension I s ≅
        q.functor ⋙ ObjectProperty.ι (finiteProjectiveCompatiblePair toBase surjection)) :=
  finiteProjectiveModulesEquivalenceOverFibreProduct toBase surjection I s

/-- The equivalence of Stacks Tag 0D2J, chosen once. -/
def finiteProjectivePatchingEquivalence :
    ObjectProperty.FullSubcategory (finiteProjectiveFibreProductModule I s) ≌
      ObjectProperty.FullSubcategory (finiteProjectiveCompatiblePair toBase surjection) :=
  (exists_finiteProjectivePatchingEquivalence I s).choose

/-- The chosen equivalence of Stacks Tag 0D2J is extension of scalars. -/
def finiteProjectivePatchingEquivalenceFunctorIso :
    ObjectProperty.ι (finiteProjectiveFibreProductModule I s) ⋙ fibreProductExtension I s ≅
      (finiteProjectivePatchingEquivalence I s).functor ⋙
        ObjectProperty.ι (finiteProjectiveCompatiblePair toBase surjection) :=
  (exists_finiteProjectivePatchingEquivalence I s).choose_spec.some

/-- Extension of scalars from finite projective `B'`-modules to compatible pairs is faithful. -/
instance : (ObjectProperty.ι (finiteProjectiveFibreProductModule I s) ⋙
    fibreProductExtension I s).Faithful :=
  Functor.Faithful.of_iso (finiteProjectivePatchingEquivalenceFunctorIso I s).symm

/-- The identification of extension of scalars of the patched module with the given compatible
pair. -/
def finiteProjectivePatchingIso
    (X : ObjectProperty.FullSubcategory (finiteProjectiveCompatiblePair toBase surjection)) :
    (fibreProductExtension I s).obj ((finiteProjectivePatchingEquivalence I s).inverse.obj X).obj ≅
      X.obj :=
  (finiteProjectivePatchingEquivalenceFunctorIso I s).app _ ≪≫
    (ObjectProperty.ι _).mapIso ((finiteProjectivePatchingEquivalence I s).counitIso.app X)

/-- Naturality of `finiteProjectivePatchingIso`. -/
theorem finiteProjectivePatchingIso_naturality
    {X Y : ObjectProperty.FullSubcategory (finiteProjectiveCompatiblePair toBase surjection)}
    (g : X ⟶ Y) :
    (fibreProductExtension I s).map ((finiteProjectivePatchingEquivalence I s).inverse.map g).hom ≫
        (finiteProjectivePatchingIso I s Y).hom =
      (finiteProjectivePatchingIso I s X).hom ≫ g.hom := by
  have h₁ := (finiteProjectivePatchingEquivalenceFunctorIso I s).hom.naturality
    ((finiteProjectivePatchingEquivalence I s).inverse.map g)
  have h₂ := congrArg InducedCategory.Hom.hom
    ((finiteProjectivePatchingEquivalence I s).counitIso.hom.naturality g)
  dsimp at h₁ h₂
  simp only [finiteProjectivePatchingIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Category.assoc]
  rw [reassoc_of% h₁]
  exact congrArg (fun t ↦ _ ≫ t) h₂

/-- The patched morphism of a morphism of compatible pairs with zero components is zero. -/
theorem finiteProjectivePatchingEquivalence_inverse_map_hom_eq_zero
    {X Y : ObjectProperty.FullSubcategory (finiteProjectiveCompatiblePair toBase surjection)}
    (g : X ⟶ Y) (h₁ : g.hom.fst = 0) (h₂ : g.hom.snd = 0) :
    ((finiteProjectivePatchingEquivalence I s).inverse.map g).hom = 0 := by
  suffices h : (finiteProjectivePatchingEquivalence I s).inverse.map g = ObjectProperty.homMk 0 from
    congrArg InducedCategory.Hom.hom h
  apply (ObjectProperty.ι (finiteProjectiveFibreProductModule I s) ⋙
    fibreProductExtension I s).map_injective
  have hn := finiteProjectivePatchingIso_naturality I s g
  rw [← Iso.eq_comp_inv] at hn
  change (fibreProductExtension I s).map
      ((finiteProjectivePatchingEquivalence I s).inverse.map g).hom =
    (fibreProductExtension I s).map 0
  rw [hn]
  apply CategoricalPullback.hom_ext
  · simp only [CategoricalPullback.comp_fst, h₁, Limits.comp_zero, Limits.zero_comp]
    exact (extendScalars_map_zero s.pullbackCone.fst.hom _ _).symm
  · simp only [CategoricalPullback.comp_snd, h₂, Limits.comp_zero, Limits.zero_comp]
    exact (extendScalars_map_zero s.pullbackCone.snd.hom _ _).symm

/-- The patched module of a compatible pair of zero modules is zero. -/
theorem isZero_obj_finiteProjectivePatchingEquivalence_inverse
    (X : ObjectProperty.FullSubcategory (finiteProjectiveCompatiblePair toBase surjection))
    (h₁ : IsZero X.obj.fst) (h₂ : IsZero X.obj.snd) :
    IsZero ((finiteProjectivePatchingEquivalence I s).inverse.obj X).obj := by
  rw [IsZero.iff_id_eq_zero]
  suffices h : 𝟙 ((finiteProjectivePatchingEquivalence I s).inverse.obj X) =
      ObjectProperty.homMk 0 from congrArg InducedCategory.Hom.hom h
  apply (ObjectProperty.ι (finiteProjectiveFibreProductModule I s) ⋙
    fibreProductExtension I s).map_injective
  rw [← cancel_epi (finiteProjectivePatchingIso I s X).inv,
    ← cancel_mono (finiteProjectivePatchingIso I s X).hom]
  exact CategoricalPullback.hom_ext (h₁.eq_of_src _ _) (h₂.eq_of_src _ _)

end Equivalence

section Complex

variable (I : Ideal A') (s : RingFibreProduct.Situation toBase surjection I)
  (E : CochainComplex (ModuleCat.{u} B) ℤ) (P : CochainComplex (ModuleCat.{u} A') ℤ)
  (φ : ((ModuleCat.extendScalars.{u, u, u} toBase).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E ≅
    ((ModuleCat.extendScalars.{u, u, u} surjection).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P)
  (hE : ∀ n, Module.Finite B (E.X n) ∧ Module.Projective B (E.X n))
  (hP : ∀ n, Module.Finite A' (P.X n) ∧ Module.Projective A' (P.X n))

/-- The degree `n` compatible pair of finite projective modules. -/
def complexPatchPair (n : ℤ) :
    ObjectProperty.FullSubcategory (finiteProjectiveCompatiblePair toBase surjection) :=
  ⟨complexPatchObj E P φ n, hE n, hP n⟩

/-- The complex of finite projective `B'`-modules patched from `E`, `P` and `φ`. -/
def patchedComplex : CochainComplex (ModuleCat.{u} s.fibreProduct) ℤ where
  X n := ((finiteProjectivePatchingEquivalence I s).inverse.obj
    (complexPatchPair E P φ hE hP n)).obj
  d i j := ((finiteProjectivePatchingEquivalence I s).inverse.map
    (ObjectProperty.homMk (complexPatchD E P φ i j))).hom
  shape i j hij := finiteProjectivePatchingEquivalence_inverse_map_hom_eq_zero I s
    (X := complexPatchPair E P φ hE hP i) (Y := complexPatchPair E P φ hE hP j)
    (ObjectProperty.homMk (complexPatchD E P φ i j))
    (show (complexPatchD E P φ i j).fst = 0 from E.shape i j hij)
    (show (complexPatchD E P φ i j).snd = 0 from P.shape i j hij)
  d_comp_d' i j k _ _ := by
    change ((finiteProjectivePatchingEquivalence I s).inverse.map _ ≫
      (finiteProjectivePatchingEquivalence I s).inverse.map _).hom = 0
    rw [← Functor.map_comp]
    exact finiteProjectivePatchingEquivalence_inverse_map_hom_eq_zero I s _
      (show (complexPatchD E P φ i j ≫ complexPatchD E P φ j k).fst = 0 from
        HomologicalComplex.d_comp_d E i j k)
      (show (complexPatchD E P φ i j ≫ complexPatchD E P φ j k).snd = 0 from
        HomologicalComplex.d_comp_d P i j k)

/-- The terms of the patched complex are finite projective. -/
theorem patchedComplex_finite_projective (n : ℤ) :
    Module.Finite s.fibreProduct ((patchedComplex I s E P φ hE hP).X n) ∧
      Module.Projective s.fibreProduct ((patchedComplex I s E P φ hE hP).X n) :=
  ((finiteProjectivePatchingEquivalence I s).inverse.obj (complexPatchPair E P φ hE hP n)).property

/-- The patched complex vanishes wherever both given complexes vanish. -/
theorem isZero_patchedComplex_X (n : ℤ) (h₁ : IsZero (E.X n)) (h₂ : IsZero (P.X n)) :
    IsZero ((patchedComplex I s E P φ hE hP).X n) :=
  isZero_obj_finiteProjectivePatchingEquivalence_inverse I s _ h₁ h₂

/-- In each degree, the scalar extensions of the patched complex form the given compatible
pair. -/
def patchedComplexExtensionIso (n : ℤ) :
    (fibreProductExtension I s).obj ((patchedComplex I s E P φ hE hP).X n) ≅
      complexPatchObj E P φ n :=
  finiteProjectivePatchingIso I s (complexPatchPair E P φ hE hP n)

/-- The degreewise identifications commute with the differentials. -/
theorem patchedComplexExtensionIso_naturality (i j : ℤ) :
    (fibreProductExtension I s).map ((patchedComplex I s E P φ hE hP).d i j) ≫
        (patchedComplexExtensionIso I s E P φ hE hP j).hom =
      (patchedComplexExtensionIso I s E P φ hE hP i).hom ≫ complexPatchD E P φ i j := by
  dsimp only [patchedComplex, patchedComplexExtensionIso]
  exact finiteProjectivePatchingIso_naturality I s
    (X := complexPatchPair E P φ hE hP i) (Y := complexPatchPair E P φ hE hP j)
    (ObjectProperty.homMk (complexPatchD E P φ i j))

/-- Extension of scalars of the patched complex to `B` is `E`. -/
def patchedComplexExtendScalarsFstIso :
    ((ModuleCat.extendScalars.{u, u, u} s.pullbackCone.fst.hom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (patchedComplex I s E P φ hE hP) ≅ E :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (CategoricalPullback.π₁ _ _).mapIso (patchedComplexExtensionIso I s E P φ hE hP n))
    (fun i j _ ↦ by
      have h := congrArg CategoricalPullback.Hom.fst
        (patchedComplexExtensionIso_naturality I s E P φ hE hP i j)
      simp only [CategoricalPullback.comp_fst] at h
      exact h.symm)

/-- Extension of scalars of the patched complex to `A'` is `P`. -/
def patchedComplexExtendScalarsSndIso :
    ((ModuleCat.extendScalars.{u, u, u} s.pullbackCone.snd.hom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (patchedComplex I s E P φ hE hP) ≅ P :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (CategoricalPullback.π₂ _ _).mapIso (patchedComplexExtensionIso I s E P φ hE hP n))
    (fun i j _ ↦ by
      have h := congrArg CategoricalPullback.Hom.snd
        (patchedComplexExtensionIso_naturality I s E P φ hE hP i j)
      simp only [CategoricalPullback.comp_snd] at h
      exact h.symm)

/-- The two identifications of the patched complex are compatible with `φ`. -/
theorem patchedComplexExtendScalarsIso_compatible (n : ℤ) :
    (ModuleCat.extendScalars.{u, u, u} toBase).map
        ((patchedComplexExtendScalarsFstIso I s E P φ hE hP).hom.f n) ≫ φ.hom.f n =
      ((fibreProductExtension I s).obj ((patchedComplex I s E P φ hE hP).X n)).iso.hom ≫
        (ModuleCat.extendScalars.{u, u, u} surjection).map
          ((patchedComplexExtendScalarsSndIso I s E P φ hE hP).hom.f n) :=
  (patchedComplexExtensionIso I s E P φ hE hP n).hom.w

end Complex

end MilnorPatching
