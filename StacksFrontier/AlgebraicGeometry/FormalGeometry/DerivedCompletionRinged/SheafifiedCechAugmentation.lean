module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.CompletionUnitRestriction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.SheafifiedCechAlternating
public import StacksFrontier.RingTheory.Cech.PresheafSummand

/-!
# The identification of the two Čech complexes respects the augmentations

`AlgebraicGeometry.RingedSite.sheafifiedCechIsoExtendedAlternatingCech` identifies the object
[Stacks, Tag 099E] *constructs* — the sheafification `K(f)` of the presheaf of Čech complexes —
with the complex the tag *displays*, the extended alternating Čech complex `Č(f)` of the same
family of global sections. Each of the two carries its own augmentation onto `𝒪`:
`AlgebraicGeometry.RingedSite.sheafifiedCechAugmentation`, the sheafification of the
presheafwise augmentation, and `AlgebraicGeometry.RingedSite.cechAugmentation`, the
identification of the degree-zero term `𝒪_{f_∅} = 𝒪_1` with `𝒪`.

This file proves that the identification carries the first to the second. This is the
compatibility needed to read `exists_iso_sheafifiedCech_of_idealOfGlobalSections_eq` of
`SheafifiedCechLocalIndependence.lean`, which compares two families' objects *over `𝒪`* in the
first spelling, in the second spelling, where [Stacks, Tag 099E] asks for the comparison.

## Main definitions

* `AlgebraicGeometry.RingedSite.unitToCechPresheafTermZero` and
  `AlgebraicGeometry.RingedSite.unitToSheafifiedCechZero`: the canonical map `𝒪 ⟶ K(f)^0` into
  the degree-zero term, at the presheaf level and after sheafification.

## Main results

* `AlgebraicGeometry.RingedSite.unitToCechPresheafTermZero_comp_augmentation`: **the degree-zero
  Čech augmentation of the presheaf of complexes is split by the inclusion of the summand at
  `∅`**, the empty subproduct `f_∅ = 1` inverting nothing.
* `AlgebraicGeometry.RingedSite.sheafifiedCechAugmentation_f_zero`: the augmentation of the
  sheafified presheaf of Čech complexes, in degree zero.
* `AlgebraicGeometry.RingedSite.unitToSheafifiedCechZero_comp_iso_hom_f_zero`: the identification
  of the two spellings carries the canonical map `𝒪 ⟶ K(f)^0` to the augmentation `𝒪 ⟶ Č(f)^0`.
* The identification carries `K(f) ⟶ 𝒪` to `Č(f) ⟶ 𝒪`:
  `AlgebraicGeometry.RingedSite.sheafifiedCechIsoExtendedAlternatingCech_hom_comp_cechAugmentation`

## Implementation notes

Both augmentations are determined in degree zero, and in degree zero both factor through the
single summand indexed by the empty subset — on one side because the index type of the
degree-zero term is a singleton, on the other because the augmentation of the presheaf of Čech
complexes is `Stacks.CechPresheaf.cechPresheafAugmentationZero_eq`. So the comparison is a
statement about the summand at `∅`, where the presheafwise augmentation sends `x/1` to `x` and
the sheafified summand is `𝒪_{f_∅}`
(`AlgebraicGeometry.RingedSite.toModuleSheafification_comp_cechSummandSheafificationIso`).

Three composites have to be unwound in degree zero to see this: the augmentation of the
`ℤ`-indexed presheaf of complexes, which is the `ℕ`-indexed one extended by zero; the
augmentation of its sheafification, which is the sheafification of the presheaf augmentation read
through the counit at `𝒪`; and the identification of the two spellings, which is the extension
comparison followed by the passage of sheafification through a product.

*Why the category-theoretic algebra goes through named abstract lemmas.* Reassociating these
composites with `rw` or `simp` fails: the objects involved — `((single V c 0).obj A).X 0` and
`A`, `(sheafifiedCech X f).X 0` and the sheafification of `(cechPresheafComplex X f).X 0`,
`(SheafOfModules.unit R).val` and `PresheafOfModules.unit R.obj` — are equal only after
semireducible definitions unfold, which is below the transparency at which `rw` checks that its
motive is type-correct. The four lemmas of the `CategoryTheory.Iso` section below state the
needed cancellations in a bare category with no dependent types, where `simp` proves them, and
they are then applied by `exact`, at which transparency the objects do agree.

## References

* [Stacks Project, Tag 099E](https://stacks.math.columbia.edu/tag/099E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v u' v' w

namespace CategoryTheory.Iso

/-- For isomorphisms `e₁ : D ≅ C` and `e₂ : E ≅ D`, the composite
`(a ≫ (b ≫ e₁.inv) ≫ e₂.inv) ≫ e₂.hom ≫ e₁.hom ≫ g` equals `a ≫ b ≫ g`. -/
theorem comp_assoc_cancel_two {𝒞 : Type u} [Category.{v} 𝒞] {A B C D E F : 𝒞}
    (a : A ⟶ B) (b : B ⟶ C) (e₁ : D ≅ C) (e₂ : E ≅ D) (g : C ⟶ F) :
    (a ≫ (b ≫ e₁.inv) ≫ e₂.inv) ≫ e₂.hom ≫ e₁.hom ≫ g = a ≫ b ≫ g := by
  simp

/-- For an isomorphism `e : D ≅ B`, `(a ≫ e.inv) ≫ e.hom ≫ b = a ≫ b`. -/
theorem comp_inv_comp_hom_comp {𝒞 : Type u} [Category.{v} 𝒞] {A B D E : 𝒞}
    (a : A ⟶ B) (e : D ≅ B) (b : B ⟶ E) :
    (a ≫ e.inv) ≫ e.hom ≫ b = a ≫ b := by
  simp

/-- For a functor `G` and isomorphisms `p : D ≅ B` and `q : E ≅ G.obj B`, the composite
`G.map (u ≫ v ≫ p.inv) ≫ (G.map p.hom ≫ q.inv) ≫ q.hom ≫ g` equals `G.map (u ≫ v) ≫ g`. -/
theorem map_comp_inv_cancel {𝒜 : Type u} [Category.{v} 𝒜] {ℬ : Type u'} [Category.{v'} ℬ]
    (G : 𝒜 ⥤ ℬ) {A B₀ B D : 𝒜} {E F : ℬ} (u : A ⟶ B₀) (v : B₀ ⟶ B) (p : D ≅ B)
    (q : E ≅ G.obj B) (g : G.obj B ⟶ F) :
    G.map (u ≫ v ≫ p.inv) ≫ (G.map p.hom ≫ q.inv) ≫ q.hom ≫ g = G.map (u ≫ v) ≫ g := by
  simp

/-- If an endomorphism `a` of `A` is the identity, then `G.map a ≫ g = g`. -/
theorem map_eq_id_comp {𝒜 : Type u} [Category.{v} 𝒜] {ℬ : Type u'} [Category.{v'} ℬ]
    (G : 𝒜 ⥤ ℬ) {A : 𝒜} {E : ℬ} {a : A ⟶ A} (ha : a = 𝟙 A) (g : G.obj A ⟶ E) :
    G.map a ≫ g = g := by
  rw [ha, G.map_id, Category.id_comp]

/-- For a functor `G`, `G.map a ≫ G.map b ≫ g = G.map (a ≫ b) ≫ g`. -/
theorem map_comp_comp {𝒜 : Type u} [Category.{v} 𝒜] {ℬ : Type u'} [Category.{v'} ℬ]
    (G : 𝒜 ⥤ ℬ) {A B D : 𝒜} {E : ℬ} (a : A ⟶ B) (b : B ⟶ D) (g : G.obj D ⟶ E) :
    G.map a ≫ G.map b ≫ g = G.map (a ≫ b) ≫ g := by
  simp

/-- If `a ≫ b = 𝟙 A`, then `a ≫ b ≫ g = g`. -/
theorem comp_eq_id_comp {𝒞 : Type u} [Category.{v} 𝒞] {A B D : 𝒞} {a : A ⟶ B} {b : B ⟶ A}
    (hab : a ≫ b = 𝟙 A) (g : A ⟶ D) : a ≫ b ≫ g = g := by
  rw [← Category.assoc, hab, Category.id_comp]

/-- If `s ≫ π = π' ≫ w` and `t ≫ π' = G.map πB`, then
`(G.map a ≫ t ≫ s) ≫ π = G.map (a ≫ πB) ≫ w`. -/
theorem map_comp_comp_comp_pi {𝒜 : Type u} [Category.{v} 𝒜] {ℬ : Type u'} [Category.{v'} ℬ]
    (G : 𝒜 ⥤ ℬ) {A B B' : 𝒜} {T S Y : ℬ} (a : A ⟶ B) (t : G.obj B ⟶ T) (s : T ⟶ S)
    (π : S ⟶ Y) (π' : T ⟶ G.obj B') (πB : B ⟶ B') (w : G.obj B' ⟶ Y)
    (h1 : s ≫ π = π' ≫ w) (h2 : t ≫ π' = G.map πB) :
    (G.map a ≫ t ≫ s) ≫ π = G.map (a ≫ πB) ≫ w := by
  rw [Category.assoc, Category.assoc, h1, ← Category.assoc t, h2, G.map_comp, Category.assoc]

end CategoryTheory.Iso

namespace Stacks.CechPresheaf

variable {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ CommRingCat.{w}) {r : ℕ}
  (f : ∀ V : Cᵒᵖ, Fin r → R.obj V)
  (hf : ∀ {V W : Cᵒᵖ} (a : V ⟶ W) (i : Fin r), (R.map a).hom (f V i) = f W i)

/-- The augmentation of the localization at the empty subproduct sends `x/1` to `x`. -/
theorem cechLocAugmentationEmpty_app_mk (V : Cᵒᵖ) (x : R.obj V) :
    ((cechLocAugmentationEmpty R f hf).app V).hom
        (LocalizedModule.mkLinearMap (Cech.cechSub (f V) (∅ : Finset (Fin r)))
          (R.obj V) x) = x := by
  show Stacks.LocalCohomology.cechTermZeroEquiv (f V) (ModuleCat.of (R.obj V) (R.obj V))
      (DirectSum.lof (R.obj V) (ExtendedAlternatingCech.Idx r 0)
        (fun s => Cech.cechMod (f V) (R.obj V) s.1) default
        (LocalizedModule.mkLinearMap (Cech.cechSub (f V) (∅ : Finset (Fin r)))
          (R.obj V) x)) = x
  rw [Stacks.LocalCohomology.cechTermZeroEquiv_lof,
    Stacks.CechBaseChange.cechModEmptyEquiv_mk]

/-- In degree zero, the augmentation of the `ℕ`-indexed presheaf of Čech complexes is
`cechPresheafAugmentationZero` followed by the identification of the degree-zero term of the
single complex on the unit with the unit. -/
theorem cechPresheafAugmentationNat_f_zero :
    (cechPresheafAugmentationNat R f hf).f 0 =
      cechPresheafAugmentationZero R f hf ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
          (PresheafOfModules.unit (R ⋙ forget₂ CommRingCat RingCat))).inv :=
  HomologicalComplex.mkHomToSingle_f _ fun i hi => by simp at hi

/-- In degree zero, the augmentation of the `ℤ`-indexed presheaf of Čech complexes is the
identification of its degree-zero term with that of the `ℕ`-indexed complex, followed by
`cechPresheafAugmentationZero` and the identification of the degree-zero term of the single
complex on the unit with the unit. -/
theorem cechPresheafAugmentation_f_zero :
    (cechPresheafAugmentation R f hf).f 0 =
      ((cechPresheafComplexNat R f hf).extendXIso ComplexShape.embeddingUpNat
          (show ComplexShape.embeddingUpNat.f 0 = (0 : ℤ) from rfl)).hom ≫
        cechPresheafAugmentationZero R f hf ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
            (PresheafOfModules.unit (R ⋙ forget₂ CommRingCat RingCat))).inv := by
  have h1 : (cechPresheafAugmentation R f hf).f 0 =
      (HomologicalComplex.extendMap (cechPresheafAugmentationNat R f hf)
          ComplexShape.embeddingUpNat).f 0 ≫
        (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
            (PresheafOfModules.unit (R ⋙ forget₂ CommRingCat RingCat)) 0 0
            (show ComplexShape.embeddingUpNat.f 0 = (0 : ℤ) from rfl)).hom.f 0 := rfl
  rw [h1, HomologicalComplex.extendSingleIso_hom_f,
    HomologicalComplex.extendMap_f _ _ (show ComplexShape.embeddingUpNat.f 0 = (0 : ℤ) from rfl),
    cechPresheafAugmentationNat_f_zero]
  exact CategoryTheory.Iso.comp_assoc_cancel_two _ _ _ _ _

end Stacks.CechPresheaf

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- The augmentation of the degree-zero term of the presheaf of Čech complexes onto `𝒪`. -/
def cechPresheafAugmentationZero :
    cechPresheafTerm X f 0 ⟶
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).val :=
  Stacks.CechPresheaf.cechPresheafAugmentationZero X.O.obj (cechFamily X f) (cechFamily_map X f)

/-- The identification of the degree-zero term of the `ℤ`-indexed presheaf of Čech complexes
with the degree-zero term of the `ℕ`-indexed one. -/
def cechPresheafComplexXZeroIso :
    (cechPresheafComplex X f).X 0 ≅ cechPresheafTerm X f 0 :=
  (cechPresheafComplexNat X f).extendXIso ComplexShape.embeddingUpNat
    (show ComplexShape.embeddingUpNat.f 0 = (0 : ℤ) from rfl)

omit [HasWeakSheafify X.J CommRingCat] in
/-- In degree zero, the augmentation of the `ℤ`-indexed presheaf of Čech complexes is
`cechPresheafComplexXZeroIso` followed by `cechPresheafAugmentationZero` and the identification
of the degree-zero term of the single complex on `𝒪` with `𝒪`. -/
theorem cechPresheafAugmentation_f_zero :
    (cechPresheafAugmentation X f).f 0 =
      (cechPresheafComplexXZeroIso X f).hom ≫ cechPresheafAugmentationZero X f ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
          (PresheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj)).inv :=
  Stacks.CechPresheaf.cechPresheafAugmentation_f_zero X.O.obj (cechFamily X f)
    (cechFamily_map X f)

/-- The canonical map `𝒪 ⟶ Č^0` at the presheaf level: into the summand at `∅`. -/
def unitToCechPresheafTermZero :
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).val ⟶
      cechPresheafTerm X f 0 :=
  unitToCechSummandPresheaf X f ∅ ≫ cechSummandInclusion X f 0 default

omit [HasWeakSheafify X.J CommRingCat] in
/-- The degree-zero Čech augmentation of the presheaf of complexes is split by the inclusion
`unitToCechPresheafTermZero` of the summand at `∅`. -/
theorem unitToCechPresheafTermZero_comp_augmentation :
    unitToCechPresheafTermZero X f ≫ cechPresheafAugmentationZero X f =
      𝟙 (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))).val := by
  refine PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext (LinearMap.ext_ring ?_)
  exact Stacks.CechPresheaf.cechLocAugmentationEmpty_app_mk X.O.obj (cechFamily X f)
    (cechFamily_map X f) V 1

omit [HasWeakSheafify X.J CommRingCat] in
/-- The projection of `unitToCechPresheafTermZero` onto the summand indexed by `A` is the
canonical map `𝒪 ⟶ 𝒪_{f_A}`. -/
theorem unitToCechPresheafTermZero_comp_cechTermProj (A : AlternatingCech.Idx r 0) :
    unitToCechPresheafTermZero X f ≫ cechTermProj X f 0 A =
      unitToCechSummandPresheaf X f A.1 := by
  obtain rfl : A = default := Subsingleton.elim A default
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun m => unitToCechSummandPresheaf X f ∅ ≫ m)
      (cechSummandInclusion_comp_cechSummandProjection_self X f 0 default)).trans
      (Category.comp_id _))

/-- The canonical map `𝒪 ⟶ Č^0` into the degree-zero term of the `ℤ`-indexed presheaf of Čech
complexes. -/
def unitToCechPresheafComplexZero :
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).val ⟶
      (cechPresheafComplex X f).X 0 :=
  unitToCechPresheafTermZero X f ≫ (cechPresheafComplexXZeroIso X f).inv

/-- The canonical map `𝒪 ⟶ K(f)^0` into the degree-zero term of the object of
[Stacks, Tag 099E]: the inclusion of the summand at `∅`, sheafified. -/
def unitToSheafifiedCechZero :
    SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶ (sheafifiedCech X f).X 0 :=
  toModuleSheafification (unitToCechPresheafComplexZero X f)

omit [HasWeakSheafify X.J CommRingCat] in
/-- In degree zero, the augmentation of the sheafified presheaf of Čech complexes is the
sheafification of `cechPresheafComplexXZeroIso` followed by `cechPresheafAugmentationZero`, then
the counit of the sheafification adjunction at `𝒪`, then the identification of the degree-zero
term of the single complex on `𝒪` with `𝒪`. -/
theorem sheafifiedCechAugmentation_f_zero :
    (sheafifiedCechAugmentation X f).f 0 =
      (moduleSheafificationFunctor X).map ((cechPresheafComplexXZeroIso X f).hom ≫
          cechPresheafAugmentationZero X f) ≫
        (PresheafOfModules.sheafificationAdjunction.{u}
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).counit.app
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
            (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).inv := by
  have h1 : (sheafifiedCechAugmentation X f).f 0 =
      (moduleSheafificationFunctor X).map ((cechPresheafAugmentation X f).f 0) ≫
        ((HomologicalComplex.singleMapHomologicalComplex (moduleSheafificationFunctor X)
            (ComplexShape.up ℤ) 0).hom.app
          (PresheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj)).f 0 ≫
        ((HomologicalComplex.single
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (ComplexShape.up ℤ) 0).map ((PresheafOfModules.sheafificationAdjunction.{u}
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).counit.app
                (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).f 0 :=
    rfl
  rw [h1, cechPresheafAugmentation_f_zero,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    HomologicalComplex.single_map_f_self]
  exact CategoryTheory.Iso.map_comp_inv_cancel _ _ _ _ _ _

omit [HasWeakSheafify X.J CommRingCat] [HasSheafify X.J AddCommGrpCat] in
/-- The counit of the sheafification adjunction at a sheaf of modules undoes the canonical map
induced by the identity. -/
theorem toModuleSheafification_id_comp_counit
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    toModuleSheafification (𝟙 F.val) ≫
        (PresheafOfModules.sheafificationAdjunction.{u}
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).counit.app F =
      𝟙 F :=
  (toModuleSheafification_comp_eq_iff (𝟙 F.val) (𝟙 F) _).2
    ((Category.id_comp _).trans
      ((congrArg (fun m => (PresheafOfModules.sheafificationAdjunction.{u}
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).homEquiv F.val F m)
          (Category.comp_id _)).symm.trans
        (homEquiv_sheafification_counit_comp (𝟙 F))))

omit [HasWeakSheafify X.J CommRingCat] [HasSheafify X.J AddCommGrpCat] in
/-- If `can ≫ ψ = χ`, then the map into the sheafification induced by `can`, followed by the
sheafification of `ψ` and `g`, is the map induced by `χ` followed by `g`. -/
theorem toModuleSheafification_comp_map_comp
    {P Q : PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj}
    {T F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (can : F.val ⟶ P)
    {ψ : P ⟶ Q} {χ : F.val ⟶ Q}
    (hχ : can ≫ ψ = χ) (g : (moduleSheafificationFunctor X).obj Q ⟶ T) :
    toModuleSheafification can ≫ (moduleSheafificationFunctor X).map ψ ≫ g =
      toModuleSheafification χ ≫ g := by
  rw [← Category.assoc, toModuleSheafification_comp_map, hχ]

omit [HasWeakSheafify X.J CommRingCat] [HasSheafify X.J AddCommGrpCat] in
/-- If `can ≫ ψ = 𝟙 F.val`, then the map into the sheafification induced by `can`, followed by
the sheafification of `ψ`, the counit at `F` and `g`, is `g`. -/
theorem toModuleSheafification_comp_map_comp_counit_comp
    {P : PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj}
    {T F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (can : F.val ⟶ P) {ψ : P ⟶ F.val} (hψ : can ≫ ψ = 𝟙 F.val) (g : F ⟶ T) :
    toModuleSheafification can ≫ (moduleSheafificationFunctor X).map ψ ≫
        ((PresheafOfModules.sheafificationAdjunction.{u}
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).counit.app F ≫ g) = g := by
  rw [toModuleSheafification_comp_map_comp X can hψ]
  exact CategoryTheory.Iso.comp_eq_id_comp (toModuleSheafification_id_comp_counit X F) g

omit [HasWeakSheafify X.J CommRingCat] in
/-- **The canonical map `𝒪 ⟶ K(f)^0` splits the augmentation `K(f) ⟶ 𝒪` in degree zero.** -/
theorem unitToSheafifiedCechZero_comp_sheafifiedCechAugmentation_f_zero :
    unitToSheafifiedCechZero X f ≫ (sheafifiedCechAugmentation X f).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).inv :=
  (congrArg (fun m => unitToSheafifiedCechZero X f ≫ m)
      (sheafifiedCechAugmentation_f_zero X f)).trans
    (toModuleSheafification_comp_map_comp_counit_comp X
      (unitToCechPresheafComplexZero X f)
      ((CategoryTheory.Iso.comp_inv_comp_hom_comp (unitToCechPresheafTermZero X f)
          (cechPresheafComplexXZeroIso X f) (cechPresheafAugmentationZero X f)).trans
        (unitToCechPresheafTermZero_comp_augmentation X f))
      _)

omit [HasWeakSheafify X.J CommRingCat] in
/-- In degree zero, the identification of the presheaf of Čech complexes with the alternating
Čech complex is `cechPresheafComplexXZeroIso` followed by `cechPresheafTermIsoTerm` in degree
zero. -/
theorem cechPresheafComplexIsoAlternating_hom_f_zero :
    (cechPresheafComplexIsoAlternating X f).hom.f 0 =
      (cechPresheafComplexXZeroIso X f).hom ≫ (cechPresheafTermIsoTerm X f 0).hom :=
  congrArg Iso.hom (HomologicalComplex.extendUpNatXIso_natCast (cechPresheafComplexNat X f)
    (AlternatingCech.complex (cechSummandFunctor X f))
    (fun _ hp => AlternatingCech.isZero_complex_X_of_neg _ hp) (cechTermIso X f) 0)

/-- **The identification of the two spellings carries the canonical map `𝒪 ⟶ K(f)^0` to the
augmentation `𝒪 ⟶ Č(f)^0`.** Both are determined by their components at the subsets of
cardinality zero, where the only one is `∅` and both are the canonical map `𝒪 ⟶ 𝒪_{f_∅}`. -/
theorem unitToSheafifiedCechZero_comp_iso_hom_f_zero :
    unitToSheafifiedCechZero X f ≫ (sheafifiedCechIsoExtendedAlternatingCech X f).hom.f 0 =
      extendedAlternatingCechAugmentation X f := by
  refine Pi.hom_ext _ _ fun A => ?_
  have hproj : (sheafifiedCechIsoExtendedAlternatingCech X f).hom.f 0 ≫
        Pi.π (fun S : AlternatingCech.Idx r 0 =>
          awayModule X (prodGlobalSection f S.1)) A =
      (moduleSheafificationFunctor X).map ((cechPresheafComplexIsoAlternating X f).hom.f 0 ≫
          Pi.π (fun S : AlternatingCech.Idx r 0 => (cechSummandFunctor X f).obj S.1) A) ≫
        (cechSummandSheafificationIso X f A.1).hom := by
    show ((moduleSheafificationFunctor X).map ((cechPresheafComplexIsoAlternating X f).hom.f 0) ≫
        (AlternatingCech.mapTermIso (moduleSheafificationFunctor X) (cechSummandFunctor X f)
            (0 : ℤ)).hom ≫
          AlternatingCech.mapTerm (cechSummandFunctorSheafificationIso X f).hom (0 : ℤ)) ≫
        Pi.π (fun S : AlternatingCech.Idx r 0 =>
          awayModule X (prodGlobalSection f S.1)) A = _
    exact CategoryTheory.Iso.map_comp_comp_comp_pi _ _ _ _ _ _ _ _
      (AlternatingCech.mapTerm_comp_pi (cechSummandFunctorSheafificationIso X f).hom 0 A)
      (AlternatingCech.mapTermIso_hom_comp_pi (moduleSheafificationFunctor X)
        (cechSummandFunctor X f) 0 A)
  have hchi : unitToCechPresheafComplexZero X f ≫
        ((cechPresheafComplexIsoAlternating X f).hom.f 0 ≫
          Pi.π (fun S : AlternatingCech.Idx r 0 => (cechSummandFunctor X f).obj S.1) A) =
      unitToCechSummandPresheaf X f A.1 := by
    rw [cechPresheafComplexIsoAlternating_hom_f_zero]
    refine (congrArg (unitToCechPresheafComplexZero X f ≫ ·) (Category.assoc _ _ _)).trans
      ((CategoryTheory.Iso.comp_inv_comp_hom_comp (unitToCechPresheafTermZero X f)
        (cechPresheafComplexXZeroIso X f) _).trans ?_)
    exact (congrArg (unitToCechPresheafTermZero X f ≫ ·)
      (cechPresheafTermIsoTerm_hom_comp_pi X f 0 A)).trans
      (unitToCechPresheafTermZero_comp_cechTermProj X f A)
  exact ((Category.assoc _ _ _).trans
    ((congrArg (fun m => unitToSheafifiedCechZero X f ≫ m) hproj).trans
      ((toModuleSheafification_comp_map_comp X _ hchi _).trans
        (toModuleSheafification_comp_cechSummandSheafificationIso X f A.1)))).trans
    (extendedAlternatingCechAugmentation_comp_pi X f A).symm

/-- **The identification of the two Čech complexes of [Stacks, Tag 099E] respects the
augmentations.** The identification of the object the tag constructs with the complex it
displays carries the augmentation `K(f) ⟶ 𝒪` of the first onto the augmentation `Č(f) ⟶ 𝒪` of
the second.

Both maps land in `𝒪` placed in degree zero, so both are determined in degree zero; there both
factor through the canonical map `𝒪 ⟶ K(f)^0`, which is invertible, and after it both are the
identity of `𝒪`. -/
theorem sheafifiedCechIsoExtendedAlternatingCech_hom_comp_cechAugmentation :
    (sheafifiedCechIsoExtendedAlternatingCech X f).hom ≫ cechAugmentation X f =
      sheafifiedCechAugmentation X f := by
  have : IsIso ((sheafifiedCechIsoExtendedAlternatingCech X f).hom.f 0) :=
    inferInstanceAs (IsIso ((HomologicalComplex.eval
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ) 0).map (sheafifiedCechIsoExtendedAlternatingCech X f).hom))
  have hinv : extendedAlternatingCechAugmentation X f ≫ cechAugmentationZero X f =
      𝟙 (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    extendedAlternatingCechAugmentation_comp_cechAugmentationZero X f
  have he : IsIso (extendedAlternatingCechAugmentation X f) :=
    ⟨cechAugmentationZero X f, hinv,
      cechAugmentationZero_comp_extendedAlternatingCechAugmentation X f⟩
  have : IsIso (unitToSheafifiedCechZero X f ≫
      (sheafifiedCechIsoExtendedAlternatingCech X f).hom.f 0) := by
    rw [unitToSheafifiedCechZero_comp_iso_hom_f_zero]
    exact he
  have : IsIso (unitToSheafifiedCechZero X f) :=
    IsIso.of_isIso_comp_right _ ((sheafifiedCechIsoExtendedAlternatingCech X f).hom.f 0)
  refine HomologicalComplex.to_single_hom_ext ?_
  refine (cancel_epi (unitToSheafifiedCechZero X f)).1 ?_
  exact ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun m => m ≫ (cechAugmentation X f).f 0)
        (unitToSheafifiedCechZero_comp_iso_hom_f_zero X f)).trans
      ((congrArg (fun m => extendedAlternatingCechAugmentation X f ≫ m)
          (cechAugmentation_f_zero X f)).trans
        (CategoryTheory.Iso.comp_eq_id_comp hinv _)))).trans
    (unitToSheafifiedCechZero_comp_sheafifiedCechAugmentation_f_zero X f).symm

end AlgebraicGeometry.RingedSite

end
