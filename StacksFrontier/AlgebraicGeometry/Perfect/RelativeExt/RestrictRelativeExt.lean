module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExt.RestrictTarget
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExt.PartACore
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PullbackFlatness
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExt.PullbackTensorSupport

/-!
# Restricting the relative `Ext` groups of [Stacks, Tag 08IF] to an open subscheme

Let `f : X ⟶ S` be a morphism of schemes, `j : U ⟶ X` an open immersion, `𝒢` a complex of
`𝒪_X`-modules and `E` an object of `D(𝒪_X)`. Restriction to `U` gives maps

`Ext^i_{𝒪_X}(E, 𝒢 ⊗ f^*ℱ) ⟶ Ext^i_{𝒪_U}(E|_U, 𝒢|_U ⊗ (f|_U)^*ℱ)`,

natural in the `𝒪_S`-module `ℱ` and compatible with the boundary maps of short exact sequences.
They are bijective when the terms of `𝒢` vanish outside a closed subset of `X` contained in `U`.
This is the step "we may replace `X` by a quasi-compact open neighbourhood of the support of
`𝒢`" of the proof of [Stacks, Tag 08IF].

Restriction to `U` is the functor `D(j^*)` induced by the exact functor `j^*`; on `D(𝒪_X)` it is
the derived pullback `Lj^*`
(`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso`).

## Main definitions

* `Stacks.Cohomology.RelativeExt.restrictDerived`: `D(j^*) : D(𝒪_X) ⥤ D(𝒪_U)`.
* `Stacks.Cohomology.RelativeExt.restrictRelativeExt`: the restriction map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingedSpaceModuleAdjunction
open TopologicalSpace

universe u

namespace Stacks.Cohomology.RelativeExt

attribute [local instance] HasDerivedCategory.standard

variable {X S U : Scheme.{u}} (f : X ⟶ S) (j : U ⟶ X) [IsOpenImmersion j]

/-- The underlying morphism of sheafed spaces of an open immersion of schemes is an open
immersion. -/
theorem isOpenImmersion_toShHom : SheafedSpace.IsOpenImmersion j.toLRSHom.toShHom :=
  (inferInstance : IsOpenImmersion j)

attribute [local instance] isOpenImmersion_toShHom

/-- The pullback of modules `j^*` along an open immersion preserves finite limits. -/
theorem modulePullback_preservesFiniteLimits :
    PreservesFiniteLimits (modulePullback j.toLRSHom.toShHom) :=
  (modulePullback j.toLRSHom.toShHom).preservesFiniteLimits_of_preservesHomology

attribute [local instance] modulePullback_preservesFiniteLimits

/-- **Restriction to `U`**, `D(j^*) : D(𝒪_X) ⥤ D(𝒪_U)`, induced by the exact functor `j^*`. -/
abbrev restrictDerived : DStd X ⥤ DStd U :=
  (modulePullback j.toLRSHom.toShHom).mapDerivedCategory

variable {G : CochainComplex (TModules X.toRingedSpace) ℤ}


/-- `j^*` on complexes, in the spelling of the complexes of [Stacks, Tag 08IF], is additive. -/
instance pullbackComplexFunctor_additive' :
    ((modulePullback j.toLRSHom.toShHom).mapHomologicalComplex (ComplexShape.up ℤ) :
      CochainComplex (TModules X.toRingedSpace) ℤ ⥤
        CochainComplex (TModules U.toRingedSpace) ℤ).Additive :=
  @Functor.map_homogical_complex_additive _ _ _ _ _ _ _ (modulePullback j.toLRSHom.toShHom)
    (modulePullback_additive _) _

/-- `j^*` on complexes, in the spelling of the complexes of [Stacks, Tag 08IF], preserves zero
morphisms. -/
instance pullbackComplexFunctor_preservesZeroMorphisms' :
    ((modulePullback j.toLRSHom.toShHom).mapHomologicalComplex (ComplexShape.up ℤ) :
      CochainComplex (TModules X.toRingedSpace) ℤ ⥤
        CochainComplex (TModules U.toRingedSpace) ℤ).PreservesZeroMorphisms :=
  @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _ (pullbackComplexFunctor_additive' j)


variable (G) in
/-- **`𝒢|_U`**, the complex of `𝒪_U`-modules `j^*𝒢`. -/
abbrev restrictComplex : CochainComplex (TModules U.toRingedSpace) ℤ :=
  pullbackComplex j.toLRSHom.toShHom G

variable (G) in
/-- `D(j^*)(𝒢 ⊗ f^*ℱ) ≅ 𝒢|_U ⊗ (f|_U)^*ℱ` in `D(𝒪_U)`. -/
def restrictTargetDerivedIso (F : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) :
    (restrictDerived j).obj
        (DerivedCategory.Q.obj ((relativeExtTargetFunctor f.toLRSHom.toShHom G).obj F)) ≅
      DerivedCategory.Q.obj
        ((relativeExtTargetFunctor (j ≫ f).toLRSHom.toShHom (restrictComplex j G)).obj F) :=
  (Functor.mapDerivedCategoryFactors (modulePullback j.toLRSHom.toShHom)).app _ ≪≫
    DerivedCategory.Q.mapIso
      ((restrictTargetIso j.toLRSHom.toShHom f.toLRSHom.toShHom G).app F).symm

variable (G) in
/-- **Restriction of the relative `Ext` groups to `U`**:
`Ext^i_{𝒪_X}(E, 𝒢 ⊗ f^*ℱ) ⟶ Ext^i_{𝒪_U}(E|_U, 𝒢|_U ⊗ (f|_U)^*ℱ)`. -/
def restrictRelativeExt (E : DStd X) (F : SheafOfModules.{u} (structureSheafRing S.toRingedSpace))
    (i : ℤ) :
    relativeExtGroup f G E F i →+
      relativeExtGroup (j ≫ f) (restrictComplex j G) ((restrictDerived j).obj E) F i where
  toFun y := y.map (restrictDerived j) ≫ ((restrictTargetDerivedIso f j G F).hom)⟦i⟧'
  map_zero' := by
    change ShiftedHom.map (0 : ShiftedHom _ _ i) _ ≫ _ = 0
    rw [ShiftedHom.map_zero, zero_comp]
  map_add' y z := by
    change ShiftedHom.map (y + z) _ ≫ _ = ShiftedHom.map y _ ≫ _ + ShiftedHom.map z _ ≫ _
    rw [ShiftedHom.map_add, Preadditive.add_comp]

/-- The restriction map sends `y` to `D(j^*)(y)` composed with the shift of the isomorphism
`D(j^*)(𝒢 ⊗ f^*ℱ) ≅ 𝒢|_U ⊗ (f|_U)^*ℱ`. -/
theorem restrictRelativeExt_apply (E : DStd X)
    (F : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) (i : ℤ)
    (y : relativeExtGroup f G E F i) :
    restrictRelativeExt f j G E F i y =
      y.map (restrictDerived j) ≫ ((restrictTargetDerivedIso f j G F).hom)⟦i⟧' := rfl

/-- The isomorphism `D(j^*)(𝒢 ⊗ f^*ℱ) ≅ 𝒢|_U ⊗ (f|_U)^*ℱ` is natural in the `𝒪_S`-module `ℱ`. -/
theorem restrictTargetDerivedIso_hom_naturality
    {F F' : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)} (v : F ⟶ F') :
    (restrictDerived j).map
        (DerivedCategory.Q.map ((relativeExtTargetFunctor f.toLRSHom.toShHom G).map v)) ≫
        (restrictTargetDerivedIso f j G F').hom =
      (restrictTargetDerivedIso f j G F).hom ≫
        DerivedCategory.Q.map
          ((relativeExtTargetFunctor (j ≫ f).toLRSHom.toShHom (restrictComplex j G)).map v) := by
  have h₁ := Functor.mapDerivedCategoryFactors_hom_naturality
    (modulePullback j.toLRSHom.toShHom) ((relativeExtTargetFunctor f.toLRSHom.toShHom G).map v)
  have h₂ := (DerivedCategory.Q.map_comp _ _).symm.trans ((congrArg DerivedCategory.Q.map
    ((restrictTargetIso j.toLRSHom.toShHom f.toLRSHom.toShHom G).inv.naturality v)).trans
      (DerivedCategory.Q.map_comp _ _))
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₁).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₂).trans (Category.assoc _ _ _).symm)))

/-- **The restriction map is natural in the `𝒪_S`-module `ℱ`.** -/
theorem restrictRelativeExt_naturality (E : DStd X) (i : ℤ)
    {F F' : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)} (v : F ⟶ F')
    (y : relativeExtGroup f G E F i) :
    restrictRelativeExt f j G E F' i
        (y ≫ (DerivedCategory.Q.map ((relativeExtTargetFunctor f.toLRSHom.toShHom G).map v))⟦i⟧') =
      restrictRelativeExt f j G E F i y ≫
        (DerivedCategory.Q.map
          ((relativeExtTargetFunctor (j ≫ f).toLRSHom.toShHom
            (restrictComplex j G)).map v))⟦i⟧' := by
  rw [restrictRelativeExt_apply, restrictRelativeExt_apply]
  simp only [ShiftedHom.map, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [Functor.commShiftIso_hom_naturality_assoc, ← CategoryTheory.Functor.map_comp,
    restrictTargetDerivedIso_hom_naturality, CategoryTheory.Functor.map_comp]

variable {f j} in
/-- **`𝒢|_U` is bounded and flat over `S`** when `𝒢` is: pullback along an open immersion is
additive, and flatness over the base is checked at stalks (Stacks 02JZ). -/
theorem isBoundedFlatOver_restrictComplex (hG : IsBoundedFlatOver f.toLRSHom.toShHom G) :
    IsBoundedFlatOver (j ≫ f).toLRSHom.toShHom (restrictComplex j G) where
  bounded := by
    obtain ⟨a, b, ha, hb⟩ := hG.bounded
    refine ⟨a, b, (CochainComplex.isStrictlyGE_iff _ a).2 fun i hi => ?_,
      (CochainComplex.isStrictlyLE_iff _ b).2 fun i hi => ?_⟩
    · exact Functor.map_isZero _ ((CochainComplex.isStrictlyGE_iff G a).1 ha i hi)
    · exact Functor.map_isZero _ ((CochainComplex.isStrictlyLE_iff G b).1 hb i hi)
  isFlatOver q x :=
    (isFlatOverAt_iff_modulePullback_isFlatOverAt j f (G.X q) x
      (Flat.stalkMap j x)).mp (hG.isFlatOver q (j.base x))

variable {j} in
/-- `𝒢|_U` vanishes in degrees `< b` when `𝒢` does. -/
theorem isStrictlyGE_restrictComplex (b : ℤ) (hb : G.IsStrictlyGE b) :
    (restrictComplex j G).IsStrictlyGE b :=
  (CochainComplex.isStrictlyGE_iff _ b).2 fun i hi =>
    @Functor.map_isZero _ _ _ _ _ _ (modulePullback j.toLRSHom.toShHom)
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _ (modulePullback_additive _)) _
      ((CochainComplex.isStrictlyGE_iff G b).1 hb i hi)

/-- Conjugating a composite of shifted morphisms by isomorphisms. -/
theorem _root_.CategoryTheory.ShiftedHom.comp_conj' {C : Type*} [Category C] [HasShift C ℤ]
    {W Y₃ Y₁ Z₃ Z₁ : C} {n m : ℤ} (x : ShiftedHom W Y₃ n) (δ : ShiftedHom Y₃ Y₁ (1 : ℤ))
    (δ' : ShiftedHom Z₃ Z₁ (1 : ℤ)) (e₃ : Y₃ ≅ Z₃) (e₁ : Y₁ ≅ Z₁)
    (hδ : δ' ≫ e₁.inv⟦(1 : ℤ)⟧' = e₃.inv ≫ δ) (h : 1 + n = m) :
    x.comp δ h ≫ e₁.hom⟦m⟧' = ShiftedHom.comp (x ≫ e₃.hom⟦n⟧') δ' h := by
  have hδ' : δ ≫ e₁.hom⟦(1 : ℤ)⟧' = e₃.hom ≫ δ' := by
    rw [← cancel_epi e₃.inv, Iso.inv_hom_id_assoc, ← reassoc_of% hδ,
      ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.comp_id]
  simp only [ShiftedHom.comp, Category.assoc]
  rw [← (shiftFunctorAdd' C 1 n m h).inv.naturality e₁.hom, Functor.comp_map,
    ← CategoryTheory.Functor.map_comp_assoc, ← CategoryTheory.Functor.map_comp_assoc, hδ',
    CategoryTheory.Functor.map_comp_assoc]

/-- In a category with a shift by `ℤ`, if `Dδ = fh₃ ≫ δj ≫ fi₁⟦1⟧' ≫ chi`, `δU ≫ P₁⟦1⟧' = P₃ ≫ δj`,
`fi₃ ≫ fh₃ = 𝟙 e` and `chi ≫ ch = 𝟙 _`, then `δU ≫ (P₁ ≫ fi₁)⟦1⟧' = (P₃ ≫ fi₃) ≫ (Dδ ≫ ch)`. -/
theorem boundary_conj_aux {C : Type*} [Category C] [HasShift C ℤ] {a b c d e g w : C}
    (δU : a ⟶ b⟦(1 : ℤ)⟧) (P₁ : b ⟶ c) (fi₁ : c ⟶ d) (P₃ : a ⟶ e) (fi₃ : e ⟶ g)
    (fh₃ : g ⟶ e) (δj : e ⟶ c⟦(1 : ℤ)⟧) (Dδ : g ⟶ w) (ch : w ⟶ d⟦(1 : ℤ)⟧)
    (chi : d⟦(1 : ℤ)⟧ ⟶ w)
    (key : Dδ = fh₃ ≫ δj ≫ fi₁⟦(1 : ℤ)⟧' ≫ chi) (hnat : δU ≫ P₁⟦(1 : ℤ)⟧' = P₃ ≫ δj)
    (hf : fi₃ ≫ fh₃ = 𝟙 e) (hc : chi ≫ ch = 𝟙 _) :
    δU ≫ (P₁ ≫ fi₁)⟦(1 : ℤ)⟧' = (P₃ ≫ fi₃) ≫ (Dδ ≫ ch) := by
  rw [key, CategoryTheory.Functor.map_comp, reassoc_of% hnat]
  simp only [Category.assoc, reassoc_of% hf, hc, Category.comp_id]

/-- **The restriction map is compatible with the boundary maps** of a short exact sequence
`0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` of `𝒪_S`-modules. -/
theorem restrictRelativeExt_boundary (hG : IsBoundedFlatOver f.toLRSHom.toShHom G) (E : DStd X)
    {A : ShortComplex (SheafOfModules.{u} (structureSheafRing S.toRingedSpace))}
    (hA : A.ShortExact) (n m : ℤ) (h : 1 + n = m) (y : relativeExtGroup f G E A.X₃ n) :
    restrictRelativeExt f j G E A.X₁ m (y.comp (relativeExtBoundary hG hA) h) =
      (restrictRelativeExt f j G E A.X₃ n y).comp
        (relativeExtBoundary (isBoundedFlatOver_restrictComplex hG) hA) h := by
  refine (congrArg (· ≫ ((restrictTargetDerivedIso f j G A.X₁).hom)⟦m⟧')
    (ShiftedHom.map_comp _ _ h (restrictDerived j))).trans ?_
  refine ShiftedHom.comp_conj' _ _ _ (restrictTargetDerivedIso f j G A.X₃)
    (restrictTargetDerivedIso f j G A.X₁) ?_ h
  let ρ := restrictTargetIso j.toLRSHom.toShHom f.toLRSHom.toShHom G
  have hS := shortExact_relativeExtTarget _ G hG.isFlatOver hA
  have key := DerivedCategory.map_triangleOfSESδ (modulePullback j.toLRSHom.toShHom) hS
  have i1 : ((modulePullback j.toLRSHom.toShHom).mapHomologicalComplex
    (ComplexShape.up ℤ)).PreservesZeroMorphisms := inferInstance
  have i2 : PreservesFiniteLimits ((modulePullback j.toLRSHom.toShHom).mapHomologicalComplex
    (ComplexShape.up ℤ)) := inferInstance
  have i3 : PreservesFiniteColimits ((modulePullback j.toLRSHom.toShHom).mapHomologicalComplex
    (ComplexShape.up ℤ)) := inferInstance
  have hjS := @ShortComplex.ShortExact.map_of_exact _ _ _ _ _ _ _ hS
    ((modulePullback j.toLRSHom.toShHom).mapHomologicalComplex (ComplexShape.up ℤ)) i1 i2 i3
  have hSU := shortExact_relativeExtTarget _ (restrictComplex j G)
    (isBoundedFlatOver_restrictComplex (f := f) (j := j) hG).isFlatOver hA
  let φ : A.map (relativeExtTargetFunctor (j ≫ f).toLRSHom.toShHom (restrictComplex j G)) ⟶
      @ShortComplex.map _ _ _ _ _ _ (A.map (relativeExtTargetFunctor f.toLRSHom.toShHom G))
        ((modulePullback j.toLRSHom.toShHom).mapHomologicalComplex (ComplexShape.up ℤ)) i1 :=
    { τ₁ := ρ.hom.app A.X₁
      τ₂ := ρ.hom.app A.X₂
      τ₃ := ρ.hom.app A.X₃
      comm₁₂ := (ρ.hom.naturality A.f).symm
      comm₂₃ := (ρ.hom.naturality A.g).symm }
  have hnat := DerivedCategory.triangleOfSESδ_naturality hSU hjS φ
  exact boundary_conj_aux (C := DStd U) _ _ _ _ _ _ _ _ _ _ key hnat (Iso.inv_hom_id_app _ _)
    (Iso.inv_hom_id_app _ _)

variable {f} in
/-- **`𝒢 ⊗ f^*ℱ` is supported where `𝒢` is**: if every term `𝒢^q` has vanishing stalks outside
`Z ⊆ X`, so has every cohomology sheaf of every shift of `𝒢 ⊗ f^*ℱ`. -/
theorem cohomologySupportedOn_relativeExtTarget_shift (Z : Set X)
    (hGZ : ∀ (q : ℤ) (x : X), x ∉ Z →
      IsZero (TopCat.Presheaf.stalk (X := X.carrier) (G.X q).val.presheaf x))
    (F : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) (i : ℤ) :
    Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn
      (structureSheafRing X.toRingedSpace) Z
      ((DerivedCategory.Q.obj ((relativeExtTargetFunctor f.toLRSHom.toShHom G).obj F))⟦i⟧) := by
  refine Stacks.Cohomology.PushforwardRestriction.cohomologySupportedOn_of_iso _ Z
    ((DerivedCategory.Q.commShiftIso i).app _) ?_
  intro k x hx
  rw [← AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj_iff]
  let T : CochainComplex (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ℤ :=
    ((relativeExtTargetFunctor f.toLRSHom.toShHom G).obj F)⟦i⟧
  refine IsZero.of_iso ?_
    ((AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing X.toRingedSpace) x).mapIso
      ((DerivedCategory.homologyFunctorFactors _ k).app T))
  refine isZero_stalk_homology_of_isZero_stalk_X x T (fun n => ?_) k
  let e : T.X n ≅ ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj
      ((modulePullback f.toLRSHom.toShHom).obj F)).obj (G.X (n + i)) :=
    ((sheafTensorFlip (X := X.toRingedSpace)).app (G.X (n + i))).app
      ((modulePullback f.toLRSHom.toShHom).obj F)
  have h0 : IsZero ((AlgebraicGeometry.SheafOfModules.stalkFunctor
      (structureSheafRing X.toRingedSpace) x).obj (G.X (n + i))) :=
    (AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj_iff _ x _).2 (hGZ (n + i) x hx)
  exact (isZero_stalk_sheafTensor_of_isZero_stalk_right x
    ((modulePullback f.toLRSHom.toShHom).obj F) (G.X (n + i)) h0).of_iso
      ((AlgebraicGeometry.SheafOfModules.stalkFunctor
        (structureSheafRing X.toRingedSpace) x).mapIso e)

/-- On morphisms, `D(j^*)` is `Lj^*` conjugated by the isomorphism `Lj^* ≅ D(j^*)`. -/
private theorem restrictDerived_map_eq {A M : DStd X} (φ : A ⟶ M) :
    (restrictDerived j).map φ =
      (Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso
          j.toLRSHom.toShHom).inv.app A ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          j.toLRSHom.toShHom).map φ ≫
        (Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso
          j.toLRSHom.toShHom).hom.app M := by
  rw [(Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso
    j.toLRSHom.toShHom).hom.naturality φ, Iso.inv_hom_id_app_assoc]

/-- **Restriction `D(j^*)` is bijective on maps `A ⟶ M` when `Lj^*` is**: the two functors are
isomorphic for an open immersion. -/
theorem bijective_restrictDerived_map_of (A M : DStd X)
    (hb : Function.Bijective (fun φ : A ⟶ M =>
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        j.toLRSHom.toShHom).map φ)) :
    Function.Bijective (fun φ : A ⟶ M => (restrictDerived j).map φ) := by
  let ι := Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso
    j.toLRSHom.toShHom
  have key : (fun φ : A ⟶ M => (restrictDerived j).map φ) = ⇑((ι.app A).homCongr (ι.app M)) ∘
      (fun φ : A ⟶ M =>
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          j.toLRSHom.toShHom).map φ) :=
    funext fun φ => restrictDerived_map_eq j φ
  rw [key]
  exact (Equiv.bijective _).comp hb

/-- **The restriction map is bijective when the derived pullback `Lj^*` is bijective on
morphisms** `E ⟶ (𝒢 ⊗ f^*ℱ)[i]`: on `D(𝒪_X)`, restriction is `Lj^*` up to the isomorphism
`Lj^* ≅ D(j^*)` of an open immersion. -/
theorem restrictRelativeExt_bijective_of (E : DStd X)
    (F : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) (i : ℤ)
    (hb : Function.Bijective (fun φ : E ⟶
      (DerivedCategory.Q.obj ((relativeExtTargetFunctor f.toLRSHom.toShHom G).obj F))⟦i⟧ =>
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          j.toLRSHom.toShHom).map φ)) :
    Function.Bijective (restrictRelativeExt f j G E F i) := by
  let ι := Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso
    j.toLRSHom.toShHom
  let w := ι.app
      ((DerivedCategory.Q.obj ((relativeExtTargetFunctor f.toLRSHom.toShHom G).obj F))⟦i⟧) ≪≫
    ((restrictDerived j).commShiftIso i).app _ ≪≫
      (shiftFunctor (DStd U) i).mapIso (restrictTargetDerivedIso f j G F)
  have key : ⇑(restrictRelativeExt f j G E F i) = ⇑((ι.app E).homCongr w) ∘
      (fun φ : E ⟶
        (DerivedCategory.Q.obj ((relativeExtTargetFunctor f.toLRSHom.toShHom G).obj F))⟦i⟧ =>
          (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            j.toLRSHom.toShHom).map φ) := by
    funext y
    rw [Function.comp_apply, Iso.homCongr_apply, restrictRelativeExt_apply, ShiftedHom.map,
      Category.assoc, restrictDerived_map_eq]
    simp only [Category.assoc]
    rfl
  rw [key]
  exact (Equiv.bijective _).comp hb

end Stacks.Cohomology.RelativeExt

end
