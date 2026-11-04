module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantWeakSerre
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.Monoidal
public import StacksFrontier.Homology.KFlat.BaseChange

/-!
# Change of rings for sheaves of modules over a ring

Let `(C, J)` be a site and `f : Λ →+* S` a homomorphism of commutative rings. Restriction of
scalars along `f`, applied sectionwise, carries sheaves of `S`-modules to sheaves of
`Λ`-modules; it has a left adjoint, extension of scalars `F ↦ (U ↦ S ⊗_Λ F(U))^#`, and a right
adjoint, coextension of scalars applied sectionwise. When `f` is surjective, restriction of
scalars is fully faithful, so extension of scalars after restriction is the identity.

These functors are compatible with constant sheaves, with restriction to a slice site and with
inverse images, and local constancy of finite type of a sheaf of `S`-modules can be tested after
restriction of scalars along a surjective `f`. The projection formula
`N ⊗_S (S ⊗_Λ F) ≅ N ⊗_Λ F` holds for sheaves `N` of `S`-modules and `F` of `Λ`-modules.

## Main definitions

* `Stacks.ModuleSheaf.restrictScalars`: restriction of scalars.
* `Stacks.ModuleSheaf.extendScalars`: extension of scalars.
* `Stacks.ModuleSheaf.coextendScalars`: coextension of scalars.
* `Stacks.ModuleSheaf.extendRestrictScalarsAdj`, `Stacks.ModuleSheaf.restrictCoextendScalarsAdj`:
  the two adjunctions.
* `Stacks.ModuleSheaf.fullyFaithfulRestrictScalars`: full faithfulness for surjective `f`.
* `Stacks.ModuleSheaf.restrictScalarsConstantSheafIso`,
  `Stacks.ModuleSheaf.extendScalarsConstantSheafIso`: compatibility with constant sheaves.
* `Stacks.ModuleSheaf.overPullbackCompExtendScalarsIso`: extension of scalars commutes with
  restriction to a slice site.
* `Stacks.ModuleSheaf.restrictScalarsSheafPullbackIso`: restriction of scalars commutes with
  inverse image along a continuous functor, for any choice of inverse images.
* `Stacks.ModuleSheaf.restrictScalarsTensorExtendScalarsIso`: the projection formula, with its
  objectwise forms `ModuleCat.restrictScalarsTensorExtendScalarsIso` and
  `Stacks.ModuleSheaf.presheafRestrictScalarsTensorExtendScalarsIso`.

## Main results

* `Stacks.ModuleSheaf.isFiniteTypeLocallyConstantModuleSheaf_restrictScalars_iff`: for
  surjective `f`, a sheaf of `S`-modules is locally constant of finite type exactly when its
  restriction of scalars is.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u v' u'

namespace Stacks.ModuleSheaf

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {Λ S : Type w} [CommRing Λ] [CommRing S] (f : Λ →+* S)

/-! ### The three functors -/

/-- Sectionwise restriction of scalars along `f` carries sheaves to sheaves. -/
instance hasSheafCompose_restrictScalars :
    J.HasSheafCompose (ModuleCat.restrictScalars.{w} f) := by
  have : PreservesLimitsOfSize.{v, max u v} (ModuleCat.restrictScalars.{w} f) :=
    (ModuleCat.extendRestrictScalarsAdj.{w} f).rightAdjoint_preservesLimits
  exact ⟨fun P hP ↦ Presheaf.isSheaf_comp_of_isSheaf J P _ hP⟩

/-- Sectionwise coextension of scalars along `f` carries sheaves to sheaves. -/
instance hasSheafCompose_coextendScalars :
    J.HasSheafCompose (ModuleCat.coextendScalars f :
      ModuleCat.{w} Λ ⥤ ModuleCat.{w} S) := by
  have : PreservesLimitsOfSize.{v, max u v} (ModuleCat.coextendScalars f :
      ModuleCat.{w} Λ ⥤ ModuleCat.{w} S) :=
    (ModuleCat.restrictCoextendScalarsAdj.{w} f).rightAdjoint_preservesLimits
  exact ⟨fun P hP ↦ Presheaf.isSheaf_comp_of_isSheaf J P _ hP⟩

/-- **Restriction of scalars** along `f`, from sheaves of `S`-modules to sheaves of
`Λ`-modules. -/
def restrictScalars : Sheaf J (ModuleCat.{w} S) ⥤ Sheaf J (ModuleCat.{w} Λ) :=
  sheafCompose J (ModuleCat.restrictScalars.{w} f)

/-- **Coextension of scalars** along `f`, applied sectionwise. -/
def coextendScalars : Sheaf J (ModuleCat.{w} Λ) ⥤ Sheaf J (ModuleCat.{w} S) :=
  sheafCompose J (ModuleCat.coextendScalars f :
      ModuleCat.{w} Λ ⥤ ModuleCat.{w} S)

/-- Restriction of scalars is left adjoint to coextension of scalars. -/
def restrictCoextendScalarsAdj : restrictScalars J f ⊣ coextendScalars J f :=
  Adjunction.restrictFullyFaithful
    ((ModuleCat.restrictCoextendScalarsAdj.{w} f).whiskerRight Cᵒᵖ)
    (fullyFaithfulSheafToPresheaf J _) (fullyFaithfulSheafToPresheaf J _) (Iso.refl _)
    (Iso.refl _)

/-- Restriction of scalars is a left adjoint. -/
instance : (restrictScalars J f).IsLeftAdjoint := (restrictCoextendScalarsAdj J f).isLeftAdjoint

/-- Restriction of scalars is faithful. -/
instance : (restrictScalars J f).Faithful :=
  inferInstanceAs (sheafCompose J (ModuleCat.restrictScalars.{w} f)).Faithful

/-- Restriction of scalars is additive. -/
instance : (restrictScalars J f).Additive where
  map_add := rfl

/-- Sectionwise restriction of scalars commutes with sheafification. -/
instance : J.PreservesSheafification (ModuleCat.restrictScalars.{w} f) :=
  Sheaf.preservesSheafification_of_adjunction J (ModuleCat.restrictCoextendScalarsAdj.{w} f)

/-- Sectionwise extension of scalars commutes with sheafification. -/
instance : J.PreservesSheafification (ModuleCat.extendScalars.{w, w, w} f) :=
  Sheaf.preservesSheafification_of_adjunction J (ModuleCat.extendRestrictScalarsAdj.{w} f)

section Extend

variable [UnivLE.{max u v, w}]

/-- **Extension of scalars** along `f`: the sheafification of `U ↦ S ⊗_Λ F(U)`. -/
def extendScalars : Sheaf J (ModuleCat.{w} Λ) ⥤ Sheaf J (ModuleCat.{w} S) :=
  Sheaf.composeAndSheafify J (ModuleCat.extendScalars.{w, w, w} f)

/-- Extension of scalars is left adjoint to restriction of scalars. -/
def extendRestrictScalarsAdj : extendScalars J f ⊣ restrictScalars J f :=
  Sheaf.adjunction J (ModuleCat.extendRestrictScalarsAdj.{w} f)

/-- Restriction of scalars is a right adjoint. -/
instance : (restrictScalars J f).IsRightAdjoint := (extendRestrictScalarsAdj J f).isRightAdjoint

/-- Extension of scalars is a left adjoint. -/
instance : (extendScalars J f).IsLeftAdjoint := (extendRestrictScalarsAdj J f).isLeftAdjoint

/-- Extension of scalars along `f` is additive. -/
instance : (extendScalars J f).Additive := by
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint (extendScalars J f)
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (extendScalars J f)
  exact Functor.additive_of_preservesBinaryBiproducts _

end Extend

/-! ### Surjective ring maps -/

variable {f} in
/-- Restriction of scalars along a surjective ring map is full: a `Λ`-linear map between
`S`-modules is `S`-linear. -/
theorem _root_.ModuleCat.full_restrictScalars_of_surjective (hf : Function.Surjective f) :
    (ModuleCat.restrictScalars.{w} f).Full where
  map_surjective {M N} g := by
    refine ⟨ModuleCat.ofHom
      { toFun := g.hom
        map_add' := map_add g.hom
        map_smul' := fun s x => ?_ }, rfl⟩
    obtain ⟨r, rfl⟩ := hf s
    exact g.hom.map_smul r x

variable {f} in
/-- **Restriction of scalars along a surjective ring map is fully faithful.** -/
def fullyFaithfulRestrictScalars (hf : Function.Surjective f) :
    (restrictScalars J f).FullyFaithful := by
  have := ModuleCat.full_restrictScalars_of_surjective hf
  exact Functor.FullyFaithful.ofFullyFaithful (sheafCompose J (ModuleCat.restrictScalars.{w} f))

variable {f} in
/-- For a surjective ring map, extension of scalars after restriction of scalars is the
identity. -/
def restrictScalarsCompExtendScalarsIso [UnivLE.{max u v, w}] (hf : Function.Surjective f) :
    restrictScalars J f ⋙ extendScalars J f ≅ 𝟭 _ := by
  have := (fullyFaithfulRestrictScalars J hf).full
  have := (fullyFaithfulRestrictScalars J hf).faithful
  exact asIso (extendRestrictScalarsAdj J f).counit

/-! ### Constant sheaves -/

section Constant

variable [UnivLE.{max u v, w}]

/-- Restriction of scalars of a constant sheaf is the constant sheaf on the restriction of
scalars. -/
def restrictScalarsConstantSheafIso :
    constantSheaf J (ModuleCat.{w} S) ⋙ restrictScalars J f ≅
      ModuleCat.restrictScalars.{w} f ⋙ constantSheaf J (ModuleCat.{w} Λ) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Functor.const Cᵒᵖ)
      (sheafComposeNatIso J (ModuleCat.restrictScalars.{w} f)
        (sheafificationAdjunction J _) (sheafificationAdjunction J _)).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.compConstIso Cᵒᵖ
      (ModuleCat.restrictScalars.{w} f)).symm _ ≪≫
    Functor.associator _ _ _

/-- Extension of scalars of a constant sheaf is the constant sheaf on the extension of
scalars. -/
def extendScalarsConstantSheafIso :
    constantSheaf J (ModuleCat.{w} Λ) ⋙ extendScalars J f ≅
      ModuleCat.extendScalars.{w, w, w} f ⋙ constantSheaf J (ModuleCat.{w} S) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Functor.const Cᵒᵖ)
      (presheafToSheafCompComposeAndSheafifyIso J (ModuleCat.extendScalars.{w, w, w} f)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.compConstIso Cᵒᵖ
      (ModuleCat.extendScalars.{w, w, w} f)).symm _ ≪≫
    Functor.associator _ _ _

end Constant

/-! ### Restriction to a slice site -/

section Over

variable [UnivLE.{max u v, w}]

/-- **Extension of scalars commutes with restriction to a slice site.** -/
def overPullbackCompExtendScalarsIso (U : C) :
    J.overPullback (ModuleCat.{w} Λ) U ⋙ extendScalars (J.over U) f ≅
      extendScalars J f ⋙ J.overPullback (ModuleCat.{w} S) U :=
  Functor.isoWhiskerLeft
    (sheafToPresheaf J (ModuleCat.{w} Λ) ⋙
      (Functor.whiskeringRight Cᵒᵖ _ _).obj (ModuleCat.extendScalars.{w, w, w} f))
    ((Over.forget U).pushforwardContinuousSheafificationCompatibility (ModuleCat.{w} S)
      (J.over U) J)

end Over

/-! ### Inverse images -/

section InverseImage

variable {D : Type u'} [Category.{v'} D] (K : GrothendieckTopology D)
  (G : C ⥤ D) [G.IsContinuous J K]

/-- Coextension of scalars commutes with direct image along a continuous functor, on the
nose. -/
def sheafPushforwardContinuousCompCoextendScalarsIso :
    G.sheafPushforwardContinuous (ModuleCat.{w} Λ) J K ⋙ coextendScalars J f ≅
      coextendScalars K f ⋙ G.sheafPushforwardContinuous (ModuleCat.{w} S) J K :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

variable {J K G}

/-- **Restriction of scalars commutes with inverse image** along a continuous functor `G`,
for any choices `LS`, `LΛ` of left adjoints of the direct images. -/
def restrictScalarsSheafPullbackIso
    {LS : Sheaf J (ModuleCat.{w} S) ⥤ Sheaf K (ModuleCat.{w} S)}
    {LΛ : Sheaf J (ModuleCat.{w} Λ) ⥤ Sheaf K (ModuleCat.{w} Λ)}
    (adjS : LS ⊣ G.sheafPushforwardContinuous (ModuleCat.{w} S) J K)
    (adjΛ : LΛ ⊣ G.sheafPushforwardContinuous (ModuleCat.{w} Λ) J K) :
    LS ⋙ restrictScalars K f ≅ restrictScalars J f ⋙ LΛ :=
  Adjunction.leftAdjointUniq (adjS.comp (restrictCoextendScalarsAdj K f))
    (((restrictCoextendScalarsAdj J f).comp adjΛ).ofNatIsoRight
      (sheafPushforwardContinuousCompCoextendScalarsIso J f K G))

end InverseImage

end

/-! ### The projection formula -/

section ProjectionFormula

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {Λ S : Type w} [CommRing Λ] [CommRing S] (f : Λ →+* S)

open MonoidalCategory

attribute [local instance] Sheaf.monoidalCategory

/-- The projection formula for modules: for an `S`-module `V` and a `Λ`-module `W`,
`V ⊗_S (S ⊗_Λ W) ≅ V ⊗_Λ W` as `Λ`-modules, naturally in both. -/
def _root_.ModuleCat.restrictScalarsTensorExtendScalarsIso :
    (𝟭 (ModuleCat.{w} S)).prod (ModuleCat.extendScalars.{w, w, w} f) ⋙ tensor _ ⋙
        ModuleCat.restrictScalars.{w} f ≅
      (ModuleCat.restrictScalars.{w} f).prod (𝟭 _) ⋙ tensor _ :=
  NatIso.ofComponents (fun X => projectionFormulaIso f X.1 X.2) (fun {X Y} g => by
    obtain ⟨α, β⟩ := g
    change (ModuleCat.restrictScalars f).map (α ⊗ₘ (ModuleCat.extendScalars f).map β) ≫ _ =
      _ ≫ ((ModuleCat.restrictScalars f).map α ⊗ₘ β)
    rw [tensorHom_def, tensorHom_def, Functor.map_comp, Category.assoc,
      projectionFormulaIso_natural_right, ← Category.assoc, projectionFormulaIso_natural_left,
      Category.assoc])

/-- The projection formula for presheaves of modules, computed objectwise. -/
def presheafRestrictScalarsTensorExtendScalarsIso :
    (𝟭 (Cᵒᵖ ⥤ ModuleCat.{w} S)).prod
          ((Functor.whiskeringRight Cᵒᵖ _ _).obj (ModuleCat.extendScalars.{w, w, w} f)) ⋙
        tensor _ ⋙ (Functor.whiskeringRight Cᵒᵖ _ _).obj (ModuleCat.restrictScalars.{w} f) ≅
      ((Functor.whiskeringRight Cᵒᵖ _ _).obj (ModuleCat.restrictScalars.{w} f)).prod (𝟭 _) ⋙
        tensor _ :=
  NatIso.ofComponents (fun X => NatIso.ofComponents
    (fun U => (ModuleCat.restrictScalarsTensorExtendScalarsIso f).app (X.1.obj U, X.2.obj U))
    (fun {U U'} g => (ModuleCat.restrictScalarsTensorExtendScalarsIso f).hom.naturality
      ((X.1.map g, X.2.map g) : (X.1.obj U, X.2.obj U) ⟶ (X.1.obj U', X.2.obj U'))))
    (fun {X Y} g => by
      ext U : 2
      exact (ModuleCat.restrictScalarsTensorExtendScalarsIso f).hom.naturality
        ((g.1.app U, g.2.app U) : (X.1.obj U, X.2.obj U) ⟶ (Y.1.obj U, Y.2.obj U)))

variable [UnivLE.{max u v, w}]

/-- **The projection formula** for sheaves of modules: for a sheaf `N` of `S`-modules and a
sheaf `F` of `Λ`-modules, `N ⊗_S (S ⊗_Λ F) ≅ N ⊗_Λ F` as sheaves of `Λ`-modules, naturally in
both. -/
def restrictScalarsTensorExtendScalarsIso :
    (𝟭 (Sheaf J (ModuleCat.{w} S))).prod (extendScalars J f) ⋙ tensor _ ⋙
        restrictScalars J f ≅
      (restrictScalars J f).prod (𝟭 _) ⋙ tensor _ :=
  let LS := presheafToSheaf J (ModuleCat.{w} S)
  let LΛ := presheafToSheaf J (ModuleCat.{w} Λ)
  let E' := (Functor.whiskeringRight Cᵒᵖ _ _).obj (ModuleCat.extendScalars.{w, w, w} f)
  let R' := (Functor.whiskeringRight Cᵒᵖ _ _).obj (ModuleCat.restrictScalars.{w} f)
  let H := (sheafToPresheaf J (ModuleCat.{w} S)).prod (sheafToPresheaf J (ModuleCat.{w} Λ))
  let e₁ : (𝟭 (Sheaf J (ModuleCat.{w} S))).prod (extendScalars J f) ⋙ tensor _ ⋙
        restrictScalars J f ≅
      H ⋙ (𝟭 _).prod E' ⋙ LS.prod LS ⋙ tensor _ ⋙ restrictScalars J f :=
    Functor.isoWhiskerRight (NatIso.prod
      (asIso (sheafificationAdjunction J (ModuleCat.{w} S)).counit).symm (Iso.refl _)) _
  let e₂ : LS.prod LS ⋙ tensor _ ⋙ restrictScalars J f ≅ tensor _ ⋙ R' ⋙ LΛ :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.Monoidal.μNatIso LS) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (tensor _)
        (sheafComposeNatIso J (ModuleCat.restrictScalars.{w} f)
          (sheafificationAdjunction J _) (sheafificationAdjunction J _)).symm
  let e₃ : (𝟭 _).prod E' ⋙ tensor _ ⋙ R' ⋙ LΛ ≅ R'.prod (𝟭 _) ⋙ LΛ.prod LΛ ⋙ tensor _ :=
    (Functor.associator _ _ _).symm ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.associator _ _ _ ≪≫ presheafRestrictScalarsTensorExtendScalarsIso f) LΛ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (Functor.Monoidal.μNatIso LΛ).symm
  let e₄ : H ⋙ R'.prod (𝟭 _) ⋙ LΛ.prod LΛ ⋙ tensor _ ≅
      (restrictScalars J f).prod (𝟭 _) ⋙ tensor _ :=
    let c := asIso (sheafificationAdjunction J (ModuleCat.{w} Λ)).counit
    let b : (H ⋙ R'.prod (𝟭 _)) ⋙ LΛ.prod LΛ ≅ (restrictScalars J f).prod (𝟭 _) :=
      (Iso.refl _ : (H ⋙ R'.prod (𝟭 _)) ⋙ LΛ.prod LΛ ≅
          (restrictScalars J f ⋙ sheafToPresheaf J _ ⋙ LΛ).prod
            (sheafToPresheaf J _ ⋙ LΛ)) ≪≫
        NatIso.prod (Functor.isoWhiskerLeft (restrictScalars J f) c ≪≫
          Functor.rightUnitor _) c
    (Functor.associator _ _ _).symm ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight b _
  e₁ ≪≫ Functor.isoWhiskerLeft H (Functor.isoWhiskerLeft _ e₂ ≪≫ e₃) ≪≫ e₄

end ProjectionFormula

/-! ### Local constancy of finite type -/

section LocallyConstant

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {Λ S : Type (max u v w)} [CommRing Λ] [CommRing S] {f : Λ →+* S}

/-- Restriction of scalars commutes with restriction to a slice site, on the nose. -/
def overPullbackCompRestrictScalarsIso (U : C) :
    J.overPullback (ModuleCat.{max u v w} S) U ⋙ restrictScalars (J.over U) f ≅
      restrictScalars J f ⋙ J.overPullback (ModuleCat.{max u v w} Λ) U :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- Local constancy of finite type transfers along a construction `E ↦ φ E` on modules that
preserves finite generation and is compatible with the restrictions to slice sites. -/
private theorem isFiniteTypeLocallyConstantModuleSheaf_of_forall {R R' : Type (max u v w)}
    [CommRing R] [CommRing R'] (F : Sheaf J (ModuleCat.{max u v w} R))
    (F' : Sheaf J (ModuleCat.{max u v w} R')) (φ : ModuleCat.{max u v w} R → ModuleCat R')
    (hφ : ∀ E, ModuleCat.isFG R E → ModuleCat.isFG R' (φ E))
    (h : ∀ (V : C) (E : ModuleCat.{max u v w} R),
      ((constantSheaf (J.over V) (ModuleCat.{max u v w} R)).obj E ≅
        (J.overPullback (ModuleCat.{max u v w} R) V).obj F) →
      ((constantSheaf (J.over V) (ModuleCat.{max u v w} R')).obj (φ E) ≅
        (J.overPullback (ModuleCat.{max u v w} R') V).obj F'))
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J R F) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J R' F' := by
  intro U
  obtain ⟨I, V, g, hg, hV⟩ := hF U
  refine ⟨I, V, g, hg, fun i => ?_⟩
  obtain ⟨E, hE, ⟨e⟩⟩ := hV i
  exact ⟨φ E, hφ E hE, ⟨h _ E e⟩⟩

/-- A sheaf of `S`-modules whose restriction of scalars along a surjective ring map is locally
constant of finite type is itself locally constant of finite type. -/
theorem isFiniteTypeLocallyConstantModuleSheaf_of_restrictScalars (hf : Function.Surjective f)
    (F : Sheaf J (ModuleCat.{max u v w} S))
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ
      ((restrictScalars J f).obj F)) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J S F := by
  refine isFiniteTypeLocallyConstantModuleSheaf_of_forall J _ _
    (ModuleCat.extendScalars.{max u v w, max u v w, max u v w} f).obj (fun E hE => ?_)
    (fun V E e => ?_) hF
  · rw [ModuleCat.isFG_iff] at hE ⊢
    let _ : Algebra Λ S := f.toAlgebra
    exact Module.Finite.base_change Λ S E
  · exact (extendScalarsConstantSheafIso (J.over V) f).symm.app E ≪≫
      (extendScalars (J.over V) f).mapIso
        (e ≪≫ ((overPullbackCompRestrictScalarsIso J V).app F).symm) ≪≫
      (restrictScalarsCompExtendScalarsIso (J.over V) hf).app _

/-- Restriction of scalars along a surjective ring map preserves local constancy of finite
type. -/
theorem isFiniteTypeLocallyConstantModuleSheaf_restrictScalars (hf : Function.Surjective f)
    (F : Sheaf J (ModuleCat.{max u v w} S))
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J S F) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ
      ((restrictScalars J f).obj F) := by
  refine isFiniteTypeLocallyConstantModuleSheaf_of_forall J _ _
    (ModuleCat.restrictScalars.{max u v w} f).obj (fun E hE => ?_) (fun V E e => ?_) hF
  · rw [ModuleCat.isFG_iff] at hE ⊢
    let _ : Algebra Λ S := f.toAlgebra
    let _ : Module Λ E := ((ModuleCat.restrictScalars.{max u v w} f).obj E).isModule
    have : IsScalarTower Λ S E := .of_algebraMap_smul fun _ _ => rfl
    have : Module.Finite Λ S := Module.Finite.of_surjective (Algebra.linearMap Λ S) hf
    exact Module.Finite.trans S E
  · exact (restrictScalarsConstantSheafIso (J.over V) f).symm.app E ≪≫
      (restrictScalars (J.over V) f).mapIso e ≪≫
      (overPullbackCompRestrictScalarsIso J V).app F

/-- **Local constancy of finite type is detected by restriction of scalars along a surjective
ring map.** A sheaf of `S`-modules is locally constant of finite type exactly when it is so as
a sheaf of `Λ`-modules. -/
theorem isFiniteTypeLocallyConstantModuleSheaf_restrictScalars_iff (hf : Function.Surjective f)
    (F : Sheaf J (ModuleCat.{max u v w} S)) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ
        ((restrictScalars J f).obj F) ↔
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J S F :=
  ⟨isFiniteTypeLocallyConstantModuleSheaf_of_restrictScalars J hf F,
    isFiniteTypeLocallyConstantModuleSheaf_restrictScalars J hf F⟩

end LocallyConstant

end Stacks.ModuleSheaf
