module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.GeometricFibre
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ModuleLiftLocallyConstant
public import StacksFrontier.CategoryTheory.Abelian.MonodromyFiltration
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.DenseSubsite
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.FiniteRingModuleUnderlyingAbelian

/-!
# The geometric fibre of a finite type locally constant sheaf of `F_ℓ`-vector spaces

Let `X` be a connected scheme, `x` a geometric point of `X` and `ℓ` a prime. This file attaches
to a finite type locally constant sheaf `G` of `F_ℓ`-vector spaces on Mathlib's small étale site
of `X` its geometric fibre at `x`, an abelian group with an action of `π₁(X, x)`: the finite
discrete `π₁(X, x)`-module of Tag 0DV5 (2) attached to the underlying abelian sheaf of `G`,
transported to the size-bounded small étale site of Stacks 021B of a big étale site containing
`X`. Its underlying set is the geometric fibre at `x` of the finite étale cover representing the
underlying sheaf of sets of `G`.

## Main definitions

* `Stacks.EtaleCohomology.zmodGeometricFibre`: the fibre functor, from the finite type locally
  constant sheaves of `F_ℓ`-vector spaces to abelian groups with an action of `π₁(X, x)`.
* `Stacks.EtaleCohomology.zmodGeometricFibreEquiv`: its underlying set is the geometric fibre of
  the representing cover.

## Main results

* The fibre functor is additive and fully faithful.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.ConstantSheaf

universe u

namespace Stacks.EtaleCohomology

/-- **Additive maps between `F_ℓ`-vector spaces are linear**: the forgetful functor from
`ZMod ℓ`-modules to abelian groups is full. -/
instance full_forget₂_moduleCat_zmod (ℓ : ℕ) :
    (forget₂ (ModuleCat.{u} (ZMod ℓ)) AddCommGrpCat.{u}).Full where
  map_surjective {M N} f :=
    ⟨ModuleCat.ofHom (AddMonoidHom.toZModLinearMap ℓ (show M →+ N from f.hom)), rfl⟩

variable (ℓ : ℕ) (X : Scheme.{u})

/-- The finite type locally constant sheaves of `F_ℓ`-vector spaces on the small étale site. -/
abbrev zmodFiniteTypeLocallyConstant :
    ObjectProperty (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ))) :=
  fun G ↦ IsFiniteTypeLocallyConstant (ZMod ℓ) X.smallEtaleTopology G

/-- The finite type locally constant sheaves of `F_ℓ`-vector spaces are closed under kernels
(Tag 093U (3)). -/
instance isClosedUnderKernels_zmodFiniteTypeLocallyConstant [Fact ℓ.Prime] :
    (zmodFiniteTypeLocallyConstant ℓ X).IsClosedUnderKernels :=
  isClosedUnderKernels_isFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, u + 1}
    X.smallEtaleTopology (ZMod ℓ)

/-- The finite type locally constant sheaves of `F_ℓ`-vector spaces are closed under cokernels
(Tag 093U (3)). -/
instance isClosedUnderCokernels_zmodFiniteTypeLocallyConstant [Fact ℓ.Prime] :
    (zmodFiniteTypeLocallyConstant ℓ X).IsClosedUnderCokernels :=
  isClosedUnderCokernels_isFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, u + 1}
    X.smallEtaleTopology (ZMod ℓ)

variable {ℓ X} in
/-- Over the finite ring `ZMod ℓ`, a finite type locally constant sheaf of modules is finite
locally constant. -/
theorem isFiniteLocallyConstant_of_zmodFiniteTypeLocallyConstant [NeZero ℓ]
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ))}
    (hG : zmodFiniteTypeLocallyConstant ℓ X G) :
    IsFiniteLocallyConstant X.smallEtaleTopology G := by
  refine ⟨fun U ↦ ?_⟩
  obtain ⟨I, V, f, hcov, htriv⟩ := hG U
  refine ⟨I, V, f, hcov, fun i ↦ ?_⟩
  obtain ⟨E, hE, he⟩ := htriv i
  exact ⟨E, (Stacks.GroupCohomology.moduleCat_isFG_iff_finite (ZMod ℓ) E).mp hE, he⟩

variable {ℓ} in
/-- The constant sheaf `Z/ℓZ` is a finite type locally constant sheaf of `F_ℓ`-vector spaces. -/
theorem zmodFiniteTypeLocallyConstant_constantZMod :
    zmodFiniteTypeLocallyConstant ℓ X (constantZMod.{0} ℓ X) := fun U ↦
  ⟨PUnit, fun _ ↦ U, fun _ ↦ 𝟙 U, by
    refine X.smallEtaleTopology.superset_covering (fun V f _ ↦ ?_)
      (X.smallEtaleTopology.top_mem U)
    exact ⟨U, f, 𝟙 U, ⟨PUnit.unit⟩, by simp⟩, fun _ ↦
    ⟨ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)),
      Module.Finite.equiv (ULift.moduleEquiv (R := ZMod ℓ)).symm,
      ⟨(Stacks.ConstantSheaf.overPullbackConstantSheafIso X.smallEtaleTopology
        (ModuleCat.{u + 1} (ZMod ℓ)) U).app _⟩⟩⟩

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

/-- Restriction of sheaves from Mathlib's small étale site to the size-bounded small étale site
of Stacks 021B, the functor of the equivalence `AlgebraicGeometry.SmallEtale.sheafEquiv`. -/
abbrev toBoundedSite (A : Type*) [Category A] :
    Sheaf X.1.smallEtaleTopology A ⥤ Sheaf (SmallEtale.topology B X.1 X.2) A :=
  (SmallEtale.toEtaleSite B X.1 X.2).sheafPushforwardContinuous A
    (SmallEtale.topology B X.1 X.2) X.1.smallEtaleTopology

/-- Restriction to the size-bounded small étale site is an equivalence for abelian sheaves. -/
instance isEquivalence_toBoundedSite_addCommGrp :
    (toBoundedSite B X AddCommGrpCat.{u + 1}).IsEquivalence :=
  haveI : ∀ Y : (X.1.Etale)ᵒᵖ,
      HasLimitsOfShape (StructuredArrow Y (SmallEtale.toEtaleSite B X.1 X.2).op)
        AddCommGrpCat.{u + 1} :=
    fun _ ↦ hasLimitsOfShape_of_essentiallySmall.{u} _ _
  inferInstance

/-- Restriction to the size-bounded small étale site is additive. -/
instance additive_toBoundedSite_addCommGrp :
    (toBoundedSite B X AddCommGrpCat.{u + 1}).Additive :=
  Functor.additive_of_preserves_binary_products _

variable {ℓ B X} in
/-- **The transported underlying abelian sheaf of a finite type locally constant sheaf of
`F_ℓ`-vector spaces is finite locally constant.** -/
theorem isFiniteLocallyConstant_toBoundedSite_forgetZMod [NeZero ℓ]
    {G : Sheaf X.1.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ))}
    (hG : zmodFiniteTypeLocallyConstant ℓ X.1 G) :
    isFiniteLocallyConstantAbelianSheaf.{u, u + 1, u + 1} (SmallEtale.topology B X.1 X.2)
      ((toBoundedSite B X AddCommGrpCat.{u + 1}).obj ((forgetZMod ℓ X.1).obj G)) := by
  have h₁ := isFiniteLocallyConstant_forgetModule.{u, u + 1} X.1.smallEtaleTopology (ZMod ℓ) G
    (isFiniteLocallyConstant_of_zmodFiniteTypeLocallyConstant hG)
  rw [← sheafCompose_forget₂_forget] at h₁
  exact isFiniteLocallyConstant_of_forget _ _
    ((SmallEtale.isFiniteLocallyConstant_iff_toEtaleSite B X.1 X.2 _).mp h₁)

/-- The underlying abelian sheaf of a finite type locally constant sheaf of `F_ℓ`-vector spaces,
transported to the size-bounded small étale site, as a finite locally constant abelian sheaf. -/
def zmodToFiniteLocallyConstantAbelian [NeZero ℓ] :
    (zmodFiniteTypeLocallyConstant ℓ X.1).FullSubcategory ⥤
      (isFiniteLocallyConstantAbelianSheaf.{u, u + 1, u + 1}
        (SmallEtale.topology B X.1 X.2)).FullSubcategory :=
  ObjectProperty.lift _
    ((zmodFiniteTypeLocallyConstant ℓ X.1).ι ⋙ forgetZMod ℓ X.1 ⋙
      toBoundedSite B X AddCommGrpCat.{u + 1})
    fun G ↦ isFiniteLocallyConstant_toBoundedSite_forgetZMod G.property

variable [ConnectedSpace X.1] (x : GeometricPoint X.1)

/-- **The geometric fibre at `x` of a finite type locally constant sheaf of `F_ℓ`-vector
spaces**, with its action of `π₁(X, x)`: the finite discrete module of Tag 0DV5 (2) attached to
its underlying abelian sheaf. -/
def zmodGeometricFibre [NeZero ℓ] :
    (zmodFiniteTypeLocallyConstant ℓ X.1).FullSubcategory ⥤
      Action AddCommGrpCat.{u + 1} (EtaleFundamentalGroup X.1 x) :=
  zmodToFiniteLocallyConstantAbelian ℓ B X ⋙ (geometricFibreAbelianEquivalence B X x).functor ⋙
    (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1} (EtaleFundamentalGroup X.1 x)).ι ⋙
      ContinuousGAddCommGrp.toAction _

/-- The geometric fibre functor `zmodGeometricFibre ℓ B X x` is additive. -/
instance [NeZero ℓ] : (zmodGeometricFibre ℓ B X x).Additive := by
  have : (ContinuousGAddCommGrp.toAction.{u + 1, u + 1} (EtaleFundamentalGroup X.1 x)).Additive :=
    { map_add := rfl }
  unfold zmodGeometricFibre zmodToFiniteLocallyConstantAbelian
  infer_instance

/-- The geometric fibre functor `zmodGeometricFibre ℓ B X x` is faithful. -/
instance [NeZero ℓ] : (zmodGeometricFibre ℓ B X x).Faithful := by
  have : (ContinuousGAddCommGrp.toAction.{u + 1, u + 1} (EtaleFundamentalGroup X.1 x)).Faithful :=
    ((ObjectProperty.fullyFaithfulι _).comp (ObjectProperty.fullyFaithfulι _)).faithful
  unfold zmodGeometricFibre zmodToFiniteLocallyConstantAbelian
  infer_instance

/-- The geometric fibre functor `zmodGeometricFibre ℓ B X x` is full. -/
instance [NeZero ℓ] : (zmodGeometricFibre ℓ B X x).Full := by
  have : (ContinuousGAddCommGrp.toAction.{u + 1, u + 1} (EtaleFundamentalGroup X.1 x)).Full :=
    ((ObjectProperty.fullyFaithfulι _).comp (ObjectProperty.fullyFaithfulι _)).full
  unfold zmodGeometricFibre zmodToFiniteLocallyConstantAbelian
  infer_instance

/-- The finite locally constant sheaf of sets underlying the transported abelian sheaf of `G`. -/
abbrev zmodFibreSetSheaf [NeZero ℓ] (G : (zmodFiniteTypeLocallyConstant ℓ X.1).FullSubcategory) :
    (isFiniteLocallyConstantSetSheaf.{u, u + 1, u + 1}
      (SmallEtale.topology B X.1 X.2)).FullSubcategory :=
  (forgetFiniteLocallyConstantAbelianSheaf _).obj ((zmodToFiniteLocallyConstantAbelian ℓ B X).obj G)

/-- **The geometric fibre of `G` is the geometric fibre of the cover representing its underlying
sheaf of sets.** -/
def zmodGeometricFibreEquiv [NeZero ℓ] (G : (zmodFiniteTypeLocallyConstant ℓ X.1).FullSubcategory) :
    ((zmodGeometricFibre ℓ B X x).obj G).V ≃
      (finiteEtaleFiberFunctor x).obj ((representingCover B X).obj (zmodFibreSetSheaf ℓ B X G)) :=
  geometricFibreSetEquiv B X x _

/-- The equivalence `zmodGeometricFibreEquiv` intertwines the action of `π₁(X, x)` with
evaluation of natural automorphisms of the fibre functor on the representing cover. -/
theorem zmodGeometricFibreEquiv_smul [NeZero ℓ]
    (G : (zmodFiniteTypeLocallyConstant ℓ X.1).FullSubcategory) (σ : EtaleFundamentalGroup X.1 x)
    (a : ((zmodGeometricFibre ℓ B X x).obj G).V) :
    zmodGeometricFibreEquiv ℓ B X x G ((((zmodGeometricFibre ℓ B X x).obj G).ρ σ).asHom a) =
      (σ.asIso.app ((representingCover B X).obj (zmodFibreSetSheaf ℓ B X G))).hom
        (zmodGeometricFibreEquiv ℓ B X x G a) :=
  geometricFibreSetEquiv_smul B X x _ σ a

/-- The equivalence `zmodGeometricFibreEquiv` is natural. -/
theorem zmodGeometricFibreEquiv_naturality [NeZero ℓ]
    {G H : (zmodFiniteTypeLocallyConstant ℓ X.1).FullSubcategory} (f : G ⟶ H)
    (a : ((zmodGeometricFibre ℓ B X x).obj G).V) :
    zmodGeometricFibreEquiv ℓ B X x H (((zmodGeometricFibre ℓ B X x).map f).hom a) =
      (finiteEtaleFiberFunctor x).map ((representingCover B X).map
        ((forgetFiniteLocallyConstantAbelianSheaf _).map
          ((zmodToFiniteLocallyConstantAbelian ℓ B X).map f)))
        (zmodGeometricFibreEquiv ℓ B X x G a) :=
  geometricFibreSetEquiv_naturality B X x _ a

/-- The image of a finite type locally constant sheaf of `F_ℓ`-vector spaces is finite. -/
instance finite_zmodGeometricFibre_obj [NeZero ℓ]
    (G : (zmodFiniteTypeLocallyConstant ℓ X.1).FullSubcategory) :
    Finite ((zmodGeometricFibre ℓ B X x).obj G).V :=
  ((geometricFibreAbelianEquivalence B X x).functor.obj
    ((zmodToFiniteLocallyConstantAbelian ℓ B X).obj G)).property

omit [ConnectedSpace X.1] in
/-- A sheaf of `F_ℓ`-vector spaces is killed by `ℓ`. -/
theorem nsmul_id_zmod_eq_zero (G : Sheaf X.1.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ))) :
    ℓ • 𝟙 G = 0 := by
  ext U x
  change ℓ • x = 0
  rw [← Nat.cast_smul_eq_nsmul (ZMod ℓ), ZMod.natCast_self, zero_smul]

/-- **The geometric fibre carries epimorphisms to surjections.** An epimorphism of sheaves of
`F_ℓ`-vector spaces stays an epimorphism on the underlying sheaves of sets on the size-bounded
site, hence on the representing covers, and the geometric fibre functor preserves epimorphisms
because it preserves finite colimits. -/
theorem surjective_zmodGeometricFibre_map_of_epi [NeZero ℓ]
    {G H : (zmodFiniteTypeLocallyConstant ℓ X.1).FullSubcategory} (f : G ⟶ H) (hf : Epi f.hom) :
    Function.Surjective ((zmodGeometricFibre ℓ B X x).map f).hom := by
  have h2 : Epi ((sheafCompose (SmallEtale.topology B X.1 X.2)
      (forget AddCommGrpCat.{u + 1})).map
        ((toBoundedSite B X AddCommGrpCat.{u + 1}).map ((forgetZMod ℓ X.1).map f.hom))) := by
    rw [← Sheaf.isLocallySurjective_iff_epi]
    have : Presheaf.IsLocallySurjective (SmallEtale.topology B X.1 X.2)
        ((sheafToPresheaf _ _).map ((toBoundedSite B X AddCommGrpCat.{u + 1}).map
          ((forgetZMod ℓ X.1).map f.hom))) :=
      (Sheaf.isLocallySurjective_iff_epi' (φ := (toBoundedSite B X AddCommGrpCat.{u + 1}).map
        ((forgetZMod ℓ X.1).map f.hom))).mpr inferInstance
    change Presheaf.IsLocallySurjective _ (Functor.whiskerRight _ _)
    infer_instance
  let g := (forgetFiniteLocallyConstantAbelianSheaf _).map
    ((zmodToFiniteLocallyConstantAbelian ℓ B X).map f)
  have h3 : Epi (C := FiniteLocallyConstantSheaf B X) g := (ObjectProperty.ι _).epi_of_epi_map h2
  have h4 : Epi ((representingCover B X).map g) :=
    (finiteLocallyConstantFiniteEtaleEquivalence B X).functor.map_epi g
  have := Stacks.FundamentalGroup.preservesFiniteColimits_finiteEtaleFiberFunctor x
  have h5 : Function.Surjective ((finiteEtaleFiberFunctor x).map ((representingCover B X).map g)) :=
    (epi_iff_surjective _).mp (Functor.map_epi _ _)
  intro b
  obtain ⟨a, ha⟩ := h5 (zmodGeometricFibreEquiv ℓ B X x H b)
  refine ⟨(zmodGeometricFibreEquiv ℓ B X x G).symm a, ?_⟩
  apply (zmodGeometricFibreEquiv ℓ B X x H).injective
  rwa [zmodGeometricFibreEquiv_naturality, Equiv.apply_symm_apply]

variable {ℓ B X} in
/-- **The transported underlying sheaf of sets of the constant sheaf `Z/ℓZ` is represented by the
trivial cover with `ℓ` sheets.** -/
def representingCoverConstantIso [NeZero ℓ]
    (hK : zmodFiniteTypeLocallyConstant ℓ X.1 (constantZMod.{0} ℓ X.1)) :
    (representingCover B X).obj (zmodFibreSetSheaf ℓ B X ⟨constantZMod.{0} ℓ X.1, hK⟩) ≅
      trivialCover (ULift.{u} (ZMod ℓ)) := by
  let J := SmallEtale.topology B X.1 X.2
  let ι := ULift.{u} (ZMod ℓ)
  have := preservesSheafification_forget_moduleCat.{u, u + 1, u} X.1.smallEtaleTopology (ZMod ℓ)
  have : ∀ P : (SmallEtale B X.1 X.2)ᵒᵖ ⥤ Type (u + 1),
      (SmallEtale.toEtaleSite B X.1 X.2).op.HasPointwiseRightKanExtension P :=
    fun P Y ↦ by
      have := hasLimitsOfShape_of_essentiallySmall.{u}
        (StructuredArrow Y (SmallEtale.toEtaleSite B X.1 X.2).op) (Type (u + 1))
      infer_instance
  let M := ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ))
  let e₁ : (zmodFibreSetSheaf ℓ B X ⟨constantZMod.{0} ℓ X.1, hK⟩).obj ≅
      (Sheaf.sheafifiedYoneda J).obj (splitObj B X.2 ι) :=
    eqToIso (congrArg (toBoundedSite B X (Type (u + 1))).obj
        (sheafCompose_forget₂_forget.{u, u + 1} X.1.smallEtaleTopology (ZMod ℓ)
          (constantZMod.{0} ℓ X.1))) ≪≫
      (toBoundedSite B X (Type (u + 1))).mapIso
        ((constantCommuteCompose X.1.smallEtaleTopology (forget (ModuleCat.{u + 1} (ZMod ℓ)))).app
          M) ≪≫
      (Stacks.Cohomology.DenseSubsiteConstant.constantSheafPushforwardContinuousIso J
        X.1.smallEtaleTopology (SmallEtale.toEtaleSite B X.1 X.2) (Type (u + 1))).app _ ≪≫
      (constantSheaf J (Type (u + 1))).mapIso
        (Equiv.toIso (Equiv.ulift.trans (Equiv.ulift.symm.trans Equiv.ulift.symm))) ≪≫
      constantSheafIsoSheafifiedYonedaSplitObj B X.2 ι
  let U : (finiteSmallEtaleObjects B X).FullSubcategory :=
    ⟨splitObj B X.2 ι, isFinite_hom_splitObj B X.2 ι⟩
  let e₂ : zmodFibreSetSheaf ℓ B X ⟨constantZMod.{0} ℓ X.1, hK⟩ ≅
      (finiteSmallEtaleToFiniteLocallyConstant B X).obj U :=
    ObjectProperty.isoMk _ e₁
  exact (representingCover B X).mapIso e₂ ≪≫
    (finiteEtaleSiteEquivalence B X).functor.mapIso
      ((finiteSmallEtaleToFiniteLocallyConstant B X).asEquivalence.unitIso.app U).symm ≪≫
    MorphismProperty.Over.isoMk (Iso.refl _)

variable {ℓ B X} in
/-- **The geometric fibre of the constant sheaf `Z/ℓZ` has `ℓ` elements and trivial monodromy.** -/
theorem card_zmodGeometricFibre_constant_and_smul [NeZero ℓ]
    (hK : zmodFiniteTypeLocallyConstant ℓ X.1 (constantZMod.{0} ℓ X.1)) :
    Nat.card ((zmodGeometricFibre ℓ B X x).obj ⟨constantZMod.{0} ℓ X.1, hK⟩).V = ℓ ∧
      ∀ (σ : EtaleFundamentalGroup X.1 x)
        (a : ((zmodGeometricFibre ℓ B X x).obj ⟨constantZMod.{0} ℓ X.1, hK⟩).V),
        (((zmodGeometricFibre ℓ B X x).obj ⟨constantZMod.{0} ℓ X.1, hK⟩).ρ σ).asHom a = a := by
  set K : (zmodFiniteTypeLocallyConstant ℓ X.1).FullSubcategory := ⟨constantZMod.{0} ℓ X.1, hK⟩
  let φ := representingCoverConstantIso (B := B) hK
  let e : ((zmodGeometricFibre ℓ B X x).obj K).V ≃
      (finiteEtaleFiberFunctor x).obj (trivialCover (ULift.{u} (ZMod ℓ))) :=
    (zmodGeometricFibreEquiv ℓ B X x K).trans ((finiteEtaleFiberFunctor x).mapIso φ).toEquiv
  obtain ⟨hcard, htriv⟩ := card_finiteEtaleFiber_trivialCover_and_smul x (ULift.{u} (ZMod ℓ))
  refine ⟨by rw [Nat.card_congr e, hcard, Nat.card_ulift, Nat.card_zmod], fun σ a ↦ ?_⟩
  apply e.injective
  have hn := congrArg (fun f ↦ f (zmodGeometricFibreEquiv ℓ B X x K a))
    (σ.asIso.hom.naturality φ.hom)
  simp only [types_comp_apply] at hn
  change (finiteEtaleFiberFunctor x).map φ.hom (zmodGeometricFibreEquiv ℓ B X x K _) =
    (finiteEtaleFiberFunctor x).map φ.hom (zmodGeometricFibreEquiv ℓ B X x K a)
  rw [zmodGeometricFibreEquiv_smul]
  change (finiteEtaleFiberFunctor x).map φ.hom (σ.asIso.hom.app _ _) = _
  rw [← hn]
  exact htriv σ _

variable {ℓ B X x} in
/-- **A finite type locally constant sheaf of `F_ℓ`-vector spaces with `ℓ`-group monodromy is a
successive extension of copies of `Z/ℓZ`.** If every element of `π₁(X, x)` has an `ℓ`-power
acting trivially on the geometric fibre of a finite étale cover isomorphic to the one
representing the underlying sheaf of sets of `G`, then `G` has a finite filtration from the zero
subobject to the whole sheaf whose successive quotients are the constant sheaf `Z/ℓZ`. -/
theorem exists_relSeries_constantRankOneStep_of_monodromy (hℓ : ℓ.Prime)
    (G : Sheaf X.1.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ)))
    (hG : zmodFiniteTypeLocallyConstant ℓ X.1 G) (Y : FiniteEtaleOver X.1)
    (eY : (have : NeZero ℓ := ⟨hℓ.ne_zero⟩
      (representingCover B X).obj (zmodFibreSetSheaf ℓ B X ⟨G, hG⟩)) ≅ Y)
    (hmon : ∀ σ : EtaleFundamentalGroup X.1 x, ∃ k : ℕ,
      ∀ p : (finiteEtaleFiberFunctor x).obj Y, ((σ ^ (ℓ ^ k)).asIso.app Y).hom p = p) :
    ∃ F : RelSeries (ConstantRankOneStep.{0} ℓ G),
      IsZero (Subobject.underlying.obj F.head) ∧ IsIso F.last.arrow := by
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hK := zmodFiniteTypeLocallyConstant_constantZMod (ℓ := ℓ) X.1
  obtain ⟨hcard, htriv⟩ := card_zmodGeometricFibre_constant_and_smul (B := B) x hK
  refine CategoryTheory.Abelian.exists_relSeries_cokernelIsoStep hℓ (constantZMod.{0} ℓ X.1)
    (zmodFiniteTypeLocallyConstant ℓ X.1) hK (zmodGeometricFibre ℓ B X x) hcard htriv
    (fun _ ↦ inferInstance) (surjective_zmodGeometricFibre_map_of_epi ℓ B X x)
    (fun G ↦ nsmul_id_zmod_eq_zero ℓ B X G.obj) ⟨G, hG⟩ fun σ ↦ ?_
  obtain ⟨k, hk⟩ := hmon σ
  refine ⟨k, fun a ↦ (zmodGeometricFibreEquiv ℓ B X x ⟨G, hG⟩).injective ?_⟩
  rw [zmodGeometricFibreEquiv_smul]
  apply ((finiteEtaleFiberFunctor x).mapIso eY).toEquiv.injective
  have hn := congrArg (fun f ↦ f (zmodGeometricFibreEquiv ℓ B X x ⟨G, hG⟩ a))
    ((σ ^ (ℓ ^ k)).asIso.hom.naturality eY.hom)
  simp only [types_comp_apply] at hn
  change (finiteEtaleFiberFunctor x).map eY.hom ((σ ^ (ℓ ^ k)).asIso.hom.app _ _) = _
  rw [← hn]
  exact hk _

end Stacks.EtaleCohomology

end
