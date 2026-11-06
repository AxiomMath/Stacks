module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.Products
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.DerivedDirectImageAndRestriction
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.AdjunctionViaFlatPullback
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.PullbackPreservesFlatness

/-!
# Derived direct image preserves derived completeness

Let `f : (Sh(𝒟), 𝒪') ⟶ (Sh(𝒞), 𝒪)` be a morphism of ringed sites with underlying continuous
functor `u`, and let `ℐ ⊂ 𝒪` and `ℐ' ⊂ 𝒪'` be sheaves of ideals such that `f^♯` sends `f^{-1}ℐ`
into `ℐ'`, that is, such that `f^♯(g) ∈ ℐ'(u(V))` for every object `V` of `𝒞` and every
`g ∈ ℐ(V)`. Then `Rf_*` carries `D_comp(𝒪', ℐ')` into `D_comp(𝒪, ℐ)`. Here derived completeness is
`AlgebraicGeometry.RingedSite.IsDerivedComplete`: for every object `U` and every `g ∈ ℐ(U)` the
Milnor difference `1 - g · shift` is invertible on `∏_{n ∈ ℕ} (K|_U)`, that is `T(K|_U, g) = 0`.

## Main definitions

* `Stacks.Cohomology.Localization.derivedRestrictionIso`: the derived restriction to a slice
  site is the functor the (exact) restriction induces on derived categories.
* `AlgebraicGeometry.RingedSite.fSharpSection`: `f^♯` on sections over an object of the target
  site.
* `AlgebraicGeometry.RingedSite.idealScalar`: multiplication by a local section of the structure
  sheaf, as a central endomorphism of the sheaves of modules on a slice site.

## Main results

* `Stacks.SheafOfModules.map_globalSectionToEnd`: direct image intertwines multiplication by two
  compatible families of local sections that correspond under the structure map.
* `Stacks.SemilinearFunctor.map_smul_id_mapHomologicalComplex`,
  `Stacks.SemilinearFunctor.map_smul_id_mapHomotopyCategory`,
  `Stacks.SemilinearFunctor.map_smul_id_comp` and
  `Stacks.SemilinearFunctor.map_smul_id_rightDerived`: a functor carrying multiplication by `a`
  to multiplication by `b` keeps doing so on complexes, on the homotopy category, after
  postcomposition with a linear functor, and after right derivation.
* `isDerivedCompleteAt_map_of_center`: an additive functor preserving the countable power of `K`
  and carrying multiplication by `a` to multiplication by `b` carries `T(K, a) = 0` to
  `T(F K, b) = 0`.
* `AlgebraicGeometry.RingedSite.localizedPushforward_map_idealScalar`: the direct image along the
  localized morphism intertwines multiplication by `g` with multiplication by `f^♯ g`.
* `AlgebraicGeometry.RingedSite.isDerivedCompleteAt_derivedPushforward_overFunctor`: if
  `T(K|_{u(V)}, f^♯ g) = 0` then `T((Rf_*K)|_V, g) = 0`.
* `AlgebraicGeometry.RingedSite.derivedPushforward_isDerivedComplete`: `Rf_*` carries
  `D_comp(𝒪', ℐ')` into `D_comp(𝒪, ℐ)` for a morphism of ringed sites.

## References

* [Stacks Project, Tag 099J](https://stacks.math.columbia.edu/tag/099J)
* [Stacks Project, Tag 0999](https://stacks.math.columbia.edu/tag/0999)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Cohomology.Localization
open scoped IsMulCommutative

universe v₁ u₁ w m u

namespace Stacks.SheafOfModules

/-- If the structure map `φ` of a morphism of sites carries the family `t` of sections of `S` to
the family `s` of sections of `R`, then the direct image along `φ` carries multiplication by `s`
to multiplication by `t`. -/
theorem map_globalSectionToEnd
    {C : Type u₁} [Category.{v₁} C] {D : Type*} [Category* D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
    {S : Sheaf J RingCat.{w}} {R : Sheaf K RingCat.{w}} [Functor.IsContinuous F J K]
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj R)
    [∀ U, IsMulCommutative (R.obj.obj U)] [∀ U, IsMulCommutative (S.obj.obj U)]
    (s : (R.obj ⋙ forget RingCat).sections) (t : (S.obj ⋙ forget RingCat).sections)
    (h : ∀ U : Cᵒᵖ, φ.hom.app U (t.val U) = s.val (op (F.obj U.unop)))
    (M : _root_.SheafOfModules.{m} R) :
    (_root_.SheafOfModules.pushforward.{m} φ).map ((globalSectionToEnd R s).asHom.app M) =
      (globalSectionToEnd S t).asHom.app ((_root_.SheafOfModules.pushforward.{m} φ).obj M) := by
  ext U x
  let y : M.val.obj (op (F.obj (unop U))) := x
  show s.val (op (F.obj (unop U))) • y = _
  rw [← h U]
  rfl

/-- The compatible family attached to a section over `V`, read on the slice site over `V`: its
value at an object `W → V` is the restriction of the section along that morphism. -/
theorem terminalSection_over_val {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{w}) (V : C) [∀ U, IsMulCommutative ((R.over V).obj.obj U)]
    (g : R.obj.obj (op V)) (W : (Over V)ᵒᵖ) :
    (terminalSection (R.over V) (Over.mk (𝟙 V)) Over.mkIdTerminal g).val W =
      R.obj.map ((unop W).hom).op g := by
  have key : ∀ k : (unop W) ⟶ Over.mk (𝟙 V), k.left = (unop W).hom →
      (R.over V).obj.map k.op g = R.obj.map ((unop W).hom).op g := by
    intro k hk
    show R.obj.map (k.left).op g = _
    rw [hk]
  exact key _ (Over.mkIdTerminal_from_left _)

end Stacks.SheafOfModules

namespace CategoryTheory.Linear

/-- Multiplication by a scalar on an identity morphism is the component at that object of the
central element the scalar defines. -/
theorem smul_id_eq_toCatCenter_app {A : Type*} [Ring A] {C : Type*} [Category C] [Preadditive C]
    [Linear A C] (a : A) (M : C) : a • 𝟙 M = (Linear.toCatCenter A C a).app M := rfl

/-- For the linear structure attached to the identity of the centre, the central element a
scalar defines is the scalar itself. -/
theorem toCatCenter_ofRingMorphism_id {C : Type*} [Category C] [Preadditive C]
    (a : CatCenter C) :
    letI : Linear (CatCenter C) C := Linear.ofRingMorphism (RingHom.id (CatCenter C))
    Linear.toCatCenter (CatCenter C) C a = a := by
  ext M
  exact Category.comp_id _

end CategoryTheory.Linear

namespace Stacks.SemilinearFunctor

/-- A linear functor carries multiplication by `a` on an identity morphism to multiplication by
`a` on the identity of the image. -/
private theorem map_smul_id_eq {R : Type*} [Ring R] {A B : Type*} [Category* A] [Category* B]
    [Preadditive A] [Preadditive B] [Linear R A] [Linear R B] (F : A ⥤ B) [F.Linear R]
    (a : R) (M : A) : F.map (a • 𝟙 M) = a • 𝟙 (F.obj M) := by
  rw [CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id]

/-- An additive functor carrying multiplication by `a` to multiplication by `b` does the same
degreewise on homological complexes. -/
theorem map_smul_id_mapHomologicalComplex
    {R S : Type*} [Ring R] [Ring S] {A B : Type*} [Category* A] [Category* B]
    [Preadditive A] [Preadditive B] [Linear R A] [Linear S B]
    (F : A ⥤ B) [F.Additive] (a : R) (b : S)
    (h : ∀ M : A, F.map (a • 𝟙 M) = b • 𝟙 (F.obj M))
    {ι : Type*} (c : ComplexShape ι) (E : HomologicalComplex A c) :
    (F.mapHomologicalComplex c).map (a • 𝟙 E) =
      b • 𝟙 ((F.mapHomologicalComplex c).obj E) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  show F.map ((a • 𝟙 E).f n) = _
  rw [HomologicalComplex.smul_f_apply, HomologicalComplex.smul_f_apply,
    HomologicalComplex.id_f, HomologicalComplex.id_f]
  exact h (E.X n)

/-- An additive functor carrying multiplication by `a` to multiplication by `b` does the same on
the homotopy category of complexes. -/
theorem map_smul_id_mapHomotopyCategory
    {R S : Type*} [Ring R] [Ring S] {A B : Type*} [Category* A] [Category* B]
    [Preadditive A] [Preadditive B] [Linear R A] [Linear S B]
    (F : A ⥤ B) [F.Additive] (a : R) (b : S)
    (h : ∀ M : A, F.map (a • 𝟙 M) = b • 𝟙 (F.obj M))
    {ι : Type*} (c : ComplexShape ι) (M : HomotopyCategory A c) :
    (F.mapHomotopyCategory c).map (a • 𝟙 M) =
      b • 𝟙 ((F.mapHomotopyCategory c).obj M) := by
  obtain ⟨E⟩ := M
  show (F.mapHomotopyCategory c).map (a • 𝟙 ((HomotopyCategory.quotient A c).obj E)) =
    b • 𝟙 ((F.mapHomotopyCategory c).obj ((HomotopyCategory.quotient A c).obj E))
  rw [← map_smul_id_eq (HomotopyCategory.quotient A c) a E,
    CategoryTheory.Functor.mapHomotopyCategory_map,
    map_smul_id_mapHomologicalComplex F a b h c E, map_smul_id_eq]
  rfl

/-- Postcomposition with a linear functor preserves the property of carrying multiplication by
`a` to multiplication by `b`. -/
theorem map_smul_id_comp
    {R S : Type*} [Ring R] [Ring S] {A B C : Type*} [Category* A] [Category* B] [Category* C]
    [Preadditive A] [Preadditive B] [Preadditive C] [Linear R A] [Linear S B] [Linear S C]
    (F : A ⥤ B) (G : B ⥤ C) [Functor.Linear S G] (a : R) (b : S)
    (h : ∀ M : A, F.map (a • 𝟙 M) = b • 𝟙 (F.obj M)) (M : A) :
    (F ⋙ G).map (a • 𝟙 M) = b • 𝟙 ((F ⋙ G).obj M) := by
  show G.map (F.map (a • 𝟙 M)) = _
  rw [h M, map_smul_id_eq]
  rfl

/-- If `G` carries multiplication by `a` to multiplication by `b`, then so does any right derived
functor `RF` of `G` along a linear localization functor `L`. -/
theorem map_smul_id_rightDerived
    {R S : Type*} [Ring R] [Ring S]
    {H₁ D₁ D₂ : Type*} [Category* H₁] [Category* D₁] [Category* D₂]
    [Preadditive H₁] [Preadditive D₁] [Preadditive D₂]
    [Linear R H₁] [Linear R D₁] [Linear S D₂]
    {G : H₁ ⥤ D₂} {L : H₁ ⥤ D₁} (RF : D₁ ⥤ D₂) (α : G ⟶ L ⋙ RF)
    (W : MorphismProperty H₁) [L.IsLocalization W] [RF.IsRightDerivedFunctor α W]
    [Functor.Linear R L] (a : R) (b : S)
    (h : ∀ M : H₁, G.map (a • 𝟙 M) = b • 𝟙 (G.obj M)) (K : D₁) :
    RF.map (a • 𝟙 K) = b • 𝟙 (RF.obj K) := by
  let τ₁ : RF ⟶ RF :=
    { app := fun K ↦ RF.map (a • 𝟙 K)
      naturality := fun K K' φ ↦ by
        rw [← RF.map_comp, ← RF.map_comp, Linear.smul_comp, Category.id_comp, Linear.comp_smul,
          Category.comp_id] }
  let τ₂ : RF ⟶ RF :=
    { app := fun K ↦ b • 𝟙 (RF.obj K)
      naturality := fun K K' φ ↦ by
        rw [Linear.smul_comp, Category.id_comp, Linear.comp_smul, Category.comp_id] }
  have hτ : τ₁ = τ₂ := by
    refine Functor.rightDerived_ext RF α W RF τ₁ τ₂ ?_
    ext M
    show α.app M ≫ RF.map (a • 𝟙 (L.obj M)) = α.app M ≫ (b • 𝟙 (RF.obj (L.obj M)))
    have hn : G.map (a • 𝟙 M) ≫ α.app M = α.app M ≫ RF.map (L.map (a • 𝟙 M)) :=
      α.naturality (a • 𝟙 M)
    rw [← map_smul_id_eq L a M, ← hn, h M, Linear.smul_comp, Category.id_comp, Linear.comp_smul]
    simp
  exact NatTrans.congr_app hτ K

end Stacks.SemilinearFunctor

/-- Let `F` be an additive functor preserving the countable power of `K` and carrying
multiplication by `a` to multiplication by `b`. If the Milnor difference `1 - a · shift` is
invertible on `∏_{n ∈ ℕ} K`, then `1 - b · shift` is invertible on `∏_{n ∈ ℕ} F K`. -/
theorem isDerivedCompleteAt_map_of_center
    {A B : Type*} [CommRing A] [CommRing B]
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [Linear A C] [Linear B D] [HasProductsOfShape ℕ C] [HasProductsOfShape ℕ D]
    (F : C ⥤ D) [F.Additive] (K : C) (a : A) (b : B)
    [PreservesLimit (Discrete.functor fun _ : ℕ => K) F]
    (hid : ∀ L : C, F.map (a • 𝟙 L) = b • 𝟙 (F.obj L))
    (hK : IsDerivedCompleteAt K a) : IsDerivedCompleteAt (F.obj K) b := by
  have hsmul : ∀ {L M : C} (h : L ⟶ M), F.map (a • h) = b • F.map h := fun {L M} h ↦ by
    rw [show a • h = (a • 𝟙 L) ≫ h by rw [Linear.smul_comp, Category.id_comp],
      F.map_comp, hid L, Linear.smul_comp, Category.id_comp]
  have key : F.map (oneSubSmulShift K a) ≫ piComparison F (fun _ : ℕ ↦ K) =
      piComparison F (fun _ : ℕ ↦ K) ≫ oneSubSmulShift (F.obj K) b := by
    refine Pi.hom_ext _ _ fun n ↦ ?_
    rw [Category.assoc, Category.assoc, oneSubSmulShift_π, piComparison_comp_π,
      ← F.map_comp, oneSubSmulShift_π, F.map_sub, hsmul, Preadditive.comp_sub,
      piComparison_comp_π, Linear.comp_smul, piComparison_comp_π]
  rw [isDerivedCompleteAt_iff_isIso] at hK ⊢
  have h2 : IsIso (piComparison F (fun _ : ℕ ↦ K) ≫ oneSubSmulShift (F.obj K) b) := by
    rw [← key]
    infer_instance
  exact IsIso.of_isIso_comp_left (piComparison F (fun _ : ℕ ↦ K)) _

namespace Stacks.Cohomology.Localization

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

/-- The functor that restriction to a slice site induces on derived categories is the derived
restriction `derivedRestriction X U`. -/
def derivedRestrictionIso (X : RingedSite.{u, u, u}) (U : X.C) :
    (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory ≅
      derivedRestriction X U := by
  let F := SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U
  let W := HomotopyCategory.quasiIso
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)
  let _ : F.mapDerivedCategory.IsRightDerivedFunctor F.mapDerivedCategoryFactorsh.inv W :=
    CategoryTheory.Functor.isRightDerivedFunctor_of_inverts W F.mapDerivedCategory
      F.mapDerivedCategoryFactorsh
  exact CategoryTheory.Functor.rightDerivedUnique F.mapDerivedCategory (derivedRestriction X U)
    F.mapDerivedCategoryFactorsh.inv
    ((homotopyRestriction X U).totalRightDerivedUnit DerivedCategory.Qh W) W

end Stacks.Cohomology.Localization

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y) (V : Y.C)

/-- `f^♯` on sections over an object of the target site: the image in `𝒪'(u(V))` of a section of
`𝒪` over `V`. -/
abbrev fSharpSection (g : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (op V)) :
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op (f.u.obj V)) :=
  f.toRingedToposSiteHom.fSharpRing.hom.app (op V) g

/-- The structure sheaf of a ringed site is a sheaf of commutative rings, hence so is its
restriction to a slice site. -/
local instance isMulComm (Z : RingedSite.{u, u, u}) (U : Z.C) :
    ∀ W, IsMulCommutative
      (((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).over U).obj.obj W) := fun W ↦ by
  change IsMulCommutative (Z.O.obj.obj (op W.unop.left))
  infer_instance

/-- The same, in the spelling in which the structure sheaf of the localized ringed site is
written. -/
local instance isMulCommLocalized (Z : RingedSite.{u, u, u}) (U : Z.C) :
    ∀ W, IsMulCommutative
      ((Stacks.SheafOfModules.Tensor.ringSheaf (Z.over U).ringedTopos.O).obj.obj W) := fun W ↦ by
  change IsMulCommutative (Z.O.obj.obj (op W.unop.left))
  infer_instance

/-- Continuity of the functor underlying the localized morphism of ringed sites, in the shape
instance search keys on. -/
local instance isContinuous_localized :
    (f.localized V).toRingedToposSiteHom.u.IsContinuous
      (Y.over V).ringedTopos.J (X.over (f.u.obj V)).ringedTopos.J :=
  (f.localized V).isContinuous

attribute [local instance] Stacks.Cohomology.Localization.additive_localizedPushforward

/-- Restriction of sheaves of modules to a slice site preserves finite limits. -/
local instance overFunctorPreservesFiniteLimits (Z : RingedSite.{u, u, u}) (U : Z.C) :
    PreservesFiniteLimits
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) U) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits U

/-- Restriction of sheaves of modules to a slice site preserves finite colimits. -/
local instance overFunctorPreservesFiniteColimits (Z : RingedSite.{u, u, u}) (U : Z.C) :
    PreservesFiniteColimits
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) U) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits U

/-- The sheaves of modules on a slice site form a category linear over the centre of itself, by
the tautological ring map. -/
@[instance_reducible]
local instance overLinear (Z : RingedSite.{u, u, u}) (U : Z.C) :
    Linear (CatCenter (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).over U)))
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).over U)) :=
  Linear.ofRingMorphism (RingHom.id _)

/-- The derived category of the sheaves of modules on a slice site has countable products. -/
local instance overHasProductsOfShapeNat (Z : RingedSite.{u, u, u}) (U : Z.C) :
    HasProductsOfShape ℕ (DerivedCategory
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).over U))) :=
  hasProductsOfShape_nat_derivedCategory_over.{u, u, u} Z U

/-- Multiplication by a local section of the structure sheaf, as a central endomorphism of the
sheaves of modules on the slice site at the object over which the section lives. -/
abbrev idealScalar (Z : RingedSite.{u, u, u}) (W : Z.C)
    (g : (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj.obj (op W)) :
    CatCenter (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).over W)) :=
  Stacks.SheafOfModules.terminalSectionToEnd ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).over W)
    (Over.mk (𝟙 W)) Over.mkIdTerminal g

/-- The direct image along the localized morphism carries multiplication by `f^♯ g` on the
sheaves of modules over `u(V)` to multiplication by `g` on the sheaves of modules over `V`. -/
theorem localizedPushforward_map_idealScalar
    (g : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (op V))
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (f.u.obj V))) :
    (localizedPushforward f V).map ((idealScalar X (f.u.obj V) (fSharpSection f V g)).app M) =
      (idealScalar Y V g).app ((localizedPushforward f V).obj M) := by
  refine Stacks.SheafOfModules.map_globalSectionToEnd
    (f.localized V).toRingedToposSiteHom.fSharpRing _ _ (fun W ↦ ?_) M
  rw [Stacks.SheafOfModules.terminalSection_over_val,
    Stacks.SheafOfModules.terminalSection_over_val, fSharpRing_localized f V]
  have hnat := congrArg (fun k ↦ (ConcreteCategory.hom k) g)
    (f.toRingedToposSiteHom.fSharpRing.hom.naturality ((unop W).hom).op)
  simp only [RingCat.comp_apply] at hnat
  exact hnat

/-- Let `f : (Sh(𝒟), 𝒪') ⟶ (Sh(𝒞), 𝒪)` be a morphism of ringed sites, let `V` be an object of `𝒞`
and let `g` be a section of `𝒪` over `V`. If `T(K|_{u(V)}, f^♯g) = 0` then
`T((Rf_*K)|_V, g) = 0`. -/
theorem isDerivedCompleteAt_derivedPushforward_overFunctor
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (g : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (op V))
    (hKU : IsDerivedCompleteAt
      ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (f.u.obj V)).mapDerivedCategory.obj K)
      (idealScalar X (f.u.obj V) (fSharpSection f V g))) :
    IsDerivedCompleteAt
      ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        V).mapDerivedCategory.obj
        ((derivedPushforward.{u} f.toRingedToposSiteHom).obj K))
      (idealScalar Y V g) := by
  let AV := SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over V)
  let AU := SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (f.u.obj V))
  let AU' :=
    SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over (f.u.obj V)).ringedTopos.O))
  let : Linear (CatCenter AU) AU' := Linear.ofRingMorphism (RingHom.id (CatCenter AU))
  let AV' := SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (Y.over V).ringedTopos.O))
  let : Linear (CatCenter AV) AV' := Linear.ofRingMorphism (RingHom.id (CatCenter AV))
  have hpf : Stacks.Sheaves.InverseImageExactness.PullbackPreservesIsFlatUniv.{u} :=
    AlgebraicGeometry.RingedToposSiteHom.pullbackPreservesIsFlatUniv.{u}
  have hmos := (f.localized V).isMorphismOfSites
  have hlfd := pullbackOnHomotopy_hasLeftDerivedFunctor_of_flatPullback
    (f.localized V).toRingedToposSiteHom hmos hpf
  have hpl0 : PreservesLimitsOfSize.{0, 0} (derivedLocalizedPushforward f V) :=
    (derivedPullbackPushforwardAdjunctionOfFlatPullback
      (f.localized V).toRingedToposSiteHom hmos hpf).rightAdjoint_preservesLimits
  have hbp : PreservesLimitsOfShape (Discrete WalkingPair) (derivedLocalizedPushforward f V) :=
    hpl0.preservesLimitsOfShape
  have hadd : (derivedLocalizedPushforward f V).Additive :=
    CategoryTheory.Functor.additive_of_preserves_binary_products _
  have hnat : PreservesLimitsOfShape (Discrete ℕ) (derivedLocalizedPushforward f V) :=
    hpl0.preservesLimitsOfShape
  refine (isDerivedCompleteAt_iff_of_iso
    ((Stacks.Cohomology.Localization.derivedRestrictionIso Y V).app
        ((derivedPushforward.{u} f.toRingedToposSiteHom).obj K) ≪≫
      (derivedPushforwardOverFunctorIso f V).app K ≪≫
      (derivedLocalizedPushforward f V).mapIso
        ((Stacks.Cohomology.Localization.derivedRestrictionIso X (f.u.obj V)).app K).symm)
    (idealScalar Y V g)).mpr ?_
  refine isDerivedCompleteAt_map_of_center (derivedLocalizedPushforward f V)
    ((SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (f.u.obj V)).mapDerivedCategory.obj K)
    (idealScalar X (f.u.obj V) (fSharpSection f V g)) (idealScalar Y V g) ?_ hKU
  have hadd0 : (f.localized V).toRingedToposSiteHom.pushforwardTopos.Additive :=
    RingedToposSiteHom.pushforwardTopos_additive.{u} _
  refine Stacks.SemilinearFunctor.map_smul_id_rightDerived
    (derivedPushforward.{u} (f.localized V).toRingedToposSiteHom)
    (derivedPushforwardUnit.{u} (f.localized V).toRingedToposSiteHom)
    (HomotopyCategory.quasiIso AU' (ComplexShape.up ℤ)) _ _
    (fun M ↦ Stacks.SemilinearFunctor.map_smul_id_comp _ DerivedCategory.Qh _ _
      (Stacks.SemilinearFunctor.map_smul_id_mapHomotopyCategory _ _ _ (fun N ↦ ?_)
        (ComplexShape.up ℤ)) M)
  exact Eq.trans
    (congrArg (fun h ↦ (f.localized V).toRingedToposSiteHom.pushforwardTopos.map h)
      (Category.comp_id ((idealScalar X (f.u.obj V) (fSharpSection f V g)).app N)))
    ((localizedPushforward_map_idealScalar f V g N).trans (Category.comp_id _).symm)

/-- Let `f : (Sh(𝒟), 𝒪') ⟶ (Sh(𝒞), 𝒪)` be a morphism of ringed sites and let `ℐ ⊂ 𝒪` and
`ℐ' ⊂ 𝒪'` be sheaves of ideals such that `f^♯` sends `f^{-1}ℐ` into `ℐ'`, that is, such that
`f^♯(g) ∈ ℐ'(u(V))` for every object `V` of `𝒞` and every `g ∈ ℐ(V)`. Then `Rf_*` sends
`D_comp(𝒪', ℐ')` into `D_comp(𝒪, ℐ)`. -/
theorem derivedPushforward_isDerivedComplete
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))
    (I' : SheafOfModules.Submodule
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hI : ∀ (W : Y.C) (s : ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj.obj (op W)),
      s ∈ I.toSubmodule.obj (op W) →
        fSharpSection f W s ∈ I'.toSubmodule.obj (op (f.u.obj W)))
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hK : IsDerivedComplete.{u, u, u, u} X I' K) :
    IsDerivedComplete.{u, u, u, u} Y I
      ((derivedPushforward.{u} f.toRingedToposSiteHom).obj K) := by
  intro W s hs
  obtain ⟨_, _, _, _, hKU⟩ := hK (f.u.obj W) (fSharpSection f W s) (hI W s hs)
  exact ⟨inferInstance, overFunctorPreservesFiniteLimits Y W,
    overFunctorPreservesFiniteColimits Y W, overHasProductsOfShapeNat Y W,
    isDerivedCompleteAt_derivedPushforward_overFunctor f W K s hKU⟩

end AlgebraicGeometry.RingedSite

end
