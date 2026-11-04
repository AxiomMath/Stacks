module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkColimit
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.CategoryTheory.Localization.LeftDerivedByResolutions
public import StacksFrontier.Homology.KFlat.ScalarBaseChange
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Unconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.OnARingedSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.StalkCriterion
public import StacksFrontier.Topology.Sheaves.Functors.Module.SemilinearStalk
public import StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic
public import StacksFrontier.Topology.Sheaves.Modules.StalkExactness

/-!
# Stalks of the derived pullback of sheaves of modules on a scheme

Let `f : X ⟶ Y` be a morphism of schemes and `x : X`. The stalk functor
`Stacks.ModuleSkyscraper.modulesStalkFunctor X x : X.Modules ⥤ ModuleCat 𝒪_{X,x}` is exact, so
it induces a functor `derivedStalkFunctor x` on unbounded derived categories, and the stalk
formula for the underived pullback (Stacks 0098) lifts to a comparison

`L f^* ⋙ (−)_x  ≅  (−)_{f x} ⋙ (𝒪_{X,x} ⊗ᴸ_{𝒪_{Y,f x}} −)`

between the derived pullback followed by the stalk at `x` and the stalk at `f x` followed by
derived extension of scalars along `f^♯_x`. The comparison is determined by its compatibility
with the two derived-functor counits.

## Main definitions

* `AlgebraicGeometry.derivedStalkFunctor`: the stalk functor on unbounded derived categories of
  sheaves of modules on a scheme.
* `AlgebraicGeometry.pullbackComparisonOnComplex`: the canonical map from the derived pullback
  of a complex to the degreewise pullback of that complex.
* `AlgebraicGeometry.derivedPullbackStalkIso`: the derived stalk comparison.

## Main results

* `AlgebraicGeometry.kFlat_modulesStalkFunctor`: the degreewise stalk of a K-flat complex of
  `𝒪_X`-modules is K-flat over the local ring at the point.
* `AlgebraicGeometry.exists_unique_derivedPullbackStalkIso`: the derived stalk comparison exists
  and is the unique natural isomorphism compatible with the two derived-functor counits.
* `AlgebraicGeometry.derivedPullbackStalkIso_comp_comparison`: that compatibility, as an
  equation.

## Implementation notes

Two spellings of the stalk of a sheaf of modules occur, and they are kept apart deliberately.
`AlgebraicGeometry.SheafOfModules.stalkFunctor` takes modules over the `RingCat`-valued stalk of
the ring sheaf, which is the ring the K-flatness criterion of Stacks 06YB is stated over;
`Stacks.ModuleSkyscraper.modulesStalkFunctor` takes modules over the `CommRingCat`-valued stalk
`𝒪_{X,x}`, which is the ring `AlgebraicGeometry.Scheme.Hom.stalkMap` and
`ModuleCat.extendScalars` are stated over. `restrictScalarsStalkIso` is the comparison between
them, and `stalkComplexIso` its degreewise form; everything downstream of
`kFlat_modulesStalkFunctor` uses the second spelling only.

The model of the derived category is free: the statements below take
`[HasDerivedCategory.{w} ·]` for each of the four categories involved as a binder rather than
fixing `HasDerivedCategory.standard`. A statement proved for one model says nothing about
another, the two derived categories being merely equivalent and not equal, and both the locally
small model with morphisms in `Type u` and the standard model with morphisms in `Type (u + 1)`
are wanted here. `hasDerivedCategory_ringedSpaceModules` carries such a binder between the two
spellings `X.Modules` and `SheafOfModules (structureSheafRing X.toSheafedSpace)` of one and the
same category, the second being the one the derived pullback of a morphism of ringed spaces is
stated in.

The uniqueness statement is obtained by running the universal property of a left derived functor
twice: the K-flat complexes resolve every complex of `𝒪_Y`-modules (Stacks 06YF), both sides of
the comparison are isomorphic to degreewise pullback on them, and a natural transformation
between left derived functors is determined by its restriction to the resolving class.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 06YB](https://stacks.math.columbia.edu/tag/06YB)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry RingedSpaceModuleAdjunction

universe u w

namespace AlgebraicGeometry

/-- A model for the derived category of `𝒪_X`-modules is a model for the derived category of
sheaves of modules over the sheaf of rings of the ringed space underlying `X`: `X.Modules` and
`SheafOfModules (structureSheafRing X.toSheafedSpace)` are the same category in two spellings, the
scheme-level one and the ringed-space one in which the derived pullback is stated. -/
local instance hasDerivedCategory_ringedSpaceModules {Z : Scheme.{u}}
    [h : HasDerivedCategory.{w} Z.Modules] :
    HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing Z.toSheafedSpace)) := h

/-- The same for the third spelling of the sheaf of rings of `X`, the one the K-flatness of a
complex of `𝒪_X`-modules is stated over. -/
local instance hasDerivedCategory_tensorRingSheafModules {Z : Scheme.{u}}
    [h : HasDerivedCategory.{w} Z.Modules] :
    HasDerivedCategory.{w}
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.toSheafedSpace.sheaf)) := h

variable {X : Scheme.{u}} (x : X)

/-! ### The two spellings of the stalk ring -/

/-- The `RingCat`-valued stalk of the sheaf of rings of a scheme is the local ring `𝒪_{X,x}`.
This is `SemilinearStalk.commStalkRingEquiv` read at the sheaf of rings of a scheme. -/
abbrev ringCatStalkRingEquiv :
    ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) x) ≃+* ToType (X.presheaf.stalk x) :=
  SemilinearStalk.commStalkRingEquiv X.presheaf x

/-- The stalk of a sheaf of `𝒪_X`-modules over the local ring `𝒪_{X,x}` is the stalk over the
`RingCat`-valued stalk of the ring sheaf, with its scalars restricted along
`ringCatStalkRingEquiv`. The two have the same underlying abelian group; the content is that the
two scalar actions correspond, which is `SemilinearStalk.comm_smul_eq`. -/
def restrictScalarsStalkObjIso (M : X.Modules) :
    (ModuleCat.restrictScalars (ringCatStalkRingEquiv x).symm.toRingHom).obj
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).obj M) ≅
      (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj M where
  hom := ConcreteCategory.ofHom (C := ModuleCat.{u} (ToType (X.presheaf.stalk x)))
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun r m => by
        have h := SemilinearStalk.comm_smul_eq X.presheaf x M.val
          ((ringCatStalkRingEquiv x).symm r) m
        rw [RingEquiv.apply_symm_apply] at h
        exact h.symm }
  inv := ConcreteCategory.ofHom (C := ModuleCat.{u} (ToType (X.presheaf.stalk x)))
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun r m => by
        have h := SemilinearStalk.comm_smul_eq X.presheaf x M.val
          ((ringCatStalkRingEquiv x).symm r) m
        rw [RingEquiv.apply_symm_apply] at h
        exact h }
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- `restrictScalarsStalkObjIso` applied degreewise to a cochain complex. -/
def stalkComplexIso (P : CochainComplex X.Modules ℤ) :
    ((ModuleCat.restrictScalars (ringCatStalkRingEquiv x).symm.toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
      (((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) ≅
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P :=
  HomologicalComplex.Hom.isoOfComponents (fun i => restrictScalarsStalkObjIso x (P.X i))
    (fun _ _ _ => rfl)

/-! ### Exactness of the stalk functor -/

/-- The stalk functor `Stacks.ModuleSkyscraper.modulesStalkFunctor X x` preserves finite
limits. -/
instance modulesStalkFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (Stacks.ModuleSkyscraper.modulesStalkFunctor X x) := by
  have h : PreservesFiniteLimits (Stacks.ModuleSkyscraper.modulesStalkFunctor X x ⋙
      forget₂ (ModuleCat.{u} (ToType (X.presheaf.stalk x))) AddCommGrpCat.{u}) := by
    change PreservesFiniteLimits (Scheme.Modules.toPresheaf X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
    exact comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_reflects_of_preserves
    (Stacks.ModuleSkyscraper.modulesStalkFunctor X x)
    (forget₂ (ModuleCat.{u} (ToType (X.presheaf.stalk x))) AddCommGrpCat.{u})

/-- The stalk functor `Stacks.ModuleSkyscraper.modulesStalkFunctor X x` preserves colimits. -/
instance modulesStalkFunctor_preservesColimits :
    PreservesColimits (Stacks.ModuleSkyscraper.modulesStalkFunctor X x) :=
  (Stacks.ModuleSkyscraper.modulesStalkSkyAdjunction X x).leftAdjoint_preservesColimits

/-- The stalk functor `Stacks.ModuleSkyscraper.modulesStalkFunctor X x` is additive. -/
instance modulesStalkFunctor_additive :
    (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).Additive :=
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (Stacks.ModuleSkyscraper.modulesStalkFunctor X x)
  Functor.additive_of_preservesBinaryBiproducts _

/-! ### K-flatness of the stalk complex -/

open CategoryTheory.MonoidalCategory in
/-- **Restriction of scalars along a ring isomorphism preserves K-flatness.** It agrees with
extension of scalars along the inverse, which preserves K-flatness by Stacks 06Y1. -/
lemma kFlat_restrictScalars_ringEquiv {R S : Type u} [CommRing R] [CommRing S] (e : S ≃+* R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : K.KFlat) :
    CochainComplex.KFlat
      (((ModuleCat.restrictScalars e.toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) := by
  let i := (ModuleCat.extendRestrictScalarsAdj.{u} e.symm.toRingHom).leftAdjointUniq
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).toAdjunction
  exact CochainComplex.KFlat.of_iso ((NatIso.mapHomologicalComplex i (ComplexShape.up ℤ)).app K)
    (CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{u, u, u} e.symm.toRingHom K hK)

/-- **The stalk of a K-flat complex is K-flat.** If `P` is a K-flat complex of `𝒪_X`-modules
then the complex of its stalks at `x` is K-flat over the local ring `𝒪_{X,x}`.

This is the stalk criterion for K-flatness (Stacks 06YB) read over `𝒪_{X,x}` rather than over
the `RingCat`-valued stalk of the ring sheaf; the passage between the two is `stalkComplexIso`
together with `kFlat_restrictScalars_ringEquiv`. -/
lemma kFlat_modulesStalkFunctor (P : CochainComplex X.Modules ℤ)
    (hP : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex X.toSheafedSpace P) :
    CochainComplex.KFlat
      (((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) := by
  have h := (Stacks.SheafOfModules.KFlatStalkCriterion.kFlat_iff_stalkwise X.sheaf P).1 hP x
  have h2 := kFlat_restrictScalars_ringEquiv (ringCatStalkRingEquiv x).symm _ h
  exact CochainComplex.KFlat.of_iso (stalkComplexIso x P) h2

/-! ### The derived stalk functor -/

/-- **The derived stalk functor on a scheme.** The stalk functor at `x` is exact, so it induces
a functor from the unbounded derived category of sheaves of `𝒪_X`-modules to the unbounded
derived category of `𝒪_{X,x}`-modules. -/
def derivedStalkFunctor [HasDerivedCategory.{w} X.Modules]
    [HasDerivedCategory.{w} (ModuleCat.{u} (X.presheaf.stalk x))] :
    DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat.{u} (X.presheaf.stalk x)) :=
  (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapDerivedCategory

/-- The canonical map from the derived pullback of a complex of `𝒪_Y`-modules to the
degreewise pullback of that complex. It is the comparison of the left derived functor of
`f^*`, read through the identification of the homotopy-category quotient with `Q`. -/
def pullbackComparisonOnComplex {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} Y.Modules]
    (P : CochainComplex Y.Modules ℤ) :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        f.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((Scheme.Modules.pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        f.toLRSHom.toShHom).mapIso
      ((DerivedCategory.quotientCompQhIso Y.Modules).app P).symm).hom ≫
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
        f.toLRSHom.toShHom).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P) ≫
    (DerivedCategory.Qh.mapIso
      (((modulePullback f.toLRSHom.toShHom).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).app P)).hom ≫
    ((DerivedCategory.quotientCompQhIso X.Modules).app _).hom

/-- Two left derived functors of the same functor, each computed by the same resolving class,
are uniquely isomorphic compatibly with their comparisons.

This is `CategoryTheory.LeftDerivedByResolutions.exists_leftDerivedIso_of_resolutions` with the
`IsLeftDerivedFunctor` hypothesis on the first functor replaced by invertibility of its
comparison on the resolving class, and with the uniqueness clause added; uniqueness is
`CategoryTheory.Functor.leftDerived_ext`. -/
private lemma exists_unique_iso_of_resolutions
    {C D H : Type*} [Category C] [Category D] [Category H]
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
    (P : ObjectProperty C)
    (hP : ∀ Z, ∃ Y, P Y ∧ ∃ s : Y ⟶ Z, W s)
    (L : C ⥤ D) [L.IsLocalization W] (F G : D ⥤ H) (U : C ⥤ H)
    (α : L ⋙ F ⟶ U) (β : L ⋙ G ⟶ U)
    (hα : ∀ Z, P Z → IsIso (α.app Z))
    (hβ : ∀ Z, P Z → IsIso (β.app Z)) :
    ∃! e : F ≅ G, ∀ Z, e.hom.app (L.obj Z) ≫ β.app Z = α.app Z := by
  have hU : ∀ {Z W' : C} (s : Z ⟶ W'), W s → P Z → P W' → IsIso (U.map s) := by
    intro Z W' s hs hZ hW'
    have := hα Z hZ
    have := hα W' hW'
    have : IsIso (L.map s) := Localization.inverts L W s hs
    have : IsIso ((L ⋙ F).map s) := by
      show IsIso (F.map (L.map s)); infer_instance
    rw [← isIso_comp_left_iff (α.app Z), ← α.naturality s]
    infer_instance
  have hP' : ∀ Z, ∃ (Y : C) (_ : P Y) (s : Y ⟶ Z), W s := fun Z =>
    (hP Z).imp fun _ ⟨hY, h⟩ => ⟨hY, h⟩
  have := LeftDerivedByResolutions.isLeftDerivedFunctor_of_isIso_on_resolutions
    W P hP' U hU L F α hα
  have := LeftDerivedByResolutions.isLeftDerivedFunctor_of_isIso_on_resolutions
    W P hP' U hU L G β hβ
  refine ⟨Functor.leftDerivedNatIso F G α β W (Iso.refl U), fun Z => ?_, ?_⟩
  · exact (Functor.leftDerivedNatTrans_app F G α β W (𝟙 U) Z).trans (Category.comp_id _)
  · refine fun e' he' => Iso.ext <| G.leftDerived_ext β W F _ _ ?_
    ext Z
    exact (he' Z).trans
      ((Functor.leftDerivedNatTrans_app F G α β W (𝟙 U) Z).trans (Category.comp_id _)).symm

/-- `exists_unique_iso_of_resolutions` for the derived category of an abelian category, with the
resolving class given on cochain complexes rather than on the homotopy category.

The comparison with the homotopy-category form is the content: a natural transformation out of
`Qh ⋙ F` is the lift of one out of `Q ⋙ F`, and the two normalization conditions correspond
because every object of the homotopy category is a quotient of a cochain complex. -/
private lemma exists_unique_iso_on_complexes
    {A B : Type*} [Category A] [Abelian A] [HasDerivedCategory A] [Category B]
    (P : ObjectProperty (CochainComplex A ℤ))
    (hP : ∀ K, ∃ L, P L ∧ ∃ s : L ⟶ K, QuasiIso s)
    (F G : DerivedCategory A ⥤ B)
    (U : CochainComplex A ℤ ⥤ B) (Uh : HomotopyCategory A (ComplexShape.up ℤ) ⥤ B)
    (uIso : HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙ Uh ≅ U)
    (α : DerivedCategory.Q ⋙ F ⟶ U) (β : DerivedCategory.Q ⋙ G ⟶ U)
    (hα : ∀ K, P K → IsIso (α.app K))
    (hβ : ∀ K, P K → IsIso (β.app K)) :
    ∃! e : F ≅ G, ∀ K, e.hom.app (DerivedCategory.Q.obj K) ≫ β.app K = α.app K := by
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let lift (H : DerivedCategory A ⥤ B) (γ : DerivedCategory.Q ⋙ H ⟶ U) :
      DerivedCategory.Qh ⋙ H ⟶ Uh := Quotient.natTransLift _
    (Functor.whiskerRight (DerivedCategory.quotientCompQhIso A).hom H ≫ γ ≫ uIso.inv)
  let αh := lift F α
  let βh := lift G β
  have hPh (K : HomotopyCategory A (ComplexShape.up ℤ)) :
      ∃ L, P L.as ∧ ∃ s : L ⟶ K, HomotopyCategory.quasiIso A (ComplexShape.up ℤ) s := by
    obtain ⟨L, hL, s, hs⟩ := hP K.as
    exact ⟨q.obj L, hL, q.map s, (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  have hlift (H : DerivedCategory A ⥤ B) (γ : DerivedCategory.Q ⋙ H ⟶ U)
      (hγ : ∀ K, P K → IsIso (γ.app K)) (K : HomotopyCategory A (ComplexShape.up ℤ))
      (hK : P K.as) : IsIso ((lift H γ).app K) := by
    have := hγ K.as hK
    change IsIso (H.map ((DerivedCategory.quotientCompQhIso A).hom.app K.as) ≫
      γ.app K.as ≫ uIso.inv.app K.as)
    infer_instance
  have compat (e : F ≅ G) :
      (∀ K, e.hom.app (DerivedCategory.Qh.obj K) ≫ βh.app K = αh.app K) ↔
        (∀ K, e.hom.app (DerivedCategory.Q.obj K) ≫ β.app K = α.app K) := by
    have hc (K : CochainComplex A ℤ) :
        (e.hom.app (DerivedCategory.Qh.obj (q.obj K)) ≫ βh.app (q.obj K) = αh.app (q.obj K)) ↔
          (e.hom.app (DerivedCategory.Q.obj K) ≫ β.app K = α.app K) := by
      show (e.hom.app _ ≫ (G.map ((DerivedCategory.quotientCompQhIso A).hom.app K) ≫
        β.app K ≫ uIso.inv.app K) =
          F.map ((DerivedCategory.quotientCompQhIso A).hom.app K) ≫
            α.app K ≫ uIso.inv.app K) ↔ _
      rw [← Category.assoc, ← e.hom.naturality, Category.assoc, cancel_epi, ← Category.assoc,
        cancel_mono]
    exact ⟨fun h K => (hc K).1 (h (q.obj K)), fun h K => (hc K.as).2 (h K.as)⟩
  obtain ⟨e, he, hu⟩ := exists_unique_iso_of_resolutions
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) (fun K => P K.as) hPh
    DerivedCategory.Qh F G Uh αh βh (hlift F α hα) (hlift G β hβ)
  exact ⟨e, (compat e).1 he, fun e' he' => hu e' ((compat e').2 he')⟩

/-- A K-flat complex computes the derived pullback: on it the comparison from the derived
pullback to the degreewise pullback is invertible. -/
public lemma isIso_pullbackComparisonOnComplex_of_kFlat {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} Y.Modules]
    (P : CochainComplex Y.Modules ℤ)
    (hP : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y.toSheafedSpace P) :
    IsIso (pullbackComparisonOnComplex f P) := by
  have hcmp := LeftDerivedByResolutions.isIso_app_of_resolutions
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y.toSheafedSpace))
      (ComplexShape.up ℤ))
    (Stacks.Cohomology.KFlatDerivedPullback.IsKFlat Y.toSheafedSpace)
    (Stacks.Cohomology.KFlatDerivedPullback.hasResolutions_isKFlat Y.toSheafedSpace)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackOnHomotopy f.toLRSHom.toShHom)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackInvertsQuasiIso_isKFlat
      f.toLRSHom.toShHom)
    DerivedCategory.Qh
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toLRSHom.toShHom)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
      f.toLRSHom.toShHom) _ hP
  have h1 : IsIso (((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      f.toLRSHom.toShHom).mapIso
      ((DerivedCategory.quotientCompQhIso Y.Modules).app P).symm).hom) := inferInstance
  have h3 : IsIso ((DerivedCategory.Qh.mapIso
      (((modulePullback f.toLRSHom.toShHom).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).app P)).hom) := inferInstance
  have h4 : IsIso (((DerivedCategory.quotientCompQhIso X.Modules).app
      (((modulePullback f.toLRSHom.toShHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P)).hom) := inferInstance
  unfold pullbackComparisonOnComplex
  exact IsIso.comp_isIso' h1 (IsIso.comp_isIso' hcmp (IsIso.comp_isIso' h3 h4))

/-- **The derived stalk comparison for a pullback is uniquely determined.** There is exactly one
natural isomorphism

`L f^* ⋙ (−)_x  ≅  (−)_{f x} ⋙ (𝒪_{X,x} ⊗ᴸ_{𝒪_{Y,f x}} −)`

compatible with the comparison of the derived pullback, the comparison of derived extension of
scalars, and the stalk formula for the underived pullback. -/
theorem exists_unique_derivedPullbackStalkIso {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} Y.Modules]
    [HasDerivedCategory.{w} (ModuleCat.{u} (X.presheaf.stalk x))]
    [HasDerivedCategory.{w} (ModuleCat.{u} (Y.presheaf.stalk (f x)))] :
    let T := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (f.stalkMap x).hom
    ∃! e : Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        f.toLRSHom.toShHom ⋙ derivedStalkFunctor x ≅ derivedStalkFunctor (f x) ⋙ T.functor,
      ∀ P : CochainComplex Y.Modules ℤ,
        e.hom.app (DerivedCategory.Q.obj P) ≫
            T.functor.map ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y
              (f x)).mapDerivedCategoryFactors.hom.app P) ≫
            T.comparison.app (((Stacks.ModuleSkyscraper.modulesStalkFunctor Y
              (f x)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) =
          (derivedStalkFunctor x).map (pullbackComparisonOnComplex f P) ≫
            (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapDerivedCategoryFactors.hom.app
              (((Scheme.Modules.pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex
                (Stacks.ModuleSkyscraper.pullbackStalkIso f x).symm
                (ComplexShape.up ℤ)).hom.app P) := by
  let T := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (f.stalkMap x).hom
  let D := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toLRSHom.toShHom
  let S := Stacks.ModuleSkyscraper.modulesStalkFunctor Y (f x)
  let E := ModuleCat.extendScalars (f.stalkMap x).hom
  have : E.IsLeftAdjoint := (ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom).isLeftAdjoint
  have : E.Additive := CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _
    (by change PreservesFiniteColimits E; infer_instance)
  let F := D ⋙ derivedStalkFunctor x
  let G := derivedStalkFunctor (f x) ⋙ T.functor
  let U := (S ⋙ E).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q
  let Uh := (S ⋙ E).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  let uIso : HomotopyCategory.quotient Y.Modules (ComplexShape.up ℤ) ⋙ Uh ≅ U :=
    Functor.isoWhiskerRight ((S ⋙ E).mapHomotopyCategoryFactors (ComplexShape.up ℤ))
        DerivedCategory.Qh ≪≫
      Functor.isoWhiskerLeft ((S ⋙ E).mapHomologicalComplex (ComplexShape.up ℤ))
        (DerivedCategory.quotientCompQhIso _)
  let α₀ : DerivedCategory.Q ⋙ D ⟶
      (Scheme.Modules.pullback f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso Y.Modules).inv D ≫
      Functor.whiskerLeft (HomotopyCategory.quotient Y.Modules (ComplexShape.up ℤ))
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
          f.toLRSHom.toShHom) ≫
      Functor.whiskerRight
        ((modulePullback f.toLRSHom.toShHom).mapHomotopyCategoryFactors
          (ComplexShape.up ℤ)).hom DerivedCategory.Qh ≫
      Functor.whiskerLeft
        ((Scheme.Modules.pullback f).mapHomologicalComplex (ComplexShape.up ℤ))
        (DerivedCategory.quotientCompQhIso X.Modules).hom
  let α : DerivedCategory.Q ⋙ F ⟶ U :=
    Functor.whiskerRight α₀ (derivedStalkFunctor x) ≫
      Functor.whiskerLeft
        ((Scheme.Modules.pullback f).mapHomologicalComplex (ComplexShape.up ℤ))
        (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapDerivedCategoryFactors.hom ≫
      Functor.whiskerRight
        ((NatIso.mapHomologicalComplex (Stacks.ModuleSkyscraper.pullbackStalkIso f x).symm
          (ComplexShape.up ℤ)).hom) DerivedCategory.Q
  let β : DerivedCategory.Q ⋙ G ⟶ U :=
    Functor.whiskerRight S.mapDerivedCategoryFactors.hom T.functor ≫
      Functor.whiskerLeft (S.mapHomologicalComplex (ComplexShape.up ℤ)) T.comparison
  have hα (P : CochainComplex Y.Modules ℤ)
      (hP : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y.toSheafedSpace P) :
      IsIso (α.app P) := by
    have h : α₀.app P = pullbackComparisonOnComplex f P := rfl
    have hc := isIso_pullbackComparisonOnComplex_of_kFlat f P hP
    have g1 : IsIso ((derivedStalkFunctor x).map (pullbackComparisonOnComplex f P)) :=
      ((derivedStalkFunctor x).mapIso (@asIso _ _ _ _ _ hc)).isIso_hom
    have g2 : IsIso (((Stacks.ModuleSkyscraper.modulesStalkFunctor X
        x).mapDerivedCategoryFactors.app
        (((Scheme.Modules.pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)).hom) :=
      inferInstance
    have g3 : IsIso (DerivedCategory.Q.map
        (((NatIso.mapHomologicalComplex
          (Stacks.ModuleSkyscraper.pullbackStalkIso f x).symm
          (ComplexShape.up ℤ)).app P).hom)) :=
      (DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex
        (Stacks.ModuleSkyscraper.pullbackStalkIso f x).symm (ComplexShape.up ℤ)).app P)).isIso_hom
    show IsIso ((derivedStalkFunctor x).map (α₀.app P) ≫ _ ≫ _)
    rw [h]
    exact IsIso.comp_isIso' g1 (IsIso.comp_isIso' g2 g3)
  have hβ (P : CochainComplex Y.Modules ℤ)
      (hP : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y.toSheafedSpace P) :
      IsIso (β.app P) := by
    have := T.comparison_isIso_of_kFlat _ (kFlat_modulesStalkFunctor (f x) P hP)
    show IsIso (T.functor.map (S.mapDerivedCategoryFactors.hom.app P) ≫ T.comparison.app _)
    infer_instance
  have hP (K : CochainComplex Y.Modules ℤ) :
      ∃ P, Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y.toSheafedSpace P ∧
        ∃ s : P ⟶ K, QuasiIso s := by
    obtain ⟨P, s, hP, -, hs, -⟩ :=
      Stacks.Cohomology.KFlatDerivedPullback.exists_kFlatResolution Y.toSheafedSpace K
    exact ⟨P, hP, s, hs⟩
  obtain ⟨e, he, hu⟩ := exists_unique_iso_on_complexes
    (fun P => Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y.toSheafedSpace P) hP
    F G U Uh uIso α β hα hβ
  exact ⟨e, fun P => he P, fun e' he' => hu e' fun P => he' P⟩

/-- **Stalks of the derived pullback.** The stalk at `x` of the derived pullback of `K` along
`f` is the derived base change of the stalk of `K` at `f x` along `f^♯_x`, naturally in `K`.

This is the isomorphism `exists_unique_derivedPullbackStalkIso` produces; its characterizing
property is `derivedPullbackStalkIso_comp_comparison`. -/
def derivedPullbackStalkIso {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} Y.Modules]
    [HasDerivedCategory.{w} (ModuleCat.{u} (X.presheaf.stalk x))]
    [HasDerivedCategory.{w} (ModuleCat.{u} (Y.presheaf.stalk (f x)))] :
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toLRSHom.toShHom ⋙
        derivedStalkFunctor x ≅
      derivedStalkFunctor (f x) ⋙
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (f.stalkMap x).hom).functor :=
  Classical.choose (exists_unique_derivedPullbackStalkIso f x).exists

/-- The derived stalk comparison is compatible with the two derived-functor counits and with
the stalk formula for the underived pullback. This equation characterizes
`derivedPullbackStalkIso` uniquely. -/
theorem derivedPullbackStalkIso_comp_comparison {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} Y.Modules]
    [HasDerivedCategory.{w} (ModuleCat.{u} (X.presheaf.stalk x))]
    [HasDerivedCategory.{w} (ModuleCat.{u} (Y.presheaf.stalk (f x)))]
    (P : CochainComplex Y.Modules ℤ) :
    let T := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (f.stalkMap x).hom
    (derivedPullbackStalkIso f x).hom.app (DerivedCategory.Q.obj P) ≫
        T.functor.map ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y
          (f x)).mapDerivedCategoryFactors.hom.app P) ≫
        T.comparison.app (((Stacks.ModuleSkyscraper.modulesStalkFunctor Y
          (f x)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) =
      (derivedStalkFunctor x).map (pullbackComparisonOnComplex f P) ≫
        (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapDerivedCategoryFactors.hom.app
          (((Scheme.Modules.pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (Stacks.ModuleSkyscraper.pullbackStalkIso f x).symm
            (ComplexShape.up ℤ)).hom.app P) :=
  (Classical.choose_spec (exists_unique_derivedPullbackStalkIso f x).exists) P

end AlgebraicGeometry

end
