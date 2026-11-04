module

public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.RightDerivedSheafToPresheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.AbelianDerivedExistence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedAdjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.LocalNature
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroUnitSections
public import StacksFrontier.Homology.HomComplex.RHom
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Homology.Injectives.Spaltenstein.RightDerivedFunctor
import StacksCore.Tactic.StacksAttribute

/-!
# Derived sections over an object along a continuous and cocontinuous functor of sites

Let `u : C ⥤ D` be a continuous and cocontinuous functor of sites and let
`g : Sh(C) ⟶ Sh(D)` be the corresponding morphism of topoi, so that `g⁻¹` is restriction along
`u`. For an object `U` of `C` the derived sections over `U` of an inverse image are the derived
sections over `u(U)`: `RΓ(U, g⁻¹M) = RΓ(u(U), M)` for `M` in the unbounded derived category of
abelian sheaves on `D`, and `RΓ(U, g^*M) = RΓ(u(U), M)` for `M` in the unbounded derived
category of modules over a sheaf of rings `O_D`, where the structure sheaf on `C` is
`O_C = g⁻¹O_D`.

Both statements are proved the way the source proves them. Sections over `U` are corepresented
by the extension by zero `j_{U!}O_U` of the structure sheaf of the localization of the site at
`U`, so derived sections over `U` of a complex are the morphisms out of that generator in the
derived category; the derived adjunction `Lg_! ⊣ g^*` of Stacks 07AC moves those morphisms to
the other site, where the complex is K-injective and derived morphisms are homotopy classes.
Neither proof shows that `g^*` preserves K-injectivity — which would need left exactness of
lower shriek, hence fibre products and equalizers in the source site — and neither needs it.

## Main definitions

* `Stacks.Cohomology.DerivedLowerShriek.alongFunctor_moduleSections` and
  `Stacks.Cohomology.DerivedLowerShriek.alongFunctor_abelianSections`: sections over an object
  of a sheaf of modules, as an abelian group, and of an abelian sheaf.
* `Stacks.Cohomology.DerivedLowerShriek.derivedModuleSections` and
  `Stacks.Cohomology.DerivedLowerShriek.derivedAbelianSections`: their unbounded right derived
  functors `RΓ(U, -)`.
* `Stacks.Cohomology.DerivedLowerShriek.moduleSectionsCorepresentation` and
  `Stacks.Cohomology.DerivedLowerShriek.abelianSectionsCorepresentation`: Stacks 0G1V as an
  isomorphism of additive functors, `Hom(j_{U!}O_U, -) ≅ Γ(U, -)`.

## Main results

* `Stacks.Cohomology.DerivedLowerShriek.rightDerivedUnit_isIso_of_corepresentable`: the
  right-derived unit of a corepresentable additive functor is invertible at a complex as soon as
  the localization map on morphisms out of the representing single complex into every shift of
  that complex is bijective.
* `Stacks.Cohomology.DerivedLowerShriek.map_bijective_of_adjunction_comparison`: an adjunction
  whose derived incarnation is compatible with it transports bijectivity of a localization map
  on morphisms into an object to bijectivity on morphisms into its right adjoint image.
* `Stacks.Cohomology.DerivedLowerShriek.derivedModuleSectionsRestrictionIso`: **Stacks 0DD8**,
  part (2).
* `Stacks.Cohomology.DerivedLowerShriek.derivedAbelianSectionsRestrictionIso`: **Stacks 0DD8**,
  part (1).

## Implementation notes

`Γ(U, -) ∘ g^*` is `Γ(u(U), -)` on the nose, the underlying presheaf of a restriction being
precomposition with `uᵒᵖ`, so no comparison of sections functors intervenes: the two sides of
each statement are right derived functors of one and the same functor on the unbounded homotopy
category, and the content is that the composite is one of them. That is
`Stacks.Injectives.KInjectiveResolution.isRightDerivedFunctor_of_isIso_app_quotient_isKInjective`
applied to the transported unit, and the two derived functors are then identified by
`CategoryTheory.Functor.rightDerivedUnique`.

Both statements carry the one input of Stacks 07AC that this library leaves open — the
acyclicity hypothesis of Stacks 0794, which
`Stacks.Cohomology.DerivedLowerShriek.hasPointwiseLeftDerivedLowerShriek_of_acyclic` and
`Stacks.Cohomology.DerivedLowerShriek.hasPointwiseLeftDerivedAbelianLowerShriek_of_acyclic`
reduce the existence half of Stacks 07AC to — in the shape of the two instance hypotheses of
the derived adjunction, together with the invertibility of the derived lower-shriek counit at
the single complex of the generator. The latter is the half of Stacks 0794 that says the left
derived functor is computed on the `P`-cellular complexes, specialised to a single complex with
term in `P`; it is not available as a declaration here, the resolving class of the construction
being private to
`StacksFrontier/Algebra/Homology/DerivedCategory/UnboundedComplexes.lean`, and so it is a
hypothesis.

## References

* [Stacks Project, Tag 0DD8](https://stacks.math.columbia.edu/tag/0DD8)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
* [Stacks Project, Tag 0G1V](https://stacks.math.columbia.edu/tag/0G1V)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

namespace Stacks.Cohomology.DerivedLowerShriek

/-! ### The corepresentability criterion for a right-derived unit -/

section Corepresentable

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]

/-- If `f₂ ∘ w = b ∘ f₁` with `f₁`, `f₂` and `b` bijective, then `w` is bijective. -/
private theorem bijective_of_comm {β₁ β₂ β₃ β₄ : Type*} (w : β₁ → β₂) (f₁ : β₁ → β₃)
    (f₂ : β₂ → β₄) (b : β₃ → β₄) (h : ∀ a, f₂ (w a) = b (f₁ a))
    (hf₁ : Function.Bijective f₁) (hf₂ : Function.Bijective f₂) (hb : Function.Bijective b) :
    Function.Bijective w :=
  (hf₂.of_comp_iff' w).mp ((funext h : f₂ ∘ w = b ∘ f₁) ▸ hb.comp hf₁)

/-- **Postcomposition on the cohomology of a Hom complex is postcomposition in the homotopy
category.** The map induced on the degree-`n` cohomology of `Hom^•(K, -)` by `g : L ⟶ L'` is
invertible as soon as postcomposition with `g⟦n⟧` on morphisms out of `K` in the homotopy
category is bijective. -/
theorem isIso_homologyMap_homComplexPostcomp
    (K : CochainComplex A ℤ) {L L' : CochainComplex A ℤ} (g : L ⟶ L') (n : ℤ)
    (h : Function.Bijective
      (fun a : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K ⟶
          (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (L⟦n⟧) =>
        a ≫ (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (g⟦n⟧'))) :
    IsIso (HomologicalComplex.homologyMap (homComplexPostcomp K g) n) := by
  have hb : ∀ M : CochainComplex A ℤ, Function.Bijective
      (CochainComplex.HomComplex.CohomologyClass.toHom :
        CochainComplex.HomComplex.CohomologyClass K M n → _) := fun M =>
    CochainComplex.HomComplex.CohomologyClass.toHom_bijective K M n
  have hcomm : ∀ c : CochainComplex.HomComplex.CohomologyClass K L n,
      CochainComplex.HomComplex.CohomologyClass.toHom (cohomologyClassPostcomp K g n c) =
        CochainComplex.HomComplex.CohomologyClass.toHom c ≫
          (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (g⟦n⟧') :=
    fun c => toHom_cohomologyClassPostcomp g n c
  have hbij : Function.Bijective (cohomologyClassPostcomp K g n) :=
    bijective_of_comm _ _ _ _ hcomm (hb L) (hb L') h
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨fun x y hxy => ?_, fun z => ?_⟩
  · refine (CochainComplex.HomComplex.homologyAddEquiv K L n).injective (hbij.injective ?_)
    rw [homologyAddEquiv_postcomp K g n x, homologyAddEquiv_postcomp K g n y]
    exact congrArg _ hxy
  · obtain ⟨c, hc⟩ := hbij.surjective (CochainComplex.HomComplex.homologyAddEquiv K L' n z)
    refine ⟨(CochainComplex.HomComplex.homologyAddEquiv K L n).symm c,
      (CochainComplex.HomComplex.homologyAddEquiv K L' n).injective ?_⟩
    rw [← homologyAddEquiv_postcomp K g n, AddEquiv.apply_symm_apply, hc]

/-- **The corepresentable quasi-isomorphism criterion.** For an additive functor `T` corepresented
by an object `A₀`, a morphism of complexes `g` becomes a quasi-isomorphism after applying `T`
degreewise as soon as postcomposition with every shift of `g` on morphisms out of the single
complex `A₀[0]` in the homotopy category is bijective. -/
theorem quasiIso_mapHomologicalComplex_of_corepresentable
    (T : A ⥤ AddCommGrpCat.{v₁}) [T.Additive] (A₀ : A)
    (e : preadditiveCoyoneda.obj (op A₀) ≅ T)
    {L L' : CochainComplex A ℤ} (g : L ⟶ L')
    (h : ∀ n : ℤ, Function.Bijective
      (fun a : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
            ((CochainComplex.singleFunctor A 0).obj A₀) ⟶
          (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (L⟦n⟧) =>
        a ≫ (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (g⟦n⟧'))) :
    QuasiIso ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map g) := by
  set c := ComplexShape.up ℤ with hc
  let i : ∀ Z : CochainComplex A ℤ,
      ((CochainComplex.singleFunctor A 0).obj A₀).HomComplex Z ≅
        (T.mapHomologicalComplex c).obj Z := fun Z =>
    Stacks.Cohomology.Locality.homComplexSingleIsoCoyoneda A₀ Z ≪≫
      (NatIso.mapHomologicalComplex e c).app Z
  have hnat : homComplexPostcomp ((CochainComplex.singleFunctor A 0).obj A₀) g ≫ (i L').hom =
      (i L).hom ≫ (T.mapHomologicalComplex c).map g := by
    dsimp only [i, Iso.trans_hom, Iso.app_hom]
    rw [← Category.assoc, Stacks.Cohomology.homComplexSingleIsoCoyoneda_naturality A₀ g,
      Category.assoc, (NatIso.mapHomologicalComplex e c).hom.naturality g, ← Category.assoc]
  have key : (i L).inv ≫ homComplexPostcomp ((CochainComplex.singleFunctor A 0).obj A₀) g ≫
        (i L').hom = (T.mapHomologicalComplex c).map g := by
    rw [hnat, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  refine ⟨fun n => ?_⟩
  rw [quasiIsoAt_iff_isIso_homologyMap, ← key,
    HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
  have h1 : IsIso (HomologicalComplex.homologyMap (i L).inv n) :=
    AlgebraicGeometry.RingedSite.isIso_homologyMap_of_iso (i L).symm n
  have h2 := isIso_homologyMap_homComplexPostcomp
    ((CochainComplex.singleFunctor A 0).obj A₀) g n (h n)
  have h3 : IsIso (HomologicalComplex.homologyMap (i L').hom n) :=
    AlgebraicGeometry.RingedSite.isIso_homologyMap_of_iso (i L') n
  infer_instance

variable [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{v₂} A]

omit [HasDerivedCategory.{v₂} A] in
/-- Every cochain complex admits a quasi-isomorphism to a `K`-injective complex, by the
functorial `K`-injective resolutions of Stacks 079P. -/
theorem exists_quasiIso_isKInjective_of_isGrothendieckAbelian (K : CochainComplex A ℤ) :
    ∃ (I : CochainComplex A ℤ) (f : K ⟶ I), I.IsKInjective ∧ QuasiIso f :=
  ⟨(Stacks.Injectives.kInjectiveResolutionFunctor A).obj K,
    (Stacks.Injectives.kInjectiveResolutionInclusion A).app K, inferInstance, inferInstance⟩

/-- The unit of a right derived functor is invertible at a `K`-injective complex. This is the
second conclusion of Stacks 070K, with its hypothesis discharged by the functorial `K`-injective
resolutions of Stacks 079P. -/
theorem alongFunctor_rightDerivedUnit_isIso_at_kInjective {H : Type u₃} [Category.{v₃} H]
    (F : HomotopyCategory A (ComplexShape.up ℤ) ⥤ H)
    (RF : DerivedCategory A ⥤ H)
    (α : F ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (I : CochainComplex A ℤ) [I.IsKInjective] :
    IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    F exists_quasiIso_isKInjective_of_isGrothendieckAbelian).2 _ RF α I inferInstance

/-- **A right-derived unit is invertible at a complex whose `K`-injective resolution it already
inverts.** -/
theorem rightDerivedUnit_isIso_of_quasiIso_resolution {H : Type u₃} [Category.{v₃} H]
    (F : HomotopyCategory A (ComplexShape.up ℤ) ⥤ H)
    (RF : DerivedCategory A ⥤ H)
    (α : F ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    {Z I : CochainComplex A ℤ} (q : Z ⟶ I) [QuasiIso q] [I.IsKInjective]
    (hq : IsIso (F.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map q))) :
    IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Z)) := by
  have h1 := alongFunctor_rightDerivedUnit_isIso_at_kInjective F RF α I
  have h2 : IsIso ((DerivedCategory.Qh ⋙ RF).map
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map q)) :=
    inferInstanceAs (IsIso (RF.map (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map q))))
  have hnat := α.naturality ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map q)
  have : IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Z) ≫
      (DerivedCategory.Qh ⋙ RF).map
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map q)) := by
    rw [← hnat]
    exact Iso.isIso_hom (asIso (F.map ((HomotopyCategory.quotient A
      (ComplexShape.up ℤ)).map q)) ≪≫ asIso (α.app _))
  exact IsIso.of_isIso_comp_right _ ((DerivedCategory.Qh ⋙ RF).map
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map q))

private theorem bijective_postcomp_isIso {B : Type u₃} [Category.{v₃} B] {X Y Y' : B}
    (φ : Y ⟶ Y') [IsIso φ] : Function.Bijective (fun a : X ⟶ Y => a ≫ φ) := by
  constructor
  · intro a a' ha
    exact (cancel_mono φ).mp ha
  · intro b
    exact ⟨b ≫ inv φ, by simp⟩

omit [IsGrothendieckAbelian.{w} A] in
/-- Bijectivity of the localization map on morphisms into `Y` and into `Y'` transfers along an
isomorphism `Y ⟶ Y'` of the homotopy category to bijectivity of postcomposition with it. -/
theorem bijective_postcomp_of_qh_bijective
    {X Y Y' : HomotopyCategory A (ComplexShape.up ℤ)} (m : Y ⟶ Y')
    [IsIso (DerivedCategory.Qh.map m)]
    (hY : Function.Bijective (DerivedCategory.Qh.map : (X ⟶ Y) → _))
    (hY' : Function.Bijective (DerivedCategory.Qh.map : (X ⟶ Y') → _)) :
    Function.Bijective (fun a : X ⟶ Y => a ≫ m) :=
  bijective_of_comm _ DerivedCategory.Qh.map DerivedCategory.Qh.map
    (fun b => b ≫ DerivedCategory.Qh.map m)
    (fun a => DerivedCategory.Qh.map_comp a m) hY hY'
    (bijective_postcomp_isIso (DerivedCategory.Qh.map m))

omit [IsGrothendieckAbelian.{w} A] in
/-- Bijectivity of the localization map on morphisms into an object transfers along an
isomorphism of that object. -/
theorem qh_map_bijective_of_iso
    {X Y Y' : HomotopyCategory A (ComplexShape.up ℤ)} (φ : Y ≅ Y')
    (hY : Function.Bijective (DerivedCategory.Qh.map : (X ⟶ Y) → _)) :
    Function.Bijective (DerivedCategory.Qh.map : (X ⟶ Y') → _) := by
  refine bijective_of_comm _ (fun a : X ⟶ Y' => a ≫ φ.inv)
    (fun b => b ≫ DerivedCategory.Qh.map φ.inv) DerivedCategory.Qh.map ?_
    (bijective_postcomp_isIso φ.inv) (bijective_postcomp_isIso (DerivedCategory.Qh.map φ.inv)) hY
  intro a
  exact (DerivedCategory.Qh.map_comp a φ.inv).symm

/-- **The right-derived unit of a corepresentable additive functor is invertible at a complex `Z`
as soon as the localization map on morphisms from the representing single complex into every
shift of `Z` is bijective.** -/
theorem rightDerivedUnit_isIso_of_corepresentable
    (T : A ⥤ AddCommGrpCat.{v₁}) [T.Additive] (A₀ : A)
    (e : preadditiveCoyoneda.obj (op A₀) ≅ T)
    [HasDerivedCategory.{v₄} AddCommGrpCat.{v₁}]
    (RT : DerivedCategory A ⥤ DerivedCategory AddCommGrpCat.{v₁})
    (α : T.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RT)
    [RT.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (Z : CochainComplex A ℤ)
    (hZ : ∀ n : ℤ, Function.Bijective (DerivedCategory.Qh.map :
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
          ((CochainComplex.singleFunctor A 0).obj A₀) ⟶
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (Z⟦n⟧)) → _)) :
    IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Z)) := by
  refine rightDerivedUnit_isIso_of_quasiIso_resolution _ RT α
    ((Stacks.Injectives.kInjectiveResolutionInclusion A).app Z) ?_
  have hqi : QuasiIso ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((Stacks.Injectives.kInjectiveResolutionInclusion A).app Z)) := by
    refine quasiIso_mapHomologicalComplex_of_corepresentable T A₀ e _ (fun n => ?_)
    refine bijective_postcomp_of_qh_bijective _ (hZ n) ?_
    exact CochainComplex.IsKInjective.Qh_map_bijective _
      (((Stacks.Injectives.kInjectiveResolutionFunctor A).obj Z)⟦n⟧)
  show IsIso (DerivedCategory.Qh.map ((T.mapHomotopyCategory (ComplexShape.up ℤ)).map
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
      ((Stacks.Injectives.kInjectiveResolutionInclusion A).app Z))))
  rw [Functor.mapHomotopyCategory_map]
  exact isIso_Qh_map_quotient_map_of_quasiIso
    ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((Stacks.Injectives.kInjectiveResolutionInclusion A).app Z))

end Corepresentable

/-! ### Transporting bijectivity of a localization map along an adjunction -/

/-- **An adjunction compatible with its derived incarnation transports bijectivity of the
localization map.** If the unit of the derived adjunction factors the image of the unit of the
underlying adjunction through the two comparison transformations, and both comparisons are
invertible at the objects in question, then bijectivity of the localization map on morphisms
`L X ⟶ Y` gives bijectivity on morphisms `X ⟶ R Y`. -/
theorem map_bijective_of_adjunction_comparison
    {A : Type u₁} {B : Type u₂} {DA : Type u₃} {DB : Type u₄}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} DA] [Category.{v₄} DB]
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R)
    (QA : A ⥤ DA) (QB : B ⥤ DB)
    {LD : DA ⥤ DB} {RD : DB ⥤ DA} (adjD : LD ⊣ RD)
    (a : QA ⋙ LD ⟶ L ⋙ QB) (b : R ⋙ QA ⟶ QB ⋙ RD)
    (h : ∀ X, adjD.unit.app (QA.obj X) ≫ RD.map (a.app X) =
      QA.map (adj.unit.app X) ≫ b.app (L.obj X))
    (X : A) (Y : B) [IsIso (a.app X)] [IsIso (b.app Y)]
    (hQ : Function.Bijective (QB.map : (L.obj X ⟶ Y) → _)) :
    Function.Bijective (QA.map : (X ⟶ R.obj Y) → _) := by
  let ε : (L.obj X ⟶ Y) ≃ (QA.obj X ⟶ RD.obj (QB.obj Y)) :=
    (Equiv.ofBijective _ hQ).trans
      ((Iso.homCongr (asIso (a.app X)).symm (Iso.refl _)).trans (adjD.homEquiv _ _))
  have he (f : L.obj X ⟶ Y) : ε f = QA.map (adj.homEquiv X Y f) ≫ b.app Y := by
    show adjD.unit.app _ ≫ RD.map ((a.app X) ≫ QB.map f ≫ 𝟙 _) = _
    rw [Category.comp_id, Functor.map_comp, ← Category.assoc, h]
    simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
    congr 1
    exact (b.naturality f).symm
  have hcomp : Function.Bijective (fun f : X ⟶ R.obj Y => QA.map f ≫ b.app Y) := by
    have hb := ε.bijective.comp (adj.homEquiv X Y).symm.bijective
    simpa only [Function.comp_def, he, Equiv.apply_symm_apply] using hb
  exact (Function.Bijective.of_comp_iff' (bijective_postcomp_isIso (b.app Y)) _).mp hcomp

/-! ### Right derived functors recognised on K-injective complexes -/

section Recognition

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
  [HasDerivedCategory.{v₂} A] {H : Type u₃} [Category.{v₃} H]

/-- A candidate for the right derived functor of a functor on the homotopy category is the right
derived functor as soon as its unit is invertible at the K-injective complexes. This is
`Stacks.Injectives.KInjectiveResolution.isRightDerivedFunctor_of_isIso_app_quotient_isKInjective`
with its resolution hypothesis discharged from Grothendieck abelianness. -/
theorem isRightDerivedFunctor_of_isIso_app_kInjective
    (F : HomotopyCategory A (ComplexShape.up ℤ) ⥤ H)
    (R : DerivedCategory A ⥤ H) (α : F ⟶ DerivedCategory.Qh ⋙ R)
    (hα : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I))) :
    R.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  Stacks.Injectives.KInjectiveResolution.isRightDerivedFunctor_of_isIso_app_quotient_isKInjective
    exists_quasiIso_isKInjective_of_isGrothendieckAbelian F R α hα

omit [HasDerivedCategory.{v₂} A] in
/-- Every functor out of the unbounded homotopy category of a Grothendieck abelian category has
a right derived functor, by the functorial `K`-injective resolutions of Stacks 079P. -/
@[sga "4 XVII 4.1.2" "partial"]
theorem alongFunctor_hasRightDerivedFunctor_of_isGrothendieckAbelian
    (F : HomotopyCategory A (ComplexShape.up ℤ) ⥤ H) :
    F.HasRightDerivedFunctor (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  have : F.HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{v₁,
      v₃, 0, u₁, u₃, 0} F exists_quasiIso_isKInjective_of_isGrothendieckAbelian).1
  Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor F _

end Recognition

/-! ### Sections over an object of a site -/

section Sections

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- Sections of an abelian sheaf over an object of a site. -/
abbrev alongFunctor_abelianSections (U : C) : Sheaf J AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  (sheafSections J AddCommGrpCat.{u}).obj (op U)

/-- Sections over `U` of abelian sheaves form an additive functor. -/
instance additive_abelianSections (U : C) : (alongFunctor_abelianSections J U).Additive where
  map_add := rfl

/-- Sections of a sheaf of modules over an object of a site, as an abelian group. -/
abbrev alongFunctor_moduleSections (R : Sheaf J RingCat.{u}) (U : C) :
    SheafOfModules.{u} R ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf R ⋙ alongFunctor_abelianSections J U

/-- Sections over `U` of sheaves of modules form an additive functor. -/
instance additive_moduleSections (R : Sheaf J RingCat.{u}) (U : C) :
    (alongFunctor_moduleSections J R U).Additive where
  map_add := rfl

attribute [local instance] HasDerivedCategory.standard

/-- Sections over `U` of sheaves of modules have an unbounded right derived functor. -/
instance hasRightDerivedFunctor_moduleSections (R : Sheaf J RingCat.{u}) (U : C) :
    ((alongFunctor_moduleSections J R U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} R) (ComplexShape.up ℤ)) :=
  alongFunctor_hasRightDerivedFunctor_of_isGrothendieckAbelian _

/-- Sections over `U` of abelian sheaves have an unbounded right derived functor. -/
instance hasRightDerivedFunctor_abelianSections (U : C)
    [HasSheafify J AddCommGrpCat.{u}] :
    ((alongFunctor_abelianSections J U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{u}) (ComplexShape.up ℤ)) :=
  alongFunctor_hasRightDerivedFunctor_of_isGrothendieckAbelian _

/-- `RΓ(U, -)` on sheaves of modules: the unbounded right derived functor of sections over `U`.
-/
abbrev derivedModuleSections (R : Sheaf J RingCat.{u}) (U : C) :
    DerivedCategory (SheafOfModules.{u} R) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  ((alongFunctor_moduleSections J R U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{u} R) (ComplexShape.up ℤ))

/-- `RΓ(U, -)` on abelian sheaves: the unbounded right derived functor of sections over `U`. -/
abbrev derivedAbelianSections (U : C) [HasSheafify J AddCommGrpCat.{u}] :
    DerivedCategory (Sheaf J AddCommGrpCat.{u}) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  ((alongFunctor_abelianSections J U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{u}) (ComplexShape.up ℤ))

/-- **Stacks 0G1V as an isomorphism of additive functors.** Sections over `U` of a sheaf of
modules are the morphisms out of the extension by zero `j_{U!}O_U` of the structure sheaf of
the localization of the site at `U`. -/
def moduleSectionsCorepresentation (R : Sheaf J RingCat.{u}) (U : C)
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    preadditiveCoyoneda.obj (op (extensionByZeroUnit R U)) ≅ alongFunctor_moduleSections J R U := by
  refine NatIso.ofComponents (fun F => ?_) ?_
  · exact (show (_ ≃+ (F.val.obj (op U) : Type u)) from
      { Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv J R U F with
        map_add' := by
          intro f g
          change Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv J R U F (f + g) =
            Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv J R U F f +
              Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv J R U F g
          rfl }).toAddCommGrpIso
  · intro F G g
    ext φ
    exact Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv_naturality J R U φ g

/-- **Morphisms out of `j_{U!} ℤ_U` are sections over `U`, as an isomorphism of additive
functors.** -/
def abelianSectionsCorepresentation (U : C) [HasSheafify J AddCommGrpCat.{u}] :
    preadditiveCoyoneda.obj (op (extensionByZeroUnitAb.{u} J U)) ≅
      alongFunctor_abelianSections J U := by
  refine NatIso.ofComponents (fun F => ?_) ?_
  · exact (show (_ ≃+ (F.obj.obj (op U) : Type u)) from
      { extensionByZeroUnitAbHomEquiv.{u} J U F with
        map_add' := by
          intro f g
          change extensionByZeroUnitAbHomEquiv.{u} J U F (f + g) =
            extensionByZeroUnitAbHomEquiv.{u} J U F f +
              extensionByZeroUnitAbHomEquiv.{u} J U F g
          rfl }).toAddCommGrpIso
  · intro F G g
    ext φ
    exact extensionByZeroUnitAbHomEquiv_naturality.{u} J φ g

end Sections

/-! ### Stacks 0DD8, part (2): sheaves of modules -/

section Modules

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K] (O : Sheaf K RingCat.{u}) (U : C)

attribute [local instance] HasDerivedCategory.standard

omit [f.IsCocontinuous J K] in
/-- **`Γ(U, g^*(-)) = Γ(u(U), -)`.** The underlying presheaf of a restriction is precomposition
with `uᵒᵖ`, so sections over `U` of a restricted sheaf of modules are sections over `u(U)`. -/
theorem restrictionModules_comp_moduleSections :
    restrictionModules J K f O ⋙ alongFunctor_moduleSections J (inverseImageRing J K f O) U =
      alongFunctor_moduleSections K O (f.obj U) :=
  rfl

variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(SheafOfModules.pushforward.{u} (F := f) (idRingMap J K f O)).IsRightAdjoint]
  [(lowerShriekOnHomotopy J K f O ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
    (sourceQuasiIso J K f O)]
  [IsGrothendieckAbelian.{u} (SheafOfModules.{u} O)]
  [(derivedLowerShriek J K f O ⋙ derivedRestriction J K f O).IsLeftDerivedFunctor
    ((Functor.associator DerivedCategory.Qh (derivedLowerShriek J K f O)
        (derivedRestriction J K f O)).inv ≫
      Functor.whiskerRight (derivedLowerShriekComparison J K f O)
        (derivedRestriction J K f O))
    (sourceQuasiIso J K f O)]

/-- The invertibility of the derived lower-shriek counit at the single complex of the
extension by zero `j_{U!}O_U`. This is the half of Stacks 0794 saying that the left derived
functor is computed on the `P`-cellular complexes, at a single complex whose term lies in `P`;
it is the one input of Stacks 07AC not available as a declaration in this library. -/
abbrev DerivedLowerShriekComputesGenerator : Prop :=
  IsIso ((derivedLowerShriekComparison J K f O).app
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
      ((CochainComplex.singleFunctor _ 0).obj
        (extensionByZeroUnit (inverseImageRing J K f O) U))))

variable [IsGrothendieckAbelian.{u} (SheafOfModules.{u} (inverseImageRing J K f O))]

/-- **The restriction of a K-injective complex of modules computes derived sections over an
object.** Sections over `U` are corepresented by `j_{U!}O_U` (Stacks 0G1V), and the derived
adjunction of Stacks 07AC turns morphisms out of that generator into morphisms out of its
derived lower shriek on the other site, where the complex is K-injective. -/
theorem moduleSections_restriction_rightDerivedUnit_isIso
    (hgen : DerivedLowerShriekComputesGenerator J K f O U)
    (I : CochainComplex (SheafOfModules.{u} O) ℤ) [I.IsKInjective]
    (RT : DerivedCategory (SheafOfModules.{u} (inverseImageRing J K f O)) ⥤
      DerivedCategory AddCommGrpCat.{u})
    (α : (alongFunctor_moduleSections J (inverseImageRing J K f O) U).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RT)
    [RT.IsRightDerivedFunctor α (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (inverseImageRing J K f O)) (ComplexShape.up ℤ))] :
    IsIso (α.app ((restrictionOnHomotopy J K f O).obj
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := by
  have hgen' := hgen
  refine rightDerivedUnit_isIso_of_corepresentable
    (alongFunctor_moduleSections J (inverseImageRing J K f O) U)
    (extensionByZeroUnit (inverseImageRing J K f O) U)
    (moduleSectionsCorepresentation J (inverseImageRing J K f O) U) RT α
    (((restrictionModules J K f O).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
    (fun n => ?_)
  refine qh_map_bijective_of_iso
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
      ((((restrictionModules J K f O).mapHomologicalComplex
        (ComplexShape.up ℤ)).commShiftIso n).app I)) ?_
  exact map_bijective_of_adjunction_comparison (homotopyAdjunction J K f O)
    DerivedCategory.Qh DerivedCategory.Qh (derivedLowerShriekAdjunction J K f O)
    (derivedLowerShriekComparison J K f O) (derivedRestrictionComparison J K f O)
    (derivedLowerShriekAdjunction_unit_fac J K f O) _ _
    (CochainComplex.IsKInjective.Qh_map_bijective _ (I⟦n⟧))

/-- The unit exhibiting derived restriction followed by derived sections over `U` as a
candidate right derived functor of sections over `u(U)`. -/
def restrictedModuleSectionsUnit :
    (alongFunctor_moduleSections K O (f.obj U)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ (derivedRestriction J K f O ⋙
        derivedModuleSections J (inverseImageRing J K f O) U) :=
  (Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso
    (eqToIso (restrictionModules_comp_moduleSections J K f O U))
    (ComplexShape.up ℤ)).symm DerivedCategory.Qh).hom ≫
  (Functor.associator _ _ _).hom ≫
  Functor.whiskerLeft (restrictionOnHomotopy J K f O)
    (((alongFunctor_moduleSections J (inverseImageRing J K f O) U).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (inverseImageRing J K f O)) (ComplexShape.up ℤ))) ≫
  (Functor.associator _ _ _).inv ≫
  Functor.whiskerRight (derivedRestrictionComparison J K f O)
    (derivedModuleSections J (inverseImageRing J K f O) U) ≫
  (Functor.associator _ _ _).hom

/-- **Stacks 0DD8, part (2).** Let `u : C ⥤ D` be a continuous and cocontinuous functor of
sites, let `g : Sh(C) ⟶ Sh(D)` be the corresponding morphism of topoi, let `O_D` be a sheaf of
rings on `D` and let `O_C = g⁻¹O_D`. For every object `U` of `C` and every `M` in the unbounded
derived category of `O_D`-modules, `RΓ(U, g^*M) = RΓ(u(U), M)`, naturally in `M`. -/
@[stacks 0DD8 "part (2)"]
def derivedModuleSectionsRestrictionIso
    (hgen : DerivedLowerShriekComputesGenerator J K f O U) :
    derivedRestriction J K f O ⋙ derivedModuleSections J (inverseImageRing J K f O) U ≅
      derivedModuleSections K O (f.obj U) := by
  have hβ : (derivedRestriction J K f O ⋙
      derivedModuleSections J (inverseImageRing J K f O) U).IsRightDerivedFunctor
        (restrictedModuleSectionsUnit J K f O U)
        (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ)) := by
    refine isRightDerivedFunctor_of_isIso_app_kInjective _ _ _ (fun I hI => ?_)
    have := hI
    have := moduleSections_restriction_rightDerivedUnit_isIso J K f O U hgen I _
      (((alongFunctor_moduleSections J (inverseImageRing J K f O) U).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso
          (SheafOfModules.{u} (inverseImageRing J K f O)) (ComplexShape.up ℤ)))
    dsimp only [restrictedModuleSectionsUnit]
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    infer_instance
  exact Functor.rightDerivedUnique _ _ (restrictedModuleSectionsUnit J K f O U)
    (((alongFunctor_moduleSections K O (f.obj U)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))

end Modules

/-! ### Stacks 0DD8, part (1): abelian sheaves -/

section Abelian

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K] (U : C)

attribute [local instance] HasDerivedCategory.standard

omit [f.IsCocontinuous J K] in
/-- **`Γ(U, g⁻¹(-)) = Γ(u(U), -)`.** The underlying presheaf of a restriction is precomposition
with `uᵒᵖ`, so sections over `U` of a restricted abelian sheaf are sections over `u(U)`. -/
theorem abelianRestriction_comp_abelianSections :
    f.sheafPushforwardContinuous AddCommGrpCat.{u} J K ⋙ alongFunctor_abelianSections J U =
      alongFunctor_abelianSections K (f.obj U) :=
  rfl

variable [HasSheafify J AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
  [(f.sheafPushforwardContinuous AddCommGrpCat.{u} J K).IsRightAdjoint]
  [∀ F : Cᵒᵖ ⥤ AddCommGrpCat.{u}, f.op.HasPointwiseRightKanExtension F]
  [(abelianLowerShriekOnHomotopy.{u} J K f ⋙
    DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
    (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{u}) (ComplexShape.up ℤ))]
  [IsGrothendieckAbelian.{u} (Sheaf K AddCommGrpCat.{u})]
  [(derivedAbelianLowerShriek.{u} J K f ⋙
    derivedAbelianRestriction.{u} J K f).IsLeftDerivedFunctor
    ((Functor.associator DerivedCategory.Qh (derivedAbelianLowerShriek.{u} J K f)
      (derivedAbelianRestriction.{u} J K f)).inv ≫
      Functor.whiskerRight (derivedAbelianLowerShriekComparison.{u} J K f)
        (derivedAbelianRestriction.{u} J K f))
    (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{u}) (ComplexShape.up ℤ))]

/-- The invertibility of the derived lower-shriek counit at the single complex of the free
abelian sheaf `j_{U!} ℤ_U`. This is the half of Stacks 0794 saying that the left derived
functor is computed on the `P`-cellular complexes, at a single complex whose term lies in `P`;
it is the one input of Stacks 07AC not available as a declaration in this library. -/
abbrev DerivedAbelianLowerShriekComputesGenerator : Prop :=
  IsIso ((derivedAbelianLowerShriekComparison.{u} J K f).app
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
      ((CochainComplex.singleFunctor _ 0).obj (extensionByZeroUnitAb.{u} J U))))

variable [IsGrothendieckAbelian.{u} (Sheaf J AddCommGrpCat.{u})]

/-- **The restriction of a K-injective complex of abelian sheaves computes derived sections
over an object.** Sections over `U` are corepresented by `j_{U!} ℤ_U`, and the derived
adjunction of Stacks 07AC turns morphisms out of that generator into morphisms out of its
derived lower shriek on the other site, where the complex is K-injective. -/
theorem abelianSections_restriction_rightDerivedUnit_isIso
    (hgen : DerivedAbelianLowerShriekComputesGenerator J K f U)
    (I : CochainComplex (Sheaf K AddCommGrpCat.{u}) ℤ) [I.IsKInjective]
    (RT : DerivedCategory (Sheaf J AddCommGrpCat.{u}) ⥤ DerivedCategory AddCommGrpCat.{u})
    (α : (alongFunctor_abelianSections J U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RT)
    [RT.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{u}) (ComplexShape.up ℤ))] :
    IsIso (α.app ((abelianRestrictionOnHomotopy.{u} J K f).obj
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := by
  have hgen' := hgen
  refine rightDerivedUnit_isIso_of_corepresentable (alongFunctor_abelianSections J U)
    (extensionByZeroUnitAb.{u} J U) (abelianSectionsCorepresentation J U) RT α
    (((abelianRestriction.{u} J K f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
    (fun n => ?_)
  refine qh_map_bijective_of_iso
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
      ((((abelianRestriction.{u} J K f).mapHomologicalComplex
        (ComplexShape.up ℤ)).commShiftIso n).app I)) ?_
  exact map_bijective_of_adjunction_comparison (abelianHomotopyAdjunction.{u} J K f)
    DerivedCategory.Qh DerivedCategory.Qh (derivedAbelianLowerShriekAdjunction.{u} J K f)
    (derivedAbelianLowerShriekComparison.{u} J K f)
    (derivedAbelianRestrictionComparison.{u} J K f)
    (derivedAbelianLowerShriekAdjunction_unit_fac.{u} J K f) _ _
    (CochainComplex.IsKInjective.Qh_map_bijective _ (I⟦n⟧))

/-- The unit exhibiting derived restriction followed by derived sections over `U` as a
candidate right derived functor of sections over `u(U)`. -/
def restrictedAbelianSectionsUnit :
    (alongFunctor_abelianSections K (f.obj U)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ (derivedAbelianRestriction.{u} J K f ⋙
        derivedAbelianSections J U) :=
  (Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso
    (eqToIso (abelianRestriction_comp_abelianSections J K f U))
    (ComplexShape.up ℤ)).symm DerivedCategory.Qh).hom ≫
  (Functor.associator _ _ _).hom ≫
  Functor.whiskerLeft (abelianRestrictionOnHomotopy.{u} J K f)
    (((alongFunctor_abelianSections J U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{u}) (ComplexShape.up ℤ))) ≫
  (Functor.associator _ _ _).inv ≫
  Functor.whiskerRight (derivedAbelianRestrictionComparison.{u} J K f)
    (derivedAbelianSections J U) ≫
  (Functor.associator _ _ _).hom

/-- **Stacks 0DD8, part (1).** Let `u : C ⥤ D` be a continuous and cocontinuous functor of
sites and let `g : Sh(C) ⟶ Sh(D)` be the corresponding morphism of topoi. For every object `U`
of `C` and every `M` in the unbounded derived category of abelian sheaves on `D`,
`RΓ(U, g⁻¹M) = RΓ(u(U), M)`, naturally in `M`. -/
@[stacks 0DD8 "part (1)"]
def derivedAbelianSectionsRestrictionIso
    (hgen : DerivedAbelianLowerShriekComputesGenerator J K f U) :
    derivedAbelianRestriction.{u} J K f ⋙ derivedAbelianSections J U ≅
      derivedAbelianSections K (f.obj U) := by
  have hβ : (derivedAbelianRestriction.{u} J K f ⋙
      derivedAbelianSections J U).IsRightDerivedFunctor
        (restrictedAbelianSectionsUnit J K f U)
        (HomotopyCategory.quasiIso (Sheaf K AddCommGrpCat.{u}) (ComplexShape.up ℤ)) := by
    refine isRightDerivedFunctor_of_isIso_app_kInjective _ _ _ (fun I hI => ?_)
    have := hI
    have := abelianSections_restriction_rightDerivedUnit_isIso J K f U hgen I _
      (((alongFunctor_abelianSections J U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{u}) (ComplexShape.up ℤ)))
    dsimp only [restrictedAbelianSectionsUnit]
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    infer_instance
  exact Functor.rightDerivedUnique _ _ (restrictedAbelianSectionsUnit J K f U)
    (((alongFunctor_abelianSections K (f.obj U)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf K AddCommGrpCat.{u}) (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso (Sheaf K AddCommGrpCat.{u}) (ComplexShape.up ℤ))

end Abelian

end Stacks.Cohomology.DerivedLowerShriek

end
