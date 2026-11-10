module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackInvertible.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonIso
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.DescentData
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison

/-!
# Pulling back homomorphisms of invertible modules along a section

Let `f : X ⟶ Y` be a morphism of schemes whose comparison map `𝒪_Y ⟶ f_*𝒪_X` is an
isomorphism, and let `σ : Y ⟶ X` be a section of `f`. Then for invertible `𝒪_X`-modules `L`
and `M`, pullback along `σ` is a bijection from `L ⟶ M` to `σ^*L ⟶ σ^*M` as soon as the two
are isomorphic at all. So an isomorphism `σ^*L ≅ σ^*M` downstairs has exactly one preimage
upstairs: isomorphisms of invertible modules on `X` can be *normalised* by prescribing their
restriction along the section.

The mechanism is that `σ^*` is bijective on endomorphisms of the structure sheaf: on `𝒪_Y`
the hypothesis on `f` makes the unit of `f^* ⊣ f_*` an isomorphism, so `f^*` is bijective on
endomorphisms of `𝒪_Y`, and `σ^* ∘ f^*` is the identity. Tensoring by an invertible module is
an equivalence commuting with pullback, so the same holds for the endomorphisms of any
invertible module.

## Main definitions

* `Stacks.Picard.modulePullbackUnitIso` — the comparison `f^*𝒪_Y ≅ 𝒪_X`.
* `Stacks.Picard.sectionNormalizedIso` — the unique isomorphism of two invertible modules on
  `X` restricting along the section to a prescribed isomorphism downstairs.

## Main results

* `Stacks.Picard.bijective_sectionPullback_map` — pullback along the section is a bijection on
  homomorphisms between two isomorphic invertible modules.
* `Stacks.Picard.existsUnique_sectionPullback_mapIso` and
  `Stacks.Picard.injective_sectionPullback_mapIso` — the corresponding statements for
  isomorphisms.
* `Stacks.Picard.sectionNormalizedIso_trans` and `Stacks.Picard.sectionNormalizedIso_symm` —
  normalisation is compatible with composition and inversion, which is what makes a family of
  normalised isomorphisms agree on overlaps.
* `Stacks.Picard.bijective_pullHom_section` — the same bijectivity for the homomorphisms between
  two pullbacks of invertible modules, in the form the presheaf of morphisms of a pseudofunctor
  restricts them.

## References

* [Stacks Project, Tag 0B9N](https://stacks.math.columbia.edu/tag/0B9N)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Picard

/-! ### Transport of bijectivity of the action of a functor on homomorphisms -/

/-- A functor isomorphic to one that is bijective on a hom-set is bijective on it too. -/
private theorem bijective_map_of_natIso {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (e : F ≅ G) (A B : C)
    (h : Function.Bijective (G.map : (A ⟶ B) → (G.obj A ⟶ G.obj B))) :
    Function.Bijective (F.map : (A ⟶ B) → (F.obj A ⟶ F.obj B)) := by
  have heq : (F.map : (A ⟶ B) → (F.obj A ⟶ F.obj B)) =
      (Iso.homCongr (e.app A).symm (e.app B).symm) ∘ G.map := by
    funext a
    simp only [Function.comp_apply, Iso.homCongr_apply, Iso.symm_inv, Iso.symm_hom]
    change F.map a = e.hom.app A ≫ G.map a ≫ e.inv.app B
    rw [← e.hom.naturality_assoc]
    simp
  rw [heq]
  exact (Iso.homCongr (e.app A).symm (e.app B).symm).bijective.comp h

/-- Bijectivity of a functor on an endomorphism monoid transports along an isomorphism. -/
private theorem bijective_map_end_of_iso {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {L M : C} (e : L ≅ M)
    (h : Function.Bijective (F.map : (L ⟶ L) → (F.obj L ⟶ F.obj L))) :
    Function.Bijective (F.map : (M ⟶ M) → (F.obj M ⟶ F.obj M)) := by
  have heq : (F.map : (M ⟶ M) → (F.obj M ⟶ F.obj M)) =
      (Iso.homCongr (F.mapIso e) (F.mapIso e)) ∘ F.map ∘ (Iso.homCongr e.symm e.symm) := by
    funext a
    simp [Iso.homCongr_apply]
  rw [heq]
  exact (Iso.homCongr (F.mapIso e) (F.mapIso e)).bijective.comp
    (h.comp (Iso.homCongr e.symm e.symm).bijective)

/-- If `F` is bijective on a hom-set and `F ⋙ G` is the identity, then `G` is bijective on the
image hom-set. -/
private theorem bijective_map_of_retraction {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (G : D ⥤ C) (e : F ⋙ G ≅ 𝟭 C) (A B : C)
    (h : Function.Bijective (F.map : (A ⟶ B) → (F.obj A ⟶ F.obj B))) :
    Function.Bijective (G.map : (F.obj A ⟶ F.obj B) → (G.obj (F.obj A) ⟶ G.obj (F.obj B))) := by
  have hcomp : Function.Bijective ((F ⋙ G).map :
      (A ⟶ B) → (G.obj (F.obj A) ⟶ G.obj (F.obj B))) :=
    bijective_map_of_natIso e A B Function.bijective_id
  exact (Function.Bijective.of_comp_iff _ h).mp hcomp

/-- Bijectivity of a functor on a hom-set passes to the images under a fully faithful
endofunctor commuting with it. -/
private theorem bijective_map_of_tensor_comparison {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (T : C ⥤ C) (U : D ⥤ D) (hT : T.FullyFaithful) (hU : U.FullyFaithful)
    (e : T ⋙ F ≅ F ⋙ U) (A B : C)
    (h : Function.Bijective (F.map : (A ⟶ B) → (F.obj A ⟶ F.obj B))) :
    Function.Bijective (F.map : (T.obj A ⟶ T.obj B) → (F.obj (T.obj A) ⟶ F.obj (T.obj B))) := by
  have hcomp : Function.Bijective ((T ⋙ F).map : (A ⟶ B) → _) :=
    bijective_map_of_natIso e A B ((hU.map_bijective _ _).comp h)
  exact (Function.Bijective.of_comp_iff _ (hT.map_bijective A B)).mp hcomp

/-- An equivalence of categories is fully faithful, with the equivalence supplied as data
rather than found by instance resolution. -/
private def fullyFaithfulOfIsEquivalence {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    (h : F.IsEquivalence) : F.FullyFaithful :=
  have := h
  Functor.FullyFaithful.ofFullyFaithful F

/-- Bijectivity of a functor on an endomorphism monoid extends to the homomorphisms into an
isomorphic object. -/
private theorem bijective_map_of_iso {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {L M : C} (e : L ≅ M)
    (h : Function.Bijective (F.map : (L ⟶ L) → (F.obj L ⟶ F.obj L))) :
    Function.Bijective (F.map : (L ⟶ M) → (F.obj L ⟶ F.obj M)) := by
  refine ⟨fun a b hab => (cancel_mono e.inv).mp
    (h.injective (by simp only [Functor.map_comp, hab])), fun a => ?_⟩
  obtain ⟨b, hb⟩ := h.surjective (a ≫ F.map e.inv)
  refine ⟨b ≫ e.hom, ?_⟩
  rw [Functor.map_comp, hb, Category.assoc, ← Functor.map_comp, e.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.comp_id]

/-- A functor bijective on the endomorphisms of two isomorphic objects reflects an isomorphism
between their images, uniquely. -/
private theorem existsUnique_iso_of_bijective_end {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {L M : C} (e : L ≅ M)
    (hL : Function.Bijective (F.map : (L ⟶ L) → (F.obj L ⟶ F.obj L)))
    (hM : Function.Bijective (F.map : (M ⟶ M) → (F.obj M ⟶ F.obj M)))
    (a : F.obj L ≅ F.obj M) :
    ∃! b : L ≅ M, F.mapIso b = a := by
  obtain ⟨b, hb⟩ := (bijective_map_of_iso F e hL).surjective a.hom
  obtain ⟨c, hc⟩ := (bijective_map_of_iso F e.symm hM).surjective a.inv
  have hbc : b ≫ c = 𝟙 L := hL.injective (by simp [hb, hc])
  have hcb : c ≫ b = 𝟙 M := hM.injective (by simp [hb, hc])
  exact ⟨⟨b, c, hbc, hcb⟩, Iso.ext hb, fun d hd =>
    Iso.ext ((bijective_map_of_iso F e hL).injective ((congrArg Iso.hom hd).trans hb.symm))⟩

/-! ### Pullback along a morphism with invariant structure sheaf -/

/-- The comparison of the unit module with the pushforward of the unit module is an
isomorphism as soon as the comparison map of sheaves of rings is. -/
private theorem unitToPushforwardObjUnit_isIso {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
    {R : Sheaf K RingCat.{u}} {S : Sheaf J RingCat.{u}} [F.IsContinuous J K]
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R) [IsIso φ] :
    IsIso (SheafOfModules.unitToPushforwardObjUnit φ) := by
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf _),
    ← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _), NatTrans.isIso_iff_isIso_app]
  intro V
  change IsIso ((forget₂ RingCat AddCommGrpCat).map (φ.hom.app V))
  infer_instance

/-- A left adjoint is bijective on homomorphisms into an object at which the unit is an
isomorphism. -/
private theorem bijective_map_of_unit_isIso {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (M N : C) [IsIso (adj.unit.app N)] :
    Function.Bijective (F.map : (M ⟶ N) → (F.obj M ⟶ F.obj N)) := by
  rw [← (adj.homEquiv M (F.obj N)).bijective.of_comp_iff']
  have heq : (adj.homEquiv M (F.obj N)) ∘ F.map = fun a : M ⟶ N => a ≫ adj.unit.app N := by
    funext a
    simp only [Function.comp_apply, Adjunction.homEquiv_unit]
    exact (adj.unit.naturality a).symm
  rw [heq]
  exact ⟨fun _ _ h => (cancel_mono _).mp h, fun a => ⟨a ≫ inv (adj.unit.app N), by simp⟩⟩

/-- **Pullback along a morphism of schemes with invariant structure sheaf is bijective on the
endomorphisms of the structure sheaf.** -/
theorem bijective_modulePullback_map_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso f.toLRSHom.toHom.c] :
    Function.Bijective ((Scheme.Modules.pullback f).map :
      (SheafOfModules.unit Y.ringCatSheaf ⟶ SheafOfModules.unit Y.ringCatSheaf) →
      ((Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ⟶
        (Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf))) := by
  have hφ : IsIso (structureSheafHom f.toLRSHom.toShHom) := by
    rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _)]
    change IsIso (Functor.whiskerRight f.toLRSHom.toHom.c (forget₂ CommRingCat RingCat))
    infer_instance
  have hfin : (opensMap f.toLRSHom.toShHom).Final := CategoryTheory.final_of_representablyFlat _
  have hpuu : IsIso (SheafOfModules.pullbackObjUnitToUnit
      (structureSheafHom f.toLRSHom.toShHom)) :=
    inferInstance
  have hmap : IsIso ((SheafOfModules.pushforward (structureSheafHom f.toLRSHom.toShHom)).map
      (SheafOfModules.pullbackObjUnitToUnit (structureSheafHom f.toLRSHom.toShHom))) :=
    inferInstance
  have hcomp : (SheafOfModules.pullbackPushforwardAdjunction
        (structureSheafHom f.toLRSHom.toShHom)).unit.app
          (SheafOfModules.unit Y.ringCatSheaf) ≫
      (SheafOfModules.pushforward (structureSheafHom f.toLRSHom.toShHom)).map
        (SheafOfModules.pullbackObjUnitToUnit (structureSheafHom f.toLRSHom.toShHom)) =
        SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f.toLRSHom.toShHom) :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  have hunit : IsIso ((SheafOfModules.pullbackPushforwardAdjunction
      (structureSheafHom f.toLRSHom.toShHom)).unit.app
        (SheafOfModules.unit Y.ringCatSheaf)) := by
    have hboth : IsIso ((SheafOfModules.pullbackPushforwardAdjunction
          (structureSheafHom f.toLRSHom.toShHom)).unit.app
            (SheafOfModules.unit Y.ringCatSheaf) ≫
        (SheafOfModules.pushforward (structureSheafHom f.toLRSHom.toShHom)).map
          (SheafOfModules.pullbackObjUnitToUnit
            (structureSheafHom f.toLRSHom.toShHom))) := by
      rw [hcomp]
      exact unitToPushforwardObjUnit_isIso _
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hmap hboth
  exact bijective_map_of_unit_isIso
    (SheafOfModules.pullbackPushforwardAdjunction (structureSheafHom f.toLRSHom.toShHom)) _ _

/-- **Pullback along a section of a morphism with invariant structure sheaf is bijective on the
endomorphisms of the structure sheaf.** -/
private theorem bijective_sectionPullback_map_unit {X Y : Scheme.{u}} (f : X ⟶ Y) (σ : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 Y) [IsIso f.toLRSHom.toHom.c] :
    Function.Bijective ((Scheme.Modules.pullback σ).map :
      (SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) →
      ((Scheme.Modules.pullback σ).obj (SheafOfModules.unit X.ringCatSheaf) ⟶
        (Scheme.Modules.pullback σ).obj (SheafOfModules.unit X.ringCatSheaf))) := by
  let e : Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback σ ≅ 𝟭 Y.Modules :=
    Scheme.Modules.pullbackComp σ f ≪≫
      eqToIso (congrArg Scheme.Modules.pullback hσ) ≪≫ Scheme.Modules.pullbackId Y
  exact bijective_map_end_of_iso (Scheme.Modules.pullback σ)
    (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f)
    (bijective_map_of_retraction _ _ e _ _ (bijective_modulePullback_map_unit f))

/-! ### Pullback along a section is bijective on homomorphisms of invertible modules -/

/-- Partially applying the tensor bifunctor of a scheme on the left is tensoring on the left.
The first component of the morphism is only required to be the identity up to an equation, so
that the lemma applies to the image of an identity under a functor. -/
private theorem tensorSheaf_map_id_left (Y : Scheme.{u}) (L : Y.Modules) {M N : Y.Modules}
    (a : M ⟶ N) (e : L ⟶ L) (he : e = 𝟙 L) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.presheaf, Y.IsSheaf⟩))).map
        (X := (L, M)) (Y := (L, N)) (e, a) =
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        ⟨Y.presheaf, Y.IsSheaf⟩).obj (L))).map a := by
  subst he
  exact Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map _ (𝟙 L) a

/-- Pulling back the tensor product by a fixed module is tensoring by its pullback. -/
private def modulePullbackTensorLeftIso {X Y : Scheme.{u}} (g : X ⟶ Y) (L : Y.Modules) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩).obj (L)) ⋙
        Scheme.Modules.pullback g ≅
      Scheme.Modules.pullback g ⋙
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨X.presheaf, X.IsSheaf⟩).obj
          (((Scheme.Modules.pullback g).obj L))) :=
  NatIso.ofComponents
    (fun M => (Stacks.RingedSpace.comparisonBifunctorIso g.toLRSHom.toShHom).app (L, M))
    (by
      intro M N a
      have h := (Stacks.RingedSpace.comparisonBifunctorIso g.toLRSHom.toShHom).hom.naturality
        (X := (L, M)) (Y := (L, N)) (𝟙 L, a)
      have hY := tensorSheaf_map_id_left Y L a (𝟙 L) rfl
      have hX := tensorSheaf_map_id_left X ((Scheme.Modules.pullback g).obj L)
        ((Scheme.Modules.pullback g).map a) ((Scheme.Modules.pullback g).map (𝟙 L))
        (CategoryTheory.Functor.map_id _ _)
      exact (congrArg (fun t => (Scheme.Modules.pullback g).map t ≫
          (Stacks.RingedSpace.comparisonBifunctorIso g.toLRSHom.toShHom).hom.app (L, N))
            hY.symm).trans (h.trans (congrArg (fun t =>
          (Stacks.RingedSpace.comparisonBifunctorIso g.toLRSHom.toShHom).hom.app (L, M) ≫ t) hX)))

/-- **Pullback along a section of a morphism with invariant structure sheaf is bijective on the
endomorphisms of an invertible module.** -/
theorem bijective_sectionPullback_map_end {X Y : Scheme.{u}} (f : X ⟶ Y) (σ : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 Y) [IsIso f.toLRSHom.toHom.c] (L : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    Function.Bijective ((Scheme.Modules.pullback σ).map : (L ⟶ L) →
      ((Scheme.Modules.pullback σ).obj L ⟶ (Scheme.Modules.pullback σ).obj L)) := by
  have hinv : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      ((Scheme.Modules.pullback σ).obj L) :=
    Stacks.RingedSpace.modulePullback_isInvertible σ.toLRSHom.toShHom L
  have h := bijective_map_of_tensor_comparison (Scheme.Modules.pullback σ)
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨X.presheaf, X.IsSheaf⟩).obj (L)))
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩).obj
      (((Scheme.Modules.pullback σ).obj L))))
    (fullyFaithfulOfIsEquivalence _
      (Stacks.SheafOfModules.tensorLeftFunctor_isEquivalence X.presheaf X.ringCatSheaf.2 L))
    (fullyFaithfulOfIsEquivalence _
      (Stacks.SheafOfModules.tensorLeftFunctor_isEquivalence Y.presheaf Y.ringCatSheaf.2
        ((Scheme.Modules.pullback σ).obj L)))
    (modulePullbackTensorLeftIso σ L) (SheafOfModules.unit X.ringCatSheaf)
    (SheafOfModules.unit X.ringCatSheaf) (bijective_sectionPullback_map_unit f σ hσ)
  exact bijective_map_end_of_iso (Scheme.Modules.pullback σ)
    (Stacks.SheafOfModules.Invertible.tensorProductRightUnitor X.presheaf X.ringCatSheaf.2 L) h

/-- **Pullback along a section of a morphism with invariant structure sheaf is bijective on the
homomorphisms between two isomorphic invertible modules.** -/
theorem bijective_sectionPullback_map {X Y : Scheme.{u}} (f : X ⟶ Y) (σ : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 Y) [IsIso f.toLRSHom.toHom.c] (L M : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] (e : L ≅ M) :
    Function.Bijective ((Scheme.Modules.pullback σ).map : (L ⟶ M) →
      ((Scheme.Modules.pullback σ).obj L ⟶ (Scheme.Modules.pullback σ).obj M)) :=
  bijective_map_of_iso _ e (bijective_sectionPullback_map_end f σ hσ L)

/-- **An isomorphism of the restrictions along the section of two isomorphic invertible modules
comes from exactly one isomorphism upstairs.** -/
theorem existsUnique_sectionPullback_mapIso {X Y : Scheme.{u}} (f : X ⟶ Y) (σ : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 Y) [IsIso f.toLRSHom.toHom.c] (L M : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] (e : L ≅ M)
    (a : (Scheme.Modules.pullback σ).obj L ≅ (Scheme.Modules.pullback σ).obj M) :
    ∃! b : L ≅ M, (Scheme.Modules.pullback σ).mapIso b = a :=
  existsUnique_iso_of_bijective_end (Scheme.Modules.pullback σ) e
    (bijective_sectionPullback_map_end f σ hσ L) (bijective_sectionPullback_map_end f σ hσ M) a

/-- **An isomorphism of two isomorphic invertible modules is determined by its restriction
along the section.** -/
theorem injective_sectionPullback_mapIso {X Y : Scheme.{u}} (f : X ⟶ Y) (σ : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 Y) [IsIso f.toLRSHom.toHom.c] (L M : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] (e : L ≅ M) :
    Function.Injective (fun a : L ≅ M => (Scheme.Modules.pullback σ).mapIso a) := fun a _ hab =>
  (existsUnique_sectionPullback_mapIso f σ hσ L M e
    ((Scheme.Modules.pullback σ).mapIso a)).unique rfl hab.symm

/-! ### Normalised isomorphisms -/

/-- The unique isomorphism of two isomorphic invertible modules on `X` whose restriction along
the section is a prescribed isomorphism downstairs. -/
def sectionNormalizedIso {X Y : Scheme.{u}} (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y)
    [IsIso f.toLRSHom.toHom.c] (L M : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] (e : L ≅ M)
    (a : (Scheme.Modules.pullback σ).obj L ≅ (Scheme.Modules.pullback σ).obj M) : L ≅ M :=
  Classical.choose (existsUnique_sectionPullback_mapIso f σ hσ L M e a)

/-- The normalised isomorphism restricts along the section to the prescribed isomorphism. -/
theorem sectionNormalizedIso_spec {X Y : Scheme.{u}} (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y)
    [IsIso f.toLRSHom.toHom.c] (L M : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] (e : L ≅ M)
    (a : (Scheme.Modules.pullback σ).obj L ≅ (Scheme.Modules.pullback σ).obj M) :
    (Scheme.Modules.pullback σ).mapIso (sectionNormalizedIso f σ hσ L M e a) = a :=
  (Classical.choose_spec (existsUnique_sectionPullback_mapIso f σ hσ L M e a)).1

/-- Three isomorphisms whose restrictions along the section compose, compose. -/
private theorem sectionNormalizedIso_comp {X Y : Scheme.{u}} (f : X ⟶ Y) (σ : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 Y) [IsIso f.toLRSHom.toHom.c] (L M N : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]
    (a : L ≅ M) (b : M ≅ N) (c : L ≅ N) {Q : Y.Modules}
    (α : (Scheme.Modules.pullback σ).obj L ≅ Q)
    (β : (Scheme.Modules.pullback σ).obj M ≅ Q)
    (γ : (Scheme.Modules.pullback σ).obj N ≅ Q)
    (ha : (Scheme.Modules.pullback σ).mapIso a = α ≪≫ β.symm)
    (hb : (Scheme.Modules.pullback σ).mapIso b = β ≪≫ γ.symm)
    (hc : (Scheme.Modules.pullback σ).mapIso c = α ≪≫ γ.symm) :
    a ≪≫ b = c := by
  apply injective_sectionPullback_mapIso f σ hσ L N (a ≪≫ b)
  beta_reduce
  rw [Functor.mapIso_trans, ha, hb, hc]
  simp

/-- Normalised isomorphisms compose: this is the cocycle condition of a family of
normalisations against a fixed family of trivialisations downstairs. -/
theorem sectionNormalizedIso_trans {X Y : Scheme.{u}} (f : X ⟶ Y) (σ : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 Y) [IsIso f.toLRSHom.toHom.c] (L M N : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]
    (a : L ≅ M) (b : M ≅ N) {Q : Y.Modules}
    (α : (Scheme.Modules.pullback σ).obj L ≅ Q)
    (β : (Scheme.Modules.pullback σ).obj M ≅ Q)
    (γ : (Scheme.Modules.pullback σ).obj N ≅ Q) :
    sectionNormalizedIso f σ hσ L M a (α ≪≫ β.symm) ≪≫
        sectionNormalizedIso f σ hσ M N b (β ≪≫ γ.symm) =
      sectionNormalizedIso f σ hσ L N (a ≪≫ b) (α ≪≫ γ.symm) :=
  sectionNormalizedIso_comp f σ hσ L M N _ _ _ α β γ
    (sectionNormalizedIso_spec f σ hσ L M a _) (sectionNormalizedIso_spec f σ hσ M N b _)
    (sectionNormalizedIso_spec f σ hσ L N (a ≪≫ b) _)

/-- Normalising the identity against one trivialisation gives the identity. -/
theorem sectionNormalizedIso_refl {X Y : Scheme.{u}} (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y)
    [IsIso f.toLRSHom.toHom.c] (L : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (e : L ≅ L) :
    sectionNormalizedIso f σ hσ L L e (Iso.refl _) = Iso.refl L := by
  apply injective_sectionPullback_mapIso f σ hσ L L e
  beta_reduce
  rw [sectionNormalizedIso_spec]
  simp

/-- Normalisation commutes with inversion. -/
theorem sectionNormalizedIso_symm {X Y : Scheme.{u}} (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y)
    [IsIso f.toLRSHom.toHom.c] (L M : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] (e : L ≅ M)
    (a : (Scheme.Modules.pullback σ).obj L ≅ (Scheme.Modules.pullback σ).obj M) :
    (sectionNormalizedIso f σ hσ L M e a).symm =
      sectionNormalizedIso f σ hσ M L e.symm a.symm := by
  apply injective_sectionPullback_mapIso f σ hσ M L e.symm
  beta_reduce
  rw [Functor.mapIso_symm, sectionNormalizedIso_spec, sectionNormalizedIso_spec]

/-! ### Restriction of homomorphisms between pullbacks along a section -/

open Pseudofunctor.LocallyDiscreteOpToCat in
/-- Restricting homomorphisms between two pullbacks along a morphism `g` is bijective as soon as
pullback along `g` is bijective on the corresponding homomorphisms: the two differ by the
coherence isomorphisms of the pseudofunctor. -/
theorem bijective_pullHom {C : Type*} [Category C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat} {X₁ X₂ Y Z : C}
    {M₁ : F.obj (.mk (.op X₁))} {M₂ : F.obj (.mk (.op X₂))}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (g : Z ⟶ Y) (gf₁ : Z ⟶ X₁) (gf₂ : Z ⟶ X₂)
    (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂)
    (h : Function.Bijective ((F.map g.op.toLoc).toFunctor.map :
      ((F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) → _)) :
    Function.Bijective (fun a :
      (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂ =>
        pullHom a g gf₁ gf₂ h₁ h₂) := by
  let e₁ := (Cat.Hom.toNatIso (F.mapComp' f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
    (by simp [← Quiver.Hom.comp_toLoc, ← op_comp, h₁]))).app M₁
  let e₂ := (Cat.Hom.toNatIso (F.mapComp' f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
    (by simp [← Quiver.Hom.comp_toLoc, ← op_comp, h₂]))).app M₂
  exact (Iso.homCongr e₁.symm e₂.symm).bijective.comp h

open Pseudofunctor.LocallyDiscreteOpToCat in
/-- **Restriction along a section of a morphism with invariant structure sheaf is bijective on
the homomorphisms between two pullbacks of invertible modules**, provided the two are isomorphic
at all. This is what determines such a homomorphism by its restriction along the section. -/
theorem bijective_pullHom_section {Y Z₁ Z₂ V : Scheme.{u}} (p : Y ⟶ Z₁) (q : Y ⟶ Z₂)
    (f : Y ⟶ V) (σ : V ⟶ Y) (hσ : σ ≫ f = 𝟙 V) [IsIso f.toLRSHom.toHom.c]
    (L₁ : Z₁.Modules) (L₂ : Z₂.Modules)
    [Stacks.SheafOfModules.IsInvertible Z₁.presheaf Z₁.ringCatSheaf.2 L₁]
    [Stacks.SheafOfModules.IsInvertible Z₂.presheaf Z₂.ringCatSheaf.2 L₂]
    (e : (Scheme.Modules.pullback p).obj L₁ ≅ (Scheme.Modules.pullback q).obj L₂) :
    Function.Bijective (fun a : (Scheme.Modules.pullback p).obj L₁ ⟶
      (Scheme.Modules.pullback q).obj L₂ =>
        pullHom (F := modulePullbackPseudofunctor) a σ (σ ≫ p) (σ ≫ q) rfl rfl) := by
  have h1 : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      ((modulePullbackPseudofunctor.map p.op.toLoc).toFunctor.obj L₁) :=
    Stacks.RingedSpace.modulePullback_isInvertible p.toLRSHom.toShHom L₁
  have h2 : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      ((modulePullbackPseudofunctor.map q.op.toLoc).toFunctor.obj L₂) :=
    Stacks.RingedSpace.modulePullback_isInvertible q.toLRSHom.toShHom L₂
  exact bijective_pullHom (F := modulePullbackPseudofunctor) (M₁ := L₁) (M₂ := L₂)
    (f₁ := p) (f₂ := q) σ (σ ≫ p) (σ ≫ q) rfl rfl
    (bijective_sectionPullback_map f σ hσ _ _ e)

end Stacks.Picard

end
