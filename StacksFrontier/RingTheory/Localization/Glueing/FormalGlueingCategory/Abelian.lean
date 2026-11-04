module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingComplex
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingCategory.Exactness
import all StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingCategory.Exactness

/-!
# Module glueing data form an abelian category

For a flat ring map `R → S`, the category of module glueing data has finite limits and finite
colimits computed componentwise, it is abelian, and the canonical functor is exact.

## Main results

* `FormalGlueing.moduleGlueingConstruction_abelian_exact_preservesColimits`: module glueing data
  form an abelian category, and the canonical functor is exact and preserves arbitrary colimits.

## Implementation notes

Exactness is expressed as preservation of finite limits and finite colimits. The ideal generated
by the finite family does not occur separately because both the glueing category and its
canonical functor depend directly on the chosen family of generators.

## References

* [Stacks Project, Tag 05EN](https://stacks.math.columbia.edu/tag/05EN)
-/

/-! ### Exactness of the canonical module glueing functor -/

section

namespace FormalGlueing

universe u v w

open CategoryTheory CategoryTheory.Limits FormalGlueing Cech TensorProduct

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
variable {r : ℕ} (f : Fin r → R)

attribute [local instance] LocalizedModule.moduleOfIsLocalization

attribute [local instance] sectionsScalarTower

attribute [local instance] moduleGlueingCategory

attribute [local instance] glueingPreadditive

attribute [local instance] genericEvaluation_additive localEvaluation_additive

attribute [local instance] localizationFunctor_additive

attribute [local instance] scalarExtension_additive

attribute [local instance] localization_preservesFiniteLimits localization_preservesFiniteColimits
  scalarExtension_preservesFiniteLimits scalarExtension_preservesFiniteColimits

section FiniteLimits

variable [Module.Flat R S]
variable {J : Type} [SmallCategory J] [FinCategory J]
variable (c : LocalizationComparisons.{u, max u v w} f)
variable (D : J ⥤ ModuleGlueingDatum.{u, v, w} S f c)

private def limitAlpha (i : Fin r) :
    LocalizedModule.Away (algebraMap R S (f i)) ↑(limit (D ⋙ genericEvaluation S f c)) ≃ₗ[S]
      S ⊗[R] restrictFromAway f i (limit (D ⋙ localEvaluation S f c i)) :=
  (mapLimitIso (D ⋙ genericEvaluation S f c) (D ⋙ localEvaluation S f c i)
    (localizationFunctor (Submonoid.powers (algebraMap R S (f i))))
    (ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i))) ⋙
      scalarExtension (R := R) S)
    (Functor.isoWhiskerLeft D (alphaNaturalIso S f c i))).toLinearEquiv

private def limitAlphaIJ (i j : Fin r) :
    cechMod f (restrictFromAway f i (limit (D ⋙ localEvaluation S f c i))) {j} ≃ₗ[R]
      cechMod f (restrictFromAway f j (limit (D ⋙ localEvaluation S f c j))) {i} :=
  (mapLimitIso (D ⋙ localEvaluation S f c i) (D ⋙ localEvaluation S f c j)
    (ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i))) ⋙
      localizationFunctor (cechSub f {j}))
    (ModuleCat.restrictScalars (algebraMap R (Localization.Away (f j))) ⋙
      localizationFunctor (cechSub f {i}))
    (Functor.isoWhiskerLeft D (alphaIJNaturalIso S f c i j))).toLinearEquiv

private abbrev localLimitMap (i : Fin r) (j : J) :=
  ((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i)))).map
    (limit.π (D ⋙ localEvaluation S f c i) j)).hom

private theorem limitAlpha_π (i : Fin r) (j : J)
    (x : LocalizedModule.Away (algebraMap R S (f i)) ↑(limit (D ⋙ genericEvaluation S f c))) :
    TensorProduct.map LinearMap.id
      (((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i)))).map
        (limit.π (D ⋙ localEvaluation S f c i) j)).hom) (limitAlpha S f c D i x) =
      (D.obj j).alpha i
        ((LocalizedModule.map (Submonoid.powers (algebraMap R S (f i)))
          (limit.π (D ⋙ genericEvaluation S f c) j).hom) x) :=
  DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (mapLimitIso_hom_π (D ⋙ genericEvaluation S f c) (D ⋙ localEvaluation S f c i)
      (localizationFunctor (Submonoid.powers (algebraMap R S (f i))))
      (ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i))) ⋙
        scalarExtension (R := R) S)
      (Functor.isoWhiskerLeft D (alphaNaturalIso S f c i)) j)) x

/-- `limitAlpha_π` evaluated on an element coming from the generic limit. -/
private theorem limitAlpha_mk_π (i : Fin r) (j : J) (m : ↑(limit (D ⋙ genericEvaluation S f c))) :
    TensorProduct.map LinearMap.id (localLimitMap S f c D i j)
        (limitAlpha S f c D i (LocalizedModule.mkLinearMap _ _ m)) =
      (D.obj j).alpha i
        (LocalizedModule.mkLinearMap _ _ (limit.π (D ⋙ genericEvaluation S f c) j m)) := by
  simpa only [LocalizedModule.mkLinearMap_apply, LocalizedModule.map_mk] using
    limitAlpha_π S f c D i j (LocalizedModule.mkLinearMap _ _ m)

omit [Module.Flat R S] in
private theorem limitAlphaIJ_π (i k : Fin r) (j : J)
    (x : cechMod f (restrictFromAway f i (limit (D ⋙ localEvaluation S f c i))) {k}) :
    localizedMap f {i}
      (((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f k)))).map
        (limit.π (D ⋙ localEvaluation S f c k) j)).hom) (limitAlphaIJ S f c D i k x) =
      (D.obj j).alphaIJ i k
        (localizedMap f {k}
          (((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i)))).map
            (limit.π (D ⋙ localEvaluation S f c i) j)).hom) x) :=
  DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (mapLimitIso_hom_π (D ⋙ localEvaluation S f c i) (D ⋙ localEvaluation S f c k)
      (ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i))) ⋙
        localizationFunctor (cechSub f {k}))
      (ModuleCat.restrictScalars (algebraMap R (Localization.Away (f k))) ⋙
        localizationFunctor (cechSub f {i}))
      (Functor.isoWhiskerLeft D (alphaIJNaturalIso S f c i k)) j)) x

omit [Module.Flat R S] in
private theorem limitAlphaIJ_π_linear (i k : Fin r) (j : J) :
    (localizedMap f {i} (localLimitMap S f c D k j)).comp (limitAlphaIJ S f c D i k).toLinearMap =
      ((D.obj j).alphaIJ i k).toLinearMap.comp (localizedMap f {k} (localLimitMap S f c D i j)) :=
  LinearMap.ext (limitAlphaIJ_π S f c D i k j)

omit [Module.Flat R S] in
private theorem limitAlphaIJ_tensor_π (i k : Fin r) (j : J)
    (x : S ⊗[R] cechMod f (restrictFromAway f i (limit (D ⋙ localEvaluation S f c i))) {k}) :
    TensorProduct.map LinearMap.id (localizedMap f {i} (localLimitMap S f c D k j))
        (TensorProduct.map LinearMap.id (limitAlphaIJ S f c D i k).toLinearMap x) =
      TensorProduct.map LinearMap.id ((D.obj j).alphaIJ i k).toLinearMap
        (TensorProduct.map LinearMap.id (localizedMap f {k} (localLimitMap S f c D i j)) x) :=
  tensorMap_commute S _ _ _ _ (limitAlphaIJ_π_linear S f c D i k j) x

omit [Module.Flat R S] in
private theorem limitAlphaIJ_localized_π (i k : Fin r) (j : J) (t : Finset (Fin r))
    (x : cechMod f (cechMod f (restrictFromAway f i (limit (D ⋙ localEvaluation S f c i))) {k}) t) :
    localizedMap f t (localizedMap f {i} (localLimitMap S f c D k j))
        (localizedMap f t (limitAlphaIJ S f c D i k).toLinearMap x) =
      localizedMap f t ((D.obj j).alphaIJ i k).toLinearMap
        (localizedMap f t (localizedMap f {k} (localLimitMap S f c D i j)) x) :=
  localizedMap_commute f _ _ _ _ (limitAlphaIJ_π_linear S f c D i k j) t x

private def limitDatum : ModuleGlueingDatum.{u, v, w} S f c where
  generic := limit (D ⋙ genericEvaluation S f c)
  localPiece i := limit (D ⋙ localEvaluation S f c i)
  alpha := limitAlpha S f c D
  alphaIJ := limitAlphaIJ S f c D
  alpha_compatibility i k m := by
    apply mapLimit_ext (D ⋙ localEvaluation S f c k)
      (ModuleCat.restrictScalars (algebraMap R (Localization.Away (f k))) ⋙
        localizationFunctor (cechSub f {i}) ⋙ scalarExtension (R := R) S)
    intro j
    change TensorProduct.map LinearMap.id (localizedMap f {i} (localLimitMap S f c D k j))
      (TensorProduct.map LinearMap.id (limitAlphaIJ S f c D i k).toLinearMap
        (TensorProduct.map LinearMap.id (LocalizedModule.mkLinearMap (cechSub f {k}) _)
          (limitAlpha S f c D i (LocalizedModule.mkLinearMap _ _ m)))) =
      TensorProduct.map LinearMap.id (localizedMap f {i} (localLimitMap S f c D k j))
        (TensorProduct.map LinearMap.id (LocalizedModule.mkLinearMap (cechSub f {i}) _)
          (limitAlpha S f c D k (LocalizedModule.mkLinearMap _ _ m)))
    rw [limitAlphaIJ_tensor_π, tensorMap_localizedMk, tensorMap_localizedMk,
      limitAlpha_mk_π, limitAlpha_mk_π]
    exact (D.obj j).alpha_compatibility i k ((limit.π (D ⋙ genericEvaluation S f c) j) m)
  cocycle i j k := by
    apply LinearMap.ext
    intro x
    apply mapLimit_ext (D ⋙ localEvaluation S f c k)
      (ModuleCat.restrictScalars (algebraMap R (Localization.Away (f k))) ⋙
        localizationFunctor (cechSub f ({j} ∪ {i})))
    intro a
    change localizedMap f ({j} ∪ {i}) (localLimitMap S f c D k a) _ =
      localizedMap f ({j} ∪ {i}) (localLimitMap S f c D k a) _
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      iterated_naturality_apply, iterated_symm_naturality_apply,
      cechModCongr_naturality, limitAlphaIJ_localized_π]
    exact DFunLike.congr_fun ((D.obj a).cocycle i j k)
      (localizedMap f ({j} ∪ {k}) (localLimitMap S f c D i a) x)

private def limitProjection (j : J) : limitDatum S f c D ⟶ D.obj j where
  generic := limit.π (D ⋙ genericEvaluation S f c) j
  localPiece i := limit.π (D ⋙ localEvaluation S f c i) j
  alpha_compatibility i m := by
    exact (limitAlpha_mk_π S f c D i j m).symm
  alphaIJ_compatibility i k m := by
    simpa only [localizedMap_mk] using!
      (limitAlphaIJ_π S f c D i k j (LocalizedModule.mkLinearMap _ _ m)).symm

private def limitCone : Cone D where
  pt := limitDatum S f c D
  π :=
    { app := limitProjection S f c D
      naturality {j k} a := by
        apply ModuleGlueingMap.ext
        · change limit.π (D ⋙ genericEvaluation S f c) k =
            limit.π (D ⋙ genericEvaluation S f c) j ≫ (genericEvaluation S f c).map (D.map a)
          simpa only [Functor.comp_map, Functor.const_obj_map, Category.id_comp] using
            (limit.w (D ⋙ genericEvaluation S f c) a).symm
        · funext i
          change limit.π (D ⋙ localEvaluation S f c i) k =
            limit.π (D ⋙ localEvaluation S f c i) j ≫ (localEvaluation S f c i).map (D.map a)
          simpa only [Functor.comp_map, Functor.const_obj_map, Category.id_comp] using
            (limit.w (D ⋙ localEvaluation S f c i) a).symm }

omit [Module.Flat R S] [FinCategory J] in
private theorem localLimitLift_fac (s : Cone D) (i : Fin r) (j : J) :
    (localLimitMap S f c D i j).comp
      (((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i)))).map
        (limit.lift (D ⋙ localEvaluation S f c i) ((localEvaluation S f c i).mapCone s))).hom) =
      ((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i)))).map
        ((s.π.app j).localPiece i)).hom := by
  show ((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i)))).map
    (limit.lift (D ⋙ localEvaluation S f c i) ((localEvaluation S f c i).mapCone s) ≫
      limit.π (D ⋙ localEvaluation S f c i) j)).hom = _
  rw [limit.lift_π]
  rfl

private def limitLift (s : Cone D) : s.pt ⟶ limitDatum S f c D where
  generic := limit.lift (D ⋙ genericEvaluation S f c) ((genericEvaluation S f c).mapCone s)
  localPiece i := limit.lift (D ⋙ localEvaluation S f c i) ((localEvaluation S f c i).mapCone s)
  alpha_compatibility i m := by
    apply mapLimit_ext (D ⋙ localEvaluation S f c i)
      (ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i))) ⋙
        scalarExtension (R := R) S)
    intro j
    change TensorProduct.map LinearMap.id (localLimitMap S f c D i j)
      (limitAlpha S f c D i (LocalizedModule.mkLinearMap _ _
        (limit.lift (D ⋙ genericEvaluation S f c) ((genericEvaluation S f c).mapCone s) m))) =
      TensorProduct.map LinearMap.id (localLimitMap S f c D i j)
        (TensorProduct.map LinearMap.id _ (s.pt.alpha i (LocalizedModule.mkLinearMap _ _ m)))
    rw [limitAlpha_mk_π, TensorProduct.map_map, localLimitLift_fac, LinearMap.comp_id]
    have h := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
      (limit.lift_π ((genericEvaluation S f c).mapCone s) j)) m
    change (limit.π (D ⋙ genericEvaluation S f c) j)
      (limit.lift (D ⋙ genericEvaluation S f c) ((genericEvaluation S f c).mapCone s) m) =
        (s.π.app j).generic m at h
    rw [h]
    exact (s.π.app j).alpha_compatibility i m
  alphaIJ_compatibility i k m := by
    apply mapLimit_ext (D ⋙ localEvaluation S f c k)
      (ModuleCat.restrictScalars (algebraMap R (Localization.Away (f k))) ⋙
        localizationFunctor (cechSub f {i}))
    intro j
    change localizedMap f {i} (localLimitMap S f c D k j)
      (limitAlphaIJ S f c D i k (LocalizedModule.mkLinearMap (cechSub f {k}) _
        (limit.lift (D ⋙ localEvaluation S f c i) ((localEvaluation S f c i).mapCone s) m))) =
      localizedMap f {i} (localLimitMap S f c D k j)
        (localizedMap f {i} _ (s.pt.alphaIJ i k (LocalizedModule.mkLinearMap (cechSub f {k}) _ m)))
    rw [limitAlphaIJ_π]
    change _ = ((localizedMap f {i} (localLimitMap S f c D k j)).comp (localizedMap f {i} _)) _
    rw [← localizedMap_comp, localLimitLift_fac, localizedMap_mk]
    have h := DFunLike.congr_fun (localLimitLift_fac S f c D s i j) m
    change localLimitMap S f c D i j
      (limit.lift (D ⋙ localEvaluation S f c i) ((localEvaluation S f c i).mapCone s) m) =
        (s.π.app j).localPiece i m at h
    rw [h]
    exact (s.π.app j).alphaIJ_compatibility i k m

private def limitConeIsLimit : IsLimit (limitCone S f c D) where
  lift := limitLift S f c D
  fac s j := by
    apply ModuleGlueingMap.ext
    · exact limit.lift_π ((genericEvaluation S f c).mapCone s) j
    · funext i
      exact limit.lift_π ((localEvaluation S f c i).mapCone s) j
  uniq s m h := by
    apply ModuleGlueingMap.ext
    · apply limit.hom_ext
      intro j
      exact (congrArg ModuleGlueingMap.generic (h j)).trans
        (limit.lift_π ((genericEvaluation S f c).mapCone s) j).symm
    · funext i
      apply limit.hom_ext
      intro j
      exact (congrArg (fun a ↦ a.localPiece i) (h j)).trans
        (limit.lift_π ((localEvaluation S f c i).mapCone s) j).symm

end FiniteLimits

private theorem glueingHasFiniteLimits [Module.Flat R S]
    (c : LocalizationComparisons.{u, max u v w} f) :
    HasFiniteLimits (ModuleGlueingDatum.{u, v, w} S f c) where
  out _ _ _ := ⟨fun D ↦ ⟨⟨limitCone S f c D, limitConeIsLimit S f c D⟩⟩⟩

attribute [local instance] glueingHasFiniteLimits


private theorem genericEvaluation_preservesFiniteLimits [Module.Flat R S]
    (c : LocalizationComparisons.{u, max u v w} f) :
    PreservesFiniteLimits (genericEvaluation S f c) where
  preservesFiniteLimits _ _ _ :=
    { preservesLimit := fun {D} ↦
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit S f c D)
          (show IsLimit ((genericEvaluation S f c).mapCone (limitCone S f c D)) from
            limit.isLimit (D ⋙ genericEvaluation S f c)) }

private theorem localEvaluation_preservesFiniteLimits [Module.Flat R S]
    (c : LocalizationComparisons.{u, max u v w} f) (i : Fin r) :
    PreservesFiniteLimits (localEvaluation S f c i) where
  preservesFiniteLimits _ _ _ :=
    { preservesLimit := fun {D} ↦
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit S f c D)
          (show IsLimit ((localEvaluation S f c i).mapCone (limitCone S f c D)) from
            limit.isLimit (D ⋙ localEvaluation S f c i)) }

attribute [local instance] genericEvaluation_preservesFiniteLimits
  localEvaluation_preservesFiniteLimits

private def isLimit_of_components [Module.Flat R S]
    {J : Type} [SmallCategory J] [FinCategory J]
    (c : LocalizationComparisons.{u, max u v w} f)
    (D : J ⥤ ModuleGlueingDatum.{u, v, w} S f c) (s : Cone D)
    (hg : IsLimit ((genericEvaluation S f c).mapCone s))
    (hl : ∀ i, IsLimit ((localEvaluation S f c i).mapCone s)) : IsLimit s := by
  letI : IsIso (limitLift S f c D s).generic := by
    change IsIso ((hg.conePointUniqueUpToIso (limit.isLimit (D ⋙ genericEvaluation S f c))).hom)
    infer_instance
  letI : ∀ i, IsIso ((limitLift S f c D s).localPiece i) := fun i ↦ by
    change IsIso (((hl i).conePointUniqueUpToIso (limit.isLimit (D ⋙ localEvaluation S f c i))).hom)
    infer_instance
  letI : IsIso ((limitConeIsLimit S f c D).lift s) :=
    isIso_of_components S f c (limitLift S f c D s)
  exact (limitConeIsLimit S f c D).ofPointIso

private theorem canonical_additive : (canonicalFunctor.{u, v, w} S f).Additive where
  map_add {X Y} a b := by
    apply ModuleGlueingMap.ext
    · apply ModuleCat.hom_ext
      exact (AlgebraTensorModule.lTensor S S).map_add a.hom b.hom
    · funext i
      apply ModuleCat.hom_ext
      ext x
      induction x using LocalizedModule.induction_on with
      | h m s =>
        show LocalizedModule.map (Submonoid.powers (f i)) (a.hom + b.hom)
          (LocalizedModule.mk m s) =
          LocalizedModule.map (Submonoid.powers (f i)) a.hom (LocalizedModule.mk m s) +
            LocalizedModule.map (Submonoid.powers (f i)) b.hom (LocalizedModule.mk m s)
        simp [LocalizedModule.map_mk]

attribute [local instance] canonical_additive

private theorem canonicalLocal_preservesFiniteLimits (i : Fin r) :
    PreservesFiniteLimits (canonicalFunctor.{u, v, w} S f ⋙
      localEvaluation S f (localizationComparisons f) i) := by
  apply And.left ∘ ((Functor.exact_tfae _).out 2 4).mp
  intro K hK
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hK ⊢
  exact IsLocalizedModule.map_exact (Submonoid.powers (f i))
    (LocalizedModule.mkLinearMap _ K.X₁) (LocalizedModule.mkLinearMap _ K.X₂)
    (LocalizedModule.mkLinearMap _ K.X₃) K.f.hom K.g.hom hK

attribute [local instance] canonicalLocal_preservesFiniteLimits

private theorem canonical_preservesFiniteLimits [Module.Flat R S] :
    PreservesFiniteLimits (canonicalFunctor.{u, v, w} S f) where
  preservesFiniteLimits _ _ _ :=
    { preservesLimit := fun {D} ↦
        preservesLimit_of_preserves_limit_cone (limit.isLimit D)
          (isLimit_of_components S f (localizationComparisons f)
            (D ⋙ canonicalFunctor S f) ((canonicalFunctor S f).mapCone (limit.cone D))
            (show IsLimit ((scalarExtension (R := R) S).mapCone (limit.cone D)) from
              isLimitOfPreserves (scalarExtension (R := R) S) (limit.isLimit D))
            (fun i ↦ isLimitOfPreserves
              (canonicalFunctor S f ⋙ localEvaluation S f (localizationComparisons f) i)
              (limit.isLimit D))) }

private def mapColimitIso {J C D E : Type*} [Category J] [Category C] [Category D] [Category E]
    (F : J ⥤ C) (G : J ⥤ D) (L : C ⥤ E) (K : D ⥤ E)
    [HasColimit F] [HasColimit G] [HasColimit (F ⋙ L)] [HasColimit (G ⋙ K)]
    [PreservesColimit F L] [PreservesColimit G K] (e : F ⋙ L ≅ G ⋙ K) :
    L.obj (colimit F) ≅ K.obj (colimit G) :=
  preservesColimitIso L F ≪≫ HasColimit.isoOfNatIso e ≪≫ (preservesColimitIso K G).symm

private theorem mapColimitIso_ι_hom {J C D E : Type*}
    [Category J] [Category C] [Category D] [Category E]
    (F : J ⥤ C) (G : J ⥤ D) (L : C ⥤ E) (K : D ⥤ E)
    [HasColimit F] [HasColimit G] [HasColimit (F ⋙ L)] [HasColimit (G ⋙ K)]
    [PreservesColimit F L] [PreservesColimit G K] (e : F ⋙ L ≅ G ⋙ K) (j : J) :
    L.map (colimit.ι F j) ≫ (mapColimitIso F G L K e).hom =
      e.hom.app j ≫ K.map (colimit.ι G j) := by
  simp [mapColimitIso]

private theorem mapColimit_hom_ext {A : Type*} [Category A] {J : Type*} [Category J]
    (D : J ⥤ A) (F : A ⥤ ModuleCat.{w} R) [HasColimit D] [PreservesColimit D F]
    {N : ModuleCat.{w} R} (a b : F.obj (colimit D) →ₗ[R] N)
    (h : ∀ j, a.comp (F.map (colimit.ι D j)).hom = b.comp (F.map (colimit.ι D j)).hom) : a = b := by
  have e : ModuleCat.ofHom a = ModuleCat.ofHom b :=
    (isColimitOfPreserves F (colimit.isColimit D)).hom_ext (fun j ↦ ModuleCat.hom_ext (h j))
  exact congrArg ModuleCat.Hom.hom e

section FiniteColimits

variable [Module.Flat R S]
variable {J : Type} [SmallCategory J] [FinCategory J]
variable (c : LocalizationComparisons.{u, max u v w} f)
variable (D : J ⥤ ModuleGlueingDatum.{u, v, w} S f c)

private def colimitAlpha (i : Fin r) :
    LocalizedModule.Away (algebraMap R S (f i)) ↑(colimit (D ⋙ genericEvaluation S f c)) ≃ₗ[S]
      S ⊗[R] restrictFromAway f i (colimit (D ⋙ localEvaluation S f c i)) :=
  (mapColimitIso (D ⋙ genericEvaluation S f c) (D ⋙ localEvaluation S f c i)
    (localizationFunctor (Submonoid.powers (algebraMap R S (f i))))
    (ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i))) ⋙
      scalarExtension (R := R) S)
    (Functor.isoWhiskerLeft D (alphaNaturalIso S f c i))).toLinearEquiv

private def colimitAlphaIJ (i j : Fin r) :
    cechMod f (restrictFromAway f i (colimit (D ⋙ localEvaluation S f c i))) {j} ≃ₗ[R]
      cechMod f (restrictFromAway f j (colimit (D ⋙ localEvaluation S f c j))) {i} :=
  (mapColimitIso (D ⋙ localEvaluation S f c i) (D ⋙ localEvaluation S f c j)
    (ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i))) ⋙
      localizationFunctor (cechSub f {j}))
    (ModuleCat.restrictScalars (algebraMap R (Localization.Away (f j))) ⋙
      localizationFunctor (cechSub f {i}))
    (Functor.isoWhiskerLeft D (alphaIJNaturalIso S f c i j))).toLinearEquiv

private abbrev localColimitMap (i : Fin r) (j : J) :
    restrictFromAway f i ((D.obj j).localPiece i) →ₗ[R]
      restrictFromAway f i (colimit (D ⋙ localEvaluation S f c i)) :=
  ((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i)))).map
    (colimit.ι (D ⋙ localEvaluation S f c i) j)).hom

private theorem colimitAlpha_ι (i : Fin r) (j : J)
    (x : LocalizedModule.Away (algebraMap R S (f i)) (D.obj j).generic) :
    colimitAlpha S f c D i
        ((LocalizedModule.map (Submonoid.powers (algebraMap R S (f i)))
          (colimit.ι (D ⋙ genericEvaluation S f c) j).hom) x) =
      TensorProduct.map LinearMap.id (localColimitMap S f c D i j) ((D.obj j).alpha i x) :=
  DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (mapColimitIso_ι_hom (D ⋙ genericEvaluation S f c) (D ⋙ localEvaluation S f c i)
      (localizationFunctor (Submonoid.powers (algebraMap R S (f i))))
      (ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i))) ⋙
        scalarExtension (R := R) S)
      (Functor.isoWhiskerLeft D (alphaNaturalIso S f c i)) j)) x

private theorem colimitAlpha_mk_ι (i : Fin r) (j : J) (m : (D.obj j).generic) :
    colimitAlpha S f c D i (LocalizedModule.mkLinearMap _ _
      (colimit.ι (D ⋙ genericEvaluation S f c) j m)) =
      TensorProduct.map LinearMap.id (localColimitMap S f c D i j)
        ((D.obj j).alpha i (LocalizedModule.mkLinearMap _ _ m)) := by
  simpa only [LocalizedModule.mkLinearMap_apply, LocalizedModule.map_mk] using!
    colimitAlpha_ι S f c D i j (LocalizedModule.mkLinearMap _ _ m)

omit [Module.Flat R S] in
private theorem colimitAlphaIJ_ι_linear (i k : Fin r) (j : J) :
    (colimitAlphaIJ S f c D i k).toLinearMap.comp
        (localizedMap f {k} (localColimitMap S f c D i j)) =
      (localizedMap f {i} (localColimitMap S f c D k j)).comp
        ((D.obj j).alphaIJ i k).toLinearMap :=
  congrArg ModuleCat.Hom.hom
    (mapColimitIso_ι_hom (D ⋙ localEvaluation S f c i) (D ⋙ localEvaluation S f c k)
      (ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i))) ⋙
        localizationFunctor (cechSub f {k}))
      (ModuleCat.restrictScalars (algebraMap R (Localization.Away (f k))) ⋙
        localizationFunctor (cechSub f {i}))
      (Functor.isoWhiskerLeft D (alphaIJNaturalIso S f c i k)) j)

omit [Module.Flat R S] in
private theorem colimitAlphaIJ_mk_ι (i k : Fin r) (j : J)
    (m : restrictFromAway f i ((D.obj j).localPiece i)) :
    colimitAlphaIJ S f c D i k (LocalizedModule.mkLinearMap (cechSub f {k}) _
      (localColimitMap S f c D i j m)) =
      localizedMap f {i} (localColimitMap S f c D k j)
        ((D.obj j).alphaIJ i k (LocalizedModule.mkLinearMap (cechSub f {k}) _ m)) := by
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, localizedMap_mk] using
    DFunLike.congr_fun (colimitAlphaIJ_ι_linear S f c D i k j)
      (LocalizedModule.mkLinearMap (cechSub f {k}) _ m)

omit [Module.Flat R S] in
private theorem colimitAlphaIJ_tensor_ι (i k : Fin r) (j : J)
    (x : S ⊗[R] cechMod f (restrictFromAway f i ((D.obj j).localPiece i)) {k}) :
    TensorProduct.map LinearMap.id (colimitAlphaIJ S f c D i k).toLinearMap
        (TensorProduct.map LinearMap.id (localizedMap f {k} (localColimitMap S f c D i j)) x) =
      TensorProduct.map LinearMap.id (localizedMap f {i} (localColimitMap S f c D k j))
        (TensorProduct.map LinearMap.id ((D.obj j).alphaIJ i k).toLinearMap x) :=
  tensorMap_commute S _ _ _ _ (colimitAlphaIJ_ι_linear S f c D i k j) x

omit [Module.Flat R S] in
private theorem colimitAlphaIJ_localized_ι (i k : Fin r) (j : J) (t : Finset (Fin r))
    (x : cechMod f (cechMod f (restrictFromAway f i ((D.obj j).localPiece i)) {k}) t) :
    localizedMap f t (colimitAlphaIJ S f c D i k).toLinearMap
        (localizedMap f t (localizedMap f {k} (localColimitMap S f c D i j)) x) =
      localizedMap f t (localizedMap f {i} (localColimitMap S f c D k j))
        (localizedMap f t ((D.obj j).alphaIJ i k).toLinearMap x) :=
  localizedMap_commute f _ _ _ _ (colimitAlphaIJ_ι_linear S f c D i k j) t x

private abbrev colimitCompatibilityLeft (i k : Fin r) :
    ↑(colimit (D ⋙ genericEvaluation S f c)) →ₗ[S]
      S ⊗[R] cechMod f (restrictFromAway f k (colimit (D ⋙ localEvaluation S f c k))) {i} :=
  (AlgebraTensorModule.lTensor S S (colimitAlphaIJ S f c D i k).toLinearMap).comp
    ((AlgebraTensorModule.lTensor S S (LocalizedModule.mkLinearMap (cechSub f {k}) _)).comp
      ((colimitAlpha S f c D i).toLinearMap.comp (LocalizedModule.mkLinearMap _ _)))

private abbrev colimitCompatibilityRight (i k : Fin r) :
    ↑(colimit (D ⋙ genericEvaluation S f c)) →ₗ[S]
      S ⊗[R] cechMod f (restrictFromAway f k (colimit (D ⋙ localEvaluation S f c k))) {i} :=
  (AlgebraTensorModule.lTensor S S (LocalizedModule.mkLinearMap (cechSub f {i}) _)).comp
    ((colimitAlpha S f c D k).toLinearMap.comp (LocalizedModule.mkLinearMap _ _))

private theorem colimitCompatibility (i k : Fin r) :
    colimitCompatibilityLeft S f c D i k = colimitCompatibilityRight S f c D i k := by
  apply mapColimit_hom_ext (D ⋙ genericEvaluation S f c) (𝟭 (ModuleCat.{max u v w} S))
    (N := ModuleCat.of S (S ⊗[R]
      cechMod f (restrictFromAway f k (colimit (D ⋙ localEvaluation S f c k))) {i}))
  intro j
  ext m
  show TensorProduct.map LinearMap.id (colimitAlphaIJ S f c D i k).toLinearMap
    (TensorProduct.map LinearMap.id (LocalizedModule.mkLinearMap (cechSub f {k}) _)
      (colimitAlpha S f c D i (LocalizedModule.mkLinearMap _ _
        (colimit.ι (D ⋙ genericEvaluation S f c) j m)))) =
    TensorProduct.map LinearMap.id (LocalizedModule.mkLinearMap (cechSub f {i}) _)
      (colimitAlpha S f c D k (LocalizedModule.mkLinearMap _ _
        (colimit.ι (D ⋙ genericEvaluation S f c) j m)))
  rw [colimitAlpha_mk_ι, colimitAlpha_mk_ι, ← tensorMap_localizedMk,
    ← tensorMap_localizedMk, colimitAlphaIJ_tensor_ι]
  exact congrArg (TensorProduct.map LinearMap.id (localizedMap f {i} (localColimitMap S f c D k j)))
    ((D.obj j).alpha_compatibility i k m)

omit [Module.Flat R S] in
private theorem cocycle_apply (X : ModuleGlueingDatum.{u, v, w} S f c) (i j k : Fin r)
    (x : cechMod f (restrictFromAway f i (X.localPiece i)) ({j} ∪ {k})) :
    c.iterated (restrictFromAway f k (X.localPiece k)) {j} {i}
      (localizedMap f {i} (X.alphaIJ j k).toLinearMap
        ((c.iterated (restrictFromAway f j (X.localPiece j)) {k} {i}).symm
          (cechModCongr f (Finset.union_comm {i} {k})
            (c.iterated (restrictFromAway f j (X.localPiece j)) {i} {k}
              (localizedMap f {k} (X.alphaIJ i j).toLinearMap
                ((c.iterated (restrictFromAway f i (X.localPiece i)) {j} {k}).symm x)))))) =
    cechModCongr f (Finset.union_comm {i} {j})
      (c.iterated (restrictFromAway f k (X.localPiece k)) {i} {j}
        (localizedMap f {j} (X.alphaIJ i k).toLinearMap
          ((c.iterated (restrictFromAway f i (X.localPiece i)) {k} {j}).symm
            (cechModCongr f (Finset.union_comm {j} {k}) x)))) :=
  DFunLike.congr_fun (X.cocycle i j k) x

private def colimitDatum : ModuleGlueingDatum.{u, v, w} S f c where
  generic := colimit (D ⋙ genericEvaluation S f c)
  localPiece i := colimit (D ⋙ localEvaluation S f c i)
  alpha := colimitAlpha S f c D
  alphaIJ := colimitAlphaIJ S f c D
  alpha_compatibility i k m := DFunLike.congr_fun (colimitCompatibility S f c D i k) m
  cocycle i j k := by
    apply mapColimit_hom_ext (D ⋙ localEvaluation S f c i)
      (ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i))) ⋙
        localizationFunctor (cechSub f ({j} ∪ {k})))
      (N := ModuleCat.of R (cechMod f
        (restrictFromAway f k (colimit (D ⋙ localEvaluation S f c k))) ({j} ∪ {i})))
    intro a
    ext x
    rw [show ((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i))) ⋙
        localizationFunctor (cechSub f ({j} ∪ {k}))).map
          (colimit.ι (D ⋙ localEvaluation S f c i) a)).hom =
        localizedMap f ({j} ∪ {k}) (localColimitMap S f c D i a) from rfl]
    have h := congrArg
      (localizedMap f ({j} ∪ {i}) (localColimitMap S f c D k a))
      (cocycle_apply S f c (D.obj a) i j k x)
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      iterated_naturality_apply, iterated_symm_naturality_apply,
      cechModCongr_naturality, ← colimitAlphaIJ_localized_ι] using! h

private def colimitInclusion (j : J) : D.obj j ⟶ colimitDatum S f c D where
  generic := colimit.ι (D ⋙ genericEvaluation S f c) j
  localPiece i := colimit.ι (D ⋙ localEvaluation S f c i) j
  alpha_compatibility i m := colimitAlpha_mk_ι S f c D i j m
  alphaIJ_compatibility i k m := colimitAlphaIJ_mk_ι S f c D i k j m


private def colimitCocone : Cocone D where
  pt := colimitDatum S f c D
  ι :=
    { app := colimitInclusion S f c D
      naturality {j k} a := by
        apply ModuleGlueingMap.ext
        · change (genericEvaluation S f c).map (D.map a) ≫
            colimit.ι (D ⋙ genericEvaluation S f c) k = _
          simpa only [Functor.comp_map, Functor.const_obj_map, Category.comp_id] using!
            colimit.w (D ⋙ genericEvaluation S f c) a
        · funext i
          change (localEvaluation S f c i).map (D.map a) ≫
            colimit.ι (D ⋙ localEvaluation S f c i) k = _
          simpa only [Functor.comp_map, Functor.const_obj_map, Category.comp_id] using!
            colimit.w (D ⋙ localEvaluation S f c i) a }

private abbrev localColimitDesc (s : Cocone D) (i : Fin r) :
    restrictFromAway f i (colimit (D ⋙ localEvaluation S f c i)) →ₗ[R]
      restrictFromAway f i (s.pt.localPiece i) :=
  ((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i)))).map
    (colimit.desc (D ⋙ localEvaluation S f c i) ((localEvaluation S f c i).mapCocone s))).hom

omit [Module.Flat R S] [FinCategory J] in
private theorem localColimitDesc_fac (s : Cocone D) (i : Fin r) (j : J) :
    (localColimitDesc S f c D s i).comp (localColimitMap S f c D i j) =
      ((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i)))).map
        ((s.ι.app j).localPiece i)).hom := by
  show ((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i)))).map
    (colimit.ι (D ⋙ localEvaluation S f c i) j ≫
      colimit.desc (D ⋙ localEvaluation S f c i) ((localEvaluation S f c i).mapCocone s))).hom = _
  rw [colimit.ι_desc]
  rfl

private theorem colimitDesc_alpha (s : Cocone D) (i : Fin r) :
    (s.pt.alpha i).toLinearMap.comp ((LocalizedModule.mkLinearMap _ _).comp
      (colimit.desc (D ⋙ genericEvaluation S f c) ((genericEvaluation S f c).mapCocone s)).hom) =
    (AlgebraTensorModule.lTensor S S (localColimitDesc S f c D s i)).comp
      ((colimitAlpha S f c D i).toLinearMap.comp (LocalizedModule.mkLinearMap _ _)) := by
  apply mapColimit_hom_ext (D ⋙ genericEvaluation S f c) (𝟭 (ModuleCat.{max u v w} S))
    (N := ModuleCat.of S (S ⊗[R] restrictFromAway f i (s.pt.localPiece i)))
  intro j
  ext m
  show s.pt.alpha i (LocalizedModule.mkLinearMap _ _
    ((colimit.ι (D ⋙ genericEvaluation S f c) j ≫
      colimit.desc (D ⋙ genericEvaluation S f c) ((genericEvaluation S f c).mapCocone s)) m)) =
    TensorProduct.map LinearMap.id (localColimitDesc S f c D s i)
      (colimitAlpha S f c D i (LocalizedModule.mkLinearMap _ _
        (colimit.ι (D ⋙ genericEvaluation S f c) j m)))
  rw [colimit.ι_desc, colimitAlpha_mk_ι, TensorProduct.map_map, localColimitDesc_fac]
  exact (s.ι.app j).alpha_compatibility i m

omit [Module.Flat R S] in
private theorem colimitDesc_alphaIJ (s : Cocone D) (i k : Fin r) :
    (s.pt.alphaIJ i k).toLinearMap.comp ((LocalizedModule.mkLinearMap (cechSub f {k}) _).comp
      (localColimitDesc S f c D s i)) =
    (localizedMap f {i} (localColimitDesc S f c D s k)).comp
      ((colimitAlphaIJ S f c D i k).toLinearMap.comp
        (LocalizedModule.mkLinearMap (cechSub f {k}) _)) := by
  apply mapColimit_hom_ext (D ⋙ localEvaluation S f c i)
    (ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i))))
    (N := ModuleCat.of R (cechMod f (restrictFromAway f k (s.pt.localPiece k)) {i}))
  intro j
  ext m
  show s.pt.alphaIJ i k (LocalizedModule.mkLinearMap (cechSub f {k}) _
    (((localColimitDesc S f c D s i).comp (localColimitMap S f c D i j)) m)) =
    localizedMap f {i} (localColimitDesc S f c D s k)
      (colimitAlphaIJ S f c D i k
        (LocalizedModule.mkLinearMap (cechSub f {k}) _ (localColimitMap S f c D i j m)))
  rw [localColimitDesc_fac, colimitAlphaIJ_mk_ι]
  show _ = ((localizedMap f {i} (localColimitDesc S f c D s k)).comp
    (localizedMap f {i} (localColimitMap S f c D k j))) _
  rw [← localizedMap_comp, localColimitDesc_fac]
  exact (s.ι.app j).alphaIJ_compatibility i k m

private def colimitDesc (s : Cocone D) : colimitDatum S f c D ⟶ s.pt where
  generic := colimit.desc (D ⋙ genericEvaluation S f c) ((genericEvaluation S f c).mapCocone s)
  localPiece i := colimit.desc (D ⋙ localEvaluation S f c i) ((localEvaluation S f c i).mapCocone s)
  alpha_compatibility i m := DFunLike.congr_fun (colimitDesc_alpha S f c D s i) m
  alphaIJ_compatibility i k m := DFunLike.congr_fun (colimitDesc_alphaIJ S f c D s i k) m

private def colimitCoconeIsColimit : IsColimit (colimitCocone S f c D) where
  desc := colimitDesc S f c D
  fac s j := by
    apply ModuleGlueingMap.ext
    · exact colimit.ι_desc ((genericEvaluation S f c).mapCocone s) j
    · funext i
      exact colimit.ι_desc ((localEvaluation S f c i).mapCocone s) j
  uniq s m h := by
    apply ModuleGlueingMap.ext
    · apply colimit.hom_ext
      intro j
      exact (congrArg ModuleGlueingMap.generic (h j)).trans
        (colimit.ι_desc ((genericEvaluation S f c).mapCocone s) j).symm
    · funext i
      apply colimit.hom_ext
      intro j
      exact (congrArg (fun a ↦ a.localPiece i) (h j)).trans
        (colimit.ι_desc ((localEvaluation S f c i).mapCocone s) j).symm

end FiniteColimits

private theorem glueingHasFiniteColimits [Module.Flat R S]
    (c : LocalizationComparisons.{u, max u v w} f) :
    HasFiniteColimits (ModuleGlueingDatum.{u, v, w} S f c) where
  out _ _ _ := ⟨fun D ↦ ⟨⟨colimitCocone S f c D, colimitCoconeIsColimit S f c D⟩⟩⟩

attribute [local instance] glueingHasFiniteColimits

private theorem genericEvaluation_preservesFiniteColimits [Module.Flat R S]
    (c : LocalizationComparisons.{u, max u v w} f) :
    PreservesFiniteColimits (genericEvaluation S f c) where
  preservesFiniteColimits _ _ _ :=
    { preservesColimit := fun {D} ↦
        preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit S f c D)
          (show IsColimit ((genericEvaluation S f c).mapCocone (colimitCocone S f c D)) from
            colimit.isColimit (D ⋙ genericEvaluation S f c)) }

private theorem localEvaluation_preservesFiniteColimits [Module.Flat R S]
    (c : LocalizationComparisons.{u, max u v w} f) (i : Fin r) :
    PreservesFiniteColimits (localEvaluation S f c i) where
  preservesFiniteColimits _ _ _ :=
    { preservesColimit := fun {D} ↦
        preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit S f c D)
          (show IsColimit ((localEvaluation S f c i).mapCocone (colimitCocone S f c D)) from
            colimit.isColimit (D ⋙ localEvaluation S f c i)) }

attribute [local instance] genericEvaluation_preservesFiniteColimits
  localEvaluation_preservesFiniteColimits

@[instance_reducible] private def glueingAbelian [Module.Flat R S]
    (c : LocalizationComparisons.{u, max u v w} f) :
    Abelian (ModuleGlueingDatum.{u, v, w} S f c) := by
  letI : ∀ {X Y : ModuleGlueingDatum.{u, v, w} S f c} (g : X ⟶ Y),
      IsIso (Abelian.coimageImageComparison g) := fun {X Y} g ↦ by
    have : IsIso ((Abelian.coimageImageComparison g).generic) := by
      change IsIso ((genericEvaluation S f c).map (Abelian.coimageImageComparison g))
      rw [Arrow.isIso_iff_isIso_of_isIso
        (Abelian.PreservesCoimageImageComparison.iso (genericEvaluation S f c) g).hom]
      infer_instance
    have : ∀ i, IsIso ((Abelian.coimageImageComparison g).localPiece i) := fun i ↦ by
      change IsIso ((localEvaluation S f c i).map (Abelian.coimageImageComparison g))
      rw [Arrow.isIso_iff_isIso_of_isIso
        (Abelian.PreservesCoimageImageComparison.iso (localEvaluation S f c i) g).hom]
      infer_instance
    exact isIso_of_components S f c (Abelian.coimageImageComparison g)
  exact Abelian.ofCoimageImageComparisonIsIso

/-- For a flat ring map, the category of module glueing data is abelian, and the canonical
functor from modules is exact and preserves arbitrary colimits. -/
@[stacks 05EN]
public theorem moduleGlueingConstruction_abelian_exact_preservesColimits
    {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S] [Module.Flat R S]
    {r : ℕ} (f : Fin r → R) :
    let c := moduleGlueingConstruction.{u, v, w} S f
    letI := c.category
    Nonempty (Abelian (ModuleGlueingDatum.{u, v, w} S f c.comparison)) ∧
      exactFunctor (ModuleCat.{max u v w} R)
        (ModuleGlueingDatum.{u, v, w} S f c.comparison) c.canonical ∧
      PreservesColimits c.canonical := by
  let := canonical_preservesFiniteLimits.{u, v, w} S f
  let := canonical_preservesColimits.{u, v, w} S f
  refine ⟨⟨glueingAbelian S f (localizationComparisons f)⟩, ?_, ?_⟩
  · show PreservesFiniteLimits (canonicalFunctor.{u, v, w} S f) ∧
      PreservesFiniteColimits (canonicalFunctor.{u, v, w} S f)
    exact ⟨inferInstance, inferInstance⟩
  · exact canonical_preservesColimits S f


end

end FormalGlueing


end
