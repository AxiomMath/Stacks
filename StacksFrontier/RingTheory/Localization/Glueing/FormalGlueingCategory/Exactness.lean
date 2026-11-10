module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingComplex
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingCategory.Adjunction

/-!
# Left exactness of compatible sections

The compatible-sections functor `H⁰` on module glueing data is left exact, and the canonical
functor `Can` preserves colimits. This file also sets up the additive structure on module glueing
data and the exactness of localization and of flat scalar extension, used in
`FormalGlueingCategory.Abelian`.

## Main results

* `FormalGlueing.compatibleSectionsFunctor_preservesFiniteLimits`: the compatible-sections
  functor `H⁰` is left exact.
-/

@[expose] public section

namespace FormalGlueing

universe u v w

open CategoryTheory Cech TensorProduct

variable {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
variable {r : ℕ} (f : Fin r → R)

attribute [local instance] LocalizedModule.moduleOfIsLocalization

/-! ### Left exactness of the compatible-sections functor -/

section SectionsLeftExact

set_option backward.isDefEq.respectTransparency false

open CategoryTheory.Limits

/-- The comparison of iterated localizations is unique: both are pinned down on
denominator-one fractions. -/
theorem localizationComparisons_eq (comparison : LocalizationComparisons.{u, w} f) :
    comparison = localizationComparisons f := by
  cases comparison with
  | mk iterated iterated_mk =>
  have : iterated = (localizationComparisons f).iterated := by
    funext M _ _ s t
    apply LinearEquiv.toLinearMap_injective
    let := iterated_isLocalized f M s t
    apply IsLocalizedModule.ext (Submonoid.closure (f '' (↑(s ∪ t) : Set (Fin r))))
      ((LocalizedModule.mkLinearMap (cechSub f t) _).comp
        (LocalizedModule.mkLinearMap (cechSub f s) M))
      (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap (cechSub f (s ∪ t)) M))
    ext m
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [iterated_mk, (localizationComparisons f).iterated_mk]
  subst this
  rfl

noncomputable section

private theorem sectionsScalarTower (N : ModuleCat.{w} S) :
    IsScalarTower R S (restrictFromTarget (R := R) S N) :=
  ⟨fun a b m ↦ by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩

attribute [local instance] sectionsScalarTower

private theorem sectionsAwayUnits (i : Fin r)
    (N : ModuleCat.{w} (Localization.Away (f i)))
    (a : Submonoid.powers (f i)) :
    IsUnit (algebraMap R (Module.End R (restrictFromAway f i N)) a) := by
  rw [Module.End.isUnit_iff]
  exact (IsLocalization.map_units (Localization.Away (f i)) a).smul_bijective

private def sectionsLiftAway (M : ModuleCat.{w} R) (i : Fin r)
    (N : ModuleCat.{max u w} (Localization.Away (f i)))
    (g : M →ₗ[R] restrictFromAway f i N) : canonicalLocalPiece f M i ⟶ N := by
  letI : Module R N := Module.compHom N (algebraMap R (Localization.Away (f i)))
  letI : IsScalarTower R (Localization.Away (f i)) N :=
    sectionsScalarTower (Localization.Away (f i)) N
  exact ModuleCat.ofHom <| LinearMap.extendScalarsOfIsLocalization
    (Submonoid.powers (f i)) (Localization.Away (f i))
    (N := restrictFromAway f i N)
    (LocalizedModule.lift (Submonoid.powers (f i)) g (sectionsAwayUnits f i N))

private theorem sectionsLiftAway_mk (M : ModuleCat.{w} R) (i : Fin r)
    (N : ModuleCat.{max u w} (Localization.Away (f i)))
    (g : M →ₗ[R] restrictFromAway f i N) (m : M) :
    sectionsLiftAway f M i N g (canonicalLocalMk f M i m) = g m :=
  LocalizedModule.lift_mk_one (Submonoid.powers (f i)) (g := g) (sectionsAwayUnits f i N) m

private theorem sectionsAway_hom_ext (M : ModuleCat.{w} R) (i : Fin r)
    (N : ModuleCat.{max u w} (Localization.Away (f i)))
    (g h : canonicalLocalPiece f M i ⟶ N)
    (he : ∀ m, g (canonicalLocalMk f M i m) = h (canonicalLocalMk f M i m)) : g = h := by
  apply (ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i)))).map_injective
  apply ModuleCat.hom_ext
  apply IsLocalizedModule.ext (Submonoid.powers (f i))
    (canonicalLocalMk f M i) (sectionsAwayUnits f i N)
  exact LinearMap.ext he

private def sectionsLiftGeneric (M : ModuleCat.{w} R) (N : ModuleCat.{max v w} S)
    (g : M →ₗ[R] restrictFromTarget (R := R) S N) :
    ModuleCat.of S (S ⊗[R] M) ⟶ N := by
  letI : Module R N := Module.compHom N (algebraMap R S)
  letI : IsScalarTower R S N := sectionsScalarTower S N
  exact ModuleCat.ofHom <| AlgebraTensorModule.lift (P := restrictFromTarget (R := R) S N)
    (LinearMap.toSpanSingleton S (M →ₗ[R] restrictFromTarget (R := R) S N) g)

private theorem sectionsLiftGeneric_tmul (M : ModuleCat.{w} R)
    (N : ModuleCat.{max v w} S) (g : M →ₗ[R] restrictFromTarget (R := R) S N)
    (s : S) (m : M) : sectionsLiftGeneric S M N g (s ⊗ₜ[R] m) = s • g m := rfl

private def sectionsGenericProj (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f)) :
    compatibleSections S f (localizationComparisons f) X →ₗ[R]
      restrictFromTarget (R := R) S X.generic :=
  (LinearMap.fst R _ _).comp (compatibleSections S f (localizationComparisons f) X).subtype

private def sectionsLocalProj (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f))
    (i : Fin r) : compatibleSections S f (localizationComparisons f) X →ₗ[R]
      restrictFromAway f i (X.localPiece i) :=
  (LinearMap.proj i).comp ((LinearMap.snd R _ _).comp
    (compatibleSections S f (localizationComparisons f) X).subtype)

private def sectionsLiftCanonical (M : ModuleCat.{max u v w} R)
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f))
    (g : M →ₗ[R] compatibleSections S f (localizationComparisons f) X) :
    ModuleGlueingMap S f (localizationComparisons f) (canonicalDatum S f M) X where
  generic := sectionsLiftGeneric S M X.generic ((sectionsGenericProj S f X).comp g)
  localPiece i := sectionsLiftAway f M i (X.localPiece i) ((sectionsLocalProj S f X i).comp g)
  alpha_compatibility i m := by
    induction m using TensorProduct.inductionOn with
    | tmul s m =>
      change X.alpha i (LocalizedModule.mkLinearMap _ _
          (s • (sectionsGenericProj S f X (g m)))) =
        TensorProduct.map _ _ (canonicalAlpha S f M i
          (LocalizedModule.mkLinearMap _ _ (s ⊗ₜ[R] m)))
      rw [map_smul, map_smul, canonicalAlpha_mk, TensorProduct.map_tmul]
      change s • (X.alpha i (LocalizedModule.mkLinearMap _ _ (g m).1.1)) =
        s ⊗ₜ[R] (show restrictFromAway f i (X.localPiece i) from
          sectionsLiftAway f M i (X.localPiece i) _ (canonicalLocalMk f M i m))
      rw [(g m).2.1 i, sectionsLiftAway_mk]
      change s • ((1 : S) ⊗ₜ[R] (show restrictFromAway f i (X.localPiece i) from (g m).1.2 i)) =
        s ⊗ₜ[R] (show restrictFromAway f i (X.localPiece i) from (g m).1.2 i)
      rw [TensorProduct.smul_tmul']
      change (s * 1) ⊗ₜ[R] _ = s ⊗ₜ[R] _
      rw [mul_one]
    | add a b ha hb => simpa only [ModuleCat.Hom.hom, map_add] using congrArg₂ (· + ·) ha hb
  alphaIJ_compatibility i j m := by
    let a : restrictFromAway f i (canonicalLocalPiece f M i) →ₗ[R]
        restrictFromAway f i (X.localPiece i) :=
      ((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i)))).map
        (sectionsLiftAway f M i (X.localPiece i) ((sectionsLocalProj S f X i).comp g))).hom
    let b : restrictFromAway f j (canonicalLocalPiece f M j) →ₗ[R]
        restrictFromAway f j (X.localPiece j) :=
      ((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f j)))).map
        (sectionsLiftAway f M j (X.localPiece j) ((sectionsLocalProj S f X j).comp g))).hom
    suffices (X.alphaIJ i j).toLinearMap.comp
        ((LocalizedModule.mkLinearMap (cechSub f {j}) _).comp a) =
      (localizedMap f {i} b).comp ((canonicalAlphaIJ f M i j).toLinearMap.comp
        (LocalizedModule.mkLinearMap (cechSub f {j}) _)) from
      DFunLike.congr_fun this m
    apply IsLocalizedModule.ext (Submonoid.powers (f i)) (canonicalLocalMk f M i)
    · intro s
      exact IsLocalizedModule.map_units (S := cechSub f {i})
        (LocalizedModule.mkLinearMap (cechSub f {i})
          (restrictFromAway f j (X.localPiece j)))
        ⟨s, by simpa only [cechSub, Finset.prod_singleton] using s.2⟩
    · ext n
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, canonicalAlphaIJ_mk,
        localizedMap_mk]
      change X.alphaIJ i j (LocalizedModule.mkLinearMap _ _
        (sectionsLiftAway f M i (X.localPiece i) _ (canonicalLocalMk f M i n))) =
          LocalizedModule.mkLinearMap (cechSub f {i}) (restrictFromAway f j (X.localPiece j))
            (sectionsLiftAway f M j (X.localPiece j) _ (canonicalLocalMk f M j n))
      rw [sectionsLiftAway_mk, sectionsLiftAway_mk]
      exact (g n).2.2 i j

attribute [local instance] moduleGlueingCategory

private def sectionsCanonicalHomEquiv (M : ModuleCat.{max u v w} R)
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f)) :
    ((canonicalFunctor S f).obj M ⟶ X) ≃
      (M ⟶ (compatibleSectionsFunctor S f (localizationComparisons f)).obj X) where
  toFun g := (canonicalSectionsUnit S f).app M ≫
    (compatibleSectionsFunctor S f (localizationComparisons f)).map g
  invFun g := sectionsLiftCanonical S f M X g.hom
  left_inv g := by
    apply ModuleGlueingMap.ext
    · let : Module R X.generic := Module.compHom X.generic (algebraMap R S)
      let : IsScalarTower R S X.generic := sectionsScalarTower S X.generic
      apply ModuleCat.hom_ext
      apply AlgebraTensorModule.ext
      intro s m
      change s • g.generic (1 ⊗ₜ[R] m) = g.generic (s ⊗ₜ[R] m)
      rw [← map_smul]
      change g.generic ((s * 1) ⊗ₜ[R] m) = g.generic (s ⊗ₜ[R] m)
      rw [mul_one]
    · funext i
      apply sectionsAway_hom_ext
      intro m
      dsimp only [sectionsLiftCanonical]
      rw [sectionsLiftAway_mk]
      rfl
  right_inv g := by
    ext m
    apply Subtype.ext
    apply Prod.ext
    · change (1 : S) • (g m).1.1 = (g m).1.1
      exact one_smul _ _
    · funext i
      exact sectionsLiftAway_mk f M i (X.localPiece i) _ m

private def canonicalSectionsAdjunctionAux :
    canonicalFunctor S f ⊣ compatibleSectionsFunctor S f (localizationComparisons f) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := sectionsCanonicalHomEquiv S f
      homEquiv_naturality_left_symm := by
        intro M N X a g
        apply (sectionsCanonicalHomEquiv S f M X).injective
        rw [Equiv.apply_symm_apply]
        change a ≫ g = (canonicalSectionsUnit S f).app M ≫
          (compatibleSectionsFunctor S f (localizationComparisons f)).map
            ((canonicalFunctor S f).map a ≫ (sectionsCanonicalHomEquiv S f N X).symm g)
        rw [Functor.map_comp, ← Category.assoc, ← Functor.comp_map,
          ← NatTrans.naturality, Category.assoc]
        exact congrArg (a ≫ ·) ((sectionsCanonicalHomEquiv S f N X).apply_symm_apply g).symm
      homEquiv_naturality_right := by
        intro M X Y a b
        change (canonicalSectionsUnit S f).app M ≫
            (compatibleSectionsFunctor S f (localizationComparisons f)).map (a ≫ b) =
          ((canonicalSectionsUnit S f).app M ≫
            (compatibleSectionsFunctor S f (localizationComparisons f)).map a) ≫
            (compatibleSectionsFunctor S f (localizationComparisons f)).map b
        rw [Functor.map_comp, Category.assoc] }

end

/-- The compatible-sections functor `H⁰` preserves finite limits: it is right adjoint to the
canonical glueing functor, since compatible tuples form the equalizer of the generic/local and
overlap comparison maps out of the product of the component modules. -/
public theorem compatibleSectionsFunctor_preservesFiniteLimits
    (comparison : LocalizationComparisons.{u, max u v w} f) :
    letI := moduleGlueingCategory S f comparison
    PreservesFiniteLimits (compatibleSectionsFunctor.{u, v, w} S f comparison) := by
  obtain rfl := localizationComparisons_eq f comparison
  let := moduleGlueingCategory S f (localizationComparisons f)
  have : PreservesLimitsOfSize.{0, 0}
      (compatibleSectionsFunctor.{u, v, w} S f (localizationComparisons f)) :=
    (canonicalSectionsAdjunctionAux.{u, v, w} S f).rightAdjoint_preservesLimits.{0, 0}
  exact PreservesLimitsOfSize.preservesFiniteLimits _

/-- The compatible-sections functor of `moduleGlueingConstruction` preserves finite limits. -/
public theorem moduleGlueingConstruction_sections_preservesFiniteLimits :
    letI := (moduleGlueingConstruction.{u, v, w} S f).category
    PreservesFiniteLimits (moduleGlueingConstruction.{u, v, w} S f).sections :=
  compatibleSectionsFunctor_preservesFiniteLimits S f (localizationComparisons f)

end SectionsLeftExact

end FormalGlueing

end

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

private theorem canonical_preservesColimits : PreservesColimits (canonicalFunctor.{u, v, w} S f) :=
  (canonicalSectionsAdjunctionAux.{u, v, w} S f).leftAdjoint_preservesColimits

private theorem localizedMap_add {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (t : Finset (Fin r)) (a b : M →ₗ[R] N) :
    localizedMap f t (a + b) = localizedMap f t a + localizedMap f t b := by
  ext x
  induction x using LocalizedModule.induction_on with
  | h m s => simp [localizedMap, LocalizedModule.map_mk]

private theorem localizedMap_neg {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (t : Finset (Fin r)) (a : M →ₗ[R] N) :
    localizedMap f t (-a) = -localizedMap f t a := by
  ext x
  induction x using LocalizedModule.induction_on with
  | h m s => simp [localizedMap, LocalizedModule.map_mk]

private def compatibleMaps
    (c : LocalizationComparisons.{u, max u v w} f)
    (X Y : ModuleGlueingDatum.{u, v, w} S f c) :
    AddSubgroup ((X.generic ⟶ Y.generic) × ∀ i, X.localPiece i ⟶ Y.localPiece i) where
  carrier a :=
    (∀ i (m : restrictFromTarget (R := R) S X.generic),
      Y.alpha i (LocalizedModule.mkLinearMap _ _ (a.1 m)) =
        TensorProduct.map LinearMap.id
          (((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i)))).map (a.2 i)).hom)
          (X.alpha i (LocalizedModule.mkLinearMap _ _ m))) ∧
    (∀ i j (m : restrictFromAway f i (X.localPiece i)),
      Y.alphaIJ i j (LocalizedModule.mkLinearMap (cechSub f {j}) _ (a.2 i m)) =
        localizedMap f {i}
          (((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f j)))).map (a.2 j)).hom)
          (X.alphaIJ i j (LocalizedModule.mkLinearMap (cechSub f {j}) _ m)))
  zero_mem' := by
    constructor
    · intro i m
      simp
    · intro i j m
      simp [localizedMap]
  add_mem' {a b} ha hb := by
    constructor
    · intro i m
      change Y.alpha i (LocalizedModule.mkLinearMap _ _ (a.1.hom m + b.1.hom m)) = _
      rw [map_add, map_add, ha.1, hb.1]
      change _ = TensorProduct.map LinearMap.id
        ((((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i)))).map (a.2 i)).hom) +
          (((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i)))).map
            (b.2 i)).hom)) _
      rw [TensorProduct.map_add_right, LinearMap.add_apply]
    · intro i j m
      change Y.alphaIJ i j (LocalizedModule.mkLinearMap _ _ ((a.2 i).hom m + (b.2 i).hom m)) = _
      rw [map_add, map_add, ha.2, hb.2]
      change _ = localizedMap f {i}
        ((((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f j)))).map (a.2 j)).hom) +
          (((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f j)))).map
            (b.2 j)).hom)) _
      rw [localizedMap_add, LinearMap.add_apply]
  neg_mem' {a} ha := by
    constructor
    · intro i m
      change Y.alpha i (LocalizedModule.mkLinearMap _ _ (-a.1.hom m)) = _
      rw [map_neg, map_neg, ha.1]
      change _ = TensorProduct.map LinearMap.id
        (-((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i)))).map (a.2 i)).hom) _
      exact (DFunLike.congr_fun (LinearMap.lTensor_neg (M := S)
        ((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i)))).map
          (a.2 i)).hom) _).symm
    · intro i j m
      change Y.alphaIJ i j (LocalizedModule.mkLinearMap _ _ (-(a.2 i).hom m)) = _
      rw [map_neg, map_neg, ha.2]
      change _ = localizedMap f {i}
        (-((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f j)))).map (a.2 j)).hom) _
      rw [localizedMap_neg, LinearMap.neg_apply]

private def compatibleMapsEquiv
    (c : LocalizationComparisons.{u, max u v w} f)
    (X Y : ModuleGlueingDatum.{u, v, w} S f c) :
    (X ⟶ Y) ≃ compatibleMaps S f c X Y where
  toFun a := ⟨⟨a.generic, a.localPiece⟩, a.alpha_compatibility, a.alphaIJ_compatibility⟩
  invFun a := ⟨a.1.1, a.1.2, a.2.1, a.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[instance_reducible] private def glueingPreadditive
    (c : LocalizationComparisons.{u, max u v w} f) :
    Preadditive (ModuleGlueingDatum.{u, v, w} S f c) where
  homGroup X Y := (compatibleMapsEquiv S f c X Y).addCommGroup
  add_comp X Y Z a b g := by
    apply ModuleGlueingMap.ext
    · change (a.generic + b.generic) ≫ g.generic = a.generic ≫ g.generic + b.generic ≫ g.generic
      exact Preadditive.add_comp _ _ _ _ _ _
    · funext i
      change (a.localPiece i + b.localPiece i) ≫ g.localPiece i =
        a.localPiece i ≫ g.localPiece i + b.localPiece i ≫ g.localPiece i
      exact Preadditive.add_comp _ _ _ _ _ _
  comp_add X Y Z a g h := by
    apply ModuleGlueingMap.ext
    · change a.generic ≫ (g.generic + h.generic) = a.generic ≫ g.generic + a.generic ≫ h.generic
      exact Preadditive.comp_add _ _ _ _ _ _
    · funext i
      change a.localPiece i ≫ (g.localPiece i + h.localPiece i) =
        a.localPiece i ≫ g.localPiece i + a.localPiece i ≫ h.localPiece i
      exact Preadditive.comp_add _ _ _ _ _ _

attribute [local instance] glueingPreadditive

private def genericEvaluation (c : LocalizationComparisons.{u, max u v w} f) :
    ModuleGlueingDatum.{u, v, w} S f c ⥤ ModuleCat.{max u v w} S where
  obj X := X.generic
  map a := a.generic

private def localEvaluation (c : LocalizationComparisons.{u, max u v w} f) (i : Fin r) :
    ModuleGlueingDatum.{u, v, w} S f c ⥤ ModuleCat.{max u v w} (Localization.Away (f i)) where
  obj X := X.localPiece i
  map a := a.localPiece i

private theorem genericEvaluation_additive (c : LocalizationComparisons.{u, max u v w} f) :
    (genericEvaluation S f c).Additive := ⟨rfl⟩

private theorem localEvaluation_additive
    (c : LocalizationComparisons.{u, max u v w} f) (i : Fin r) :
    (localEvaluation S f c i).Additive := ⟨rfl⟩

attribute [local instance] genericEvaluation_additive localEvaluation_additive

private def localizationFunctor (T : Submonoid R) :
    ModuleCat.{w} R ⥤ ModuleCat.{max u w} R where
  obj M := ModuleCat.of R (LocalizedModule T M)
  map a := ModuleCat.ofHom ((LocalizedModule.map T a.hom).restrictScalars R)
  map_id M := by
    apply ModuleCat.hom_ext
    ext x
    induction x using LocalizedModule.induction_on with
    | h m s => simp
  map_comp a b := by
    apply ModuleCat.hom_ext
    ext x
    induction x using LocalizedModule.induction_on with
    | h m s => simp [LocalizedModule.map_mk]

private theorem localizationFunctor_additive (T : Submonoid R) :
    (localizationFunctor.{u, w} T).Additive where
  map_add {X Y} a b := by
    apply ModuleCat.hom_ext
    ext x
    induction x using LocalizedModule.induction_on with
    | h m s => simp [localizationFunctor, LocalizedModule.map_mk]

attribute [local instance] localizationFunctor_additive

private theorem localizationFunctor_exact (T : Submonoid R) :
    PreservesFiniteLimits (localizationFunctor.{u, w} T) ∧
      PreservesFiniteColimits (localizationFunctor.{u, w} T) := by
  apply ((Functor.exact_tfae _).out 2 4).mp
  intro K hK
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hK ⊢
  exact IsLocalizedModule.map_exact T
    (LocalizedModule.mkLinearMap T K.X₁) (LocalizedModule.mkLinearMap T K.X₂)
    (LocalizedModule.mkLinearMap T K.X₃) K.f.hom K.g.hom hK

private def scalarExtension : ModuleCat.{w} R ⥤ ModuleCat.{max v w} S where
  obj M := ModuleCat.of S (S ⊗[R] M)
  map a := ModuleCat.ofHom (AlgebraTensorModule.lTensor S S a.hom)
  map_id _ := ModuleCat.hom_ext (AlgebraTensorModule.lTensor_id)
  map_comp _ _ := ModuleCat.hom_ext (AlgebraTensorModule.lTensor_comp _ _)

private theorem scalarExtension_additive : (scalarExtension.{u, v, w} (R := R) S).Additive where
  map_add {X Y} a b := by
    apply ModuleCat.hom_ext
    change AlgebraTensorModule.lTensor S S (a.hom + b.hom) =
      AlgebraTensorModule.lTensor S S a.hom + AlgebraTensorModule.lTensor S S b.hom
    apply AlgebraTensorModule.ext
    intro s x
    exact TensorProduct.tmul_add s (a.hom x) (b.hom x)

attribute [local instance] scalarExtension_additive

private theorem scalarExtension_exact [Module.Flat R S] :
    PreservesFiniteLimits (scalarExtension.{u, v, w} (R := R) S) ∧
      PreservesFiniteColimits (scalarExtension.{u, v, w} (R := R) S) := by
  apply ((Functor.exact_tfae _).out 2 4).mp
  intro K hK
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hK ⊢
  exact Module.Flat.lTensor_exact S hK

private theorem localization_preservesFiniteLimits (T : Submonoid R) :
    PreservesFiniteLimits (localizationFunctor.{u, w} T) := (localizationFunctor_exact T).1

private theorem localization_preservesFiniteColimits (T : Submonoid R) :
    PreservesFiniteColimits (localizationFunctor.{u, w} T) := (localizationFunctor_exact T).2

private theorem scalarExtension_preservesFiniteLimits [Module.Flat R S] :
    PreservesFiniteLimits (scalarExtension.{u, v, w} (R := R) S) :=
  (scalarExtension_exact (R := R) S).1

private theorem scalarExtension_preservesFiniteColimits [Module.Flat R S] :
    PreservesFiniteColimits (scalarExtension.{u, v, w} (R := R) S) :=
  (scalarExtension_exact (R := R) S).2

attribute [local instance] localization_preservesFiniteLimits localization_preservesFiniteColimits
  scalarExtension_preservesFiniteLimits scalarExtension_preservesFiniteColimits

private theorem isUnit_of_localizedEquiv (T : Submonoid R)
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : LocalizedModule T M ≃ₗ[R] N) (s : T) :
    IsUnit (algebraMap R (Module.End R N) s) := by
  rw [Module.End.isUnit_iff]
  have h := IsLocalizedModule.map_units (LocalizedModule.mkLinearMap T M) s
  rw [Module.End.isUnit_iff] at h
  constructor
  · intro x y hxy
    apply e.symm.injective
    apply h.1
    change (s : R) • e.symm x = (s : R) • e.symm y
    change (s : R) • x = (s : R) • y at hxy
    rw [← e.symm.map_smul, ← e.symm.map_smul, hxy]
  · intro y
    obtain ⟨x, hx⟩ := h.2 (e.symm y)
    refine ⟨e x, ?_⟩
    change (s : R) • e x = y
    rw [← e.map_smul]
    change e ((algebraMap R (Module.End R (LocalizedModule T M)) s) x) = y
    rw [hx, e.apply_symm_apply]

private abbrev restrictedLocalEvaluation (c : LocalizationComparisons.{u, max u v w} f)
    (i : Fin r) :=
  localEvaluation S f c i ⋙ ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i)))

private def alphaNaturalIso (c : LocalizationComparisons.{u, max u v w} f) (i : Fin r) :
    genericEvaluation S f c ⋙ localizationFunctor (Submonoid.powers (algebraMap R S (f i))) ≅
      restrictedLocalEvaluation S f c i ⋙ scalarExtension (R := R) S :=
  NatIso.ofComponents (fun X ↦ (X.alpha i).toModuleIso) (by
    intro X Y g
    apply ModuleCat.hom_ext
    change (Y.alpha i).toLinearMap.comp
        ((LocalizedModule.map (Submonoid.powers (algebraMap R S (f i)))
          g.generic.hom).restrictScalars S) =
      (AlgebraTensorModule.lTensor S S
        ((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i)))).map
          (g.localPiece i)).hom).comp
        (X.alpha i).toLinearMap
    apply IsLocalizedModule.ext (Submonoid.powers (algebraMap R S (f i)))
      (LocalizedModule.mkLinearMap _ X.generic) (isUnit_of_localizedEquiv _ (Y.alpha i))
    ext m
    simpa only [LinearMap.comp_apply, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
      AlgebraTensorModule.coe_lTensor, LocalizedModule.mkLinearMap_apply,
      LocalizedModule.map_mk] using! g.alpha_compatibility i m)

private def alphaIJNaturalIso (c : LocalizationComparisons.{u, max u v w} f) (i j : Fin r) :
    restrictedLocalEvaluation S f c i ⋙ localizationFunctor (cechSub f {j}) ≅
      restrictedLocalEvaluation S f c j ⋙ localizationFunctor (cechSub f {i}) :=
  NatIso.ofComponents (fun X ↦ (X.alphaIJ i j).toModuleIso) (by
    intro X Y g
    apply ModuleCat.hom_ext
    change (Y.alphaIJ i j).toLinearMap.comp
        (localizedMap f {j}
          ((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i)))).map
            (g.localPiece i)).hom) =
      (localizedMap f {i}
        ((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f j)))).map
          (g.localPiece j)).hom).comp
        (X.alphaIJ i j).toLinearMap
    apply IsLocalizedModule.ext (cechSub f {j}) (LocalizedModule.mkLinearMap _ _)
      (isUnit_of_localizedEquiv _ (Y.alphaIJ i j))
    ext m
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, localizedMap_mk,
      ModuleCat.RestrictScalars.map'] using! g.alphaIJ_compatibility i j m)

private theorem inverse_naturality {C E : Type*} [Category C] [Category E]
    {F G : C ⥤ E} (a : F ⟶ G) {X Y : C} (g : X ⟶ Y)
    [IsIso (F.map g)] [IsIso (G.map g)] :
    inv (F.map g) ≫ a.app X = a.app Y ≫ inv (G.map g) := by
  apply (cancel_epi (F.map g)).mp
  rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp,
    ← Category.assoc, a.naturality, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

private def inverseGlueingMap (c : LocalizationComparisons.{u, max u v w} f)
    {X Y : ModuleGlueingDatum.{u, v, w} S f c} (g : X ⟶ Y)
    [IsIso g.generic] [∀ i, IsIso (g.localPiece i)] : Y ⟶ X where
  generic := inv g.generic
  localPiece i := inv (g.localPiece i)
  alpha_compatibility i m := by
    have : IsIso ((genericEvaluation S f c).map g) := ‹IsIso g.generic›
    have : IsIso ((localEvaluation S f c i).map g) := inferInstanceAs (IsIso (g.localPiece i))
    have : IsIso ((restrictedLocalEvaluation S f c i).map g) := by
      change IsIso ((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i)))).map
        (g.localPiece i))
      infer_instance
    have : IsIso ((genericEvaluation S f c ⋙ localizationFunctor
        (Submonoid.powers (algebraMap R S (f i)))).map g) := by
      change IsIso ((localizationFunctor (Submonoid.powers (algebraMap R S (f i)))).map g.generic)
      infer_instance
    have : IsIso ((restrictedLocalEvaluation S f c i ⋙ scalarExtension (R := R) S).map g) := by
      change IsIso ((scalarExtension (R := R) S).map ((restrictedLocalEvaluation S f c i).map g))
      infer_instance
    have e := inverse_naturality (alphaNaturalIso S f c i).hom g
    change inv ((localizationFunctor (Submonoid.powers (algebraMap R S (f i)))).map g.generic) ≫
        (X.alpha i).toModuleIso.hom = (Y.alpha i).toModuleIso.hom ≫
          inv ((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i))) ⋙
            scalarExtension (R := R) S).map (g.localPiece i)) at e
    rw [← Functor.map_inv, ← Functor.map_inv] at e
    have h := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom e)
      (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S (f i))) Y.generic m)
    simpa only [localizationFunctor, scalarExtension, Functor.comp_map, ModuleCat.hom_comp,
      ModuleCat.hom_ofHom, LinearMap.comp_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearEquiv.toModuleIso_hom,
      LinearMap.coe_restrictScalars, AlgebraTensorModule.coe_lTensor,
      LocalizedModule.mkLinearMap_apply, LocalizedModule.map_mk, LinearEquiv.coe_coe] using! h
  alphaIJ_compatibility i j m := by
    have : ∀ k, IsIso ((restrictedLocalEvaluation S f c k).map g) := fun k ↦ by
      change IsIso ((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f k)))).map
        (g.localPiece k))
      infer_instance
    have : ∀ a b, IsIso
        ((restrictedLocalEvaluation S f c a ⋙ localizationFunctor (cechSub f {b})).map g) :=
      fun a b ↦ by
        change IsIso ((localizationFunctor (cechSub f {b})).map
          ((restrictedLocalEvaluation S f c a).map g))
        infer_instance
    have e := inverse_naturality (alphaIJNaturalIso S f c i j).hom g
    change inv ((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f i))) ⋙
          localizationFunctor (cechSub f {j})).map (g.localPiece i)) ≫
        (X.alphaIJ i j).toModuleIso.hom = (Y.alphaIJ i j).toModuleIso.hom ≫
          inv ((ModuleCat.restrictScalars (algebraMap R (Localization.Away (f j))) ⋙
            localizationFunctor (cechSub f {i})).map (g.localPiece j)) at e
    rw [← Functor.map_inv, ← Functor.map_inv] at e
    have h := congrArg ModuleCat.Hom.hom e
    change (X.alphaIJ i j).toLinearMap.comp
      (localizedMap f {j} ((ModuleCat.restrictScalars
        (algebraMap R (Localization.Away (f i)))).map (inv (g.localPiece i))).hom) =
      (localizedMap f {i} ((ModuleCat.restrictScalars
        (algebraMap R (Localization.Away (f j)))).map (inv (g.localPiece j))).hom).comp
        (Y.alphaIJ i j).toLinearMap at h
    have hh := DFunLike.congr_fun h (LocalizedModule.mkLinearMap (cechSub f {j})
      (restrictFromAway f i (Y.localPiece i)) m)
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, localizedMap_mk,
      ModuleCat.RestrictScalars.map'] using! hh


private theorem isIso_of_components (c : LocalizationComparisons.{u, max u v w} f)
    {X Y : ModuleGlueingDatum.{u, v, w} S f c} (g : X ⟶ Y)
    [IsIso g.generic] [∀ i, IsIso (g.localPiece i)] : IsIso g := by
  refine ⟨⟨inverseGlueingMap S f c g, ?_, ?_⟩⟩
  · apply ModuleGlueingMap.ext
    · exact IsIso.hom_inv_id g.generic
    · funext i
      exact IsIso.hom_inv_id (g.localPiece i)
  · apply ModuleGlueingMap.ext
    · exact IsIso.inv_hom_id g.generic
    · funext i
      exact IsIso.inv_hom_id (g.localPiece i)

private def mapLimitIso {J C D E : Type*} [Category J] [Category C] [Category D] [Category E]
    (F : J ⥤ C) (G : J ⥤ D) (L : C ⥤ E) (K : D ⥤ E)
    [HasLimit F] [HasLimit G] [HasLimit (F ⋙ L)] [HasLimit (G ⋙ K)]
    [PreservesLimit F L] [PreservesLimit G K] (e : F ⋙ L ≅ G ⋙ K) :
    L.obj (limit F) ≅ K.obj (limit G) :=
  preservesLimitIso L F ≪≫ HasLimit.isoOfNatIso e ≪≫ (preservesLimitIso K G).symm

private theorem mapLimitIso_hom_π {J C D E : Type*}
    [Category J] [Category C] [Category D] [Category E]
    (F : J ⥤ C) (G : J ⥤ D) (L : C ⥤ E) (K : D ⥤ E)
    [HasLimit F] [HasLimit G] [HasLimit (F ⋙ L)] [HasLimit (G ⋙ K)]
    [PreservesLimit F L] [PreservesLimit G K] (e : F ⋙ L ≅ G ⋙ K) (j : J) :
    (mapLimitIso F G L K e).hom ≫ K.map (limit.π G j) =
      L.map (limit.π F j) ≫ e.hom.app j := by
  simp [mapLimitIso, Category.assoc]

private theorem iterated_naturality
    (c : LocalizationComparisons.{u, w} f)
    {M N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (a : M →ₗ[R] N) (s t : Finset (Fin r)) :
    (localizedMap f (s ∪ t) a).comp (c.iterated M s t).toLinearMap =
      (c.iterated N s t).toLinearMap.comp (localizedMap f t (localizedMap f s a)) := by
  apply IsLocalizedModule.ext (cechSub f t) (LocalizedModule.mkLinearMap _ _)
    (isUnit_of_localizedEquiv _ (c.iterated N s t))
  apply IsLocalizedModule.ext (cechSub f s) (LocalizedModule.mkLinearMap _ _)
    (isUnit_of_localizedEquiv _ ((c.iterated N t s).trans
      (cechModCongr f (Finset.union_comm t s))))
  ext m
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, iterated_mk, localizedMap_mk]

private theorem iterated_naturality_apply
    (c : LocalizationComparisons.{u, w} f)
    {M N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (a : M →ₗ[R] N) (s t : Finset (Fin r)) (x : cechMod f (cechMod f M s) t) :
    localizedMap f (s ∪ t) a (c.iterated M s t x) =
      c.iterated N s t (localizedMap f t (localizedMap f s a) x) :=
  DFunLike.congr_fun (iterated_naturality f c a s t) x

private theorem iterated_symm_naturality_apply
    (c : LocalizationComparisons.{u, w} f)
    {M N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (a : M →ₗ[R] N) (s t : Finset (Fin r)) (x : cechMod f M (s ∪ t)) :
    localizedMap f t (localizedMap f s a) ((c.iterated M s t).symm x) =
      (c.iterated N s t).symm (localizedMap f (s ∪ t) a x) := by
  apply (c.iterated N s t).injective
  rw [← iterated_naturality_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

private theorem cechModCongr_naturality
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (a : M →ₗ[R] N) {s t : Finset (Fin r)} (h : s = t) (x : cechMod f M s) :
    localizedMap f t a (cechModCongr f h x) = cechModCongr f h (localizedMap f s a x) := by
  subst t
  rfl

private theorem localizedMap_commute
    {M N P Q : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (a : M →ₗ[R] N) (b : P →ₗ[R] Q) (p : M →ₗ[R] P) (q : N →ₗ[R] Q)
    (h : q.comp a = b.comp p) (t : Finset (Fin r)) (x : cechMod f M t) :
    localizedMap f t q (localizedMap f t a x) =
      localizedMap f t b (localizedMap f t p x) := by
  change ((localizedMap f t q).comp (localizedMap f t a)) x =
    ((localizedMap f t b).comp (localizedMap f t p)) x
  rw [← localizedMap_comp, ← localizedMap_comp, h]

private theorem tensorMap_commute
    {M N P Q : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (a : M →ₗ[R] N) (b : P →ₗ[R] Q) (p : M →ₗ[R] P) (q : N →ₗ[R] Q)
    (h : q.comp a = b.comp p) (x : S ⊗[R] M) :
    TensorProduct.map LinearMap.id q (TensorProduct.map LinearMap.id a x) =
      TensorProduct.map LinearMap.id b (TensorProduct.map LinearMap.id p x) := by
  rw [TensorProduct.map_map, TensorProduct.map_map, h]

private theorem tensorMap_localizedMk
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (a : M →ₗ[R] N) (t : Finset (Fin r)) (x : S ⊗[R] M) :
    TensorProduct.map LinearMap.id (localizedMap f t a)
        (TensorProduct.map LinearMap.id (LocalizedModule.mkLinearMap (cechSub f t) M) x) =
      TensorProduct.map LinearMap.id (LocalizedModule.mkLinearMap (cechSub f t) N)
        (TensorProduct.map LinearMap.id a x) :=
  tensorMap_commute S (LocalizedModule.mkLinearMap (cechSub f t) M)
    (LocalizedModule.mkLinearMap (cechSub f t) N) a (localizedMap f t a)
    (LinearMap.ext (localizedMap_mk f t a)) x

private theorem mapLimit_ext {A : Type*} [Category A] {J : Type*} [Category J]
    (D : J ⥤ A) (F : A ⥤ ModuleCat.{w} R) [HasLimit D] [PreservesLimit D F]
    [PreservesLimit (D ⋙ F) (forget (ModuleCat.{w} R))]
    (x y : F.obj (limit D))
    (h : ∀ j, F.map (limit.π D j) x = F.map (limit.π D j) y) : x = y :=
  Concrete.isLimit_ext (D ⋙ F) (isLimitOfPreserves F (limit.isLimit D)) x y h

end

end FormalGlueing


end
