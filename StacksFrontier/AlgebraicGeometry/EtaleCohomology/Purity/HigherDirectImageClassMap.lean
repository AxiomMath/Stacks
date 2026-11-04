module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.HigherDirectImageSliceAction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom

/-!
# The map `𝓗om_Λ(F, G) ⟶ R^q g_*(g⁻¹ G)`, `α ↦ α_* s`

Let `g : X ⟶ U` be a morphism of schemes, `F`, `G` sheaves of `Λ`-modules on `U_étale` and `s` a
global section of `R^q g_*(g⁻¹ F)` (on underlying abelian sheaves). A section of the internal hom
`𝓗om_Λ(F, G)` (`Stacks.ConstantSheaf.moduleSheafHom`) over an étale `V ⟶ U` is a morphism
`α : F|_V ⟶ G|_V`; the étale-local action of `R^q g_* ∘ g⁻¹`
(`Stacks.EtaleCohomology.higherDirectImageInverseImageSectionMap`) sends the restriction `s|_V` to
a section `α_* s` of `R^q g_*(g⁻¹ G)` over `V`. Since the action commutes with restriction, this
is a morphism of abelian sheaves (`Stacks.EtaleCohomology.higherDirectImageClassMap`). It sends the
identity to `s` (`Stacks.EtaleCohomology.higherDirectImageClassMap_app_id`), is natural in `G`
(`Stacks.EtaleCohomology.moduleSheafHomMap_comp_higherDirectImageClassMap`), and precomposition
with `p : F' ⟶ F` shifts the class to `p_* s`
(`Stacks.EtaleCohomology.moduleSheafHomMap_comp_higherDirectImageClassMap_of_comp`).

For `g = j` the inclusion of the complement of a divisor, `F = μ_N`, `q = 1` and `s` the
fundamental class of the divisor, this is the canonical map `𝓗om(μ_N, H) ⟶ R¹ j_*(j⁻¹ H)` of the
tower form of purity ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main definitions

* `Stacks.EtaleCohomology.higherDirectImageClassMap`.

## Main results

* `Stacks.EtaleCohomology.higherDirectImageClassMap_app_id`.
* `Stacks.EtaleCohomology.moduleSheafHomMap_comp_higherDirectImageClassMap`.
* `Stacks.EtaleCohomology.moduleSheafHomMap_comp_higherDirectImageClassMap_of_comp`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

universe u

namespace Stacks.EtaleCohomology

variable {X U : Scheme.{u}} (g : X ⟶ U) (q : ℕ) (Λ : Type*) [CommRing Λ]
  {F G : Sheaf (smallEtaleTopology U) (ModuleCat.{u + 1} Λ)}

/-- The underlying abelian sheaf of a sheaf of `Λ`-modules. -/
abbrev smallEtaleModuleSheafForgetAb (F : Sheaf (smallEtaleTopology U) (ModuleCat.{u + 1} Λ)) :
    Sheaf (smallEtaleTopology U) Ab.{u + 1} :=
  (sheafCompose (smallEtaleTopology U) (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F

variable {Λ} in
/-- A section of `𝓗om_Λ(F, G)` over `V`, as a morphism between the restrictions to the slice over
`V` of the underlying abelian sheaves. -/
def moduleSheafHomForgetSliceHom (V : U.Etale)
    (α : ((smallEtaleTopology U).overPullback (ModuleCat.{u + 1} Λ) V).obj F ⟶
      ((smallEtaleTopology U).overPullback (ModuleCat.{u + 1} Λ) V).obj G) :
    ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj (smallEtaleModuleSheafForgetAb Λ F) ⟶
      ((smallEtaleTopology U).overPullback Ab.{u + 1} V).obj (smallEtaleModuleSheafForgetAb Λ G) :=
  (sheafCompose ((smallEtaleTopology U).over V)
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map α

/-- `moduleSheafHomForgetSliceHom` is additive. -/
theorem moduleSheafHomForgetSliceHom_add (V : U.Etale)
    (α β : ((smallEtaleTopology U).overPullback (ModuleCat.{u + 1} Λ) V).obj F ⟶
      ((smallEtaleTopology U).overPullback (ModuleCat.{u + 1} Λ) V).obj G) :
    moduleSheafHomForgetSliceHom V (α + β) =
      moduleSheafHomForgetSliceHom V α + moduleSheafHomForgetSliceHom V β := by
  apply Sheaf.hom_ext
  ext P : 2
  rfl

variable {Λ}
variable {t : U.Etale} (ht : IsTerminal t)
  (s : ToType ((((smallEtalePushforwardAb g).rightDerived q).obj
    ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb Λ F))).obj.obj (op t)))

/-- **The map `𝓗om_Λ(F, G) ⟶ R^q g_*(g⁻¹ G)`, `α ↦ α_* s`**, of a global section `s` of
`R^q g_*(g⁻¹ F)`, on underlying abelian sheaves. -/
def higherDirectImageClassMap :
    smallEtaleModuleSheafForgetAb Λ
        (Stacks.ConstantSheaf.moduleSheafHom (smallEtaleTopology U) Λ F G) ⟶
      ((smallEtalePushforwardAb g).rightDerived q).obj
        ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb Λ G)) :=
  ⟨{ app := fun V => AddCommGrpCat.ofHom (AddMonoidHom.mk'
      (fun α => higherDirectImageInverseImageSectionMap g q V.unop
          (moduleSheafHomForgetSliceHom V.unop α)
          ((((smallEtalePushforwardAb g).rightDerived q).obj
            ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb Λ F))).obj.map
              (ht.from V.unop).op s))
      (fun α β =>
        (congrArg (fun φ => ConcreteCategory.hom
            (higherDirectImageInverseImageSectionMap g q V.unop φ)
            ((((smallEtalePushforwardAb g).rightDerived q).obj
              ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb Λ F))).obj.map
                (ht.from V.unop).op s))
          (moduleSheafHomForgetSliceHom_add Λ (F := F) (G := G) V.unop α β)).trans
        (congrArg (fun φ : (((smallEtalePushforwardAb g).rightDerived q).obj
              ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb Λ F))).obj.obj
                (op V.unop) ⟶
            (((smallEtalePushforwardAb g).rightDerived q).obj
              ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb Λ G))).obj.obj
                (op V.unop) =>
            ConcreteCategory.hom φ
            ((((smallEtalePushforwardAb g).rightDerived q).obj
              ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb Λ F))).obj.map
                (ht.from V.unop).op s))
          (higherDirectImageInverseImageSectionMap_add g q V.unop
            (moduleSheafHomForgetSliceHom V.unop α) (moduleSheafHomForgetSliceHom V.unop β)))))
     naturality := fun V W f => by
       refine AddCommGrpCat.ext (fun α => ?_)
       have hs : (((smallEtalePushforwardAb g).rightDerived q).obj
             ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb Λ F))).obj.map
               (ht.from W.unop).op s =
           (((smallEtalePushforwardAb g).rightDerived q).obj
             ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb Λ F))).obj.map f
             ((((smallEtalePushforwardAb g).rightDerived q).obj
               ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb Λ F))).obj.map
                 (ht.from V.unop).op s) := by
         have hop : (ht.from W.unop).op = (ht.from V.unop).op ≫ f :=
           Quiver.Hom.unop_inj (ht.hom_ext _ _)
         rw [hop, Functor.map_comp, ConcreteCategory.comp_apply]
       have hr := congrArg (fun φ : (((smallEtalePushforwardAb g).rightDerived q).obj
             ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb Λ F))).obj.obj
               (op V.unop) ⟶
           (((smallEtalePushforwardAb g).rightDerived q).obj
             ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb Λ G))).obj.obj
               (op W.unop) =>
           ConcreteCategory.hom φ
           ((((smallEtalePushforwardAb g).rightDerived q).obj
             ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb Λ F))).obj.map
               (ht.from V.unop).op s))
         (higherDirectImageInverseImageSectionMap_restrict g q f.unop
           (moduleSheafHomForgetSliceHom V.unop α))
       simp only [ConcreteCategory.comp_apply] at hr
       change higherDirectImageInverseImageSectionMap g q W.unop
           (moduleSheafHomForgetSliceHom W.unop
             ((smallEtaleTopology U).overMapPullback (ModuleCat.{u + 1} Λ) f.unop |>.map α)) _ = _
       rw [hs]
       exact hr }⟩

/-- `moduleSheafHomForgetSliceHom` is compatible with pre- and postcomposition. -/
private theorem moduleSheafHomForgetSliceHom_comp_map
    {F' G' : Sheaf (smallEtaleTopology U) (ModuleCat.{u + 1} Λ)} (V : U.Etale) (p : F' ⟶ F)
    (β : ((smallEtaleTopology U).overPullback (ModuleCat.{u + 1} Λ) V).obj F ⟶
      ((smallEtaleTopology U).overPullback (ModuleCat.{u + 1} Λ) V).obj G) (w : G ⟶ G') :
    moduleSheafHomForgetSliceHom V
      (((smallEtaleTopology U).overPullback (ModuleCat.{u + 1} Λ) V).map p ≫ β ≫
        ((smallEtaleTopology U).overPullback (ModuleCat.{u + 1} Λ) V).map w) =
    ((smallEtaleTopology U).overPullback Ab.{u + 1} V).map
        ((sheafCompose (smallEtaleTopology U)
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map p) ≫
      moduleSheafHomForgetSliceHom V β ≫
      ((smallEtaleTopology U).overPullback Ab.{u + 1} V).map
        ((sheafCompose (smallEtaleTopology U)
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map w) := by
  simp only [moduleSheafHomForgetSliceHom, Functor.map_comp]
  rfl

/-- The class map on sections over `V`. -/
theorem higherDirectImageClassMap_app_apply (V : U.Etale)
    (α : ((smallEtaleTopology U).overPullback (ModuleCat.{u + 1} Λ) V).obj F ⟶
      ((smallEtaleTopology U).overPullback (ModuleCat.{u + 1} Λ) V).obj G) :
    (higherDirectImageClassMap g q ht s).hom.app (op V) α =
      higherDirectImageInverseImageSectionMap g q V (moduleSheafHomForgetSliceHom V α)
        ((((smallEtalePushforwardAb g).rightDerived q).obj
          ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb Λ F))).obj.map
            (ht.from V).op s) := rfl

/-- **The class map sends the identity to the class**: `id_* s = s`. -/
theorem higherDirectImageClassMap_app_id (V : U.Etale) :
    (higherDirectImageClassMap (G := F) g q ht s).hom.app (op V)
        (𝟙 (((smallEtaleTopology U).overPullback (ModuleCat.{u + 1} Λ) V).obj F)) =
      (((smallEtalePushforwardAb g).rightDerived q).obj
          ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb Λ F))).obj.map
            (ht.from V).op s := by
  rw [higherDirectImageClassMap_app_apply]
  have h1 : moduleSheafHomForgetSliceHom V
      (𝟙 (((smallEtaleTopology U).overPullback (ModuleCat.{u + 1} Λ) V).obj F)) = 𝟙 _ :=
    (sheafCompose ((smallEtaleTopology U).over V)
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map_id _
  rw [h1, higherDirectImageInverseImageSectionMap_id]
  rfl

/-- **The class map is natural in the target**: postcomposing with `w : G ⟶ G'` and then
taking `α ↦ α_* s` is `R^q g_* g⁻¹ w` after `α ↦ α_* s`. -/
theorem moduleSheafHomMap_comp_higherDirectImageClassMap {G' : Sheaf (smallEtaleTopology U)
    (ModuleCat.{u + 1} Λ)} (w : G ⟶ G') :
    (sheafCompose (smallEtaleTopology U) (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
        (Stacks.ConstantSheaf.moduleSheafHomMap (smallEtaleTopology U) Λ (𝟙 F) w) ≫
      higherDirectImageClassMap g q ht s =
    higherDirectImageClassMap g q ht s ≫ ((smallEtalePushforwardAb g).rightDerived q).map
      ((smallEtalePullbackAb g).map ((sheafCompose (smallEtaleTopology U)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map w)) := by
  apply Sheaf.hom_ext
  ext V : 2
  refine AddCommGrpCat.ext (fun α => ?_)
  have h1 := moduleSheafHomForgetSliceHom_comp_map V.unop (𝟙 F) α w
  simp only [CategoryTheory.Functor.map_id, Category.id_comp] at h1
  have h2 := congrArg (fun φ => higherDirectImageInverseImageSectionMap g q V.unop φ) h1
  simp only [higherDirectImageInverseImageSectionMap_comp_map] at h2
  exact ConcreteCategory.congr_hom h2 ((((smallEtalePushforwardAb g).rightDerived q).obj
    ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb Λ F))).obj.map
      (ht.from V.unop).op s)

/-- **Precomposition shifts the class**: precomposing with `p : F' ⟶ F` and then taking
`α ↦ α_* s'` is `α ↦ α_* (p_* s')`. -/
theorem moduleSheafHomMap_comp_higherDirectImageClassMap_of_comp {F' : Sheaf (smallEtaleTopology U)
    (ModuleCat.{u + 1} Λ)} (p : F' ⟶ F)
    (s' : ToType ((((smallEtalePushforwardAb g).rightDerived q).obj
      ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb Λ F'))).obj.obj (op t))) :
    (sheafCompose (smallEtaleTopology U) (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
        (Stacks.ConstantSheaf.moduleSheafHomMap (smallEtaleTopology U) Λ p (𝟙 G)) ≫
      higherDirectImageClassMap g q ht s' =
    higherDirectImageClassMap g q ht
      ((((smallEtalePushforwardAb g).rightDerived q).map ((smallEtalePullbackAb g).map
        ((sheafCompose (smallEtaleTopology U)
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map p))).hom.app (op t) s') := by
  apply Sheaf.hom_ext
  ext V : 2
  refine AddCommGrpCat.ext (fun α => ?_)
  have h1 := moduleSheafHomForgetSliceHom_comp_map V.unop p α (𝟙 G)
  simp only [CategoryTheory.Functor.map_id, Category.comp_id] at h1
  have h2 := congrArg (fun φ => higherDirectImageInverseImageSectionMap g q V.unop φ) h1
  simp only [higherDirectImageInverseImageSectionMap_map_comp] at h2
  have hnat := NatTrans.naturality_apply (((smallEtalePushforwardAb g).rightDerived q).map
    ((smallEtalePullbackAb g).map ((sheafCompose (smallEtaleTopology U)
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map p))).hom (ht.from V.unop).op s'
  refine (ConcreteCategory.congr_hom h2 ((((smallEtalePushforwardAb g).rightDerived q).obj
    ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb Λ F'))).obj.map
      (ht.from V.unop).op s')).trans ?_
  rw [ConcreteCategory.comp_apply, hnat]
  rfl

end Stacks.EtaleCohomology

end
