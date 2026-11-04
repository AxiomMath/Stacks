module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.ConnectingMapDeltaFunctor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.ObstructionRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.StalkSectionsPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkOfHigherDirectImage
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.Precomp

/-!
# Restriction of étale cohomology and stalks of base change maps as morphisms of δ-functors

For a morphism `k : Z' ⟶ Z` of schemes over `T`, the pull back maps
`H^n(Z, c⁻¹F) ⟶ H^n(Z', c'⁻¹F)` of étale cohomology, and for a commutative square of schemes and
a geometric point `x` of its upper left corner, the maps `(R^n g_* F)_{f(x)} ⟶ (R^n h_* e⁻¹F)_x`
induced by the base change map of Stacks 0F02, are morphisms of δ-functors in the abelian sheaf
`F` on `T`. This file constructs them, together with the computations of the underived base
change map and of the comparison of iterated inverse images on images of sections under units,
which identify such morphisms in degree zero.

## Main definitions

* `Stacks.EtaleCohomology.etaleCohomologyRestrictionHom`,
  `Stacks.EtaleCohomology.etaleCohomologyRestrictionPrecompHom`: restriction of étale cohomology
  along a morphism over `T`, as a morphism of δ-functors.
* `Stacks.EtaleCohomology.higherBaseChangeStalkHom`: the stalk at a geometric point of the base
  change map on higher direct images, as a morphism of δ-functors.

## Main results

* `Stacks.EtaleCohomology.smallEtaleBaseChangeAb_app_unitApp`: the underived base change map on
  images of sections under the unit.
* `Stacks.EtaleCohomology.smallEtalePullbackAbComp'_sectionsRestrictionAlong_unitApp`: the
  comparison of iterated inverse images on restrictions of images of sections under the unit.

## References

* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
* [Stacks Project, Tag 010R](https://stacks.math.columbia.edu/tag/010R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### Restriction of étale cohomology as a morphism of δ-functors -/

section Restriction

variable {T Z Z' : Scheme.{u}} (c : Z ⟶ T) (c' : Z' ⟶ T) (k : Z' ⟶ Z) (hk : c' = k ≫ c)

/-- **Étale cohomology of the inverse image along `c : Z ⟶ T`**, `F ↦ H^n(Z, c⁻¹F)`, as a
δ-functor in the abelian sheaf `F` on `T`. -/
abbrev etaleCohomologyPullbackDeltaFunctor :
    DeltaFunctor (Sheaf (smallEtaleTopology T) Ab.{u + 1}) Ab.{u + 1} :=
  ModuleSheafCohomology.extDeltaFunctor (smallEtalePullbackAb c)
    (AlgebraicGeometry.smallEtaleConstantSheafInt Z)

/-- **Restriction of étale cohomology along a morphism over `T`**, as a morphism of δ-functors:
for `k : Z' ⟶ Z` with `c' = k ≫ c`, the pull back maps `H^n(Z, c⁻¹F) ⟶ H^n(Z', c'⁻¹F)`. -/
def etaleCohomologyRestrictionHom :
    etaleCohomologyPullbackDeltaFunctor c ⟶ etaleCohomologyPullbackDeltaFunctor c' where
  app n :=
    { app := fun F => AddCommGrpCat.ofHom
        (etaleCohomologyPullback k ((smallEtalePullbackAbComp' k c c' hk).hom.app F) n)
      naturality := fun F F' φ => by
        ext x
        change (etaleCohomologyPullback k ((smallEtalePullbackAbComp' k c c' hk).hom.app F') n)
            (x.comp (Ext.mk₀ ((smallEtalePullbackAb c).map φ)) (add_zero n)) =
          (etaleCohomologyPullback k ((smallEtalePullbackAbComp' k c c' hk).hom.app F) n x).comp
            (Ext.mk₀ ((smallEtalePullbackAb c').map φ)) (add_zero n)
        exact (etaleCohomologyPullback_comp_mk₀_of_comm k _ _ _ _
          ((smallEtalePullbackAbComp' k c c' hk).hom.naturality φ) n x).symm }
  comm {S} hS n := by
    ext x
    change ((etaleCohomologyPullback k ((smallEtalePullbackAbComp' k c c' hk).hom.app S.X₃) n
        x).comp (hS.map_of_exact (smallEtalePullbackAb c')).extClass rfl) =
      etaleCohomologyPullback k ((smallEtalePullbackAbComp' k c c' hk).hom.app S.X₁) (n + 1)
        (x.comp (hS.map_of_exact (smallEtalePullbackAb c)).extClass rfl)
    exact etaleCohomologyPullback_comp_extClass k (hS.map_of_exact (smallEtalePullbackAb c))
      (hS.map_of_exact (smallEtalePullbackAb c')) _ _ _
      ((smallEtalePullbackAbComp' k c c' hk).hom.naturality S.f)
      ((smallEtalePullbackAbComp' k c c' hk).hom.naturality S.g) n x

/-- The component of `etaleCohomologyRestrictionHom` in degree `n` at `F` is the pull back map
`etaleCohomologyPullback` along `k`. -/
theorem etaleCohomologyRestrictionHom_app_app (n : ℕ)
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    ((etaleCohomologyRestrictionHom c c' k hk).app n).app F = AddCommGrpCat.ofHom
      (etaleCohomologyPullback k ((smallEtalePullbackAbComp' k c c' hk).hom.app F) n) :=
  rfl

/-- The component of `etaleCohomologyRestrictionHom` in degree `n` at `F` sends a class `y` to its
pull back `etaleCohomologyPullback` along `k`. -/
theorem etaleCohomologyRestrictionHom_app_app_apply (n : ℕ)
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1})
    (y : Sheaf.H.{u + 1} ((smallEtalePullbackAb c).obj F) n) :
    ((etaleCohomologyRestrictionHom c c' k hk).app n).app F y =
      etaleCohomologyPullback k ((smallEtalePullbackAbComp' k c c' hk).hom.app F) n y :=
  rfl

/-- Restriction along an isomorphism of schemes is an isomorphism. -/
instance isIso_etaleCohomologyRestrictionHom_app_app [IsIso k] (n : ℕ)
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    IsIso (((etaleCohomologyRestrictionHom c c' k hk).app n).app F) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact bijective_etaleCohomologyPullback_of_isIso k _ n

/-- **Restriction of étale cohomology into a precomposed δ-functor.** For `k : Z' ⟶ Z`, an exact
functor `Ψ` and a natural map `ψ : k⁻¹ c⁻¹ ⟶ c'⁻¹ Ψ`, the pull back maps
`H^n(Z, c⁻¹F) ⟶ H^n(Z', c'⁻¹ΨF)` form a morphism of δ-functors. -/
def etaleCohomologyRestrictionPrecompHom {T' : Scheme.{u}}
    (Ψ : Sheaf (smallEtaleTopology T) Ab.{u + 1} ⥤ Sheaf (smallEtaleTopology T') Ab.{u + 1})
    [Ψ.Additive] [PreservesFiniteLimits Ψ] [PreservesFiniteColimits Ψ] (c'' : Z' ⟶ T')
    (ψ : smallEtalePullbackAb c ⋙ smallEtalePullbackAb k ⟶ Ψ ⋙ smallEtalePullbackAb c'') :
    etaleCohomologyPullbackDeltaFunctor c ⟶
      (etaleCohomologyPullbackDeltaFunctor c'').precomp Ψ where
  app n :=
    { app := fun F => AddCommGrpCat.ofHom (etaleCohomologyPullback k (ψ.app F) n)
      naturality := fun F F' φ => by
        ext x
        change (etaleCohomologyPullback k (ψ.app F') n)
            (x.comp (Ext.mk₀ ((smallEtalePullbackAb c).map φ)) (add_zero n)) =
          (etaleCohomologyPullback k (ψ.app F) n x).comp
            (Ext.mk₀ ((smallEtalePullbackAb c'').map (Ψ.map φ))) (add_zero n)
        exact (etaleCohomologyPullback_comp_mk₀_of_comm k _ _ _ _ (ψ.naturality φ) n x).symm }
  comm {S} hS n := by
    ext x
    change ((etaleCohomologyPullback k (ψ.app S.X₃) n x).comp
        ((hS.map_of_exact Ψ).map_of_exact (smallEtalePullbackAb c'')).extClass rfl) =
      etaleCohomologyPullback k (ψ.app S.X₁) (n + 1)
        (x.comp (hS.map_of_exact (smallEtalePullbackAb c)).extClass rfl)
    exact etaleCohomologyPullback_comp_extClass k (hS.map_of_exact (smallEtalePullbackAb c))
      ((hS.map_of_exact Ψ).map_of_exact (smallEtalePullbackAb c'')) _ _ _ (ψ.naturality S.f)
      (ψ.naturality S.g) n x

/-- The component of `etaleCohomologyRestrictionPrecompHom` in degree `n` at `F` sends a class `y`
to its pull back along `k` through `ψ.app F`. -/
theorem etaleCohomologyRestrictionPrecompHom_app_app_apply {T' : Scheme.{u}}
    (Ψ : Sheaf (smallEtaleTopology T) Ab.{u + 1} ⥤ Sheaf (smallEtaleTopology T') Ab.{u + 1})
    [Ψ.Additive] [PreservesFiniteLimits Ψ] [PreservesFiniteColimits Ψ] (c'' : Z' ⟶ T')
    (ψ : smallEtalePullbackAb c ⋙ smallEtalePullbackAb k ⟶ Ψ ⋙ smallEtalePullbackAb c'') (n : ℕ)
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1})
    (y : Sheaf.H.{u + 1} ((smallEtalePullbackAb c).obj F) n) :
    ((etaleCohomologyRestrictionPrecompHom c k Ψ c'' ψ).app n).app F y =
      etaleCohomologyPullback k (ψ.app F) n y :=
  rfl

/-- Restriction along an isomorphism of schemes, with an isomorphism of sheaves, is an
isomorphism. -/
theorem isIso_etaleCohomologyRestrictionPrecompHom_app_app {T' : Scheme.{u}}
    (Ψ : Sheaf (smallEtaleTopology T) Ab.{u + 1} ⥤ Sheaf (smallEtaleTopology T') Ab.{u + 1})
    [Ψ.Additive] [PreservesFiniteLimits Ψ] [PreservesFiniteColimits Ψ] (c'' : Z' ⟶ T')
    (ψ : smallEtalePullbackAb c ⋙ smallEtalePullbackAb k ⟶ Ψ ⋙ smallEtalePullbackAb c'')
    [IsIso k] [IsIso ψ] (n : ℕ) (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    IsIso (((etaleCohomologyRestrictionPrecompHom c k Ψ c'' ψ).app n).app F) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact bijective_etaleCohomologyPullback_of_isIso k _ n

end Restriction

/-! ### The stalk of the base change map as a morphism of δ-functors -/

/-- Pasting a naturality square onto a commutative square. -/
theorem comp_comp_eq_comp_comp_of_comm {C : Type*} [Category* C] {P P' Q Q' R R' : C}
    {a : P ⟶ P'} {i : P ⟶ Q} {i' : P' ⟶ Q'} {c : Q ⟶ Q'} {s : Q ⟶ R} {s' : Q' ⟶ R'}
    {b : R ⟶ R'} (hi : a ≫ i' = i ≫ c) (hs : c ≫ s' = s ≫ b) :
    a ≫ i' ≫ s' = (i ≫ s) ≫ b := by
  rw [← Category.assoc, hi, Category.assoc, hs, Category.assoc]

section BaseChangeStalk

variable {X Y S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T)
  (w : h ≫ f = e ≫ g) {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X)

/-- The stalks of the higher direct images along `g` at `x ≫ f`, as a δ-functor. -/
abbrev higherDirectImageStalkAtDeltaFunctor :
    DeltaFunctor (Sheaf (smallEtaleTopology T) Ab.{u + 1}) Ab.{u + 1} :=
  (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (smallEtalePushforwardAb g)).postcomp (smallEtaleStalkAb (x ≫ f))

/-- The stalks at `x` of the higher direct images along `h` of the inverse images along `e`, as a
δ-functor in the sheaf on `T`. -/
abbrev higherDirectImagePullbackStalkDeltaFunctor :
    DeltaFunctor (Sheaf (smallEtaleTopology T) Ab.{u + 1}) Ab.{u + 1} :=
  ((Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (smallEtalePushforwardAb h)).postcomp (smallEtaleStalkAb x)).precomp (smallEtalePullbackAb e)

/-- The comparison of stalks `(G)_{f(x)} ≅ (f⁻¹ G)_x` is natural in the sheaf `G`. -/
private theorem stalk_map_comp_stalkPullbackAbIso_inv_app
    {A B : Sheaf (smallEtaleTopology S) Ab.{u + 1}} (m : A ⟶ B) :
    (smallEtaleStalkAb (x ≫ f)).map m ≫ (smallEtaleStalkPullbackAbIso f x).inv.app B =
      (smallEtaleStalkPullbackAbIso f x).inv.app A ≫
        (smallEtaleStalkAb x).map ((smallEtalePullbackAb f).map m) :=
  ((smallEtaleStalkPullbackAbIso f x).inv.naturality _).trans
    (congrArg (_ ≫ ·) (Functor.comp_map _ _ _))

/-- **The base change map on stalks commutes with the connecting morphisms.** -/
theorem stalk_higherBaseChangeMapAb_comp_δ
    {S : ShortComplex (Sheaf (smallEtaleTopology T) Ab.{u + 1})}
    (hS : S.ShortExact) (n : ℕ) :
    ((smallEtaleStalkPullbackAbIso f x).inv.app (((smallEtalePushforwardAb g).rightDerived n).obj
        S.X₃) ≫ (smallEtaleStalkAb x).map ((higherBaseChangeMapAb f g h e w n).app S.X₃)) ≫
      (smallEtaleStalkAb x).map ((Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
        (smallEtalePushforwardAb h)).δ (hS.map_of_exact (smallEtalePullbackAb e)) n) =
    (smallEtaleStalkAb (x ≫ f)).map
        ((Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
          (smallEtalePushforwardAb g)).δ hS n) ≫
      (smallEtaleStalkPullbackAbIso f x).inv.app
          (((smallEtalePushforwardAb g).rightDerived (n + 1)).obj S.X₁) ≫
        (smallEtaleStalkAb x).map ((higherBaseChangeMapAb f g h e w (n + 1)).app S.X₁) := by
  have hδ : (higherBaseChangeMapAb f g h e w n).app S.X₃ ≫
      (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
        (smallEtalePushforwardAb h)).δ (hS.map_of_exact (smallEtalePullbackAb e)) n =
      (smallEtalePullbackAb f).map
          ((Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
            (smallEtalePushforwardAb g)).δ hS n) ≫
        (higherBaseChangeMapAb f g h e w (n + 1)).app S.X₁ :=
    ((congrArg (_ ≫ ·) (higherBaseChangeδTarget_eq h e n hS).symm).trans
      (higherBaseChangeMapAb_comm' f g h e w n hS)).trans
        (congrArg (· ≫ _) (higherBaseChangeδSource_eq f g n hS))
  exact (comp_comp_eq_comp_comp_of_comm (stalk_map_comp_stalkPullbackAbIso_inv_app f x _)
    (((smallEtaleStalkAb x).map_comp _ _).symm.trans
      ((congrArg (smallEtaleStalkAb x).map hδ.symm).trans
        ((smallEtaleStalkAb x).map_comp _ _)))).symm

/-- The base change map on stalks is natural in the sheaf. -/
theorem stalk_higherBaseChangeMapAb_naturality (n : ℕ)
    {F F' : Sheaf (smallEtaleTopology T) Ab.{u + 1}} (φ : F ⟶ F') :
    ((smallEtalePushforwardAb g).rightDerived n ⋙ smallEtaleStalkAb (x ≫ f)).map φ ≫
        ((smallEtaleStalkPullbackAbIso f x).inv.app
            (((smallEtalePushforwardAb g).rightDerived n).obj F') ≫
          (smallEtaleStalkAb x).map ((higherBaseChangeMapAb f g h e w n).app F')) =
      ((smallEtaleStalkPullbackAbIso f x).inv.app
            (((smallEtalePushforwardAb g).rightDerived n).obj F) ≫
          (smallEtaleStalkAb x).map ((higherBaseChangeMapAb f g h e w n).app F)) ≫
        (smallEtalePullbackAb e ⋙ (smallEtalePushforwardAb h).rightDerived n ⋙
          smallEtaleStalkAb x).map φ := by
  simp only [Functor.comp_map]
  have hn : (smallEtalePullbackAb f).map (((smallEtalePushforwardAb g).rightDerived n).map φ) ≫
      (higherBaseChangeMapAb f g h e w n).app F' =
      (higherBaseChangeMapAb f g h e w n).app F ≫
        ((smallEtalePushforwardAb h).rightDerived n).map ((smallEtalePullbackAb e).map φ) :=
    (congrArg (· ≫ _) (Functor.comp_map _ _ _).symm).trans
      (((higherBaseChangeMapAb f g h e w n).naturality φ).trans
        (congrArg (_ ≫ ·) (Functor.comp_map _ _ _)))
  exact comp_comp_eq_comp_comp_of_comm (stalk_map_comp_stalkPullbackAbIso_inv_app f x _)
    (((smallEtaleStalkAb x).map_comp _ _).symm.trans
      ((congrArg (smallEtaleStalkAb x).map hn).trans ((smallEtaleStalkAb x).map_comp _ _)))

/-- The base change map on stalks commutes with the connecting morphisms of the two δ-functors. -/
theorem stalk_higherBaseChangeMapAb_comp_deltaFunctor_δ
    {S : ShortComplex (Sheaf (smallEtaleTopology T) Ab.{u + 1})} (hS : S.ShortExact) (n : ℕ) :
    ((smallEtaleStalkPullbackAbIso f x).inv.app (((smallEtalePushforwardAb g).rightDerived n).obj
        S.X₃) ≫ (smallEtaleStalkAb x).map ((higherBaseChangeMapAb f g h e w n).app S.X₃)) ≫
      (higherDirectImagePullbackStalkDeltaFunctor h e x).δ hS n =
    (higherDirectImageStalkAtDeltaFunctor f g x).δ hS n ≫
      ((smallEtaleStalkPullbackAbIso f x).inv.app
          (((smallEtalePushforwardAb g).rightDerived (n + 1)).obj S.X₁) ≫
        (smallEtaleStalkAb x).map ((higherBaseChangeMapAb f g h e w (n + 1)).app S.X₁)) := by
  simp only [DeltaFunctor.precomp_δ, DeltaFunctor.postcomp_δ]
  exact stalk_higherBaseChangeMapAb_comp_δ f g h e w x hS n

/-- **The stalk at `x` of the base change map, as a morphism of δ-functors**: the components are
`(R^n g_* F)_{f(x)} ≅ (f⁻¹ R^n g_* F)_x ⟶ (R^n h_* e⁻¹ F)_x`. -/
def higherBaseChangeStalkHom :
    higherDirectImageStalkAtDeltaFunctor f g x ⟶
      higherDirectImagePullbackStalkDeltaFunctor h e x where
  app n :=
    { app := fun F => (smallEtaleStalkPullbackAbIso f x).inv.app
          (((smallEtalePushforwardAb g).rightDerived n).obj F) ≫
        (smallEtaleStalkAb x).map ((higherBaseChangeMapAb f g h e w n).app F)
      naturality := fun _ _ φ => stalk_higherBaseChangeMapAb_naturality f g h e w x n φ }
  comm hS n := stalk_higherBaseChangeMapAb_comp_deltaFunctor_δ f g h e w x hS n

/-- The component of `higherBaseChangeStalkHom` in degree `n` at `F` is the comparison of stalks
`(R^n g_* F)_{f(x)} ≅ (f⁻¹ R^n g_* F)_x` followed by the stalk at `x` of the base change map. -/
theorem higherBaseChangeStalkHom_app_app (n : ℕ) (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    ((higherBaseChangeStalkHom f g h e w x).app n).app F =
      (smallEtaleStalkPullbackAbIso f x).inv.app
          (((smallEtalePushforwardAb g).rightDerived n).obj F) ≫
        (smallEtaleStalkAb x).map ((higherBaseChangeMapAb f g h e w n).app F) :=
  rfl

end BaseChangeStalk

/-! ### Restriction of sections of inverse images, on units -/

section UnitSections

variable {Z Y T : Scheme.{u}} (c : Z ⟶ Y) (e : Y ⟶ T) (ce : Z ⟶ T) (hce : ce = c ≫ e)
  (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) (U : T.Etale)
  (r : Z ⟶ ((smallEtaleBaseChange e).obj U).left)
  (hr : r ≫ ((smallEtaleBaseChange e).obj U).hom = c)

include hce hr in
/-- If `r ≫ (e⁻¹ U ⟶ Y) = c` and `ce = c ≫ e`, then `r` followed by the projection `e⁻¹ U ⟶ U` and
the structure morphism of `U` is `ce`. -/
theorem comp_fst_hom_eq_of_eq : (r ≫ pullback.fst U.hom e) ≫ U.hom = ce :=
  (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) pullback.condition).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ e) hr).trans hce.symm)))

/-- **The comparison of iterated inverse images on restrictions of units.** The restriction
along `r` of the image under the unit of `e` of a section `σ` of `F` over `U`, followed by the
comparison `c⁻¹ e⁻¹ F ≅ (c ≫ e)⁻¹ F`, is the restriction of `σ` along `r` followed by the
projection to `U`. -/
theorem smallEtalePullbackAbComp'_sectionsRestrictionAlong_unitApp
    (σ : ToType (F.obj.obj (op U))) :
    ((smallEtalePullbackAbComp' c e ce hce).hom.app F).hom.app (op (Scheme.Etale.mk (𝟙 Z)))
        (sectionsRestrictionAlong c ((smallEtalePullbackAb e).obj F) _ r hr
          (smallEtalePullbackAbUnitApp e F U σ)) =
      sectionsRestrictionAlong ce F U (r ≫ pullback.fst U.hom e)
        (comp_fst_hom_eq_of_eq c e ce hce U r hr) σ := by
  change ((smallEtalePullbackAbComp' c e ce hce).hom.app F).hom.app _
      (((smallEtalePullbackAb c).obj ((smallEtalePullbackAb e).obj F)).obj.map
        (smallEtaleBaseChangeLift c _ r hr).op
          (smallEtalePullbackAbUnitApp c ((smallEtalePullbackAb e).obj F) _
            (smallEtalePullbackAbUnitApp e F U σ))) =
    ((smallEtalePullbackAb ce).obj F).obj.map
      (smallEtaleBaseChangeLift ce U (r ≫ pullback.fst U.hom e)
        (comp_fst_hom_eq_of_eq c e ce hce U r hr)).op (smallEtalePullbackAbUnitApp ce F U σ)
  have hnat := ConcreteCategory.congr_hom
    (((smallEtalePullbackAbComp' c e ce hce).hom.app F).hom.naturality
      (smallEtaleBaseChangeLift c _ r hr).op)
    (smallEtalePullbackAbUnitApp c ((smallEtalePullbackAb e).obj F) _
      (smallEtalePullbackAbUnitApp e F U σ))
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hnat
  refine hnat.trans ?_
  let k' : (smallEtaleBaseChange c).obj ((smallEtaleBaseChange e).obj U) ⟶
      (smallEtaleBaseChange ce).obj U :=
    smallEtaleBaseChangeHomMk ce (pullback.fst _ c ≫ pullback.fst U.hom e)
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) pullback.condition).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ e) pullback.condition).trans
          ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hce.symm))))))
  have hk := pullbackSectionsMap_map_unitApp e F c ce hce (𝟙 _) σ k' (by
    rw [smallEtaleBaseChangeHomMk_left_fst]
    exact (congrArg (pullback.fst _ c ≫ ·) (Category.id_comp _)).symm)
  rw [op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply] at hk
  change ((smallEtalePullbackAb ce).obj F).obj.map _
      (pullbackSectionsMap c e ce hce F _ (smallEtalePullbackAbUnitApp e F U σ)) = _
  rw [hk, presheaf_map_map_apply]
  refine map_eq_map_of_left_fst ce F _ _ ?_ _
  refine ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    (smallEtaleBaseChangeHomMk_left_fst ce _ _)).trans ?_)).trans
    ((congrArg (· ≫ pullback.fst U.hom ce) (smallEtaleBaseChangeLift_left ce U _ _)).trans
      (pullback.lift_fst _ _ _)).symm
  refine (Category.assoc _ _ _).symm.trans (congrArg (· ≫ pullback.fst U.hom e) ?_)
  exact (congrArg (· ≫ pullback.fst _ c) (smallEtaleBaseChangeLift_left c _ r hr)).trans
    (pullback.lift_fst _ _ _)

end UnitSections

/-! ### The underived base change map on units -/

section BaseChangeUnits

variable {X Y S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T)
  (w : h ≫ f = e ≫ g)

/-- The inverse of the comparison of direct images along a composite, on sections. -/
theorem smallEtalePushforwardAbComp'_inv_app_hom_app {X' Y' Z' : Scheme.{u}} (a : X' ⟶ Y')
    (b : Y' ⟶ Z') (ab : X' ⟶ Z') (hab : ab = a ≫ b) (M : Sheaf (smallEtaleTopology X') Ab.{u + 1})
    (U : (Z'.Etale)ᵒᵖ) :
    ((smallEtalePushforwardAbComp' a b ab hab).inv.app M).hom.app U =
      M.obj.map (Opposite.op ((smallEtaleBaseChangeComp' a b ab hab).inv.app U.unop)) :=
  Functor.sheafPushforwardContinuousComp'_inv_app_hom_app _ _ _ _ _ M U

/-- The canonical isomorphism `Y ×_X (X ×_S V) ≅ Y ×_T (T ×_S V)` of étale `Y`-schemes attached to
the commutative square, for an étale `S`-scheme `V`. -/
def smallEtaleSquareBaseChangeHom (V : S.Etale) :
    (smallEtaleBaseChange h).obj ((smallEtaleBaseChange f).obj V) ⟶
      (smallEtaleBaseChange e).obj ((smallEtaleBaseChange g).obj V) :=
  (smallEtaleBaseChangeComp' h f (h ≫ f) rfl).inv.app V ≫
    (smallEtaleBaseChangeComp' e g (h ≫ f) w).hom.app V

/-- The square comparison of direct images is, on sections over `V`, restriction along
`Stacks.EtaleCohomology.smallEtaleSquareBaseChangeHom`. -/
theorem smallEtaleSquarePushforwardIso_hom_app_hom_app (M : Sheaf (smallEtaleTopology Y) Ab.{u + 1})
    (V : S.Etale) :
    ((smallEtaleSquarePushforwardIso f g h e w).hom.app M).hom.app (op V) =
      M.obj.map (smallEtaleSquareBaseChangeHom f g h e w V).op := by
  change ((smallEtalePushforwardAbComp' e g (h ≫ f) w).hom.app M).hom.app (op V) ≫
      ((smallEtalePushforwardAbComp' h f (h ≫ f) rfl).inv.app M).hom.app (op V) = _
  rw [smallEtalePushforwardAbComp'_hom_app_hom_app, smallEtalePushforwardAbComp'_inv_app_hom_app]
  exact (M.obj.map_comp _ _).symm

/-- The square isomorphism of base changes is compatible with the projections to `V`. -/
theorem smallEtaleSquareBaseChangeHom_left_fst_fst (V : S.Etale) :
    (smallEtaleSquareBaseChangeHom f g h e w V).left ≫
        pullback.fst ((smallEtaleBaseChange g).obj V).hom e ≫ pullback.fst V.hom g =
      pullback.fst ((smallEtaleBaseChange f).obj V).hom h ≫ pullback.fst V.hom f := by
  have h1 := smallEtaleBaseChangeComp'_fst_fst e g (h ≫ f) w V
  have h2 := smallEtaleBaseChangeComp'_fst_fst h f (h ≫ f) rfl V
  have h3 : ((smallEtaleBaseChangeComp' h f (h ≫ f) rfl).inv.app V).left ≫
      ((smallEtaleBaseChangeComp' h f (h ≫ f) rfl).hom.app V).left = 𝟙 _ :=
    congrArg (fun φ => φ.left) ((smallEtaleBaseChangeComp' h f (h ≫ f) rfl).inv_hom_id_app V)
  change (((smallEtaleBaseChangeComp' h f (h ≫ f) rfl).inv.app V).left ≫
      ((smallEtaleBaseChangeComp' e g (h ≫ f) w).hom.app V).left) ≫ _ = _
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h1).trans ?_)
  refine (congrArg (_ ≫ ·) h2.symm).trans ?_
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h3).trans (Category.id_comp _))

/-- **The underived base change map on units.** The base change map
`f⁻¹ g_* F ⟶ h_* e⁻¹ F` carries the image under the unit of `f` of a section `σ` of `g_* F` over
`V` to the restriction of the image of `σ` under the unit of `e` along the square isomorphism of
base changes. -/
theorem smallEtaleBaseChangeAb_app_unitApp (F : Sheaf (smallEtaleTopology T) Ab.{u + 1})
    (V : S.Etale) (σ : ToType (F.obj.obj (op ((smallEtaleBaseChange g).obj V)))) :
    ((smallEtaleBaseChangeAb f g h e w).app F).hom.app (op ((smallEtaleBaseChange f).obj V))
        (smallEtalePullbackAbUnitApp f ((smallEtalePushforwardAb g).obj F) V σ) =
      ((smallEtalePullbackAb e).obj F).obj.map (smallEtaleSquareBaseChangeHom f g h e w V).op
        (smallEtalePullbackAbUnitApp e F ((smallEtaleBaseChange g).obj V) σ) := by
  have hm : (smallEtaleBaseChangeAb f g h e w).app F =
      ((smallEtaleAdjunctionAb f).homEquiv _ _).symm
        ((smallEtalePushforwardAb g).map ((smallEtaleAdjunctionAb e).unit.app F) ≫
          (smallEtaleSquarePushforwardIso f g h e w).hom.app ((smallEtalePullbackAb e).obj F)) := by
    refine (smallEtaleBaseChangeAb_app_eq f g h e w F).trans ?_
    refine Eq.trans ?_ ((smallEtaleAdjunctionAb f).homEquiv_counit _ _ _).symm
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ _) ((smallEtalePullbackAb f).map_comp _ _).symm)
  have key : (smallEtaleAdjunctionAb f).unit.app ((smallEtalePushforwardAb g).obj F) ≫
      (smallEtalePushforwardAb f).map ((smallEtaleBaseChangeAb f g h e w).app F) =
    (smallEtalePushforwardAb g).map ((smallEtaleAdjunctionAb e).unit.app F) ≫
      (smallEtaleSquarePushforwardIso f g h e w).hom.app ((smallEtalePullbackAb e).obj F) := by
    rw [hm]
    exact ((smallEtaleAdjunctionAb f).homEquiv_unit _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  have := ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.app (op V)) key) σ
  change ((smallEtaleBaseChangeAb f g h e w).app F).hom.app _
      (smallEtalePullbackAbUnitApp f ((smallEtalePushforwardAb g).obj F) V σ) =
    ((smallEtaleSquarePushforwardIso f g h e w).hom.app ((smallEtalePullbackAb e).obj F)).hom.app
      (op V) (smallEtalePullbackAbUnitApp e F ((smallEtaleBaseChange g).obj V) σ) at this
  refine this.trans ?_
  rw [smallEtaleSquarePushforwardIso_hom_app_hom_app]
  rfl

end BaseChangeUnits

end Stacks.EtaleCohomology
