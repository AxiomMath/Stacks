module

public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisRightDerived
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId
public import StacksFrontier.CategoryTheory.Adjunction.CompUnitComparison
public import StacksFrontier.CategoryTheory.Adjunction.ReflectiveUnitExt
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.CohomologyOverAnObject

/-!
# Restriction maps on the cohomology of modules on algebraic spaces

Let `j : Y ⟶ X` be an étale morphism of algebraic spaces over a scheme `S`.  For a sheaf of
`𝒪_X`-modules `F`, restriction of sections `Γ(X, F) ⟶ Γ(Y, F|_Y)` is global sections applied to
the unit `F ⟶ j_*(F|_Y)` of the adjunction of Stacks 03LU, read through
`Γ(X, j_* -) = Γ(Y, -)`.  Deriving it gives the restriction maps
`Hⁿ(X, F) ⟶ Hⁿ(Y, F|_Y)` on cohomology, the cohomology of
`AlgebraicGeometry.Space.globalSectionsAb`, global sections valued in abelian groups.

Facts about their surjectivity:

* restriction along a composite `k = f ≫ g` is restriction along `g` followed by restriction
  along `f`, so surjectivity in a fixed degree is stable under composition;
* restriction along an isomorphism is invertible;
* for an elementary distinguished square `(U ⊆ X, j_V : V ⟶ X)` whose étale part is an open
  immersion, the map `j_{V,*}F|_V ⟶ j_{P,*}F|_P` of the Mayer–Vietoris sequence of Stacks 08GW
  is restriction along `P = U ×_X V ⟶ V`, so it is onto on `Hⁿ` as soon as that restriction is;
* across any elementary distinguished square, `Hⁿ(X, F) ⟶ Hⁿ(U, F|_U)` is onto as soon as the
  map `Hⁿ(V, F|_V) ⟶ Hⁿ(P, F|_P)` of the Mayer–Vietoris sequence is.

## Main definitions

* `AlgebraicGeometry.Space.globalSectionsAbRestriction`: the restriction
  `Γ(X, -) ⟶ Γ(X, j_*(-)|_Y)` as a morphism of functors.
* `AlgebraicGeometry.Space.cohomologyRestriction`: the restriction map
  `Hⁿ(X, F) ⟶ Hⁿ(Y, F|_Y)`.

## Main results

* `AlgebraicGeometry.Space.globalSectionsAbRestriction_comp`: restriction along a composite.
* `AlgebraicGeometry.Space.epi_rightDerived_globalSectionsAbRestriction_comp`: surjectivity of
  restriction on `Hⁿ` is stable under composition.
* `AlgebraicGeometry.Space.isIso_etaleModulePullbackAdjunction_unit_of_isIso`: restriction of
  modules along an isomorphism has invertible unit.
* `AlgebraicGeometry.Space.epi_rightDerived_globalSectionsAbRestriction_edsOpenHom_of_epi`:
  Mayer–Vietoris surjectivity for an elementary distinguished square.
* `AlgebraicGeometry.Space.epi_rightDerived_whiskerRight_edsEtaleComparison_of_epi`: the
  Mayer–Vietoris map out of an open étale part is a restriction.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 08GW](https://stacks.math.columbia.edu/tag/08GW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback
  hasInjectiveResolutions_modules enoughInjectives_modules
  smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The right derived transformation of an invertible natural transformation is invertible at
every object. -/
theorem isIso_rightDerived_app_of_isIso {A₀ B₀ : Type*} [Category A₀] [Category B₀] [Abelian A₀]
    [HasInjectiveResolutions A₀] [Abelian B₀] {F G : A₀ ⥤ B₀} [F.Additive] [G.Additive]
    (α : F ⟶ G) [IsIso α] (n : ℕ) (X : A₀) : IsIso ((NatTrans.rightDerived α n).app X) :=
  ⟨⟨(NatTrans.rightDerived (inv α) n).app X, by
    rw [← NatTrans.comp_app, ← NatTrans.rightDerived_comp, IsIso.hom_inv_id,
      NatTrans.rightDerived_id, NatTrans.id_app], by
    rw [← NatTrans.comp_app, ← NatTrans.rightDerived_comp, IsIso.inv_hom_id,
      NatTrans.rightDerived_id, NatTrans.id_app]⟩⟩

/-- A morphism which becomes an epimorphism after composing with an isomorphism is an
epimorphism. -/
theorem epi_of_epi_comp_isIso {C₀ : Type*} [Category C₀] {X₀ Y₀ Z₀ : C₀} (f : X₀ ⟶ Y₀)
    (g : Y₀ ⟶ Z₀) [IsIso g] (h : Epi (f ≫ g)) : Epi f := by
  rw [← Category.comp_id f, ← IsIso.hom_inv_id g, ← Category.assoc]
  infer_instance

section Restriction

variable {Y X : AlgebraicSpaces B S hS} (j : Y ⟶ X) (hj : IsEtale B S hS j.hom)

/-- Global sections of the direct image of the restriction is an additive functor. -/
instance additive_restrictPushGlobalSectionsAb :
    ((etaleModulePullback.{u, u} B S hS j hj ⋙ modulePushforward B S hS j) ⋙
      globalSectionsAb B S hS X).Additive :=
  inferInstance

/-- For `j : Y ⟶ X` étale, the morphism `Γ(X, F) ⟶ Γ(X, j_*(F|_Y))` obtained by applying global
sections to the unit of the adjunction `(-)|_Y ⊣ j_*` of Stacks 03LU. -/
def globalSectionsAbRestriction :
    globalSectionsAb B S hS X ⟶
      (etaleModulePullback.{u, u} B S hS j hj ⋙ modulePushforward B S hS j) ⋙
        globalSectionsAb B S hS X :=
  Functor.whiskerRight (etaleModulePullbackAdjunction B S hS j hj).unit
    (globalSectionsAb B S hS X)

/-- The restriction map `Hⁿ(X, F) ⟶ Hⁿ(Y, F|_Y)` along an étale morphism `j : Y ⟶ X`: the
right derived transformation of the restriction of global sections, read through
`Rⁿ(Γ(X, j_*(-)|_Y))(F) ≅ Hⁿ(Y, F|_Y)`. -/
def cohomologyRestriction (F : Modules.{u, u} B S hS X.1 X.2) (n : ℕ) :
    ((globalSectionsAb B S hS X).rightDerived n).obj F ⟶
      ((globalSectionsAb B S hS Y).rightDerived n).obj
        ((etaleModulePullback.{u, u} B S hS j hj).obj F) :=
  (NatTrans.rightDerived (globalSectionsAbRestriction B S hS j hj) n).app F ≫
    (rightDerivedGlobalSectionsAbRestrictPushIso B S hS j hj F n).hom

/-- The restriction map on `Hⁿ` is onto exactly when the right derived transformation of the
restriction of global sections is. -/
theorem epi_cohomologyRestriction_iff (F : Modules.{u, u} B S hS X.1 X.2) (n : ℕ) :
    Epi (cohomologyRestriction B S hS j hj F n) ↔
      Epi ((NatTrans.rightDerived (globalSectionsAbRestriction B S hS j hj) n).app F) := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ by dsimp only [cohomologyRestriction]; infer_instance⟩
  rw [show (NatTrans.rightDerived (globalSectionsAbRestriction B S hS j hj) n).app F =
      cohomologyRestriction B S hS j hj F n ≫
        (rightDerivedGlobalSectionsAbRestrictPushIso B S hS j hj F n).inv by
    simp [cohomologyRestriction]]
  infer_instance

/-- If the cohomology of the restriction vanishes in degree `n`, the restriction map of global
sections is onto on `Rⁿ`. -/
theorem epi_rightDerived_globalSectionsAbRestriction_of_isZero
    (F : Modules.{u, u} B S hS X.1 X.2) (n : ℕ)
    (h : IsZero (((globalSectionsAb B S hS Y).rightDerived n).obj
      ((etaleModulePullback.{u, u} B S hS j hj).obj F))) :
    Epi ((NatTrans.rightDerived (globalSectionsAbRestriction B S hS j hj) n).app F) :=
  ⟨fun _ _ _ => (h.of_iso (rightDerivedGlobalSectionsAbRestrictPushIso B S hS j hj F n)).eq_of_src
    _ _⟩

end Restriction

/-- Restriction along `k = f ≫ g` inverts a morphism which restriction along `g` inverts. -/
private theorem isIso_map_etaleModulePullback_of_isIso_map_comp {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : IsEtale B S hS f.hom) (hg : IsEtale B S hS g.hom)
    {k : X ⟶ Z} (hk : f ≫ g = k) (hk' : IsEtale B S hS k.hom) {M N : Modules.{u, u} B S hS Z.1 Z.2}
    (φ : M ⟶ N) (h : IsIso ((etaleModulePullback.{u, u} B S hS g hg).map φ)) :
    IsIso ((etaleModulePullback.{u, u} B S hS k hk').map φ) :=
  (NatIso.isIso_map_iff (etaleModulePullbackFactorIso B S hS f g hf hg hk hk') φ).1
    (inferInstanceAs (IsIso ((etaleModulePullback.{u, u} B S hS f hf).map
      ((etaleModulePullback.{u, u} B S hS g hg).map φ))))

/-! ### Restriction along an isomorphism -/

section Iso

variable {Y X : AlgebraicSpaces B S hS}

/-- Restriction of modules along an open immersion has invertible counit, as a natural
transformation. -/
theorem isIso_etaleModulePullbackAdjunction_counit_of_isOpenImmersion (e : Y ⟶ X)
    (he : IsEtale B S hS e.hom) (hopen : IsOpenImmersion B S hS e.hom) :
    IsIso (etaleModulePullbackAdjunction B S hS e he).counit :=
  have (G : Modules.{u, u} B S hS Y.1 Y.2) :
      IsIso ((etaleModulePullbackAdjunction B S hS e he).counit.app G) :=
    isIso_etaleModulePullbackAdjunction_counit B S hS e hopen G
  NatIso.isIso_of_isIso_app _

/-- Restriction of modules along the identity reflects isomorphisms. -/
theorem isIso_of_isIso_map_etaleModulePullback_id (hid : IsEtale B S hS (𝟙 X.1))
    {M N : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ N)
    (h : IsIso ((etaleModulePullback.{u, u} B S hS (𝟙 X) hid).map φ)) : IsIso φ := by
  have h3 : IsIso ((modulePullback B S hS (𝟙 X)).map φ) :=
    (NatIso.isIso_map_iff (modulePullbackIsoEtaleModulePullback B S hS (𝟙 X) hid) φ).2 h
  exact isIso_of_reflects_iso φ (modulePullback B S hS (𝟙 X))

variable (e : Y ⟶ X) [IsIso e] (he : IsEtale B S hS e.hom)

/-- Restriction of modules along an isomorphism `e`, followed by restriction along its inverse,
inverts what restriction along the identity inverts. -/
theorem isIso_map_etaleModulePullback_id_of_isIso (hinv : IsEtale B S hS (inv e).hom)
    (hid : IsEtale B S hS (𝟙 X.1)) {M N : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ N)
    (hφ : IsIso ((etaleModulePullback.{u, u} B S hS e he).map φ)) :
    IsIso ((etaleModulePullback.{u, u} B S hS (𝟙 X) hid).map φ) :=
  isIso_map_etaleModulePullback_of_isIso_map_comp B S hS (inv e) e hinv he (IsIso.inv_hom_id e)
    hid φ hφ

/-- Restriction of modules along an isomorphism of algebraic spaces has invertible unit. -/
theorem isIso_etaleModulePullbackAdjunction_unit_of_isIso :
    IsIso (etaleModulePullbackAdjunction B S hS e he).unit := by
  have hhom : IsIso e.hom := (ObjectProperty.isIso_hom_iff e).2 inferInstance
  have hinvhom : IsIso (inv e).hom := (ObjectProperty.isIso_hom_iff (inv e)).2 inferInstance
  have := isIso_etaleModulePullbackAdjunction_counit_of_isOpenImmersion B S hS e he
    (isOpenImmersion_of_isIso B S hS e.hom)
  have h (M : Modules.{u, u} B S hS X.1 X.2) :
      IsIso ((etaleModulePullbackAdjunction B S hS e he).unit.app M) :=
    isIso_of_isIso_map_etaleModulePullback_id B S hS (isEtale_of_isIso B S hS _) _
      (isIso_map_etaleModulePullback_id_of_isIso B S hS e he (isEtale_of_isIso B S hS _) _ _
        (Adjunction.isIso_map_unit_app_of_isIso_counit _ M))
  exact NatIso.isIso_of_isIso_app _

/-- Restriction of cohomology along an isomorphism of algebraic spaces is invertible, at the
level of the right derived transformation of the restriction of global sections. -/
theorem isIso_rightDerived_globalSectionsAbRestriction_of_isIso
    (M : Modules.{u, u} B S hS X.1 X.2) (n : ℕ) :
    IsIso ((NatTrans.rightDerived (globalSectionsAbRestriction B S hS e he) n).app M) := by
  have := isIso_etaleModulePullbackAdjunction_unit_of_isIso B S hS e he
  have := modulePushforward_additive B S hS e
  have : IsIso (globalSectionsAbRestriction B S hS e he) := by
    dsimp only [globalSectionsAbRestriction]
    infer_instance
  exact isIso_rightDerived_app_of_isIso _ n M

end Iso

/-! ### Restriction along a composite -/

section Comp

variable {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : IsEtale B S hS f.hom)
  (hg : IsEtale B S hS g.hom) {k : X ⟶ Z} (hk : f ≫ g = k) (hk' : IsEtale B S hS k.hom)

/-- For a factorization `k = f ≫ g` of étale morphisms, the
unit `M ⟶ k_*(M|_X)` is the unit `M ⟶ g_*(M|_Y)`, followed by `g_*` of the unit
`M|_Y ⟶ f_*((M|_Y)|_X)`, followed by the isomorphism `(M|_Y)|_X ≅ M|_X` together with its
conjugate on direct images. -/
theorem etaleModulePullbackAdjunction_unit_app_comp (M : Modules.{u, u} B S hS Z.1 Z.2) :
    (etaleModulePullbackAdjunction B S hS k hk').unit.app M =
      (etaleModulePullbackAdjunction B S hS g hg).unit.app M ≫
        (modulePushforward B S hS g).map ((etaleModulePullbackAdjunction B S hS f hf).unit.app
          ((etaleModulePullback.{u, u} B S hS g hg).obj M)) ≫
        (Adjunction.compUnitComparisonIso
          (etaleModulePullbackAdjunction B S hS g hg) (etaleModulePullbackAdjunction B S hS f hf)
          (etaleModulePullbackAdjunction B S hS k hk')
          (etaleModulePullbackFactorIso B S hS f g hf hg hk hk')).hom.app M :=
  Adjunction.unit_app_eq_comp_compUnitComparisonIso _ _ _ _ M

/-- For a factorization `k = f ≫ g` of étale morphisms, the
restriction of global sections along `k` is the restriction along `g`, followed by the
restriction along `f` read on the direct image along `g`, followed by the isomorphism
`(F|_Y)|_X ≅ F|_X` together with its conjugate on direct images. -/
theorem globalSectionsAbRestriction_comp :
    globalSectionsAbRestriction B S hS k hk' =
      globalSectionsAbRestriction B S hS g hg ≫
        Functor.whiskerRight (Functor.whiskerLeft (etaleModulePullback.{u, u} B S hS g hg)
          (Functor.whiskerRight (etaleModulePullbackAdjunction B S hS f hf).unit
            (modulePushforward B S hS g))) (globalSectionsAb B S hS Z) ≫
        Functor.whiskerRight (Adjunction.compUnitComparisonIso
          (etaleModulePullbackAdjunction B S hS g hg) (etaleModulePullbackAdjunction B S hS f hf)
          (etaleModulePullbackAdjunction B S hS k hk')
          (etaleModulePullbackFactorIso B S hS f g hf hg hk hk')).hom
          (globalSectionsAb B S hS Z) := by
  have h : globalSectionsAbRestriction B S hS k hk' =
      Functor.whiskerRight ((etaleModulePullbackAdjunction B S hS g hg).unit ≫
        Functor.whiskerLeft (etaleModulePullback.{u, u} B S hS g hg)
          (Functor.whiskerRight (etaleModulePullbackAdjunction B S hS f hf).unit
            (modulePushforward B S hS g)) ≫
        (Adjunction.compUnitComparisonIso
          (etaleModulePullbackAdjunction B S hS g hg) (etaleModulePullbackAdjunction B S hS f hf)
          (etaleModulePullbackAdjunction B S hS k hk')
          (etaleModulePullbackFactorIso B S hS f g hf hg hk hk')).hom)
        (globalSectionsAb B S hS Z) :=
    congrArg (fun φ => Functor.whiskerRight φ (globalSectionsAb B S hS Z))
      (NatTrans.ext (funext fun M =>
        etaleModulePullbackAdjunction_unit_app_comp B S hS f g hf hg hk hk' M))
  rw [h, Functor.whiskerRight_comp, Functor.whiskerRight_comp]
  rfl

/-- If restriction along `f` is onto on `Rⁿ` at `F|_Y`, then so is the right derived
transformation of `Γ(Z, g_*(-)) ⟶ Γ(Z, g_* f_*((-)|_X))`, induced by the unit along `f`, at
`F`. -/
theorem epi_rightDerived_whiskerLeft_of_epi (M : Modules.{u, u} B S hS Z.1 Z.2) (n : ℕ)
    (h : Epi ((NatTrans.rightDerived (globalSectionsAbRestriction B S hS f hf) n).app
      ((etaleModulePullback.{u, u} B S hS g hg).obj M))) :
    Epi ((NatTrans.rightDerived (Functor.whiskerRight (Functor.whiskerLeft
      (etaleModulePullback.{u, u} B S hS g hg)
        (Functor.whiskerRight (etaleModulePullbackAdjunction B S hS f hf).unit
          (modulePushforward B S hS g))) (globalSectionsAb B S hS Z)) n).app M) := by
  have hw : Functor.whiskerRight (Functor.whiskerLeft (etaleModulePullback.{u, u} B S hS g hg)
        (Functor.whiskerRight (etaleModulePullbackAdjunction B S hS f hf).unit
          (modulePushforward B S hS g))) (globalSectionsAb B S hS Z) =
      Functor.whiskerLeft (etaleModulePullback.{u, u} B S hS g hg)
        (Functor.whiskerRight (etaleModulePullbackAdjunction B S hS f hf).unit
          (modulePushforward B S hS g ⋙ globalSectionsAb B S hS Z)) := rfl
  rw [hw]
  have := preservesInjectiveObjects_etaleModulePullback B S hS g hg
  have := modulePushforward_additive B S hS f
  have := modulePushforward_additive B S hS g
  let α := Functor.whiskerRight (etaleModulePullbackAdjunction B S hS f hf).unit
    (modulePushforward B S hS g ⋙ globalSectionsAb B S hS Z)
  let ε := globalSectionsModulePushforwardIso B S hS g
  have hcomm : α ≫ Functor.whiskerLeft (etaleModulePullback.{u, u} B S hS f hf ⋙
        modulePushforward B S hS f) ε.hom =
      ε.hom ≫ globalSectionsAbRestriction B S hS f hf :=
    NatTrans.ext (funext fun N =>
      (ε.hom.naturality ((etaleModulePullbackAdjunction B S hS f hf).unit.app N)))
  have hR := congrArg (fun φ => (NatTrans.rightDerived φ n).app
    ((etaleModulePullback.{u, u} B S hS g hg).obj M)) hcomm
  simp only [NatTrans.rightDerived_comp, NatTrans.comp_app] at hR
  have : IsIso ((NatTrans.rightDerived (Functor.whiskerLeft
      (etaleModulePullback.{u, u} B S hS f hf ⋙ modulePushforward B S hS f) ε.hom) n).app
        ((etaleModulePullback.{u, u} B S hS g hg).obj M)) :=
    isIso_rightDerived_app_of_isIso _ n _
  have : IsIso ((NatTrans.rightDerived ε.hom n).app
      ((etaleModulePullback.{u, u} B S hS g hg).obj M)) :=
    isIso_rightDerived_app_of_isIso _ n _
  have hα : Epi ((NatTrans.rightDerived α n).app
      ((etaleModulePullback.{u, u} B S hS g hg).obj M)) := by
    refine epi_of_epi_comp_isIso _ ((NatTrans.rightDerived (Functor.whiskerLeft
      (etaleModulePullback.{u, u} B S hS f hf ⋙ modulePushforward B S hS f) ε.hom) n).app
        ((etaleModulePullback.{u, u} B S hS g hg).obj M)) ?_
    rw [hR]
    infer_instance
  have key := Stacks.RightDerivedComp.objIso_hom_natTrans
    (etaleModulePullback.{u, u} B S hS g hg) (injectiveResolution M)
    (fun m hm => Functor.isZero_rightDerived_of_exact _ M m hm) α n
  have h3 : Epi ((Stacks.RightDerivedComp.objIso (etaleModulePullback.{u, u} B S hS g hg)
      (injectiveResolution M) (fun m hm => Functor.isZero_rightDerived_of_exact _ M m hm) _ n).hom ≫
      (NatTrans.rightDerived α n).app ((etaleModulePullback.{u, u} B S hS g hg).obj M)) :=
    inferInstance
  rw [key] at h3
  exact epi_of_epi_comp_isIso _ _ h3

/-- The right derived transformation of the comparison isomorphism of
`AlgebraicGeometry.Space.etaleModulePullbackAdjunction_unit_app_comp`, on global sections, is
invertible. -/
private theorem isIso_rightDerived_whiskerRight_compUnitComparisonIso
    (M : Modules.{u, u} B S hS Z.1 Z.2) (n : ℕ) :
    IsIso ((NatTrans.rightDerived (Functor.whiskerRight (Adjunction.compUnitComparisonIso
      (etaleModulePullbackAdjunction B S hS g hg) (etaleModulePullbackAdjunction B S hS f hf)
      (etaleModulePullbackAdjunction B S hS k hk')
      (etaleModulePullbackFactorIso B S hS f g hf hg hk hk')).hom
      (globalSectionsAb B S hS Z)) n).app M) := by
  have := modulePushforward_additive B S hS f
  have := modulePushforward_additive B S hS g
  have := modulePushforward_additive B S hS k
  exact isIso_rightDerived_app_of_isIso _ n M

include hk in
/-- For étale morphisms `f : X ⟶ Y`, `g : Y ⟶ Z` and `k = f ≫ g`, if restriction along `g` is
onto on `Hⁿ` at `M` and restriction along `f` is onto on `Hⁿ` at `M|_Y`, then restriction along
`k` is onto on `Hⁿ` at `M`. -/
theorem epi_rightDerived_globalSectionsAbRestriction_comp (M : Modules.{u, u} B S hS Z.1 Z.2)
    (n : ℕ) (hgM : Epi ((NatTrans.rightDerived (globalSectionsAbRestriction B S hS g hg) n).app M))
    (hfM : Epi ((NatTrans.rightDerived (globalSectionsAbRestriction B S hS f hf) n).app
      ((etaleModulePullback.{u, u} B S hS g hg).obj M))) :
    Epi ((NatTrans.rightDerived (globalSectionsAbRestriction B S hS k hk') n).app M) := by
  have := modulePushforward_additive B S hS f
  have := modulePushforward_additive B S hS g
  have := modulePushforward_additive B S hS k
  rw [globalSectionsAbRestriction_comp B S hS f g hf hg hk hk']
  simp only [NatTrans.rightDerived_comp, NatTrans.comp_app]
  have := epi_rightDerived_whiskerLeft_of_epi B S hS f g hf hg M n hfM
  have := isIso_rightDerived_whiskerRight_compUnitComparisonIso B S hS f g hf hg hk hk' M n
  exact epi_comp' hgM (epi_comp' inferInstance inferInstance)

/-- Let `k = f ≫ g` with `g` an open immersion, and let `ρ : g_*((-)|_Y) ⟶ k_*((-)|_X)` satisfy
`η_g ≫ ρ = η_k`.  Then `ρ` is `g_*` of the unit along `f` followed by the comparison of
`AlgebraicGeometry.Space.etaleModulePullbackAdjunction_unit_app_comp`. -/
theorem eq_whiskerLeft_comp_of_unit_comp (hgo : IsOpenImmersion B S hS g.hom)
    (ρ : etaleModulePullback.{u, u} B S hS g hg ⋙ modulePushforward B S hS g ⟶
      etaleModulePullback.{u, u} B S hS k hk' ⋙ modulePushforward B S hS k)
    (hρ : (etaleModulePullbackAdjunction B S hS g hg).unit ≫ ρ =
      (etaleModulePullbackAdjunction B S hS k hk').unit) :
    ρ = Functor.whiskerLeft (etaleModulePullback.{u, u} B S hS g hg)
        (Functor.whiskerRight (etaleModulePullbackAdjunction B S hS f hf).unit
          (modulePushforward B S hS g)) ≫ (Adjunction.compUnitComparisonIso
          (etaleModulePullbackAdjunction B S hS g hg) (etaleModulePullbackAdjunction B S hS f hf)
          (etaleModulePullbackAdjunction B S hS k hk')
          (etaleModulePullbackFactorIso B S hS f g hf hg hk hk')).hom := by
  have := isIso_etaleModulePullbackAdjunction_counit_of_isOpenImmersion B S hS g hg hgo
  refine Adjunction.natTrans_ext_of_unit_comp (etaleModulePullbackAdjunction B S hS g hg) ?_ ?_
  · intro M N φ hφ
    have := isIso_map_etaleModulePullback_of_isIso_map_comp B S hS f g hf hg hk hk' φ hφ
    exact inferInstanceAs (IsIso ((modulePushforward B S hS k).map
      ((etaleModulePullback.{u, u} B S hS k hk').map φ)))
  · rw [hρ]
    exact NatTrans.ext (funext fun M =>
      etaleModulePullbackAdjunction_unit_app_comp B S hS f g hf hg hk hk' M)

/-- The restriction along `f` read on the direct image along `g`, followed by the comparison
isomorphism of `AlgebraicGeometry.Space.etaleModulePullbackAdjunction_unit_app_comp`, is onto on
`Rⁿ(Γ(Z, -))` at `M` as soon as restriction along `f` is onto on `Hⁿ` at `M|_Y`. -/
theorem epi_rightDerived_whiskerRight_whiskerLeft_comp (M : Modules.{u, u} B S hS Z.1 Z.2)
    (n : ℕ) (h : Epi ((NatTrans.rightDerived (globalSectionsAbRestriction B S hS f hf) n).app
      ((etaleModulePullback.{u, u} B S hS g hg).obj M))) :
    Epi ((NatTrans.rightDerived (Functor.whiskerRight
      (Functor.whiskerLeft (etaleModulePullback.{u, u} B S hS g hg)
        (Functor.whiskerRight (etaleModulePullbackAdjunction B S hS f hf).unit
          (modulePushforward B S hS g)) ≫ (Adjunction.compUnitComparisonIso
          (etaleModulePullbackAdjunction B S hS g hg) (etaleModulePullbackAdjunction B S hS f hf)
          (etaleModulePullbackAdjunction B S hS k hk')
          (etaleModulePullbackFactorIso B S hS f g hf hg hk hk')).hom)
        (globalSectionsAb B S hS Z)) n).app M) := by
  have := modulePushforward_additive B S hS f
  have := modulePushforward_additive B S hS g
  have := modulePushforward_additive B S hS k
  rw [Functor.whiskerRight_comp]
  simp only [NatTrans.rightDerived_comp, NatTrans.comp_app]
  have := epi_rightDerived_whiskerLeft_of_epi B S hS f g hf hg M n h
  have := isIso_rightDerived_whiskerRight_compUnitComparisonIso B S hS f g hf hg hk hk' M n
  exact epi_comp' inferInstance inferInstance

include hk in
/-- Let `k = f ≫ g` with `g` an open immersion, and let `ρ : g_*((-)|_Y) ⟶ k_*((-)|_X)` satisfy
`η_g ≫ ρ = η_k`.  If restriction along `f` is onto on `Hⁿ` at `M|_Y`, then `ρ` is onto on
`Rⁿ(Γ(Z, -))` at `M`. -/
theorem epi_rightDerived_whiskerRight_of_unit_comp (hgo : IsOpenImmersion B S hS g.hom)
    (ρ : etaleModulePullback.{u, u} B S hS g hg ⋙ modulePushforward B S hS g ⟶
      etaleModulePullback.{u, u} B S hS k hk' ⋙ modulePushforward B S hS k)
    (hρ : (etaleModulePullbackAdjunction B S hS g hg).unit ≫ ρ =
      (etaleModulePullbackAdjunction B S hS k hk').unit)
    (M : Modules.{u, u} B S hS Z.1 Z.2) (n : ℕ)
    (h : Epi ((NatTrans.rightDerived (globalSectionsAbRestriction B S hS f hf) n).app
      ((etaleModulePullback.{u, u} B S hS g hg).obj M))) :
    Epi ((NatTrans.rightDerived (Functor.whiskerRight ρ (globalSectionsAb B S hS Z)) n).app
      M) := by
  rw [eq_whiskerLeft_comp_of_unit_comp B S hS f g hf hg hk hk' hgo ρ hρ]
  exact epi_rightDerived_whiskerRight_whiskerLeft_comp B S hS f g hf hg hk hk' M n h

end Comp

/-! ### Restriction across an elementary distinguished square -/

section Square

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- The map `j_{V,*}F|_V ⟶ j_{P,*}F|_P` of Stacks 08GW part (1), composed after the unit
`F ⟶ j_{V,*}F|_V`, is the unit `F ⟶ j_{P,*}F|_P`. -/
theorem edsAdjEtale_unit_comp_conjugateEquiv :
    (edsAdjEtale B S hS hsq).unit ≫
      conjugateEquiv ((edsAdjEtale B S hS hsq).comp (edsLowerShriekAdjEtale B S hS hsq))
        ((edsAdjInter B S hS hsq).comp (edsLowerShriekAdjInter B S hS hsq))
        (edsShriekEtaleComparison B S hS hsq (edsLowerShriekAdjEtale B S hS hsq)
          (edsLowerShriekAdjInter B S hS hsq)) = (edsAdjInter B S hS hsq).unit :=
  Adjunction.unit_comp_conjugateEquiv_comp _ _ _ _ _
    (edsShriekEtaleComparison_comp_counit B S hS hsq _ _)

/-- Let `(U ⊆ W, j_V : V ⟶ W)` be an
elementary distinguished square with intersection `P` and let `F` be an `𝒪_W`-module.  If the
map `Hⁿ(V, F|_V) ⟶ Hⁿ(P, F|_P)` of the Mayer–Vietoris sequence is onto, then so is the
restriction `Hⁿ(W, F) ⟶ Hⁿ(U, F|_U)`. -/
theorem epi_rightDerived_globalSectionsAbRestriction_edsOpenHom_of_epi
    (F : Modules.{u, u} B S hS W.1 W.2) (n : ℕ)
    (h : Epi ((NatTrans.rightDerived (Functor.whiskerRight
      (conjugateEquiv ((edsAdjEtale B S hS hsq).comp (edsLowerShriekAdjEtale B S hS hsq))
        ((edsAdjInter B S hS hsq).comp (edsLowerShriekAdjInter B S hS hsq))
        (edsShriekEtaleComparison B S hS hsq (edsLowerShriekAdjEtale B S hS hsq)
          (edsLowerShriekAdjInter B S hS hsq))) (globalSectionsAb B S hS W)) n).app F)) :
    Epi ((NatTrans.rightDerived (globalSectionsAbRestriction B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq)) n).app F) :=
  CategoryTheory.PushforwardMayerVietoris.epi_rightDerived_whiskerRight_of_natural_shortExact
    (edsAdjOpen B S hS hsq).unit (edsAdjEtale B S hS hsq).unit
    (conjugateEquiv ((edsAdjOpen B S hS hsq).comp (edsLowerShriekAdjOpen B S hS hsq))
      ((edsAdjInter B S hS hsq).comp (edsLowerShriekAdjInter B S hS hsq))
      (edsShriekOpenComparison B S hS hsq (edsLowerShriekAdjOpen B S hS hsq)
        (edsLowerShriekAdjInter B S hS hsq)))
    (conjugateEquiv ((edsAdjEtale B S hS hsq).comp (edsLowerShriekAdjEtale B S hS hsq))
      ((edsAdjInter B S hS hsq).comp (edsLowerShriekAdjInter B S hS hsq))
      (edsShriekEtaleComparison B S hS hsq (edsLowerShriekAdjEtale B S hS hsq)
        (edsLowerShriekAdjInter B S hS hsq)))
    (globalSectionsAb B S hS W) (zero_edsRestrictPushMayerVietorisLowerShriek B S hS hsq)
    (shortExact_edsRestrictPushMayerVietorisLowerShriek B S hS hsq) F n h

/-- If `Hⁿ(P, F|_P) = 0`
for the intersection `P` of an elementary distinguished square `(U ⊆ W, V ⟶ W)`, then the
restriction `Hⁿ(W, F) ⟶ Hⁿ(U, F|_U)` is onto. -/
theorem epi_rightDerived_globalSectionsAbRestriction_edsOpenHom_of_isZero
    (F : Modules.{u, u} B S hS W.1 W.2) (n : ℕ)
    (h : IsZero (((globalSectionsAb B S hS (edsInter B S hS hsq)).rightDerived n).obj
      ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
        (isEtale_edsInterHom B S hS hsq)).obj F))) :
    Epi ((NatTrans.rightDerived (globalSectionsAbRestriction B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq)) n).app F) :=
  epi_rightDerived_globalSectionsAbRestriction_edsOpenHom_of_epi B S hS hsq F n
    ⟨fun _ _ _ => (h.of_iso (rightDerivedGlobalSectionsAbRestrictPushIso B S hS
      (edsInterHom B S hS hsq) (isEtale_edsInterHom B S hS hsq) F n)).eq_of_src _ _⟩

/-- Let `(U ⊆ W, j_V : V ⟶ W)` be an elementary distinguished square whose étale part `j_V` is an
open immersion, with intersection `P` and projection `s : P ⟶ V`.  If restriction along `s` is
onto on `Hⁿ` at `F|_V`, then the map `Hⁿ(V, F|_V) ⟶ Hⁿ(P, F|_P)` of the Mayer–Vietoris sequence
is onto at `F`. -/
theorem epi_rightDerived_whiskerRight_edsEtaleComparison_of_epi
    (hfV : IsOpenImmersion B S hS fV) (F : Modules.{u, u} B S hS W.1 W.2) (n : ℕ)
    (h : Epi ((NatTrans.rightDerived (globalSectionsAbRestriction B S hS (edsSnd B S hS hsq)
      (isEtale_edsSnd B S hS hsq)) n).app ((etaleModulePullback.{u, u} B S hS
        (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)).obj F))) :
    Epi ((NatTrans.rightDerived (Functor.whiskerRight
      (conjugateEquiv ((edsAdjEtale B S hS hsq).comp (edsLowerShriekAdjEtale B S hS hsq))
        ((edsAdjInter B S hS hsq).comp (edsLowerShriekAdjInter B S hS hsq))
        (edsShriekEtaleComparison B S hS hsq (edsLowerShriekAdjEtale B S hS hsq)
          (edsLowerShriekAdjInter B S hS hsq))) (globalSectionsAb B S hS W)) n).app F) :=
  epi_rightDerived_whiskerRight_of_unit_comp B S hS (edsSnd B S hS hsq)
    (edsEtaleHom B S hS hsq) (isEtale_edsSnd B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)
    (edsSnd_comp_edsEtaleHom B S hS hsq) (isEtale_edsInterHom B S hS hsq) hfV _
    (edsAdjEtale_unit_comp_conjugateEquiv B S hS hsq) F n h

end Square

end AlgebraicGeometry.Space

end
