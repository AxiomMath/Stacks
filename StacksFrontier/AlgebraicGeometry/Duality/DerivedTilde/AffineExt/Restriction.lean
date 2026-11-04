module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineExt.Values
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineExt.ExactFunctorClasses

/-!
# Restriction between principal opens

For `D(g) ⊆ D(f)`, restriction of sections of the internal Hom complex corresponds to composition
with restriction of sections of the resolution, and restriction of sections of a module from
`D(f)` to `D(g)` corresponds to base change along `R_f ⟶ R_g`.

## Main results

* `AlgebraicGeometry.AffineExt.sectionComplexIso_restrict`.
* `AlgebraicGeometry.AffineExt.homEquiv_symm_comp_restrictR`.
* `AlgebraicGeometry.AffineExt.tildeBasicOpenIso_restrict`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CochainComplex.HomComplex

universe u

namespace AlgebraicGeometry.AffineExt

attribute [local instance 10000] HasDerivedCategory.standard

variable (R : CommRingCat.{u}) (K L : DerivedCategory (ModuleCat.{u} R))

/-- Restriction of sections from `U` to `V ⊆ U`, as `R`-linear maps. -/
def restrictR {U V : (Spec R).Opens} (h : V ≤ U) :
    TildeSlice.sectionsR U ⟶ TildeSlice.sectionsR V :=
  Functor.whiskerLeft (modulesSpecToSheaf ⋙ TopCat.Sheaf.forget _ _)
    ((evaluation _ _).map (homOfLE h).op)

/-- `restrictR R h` sends a section `x` of `F` over `U` to its restriction `F(U) ⟶ F(V)`. -/
lemma restrictR_app_apply {U V : (Spec R).Opens} (h : V ≤ U) (F : (Spec R).Modules)
    (x : (TildeSlice.sectionsR U).obj F) :
    (restrictR R h).app F x = F.val.map (homOfLE h).op (show F.val.obj (op U) from x) :=
  rfl

/-- The component of `sectionComplexIso` in degree `n`, evaluated at a section `s` and the
indices `p + n = q`, is `TildeSlice.tildeOverHomEquiv` applied to the corresponding component of
`(homModel R K L).sectionsIso U`. -/
lemma sectionComplexIso_hom_f_v (U : (Spec R).Opens) (n p q : ℤ) (hpq : p + n = q)
    (s : ((homModel R K L).obj.X n).val.obj (op U)) :
    (((sectionComplexIso R K L U).hom.f n) s).v p q hpq =
      TildeSlice.tildeOverHomEquiv U _ _
        ((AddCommGrpCat.Hom.hom (((homModel R K L).sectionsIso U).hom.f n) s).v p q hpq) :=
  rfl

/-- **The section complexes of the internal Hom complex restrict compatibly.** Restricting a
section from `U` to `V` corresponds, on Hom complexes of `R`-modules, to composing with the
restriction of sections of the resolution. -/
lemma sectionComplexIso_restrict {U V : (Spec R).Opens} (h : V ≤ U) (n p q : ℤ) (hpq : p + n = q)
    (s : ((homModel R K L).obj.X n).val.obj (op U)) :
    (((sectionComplexIso R K L V).hom.f n)
        (((homModel R K L).obj.X n).val.map (homOfLE h).op s)).v p q hpq =
      (((sectionComplexIso R K L U).hom.f n) s).v p q hpq ≫ (restrictR R h).app _ := by
  ext m
  refine (DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (sectionComplexIso_hom_f_v R K L V n p q hpq _)) m).trans ?_
  refine Eq.trans ?_ (DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (congrArg (· ≫ (restrictR R h).app _) (sectionComplexIso_hom_f_v R K L U n p q hpq s))) m).symm
  refine (TildeSlice.tildeOverHomEquiv_apply V _ _ _ m).trans ?_
  refine (((homModel R K L).restrict_natural (homOfLE h) n p q hpq s (𝟙 V) _).symm).trans ?_
  refine Eq.trans ?_ (congrArg ((restrictR R h).app _).hom
    (TildeSlice.tildeOverHomEquiv_apply U _ _ _ m)).symm
  let φ := ((AddCommGrpCat.Hom.hom (((homModel R K L).sectionsIso U).hom.f n) s).v p q hpq).val
  have key := PresheafOfModules.naturality_apply φ
    (Over.homMk (homOfLE h) : Over.mk (homOfLE h) ⟶ Over.mk (𝟙 U)).op
    (tilde.toOpen ((srcModel R K).X p) U m)
  have k2 : (((tilde.functor R).obj ((srcModel R K).X p)).over U).val.map
      (Over.homMk (homOfLE h) : Over.mk (homOfLE h) ⟶ Over.mk (𝟙 U)).op
        (tilde.toOpen ((srcModel R K).X p) U m) = tilde.toOpen ((srcModel R K).X p) V m :=
    ConcreteCategory.congr_hom (tilde.toOpen_res ((srcModel R K).X p) U V (homOfLE h)) m
  exact (congrArg (fun x => (φ.app (op (Over.mk (homOfLE h)))).hom x) k2).symm.trans key

/-! ### Restriction between principal opens on the module side -/

open TensorProduct
open scoped ChangeOfRings

/-- For `ψ = φ`, the inverse of the `eqToIso` between `extendScalars φ` and `extendScalars ψ` sends
`1 ⊗ m` to `1 ⊗ m`. -/
lemma eqToIso_inv_extendScalars_app_one_tmul {A B : Type u} [CommRing A] [CommRing B]
    {φ ψ : A →+* B} (hφψ : ψ = φ)
    (e : ModuleCat.extendScalars.{u, u, u} φ = ModuleCat.extendScalars.{u, u, u} ψ)
    (M : ModuleCat.{u} A) (m : M) :
    (eqToIso e).inv.app M ((1 : B) ⊗ₜ[A, ψ] m) = (1 : B) ⊗ₜ[A, φ] m := by
  subst hφψ
  rfl

/-- The inverse of `extendScalarsCompIso R h` sends `1 ⊗ m ∈ R_g ⊗_R M` to the image of `m` under
the unit `M ⟶ R_f ⊗_R M` followed by the unit `R_f ⊗_R M ⟶ R_g ⊗_{R_f} (R_f ⊗_R M)`. -/
lemma extendScalarsCompIso_inv_app_one_tmul {f g : R} (h : basicOpen R g ≤ basicOpen R f)
    (M : ModuleCat.{u} R) (m : M) :
    (extendScalarsCompIso R h).inv.app M ((1 : locRing R g) ⊗ₜ[R, (locMap R g).hom] m) =
      (ModuleCat.extendRestrictScalarsAdj (resMap R h).hom).unit.app _
        ((ModuleCat.extendRestrictScalarsAdj (locMap R f).hom).unit.app M m) := by
  refine (ConcreteCategory.comp_apply _ _ _).trans ?_
  refine (congrArg _ (eqToIso_inv_extendScalars_app_one_tmul
      (by rw [← CommRingCat.hom_comp, locMap_comp_resMap] :
        (locMap R g).hom = (resMap R h).hom.comp (locMap R f).hom) _ M m)).trans ?_
  exact ModuleCat.extendScalarsComp_hom_app_one_tmul _ _ M m

/-- Restriction of sections from `U` to `V ⊆ U`, linear over the restriction map of rings. -/
def restrictS {U V : (Spec R).Opens} (h : V ≤ U) (F : (Spec R).Modules) :
    (sectionsS R U).obj F ⟶
      (ModuleCat.restrictScalars ((Spec R).presheaf.map (homOfLE h).op).hom).obj
        ((sectionsS R V).obj F) :=
  F.val.map (homOfLE h).op

/-- The base change map `R_g ⊗_{R_f} F(D(f)) ⟶ F(D(g))` induced by restriction of sections. -/
def baseChangeRestrict {f g : R} (h : basicOpen R g ≤ basicOpen R f) :
    sectionsS R (basicOpen R f) ⋙ ModuleCat.extendScalars.{u, u, u} (resMap R h).hom ⟶
      sectionsS R (basicOpen R g) where
  app F :=
    ((ModuleCat.extendRestrictScalarsAdj (resMap R h).hom).homEquiv _ _).symm (restrictS R h F)
  naturality {F G} φ := by
    rw [Functor.comp_map, ← Adjunction.homEquiv_naturality_left_symm,
      ← Adjunction.homEquiv_naturality_right_symm]
    congr 1
    ext x
    exact (PresheafOfModules.naturality_apply φ.val (homOfLE h).op x).symm

/-- The `B`-linear extension of an `A`-linear map `r : M ⟶ N` agrees with `r` on the image of the
unit `M ⟶ B ⊗_A M`. -/
lemma extendRestrictScalarsAdj_homEquiv_symm_unit {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (r : M ⟶ (ModuleCat.restrictScalars φ).obj N) (m : M) :
    ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv M N).symm r
        ((ModuleCat.extendRestrictScalarsAdj φ).unit.app M m) = r m :=
  ConcreteCategory.congr_hom (((ModuleCat.extendRestrictScalarsAdj φ).homEquiv_unit
    (f := ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv M N).symm r)).symm.trans
      (((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).apply_symm_apply _)) m

/-- `baseChangeRestrict R h` sends the image of a section `x ∈ F(D(f))` in `R_g ⊗_{R_f} F(D(f))`
to the restriction of `x` to `D(g)`. -/
lemma baseChangeRestrict_app_unit {f g : R} (h : basicOpen R g ≤ basicOpen R f)
    (F : (Spec R).Modules) (x : (sectionsS R (basicOpen R f)).obj F) :
    (baseChangeRestrict R h).app F
        ((ModuleCat.extendRestrictScalarsAdj (resMap R h).hom).unit.app _ x) =
      restrictS R h F x :=
  ConcreteCategory.congr_hom (((ModuleCat.extendRestrictScalarsAdj (resMap R h).hom).homEquiv_unit
    (f := (baseChangeRestrict R h).app F)).symm.trans
      (((ModuleCat.extendRestrictScalarsAdj (resMap R h).hom).homEquiv _ _).apply_symm_apply _)) x

/-- The composite `R_g ⊗_R M ⟶ R_g ⊗_{R_f} (R_f ⊗_R M) ⟶ R_g ⊗_{R_f} F(D(f)) ⟶ F(D(g))` sends
`1 ⊗ m` to the restriction to `D(g)` of the image of `m` under the `R_f`-linear map `T`. -/
private lemma extendScalarsCompIso_inv_comp_baseChangeRestrict_one_tmul {f g : R}
    (h : basicOpen R g ≤ basicOpen R f) (M : ModuleCat.{u} R) (F : (Spec R).Modules)
    (T : (ModuleCat.extendScalars.{u, u, u} (locMap R f).hom).obj M ⟶
      (sectionsS R (basicOpen R f)).obj F) (m : M) :
    ((extendScalarsCompIso R h).inv.app M ≫
        (ModuleCat.extendScalars.{u, u, u} (resMap R h).hom).map T ≫
        (baseChangeRestrict R h).app F) ((1 : locRing R g) ⊗ₜ[R, (locMap R g).hom] m) =
      restrictS R h F (T ((ModuleCat.extendRestrictScalarsAdj (locMap R f).hom).unit.app M m)) := by
  refine (ConcreteCategory.comp_apply _ _ _).trans ?_
  refine Eq.trans (congrArg _ (extendScalarsCompIso_inv_app_one_tmul R h M m)) ?_
  refine (ConcreteCategory.comp_apply _ _ _).trans ?_
  refine Eq.trans (congrArg ((baseChangeRestrict R h).app F).hom
    (ModuleCat.ExtendScalars.map_tmul _ _ 1 _)) ?_
  exact baseChangeRestrict_app_unit R h F _

/-- **Restriction of `R`-linear maps into sections, read over the localizations.** For an
`R`-linear map `ψ : M ⟶ F(D(f))`, the `R_g`-linear extension of `ψ` followed by restriction to
`D(g)` is the base change along `R_f ⟶ R_g` of the `R_f`-linear extension of `ψ`. -/
lemma homEquiv_symm_comp_restrictR {f g : R} (h : basicOpen R g ≤ basicOpen R f)
    (M : ModuleCat.{u} R) (F : (Spec R).Modules)
    (ψ : M ⟶ (TildeSlice.sectionsR (basicOpen R f)).obj F) :
    ((ModuleCat.extendRestrictScalarsAdj (locMap R g).hom).homEquiv M
        ((sectionsS R (basicOpen R g)).obj F)).symm (ψ ≫ (restrictR R h).app F) =
      (extendScalarsCompIso R h).inv.app M ≫
        (ModuleCat.extendScalars.{u, u, u} (resMap R h).hom).map
          (((ModuleCat.extendRestrictScalarsAdj (locMap R f).hom).homEquiv M
            ((sectionsS R (basicOpen R f)).obj F)).symm ψ) ≫
        (baseChangeRestrict R h).app F := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  refine (extendRestrictScalarsAdj_homEquiv_symm_unit (locMap R g).hom _ m).trans ?_
  refine Eq.trans ?_
    (extendScalarsCompIso_inv_comp_baseChangeRestrict_one_tmul R h M F _ m).symm
  exact congrArg (restrictS R h F).hom
    (extendRestrictScalarsAdj_homEquiv_symm_unit (locMap R f).hom ψ m).symm

/-- **The identification of sections of `M̃` with localizations is compatible with
restriction.** -/
lemma tildeBasicOpenIso_restrict {f g : R} (h : basicOpen R g ≤ basicOpen R f)
    (M : ModuleCat.{u} R) :
    (tildeBasicOpenIso R g M).hom =
      (extendScalarsCompIso R h).inv.app M ≫
        (ModuleCat.extendScalars.{u, u, u} (resMap R h).hom).map (tildeBasicOpenIso R f M).hom ≫
        (baseChangeRestrict R h).app ((tilde.functor R).obj M) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  refine (tildeBasicOpenIso_hom_one_tmul R g M m).trans ?_
  refine Eq.trans ?_
    (extendScalarsCompIso_inv_comp_baseChangeRestrict_one_tmul R h M ((tilde.functor R).obj M)
      (tildeBasicOpenIso R f M).hom m).symm
  refine Eq.trans ?_ (congrArg (ConcreteCategory.hom (restrictS R h ((tilde.functor R).obj M)))
    (tildeBasicOpenIso_hom_one_tmul R f M m).symm)
  exact (ConcreteCategory.congr_hom (tilde.toOpen_res M (basicOpen R f) (basicOpen R g)
    (homOfLE h)) m).symm

end AlgebraicGeometry.AffineExt
