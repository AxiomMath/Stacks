module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCartesianQcoh
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleHomSheafGlue
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedSite
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleEssSurjReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PointsOtherTopologies.SmallEtale
public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.FiniteDisjointSections
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianChangeOfRings
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ConstantBaseRing
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleQcqsPushforward

/-!
# Sections over affine objects of the sheafification of a cartesian presheaf of modules

Let `S` be a scheme in a big étale site and let `P` be a presheaf of modules on the small étale
site of `S` which is *cartesian between affine objects*: for every morphism `T ⟶ T'` of affine
objects the base change comparison `𝒪(T) ⊗_{𝒪(T')} P(T') ⟶ P(T)` is bijective. Then the
sheafification unit `P ⟶ P^#` is bijective on the sections over every affine object
(`AlgebraicGeometry.SmallEtale.bijective_sheafificationAdjunction_unit_app_of_isAffine`).

As a consequence, when the small étale site has an affine terminal object `t`, every module `T`
over `Γ(t, 𝒪)` is the module of global sections of a sheaf of modules, namely of the
sheafification of the cartesian presheaf `V ↦ 𝒪(V) ⊗_{Γ(t, 𝒪)} T`
(`AlgebraicGeometry.SmallEtale.exists_sheafOfModules_sections_iso`).

These are inputs of the base change property of locally quasi-coherent modules with the flat
base change property along flat morphisms of affines (Stacks 0779, its input R2).

## Implementation notes

The restriction of `P` to the small affine étale site is a sheaf by flat descent,
`AlgebraicGeometry.SmallEtale.isSheaf_of_cartesian_smallAffineEtale`; the small affine étale
site is a dense subsite of the small étale site (**Stacks 04HR**), so a covering sieve of an
affine object restricts to a covering sieve of the affine site. The unit of sheafification is
locally injective and locally surjective; injectivity at an affine object is separatedness of the
affine restriction, and surjectivity is the amalgamation in the affine restriction of the local
preimages, which are compatible by injectivity.

## References

* [Stacks Project, Tag 04HR](https://stacks.math.columbia.edu/tag/04HR)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A covering sieve of an affine object of the small étale site restricts to a covering sieve
of the small affine étale site. -/
theorem functorPullback_mem_smallAffineEtale {V : SmallAffineEtale B S hS}
    {T : Sieve ((SmallAffineEtale.inclusion B S hS).obj V)}
    (hT : T ∈ topology B S hS ((SmallAffineEtale.inclusion B S hS).obj V)) :
    T.functorPullback (SmallAffineEtale.inclusion B S hS) ∈ SmallAffineEtale.topology B S hS V := by
  have := (SmallAffineEtale.inclusion_isSpecialCocontinuous B S hS).2
  have := Functor.IsDenseSubsite.isCoverDense (SmallAffineEtale.topology B S hS)
    (topology B S hS) (SmallAffineEtale.inclusion B S hS)
  have := Functor.IsDenseSubsite.isLocallyFull (SmallAffineEtale.topology B S hS)
    (topology B S hS) (SmallAffineEtale.inclusion B S hS)
  rw [← (SmallAffineEtale.inclusion B S hS).functorPushforward_mem_iff
    (SmallAffineEtale.topology B S hS) (topology B S hS)]
  exact Functor.IsCoverDense.functorPullback_pushforward_covering ⟨T, hT⟩

variable {B S hS} in
/-- The restriction of a presheaf of modules on the small étale site to the small affine étale
site, over the rings of the affine objects. -/
abbrev affineRestriction (P : PresheafOfModules.{u} (structureSheaf B S hS).obj) :
    PresheafOfModules.{u} (affineChartRings B S hS ⋙ forget₂ CommRingCat RingCat) :=
  (PresheafOfModules.pushforward₀ (SmallAffineEtale.inclusion B S hS)
    (structureSheaf B S hS).obj).obj P

variable {B S hS} in
/-- A presheaf of modules on the small étale site which is cartesian between affine objects
restricts to a sheaf on the small affine étale site, by flat descent. -/
theorem isSheaf_affineRestriction (P : PresheafOfModules.{u} (structureSheaf B S hS).obj)
    (hP : ∀ {T T' : SmallEtale B S hS} (g : T ⟶ T'),
      _root_.AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T) →
      _root_.AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T') → Function.Bijective
        (Stacks.PresheafOfModules.restrictionBaseChange (R := commStructurePresheaf B S hS) P
          g.op)) :
    Presheaf.IsSheaf (SmallAffineEtale.topology B S hS) (affineRestriction P).presheaf :=
  isSheaf_of_cartesian_smallAffineEtale B S hS (affineRestriction P) fun {X Y} f =>
    (ConcreteCategory.isIso_iff_bijective _).2
      (hP ((SmallAffineEtale.inclusion B S hS).map f.unop) Y.unop.property X.unop.property)

variable {B S hS} in
/-- The underlying abelian presheaf of the affine restriction of a presheaf of modules cartesian
between affine objects is a sheaf on the small affine étale site. -/
theorem isSheaf_affineRestriction_forget (P : PresheafOfModules.{u} (structureSheaf B S hS).obj)
    (hP : ∀ {T T' : SmallEtale B S hS} (g : T ⟶ T'),
      _root_.AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T) →
      _root_.AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T') → Function.Bijective
        (Stacks.PresheafOfModules.restrictionBaseChange (R := commStructurePresheaf B S hS) P
          g.op)) :
    Presheaf.IsSheaf (SmallAffineEtale.topology B S hS)
      ((affineRestriction P).presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u}) :=
  SheafOfModules.isSheaf_sections
    (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallAffineEtaleRingedSite B S hS).O)
    ⟨affineRestriction P, isSheaf_affineRestriction P hP⟩

variable {B S hS} in
/-- The map to the sheafification of a presheaf of modules cartesian between affine objects is
injective on the sections over every affine object. -/
theorem injective_toSheafify_app_of_isAffine
    (P : PresheafOfModules.{u} (structureSheaf B S hS).obj)
    (hP : ∀ {T T' : SmallEtale B S hS} (g : T ⟶ T'),
      _root_.AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T) →
      _root_.AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T') → Function.Bijective
        (Stacks.PresheafOfModules.restrictionBaseChange (R := commStructurePresheaf B S hS) P
          g.op))
    (W : SmallAffineEtale B S hS) :
    Function.Injective ((CategoryTheory.toSheafify (topology B S hS) P.presheaf).app
      (op ((SmallAffineEtale.inclusion B S hS).obj W))) := by
  intro a b hab
  exact ((isSheaf_affineRestriction_forget P hP).isSheafFor _
    (functorPullback_mem_smallAffineEtale B S hS
      (Presheaf.equalizerSieve_mem _ _ a b hab))).isSeparatedFor.ext fun _ _ hf => hf

/-- **The sheafification unit of a presheaf of modules cartesian between affine objects is
bijective at every affine object of the small étale site.** The presheaf is a sheaf on the small
affine étale site by flat descent, and the small affine étale site is a dense subsite, so the
locally injective and locally surjective unit is injective and surjective on the sections over
an affine object. -/
theorem bijective_sheafificationAdjunction_unit_app_of_isAffine
    (P : PresheafOfModules.{u} (structureSheaf B S hS).obj)
    (hP : ∀ {T T' : SmallEtale B S hS} (g : T ⟶ T'),
      _root_.AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T) →
      _root_.AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T') → Function.Bijective
        (Stacks.PresheafOfModules.restrictionBaseChange (R := commStructurePresheaf B S hS) P
          g.op))
    {V : SmallEtale B S hS} (hV : _root_.AlgebraicGeometry.IsAffine ((toScheme B S hS).obj V)) :
    Function.Bijective (((PresheafOfModules.sheafificationAdjunction
      (𝟙 (structureSheaf B S hS).obj)).unit.app P).app (op V)) := by
  let J := topology B S hS
  let ι := SmallAffineEtale.inclusion B S hS
  let F := P.presheaf
  let Q := CategoryTheory.toSheafify J F
  let G := CategoryTheory.sheafify J F
  have hG : Presheaf.IsSheaf J (G ⋙ CategoryTheory.forget AddCommGrpCat.{u}) :=
    SheafOfModules.isSheaf_sections
      ((PresheafOfModules.sheafification (𝟙 (structureSheaf B S hS).obj)).obj P)
  have hA := isSheaf_affineRestriction_forget P hP
  let V' : SmallAffineEtale B S hS := ⟨V, hV⟩
  change Function.Bijective (Q.app (op (ι.obj V')))
  refine ⟨injective_toSheafify_app_of_isAffine P hP V', fun s => ?_⟩
  have hI := functorPullback_mem_smallAffineEtale B S hS (V := V') (Presheaf.imageSieve_mem J Q s)
  let x : Presieve.FamilyOfElements
      ((affineRestriction P).presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u})
      ((Presheaf.imageSieve Q s).functorPullback ι).arrows :=
    fun W f hf => Presheaf.localPreimage Q s (ι.map f) hf
  have hx : ∀ ⦃W : SmallAffineEtale B S hS⦄ (f : W ⟶ V')
      (hf : ((Presheaf.imageSieve Q s).functorPullback ι).arrows f),
      Q.app (op (ι.obj W)) (x f hf) = G.map (ι.map f).op s := fun W f hf =>
    Presheaf.app_localPreimage Q s (ι.map f) hf
  have hcomp : x.Compatible := by
    intro W₁ W₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ hcomm
    apply injective_toSheafify_app_of_isAffine P hP Z
    have e₁ := NatTrans.naturality_apply Q (ι.map g₁).op (x f₁ hf₁)
    have e₂ := NatTrans.naturality_apply Q (ι.map g₂).op (x f₂ hf₂)
    rw [hx f₁ hf₁, ← G.map_comp_apply, ← op_comp, ← ι.map_comp] at e₁
    rw [hx f₂ hf₂, ← G.map_comp_apply, ← op_comp, ← ι.map_comp, ← hcomm] at e₂
    exact e₁.trans e₂.symm
  let t := (hA.isSheafFor _ hI).amalgamate x hcomp
  have ht : ∀ ⦃W : SmallAffineEtale B S hS⦄ (f : W ⟶ V')
      (hf : ((Presheaf.imageSieve Q s).functorPullback ι).arrows f),
      F.map (ι.map f).op t = x f hf := fun W f hf =>
    (hA.isSheafFor _ hI).valid_glue hcomp f hf
  have hpush : ((Presheaf.imageSieve Q s).functorPullback ι).functorPushforward ι ∈
      J (ι.obj V') :=
    (ι.functorPushforward_mem_iff (SmallAffineEtale.topology B S hS) J).2 hI
  refine ⟨t, (hG.isSheafFor _ hpush).isSeparatedFor.ext ?_⟩
  rintro Y h ⟨W, f, h', hf, rfl⟩
  have e := NatTrans.naturality_apply Q (ι.map f).op t
  rw [ht f hf, hx f hf] at e
  change G.map (h' ≫ ι.map f).op (Q.app _ t) = G.map (h' ≫ ι.map f).op s
  rw [op_comp, G.map_comp_apply, G.map_comp_apply, ← e]

variable {B S hS} in
/-- The constant presheaf of rings on the small étale site with value the ring of global
functions of an object `t`. -/
abbrev constGlobalRing (t : SmallEtale B S hS) : (SmallEtale B S hS)ᵒᵖ ⥤ CommRingCat.{u} :=
  (Functor.const _).obj ((commStructurePresheaf B S hS).obj (op t))

variable {B S hS} in
/-- The constant presheaf of modules with value a module over the ring of global functions of
`t`, over the constant presheaf of rings. -/
abbrev constGlobalModule (t : SmallEtale B S hS)
    (T : ModuleCat.{u} ((commStructurePresheaf B S hS).obj (op t))) :
    PresheafOfModules.{u} (Stacks.ringPresheaf (constGlobalRing t)) :=
  Stacks.PresheafOfModules.ofFunctorObj (C := SmallEtale B S hS)
    ((commStructurePresheaf B S hS).obj (op t)) ((Functor.const _).obj T)

variable {B S hS} in
/-- A constant presheaf of modules over a constant presheaf of rings is cartesian. -/
theorem isIso_restrictionBaseChange_constGlobalModule (t : SmallEtale B S hS)
    (T : ModuleCat.{u} ((commStructurePresheaf B S hS).obj (op t)))
    {X Y : (SmallEtale B S hS)ᵒᵖ} (f : X ⟶ Y) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange (R := constGlobalRing t)
      (constGlobalModule t T) f) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact Stacks.PresheafOfModules.bijective_restrictionBaseChange_of_isBaseChange
    (R := constGlobalRing t) (constGlobalModule t T) f LinearMap.id (fun _ => rfl)
    (IsBaseChange.ofEquiv (LinearEquiv.refl _ _))

variable {B S hS} in
/-- The ring maps from the global functions of a terminal object to the functions on every
object. -/
def globalRingHom {t : SmallEtale B S hS} (ht : IsTerminal t) :
    constGlobalRing t ⟶ commStructurePresheaf B S hS where
  app V := (commStructurePresheaf B S hS).map (ht.from V.unop).op
  naturality V W f := by
    change 𝟙 _ ≫ _ = _
    rw [Category.id_comp, ← Functor.map_comp]
    exact congrArg (fun g => (commStructurePresheaf B S hS).map g)
      (Quiver.Hom.unop_inj (ht.hom_ext _ _))

variable {B S hS} in
/-- At the terminal object itself the ring map from the global functions is the identity. -/
theorem globalRingHom_app_self {t : SmallEtale B S hS} (ht : IsTerminal t)
    (r : (commStructurePresheaf B S hS).obj (op t)) :
    ((globalRingHom ht).app (op t)).hom r = r := by
  change ((commStructurePresheaf B S hS).map (ht.from t).op).hom r = r
  rw [show ht.from t = 𝟙 t from ht.hom_ext _ _, op_id, CategoryTheory.Functor.map_id]
  rfl

variable {B S hS} in
/-- The base change along `globalRingHom` of a constant presheaf of modules is cartesian. -/
theorem bijective_restrictionBaseChange_changeOfRings_constGlobalModule {t : SmallEtale B S hS}
    (ht : IsTerminal t) (T : ModuleCat.{u} ((commStructurePresheaf B S hS).obj (op t)))
    {T₁ T₂ : SmallEtale B S hS} (g : T₁ ⟶ T₂) :
    Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange
      (R := commStructurePresheaf B S hS)
      ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings (globalRingHom ht)).obj
        (constGlobalModule t T)) g.op) := by
  have := isIso_restrictionBaseChange_constGlobalModule t T g.op
  exact (ConcreteCategory.isIso_iff_bijective _).1
    (Stacks.PresheafOfModules.ChangeOfRings.isIso_restrictionBaseChange_changeOfRings
      (globalRingHom ht) (constGlobalModule t T) g.op)

variable {B S hS} in
/-- At a terminal object `t`, the base change along `globalRingHom` of the constant presheaf of
modules with value `T` has sections `T`. -/
def changeOfRingsConstGlobalModuleObjIso {t : SmallEtale B S hS} (ht : IsTerminal t)
    (T : ModuleCat.{u} ((commStructurePresheaf B S hS).obj (op t))) :
    ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings (globalRingHom ht)).obj
      (constGlobalModule t T)).obj (op t) ≅ T := by
  let θ := globalRingHom ht
  let P : PresheafOfModules.{u} (structureSheaf B S hS).obj :=
    (Stacks.PresheafOfModules.ChangeOfRings.changeOfRings θ).obj (constGlobalModule t T)
  let Γ₁ := (constGlobalRing t).obj (op t)
  let Γ₂ := (commStructurePresheaf B S hS).obj (op t)
  let M₀ := (constGlobalModule t T).obj (op t)
  let : Algebra Γ₁ Γ₂ := (θ.app (op t)).hom.toAlgebra
  have hθ : ∀ c : Γ₁, algebraMap Γ₁ Γ₂ c = c := globalRingHom_app_self ht
  let f₀ : Γ₂ →ₗ[Γ₁] M₀ →ₗ[Γ₁] M₀ := LinearMap.mk₂ Γ₁ (fun a x => (a : Γ₁) • x)
    (fun _ _ _ => add_smul _ _ _) (fun c a x => by
      change ((algebraMap Γ₁ Γ₂ c * a : Γ₂) : Γ₁) • x = c • ((a : Γ₁) • x)
      rw [hθ, mul_smul])
    (fun _ _ _ => smul_add _ _ _) (fun c a x => by
      change (a : Γ₁) • (c • x) = c • ((a : Γ₁) • x)
      rw [smul_smul, smul_smul, mul_comm])
  let k : TensorProduct Γ₁ Γ₂ M₀ →ₗ[Γ₁] M₀ := TensorProduct.lift f₀
  have hk : ∀ a x, k (a ⊗ₜ x) = (a : Γ₁) • x := fun _ _ => TensorProduct.lift.tmul _ _
  have kj : ∀ x, k ((1 : Γ₂) ⊗ₜ x) = x := fun x => (hk _ x).trans (one_smul _ x)
  have jk : ∀ y, (1 : Γ₂) ⊗ₜ[Γ₁] k y = y := fun y => by
    induction y using TensorProduct.inductionOn with
    | add a b ha hb => rw [map_add, TensorProduct.tmul_add, ha, hb]
    | tmul a x =>
      rw [hk, ← TensorProduct.smul_tmul (R := Γ₁) (R' := Γ₁) (a : Γ₁) (1 : Γ₂) x]
      congr 1
      exact (Algebra.smul_def (R := Γ₁) (a : Γ₁) (1 : Γ₂)).trans ((mul_one _).trans (hθ a))
  have hks : ∀ (c : Γ₂) y, k (c • y) = (c : Γ₁) • k y := fun c y => by
    induction y using TensorProduct.inductionOn with
    | add a b ha hb => rw [smul_add, map_add, ha, hb, map_add, smul_add]
    | tmul a x =>
      rw [TensorProduct.smul_tmul', hk, hk, smul_eq_mul]
      exact mul_smul _ _ x
  let : Module ((structureSheaf B S hS).obj.obj (op t)) T := inferInstanceAs (Module Γ₂ T)
  let e : P.obj (op t) ≃ₗ[(structureSheaf B S hS).obj.obj (op t)] T :=
    { toFun := fun y => k y
      invFun := fun x => (1 : Γ₂) ⊗ₜ[Γ₁] x
      left_inv := jk
      right_inv := kj
      map_add' := map_add k
      map_smul' := hks }
  exact e.toModuleIso

/-- **Every module over the ring of global functions of an affine terminal object of the small
étale site is the module of global sections of a sheaf of modules.** It is the global sections
of the sheafification of the cartesian presheaf `V ↦ 𝒪(V) ⊗_{Γ(t)} T`, by
`AlgebraicGeometry.SmallEtale.bijective_sheafificationAdjunction_unit_app_of_isAffine`. -/
theorem exists_sheafOfModules_sections_iso {t : SmallEtale B S hS} (ht : IsTerminal t)
    (hta : _root_.AlgebraicGeometry.IsAffine ((toScheme B S hS).obj t))
    (T : ModuleCat.{u} ((commStructurePresheaf B S hS).obj (op t))) :
    ∃ L : SheafOfModules.{u} (structureSheaf B S hS), Nonempty (L.val.obj (op t) ≅ T) := by
  let P : PresheafOfModules.{u} (structureSheaf B S hS).obj :=
    (Stacks.PresheafOfModules.ChangeOfRings.changeOfRings (globalRingHom ht)).obj
      (constGlobalModule t T)
  let L := (PresheafOfModules.sheafification (𝟙 (structureSheaf B S hS).obj)).obj P
  let η := ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (structureSheaf B S hS).obj)).unit.app P).app (op t)
  have hη := bijective_sheafificationAdjunction_unit_app_of_isAffine B S hS P
    (fun g _ _ => bijective_restrictionBaseChange_changeOfRings_constGlobalModule ht T g) hta
  let ηl : P.obj (op t) →ₗ[(structureSheaf B S hS).obj.obj (op t)] L.val.obj (op t) :=
    { toFun := fun x => η x
      map_add' := map_add η.hom
      map_smul' := η.hom.map_smul }
  exact ⟨L, ⟨(LinearEquiv.ofBijective ηl hη).toModuleIso.symm ≪≫
    changeOfRingsConstGlobalModuleObjIso ht T⟩⟩

end AlgebraicGeometry.SmallEtale

end
