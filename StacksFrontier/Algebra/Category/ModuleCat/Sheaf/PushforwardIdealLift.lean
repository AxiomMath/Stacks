module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyBijectiveCovering

/-!
# Maps of ideals induced by a map of ambient sheaves of rings

Let `F : C ⥤ D` be a continuous functor of sites. On `C` let `π₁ : A₁ ⟶ R₁` be a map of sheaves
of rings and `I₁` an `R₁`-module with an `A₁`-linear map `ι₁ : I₁ ⟶ A₁` (an "ideal" of `A₁`);
on `D` let `π₀ : A₀ ⟶ R₀`, `I₀` and `ι₀` be the same data with `ι₀` injective on sections.
Given maps of sheaves of rings `φA : A₁ ⟶ F^*A₀` and `φR : R₁ ⟶ F^*R₀` compatible with `π₁`
and `π₀`, a family of maps `e_U : I₁(U) ⟶ I₀(F U)` with `ι₀ ∘ e_U = φA ∘ ι₁` is automatically
additive, natural and `A₁`-semilinear; when `π₁` is locally surjective it is therefore a
morphism of sheaves of `R₁`-modules `I₁ ⟶ φR_* I₀` (`SheafOfModules.idealLift`). It is an
isomorphism as soon as every `e_U` is bijective.

## Main definitions
* `SheafOfModules.idealLift`: the morphism `I₁ ⟶ (pushforward φR).obj I₀`.
* `SheafOfModules.isIso_idealLift`: it is an isomorphism if it is bijective on sections.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u₁ u₂ v₁ v₂ u

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  [F.IsContinuous J K]
  {A₁ R₁ : Sheaf J RingCat.{u}} {A₀ R₀ : Sheaf K RingCat.{u}}
  {π₁ : A₁ ⟶ R₁} {π₀ : A₀ ⟶ R₀}
  {I₁ : SheafOfModules.{u} R₁} {I₀ : SheafOfModules.{u} R₀}
  (ι₁ : (restrictScalars π₁).obj I₁ ⟶ unit A₁) (ι₀ : (restrictScalars π₀).obj I₀ ⟶ unit A₀)
  (φA : A₁ ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj A₀)
  (φR : R₁ ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R₀)
  (e : ∀ U : Cᵒᵖ, I₁.val.obj U → I₀.val.obj (F.op.obj U))

/-- The defining property of a lift: `ι₀ ∘ e_U = φA ∘ ι₁`. -/
def IsIdealLift : Prop :=
  ∀ (U : Cᵒᵖ) (m : I₁.val.obj U),
    (show A₀.obj.obj (F.op.obj U) from ι₀.val.app (F.op.obj U) (e U m)) =
      φA.hom.app U (show A₁.obj.obj U from ι₁.val.app U m)

variable {ι₁ ι₀ φA e}

/-- Compatibility `π₁ ≫ φR = φA ≫ π₀` evaluated on a section. -/
private theorem comm_hom_app_apply
    (comm : π₁ ≫ φR = φA ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map π₀)
    (U : Cᵒᵖ) (a : A₁.obj.obj U) :
    (show R₀.obj.obj (F.op.obj U) from φR.hom.app U (π₁.hom.app U a)) =
      π₀.hom.app (F.op.obj U) (φA.hom.app U a) :=
  ConcreteCategory.congr_hom (congrArg (fun k => k.hom.app U) comm) a

section

variable (he : IsIdealLift ι₁ ι₀ φA e) (hinj : ∀ V : Dᵒᵖ, Function.Injective (ι₀.val.app V))
include he hinj

theorem IsIdealLift.map_add (U : Cᵒᵖ) (m m' : I₁.val.obj U) :
    e U (m + m') = e U m + e U m' := by
  apply hinj
  have h1 := he U (m + m')
  have h2 := he U m
  have h3 := he U m'
  have a1 : (show A₁.obj.obj U from ι₁.val.app U (m + m')) =
      (show A₁.obj.obj U from ι₁.val.app U m) + (show A₁.obj.obj U from ι₁.val.app U m') :=
    (ι₁.val.app U).hom.map_add m m'
  have a0 : (show A₀.obj.obj (F.op.obj U) from ι₀.val.app (F.op.obj U) (e U m + e U m')) =
      (show A₀.obj.obj (F.op.obj U) from ι₀.val.app (F.op.obj U) (e U m)) +
        (show A₀.obj.obj (F.op.obj U) from ι₀.val.app (F.op.obj U) (e U m')) :=
    (ι₀.val.app (F.op.obj U)).hom.map_add (e U m) (e U m')
  show (show A₀.obj.obj (F.op.obj U) from ι₀.val.app (F.op.obj U) (e U (m + m'))) =
    (show A₀.obj.obj (F.op.obj U) from ι₀.val.app (F.op.obj U) (e U m + e U m'))
  rw [h1, a0, h2, h3, a1]
  exact _root_.map_add _ _ _

theorem IsIdealLift.naturality {U U' : Cᵒᵖ} (p : U ⟶ U') (m : I₁.val.obj U) :
    e U' (I₁.val.map p m) = I₀.val.map (F.op.map p) (e U m) := by
  apply hinj
  have h1 := he U' (I₁.val.map p m)
  have h2 := he U m
  have n1 : (show A₁.obj.obj U' from ι₁.val.app U' (I₁.val.map p m)) =
      A₁.obj.map p (show A₁.obj.obj U from ι₁.val.app U m) :=
    PresheafOfModules.naturality_apply ι₁.val p m
  have n0 : (show A₀.obj.obj (F.op.obj U') from
      ι₀.val.app (F.op.obj U') (I₀.val.map (F.op.map p) (e U m))) =
      A₀.obj.map (F.op.map p) (show A₀.obj.obj (F.op.obj U) from
        ι₀.val.app (F.op.obj U) (e U m)) :=
    PresheafOfModules.naturality_apply ι₀.val (F.op.map p) (e U m)
  have nA : φA.hom.app U' (A₁.obj.map p (show A₁.obj.obj U from ι₁.val.app U m)) =
      A₀.obj.map (F.op.map p) (φA.hom.app U (show A₁.obj.obj U from ι₁.val.app U m)) :=
    ConcreteCategory.congr_hom (φA.hom.naturality p) _
  show (show A₀.obj.obj (F.op.obj U') from ι₀.val.app (F.op.obj U') (e U' (I₁.val.map p m))) =
    (show A₀.obj.obj (F.op.obj U') from
      ι₀.val.app (F.op.obj U') (I₀.val.map (F.op.map p) (e U m)))
  rw [h1, n1, nA, n0, h2]

variable (comm : π₁ ≫ φR = φA ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map π₀)
include comm

theorem IsIdealLift.map_smul (U : Cᵒᵖ) (a : A₁.obj.obj U) (m : I₁.val.obj U) :
    e U (π₁.hom.app U a • m) =
      (show R₀.obj.obj (F.op.obj U) from φR.hom.app U (π₁.hom.app U a)) • e U m := by
  apply hinj
  have hc := comm_hom_app_apply φR comm U a
  have h1 := he U (π₁.hom.app U a • m)
  have h2 := he U m
  have s1 : (show A₁.obj.obj U from ι₁.val.app U (π₁.hom.app U a • m)) =
      a * (show A₁.obj.obj U from ι₁.val.app U m) :=
    (ι₁.val.app U).hom.map_smul a m
  have s0 : (show A₀.obj.obj (F.op.obj U) from ι₀.val.app (F.op.obj U)
      (π₀.hom.app (F.op.obj U) (φA.hom.app U a) • e U m)) =
      (show A₀.obj.obj (F.op.obj U) from φA.hom.app U a) *
        (show A₀.obj.obj (F.op.obj U) from ι₀.val.app (F.op.obj U) (e U m)) :=
    (ι₀.val.app (F.op.obj U)).hom.map_smul (φA.hom.app U a) (e U m)
  show (show A₀.obj.obj (F.op.obj U) from
      ι₀.val.app (F.op.obj U) (e U (π₁.hom.app U a • m))) =
    (show A₀.obj.obj (F.op.obj U) from
      ι₀.val.app (F.op.obj U)
        ((show R₀.obj.obj (F.op.obj U) from φR.hom.app U (π₁.hom.app U a)) • e U m))
  rw [hc, h1, s0, s1, _root_.map_mul, h2]
  rfl

end

/-- Sections of an isomorphism of sheaves of rings are bijective. -/
theorem bijective_hom_app_of_isIso {𝒞 : Type u₁} [Category.{v₁} 𝒞] {L : GrothendieckTopology 𝒞}
    {P Q : Sheaf L RingCat.{u}} (φ : P ⟶ Q) [IsIso φ] (U : 𝒞ᵒᵖ) :
    Function.Bijective (φ.hom.app U) := by
  have : IsIso φ.hom := (inferInstance : IsIso ((sheafToPresheaf L RingCat.{u}).map φ))
  exact ConcreteCategory.bijective_of_isIso (φ.hom.app U)

/-- Two maps into a module with restricted scalars agree if they agree after a family of
injective maps on sections. -/
theorem hom_ext_of_injective {𝒞 : Type u₁} [Category.{v₁} 𝒞] {L : GrothendieckTopology 𝒞}
    {R R' : Sheaf L RingCat.{u}} {α : R ⟶ R'} {I : SheafOfModules.{u} R}
    {M : SheafOfModules.{u} R'} {d₁ d₂ : I ⟶ (restrictScalars α).obj M} {T : 𝒞ᵒᵖ → Type*}
    (ι : ∀ U, M.val.obj U → T U) (hι : ∀ U, Function.Injective (ι U))
    (h : ∀ U x, ι U (d₁.val.app U x) = ι U (d₂.val.app U x)) : d₁ = d₂ :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun x => hι U (h U x)))

/-- Evaluating a composite of two morphisms of sheaves of modules on a section. -/
theorem comp_val_app_eq {𝒞 : Type u₁} [Category.{v₁} 𝒞] {L : GrothendieckTopology 𝒞}
    {R : Sheaf L RingCat.{u}} {M N P : SheafOfModules.{u} R} (f : M ⟶ N) (g : N ⟶ P)
    {U : 𝒞ᵒᵖ} {x : M.val.obj U} {y : N.val.obj U} {z : P.val.obj U}
    (hf : f.val.app U x = y) (hg : g.val.app U y = z) : (f ≫ g).val.app U x = z := by
  subst hf hg
  rfl

/-- Evaluating a composite of three morphisms of sheaves of modules on a section. -/
theorem comp_comp_val_app_eq {𝒞 : Type u₁} [Category.{v₁} 𝒞] {L : GrothendieckTopology 𝒞}
    {R : Sheaf L RingCat.{u}} {M N P Q : SheafOfModules.{u} R} (f : M ⟶ N) (g : N ⟶ P)
    (h : P ⟶ Q) {U : 𝒞ᵒᵖ} {x : M.val.obj U} {y : N.val.obj U} {z : P.val.obj U}
    {w : Q.val.obj U} (hf : f.val.app U x = y) (hg : g.val.app U y = z) (hh : h.val.app U z = w) :
    (f ≫ g ≫ h).val.app U x = w := by
  subst hf hg hh
  rfl

/-- `congrArg` for a function on the sections of `M` applied to sections of `M` with restricted
scalars; stated generically so that the identification of the two section types is checked once,
on variables. -/
theorem congr_restrictScalars_val {𝒞 : Type u₁} [Category.{v₁} 𝒞] {L : GrothendieckTopology 𝒞}
    {R R' : Sheaf L RingCat.{u}} (α : R ⟶ R') (M : SheafOfModules.{u} R') {U : 𝒞ᵒᵖ} {T : Sort*}
    (f : M.val.obj U → T) {a b : ((restrictScalars α).obj M).val.obj U} (h : a = b) :
    f a = f b :=
  congrArg f h

section Bijective

variable (he : IsIdealLift ι₁ ι₀ φA e) (hinj : ∀ V : Dᵒᵖ, Function.Injective (ι₀.val.app V))
include he hinj

/-- A lift is injective if `ι₁` is injective and `φA` is an isomorphism. -/
theorem IsIdealLift.injective [IsIso φA] (hinj₁ : ∀ U : Cᵒᵖ, Function.Injective (ι₁.val.app U))
    (U : Cᵒᵖ) : Function.Injective (e U) := by
  intro m m' h
  apply hinj₁ U
  apply (bijective_hom_app_of_isIso φA U).1
  show φA.hom.app U (show A₁.obj.obj U from ι₁.val.app U m) =
    φA.hom.app U (show A₁.obj.obj U from ι₁.val.app U m')
  rw [← he U m, ← he U m', h]

variable (comm : π₁ ≫ φR = φA ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map π₀)
include comm

/-- A lift is surjective if `φA` and `φR` are isomorphisms, `ι₀` lands in the kernel of `π₀` and
`ι₁` exhausts the kernel of `π₁`. -/
theorem IsIdealLift.surjective [IsIso φA] [IsIso φR]
    (hzero : ∀ (V : Dᵒᵖ) (n : I₀.val.obj V),
      π₀.hom.app V (show A₀.obj.obj V from ι₀.val.app V n) = 0)
    (huniv : ∀ (U : Cᵒᵖ) (a : A₁.obj.obj U), π₁.hom.app U a = 0 →
      ∃ m : I₁.val.obj U, (show A₁.obj.obj U from ι₁.val.app U m) = a)
    (U : Cᵒᵖ) : Function.Surjective (e U) := by
  intro n
  obtain ⟨a, ha⟩ := (bijective_hom_app_of_isIso φA U).2
    (show A₀.obj.obj (F.op.obj U) from ι₀.val.app (F.op.obj U) n)
  have hc := comm_hom_app_apply φR comm U a
  have h0 : π₁.hom.app U a = 0 := by
    apply (bijective_hom_app_of_isIso φR U).1
    show (show R₀.obj.obj (F.op.obj U) from φR.hom.app U (π₁.hom.app U a)) =
      (show R₀.obj.obj (F.op.obj U) from φR.hom.app U 0)
    rw [hc, _root_.map_zero, ha]
    exact hzero _ n
  obtain ⟨m, hm⟩ := huniv U a h0
  refine ⟨m, hinj _ ?_⟩
  show (show A₀.obj.obj (F.op.obj U) from ι₀.val.app (F.op.obj U) (e U m)) =
    (show A₀.obj.obj (F.op.obj U) from ι₀.val.app (F.op.obj U) n)
  rw [he U m, hm, ha]

end Bijective

/-! ### The lift as a morphism of sheaves of modules -/

section Construction

variable (he : IsIdealLift ι₁ ι₀ φA e)
  (hinj : ∀ V : Dᵒᵖ, Function.Injective (ι₀.val.app V))
  (comm : π₁ ≫ φR = φA ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map π₀)

/-- The lift, as a map of presheaves of `A₁`-modules. -/
def idealLiftRestrict : ((restrictScalars π₁).obj I₁).val ⟶
    ((restrictScalars π₁).obj ((pushforward.{u} φR).obj I₀)).val :=
  PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom (AddMonoidHom.mk' (e U) (he.map_add hinj U))
      naturality U U' p := by
        ext m
        exact he.naturality hinj p m }
    (fun U a m => he.map_smul φR hinj comm U a m)

variable [Presheaf.IsLocallySurjective J π₁.hom]

/-- **The lift `I₁ ⟶ φR_* I₀` of a compatible map of ambient sheaves of rings**: the family
`e_U`, which is `R₁`-linear because it is `A₁`-semilinear and `π₁` is locally surjective. -/
def idealLift : I₁ ⟶ (pushforward.{u} φR).obj I₀ :=
  ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective (J := J) (α := π₁.hom)
    ((pushforward.{u} φR).obj I₀).isSheaf).symm (idealLiftRestrict φR he hinj comm)⟩

theorem idealLift_val_app (U : Cᵒᵖ) (m : I₁.val.obj U) :
    (idealLift φR he hinj comm).val.app U m =
      (show ((pushforward.{u} φR).obj I₀).val.obj U from e U m) :=
  rfl

/-- The lift is an isomorphism when it is bijective on sections. -/
theorem isIso_idealLift (hbij : ∀ U : Cᵒᵖ, Function.Bijective (e U)) :
    IsIso (idealLift φR he hinj comm) :=
  Stacks.SheafOfModules.isIso_of_bijective_val_app_on _ (fun _ => True)
    (fun W => J.superset_covering (fun Y p _ => ⟨Y, 𝟙 Y, p, trivial, Category.id_comp p⟩)
      (J.top_mem W))
    (fun Z _ => hbij (op Z))

end Construction

end SheafOfModules
