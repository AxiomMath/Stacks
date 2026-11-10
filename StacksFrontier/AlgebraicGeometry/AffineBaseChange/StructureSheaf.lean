module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Units
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackComp

/-!
# The base-change morphism carries the structure sheaf to the structure sheaf

For a commutative square of schemes
```
X' --g'--> X
|f'        |f
S' --g-->  S
```
the base-change morphism `g^* f_* ⟶ f'_* (g')^*` of
`Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans` is evaluated here at the
**structure sheaf** of `X`, read as a module over itself. The answer is that it carries the
structure morphism `f^♯` of `f` to the structure morphism `(f')^♯` of `f'`, the two inverse
images of structure sheaves being identified with structure sheaves by
`RingedSpaceModuleAdjunction.modulePullbackObjUnitIso`.

## Main definitions

* `Stacks.AlgebraicGeometry.AffineBaseChange.structureUnitHom` — the structure morphism
  `f^♯ : 𝒪_S ⟶ f_* 𝒪_X` as a morphism of sheaves of `𝒪_S`-modules, which is
  `RingedSpaceModuleAdjunction.structureSheafModuleHom`, ascribed at the `Scheme.Modules`
  spelling of the two categories.
* `Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso` — the identification
  `f^* 𝒪_S ≅ 𝒪_X`, which is `RingedSpaceModuleAdjunction.modulePullbackObjUnitIso`, ascribed
  the same way.

## Main results

* `Stacks.AlgebraicGeometry.AffineBaseChange.baseChangeNatTrans_structureUnitHom` — **the
  base-change morphism at the structure sheaf is the structure morphism**: the inverse image
  along `g` of `f^♯`, followed by the base-change morphism and the direct image along `f'` of
  `(g')^* 𝒪_X ≅ 𝒪_{X'}`, is `𝒪_{S'} ≅ g^* 𝒪_S` followed by `(f')^♯`.
* `Stacks.AlgebraicGeometry.AffineBaseChange.homEquiv_pullbackUnitIso` — `f^♯` is the adjoint
  transpose of `f^* 𝒪_S ≅ 𝒪_X`.
* `Stacks.AlgebraicGeometry.AffineBaseChange.structureUnitHom_comp` — `f^♯` is multiplicative.
* `Stacks.AlgebraicGeometry.AffineBaseChange.structureUnitHom_pushforwardSquareIso` — and
  compatible with the identification of the two composite direct images around the square.
* `Stacks.AlgebraicGeometry.AffineBaseChange.tilde_map_comp_pushforwardTildeIso_inv` —
  **[Stacks, Tag 01I9] at the ring itself is the structure morphism of `Spec φ`**: the
  associated sheaf of a map of `R`-modules `R ⟶ S` sending `1` to `1`, followed by the inverse
  of the comparison of Tag 01I9, is `𝒪_{Spec R} ⟶ (Spec φ)_* 𝒪_{Spec S}`. This is the affine
  half of the same statement; the two together identify the composite of Tag 01I9 and Tag 02KG
  at the module `S` with the canonical map of structure sheaves.

## Implementation notes

The whole content is in `RingedSpaceModuleAdjunction`: there the structure morphism of a
composite is the composite of the structure morphisms **by `rfl`**
(`RingedSpaceModuleAdjunction.structureSheafModuleHom_comp`), because the direct image of
sheaves of modules along a composite of morphisms of ringed spaces is definitionally the
composite of the direct images. So no computation on sections is needed anywhere below: the
proof of the main result is one application of the hom-set bijection of `g^* ⊣ g_*`, the
characterising equation `..AffineBaseChange.unit_comp_pushforward_baseChangeNatTrans` of the
mate, and that `rfl`. The affine statement of the last section is the one place where sections
are computed: there the comparison of Tag 01I9 is characterised only by its effect on the
canonical global sections, and the tilde--global-sections adjunction reduces a morphism out of
`𝒪_{Spec R}` to an `R`-linear map out of `R`.

`structureUnitHom` and `pullbackUnitIso` exist because of the clash the implementation notes
of `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStrictUnit` record: the index
`Stacks.RingedSpace.structureRingSheaf X.toRingedSpace` and the index `X.ringCatSheaf` are
equal by `rfl` and not syntactically, so a goal that applies a `Scheme.Modules` functor to an
object spelled with the first is not type-correct at the `implicit` transparency level and
every `rw`, `simp` and `subst` on it fails. The cure prescribed there is applied: both are
`def`s with an **ascribed** type at the `Scheme.Modules` spelling, every statement below is
written with them, and the crossing happens inside a proof given by `:=`.

## References

* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.AlgebraicGeometry.AffineBaseChange

/-! ### The structure morphism as a morphism of sheaves of modules -/

section StructureUnit

variable {X S : Scheme.{u}}

/-- The structure sheaf of a scheme, read as a module over itself and ascribed at the
`AlgebraicGeometry.Scheme.Modules` spelling of the category it lives in. -/
def unitObj (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit (structureSheafRing X.toRingedSpace)

/-- The structure morphism `f^♯ : 𝒪_S ⟶ f_* 𝒪_X` of a morphism of schemes, read as a morphism
of sheaves of `𝒪_S`-modules between the two structure sheaves regarded as modules over
themselves. This is `RingedSpaceModuleAdjunction.structureSheafModuleHom`, ascribed at the
`Scheme.Modules` spelling of the two categories. -/
def structureUnitHom (h : X ⟶ S) :
    unitObj S ⟶ (Scheme.Modules.pushforward h).obj (unitObj X) :=
  structureSheafModuleHom h.toLRSHom.toShHom

/-- The identification `f^* 𝒪_S ≅ 𝒪_X`, which is
`RingedSpaceModuleAdjunction.modulePullbackObjUnitIso`, ascribed at the `Scheme.Modules`
spelling. -/
def pullbackUnitIso (h : X ⟶ S) :
    (Scheme.Modules.pullback h).obj (unitObj S) ≅ unitObj X :=
  modulePullbackObjUnitIso h.toLRSHom.toShHom

/-- The forward map of `pullbackUnitIso h` is that of
`RingedSpaceModuleAdjunction.modulePullbackObjUnitIso`. -/
@[simp]
theorem pullbackUnitIso_hom (h : X ⟶ S) :
    (pullbackUnitIso h).hom = (modulePullbackObjUnitIso h.toLRSHom.toShHom).hom :=
  rfl

/-- The inverse map of `pullbackUnitIso h` is that of
`RingedSpaceModuleAdjunction.modulePullbackObjUnitIso`. -/
@[simp]
theorem pullbackUnitIso_inv (h : X ⟶ S) :
    (pullbackUnitIso h).inv = (modulePullbackObjUnitIso h.toLRSHom.toShHom).inv :=
  rfl

/-- **The structure morphism is the adjoint transpose of `f^* 𝒪_S ≅ 𝒪_X`.** -/
theorem homEquiv_pullbackUnitIso (h : X ⟶ S) :
    (Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv _ _ (pullbackUnitIso h).hom =
      structureUnitHom h :=
  homEquiv_modulePullbackUnitToUnit h.toLRSHom.toShHom

/-- The structure morphism read through the unit of `h^* ⊣ h_*`. -/
theorem unit_comp_map_pullbackUnitIso (h : X ⟶ S) :
    (Scheme.Modules.pullbackPushforwardAdjunction h).unit.app (unitObj S) ≫
        (Scheme.Modules.pushforward h).map (pullbackUnitIso h).hom =
      structureUnitHom h :=
  (Adjunction.homEquiv_unit (adj := Scheme.Modules.pullbackPushforwardAdjunction h)
      (X := unitObj S) (Y := unitObj X)
      (f := (pullbackUnitIso h).hom)).symm.trans
    (homEquiv_pullbackUnitIso h)

/-- **The structure morphism is multiplicative.** The structure morphism of `h ≫ k` is that of
`k` followed by the direct image along `k` of that of `h`. -/
theorem structureUnitHom_comp {Z : Scheme.{u}} (h : X ⟶ S) (k : S ⟶ Z) :
    structureUnitHom (h ≫ k) =
      structureUnitHom k ≫ (Scheme.Modules.pushforward k).map (structureUnitHom h) :=
  structureSheafModuleHom_comp h.toLRSHom.toShHom k.toLRSHom.toShHom

/-- The comparison of the direct images along two equal morphisms carries the structure
morphism of the one to the structure morphism of the other. -/
theorem structureUnitHom_pushforwardCongr {h₁ h₂ : X ⟶ S} (w : h₁ = h₂) :
    structureUnitHom h₁ ≫
        (Scheme.Modules.pushforwardCongr w).hom.app (unitObj X) =
      structureUnitHom h₂ := by
  subst w
  have h : (Scheme.Modules.pushforwardCongr (rfl : h₁ = h₁)).hom.app (unitObj X) = 𝟙 _ := by
    ext U
    simp
  rw [h, Category.comp_id]

end StructureUnit

/-! ### The base-change morphism at the structure sheaf -/

section BaseChange

variable {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}

/-- The identification of the two composite direct images around a commutative square carries
the structure morphism of one composite to the structure morphism of the other. -/
theorem structureUnitHom_pushforwardSquareIso (w : g' ≫ f = f' ≫ g) :
    structureUnitHom (g' ≫ f) ≫
        (AffinePushforward.pushforwardSquareIso w).hom.app
          (unitObj X') =
      structureUnitHom (f' ≫ g) := by
  have key : (AffinePushforward.pushforwardSquareIso w).hom.app (unitObj X') =
      (Scheme.Modules.pushforwardCongr w).hom.app (unitObj X') := by
    change 𝟙 ((Scheme.Modules.pushforward (g' ≫ f)).obj (unitObj X')) ≫
        (Scheme.Modules.pushforwardCongr w).hom.app (unitObj X') ≫
        𝟙 ((Scheme.Modules.pushforward (f' ≫ g)).obj (unitObj X')) = _
    rw [Category.id_comp, Category.comp_id]
  rw [key]
  exact structureUnitHom_pushforwardCongr w

/-- The same, with the structure morphism of the composite split by
`structureUnitHom_comp` and the result right-associated. -/
theorem structureUnitHom_comp_pushforwardSquareIso (w : g' ≫ f = f' ≫ g) :
    structureUnitHom f ≫ ((Scheme.Modules.pushforward f).map (structureUnitHom g') ≫
        (AffinePushforward.pushforwardSquareIso w).hom.app (unitObj X')) =
      structureUnitHom g ≫ (Scheme.Modules.pushforward g).map (structureUnitHom f') :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg
          (fun u => u ≫ (AffinePushforward.pushforwardSquareIso w).hom.app (unitObj X'))
          (structureUnitHom_comp g' f).symm).trans
      ((structureUnitHom_pushforwardSquareIso w).trans (structureUnitHom_comp f' g)))

/-- Fusing the unit of `(g')^* ⊣ (g')_*` with the direct image of `(g')^* 𝒪_X ≅ 𝒪_{X'}` inside
the direct image along `f`: the result is the direct image of the structure morphism of `g'`. -/
theorem map_unit_comp_map_map_pullbackUnitIso (w : g' ≫ f = f' ≫ g) :
    (Scheme.Modules.pushforward f).map
          ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app (unitObj X)) ≫
        ((Scheme.Modules.pushforward f).map
            ((Scheme.Modules.pushforward g').map (pullbackUnitIso g').hom) ≫
          (AffinePushforward.pushforwardSquareIso w).hom.app (unitObj X')) =
      (Scheme.Modules.pushforward f).map (structureUnitHom g') ≫
        (AffinePushforward.pushforwardSquareIso w).hom.app (unitObj X') :=
  (Category.assoc _ _ _).symm.trans
    (congrArg
      (fun u => u ≫ (AffinePushforward.pushforwardSquareIso w).hom.app (unitObj X'))
      ((Functor.map_comp _ _ _).symm.trans
        (congrArg (fun u => (Scheme.Modules.pushforward f).map u)
          (unit_comp_map_pullbackUnitIso g'))))

/-- The adjoint transpose of the base-change morphism. -/
theorem homEquiv_baseChangeNatTrans (w : g' ≫ f = f' ≫ g) (F : X.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
        ((AffinePushforward.baseChangeNatTrans w).app F) =
      (Scheme.Modules.pushforward f).map
          ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app F) ≫
        (AffinePushforward.pushforwardSquareIso w).hom.app
          ((Scheme.Modules.pullback g').obj F) :=
  (Adjunction.homEquiv_unit (adj := Scheme.Modules.pullbackPushforwardAdjunction g)
      (f := (AffinePushforward.baseChangeNatTrans w).app F)).trans
    (unit_comp_pushforward_baseChangeNatTrans w F)

/-- **The base-change morphism at the structure sheaf is the structure morphism.** The inverse
image along `g` of `f^♯`, followed by the base-change morphism of the square and the direct
image along `f'` of the identification `(g')^* 𝒪_X ≅ 𝒪_{X'}`, is the identification
`g^* 𝒪_S ≅ 𝒪_{S'}` followed by `(f')^♯`. -/
theorem baseChangeNatTrans_structureUnitHom (w : g' ≫ f = f' ≫ g) :
    (Scheme.Modules.pullback g).map (structureUnitHom f) ≫
        (AffinePushforward.baseChangeNatTrans w).app (unitObj X) ≫
          (Scheme.Modules.pushforward f').map (pullbackUnitIso g').hom =
      (pullbackUnitIso g).hom ≫ structureUnitHom f' := by
  have hnat : (AffinePushforward.pushforwardSquareIso w).hom.app
          ((Scheme.Modules.pullback g').obj (unitObj X)) ≫
        (Scheme.Modules.pushforward g).map
          ((Scheme.Modules.pushforward f').map (pullbackUnitIso g').hom) =
      (Scheme.Modules.pushforward f).map
          ((Scheme.Modules.pushforward g').map (pullbackUnitIso g').hom) ≫
        (AffinePushforward.pushforwardSquareIso w).hom.app (unitObj X') :=
    ((AffinePushforward.pushforwardSquareIso w).hom.naturality
      (pullbackUnitIso g').hom).symm
  refine ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).injective ?_
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_naturality_right, homEquiv_baseChangeNatTrans,
    homEquiv_pullbackUnitIso]
  exact (congrArg
        (fun z => structureUnitHom f ≫ (Scheme.Modules.pushforward f).map
          ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app (unitObj X)) ≫ z)
        hnat).trans
    ((congrArg (fun z => structureUnitHom f ≫ z)
        (map_unit_comp_map_map_pullbackUnitIso w)).trans
      (structureUnitHom_comp_pushforwardSquareIso w))

end BaseChange

/-! ### Tag 01I9 at the ring itself -/

section AffineTilde

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- A map of `R`-modules from `R` to `S` with its scalars restricted along `φ` that sends `1`
to `1` is `φ`. -/
theorem hom_apply_of_map_one
    (u : ModuleCat.of R R ⟶ (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S S))
    (hu : u.hom (1 : R) = (1 : S)) (a : R) : u.hom a = φ a := by
  have h0 := u.hom.map_smul a (1 : R)
  rw [hu] at h0
  refine Eq.trans (Eq.trans
    (congrArg u.hom (show a = (a • (1 : R) : R) from (mul_one a).symm)) h0) ?_
  change (CommRingCat.Hom.hom φ) a • (1 : S) = (CommRingCat.Hom.hom φ) a
  exact mul_one _

/-- The associated sheaf of a map of modules, on the canonical global sections. -/
theorem tilde_functor_map_val_app_toOpen {M N : ModuleCat.{u} R} (v : M ⟶ N) (m : M) :
    (((tilde.functor R).map v).val.app (op (⊤ : (Spec R).Opens)))
        ((tilde.toOpen M ⊤).hom m) =
      (tilde.toOpen N ⊤).hom (v.hom m) :=
  congr($(tilde.toOpen_map_app v (⊤ : (Spec R).Opens)).hom m)

/-- The inverse of the comparison of [Stacks, Tag 01I9] on the canonical global sections: it
carries the global section of the associated sheaf of the restricted module represented by `n`
to the global section represented by the same `n`. -/
theorem pushforwardTildeIso_inv_app_toOpen (N : ModuleCat.{u} S) (n : N) :
    ((((pushforwardTildeIso R S φ).app N).inv).val.app (op (⊤ : (Spec R).Opens)))
        ((tilde.toOpen ((ModuleCat.restrictScalars φ.hom).obj N) ⊤).hom n) =
      (tilde.toOpen N (⊤ : (Spec S).Opens)).hom n :=
  (congrArg
      (fun y => ((((pushforwardTildeIso R S φ).app N).inv).val.app
        (op (⊤ : (Spec R).Opens))) y)
      (pushforwardTildeIso_hom_app_toOpen R S φ N n)).symm.trans
    (congrArg
      (fun f : (tilde.functor S ⋙ Scheme.Modules.pushforward (Spec.map φ)).obj N ⟶
          (tilde.functor S ⋙ Scheme.Modules.pushforward (Spec.map φ)).obj N =>
        f.val.app (op (⊤ : (Spec R).Opens)) ((tilde.toOpen N (⊤ : (Spec S).Opens)).hom n))
      ((pushforwardTildeIso R S φ).app N).hom_inv_id)

/-- The structure morphism of a morphism of schemes, on global sections, is the morphism's own
map on global sections. -/
theorem structureUnitHom_val_app_top {X S' : Scheme.{u}} (h : X ⟶ S') (x : Γ(S', ⊤)) :
    ((structureUnitHom h).val.app (op (⊤ : S'.Opens))) x = h.appTop x :=
  (SheafOfModules.unitToPushforwardObjUnit_val_app_apply
    (structureSheafHom h.toLRSHom.toShHom) x).trans rfl

/-- The map on global sections of `Spec φ` is `φ`, read through the canonical global sections
of the structure sheaves. -/
theorem appTop_specMap_toOpen (a : R) :
    (Spec.map φ).appTop ((tilde.toOpen (ModuleCat.of R R) (⊤ : (Spec R).Opens)).hom a) =
      (tilde.toOpen (ModuleCat.of S S) (⊤ : (Spec S).Opens)).hom (φ a) := by
  change (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv a) = (Scheme.ΓSpecIso S).inv (φ a)
  rw [← CategoryTheory.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
    CategoryTheory.comp_apply]

/-- The associated sheaf of a map of `R`-modules `R ⟶ S` sending `1` to `1`, followed by the
inverse of the comparison identifying the direct image along `Spec φ` of the associated sheaf of
`S` with the associated sheaf of `S` restricted to an `R`-module, is the structure morphism
`𝒪_{Spec R} ⟶ (Spec φ)_* 𝒪_{Spec S}`. -/
@[stacks 01I9 "affine_pushforward_tilde at the ring itself: the comparison carries the
structure map of φ to the structure morphism of Spec φ"]
theorem tilde_map_comp_pushforwardTildeIso_inv
    (u : ModuleCat.of R R ⟶ (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S S))
    (hu : u.hom (1 : R) = (1 : S)) :
    (tilde.functor R).map u ≫ ((pushforwardTildeIso R S φ).app (ModuleCat.of S S)).inv =
      structureUnitHom (Spec.map φ) := by
  refine ((tilde.adjunction (R := R)).homEquiv (ModuleCat.of R R) _).injective ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun a => ?_)
  exact ((congrArg
            (fun y => ((((pushforwardTildeIso R S φ).app (ModuleCat.of S S)).inv).val.app
              (op (⊤ : (Spec R).Opens))) y)
            (tilde_functor_map_val_app_toOpen u a)).trans
        ((pushforwardTildeIso_inv_app_toOpen φ (ModuleCat.of S S) (u.hom a)).trans
          (congrArg (fun z => (tilde.toOpen (ModuleCat.of S S) (⊤ : (Spec S).Opens)).hom z)
            (hom_apply_of_map_one φ u hu a)))).trans
    ((structureUnitHom_val_app_top (Spec.map φ) _).trans (appTop_specMap_toOpen φ a)).symm

end AffineTilde

end Stacks.AlgebraicGeometry.AffineBaseChange

end
