module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDuality.KInjectiveSections
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCartesian
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleOpenCoverQuasicoherence
public import Mathlib.Algebra.Category.ModuleCat.Descent

/-!
# Sections of `ε^* M̃` over an affine étale object

Let `V` be an object of the small étale site of `Spec A` whose underlying scheme is affine. The
sections of `ε^* M̃` over `V` are the base change `𝒪(V) ⊗_A M`: the canonical map
`b ⊗ m ↦ b • m|_V` is bijective. This is the cartesian condition of a quasi-coherent module on the
small étale site between the affine objects `V` and `⊤`
(`AlgebraicGeometry.SmallEtale.bijective_restrictionBaseChange_of_isQuasicoherentOnSite`, from
Stacks 03DX), combined with the identification `M ≅ Γ(ε^* M̃)` given by the unit of `ε^*T ⊣ Γ`,
which is invertible by Stacks 03DX (1) on the small étale site and by `M ↦ M̃` being fully
faithful.

Since `A ⟶ 𝒪(V)` is flat, `M ↦ (ε^* M̃)(V)` is then an exact functor.

## Main definitions

* `AlgebraicGeometry.AffineEtaleDuality.cartMap`: the map `𝒪(V) ⊗_A M ⟶ (ε^* M̃)(V)`.

## Main results

* `AlgebraicGeometry.AffineEtaleDuality.isIso_cartMap`: it is invertible for `V` affine.
* `AlgebraicGeometry.AffineEtaleDuality.flat_ρc`: `A ⟶ 𝒪(V)` is a flat ring map for `V` affine.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open scoped ChangeOfRings

universe u

namespace ModuleCat

/-- The adjoint-transpose of `g` sends `1 ⊗ n` to `g n`. -/
private lemma homEquiv_symm_apply_one_tmul {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    {N : ModuleCat.{u} R} {M : ModuleCat.{u} S} (g : N ⟶ (restrictScalars f).obj M) (n : N) :
    (((extendRestrictScalarsAdj f).homEquiv N M).symm g).hom ((1 : S) ⊗ₜ[R, f] n) = g n :=
  congrArg (fun h => h.hom n) (((extendRestrictScalarsAdj f).homEquiv N M).apply_symm_apply g)

/-- Extension of scalars along a bijective ring map, applied to an isomorphism onto a restriction
of scalars, is an isomorphism. -/
lemma isIso_homEquiv_symm_of_bijective {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Bijective f) {N : ModuleCat.{u} R} {M : ModuleCat.{u} S}
    (g : N ⟶ (restrictScalars f).obj M) [IsIso g] :
    IsIso (((extendRestrictScalarsAdj f).homEquiv N M).symm g) := by
  let : Module R S := Module.compHom S f
  set φ := ((extendRestrictScalarsAdj f).homEquiv N M).symm g with hφdef
  have hφ1 : ∀ n : N, φ ((1 : S) ⊗ₜ[R, f] n) = g n := homEquiv_symm_apply_one_tmul f g
  have hone : ∀ x : ((extendScalars f).obj N : Type u), ∃ n : N, x = (1 : S) ⊗ₜ[R, f] n := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul s n =>
      obtain ⟨r, rfl⟩ := hf.2 s
      refine ⟨r • n, ?_⟩
      have h1 := ((extendRestrictScalarsAdj f).unit.app N).hom.map_smul r n
      rw [extendRestrictScalarsAdj_unit_app_apply] at h1
      refine Eq.trans ?_ h1.symm
      rw [extendRestrictScalarsAdj_unit_app_apply]
      exact ((ExtendScalars.smul_tmul f (f r) (1 : S) n).trans (by rw [mul_one]; rfl)).symm
    | add x y hx hy =>
      obtain ⟨n, rfl⟩ := hx
      obtain ⟨n', rfl⟩ := hy
      exact ⟨n + n', (tmul_add _ _ _).symm⟩
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun x y hxy => ?_, fun m => ?_⟩
  · obtain ⟨n, rfl⟩ := hone x
    obtain ⟨n', rfl⟩ := hone y
    have h1 : g n = g n' := by
      rw [← hφ1, ← hφ1]
      exact hxy
    rw [(ConcreteCategory.bijective_of_isIso g).1 h1]
  · obtain ⟨n, hn⟩ := (ConcreteCategory.bijective_of_isIso g).2 m
    exact ⟨(1 : S) ⊗ₜ[R, f] n, (hφ1 n).trans hn⟩

end ModuleCat

namespace AlgebraicGeometry.AffineEtaleDuality

variable (A : CommRingCat.{u}) (B : BigEtaleSite.{u}) (hX : B.Contains (Spec A))

/-- **The unit `M ⟶ Γ(ε^* M̃)` is an isomorphism.** -/
instance isIso_epsTAdj_unit_app (M : ModuleCat.{u} A) : IsIso ((epsTAdj A B hX).unit.app M) := by
  have h : (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf) ((tilde.functor A).obj M) :=
    inferInstanceAs (((tilde.functor A).obj M).IsQuasicoherent)
  have : IsIso ((SmallEtale.associatedModuleAdjunction B (Spec A) hX).unit.app
      ((tilde.functor A).obj M)) :=
    SmallEtale.unitIsoOnQuasicoherent B (Spec A) hX ⟨_, h⟩
  change IsIso (tilde.adjunction.unit.app M ≫ moduleSpecΓFunctor.map
    ((SmallEtale.associatedModuleAdjunction B (Spec A) hX).unit.app ((tilde.functor A).obj M)))
  infer_instance

/-- `A ⟶ 𝒪(⊤)` is bijective. -/
lemma bijective_ρtop : Function.Bijective (ρtop A B hX) := by
  have h₁ : IsIso ((SmallEtale.structureMap B (Spec A) hX).hom.app (op ⊤)) :=
    SmallEtale.isIso_structureMap_hom_app B (Spec A) hX (op ⊤)
  exact (ConcreteCategory.bijective_of_isIso
    ((SmallEtale.structureMap B (Spec A) hX).hom.app (op ⊤))).comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).inv)

/-- `ε^* M̃` is quasi-coherent on the small étale site. -/
lemma isQuasicoherentOnSite_epsT (M : ModuleCat.{u} A) :
    ((epsT A B hX).obj M).IsQuasicoherentOnSite :=
  SmallEtale.isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B (Spec A) hX _
    (inferInstanceAs (((tilde.functor A).obj M).IsQuasicoherent))

/-- The underlying scheme of `⊤` is affine. -/
lemma isAffine_top :
    AlgebraicGeometry.IsAffine ((SmallEtale.toScheme B (Spec A) hX).obj (top A B hX)) :=
  isAffineOpen_top (Spec A)

/-- The ring map `A ⟶ 𝒪(V)`, with target the ring of sections read as a commutative ring. -/
def ρc (V : Site A B hX) : A →+* (Rc A B hX).obj (op V) := ρV A B hX V

/-- The sections over `V` of an `𝒪_étale`-module, as a module over the commutative ring
`𝒪(V)`. -/
def evc (V : Site A B hX) (H : Mod A B hX) : ModuleCat.{u} ((Rc A B hX).obj (op V)) :=
  H.val.obj (op V)

/-- **The cartesian map `𝒪(V) ⊗_A M ⟶ (ε^* M̃)(V)`**, `b ⊗ m ↦ b • m|_V`. -/
def cartMap (M : ModuleCat.{u} A) (V : Site A B hX) :
    (ModuleCat.extendScalars (ρc A B hX V)).obj M ⟶ evc A B hX V ((epsT A B hX).obj M) :=
  ((ModuleCat.extendRestrictScalarsAdj (ρc A B hX V)).homEquiv _ _).symm
    (unitSectionAtLinear A B hX M V)

/-- The cartesian map sends `1 ⊗ m` to the restriction `m|_V` of the global section `m`. -/
lemma cartMap_one_tmul (M : ModuleCat.{u} A) (V : Site A B hX) (m : M) :
    (cartMap A B hX M V).hom ((1 : (Rc A B hX).obj (op V)) ⊗ₜ[A, ρc A B hX V] m) =
      unitSectionAt A B hX M V m :=
  ModuleCat.homEquiv_symm_apply_one_tmul _ (unitSectionAtLinear A B hX M V) m

/-- The ring map `A ⟶ 𝒪(⊤)`, with target read as a commutative ring. -/
def ρtopc : A →+* (Rc A B hX).obj (op (top A B hX)) := ρtop A B hX

/-- The ring map `A ⟶ 𝒪(V)` is `A ⟶ 𝒪(⊤)` followed by the restriction `𝒪(⊤) ⟶ 𝒪(V)`. -/
lemma ρc_eq (V : Site A B hX) :
    ρc A B hX V = ((Rc A B hX).map (toTop A B hX V).op).hom.comp (ρtopc A B hX) := rfl

/-- The unit `M ⟶ Γ(ε^* M̃)`, read as an `A`-linear map into the restriction of scalars of the
sections over `⊤`. -/
def unitTop (M : ModuleCat.{u} A) :
    M ⟶ (ModuleCat.restrictScalars (ρtopc A B hX)).obj
      (evc A B hX (top A B hX) ((epsT A B hX).obj M)) :=
  (epsTAdj A B hX).unit.app M

/-- The unit `M ⟶ Γ(ε^* M̃)`, read as an `A`-linear map into the sections over `⊤`, is an
isomorphism. -/
instance isIso_unitTop (M : ModuleCat.{u} A) : IsIso (unitTop A B hX M) :=
  isIso_epsTAdj_unit_app A B hX M

/-- **The cartesian map is an isomorphism over an affine object.** For `V` with affine
underlying scheme, `𝒪(V) ⊗_A M ⟶ (ε^* M̃)(V)` is bijective. -/
theorem isIso_cartMap (M : ModuleCat.{u} A) (V : Site A B hX)
    (hV : AlgebraicGeometry.IsAffine ((SmallEtale.toScheme B (Spec A) hX).obj V)) :
    IsIso (cartMap A B hX M V) := by
  have hrb := SmallEtale.bijective_restrictionBaseChange_of_isQuasicoherentOnSite B (Spec A) hX
    ((epsT A B hX).obj M) (isQuasicoherentOnSite_epsT A B hX M) hV (isAffine_top A B hX)
    (toTop A B hX V)
  have hb : Function.Bijective (ρtopc A B hX) := bijective_ρtop A B hX
  have hu'' : IsIso (((ModuleCat.extendRestrictScalarsAdj (ρtopc A B hX)).homEquiv _ _).symm
      (unitTop A B hX M)) :=
    ModuleCat.isIso_homEquiv_symm_of_bijective (ρtopc A B hX) hb _
  have h2 := ConcreteCategory.bijective_of_isIso
    ((ModuleCat.extendScalars ((Rc A B hX).map (toTop A B hX V).op).hom).map
      (((ModuleCat.extendRestrictScalarsAdj (ρtopc A B hX)).homEquiv _ _).symm
        (unitTop A B hX M)))
  have h1 := ConcreteCategory.bijective_of_isIso
    ((ModuleCat.extendScalarsComp (ρtopc A B hX)
      ((Rc A B hX).map (toTop A B hX V).op).hom).hom.app M)
  let c' : (ModuleCat.extendScalars (ρc A B hX V)).obj M ⟶ evc A B hX V ((epsT A B hX).obj M) :=
    (ModuleCat.extendScalarsComp (ρtopc A B hX)
        ((Rc A B hX).map (toTop A B hX V).op).hom).hom.app M ≫
      (ModuleCat.extendScalars ((Rc A B hX).map (toTop A B hX V).op).hom).map
        (((ModuleCat.extendRestrictScalarsAdj (ρtopc A B hX)).homEquiv _ _).symm
          (unitTop A B hX M)) ≫
      Stacks.PresheafOfModules.restrictionBaseChange
          (R := SmallEtale.commStructurePresheaf B (Spec A) hX)
        ((epsT A B hX).obj M).val (toTop A B hX V).op
  have hc' : Function.Bijective c' := hrb.comp (h2.comp h1)
  have heq : cartMap A B hX M V = c' := by
    refine ModuleCat.ExtendScalars.hom_ext (fun m => (cartMap_one_tmul A B hX M V m).trans ?_)
    have e1 := ModuleCat.extendScalarsComp_hom_app_one_tmul (ρtopc A B hX)
      ((Rc A B hX).map (toTop A B hX V).op).hom M m
    have e2 : (((ModuleCat.extendRestrictScalarsAdj (ρtopc A B hX)).homEquiv _ _).symm
        (unitTop A B hX M)).hom ((1 : (Rc A B hX).obj (op (top A B hX))) ⊗ₜ[A, ρtopc A B hX] m) =
        (unitTop A B hX M).hom m :=
      ModuleCat.homEquiv_symm_apply_one_tmul _ (unitTop A B hX M) m
    have e3 := Stacks.PresheafOfModules.restrictionBaseChange_one_tmul
      (R := SmallEtale.commStructurePresheaf B (Spec A) hX) ((epsT A B hX).obj M).val
      (toTop A B hX V).op ((unitTop A B hX M).hom m)
    have step1 := congrArg (fun x => (Stacks.PresheafOfModules.restrictionBaseChange
      (R := SmallEtale.commStructurePresheaf B (Spec A) hX) ((epsT A B hX).obj M).val
        (toTop A B hX V).op).hom (((ModuleCat.extendScalars
          ((Rc A B hX).map (toTop A B hX V).op).hom).map
        (((ModuleCat.extendRestrictScalarsAdj (ρtopc A B hX)).homEquiv _ _).symm
          (unitTop A B hX M))).hom x)) e1
    have step3 := congrArg (fun x => (Stacks.PresheafOfModules.restrictionBaseChange
      (R := SmallEtale.commStructurePresheaf B (Spec A) hX) ((epsT A B hX).obj M).val
        (toTop A B hX V).op).hom
          ((1 : (Rc A B hX).obj (op V)) ⊗ₜ[(Rc A B hX).obj (op (top A B hX)),
            ((Rc A B hX).map (toTop A B hX V).op).hom] x)) e2
    exact (step1.trans (step3.trans e3)).symm
  rw [ConcreteCategory.isIso_iff_bijective, heq]
  exact hc'

/-- The cartesian map is natural in the module. -/
lemma cartMap_naturality {M M' : ModuleCat.{u} A} (f : M ⟶ M') (V : Site A B hX) :
    (ModuleCat.extendScalars (ρc A B hX V)).map f ≫ cartMap A B hX M' V =
      cartMap A B hX M V ≫ (show evc A B hX V ((epsT A B hX).obj M) ⟶
        evc A B hX V ((epsT A B hX).obj M') from ((epsT A B hX).map f).val.app (op V)) := by
  refine ModuleCat.ExtendScalars.hom_ext (fun m => ?_)
  refine ((congrArg (cartMap A B hX M' V).hom (ModuleCat.ExtendScalars.map_tmul _ f 1 m)).trans
    (cartMap_one_tmul A B hX M' V (f m))).trans ?_
  refine Eq.trans ?_ (congrArg (((epsT A B hX).map f).val.app (op V)).hom
    (cartMap_one_tmul A B hX M V m)).symm
  exact (unitSectionAt_naturality A B hX f V m).symm

/-- **`A ⟶ 𝒪(V)` is flat for `V` affine**: it is the bijection `A ⟶ 𝒪(⊤)` followed by the flat
restriction map of chart rings of the small affine étale site. -/
lemma flat_ρc (V : Site A B hX)
    (hV : AlgebraicGeometry.IsAffine ((SmallEtale.toScheme B (Spec A) hX).obj V)) :
    (ρc A B hX V).Flat := by
  rw [ρc_eq]
  refine RingHom.Flat.comp (RingHom.Flat.of_bijective (bijective_ρtop A B hX)) ?_
  exact SmallEtale.flat_affineChartRings_map B (Spec A) hX
    (U := ⟨V, hV⟩) (V := ⟨top A B hX, isAffine_top A B hX⟩)
    (ObjectProperty.homMk (toTop A B hX V))

/-- The cartesian map as an isomorphism, for `V` affine. -/
def cartIso (M : ModuleCat.{u} A) (V : Site A B hX)
    (hV : AlgebraicGeometry.IsAffine ((SmallEtale.toScheme B (Spec A) hX).obj V)) :
    (ModuleCat.extendScalars (ρc A B hX V)).obj M ≅ evc A B hX V ((epsT A B hX).obj M) :=
  @asIso _ _ _ _ (cartMap A B hX M V) (isIso_cartMap A B hX M V hV)

/-- The forward map of `cartIso` is the cartesian map `cartMap`. -/
lemma cartIso_hom (M : ModuleCat.{u} A) (V : Site A B hX)
    (hV : AlgebraicGeometry.IsAffine ((SmallEtale.toScheme B (Spec A) hX).obj V)) :
    (cartIso A B hX M V hV).hom = cartMap A B hX M V := rfl

/-- **`M ↦ (ε^* M̃)(V)` is base change along `A ⟶ 𝒪(V)`**, for `V` affine, naturally in `M`. -/
def cartNatIso (V : Site A B hX)
    (hV : AlgebraicGeometry.IsAffine ((SmallEtale.toScheme B (Spec A) hX).obj V)) :
    ModuleCat.extendScalars (ρc A B hX V) ⋙ ModuleCat.restrictScalars (ρc A B hX V) ≅
      epsT A B hX ⋙ secA A B hX V :=
  NatIso.ofComponents
    (fun M => (ModuleCat.restrictScalars (ρc A B hX V)).mapIso (cartIso A B hX M V hV))
    (fun {_ _} f =>
      (congrArg (ModuleCat.restrictScalars (ρc A B hX V)).map (cartMap_naturality A B hX f V)))

/-- The component of `cartNatIso` at `M` is the cartesian map `cartMap`, viewed as an `A`-linear
map. -/
lemma cartNatIso_hom_app (V : Site A B hX)
    (hV : AlgebraicGeometry.IsAffine ((SmallEtale.toScheme B (Spec A) hX).obj V))
    (M : ModuleCat.{u} A) :
    (cartNatIso A B hX V hV).hom.app M =
      (ModuleCat.restrictScalars (ρc A B hX V)).map (cartMap A B hX M V) := rfl

/-- `M ↦ (ε^* M̃)(V)` preserves finite limits for `V` affine. -/
lemma preservesFiniteLimits_epsT_secA (V : Site A B hX)
    (hV : AlgebraicGeometry.IsAffine ((SmallEtale.toScheme B (Spec A) hX).obj V)) :
    PreservesFiniteLimits (epsT A B hX ⋙ secA A B hX V) := by
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat (flat_ρc A B hX V hV)
  have : PreservesFiniteLimits (ModuleCat.extendScalars (ρc A B hX V) ⋙
      ModuleCat.restrictScalars (ρc A B hX V)) := comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_natIso (cartNatIso A B hX V hV)

/-- `M ↦ (ε^* M̃)(V)` preserves finite colimits for `V` affine. -/
lemma preservesFiniteColimits_epsT_secA (V : Site A B hX)
    (hV : AlgebraicGeometry.IsAffine ((SmallEtale.toScheme B (Spec A) hX).obj V)) :
    PreservesFiniteColimits (epsT A B hX ⋙ secA A B hX V) := by
  have : PreservesColimitsOfSize.{0, 0} (ModuleCat.extendScalars (ρc A B hX V)) :=
    (ModuleCat.extendRestrictScalarsAdj (ρc A B hX V)).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits (ModuleCat.extendScalars (ρc A B hX V)) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  have : PreservesFiniteColimits (ModuleCat.extendScalars (ρc A B hX V) ⋙
      ModuleCat.restrictScalars (ρc A B hX V)) := comp_preservesFiniteColimits _ _
  exact preservesFiniteColimits_of_natIso (cartNatIso A B hX V hV)

end AlgebraicGeometry.AffineEtaleDuality

end
