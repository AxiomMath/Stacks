module

public import StacksFrontier.AlgebraicGeometry.SectionProduct.Stalk
public import StacksFrontier.AlgebraicGeometry.TensorSectionNonvanishing.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleTrivialization

/-!
# Multiplication by a nonvanishing section is bijective on stalks

Let `X` be a scheme, `F` an `𝒪_X`-module and `f : 𝒪_X ⟶ L` a global section of an `𝒪_X`-module
`L`. This file proves that

`Stacks.TensorSectionNonvanishing.mulRight F f : F ⟶ F ⊗ L`

is **bijective** on the stalk at `x` as soon as `f` is bijective on sections over every open
inside some neighbourhood of `x`. This is the whiskered form of clause 2 of [Stacks, Tag 01CY]:
for `L` invertible and `f` nonvanishing, `f` is an isomorphism over every open inside the
nonvanishing locus (`Stacks.SheafOfModules.isIso_over_of_le_nonvanishingLocus`), and this
survives tensoring by an arbitrary `F`.

## Main definitions

* `Stacks.SectionProduct.BijStalk`: a morphism of `𝒪_X`-modules is bijective on the stalk at `x`.

## Main results

* `Stacks.SectionProduct.pstalkHom_bijective_of_app_bijective_le`: a morphism of presheaves of
  modules that is bijective on sections over every open inside `W` is bijective on the stalk at
  every point of `W`.
* `Stacks.SectionProduct.whiskerLeft_app_bijective`: tensoring on the left preserves
  bijectivity on sections over a fixed open.
* `Stacks.SectionProduct.BijStalk.whiskerLeft`: tensoring on the left preserves bijectivity on
  the stalk at `x`, for a morphism bijective on sections near `x`.
* `Stacks.SectionProduct.bijective_mapFun_mulRight_of_app_bijective`: multiplication by a global
  section `f` is bijective on the stalk at `x` when `f` is bijective on sections near `x`.
* `Stacks.SectionProduct.app_bijective_of_le_nonvanishingLocus`: a section of a module
  trivialised by a pairing is bijective on sections over every open inside its nonvanishing
  locus.

## Implementation notes

At the presheaf level the objectwise tensor product is sectionwise, so
`(PresheafOfModules.tensorHom (𝟙 A) φ).app U` sends `a ⊗ₜ p` to `a ⊗ₜ φ.app U p`, and tensoring
with a bijection is a bijection. Bijectivity on all small enough opens gives bijectivity on the
stalk, the stalk being a filtered colimit over neighbourhoods and the opens inside `W` being
cofinal among those. Sheafification does not change stalks, and the monoidal `tensorLeft` of
`SheafOfModules` is isomorphic to the sheafified sectionwise tensor product by
`Stacks.SheafInternalHom.tensorLeftIso`. No flatness of `F` is needed: `f` is not merely
injective but invertible near `x`.

The hypothesis is phrased as bijectivity of `φ.app (op U)` for every `U ≤ W`, rather than as
`IsIso (φ.over W)`; the two are interchangeable by `Stacks.SheafOfModules.over_app_eq`.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
-/

@[expose] public noncomputable section

open CategoryTheory Category AlgebraicGeometry Opposite MonoidalCategory
  Stacks.SheafOfModules.TensorSheafification
open TopologicalSpace
open scoped TensorProduct

universe u

namespace Stacks.SectionProduct

variable {X : Scheme.{u}}

/-! ### Bijectivity on a stalk from bijectivity on a neighbourhood basis -/

/-- A morphism of presheaves of modules bijective on sections over every open inside `W` is
bijective on the stalk at every point of `W`. -/
theorem pstalkHom_bijective_of_app_bijective_le
    {P Q : PresheafOfModulesOfCommRing.{u} X.presheaf} (ψ : P ⟶ Q) {W : X.Opens} {x : X}
    (hx : x ∈ W) (h : ∀ U : X.Opens, U ≤ W → Function.Bijective (ψ.app (op U))) :
    Function.Bijective (pstalkHom ψ x) := by
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
    obtain ⟨U, hxU, t, rfl⟩ := exists_pgerm_eq P a
    set V : X.Opens := U ⊓ W with hV
    have hxV : x ∈ V := ⟨hxU, hx⟩
    set i : V ⟶ U := homOfLE inf_le_left with hi
    set t' := P.map i.op t with ht'
    have hres : pgerm P V x hxV t' = pgerm P U x hxU t := pgerm_res P i x hxV t
    have hzero : pgerm Q V x hxV (ψ.app (op V) t') = pgerm Q V x hxV 0 := by
      rw [← pstalkHom_pgerm ψ x V hxV t', hres, ha]
      exact (map_zero (pgerm Q V x hxV)).symm
    obtain ⟨W', hxW', j₁, j₂, hj⟩ := pgerm_eq_exists Q x hxV hxV (ψ.app (op V) t') 0 hzero
    have hW'le : W' ≤ W := (leOfHom j₁).trans inf_le_right
    have hnat : ψ.app (op W') (P.map j₁.op t') = Q.map j₁.op (ψ.app (op V) t') :=
      PresheafOfModules.naturality_apply ψ j₁.op t'
    have hker : P.map j₁.op t' = 0 := (h W' hW'le).1 <| by
      rw [hnat, hj, map_zero]
      exact (map_zero _).symm
    have hgerm : pgerm P W' x hxW' (P.map j₁.op t') = pgerm P V x hxV t' :=
      pgerm_res P j₁ x hxW' t'
    rw [← hres, ← hgerm, hker]
    exact map_zero (pgerm P W' x hxW')
  · intro z
    obtain ⟨U, hxU, t, rfl⟩ := exists_pgerm_eq Q z
    set V : X.Opens := U ⊓ W with hV
    have hxV : x ∈ V := ⟨hxU, hx⟩
    set i : V ⟶ U := homOfLE inf_le_left with hi
    obtain ⟨s, hs⟩ := (h V inf_le_right).2 (Q.map i.op t)
    refine ⟨pgerm P V x hxV s, ?_⟩
    rw [pstalkHom_pgerm ψ x V hxV s, hs, pgerm_res Q i x hxV t]

/-! ### Tensoring on the left preserves bijectivity on sections -/

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-- An additive map `F : MA ⊗[R] MP → MA ⊗[R] MQ` sending `a ⊗ₜ p` to `a ⊗ₜ g p` for a bijective
linear map `g : MP →ₗ[R] MQ` is bijective. -/
theorem bijective_of_tmul_eq {R : Type*} [CommRing R] {MA MP MQ : Type*}
    [AddCommGroup MA] [Module R MA] [AddCommGroup MP] [Module R MP]
    [AddCommGroup MQ] [Module R MQ] {g : MP →ₗ[R] MQ} (hg : Function.Bijective g)
    (F : MA ⊗[R] MP → MA ⊗[R] MQ)
    (hFadd : ∀ u v : MA ⊗[R] MP, F (u + v) = F u + F v)
    (hF : ∀ (a : MA) (p : MP), F (a ⊗ₜ[R] p) = a ⊗ₜ[R] g p) :
    Function.Bijective F := by
  classical
  have key : ∀ z : MA ⊗[R] MP,
      F z = TensorProduct.congr (LinearEquiv.refl R MA) (LinearEquiv.ofBijective g hg) z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a p => rw [hF a p, TensorProduct.congr_tmul]; rfl
    | add u v hu hv =>
        rw [hFadd u v, hu, hv]
        exact (map_add (TensorProduct.congr (LinearEquiv.refl R MA)
          (LinearEquiv.ofBijective g hg)) u v).symm
  rw [funext key]
  exact (TensorProduct.congr (LinearEquiv.refl R MA)
    (LinearEquiv.ofBijective g hg)).bijective

/-- If `φ` is bijective on sections over `U`, then so is `A ◁ φ`, for presheaves of modules. -/
theorem whiskerLeft_app_bijective (A : PresheafOfModulesOfCommRing.{u} X.presheaf)
    {P Q : PresheafOfModulesOfCommRing.{u} X.presheaf} (φ : P ⟶ Q) (U : X.Opens)
    (h : Function.Bijective (φ.app (op U))) :
    Function.Bijective ((PresheafOfModules.tensorHom (𝟙 A) φ).app (op U)) :=
  bijective_of_tmul_eq (g := ModuleCat.Hom.hom (φ.app (op U))) h _
    (fun u v => map_add _ u v) (fun _ _ => rfl)

/-! ### Bijectivity on stalks for modules on a scheme -/

/-- The map induced by a morphism of `𝒪_X`-modules on the stalks at `x` is bijective. -/
def BijStalk {M N : X.Modules} (φ : M ⟶ N) (x : X) : Prop :=
  Function.Bijective (Stacks.ModuleStalk.mapFun φ x)

/-- An isomorphism of `𝒪_X`-modules is bijective on every stalk. -/
theorem bijStalk_of_isIso {M N : X.Modules} (φ : M ⟶ N) [IsIso φ] (x : X) : BijStalk φ x :=
  mapFun_bijective_of_isIso φ x

/-- A morphism with a two-sided inverse is bijective on stalks. -/
theorem bijStalk_of_hom_inv {M N : X.Modules} {e : M ⟶ N} {e' : N ⟶ M}
    (h1 : e ≫ e' = 𝟙 M) (h2 : e' ≫ e = 𝟙 N) (x : X) : BijStalk e x := by
  constructor
  · intro a b hab
    have hc := congrArg (Stacks.ModuleStalk.mapFun e' x) hab
    rwa [← Stacks.ModuleStalk.mapFun_comp, ← Stacks.ModuleStalk.mapFun_comp, h1,
      Stacks.ModuleStalk.mapFun_id, Stacks.ModuleStalk.mapFun_id] at hc
  · intro z
    exact ⟨Stacks.ModuleStalk.mapFun e' x z, by
      rw [← Stacks.ModuleStalk.mapFun_comp, h2, Stacks.ModuleStalk.mapFun_id]⟩

/-- The map on stalks induced by a composite is the composite of the induced maps. -/
private theorem mapFun_comp_eq {M N K : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ K) (x : X) :
    Stacks.ModuleStalk.mapFun (φ ≫ ψ) x =
      Stacks.ModuleStalk.mapFun ψ x ∘ Stacks.ModuleStalk.mapFun φ x :=
  funext fun m => Stacks.ModuleStalk.mapFun_comp φ ψ x m

/-- A composite of morphisms bijective on the stalk at `x` is bijective on the stalk at `x`. -/
theorem BijStalk.comp {M N K : X.Modules} {φ : M ⟶ N} {ψ : N ⟶ K} {x : X}
    (hφ : BijStalk φ x) (hψ : BijStalk ψ x) : BijStalk (φ ≫ ψ) x := by
  rw [BijStalk, mapFun_comp_eq]
  exact Function.Bijective.comp hψ hφ

/-- Bijectivity on the stalk at `x` transfers along an equality of morphisms. -/
theorem bijStalk_congr {M N : X.Modules} {φ ψ : M ⟶ N} (h : φ = ψ) {x : X}
    (hφ : BijStalk φ x) : BijStalk ψ x := h ▸ hφ

/-- If `e` and `φ ≫ e` are bijective on the stalk at `x`, then so is `φ`. -/
theorem BijStalk.of_comp_right {M N K : X.Modules} (φ : M ⟶ N) {e : N ⟶ K} {x : X}
    (he : BijStalk e x) (h : BijStalk (φ ≫ e) x) : BijStalk φ x := by
  rw [BijStalk, mapFun_comp_eq] at h
  exact (Function.Bijective.of_comp_iff' he _).mp h

/-- If `e` and `e ≫ ψ` are bijective on the stalk at `x`, then so is `ψ`. -/
theorem BijStalk.of_comp_left {M N K : X.Modules} {e : M ⟶ N} (ψ : N ⟶ K) {x : X}
    (he : BijStalk e x) (h : BijStalk (e ≫ ψ) x) : BijStalk ψ x := by
  rw [BijStalk, mapFun_comp_eq] at h
  exact (Function.Bijective.of_comp_iff _ he).mp h

/-- If a morphism of presheaves of modules is bijective on the stalk at `x`, then so is its
sheafification. -/
theorem bijective_pstalkHom_sheafify_map
    {P Q : PresheafOfModulesOfCommRing.{u} X.presheaf} (φ : P ⟶ Q) (x : X)
    (h : Function.Bijective (pstalkHom φ x)) :
    Function.Bijective
      (pstalkHom ((forgetFun X).map ((sheafify X.presheaf (hStruct X)).map φ)) x) := by
  have hnat : φ ≫ toSheafify X.presheaf (hStruct X) Q =
      toSheafify X.presheaf (hStruct X) P ≫
        (forgetFun X).map ((sheafify X.presheaf (hStruct X)).map φ) :=
    (sheafifyAdjunction X.presheaf (hStruct X)).unit.naturality φ
  have hP := pstalkHom_toSheafify_bijective P x
  have hQ := pstalkHom_toSheafify_bijective Q x
  have hleft : Function.Bijective
      (pstalkHom (toSheafify X.presheaf (hStruct X) Q) x ∘ pstalkHom φ x) := hQ.comp h
  have hcomp : ∀ v, pstalkHom ((forgetFun X).map ((sheafify X.presheaf (hStruct X)).map φ)) x
      (pstalkHom (toSheafify X.presheaf (hStruct X) P) x v) =
      pstalkHom (toSheafify X.presheaf (hStruct X) Q) x (pstalkHom φ x v) := by
    intro v
    have l := pstalkHom_comp (toSheafify X.presheaf (hStruct X) P)
      ((forgetFun X).map ((sheafify X.presheaf (hStruct X)).map φ)) x v
    have r := pstalkHom_comp φ (toSheafify X.presheaf (hStruct X) Q) x v
    have e := congrArg
      (fun α : P ⟶ (forgetFun X).obj ((sheafify X.presheaf (hStruct X)).obj Q) =>
        pstalkHom α x v) hnat
    exact l.symm.trans (e.symm.trans r)
  have hright : Function.Bijective
      (pstalkHom ((forgetFun X).map ((sheafify X.presheaf (hStruct X)).map φ)) x ∘
        pstalkHom (toSheafify X.presheaf (hStruct X) P) x) := by
    have : (pstalkHom ((forgetFun X).map ((sheafify X.presheaf (hStruct X)).map φ)) x ∘
        pstalkHom (toSheafify X.presheaf (hStruct X) P) x) =
        pstalkHom (toSheafify X.presheaf (hStruct X) Q) x ∘ pstalkHom φ x := funext hcomp
    rw [this]
    exact hleft
  exact (Function.Bijective.of_comp_iff _ hP).mp hright

/-- If `f` is bijective on sections over every open inside a neighbourhood `W` of `x`, then
`A ◁ f` is bijective on the stalk at `x`. -/
theorem BijStalk.whiskerLeft (A : X.Modules) {M N : X.Modules} (f : M ⟶ N) {W : X.Opens} {x : X}
    (hx : x ∈ W)
    (hf : ∀ U : X.Opens, U ≤ W → Function.Bijective (((forgetFun X).map f).app (op U))) :
    BijStalk (A ◁ f) x := by
  set e := Stacks.SheafInternalHom.tensorLeftIso X.presheaf (hStruct X) A with he
  have hpre : Function.Bijective
      (pstalkHom (PresheafOfModules.tensorHom (𝟙 A.val) f.val) x) :=
    pstalkHom_bijective_of_app_bijective_le _ hx fun U hU =>
      whiskerLeft_app_bijective A.val f.val U (hf U hU)
  refine BijStalk.of_comp_right _
    (bijStalk_of_hom_inv (e.hom_inv_id_app N) (e.inv_hom_id_app N) x) ?_
  refine bijStalk_congr (e.hom.naturality f).symm ?_
  exact BijStalk.comp (bijStalk_of_hom_inv (e.hom_inv_id_app M) (e.inv_hom_id_app M) x)
    (bijective_pstalkHom_sheafify_map (PresheafOfModules.tensorHom (𝟙 A.val) f.val) x hpre)

/-! ### Multiplication by a section on stalks -/

open Stacks.TensorSectionNonvanishing

/-- If a global section `f` of `L` is bijective on sections over every open inside a
neighbourhood `W` of `x`, then multiplication by `f`, `F ⟶ F ⊗ L`, is bijective on the stalk at
`x`. -/
theorem bijective_mapFun_mulRight_of_app_bijective (F : X.Modules) {L : X.Modules}
    (f : 𝟙_ X.Modules ⟶ L) {W : X.Opens} {x : X} (hx : x ∈ W)
    (hf : ∀ U : X.Opens, U ≤ W → Function.Bijective (((forgetFun X).map f).app (op U))) :
    Function.Bijective (Stacks.ModuleStalk.mapFun (mulRight F f) x) := by
  have hw : BijStalk (F ◁ f) x := BijStalk.whiskerLeft F f hx hf
  have hu : BijStalk ((ρ_ F).inv) x := bijStalk_of_isIso _ x
  exact BijStalk.comp hu hw

/-! ### Clause 2 at a point of the nonvanishing locus -/

section Nonvanishing

open Stacks.SheafOfModules
open Stacks.SheafOfModules.TensorStalkRingedSpace

variable (L N : X.Modules)

/-- A global section `s` of a module `L` trivialised by `ψ : L ⊗ N ≅ 𝒪_X` is bijective on
sections over every open inside its nonvanishing locus. -/
theorem app_bijective_of_le_nonvanishingLocus
    (ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (L)).obj (N)) ≅
        _root_.SheafOfModules.unit _) (s : L.sections)
    {W : X.Opens}
    (hW : ∀ y ∈ W,
      y ∈ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) L s)
    (U : X.Opens) (hU : U ≤ W) :
    Function.Bijective (((forgetFun X).map (L.unitHomEquiv.symm s)).app (op U)) := by
  refine TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective
    ((_root_.SheafOfModules.toSheaf _).map (L.unitHomEquiv.symm s)) U ?_
  intro y hy
  exact (Stacks.SheafOfModules.bijective_stalkFunctor_iff (X := X.toRingedSpace) _ _ _ y).mpr
    (Stacks.SheafOfModules.bijective_stalkMapL_of_mem_nonvanishingLocus
      (X := X.toRingedSpace) ψ s y (hW y (hU hy)))

end Nonvanishing

end Stacks.SectionProduct

end
