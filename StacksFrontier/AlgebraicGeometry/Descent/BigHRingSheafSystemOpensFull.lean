module

public import StacksFrontier.AlgebraicGeometry.Descent.BigHRingSheafSystemOpensFaithful
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitModuleZariskiPullHom

/-!
# Descent along a family of opens is full, for a system of sheaves of rings

Let `𝓡` be a system of sheaves of rings on the big h category over `S`
(`AlgebraicGeometry.BigHOver.RingSheafSystem`) with the restriction property
(`AlgebraicGeometry.BigHOver.RingSheafSystem.UnitBijective`), and let `W i` be a family of opens of
the underlying scheme of an object `U` that covers it. Then the canonical functor from sheaves of
`𝓡 U`-modules to descent data along the inclusions of the `W i` is full.

Given a morphism of descent data `φ` from `M` to `N`, transpose its components to morphisms
`A i : M ⟶ ι_* ι^* N` along the inclusions `ι` of the `W i`. The unit `N ⟶ ι_* ι^* N` is bijective
on the sections over the opens contained in `W i`, so `A i` is, over those opens, a morphism into
`N` itself. Over an open contained in two members the two local morphisms agree: after
composition with the unit along the inclusion of the overlap both become the transpose of the
common restriction of the two components of `φ` to the overlap, which is what the compatibility
condition of `φ` says. The local morphisms glue (`TopCat.Sheaf.existsUnique_hom_of_localModuleHom`)
to a morphism `M ⟶ N` whose extensions of scalars are the components of `φ`.

## Main definitions

* `AlgebraicGeometry.BigHOver.RingSheafSystem.liftLocal`: a morphism `M ⟶ ι_* ι^* N` along the
  inclusion of an open, read as a morphism `M ⟶ N` over the opens contained in it.

## Main results

* `AlgebraicGeometry.BigHOver.RingSheafSystem.unit_eq_unit_comp_etaG`: the unit along a commuting
  triangle, through `AlgebraicGeometry.BigHOver.RingSheafSystem.etaG`.
* `AlgebraicGeometry.BigHOver.RingSheafSystem.homEquiv_comp_etaG_compInv`: transposition along a
  commuting triangle, through `AlgebraicGeometry.BigHOver.RingSheafSystem.etaG`.
* `AlgebraicGeometry.BigHOver.RingSheafSystem.exists_pull_map_eq_opens`: morphisms of the
  extensions of scalars to the members of an open covering, compatible over the overlaps, are the
  extensions of scalars of one morphism.
* `AlgebraicGeometry.BigHOver.RingSheafSystem.full_toDescentData_opens`: **the descent functor of
  the pseudofunctor of modules of `𝓡` along an open covering is full.**

## Implementation notes

Every equation that mixes the components of a morphism of descent data (typed in the fibres of
the pseudofunctor) with composition of morphisms of sheaves of modules is first proved for
arbitrary arrows and morphisms, and only then instantiated. The compatibility condition of a
morphism of descent data is consumed through Mathlib's transport `pullHom`, by
`CategoryTheory.Pseudofunctor.DescentData.pullHom_hom_eq_of_toDescentData`, which is stated at a
variable pseudofunctor and so never unfolds the pseudofunctor of modules.

## References

* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.BigHOver.RingSheafSystem

universe u

variable {B : BigHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {𝓡 : RingSheafSystem B S hS}

section Triangle

variable (𝓡)

/-- **Transposition along a commuting triangle, through
`AlgebraicGeometry.BigHOver.RingSheafSystem.etaG`.** For `b ≫ a = q`, the transpose along `a` of a
morphism `φ`, followed by the comparison of the pushforward along `a` with the pushforward along
`q`, is the transpose along `q` of the restriction of `φ` along `b`. -/
lemma homEquiv_comp_etaG_compInv {Y X U : BigHOver B S hS} (a : X ⟶ U) (b : Y ⟶ X)
    (q : Y ⟶ U) (hq : b ≫ a = q) {M N : SheafOfModules.{u} (𝓡.ring U)}
    (φ : (𝓡.pull a.op).obj M ⟶ (𝓡.pull a.op).obj N) :
    (𝓡.adj a).homEquiv M _ φ ≫ 𝓡.etaG b a q hq ((𝓡.pull a.op).obj N) ≫
        (𝓡.push q).map (𝓡.compInv a b q hq N) =
      (𝓡.adj q).homEquiv M _
        (𝓡.compHom a b q hq M ≫ (𝓡.pull b.op).map φ ≫ 𝓡.compInv a b q hq N) := by
  rw [𝓡.etaG_comp_push_map, 𝓡.homEquiv_mapComp'_hom]

/-- **The unit along a commuting triangle, through
`AlgebraicGeometry.BigHOver.RingSheafSystem.etaG`.** For `b ≫ a = q`, the unit along `q` is the
unit along `a` followed by the comparison of the pushforward along `a` with the pushforward along
`q`. -/
lemma unit_eq_unit_comp_etaG {Y X U : BigHOver B S hS} (a : X ⟶ U) (b : Y ⟶ X)
    (q : Y ⟶ U) (hq : b ≫ a = q) (N : SheafOfModules.{u} (𝓡.ring U)) :
    (𝓡.adj q).unit.app N = (𝓡.adj a).unit.app N ≫ 𝓡.etaG b a q hq ((𝓡.pull a.op).obj N) ≫
        (𝓡.push q).map (𝓡.compInv a b q hq N) := by
  have h := 𝓡.homEquiv_comp_etaG_compInv a b q hq (𝟙 ((𝓡.pull a.op).obj N))
  rw [CategoryTheory.Functor.map_id, Category.id_comp, compHom_compInv,
    Adjunction.homEquiv_id, Adjunction.homEquiv_id] at h
  exact h.symm

/-- **Two sections whose units along two members agree with the transposes of two compatible
morphisms have the same unit along the overlap.** For `b₁ ≫ a₁ = q = b₂ ≫ a₂` and morphisms
`φ₁`, `φ₂` of the extensions of scalars along `a₁`, `a₂` whose conjugated restrictions along `b₁`,
`b₂` agree, if the units along `a₁` and `a₂` send `y₁` and `y₂` to the values of the transposes of
`φ₁` and `φ₂` at a common section `x`, then the units along `q` of `y₁` and `y₂` agree. -/
lemma unit_app_eq_unit_app_of_conj_eq {Y X₁ X₂ U : BigHOver B S hS} (a₁ : X₁ ⟶ U)
    (a₂ : X₂ ⟶ U) (b₁ : Y ⟶ X₁) (b₂ : Y ⟶ X₂) (q : Y ⟶ U) (h₁ : b₁ ≫ a₁ = q)
    (h₂ : b₂ ≫ a₂ = q) {M N : SheafOfModules.{u} (𝓡.ring U)}
    (φ₁ : (𝓡.pull a₁.op).obj M ⟶ (𝓡.pull a₁.op).obj N)
    (φ₂ : (𝓡.pull a₂.op).obj M ⟶ (𝓡.pull a₂.op).obj N)
    (hc : 𝓡.compHom a₁ b₁ q h₁ M ≫ (𝓡.pull b₁.op).map φ₁ ≫ 𝓡.compInv a₁ b₁ q h₁ N =
      𝓡.compHom a₂ b₂ q h₂ M ≫ (𝓡.pull b₂.op).map φ₂ ≫ 𝓡.compInv a₂ b₂ q h₂ N)
    (T : (((toScheme B S hS).obj U).Opens)ᵒᵖ) (x : ToType (M.val.obj T))
    (y₁ y₂ : ToType (N.val.obj T))
    (hy₁ : ((𝓡.adj a₁).unit.app N).val.app T y₁ = ((𝓡.adj a₁).homEquiv M _ φ₁).val.app T x)
    (hy₂ : ((𝓡.adj a₂).unit.app N).val.app T y₂ = ((𝓡.adj a₂).homEquiv M _ φ₂).val.app T x) :
    ((𝓡.adj q).unit.app N).val.app T y₁ = ((𝓡.adj q).unit.app N).val.app T y₂ := by
  have ti := 𝓡.homEquiv_comp_etaG_compInv a₁ b₁ q h₁ φ₁
  rw [hc] at ti
  have ki := congrFun (coe_app_congr (𝓡.unit_eq_unit_comp_etaG a₁ b₁ q h₁ N) T) y₁
  have kj := congrFun (coe_app_congr (𝓡.unit_eq_unit_comp_etaG a₂ b₂ q h₂ N) T) y₂
  have gi := congrFun (coe_app_congr ti T) x
  have gj := congrFun (coe_app_congr (𝓡.homEquiv_comp_etaG_compInv a₂ b₂ q h₂ φ₂) T) x
  simp only [coe_app_comp, Function.comp_apply] at ki kj gi gj
  rw [ki, kj, hy₁, hy₂, gi, gj]

end Triangle

variable {U : BigHOver B S hS}

section Local

variable (h𝓡 : 𝓡.UnitBijective) (V₀ : ((toScheme B S hS).obj U).Opens)
  {M N : SheafOfModules.{u} (𝓡.ring U)}
  (A : M ⟶ (𝓡.push (opensι B S hS V₀)).obj ((𝓡.pull (opensι B S hS V₀).op).obj N))

/-- The unit along the inclusion of an open, on the sections over an open contained in it, as a
linear equivalence. -/
def unitEquiv (N : SheafOfModules.{u} (𝓡.ring U)) (V : ((toScheme B S hS).obj U).Opens)
    (hV : V ≤ V₀) :
    (N.val.obj (op V)) ≃ₗ[ToType ((𝓡.ring U).obj.obj (op V))]
      (((𝓡.push (opensι B S hS V₀)).obj ((𝓡.pull (opensι B S hS V₀).op).obj N)).val.obj (op V)) :=
  LinearEquiv.ofBijective (((𝓡.adj (opensι B S hS V₀)).unit.app N).val.app (op V)).hom
    (h𝓡 U V₀ N V hV)

/-- The sections map of `liftLocal`. -/
def liftLocalApp (V : ((toScheme B S hS).obj U).Opens) (hV : V ≤ V₀) :
    M.val.obj (op V) ⟶ N.val.obj (op V) :=
  ModuleCat.ofHom ((unitEquiv h𝓡 V₀ N V hV).symm.toLinearMap ∘ₗ (A.val.app (op V)).hom)

/-- The unit along the inclusion of `V₀` sends the sections of `liftLocalApp A` over an open
`V ≤ V₀` to the sections of `A`. -/
lemma unit_app_liftLocalApp (V : ((toScheme B S hS).obj U).Opens) (hV : V ≤ V₀)
    (x : ToType (M.val.obj (op V))) :
    ((𝓡.adj (opensι B S hS V₀)).unit.app N).val.app (op V) (liftLocalApp h𝓡 V₀ A V hV x) =
      A.val.app (op V) x :=
  (unitEquiv h𝓡 V₀ N V hV).apply_symm_apply _

/-- **A morphism `M ⟶ ι_* ι^* N` along the inclusion `ι` of an open `V₀`, read as a morphism
`M ⟶ N` over the opens contained in `V₀`**, for a system with the restriction property. -/
def liftLocal : TopCat.Sheaf.LocalModuleHom M.val N.val V₀ where
  app V hV := liftLocalApp h𝓡 V₀ A V hV
  naturality {V W} hV hWV s := by
    apply (h𝓡 U V₀ N W (hWV.trans hV)).1
    refine (unit_app_liftLocalApp h𝓡 V₀ A W (hWV.trans hV) _).trans ?_
    rw [PresheafOfModules.resLE_apply, PresheafOfModules.resLE_apply,
      PresheafOfModules.naturality_apply]
    refine Eq.trans ?_ (PresheafOfModules.naturality_apply
      ((𝓡.adj (opensι B S hS V₀)).unit.app N).val (homOfLE hWV).op _).symm
    rw [unit_app_liftLocalApp]
    rfl

/-- The sections of `liftLocal A` over an open `V ≤ V₀` are `liftLocalApp A V`. -/
lemma liftLocal_app (V : ((toScheme B S hS).obj U).Opens) (hV : V ≤ V₀) :
    (liftLocal h𝓡 V₀ A).app V hV = liftLocalApp h𝓡 V₀ A V hV :=
  rfl

/-- A morphism `M ⟶ N` which agrees with `liftLocal A` over the opens contained in `V₀` is the
transpose of `A`. -/
lemma comp_unit_eq_of_app_eq {χ : M ⟶ N}
    (hχ : ∀ (V : ((toScheme B S hS).obj U).Opens) (hV : V ≤ V₀),
      χ.val.app (op V) = liftLocalApp h𝓡 V₀ A V hV) :
    χ ≫ (𝓡.adj (opensι B S hS V₀)).unit.app N = A := by
  refine 𝓡.hom_ext_push _ _ fun T hT => ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  change ((𝓡.adj (opensι B S hS V₀)).unit.app N).val.app (op T) (χ.val.app (op T) x) = _
  rw [hχ T hT]
  exact unit_app_liftLocalApp h𝓡 V₀ A T hT x

/-- A morphism whose composite with the unit along the inclusion of an open is the transpose of a
morphism `φ` of the extensions of scalars has extension of scalars `φ`. -/
lemma pull_map_eq_of_comp_unit_eq {M N : SheafOfModules.{u} (𝓡.ring U)} (χ : M ⟶ N)
    (φ : (𝓡.pull (opensι B S hS V₀).op).obj M ⟶ (𝓡.pull (opensι B S hS V₀).op).obj N)
    (e : χ ≫ (𝓡.adj (opensι B S hS V₀)).unit.app N = (𝓡.adj (opensι B S hS V₀)).homEquiv M _ φ) :
    (𝓡.pull (opensι B S hS V₀).op).map χ = φ := by
  apply ((𝓡.adj (opensι B S hS V₀)).homEquiv M _).injective
  rw [Adjunction.homEquiv_unit, ← e]
  exact ((𝓡.adj (opensι B S hS V₀)).unit.naturality χ).symm

end Local

variable {ι : Type u} {W : ι → ((toScheme B S hS).obj U).Opens}
  {M N : SheafOfModules.{u} (𝓡.ring U)}

/-- The local morphisms attached to two members agree over the opens contained in both, as soon as
the two conjugated restrictions of the components to the overlap agree. -/
lemma liftLocalApp_eq (h𝓡 : 𝓡.UnitBijective) (i j : ι)
    (φi : (𝓡.pull (opensι B S hS (W i)).op).obj M ⟶ (𝓡.pull (opensι B S hS (W i)).op).obj N)
    (φj : (𝓡.pull (opensι B S hS (W j)).op).obj M ⟶ (𝓡.pull (opensι B S hS (W j)).op).obj N)
    (hc : 𝓡.compHom (opensι B S hS (W i)) (opensHom B S hS (inf_le_left : W i ⊓ W j ≤ W i))
          (opensι B S hS (W i ⊓ W j)) (opensHom_opensι B S hS _) M ≫
        (𝓡.pull (opensHom B S hS (inf_le_left : W i ⊓ W j ≤ W i)).op).map φi ≫
        𝓡.compInv (opensι B S hS (W i)) (opensHom B S hS (inf_le_left : W i ⊓ W j ≤ W i))
          (opensι B S hS (W i ⊓ W j)) (opensHom_opensι B S hS _) N =
      𝓡.compHom (opensι B S hS (W j)) (opensHom B S hS (inf_le_right : W i ⊓ W j ≤ W j))
          (opensι B S hS (W i ⊓ W j)) (opensHom_opensι B S hS _) M ≫
        (𝓡.pull (opensHom B S hS (inf_le_right : W i ⊓ W j ≤ W j)).op).map φj ≫
        𝓡.compInv (opensι B S hS (W j)) (opensHom B S hS (inf_le_right : W i ⊓ W j ≤ W j))
          (opensι B S hS (W i ⊓ W j)) (opensHom_opensι B S hS _) N)
    (V : ((toScheme B S hS).obj U).Opens) (hVi : V ≤ W i) (hVj : V ≤ W j) :
    liftLocalApp h𝓡 (W i) ((𝓡.adj (opensι B S hS (W i))).homEquiv M _ φi) V hVi =
      liftLocalApp h𝓡 (W j) ((𝓡.adj (opensι B S hS (W j))).homEquiv M _ φj) V hVj := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => (h𝓡 U (W i ⊓ W j) N V (le_inf hVi hVj)).1 ?_)
  exact 𝓡.unit_app_eq_unit_app_of_conj_eq (opensι B S hS (W i)) (opensι B S hS (W j))
    (opensHom B S hS (inf_le_left : W i ⊓ W j ≤ W i))
    (opensHom B S hS (inf_le_right : W i ⊓ W j ≤ W j)) (opensι B S hS (W i ⊓ W j))
    (opensHom_opensι B S hS _) (opensHom_opensι B S hS _) φi φj hc (op V) x _ _
    (unit_app_liftLocalApp h𝓡 (W i) _ V hVi x) (unit_app_liftLocalApp h𝓡 (W j) _ V hVj x)

/-- **Morphisms of extensions of scalars to the members of an open covering, compatible over the
overlaps, are the extensions of scalars of one morphism**, for a system with the restriction
property. -/
lemma exists_pull_map_eq_opens (h𝓡 : 𝓡.UnitBijective) (W : ι → ((toScheme B S hS).obj U).Opens)
    (hW : ⨆ i, W i = ⊤)
    (φ : ∀ i, (𝓡.pull (opensι B S hS (W i)).op).obj M ⟶ (𝓡.pull (opensι B S hS (W i)).op).obj N)
    (hc : ∀ i j, 𝓡.compHom (opensι B S hS (W i)) (opensHom B S hS (inf_le_left : W i ⊓ W j ≤ W i))
          (opensι B S hS (W i ⊓ W j)) (opensHom_opensι B S hS _) M ≫
        (𝓡.pull (opensHom B S hS (inf_le_left : W i ⊓ W j ≤ W i)).op).map (φ i) ≫
        𝓡.compInv (opensι B S hS (W i)) (opensHom B S hS (inf_le_left : W i ⊓ W j ≤ W i))
          (opensι B S hS (W i ⊓ W j)) (opensHom_opensι B S hS _) N =
      𝓡.compHom (opensι B S hS (W j)) (opensHom B S hS (inf_le_right : W i ⊓ W j ≤ W j))
          (opensι B S hS (W i ⊓ W j)) (opensHom_opensι B S hS _) M ≫
        (𝓡.pull (opensHom B S hS (inf_le_right : W i ⊓ W j ≤ W j)).op).map (φ j) ≫
        𝓡.compInv (opensι B S hS (W j)) (opensHom B S hS (inf_le_right : W i ⊓ W j ≤ W j))
          (opensι B S hS (W i ⊓ W j)) (opensHom_opensι B S hS _) N) :
    ∃ χ : M ⟶ N, ∀ i, (𝓡.pull (opensι B S hS (W i)).op).map χ = φ i := by
  obtain ⟨ψ, hψ, -⟩ := TopCat.Sheaf.existsUnique_hom_of_localModuleHom W hW M.val N.val
    N.isSheaf (fun i => liftLocal h𝓡 (W i) ((𝓡.adj (opensι B S hS (W i))).homEquiv M _ (φ i)))
    (fun i j V hVi hVj => liftLocalApp_eq h𝓡 i j (φ i) (φ j) (hc i j) V hVi hVj)
  exact ⟨⟨ψ⟩, fun i => pull_map_eq_of_comp_unit_eq (W i) (⟨ψ⟩ : M ⟶ N) (φ i)
    (comp_unit_eq_of_app_eq h𝓡 (W i) _ (χ := ⟨ψ⟩) (hψ i))⟩

/-- `AlgebraicGeometry.BigHOver.RingSheafSystem.exists_pull_map_eq_opens` with the compatibility
over the overlaps stated through Mathlib's transport
`CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom`, the form in which the compatibility
condition of a morphism of descent data is available. -/
lemma exists_pull_map_eq_opens_of_pullHom (h𝓡 : 𝓡.UnitBijective)
    (W : ι → ((toScheme B S hS).obj U).Opens) (hW : ⨆ i, W i = ⊤)
    (φ : ∀ i, (𝓡.pull (opensι B S hS (W i)).op).obj M ⟶ (𝓡.pull (opensι B S hS (W i)).op).obj N)
    (hc : ∀ i j, Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := 𝓡.modulePseudofunctor)
        (M₁ := M) (M₂ := N) (f₁ := opensι B S hS (W i)) (f₂ := opensι B S hS (W i)) (φ i)
        (opensHom B S hS (inf_le_left : W i ⊓ W j ≤ W i)) (opensι B S hS (W i ⊓ W j))
        (opensι B S hS (W i ⊓ W j)) (opensHom_opensι B S hS _) (opensHom_opensι B S hS _) =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := 𝓡.modulePseudofunctor)
        (M₁ := M) (M₂ := N) (f₁ := opensι B S hS (W j)) (f₂ := opensι B S hS (W j)) (φ j)
        (opensHom B S hS (inf_le_right : W i ⊓ W j ≤ W j)) (opensι B S hS (W i ⊓ W j))
        (opensι B S hS (W i ⊓ W j)) (opensHom_opensι B S hS _) (opensHom_opensι B S hS _)) :
    ∃ χ : M ⟶ N, ∀ i, (𝓡.pull (opensι B S hS (W i)).op).map χ = φ i := by
  refine exists_pull_map_eq_opens h𝓡 W hW φ fun i j => ?_
  have e := hc i j
  rwa [𝓡.pullHom_eq_compHom', 𝓡.pullHom_eq_compHom'] at e

/-- **The descent functor of the pseudofunctor of modules of a system of sheaves of rings along an
open covering is full**, for a system with the restriction property. This is, with
`AlgebraicGeometry.BigHOver.RingSheafSystem.faithful_toDescentData_opens`, the prestack half of
the stack condition along a family of opens. -/
theorem full_toDescentData_opens (h𝓡 : 𝓡.UnitBijective) {ι : Type u}
    (W : ι → ((toScheme B S hS).obj U).Opens) (hW : ⨆ i, W i = ⊤) :
    (𝓡.modulePseudofunctor.toDescentData (fun i => opensι B S hS (W i))).Full where
  map_surjective {M N} φ := by
    obtain ⟨χ, hχ⟩ := exists_pull_map_eq_opens_of_pullHom h𝓡 W hW (fun i => φ.hom i)
      fun i j => Pseudofunctor.DescentData.pullHom_hom_eq_of_toDescentData φ
        (opensι B S hS (W i ⊓ W j)) (opensHom B S hS (inf_le_left : W i ⊓ W j ≤ W i))
        (opensHom B S hS (inf_le_right : W i ⊓ W j ≤ W j)) (opensHom_opensι B S hS _)
        (opensHom_opensι B S hS _)
    exact ⟨χ, Pseudofunctor.DescentData.hom_ext fun i =>
      (Pseudofunctor.toDescentData_map_hom (F := 𝓡.modulePseudofunctor)
        (f := fun i => opensι B S hS (W i)) χ i).trans (hχ i)⟩

end AlgebraicGeometry.BigHOver.RingSheafSystem

end
