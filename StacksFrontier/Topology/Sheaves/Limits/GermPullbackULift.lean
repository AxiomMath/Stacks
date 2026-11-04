module

public import StacksFrontier.Topology.Sheaves.Limits.GermPullback
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift

/-!
# Germ pullbacks commute with lifting the universe

Let `𝒢` be a presheaf of types on a space `Y` in `TopCat.{u}`, with sections in `Type u`, and let
`𝒢 ⋙ uliftFunctor` be the same presheaf with its sections lifted to `Type (u + 1)`. Lifting the
universe preserves colimits, so the stalks of the lifted presheaf are the lifted stalks, and the
germs of the lifted presheaf are the germs of `𝒢`. Consequently the sections of the germ pullback
`g⁻¹𝒢` of `StacksFrontier.Topology.Sheaves.Limits.GermPullback` along a continuous map `g : Z → Y`
and those of `g⁻¹(𝒢 ⋙ uliftFunctor)` correspond, compatibly with pulling sections back along a
further map.

## Main definitions

* `TopCat.Presheaf.stalkOfSizeULiftEquiv`: the stalk of the lifted presheaf is the lifted stalk.
* `GermPullback.germsULiftEquiv`: the germs of the lifted presheaf are the germs of `𝒢`.
* `GermPullback.sectionsULiftEquiv`: the sections of `g⁻¹(𝒢 ⋙ uliftFunctor)` are those of
  `g⁻¹𝒢`.

## Main results

* `GermPullback.sectionsULiftEquiv_comap`: the correspondence of sections commutes with
  `GermPullback.comap`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat Opposite

universe u

noncomputable section

namespace TopCat.Presheaf

variable {X : TopCat.{u}} (𝒢 : X.Presheaf (Type u))

/-- The stalk of the universe lift of a presheaf of types is the universe lift of its stalk:
lifting the universe preserves colimits. -/
def stalkOfSizeULiftEquiv (x : X) :
    ULift.{u + 1} (stalkOfSize.{u, u} 𝒢 x) ≃
      stalkOfSize.{u, u + 1} (𝒢 ⋙ uliftFunctor.{u + 1, u}) x :=
  (preservesColimitIso uliftFunctor.{u + 1, u} ((OpenNhds.inclusion x).op ⋙ 𝒢)).toEquiv

/-- The comparison of stalks carries the lifted germ of a section to the germ of the lifted
section. -/
@[simp]
lemma stalkOfSizeULiftEquiv_germOfSize {V : Opens X} (x : X) (hx : x ∈ V) (s : 𝒢.obj (op V)) :
    stalkOfSizeULiftEquiv 𝒢 x (ULift.up (germOfSize.{u, u} 𝒢 V x hx s)) =
      germOfSize.{u, u + 1} (𝒢 ⋙ uliftFunctor.{u + 1, u}) V x hx (ULift.up s) :=
  congrFun (congrArg (fun f => (ConcreteCategory.hom f : _ → _))
    (ι_preservesColimitIso_hom uliftFunctor.{u + 1, u} ((OpenNhds.inclusion x).op ⋙ 𝒢)
      (op ⟨V, hx⟩))) (ULift.up s)

end TopCat.Presheaf

namespace GermPullback

variable {Y Z Z' : TopCat.{u}} (𝒢 : Y.Presheaf (Type u))

/-- The germs of the universe lift of a presheaf of types are the germs of the presheaf. -/
def germsULiftEquiv : Germs.{u, u} 𝒢 ≃ Germs.{u, u + 1} (𝒢 ⋙ uliftFunctor.{u + 1, u}) :=
  Equiv.sigmaCongrRight fun y => Equiv.ulift.symm.trans (Presheaf.stalkOfSizeULiftEquiv 𝒢 y)

/-- The comparison of germs carries the germ of a section to the germ of the lifted section. -/
@[simp]
lemma germsULiftEquiv_mk {V : Opens Y} (y : Y) (hy : y ∈ V) (s : 𝒢.obj (op V)) :
    germsULiftEquiv 𝒢 (⟨y, Presheaf.germOfSize.{u, u} 𝒢 V y hy s⟩ : Germs.{u, u} 𝒢) =
      (⟨y, Presheaf.germOfSize.{u, u + 1} (𝒢 ⋙ uliftFunctor.{u + 1, u}) V y hy (ULift.up s)⟩ :
        Germs.{u, u + 1} (𝒢 ⋙ uliftFunctor.{u + 1, u})) :=
  congrArg (Sigma.mk y) (Presheaf.stalkOfSizeULiftEquiv_germOfSize 𝒢 y hy s)

/-- The inverse comparison of germs carries the germ of a lifted section to the germ of the
section. -/
lemma germsULiftEquiv_symm_mk {V : Opens Y} (y : Y) (hy : y ∈ V)
    (t : (𝒢 ⋙ uliftFunctor.{u + 1, u}).obj (op V)) :
    (germsULiftEquiv 𝒢).symm
        (⟨y, Presheaf.germOfSize.{u, u + 1} (𝒢 ⋙ uliftFunctor.{u + 1, u}) V y hy t⟩ :
          Germs.{u, u + 1} (𝒢 ⋙ uliftFunctor.{u + 1, u})) =
      (⟨y, Presheaf.germOfSize.{u, u} 𝒢 V y hy t.down⟩ : Germs.{u, u} 𝒢) :=
  (Equiv.symm_apply_eq _).2 (germsULiftEquiv_mk 𝒢 y hy t.down).symm

variable {g : Z → Y}

/-- **The sections of the germ pullback of the lifted presheaf are those of the germ pullback of
the presheaf.** A section is a locally germwise family of germs, and the comparison of germs
carries the germs of a section to those of the lifted section and back. -/
def sectionsULiftEquiv (W : Opens Z) :
    (sheaf.{u, u} g 𝒢).presheaf.obj (op W) ≃
      (sheaf.{u, u + 1} g (𝒢 ⋙ uliftFunctor.{u + 1, u})).presheaf.obj (op W) where
  toFun σ := ⟨fun z => germsULiftEquiv 𝒢 (σ.1 z), fun z => by
    obtain ⟨W₀, hz₀, i, V, hV, s, hs⟩ := σ.2 z
    exact ⟨W₀, hz₀, i, V, hV, ULift.up s, fun x => by
      simp only [hs x, germsULiftEquiv_mk]
      rfl⟩⟩
  invFun τ := ⟨fun z => (germsULiftEquiv 𝒢).symm (τ.1 z), fun z => by
    obtain ⟨W₀, hz₀, i, V, hV, t, ht⟩ := τ.2 z
    exact ⟨W₀, hz₀, i, V, hV, t.down, fun x => by
      simp only [ht x, germsULiftEquiv_symm_mk]
      rfl⟩⟩
  left_inv σ := ext fun z => (germsULiftEquiv 𝒢).symm_apply_apply _
  right_inv τ := ext fun z => (germsULiftEquiv 𝒢).apply_symm_apply _

/-- The correspondence of sections commutes with pulling sections back along a further map. -/
lemma sectionsULiftEquiv_comap {g' : Z' → Y} {h : Z' → Z} (hh : Continuous h)
    (hcomp : ∀ z, g' z = g (h z)) {W : Opens Z} {W' : Opens Z'} (hW : ∀ z : W', h z.1 ∈ W)
    (σ : (sheaf.{u, u} g 𝒢).presheaf.obj (op W)) :
    sectionsULiftEquiv 𝒢 W' (comap hh hcomp hW σ) =
      comap hh hcomp hW (sectionsULiftEquiv 𝒢 W σ) :=
  rfl

end GermPullback

end

end
