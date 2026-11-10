module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjFunctoriality

/-!
# The image of `r_ψ` over a scheme point of the base

Let `ψ : 𝒜 ⟶ ℬ` be a map of quasi-coherent graded algebras on an algebraic space `X`, read over
the scheme points of `X`, and `r_ψ : U(ψ) ⟶ P = Proj_X(𝒜)` the morphism of Tag 085F.  Over a scheme
point `f : T ⟶ X` the base change `T ×_X P` is the scheme `Proj_T(𝒜|_T)`, and a point of it lies
in the image of `r_ψ` exactly when its section of `Proj_T(𝒜|_T)` factors through the morphism
`r_{ψ|_T}` of Tag 07ZG.  This is the form in which the image of `r_ψ` is compared with a closed
subspace of `P` chart by chart.

## Main results

* `AlgebraicGeometry.Space.RelativeProjPoints.sectionOfPoint_fibre`: the section attached to a
  point of `T ×_X P` is that point read through the identification of `T ×_X P` with
  `Proj_T(𝒜|_T)`.
* `AlgebraicGeometry.Space.RelativeProjHomPoints.mem_range_relativeMapSpaceHom_iff`: a point of
  `T ×_X P` lies in the image of `r_ψ` exactly when it factors through `r_{ψ|_T}`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj (relativeProj)
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.Tag07ZGMorphism

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {πP : P ⟶ X} {πQ : Q ⟶ X}

namespace RelativeProjPoints

variable (d : RelativeProjPoints B S hS πP)

/-- A point of the base change `T ×_X P`, read as a point of `P`, lies over `f`. -/
theorem fibre_point_comp (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {a : BigFppfOver B S hS} (k : a ⟶ d.fibre T f) :
    (yoneda.map k ≫ d.fibreToSpace T f) ≫ πP = yoneda.map (k ≫ d.fibreHom T f) ≫ f := by
  rw [Category.assoc, (d.isPullback T f).w, ← Category.assoc, ← CategoryTheory.Functor.map_comp]

/-- **The section attached to a point of `T ×_X P`** is the point itself, read through the
identification of `T ×_X P` with `Proj_T(𝒜|_T)`. -/
theorem sectionOfPoint_fibre (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {a : BigFppfOver B S hS} (k : a ⟶ d.fibre T f) :
    d.sectionOfPoint T f (k ≫ d.fibreHom T f) (yoneda.map k ≫ d.fibreToSpace T f)
        (d.fibre_point_comp T f k) =
      (BigFppfOver.toScheme B S hS).map k ≫ (d.fibreIso T f).hom := by
  rw [sectionOfPoint, pointEquivProjOver_apply]
  congr 2
  refine Yoneda.fullyFaithful.map_injective ((d.isPullback T f).hom_ext
    (d.map_pointEquivOver T f (k ≫ d.fibreHom T f)
      ⟨yoneda.map k ≫ d.fibreToSpace T f, d.fibre_point_comp T f k⟩) ?_)
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    (d.pointEquivOver T f (k ≫ d.fibreHom T f)
      ⟨yoneda.map k ≫ d.fibreToSpace T f, d.fibre_point_comp T f k⟩).2]

end RelativeProjPoints

namespace RelativeProjHomPoints

variable {dP : RelativeProjPoints B S hS πP} {dQ : RelativeProjPoints B S hS πQ}
  (hψ : RelativeProjHomPoints dP dQ)

/-- **A point of `T ×_X P` lies in the image of `r_ψ` exactly when it factors through
`r_{ψ|_T}`.**  For a scheme point `f : T ⟶ X` and a point `k : a ⟶ T ×_X P`, the point of `P`
it defines is `r_ψ` of a point of `U(ψ)` if and only if the morphism `a ⟶ Proj_T(𝒜|_T)` it
defines factors through the morphism `U(ψ|_T) ⟶ Proj_T(𝒜|_T)` of Tag 07ZG. -/
theorem mem_range_relativeMapSpaceHom_iff (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {a : BigFppfOver B S hS} (k : a ⟶ dP.fibre T f) :
    (dP.fibreToSpace T f).app (op a) k ∈ (Subfunctor.range hψ.relativeMapSpaceHom).obj (op a) ↔
      ∃ τ : (BigFppfOver.toScheme B S hS).obj a ⟶ (hψ.hom T f).relativeMapDomain.toScheme,
        τ ≫ relativeMapHom (hψ.hom T f) =
          (BigFppfOver.toScheme B S hS).map k ≫ (dP.fibreIso T f).hom := by
  have hp : (dP.fibreToSpace T f).app (op a) k =
      yonedaEquiv (yoneda.map k ≫ dP.fibreToSpace T f) := by
    rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  rw [hp]
  set r := k ≫ dP.fibreHom T f
  set p := yoneda.map k ≫ dP.fibreToSpace T f
  have hpπ : p ≫ πP = yoneda.map r ≫ f := dP.fibre_point_comp T f k
  have hsecP : ∀ (p' : yoneda.obj a ⟶ P) (hp' : p' = p) (h' : p' ≫ πP = yoneda.map r ≫ f),
      dP.sectionOfPoint T f r p' h' =
        (BigFppfOver.toScheme B S hS).map k ≫ (dP.fibreIso T f).hom := by
    rintro _ rfl _
    exact dP.sectionOfPoint_fibre T f k
  constructor
  · rintro ⟨⟨y, hy⟩, hyr⟩
    set v := yonedaEquiv.symm y with hv
    have hvy : yonedaEquiv v = y := Equiv.apply_symm_apply _ _
    have hvπ : v ≫ πQ = yoneda.map r ≫ f := by
      rw [← hpπ]
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, yonedaEquiv_comp, hvy, ← hyr]
      exact (congrArg (fun φ => φ.app (op a) ⟨y, hy⟩) hψ.relativeMapSpaceHom_comp).symm
    have hx : yonedaEquiv v ∈ hψ.relativeMapSubfunctor.obj (op a) := hvy ▸ hy
    have hd : IsDefinedOn dP dQ hψ.hom T f r v hvπ :=
      (hψ.mem_relativeMapSubfunctor_iff T f r v hvπ).1 hx
    have hpt : pointHomOn dP dQ hψ.hom T f r v hvπ hd = p := yonedaEquiv.injective <| by
      rw [← hψ.app_relativeMapSpaceHom T f r v hvπ hd hx, ← hyr]
      exact congrArg (hψ.relativeMapSpaceHom.app (op a)) (Subtype.ext hvy)
    refine ⟨liftToOpens (dQ.sectionOfPoint T f r v hvπ) (hψ.hom T f).relativeMapDomain hd, ?_⟩
    rw [← sectionOfPoint_pointHomOn]
    exact hsecP _ hpt _
  · rintro ⟨τ, hτ⟩
    set σ := τ ≫ (hψ.hom T f).relativeMapDomain.ι
    have hσ : σ ≫ (relativeProj (dQ.algebra T f)).toBase = (BigFppfOver.toScheme B S hS).map r := by
      rw [Category.assoc, ← relativeMapHom_comp_toBase, ← Category.assoc, hτ, Category.assoc,
        ← dP.fibreHom_comp, ← CategoryTheory.Functor.map_comp]
    set v := ((dQ.pointEquivProjOver T f r).symm ⟨σ, hσ⟩).1
    have hvπ : v ≫ πQ = yoneda.map r ≫ f := ((dQ.pointEquivProjOver T f r).symm ⟨σ, hσ⟩).2
    have hsec : dQ.sectionOfPoint T f r v hvπ = σ :=
      congrArg Subtype.val ((dQ.pointEquivProjOver T f r).apply_symm_apply ⟨σ, hσ⟩)
    have hd : IsDefinedOn dP dQ hψ.hom T f r v hvπ := by
      change dQ.sectionOfPoint T f r v hvπ ⁻¹ᵁ (hψ.hom T f).relativeMapDomain = ⊤
      rw [hsec, Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self, Scheme.Hom.preimage_top]
    have hx : yonedaEquiv v ∈ hψ.relativeMapSubfunctor.obj (op a) :=
      (hψ.mem_relativeMapSubfunctor_iff T f r v hvπ).2 hd
    refine ⟨⟨yonedaEquiv v, hx⟩, ?_⟩
    rw [hψ.app_relativeMapSpaceHom T f r v hvπ hd hx]
    congr 1
    refine dP.eq_of_sectionOfPoint_eq T f r _ _ (pointHomOn_comp dP dQ hψ.hom T f r v hvπ hd) hpπ ?_
    rw [sectionOfPoint_pointHomOn, dP.sectionOfPoint_fibre T f k, ← hτ]
    congr 1
    exact (liftToOpens_unique _ _ hd τ hsec.symm).symm

end RelativeProjHomPoints

end AlgebraicGeometry.Space
