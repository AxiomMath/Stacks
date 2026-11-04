module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic

/-!
# Quasi-coherent modules are closed under colimits

Let `X` be a scheme.  This file proves that the quasi-coherent `𝒪_X`-modules are closed under
colimits of any shape `K` for which the categories of modules over the rings of sections of the
affine opens of `X` have colimits of shape `K`.  In particular a cokernel of a morphism of
quasi-coherent modules is quasi-coherent, and a coproduct of quasi-coherent modules is
quasi-coherent.

## Main results

* `Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_of_isColimit_spec` is the
  affine case over a spectrum.
* `Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_of_restrict_affineOpens` is
  the locality of quasi-coherence in the form needed here.
* `Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_of_isColimit`: the point of a
  colimit cocone of quasi-coherent modules on an arbitrary scheme is quasi-coherent, recorded
  also as the instance
  `Stacks.AlgebraicGeometry.QuasicoherentColimits.isClosedUnderColimitsOfShape`.
* `Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel` and
  `Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_sigma` are the two
  specializations that the quasi-coherence theory of a sheaf of algebras uses.

## Implementation notes

The affine case is the whole content, and it is a formal consequence of the structure of
`AlgebraicGeometry.tildeEquiv`.  Quasi-coherence on `Spec R` is the essential image of `~` by
`AlgebraicGeometry.essImage_tilde`, so `tildeEquiv` identifies `ModuleCat R` with the full
subcategory of quasi-coherent modules; a diagram of quasi-coherent modules is therefore
isomorphic to `G ⋙ tilde.functor R` for a diagram `G` of modules, and `~`, being a left
adjoint, carries a colimit of `G` to a colimit of that diagram.  The resulting colimit is in
the image of `~`, hence quasi-coherent.

The passage from the affine case to an arbitrary scheme uses that `restrictFunctor` is a left
adjoint, hence preserves colimits, together with the locality of quasi-coherence.  The locality
statement in the form needed here is assembled from
`Stacks.AlgebraicGeometry.AffinePushforward.isQuasicoherent_of_presentations` and
`Stacks.AlgebraicGeometry.AffinePushforward.nonempty_presentation_of_isoSpec`: the former wants
presentations of the restrictions of the module to the members of an open covering, and on an
affine open the latter manufactures one out of quasi-coherence.

No hypothesis of the form `HasColimitsOfShape K X.Modules` is imposed; the statements are about
a colimit cocone that is given, or about `colimit` under a `HasColimit` hypothesis.  What is
assumed is `HasColimitsOfShape K (ModuleCat R)` for the rings `R` that occur, which for the two
shapes used downstream, `WalkingParallelPair` and `Discrete I` with `I : Type u`, is automatic.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe v₂ u₂ u

namespace Stacks.AlgebraicGeometry.QuasicoherentColimits

variable {K : Type u₂} [Category.{v₂} K]

/-! ### The case of a spectrum -/

/-- On a spectrum, the point of a colimit cocone of quasi-coherent modules is
quasi-coherent. -/
@[stacks 01ID "colimits"]
theorem isQuasicoherent_of_isColimit_spec (R : CommRingCat.{u})
    [HasColimitsOfShape K (ModuleCat.{u} R)] {D : K ⥤ (Spec R).Modules}
    (hD : ∀ k, (D.obj k).IsQuasicoherent) {c : Cocone D} (hc : IsColimit c) :
    c.pt.IsQuasicoherent := by
  let P := SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
  let D' : K ⥤ P.FullSubcategory := P.lift D hD
  let G : K ⥤ ModuleCat.{u} R := D' ⋙ (tildeEquiv (R := R)).inverse
  have iso : D ≅ G ⋙ tilde.functor R :=
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft D' (tildeEquiv (R := R)).counitIso.symm) P.ι
  have h₁ := (IsColimit.precomposeHomEquiv iso _).symm
    (isColimitOfPreserves (tilde.functor R) (colimit.isColimit G))
  have h₂ : ((tilde.functor R).obj (colimit G)).IsQuasicoherent := inferInstance
  exact P.prop_of_iso (hc.coconePointUniqueUpToIso h₁).symm h₂

/-! ### Locality of quasi-coherence -/

/-- A module on a scheme whose restriction to every affine open is quasi-coherent is
quasi-coherent. -/
theorem isQuasicoherent_of_restrict_affineOpens {X : Scheme.{u}} (M : X.Modules)
    (h : ∀ V : X.affineOpens,
      ((Scheme.Modules.restrictFunctor (V : X.Opens).ι).obj M).IsQuasicoherent) :
    M.IsQuasicoherent :=
  AffinePushforward.isQuasicoherent_of_presentations M (fun V : X.affineOpens ↦ (V : X.Opens))
    (IsOpenCover.mk (iSup_affineOpens_eq_top X)) fun V ↦
      have := h V
      (AffinePushforward.nonempty_presentation_of_isoSpec V.2.isoSpec _).some

/-! ### A scheme isomorphic to a spectrum -/

/-- If quasi-coherence of colimit points holds on `Y`, then it holds for the restriction along
`f : Y ⟶ X` of the point of a colimit cocone of quasi-coherent modules on `X`. -/
private theorem isQuasicoherent_restrictFunctor_obj_of_isColimit {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] {D : K ⥤ X.Modules}
    (hD : ∀ k, (D.obj k).IsQuasicoherent)
    {c : Cocone D} (hc : IsColimit c)
    (H : ∀ {D' : K ⥤ Y.Modules}, (∀ k, (D'.obj k).IsQuasicoherent) → ∀ {c' : Cocone D'},
      IsColimit c' → c'.pt.IsQuasicoherent) :
    ((Scheme.Modules.restrictFunctor f).obj c.pt).IsQuasicoherent :=
  H (fun k ↦ have := hD k; Scheme.Modules.isQuasicoherent_restrictFunctor f (D.obj k))
    (isColimitOfPreserves (Scheme.Modules.restrictFunctor f) hc)

/-- On a scheme isomorphic to a spectrum, the point of a colimit cocone of quasi-coherent
modules is quasi-coherent. -/
theorem isQuasicoherent_of_isColimit_of_isoSpec {Y : Scheme.{u}} {R : CommRingCat.{u}}
    [HasColimitsOfShape K (ModuleCat.{u} R)] (e : Y ≅ Spec R) {D : K ⥤ Y.Modules}
    (hD : ∀ k, (D.obj k).IsQuasicoherent) {c : Cocone D} (hc : IsColimit c) :
    c.pt.IsQuasicoherent := by
  have key := isQuasicoherent_restrictFunctor_obj_of_isColimit e.inv hD hc
    (isQuasicoherent_of_isColimit_spec R)
  have iso : ((Scheme.Modules.restrictFunctor e.inv).obj c.pt).restrict e.hom ≅ c.pt :=
    ((Scheme.Modules.restrictFunctorComp e.hom e.inv).app c.pt).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr e.hom_inv_id).app c.pt ≪≫
      Scheme.Modules.restrictFunctorId.app c.pt
  have := Scheme.Modules.isQuasicoherent_restrictFunctor e.hom
    ((Scheme.Modules.restrictFunctor e.inv).obj c.pt)
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso iso this

/-! ### An arbitrary scheme -/

section Scheme

variable [∀ R : CommRingCat.{u}, HasColimitsOfShape K (ModuleCat.{u} R)]

/-- **Quasi-coherence is stable under colimits.** The point of a colimit cocone of
quasi-coherent modules on a scheme is quasi-coherent. -/
theorem isQuasicoherent_of_isColimit {X : Scheme.{u}} {D : K ⥤ X.Modules}
    (hD : ∀ k, (D.obj k).IsQuasicoherent) {c : Cocone D} (hc : IsColimit c) :
    c.pt.IsQuasicoherent := by
  refine isQuasicoherent_of_restrict_affineOpens _ fun V ↦ ?_
  exact isQuasicoherent_restrictFunctor_obj_of_isColimit _ hD hc
    (isQuasicoherent_of_isColimit_of_isoSpec V.2.isoSpec)

/-- Quasi-coherence is a property of objects closed under colimits of shape `K`. -/
instance isClosedUnderColimitsOfShape (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderColimitsOfShape K where
  colimitsOfShape_le := by
    rintro M ⟨h⟩
    exact isQuasicoherent_of_isColimit (D := h.diag) h.prop_diag_obj h.isColimit

/-- A colimit of quasi-coherent modules is quasi-coherent. -/
theorem isQuasicoherent_colimit {X : Scheme.{u}} (D : K ⥤ X.Modules) [HasColimit D]
    (hD : ∀ k, (D.obj k).IsQuasicoherent) : (colimit D).IsQuasicoherent :=
  isQuasicoherent_of_isColimit hD (colimit.isColimit D)

end Scheme

/-! ### The two specializations -/

/-- A cokernel of a morphism of quasi-coherent modules is quasi-coherent. -/
instance isQuasicoherent_cokernel {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] : (cokernel φ).IsQuasicoherent :=
  isQuasicoherent_colimit (parallelPair φ 0) fun k ↦ by
    obtain _ | _ := k
    · exact (inferInstance : M.IsQuasicoherent)
    · exact (inferInstance : N.IsQuasicoherent)

/-- A coproduct of quasi-coherent modules is quasi-coherent. -/
@[stacks 01ID "direct sums"]
instance isQuasicoherent_sigma {X : Scheme.{u}} {I : Type u} (M : I → X.Modules)
    [∀ i, (M i).IsQuasicoherent] : (∐ M).IsQuasicoherent :=
  isQuasicoherent_colimit (Discrete.functor M) fun i ↦
    (inferInstance : (M i.as).IsQuasicoherent)

end Stacks.AlgebraicGeometry.QuasicoherentColimits

end
