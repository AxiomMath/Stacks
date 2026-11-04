module

public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteTypeSubmodule.Affine
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentLocal

/-!
# Finite type is local on the base, and transports along open immersions by range

Three facts about `SheafOfModules.IsFiniteType` for sheaves of modules on a scheme.

The first two concern an open immersion `f : Y ⟶ X` whose range is contained in an open `V` of
`X`: such a morphism factors through `V`, so a statement about `M.restrict V.ι` transports to one
about `M.restrict f`.

The third is locality: a quasi-coherent module which is of finite type on each member of an open
covering is of finite type.

## Main definitions

* `Stacks.AlgebraicGeometry.FiniteTypeSubmodule.liftOpensRange`: the factorisation of an open
  immersion through an open containing its range.

## Main results

* `Stacks.AlgebraicGeometry.FiniteTypeSubmodule.isFiniteType_restrict_of_opensRange_le`: a module
  of finite type on `V` is of finite type after restriction along an open immersion with range
  in `V`.
* `Stacks.AlgebraicGeometry.FiniteTypeSubmodule.isIso_restrictFunctor_map_of_opensRange_le`: a
  morphism of modules which is an isomorphism on `V` is an isomorphism after restriction along an
  open immersion with range in `V`.
* `Stacks.AlgebraicGeometry.FiniteTypeSubmodule.isFiniteType_of_restrict_cover`: a quasi-coherent
  module of finite type on each member of an open covering is of finite type.

## References

* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.FiniteTypeSubmodule

section Transport

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] {V : X.Opens}

/-- An open immersion whose range lies in an open `V` factors through `V`. -/
noncomputable def liftOpensRange (hf : f.opensRange ≤ V) : Y ⟶ V.toScheme :=
  AlgebraicGeometry.IsOpenImmersion.lift V.ι f (by
    rw [Scheme.Opens.range_ι]
    exact hf)

/-- The factorisation `liftOpensRange f hf` of an open immersion is an open immersion. -/
instance (hf : f.opensRange ≤ V) : IsOpenImmersion (liftOpensRange f hf) := by
  dsimp only [liftOpensRange]; infer_instance

/-- The factorisation `liftOpensRange f hf` followed by the inclusion of `V` is `f`. -/
@[simp]
theorem liftOpensRange_ι (hf : f.opensRange ≤ V) : liftOpensRange f hf ≫ V.ι = f :=
  AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _

/-- Restricting along an open immersion whose range lies in `V` is restricting to `V` and then
restricting further. -/
noncomputable def restrictFunctorIsoOfOpensRange (hf : f.opensRange ≤ V) :
    Scheme.Modules.restrictFunctor f ≅
      Scheme.Modules.restrictFunctor V.ι ⋙
        Scheme.Modules.restrictFunctor (liftOpensRange f hf) :=
  (Scheme.Modules.restrictFunctorCongr (liftOpensRange_ι f hf)).symm ≪≫
    Scheme.Modules.restrictFunctorComp (liftOpensRange f hf) V.ι

/-- **Finite type transports along an open immersion by its range.** If a module is of finite
type on an open `V` then it is of finite type after restriction along any open immersion whose
range is contained in `V`. -/
theorem isFiniteType_restrict_of_opensRange_le (M : X.Modules) (hf : f.opensRange ≤ V)
    (hft : (M.restrict V.ι).IsFiniteType) : (M.restrict f).IsFiniteType := by
  have := hft
  have h2 : ((Scheme.Modules.restrictFunctor V.ι ⋙
      Scheme.Modules.restrictFunctor (liftOpensRange f hf)).obj M).IsFiniteType :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_restrict (liftOpensRange f hf) _
  exact Stacks.SheafOfModules.isFiniteType_of_iso.{u}
    ((restrictFunctorIsoOfOpensRange f hf).app M).symm

/-- **Being an isomorphism after restriction transports along an open immersion by its range.**
If `(restrictFunctor V.ι).map φ` is an isomorphism, then so is `(restrictFunctor f).map φ` for
any open immersion `f` whose range is contained in `V`. -/
theorem isIso_restrictFunctor_map_of_opensRange_le {A B : X.Modules} (φ : A ⟶ B)
    (hf : f.opensRange ≤ V) (h : IsIso ((Scheme.Modules.restrictFunctor V.ι).map φ)) :
    IsIso ((Scheme.Modules.restrictFunctor f).map φ) := by
  rw [NatIso.isIso_map_iff (restrictFunctorIsoOfOpensRange f hf) φ]
  have := h
  exact Functor.map_isIso (Scheme.Modules.restrictFunctor (liftOpensRange f hf))
    ((Scheme.Modules.restrictFunctor V.ι).map φ)

end Transport

open Stacks.AlgebraicGeometry.FiniteDirectImageCoherent in
/-- **Being of finite type is local on the base, for a quasi-coherent module.** A quasi-coherent
module which is of finite type on each member of an open covering of the scheme is of finite
type. -/
theorem isFiniteType_of_restrict_cover {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type*} (U : ι → X.Opens) (hcov : iSup U = ⊤)
    (hft : ∀ i, (M.restrict (U i).ι).IsFiniteType) :
    SheafOfModules.IsFiniteType.{u, u, u} M := by
  classical
  refine Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_of_cover_isFiniteTildeOn M
    (ι := {V : X.affineOpens // ∃ i, (V : X.Opens) ≤ U i})
    (fun V => (V.1 : X.Opens)) (IsOpenCover.mk ?_) (fun V => V.1.2) (fun V => ?_)
  · refine top_le_iff.1 fun x _ => ?_
    obtain ⟨i, hi⟩ : ∃ i, x ∈ U i := by
      have : x ∈ (⊤ : X.Opens) := trivial
      rw [← hcov] at this
      exact Opens.mem_iSup.1 this
    obtain ⟨W, hW, hxW, hWU⟩ :=
      (Opens.isBasis_iff_nbhd.1 (X.isBasis_affineOpens)) hi
    exact Opens.mem_iSup.2 ⟨⟨⟨W, hW⟩, ⟨i, hWU⟩⟩, hxW⟩
  · obtain ⟨i, hi⟩ := V.2
    exact isFiniteTildeOn_of_moduleFinite_sections M V.1
      (module_finite_sections_of_isFiniteType_restrict M V.1.2
        (isFiniteType_restrict_of_le M hi (hft i)))

/-! ### Opens of an open subscheme -/

section Subscheme

variable {X : Scheme.{u}}

/-- A quasi-compact open of the ambient scheme cuts out a quasi-compact open of an open
subscheme. -/
theorem isCompact_preimage_ι (V W : X.Opens) (h : IsCompact ((W ⊓ V : X.Opens) : Set X)) :
    IsCompact ((V.ι ⁻¹ᵁ W : V.toScheme.Opens) : Set V.toScheme) := by
  rw [V.ι.isOpenEmbedding.isEmbedding.isCompact_iff, ← Scheme.Hom.coe_image,
    Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  simpa [inf_comm] using h

/-- The inclusion of a quasi-compact open of a quasi-separated scheme is a quasi-compact
morphism. -/
theorem quasiCompact_ι [QuasiSeparatedSpace X] (V : X.Opens)
    (hV : IsCompact (V : Set X)) : QuasiCompact V.ι :=
  ⟨fun O hO hOc => isCompact_preimage_ι V ⟨O, hO⟩
    (QuasiSeparatedSpace.inter_isCompact O V hO hOc V.2 hV)⟩

/-- Finite type on an open `V` is inherited by the open that `V` cuts out of an open
subscheme. -/
theorem isFiniteType_restrict_restrict_of_le (M : X.Modules) (Z V : X.Opens)
    (hft : (M.restrict V.ι).IsFiniteType) :
    ((M.restrict Z.ι).restrict (Z.ι ⁻¹ᵁ V).ι).IsFiniteType := by
  have hrange : ((Z.ι ⁻¹ᵁ V).ι ≫ Z.ι).opensRange ≤ V := by
    rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι,
      Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_le_right
  have h1 : (M.restrict ((Z.ι ⁻¹ᵁ V).ι ≫ Z.ι)).IsFiniteType :=
    isFiniteType_restrict_of_opensRange_le _ M hrange hft
  have := h1
  exact Stacks.SheafOfModules.isFiniteType_of_iso.{u}
    ((Scheme.Modules.restrictFunctorComp (Z.ι ⁻¹ᵁ V).ι Z.ι).app M)

/-- **Being of finite type is local on an open.** A quasi-coherent module which is of finite type
on each of two opens is of finite type on their union. -/
theorem isFiniteType_restrict_sup (M : X.Modules) [M.IsQuasicoherent] (W V : X.Opens)
    (hW : (M.restrict W.ι).IsFiniteType) (hV : (M.restrict V.ι).IsFiniteType) :
    SheafOfModules.IsFiniteType.{u, u, u} (M.restrict (W ⊔ V).ι) := by
  have : (M.restrict (W ⊔ V).ι).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor _ _
  refine isFiniteType_of_restrict_cover (M.restrict (W ⊔ V).ι)
    (fun b : Bool => (W ⊔ V).ι ⁻¹ᵁ cond b W V) ?_ fun b => ?_
  · rw [iSup_bool_eq]
    exact (Scheme.Hom.preimage_sup (W ⊔ V).ι (U := W) (V := V)).symm.trans
      (Scheme.Opens.ι_preimage_self (W ⊔ V))
  · cases b with
    | false => exact isFiniteType_restrict_restrict_of_le M (W ⊔ V) V hV
    | true => exact isFiniteType_restrict_restrict_of_le M (W ⊔ V) W hW

end Subscheme

end Stacks.AlgebraicGeometry.FiniteTypeSubmodule

end
