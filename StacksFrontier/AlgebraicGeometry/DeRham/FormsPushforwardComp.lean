module

public import StacksFrontier.AlgebraicGeometry.DeRham.Functoriality

/-!
# The canonical maps of Section 07HX compose

For morphisms of schemes `a : X'' ⟶ X'` and `b : X' ⟶ X` over compatible bases, the canonical
homomorphism `⋀ Ω_{X/S} ⟶ (a ≫ b)_*(⋀ Ω_{X''/S''})` of Section 07HX of the outer square is the
canonical homomorphism of the right square followed by the direct image along `b` of the
canonical homomorphism of the left square. This is checked on sections, where both sides are
determined by their values on the multiples of the exact wedges.

## Main results

* `AlgebraicGeometry.Scheme.Hom.deRhamFormsPushforwardHom_comp_apply`: the canonical maps
  compose.
* `AlgebraicGeometry.Scheme.Hom.deRhamFormsPushforwardHom_apply_heq`: the canonical maps of
  equal squares agree.

## References

* [Stacks Project, Section 07HX](https://stacks.math.columbia.edu/tag/07HX)
-/

@[expose] public section

open CategoryTheory TopologicalSpace SheafOfModules.GradedAlgebra
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X'' X' X S'' S' S : Scheme.{u}} (a : X'' ⟶ X') (b : X' ⟶ X) (s : X ⟶ S) (s' : X' ⟶ S')
  (s'' : X'' ⟶ S'') (g₁ : S' ⟶ S) (g₂ : S'' ⟶ S')

/-- **The canonical homomorphisms of Section 07HX compose**: along `X'' ⟶ X' ⟶ X`, the canonical
map of the outer square is the canonical map of the right square followed by the pushforward of
the canonical map of the left square. -/
theorem deRhamFormsPushforwardHom_comp_apply (h₁ : b ≫ s = s' ≫ g₁) (h₂ : a ≫ s' = s'' ≫ g₂)
    (h₃ : (a ≫ b) ≫ s = s'' ≫ (g₂ ≫ g₁)) (n : ℕ) (U : (X.Opens)ᵒᵖ)
    (ω : ((deRhamAlgebras s).exteriorPower n).val.obj U) :
    ((deRhamFormsPushforwardHom a s' s'' g₂ h₂).app (n : ℤ)).val.app
        ((opensMap b.toLRSHom.toShHom).op.obj U)
        (((deRhamFormsPushforwardHom b s s' g₁ h₁).app (n : ℤ)).val.app U ω) =
      ((deRhamFormsPushforwardHom (a ≫ b) s s'' (g₂ ≫ g₁) h₃).app (n : ℤ)).val.app U ω := by
  refine SheafOfModules.eq_of_exactWedges (deRhamAlgebras s) n
    (N := (modulePushforward (a ≫ b).toLRSHom.toShHom).obj
      ((deRhamAlgebras s'').exteriorPower n))
    (fun V => AddMonoidHom.comp
      (((deRhamFormsPushforwardHom a s' s'' g₂ h₂).app (n : ℤ)).val.app
        ((opensMap b.toLRSHom.toShHom).op.obj V)).hom.toAddMonoidHom
      (((deRhamFormsPushforwardHom b s s' g₁ h₁).app (n : ℤ)).val.app V).hom.toAddMonoidHom)
    (fun V => (((deRhamFormsPushforwardHom (a ≫ b) s s'' (g₂ ≫ g₁) h₃).app
        (n : ℤ)).val.app V).hom.toAddMonoidHom)
    ?_ ?_ ?_ U ω
  · intro V W i x
    refine Eq.trans (congrArg (fun y =>
      ((deRhamFormsPushforwardHom a s' s'' g₂ h₂).app (n : ℤ)).val.app
        ((opensMap b.toLRSHom.toShHom).op.obj W) y)
      (PresheafOfModules.naturality_apply
        ((deRhamFormsPushforwardHom b s s' g₁ h₁).app (n : ℤ)).val i x)) ?_
    exact PresheafOfModules.naturality_apply
      ((deRhamFormsPushforwardHom a s' s'' g₂ h₂).app (n : ℤ)).val
      ((opensMap b.toLRSHom.toShHom).op.map i) _
  · intro V W i x
    exact PresheafOfModules.naturality_apply
      ((deRhamFormsPushforwardHom (a ≫ b) s s'' (g₂ ≫ g₁) h₃).app (n : ℤ)).val i x
  · intro V c η hη
    obtain ⟨e, rfl⟩ :=
      SheafOfModules.exists_eq_homogeneousProdLeft (deRhamAlgebras s) V n η hη
    -- the opens and the ring maps along the composite
    let bV := (opensMap b.toLRSHom.toShHom).op.obj V
    let abV := (opensMap a.toLRSHom.toShHom).op.obj bV
    refine Eq.trans (congrArg (fun y =>
      ((deRhamFormsPushforwardHom a s' s'' g₂ h₂).app (n : ℤ)).val.app bV y)
      (deRhamFormsPushforwardHom_smul b s s' g₁ h₁ (n : ℤ) V c
        ((deRhamAlgebras s).exterior.toPresheafGradedAlgebra.homogeneousProdLeft V n
          fun i => SheafOfModules.exactOne (deRhamAlgebras s) V (e i)))) ?_
    refine Eq.trans (congrArg (fun y : ((relativeDifferentialFormsAlgebra s').piece
        (n : ℤ)).val.obj bV =>
      ((deRhamFormsPushforwardHom a s' s'' g₂ h₂).app (n : ℤ)).val.app bV
        (@SMul.smul (X'.sheaf.obj.obj bV)
          (((relativeDifferentialFormsAlgebra s').piece (n : ℤ)).val.obj bV) _
          ((b.app V.unop).hom c) y))
      (deRhamFormsPushforwardHom_homogeneousProdLeft b s s' g₁ h₁ V n e)) ?_
    refine Eq.trans (deRhamFormsPushforwardHom_smul a s' s'' g₂ h₂ (n : ℤ) bV
      ((b.app V.unop).hom c) _) ?_
    refine Eq.trans (congrArg (fun y : ((relativeDifferentialFormsAlgebra s'').piece
        (n : ℤ)).val.obj abV =>
      @SMul.smul (X''.sheaf.obj.obj abV)
          (((relativeDifferentialFormsAlgebra s'').piece (n : ℤ)).val.obj abV) _
          ((a.app bV.unop).hom ((b.app V.unop).hom c)) y)
      (deRhamFormsPushforwardHom_homogeneousProdLeft a s' s'' g₂ h₂ bV n
        fun i => (b.app V.unop).hom (e i))) ?_
    refine Eq.symm (Eq.trans (deRhamFormsPushforwardHom_smul (a ≫ b) s s'' (g₂ ≫ g₁) h₃
      (n : ℤ) V c _) ?_)
    refine Eq.trans (congrArg (fun y : ((relativeDifferentialFormsAlgebra s'').piece
        (n : ℤ)).val.obj abV =>
      @SMul.smul (X''.sheaf.obj.obj abV)
          (((relativeDifferentialFormsAlgebra s'').piece (n : ℤ)).val.obj abV) _
          (((a ≫ b).app V.unop).hom c) y)
      (deRhamFormsPushforwardHom_homogeneousProdLeft (a ≫ b) s s'' (g₂ ≫ g₁) h₃ V n e)) ?_
    rfl

/-- The canonical homomorphisms of Section 07HX of equal squares agree on sections, through the
identifications the equalities induce. -/
theorem deRhamFormsPushforwardHom_apply_heq {f₁ f₂ : X' ⟶ X} {s'₁ s'₂ : X' ⟶ S'} {g₁ g₂ : S' ⟶ S}
    (hf : f₁ = f₂) (hs : s'₁ = s'₂) (hg : g₁ = g₂) (h₁ : f₁ ≫ s = s'₁ ≫ g₁)
    (h₂ : f₂ ≫ s = s'₂ ≫ g₂) (n : ℤ) (U : (X.Opens)ᵒᵖ)
    (ω : ((relativeDifferentialFormsAlgebra s).piece n).val.obj U) :
    HEq (((deRhamFormsPushforwardHom f₁ s s'₁ g₁ h₁).app n).val.app U ω)
      (((deRhamFormsPushforwardHom f₂ s s'₂ g₂ h₂).app n).val.app U ω) := by
  subst hf hs hg
  rfl

end AlgebraicGeometry.Scheme.Hom

end
