module

public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.AffineSectionAlgebra
public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.HomExtOfAlgebraPullback
public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.OnePointHom
public import StacksFrontier.AlgebraicGeometry.SectionRingBaseChange.AffineBaseChange

/-!
# Over a one-point base, a morphism of deformations is determined by its section ring map

Let `φ, ψ : D₁ ⟶ D₂` be morphisms of admissible deformations of a polarized family over the same
base map, with `S'₂` a one-point scheme (the spectrum of an Artinian local ring). On such a base a
morphism of `𝒪`-modules is determined by its global sections, so the sheaf-level algebra map
`g^* 𝒜'(D₂) ⟶ 𝒜'(D₁)` of [Stacks, Tag 0D4F] is determined by the homomorphism of graded rings of
global sections; by `Hom.ext_of_algebraPullbackSheafHom` so is the morphism itself.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjBridge.modules_hom_ext_of_val_app_top`
* `Stacks.AlgebraicGeometry.SectionRingBaseChange.tailPushApp_app_top`,
  `Stacks.AlgebraicGeometry.SectionRingBaseChange.tailPullbackHom_app_heq`
* `PolarizedFamily.AdmissibleDeformation.Hom.ext_of_sectionRingHom`, in the namespace
  `Stacks.AlgebraicGeometry.ProjectiveDeformation`

## References

* [Stacks Project, Tag 0D4F](https://stacks.math.columbia.edu/tag/0D4F)
-/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.SectionAlgebra

universe u

@[expose] public noncomputable section

namespace Stacks.AlgebraicGeometry.RelativeProjBridge

variable {X : Scheme.{u}} [Subsingleton X] {M N : X.Modules}

/-- On a scheme with at most one point, a morphism of `𝒪_X`-modules is determined by its global
sections. -/
theorem modules_hom_ext_of_val_app_top {f g : M ⟶ N}
    (h : ∀ x, f.val.app (op ⊤) x = g.val.app (op ⊤) x) : f = g := by
  have : Subsingleton X.toRingedSpace.carrier := ‹Subsingleton X›
  apply (Scheme.Modules.fullyFaithfulToPresheafOfModules (X := X)).map_injective
  apply (Functor.FullyFaithful.ofFullyFaithful
    (Stacks.Cohomology.SubsingletonSections.evaluationTop X.toRingedSpace)).map_injective
  ext x
  exact h x

end Stacks.AlgebraicGeometry.RelativeProjBridge

namespace Stacks.AlgebraicGeometry.SectionRingBaseChange

variable {Y' Y T' T : Scheme.{u}} (q : Y' ⟶ Y) (g : Y ⟶ T) (g' : Y' ⟶ T') (h : T' ⟶ T)
  (w : q ≫ g = g' ≫ h) [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
  (M : Y.Modules) [Stacks.Ample.IsInvertibleModule Y M]
  (M' : Y'.Modules) [Stacks.Ample.IsInvertibleModule Y' M']
  (ε : (Scheme.Modules.pullback q).obj M ≅ M') (e : ℕ) (he : 0 < e)

/-- On global sections, the map of tail truncations into the direct image is the degreewise map
`tailMapApp` of the homomorphism of global section rings. -/
theorem tailPushApp_app_top (n : ℤ)
    (a : (tailPiece (Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.pushforwardGradedAlgebra g
      (Stacks.RelativeAmple.laurentPowers M)) e n).val.obj (op ⊤)) :
    (tailPushApp q g g' h w M M' ε e he n).val.app (op ⊤) a =
      tailMapApp _ _ e e he he le_rfl ⊤ ⊤ (h.appLE ⊤ ⊤ le_rfl).hom
        (squarePieceMap q g g' h w M M' ε ⊤ ⊤ le_rfl) n a := by
  refine (tailPushApp_app q g g' h w M M' ε e he n ⊤ a).trans ?_
  refine (ConcreteCategory.congr_hom
    ((tailPiece (Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.pushforwardGradedAlgebra g'
      (Stacks.RelativeAmple.laurentPowers M')) e n).val.map_id (op (h ⁻¹ᵁ ⊤))) _).symm.trans ?_
  refine (map_tailMapApp (le_rfl : (⊤ : T'.Opens) ≤ h ⁻¹ᵁ ⊤) _ _ n a).trans ?_
  have hρ : ((T'.ringCatSheaf.obj.map (homOfLE (le_rfl : (⊤ : T'.Opens) ≤ h ⁻¹ᵁ ⊤)).op).hom.comp
      (pullRingHom h ⊤)) = (h.appLE ⊤ ⊤ le_rfl).hom := rfl
  have hΦ : (fun m => (ConcreteCategory.hom
      (((Stacks.AlgebraicGeometry.PushforwardGradedAlgebra.pushforwardGradedAlgebra g'
        (Stacks.RelativeAmple.laurentPowers M')).piece m).val.map
          (homOfLE (le_rfl : (⊤ : T'.Opens) ≤ h ⁻¹ᵁ ⊤)).op)).toAddMonoidHom.comp
      (squarePieceMap q g g' h w M M' ε ⊤ (h ⁻¹ᵁ ⊤) le_rfl m)) =
      squarePieceMap q g g' h w M M' ε ⊤ ⊤ le_rfl := by
    funext m
    exact AddMonoidHom.ext fun y => map_sectionPull q M M' ε (g ⁻¹ᵁ ⊤) m
      (preimage_le_preimage q g g' h w ⊤ (h ⁻¹ᵁ ⊤) le_rfl) (g'.preimage_mono le_rfl) y
  exact congrArg₂ (fun ρ Φ => tailMapApp _ _ e e he he le_rfl ⊤ ⊤ ρ Φ n a) hρ hΦ


/-- **Over a one-point base, the transposed map of tail truncations is determined by its global
sections**: two squares over equal base maps whose degreewise maps of global sections agree have
the same transposed maps, degree by degree. -/
theorem tailPullbackHom_app_heq [Subsingleton T] {h₁ h₂ : T' ⟶ T} (hh : h₁ = h₂) {q₁ q₂ : Y' ⟶ Y}
    (w₁ : q₁ ≫ g = g' ≫ h₁) (w₂ : q₂ ≫ g = g' ≫ h₂)
    (ε₁ : (Scheme.Modules.pullback q₁).obj M ≅ M') (ε₂ : (Scheme.Modules.pullback q₂).obj M ≅ M')
    (key : ∀ (n : ℤ) a,
      tailMapApp _ _ e e he he le_rfl ⊤ ⊤ (h₁.appLE ⊤ ⊤ le_rfl).hom
        (squarePieceMap q₁ g g' h₁ w₁ M M' ε₁ ⊤ ⊤ le_rfl) n a =
      tailMapApp _ _ e e he he le_rfl ⊤ ⊤ (h₂.appLE ⊤ ⊤ le_rfl).hom
        (squarePieceMap q₂ g g' h₂ w₂ M M' ε₂ ⊤ ⊤ le_rfl) n a) (n : ℤ) :
    HEq ((tailPullbackHom q₁ g g' h₁ w₁ M M' ε₁ e he).app n)
      ((tailPullbackHom q₂ g g' h₂ w₂ M M' ε₂ e he).app n) := by
  subst hh
  refine heq_of_eq (congrArg ((Scheme.Modules.pullbackPushforwardAdjunction h₁).homEquiv _ _).symm
    (Stacks.AlgebraicGeometry.RelativeProjBridge.modules_hom_ext_of_val_app_top fun a => ?_))
  exact (tailPushApp_app_top q₁ g g' h₁ w₁ M M' ε₁ e he n a).trans
    ((key n a).trans (tailPushApp_app_top q₂ g g' h₁ w₂ M M' ε₂ e he n a).symm)

end Stacks.AlgebraicGeometry.SectionRingBaseChange

namespace Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom

/-- Two homomorphisms of graded algebras out of pullbacks along equal morphisms agree as soon as
they agree degree by degree. -/
theorem heq_of_app_heq {S₁ S₂ : Scheme.{u}} {g₁ g₂ : S₁ ⟶ S₂} (hg : g₁ = g₂)
    {A : SheafGradedAlgebra S₂} {A' : SheafGradedAlgebra S₁}
    (γ₁ : SheafGradedAlgebraHom (A.pullback g₁) A') (γ₂ : SheafGradedAlgebraHom (A.pullback g₂) A')
    (h : ∀ n, HEq (γ₁.app n) (γ₂.app n)) : HEq γ₁ γ₂ := by
  subst hg
  cases γ₁
  cases γ₂
  congr
  funext n
  exact eq_of_heq (h n)

end Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom

namespace Stacks.AlgebraicGeometry.ProjectiveDeformation.PolarizedFamily.AdmissibleDeformation.Hom

open Stacks.AlgebraicGeometry.SectionRingBaseChange

variable {P : PolarizedFamily.{u}} {D₁ D₂ : P.AdmissibleDeformation}

/-- **Over a one-point base, a morphism of admissible deformations is determined by its base map
and its homomorphism of graded rings of global sections**: on such a base the sheaf-level algebra
map is determined by its global sections. -/
theorem ext_of_sectionRingHom [Subsingleton D₂.S'] (φ ψ : Hom D₁ D₂) (hbase : φ.base = ψ.base)
    (h : sectionRingHom φ = sectionRingHom ψ) : φ = ψ := by
  have := D₁.finitePresentation.quasiCompact
  have := D₁.finitePresentation.quasiSeparated
  have := D₂.finitePresentation.quasiCompact
  have := D₂.finitePresentation.quasiSeparated
  refine ext_of_algebraPullbackSheafHom φ ψ hbase ?_
  have key : ∀ (n : ℤ) a,
      tailMapApp _ _ P.degreeBound P.degreeBound P.degreeBound_pos P.degreeBound_pos le_rfl ⊤ ⊤
        (φ.base.appLE ⊤ ⊤ le_rfl).hom (squarePieceMap φ.total D₂.f' D₁.f' φ.base φ.isPullback.w
          D₂.L' D₁.L' φ.polarization ⊤ ⊤ le_rfl) n a =
      tailMapApp _ _ P.degreeBound P.degreeBound P.degreeBound_pos P.degreeBound_pos le_rfl ⊤ ⊤
        (ψ.base.appLE ⊤ ⊤ le_rfl).hom (squarePieceMap ψ.total D₂.f' D₁.f' ψ.base ψ.isPullback.w
          D₂.L' D₁.L' ψ.polarization ⊤ ⊤ le_rfl) n a := by
    intro n a
    by_cases hn : 0 ≤ n
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      have hm := DFunLike.congr_fun h (DirectSum.of _ m a)
      change squareRingHom _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (DirectSum.of _ m a) =
        squareRingHom _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (DirectSum.of _ m a) at hm
      exact DirectSum.of_injective m
        ((squareRingHom_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a).symm.trans
          (hm.trans (squareRingHom_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a)))
    · have h0 : ¬ n = 0 := by omega
      have h1 : ¬ ((P.degreeBound : ℕ) : ℤ) ≤ n := by omega
      exact (tailMapApp_null h0 h1 a).trans (tailMapApp_null h0 h1 a).symm
  exact Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom.heq_of_app_heq hbase
    _ _ fun n => tailPullbackHom_app_heq D₂.f' D₁.f' D₂.L' D₁.L' P.degreeBound P.degreeBound_pos
      hbase φ.isPullback.w ψ.isPullback.w φ.polarization ψ.polarization key n

end Stacks.AlgebraicGeometry.ProjectiveDeformation.PolarizedFamily.AdmissibleDeformation.Hom

end
