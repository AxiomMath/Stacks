module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjFunctorialityClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.HomPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.ZariskiReadingAdjunction

/-!
# Maps of graded algebras surjective in high degree, on the canonical relative Proj

In Situation 0849 let `ψ : 𝒜₁ ⟶ 𝒜₂` be a map of quasi-coherent graded `𝒪_X`-algebras on an
algebraic space `X` such that `ψ_d : 𝒜₁,d ⟶ 𝒜₂,d` is surjective for `d ≫ 0`, surjectivity of a
map of sheaves of modules on the small étale site being local surjectivity. Then every
restriction `f^*ψ` of `ψ` to a scheme point `f : T ⟶ X` is an epimorphism in the same degrees, so
the results of `StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjFunctorialityClosedImmersion`
apply to `ψ` itself: `U(ψ) = Proj_X(𝒜₂)` and `r_ψ : U(ψ) ⟶ Proj_X(𝒜₁)` is a closed immersion of
algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.epi_map_of_isIso_counit`: a right adjoint between abelian categories
  carries an epimorphism between objects at which the counit is invertible to an epimorphism, as
  soon as the unit is invertible on a class of objects closed under cokernels and containing the
  images of those objects.
* `AlgebraicGeometry.Space.epi_zariskiReading_map`: the Zariski reading of quasi-coherent modules
  on a represented algebraic space preserves epimorphisms.
* `AlgebraicGeometry.Space.RelativeProjSituation.epi_restrictHom_app`: the restriction of `ψ` to a
  scheme point of `X` is an epimorphism in every degree in which `ψ` is surjective.
* `AlgebraicGeometry.Space.RelativeProjSituation.relativeMapSubfunctor_homPoints_eq_top` and
  `AlgebraicGeometry.Space.RelativeProjSituation.isClosedImmersion_relativeMapSpaceHom_homPoints`:
  the first two assertions of Stacks 085H for `ψ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Filter
open Stacks.AlgebraicGeometry.RelativeProjMapDomain

attribute [local instance 5000] SheafOfModules.instAbelian

universe u m

namespace SheafOfModules.GradedAlgebra

universe t a w v₀ u₀

variable {C : Type u₀} [Category.{v₀} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A B : GradedAlgebra.{t, a} R}
  [∀ (n : ℤ) (U : Cᵒᵖ), Small.{w} ((A.piece n).val.obj U)]
  [∀ (n : ℤ) (U : Cᵒᵖ), Small.{w} ((B.piece n).val.obj U)]

/-- A unital homomorphism which is locally surjective in degree `n` stays so after carrying it to
the small presentations. -/
theorem isLocallySurjective_smallPresentationMap_app (g : UnitalHom A B) (n : ℤ)
    (hg : Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map (g.app n).val)) :
    Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map
        ((smallPresentationMap.{t, a, w} g).app n).val) := by
  refine ⟨fun {U} s => J.superset_covering ?_
    (Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf R.obj).map (g.app n).val)
      (U := op U) (smallPieceEquiv B n (op U) s :))⟩
  intro V i hi
  change ∃ x : (A.piece n).val.obj (op V),
    (g.app n).val.app (op V) x = (B.piece n).val.map i.op (smallPieceEquiv B n (op U) s) at hi
  obtain ⟨x, hx⟩ := hi
  refine ⟨(smallPieceEquiv A n (op V)).symm x, ?_⟩
  show (smallPieceEquiv B n (op V)).symm ((g.app n).val.app (op V)
      (smallPieceEquiv A n (op V) ((smallPieceEquiv A n (op V)).symm x))) =
    (smallPiece B n).val.map i.op s
  rw [LinearEquiv.apply_symm_apply, hx]
  exact (congrArg (smallPieceEquiv B n (op V)).symm
    (smallPieceEquiv_naturality B n i.op s).symm).trans (LinearEquiv.symm_apply_apply _ _)

end SheafOfModules.GradedAlgebra

namespace AlgebraicGeometry.Space

universe u₁ v₁ u₂ v₂

/-- **A right adjoint preserves an epimorphism between objects at which the counit is
invertible**, provided the unit is invertible on a class of objects which contains the images
of the two objects and is closed under cokernels: the cokernel of the image of the epimorphism
lies in that class, and its image under the left adjoint is the cokernel of an epimorphism. -/
theorem epi_map_of_isIso_counit {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    [Abelian C] [Abelian D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (P : ObjectProperty C)
    (hP : ∀ {Y₁ Y₂ : C} (φ : Y₁ ⟶ Y₂), P Y₁ → P Y₂ → P (cokernel φ))
    (hunit : ∀ Y, P Y → IsIso (adj.unit.app Y)) {N₁ N₂ : D} (g : N₁ ⟶ N₂) (hg : Epi g)
    (hε₁ : IsIso (adj.counit.app N₁)) (hε₂ : IsIso (adj.counit.app N₂)) (h₁ : P (R.obj N₁))
    (h₂ : P (R.obj N₂)) : Epi (R.map g) := by
  have := adj.isLeftAdjoint
  have := adj.isRightAdjoint
  have := hunit _ (hP (R.map g) h₁ h₂)
  have hLg : L.map (R.map g) = adj.counit.app N₁ ≫ g ≫ inv (adj.counit.app N₂) := by
    rw [← cancel_mono (adj.counit.app N₂), Category.assoc, Category.assoc, IsIso.inv_hom_id,
      Category.comp_id]
    exact adj.counit.naturality g
  have : Epi (L.map (R.map g)) := by rw [hLg]; infer_instance
  have hz : IsZero (L.obj (cokernel (R.map g))) :=
    (isZero_cokernel_of_epi (L.map (R.map g))).of_iso (PreservesCokernel.iso L (R.map g))
  exact Preadditive.epi_of_isZero_cokernel _
    ((R.map_isZero hz).of_iso (asIso (adj.unit.app (cokernel (R.map g)))))

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The Zariski reading preserves epimorphisms of quasi-coherent modules.** For an epimorphism
`g` of quasi-coherent `𝒪`-modules on the small étale site of a represented algebraic space
`yoneda.obj T`, the induced map on the Zariski opens of the scheme of `T` is an epimorphism of
`𝒪_T`-modules. -/
theorem epi_zariskiReading_map (T : BigFppfOver B S hS)
    {N₁ N₂ : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)}
    (g : N₁ ⟶ N₂) (hg : Epi g) (h₁ : N₁.IsQuasicoherentOnSite) (h₂ : N₂.IsQuasicoherentOnSite) :
    Epi ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).map g) :=
  epi_map_of_isIso_counit (zariskiReadingAdjunction T)
    (SheafOfModules.isQuasicoherent _)
    (fun φ h₁ h₂ => @Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel
      _ _ _ φ h₁ h₂)
    (fun Y hY => isIso_zariskiReadingAdjunction_unit_app T Y hY) g hg
    (isIso_zariskiReadingAdjunction_counit_app T N₁ h₁)
    (isIso_zariskiReadingAdjunction_counit_app T N₂ h₂)
    (isQuasicoherent_zariskiReading_piece T N₁ h₁) (isQuasicoherent_zariskiReading_piece T N₂ h₂)

namespace RelativeProjSituation

variable {X : AlgebraicSpaces B S hS}
  {𝒜₁ 𝒜₂ : SheafOfModules.GradedAlgebra.{u, m, u, u + 1} (structureRingSheaf B S hS X)}
  (h₁c : ∀ (i j : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ) (a : (𝒜₁.piece i).val.obj U)
    (b : (𝒜₁.piece j).val.obj U), HEq ((𝒜₁.mul i j).app U a b) ((𝒜₁.mul j i).app U b a))
  (h₁n : ∀ n : ℤ, n < 0 → Limits.IsZero (𝒜₁.piece n))
  (h₁q : ∀ n : ℤ, (𝒜₁.piece n).IsQuasicoherentOnSite)
  (h₁k : ∀ (n : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ),
    HasCardinalLT ↥((𝒜₁.piece n).val.obj U) B.cutoff)
  (h₂c : ∀ (i j : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ) (a : (𝒜₂.piece i).val.obj U)
    (b : (𝒜₂.piece j).val.obj U), HEq ((𝒜₂.mul i j).app U a b) ((𝒜₂.mul j i).app U b a))
  (h₂n : ∀ n : ℤ, n < 0 → Limits.IsZero (𝒜₂.piece n))
  (h₂q : ∀ n : ℤ, (𝒜₂.piece n).IsQuasicoherentOnSite)
  (h₂k : ∀ (n : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ),
    HasCardinalLT ↥((𝒜₂.piece n).val.obj U) B.cutoff)
  (ψ : SheafOfModules.GradedAlgebra.UnitalHom 𝒜₁ 𝒜₂)

local notation "𝔰₁" => RelativeProjSituation.mk B S hS X 𝒜₁ h₁c h₁n h₁q h₁k
local notation "𝔰₂" => RelativeProjSituation.mk B S hS X 𝒜₂ h₂c h₂n h₂q h₂k

/-- **The restriction of `ψ` to a scheme point is an epimorphism in every degree in which `ψ` is
surjective.** If `ψ_n : 𝒜₁,n ⟶ 𝒜₂,n` is locally surjective on the small étale site of `X`, then
for every scheme point `f : T ⟶ X` the restriction `f^*ψ` is an epimorphism of `𝒪_T`-modules in
degree `n`: the pullback to the small étale site of `T` preserves epimorphisms, being a left
adjoint, and so does the Zariski reading of quasi-coherent modules. -/
theorem epi_restrictHom_app (n : ℤ)
    (hn : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS X.1)
      ((PresheafOfModules.toPresheaf _).map (ψ.app n).val))
    (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X.1) :
    Epi ((restrictHom h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ T f).app n) := by
  have := (𝔰₁).small_sections
  have := (𝔰₂).small_sections
  have h1 : Epi ((shrinkMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ).app n) :=
    Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _
      (SheafOfModules.GradedAlgebra.isLocallySurjective_smallPresentationMap_app ψ n hn)
  have h2 : Epi ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
      (smallEtaleRingedToposHom B S hS (pointHom f)).toRingedToposModulesHom).map
        ((shrinkMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ).app n)) := by
    have := (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
      (smallEtaleRingedToposHom B S hS (pointHom f)).toRingedToposModulesHom).isLeftAdjoint
    exact @Functor.map_epi _ _ _ _ _ inferInstance _ _ _ h1
  rw [epi_restrictHom_app_iff]
  exact epi_zariskiReading_map T _ h2
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom f) _
      ((𝔰₁).shrink.isQuasicoherent n))
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom f) _
      ((𝔰₂).shrink.isQuasicoherent n))

/-- Local surjectivity of `ψ_d` for `d ≫ 0` makes every restriction of `ψ` an epimorphism in all
large degrees. -/
private theorem eventually_epi_restrictHom_app
    (hsurj : ∀ᶠ d : ℕ in atTop, Presheaf.IsLocallySurjective (SmallEtale.topology B S hS X.1)
      ((PresheafOfModules.toPresheaf _).map (ψ.app (d : ℤ)).val))
    (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X.1) :
    ∀ᶠ d : ℕ in atTop, Epi ((restrictHom h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ T f).app (d : ℤ)) :=
  hsurj.mono fun d hd => epi_restrictHom_app h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ d hd T f

/-- **Stacks 085H (1) for the canonical relative Projs: `U(ψ) = Q`.** If `ψ_d : 𝒜₁,d ⟶ 𝒜₂,d` is
surjective for `d ≫ 0`, the open subspace `U(ψ)` of Stacks 085F is all of
`Q = Proj_X(𝒜₂)`. This is also Stacks 085J (1), whose hypotheses contain these. -/
@[stacks 085H "(1): U(ψ) = Q", stacks 085J "(1): U(ψ) = Q"]
theorem relativeMapSubfunctor_homPoints_eq_top
    (hsurj : ∀ᶠ d : ℕ in atTop, Presheaf.IsLocallySurjective (SmallEtale.topology B S hS X.1)
      ((PresheafOfModules.toPresheaf _).map (ψ.app (d : ℤ)).val)) :
    (homPoints h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ).relativeMapSubfunctor = ⊤ :=
  RelativeProjHomPoints.relativeMapSubfunctor_eq_top_of_eventually_epi _ <|
    eventually_epi_restrictHom_app h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ hsurj

/-- **Stacks 085H (2) for the canonical relative Projs: `r_ψ` is a closed immersion.** If
`ψ_d : 𝒜₁,d ⟶ 𝒜₂,d` is surjective for `d ≫ 0`, the morphism `r_ψ : U(ψ) ⟶ Proj_X(𝒜₁)` of
Stacks 085F, whose source is all of `Proj_X(𝒜₂)` by `relativeMapSubfunctor_homPoints_eq_top`, is
a closed immersion of algebraic spaces. This is also Stacks 085J (2), whose hypotheses contain
these. -/
@[stacks 085H "(2): r_ψ : Q ⟶ P is a closed immersion",
  stacks 085J "(2): r_ψ : Q ⟶ P is a closed immersion"]
theorem isClosedImmersion_relativeMapSpaceHom_homPoints
    (hsurj : ∀ᶠ d : ℕ in atTop, Presheaf.IsLocallySurjective (SmallEtale.topology B S hS X.1)
      ((PresheafOfModules.toPresheaf _).map (ψ.app (d : ℤ)).val)) :
    IsClosedImmersion B S hS (homPoints h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ).relativeMapSpaceHom :=
  RelativeProjHomPoints.isClosedImmersion_relativeMapSpaceHom _ <|
    eventually_epi_restrictHom_app h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ hsurj

end RelativeProjSituation

end AlgebraicGeometry.Space

end
