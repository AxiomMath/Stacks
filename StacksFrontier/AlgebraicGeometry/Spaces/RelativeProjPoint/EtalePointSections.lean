module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceQuotientQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjClosedSubspaceQuotient

/-!
# The restriction of Situation 0849 to an étale scheme point, read on sections

Let `f : T ⟶ X` be an étale scheme point of the base of Situation 0849.  A Zariski open `W` of
`T` is then an étale chart `W ⟶ T ⟶ X` of `X`, and the sections of the restriction `f^*𝒜_n` over
`W` are the sections of `𝒜_n` over that chart: pullback along an étale morphism is restriction
(Stacks 03LW).  Under this identification the restriction of a map of graded algebras is the map
itself; for the quotient map `𝒜 ⟶ 𝒜 ⧸ ℐ` the kernel of its restriction is therefore `ℐ`.

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjSituation.etalePointChart`: the étale chart `W ⟶ T ⟶ X`.
* `AlgebraicGeometry.Space.RelativeProjSituation.etalePointSectionsEquiv` and
  `AlgebraicGeometry.Space.RelativeProjSituation.etalePointReading`: the identification of the
  sections of `f^*𝒜_n` over `W` with those of `𝒜_n` over the chart.

## Main results

* `AlgebraicGeometry.Space.RelativeProjSituation.homPoints_app_eq_zero_iff`: the restriction of a
  map of graded algebras to an étale scheme point kills a section exactly when the map kills its
  reading on the chart.
* `AlgebraicGeometry.Space.RelativeProjSituation.GradedIdeal.quotientHomPoints_app_eq_zero_iff`:
  a local section of `f^*𝒜_n` is killed by the restriction of `𝒜 ⟶ 𝒜 ⧸ ℐ` exactly when its
  reading on the chart lies in `ℐ_n`.
* `AlgebraicGeometry.Space.RelativeProjSituation.isAffine_etalePointChart`: the chart cut out by
  an affine open is affine.

## Implementation notes

The statements about a map of graded algebras are proved for situations written as
`RelativeProjSituation.mk` of their fields, which is how `homPoints` presents them, and
`etalePointReading` abbreviates `etalePointSectionsEquiv` of the situation written in that
presentation: it is the same identification, but comparing the two presentations of one situation
is a definitional unfolding that the elaborator does not perform within its budget.

## References

* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 0849](https://stacks.math.columbia.edu/tag/0849)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space.RelativeProjSituation

variable (s : RelativeProjSituation.{u, u}) {T : BigFppfOver s.site s.base s.containsBase}
  (f : yoneda.obj T ⟶ s.space.1)
  (hf : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) f).hom)

/-- The étale chart `W ⟶ T ⟶ X` of the base cut out by a Zariski open `W` of an étale scheme
point `f : T ⟶ X`. -/
abbrev etalePointChart (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens) :
    SmallEtale s.site s.base s.containsBase s.space.1 :=
  (smallEtalePostcomp s.site s.base s.containsBase (pointHom (X := s.space) f) hf).obj
    ((selfOpensFunctor s.site s.base s.containsBase T).obj W)

/-- The comparison of Stacks 03LW for the étale scheme point, in degree `n`. -/
abbrev etalePointIso (n : ℤ) :=
  (modulePullbackIsoEtaleModulePullback s.site s.base s.containsBase
    (pointHom (X := s.space) f) hf).app (s.smallAlgebra.piece n)

/-- The sections of `f^*𝒜_n` over `W`, unfolded to the sections of the pullback of modules over
the étale chart `W` of the represented space. -/
def etalePointSectionsUnfold (n : ℤ)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens) :
    Γ((s.relativeProjPoints.algebra T f).piece n, W) ≃
      ((modulePullback s.site s.base s.containsBase (pointHom (X := s.space) f)).obj
        (s.smallAlgebra.piece n)).val.obj
          (op ((selfOpensFunctor s.site s.base s.containsBase T).obj W)) :=
  (((Equiv.refl _ : Γ((s.relativeProjPoints.algebra T f).piece n, W) ≃
      (((s.shrink.pointAlgebra T f).piece n).val.obj (op W) : Type u)).trans
    (Equiv.refl _ : (((s.shrink.pointAlgebra T f).piece n).val.obj (op W) : Type u) ≃
      (((SheafOfModules.pushforward.{u} (selfOpensStructureMap s.site s.base s.containsBase T)).obj
        ((etalePointAlgebra s.smallAlgebra T f).piece n)).val.obj (op W) : Type u))).trans
    (Equiv.refl _ : (((SheafOfModules.pushforward.{u}
        (selfOpensStructureMap s.site s.base s.containsBase T)).obj
        ((etalePointAlgebra s.smallAlgebra T f).piece n)).val.obj (op W) : Type u) ≃
      ((etalePointAlgebra s.smallAlgebra T f).piece n).val.obj
        (op ((selfOpensFunctor s.site s.base s.containsBase T).obj W)))).trans
    (Equiv.refl _ : (((etalePointAlgebra s.smallAlgebra T f).piece n).val.obj
        (op ((selfOpensFunctor s.site s.base s.containsBase T).obj W)) : Type u) ≃
      ((modulePullback s.site s.base s.containsBase (pointHom (X := s.space) f)).obj
        (s.smallAlgebra.piece n)).val.obj
          (op ((selfOpensFunctor s.site s.base s.containsBase T).obj W)))

/-- **The sections of `f^*𝒜_n` over a Zariski open `W` of an étale scheme point are the sections
of `𝒜_n` over the chart `W ⟶ T ⟶ X`.** -/
def etalePointSectionsEquiv (n : ℤ)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens) :
    Γ((s.relativeProjPoints.algebra T f).piece n, W) ≃
      (s.algebra.piece n).val.obj (op (s.etalePointChart f hf W)) :=
  ((s.etalePointSectionsUnfold f n W).trans (Equiv.mk
    (fun a => (s.etalePointIso f hf n).hom.val.app
      (op ((selfOpensFunctor s.site s.base s.containsBase T).obj W)) a)
    (fun b => (s.etalePointIso f hf n).inv.val.app
      (op ((selfOpensFunctor s.site s.base s.containsBase T).obj W)) b)
    (fun a => congrArg (fun k => k.val.app
      (op ((selfOpensFunctor s.site s.base s.containsBase T).obj W)) a)
        (s.etalePointIso f hf n).hom_inv_id)
    (fun b => congrArg (fun k => k.val.app
      (op ((selfOpensFunctor s.site s.base s.containsBase T).obj W)) b)
        (s.etalePointIso f hf n).inv_hom_id))).trans
    (SheafOfModules.GradedAlgebra.smallPieceEquiv s.algebra n
      (op (s.etalePointChart f hf W))).toEquiv

/-- A section of a module on a scheme is killed by a morphism exactly when it is killed on the
underlying presheaf of modules. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.Hom.app_eq_zero_iff_val {X : Scheme.{u}}
    {M N : X.Modules} (φ : M ⟶ N) (W : X.Opens) (a : Γ(M, W)) :
    φ.app W a = 0 ↔ φ.val.app (op W) a = 0 :=
  Iff.rfl

section Helpers

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A section is zero exactly when its image under an isomorphism of modules is. -/
theorem eq_zero_iff_iso_hom_val_app_eq_zero {X : AlgebraicSpaces B S hS}
    {M N : Modules.{u, u} B S hS X.1 X.2} (e : M ≅ N) (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : M.val.obj U) : x = 0 ↔ e.hom.val.app U x = 0 := by
  rw [← map_zero (e.hom.val.app U).hom]
  exact (bijective_val_app_of_iso e U).1.eq_iff.symm

/-- The comparison of Stacks 03LW is natural, on sections. -/
theorem modulePullbackIsoEtaleModulePullback_hom_naturality_apply {P X : AlgebraicSpaces B S hS}
    (g : P ⟶ X) (hg : IsEtale B S hS g.hom) {M N : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ N)
    (U : SmallEtale B S hS P.1) (x : ((modulePullback B S hS g).obj M).val.obj (op U)) :
    ((modulePullbackIsoEtaleModulePullback B S hS g hg).app N).hom.val.app (op U)
        (((modulePullback B S hS g).map φ).val.app (op U) x) =
      φ.val.app (op ((smallEtalePostcomp B S hS g hg).obj U))
        (((modulePullbackIsoEtaleModulePullback B S hS g hg).app M).hom.val.app (op U) x) :=
  congrArg (fun k => k.val.app (op U) x)
    ((modulePullbackIsoEtaleModulePullback B S hS g hg).hom.naturality φ)

end Helpers

section Map

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  {𝒜₁ 𝒜₂ : SheafOfModules.GradedAlgebra.{u, u, u, u + 1} (structureRingSheaf B S hS X)}
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
  {T : BigFppfOver B S hS} (f : yoneda.obj T ⟶ X.1)
  (hf : IsEtale B S hS (pointHom (X := X) f).hom)

local notation "𝔰₁" => RelativeProjSituation.mk B S hS X 𝒜₁ h₁c h₁n h₁q h₁k
local notation "𝔰₂" => RelativeProjSituation.mk B S hS X 𝒜₂ h₂c h₂n h₂q h₂k

/-- A section of the degree `n` piece of the point algebra of `A₁` over a Zariski open `W` is
killed by `pointAlgebraHom Φ T f` exactly when it is killed by the pullback of `Φ` along
`pointHom f` on the corresponding open of the big site. -/
theorem _root_.AlgebraicGeometry.Space.pointAlgebraHom_app_val_app_apply
    {A₁ A₂ : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X)}
    (Φ : SheafOfModules.GradedAlgebra.UnitalHom A₁ A₂) (n : ℤ)
    (W : ((BigFppfOver.toScheme B S hS).obj T).Opens)
    (x : ((zariskiReading T (etalePointAlgebra A₁ T f)).piece n).val.obj (op W)) :
    ((pointAlgebraHom Φ T f).app n).val.app (op W) x = 0 ↔
      ((modulePullback B S hS (pointHom (X := X) f)).map (Φ.app n)).val.app
        (op ((selfOpensFunctor B S hS T).obj W)) x = 0 :=
  Iff.rfl

/-- On sections over `V`, the degree `n` component of `shrinkMap` is `ψ` conjugated by the
identifications `smallPieceEquiv` of the small pieces of `𝒜₁` and `𝒜₂`. -/
theorem shrinkMap_app_val_app_apply (n : ℤ) (V : (SmallEtale B S hS X.1)ᵒᵖ)
    (y : ((𝔰₁).smallAlgebra.piece n).val.obj V) :
    ((shrinkMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ).app n).val.app V y =
      (SheafOfModules.GradedAlgebra.smallPieceEquiv 𝒜₂ n V).symm ((ψ.app n).val.app V
        (SheafOfModules.GradedAlgebra.smallPieceEquiv 𝒜₁ n V y)) :=
  rfl

/-- The value of `etalePointSectionsEquiv` on a section `a` over `W`: unfold `a`, apply
`etalePointIso`, and identify the result with a section of `𝒜₁` over the chart
`etalePointChart f hf W` by `smallPieceEquiv`. -/
theorem etalePointSectionsEquiv_apply (n : ℤ) (W : ((BigFppfOver.toScheme B S hS).obj T).Opens)
    (a : Γ(((𝔰₁).relativeProjPoints.algebra T f).piece n, W)) :
    (𝔰₁).etalePointSectionsEquiv f hf n W a =
      SheafOfModules.GradedAlgebra.smallPieceEquiv 𝒜₁ n (op ((𝔰₁).etalePointChart f hf W))
        (((𝔰₁).etalePointIso f hf n).hom.val.app (op ((selfOpensFunctor B S hS T).obj W))
          ((𝔰₁).etalePointSectionsUnfold f n W a)) :=
  rfl

/-- **A map of graded algebras restricted to an étale scheme point, on sections.** A local section
of `f^*𝒜₁` over a Zariski open `W` is killed by the restriction of `ψ` exactly when its reading on
the chart `W ⟶ T ⟶ X` is killed by `ψ`. -/
theorem homPoints_app_eq_zero_iff (n : ℤ) (W : ((BigFppfOver.toScheme B S hS).obj T).Opens)
    (a : Γ(((𝔰₁).relativeProjPoints.algebra T f).piece n, W)) :
    (((homPoints h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ).hom T f).app n).app W a = 0 ↔
      (ψ.app n).val.app (op ((𝔰₁).etalePointChart f hf W))
        ((𝔰₁).etalePointSectionsEquiv f hf n W a) = 0 := by
  rw [Scheme.Modules.Hom.app_eq_zero_iff_val, homPoints_hom, restrictHom_app]
  refine (pointAlgebraHom_app_val_app_apply f
    (shrinkMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ) n W a).trans ?_
  refine (eq_zero_iff_iso_hom_val_app_eq_zero
    ((modulePullbackIsoEtaleModulePullback B S hS (pointHom (X := X) f) hf).app
      ((𝔰₂).smallAlgebra.piece n)) (op ((selfOpensFunctor B S hS T).obj W)) _).trans ?_
  refine (Eq.to_iff (congrArg (· = 0)
    (modulePullbackIsoEtaleModulePullback_hom_naturality_apply (pointHom (X := X) f) hf
      (M := (𝔰₁).smallAlgebra.piece n) (N := (𝔰₂).smallAlgebra.piece n)
      ((shrinkMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ).app n)
      ((selfOpensFunctor B S hS T).obj W) ((𝔰₁).etalePointSectionsUnfold f n W a)))).trans ?_
  refine (Eq.to_iff (congrArg (· = 0) (shrinkMap_app_val_app_apply h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k
    ψ n (op ((𝔰₁).etalePointChart f hf W)) _))).trans ?_
  refine ((SheafOfModules.GradedAlgebra.smallPieceEquiv 𝒜₂ n
    (op ((𝔰₁).etalePointChart f hf W))).symm.map_eq_zero_iff).trans ?_
  rw [etalePointSectionsEquiv_apply]

end Map






/-- **The reading of a section of `f^*𝒜_n` over `W` on the chart `W ⟶ T ⟶ X`**, for an étale
scheme point `f`: the identification `etalePointSectionsEquiv`, for the situation presented by
`RelativeProjSituation.mk` of its fields. -/
abbrev etalePointReading (s : RelativeProjSituation.{u, u})
    {T : BigFppfOver s.site s.base s.containsBase} (f : yoneda.obj T ⟶ s.space.1)
    (hf : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) f).hom) (n : ℤ)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens) :
    Γ((s.relativeProjPoints.algebra T f).piece n, W) ≃
      (s.algebra.piece n).val.obj (op (s.etalePointChart f hf W)) :=
  (RelativeProjSituation.mk s.site s.base s.containsBase s.space s.algebra s.mul_comm
    s.negative_isZero s.isQuasicoherent s.sections_hasCardinalLT).etalePointSectionsEquiv f hf n W


/-- **The kernel of the restricted quotient map at an étale scheme point.** A local section of
`f^*𝒜_n` over a Zariski open `W` is killed by the restriction of `𝒜 ⟶ 𝒜 ⧸ ℐ` exactly when its
reading on the chart `W ⟶ T ⟶ X` lies in `ℐ_n`. -/
theorem GradedIdeal.quotientHomPoints_app_eq_zero_iff {s : RelativeProjSituation.{u, u}}
    (J : s.GradedIdeal) {T : BigFppfOver s.site s.base s.containsBase}
    (f : yoneda.obj T ⟶ s.space.1)
    (hf : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) f).hom) (n : ℤ)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens)
    (a : Γ((s.relativeProjPoints.algebra T f).piece n, W)) :
    ((J.quotientHomPoints.hom T f).app n).app W a = 0 ↔
      s.etalePointReading f hf n W a ∈ (J.piece n).obj (op (s.etalePointChart f hf W)) :=
  (homPoints_app_eq_zero_iff s.mul_comm s.negative_isZero s.isQuasicoherent
    s.sections_hasCardinalLT J.quotientSituation.mul_comm J.quotientSituation.negative_isZero
    J.quotientSituation.isQuasicoherent J.quotientSituation.sections_hasCardinalLT
    J.quotientMap f hf n W a).trans (J.toIdeal.quotientMapApp_eq_zero_iff n _ _)



/-- The chart `W ⟶ T ⟶ X` cut out by an affine open `W` of an étale scheme point is affine. -/
theorem isAffine_etalePointChart (s : RelativeProjSituation.{u, u})
    {T : BigFppfOver s.site s.base s.containsBase} (f : yoneda.obj T ⟶ s.space.1)
    (hf : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) f).hom)
    {W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens} (hW : IsAffineOpen W) :
    IsAffine ((SmallEtale.toOver s.site s.base s.containsBase s.space.1 ⋙
      BigFppfOver.toScheme s.site s.base s.containsBase).obj (s.etalePointChart f hf W)) := by
  show IsAffine ((SmallEtale.toOver s.site s.base s.containsBase (yoneda.obj T) ⋙
    BigFppfOver.toScheme s.site s.base s.containsBase).obj
      ((selfOpensFunctor s.site s.base s.containsBase T).obj W))
  rwa [selfOpensFunctor_obj s.site s.base s.containsBase T W]

end AlgebraicGeometry.Space.RelativeProjSituation
