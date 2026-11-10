module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeOnSiteAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedEpsilonCokernelIso
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedEpsilonKernelSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsRepresented

/-!
# Stacks 0D0X: restricting derivations along `ε` is injective

Let `U` be an object of the big fppf site over a scheme `S`, `X₀` its underlying scheme and
`X = h_U` the algebraic space it represents, and let `ε : X_étale ⟶ X_{0,Zar}` be the morphism of
Stacks 08H7.  A derivation of `𝒪_X` on the small étale site of `X` is determined by its values
over the charts `ε(Z)` of the Zariski opens `Z` of `X₀`.  Over an affine chart `A` mapping to
the chart of an affine open `Z`, the ring map `Γ(Z) ⟶ 𝒪_X(A)` is formally unramified (the
structure morphism of `A` is étale and factors through the open immersion of `Z`), so the
difference of two derivations agreeing on `Γ(Z)` vanishes there; such charts cover every object,
and the coefficient sheaf is separated.

This is the injectivity half of step M5 of the proof of Stacks 0D0X: restricting
`f^{-1}𝒪_Y`-derivations of `𝒪_X` along `ε^♯` is injective at every sheaf of `𝒪_X`-modules.

## Main results

* `AlgebraicGeometry.Space.leibnizHom_eq_zero_of_formallyUnramified`: an additive map satisfying
  the Leibniz rule and vanishing on the image of a formally unramified ring map is zero, with
  values in a module of any universe.
* `AlgebraicGeometry.Space.formallyUnramified_representedStructureSheaf_map`: the restriction
  `𝒪_X(ε Z) ⟶ 𝒪_X(A)` along a morphism from an affine chart is formally unramified.
* `AlgebraicGeometry.Space.derivation_d_eq_of_forall_representedEpsilonFunctor`: two derivations
  of `𝒪_X` agreeing over every chart `ε(Z)` agree.
* `AlgebraicGeometry.Space.representedEpsilonDerivationRestriction_injective`: restricting
  derivations along `ε` is injective.

## References

* [Stacks Project, Tag 0D0X](https://stacks.math.columbia.edu/tag/0D0X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace AlgebraicGeometry.Space

/-- **A Leibniz map vanishing on the image of a formally unramified ring map is zero**, with
values in a module of an arbitrary universe: it is a derivation over the source, and the module
of Kähler differentials vanishes. -/
theorem leibnizHom_eq_zero_of_formallyUnramified {A Bb : CommRingCat.{u}} (g : A ⟶ Bb)
    (hg : g.hom.FormallyUnramified) {M : Type w} [AddCommGroup M] [Module Bb M] (δ : Bb →+ M)
    (hmul : ∀ x y : Bb, δ (x * y) = x • δ y + y • δ x)
    (hvanish : ∀ x : A, δ (g x) = 0) (b : Bb) : δ b = 0 := by
  let D : (ModuleCat.of Bb M).Derivation g :=
    ModuleCat.Derivation.mk δ (fun x y => δ.map_add x y) hmul hvanish
  let := g.hom.toAlgebra
  let := Module.compHom M g.hom
  have hfu : Algebra.FormallyUnramified A Bb := by
    rw [← RingHom.formallyUnramified_algebraMap, RingHom.algebraMap_toAlgebra]
    exact hg
  have : IsScalarTower A Bb M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Subsingleton (KaehlerDifferential A Bb) := (Algebra.formallyUnramified_iff A Bb).mp hfu
  let D' : Derivation A Bb M := D
  have h := congrArg
    (fun L : KaehlerDifferential A Bb →ₗ[Bb] M => L (KaehlerDifferential.D A Bb b))
    (Subsingleton.elim D'.liftKaehlerDifferential (0 : KaehlerDifferential A Bb →ₗ[Bb] M))
  exact (show D' b = 0 by simpa using h)

/-- **Two Leibniz maps compatible on the image of a formally unramified ring map are
compatible.**  Let `g : A ⟶ B₁` be formally unramified, `m : B₁ ⟶ B₂`, `ρ : M₁ ⟶ M₂` additive and
`m`-semilinear, and `δ₁`, `δ₂` Leibniz maps on `B₁`, `B₂`.  If `δ₂ ∘ m` and `ρ ∘ δ₁` agree on the
image of `g`, they agree: their difference is a Leibniz map vanishing there. -/
theorem leibnizHom_comp_eq_of_formallyUnramified {A B₁ B₂ : CommRingCat.{u}} (g : A ⟶ B₁)
    (hg : g.hom.FormallyUnramified) (m : B₁ ⟶ B₂) {M₁ : Type w} [AddCommGroup M₁] [Module B₁ M₁]
    {M₂ : Type w} [AddCommGroup M₂] [Module B₂ M₂] (ρ : M₁ →+ M₂)
    (hρ : ∀ (b : B₁) (x : M₁), ρ (b • x) = m b • ρ x) (δ₁ : B₁ →+ M₁) (δ₂ : B₂ →+ M₂)
    (h₁ : ∀ x y : B₁, δ₁ (x * y) = x • δ₁ y + y • δ₁ x)
    (h₂ : ∀ x y : B₂, δ₂ (x * y) = x • δ₂ y + y • δ₂ x)
    (hA : ∀ a : A, δ₂ (m (g a)) = ρ (δ₁ (g a))) (r : B₁) : δ₂ (m r) = ρ (δ₁ r) := by
  let : Module B₁ M₂ := Module.compHom M₂ m.hom
  have key := leibnizHom_eq_zero_of_formallyUnramified g hg (M := M₂)
    (δ₂.comp m.hom.toAddMonoidHom - ρ.comp δ₁) ?_ ?_ r
  · exact sub_eq_zero.mp key
  · intro x y
    change δ₂ (m (x * y)) - ρ (δ₁ (x * y)) =
      m x • (δ₂ (m y) - ρ (δ₁ y)) + m y • (δ₂ (m x) - ρ (δ₁ x))
    rw [map_mul, h₂, h₁, map_add, hρ, hρ, smul_sub, smul_sub]
    abel
  · intro a
    change δ₂ (m (g a)) - ρ (δ₁ (g a)) = 0
    rw [hA, sub_self]

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- **The restriction `𝒪_X(ε Z) ⟶ 𝒪_X(A)` along a morphism from an affine chart is formally
unramified**, for `Z` an affine open of `X₀`: the structure morphism of `A` is étale and factors
through that of `ε(Z)`. -/
theorem formallyUnramified_representedStructureSheaf_map
    {A : SmallEtale B S hS (yoneda.obj U)} {Z : ((BigFppfOver.toScheme B S hS).obj U).Opens}
    (j : A ⟶ (representedEpsilonFunctor B S hS U).obj Z) (hZ : IsAffineOpen Z)
    (hA : IsAffine ((SmallEtale.toOver B S hS (yoneda.obj U) ⋙ BigFppfOver.toScheme B S hS).obj
      A)) :
    ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O.obj.map
      j.op).hom.FormallyUnramified := by
  have hetA : Etale ((BigFppfOver.toScheme B S hS).map (yonedaEquiv A.1.hom)) :=
    etale_toScheme_representedChartBase B S hS U A
  have hfac : (BigFppfOver.toScheme B S hS).map j.hom.left ≫
      (BigFppfOver.toScheme B S hS).map
        (yonedaEquiv ((representedEpsilonFunctor B S hS U).obj Z).1.hom) =
      (BigFppfOver.toScheme B S hS).map (yonedaEquiv A.1.hom) := by
    rw [← Functor.map_comp]
    congr 1
    apply yoneda.map_injective
    rw [Functor.map_comp, yoneda_map_yonedaEquiv, yoneda_map_yonedaEquiv]
    exact j.hom.w
  have : _root_.AlgebraicGeometry.FormallyUnramified
      ((BigFppfOver.toScheme B S hS).map j.hom.left ≫ (BigFppfOver.toScheme B S hS).map
        (yonedaEquiv ((representedEpsilonFunctor B S hS U).obj Z).1.hom)) := by
    rw [hfac]
    infer_instance
  have : _root_.AlgebraicGeometry.FormallyUnramified
      ((BigFppfOver.toScheme B S hS).map j.hom.left) :=
    _root_.AlgebraicGeometry.FormallyUnramified.of_comp _ ((BigFppfOver.toScheme B S hS).map
      (yonedaEquiv ((representedEpsilonFunctor B S hS U).obj Z).1.hom))
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((representedEpsilonFunctor B S hS U).obj Z).1.left) :=
    isAffine_representedEpsilonFunctor_obj B S hS U hZ
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj A.1.left) := hA
  have he : (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O.obj.map j.op
      = ((BigFppfOver.toScheme B S hS).map j.hom.left).appLE ⊤ ⊤ le_rfl :=
    (Scheme.Γ_map_op _).trans (Scheme.Hom.appLE_eq_app _).symm
  rw [he]
  exact ((BigFppfOver.toScheme B S hS).map j.hom.left).formallyUnramified_appLE
    (isAffineOpen_top _) (isAffineOpen_top _) le_rfl

variable {U}
variable {T : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O)}
  {R₁ R₂ : (SmallEtale B S hS (yoneda.obj U))ᵒᵖ ⥤ CommRingCat.{u}}
  {ψ₁ : R₁ ⟶ (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O.obj}
  {ψ₂ : R₂ ⟶ (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O.obj}
  (D₁ : PresheafOfModulesOfCommRing.Derivation' T.val ψ₁)
  (D₂ : PresheafOfModulesOfCommRing.Derivation' T.val ψ₂)

/-- **Two derivations of `𝒪_X` agreeing over the charts `ε(Z)` agree over an affine chart
mapping to the chart of an affine open.**  Their difference is a Leibniz map vanishing on the
image of the formally unramified ring map `𝒪_X(ε Z) ⟶ 𝒪_X(A)`. -/
theorem derivation_d_eq_of_hom_representedEpsilonFunctor
    (hagree : ∀ (Z : ((BigFppfOver.toScheme B S hS).obj U).Opens)
      (x : ToType ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O.obj.obj
        (op ((representedEpsilonFunctor B S hS U).obj Z)))), D₁.d x = D₂.d x)
    {A : SmallEtale B S hS (yoneda.obj U)} {Z : ((BigFppfOver.toScheme B S hS).obj U).Opens}
    (j : A ⟶ (representedEpsilonFunctor B S hS U).obj Z) (hZ : IsAffineOpen Z)
    (hA : IsAffine ((SmallEtale.toOver B S hS (yoneda.obj U) ⋙ BigFppfOver.toScheme B S hS).obj
      A))
    (a : ToType ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O.obj.obj
      (op A))) :
    D₁.d a = D₂.d a := by
  have key := leibnizHom_eq_zero_of_formallyUnramified
    ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O.obj.map j.op)
    (formallyUnramified_representedStructureSheaf_map B S hS U j hZ hA)
    (M := ToType (T.val.obj (op A))) (D₁.d (X := op A) - D₂.d (X := op A)) ?_ ?_ a
  · rwa [AddMonoidHom.sub_apply, sub_eq_zero] at key
  · intro x y
    simp only [AddMonoidHom.sub_apply, D₁.d_mul, D₂.d_mul, smul_sub]
    abel
  · intro x
    simp only [AddMonoidHom.sub_apply]
    rw [D₁.d_map j.op x, D₂.d_map j.op x, hagree Z x]
    exact sub_self _

variable {V : BigFppfOver B S hS} (φ : U ⟶ V)

include φ in
/-- **Two derivations of `𝒪_X` agreeing over every chart `ε(Z)` agree.**  The charts mapping to
`ε(Z)` for an affine square cover every object, the affine charts cover each of those, and over
the latter the two derivations agree by
`AlgebraicGeometry.Space.derivation_d_eq_of_hom_representedEpsilonFunctor`; the coefficient sheaf
is separated. -/
theorem derivation_d_eq_of_forall_representedEpsilonFunctor
    (hagree : ∀ (Z : ((BigFppfOver.toScheme B S hS).obj U).Opens)
      (x : ToType ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O.obj.obj
        (op ((representedEpsilonFunctor B S hS U).obj Z)))), D₁.d x = D₂.d x)
    (A : SmallEtale B S hS (yoneda.obj U))
    (a : ToType ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O.obj.obj
      (op A))) :
    D₁.d a = D₂.d a := by
  have step1 : ∀ (A' : SmallEtale B S hS (yoneda.obj U))
      (Z : ((BigFppfOver.toScheme B S hS).obj U).Opens) (_ : IsAffineOpen Z)
      (_ : A' ⟶ (representedEpsilonFunctor B S hS U).obj Z)
      (a' : ToType ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O.obj.obj
        (op A'))), D₁.d a' = D₂.d a' := by
    intro A' Z hZ j a'
    refine T.isSheaf.isSeparated A' _ (SmallEtale.ofArrows_openChart_affineOpens_mem B S hS _ A')
      (D₁.d a') (D₂.d a') ?_
    rintro Y g ⟨Y', h, k, ⟨O⟩, rfl⟩
    have hloc := derivation_d_eq_of_hom_representedEpsilonFunctor B S hS D₁ D₂ hagree
      (openChartInclusion B S hS _ A' O.down.1 ≫ j) hZ
      (isAffine_chartScheme_openChart B S hS _ A' O.down)
      ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O.obj.map
        (openChartInclusion B S hS _ A' O.down.1).op a')
    have hstep := (D₁.d_map (openChartInclusion B S hS _ A' O.down.1).op a').symm.trans
      (hloc.trans (D₂.d_map (openChartInclusion B S hS _ A' O.down.1).op a'))
    rw [op_comp, Functor.map_comp]
    exact congrArg (ConcreteCategory.hom (T.val.presheaf.map h.op)) hstep
  refine T.isSheaf.isSeparated A _ (coversTop_representedEpsilonFunctor_affineSquare B S hS φ A)
    (D₁.d a) (D₂.d a) ?_
  rintro Y g ⟨i, ⟨j⟩⟩
  exact (D₁.d_map g.op a).symm.trans ((step1 Y i.1.1 i.2.1 j _).trans (D₂.d_map g.op a))

attribute [local instance] isContinuous_representedToZariskiRingedToposSiteHom_u

/-- **Restricting derivations along `ε` is injective** (step M5 of the proof of Stacks 0D0X): a
`f^{-1}𝒪_Y`-derivation of `𝒪_X` is determined by its restriction `D ∘ ε^♯`, since `ε^♯` is
bijective on sections over each chart `ε(Z)`. -/
theorem representedEpsilonDerivationRestriction_injective
    (T : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O)) :
    Function.Injective (representedEpsilonDerivationRestriction B S hS φ T) := by
  intro D₁ D₂ h
  ext A a
  refine derivation_d_eq_of_forall_representedEpsilonFunctor B S hS D₁ D₂ φ (fun Z x => ?_)
    A.unop a
  have e : ((representedToZariskiRingedToposSiteHom B S hS U).fSharp.hom.app (op Z)).hom
      ((Scheme.Opens.topIso Z).hom.hom x) = x :=
    (representedToZariskiRingedToposSiteHom_fSharp_app_apply B S hS U Z _).trans
      (ConcreteCategory.congr_hom (Scheme.Opens.topIso Z).hom_inv_id x)
  have hd : (representedEpsilonDerivationRestriction B S hS φ T D₁).d (X := op Z)
      ((Scheme.Opens.topIso Z).hom.hom x) =
        (representedEpsilonDerivationRestriction B S hS φ T D₂).d (X := op Z)
          ((Scheme.Opens.topIso Z).hom.hom x) := by
    rw [h]
  exact (congrArg (D₁.d (X := op ((representedEpsilonFunctor B S hS U).obj Z))) e).symm.trans
    (hd.trans (congrArg (D₂.d (X := op ((representedEpsilonFunctor B S hS U).obj Z))) e))

end AlgebraicGeometry.Space

end
