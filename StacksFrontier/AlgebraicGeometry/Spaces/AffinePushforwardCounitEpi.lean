module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCover
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfaeComplete
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback

/-!
# The counit of the inverse image along an affine morphism is an epimorphism

Let `g : Z ⟶ W` be an affine morphism of algebraic spaces over a scheme `S` and let `N` be a
quasi-coherent `𝒪_Z`-module.  The counit `g^*g_*N ⟶ N` of the adjunction `g^* ⊣ g_*` is an
epimorphism.

## Main results

* `CategoryTheory.Adjunction.epi_counit_app_of_map_injective`: for an adjunction `L ⊣ R`, the
  counit at `X` is an epimorphism as soon as `R` is injective on the morphisms out of `X`.
* `AlgebraicGeometry.Space.eq_of_modulePushforward_map_eq_of_isAffineHom`: the direct image
  along an affine morphism is injective on the morphisms out of a quasi-coherent module.
* `AlgebraicGeometry.Space.epi_counit_modulePullbackAdjunction_app_of_isAffineHom`: the counit
  `g^*g_*N ⟶ N` is an epimorphism for `g` affine and `N` quasi-coherent.

## Implementation notes

The source's argument is that over an affine scheme the counit is `A ⊗_A M ⟶ M`.  The proof here
uses the equivalent form that `g_*` is faithful on the morphisms out of `N`.  An affine morphism
is representable, so `g_*` is the direct image along base change of étale charts
(`AlgebraicGeometry.Space.modulePushforwardChartIso`): two morphisms `φ₁ φ₂ : N ⟶ M` with the
same direct image agree on the sections over every base-changed chart `V ×_W Z`.  Over an affine
chart `V` that base change is affine, and every affine chart `A` of `Z` mapping to such a base
change has `N(A) = 𝒪(A) ⊗ N(V ×_W Z)` because `N` is quasi-coherent (the forward implication of
Descent, Proposition 03DX (2) at the small étale site); by linearity and naturality `φ₁` and `φ₂`
then agree on `N(A)`.  Those charts cover every chart of `Z`, and `M` is separated.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D] {L : C ⥤ D} {R : D ⥤ C}

/-- For an adjunction `L ⊣ R`, the counit at `X` is an epimorphism as soon as `R` is injective on
the morphisms out of `X`. -/
theorem epi_counit_app_of_map_injective (adj : L ⊣ R) (X : D)
    (h : ∀ ⦃Y : D⦄ (f g : X ⟶ Y), R.map f = R.map g → f = g) :
    Epi (adj.counit.app X) :=
  ⟨fun f g hfg => h f g (by
    simpa using congrArg (fun k => adj.unit.app (R.obj X) ≫ R.map k) hfg)⟩

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Two morphisms out of a quasi-coherent `𝒪_Z`-module which agree on the sections over every
base-changed chart `V ×_W Z`, `V` an affine étale chart of `W`, of a representable morphism
`g : Z ⟶ W` whose represented base changes are affine, are equal. -/
theorem eq_of_forall_smallBaseChange {Z W : AlgebraicSpaces B S hS} (g : Z ⟶ W)
    (hrep : yoneda.relativelyRepresentable g.hom)
    (haff : (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf g.hom)
    {N M : Modules.{u, u} B S hS Z.1 Z.2} (hN : N.IsQuasicoherentOnSite) (φ₁ φ₂ : N ⟶ M)
    (h : ∀ V : SmallEtale B S hS W.1,
      IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left) →
        φ₁.val.app (op ((smallBaseChange B S hS g hrep).obj V)) =
          φ₂.val.app (op ((smallBaseChange B S hS g hrep).obj V))) :
    φ₁ = φ₂ := by
  have key : ∀ A : SmallEtale B S hS Z.1, HasAffineChartDiagram B S hS g A →
      φ₁.val.app (op A) = φ₂.val.app (op A) := by
    rintro A ⟨hAaff, V, q, hq, hVaff⟩
    let A' := (smallBaseChange B S hS g hrep).obj V
    let a : A ⟶ A' := ObjectProperty.homMk (CostructuredArrow.homMk
      (hrep.lift A.1.hom q hq.symm) (hrep.lift_fst _ _ _))
    have hA'aff : IsAffine ((SmallEtale.toOver B S hS Z.1 ⋙ BigFppfOver.toScheme B S hS).obj
        A') :=
      @isAffine_of_isAffineHom _ _ ((BigFppfOver.toScheme B S hS).map (hrep.snd V.1.hom))
        (haff.property V.1.hom _ _ (hrep.isPullback V.1.hom)) hVaff
    ext x
    obtain ⟨t, rfl⟩ := (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS Z.1 Z.2 N hN
      A' A hA'aff hAaff a).2 x
    let _ := chartAlgebra (hF := Z.2) a
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b y =>
      rw [chartBaseChange_tmul, chartRestrictLinear_apply]
      refine ((φ₁.val.app (op A)).hom.map_smul b _).trans
        (Eq.trans ?_ ((φ₂.val.app (op A)).hom.map_smul b _).symm)
      congr 1
      have hy : (φ₁.val.app (op A')).hom y = (φ₂.val.app (op A')).hom y := by rw [h V hVaff]
      exact (PresheafOfModules.naturality_apply φ₁.val a.op y).trans
        ((congrArg (M.val.map a.op).hom hy).trans
          (PresheafOfModules.naturality_apply φ₂.val a.op y).symm)
  ext U s
  have hsieve : Presheaf.equalizerSieve (F := M.val.presheaf)
      ((φ₁.val.app U).hom s) ((φ₂.val.app U).hom s) ∈ SmallEtale.topology B S hS Z.1 U.unop :=
    mem_topology_of_hasAffineChartDiagram B S hS g U.unop _ fun A a hA =>
      (PresheafOfModules.naturality_apply φ₁.val a.op s).symm.trans
        ((congrArg (fun k => k.hom ((N.val.map a.op).hom s)) (key A hA)).trans
          (PresheafOfModules.naturality_apply φ₂.val a.op s))
  exact M.isSheaf.isSeparated _ _ hsieve _ _ (fun _ _ hf => hf)

/-- **The direct image along an affine morphism is injective on the morphisms out of a
quasi-coherent module.**  If `g : Z ⟶ W` is an affine morphism of algebraic spaces, `N` is a
quasi-coherent `𝒪_Z`-module and `φ₁ φ₂ : N ⟶ M` have the same direct image, then `φ₁ = φ₂`. -/
theorem eq_of_modulePushforward_map_eq_of_isAffineHom {Z W : AlgebraicSpaces B S hS}
    (g : Z ⟶ W) (hg : IsAffineHom B S hS g.hom)
    {N M : Modules.{u, u} B S hS Z.1 Z.2} (hN : N.IsQuasicoherentOnSite) (φ₁ φ₂ : N ⟶ M)
    (h : (modulePushforward B S hS g).map φ₁ = (modulePushforward B S hS g).map φ₂) :
    φ₁ = φ₂ := by
  obtain ⟨hrep, haff⟩ :=
    presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace B S hS Z.2 W.2 hg
  have h' : (smallBaseChangeModulePushforward.{u, u} B S hS g hrep).map φ₁ =
      (smallBaseChangeModulePushforward.{u, u} B S hS g hrep).map φ₂ := by
    have e := modulePushforwardChartIso B S hS g hrep
    exact (Iso.cancel_iso_hom_left (e.app N) _ _).1 ((e.hom.naturality φ₁).symm.trans
      ((congrArg (· ≫ e.hom.app M) h).trans (e.hom.naturality φ₂)))
  refine eq_of_forall_smallBaseChange B S hS g hrep haff hN φ₁ φ₂ fun V _ => ?_
  ext x
  exact congrArg (fun k => (k.val.app (op V)).hom x) h'

/-- **The counit of the inverse image along an affine morphism is an epimorphism on
quasi-coherent modules.**  For an affine morphism `g : Z ⟶ W` of algebraic spaces and a
quasi-coherent `𝒪_Z`-module `N`, the counit `g^*g_*N ⟶ N` is an epimorphism. -/
theorem epi_counit_modulePullbackAdjunction_app_of_isAffineHom (Z W : AlgebraicSpaces B S hS)
    (g : Z ⟶ W) (hg : IsAffineHom B S hS g.hom) (N : Modules.{u, u} B S hS Z.1 Z.2)
    (hN : N.IsQuasicoherentOnSite) :
    Epi ((modulePullbackAdjunction B S hS g).counit.app N) :=
  (modulePullbackAdjunction B S hS g).epi_counit_app_of_map_injective N
    fun _ => eq_of_modulePushforward_map_eq_of_isAffineHom B S hS g hg hN

end AlgebraicGeometry.Space

end
