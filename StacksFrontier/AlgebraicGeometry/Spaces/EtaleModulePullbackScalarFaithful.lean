module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ScalarFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms

/-!
# Étale pullback preserves scalar faithfulness

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces. If `𝒪_Y` acts faithfully on an
`𝒪_Y`-module `M`, that is `𝒪_Y → ℋom(M, M)` is injective, then `𝒪_X` acts faithfully on `f^*M`.
The sections of `f^*M` over an étale chart `U` of `X` are those of `M` over the composite chart of
`Y`, and every chart of `Y` over that composite comes from a chart of `X` over `U`.

## Main results

* `AlgebraicGeometry.Space.isScalarFaithful_etaleModulePullback`.
* `AlgebraicGeometry.Space.isScalarFaithful_modulePullback`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}

/-- **Étale restriction preserves scalar faithfulness.** A section `s` of `𝒪_X` over `U` killing
every section of `f^*M` over charts above `U` kills every section of `M` over charts of `Y` above
the composite chart: such a chart is, up to the identity of its scheme, the composite of a chart
of `X` above `U`. -/
theorem isScalarFaithful_etaleModulePullback (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    {M : Modules.{u, u} B S hS Y.1 Y.2} (hM : SheafOfModules.IsScalarFaithful M) :
    SheafOfModules.IsScalarFaithful ((etaleModulePullback B S hS f hf).obj M) := by
  intro U s hs
  let U₀ : SmallEtale B S hS X.1 := U.unop
  refine hM (op ((smallEtalePostcomp B S hS f hf).obj U₀)) s fun V i m => ?_
  let V₀ : SmallEtale B S hS Y.1 := V.unop
  let i₀ : V₀ ⟶ (smallEtalePostcomp B S hS f hf).obj U₀ := i.unop
  let ψ : yoneda.obj V₀.1.left ⟶ X.1 := yoneda.map i₀.hom.left ≫ U₀.1.hom
  have hψ : ψ ≫ f.hom = V₀.1.hom := (Category.assoc _ _ _).trans (CostructuredArrow.w i₀.hom)
  have hV' : IsEtaleChart B S hS X.1 (CostructuredArrow.mk ψ) := by
    have hcomp : IsEtale B S hS (ψ ≫ f.hom) := by
      rw [hψ]
      exact (isEtale_iff_presheaf_of_yoneda B S hS _).2 V₀.2
    exact (isEtale_iff_presheaf_of_yoneda B S hS ψ).1
      (isEtale_of_isEtale_over B S hS (isAlgebraicSpace_yoneda B S hS _) X.2 Y.2 ψ (ψ ≫ f.hom)
        f.hom hcomp hf rfl)
  let V' : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk ψ, hV'⟩
  let u : V' ⟶ U₀ := InducedCategory.homMk (CostructuredArrow.homMk i₀.hom.left rfl)
  let g : (smallEtalePostcomp B S hS f hf).obj V' ⟶ V₀ :=
    InducedCategory.homMk (CostructuredArrow.homMk (𝟙 _)
      (((congrArg (· ≫ V₀.1.hom) (yoneda.map_id _)).trans (Category.id_comp _)).trans hψ.symm))
  let σ : V₀ ⟶ (smallEtalePostcomp B S hS f hf).obj V' :=
    InducedCategory.homMk (CostructuredArrow.homMk (𝟙 _)
      (((congrArg (· ≫ ψ ≫ f.hom) (yoneda.map_id _)).trans (Category.id_comp _)).trans hψ))
  have hσu : σ ≫ (smallEtalePostcomp B S hS f hf).map u = i₀ :=
    InducedCategory.hom_ext (CostructuredArrow.hom_ext _ _ (Category.id_comp _))
  have hσg : σ ≫ g = 𝟙 _ :=
    InducedCategory.hom_ext (CostructuredArrow.hom_ext _ _ (Category.id_comp _))
  let R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O
  have h1 : (R.obj.map ((smallEtalePostcomp B S hS f hf).map u).op).hom s • M.val.map g.op m = 0 :=
    hs (op V') u.op (M.val.map g.op m)
  have hg : g.op ≫ σ.op = 𝟙 (op V₀) := Quiver.Hom.unop_inj hσg
  have hu : ((smallEtalePostcomp B S hS f hf).map u).op ≫ σ.op = i := Quiver.Hom.unop_inj hσu
  have e1 : M.val.map σ.op (M.val.map g.op m) = m :=
    (PresheafOfModules.map_comp_apply M.val g.op σ.op m).symm.trans
      ((PresheafOfModules.congr_map_apply M.val hg m).trans (by
        change M.val.presheaf.map (𝟙 _) m = m
        simp only [CategoryTheory.Functor.map_id]
        rfl))
  have e2 : (R.obj.map σ.op).hom ((R.obj.map ((smallEtalePostcomp B S hS f hf).map u).op).hom s) =
      (R.obj.map i).hom s :=
    congrArg (fun φ => RingCat.Hom.hom φ s)
      ((R.obj.map_comp _ _).symm.trans (congrArg R.obj.map hu))
  have h3 : M.val.map σ.op (((R.obj.map ((smallEtalePostcomp B S hS f hf).map u).op).hom s) •
      M.val.map g.op m) = 0 := (congrArg _ h1).trans (map_zero _)
  exact (congrArg₂ (· • ·) e2 e1).symm.trans
    ((PresheafOfModules.map_smul M.val σ.op _ _).symm.trans h3)

/-- **Pullback along an étale morphism preserves scalar faithfulness.** -/
theorem isScalarFaithful_modulePullback (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    {M : Modules.{u, u} B S hS Y.1 Y.2} (hM : SheafOfModules.IsScalarFaithful M) :
    SheafOfModules.IsScalarFaithful ((modulePullback B S hS f).obj M) :=
  (isScalarFaithful_etaleModulePullback B S hS f hf hM).of_iso
    ((modulePullbackIsoEtaleModulePullback B S hS f hf).app M).symm

end AlgebraicGeometry.Space
