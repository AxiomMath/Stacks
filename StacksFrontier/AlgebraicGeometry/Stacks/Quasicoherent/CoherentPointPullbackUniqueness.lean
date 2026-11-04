module

public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentFilteredColimitNoetherian
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineSchemeQuasicoherentEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoherentPointPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.PointPullbackFullyFaithful
public import StacksFrontier.CategoryTheory.KanExtension.ExtendMonoidal
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.Fiber

/-!
# A point is determined by its pullback functor on coherent modules

Let `𝒳` be an algebraic stack with affine diagonal and let `f₁, f₂ : Spec R ⟶ 𝒳` be two points.
If the tensor functors `f_i^* : Coh(𝒪_𝒳) ⥤ Mod^{fg}_R`
(`AlgebraicGeometry.Stack.AlgebraicStacks.coherentPointPullback`) are isomorphic as tensor
functors, then `f₁` and `f₂` are isomorphic by a 2-arrow inducing that isomorphism. This is the
uniqueness half of Stacks 0GRR.

The proof is the one of the source: the isomorphism extends uniquely to an isomorphism of the
functors `f_i^* : QCoh(𝒪_𝒳) ⥤ Mod_R`, both of which commute with all colimits
(`AlgebraicGeometry.Stack.AlgebraicStacks.preservesColimitsOfSize_pointPullback`), as coherent
modules are categorically compact in `QCoh(𝒪_𝒳)` and generate it under filtered colimits (Stacks
0FWY). The extension is again monoidal
(`CategoryTheory.ObjectProperty.isMonoidal_of_preservesFilteredColimits`), and Stacks 0GRP
(`AlgebraicGeometry.Stack.AlgebraicStacks.eq_and_exists_iso_pointPullbackTransportIso_eq`)
produces the 2-arrow.

The two inputs on `𝒳` — that coherent modules are categorically compact in `QCoh(𝒪_𝒳)` and that
every quasi-coherent module is a filtered colimit of coherent ones (Stacks 0GQZ and 0GRF, for
`𝒳` Noetherian) — are taken as explicit hypotheses `hP` and `hgen` on an object property `P` of
`QCoh(𝒪_𝒳)` cutting out the coherent modules (`hPcoh`), in the form in which Stacks 0FWY consumes
them.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_iso_coherentPointPullback_of_iso`: a monoidal
  isomorphism `F ⋙ ι ≅ f^*|_Coh` into `Mod_R` is a monoidal isomorphism `F ≅ f^*` into
  `Mod^{fg}_R`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.eq_and_exists_iso_of_coherentPointPullback_iso`: an
  isomorphism of tensor functors `f₁^* ≅ f₂^*` on `Coh(𝒪_𝒳)` comes from a 2-arrow `f₁ ≅ f₂`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.eq_and_exists_iso_of_iso_coherentPointPullback`: the
  uniqueness half of Stacks 0GRR, for a functor `F` identified with both `f₁^*` and `f₂^*`.
* `eq_and_exists_iso_of_iso_coherentPointPullback_of_isNoetherianStack` (in the namespace
  `AlgebraicGeometry.Stack.AlgebraicStacks`): the same for `𝒳` Noetherian, with no further
  hypothesis: the inputs `hP` and `hgen` are then Stacks 0GQZ
  (`AlgebraicGeometry.Stack.coherentQuasicoherent_le_isFinitelyPresentable`) and Stacks 0GRF
  (`AlgebraicGeometry.Stack.AlgebraicStacks.isFiltered_coherentSubobject_and_isColimit`, in the form
  `AlgebraicGeometry.Stack.ind_coherentQuasicoherent`).

## References

* [Stacks Project, Tag 0GRR](https://stacks.math.columbia.edu/tag/0GRR)
* [Stacks Project, Tag 0GRP](https://stacks.math.columbia.edu/tag/0GRP)
* [Stacks Project, Tag 0FWY](https://stacks.math.columbia.edu/tag/0FWY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Functor.LaxMonoidal

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u w w'

namespace AlgebraicGeometry.Stack.AlgebraicStacks

attribute [local instance] coherentAmbientMonoidal coherentAmbientBraided coherentAmbientSymmetric
  fppfModulesMonoidal fppfModulesBraided fppfModulesSymmetric
  coherentQuasicoherentInclusionBraided

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : AlgebraicStacks.{u, w} B S hS} {R : Type u} [CommRing R]
  {hR : B.Contains (Spec (CommRingCat.of R))}

/-- The unit morphism of `AlgebraicGeometry.Stack.AlgebraicStacks.coherentPointPullback` is that
of `AlgebraicGeometry.Stack.AlgebraicStacks.pointPullback`. -/
theorem coherentPointPullback_ε_hom (x : 𝒳.val.val.obj)
    (e : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x) ≅ Spec (CommRingCat.of R)) :
    (ε (coherentPointPullback B S hS 𝒳 x e)).hom = ε (pointPullback B S hS 𝒳 x e) := by
  have h : (ε (coherentPointPullback B S hS 𝒳 x e)).hom =
      ε (coherentQuasicoherentInclusion B S hS 𝒳 ⋙ pointPullback B S hS 𝒳 x e) := rfl
  rw [h, Functor.LaxMonoidal.comp_ε]
  exact (congrArg (ε (pointPullback B S hS 𝒳 x e) ≫ ·)
    ((pointPullback B S hS 𝒳 x e).map_id _)).trans (Category.comp_id _)

/-- The tensorator of `AlgebraicGeometry.Stack.AlgebraicStacks.coherentPointPullback` is that of
`AlgebraicGeometry.Stack.AlgebraicStacks.pointPullback`. -/
theorem coherentPointPullback_μ_hom (x : 𝒳.val.val.obj)
    (e : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x) ≅ Spec (CommRingCat.of R))
    (M N : Coh.{u, u, w} B S hS 𝒳) :
    (μ (coherentPointPullback B S hS 𝒳 x e) M N).hom =
      μ (pointPullback B S hS 𝒳 x e) ((coherentQuasicoherentInclusion B S hS 𝒳).obj M)
        ((coherentQuasicoherentInclusion B S hS 𝒳).obj N) := by
  have h : (μ (coherentPointPullback B S hS 𝒳 x e) M N).hom =
      μ (coherentQuasicoherentInclusion B S hS 𝒳 ⋙ pointPullback B S hS 𝒳 x e) M N := rfl
  rw [h, Functor.LaxMonoidal.comp_μ]
  exact (congrArg (μ (pointPullback B S hS 𝒳 x e) _ _ ≫ ·)
    ((pointPullback B S hS 𝒳 x e).map_id _)).trans (Category.comp_id _)

/-- **A monoidal identification with `f^*` lifts to finitely generated modules.** Let `F` be a
monoidal functor `Coh(𝒪_𝒳) ⥤ Mod^{fg}_R` and `x` a point of `𝒳` over `Spec R`. A monoidal
isomorphism between `F` followed by the inclusion `Mod^{fg}_R ⥤ Mod_R` and the restriction of
`f^* : QCoh(𝒪_𝒳) ⥤ Mod_R` to `Coh(𝒪_𝒳)` is a monoidal isomorphism `F ≅ f^*` of functors into
`Mod^{fg}_R` (`AlgebraicGeometry.Stack.AlgebraicStacks.coherentPointPullback`). -/
theorem exists_iso_coherentPointPullback_of_iso (F : Coh.{u, u, w} B S hS 𝒳 ⥤ FGModuleCat.{u} R)
    [F.Monoidal] (x : 𝒳.val.val.obj)
    (ex : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x) ≅ Spec (CommRingCat.of R))
    (E' : F ⋙ (ModuleCat.isFG.{u} R).ι ≅
      coherentQuasicoherentInclusion B S hS 𝒳 ⋙ pointPullback B S hS 𝒳 x ex)
    [NatTrans.IsMonoidal E'.hom] :
    ∃ E : F ≅ coherentPointPullback B S hS 𝒳 x ex, NatTrans.IsMonoidal E.hom := by
  refine ⟨NatIso.ofComponents (fun M ↦ (ModuleCat.isFG.{u} R).isoMk (E'.app M))
    (fun f ↦ (ModuleCat.isFG.{u} R).hom_ext (E'.hom.naturality f)), ⟨?_, fun M N ↦ ?_⟩⟩
  · apply (ModuleCat.isFG.{u} R).hom_ext
    have h := NatTrans.IsMonoidal.unit (τ := E'.hom)
    rw [Functor.LaxMonoidal.comp_ε, Functor.LaxMonoidal.comp_ε] at h
    have h' : (ε F).hom ≫ E'.hom.app (𝟙_ _) = ε (pointPullback B S hS 𝒳 x ex) :=
      (Category.id_comp _).symm.trans (h.trans ((congrArg (ε (pointPullback B S hS 𝒳 x ex) ≫ ·)
        ((pointPullback B S hS 𝒳 x ex).map_id _)).trans (Category.comp_id _)))
    rwa [← coherentPointPullback_ε_hom] at h'
  · apply (ModuleCat.isFG.{u} R).hom_ext
    have h := NatTrans.IsMonoidal.tensor (τ := E'.hom) M N
    rw [Functor.LaxMonoidal.comp_μ, Functor.LaxMonoidal.comp_μ] at h
    have h' : (μ F M N).hom ≫ E'.hom.app (M ⊗ N) = (E'.hom.app M ⊗ₘ E'.hom.app N) ≫
        μ (pointPullback B S hS 𝒳 x ex) ((coherentQuasicoherentInclusion B S hS 𝒳).obj M)
          ((coherentQuasicoherentInclusion B S hS 𝒳).obj N) :=
      (Category.id_comp _).symm.trans (h.trans
        ((congrArg (fun k ↦ (E'.hom.app M ⊗ₘ E'.hom.app N) ≫
          μ (pointPullback B S hS 𝒳 x ex) _ _ ≫ k)
          ((pointPullback B S hS 𝒳 x ex).map_id _)).trans (by rw [Category.comp_id])))
    rwa [← coherentPointPullback_μ_hom] at h'

/-- **An isomorphism of tensor functors `f₁^* ≅ f₂^*` on coherent modules comes from a 2-arrow.**
Let `𝒳` be an algebraic stack with affine diagonal (over `Spec ℤ`, Stacks 050D), let `P` be the
property of quasi-coherent `𝒪_𝒳`-modules of being coherent (`hPcoh`), and assume that coherent
modules are categorically compact in `QCoh(𝒪_𝒳)` (`hP`) and that every quasi-coherent module is a
filtered colimit of coherent ones (`hgen`) — Stacks 0GQZ and 0GRF for `𝒳` Noetherian. Let
`f₁, f₂ : Spec R ⟶ 𝒳` be points `x₁, x₂` over `q₁, q₂ : Spec R ⟶ S`, and let
`E : f₁^* ≅ f₂^*` be a monoidal isomorphism of the functors `Coh(𝒪_𝒳) ⥤ Mod^{fg}_R`. Then
`q₁ = q₂`, and there is a 2-arrow `a : x₁ ≅ x₂` over `Spec R` whose induced isomorphism of the
functors `f_i^* : QCoh(𝒪_𝒳) ⥤ Mod_R` restricts to `E` on coherent modules. -/
theorem eq_and_exists_iso_of_coherentPointPullback_iso
    (P : ObjectProperty (quasicoherentModules B S hS 𝒳))
    (hPcoh : ∀ M, P M ↔ IsCoherent B S hS 𝒳 M.obj) [LocallySmall.{u} P.FullSubcategory]
    (hP : P ≤ ObjectProperty.isFinitelyPresentable.{u} _) (hgen : ∀ M, P.ind.{u} M)
    (hΔ : Stack.IsAffineHom B (⊤_ Scheme.{u}) (contains_terminalScheme B)
      (Stack.diagonal.{u, u, u + 1} B (⊤_ Scheme.{u}) (contains_terminalScheme B)
        (AlgebraicStacks.viewOverIntegers B S hS (contains_terminalScheme B) 𝒳).val))
    {q₁ q₂ : B.obj hR ⟶ B.obj hS} {x₁ x₂ : 𝒳.val.val.obj}
    (hx₁ : 𝒳.val.val.p.obj x₁ = Over.mk q₁) (hx₂ : 𝒳.val.val.p.obj x₂ = Over.mk q₂)
    (E : coherentPointPullback B S hS 𝒳 x₁ (overSpecIso B S hS 𝒳 hx₁) ≅
      coherentPointPullback B S hS 𝒳 x₂ (overSpecIso B S hS 𝒳 hx₂))
    [NatTrans.IsMonoidal E.hom] :
    q₁ = q₂ ∧ ∃ (a : x₁ ≅ x₂) (ha : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map a.hom) ≫
        (overSpecIso B S hS 𝒳 hx₂).hom = (overSpecIso B S hS 𝒳 hx₁).hom),
      Functor.whiskerLeft (coherentQuasicoherentInclusion B S hS 𝒳)
          (pointPullbackTransportIso B S hS 𝒳 (overSpecIso B S hS 𝒳 hx₁)
            (overSpecIso B S hS 𝒳 hx₂) a ha).hom =
        (coherentPointPullbackCompIso B S hS 𝒳 x₁ _).inv ≫
          Functor.whiskerRight E.hom (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)) ≫
            (coherentPointPullbackCompIso B S hS 𝒳 x₂ _).hom := by
  have := preservesColimitsOfSize_pointPullback B S hS 𝒳 (x := x₁) (overSpecIso B S hS 𝒳 hx₁)
  have := preservesColimitsOfSize_pointPullback B S hS 𝒳 (x := x₂) (overSpecIso B S hS 𝒳 hx₂)
  let κ : P.FullSubcategory → Coh.{u, u, w} B S hS 𝒳 := fun M ↦ ⟨M.obj.obj, (hPcoh _).1 M.2⟩
  let κmap : ∀ {M N : P.FullSubcategory}, (M ⟶ N) → (κ M ⟶ κ N) :=
    fun f ↦ ObjectProperty.homMk f.hom.hom
  let τ₀ : P.ι ⋙ pointPullback B S hS 𝒳 x₁ (overSpecIso B S hS 𝒳 hx₁) ⟶
      P.ι ⋙ pointPullback B S hS 𝒳 x₂ (overSpecIso B S hS 𝒳 hx₂) :=
    { app := fun M ↦ (E.hom.app (κ M)).hom
      naturality := fun _ _ f ↦ congrArg InducedCategory.Hom.hom (E.hom.naturality (κmap f)) }
  let τ₀' : P.ι ⋙ pointPullback B S hS 𝒳 x₂ (overSpecIso B S hS 𝒳 hx₂) ⟶
      P.ι ⋙ pointPullback B S hS 𝒳 x₁ (overSpecIso B S hS 𝒳 hx₁) :=
    { app := fun M ↦ (E.inv.app (κ M)).hom
      naturality := fun _ _ f ↦ congrArg InducedCategory.Hom.hom (E.inv.naturality (κmap f)) }
  obtain ⟨φ, hφ, -⟩ := ObjectProperty.existsUnique_natTrans_of_preservesFilteredColimits P hP
    hgen _ _ τ₀
  obtain ⟨ψ, hψ, -⟩ := ObjectProperty.existsUnique_natTrans_of_preservesFilteredColimits P hP
    hgen _ _ τ₀'
  have hφM (M : P.FullSubcategory) : φ.app M.obj = (E.hom.app (κ M)).hom :=
    congrArg (fun γ ↦ γ.app M) hφ
  have hψM (M : P.FullSubcategory) : ψ.app M.obj = (E.inv.app (κ M)).hom :=
    congrArg (fun γ ↦ γ.app M) hψ
  have h₁ : φ ≫ ψ = 𝟙 _ := (ObjectProperty.existsUnique_natTrans_of_preservesFilteredColimits P hP
    hgen _ _ (Functor.whiskerLeft P.ι (φ ≫ ψ))).unique rfl <| NatTrans.ext <| funext fun M ↦ by
      refine Eq.symm ?_
      rw [Functor.whiskerLeft_app, Functor.whiskerLeft_app, NatTrans.comp_app, NatTrans.id_app]
      have h := congrArg InducedCategory.Hom.hom (E.hom_inv_id_app (κ M))
      exact (congrArg₂ (· ≫ ·) (hφM M) (hψM M)).trans h
  have h₂ : ψ ≫ φ = 𝟙 _ := (ObjectProperty.existsUnique_natTrans_of_preservesFilteredColimits P hP
    hgen _ _ (Functor.whiskerLeft P.ι (ψ ≫ φ))).unique rfl <| NatTrans.ext <| funext fun M ↦ by
      refine Eq.symm ?_
      rw [Functor.whiskerLeft_app, Functor.whiskerLeft_app, NatTrans.comp_app, NatTrans.id_app]
      have h := congrArg InducedCategory.Hom.hom (E.inv_hom_id_app (κ M))
      exact (congrArg₂ (· ≫ ·) (hψM M) (hφM M)).trans h
  let t : pointPullback B S hS 𝒳 x₁ (overSpecIso B S hS 𝒳 hx₁) ≅
      pointPullback B S hS 𝒳 x₂ (overSpecIso B S hS 𝒳 hx₂) := ⟨φ, ψ, h₁, h₂⟩
  have hunit : P (𝟙_ (quasicoherentModules B S hS 𝒳)) :=
    (hPcoh _).2 (isCoherent_sheafOfModules_unit B S hS 𝒳)
  have : NatTrans.IsMonoidal t.hom := by
    refine ObjectProperty.isMonoidal_of_preservesFilteredColimits P hP hgen φ ?_ ?_
    · have h : (ε (coherentPointPullback B S hS 𝒳 x₁ (overSpecIso B S hS 𝒳 hx₁))).hom ≫
          (E.hom.app (𝟙_ _)).hom =
            (ε (coherentPointPullback B S hS 𝒳 x₂ (overSpecIso B S hS 𝒳 hx₂))).hom :=
        congrArg InducedCategory.Hom.hom (NatTrans.IsMonoidal.unit (τ := E.hom))
      rw [coherentPointPullback_ε_hom, coherentPointPullback_ε_hom] at h
      rwa [hφM ⟨_, hunit⟩]
    · intro M N
      have h : (μ (coherentPointPullback B S hS 𝒳 x₁ (overSpecIso B S hS 𝒳 hx₁)) (κ M) (κ N)).hom ≫
          (E.hom.app (κ M ⊗ κ N)).hom = ((E.hom.app (κ M)).hom ⊗ₘ (E.hom.app (κ N)).hom) ≫
            (μ (coherentPointPullback B S hS 𝒳 x₂ (overSpecIso B S hS 𝒳 hx₂)) (κ M) (κ N)).hom :=
        congrArg InducedCategory.Hom.hom (NatTrans.IsMonoidal.tensor (τ := E.hom) (κ M) (κ N))
      rw [coherentPointPullback_μ_hom, coherentPointPullback_μ_hom] at h
      rwa [hφM M, hφM N, hφM ⟨_, (hPcoh (M.obj ⊗ N.obj)).2 (κ M ⊗ κ N).2⟩]
  obtain ⟨hq, a, ha, hat⟩ := eq_and_exists_iso_pointPullbackTransportIso_eq B S hS hΔ hx₁ hx₂ t
  refine ⟨hq, a, ha, ?_⟩
  rw [hat]
  refine NatTrans.ext (funext fun M ↦ ?_)
  simp only [coherentPointPullbackCompIso, Iso.refl_hom, Iso.refl_inv, Functor.whiskerLeft_app]
  exact hφM ⟨_, (hPcoh ((coherentQuasicoherentInclusion B S hS 𝒳).obj M)).2 M.2⟩

/-- **The uniqueness half of Stacks 0GRR.** Let `𝒳` be an algebraic stack with affine diagonal
(over `Spec ℤ`) in which coherent modules are categorically compact in `QCoh(𝒪_𝒳)` (`hP`) and
generate it under filtered colimits (`hgen`), as for `𝒳` Noetherian (Stacks 0GQZ, 0GRF). If a
tensor functor `F : Coh(𝒪_𝒳) ⥤ Mod^{fg}_R` comes from two points `f₁, f₂ : Spec R ⟶ 𝒳`, by monoidal
isomorphisms `E_i : F ≅ f_i^*`, then `f₁` and `f₂` lie over the same morphism `Spec R ⟶ S` and are
isomorphic by a 2-arrow `a`, whose induced isomorphism `f₁^* ≅ f₂^*` on `QCoh(𝒪_𝒳)` restricts to
`E₁⁻¹ ≫ E₂` on coherent modules. -/
theorem eq_and_exists_iso_of_iso_coherentPointPullback
    (P : ObjectProperty (quasicoherentModules B S hS 𝒳))
    (hPcoh : ∀ M, P M ↔ IsCoherent B S hS 𝒳 M.obj) [LocallySmall.{u} P.FullSubcategory]
    (hP : P ≤ ObjectProperty.isFinitelyPresentable.{u} _) (hgen : ∀ M, P.ind.{u} M)
    (hΔ : Stack.IsAffineHom B (⊤_ Scheme.{u}) (contains_terminalScheme B)
      (Stack.diagonal.{u, u, u + 1} B (⊤_ Scheme.{u}) (contains_terminalScheme B)
        (AlgebraicStacks.viewOverIntegers B S hS (contains_terminalScheme B) 𝒳).val))
    (F : Coh.{u, u, w} B S hS 𝒳 ⥤ FGModuleCat.{u} R) [F.Monoidal]
    {q₁ q₂ : B.obj hR ⟶ B.obj hS} {x₁ x₂ : 𝒳.val.val.obj}
    (hx₁ : 𝒳.val.val.p.obj x₁ = Over.mk q₁) (hx₂ : 𝒳.val.val.p.obj x₂ = Over.mk q₂)
    (E₁ : F ≅ coherentPointPullback B S hS 𝒳 x₁ (overSpecIso B S hS 𝒳 hx₁))
    (E₂ : F ≅ coherentPointPullback B S hS 𝒳 x₂ (overSpecIso B S hS 𝒳 hx₂))
    [NatTrans.IsMonoidal E₁.hom] [NatTrans.IsMonoidal E₂.hom] :
    q₁ = q₂ ∧ ∃ (a : x₁ ≅ x₂) (ha : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map a.hom) ≫
        (overSpecIso B S hS 𝒳 hx₂).hom = (overSpecIso B S hS 𝒳 hx₁).hom),
      Functor.whiskerLeft (coherentQuasicoherentInclusion B S hS 𝒳)
          (pointPullbackTransportIso B S hS 𝒳 (overSpecIso B S hS 𝒳 hx₁)
            (overSpecIso B S hS 𝒳 hx₂) a ha).hom =
        (coherentPointPullbackCompIso B S hS 𝒳 x₁ _).inv ≫
          Functor.whiskerRight (E₁.inv ≫ E₂.hom) (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)) ≫
            (coherentPointPullbackCompIso B S hS 𝒳 x₂ _).hom :=
  have : NatTrans.IsMonoidal (E₁.symm ≪≫ E₂).hom :=
    inferInstanceAs (NatTrans.IsMonoidal (E₁.inv ≫ E₂.hom))
  eq_and_exists_iso_of_coherentPointPullback_iso B S hS P hPcoh hP hgen hΔ hx₁ hx₂ (E₁.symm ≪≫ E₂)

/-- **The uniqueness half of Stacks 0GRR.** Let `𝒳` be a Noetherian algebraic stack with affine
diagonal (over `Spec ℤ`). If a tensor functor `F : Coh(𝒪_𝒳) ⥤ Mod^{fg}_R` comes from two points
`f₁, f₂ : Spec R ⟶ 𝒳`, by monoidal isomorphisms `E_i : F ≅ f_i^*`, then `f₁` and `f₂` lie over the
same morphism `Spec R ⟶ S` and are isomorphic by a 2-arrow `a`, whose induced isomorphism
`f₁^* ≅ f₂^*` on `QCoh(𝒪_𝒳)` restricts to `E₁⁻¹ ≫ E₂` on coherent modules.

This is `AlgebraicGeometry.Stack.AlgebraicStacks.eq_and_exists_iso_of_iso_coherentPointPullback`
with its inputs proved: coherent modules on a Noetherian algebraic stack are categorically compact
in `QCoh(𝒪_𝒳)` (Stacks 0GQZ) and every quasi-coherent module is a filtered colimit of coherent
ones (Stacks 0GRF). -/
theorem eq_and_exists_iso_of_iso_coherentPointPullback_of_isNoetherianStack
    (h𝒳 : IsNoetherianStack.{u, w, w'} B S hS 𝒳)
    (hΔ : Stack.IsAffineHom B (⊤_ Scheme.{u}) (contains_terminalScheme B)
      (Stack.diagonal.{u, u, u + 1} B (⊤_ Scheme.{u}) (contains_terminalScheme B)
        (AlgebraicStacks.viewOverIntegers B S hS (contains_terminalScheme B) 𝒳).val))
    (F : Coh.{u, u, w} B S hS 𝒳 ⥤ FGModuleCat.{u} R) [F.Monoidal]
    {q₁ q₂ : B.obj hR ⟶ B.obj hS} {x₁ x₂ : 𝒳.val.val.obj}
    (hx₁ : 𝒳.val.val.p.obj x₁ = Over.mk q₁) (hx₂ : 𝒳.val.val.p.obj x₂ = Over.mk q₂)
    (E₁ : F ≅ coherentPointPullback B S hS 𝒳 x₁ (overSpecIso B S hS 𝒳 hx₁))
    (E₂ : F ≅ coherentPointPullback B S hS 𝒳 x₂ (overSpecIso B S hS 𝒳 hx₂))
    [NatTrans.IsMonoidal E₁.hom] [NatTrans.IsMonoidal E₂.hom] :
    q₁ = q₂ ∧ ∃ (a : x₁ ≅ x₂) (ha : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map a.hom) ≫
        (overSpecIso B S hS 𝒳 hx₂).hom = (overSpecIso B S hS 𝒳 hx₁).hom),
      Functor.whiskerLeft (coherentQuasicoherentInclusion B S hS 𝒳)
          (pointPullbackTransportIso B S hS 𝒳 (overSpecIso B S hS 𝒳 hx₁)
            (overSpecIso B S hS 𝒳 hx₂) a ha).hom =
        (coherentPointPullbackCompIso B S hS 𝒳 x₁ _).inv ≫
          Functor.whiskerRight (E₁.inv ≫ E₂.hom) (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)) ≫
            (coherentPointPullbackCompIso B S hS 𝒳 x₂ _).hom :=
  eq_and_exists_iso_of_iso_coherentPointPullback B S hS (coherentQuasicoherent B S hS 𝒳)
    (fun _ ↦ Iff.rfl) (coherentQuasicoherent_le_isFinitelyPresentable B S hS 𝒳 h𝒳)
    (ind_coherentQuasicoherent B S hS 𝒳 h𝒳) hΔ F hx₁ hx₂ E₁ E₂

end AlgebraicGeometry.Stack.AlgebraicStacks
