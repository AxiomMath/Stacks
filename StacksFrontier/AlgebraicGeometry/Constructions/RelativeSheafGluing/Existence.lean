module

public import StacksFrontier.AlgebraicGeometry.Constructions.RelativeSheafGluing.PushforwardLimit

/-!
# Relative gluing of quasi-coherent sheaves: existence

The limit of the pushforwards of the local modules is a realization of a
`RelativeSheafGluingData`: `RelativeSheafGluingData.exists_realization` and
`RelativeSheafGluingData.exists_isPullback_localIso` (Stacks Project, Tag 01LI).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleHomGlue
open Stacks.AlgebraicGeometry.ModuleLimits

namespace Stacks.AlgebraicGeometry.RelativeSheafGluing

variable {S : Scheme.{u}} {𝒰 : S.OpenCover} [Category 𝒰.I₀] [𝒰.LocallyDirected]
  [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀]

namespace RelativeSheafGluingData

variable {d : Scheme.Cover.RelativeGluingData 𝒰} (D : RelativeSheafGluingData d)

section Glueing

open AlgebraicGeometry.Scheme.Modules

variable {M N : d.glued.Modules}
  (c : ∀ i, (Scheme.Modules.pullback (colimit.ι d.functor i)).obj M ⟶
    (Scheme.Modules.pullback (colimit.ι d.functor i)).obj N)

/-! ### Existence: assembling the realization

The glued module is `limit D.pushFunctor`; `RelativeSheafGluingData.isIso_chartProj`
identifies its restriction along the `i`-th chart with `D.obj i`.  What is left is to see that
these identifications exchange the prescribed transition isomorphisms, and that the glued module is
quasi-coherent.

The compatibility is proved on sections: read through
`RelativeSheafGluingData.chartProj_app`, the required identity between the restrictions
of the glued module is exactly the compatibility
`RelativeSheafGluingData.pic_compat` of the components of a section, and
`pullback_compat_of_restrict` transports the result to the inverse image.

Quasi-coherence is local on the glued scheme, and on the range of the `i`-th chart the glued module
is the quasi-coherent module `D.obj i`. -/

section Existence

/-- Restriction maps of a module along `U ≤ V ≤ W` compose to the restriction map for `U ≤ W`. -/
private lemma presheaf_map_homOfLE_comp {X : Scheme.{u}} (M : X.Modules) {U V W : X.Opens}
    (h₁ : V ≤ W) (h₂ : U ≤ V) (h₃ : U ≤ W) :
    M.presheaf.map (homOfLE h₁).op ≫ M.presheaf.map (homOfLE h₂).op =
      M.presheaf.map (homOfLE h₃).op := by
  rw [← M.presheaf.map_comp]
  exact presheaf_map_eq_presheaf_map _ _ _

/-- The components of a section of the glued module commute with the restriction maps. -/
private lemma pic_nat (a : 𝒰.I₀) {W W' : d.glued.Opens} (h : W' ≤ W)
    (hp : colimit.ι d.functor a ⁻¹ᵁ W' ≤ colimit.ι d.functor a ⁻¹ᵁ W) :
    (limit D.pushFunctor).presheaf.map (homOfLE h).op ≫ D.pic a W' =
      D.pic a W ≫ (D.obj a).presheaf.map (homOfLE hp).op := by
  refine ConcreteCategory.hom_ext _ _ fun s => ?_
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  exact app_presheaf_map_le
    (show limit D.pushFunctor ⟶
        (Scheme.Modules.pushforward (colimit.ι d.functor a)).obj (D.obj a) from
      limit.π D.pushFunctor (op a)) h s

/-- `RelativeSheafGluingData.pic_compat` at morphism level, with the open over which the
transition map is read chosen freely. -/
private lemma pic_compat' {i j : 𝒰.I₀} (hij : i ⟶ j) (V : (d.functor.obj i).Opens)
    (W : d.glued.Opens) (hA : d.functor.map hij ''ᵁ V ≤ colimit.ι d.functor j ⁻¹ᵁ W)
    (hB : V ≤ colimit.ι d.functor i ⁻¹ᵁ W) :
    D.pic j W ≫ (D.obj j).presheaf.map (homOfLE hA).op ≫ D.transSec hij V =
      D.pic i W ≫ (D.obj i).presheaf.map (homOfLE hB).op := by
  have hi : d.functor.map hij ''ᵁ V ≤ d.functor.map hij ''ᵁ (colimit.ι d.functor i ⁻¹ᵁ W) :=
    Scheme.Hom.image_mono _ hB
  have hmor : D.pic j W ≫ (D.obj j).presheaf.map (homOfLE (image_preimage_ι_le W hij)).op ≫
      D.transSec hij (colimit.ι d.functor i ⁻¹ᵁ W) = D.pic i W := by
    refine ConcreteCategory.hom_ext _ _ fun x => ?_
    simpa only [ConcreteCategory.comp_apply] using D.pic_compat hij W x
  rw [← hmor, ← presheaf_map_homOfLE_comp (D.obj j) (image_preimage_ι_le W hij) hi hA]
  simp only [Category.assoc]
  rw [D.transSec_nat hij hB hi]

/-- The local comparison of the glued module with the `i`-th local module, as an isomorphism. -/
private noncomputable abbrev chartRestrictIso (i : 𝒰.I₀) :
    (limit D.pushFunctor).restrict (colimit.ι d.functor i) ≅ D.obj i :=
  have := D.isIso_chartProj i
  asIso (D.chartProj i)

/-- **The compatibility of the local comparisons, on sections.**  Transporting a section of the
glued module to the `j`-th chart and then along the transition map of `hij` is transporting it to
the `i`-th chart. -/
private lemma chartProj_compat_app {i j : 𝒰.I₀} (hij : i ⟶ j) (V : (d.functor.obj i).Opens)
    (h1 : (d.functor.map hij ≫ colimit.ι d.functor j) ''ᵁ V ≤ colimit.ι d.functor i ''ᵁ V)
    (h2 : colimit.ι d.functor j ''ᵁ (d.functor.map hij ''ᵁ V) ≤
      (d.functor.map hij ≫ colimit.ι d.functor j) ''ᵁ V) :
    (limit D.pushFunctor).presheaf.map (homOfLE h1).op ≫
        (limit D.pushFunctor).presheaf.map (homOfLE h2).op ≫
          restrictHomApp (colimit.ι d.functor j) (D.chartProj j) (d.functor.map hij ''ᵁ V) ≫
            D.transSec hij V =
      restrictHomApp (colimit.ι d.functor i) (D.chartProj i) V := by
  have h3 : colimit.ι d.functor j ''ᵁ (d.functor.map hij ''ᵁ V) ≤
      colimit.ι d.functor i ''ᵁ V := h2.trans h1
  have hp : colimit.ι d.functor j ⁻¹ᵁ (colimit.ι d.functor j ''ᵁ (d.functor.map hij ''ᵁ V)) ≤
      colimit.ι d.functor j ⁻¹ᵁ (colimit.ι d.functor i ''ᵁ V) :=
    Scheme.Hom.preimage_mono _ h3
  have hgj : d.functor.map hij ''ᵁ V ≤
      colimit.ι d.functor j ⁻¹ᵁ (colimit.ι d.functor j ''ᵁ (d.functor.map hij ''ᵁ V)) :=
    (Scheme.Hom.preimage_image_eq (colimit.ι d.functor j) (d.functor.map hij ''ᵁ V)).ge
  have hA : d.functor.map hij ''ᵁ V ≤
      colimit.ι d.functor j ⁻¹ᵁ (colimit.ι d.functor i ''ᵁ V) := hgj.trans hp
  have hB : V ≤ colimit.ι d.functor i ⁻¹ᵁ (colimit.ι d.functor i ''ᵁ V) :=
    (Scheme.Hom.preimage_image_eq (colimit.ι d.functor i) V).ge
  have hmergeT := presheaf_map_homOfLE_comp (limit D.pushFunctor) h1 h2 h3
  calc (limit D.pushFunctor).presheaf.map (homOfLE h1).op ≫
        (limit D.pushFunctor).presheaf.map (homOfLE h2).op ≫
          restrictHomApp (colimit.ι d.functor j) (D.chartProj j) (d.functor.map hij ''ᵁ V) ≫
            D.transSec hij V
      = (limit D.pushFunctor).presheaf.map (homOfLE h3).op ≫
          D.pic j (colimit.ι d.functor j ''ᵁ (d.functor.map hij ''ᵁ V)) ≫
            (D.obj j).presheaf.map (homOfLE hgj).op ≫ D.transSec hij V := by
        rw [D.chartProj_app j (d.functor.map hij ''ᵁ V),
          ← Category.assoc ((limit D.pushFunctor).presheaf.map (homOfLE h1).op), hmergeT]
        simp only [Category.assoc]
    _ = D.pic j (colimit.ι d.functor i ''ᵁ V) ≫
          (D.obj j).presheaf.map (homOfLE hA).op ≫ D.transSec hij V := by
        rw [reassoc_of% (D.pic_nat j h3 hp),
          ← presheaf_map_homOfLE_comp (D.obj j) hp hgj hA]
        simp only [Category.assoc]
    _ = D.pic i (colimit.ι d.functor i ''ᵁ V) ≫
          (D.obj i).presheaf.map (homOfLE hB).op :=
        D.pic_compat' hij V (colimit.ι d.functor i ''ᵁ V) hA hB
    _ = restrictHomApp (colimit.ι d.functor i) (D.chartProj i) V := (D.chartProj_app i V).symm

/-- **The compatibility of the local comparisons.**  The identity of
`RelativeSheafGluingData.chartProj_compat_app`, at the level of the restriction
functor. -/
private lemma chartProj_compat {i j : 𝒰.I₀} (hij : i ⟶ j) :
    (Scheme.Modules.restrictFunctorCongr (colimit.w d.functor hij)).inv.app
          (limit D.pushFunctor) ≫
        (Scheme.Modules.restrictFunctorComp (d.functor.map hij)
            (colimit.ι d.functor j)).hom.app (limit D.pushFunctor) ≫
          (Scheme.Modules.restrictFunctor (d.functor.map hij)).map
              (D.chartRestrictIso j).hom ≫
            (Scheme.Modules.restrictFunctorIsoPullback (d.functor.map hij)).hom.app (D.obj j) ≫
              (D.transitionIso hij).hom =
      (D.chartRestrictIso i).hom := by
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  have h1 : (d.functor.map hij ≫ colimit.ι d.functor j) ''ᵁ V ≤
      colimit.ι d.functor i ''ᵁ V := (image_congr (colimit.w d.functor hij) V).le
  have h2 : colimit.ι d.functor j ''ᵁ (d.functor.map hij ''ᵁ V) ≤
      (d.functor.map hij ≫ colimit.ι d.functor j) ''ᵁ V :=
    (Scheme.Hom.comp_image (d.functor.map hij) (colimit.ι d.functor j) V).ge
  change ((Scheme.Modules.restrictFunctorCongr (colimit.w d.functor hij)).inv.app
        (limit D.pushFunctor)).app V ≫
      (((Scheme.Modules.restrictFunctorComp (d.functor.map hij)
            (colimit.ι d.functor j)).hom.app (limit D.pushFunctor)).app V ≫
        restrictHomApp (colimit.ι d.functor j) (D.chartProj j) (d.functor.map hij ''ᵁ V) ≫
          D.transSec hij V) =
    (restrictHomApp (colimit.ι d.functor i) (D.chartProj i) V :
      Γ(limit D.pushFunctor, colimit.ι d.functor i ''ᵁ V) ⟶ Γ(D.obj i, V))
  rw [Scheme.Modules.restrictFunctorCongr_inv_app_app,
    Scheme.Modules.restrictFunctorComp_hom_app_app,
    presheaf_map_eq_presheaf_map (limit D.pushFunctor) _ (homOfLE h1).op,
    presheaf_map_eq_presheaf_map (limit D.pushFunctor) _ (homOfLE h2).op]
  exact D.chartProj_compat_app hij V h1 h2

/-- **The local comparison, as the realization asks for it.**  The `i`-th local module is the
inverse image of the glued module along the `i`-th chart. -/
private noncomputable def chartIso (i : 𝒰.I₀) :
    D.obj i ≅ (Scheme.Modules.pullback (colimit.ι d.functor i)).obj (limit D.pushFunctor) :=
  (D.chartRestrictIso i).symm ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback (colimit.ι d.functor i)).app (limit D.pushFunctor)

/-- The local comparisons `RelativeSheafGluingData.chartIso` recover the prescribed
transition isomorphisms. -/
private lemma chartIso_compatible {i j : 𝒰.I₀} (hij : i ⟶ j) :
    (D.transitionIso hij).hom ≫ (D.chartIso i).hom =
      (Scheme.Modules.pullback (d.functor.map hij)).map (D.chartIso j).hom ≫
        (Scheme.Modules.pullbackComp (d.functor.map hij)
            (colimit.ι d.functor j)).hom.app (limit D.pushFunctor) ≫
          (Scheme.Modules.pullbackCongr (colimit.w d.functor hij)).hom.app
            (limit D.pushFunctor) :=
  pullback_compat_of_restrict (d.functor.map hij) (colimit.ι d.functor j)
    (colimit.w d.functor hij) (limit D.pushFunctor) (D.chartRestrictIso i)
    (D.chartRestrictIso j) (D.transitionIso hij).hom (D.chartProj_compat hij)

/-- **The glued module is quasi-coherent.**  On the range of the `i`-th chart it is the
quasi-coherent module `D.obj i`, and quasi-coherence is local on the glued scheme. -/
private lemma isQuasicoherent_limit : (limit D.pushFunctor).IsQuasicoherent := by
  have hcov : TopologicalSpace.IsOpenCover
      (fun a : Shrink 𝒰.I₀ =>
        (colimit.ι d.functor ((equivShrink 𝒰.I₀).symm a)).opensRange) := by
    refine TopologicalSpace.IsOpenCover.mk ?_
    exact (Equiv.iSup_comp (g := fun k : 𝒰.I₀ => (colimit.ι d.functor k).opensRange)
      (equivShrink 𝒰.I₀).symm).trans d.cover.isOpenCover_opensRange.iSup_eq_top
  refine isQuasicoherent_of_cover (limit D.pushFunctor) _ hcov fun a => ?_
  have := D.isQuasicoherent ((equivShrink 𝒰.I₀).symm a)
  exact isQuasicoherent_restrict_opensRange
    (colimit.ι d.functor ((equivShrink 𝒰.I₀).symm a)) (limit D.pushFunctor)
    (D.obj ((equivShrink 𝒰.I₀).symm a)) (D.chartRestrictIso ((equivShrink 𝒰.I₀).symm a))

end Existence

/-- **Stacks Project, Tag 01LI.**  *Existence.*  Let `𝒰` be a locally directed open cover of a
scheme `S` and let `d` be a relative gluing datum over it, so that `d` consists of schemes
`X i` over the members `U i` of `𝒰` with cartesian transition squares, and let `f : X ⟶ S` be the
relatively glued scheme of Tag 01LH.  Given a quasi-coherent module `F i` on each `X i` together
with isomorphisms `(ρ i j)^* (F j) ≅ F i` along the transition morphisms satisfying the cocycle
condition, there is a quasi-coherent module `F` on `X` and isomorphisms `F i ≅ (ι i)^* F`
identifying each `F i` with the inverse image of `F` on the `i`-th chart, under which the
prescribed isomorphisms `(ρ i j)^* (F j) ≅ F i` are recovered from `F`. -/
lemma exists_realization : Nonempty D.Realization :=
  ⟨{ sheaf := limit D.pushFunctor
     isQuasicoherent := D.isQuasicoherent_limit
     localIso := D.chartIso
     compatible := fun hij => D.chartIso_compatible hij }⟩

/-- **Stacks Project, Tag 01LI.**  *Existence of the whole package.*  The conclusion of Tag 01LI
spelled out: there is a morphism of schemes `f : X ⟶ S`, morphisms `i a : X a ⟶ X` compatible with
the transition morphisms of `d` and exhibiting each `X a` as the part of `X` lying over the `a`-th
member of the cover, and a quasi-coherent module `F` on `X` together with isomorphisms
`θ a : F a ≅ (i a)^* F`, such that the prescribed transition isomorphisms of the `F a` are the
ones induced by `F` through the `θ a`.

This is `RelativeSheafGluingData.exists_realization` together with the charts of the relatively
glued scheme and their two properties, which Tag 01LI quotes from Tag 01LH. -/
lemma exists_isPullback_localIso :
    ∃ (X : Scheme.{u}) (f : X ⟶ S) (i : ∀ a, d.functor.obj a ⟶ X)
      (_ : ∀ a, IsPullback (d.natTrans.app a) (i a) (𝒰.f a) f)
      (hi : ∀ {a b : 𝒰.I₀} (hab : a ⟶ b), d.functor.map hab ≫ i b = i a)
      (F : X.Modules), F.IsQuasicoherent ∧
        ∃ θ : ∀ a, D.obj a ≅ (Scheme.Modules.pullback (i a)).obj F,
          ∀ {a b : 𝒰.I₀} (hab : a ⟶ b),
            (D.transitionIso hab).hom ≫ (θ a).hom =
              (Scheme.Modules.pullback (d.functor.map hab)).map (θ b).hom ≫
                (Scheme.Modules.pullbackComp (d.functor.map hab) (i b)).hom.app F ≫
                  (Scheme.Modules.pullbackCongr (hi hab)).hom.app F := by
  obtain ⟨R⟩ := D.exists_realization
  exact ⟨d.glued, d.toBase, fun a => colimit.ι d.functor a, d.isPullback_natTrans_ι_toBase,
    fun hab => colimit.w d.functor hab, R.sheaf, R.isQuasicoherent, R.localIso,
    fun hab => R.compatible hab⟩

end Glueing

end RelativeSheafGluingData

end Stacks.AlgebraicGeometry.RelativeSheafGluing
