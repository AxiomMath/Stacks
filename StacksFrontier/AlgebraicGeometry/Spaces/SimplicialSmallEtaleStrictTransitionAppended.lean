module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleStrictDegree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphismAppendedIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.TwoIsoCoherenceOfToposHom
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleTransitionTensorPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestrictionNaturality

/-!
# The derived transitions of a pullback along an appended morphism

Let `S` be a simplicial-site situation with total ringed topos `(Sh(C), O)`, `g_n` its component
morphisms, `f_φ` its transition morphisms and `t_φ : g_n ⟶ g_m ∘ f_φ` the 2-morphism of
Stacks 04IC. Let `b : (Sh(C), O) ⟶ Z` be a morphism of ringed topoi after which `t_φ` becomes
invertible, `σ_φ : b ∘ g_n ≅ b ∘ (g_m ∘ f_φ)`. Then the derived transition
`Lf_φ^*(Lb^*M)_m ⟶ (Lb^*M)_n` of Stacks 0D9P is the derived pullback isomorphism of `σ_φ`,
inverted and read through the composition isomorphisms of Stacks 0D6D and the identifications
`Lg_k^* ≅ (-)_k` of the derived pullbacks along the component morphisms with restriction.

## Main results

* `CategoryTheory.SimplicialSiteSituation.derivedComponentModuleTransition_app_derivedPullback_eq`.

## References

* [Stacks Project, Tag 0D9P](https://stacks.math.columbia.edu/tag/0D9P)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 04IC](https://stacks.math.columbia.edu/tag/04IC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom
open Stacks.Cohomology.DerivedBaseChangeOfToposHom

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

/-- A diagram chase over arbitrary categories. A transition `t : R_m ⋙ L ⟶ R_n` is compared, at
an object `N` isomorphic by `cb` to an object `QX` where everything is computed, with a composite
through `ρ_k : G_k ≅ R_k`, a comparison `CI₁ : G_m ⋙ L ⟶ H` and three maps `CI₂, Iσ⁻¹, CI₃⁻¹` at
`N`. The hypotheses say how each factor composes with the comparisons `c` to the computed objects;
`hU` is the remaining identity between the computed maps. -/
theorem transition_eq_of_comparisons {𝒯 : Type*} {_ : Category 𝒯} {𝒞m : Type*}
    {_ : Category 𝒞m} {𝒞n : Type*} {_ : Category 𝒞n} (L : 𝒞m ⥤ 𝒞n) {Rm Gm : 𝒯 ⥤ 𝒞m}
    {Rn Gn H : 𝒯 ⥤ 𝒞n}
    (ρm : Gm ≅ Rm) (ρn : Gn ≅ Rn) (t : Rm ⋙ L ⟶ Rn) (CI₁ : Gm ⋙ L ⟶ H)
    {N QX : 𝒯} (cb : N ≅ QX)
    {B₂ B₃ V₂ V₃ W W₂ Wf Un Uf : 𝒞n} {Um Wm : 𝒞m}
    (CI₂ : H.obj N ⟶ B₂) (Iσ : B₃ ≅ B₂) (CI₃ : Gn.obj N ≅ B₃)
    (c₂ : B₂ ⟶ V₂) (c₃ : B₃ ⟶ V₃) (qσ : V₃ ≅ V₂) (hσ : Iσ.hom ≫ c₂ = c₃ ≫ qσ.hom)
    (cgn : Gn.obj QX ⟶ W) (q₃ : W ≅ V₃)
    (h₃ : CI₃.hom ≫ c₃ = Gn.map cb.hom ≫ cgn ≫ q₃.hom)
    (cH : H.obj QX ⟶ W₂) (q₂ : W₂ ⟶ V₂) (h₂ : CI₂ ≫ c₂ = H.map cb.hom ≫ cH ≫ q₂)
    (cgm : Gm.obj QX ⟶ Wm) (cf : L.obj Wm ⟶ Wf) (q₁ : Wf ⟶ W₂)
    (h₁ : CI₁.app QX ≫ cH = L.map cgm ≫ cf ≫ q₁)
    (FDm : Rm.obj QX ⟶ Um) (Em : Um ≅ Wm) (hm : ρm.hom.app QX ≫ FDm ≫ Em.hom = cgm)
    (FDn : Rn.obj QX ≅ Un) (En : Un ≅ W) (hn : ρn.hom.app QX ≫ FDn.hom ≫ En.hom = cgn)
    (cmp : L.obj Um ⟶ Uf) (qτ : Uf ⟶ Un) (ht : t.app QX = L.map FDm ≫ cmp ≫ qτ ≫ FDn.inv)
    (qw : Uf ≅ Wf) (hw : L.map Em.hom ≫ cf = cmp ≫ qw.hom)
    (hU : qτ ≫ En.hom ≫ q₃.hom ≫ qσ.hom = qw.hom ≫ q₁ ≫ q₂) :
    t.app N = L.map (ρm.inv.app N) ≫ CI₁.app N ≫ CI₂ ≫ Iσ.inv ≫ CI₃.inv ≫ ρn.hom.app N := by
  rw [← cancel_mono (Rn.map cb.hom ≫ FDn.hom ≫ En.hom)]
  have nt := t.naturality cb.hom
  have nρn := ρn.hom.naturality cb.hom
  have nρm := ρm.inv.naturality cb.hom
  have nCI := CI₁.naturality cb.hom
  simp only [Functor.comp_map] at nt nCI
  have hc₃ : Gn.map cb.hom ≫ cgn = CI₃.hom ≫ c₃ ≫ q₃.inv := by
    rw [reassoc_of% h₃, Iso.hom_inv_id, Category.comp_id]
  have hc₂ : Iσ.inv ≫ c₃ = c₂ ≫ qσ.inv := by
    rw [Iso.eq_comp_inv, Category.assoc, ← hσ, Iso.inv_hom_id_assoc]
  have hcmp : cmp = L.map Em.hom ≫ cf ≫ qw.inv := by
    rw [reassoc_of% hw, Iso.hom_inv_id, Category.comp_id]
  have key : qw.inv ≫ qτ ≫ En.hom = q₁ ≫ q₂ ≫ qσ.inv ≫ q₃.inv := by
    rw [Iso.inv_comp_eq, ← reassoc_of% hU]
    simp
  have hm' : ρm.inv.app N ≫ Gm.map cb.hom ≫ cgm = Rm.map cb.hom ≫ FDm ≫ Em.hom := by
    rw [← hm, ← reassoc_of% nρm, Iso.inv_hom_id_app_assoc]
  have hL := congrArg L.map hm'
  simp only [Functor.map_comp] at hL
  calc t.app N ≫ Rn.map cb.hom ≫ FDn.hom ≫ En.hom
      = L.map (Rm.map cb.hom) ≫ L.map FDm ≫ L.map Em.hom ≫ cf ≫ qw.inv ≫ qτ ≫ En.hom := by
        rw [← reassoc_of% nt, ht, hcmp]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = L.map (Rm.map cb.hom) ≫ L.map FDm ≫ L.map Em.hom ≫ cf ≫ q₁ ≫ q₂ ≫ qσ.inv ≫ q₃.inv := by
        rw [key]
    _ = (L.map (ρm.inv.app N) ≫ CI₁.app N ≫ CI₂ ≫ Iσ.inv ≫ CI₃.inv ≫ ρn.hom.app N) ≫
          Rn.map cb.hom ≫ FDn.hom ≫ En.hom := by
        simp only [Category.assoc]
        rw [← reassoc_of% nρn, hn, hc₃, Iso.inv_hom_id_assoc, reassoc_of% hc₂, reassoc_of% h₂,
          ← reassoc_of% nCI, reassoc_of% h₁, ← reassoc_of% hL]

/-- If `t = A ≫ m ≫ ρ`, `m = p ≫ u` and `u = q ≫ σ⁻¹ ≫ c`, then
`t ≫ ρ⁻¹ ≫ c⁻¹ ≫ σ = A ≫ p ≫ q`. -/
theorem comp_inv_comp_inv_comp_hom_eq {𝒞 : Type*} [Category* 𝒞] {P Q R G H K K' : 𝒞}
    {t : P ⟶ R} {A : P ⟶ Q} {m : Q ⟶ G} {ρh : G ⟶ R} {ρi : R ⟶ G} {p : Q ⟶ H} {u : H ⟶ G}
    {q : H ⟶ K} {σh : K' ⟶ K} {σi : K ⟶ K'} {ch : K' ⟶ G} {ci : G ⟶ K'}
    (hρ : ρh ≫ ρi = 𝟙 G) (hc : ch ≫ ci = 𝟙 K') (hσ : σi ≫ σh = 𝟙 K)
    (e₁ : t = A ≫ m ≫ ρh) (e₂ : m = p ≫ u)
    (e₃ : u = q ≫ σi ≫ ch) : t ≫ ρi ≫ ci ≫ σh = A ≫ p ≫ q := by
  subst e₁ e₂ e₃
  simp only [Category.assoc, reassoc_of% hρ, reassoc_of% hc, hσ, Category.comp_id]

/-- Images under a functor of a four-fold and a three-fold composite that agree upstairs. -/
theorem map_comp_comp_comp_eq_of_eq {𝒞 : Type*} [Category* 𝒞] {𝒟 : Type*} [Category* 𝒟]
    (Q : 𝒞 ⥤ 𝒟) {X₀ X₁ X₂ X₃ X₄ Y₁ Y₂ : 𝒞} {a : X₀ ⟶ X₁} {b : X₁ ⟶ X₂} {c : X₂ ⟶ X₃}
    {d : X₃ ⟶ X₄} {e : X₀ ⟶ Y₁} {f : Y₁ ⟶ Y₂} {g : Y₂ ⟶ X₄}
    (h : a ≫ b ≫ c ≫ d = e ≫ f ≫ g) :
    Q.map a ≫ Q.map b ≫ Q.map c ≫ Q.map d = Q.map e ≫ Q.map f ≫ Q.map g := by
  simp only [← Q.map_comp, h]

/-- A four-fold and a three-fold composite of maps of complexes agree in a degree when their
components there are given maps whose composites agree. -/
theorem comp_comp_comp_f_eq_of_eq {V : Type*} [Category* V] [Preadditive V] {ι : Type*}
    {c : ComplexShape ι} {K₀ K₁ K₂ K₃ K₄ L₁ L₂ : HomologicalComplex V c} (a : K₀ ⟶ K₁)
    (b : K₁ ⟶ K₂) (c' : K₂ ⟶ K₃) (d : K₃ ⟶ K₄) (e : K₀ ⟶ L₁) (f : L₁ ⟶ L₂) (g : L₂ ⟶ K₄)
    (i : ι) {a' : K₀.X i ⟶ K₁.X i} {b' : K₁.X i ⟶ K₂.X i} {c'' : K₂.X i ⟶ K₃.X i}
    {d' : K₃.X i ⟶ K₄.X i} {e' : K₀.X i ⟶ L₁.X i} {f' : L₁.X i ⟶ L₂.X i} {g' : L₂.X i ⟶ K₄.X i}
    (ha : a.f i = a') (hb : b.f i = b') (hc : c'.f i = c'') (hd : d.f i = d') (he : e.f i = e')
    (hf : f.f i = f') (hg : g.f i = g') (h : a' ≫ b' ≫ c'' ≫ d' = e' ≫ f' ≫ g') :
    (a ≫ b ≫ c' ≫ d).f i = (e ≫ f ≫ g).f i := by
  simp only [HomologicalComplex.comp_f, ha, hb, hc, hd, he, hf, hg, h]

/-- **A transition identity on homotopy categories from its module form.** For additive
functors and transformations at free variables, an identity between the transition `τ` read
through `e_n⁻¹, c₃⁻¹, σ` and the composite of `e_m⁻¹, c₁⁻¹, c₂⁻¹`, holding at every `B M`, holds on
homotopy categories at every `K(B) P`. -/
theorem mapHomotopyCategoryTransition_app_mapHomotopyCategory_obj_eq {ι : Type*}
    (c : ComplexShape ι) {𝒵 : Type*} {_ : Category 𝒵} {_ : Preadditive 𝒵} {𝒯 : Type*}
    {_ : Category 𝒯} {_ : Preadditive 𝒯} {𝒞m : Type*} {_ : Category 𝒞m} {_ : Preadditive 𝒞m}
    {𝒞n : Type*} {_ : Category 𝒞n} {_ : Preadditive 𝒞n} (B : 𝒵 ⥤ 𝒯) {Rm Gm : 𝒯 ⥤ 𝒞m}
    {Rn Gn Hm : 𝒯 ⥤ 𝒞n} (Fφ : 𝒞m ⥤ 𝒞n) {Kn Km : 𝒵 ⥤ 𝒞n} {_ : B.Additive} {_ : Rm.Additive}
    {_ : Gm.Additive} {_ : Rn.Additive} {_ : Gn.Additive} {_ : Hm.Additive} {_ : Fφ.Additive}
    {_ : Kn.Additive} {_ : Km.Additive}
    (τ : Rm ⋙ Fφ ⟶ Rn) (en : Gn ≅ Rn) (em : Gm ≅ Rm) (c₃ : Kn ≅ B ⋙ Gn) (σ : Kn ≅ Km)
    (c₁ : Hm ≅ Gm ⋙ Fφ) (c₂ : Km ≅ B ⋙ Hm)
    (h : ∀ M : 𝒵, τ.app (B.obj M) ≫ en.symm.hom.app (B.obj M) ≫ c₃.symm.hom.app M ≫
        σ.hom.app M =
      Fφ.map (em.symm.hom.app (B.obj M)) ≫ c₁.symm.hom.app (B.obj M) ≫ c₂.symm.hom.app M)
    (P : HomotopyCategory 𝒵 c) :
    (mapHomotopyCategoryTransition c Rm Fφ Rn τ).app ((B.mapHomotopyCategory c).obj P) ≫
        (NatTrans.mapHomotopyCategory en.symm.hom c).app ((B.mapHomotopyCategory c).obj P) ≫
        (Functor.mapHomotopyCategoryCompIso c₃.symm c).hom.app P ≫
        (NatTrans.mapHomotopyCategory σ.hom c).app P =
      (Fφ.mapHomotopyCategory c).map
          ((NatTrans.mapHomotopyCategory em.symm.hom c).app ((B.mapHomotopyCategory c).obj P)) ≫
        (Functor.mapHomotopyCategoryCompIso c₁.symm c).hom.app ((B.mapHomotopyCategory c).obj P) ≫
        (Functor.mapHomotopyCategoryCompIso c₂.symm c).hom.app P := by
  rw [mapHomotopyCategoryTransition_app, mapHomotopyCategoryCompIso_hom_app,
    mapHomotopyCategoryCompIso_hom_app, mapHomotopyCategoryCompIso_hom_app]
  refine map_comp_comp_comp_eq_of_eq (HomotopyCategory.quotient _ _) ?_
  refine HomologicalComplex.hom_ext _ _ (fun i => ?_)
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f]
  exact h (P.as.X i)

end CategoryTheory

namespace CategoryTheory.SimplicialSiteSituation

attribute [local instance] hasWeakSheafifyComponent hasSheafifyTotal
  CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})
  {Z : RingedTopos.{u, u, u}}
  [Z.J.HasSheafCompose (forget RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Z.J (Type u)]
  (b : RingedToposHom (S.totalRingedTopos O) Z)

/-- The 2-isomorphism `b ∘ g_n ≅ b ∘ (g_m ∘ f_φ)` of the 2-morphism of Stacks 04IC with `b`
appended, when that makes it invertible. -/
abbrev componentAppendedTwoIso {m n : SimplexCategory} (φ : m ⟶ n)
    (h : IsIso ((S.componentRingedTwoMorphism O φ).whiskerRight b).t) :
    RingedToposHom.TwoIso (b.comp (componentRingedToposHom S O n))
      (b.comp ((componentRingedToposHom S O m).comp (S.transitionRingedToposHom O φ))) :=
  ((S.componentRingedTwoMorphism O φ).whiskerRight b).toTwoIso h

omit [HasSheafify Z.J AddCommGrpCat] [Z.J.WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify Z.J (Type u)] in
/-- **The transition of a pullback along `b`, on sheaves of modules.** The transition
`f_φ^*(b^*M)_m ⟶ (b^*M)_n` between the restrictions, read through the identifications
`g_k^* ≅ (-)_k`, the composition isomorphisms of Stacks 03D8 and the pullback isomorphism of
`σ_φ : b ∘ g_n ≅ b ∘ (g_m ∘ f_φ)`, is the composite of the compositors. -/
theorem componentModulesTransition_app_pullbackModules {m n : SimplexCategory} (φ : m ⟶ n)
    (h : IsIso ((S.componentRingedTwoMorphism O φ).whiskerRight b).t)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) :
    (S.componentModulesTransition O φ).app (b.toModulesHom.pullbackModules.obj M) ≫
        (componentPullbackModulesRestrictionIso S O n).symm.hom.app
          (b.toModulesHom.pullbackModules.obj M) ≫
        (RingedToposHom.pullbackModulesCompIso (componentRingedToposHom S O n) b).symm.hom.app M ≫
        (S.componentAppendedTwoIso O b φ h).pullbackModulesIso.hom.app M =
      (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.map
          ((componentPullbackModulesRestrictionIso S O m).symm.hom.app
            (b.toModulesHom.pullbackModules.obj M)) ≫
        (RingedToposHom.pullbackModulesCompIso (S.transitionRingedToposHom O φ)
          (componentRingedToposHom S O m)).symm.hom.app (b.toModulesHom.pullbackModules.obj M) ≫
        (RingedToposHom.pullbackModulesCompIso
          ((componentRingedToposHom S O m).comp (S.transitionRingedToposHom O φ)) b).symm.hom.app
            M := by
  simp only [Iso.symm_hom]
  have h1 := RingedToposHom.TwoMorphism.whiskerLeft_pullbackModulesMap_eq_pullbackModulesIso
    (S.componentRingedTwoMorphism O φ) b h
  have h2 := congrArg (fun α => α.app M) h1
  simp only [Functor.whiskerLeft_app, NatTrans.comp_app] at h2
  have e1 := S.componentModuleTransition_app_eq_moduleFiberTransition O φ
    (b.toModulesHom.pullbackModules.obj M)
  have e2 : (S.moduleFiberTransition O φ).app (b.toModulesHom.pullbackModules.obj M) =
      (RingedToposHom.pullbackModulesCompIso (S.transitionRingedToposHom O φ)
          (componentRingedToposHom S O m)).inv.app (b.toModulesHom.pullbackModules.obj M) ≫
        (S.componentRingedTwoMorphism O φ).pullbackModulesMap.app
          (b.toModulesHom.pullbackModules.obj M) := by
    rw [moduleFiberTransition, NatTrans.comp_app]
  exact CategoryTheory.comp_inv_comp_inv_comp_hom_eq (Iso.hom_inv_id_app _ _)
    (Iso.hom_inv_id_app _ _) (Iso.inv_hom_id_app _ _) e1 e2 h2

omit [HasSheafify Z.J AddCommGrpCat] [Z.J.WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify Z.J (Type u)] in
/-- `CategoryTheory.SimplicialSiteSituation.componentModulesTransition_app_pullbackModules` on
homotopy categories, at the degreewise pullback along `b` of a complex. -/
theorem mapHomotopyCategoryTransition_app_pullbackMapHomotopy {m n : SimplexCategory}
    (φ : m ⟶ n) (h : IsIso ((S.componentRingedTwoMorphism O φ).whiskerRight b).t)
    (P : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
      (ComplexShape.up ℤ)) :
    (mapHomotopyCategoryTransition (ComplexShape.up ℤ) (S.componentModulesRestriction O m)
        (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules
        (S.componentModulesRestriction O n) (S.componentModulesTransition O φ)).app
          ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy b).obj P) ≫
      (NatTrans.mapHomotopyCategory (componentPullbackModulesRestrictionIso S O n).symm.hom
        (ComplexShape.up ℤ)).app
          ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy b).obj P) ≫
      (Functor.mapHomotopyCategoryCompIso
        (RingedToposHom.pullbackModulesCompIso (componentRingedToposHom S O n) b).symm
        (ComplexShape.up ℤ)).hom.app P ≫
      (NatTrans.mapHomotopyCategory (S.componentAppendedTwoIso O b φ h).pullbackModulesIso.hom
        (ComplexShape.up ℤ)).app P =
    ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.mapHomotopyCategory
        (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomotopyCategory (componentPullbackModulesRestrictionIso S O m).symm.hom
          (ComplexShape.up ℤ)).app
            ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy b).obj P)) ≫
      (Functor.mapHomotopyCategoryCompIso
        (RingedToposHom.pullbackModulesCompIso (S.transitionRingedToposHom O φ)
          (componentRingedToposHom S O m)).symm (ComplexShape.up ℤ)).hom.app
            ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy b).obj P) ≫
      (Functor.mapHomotopyCategoryCompIso
        (RingedToposHom.pullbackModulesCompIso
          ((componentRingedToposHom S O m).comp (S.transitionRingedToposHom O φ)) b).symm
        (ComplexShape.up ℤ)).hom.app P :=
  mapHomotopyCategoryTransition_app_mapHomotopyCategory_obj_eq (ComplexShape.up ℤ)
    b.toModulesHom.pullbackModules (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules
    (S.componentModulesTransition O φ) (componentPullbackModulesRestrictionIso S O n)
    (componentPullbackModulesRestrictionIso S O m)
    (RingedToposHom.pullbackModulesCompIso (componentRingedToposHom S O n) b)
    (S.componentAppendedTwoIso O b φ h).pullbackModulesIso
    (RingedToposHom.pullbackModulesCompIso (S.transitionRingedToposHom O φ)
      (componentRingedToposHom S O m))
    (RingedToposHom.pullbackModulesCompIso
      ((componentRingedToposHom S O m).comp (S.transitionRingedToposHom O φ)) b)
    (S.componentModulesTransition_app_pullbackModules O b φ h) P

end CategoryTheory.SimplicialSiteSituation

namespace Stacks.Cohomology.DerivedPullbackOfToposHom

variable {Z : RingedTopos.{u, u, u}}
  [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Two natural transformations out of the derived category of a ringed topos agree as soon as
they agree at the K-flat complexes with flat terms, which resolve every object (Stacks 06YS). -/
theorem natTrans_ext_of_isKFlat {𝒜 : Type*} [Category* 𝒜]
    {F G : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ⥤ 𝒜}
    {α β : F ⟶ G}
    (h : ∀ P, Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat (Y := Z) P →
      α.app (DerivedCategory.Qh.obj P) = β.app (DerivedCategory.Qh.obj P)) : α = β := by
  ext M
  have := Localization.essSurj
    (DerivedCategory.Qh (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)))
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
  obtain ⟨P, hP, s, hs⟩ :=
    Stacks.Cohomology.DerivedPullbackCompositionOfToposHom.hasResolutions_isKFlat' (Y := Z)
      (DerivedCategory.Qh.objPreimage M)
  have hsi : IsIso (DerivedCategory.Qh.map s) := Localization.inverts DerivedCategory.Qh _ s hs
  let ν : DerivedCategory.Qh.obj P ≅ M :=
    asIso (DerivedCategory.Qh.map s) ≪≫ DerivedCategory.Qh.objObjPreimageIso M
  rw [← cancel_epi (F.map ν.hom), α.naturality, β.naturality, h P hP]

end Stacks.Cohomology.DerivedPullbackOfToposHom

namespace CategoryTheory.SimplicialSiteSituation

attribute [local instance] hasWeakSheafifyComponent hasSheafifyTotal
  CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})
  {Z : RingedTopos.{u, u, u}}
  [Z.J.HasSheafCompose (forget RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Z.J (Type u)]
  (b : RingedToposHom (S.totalRingedTopos O) Z)

/-- **The derived transitions of `Lb^*M` are the derived pullback isomorphisms of `σ_φ`.** If the
2-morphism `t_φ : g_n ⟶ g_m ∘ f_φ` of Stacks 04IC becomes invertible after `b` is appended, with
inverse-image 2-isomorphism `σ_φ`, then the derived transition `Lf_φ^*(Lb^*M)_m ⟶ (Lb^*M)_n` of
Stacks 0D9P is, through `Lg_k^* ≅ (-)_k` and the composition isomorphisms of Stacks 0D6D, the
inverse of the derived pullback isomorphism of `σ_φ`. -/
theorem derivedComponentModuleTransition_app_derivedPullback_eq {m n : SimplexCategory}
    (φ : m ⟶ n) (h : IsIso ((S.componentRingedTwoMorphism O φ).whiskerRight b).t)
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))) :
    (S.derivedComponentModuleTransition O φ).app ((derivedPullback b).obj M) =
      (S.derivedTransitionPullback O φ).map
          ((S.derivedPullbackComponentIsoSimplicialSmallEtaleStrictDegree O m).inv.app
            ((derivedPullback b).obj M)) ≫
        (derivedPullbackCompComparison (S.transitionRingedToposHom O φ)
          (componentRingedToposHom S O m)).app ((derivedPullback b).obj M) ≫
        (derivedPullbackCompComparison
          ((componentRingedToposHom S O m).comp (S.transitionRingedToposHom O φ)) b).app M ≫
        (derivedPullbackIsoOfTwoIso (S.componentAppendedTwoIso O b φ h)).inv.app M ≫
        (derivedPullbackCompIso (componentRingedToposHom S O n) b).inv.app M ≫
        (S.derivedPullbackComponentIsoSimplicialSmallEtaleStrictDegree O n).hom.app
          ((derivedPullback b).obj M) := by
  have key : Functor.whiskerLeft (derivedPullback b) (S.derivedComponentModuleTransition O φ) =
      Functor.whiskerLeft (derivedPullback b) (Functor.whiskerRight
          (S.derivedPullbackComponentIsoSimplicialSmallEtaleStrictDegree O m).inv
          (S.derivedTransitionPullback O φ)) ≫
        Functor.whiskerLeft (derivedPullback b) (derivedPullbackCompComparison
          (S.transitionRingedToposHom O φ) (componentRingedToposHom S O m)) ≫
        derivedPullbackCompComparison
          ((componentRingedToposHom S O m).comp (S.transitionRingedToposHom O φ)) b ≫
        (derivedPullbackIsoOfTwoIso (S.componentAppendedTwoIso O b φ h)).inv ≫
        (derivedPullbackCompIso (componentRingedToposHom S O n) b).inv ≫
        Functor.whiskerLeft (derivedPullback b)
          (S.derivedPullbackComponentIsoSimplicialSmallEtaleStrictDegree O n).hom := by
    refine Stacks.Cohomology.DerivedPullbackOfToposHom.natTrans_ext_of_isKFlat (fun P hP => ?_)
    have := isIso_derivedPullbackComparison_app_isKFlat b P hP
    have hσ := derivedPullbackIsoOfTwoIso_hom_fac (S.componentAppendedTwoIso O b φ h) P
    have h₃ := derivedPullbackCompComparison_app_comp_derivedPullbackComparison_app'
      (componentRingedToposHom S O n) b P
    have h₂ := derivedPullbackCompComparison_app_comp_derivedPullbackComparison_app'
      ((componentRingedToposHom S O m).comp (S.transitionRingedToposHom O φ)) b P
    have h₁ := derivedPullbackCompComparison_app_comp_derivedPullbackComparison_app'
      (S.transitionRingedToposHom O φ) (componentRingedToposHom S O m)
      ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy b).obj P)
    have hk := fun k : SimplexCategory =>
      Stacks.Homology.leftDerivedIsoMapDerivedCategoryOfIso_hom_app _
        (S.componentModulesRestriction O k)
        (derivedPullback (X := S.componentRingedTopos O k) (Y := S.totalRingedTopos O)
          (componentRingedToposHom S O k))
        (derivedPullbackComparison (X := S.componentRingedTopos O k) (Y := S.totalRingedTopos O)
          (componentRingedToposHom S O k))
        (componentPullbackModulesRestrictionIso S O k)
        ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy b).obj P)
    have ht := liftedTransition_app_q (S.componentModulesRestriction O m).mapDerivedCategoryFactorsh
      (S.derivedTransitionComparison O φ)
      (S.componentModulesRestriction O n).mapDerivedCategoryFactorsh
      (mapHomotopyCategoryTransition (ComplexShape.up ℤ) (S.componentModulesRestriction O m)
        (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules
        (S.componentModulesRestriction O n) (S.componentModulesTransition O φ))
      (HomotopyCategory.quasiIso ((S.totalRingedTopos O).Modules) (ComplexShape.up ℤ))
      ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy b).obj P)
    have hw := (derivedPullbackComparison (X := S.componentRingedTopos O n)
      (Y := S.componentRingedTopos O m) (S.transitionRingedToposHom O φ)).naturality
      ((NatTrans.mapHomotopyCategory (componentPullbackModulesRestrictionIso S O m).symm.hom
        (ComplexShape.up ℤ)).app
          ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy b).obj P))
    have hU := map_comp_comp_comp_eq_of_eq DerivedCategory.Qh
      (S.mapHomotopyCategoryTransition_app_pullbackMapHomotopy O b φ h P)
    exact transition_eq_of_comparisons (S.derivedTransitionPullback O φ)
      (S.derivedPullbackComponentIsoSimplicialSmallEtaleStrictDegree O m)
      (S.derivedPullbackComponentIsoSimplicialSmallEtaleStrictDegree O n)
      (S.derivedComponentModuleTransition O φ)
      (derivedPullbackCompComparison (S.transitionRingedToposHom O φ)
        (componentRingedToposHom S O m))
      (asIso ((derivedPullbackComparison b).app P))
      ((derivedPullbackCompComparison
        ((componentRingedToposHom S O m).comp (S.transitionRingedToposHom O φ)) b).app
          (DerivedCategory.Qh.obj P))
      ((derivedPullbackIsoOfTwoIso (S.componentAppendedTwoIso O b φ h)).app
        (DerivedCategory.Qh.obj P))
      ((derivedPullbackCompIso (componentRingedToposHom S O n) b).app (DerivedCategory.Qh.obj P))
      _ _ (DerivedCategory.Qh.mapIso ((Stacks.Homology.mapHomotopyCategoryIso
        (S.componentAppendedTwoIso O b φ h).pullbackModulesIso (ComplexShape.up ℤ)).app P)) hσ
      _ (DerivedCategory.Qh.mapIso ((Functor.mapHomotopyCategoryCompIso
        (RingedToposHom.pullbackModulesCompIso (componentRingedToposHom S O n) b).symm
        (ComplexShape.up ℤ)).app P)) h₃
      _ _ h₂ _ _ _ h₁
      _ (DerivedCategory.Qh.mapIso ((Stacks.Homology.mapHomotopyCategoryIso
        (componentPullbackModulesRestrictionIso S O m).symm (ComplexShape.up ℤ)).app
          ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy b).obj P))) (hk m)
      ((S.componentModulesRestriction O n).mapDerivedCategoryFactorsh.app
        ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy b).obj P))
      (DerivedCategory.Qh.mapIso ((Stacks.Homology.mapHomotopyCategoryIso
        (componentPullbackModulesRestrictionIso S O n).symm (ComplexShape.up ℤ)).app
          ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy b).obj P))) (hk n)
      _ _ ht
      ((pullbackOnHomotopy (S.transitionRingedToposHom O φ)).mapIso
        ((Stacks.Homology.mapHomotopyCategoryIso
          (componentPullbackModulesRestrictionIso S O m).symm (ComplexShape.up ℤ)).app
            ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy b).obj P))) hw hU
  exact congr_app key M

end CategoryTheory.SimplicialSiteSituation

end
