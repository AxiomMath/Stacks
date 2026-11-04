module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UniverseLiftFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalizedPullbackQuasicoherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardRightExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentAlgebras
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackGlobalPresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystem
public import StacksFrontier.AlgebraicGeometry.SectionRingGeometric.GlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigToSmallEtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleModulePullbackComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleModuleQuasicoherent
public import StacksFrontier.CategoryTheory.Adjunction.LeftAdjointUniqTranspose
public import StacksFrontier.CategoryTheory.Functor.ConjugateHom
public meta import StacksFrontier.Tactic.HEqCongr

/-!
# The restrictions `i_f^*π_X^*𝓕` along a composite (towards Stacks 0DGN (2))

Let `E` be a big étale site of algebraic spaces, `f : Y ⟶ X`, `h : Z ⟶ Y`, `π_X` the comparison
morphism and `i_f : Y_{spaces,étale} ⥤ (Spaces/X)_étale` the inclusion of Stacks 0DF2. For a
quasi-coherent `𝒪_X`-module `𝓕`, `ψ_f : f_{small}^*𝓕 ≅ i_f^*π_X^*𝓕`
(`AlgebraicGeometry.BigEtaleSpaceSite.pullbackTopos_iso_restriction_pullbackTopos`). This file
shows that `ψ` is compatible with composition, through the transition
`D_{h,f} : h_{small}^*(i_f^*𝓖) ⟶ i_{h ≫ f}^*𝓖` along the projections `V ×_Y Z ⟶ V`, and that on
global sections `D_{h,f}` is the restriction of `𝓖` along `h`. These are the two compatibilities
behind Stacks 0DGN (2), `𝓕ᵃ = π_X^*𝓕`; the file also builds the three identifications of Hom
groups out of which the comparison of presheaves is assembled.

## Main results

* `AlgebraicGeometry.BigEtaleSpaceSite.inclusionPullbackTransition`: the transition `D_{h,f}`.
* `AlgebraicGeometry.BigEtaleSpaceSite.pullbackCompIso_hom_app_comp_pullbackTopos_iso_restriction`:
  `ψ_{h ≫ f}` after the composition comparison is `h_{small}^*ψ_f` followed by `D_{h,f}`.
* `AlgebraicGeometry.BigEtaleSpaceSite.inclusionPullbackTransition_sections`: on sections over the
  final object, transporting a section through `D_{h,f}` is restricting it along `h`.
* `AlgebraicGeometry.BigEtaleSpaceSite.associatedSectionsAddEquiv` and
  `AlgebraicGeometry.BigEtaleSpaceSite.associatedSectionsAddEquiv_naturality`: the components
  `Hom(f^*𝒪_X, f^*𝓕) ≃ Γ(Y, i_f^*π_X^*(ι𝓕))` of Stacks 0DGN (2) and their naturality.

## References

* [Stacks Project, Tag 0DGN](https://stacks.math.columbia.edu/tag/0DGN)
* [Stacks Project, Tag 0DG7](https://stacks.math.columbia.edu/tag/0DG7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace CategoryTheory.Adjunction

/-- Generic: a morphism out of the composite left adjoint is determined by transposes. -/
theorem leftAdjointCompIso_hom_app_comp_eq {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁]
    [Category* C₂] {L₁ : C₀ ⥤ C₁} {R₁ : C₁ ⥤ C₀} (adj₁ : L₁ ⊣ R₁) {L₂ : C₁ ⥤ C₂}
    {R₂ : C₂ ⥤ C₁} (adj₂ : L₂ ⊣ R₂) {L : C₀ ⥤ C₂} {R : C₂ ⥤ C₀} (adj : L ⊣ R)
    (e : R₂ ⋙ R₁ ≅ R) (c : L₁ ⋙ L₂ ≅ L) (hc : c = leftAdjointCompIso adj₁ adj₂ adj e)
    {X : C₀} {Y₁ : C₁} {Y₂ : C₂} (ψ₁ : L₁.obj X ⟶ Y₁) (D : L₂.obj Y₁ ⟶ Y₂) (ψ : L.obj X ⟶ Y₂)
    (h : adj₁.homEquiv _ _ ψ₁ ≫ R₁.map (adj₂.homEquiv _ _ D) ≫ e.hom.app Y₂ =
      adj.homEquiv _ _ ψ) :
    c.hom.app X ≫ ψ = L₂.map ψ₁ ≫ D := by
  subst hc
  have key := Stacks.EtaleCohomology.leftAdjointCompIso_inv_homEquiv_symm adj₁ adj₂ adj e
    (adj₁.homEquiv _ _ ψ₁) (adj₂.homEquiv _ _ D)
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, h, Equiv.symm_apply_apply] at key
  rw [← key, Iso.hom_inv_id_app_assoc]

end CategoryTheory.Adjunction


namespace CategoryTheory.Functor.FullyFaithful

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D] {L : C ⥤ D}
  [L.Additive]

/-- Conjugation through a fully faithful additive functor. -/
def conjAddEquiv (hL : L.FullyFaithful) {A B : C} {A' B' : D} (a : A' ≅ L.obj A)
    (b : B' ≅ L.obj B) : (A ⟶ B) ≃+ (A' ⟶ B') where
  toFun α := a.hom ≫ L.map α ≫ b.inv
  invFun β := hL.preimage (a.inv ≫ β ≫ b.hom)
  left_inv α := by simp
  right_inv β := by simp
  map_add' α β := by simp [Preadditive.add_comp, Preadditive.comp_add]

end CategoryTheory.Functor.FullyFaithful

namespace CategoryTheory

/-- Generic AB chase, in the association of the component equivalences. -/
theorem conj_square_AB
    {𝒜X 𝒜Y 𝒜Z 𝒞Y 𝒞Z : Type*} [Category* 𝒜X] [Category* 𝒜Y] [Category* 𝒜Z] [Category* 𝒞Y]
    [Category* 𝒞Z]
    {P₁ : 𝒜X ⥤ 𝒜Y} {P₂ : 𝒜X ⥤ 𝒜Z} {H : 𝒜Y ⥤ 𝒜Z} (e : P₂ ≅ P₁ ⋙ H)
    (ιY : 𝒜Y ⥤ 𝒞Y) (ιZ : 𝒜Z ⥤ 𝒞Z) (Hs : 𝒞Y ⥤ 𝒞Z) (M₀ M₁ : 𝒜X)
    {c₀ c₁ : 𝒞Y} {d₀ d₁ : 𝒞Z} {p₀ p₁ : 𝒞Y} {q₀ q₁ : 𝒞Z}
    (θY₀ : c₀ ≅ ιY.obj (P₁.obj M₀)) (θY₁ : c₁ ≅ ιY.obj (P₁.obj M₁))
    (θZ₀ : d₀ ≅ ιZ.obj (P₂.obj M₀)) (θZ₁ : d₁ ≅ ιZ.obj (P₂.obj M₁))
    (θh₀ : Hs.obj (ιY.obj (P₁.obj M₀)) ⟶ ιZ.obj (H.obj (P₁.obj M₀)))
    (θh₁ : Hs.obj (ιY.obj (P₁.obj M₁)) ⟶ ιZ.obj (H.obj (P₁.obj M₁))) [IsIso θh₁]
    (κ₀ : Hs.obj c₀ ⟶ d₀) (κ₁ : Hs.obj c₁ ⟶ d₁) [IsIso κ₀] [IsIso κ₁]
    (ψY₀ : c₀ ≅ p₀) (ψY₁ : c₁ ≅ p₁) (ψZ₀ : d₀ ≅ q₀) (ψZ₁ : d₁ ≅ q₁)
    (D₀ : Hs.obj p₀ ⟶ q₀) (D₁ : Hs.obj p₁ ⟶ q₁) [IsIso D₀]
    (hθ₀ : κ₀ ≫ θZ₀.hom = Hs.map θY₀.hom ≫ θh₀ ≫ ιZ.map (e.inv.app M₀))
    (hθ₁ : κ₁ ≫ θZ₁.hom = Hs.map θY₁.hom ≫ θh₁ ≫ ιZ.map (e.inv.app M₁))
    (hψ₀ : κ₀ ≫ ψZ₀.hom = Hs.map ψY₀.hom ≫ D₀)
    (hψ₁ : κ₁ ≫ ψZ₁.hom = Hs.map ψY₁.hom ≫ D₁)
    (α : P₁.obj M₀ ⟶ P₁.obj M₁)
    (hn : Hs.map (ιY.map α) ≫ θh₁ = θh₀ ≫ ιZ.map (H.map α)) :
    (ψZ₀.inv ≫ θZ₀.hom ≫ ιZ.map (e.hom.app M₀ ≫ H.map α ≫ e.inv.app M₁) ≫ θZ₁.inv) ≫
        ψZ₁.hom =
      inv D₀ ≫ Hs.map ((ψY₀.inv ≫ θY₀.hom ≫ ιY.map α ≫ θY₁.inv) ≫ ψY₁.hom) ≫ D₁ := by
  simp only [Category.assoc]
  have h0 : θZ₀.hom = inv κ₀ ≫ Hs.map θY₀.hom ≫ θh₀ ≫ ιZ.map (e.inv.app M₀) :=
    (IsIso.eq_inv_comp _).2 hθ₀
  have h1 : θZ₁.inv = ιZ.map (e.hom.app M₁) ≫ inv θh₁ ≫ Hs.map θY₁.inv ≫ κ₁ := by
    rw [← cancel_epi θZ₁.hom, Iso.hom_inv_id, (IsIso.eq_inv_comp _).2 hθ₁]
    simp only [Category.assoc, ← ιZ.map_comp_assoc, Iso.inv_hom_id_app, ιZ.map_id,
      Category.id_comp, IsIso.hom_inv_id_assoc, ← Hs.map_comp_assoc, θY₁.hom_inv_id, Hs.map_id,
      IsIso.inv_hom_id, Functor.comp_obj]
  have h2 : ψZ₀.inv = inv D₀ ≫ Hs.map ψY₀.inv ≫ κ₀ := by
    rw [← cancel_mono ψZ₀.hom, Iso.inv_hom_id]
    simp only [Category.assoc, hψ₀, ← Hs.map_comp_assoc, ψY₀.inv_hom_id, Hs.map_id,
      Category.id_comp, IsIso.inv_hom_id]
  have h3 : ψZ₁.hom = inv κ₁ ≫ Hs.map ψY₁.hom ≫ D₁ := (IsIso.eq_inv_comp _).2 hψ₁
  have k : ∀ M, ιZ.map (e.inv.app M) ≫ ιZ.map (e.hom.app M) = 𝟙 _ := fun M ↦ by
    rw [← ιZ.map_comp, Iso.inv_hom_id_app, ιZ.map_id]
  rw [h0, h1, h2, h3]
  simp only [Functor.map_comp, Category.assoc, IsIso.hom_inv_id_assoc, reassoc_of% (k M₀),
    reassoc_of% (k M₁)]
  rw [← reassoc_of% hn, IsIso.hom_inv_id_assoc]

/-- `conjAddEquiv a b α = a.hom ≫ L.map α ≫ b.inv`. -/
theorem Functor.FullyFaithful.conjAddEquiv_apply {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] {L : C ⥤ D} [L.Additive] (hL : L.FullyFaithful) {A B : C}
    {A' B' : D} (a : A' ≅ L.obj A) (b : B' ≅ L.obj B) (α : A ⟶ B) :
    hL.conjAddEquiv a b α = a.hom ≫ L.map α ≫ b.inv := rfl

/-- `homCongr` as an additive equivalence is conjugation. -/
theorem Linear.homCongr_toAddEquiv_apply (k : Type*) {C : Type*} [Category* C] [Semiring k]
    [Preadditive C] [Linear k C] {X Y W Z : C} (f₁ : X ≅ Y) (f₂ : W ≅ Z) (f : X ⟶ W) :
    (Linear.homCongr k f₁ f₂).toAddEquiv f = (f₁.inv ≫ f) ≫ f₂.hom := rfl

/-- Generic: moving a natural transition past a pulled-back morphism. -/
theorem comp_inv_comp_map_comp_eq {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (Hs : 𝒞 ⥤ 𝒟)
    {a c p : 𝒞} {b d q : 𝒟} (D₀' : Hs.obj a ⟶ b) [IsIso D₀'] (D₀ : Hs.obj c ⟶ d) [IsIso D₀]
    (u : b ⟶ d) (v : a ⟶ c) (hnat : D₀' ≫ u = Hs.map v ≫ D₀) (γ : c ⟶ p) (D₁ : Hs.obj p ⟶ q) :
    u ≫ inv D₀ ≫ Hs.map γ ≫ D₁ = inv D₀' ≫ Hs.map (v ≫ γ) ≫ D₁ := by
  have h : u ≫ inv D₀ = inv D₀' ≫ Hs.map v := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, hnat, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  rw [reassoc_of% h, Functor.map_comp, Category.assoc]

/-- Generic: evaluating composites out of two spellings of the same object. -/
theorem SheafOfModules.comp_val_app_eq_of_heq {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} {A A' B N : SheafOfModules.{w} R} (hA : A = A') (a : A ⟶ B)
    (a' : A' ⟶ B) (ha : HEq a a') (γ : B ⟶ N) (X : Cᵒᵖ) (x : A.val.obj X) (x' : A'.val.obj X)
    (hx : HEq x x') : (a ≫ γ).val.app X x = (a' ≫ γ).val.app X x' := by
  subst hA
  cases ha
  cases hx
  rfl

/-- Equal morphisms have equal components on sections. -/
theorem SheafOfModules.val_app_congr {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} {A B : SheafOfModules.{w} R} {f g : A ⟶ B} (h : f = g) (X : Cᵒᵖ)
    (x : A.val.obj X) : f.val.app X x = g.val.app X x := by
  rw [h]

/-- Restrictions of a presheaf of abelian groups along two factorizations of one morphism agree. -/
theorem Functor.map_op_map_op_apply_eq {C : Type*} [Category* C] (G : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    {U V W W' : C} (a : U ⟶ V) (b : V ⟶ W) (m : U ⟶ W') (c : W' ⟶ W) (h : a ≫ b = m ≫ c)
    (y : G.obj (Opposite.op W)) : G.map a.op (G.map b.op y) = G.map m.op (G.map c.op y) := by
  have k : G.map b.op ≫ G.map a.op = G.map c.op ≫ G.map m.op := by
    rw [← G.map_comp, ← G.map_comp, ← op_comp, ← op_comp, h]
  exact ConcreteCategory.congr_hom k y

/-- A naturality square of additive equivalences, checked on elements. -/
theorem AddCommGrpCat.comp_toAddCommGrpIso_hom {A B C D : AddCommGrpCat.{w}} (f : A ⟶ C)
    (g : B ⟶ D) (eA : A ≃+ B) (eC : C ≃+ D) (h : ∀ a, eC (f a) = g (eA a)) :
    f ≫ eC.toAddCommGrpIso.hom = eA.toAddCommGrpIso.hom ≫ g :=
  AddCommGrpCat.ext h

end CategoryTheory





namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- `ι` is additive. -/
instance additive_toSpacesEtaleModules (X : AlgebraicSpaces B S hS) :
    (toSpacesEtaleModules B S hS X).Additive := by
  haveI : (Stacks.SheafOfModules.CoherentLift.liftModuleFunctor.{u + 1, u, u}
      (smallEtaleRingedSite B S hS X.1 X.2)).Additive := ⟨rfl⟩
  haveI : (comparisonModuleEquivalence B S hS X).functor.Additive := ⟨rfl⟩
  exact inferInstanceAs ((Stacks.SheafOfModules.CoherentLift.liftModuleFunctor.{u + 1, u, u}
      (smallEtaleRingedSite B S hS X.1 X.2) ⋙
          (comparisonModuleEquivalence B S hS X).inverse).Additive)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (E : BigEtaleSpaceSite S)

section
variable {X Y : E.Spaces} (g : Y ⟶ X)

/-- Transpose of `ψ_g`. -/
theorem homEquiv_pullbackTopos_iso_restriction_pullbackTopos_hom
    (F : SheafOfModules.{u + 1} (spacesEtaleRingSheaf E X)) [F.IsQuasicoherentOnSite] :
    (smallEtaleRingedSiteHom E g).pullbackPushforwardAdjunctionTopos.homEquiv F
        ((SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E g)).obj
        ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj F))
        (pullbackTopos_iso_restriction_pullbackTopos E g F).hom =
      @CategoryStruct.comp (SheafOfModules.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (Space.spacesEtaleRingedTopos E.fppfSite S E.fppf_mem X).O)) _ F
          ((SheafOfModules.pushforward.{u + 1} (restrictSharp E X)).obj
          ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj F))
          ((smallEtaleRingedSiteHom E g).pushforwardTopos.obj ((SheafOfModules.pushforward.{u + 1}
          (inclusionFunctorSharp E g)).obj
          ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj F)))
        ((spacesEtaleRestrictionRingedSiteHom E
            X).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos.unit.app F)
        (@CategoryStruct.comp (SheafOfModules.{u + 1}
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (Space.spacesEtaleRingedTopos E.fppfSite S E.fppf_mem X).O)) _
            ((SheafOfModules.pushforward.{u + 1} (restrictSharp E X)).obj
            ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj F)) _
            ((smallEtaleRingedSiteHom E g).pushforwardTopos.obj
            ((SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E g)).obj
            ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj F)))
        (((Space.spacesEtaleRingedSiteHom E.fppfSite S E.fppf_mem g).siteTransition
          (bigEtaleRingSheaf E X) (inclusionTransition E g) (inclusionFunctorSharp E g)
          (restrictSharp E X) (ringCompatible_inclusionTransition E g)).app
              ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj F))
        ((Space.spacesEtaleRingedSiteHom E.fppfSite S E.fppf_mem g).pushforwardToposIso.hom.app _))
            := by
  dsimp only [pullbackTopos_iso_restriction_pullbackTopos, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Functor.mapIso_hom, asIso_hom]
  refine (Adjunction.homEquiv_leftAdjointUniq_inv_app_comp _ _ F _).trans ?_
  refine (Adjunction.homEquiv_ofNatIsoRight_apply _ _ _).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine eq_whisker ?_ _
  refine (Adjunction.homEquiv_naturality_left _ _ _).trans ?_
  refine whisker_eq _ ?_
  have e := (Space.spacesEtaleRingedSiteHom E.fppfSite S E.fppf_mem g).siteTransitionPullback_app
    (bigEtaleRingSheaf E X) (inclusionTransition E g) (inclusionFunctorSharp E g)
      (restrictSharp E X) (ringCompatible_inclusionTransition E g)
          ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj F)
  exact (Equiv.apply_eq_iff_eq_symm_apply _).mpr e

end

section
variable {X Y Z : E.Spaces} (h : Z ⟶ Y) (f : Y ⟶ X)

/-- The transitions compose. -/
theorem siteTransition_comp_inclusionFunctorTransition
    (M : SheafOfModules.{u + 1} (bigEtaleRingSheaf E X)) :
    @CategoryStruct.comp (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (Space.spacesEtaleRingedTopos E.fppfSite S E.fppf_mem X).O)) _
        ((SheafOfModules.pushforward.{u + 1} (restrictSharp E X)).obj M)
        ((smallEtaleRingedSiteHom E f).pushforwardTopos.obj ((SheafOfModules.pushforward.{u + 1}
        (inclusionFunctorSharp E f)).obj M)) ((smallEtaleRingedSiteHom E
        (h ≫ f)).pushforwardTopos.obj ((SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E
        (h ≫ f))).obj M))
      (@CategoryStruct.comp (SheafOfModules.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (Space.spacesEtaleRingedTopos E.fppfSite S E.fppf_mem X).O)) _
          ((SheafOfModules.pushforward.{u + 1} (restrictSharp E X)).obj M) _
          ((smallEtaleRingedSiteHom E f).pushforwardTopos.obj ((SheafOfModules.pushforward.{u + 1}
          (inclusionFunctorSharp E f)).obj M))
        (((Space.spacesEtaleRingedSiteHom E.fppfSite S E.fppf_mem f).siteTransition
          (bigEtaleRingSheaf E X) (inclusionTransition E f) (inclusionFunctorSharp E f)
          (restrictSharp E X) (ringCompatible_inclusionTransition E f)).app M)
        ((Space.spacesEtaleRingedSiteHom E.fppfSite S E.fppf_mem f).pushforwardToposIso.hom.app _))
      (@CategoryStruct.comp (SheafOfModules.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (Space.spacesEtaleRingedTopos E.fppfSite S E.fppf_mem X).O)) _
          ((smallEtaleRingedSiteHom E f).pushforwardTopos.obj ((SheafOfModules.pushforward.{u + 1}
          (inclusionFunctorSharp E f)).obj M)) ((smallEtaleRingedSiteHom E f).pushforwardTopos.obj
          ((smallEtaleRingedSiteHom E h).pushforwardTopos.obj ((SheafOfModules.pushforward.{u + 1}
          (inclusionFunctorSharp E (h ≫ f))).obj M)))
          ((smallEtaleRingedSiteHom E (h ≫ f)).pushforwardTopos.obj
              ((SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E (h ≫ f))).obj M))
        ((smallEtaleRingedSiteHom E f).pushforwardTopos.map (@CategoryStruct.comp
            (SheafOfModules.{u + 1}
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (Space.spacesEtaleRingedTopos E.fppfSite S E.fppf_mem Y).O)) _
            ((SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E f)).obj M) _
            ((smallEtaleRingedSiteHom E h).pushforwardTopos.obj
            ((SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E (h ≫ f))).obj M))
        (((Space.spacesEtaleRingedSiteHom E.fppfSite S E.fppf_mem h).siteTransition
          (bigEtaleRingSheaf E X) (inclusionFunctorTransition E h f)
          (inclusionFunctorSharp E (h ≫ f)) (inclusionFunctorSharp E f)
          (ringCompatible_inclusionFunctorTransition E h f)).app M)
        ((Space.spacesEtaleRingedSiteHom E.fppfSite S E.fppf_mem h).pushforwardToposIso.hom.app _)))
        ((smallEtaleRingedSiteHomPushforwardCompIso E h f).hom.app
            ((SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E (h ≫ f))).obj M))) =
    (@CategoryStruct.comp (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (Space.spacesEtaleRingedTopos E.fppfSite S E.fppf_mem X).O)) _
        ((SheafOfModules.pushforward.{u + 1} (restrictSharp E X)).obj M) _
        ((smallEtaleRingedSiteHom E (h ≫ f)).pushforwardTopos.obj
        ((SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E (h ≫ f))).obj M))
        (((Space.spacesEtaleRingedSiteHom E.fppfSite S E.fppf_mem (h ≫ f)).siteTransition
          (bigEtaleRingSheaf E X) (inclusionTransition E (h ≫ f)) (inclusionFunctorSharp E (h ≫ f))
          (restrictSharp E X) (ringCompatible_inclusionTransition E (h ≫ f))).app M)
        ((Space.spacesEtaleRingedSiteHom E.fppfSite S E.fppf_mem
            (h ≫ f)).pushforwardToposIso.hom.app _)) := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun W ↦ ModuleCat.hom_ext
    (LinearMap.ext fun x ↦ ?_))
  have e := Space.spacesBaseChange_comp_projection E.fppfSite S E.fppf_mem h f W.unop
  have e2 : ((Space.spacesBaseChange_comp E.fppfSite S E.fppf_mem h f).inv.app W.unop).hom.left ≫
      ((Space.spacesBaseChange_comp E.fppfSite S E.fppf_mem h f).hom.app W.unop).hom.left = 𝟙 _ :=
          by
    rw [← Over.comp_left, ← ObjectProperty.FullSubcategory.comp_hom, Iso.inv_hom_id_app]
    rfl
  have key : (inclusionFunctor E (h ≫ f)).map
        ((Space.spacesBaseChange_comp E.fppfSite S E.fppf_mem h f).inv.app W.unop) ≫
      (inclusionFunctorTransition E h f).app
        ((Space.spacesBaseChange E.fppfSite S E.fppf_mem f).functor.obj W.unop) ≫
      (inclusionTransition E f).app W.unop = (inclusionTransition E (h ≫ f)).app W.unop := by
    apply Over.OverMorphism.ext
    show ((Space.spacesBaseChange_comp E.fppfSite S E.fppf_mem h f).inv.app W.unop).hom.left ≫
      (Space.spacesBaseChange E.fppfSite S E.fppf_mem h).projection.app
          ((Space.spacesBaseChange E.fppfSite S E.fppf_mem f).functor.obj W.unop) ≫
        (Space.spacesBaseChange E.fppfSite S E.fppf_mem f).projection.app W.unop =
      (Space.spacesBaseChange E.fppfSite S E.fppf_mem (h ≫ f)).projection.app W.unop
    rw [← e, ← Category.assoc, e2, Category.id_comp]
  show (M.val.presheaf.map ((inclusionTransition E f).app W.unop).op ≫
      M.val.presheaf.map ((inclusionFunctorTransition E h f).app
        ((Space.spacesBaseChange E.fppfSite S E.fppf_mem f).functor.obj W.unop)).op ≫
      M.val.presheaf.map ((inclusionFunctor E (h ≫ f)).map
        ((Space.spacesBaseChange_comp E.fppfSite S E.fppf_mem h f).inv.app W.unop)).op) x =
    M.val.presheaf.map ((inclusionTransition E (h ≫ f)).app W.unop).op x
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, Category.assoc, key]

/-- The transition `D_{h,f} : h_{small}^*(i_f^*M) ⟶ i_{h ≫ f}^*M` for a module `M` on the big
étale site of `X`. -/
def inclusionPullbackTransition (M : SheafOfModules.{u + 1} (bigEtaleRingSheaf E X)) :
    (smallEtaleRingedSiteHom E h).pullbackTopos.obj ((SheafOfModules.pushforward.{u + 1}
        (inclusionFunctorSharp E f)).obj M) ⟶ ((SheafOfModules.pushforward.{u + 1}
        (inclusionFunctorSharp E (h ≫ f))).obj M) :=
  (Adjunction.leftAdjointUniq
    ((RingedToposHom.pullbackAdjPushforwardModules.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
      (Space.spacesEtaleRingedSiteHom E.fppfSite S E.fppf_mem h).ringedToposHom).ofNatIsoRight
      (Space.spacesEtaleRingedSiteHom E.fppfSite S E.fppf_mem h).pushforwardToposIso)
    (smallEtaleRingedSiteHom E h).pullbackPushforwardAdjunctionTopos).inv.app _ ≫
  ((Space.spacesEtaleRingedSiteHom E.fppfSite S E.fppf_mem h).siteTransitionPullback
      (bigEtaleRingSheaf E X) (inclusionFunctorTransition E h f) (inclusionFunctorSharp E (h ≫ f))
      (inclusionFunctorSharp E f) (ringCompatible_inclusionFunctorTransition E h f)).app M

/-- The transpose of `inclusionPullbackTransition E h f M` under the pullback–pushforward
adjunction of `h` is the site transition along the projections, followed by the comparison of
pushforward functors. -/
theorem homEquiv_inclusionPullbackTransition_app
    (M : SheafOfModules.{u + 1} (bigEtaleRingSheaf E X)) :
    (smallEtaleRingedSiteHom E h).pullbackPushforwardAdjunctionTopos.homEquiv
        ((SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E f)).obj M)
        ((SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E (h ≫ f))).obj M)
        (inclusionPullbackTransition E h f M) =
      (@CategoryStruct.comp (SheafOfModules.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (Space.spacesEtaleRingedTopos E.fppfSite S E.fppf_mem Y).O)) _
          ((SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E f)).obj M) _
          ((smallEtaleRingedSiteHom E h).pushforwardTopos.obj ((SheafOfModules.pushforward.{u + 1}
          (inclusionFunctorSharp E (h ≫ f))).obj M))
        (((Space.spacesEtaleRingedSiteHom E.fppfSite S E.fppf_mem h).siteTransition
          (bigEtaleRingSheaf E X) (inclusionFunctorTransition E h f)
          (inclusionFunctorSharp E (h ≫ f)) (inclusionFunctorSharp E f)
          (ringCompatible_inclusionFunctorTransition E h f)).app M)
        ((Space.spacesEtaleRingedSiteHom E.fppfSite S E.fppf_mem h).pushforwardToposIso.hom.app _))
            := by
  refine (Adjunction.homEquiv_leftAdjointUniq_inv_app_comp _ _ _ _).trans ?_
  refine (Adjunction.homEquiv_ofNatIsoRight_apply _ _ _).trans ?_
  refine eq_whisker ?_ _
  have e := (Space.spacesEtaleRingedSiteHom E.fppfSite S E.fppf_mem h).siteTransitionPullback_app
      (bigEtaleRingSheaf E X) (inclusionFunctorTransition E h f) (inclusionFunctorSharp E (h ≫ f))
      (inclusionFunctorSharp E f) (ringCompatible_inclusionFunctorTransition E h f) M
  exact (Equiv.apply_eq_iff_eq_symm_apply _).mpr e

/-- `ψ_{h ≫ f}` after the composition comparison of pullbacks is `h_{small}^*ψ_f` followed by
`D_{h,f}`. -/
theorem pullbackCompIso_hom_app_comp_pullbackTopos_iso_restriction
    (F : SheafOfModules.{u + 1} (spacesEtaleRingSheaf E X)) [F.IsQuasicoherentOnSite] :
    (smallEtaleRingedSiteHomPullbackCompIso E h f).hom.app F ≫
        (pullbackTopos_iso_restriction_pullbackTopos E (h ≫ f) F).hom =
      (smallEtaleRingedSiteHom E h).pullbackTopos.map
          (pullbackTopos_iso_restriction_pullbackTopos E f F).hom ≫
        inclusionPullbackTransition E h f
            ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj F) :=
            by
  have h1 := homEquiv_pullbackTopos_iso_restriction_pullbackTopos_hom E f F
  have h2 := homEquiv_inclusionPullbackTransition_app E h f
      ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj F)
  have h3 := homEquiv_pullbackTopos_iso_restriction_pullbackTopos_hom E (h ≫ f) F
  have h4 := siteTransition_comp_inclusionFunctorTransition E h f
      ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj F)
  refine Adjunction.leftAdjointCompIso_hom_app_comp_eq
    (smallEtaleRingedSiteHom E f).pullbackPushforwardAdjunctionTopos
    (smallEtaleRingedSiteHom E h).pullbackPushforwardAdjunctionTopos
    (smallEtaleRingedSiteHom E (h ≫ f)).pullbackPushforwardAdjunctionTopos
    (smallEtaleRingedSiteHomPushforwardCompIso E h f) _ rfl _ _ _ ?_
  rw [h3, h1]
  refine (whisker_eq _ (eq_whisker
    ((smallEtaleRingedSiteHom E f).pushforwardTopos.congr_map h2) _)).trans ?_
  refine (Category.assoc _ _ _).trans (whisker_eq _ ?_)
  with_reducible exact h4

/-- The transition `inclusionPullbackTransition E h f M` is natural in the module `M`. -/
theorem inclusionPullbackTransition_naturality {M M' : SheafOfModules.{u + 1}
    (bigEtaleRingSheaf E X)}
    (φ : M ⟶ M') :
    inclusionPullbackTransition E h f M ≫ ((SheafOfModules.pushforward.{u + 1}
        (inclusionFunctorSharp E (h ≫ f))).map φ) =
      (smallEtaleRingedSiteHom E h).pullbackTopos.map ((SheafOfModules.pushforward.{u + 1}
          (inclusionFunctorSharp E f)).map φ) ≫
        inclusionPullbackTransition E h f M' := by
  have n1 := ((Space.spacesEtaleRingedSiteHom E.fppfSite S E.fppf_mem h).siteTransitionPullback
      (bigEtaleRingSheaf E X) (inclusionFunctorTransition E h f) (inclusionFunctorSharp E (h ≫ f))
      (inclusionFunctorSharp E f) (ringCompatible_inclusionFunctorTransition E h f)).naturality φ
  have n2 := (Adjunction.leftAdjointUniq
    ((RingedToposHom.pullbackAdjPushforwardModules.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
      (Space.spacesEtaleRingedSiteHom E.fppfSite S E.fppf_mem h).ringedToposHom).ofNatIsoRight
      (Space.spacesEtaleRingedSiteHom E.fppfSite S E.fppf_mem h).pushforwardToposIso)
    (smallEtaleRingedSiteHom E h).pullbackPushforwardAdjunctionTopos).inv.naturality
        ((SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E f)).map φ)
  rw [Functor.comp_map] at n1
  unfold inclusionPullbackTransition
  rw [Category.assoc, ← n1, ← Category.assoc, ← n2, Category.assoc]

/-- The transition `inclusionPullbackTransition E h f` is an isomorphism at the structure sheaf. -/
instance isIso_inclusionPullbackTransition_unit :
    IsIso (inclusionPullbackTransition E h f (SheafOfModules.unit (bigEtaleRingSheaf E X))) := by
  haveI := isIso_inclusionFunctorTransitionPullback_app_unit E h f
  unfold inclusionPullbackTransition
  infer_instance

/-- The section `1` of `i_g^*𝒪_X` over `W`. -/
private abbrev pushforwardUnitOne {X Y : E.Spaces} (g : Y ⟶ X)
    (W : Space.SpacesEtale E.fppfSite S E.fppf_mem Y) :
    ((SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E g)).obj
      (SheafOfModules.unit (bigEtaleRingSheaf E X))).val.obj (Opposite.op W) :=
  (1 : (bigEtaleRingSheaf E X).obj.obj (Opposite.op ((inclusionFunctor E g).obj W)))

/-- On sections over the final object, transporting a section through `D_{h,f}` is restricting it
along `h`. -/
theorem inclusionPullbackTransition_sections (N : SheafOfModules.{u + 1} (bigEtaleRingSheaf E X))
    (δ : ((SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E f)).obj (SheafOfModules.unit
        (bigEtaleRingSheaf E X))) ⟶ ((SheafOfModules.pushforward.{u + 1}
        (inclusionFunctorSharp E f)).obj N)) (σ :
        (Space.SpacesEtale.final E.fppfSite S E.fppf_mem Z) ⟶
        (Space.spacesBaseChange E.fppfSite S E.fppf_mem h).functor.obj
        (Space.SpacesEtale.final E.fppfSite S E.fppf_mem Y)) :
    (@CategoryStruct.comp (SheafOfModules.{u + 1} (spacesEtaleRingSheaf E Z)) _ _ _ _
      (inv (inclusionPullbackTransition E h f (SheafOfModules.unit (bigEtaleRingSheaf E X))))
      ((smallEtaleRingedSiteHom E h).pullbackTopos.map δ ≫
        inclusionPullbackTransition E h f N)).val.app (Opposite.op
            (Space.SpacesEtale.final E.fppfSite S E.fppf_mem Z))
      (show ((SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E (h ≫ f))).obj
          (SheafOfModules.unit (bigEtaleRingSheaf E X))).val.obj (Opposite.op
          (Space.SpacesEtale.final E.fppfSite S E.fppf_mem Z)) from
        (1 : (bigEtaleRingSheaf E X).obj.obj (Opposite.op ((inclusionFunctor E (h ≫ f)).obj
            (Space.SpacesEtale.final E.fppfSite S E.fppf_mem Z))))) =
    N.val.presheaf.map (((inclusionFunctor E (h ≫ f)).map σ ≫
        (inclusionFunctorTransition E h f).app
            (Space.SpacesEtale.final E.fppfSite S E.fppf_mem Y)).op)
      (δ.val.app (Opposite.op (Space.SpacesEtale.final E.fppfSite S E.fppf_mem Y))
        (show ((SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E f)).obj
            (SheafOfModules.unit (bigEtaleRingSheaf E X))).val.obj (Opposite.op
            (Space.SpacesEtale.final E.fppfSite S E.fppf_mem Y)) from
          (1 : (bigEtaleRingSheaf E X).obj.obj (Opposite.op ((inclusionFunctor E f).obj
              (Space.SpacesEtale.final E.fppfSite S E.fppf_mem Y)))))) := by
  generalize hs : @CategoryStruct.comp (SheafOfModules.{u + 1} (spacesEtaleRingSheaf E Z)) _ _ _ _
      (inv (inclusionPullbackTransition E h f (SheafOfModules.unit (bigEtaleRingSheaf E X))))
      ((smallEtaleRingedSiteHom E h).pullbackTopos.map δ ≫
        inclusionPullbackTransition E h f N) = s
  have hs' : inclusionPullbackTransition E h f (SheafOfModules.unit (bigEtaleRingSheaf E X)) ≫ s =
      (smallEtaleRingedSiteHom E h).pullbackTopos.map δ ≫ inclusionPullbackTransition E h f N := by
    rw [← hs, IsIso.hom_inv_id_assoc]
  have t := congrArg ((smallEtaleRingedSiteHom E h).pullbackPushforwardAdjunctionTopos.homEquiv
    ((SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E f)).obj (SheafOfModules.unit
        (bigEtaleRingSheaf E X))) ((SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E
        (h ≫ f))).obj N)) hs'
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left,
    homEquiv_inclusionPullbackTransition_app, homEquiv_inclusionPullbackTransition_app] at t
  have t2 := congrArg (fun φ ↦ φ.val.app (Opposite.op
      (Space.SpacesEtale.final E.fppfSite S E.fppf_mem Y))
      (pushforwardUnitOne E f (Space.SpacesEtale.final E.fppfSite S E.fppf_mem Y))) t
  change s.val.app (Opposite.op ((Space.spacesBaseChange E.fppfSite S E.fppf_mem h).functor.obj
      (Space.SpacesEtale.final E.fppfSite S E.fppf_mem Y))) ((PresheafOfModules.unit
      (bigEtaleRingSheaf E X).obj).map ((inclusionFunctorTransition E h f).app
      (Space.SpacesEtale.final E.fppfSite S E.fppf_mem Y)).op
      (pushforwardUnitOne E f (Space.SpacesEtale.final E.fppfSite S E.fppf_mem Y))) =
    N.val.map ((inclusionFunctorTransition E h f).app
      (Space.SpacesEtale.final E.fppfSite S E.fppf_mem Y)).op
      (δ.val.app (Opposite.op (Space.SpacesEtale.final E.fppfSite S E.fppf_mem Y))
        (pushforwardUnitOne E f (Space.SpacesEtale.final E.fppfSite S E.fppf_mem Y))) at t2
  rw [PresheafOfModules.unit_map_one] at t2
  have hone : ((SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E (h ≫ f))).obj
      (SheafOfModules.unit (bigEtaleRingSheaf E X))).val.map σ.op
      (pushforwardUnitOne E (h ≫ f) _) = pushforwardUnitOne E (h ≫ f) _ :=
    PresheafOfModules.unit_map_one (R := (bigEtaleRingSheaf E X).obj)
      ((inclusionFunctor E (h ≫ f)).map σ).op
  have n := PresheafOfModules.naturality_apply s.val σ.op (pushforwardUnitOne E (h ≫ f) _)
  rw [hone, t2] at n
  refine n.trans ?_
  change (N.val.presheaf.map ((inclusionFunctorTransition E h f).app
      (Space.SpacesEtale.final E.fppfSite S E.fppf_mem Y)).op ≫
    N.val.presheaf.map ((inclusionFunctor E (h ≫ f)).map σ).op) _ = _
  rw [← Functor.map_comp, ← op_comp]

end

section Components

variable {X : E.Spaces} (F : Space.Modules.{u, u} E.fppfSite S E.fppf_mem X.1 X.2)

/-- `θ_f` as an isomorphism. -/
def toSpacesEtaleModulesPullbackIso {Y : E.Spaces} (f : Y ⟶ X)
    (M : Space.Modules.{u, u} E.fppfSite S E.fppf_mem X.1 X.2) :
    (smallEtaleRingedSiteHom E f).pullbackTopos.obj
        ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj M) ≅
      (Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem Y).obj
        ((Space.modulePullback E.fppfSite S E.fppf_mem f).obj M) :=
  asIso ((toSpacesEtaleModulesPullbackHom E f).app M)

/-- The structure sheaf of `X_{spaces,étale}` is a quasi-coherent module. -/
theorem isQuasicoherentOnSite_unit_modules (X : E.Spaces) :
    (SheafOfModules.unit _ : Space.Modules.{u, u} E.fppfSite S E.fppf_mem X.1
        X.2).IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_of_presentation
    Stacks.SheafOfModules.presentationUnit

variable (X) in
/-- `π_X^*(ι𝒪) ≅ 𝒪`. -/
def pullbackToSpacesEtaleModulesUnitIso :
    ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj
        ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj
        (SheafOfModules.unit _))) ≅ SheafOfModules.unit (bigEtaleRingSheaf E X) :=
  (spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.mapIso
      (Space.toSpacesEtaleModulesUnitIso E.fppfSite S E.fppf_mem X) ≪≫
    (Stacks.Sheaves.LocalizedPullback.pullbackToposUnitIso
        (spacesEtaleRestrictionRingedSiteHom E X)).symm

/-- The final object of `Y_spet` maps to `Y` in `Over X`. -/
def overFinalIso (Y : Over X) :
    Y ≅ (inclusionFunctor E Y.hom).obj (Space.SpacesEtale.final E.fppfSite S E.fppf_mem Y.left) :=
  Over.isoMk (Iso.refl _) (by simp [Space.SpacesEtale.final])

end Components

section Components2

variable {X : E.Spaces} (F : Space.Modules.{u, u} E.fppfSite S E.fppf_mem X.1 X.2)
  [hF : F.IsQuasicoherentOnSite]

/-- The additive equivalence `Hom(f^*𝒪_X, f^*F) ≃+ Hom(f_{small}^*(ι𝒪_X), f_{small}^*(ιF))`
induced by the fully faithful functor `ι` and the isomorphisms `θ_f`. -/
def associatedSectionsEquivSpacesEtale {Y : E.Spaces} (f : Y ⟶ X) :
    ((Space.modulePullback E.fppfSite S E.fppf_mem f).obj
        (SheafOfModules.unit _ : Space.Modules.{u, u} E.fppfSite S E.fppf_mem X.1 X.2) ⟶
        (Space.modulePullback E.fppfSite S E.fppf_mem f).obj F) ≃+
      (((smallEtaleRingedSiteHom E f).pullbackTopos.obj
          ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj (SheafOfModules.unit _))) ⟶
          ((smallEtaleRingedSiteHom E f).pullbackTopos.obj
          ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj F))) :=
  (Space.fullyFaithfulToSpacesEtaleModules E.fppfSite S E.fppf_mem Y).conjAddEquiv
    (toSpacesEtaleModulesPullbackIso E f _) (toSpacesEtaleModulesPullbackIso E f F)

/-- Step B. -/
def spacesEtaleEquivRestriction {Y : E.Spaces} (f : Y ⟶ X) :
    (((smallEtaleRingedSiteHom E f).pullbackTopos.obj
        ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj (SheafOfModules.unit _))) ⟶
        ((smallEtaleRingedSiteHom E f).pullbackTopos.obj
        ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj F))) ≃+
        (((SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E f)).obj
        ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj
        ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj (SheafOfModules.unit _)))) ⟶
        ((SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E f)).obj
        ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj
        ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj F)))) :=
  haveI := isQuasicoherentOnSite_unit_modules E X
  haveI := Space.isQuasicoherentOnSite_toSpacesEtaleModules E.fppfSite S E.fppf_mem X
    (SheafOfModules.unit _)
  haveI := Space.isQuasicoherentOnSite_toSpacesEtaleModules E.fppfSite S E.fppf_mem X F
  (Linear.homCongr ℤ (pullbackTopos_iso_restriction_pullbackTopos E f _)
    (pullbackTopos_iso_restriction_pullbackTopos E f _)).toAddEquiv

/-- The unit of `Y_spet` is `i_f^*π^*(ι𝒪)`. -/
def restrictionUnitIso {Y : E.Spaces} (f : Y ⟶ X) :
    SheafOfModules.unit (spacesEtaleRingSheaf E Y) ≅ ((SheafOfModules.pushforward.{u + 1}
        (inclusionFunctorSharp E f)).obj
        ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj
        ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj (SheafOfModules.unit _)))) :=
  (SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E f)).mapIso
    (pullbackToSpacesEtaleModulesUnitIso E X).symm

/-- Step C: evaluation at the final object of `Y_spet`. -/
def restrictionEquivSections {Y : E.Spaces} (f : Y ⟶ X) :
    (((SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E f)).obj
        ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj
        ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj (SheafOfModules.unit _)))) ⟶
        ((SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E f)).obj
        ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj
        ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj F)))) ≃+
        ((SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E f)).obj
          ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj
          ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj F))).val.obj
          (Opposite.op (Space.SpacesEtale.final E.fppfSite S E.fppf_mem Y)) :=
  (Stacks.SectionRingGeometric.homAddEquivOfIso (restrictionUnitIso E f).symm _).trans
    (Stacks.SectionRingGeometric.unitHomAddEquiv
      (Space.SpacesEtale.final_isTerminal E.fppfSite S E.fppf_mem Y)
          ((SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E f)).obj
          ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj
          ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj F))))

end Components2

/-- `D_{h,f}` is invertible on `π_X^*𝓖` for `𝓖` quasi-coherent. -/
instance isIso_inclusionPullbackTransition_pullback {X Y Z : E.Spaces} (h : Z ⟶ Y) (f : Y ⟶ X)
    (G : SheafOfModules.{u + 1} (spacesEtaleRingSheaf E X)) [G.IsQuasicoherentOnSite] :
    IsIso (inclusionPullbackTransition E h f
      ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj G)) := by
  haveI := isIso_inclusionFunctorTransitionPullback_app_pullback E h f G
  unfold inclusionPullbackTransition
  infer_instance

section AB

attribute [local instance] isQuasicoherentOnSite_unit_modules
  Space.isQuasicoherentOnSite_toSpacesEtaleModules

variable {X : E.Spaces} (F : Space.Modules.{u, u} E.fppfSite S E.fppf_mem X.1 X.2)
  [hF : F.IsQuasicoherentOnSite] {Z : E.Spaces}

/-- The value of `associatedSectionsEquivSpacesEtale` on a morphism. -/
theorem associatedSectionsEquivSpacesEtale_apply {Y : E.Spaces} (f : Y ⟶ X)
    (α : (Space.modulePullback E.fppfSite S E.fppf_mem f).obj
        (SheafOfModules.unit _ : Space.Modules.{u, u} E.fppfSite S E.fppf_mem X.1 X.2) ⟶
        (Space.modulePullback E.fppfSite S E.fppf_mem f).obj F) :
    associatedSectionsEquivSpacesEtale E F f α =
      @CategoryStruct.comp (SheafOfModules.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem Y).O)) _ _ _ _
        (@Iso.hom (SheafOfModules.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem Y).O)) _ _ _
          (toSpacesEtaleModulesPullbackIso E f _))
        (@CategoryStruct.comp (SheafOfModules.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem Y).O)) _ _ _ _
          ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem Y).map α)
          (@Iso.inv (SheafOfModules.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem Y).O)) _ _ _
            (toSpacesEtaleModulesPullbackIso E f F))) :=
  (DFunLike.congr_fun (show associatedSectionsEquivSpacesEtale E F
      f = (Space.fullyFaithfulToSpacesEtaleModules E.fppfSite S E.fppf_mem
        Y).conjAddEquiv (toSpacesEtaleModulesPullbackIso E f _)
        (toSpacesEtaleModulesPullbackIso E f F) from rfl) α).trans
    (Functor.FullyFaithful.conjAddEquiv_apply
      (Space.fullyFaithfulToSpacesEtaleModules E.fppfSite S E.fppf_mem Y)
      (toSpacesEtaleModulesPullbackIso E f _)
      (toSpacesEtaleModulesPullbackIso E f F) α)

/-- Step B, written out. -/
theorem spacesEtaleEquivRestriction_apply {Y : E.Spaces} (f : Y ⟶ X)
    (β : ((smallEtaleRingedSiteHom E f).pullbackTopos.obj
        ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj (SheafOfModules.unit _))) ⟶
        ((smallEtaleRingedSiteHom E f).pullbackTopos.obj
        ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj F))) :
    spacesEtaleEquivRestriction E F f β =
      ((pullbackTopos_iso_restriction_pullbackTopos E f _).inv ≫ β) ≫
        (pullbackTopos_iso_restriction_pullbackTopos E f _).hom :=
  (DFunLike.congr_fun (show spacesEtaleEquivRestriction E F
      f = (Linear.homCongr ℤ
        (pullbackTopos_iso_restriction_pullbackTopos E f _)
        (pullbackTopos_iso_restriction_pullbackTopos E f _)).toAddEquiv from rfl) β).trans
    (Linear.homCongr_toAddEquiv_apply ℤ
        (pullbackTopos_iso_restriction_pullbackTopos E f _)
        (pullbackTopos_iso_restriction_pullbackTopos E f _) β)

/-- Steps A and B carry the restriction of `𝓕ᵃ` along `h` to conjugation by `D_{h,f}`. -/
theorem spacesEtaleEquivRestriction_conjHom {Y : E.Spaces} (f : Y ⟶ X) (h : Z ⟶ Y)
    (α : (Space.modulePullback E.fppfSite S E.fppf_mem f).obj
        (SheafOfModules.unit _ : Space.Modules.{u, u} E.fppfSite S E.fppf_mem X.1 X.2) ⟶
        (Space.modulePullback E.fppfSite S E.fppf_mem f).obj F) :
    spacesEtaleEquivRestriction E F (h ≫ f)
        (associatedSectionsEquivSpacesEtale E F (h ≫ f)
          (Functor.conjHom (Space.modulePullbackCompIso E.fppfSite S E.fppf_mem h f).symm α)) =
      @CategoryStruct.comp (SheafOfModules.{u + 1} (spacesEtaleRingSheaf E Z)) _ _ _ _
        (inv (inclusionPullbackTransition E h f
          ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj
            ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj
              (SheafOfModules.unit _)))))
        ((smallEtaleRingedSiteHom E h).pullbackTopos.map
          (spacesEtaleEquivRestriction E F f (associatedSectionsEquivSpacesEtale E F f α)) ≫
        inclusionPullbackTransition E h f
          ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj
            ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj F))) := by
  have key := conj_square_AB
    (𝒞Y := SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.spacesEtaleRingedTopos E.fppfSite S E.fppf_mem Y).O))
    (𝒞Z := SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.spacesEtaleRingedTopos E.fppfSite S E.fppf_mem Z).O))
    (Space.modulePullbackCompIso E.fppfSite S E.fppf_mem h f).symm
    (Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem Y)
    (Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem Z)
    (smallEtaleRingedSiteHom E h).pullbackTopos
    (SheafOfModules.unit _) F
    (toSpacesEtaleModulesPullbackIso E f _) (toSpacesEtaleModulesPullbackIso E f F)
    (toSpacesEtaleModulesPullbackIso E (h ≫ f) _)
    (toSpacesEtaleModulesPullbackIso E (h ≫ f) F)
    ((toSpacesEtaleModulesPullbackHom E h).app _) ((toSpacesEtaleModulesPullbackHom E h).app _)
    ((smallEtaleRingedSiteHomPullbackCompIso E h f).hom.app _)
    ((smallEtaleRingedSiteHomPullbackCompIso E h f).hom.app _)
    (pullbackTopos_iso_restriction_pullbackTopos E f _)
    (pullbackTopos_iso_restriction_pullbackTopos E f _)
    (pullbackTopos_iso_restriction_pullbackTopos E (h ≫ f) _)
    (pullbackTopos_iso_restriction_pullbackTopos E (h ≫ f) _)
    (inclusionPullbackTransition E h f _) (inclusionPullbackTransition E h f _)
    (toSpacesEtaleModulesPullbackHom_comp_app E h f _)
    (toSpacesEtaleModulesPullbackHom_comp_app E h f F)
    (pullbackCompIso_hom_app_comp_pullbackTopos_iso_restriction E h f _)
    (pullbackCompIso_hom_app_comp_pullbackTopos_iso_restriction E h f _)
    α ((toSpacesEtaleModulesPullbackHom E h).naturality α)
  refine ((congrArg (spacesEtaleEquivRestriction E F (h ≫ f))
    (associatedSectionsEquivSpacesEtale_apply E F (h ≫ f) _)).trans
    (spacesEtaleEquivRestriction_apply E F (h ≫ f) _)).trans ?_
  refine Eq.trans ?_ (whisker_eq _ (eq_whisker
    ((smallEtaleRingedSiteHom E h).pullbackTopos.congr_map
    ((congrArg (spacesEtaleEquivRestriction E F f)
      (associatedSectionsEquivSpacesEtale_apply E F f α)).trans
      (spacesEtaleEquivRestriction_apply E F f _)).symm) _))
  exact eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq key) (by heq_congr)))

/-- Step C, written out. -/
theorem restrictionEquivSections_apply {Y : E.Spaces} (f : Y ⟶ X)
    (γ : ((SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E f)).obj
        ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj
        ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj (SheafOfModules.unit _)))) ⟶
        ((SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E f)).obj
        ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj
        ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj F)))) :
    restrictionEquivSections E F f γ =
        (((restrictionUnitIso E f).hom ≫ γ).val.app
          (Opposite.op (Space.SpacesEtale.final E.fppfSite S E.fppf_mem Y))
          (1 : (spacesEtaleRingSheaf E Y).obj.obj
            (Opposite.op (Space.SpacesEtale.final E.fppfSite S E.fppf_mem Y)))) := rfl

omit hF in
/-- Evaluating at `1` through `𝒪_{Y} = i_f^*𝒪`. -/
theorem restrictionUnitIso_hom_comp_val_app {Y : E.Spaces} (f : Y ⟶ X)
    {N : SheafOfModules.{u + 1} (spacesEtaleRingSheaf E Y)}
    (γ : ((SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E f)).obj
        ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj
        ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj
          (SheafOfModules.unit _)))) ⟶ N) :
    ((restrictionUnitIso E f).hom ≫ γ).val.app
          (Opposite.op (Space.SpacesEtale.final E.fppfSite S E.fppf_mem Y))
          (1 : (spacesEtaleRingSheaf E Y).obj.obj
            (Opposite.op (Space.SpacesEtale.final E.fppfSite S E.fppf_mem Y))) =
    (((SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E f)).map
      (pullbackToSpacesEtaleModulesUnitIso E X).inv) ≫ γ).val.app
        (Opposite.op (Space.SpacesEtale.final E.fppfSite S E.fppf_mem Y))
        (show ((SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E f)).obj
          (SheafOfModules.unit (bigEtaleRingSheaf E X))).val.obj (Opposite.op
          (Space.SpacesEtale.final E.fppfSite S E.fppf_mem Y)) from
        (1 : (bigEtaleRingSheaf E X).obj.obj (Opposite.op ((inclusionFunctor E f).obj
            (Space.SpacesEtale.final E.fppfSite S E.fppf_mem Y))))) :=
  SheafOfModules.comp_val_app_eq_of_heq rfl _ _ (by heq_congr) γ _ _ _ (by heq_congr)

omit hF in
/-- The unit comparison commutes with `D_{h,f}`. -/
theorem restrictionUnit_comp_transition {Y : E.Spaces} (f : Y ⟶ X) (h : Z ⟶ Y)
    (γ : ((SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E f)).obj
        ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj
        ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj (SheafOfModules.unit _)))) ⟶
        ((SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E f)).obj
        ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj
        ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj F)))) :
    (SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E (h ≫ f))).map
      (pullbackToSpacesEtaleModulesUnitIso E X).inv ≫
      (@CategoryStruct.comp (SheafOfModules.{u + 1} (spacesEtaleRingSheaf E Z)) _ _ _ _
        (inv (inclusionPullbackTransition E h f
          ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj
            ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj
              (SheafOfModules.unit _)))))
        ((smallEtaleRingedSiteHom E h).pullbackTopos.map γ ≫
        inclusionPullbackTransition E h f
          ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj
            ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj F)))) =
      @CategoryStruct.comp (SheafOfModules.{u + 1} (spacesEtaleRingSheaf E Z)) _ _ _ _
      (inv (inclusionPullbackTransition E h f (SheafOfModules.unit (bigEtaleRingSheaf E X))))
      ((smallEtaleRingedSiteHom E h).pullbackTopos.map
        ((SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E f)).map
          (pullbackToSpacesEtaleModulesUnitIso E X).inv ≫ γ) ≫
        inclusionPullbackTransition E h f
          ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj
            ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj F))) := by
  have e1 := comp_inv_comp_map_comp_eq (smallEtaleRingedSiteHom E h).pullbackTopos
    (inclusionPullbackTransition E h f (SheafOfModules.unit (bigEtaleRingSheaf E X)))
    (inclusionPullbackTransition E h f
          ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj
            ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj
              (SheafOfModules.unit _))))
    ((SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E (h ≫ f))).map
      (pullbackToSpacesEtaleModulesUnitIso E X).inv)
    ((SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E f)).map
      (pullbackToSpacesEtaleModulesUnitIso E X).inv)
    (inclusionPullbackTransition_naturality E h f (pullbackToSpacesEtaleModulesUnitIso E X).inv)
    γ (inclusionPullbackTransition E h f
          ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj
            ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj F)))
  exact eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq e1) (by heq_congr)))

omit hF in
/-- The section of `Y ×_Y Z ⟶ Z` given by `h`. -/
def finalBaseChangeHom {Y : E.Spaces} (h : Z ⟶ Y) :
    Space.SpacesEtale.final E.fppfSite S E.fppf_mem Z ⟶
      (Space.spacesBaseChange E.fppfSite S E.fppf_mem h).functor.obj
        (Space.SpacesEtale.final E.fppfSite S E.fppf_mem Y) :=
  ObjectProperty.homMk (Over.homMk (pullback.lift h (𝟙 Z) (by simp [Space.SpacesEtale.final]))
    (pullback.lift_snd _ _ _))

omit hF in
/-- The morphism of `Over X` underlying the restriction along `h`. -/
theorem overFinalIso_hom_comp_finalBaseChangeHom (Y : Over X) (h : Z ⟶ Y.left)
    (m : (⟨Z, ⟨PUnit.unit⟩, h ≫ Y.hom⟩ : Over X) ⟶ Y) (hm : m.left = h) :
    (overFinalIso E (⟨Z, ⟨PUnit.unit⟩, h ≫ Y.hom⟩ : Over X)).hom ≫
      ((inclusionFunctor E (h ≫ Y.hom)).map (finalBaseChangeHom E h) ≫
        (inclusionFunctorTransition E h Y.hom).app
          (Space.SpacesEtale.final E.fppfSite S E.fppf_mem Y.left)) =
      m ≫ (overFinalIso E Y).hom := by
  apply Over.OverMorphism.ext
  show 𝟙 Z ≫ (pullback.lift h (𝟙 Z) _ ≫ pullback.fst _ h) = m.left ≫ 𝟙 _
  rw [hm, Category.id_comp, Category.comp_id]
  exact pullback.lift_fst _ _ _


/-- Step C carries conjugation by `D_{h,f}` to restriction along `h`. -/
theorem restrictionEquivSections_transition {Y : E.Spaces} (f : Y ⟶ X) (h : Z ⟶ Y)
    (γ : ((SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E f)).obj
        ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj
        ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj (SheafOfModules.unit _)))) ⟶
        ((SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E f)).obj
        ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj
        ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj F)))) :
    restrictionEquivSections E F (h ≫ f)
        (@CategoryStruct.comp (SheafOfModules.{u + 1} (spacesEtaleRingSheaf E Z)) _ _ _ _
        (inv (inclusionPullbackTransition E h f
          ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj
            ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj
              (SheafOfModules.unit _)))))
        ((smallEtaleRingedSiteHom E h).pullbackTopos.map γ ≫
        inclusionPullbackTransition E h f
          ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj
            ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj F)))) =
      ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj
        ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj F)).val.presheaf.map
        (((inclusionFunctor E (h ≫ f)).map (finalBaseChangeHom E h) ≫
          (inclusionFunctorTransition E h f).app
            (Space.SpacesEtale.final E.fppfSite S E.fppf_mem Y)).op)
        (restrictionEquivSections E F f γ) := by
  have k1 := restrictionUnitIso_hom_comp_val_app E (h ≫ f)
      (@CategoryStruct.comp (SheafOfModules.{u + 1} (spacesEtaleRingSheaf E Z)) _ _ _ _
        (inv (inclusionPullbackTransition E h f
          ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj
            ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj
              (SheafOfModules.unit _)))))
        ((smallEtaleRingedSiteHom E h).pullbackTopos.map γ ≫
        inclusionPullbackTransition E h f
          ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj
            ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj F))))
  have k2 := SheafOfModules.val_app_congr (restrictionUnit_comp_transition E F f h γ)
    (Opposite.op (Space.SpacesEtale.final E.fppfSite S E.fppf_mem Z))
        (show ((SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E (h ≫ f))).obj
          (SheafOfModules.unit (bigEtaleRingSheaf E X))).val.obj (Opposite.op
          (Space.SpacesEtale.final E.fppfSite S E.fppf_mem Z)) from
        (1 : (bigEtaleRingSheaf E X).obj.obj (Opposite.op ((inclusionFunctor E (h ≫ f)).obj
            (Space.SpacesEtale.final E.fppfSite S E.fppf_mem Z)))))
  have k3 := inclusionPullbackTransition_sections E h f
      ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj
        ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj F))
    ((SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E f)).map
          (pullbackToSpacesEtaleModulesUnitIso E X).inv ≫ γ) (finalBaseChangeHom E h)
  have k4 := (restrictionEquivSections_apply E F f γ).trans
    (restrictionUnitIso_hom_comp_val_app E f γ)
  exact ((restrictionEquivSections_apply E F (h ≫ f) _).trans (k1.trans (k2.trans k3))).trans
    (congrArg (((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj
        ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj F)).val.presheaf.map
        (((inclusionFunctor E (h ≫ f)).map (finalBaseChangeHom E h) ≫
          (inclusionFunctorTransition E h f).app
            (Space.SpacesEtale.final E.fppfSite S E.fppf_mem Y)).op)) k4).symm

/-- `Hom(f^*𝒪, f^*𝓕) ≃ Γ(Y_spet, i_f^*π_X^*(ι𝓕))`. -/
def associatedSectionsEquivRestriction {Y : E.Spaces} (f : Y ⟶ X) :
    ((Space.modulePullback E.fppfSite S E.fppf_mem f).obj
        (SheafOfModules.unit _ : Space.Modules.{u, u} E.fppfSite S E.fppf_mem X.1 X.2) ⟶
        (Space.modulePullback E.fppfSite S E.fppf_mem f).obj F) ≃+
      ((SheafOfModules.pushforward.{u + 1} (inclusionFunctorSharp E f)).obj
        ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj
        ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj F))).val.obj
          (Opposite.op (Space.SpacesEtale.final E.fppfSite S E.fppf_mem Y)) :=
  ((associatedSectionsEquivSpacesEtale E F f).trans (spacesEtaleEquivRestriction E F f)).trans
    (restrictionEquivSections E F f)

/-- The composite of steps A, B and C, written out. -/
theorem associatedSectionsEquivRestriction_apply {Y : E.Spaces} (f : Y ⟶ X)
    (α : (Space.modulePullback E.fppfSite S E.fppf_mem f).obj
        (SheafOfModules.unit _ : Space.Modules.{u, u} E.fppfSite S E.fppf_mem X.1 X.2) ⟶
        (Space.modulePullback E.fppfSite S E.fppf_mem f).obj F) :
    associatedSectionsEquivRestriction E F f α = restrictionEquivSections E F f
      (spacesEtaleEquivRestriction E F f (associatedSectionsEquivSpacesEtale E F f α)) := rfl

/-- The component of `𝓕ᵃ ≅ π_X^*(ι𝓕)` at `Y`. -/
def associatedSectionsAddEquiv (Y : Over X) :
    ((Space.modulePullback E.fppfSite S E.fppf_mem Y.hom).obj
        (SheafOfModules.unit _ : Space.Modules.{u, u} E.fppfSite S E.fppf_mem X.1 X.2) ⟶
        (Space.modulePullback E.fppfSite S E.fppf_mem Y.hom).obj F) ≃+
      ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj
        ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj F)).val.presheaf.obj
          (Opposite.op Y) :=
  (associatedSectionsEquivRestriction E F Y.hom).trans
    (((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj
        ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj F)).val.presheaf.mapIso
          (overFinalIso E Y).op).addCommGroupIsoToAddEquiv

/-- The component of `𝓕ᵃ ≅ π_X^*(ι𝓕)`, written out. -/
theorem associatedSectionsAddEquiv_apply (Y : Over X)
    (α : (Space.modulePullback E.fppfSite S E.fppf_mem Y.hom).obj
        (SheafOfModules.unit _ : Space.Modules.{u, u} E.fppfSite S E.fppf_mem X.1 X.2) ⟶
        (Space.modulePullback E.fppfSite S E.fppf_mem Y.hom).obj F) :
    associatedSectionsAddEquiv E F Y α =
      ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj
        ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj F)).val.presheaf.map
          (overFinalIso E Y).hom.op
      (associatedSectionsEquivRestriction E F Y.hom α) := rfl

/-- Steps A, B and C carry the restriction of `𝓕ᵃ` along `h` to restriction along `h`. -/
theorem associatedSectionsEquivRestriction_conjHom {Y : E.Spaces} (f : Y ⟶ X) (h : Z ⟶ Y)
    {g : Z ⟶ X} (hg : h ≫ f = g)
    (v : (inclusionFunctor E g).obj (Space.SpacesEtale.final E.fppfSite S E.fppf_mem Z) ⟶
      (inclusionFunctor E f).obj (Space.SpacesEtale.final E.fppfSite S E.fppf_mem Y))
    (hv : v.left = h)
    (α : (Space.modulePullback E.fppfSite S E.fppf_mem f).obj
        (SheafOfModules.unit _ : Space.Modules.{u, u} E.fppfSite S E.fppf_mem X.1 X.2) ⟶
        (Space.modulePullback E.fppfSite S E.fppf_mem f).obj F) :
    associatedSectionsEquivRestriction E F g
        (Functor.conjHom (Space.modulePullbackTriangle E.fppfSite S E.fppf_mem hg) α) =
      ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj
        ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj F)).val.presheaf.map v.op
          (associatedSectionsEquivRestriction E F f α) := by
  subst hg
  have hv' : v = (inclusionFunctor E (h ≫ f)).map (finalBaseChangeHom E h) ≫
      (inclusionFunctorTransition E h f).app
        (Space.SpacesEtale.final E.fppfSite S E.fppf_mem Y) := by
    apply Over.OverMorphism.ext
    show v.left = pullback.lift h (𝟙 Z) _ ≫ pullback.fst _ h
    rw [hv]
    exact (pullback.lift_fst _ _ _).symm
  subst hv'
  have t1 := spacesEtaleEquivRestriction_conjHom E F f h α
  have t2 := (congrArg (restrictionEquivSections E F (h ≫ f)) t1).trans
      (restrictionEquivSections_transition E F f h _)
  have t3 := (associatedSectionsEquivRestriction_apply E F (h ≫ f) _).trans t2
  rw [Space.modulePullbackTriangle_rfl]
  have t4 := t3.trans (congrArg
      (((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj
        ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj F)).val.presheaf.map
    ((inclusionFunctor E (h ≫ f)).map (finalBaseChangeHom E h) ≫
      (inclusionFunctorTransition E h f).app
        (Space.SpacesEtale.final E.fppfSite S E.fppf_mem Y)).op)
    (associatedSectionsEquivRestriction_apply E F f α)).symm
  with_reducible exact t4

/-- Naturality of the components of `𝓕ᵃ ≅ π_X^*(ι𝓕)`. -/
theorem associatedSectionsAddEquiv_naturality {Y Y' : Over X} (m : Y' ⟶ Y)
    (α : (Space.modulePullback E.fppfSite S E.fppf_mem Y.hom).obj
        (SheafOfModules.unit _ : Space.Modules.{u, u} E.fppfSite S E.fppf_mem X.1 X.2) ⟶
        (Space.modulePullback E.fppfSite S E.fppf_mem Y.hom).obj F) :
    associatedSectionsAddEquiv E F Y'
        (Functor.conjHom (Space.modulePullbackTriangle E.fppfSite S E.fppf_mem (Over.w m)) α) =
      ((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj
        ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj F)).val.presheaf.map m.op
          (associatedSectionsAddEquiv E F Y α) := by
  refine (associatedSectionsAddEquiv_apply E F Y' _).trans ?_
  refine Eq.trans ?_ (congrArg
      (((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj
        ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj F)).val.presheaf.map m.op)
    (associatedSectionsAddEquiv_apply E F Y α)).symm
  refine (congrArg
      (((spacesEtaleRestrictionRingedSiteHom E X).toRingedToposSiteHom.pullbackTopos.obj
        ((Space.toSpacesEtaleModules E.fppfSite S E.fppf_mem X).obj F)).val.presheaf.map
          (overFinalIso E Y').hom.op)
    (associatedSectionsEquivRestriction_conjHom E F Y.hom m.left (Over.w m)
      ((overFinalIso E Y').inv ≫ m ≫ (overFinalIso E Y).hom)
      ((Category.id_comp _).trans (Category.comp_id _)) α)).trans ?_
  exact Functor.map_op_map_op_apply_eq _ _ _ _ _ (Iso.hom_inv_id_assoc _ _) _

end AB

end AlgebraicGeometry.BigEtaleSpaceSite

end
