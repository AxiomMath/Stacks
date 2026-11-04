module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.HigherDirectImageBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatOverStackOfFlatObject
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Equalizers
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Injectives
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageFppfWeakSerre
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PullbackUnivLE

/-!
# Base change of higher direct images of fppf modules (Stacks 075H at module universe `u + 1`)

Let `S` be a scheme and let

```
𝒴' ×_𝒴 𝒳 --- g' ---> 𝒳
   |                 |
   f'                f
   |                 |
   v                 v
  𝒴' ------ g -----> 𝒴
```

be the canonical 2-cartesian square of categories fibred in groupoids over `(Sch/S)_fppf`.
**Stacks 075H** says that the base change map `g^{-1} Rf_* ℱ ⟶ Rf'_* (g')^{-1} ℱ` is an
isomorphism, also for `ℱ` in `Mod(𝒳_τ, 𝒪_𝒳)`. This file proves the module statement on the fppf
sites at module universe `u + 1`, the universe in which the direct images of modules on algebraic
stacks live: in degree zero for every square, and in every degree when the projection `g'` is
faithful (which holds as soon as `𝒴'` is faithful over the base, e.g. a scheme or a stack
representable by an affine scheme), in which case `(g')^*` preserves injectives.

## The argument

The base-change map is the mate, for the inverse-image / direct-image adjunctions of
**Stacks 06WE** along `f` and along `f'`, of the 2-cell `f'^* g^* ⟶ (g')^* f^*` induced by the
comparison isomorphism `ψ` of the square (Stacks 0040), which lies over identities
(`AlgebraicGeometry.Stack.modulePullbackBaseChangeTwoCell`). It is `𝒪`-linear by construction.
Its invertibility is checked on underlying abelian presheaves, where inverse images are
precompositions, the direct image is a right Kan extension whose counit is the counit of 06WE
(`AlgebraicGeometry.Stack.moduleSheafAdjunction_counit_realization`), and the mate becomes the
base change of right Kan extensions along the opposite square, invertible because the square is
Guitart exact (Stacks 075B,
`CategoryTheory.TwoFibreProductOver.guitartExact_twoFibreProductSquare`). The category-theoretic
core is `CategoryTheory.isIso_mateEquiv_app_of_realization`.

In higher degrees: `g^*` is exact, so `g^* ∘ Rⁿf_* ≅ Rⁿ(g^* ∘ f_*)`; the degree-zero
isomorphism identifies this with `Rⁿ(f'_* ∘ (g')^*)`; and `(g')^*` is exact and carries
injectives to injectives when `g'` is faithful and its source has equalizers (Stacks 06X1/06X2,
`AlgebraicGeometry.Stack.preservesInjectiveObjects_modulePullback_of_faithful`), so
`Rⁿ(f'_* ∘ (g')^*) ≅ Rⁿf'_* ∘ (g')^*`. This replaces the source's appeal to the value description
of Stacks 075G, and removes the linearity hypothesis `hlinear` that the base statements
`AlgebraicGeometry.Stack.nonempty_moduleDirectImageBaseChangeIso` and
`AlgebraicGeometry.Stack.nonempty_moduleHigherDirectImageBaseChangeIso` carry.

## Main results

* `CategoryTheory.isIso_mateEquiv_app_of_realization`: a mate is invertible when its realizations
  as functor-valued presheaves are base changes of Kan extensions along a Guitart exact square.
* `AlgebraicGeometry.Stack.isIso_fppfModuleDirectImageBaseChange_app`,
  `AlgebraicGeometry.Stack.fppfModuleDirectImageBaseChangeIso`: **Stacks 075H in degree zero** for
  sheaves of modules, `f_* ⋙ g^* ≅ (g')^* ⋙ f'_*`.
* `AlgebraicGeometry.Stack.fppfModuleHigherDirectImageBaseChangeIso`: **Stacks 075H in every
  degree** for sheaves of modules, `g^* Rⁿf_* ℱ ≅ Rⁿf'_* (g')^* ℱ`, for a faithful `g'`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.fppfHigherDirectImageBaseChangeIso`: the same for
  fppf modules on algebraic stacks, when `𝒴'` is faithful over the base.

## Implementation notes

The local `irreducible` attribute on `AlgebraicGeometry.Stack.ringStructureSheafCore` in some
sections keeps the elaborator from trying to decide, by unfolding the structure sheaves, the
(false) definitional equality of the two presheaves of rings that the transport of scalars in
`AlgebraicGeometry.Stack.modulePullback` identifies propositionally; no statement depends on it.
The global module-sheaf instances of `Stacks.Cohomology.SiteModules` are switched off, as in
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageFppfWeakSerre`'s consumers, so
that the higher direct images are those of the Abelian structure of Mathlib.

## References

* [Stacks Project, Tag 075H](https://stacks.math.columbia.edu/tag/075H)
* [Stacks Project, Tag 075B](https://stacks.math.columbia.edu/tag/075B)
* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 06X2](https://stacks.math.columbia.edu/tag/06X2)
* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

namespace CategoryTheory

section MateRealization

variable {𝒜 : Type*} {ℬ : Type*} {𝒜' : Type*} {ℬ' : Type*} [Category 𝒜] [Category ℬ]
  [Category 𝒜'] [Category ℬ']
  {X₀ : Type*} {Y₀ : Type*} {Y₀' : Type*} {P₀ : Type*} [Category X₀] [Category Y₀]
  [Category Y₀'] [Category P₀] {D : Type*} [Category D]
  {L₁ : 𝒜 ⥤ ℬ} {R₁ : ℬ ⥤ 𝒜} (adj₁ : L₁ ⊣ R₁) {L₂ : 𝒜' ⥤ ℬ'} {R₂ : ℬ' ⥤ 𝒜'} (adj₂ : L₂ ⊣ R₂)
  {G : 𝒜 ⥤ 𝒜'} {H : ℬ ⥤ ℬ'} (α : TwoSquare G L₁ L₂ H)
  {U₁ : 𝒜 ⥤ Y₀ ⥤ D} {U₂ : ℬ ⥤ X₀ ⥤ D} {U₃ : 𝒜' ⥤ Y₀' ⥤ D} {U₄ : ℬ' ⥤ P₀ ⥤ D}
  {fo : X₀ ⥤ Y₀} {go : Y₀' ⥤ Y₀} {fsto : P₀ ⥤ X₀} {sndo : P₀ ⥤ Y₀'}
  (w : TwoSquare sndo fsto go fo)
  (eL₁ : L₁ ⋙ U₂ ≅ U₁ ⋙ (Functor.whiskeringLeft _ _ D).obj fo)
  (eL₂ : L₂ ⋙ U₄ ≅ U₃ ⋙ (Functor.whiskeringLeft _ _ D).obj sndo)
  (eG : G ⋙ U₃ ≅ U₁ ⋙ (Functor.whiskeringLeft _ _ D).obj go)
  (eH : H ⋙ U₄ ≅ U₂ ⋙ (Functor.whiskeringLeft _ _ D).obj fsto)

/-- **Invertibility of a mate, read through realizations as presheaves.** Let `L₁ ⊣ R₁` and
`L₂ ⊣ R₂` be adjunctions and `α : G ⋙ L₂ ⟶ L₁ ⋙ H` a 2-cell, and suppose all four categories are
realized, through functors `Uᵢ`, in categories of functors to `D` on which the left adjoints `L₁`,
`L₂` and the functors `G`, `H` act as precomposition with `fo`, `sndo`, `go`, `fsto`, and `α` acts
as whiskering with a Guitart exact square `w : sndo ⋙ go ⟶ fsto ⋙ fo`. If the counit of `L₁ ⊣ R₁`
realizes each `R₁ M` as a pointwise right Kan extension along `fo`, the counit of `L₂ ⊣ R₂`
realizes each `R₂ (H M)` as a right Kan extension along `sndo`, and `U₃` reflects isomorphisms,
then the mate `R₁ ⋙ G ⟶ H ⋙ R₂` of `α` is an isomorphism at every object.

This is the abstract form of the base change of direct images along a Guitart exact square: on
realizations the mate is the base change of right Kan extensions. -/
theorem isIso_mateEquiv_app_of_realization [w.GuitartExact] [U₃.ReflectsIsomorphisms]
    (hα : ∀ A : 𝒜, Functor.whiskerLeft sndo (eG.inv.app A) ≫ eL₂.inv.app (G.obj A) ≫
      U₄.map (α.app A) ≫ eH.hom.app (L₁.obj A) =
        Functor.whiskerRight w.natTrans (U₁.obj A) ≫
          Functor.whiskerLeft fsto (eL₁.inv.app A))
    (hK₁ : ∀ M : ℬ, (Functor.RightExtension.mk (U₁.obj (R₁.obj M))
      (eL₁.inv.app (R₁.obj M) ≫ U₂.map (adj₁.counit.app M))).IsPointwiseRightKanExtension)
    (hK₂ : ∀ M : ℬ, (U₃.obj (R₂.obj (H.obj M))).IsRightKanExtension
      (eL₂.inv.app (R₂.obj (H.obj M)) ≫ U₄.map (adj₂.counit.app (H.obj M)) ≫ eH.hom.app M))
    (M : ℬ) : IsIso ((mateEquiv adj₁ adj₂ α).natTrans.app M) := by
  set θ := (mateEquiv adj₁ adj₂ α).natTrans.app M
  let E₁ := Functor.RightExtension.mk (U₁.obj (R₁.obj M))
    (eL₁.inv.app (R₁.obj M) ≫ U₂.map (adj₁.counit.app M))
  have : ((U₁ ⋙ (Functor.whiskeringLeft Y₀' Y₀ D).obj go).obj (R₁.obj M)).IsRightKanExtension
      (E₁.compTwoSquare w).hom := ((hK₁ M).compTwoSquare w).isRightKanExtension
  have : (U₃.obj ((H ⋙ R₂).obj M)).IsRightKanExtension
      (eL₂.inv.app (R₂.obj (H.obj M)) ≫ U₄.map (adj₂.counit.app (H.obj M)) ≫ eH.hom.app M) :=
    hK₂ M
  have key : IsIso (U₃.map θ) := by
    rw [← Functor.isRightKanExtension_iff_isIso (U₃.map θ)
      (eL₂.inv.app (R₂.obj (H.obj M)) ≫ U₄.map (adj₂.counit.app (H.obj M)) ≫ eH.hom.app M) _
      rfl]
    refine Functor.isRightKanExtension_of_iso (eG.app (R₁.obj M)).symm
      (E₁.compTwoSquare w).hom _ ?_
    ext z
    have h2' := NatTrans.congr_app (eL₂.inv.naturality θ) z
    have h3' := NatTrans.congr_app (eH.hom.naturality (adj₁.counit.app M)) z
    have h4' := NatTrans.congr_app (hα (R₁.obj M)) z
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.id_obj, Functor.comp_map, Functor.comp_obj, Functor.whiskeringLeft_obj_map]
      at h2' h3' h4'
    have h1' : (U₄.map (L₂.map θ)).app z ≫ (U₄.map (adj₂.counit.app (H.obj M))).app z =
        (U₄.map (α.app (R₁.obj M))).app z ≫ (U₄.map (H.map (adj₁.counit.app M))).app z := by
      rw [← NatTrans.comp_app, ← Functor.map_comp, mateEquiv_counit adj₁ adj₂ α M, Functor.map_comp,
        NatTrans.comp_app]
    simp only [Functor.RightExtension.compTwoSquare, NatTrans.comp_app, Functor.whiskerLeft_app,
      Iso.symm_hom, Iso.app_inv, Functor.comp_obj, E₁]
    rw [reassoc_of% h2', reassoc_of% h1', h3', reassoc_of% h4']
    simp [Functor.RightExtension.mk]
  exact isIso_of_reflects_iso θ U₃

end MateRealization

end CategoryTheory


namespace AlgebraicGeometry.Stack

universe u v w m v' w'

section Counit

variable {X : Type v} [Category.{w} X] {Y : Type v'} [Category.{w'} Y]
  (f : X ⥤ Y) (R : Yᵒᵖ ⥤ RingCat.{u})

/-- The counit of the adjunction of `moduleDirectImageData`, read on underlying abelian
presheaves, is the counit of the right Kan extension. -/
theorem toPresheaf_map_moduleDirectImageData_counit_app
    (T : Xᵒᵖ ⥤ RingCat.{u}) (h : T = f.op ⋙ R)
    (N : PresheafOfModules.{max u v w m v' w'} T) :
    (PresheafOfModules.toPresheaf T).map
        ((moduleDirectImageData.{u, v, w, m} f R T h).2.2.counit.app N) =
      Functor.whiskerLeft f.op
          ((moduleDirectImageData.{u, v, w, m} f R T h).2.1.hom.app N) ≫
        f.op.ranCounit.app ((PresheafOfModules.toPresheaf T).obj N) := by
  subst h
  rw [← Functor.ranAdjunction_counit]
  exact (Adjunction.rightAdjointUniq_hom_app_counit
    (sectionsAdjunction.{v, w, max u m} f.op)
    (f.op.ranAdjunction AddCommGrpCat.{max u v w m v' w'})
    ((PresheafOfModules.toPresheaf (f.op ⋙ R)).obj N)).symm

end Counit

section BaseChangeSquare

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] {𝒴' : Type (u + 1)} [Category.{u} 𝒴']
  {𝒴 : Type (u + 1)} [Category.{u} 𝒴]
  (p𝒳 : 𝒳 ⥤ BigFppfOver B S hS) (p𝒴' : 𝒴' ⥤ BigFppfOver B S hS)
  (p𝒴 : 𝒴 ⥤ BigFppfOver B S hS) (f : 𝒳 ⥤ 𝒴) (g : 𝒴' ⥤ 𝒴)
  (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴' : p𝒴'.IsFiberedInGroupoids)
  (h𝒴 : p𝒴.IsFiberedInGroupoids) (hfc : f ⋙ p𝒴 = p𝒳) (hgc : g ⋙ p𝒴 = p𝒴')

/-- The structure sheaf of a category fibred in groupoids sends an arrow lying over an identity
to an identification: both ends carry the ring of the same scheme. -/
theorem ringStructureSheafCore_obj_map_op_of_isHomLift {𝒵 : Type (u + 1)} [Category.{u} 𝒵]
    (p : 𝒵 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology) {a b : 𝒵} {U : BigFppfOver B S hS}
    (φ : a ⟶ b) (h : p.IsHomLift (𝟙 U) φ) :
    (ringStructureSheafCore B S hS p hp τ hτ).obj.map φ.op =
      eqToHom (congrArg (fun x => (BigFppfOver.structureSheaf B S hS).obj.obj (op x))
        ((IsHomLift.codomain_eq p (𝟙 U) φ).trans (IsHomLift.domain_eq p (𝟙 U) φ).symm)) := by
  show (BigFppfOver.structureSheaf B S hS).obj.map (p.map φ).op = _
  rw [IsHomLift.fac' p (𝟙 U) φ, Category.id_comp, eqToHom_trans, eqToHom_op, eqToHom_map]

/-- **The 2-cell of the canonical square on inverse images of modules.** For the canonical
2-cartesian square of categories fibred in groupoids, the comparison isomorphism `ψ` of
Stacks 0040, which lies over identities, induces a morphism `f'^* g^* ⟶ (g')^* f^*` of inverse
images of sheaves of modules (Stacks 06WE): at a module `N` on `𝒴` and an object `(U, x, y, φ)`
of the apex it is the restriction of `N` along `φ : f(x) ≅ g(y)`. -/
def modulePullbackBaseChangeTwoCell :
    TwoSquare
      (modulePullback.{u, _, _, u + 1, _, _} B S hS p𝒴' p𝒴 h𝒴' h𝒴 g hgc B.topology le_rfl)
      (modulePullback.{u, _, _, u + 1, _, _} B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc B.topology le_rfl)
      (modulePullback.{u, _, _, u + 1, _, _} B S hS
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
        (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒴'
        (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.snd_comp_eq
        B.topology le_rfl)
      (modulePullback.{u, _, _, u + 1, _, _} B S hS
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳
        (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒳
        (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.fst_comp_eq
        B.topology le_rfl) := by
  let pP := TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g
  let hP := TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc
  let fst := TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g
  let snd := TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g
  have : p𝒳.IsFibered := h𝒳.isFibered
  have : p𝒴'.IsFibered := h𝒴'.isFibered
  have : p𝒴.IsFibered := h𝒴.isFibered
  have : pP.IsFibered := hP.isFibered
  let J := B.topology.over (B.obj hS)
  have : f.IsContinuous (associatedTopology B S hS p𝒳 B.topology)
      (associatedTopology B S hS p𝒴 B.topology) :=
    ((h𝒴.isFibredOneMorphism hfc).isContinuous_and_isCocontinuous_inheritedTopology J).1
  have : g.IsContinuous (associatedTopology B S hS p𝒴' B.topology)
      (associatedTopology B S hS p𝒴 B.topology) :=
    ((h𝒴.isFibredOneMorphism hgc).isContinuous_and_isCocontinuous_inheritedTopology J).1
  have : fst.IsContinuous (associatedTopology B S hS pP B.topology)
      (associatedTopology B S hS p𝒳 B.topology) :=
    ((h𝒳.isFibredOneMorphism TwoFibreProductOver.fst_comp_eq)
      |>.isContinuous_and_isCocontinuous_inheritedTopology J).1
  have : snd.IsContinuous (associatedTopology B S hS pP B.topology)
      (associatedTopology B S hS p𝒴' B.topology) :=
    ((h𝒴'.isFibredOneMorphism TwoFibreProductOver.snd_comp_eq)
      |>.isContinuous_and_isCocontinuous_inheritedTopology J).1
  have : (fst ⋙ f).IsContinuous (associatedTopology B S hS pP B.topology)
      (associatedTopology B S hS p𝒴 B.topology) :=
    Functor.isContinuous_comp _ _ _ (associatedTopology B S hS p𝒳 B.topology) _
  have : (snd ⋙ g).IsContinuous (associatedTopology B S hS pP B.topology)
      (associatedTopology B S hS p𝒴 B.topology) :=
    Functor.isContinuous_comp _ _ _ (associatedTopology B S hS p𝒴' B.topology) _
  let φf : ringStructureSheafCore B S hS p𝒳 h𝒳 B.topology le_rfl ⟶
      (f.sheafPushforwardContinuous RingCat.{u} _ _).obj
        (ringStructureSheafCore B S hS p𝒴 h𝒴 B.topology le_rfl) :=
    ⟨eqToHom (ringStructureSheafCore_obj_eq B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc B.topology le_rfl)⟩
  let φg : ringStructureSheafCore B S hS p𝒴' h𝒴' B.topology le_rfl ⟶
      (g.sheafPushforwardContinuous RingCat.{u} _ _).obj
        (ringStructureSheafCore B S hS p𝒴 h𝒴 B.topology le_rfl) :=
    ⟨eqToHom (ringStructureSheafCore_obj_eq B S hS p𝒴' p𝒴 h𝒴' h𝒴 g hgc B.topology le_rfl)⟩
  let φfst : ringStructureSheafCore B S hS pP hP B.topology le_rfl ⟶
      (fst.sheafPushforwardContinuous RingCat.{u} _ _).obj
        (ringStructureSheafCore B S hS p𝒳 h𝒳 B.topology le_rfl) :=
    ⟨eqToHom (ringStructureSheafCore_obj_eq B S hS pP p𝒳 hP h𝒳 fst
      TwoFibreProductOver.fst_comp_eq B.topology le_rfl)⟩
  let φsnd : ringStructureSheafCore B S hS pP hP B.topology le_rfl ⟶
      (snd.sheafPushforwardContinuous RingCat.{u} _ _).obj
        (ringStructureSheafCore B S hS p𝒴' h𝒴' B.topology le_rfl) :=
    ⟨eqToHom (ringStructureSheafCore_obj_eq B S hS pP p𝒴' hP h𝒴' snd
      TwoFibreProductOver.snd_comp_eq B.topology le_rfl)⟩
  have he : ((φsnd ≫ (snd.sheafPushforwardContinuous RingCat.{u} _ _).map φg :
      ringStructureSheafCore B S hS pP hP B.topology le_rfl ⟶
        ((snd ⋙ g).sheafPushforwardContinuous RingCat.{u} _ _).obj
          (ringStructureSheafCore B S hS p𝒴 h𝒴 B.topology le_rfl))) ≫
      (Functor.sheafPushforwardContinuousNatTrans (F := fst ⋙ f) (F' := snd ⋙ g)
        (TwoFibreProductOver.psiIso p𝒳 p𝒴' p𝒴 f g).hom _ _ _).app
          (ringStructureSheafCore B S hS p𝒴 h𝒴 B.topology le_rfl) =
      φfst ≫ (fst.sheafPushforwardContinuous RingCat.{u} _ _).map φf := by
    refine Sheaf.hom_ext (NatTrans.ext (funext fun z => ?_))
    have := TwoFibreProductOver.psiIso_hom_vertical (p𝒳 := p𝒳) (p𝒴 := p𝒴') (p𝒮 := p𝒴)
      (F := f) (G := g) z.unop
    change (eqToHom (ringStructureSheafCore_obj_eq B S hS pP p𝒴' hP h𝒴' snd
          TwoFibreProductOver.snd_comp_eq B.topology le_rfl)).app z ≫
        (eqToHom (ringStructureSheafCore_obj_eq B S hS p𝒴' p𝒴 h𝒴' h𝒴 g hgc B.topology
          le_rfl)).app (op (snd.obj z.unop)) ≫
        (BigFppfOver.structureSheaf B S hS).obj.map
          (p𝒴.map ((TwoFibreProductOver.psiIso p𝒳 p𝒴' p𝒴 f g).hom.app z.unop)).op =
      (eqToHom (ringStructureSheafCore_obj_eq B S hS pP p𝒳 hP h𝒳 fst
          TwoFibreProductOver.fst_comp_eq B.topology le_rfl)).app z ≫
        (eqToHom (ringStructureSheafCore_obj_eq B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc B.topology
          le_rfl)).app (op (fst.obj z.unop))
    rw [IsHomLift.fac' p𝒴 (𝟙 z.unop.base)
      ((TwoFibreProductOver.psiIso p𝒳 p𝒴' p𝒴 f g).hom.app z.unop), Category.id_comp,
      eqToHom_trans, eqToHom_op, eqToHom_map]
    simp only [eqToHom_app]
    exact (eqToHom_trans_assoc _ _ _).trans ((eqToHom_trans _ _).trans (eqToHom_trans _ _).symm)
  exact (SheafOfModules.pushforwardComp.{u + 1} φsnd φg).hom ≫
    SheafOfModules.pushforwardNatTrans.{u + 1} (F := fst ⋙ f) (G := snd ⋙ g)
      (S := ringStructureSheafCore B S hS p𝒴 h𝒴 B.topology le_rfl)
      (φsnd ≫ (snd.sheafPushforwardContinuous RingCat.{u} _ _).map φg)
      (TwoFibreProductOver.psiIso p𝒳 p𝒴' p𝒴 f g).hom ≫
    (SheafOfModules.pushforwardCongr (F := fst ⋙ f) he).hom ≫
    (SheafOfModules.pushforwardComp.{u + 1} φfst φf).inv

end BaseChangeSquare

section CounitRealization

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒵 : Type (u + 1)} [Category.{u} 𝒵] {𝒲 : Type (u + 1)} [Category.{u} 𝒲]
  (p : 𝒵 ⥤ BigFppfOver B S hS) (q : 𝒲 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (F : 𝒵 ⥤ 𝒲) (hF : F ⋙ q = p)

attribute [local irreducible] ringStructureSheafCore

/-- The counit of the adjunction of `AlgebraicGeometry.Stack.moduleFunctoriality` (Stacks 06WD),
read on underlying abelian presheaves, is the counit of the right Kan extension along `F.op`
precomposed with `AlgebraicGeometry.Stack.ModuleFunctoriality.pushforward_iso`. -/
theorem toPresheaf_map_moduleFunctoriality_counit_app
    (N : PresheafOfModules.{u + 1} (ringStructureSheafCore B S hS p hp B.topology le_rfl).obj) :
    (PresheafOfModules.toPresheaf _).map
        ((moduleFunctoriality.{u, u + 1, u, u} B S hS p q hp hq F hF).adjunction.counit.app N) =
      Functor.whiskerLeft F.op
          ((moduleFunctoriality.{u, u + 1, u, u} B S hS p q hp hq F hF).pushforward_iso.hom.app
            N) ≫
        F.op.ranCounit.app ((PresheafOfModules.toPresheaf _).obj N) :=
  toPresheaf_map_moduleDirectImageData_counit_app.{u, u + 1, u, u, u + 1, u} F
    (ringStructureSheafCore B S hS q hq B.topology le_rfl).obj
    (ringStructureSheafCore B S hS p hp B.topology le_rfl).obj
    (moduleFunctoriality.{u, u + 1, u, u} B S hS p q hp hq F hF).structurePresheaf_eq N

/-- **The counit of Stacks 06WE, realized on underlying abelian presheaves**, at the level of
functors: the counit `F^* F_* ⟶ 𝟭` of the inverse-image / direct-image adjunction, read on
underlying abelian presheaves through `AlgebraicGeometry.Stack.modulePullbackCompToPresheafIso`, is
the counit of the right Kan extension along `F.op` precomposed with the identification
`AlgebraicGeometry.Stack.moduleSheafPushforwardCompToPresheafIso` of the direct image with that
Kan extension. -/
theorem moduleSheafAdjunction_counit_realization :
    Functor.whiskerLeft (moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS p q hp hq F hF
          B.topology le_rfl)
        (modulePullbackCompToPresheafIso.{u, u + 1, u, u + 1, u, u} B S hS p q hp hq F hF
          B.topology le_rfl).inv ≫
      Functor.whiskerRight
        (moduleSheafAdjunction.{u, u + 1, u, u, u + 1, u} B S hS p q hp hq F hF
          B.topology le_rfl).counit
        (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _) =
      Functor.whiskerRight
          (moduleSheafPushforwardCompToPresheafIso.{u, u + 1, u, u + 1, u, u}
            B S hS p q hp hq F hF B.topology le_rfl).hom
          ((Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj F.op) ≫
        Functor.whiskerLeft (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _)
          (F.op.ranAdjunction AddCommGrpCat.{u + 1}).counit := by
  ext M : 2
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_map, moduleSheafAdjunction, Functor.ranAdjunction_counit]
  have h := Adjunction.map_restrictFullyFaithful_counit_app
    (L := modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS p q hp hq F hF B.topology le_rfl)
    (R := moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS p q hp hq F hF
      B.topology le_rfl)
    (moduleFunctoriality.{u, u + 1, u, u} B S hS p q hp hq F hF).adjunction
    (SheafOfModules.fullyFaithfulForget (ringStructureSheafCore B S hS q hq B.topology le_rfl))
    (SheafOfModules.fullyFaithfulForget (ringStructureSheafCore B S hS p hp B.topology le_rfl))
    (Functor.isoWhiskerLeft
        (SheafOfModules.forget (ringStructureSheafCore B S hS q hq B.topology le_rfl))
        (moduleFunctoriality.{u, u + 1, u, u} B S hS p q hp hq F hF).pullback_iso ≪≫
      (modulePullbackForgetIso.{u, u + 1, u, u + 1, u + 1, u}
        B S hS p q hp hq F hF B.topology le_rfl).symm)
    (Iso.refl _) M
  rw [h]
  have hpb : (moduleFunctoriality.{u, u + 1, u, u} B S hS p q hp hq F hF).pullback_iso =
      Iso.refl _ := rfl
  simp only [hpb, modulePullbackForgetIso, modulePullbackCompToPresheafIso,
    moduleSheafPushforwardCompToPresheafIso, Iso.trans_inv, Iso.refl_inv,
    Functor.isoWhiskerLeft_hom, NatTrans.id_app, Functor.whiskerLeft_app]
  exact toPresheaf_map_moduleFunctoriality_counit_app B S hS p q hp hq F hF M.val

/-- **The direct image of Stacks 06WE is a pointwise right Kan extension on underlying abelian
presheaves.** For a sheaf of modules `M` on the source, the underlying abelian presheaf of `F_* M`,
together with the counit `F^* F_* M ⟶ M` read on underlying abelian presheaves, is a pointwise
right Kan extension of the underlying abelian presheaf of `M` along `F.op`. -/
noncomputable def isPointwiseRightKanExtension_moduleSheafPushforward
    (M : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS p hp B.topology le_rfl)) :
    (Functor.RightExtension.mk
      ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).obj
        ((moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS p q hp hq F hF
          B.topology le_rfl).obj M))
      ((modulePullbackCompToPresheafIso.{u, u + 1, u, u + 1, u, u} B S hS p q hp hq F hF
          B.topology le_rfl).inv.app
          ((moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS p q hp hq F hF
            B.topology le_rfl).obj M) ≫
        (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
          ((moduleSheafAdjunction.{u, u + 1, u, u, u + 1, u} B S hS p q hp hq F hF
            B.topology le_rfl).counit.app M))).IsPointwiseRightKanExtension := by
  have h := congrArg (fun t => t.app M)
    (moduleSheafAdjunction_counit_realization B S hS p q hp hq F hF)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.ranAdjunction_counit, Functor.whiskeringLeft_obj_map] at h
  refine (Functor.RightExtension.isPointwiseRightKanExtensionEquivOfIso
    (CostructuredArrow.isoMk
      ((moduleSheafPushforwardCompToPresheafIso.{u, u + 1, u, u + 1, u, u}
        B S hS p q hp hq F hF B.topology le_rfl).app M).symm ?_))
    (F.op.isPointwiseRightKanExtensionRanCounit _)
  simp only [Functor.RightExtension.mk, CostructuredArrow.mk_hom_eq_self, Iso.symm_hom,
    Iso.app_inv, h, Functor.id_obj]
  rw [Functor.whiskeringLeft_obj_map, ← Functor.whiskerLeft_comp_assoc, Iso.inv_hom_id_app]
  exact Category.id_comp _

/-- The ring map of `AlgebraicGeometry.Stack.ringStructureSheafCoreHom` is the one through which
`AlgebraicGeometry.Stack.modulePullback` transports scalars. -/
theorem ringStructureSheafCoreHom_eq_eqToHom (τ : GrothendieckTopology B.Schemes)
    (hτ : τ ≤ B.topology) :
    letI : p.IsFibered := hp.isFibered
    letI : q.IsFibered := hq.isFibered
    letI := ((hq.isFibredOneMorphism hF).isContinuous_and_isCocontinuous_inheritedTopology
      (τ.over (B.obj hS))).1
    ringStructureSheafCoreHom B S hS p q F τ hp hq hF hτ =
      ⟨eqToHom (ringStructureSheafCore_obj_eq B S hS p q hp hq F hF τ hτ)⟩ := by
  subst hF
  with_unfolding_all rfl

/-- **Stacks 06X1 / 06X2 for sheaves of modules, through the inverse image of Stacks 06WE.** The
inverse image of sheaves of modules along a faithful 1-morphism of categories fibred in
groupoids whose source has equalizers carries injective sheaves of modules to injective ones, at
module universe `u + 1`. -/
theorem preservesInjectiveObjects_modulePullback_of_faithful [F.Faithful] [HasEqualizers 𝒵]
    [HasSheafify (associatedTopology B S hS q B.topology) AddCommGrpCat.{u + 1}]
    [(associatedTopology B S hS q B.topology).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [HasSheafify (associatedTopology B S hS p B.topology) AddCommGrpCat.{u + 1}]
    [(associatedTopology B S hS p B.topology).WEqualsLocallyBijective AddCommGrpCat.{u + 1}] :
    (modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS p q hp hq F hF B.topology
      le_rfl).PreservesInjectiveObjects := by
  have : p.IsFibered := hp.isFibered
  have : q.IsFibered := hq.isFibered
  have := ((hq.isFibredOneMorphism hF).isContinuous_and_isCocontinuous_inheritedTopology
    (B.topology.over (B.obj hS))).1
  refine ⟨fun {I} _ => ?_⟩
  have hinj := injective_sheafOfModules_pushforward_obj.{u, u + 1, u + 1, u, u, u + 1}
    B S hS p q F B.topology hp hq hF le_rfl
    (PresheafOfModules.isRightAdjoint_pushforward_of_univLE.{u + 1} (F := F)
      (R := (ringStructureSheafCore B S hS q hq B.topology le_rfl).obj)
      (S := (ringStructureSheafCore B S hS p hp B.topology le_rfl).obj)
      (ringStructureSheafCoreHom B S hS p q F B.topology hp hq hF le_rfl).hom) I
  rwa [ringStructureSheafCoreHom_eq_eqToHom] at hinj

end CounitRealization

section DirectImageBaseChange

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] {𝒴' : Type (u + 1)} [Category.{u} 𝒴']
  {𝒴 : Type (u + 1)} [Category.{u} 𝒴]
  (p𝒳 : 𝒳 ⥤ BigFppfOver B S hS) (p𝒴' : 𝒴' ⥤ BigFppfOver B S hS)
  (p𝒴 : 𝒴 ⥤ BigFppfOver B S hS) (f : 𝒳 ⥤ 𝒴) (g : 𝒴' ⥤ 𝒴)
  (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴' : p𝒴'.IsFiberedInGroupoids)
  (h𝒴 : p𝒴.IsFiberedInGroupoids) (hfc : f ⋙ p𝒴 = p𝒳) (hgc : g ⋙ p𝒴 = p𝒴')

attribute [local irreducible] ringStructureSheafCore

/-- **The base-change map of Stacks 075H for sheaves of modules.** For the canonical
2-cartesian square of categories fibred in groupoids over `(Sch/S)_fppf`, the base-change map
`g^* f_* ℱ ⟶ f'_* (g')^* ℱ` of sheaves of modules: the mate, for the inverse-image / direct-image
adjunctions of Stacks 06WE along `f` and along the second projection `f'`, of the 2-cell
`AlgebraicGeometry.Stack.modulePullbackBaseChangeTwoCell` induced by the comparison isomorphism of
the square. -/
abbrev fppfModuleDirectImageBaseChange :=
  mateEquiv
    (moduleSheafAdjunction.{u, u + 1, u, u, u + 1, u} B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc
      B.topology le_rfl)
    (moduleSheafAdjunction.{u, u + 1, u, u, u + 1, u} B S hS
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
      (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒴'
      (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.snd_comp_eq
      B.topology le_rfl)
    (modulePullbackBaseChangeTwoCell B S hS p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc)

/-- **Stacks 075H in degree zero for sheaves of modules.** The base-change map
`g^* f_* ℱ ⟶ f'_* (g')^* ℱ` of sheaves of modules on the fppf sites, for the canonical
2-cartesian square, is an isomorphism at every `ℱ`.

Through the realization of modules as abelian presheaves, inverse images are precompositions,
direct images are right Kan extensions
(`AlgebraicGeometry.Stack.moduleSheafAdjunction_counit_realization`), and the mate becomes the
base change of right Kan extensions along the opposite square, which is Guitart exact by Stacks
075B (`CategoryTheory.TwoFibreProductOver.guitartExact_twoFibreProductSquare`); see
`AlgebraicGeometry.Stack.isIso_mateEquiv_app_of_realization`. -/
theorem isIso_fppfModuleDirectImageBaseChange_app
    (M : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS p𝒳 h𝒳 B.topology le_rfl)) :
    IsIso ((fppfModuleDirectImageBaseChange B S hS p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc).natTrans.app
      M) := by
  have : (baseChangeTwoSquare p𝒳 p𝒴' p𝒴 f g).GuitartExact :=
    TwoFibreProductOver.guitartExact_twoFibreProductSquare p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc
  refine isIso_mateEquiv_app_of_realization _ _ _ (baseChangeTwoSquare p𝒳 p𝒴' p𝒴 f g).op
    (modulePullbackCompToPresheafIso.{u, u + 1, u, u + 1, u, u} B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc
      B.topology le_rfl)
    (modulePullbackCompToPresheafIso.{u, u + 1, u, u + 1, u, u} B S hS
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
      (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒴'
      (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.snd_comp_eq
      B.topology le_rfl)
    (modulePullbackCompToPresheafIso.{u, u + 1, u, u + 1, u, u} B S hS p𝒴' p𝒴 h𝒴' h𝒴 g hgc
      B.topology le_rfl)
    (modulePullbackCompToPresheafIso.{u, u + 1, u, u + 1, u, u} B S hS
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳
      (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒳
      (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.fst_comp_eq
      B.topology le_rfl) ?_ ?_ ?_ M
  · intro A
    ext z x
    rfl
  · exact isPointwiseRightKanExtension_moduleSheafPushforward B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc
  · exact fun N => (isPointwiseRightKanExtension_moduleSheafPushforward B S hS
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
      (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒴'
      (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.snd_comp_eq
      ((modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳
        (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒳
        (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.fst_comp_eq
        B.topology le_rfl).obj N)).isRightKanExtension

/-- **Stacks 075H in degree zero for sheaves of modules**, as an isomorphism of functors:
`f_* ⋙ g^* ≅ (g')^* ⋙ f'_*` for the canonical 2-cartesian square, the mate of the 2-cell of
the square (`AlgebraicGeometry.Stack.fppfModuleDirectImageBaseChange`). -/
noncomputable def fppfModuleDirectImageBaseChangeIso :
    moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc
        B.topology le_rfl ⋙
      modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS p𝒴' p𝒴 h𝒴' h𝒴 g hgc
        B.topology le_rfl ≅
    modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳
        (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒳
        (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.fst_comp_eq
        B.topology le_rfl ⋙
      moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
        (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒴'
        (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.snd_comp_eq
        B.topology le_rfl :=
  haveI := isIso_fppfModuleDirectImageBaseChange_app B S hS p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc
  haveI : IsIso
      (fppfModuleDirectImageBaseChange B S hS p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc).natTrans :=
    NatIso.isIso_of_isIso_app _
  asIso (fppfModuleDirectImageBaseChange B S hS p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc).natTrans

variable
  [HasSheafify (associatedTopology B S hS p𝒳 B.topology) AddCommGrpCat.{u + 1}]
  [(associatedTopology B S hS p𝒳 B.topology).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [HasSheafify (associatedTopology B S hS p𝒴 B.topology) AddCommGrpCat.{u + 1}]
  [(associatedTopology B S hS p𝒴 B.topology).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [HasSheafify (associatedTopology B S hS p𝒴' B.topology) AddCommGrpCat.{u + 1}]
  [(associatedTopology B S hS p𝒴' B.topology).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [HasSheafify (associatedTopology B S hS
    (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) B.topology) AddCommGrpCat.{u + 1}]
  [(associatedTopology B S hS (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g)
    B.topology).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]

/-- **Stacks 075H for sheaves of modules, in every degree.** For the canonical 2-cartesian square
of categories fibred in groupoids over `(Sch/S)_fppf` whose first projection `g' : 𝒴' ×_𝒴 𝒳 ⥤ 𝒳`
is faithful and whose apex has equalizers, the base change map is an isomorphism
`g^* Rⁿf_* ℱ ≅ Rⁿf'_* (g')^* ℱ` of sheaves of modules, at module universe `u + 1`.

The inverse image `g^*` is exact, so it may be pulled into the right derived functor; the
degree-zero isomorphism `AlgebraicGeometry.Stack.fppfModuleDirectImageBaseChangeIso` identifies
`f_* ⋙ g^*` with `(g')^* ⋙ f'_*`; and `(g')^*` is exact and, `g'` being faithful with source
having equalizers, carries injectives to injectives (Stacks 06X1 / 06X2,
`AlgebraicGeometry.Stack.preservesInjectiveObjects_modulePullback_of_faithful`), so it carries an
injective resolution of `ℱ` to one of `(g')^* ℱ`. This is the step the source takes through the
value description of Stacks 075G; faithfulness of `g'` holds for instance when `𝒴'` is
representable by a scheme (its structure functor is faithful). -/
noncomputable def fppfModuleHigherDirectImageBaseChangeIso
    [(TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g).Faithful]
    [HasEqualizers (TwoFibreProductOver p𝒳 p𝒴' p𝒴 f g)] (n : ℕ)
    (M : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS p𝒳 h𝒳 B.topology le_rfl)) :
    (modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS p𝒴' p𝒴 h𝒴' h𝒴 g hgc
        B.topology le_rfl).obj
        ((moduleSheafHigherDirectImage.{u, u + 1, u, u + 1, u} B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc
          B.topology le_rfl n).obj M) ≅
      (moduleSheafHigherDirectImage.{u, u + 1, u, u + 1, u} B S hS
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
        (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒴'
        (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.snd_comp_eq
        B.topology le_rfl n).obj
        ((modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS
          (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳
          (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒳
          (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.fst_comp_eq
          B.topology le_rfl).obj M) := by
  let hP := TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc
  letI : EnoughInjectives
      (SheafOfModules.{u + 1} (ringStructureSheafCore B S hS p𝒳 h𝒳 B.topology le_rfl)) :=
    enoughInjectives_moduleSheaves.{u, u + 1, u, u + 1} B S hS p𝒳 h𝒳 B.topology le_rfl
  letI : EnoughInjectives (SheafOfModules.{u + 1} (ringStructureSheafCore B S hS
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) hP B.topology le_rfl)) :=
    enoughInjectives_moduleSheaves.{u, u + 1, u, u + 1} B S hS _ hP B.topology le_rfl
  letI : PreservesFiniteLimits (modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS p𝒴' p𝒴
      h𝒴' h𝒴 g hgc B.topology le_rfl) :=
    preservesFiniteLimits_modulePullback'.{u, u + 1, u, u + 1, u, u + 1}
      B S hS p𝒴' p𝒴 h𝒴' h𝒴 g hgc B.topology le_rfl
  letI := (moduleSheafAdjunction.{u, u + 1, u, u, u + 1, u} B S hS p𝒴' p𝒴 h𝒴' h𝒴 g hgc
    B.topology le_rfl).leftAdjoint_preservesColimits
  letI : PreservesFiniteLimits (modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳 hP h𝒳
      (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.fst_comp_eq
      B.topology le_rfl) :=
    preservesFiniteLimits_modulePullback'.{u, u + 1, u, u + 1, u, u + 1}
      B S hS _ p𝒳 hP h𝒳 _ TwoFibreProductOver.fst_comp_eq B.topology le_rfl
  letI := (moduleSheafAdjunction.{u, u + 1, u, u, u + 1, u} B S hS
    (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳 hP h𝒳
    (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.fst_comp_eq
    B.topology le_rfl).leftAdjoint_preservesColimits
  letI := preservesInjectiveObjects_modulePullback_of_faithful B S hS
    (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳 hP h𝒳
    (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.fst_comp_eq
  exact ((Functor.rightDerivedCompIso
      (moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc
        B.topology le_rfl)
      (modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS p𝒴' p𝒴 h𝒴' h𝒴 g hgc
        B.topology le_rfl) n).app M).symm ≪≫
    (Functor.rightDerivedIsoOfNatIso
      (fppfModuleDirectImageBaseChangeIso B S hS p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) n).app M ≪≫
    Functor.rightDerivedCompIsoOfPreservesInjectiveObjects _ _ M n

end DirectImageBaseChange

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] hasSheafify_fppfAssociatedTopology
  wEqualsLocallyBijective_fppfAssociatedTopology

/-- **Stacks 075H for fppf modules on algebraic stacks, in every degree.** Let `f : 𝒳 ⟶ 𝒴` and
`g : 𝒴' ⟶ 𝒴` be 1-morphisms of algebraic stacks over `S`, let `𝒴' ×_𝒴 𝒳` be their 2-fibre
product (Stacks 04T2) with projections `g' : 𝒴' ×_𝒴 𝒳 ⟶ 𝒳` and `f' : 𝒴' ×_𝒴 𝒳 ⟶ 𝒴'`, and
suppose the structure functor of `𝒴'` is faithful (for instance `𝒴'` is a scheme or is
representable by an affine scheme). Then for every `𝒪_𝒳`-module `ℱ` on the fppf site and every
degree `n` the base change map is an isomorphism `g^* Rⁿf_* ℱ ≅ Rⁿf'_* (g')^* ℱ`.

This is `AlgebraicGeometry.Stack.fppfModuleHigherDirectImageBaseChangeIso` in the seating of
`AlgebraicGeometry.Stack.AlgebraicStacks.fppfHigherDirectImage`: the first projection is faithful
by `CategoryTheory.TwoFibreProductOver.faithful_fst` and the apex has equalizers, being
an algebraic stack (`AlgebraicGeometry.Stack.AlgebraicStacks.hasEqualizers`). -/
noncomputable def fppfHigherDirectImageBaseChangeIso {𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴) [𝒴'.val.val.p.Faithful] (n : ℕ) (F : fppfModules B S hS 𝒳) :
    (fppfModulePullback B S hS g).obj ((fppfHigherDirectImage B S hS f n).obj F) ≅
      (fppfHigherDirectImage B S hS (twoFibreProductSquareAlgebraicStacks B S hS f g).snd n).obj
        ((fppfModulePullback B S hS (twoFibreProductSquareAlgebraicStacks B S hS f g).fst).obj F) :=
  letI : (TwoFibreProductOver.fst 𝒳.val.val.p 𝒴'.val.val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor g.hom)).Faithful :=
    TwoFibreProductOver.faithful_fst _ _ _ _ _
  letI : HasEqualizers (TwoFibreProductOver 𝒳.val.val.p 𝒴'.val.val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor g.hom)) :=
    AlgebraicStacks.hasEqualizers B S hS (twoFibreProductAlgebraicStack B S hS f g)
  letI := hasSheafify_fppfAssociatedTopology B S hS (twoFibreProductAlgebraicStack B S hS f g)
  letI := wEqualsLocallyBijective_fppfAssociatedTopology B S hS
    (twoFibreProductAlgebraicStack B S hS f g)
  fppfModuleHigherDirectImageBaseChangeIso B S hS 𝒳.val.val.p 𝒴'.val.val.p 𝒴.val.val.p
    (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor g.hom)
    𝒳.val.isFiberedInGroupoids 𝒴'.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor_comp_p f.hom) (CatFiberedInGroupoids.homFunctor_comp_p g.hom)
    n F

end AlgebraicGeometry.Stack.AlgebraicStacks

end
