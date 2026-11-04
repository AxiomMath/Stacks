module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PointTwistGraded
meta import StacksFrontier.Tactic.HEqCongr

/-!
# The base change identification of `𝒪_P(n)` to a scheme point is natural in the point

In Situation 0849 let `P = Proj_X(𝒜)` be the relative homogeneous spectrum of Stacks 084B and
`𝒪_P(n)` the twists of Stacks 084D.  For a scheme point `f : T ⟶ X` the inverse image of
`𝒪_P(n)` along `T ×_X P ⟶ P` is identified with the twist `𝒪(n)` of Stacks 01NR on
`T ×_X P = Proj_T(f^*𝒜)`
(`AlgebraicGeometry.Space.RelativeProjSituation.fibreToSpaceTwistModuleIso`).
This file proves that **the identification is natural in the scheme point**: along a morphism
`τ : T' ⟶ T` of the site and a morphism `y : T' ×_X P ⟶ T ×_X P` of base changes lying over `τ`,
the identification at `f ∘ τ` is the identification at `f` pulled back along `y`
(`AlgebraicGeometry.Space.attachedModuleIsoPullback`), read through the comparison
`y^*𝒪(n) ≅ 𝒪(n)` of twists of Tag 01O3
(`AlgebraicGeometry.Space.RelativeProjSituation.fibreToSpaceTwistModuleIso_comp`).

The proof checks the description of the pulled-back identification on the étale cover
`T'_U ×_{T'} P'' ⟶ T' ×_X P` and concludes by the faithfulness of the inverse image along the
atlas (`AlgebraicGeometry.Space.attachedModuleIsoPullback_eq_of_spec`).  The two presenting
schemes `T'_U ×_{T'} P''` and `T_U ×_T P'` belong to two different base changes of the situation;
their comparisons of twists are related through the base change `T_U ×_X P` of `P` itself
(`AlgebraicGeometry.Space.comparison_eq_pullback_ratio`, instantiated in
`AlgebraicGeometry.Space.RelativeProjSituation.chartTwistComparison_pointNatural`).

## Main definitions

* `AlgebraicGeometry.Space.attachedModuleIsoPullback`: an identification `h^*𝒯 ≅ N^a` on a
  representable algebraic space, transferred along a morphism of schemes `y : W' ⟶ W`.
* `AlgebraicGeometry.Space.RelativeProjSituation.pointPresentationMap`: the morphism of presenting
  schemes `T'_U ×_{T'} P'' ⟶ T_U ×_T P'` over `τ`.

## Main results

* `AlgebraicGeometry.Space.attachedModuleIsoPullback_spec_represented`: the description on the
  étale cover of a transferred identification, from the coherence of the comparisons of
  Stacks 03LU (`AlgebraicGeometry.Space.modulePullbackCompInv_chain_eq`).
* `AlgebraicGeometry.Space.RelativeProjPoints.pullbackTransitionCompatibleIso_comp`: the
  identification of a descended module along a representable base change is natural.
* `AlgebraicGeometry.Space.RelativeProjSituation.fibreToSpaceTwistModuleIso_comp`: **the base
  change identification of Stacks 084D is natural in the scheme point.**

## References

* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
-/

@[expose] public noncomputable section

universe u m

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Space

/-! ### Coherence of the contractions of pullbacks of quasi-coherent modules -/

section QuasicoherentCoherence

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The underlying morphism of a transport between pullbacks along equal morphisms. -/
theorem quasicoherentPullbackEqToHom_hom {V U : BigFppfOver B S hS} {k₁ k₂ : V ⟶ U}
    (e : k₁ = k₂) (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    (quasicoherentPullbackEqToHom B S hS e M).hom =
      eqToHom (congrArg (fun k => (quasicoherentPullbackObj B S hS k M).obj) e) := by
  subst e
  rfl

/-- Transports between pullbacks along equal morphisms compose. -/
@[reassoc]
theorem quasicoherentPullbackEqToHom_trans {V U : BigFppfOver B S hS} {k₁ k₂ k₃ : V ⟶ U}
    (e : k₁ = k₂) (e' : k₂ = k₃) (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    quasicoherentPullbackEqToHom B S hS e M ≫ quasicoherentPullbackEqToHom B S hS e' M =
      quasicoherentPullbackEqToHom B S hS (e.trans e') M := by
  subst e e'
  rfl

/-- **The contraction `h^*(g^*M) ≅ (h ≫ g)^*M` is natural in `M`.** -/
@[reassoc]
theorem quasicoherentPullbackMap_map_comp_compIso_hom {W V U : BigFppfOver B S hS} (h : W ⟶ V)
    (g : V ⟶ U) {M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory} (φ : M ⟶ N) :
    quasicoherentPullbackMap B S hS h (quasicoherentPullbackMap B S hS g φ) ≫
        (quasicoherentPullbackCompIso B S hS h g N).hom =
      (quasicoherentPullbackCompIso B S hS h g M).hom ≫ quasicoherentPullbackMap B S hS (h ≫ g) φ :=
  ObjectProperty.hom_ext _ ((Scheme.Modules.pullbackComp
    (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) h.left)
    (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
      g.left)).hom.naturality φ.hom)

/-- The contraction `h^*(g^*M) ≅ (h ≫ g)^*M` is natural in `M`, inverted. -/
@[reassoc]
theorem quasicoherentPullbackCompIso_inv_comp_map_map {W V U : BigFppfOver B S hS} (h : W ⟶ V)
    (g : V ⟶ U) {M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory} (φ : M ⟶ N) :
    (quasicoherentPullbackCompIso B S hS h g M).inv ≫
        quasicoherentPullbackMap B S hS h (quasicoherentPullbackMap B S hS g φ) =
      quasicoherentPullbackMap B S hS (h ≫ g) φ ≫
        (quasicoherentPullbackCompIso B S hS h g N).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← quasicoherentPullbackMap_map_comp_compIso_hom,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The pullback of an isomorphism followed by the pullback of its inverse. -/
@[reassoc]
theorem quasicoherentPullbackMap_hom_comp_map_inv {V U : BigFppfOver B S hS} (g : V ⟶ U)
    {M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory} (e : M ≅ N) :
    quasicoherentPullbackMap B S hS g e.hom ≫ quasicoherentPullbackMap B S hS g e.inv = 𝟙 _ := by
  rw [← quasicoherentPullbackMap_comp, Iso.hom_inv_id, quasicoherentPullbackMap_id]

/-- The pullback of the inverse of an isomorphism followed by the pullback of the isomorphism. -/
@[reassoc]
theorem quasicoherentPullbackMap_inv_comp_map_hom {V U : BigFppfOver B S hS} (g : V ⟶ U)
    {M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory} (e : M ≅ N) :
    quasicoherentPullbackMap B S hS g e.inv ≫ quasicoherentPullbackMap B S hS g e.hom = 𝟙 _ := by
  rw [← quasicoherentPullbackMap_comp, Iso.inv_hom_id, quasicoherentPullbackMap_id]

/-- The associativity of the contractions of pullbacks of modules on schemes, at a module. -/
private theorem pullbackComp_hom_app_assoc_eq {X Y Z Z' : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : Z ⟶ Z') (M : Z'.Modules) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app M) ≫
        (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app M =
      (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫
        (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M ≫ eqToHom (by rw [Category.assoc]) := by
  have hT := NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity f g h) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.id_comp, eqToHom_app] at hT
  calc _ = ((Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app M) ≫
        (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app M) ≫
        ((Scheme.Modules.pullbackComp f (g ≫ h)).inv.app M ≫
          (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).inv.app M) ≫
            (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫
              (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M) ≫
          eqToHom (by rw [Category.assoc]) := by
        rw [hT, eqToHom_trans, eqToHom_refl, Category.comp_id]
    _ = _ := by
        simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
        rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
          Category.id_comp]

/-- The associativity of the contractions of pullbacks of modules on schemes, inverted. -/
private theorem pullbackComp_inv_app_assoc_eq {X Y Z Z' : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : Z ⟶ Z') (M : Z'.Modules) :
    (Scheme.Modules.pullbackComp f (g ≫ h)).inv.app M ≫
        (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).inv.app M) =
      eqToHom (by rw [Category.assoc]) ≫ (Scheme.Modules.pullbackComp (f ≫ g) h).inv.app M ≫
        (Scheme.Modules.pullbackComp f g).inv.app ((Scheme.Modules.pullback h).obj M) := by
  have hT := NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity f g h) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.id_comp, eqToHom_app] at hT
  rw [← hT]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
  exact (Category.comp_id _).symm

/-- **The associativity of the contractions of pullbacks of quasi-coherent modules.** -/
@[reassoc]
theorem quasicoherentPullbackMap_compIso_hom_comp_compIso_hom {A V W U : BigFppfOver B S hS}
    (w : A ⟶ V) (φ : V ⟶ W) (a : W ⟶ U) (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    quasicoherentPullbackMap B S hS w (quasicoherentPullbackCompIso B S hS φ a M).hom ≫
        (quasicoherentPullbackCompIso B S hS w (φ ≫ a) M).hom =
      (quasicoherentPullbackCompIso B S hS w φ (quasicoherentPullbackObj B S hS a M)).hom ≫
        (quasicoherentPullbackCompIso B S hS (w ≫ φ) a M).hom ≫
          quasicoherentPullbackEqToHom B S hS (Category.assoc w φ a) M := by
  refine ObjectProperty.hom_ext _ ?_
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.comp_hom, quasicoherentPullbackEqToHom_hom]
  exact pullbackComp_hom_app_assoc_eq _ _ _ M.obj

/-- **The associativity of the contractions of pullbacks of quasi-coherent modules**, inverted. -/
@[reassoc]
theorem quasicoherentPullbackCompIso_inv_comp_map_compIso_inv {A V W U : BigFppfOver B S hS}
    (w : A ⟶ V) (φ : V ⟶ W) (a : W ⟶ U) (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    (quasicoherentPullbackCompIso B S hS w (φ ≫ a) M).inv ≫
        quasicoherentPullbackMap B S hS w (quasicoherentPullbackCompIso B S hS φ a M).inv =
      quasicoherentPullbackEqToHom B S hS (Category.assoc w φ a).symm M ≫
        (quasicoherentPullbackCompIso B S hS (w ≫ φ) a M).inv ≫
          (quasicoherentPullbackCompIso B S hS w φ (quasicoherentPullbackObj B S hS a M)).inv := by
  refine ObjectProperty.hom_ext _ ?_
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.comp_hom, quasicoherentPullbackEqToHom_hom]
  exact pullbackComp_inv_app_assoc_eq _ _ _ M.obj

/-- Two pullbacks of composable morphisms, followed by a morphism, are the pullback of the
composite. -/
theorem quasicoherentPullbackMap_comp_comp {V U : BigFppfOver B S hS} (g : V ⟶ U)
    {M N K : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    (φ : M ⟶ N) (ψ : N ⟶ K) {Z : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj V).ringCatSheaf).FullSubcategory}
    (h : quasicoherentPullbackObj B S hS g K ⟶ Z) :
    quasicoherentPullbackMap B S hS g φ ≫ quasicoherentPullbackMap B S hS g ψ ≫ h =
      quasicoherentPullbackMap B S hS g (φ ≫ ψ) ≫ h := by
  rw [quasicoherentPullbackMap_comp, Category.assoc]

/-- A morphism pulled back along `φ` between two contractions, then pulled back along `w`, is the
morphism pulled back along `w ≫ φ` between the contractions. -/
@[reassoc]
theorem quasicoherentPullbackMap_conj_compIso {A V W U U' : BigFppfOver B S hS} (w : A ⟶ V)
    (φ : V ⟶ W) (a : W ⟶ U) (b : W ⟶ U') {M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    {N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U').ringCatSheaf).FullSubcategory}
    (f : quasicoherentPullbackObj B S hS a M ⟶ quasicoherentPullbackObj B S hS b N) :
    (quasicoherentPullbackCompIso B S hS w (φ ≫ a) M).inv ≫
        quasicoherentPullbackMap B S hS w ((quasicoherentPullbackCompIso B S hS φ a M).inv ≫
          quasicoherentPullbackMap B S hS φ f ≫ (quasicoherentPullbackCompIso B S hS φ b N).hom) ≫
        (quasicoherentPullbackCompIso B S hS w (φ ≫ b) N).hom =
      quasicoherentPullbackEqToHom B S hS (Category.assoc w φ a).symm M ≫
        (quasicoherentPullbackCompIso B S hS (w ≫ φ) a M).inv ≫
          quasicoherentPullbackMap B S hS (w ≫ φ) f ≫
            (quasicoherentPullbackCompIso B S hS (w ≫ φ) b N).hom ≫
              quasicoherentPullbackEqToHom B S hS (Category.assoc w φ b) N := by
  simp only [quasicoherentPullbackMap_comp, Category.assoc,
    quasicoherentPullbackMap_compIso_hom_comp_compIso_hom]
  refine (quasicoherentPullbackCompIso_inv_comp_map_compIso_inv_assoc B S hS w φ a M _).trans ?_
  exact congrArg (fun t => _ ≫ _ ≫ t)
    ((quasicoherentPullbackCompIso_inv_comp_map_map_assoc B S hS w φ f _).trans
      (congrArg (_ ≫ ·) (Iso.inv_hom_id_assoc _ _)))

/-- Three transports between pullbacks along equal morphisms, returning to the start, cancel. -/
theorem quasicoherentPullbackEqToHom_trans_trans_assoc {V U : BigFppfOver B S hS}
    {k₁ k₂ k₃ : V ⟶ U} (e₁ : k₁ = k₂) (e₂ : k₂ = k₃) (e₃ : k₃ = k₁)
    (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory)
    {Z : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj V).ringCatSheaf).FullSubcategory}
    (h : quasicoherentPullbackObj B S hS k₁ M ⟶ Z) :
    quasicoherentPullbackEqToHom B S hS e₁ M ≫ quasicoherentPullbackEqToHom B S hS e₂ M ≫
        quasicoherentPullbackEqToHom B S hS e₃ M ≫ h = h := by
  subst e₁ e₂
  exact Category.id_comp _

/-- The pullback of `f ≫ e⁻¹`, followed by the pullback of `e`, is the pullback of `f`. -/
theorem quasicoherentPullbackMap_comp_inv_comp_hom {V U : BigFppfOver B S hS} (g : V ⟶ U)
    {M N K : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    (f : M ⟶ N) (e : K ≅ N) {Z : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj V).ringCatSheaf).FullSubcategory}
    (h : quasicoherentPullbackObj B S hS g N ⟶ Z) :
    quasicoherentPullbackMap B S hS g (f ≫ e.inv) ≫ quasicoherentPullbackMap B S hS g e.hom ≫ h =
      quasicoherentPullbackMap B S hS g f ≫ h := by
  rw [quasicoherentPullbackMap_comp_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **The ratio of two comparisons through a common factor is natural.**  Let `Θ : yU^*M ≅ M''`
and `ΘB : c^*N ≅ M''` on `V` both factor through `φ : V ⟶ Z`, as `tA : a^*M ≅ G` and
`tB : b^*N ≅ G` pulled back along `φ` followed by `βφ : φ^*G ≅ M''`, and let `Θ' : yU'^*M ≅ M'''`
on `V'` factor in the same way through `w ≫ φ`, with a third factorization
`c' ≫ y = (w ≫ φ) ≫ b` relating `cmp : y^*N ≅ N'` and `ΘB' : c'^*N' ≅ M'''`.  Then `Θ'` is the
pullback along `w` of the ratio `Θ ≫ ΘB⁻¹`, followed by `cmp` and `ΘB'`. -/
theorem comparison_eq_pullback_ratio {V' V Z YU YT YT' : BigFppfOver B S hS} (w : V' ⟶ V)
    (φ : V ⟶ Z) (a : Z ⟶ YU) (b : Z ⟶ YT) (c' : V' ⟶ YT') (y : YT' ⟶ YT)
    {M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj YU).ringCatSheaf).FullSubcategory}
    {N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj YT).ringCatSheaf).FullSubcategory}
    {N' : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj YT').ringCatSheaf).FullSubcategory}
    {G : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj Z).ringCatSheaf).FullSubcategory}
    {M'' : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj V).ringCatSheaf).FullSubcategory}
    {M''' : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj V').ringCatSheaf).FullSubcategory}
    (tA : quasicoherentPullbackObj B S hS a M ≅ G) (tB : quasicoherentPullbackObj B S hS b N ≅ G)
    (βφ : quasicoherentPullbackObj B S hS φ G ≅ M'')
    (βψ : quasicoherentPullbackObj B S hS (w ≫ φ) G ≅ M''')
    (cmp : quasicoherentPullbackObj B S hS y N ≅ N')
    (ΘB' : quasicoherentPullbackObj B S hS c' N' ≅ M''')
    {yU : V ⟶ YU} {c : V ⟶ YT} {yU' : V' ⟶ YU}
    (Θ : quasicoherentPullbackObj B S hS yU M ≅ M'')
    (ΘB : quasicoherentPullbackObj B S hS c N ≅ M'')
    (Θ' : quasicoherentPullbackObj B S hS yU' M ≅ M''')
    (eA : yU = φ ≫ a) (eB : c = φ ≫ b) (eA' : yU' = (w ≫ φ) ≫ a) (eC : c' ≫ y = (w ≫ φ) ≫ b)
    (hwc : c' ≫ y = w ≫ c) (hwy : w ≫ yU = yU')
    (hΘ : Θ.hom = quasicoherentPullbackEqToHom B S hS eA M ≫
      (quasicoherentPullbackCompIso B S hS φ a M).inv ≫
        quasicoherentPullbackMap B S hS φ tA.hom ≫ βφ.hom)
    (hΘB : ΘB.hom = quasicoherentPullbackEqToHom B S hS eB N ≫
      (quasicoherentPullbackCompIso B S hS φ b N).inv ≫
        quasicoherentPullbackMap B S hS φ tB.hom ≫ βφ.hom)
    (hΘ' : Θ'.hom = quasicoherentPullbackEqToHom B S hS eA' M ≫
      (quasicoherentPullbackCompIso B S hS (w ≫ φ) a M).inv ≫
        quasicoherentPullbackMap B S hS (w ≫ φ) tA.hom ≫ βψ.hom)
    (hΛ : (quasicoherentPullbackCompIso B S hS c' y N).inv ≫
        quasicoherentPullbackMap B S hS c' cmp.hom ≫ ΘB'.hom =
      quasicoherentPullbackEqToHom B S hS eC N ≫
        (quasicoherentPullbackCompIso B S hS (w ≫ φ) b N).inv ≫
          quasicoherentPullbackMap B S hS (w ≫ φ) tB.hom ≫ βψ.hom) :
    quasicoherentPullbackEqToHom B S hS hwy M ≫ Θ'.hom =
      (quasicoherentPullbackCompIso B S hS w yU M).inv ≫
        quasicoherentPullbackMap B S hS w Θ.hom ≫ quasicoherentPullbackMap B S hS w ΘB.inv ≫
          (quasicoherentPullbackCompIso B S hS w c N).hom ≫
            quasicoherentPullbackEqToHom B S hS hwc.symm N ≫
              (quasicoherentPullbackCompIso B S hS c' y N).inv ≫
                quasicoherentPullbackMap B S hS c' cmp.hom ≫ ΘB'.hom := by
  subst eA eB hwy
  have hR : Θ.hom ≫ ΘB.inv = (quasicoherentPullbackCompIso B S hS φ a M).inv ≫
      quasicoherentPullbackMap B S hS φ (tA.hom ≫ tB.inv) ≫
        (quasicoherentPullbackCompIso B S hS φ b N).hom := by
    refine (Iso.comp_inv_eq ΘB).2 ?_
    simp only [hΘ, hΘB, quasicoherentPullbackEqToHom_rfl, Category.id_comp, Category.assoc,
      Iso.hom_inv_id_assoc, quasicoherentPullbackMap_comp]
    exact congrArg (fun t => _ ≫ _ ≫ t)
      (quasicoherentPullbackMap_inv_comp_map_hom_assoc B S hS φ tB βφ.hom).symm
  simp only [quasicoherentPullbackEqToHom_rfl, Category.id_comp, hΛ, hΘ',
    quasicoherentPullbackMap_comp_comp, hR]
  refine Eq.trans ?_ (quasicoherentPullbackMap_conj_compIso_assoc B S hS w φ a b
    (tA.hom ≫ tB.inv) _).symm
  refine congrArg (fun t => _ ≫ _ ≫ t) ?_
  refine Eq.trans ?_ (congrArg (fun t => _ ≫ _ ≫ t)
    (quasicoherentPullbackEqToHom_trans_trans_assoc B S hS _ _ _ N _)).symm
  refine Eq.trans ?_ (congrArg (fun t => _ ≫ t) (Iso.hom_inv_id_assoc _ _)).symm
  exact (quasicoherentPullbackMap_comp_inv_comp_hom B S hS _ _ _ _).symm

end QuasicoherentCoherence

/-! ### Coherence of the composition comparisons of inverse images on algebraic spaces -/

section SpaceCoherence

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Two transports compose to a transport, followed by a morphism. -/
theorem pullbackTransport_comp_pullbackTransport_assoc {T X : AlgebraicSpaces B S hS}
    (M : Modules.{u, u} B S hS X.1 X.2) {f g k : T ⟶ X} (h₁ : f = g) (h₂ : g = k)
    {Z : Modules.{u, u} B S hS T.1 T.2} (q : (modulePullback B S hS k).obj M ⟶ Z) :
    pullbackTransport M h₁ ≫ pullbackTransport M h₂ ≫ q =
      pullbackTransport M (h₁.trans h₂) ≫ q := by
  subst h₁ h₂
  rfl

/-- Transport along `rfl` is the identity. -/
private theorem pullbackTransport_rfl {T X : AlgebraicSpaces B S hS}
    (M : Modules.{u, u} B S hS X.1 X.2) (f : T ⟶ X) : pullbackTransport M (rfl : f = f) = 𝟙 _ :=
  rfl

/-- A transport, the inverse comparison, the comparison and the inverse transport cancel. -/
theorem pullbackTransport_symm_comp_compInv_comp_compHom_comp_pullbackTransport
    {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Modules.{u, u} B S hS Z.1 Z.2)
    {q : X ⟶ Z} (hq : f ≫ g = q) :
    pullbackTransport M hq.symm ≫ modulePullbackCompInv B S hS f g M ≫
        modulePullbackCompHom B S hS f g M ≫ pullbackTransport M hq = 𝟙 _ := by
  subst hq
  rw [pullbackTransport_rfl, Category.id_comp, Category.comp_id,
    modulePullbackCompInv_comp_compHom]

/-- **The comparison `f^*g^*M ⟶ (f ≫ g)^*M` of Stacks 03LU is natural in `M`.** -/
@[reassoc]
theorem modulePullbackCompHom_naturality {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (g : Y ⟶ Z) {M N : Modules.{u, u} B S hS Z.1 Z.2} (φ : M ⟶ N) :
    (modulePullback B S hS f).map ((modulePullback B S hS g).map φ) ≫
        modulePullbackCompHom B S hS f g N =
      modulePullbackCompHom B S hS f g M ≫ (modulePullback B S hS (f ≫ g)).map φ :=
  (modulePullbackCompIso B S hS f g).hom.naturality φ

/-- The inverse comparison `(f ≫ g)^*M ⟶ f^*g^*M` of Stacks 03LU is natural in `M`. -/
@[reassoc]
theorem modulePullbackCompInv_naturality {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (g : Y ⟶ Z) {M N : Modules.{u, u} B S hS Z.1 Z.2} (φ : M ⟶ N) :
    (modulePullback B S hS (f ≫ g)).map φ ≫ modulePullbackCompInv B S hS f g N =
      modulePullbackCompInv B S hS f g M ≫
        (modulePullback B S hS f).map ((modulePullback B S hS g).map φ) :=
  (modulePullbackCompIso B S hS f g).inv.naturality φ

/-- The inverse comparison followed by the comparison, followed by a morphism. -/
theorem modulePullbackCompInv_comp_compHom_assoc {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (g : Y ⟶ Z) (M : Modules.{u, u} B S hS Z.1 Z.2) {K : Modules.{u, u} B S hS X.1 X.2}
    (q : (modulePullback B S hS (f ≫ g)).obj M ⟶ K) :
    modulePullbackCompInv B S hS f g M ≫ modulePullbackCompHom B S hS f g M ≫ q = q := by
  rw [← Category.assoc, modulePullbackCompInv_comp_compHom, Category.id_comp]

/-- The inverse image of the inverse comparison followed by that of the comparison. -/
theorem modulePullback_map_compInv_comp_map_compHom_assoc {W X Y Z : AlgebraicSpaces B S hS}
    (e : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z) (M : Modules.{u, u} B S hS Z.1 Z.2)
    {K : Modules.{u, u} B S hS W.1 W.2}
    (q : (modulePullback B S hS e).obj ((modulePullback B S hS (f ≫ g)).obj M) ⟶ K) :
    (modulePullback B S hS e).map (modulePullbackCompInv B S hS f g M) ≫
        (modulePullback B S hS e).map (modulePullbackCompHom B S hS f g M) ≫ q = q := by
  rw [← Functor.map_comp_assoc, modulePullbackCompInv_comp_compHom,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- The associativity of Stacks 03LU, with the transport to the other bracketing. -/
@[reassoc]
theorem modulePullbackCompHom_comp_compHom {V W W' X : AlgebraicSpaces B S hS} (f : V ⟶ W)
    (g : W ⟶ W') (k : W' ⟶ X) (M : Modules.{u, u} B S hS X.1 X.2) :
    modulePullbackCompHom B S hS f g ((modulePullback B S hS k).obj M) ≫
        modulePullbackCompHom B S hS (f ≫ g) k M =
      (modulePullback B S hS f).map (modulePullbackCompHom B S hS g k M) ≫
        modulePullbackCompHom B S hS f (g ≫ k) M ≫
          pullbackTransport M (Category.assoc f g k).symm := by
  have h := modulePullbackCompHom_assoc_transport B S hS f g k M rfl (Category.assoc f g k).symm
  rwa [pullbackTransport_rfl, Category.comp_id] at h

/-- The associativity of Stacks 03LU, read from the other bracketing. -/
@[reassoc]
theorem modulePullback_map_compHom_comp_compHom {V W W' X : AlgebraicSpaces B S hS} (f : V ⟶ W)
    (g : W ⟶ W') (k : W' ⟶ X) (M : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullback B S hS f).map (modulePullbackCompHom B S hS g k M) ≫
        modulePullbackCompHom B S hS f (g ≫ k) M =
      modulePullbackCompHom B S hS f g ((modulePullback B S hS k).obj M) ≫
        modulePullbackCompHom B S hS (f ≫ g) k M ≫ pullbackTransport M (Category.assoc f g k) := by
  have h := modulePullbackCompHom_assoc_transport B S hS f g k M (Category.assoc f g k) rfl
  rw [pullbackTransport_rfl, Category.comp_id] at h
  exact h.symm

/-- **The chain of comparisons and transports between two iterated inverse images along two
factorizations of the same morphism is the canonical one.**  For `A' ≫ ry = rw ≫ A`,
`A ≫ hW = ryU ≫ ab` and `rw ≫ ryU = q`, the composite of comparisons of Stacks 03LU and
transports `A'^*(ry ≫ hW)^*𝒯 ⟶ q^*ab^*𝒯` through `rw^*A^*hW^*𝒯` is the comparison followed by
the transport along `A' ≫ ry ≫ hW = q ≫ ab`. -/
theorem modulePullbackCompInv_chain_eq {V'' W'' W₀ V₀ U₀ X : AlgebraicSpaces B S hS}
    (A' : V'' ⟶ W'') (ry : W'' ⟶ W₀) (hW : W₀ ⟶ X) (A : V₀ ⟶ W₀) (rw : V'' ⟶ V₀)
    (ryU : V₀ ⟶ U₀) (ab : U₀ ⟶ X) {q₁ q₂ : V'' ⟶ W₀} (q : V'' ⟶ U₀)
    (T : Modules.{u, u} B S hS X.1 X.2) (p₁ : A' ≫ ry = q₁) (p₂ : q₁ = q₂) (p₃ : q₂ = rw ≫ A)
    (hY : A ≫ hW = ryU ≫ ab) (pq : rw ≫ ryU = q) (hY' : A' ≫ ry ≫ hW = q ≫ ab) :
    (modulePullback B S hS A').map (modulePullbackCompInv B S hS ry hW T) ≫
        modulePullbackCompHom B S hS A' ry ((modulePullback B S hS hW).obj T) ≫
          pullbackTransport ((modulePullback B S hS hW).obj T) p₁ ≫
          pullbackTransport ((modulePullback B S hS hW).obj T) p₂ ≫
          pullbackTransport ((modulePullback B S hS hW).obj T) p₃ ≫
            modulePullbackCompInv B S hS rw A ((modulePullback B S hS hW).obj T) ≫
              (modulePullback B S hS rw).map (modulePullbackCompHom B S hS A hW T) ≫
              (modulePullback B S hS rw).map (pullbackTransport T hY) ≫
              (modulePullback B S hS rw).map (modulePullbackCompInv B S hS ryU ab T) ≫
                modulePullbackCompHom B S hS rw ryU ((modulePullback B S hS ab).obj T) ≫
                  pullbackTransport ((modulePullback B S hS ab).obj T) pq =
      modulePullbackCompHom B S hS A' (ry ≫ hW) T ≫ pullbackTransport T hY' ≫
        modulePullbackCompInv B S hS q ab T := by
  subst pq
  rw [pullbackTransport_comp_pullbackTransport_assoc,
    pullbackTransport_comp_pullbackTransport_assoc,
    pullbackTransport_rfl, Category.comp_id]
  refine (Iso.cancel_iso_hom_right _ _ ((modulePullbackCompIso B S hS (rw ≫ ryU) ab).app T)).1 ?_
  change _ ≫ modulePullbackCompHom B S hS (rw ≫ ryU) ab T =
    _ ≫ modulePullbackCompHom B S hS (rw ≫ ryU) ab T
  simp only [Category.assoc, modulePullbackCompInv_comp_compHom, Category.comp_id]
  rw [modulePullbackCompHom_comp_compHom, modulePullback_map_compInv_comp_map_compHom_assoc,
    modulePullback_map_pullbackTransport_comp_compHom_assoc,
    modulePullback_map_compHom_comp_compHom_assoc, modulePullbackCompInv_comp_compHom_assoc,
    pullbackTransport_comp_compHom_assoc, modulePullbackCompHom_comp_compHom_assoc,
    modulePullback_map_compInv_comp_map_compHom_assoc]
  simp only [pullbackTransport_comp_pullbackTransport_assoc]
  exact congrArg (_ ≫ ·) (pullbackTransport_comp T _ _ hY')

end SpaceCoherence

/-! ### Abstract shapes of the chases, at variables -/

section Abstract

variable {D : Type*} [Category D]

/-- A composite of two morphisms, between two endomorphisms equal to identities. -/
theorem eq_id_comp_comp_comp_id {a b c : D} (x : a ⟶ b) (y : b ⟶ c) (i : a ⟶ a) (j : c ⟶ c)
    (hi : i = 𝟙 a) (hj : j = 𝟙 c) : x ≫ y = i ≫ x ≫ y ≫ j := by
  subst hi hj
  simp

/-- Solving an equation `z₁ ≫ z₂ ≫ z₃ = x ≫ y ≫ β` for `x ≫ y`. -/
theorem comp_eq_comp_inv_of_eq {a b c d e f : D} (x : a ⟶ b) (y : b ⟶ c) (z₁ : a ⟶ d)
    (z₂ : d ⟶ e) (z₃ : e ⟶ f) (β : c ≅ f) (H : z₁ ≫ z₂ ≫ z₃ = x ≫ y ≫ β.hom) :
    x ≫ y = z₁ ≫ z₂ ≫ z₃ ≫ β.inv := by
  rw [← Category.assoc z₂, ← Category.assoc z₁, H]
  simp

/-- Solving an equation `P₁ ≫ P₂ ≫ P₃ = a₁ ≫ a₂ ≫ Z₁ ≫ Z₂ ≫ b` for `Z₁ ≫ Z₂`, given left
inverses of `a₁ ≫ a₂` and right inverses of `b`. -/
theorem comp_eq_inv_comp_of_eq {a b c d e f g h : D} (P₁ : a ⟶ b) (P₂ : b ⟶ c) (P₃ : c ⟶ h)
    (a₁ : a ⟶ d) (a₂ : d ⟶ e) (Z₁ : e ⟶ f) (Z₂ : f ⟶ g) (b₀ : g ⟶ h) (j₂ : e ⟶ d) (j₁ : d ⟶ a)
    (b' : h ⟶ g) (ha : j₂ ≫ j₁ ≫ a₁ ≫ a₂ = 𝟙 e) (hb : b₀ ≫ b' = 𝟙 g)
    (H : P₁ ≫ P₂ ≫ P₃ = a₁ ≫ a₂ ≫ Z₁ ≫ Z₂ ≫ b₀) :
    Z₁ ≫ Z₂ = j₂ ≫ j₁ ≫ P₁ ≫ P₂ ≫ P₃ ≫ b' := by
  rw [← Category.assoc P₂, ← Category.assoc P₁, H]
  simp only [Category.assoc, hb, Category.comp_id, reassoc_of% ha]

/-- The images of two composable morphisms under a functor to a full subcategory, read on
underlying morphisms. -/
theorem functor_map_hom_comp_map_hom {C : Type*} [Category C] {Q : ObjectProperty D}
    (F : C ⥤ Q.FullSubcategory) {a b c : C} (f : a ⟶ b) (g : b ⟶ c) :
    (F.map f).hom ≫ (F.map g).hom = (F.map (f ≫ g)).hom := by
  rw [F.map_comp, ObjectProperty.FullSubcategory.comp_hom]

/-- The image of an identity, read on underlying morphisms. -/
theorem functor_map_id_hom {C : Type*} [Category C] {Q : ObjectProperty D}
    (F : C ⥤ Q.FullSubcategory) (a : C) : (F.map (𝟙 a)).hom = 𝟙 _ := by
  rw [F.map_id]
  rfl

/-- The image of the inverse of an isomorphism followed by the image of the isomorphism, read on
underlying morphisms. -/
theorem functor_map_inv_hom_comp_map_hom_hom {C : Type*} [Category C] {Q : ObjectProperty D}
    (F : C ⥤ Q.FullSubcategory) {a b : C} (e : a ≅ b) :
    (F.map e.inv).hom ≫ (F.map e.hom).hom = 𝟙 _ := by
  rw [functor_map_hom_comp_map_hom, e.inv_hom_id, F.map_id]
  rfl

/-- The abstract shape of `AlgebraicGeometry.Space.modulePullback_map_reading_comp`. -/
theorem reading_comp_chase {a b c d e f g h k : D} (F₀ : a ⟶ b) (P : b ⟶ c) (Q : c ⟶ d)
    (cH₁ : b ⟶ e) (tr₁ : e ⟶ f) (ρ : f ⟶ g) (Ei : g ⟶ d) (cH₂ : a ⟶ h) (G : h ⟶ e)
    (tr₂ : h ⟶ k) (G' : k ⟶ f) (L1 : P ≫ Q = cH₁ ≫ tr₁ ≫ ρ ≫ Ei) (N1 : F₀ ≫ cH₁ = cH₂ ≫ G)
    (N2 : G ≫ tr₁ = tr₂ ≫ G') :
    F₀ ≫ P ≫ Q = cH₂ ≫ tr₂ ≫ G' ≫ ρ ≫ Ei := by
  rw [L1, reassoc_of% N1, reassoc_of% N2]

/-- A morphism transported along a transport and its inverse. -/
theorem comp_eq_of_naturality {a b c d e f : D} (G₁ : a ⟶ b) (R₁ : b ⟶ f) (t₁ : a ⟶ c)
    (G₂ : c ⟶ d) (t₂ : b ⟶ d) (t₃ : d ⟶ b) (R₂ : d ⟶ e) (q : e ⟶ f)
    (N₁ : t₁ ≫ G₂ = G₁ ≫ t₂) (N₂ : t₃ ≫ R₁ = R₂ ≫ q) (hinv : t₂ ≫ t₃ = 𝟙 b) :
    G₁ ≫ R₁ = t₁ ≫ G₂ ≫ R₂ ≫ q := by
  rw [← N₂, reassoc_of% N₁, reassoc_of% hinv]

/-- The first two steps of the abstract shape of
`AlgebraicGeometry.Space.modulePullback_map_reading_eq`. -/
theorem reading_chase_ab {X1 X2 X3 X4 A1 A2 A3 A4 B1 B2 B3 : D}
    (m1 : X1 ⟶ X2) (m2 : X2 ⟶ X3) (m3 : X3 ⟶ X4)
    (a1 : X1 ⟶ A1) (a2 : A1 ⟶ A2) (a3 : A2 ⟶ A3) (a4 : A3 ⟶ A4) (a5 : A4 ⟶ X4)
    (b1 : A2 ⟶ B1) (b2 : B1 ⟶ B2) (b3 : B2 ⟶ B3) (b4 : B3 ⟶ A4)
    (hA : m1 ≫ m2 ≫ m3 = a1 ≫ a2 ≫ a3 ≫ a4 ≫ a5) (hB : a3 ≫ a4 = b1 ≫ b2 ≫ b3 ≫ b4) :
    m1 ≫ m2 ≫ m3 = a1 ≫ a2 ≫ b1 ≫ b2 ≫ b3 ≫ b4 ≫ a5 := by
  rw [hA, reassoc_of% hB]

/-- The middle steps of the abstract shape of
`AlgebraicGeometry.Space.modulePullback_map_reading_eq`. -/
theorem reading_chase_cde {B1 B2 B3 C1 C2 C3 C4 C5 D1 D2 D3 D4 D5 E1 : D}
    (x : B1 ⟶ B2) (y : B2 ⟶ B3)
    (c1 : B1 ⟶ C1) (c2 : C1 ⟶ C2) (c3 : C2 ⟶ C3) (c4 : C3 ⟶ C4) (c5 : C4 ⟶ C5) (c6 : C5 ⟶ B3)
    (d1 : C2 ⟶ D1) (d2 : D1 ⟶ D2) (d3 : D2 ⟶ D3) (d4 : D3 ⟶ D4) (d5 : D4 ⟶ D5) (d6 : D5 ⟶ C4)
    (e1 : D5 ⟶ E1) (e2 : E1 ⟶ C5)
    (hC : x ≫ y = c1 ≫ c2 ≫ c3 ≫ c4 ≫ c5 ≫ c6)
    (hD : c3 ≫ c4 = d1 ≫ d2 ≫ d3 ≫ d4 ≫ d5 ≫ d6) (hE : d6 ≫ c5 = e1 ≫ e2) :
    x ≫ y = c1 ≫ c2 ≫ d1 ≫ d2 ≫ d3 ≫ d4 ≫ d5 ≫ e1 ≫ e2 ≫ c6 := by
  rw [hC, reassoc_of% hD, reassoc_of% hE]

/-- The last step of the abstract shape of
`AlgebraicGeometry.Space.modulePullback_map_reading_eq`. -/
theorem reading_chase_f {B1 B3 C1 C2 C5 D1 D2 D3 D4 D5 E1 F1 F2 F3 F4 : D} (L : B1 ⟶ B3)
    (c1 : B1 ⟶ C1) (c2 : C1 ⟶ C2) (c6 : C5 ⟶ B3)
    (d1 : C2 ⟶ D1) (d2 : D1 ⟶ D2) (d3 : D2 ⟶ D3) (d4 : D3 ⟶ D4) (d5 : D4 ⟶ D5)
    (e1 : D5 ⟶ E1) (e2 : E1 ⟶ C5)
    (f1 : D3 ⟶ F1) (f2 : F1 ⟶ F2) (f3 : F2 ⟶ F3) (f4 : F3 ⟶ F4) (f5 : F4 ⟶ E1)
    (hL : L = c1 ≫ c2 ≫ d1 ≫ d2 ≫ d3 ≫ d4 ≫ d5 ≫ e1 ≫ e2 ≫ c6)
    (hF : d4 ≫ d5 ≫ e1 = f1 ≫ f2 ≫ f3 ≫ f4 ≫ f5) :
    L = c1 ≫ c2 ≫ d1 ≫ d2 ≫ d3 ≫ f1 ≫ f2 ≫ f3 ≫ f4 ≫ f5 ≫ e2 ≫ c6 := by
  rw [hL, reassoc_of% hF]

/-- The assembly of the abstract shape of
`AlgebraicGeometry.Space.modulePullback_map_reading_eq`. -/
theorem reading_chase {X0 X1 X2 X3 X4 A1 A2 A4 B1 B2 B3 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 : D}
    (m0 : X0 ⟶ X1) (m1 : X1 ⟶ X2) (m2 : X2 ⟶ X3) (m3 : X3 ⟶ X4)
    (a1 : X1 ⟶ A1) (a2 : A1 ⟶ A2) (a5 : A4 ⟶ X4)
    (b1 : A2 ⟶ B1) (b2 : B1 ⟶ B2) (b3 : B2 ⟶ B3) (b4 : B3 ⟶ A4)
    (k1 : B1 ⟶ K1) (k2 : K1 ⟶ K2) (k3 : K2 ⟶ K3) (k4 : K3 ⟶ K4) (k5 : K4 ⟶ K5) (k6 : K5 ⟶ K6)
    (k7 : K6 ⟶ K7) (k8 : K7 ⟶ K8) (k9 : K8 ⟶ K9) (k10 : K9 ⟶ K10) (k11 : K10 ⟶ K11)
    (k12 : K11 ⟶ B3)
    (hAB : m1 ≫ m2 ≫ m3 = a1 ≫ a2 ≫ b1 ≫ b2 ≫ b3 ≫ b4 ≫ a5)
    (hK : b2 ≫ b3 = k1 ≫ k2 ≫ k3 ≫ k4 ≫ k5 ≫ k6 ≫ k7 ≫ k8 ≫ k9 ≫ k10 ≫ k11 ≫ k12) :
    m0 ≫ m1 ≫ m2 ≫ m3 =
      (m0 ≫ a1 ≫ a2 ≫ b1 ≫ k1 ≫ k2 ≫ k3 ≫ k4 ≫ k5 ≫ k6 ≫ k7) ≫ k8 ≫ k9 ≫ k10 ≫ k11 ≫ k12 ≫
        b4 ≫ a5 := by
  rw [hAB, reassoc_of% hK]
  simp only [Category.assoc]

/-- The inverse image along a functor of an equation of a composite of two morphisms with a
composite of six. -/
theorem functor_map_comp_eq_of_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {a b c d₁ d₂ d₃ d₄ d₅ : C} (x₁ : a ⟶ b) (x₂ : b ⟶ c) (y₁ : a ⟶ d₁) (y₂ : d₁ ⟶ d₂)
    (y₃ : d₂ ⟶ d₃) (y₄ : d₃ ⟶ d₄) (y₅ : d₄ ⟶ d₅) (y₆ : d₅ ⟶ c)
    (h : x₁ ≫ x₂ = y₁ ≫ y₂ ≫ y₃ ≫ y₄ ≫ y₅ ≫ y₆) :
    F.map x₁ ≫ F.map x₂ = F.map y₁ ≫ F.map y₂ ≫ F.map y₃ ≫ F.map y₄ ≫ F.map y₅ ≫ F.map y₆ := by
  rw [← F.map_comp, h]
  simp only [F.map_comp]

/-- A chain of seven morphisms in the image of a functor to a full subcategory, read on
underlying morphisms, is the image of their composite. -/
theorem functor_map_hom_chain_eq {C D : Type*} [Category C] [Category D] {Q : ObjectProperty D}
    (F : C ⥤ Q.FullSubcategory) {a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ m : C} (f₁ : a₀ ⟶ a₁) (f₂ : a₁ ⟶ a₂)
    (f₃ : a₂ ⟶ a₃) (f₄ : a₃ ⟶ a₄) (f₅ : a₄ ⟶ a₅) (f₆ : a₅ ⟶ a₆) (f₇ : a₆ ⟶ a₇)
    (f₂a : a₁ ⟶ m) (f₂b : m ⟶ a₂) (i : a₀ ⟶ a₀) (g : a₀ ⟶ a₇) (h₂ : f₂ = f₂a ≫ f₂b)
    (hi : i = 𝟙 a₀) (H : i ≫ g = f₁ ≫ f₂a ≫ f₂b ≫ f₃ ≫ f₄ ≫ f₅ ≫ f₆ ≫ f₇) :
    (F.map f₁).hom ≫ (F.map f₂).hom ≫ (F.map f₃).hom ≫ (F.map f₄).hom ≫ (F.map f₅).hom ≫
      (F.map f₆).hom ≫ (F.map f₇).hom = (F.map g).hom := by
  subst h₂ hi
  rw [Category.id_comp] at H
  rw [H]
  simp only [F.map_comp, ObjectProperty.FullSubcategory.comp_hom, Category.assoc]

/-- The abstract shape of
`AlgebraicGeometry.Space.attachedModuleIsoPullback_spec_represented`. -/
theorem attached_chase {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {P Q R S' T' : C} {Y1 Y2 Z1 G0 G1 G2 G3 G4 H1 H2 H3 H4 : D}
    (k0 : P ⟶ Q) (k1 : Q ⟶ R) (k2 : R ⟶ S') (k3 : S' ⟶ T')
    (r1 : F.obj T' ⟶ Y1) (r2 : Y1 ⟶ Y2) (ρc : F.obj S' ⟶ Z1) (ecm : Z1 ⟶ Y1)
    (L : F.obj P ⟶ G2) (cH : F.obj P ⟶ G0) (trY : G0 ⟶ G1) (cI : G1 ⟶ G2) (f3 : G2 ⟶ G3)
    (f4 : G3 ⟶ G4) (E1 : G4 ⟶ H1) (E2 : H1 ⟶ H2) (E3 : H2 ⟶ H3) (E4 : H3 ⟶ H4) (E5 : H4 ⟶ Z1)
    (eΘ : G4 ⟶ Y2) (hN : F.map k3 ≫ r1 = ρc ≫ ecm)
    (hG1 : F.map k0 ≫ F.map k1 ≫ F.map k2 ≫ ρc = L ≫ f3 ≫ f4 ≫ E1 ≫ E2 ≫ E3 ≫ E4 ≫ E5)
    (hCanon : L = cH ≫ trY ≫ cI)
    (hEm : E1 ≫ E2 ≫ E3 ≫ E4 ≫ E5 ≫ ecm ≫ r2 = eΘ) :
    F.map (k0 ≫ k1 ≫ k2 ≫ k3) ≫ r1 ≫ r2 = (cH ≫ trY ≫ cI) ≫ f3 ≫ f4 ≫ eΘ := by
  rw [hCanon] at hG1
  simp only [F.map_comp, Category.assoc]
  rw [reassoc_of% hN, reassoc_of% hG1]
  simp only [hEm]

/-- An equation transported along heterogeneous equalities of its two sides. -/
theorem eq_of_heq_of_heq.{w} {α β : Sort w} {a b : α} {a' b' : β} (ha : HEq a a') (hb : HEq b b')
    (h : a = b) : a' = b' :=
  eq_of_heq (ha.symm.trans ((heq_of_eq h).trans hb))

/-- Two equations `L₂ = R₂` and `L₃ = R₃`, glued by heterogeneous equalities `Lg ≍ L₂`,
`R₂ ≍ R₃` and `Rg ≍ L₃`, give `Lg = Rg`. -/
theorem eq_of_eq_of_eq_of_heq.{w} {α β γ : Sort w} {L₂ R₂ : α} {Lg Rg : β} {L₃ R₃ : γ}
    (h₂ : L₂ = R₂) (h₃ : L₃ = R₃) (hL : HEq Lg L₂) (hR : HEq R₂ R₃) (hR' : HEq Rg L₃) :
    Lg = Rg :=
  eq_of_heq (hL.trans ((heq_of_eq h₂).trans (hR.trans ((heq_of_eq h₃).symm.trans hR'.symm))))

/-- Cancelling two morphisms with left inverses on the right of an equation. -/
theorem eq_of_comp_comp_eq_comp_comp {C : Type*} [Category C] {X Y Z W : C} {a b : X ⟶ Y}
    (r₁ : Y ⟶ Z) (r₂ : Z ⟶ W) (s₁ : Z ⟶ Y) (s₂ : W ⟶ Z) (h₁ : r₁ ≫ s₁ = 𝟙 _)
    (h₂ : r₂ ≫ s₂ = 𝟙 _) (h : a ≫ r₁ ≫ r₂ = b ≫ r₁ ≫ r₂) : a = b := by
  simpa only [Category.assoc, reassoc_of% h₂, h₁, Category.comp_id] using
    congrArg (· ≫ s₂ ≫ s₁) h

/-- Reassociating the right-hand side `(x ≫ y ≫ z) ≫ t` of an equation. -/
theorem eq_comp_comp_comp_of_eq_comp {C : Type*} [Category C] {X Y Z W V : C} (a : X ⟶ V)
    (x : X ⟶ Y) (y : Y ⟶ Z) (z : Z ⟶ W) (t : W ⟶ V) (h : a = (x ≫ y ≫ z) ≫ t) :
    a = x ≫ y ≫ z ≫ t := by
  simpa only [Category.assoc] using h

/-- The underlying morphisms of an equation of isomorphisms
`F(E₀) ≪≫ ρ ≪≫ ι(G(θB)) = π ≪≫ K ≪≫ R ≪≫ ι(G(θ))`, with the first factor `π` written out as
`cH ≫ tr ≫ cI`. -/
theorem map_hom_comp_eq_of_iso_eq {C C' D : Type*} [Category C] [Category C'] [Category D]
    {Q : ObjectProperty D} (F : C ⥤ D) (G : C' ⥤ Q.FullSubcategory) {a b : C} {p q r : C'}
    {d₀ d₁ d₃ d₄ : D} (E₀ : a ≅ b) (ρ : F.obj b ≅ (G.obj p).obj) (θB : p ≅ r)
    (π : F.obj a ≅ d₃) (K : d₃ ≅ d₄) (R : d₄ ≅ (G.obj q).obj) (θ : q ≅ r)
    (cH : F.obj a ⟶ d₀) (tr : d₀ ⟶ d₁) (cI : d₁ ⟶ d₃) (hπ : π.hom = cH ≫ tr ≫ cI)
    (H : F.mapIso E₀ ≪≫ ρ ≪≫ (ObjectProperty.ι _).mapIso (G.mapIso θB) =
      π ≪≫ K ≪≫ R ≪≫ (ObjectProperty.ι _).mapIso (G.mapIso θ)) :
    F.map E₀.hom ≫ ρ.hom ≫ (G.map θB.hom).hom =
      cH ≫ tr ≫ cI ≫ K.hom ≫ R.hom ≫ (G.map θ.hom).hom := by
  simpa only [Iso.trans_hom, Functor.mapIso_hom, ObjectProperty.ι_map, hπ, Category.assoc] using
    congrArg Iso.hom H

end Abstract

/-! ### Readings of an identification `h^*𝒯 ≅ N^a` along morphisms of schemes -/

section Readings

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The identification `g^*(M^a) ≅ (g^*M)^a` composes**, read with the inverse contraction:
the inverse image along `h` of the identification along `g`, followed by the identification
along `h`, is the comparison of Stacks 03LU, the transport to the represented composite, the
identification along `h ≫ g` and the module attached to the inverse contraction of the
pullbacks. -/
theorem modulePullback_map_modulePullbackRepresentedQuasicoherentIso_hom_comp
    {Z' Z W : BigFppfOver B S hS} (h : Z' ⟶ Z) (g : Z ⟶ W)
    (N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj W).ringCatSheaf).FullSubcategory) :
    (modulePullback B S hS (representedSpaceMap B S hS h)).map
        (modulePullbackRepresentedQuasicoherentIso B S hS g N).hom ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS h
        (quasicoherentPullbackObj B S hS g N)).hom =
    modulePullbackCompHom B S hS (representedSpaceMap B S hS h) (representedSpaceMap B S hS g)
        ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj N).obj ≫
      pullbackTransport _ (algebraicSpacesComp_representedSpaceMap B S hS h g) ≫
        (modulePullbackRepresentedQuasicoherentIso B S hS (h ≫ g) N).hom ≫
          ((representedQuasicoherentSchemeEquivalence B S hS Z').functor.map
            (quasicoherentPullbackCompIso B S hS h g N).inv).hom :=
  comp_eq_comp_inv_of_eq _ _ _ _ _ ((ObjectProperty.ι _).mapIso
    ((representedQuasicoherentSchemeEquivalence B S hS Z').functor.mapIso
      (quasicoherentPullbackCompIso B S hS h g N)))
    (compHom_comp_modulePullbackRepresentedQuasicoherentIso_hom B S hS h g N)

variable {X : AlgebraicSpaces B S hS} (T : Modules.{u, u} B S hS X.1 X.2)

/-- **The reading of a morphism `h^*𝒯 ⟶ N^a` along a composite** `h ≫ g` of morphisms of
schemes: its inverse image along `g`, read through `g^*(N^a) ≅ (g^*N)^a`, then pulled back along
`h` and read again, is the comparison of Stacks 03LU, the transport to the represented composite,
the reading along `h ≫ g` and the module attached to the inverse contraction of the pullbacks. -/
theorem modulePullback_map_reading_comp {Z' Z W : BigFppfOver B S hS} (h : Z' ⟶ Z) (g : Z ⟶ W)
    (hW : (⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ : AlgebraicSpaces B S hS) ⟶ X)
    {N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj W).ringCatSheaf).FullSubcategory}
    (E₀ : (modulePullback B S hS hW).obj T ⟶
      ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj N).obj) :
    (modulePullback B S hS (representedSpaceMap B S hS h)).map
        ((modulePullback B S hS (representedSpaceMap B S hS g)).map E₀) ≫
      (modulePullback B S hS (representedSpaceMap B S hS h)).map
        (modulePullbackRepresentedQuasicoherentIso B S hS g N).hom ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS h
        (quasicoherentPullbackObj B S hS g N)).hom =
    modulePullbackCompHom B S hS (representedSpaceMap B S hS h) (representedSpaceMap B S hS g)
        ((modulePullback B S hS hW).obj T) ≫
      pullbackTransport _ (algebraicSpacesComp_representedSpaceMap B S hS h g) ≫
        (modulePullback B S hS (representedSpaceMap B S hS (h ≫ g))).map E₀ ≫
        (modulePullbackRepresentedQuasicoherentIso B S hS (h ≫ g) N).hom ≫
          ((representedQuasicoherentSchemeEquivalence B S hS Z').functor.map
            (quasicoherentPullbackCompIso B S hS h g N).inv).hom := by
  have L1 := modulePullback_map_modulePullbackRepresentedQuasicoherentIso_hom_comp h g N
  have N1 := modulePullbackCompHom_naturality (representedSpaceMap B S hS h)
    (representedSpaceMap B S hS g) E₀
  have N2 := pullbackTransport_naturality E₀ (algebraicSpacesComp_representedSpaceMap B S hS h g)
  exact reading_comp_chase _ _ _ _ _ _ _ _ _ _ _ L1 N1 N2

/-- `AlgebraicGeometry.Space.modulePullback_map_reading_comp`, solved for the reading along the
composite. -/
theorem reading_comp_eq {Z' Z W : BigFppfOver B S hS} (h : Z' ⟶ Z) (g : Z ⟶ W)
    (hW : (⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ : AlgebraicSpaces B S hS) ⟶ X)
    {N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj W).ringCatSheaf).FullSubcategory}
    (E₀ : (modulePullback B S hS hW).obj T ⟶
      ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj N).obj) :
    (modulePullback B S hS (representedSpaceMap B S hS (h ≫ g))).map E₀ ≫
        (modulePullbackRepresentedQuasicoherentIso B S hS (h ≫ g) N).hom =
      pullbackTransport _ (algebraicSpacesComp_representedSpaceMap B S hS h g).symm ≫
        modulePullbackCompInv B S hS (representedSpaceMap B S hS h) (representedSpaceMap B S hS g)
          ((modulePullback B S hS hW).obj T) ≫
        (modulePullback B S hS (representedSpaceMap B S hS h)).map
          ((modulePullback B S hS (representedSpaceMap B S hS g)).map E₀) ≫
        (modulePullback B S hS (representedSpaceMap B S hS h)).map
          (modulePullbackRepresentedQuasicoherentIso B S hS g N).hom ≫
          (modulePullbackRepresentedQuasicoherentIso B S hS h
            (quasicoherentPullbackObj B S hS g N)).hom ≫
            ((representedQuasicoherentSchemeEquivalence B S hS Z').functor.map
              (quasicoherentPullbackCompIso B S hS h g N).hom).hom := by
  have H := modulePullback_map_reading_comp T h g hW E₀
  have ha := pullbackTransport_symm_comp_compInv_comp_compHom_comp_pullbackTransport
    (representedSpaceMap B S hS h) (representedSpaceMap B S hS g) ((modulePullback B S hS hW).obj T)
    (algebraicSpacesComp_representedSpaceMap B S hS h g)
  have hb := functor_map_inv_hom_comp_map_hom_hom
    (representedQuasicoherentSchemeEquivalence B S hS Z').functor
    (quasicoherentPullbackCompIso B S hS h g N)
  exact comp_eq_inv_comp_of_eq _ _ _ _ _ _ _ _ _ _ _ ha hb H

/-- The reading of a morphism `h^*𝒯 ⟶ N^a` along a morphism `k₁` of schemes, transported to an
equal morphism `k₂`. -/
theorem reading_eq_of_eq {Z W : BigFppfOver B S hS} {k₁ k₂ : Z ⟶ W} (e : k₁ = k₂)
    (hW : (⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ : AlgebraicSpaces B S hS) ⟶ X)
    {N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj W).ringCatSheaf).FullSubcategory}
    (E₀ : (modulePullback B S hS hW).obj T ⟶
      ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj N).obj) :
    (modulePullback B S hS (representedSpaceMap B S hS k₁)).map E₀ ≫
        (modulePullbackRepresentedQuasicoherentIso B S hS k₁ N).hom =
      pullbackTransport _ (congrArg (representedSpaceMap B S hS) e) ≫
        (modulePullback B S hS (representedSpaceMap B S hS k₂)).map E₀ ≫
          (modulePullbackRepresentedQuasicoherentIso B S hS k₂ N).hom ≫
            ((representedQuasicoherentSchemeEquivalence B S hS Z).functor.map
              (quasicoherentPullbackEqToHom B S hS e.symm N)).hom := by
  subst e
  have h1 := functor_map_id_hom (representedQuasicoherentSchemeEquivalence B S hS Z).functor
    (quasicoherentPullbackObj B S hS k₁ N)
  exact eq_id_comp_comp_comp_id _ _ _ _ rfl h1

section Transfer

variable {V'' W' W V U : BigFppfOver B S hS} (c' : V'' ⟶ W') (y : W' ⟶ W) (w : V'' ⟶ V)
  (c : V ⟶ W) (yU : V ⟶ U)
  (hW : (⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ : AlgebraicSpaces B S hS) ⟶ X)
  (ab : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶ X)
  {N : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj W).ringCatSheaf).FullSubcategory}
  {M : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
  (E₀ : (modulePullback B S hS hW).obj T ⟶
    ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj N).obj)
  (κ : (modulePullback B S hS ab).obj T ⟶
    ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj)
  (Ψ : quasicoherentPullbackObj B S hS yU M ⟶ quasicoherentPullbackObj B S hS c N)
  (hY : representedSpaceMap B S hS c ≫ hW = representedSpaceMap B S hS yU ≫ ab)
  (hE : (modulePullback B S hS (representedSpaceMap B S hS c)).map E₀ ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS c N).hom =
    modulePullbackCompHom B S hS (representedSpaceMap B S hS c) hW T ≫ pullbackTransport T hY ≫
      modulePullbackCompInv B S hS (representedSpaceMap B S hS yU) ab T ≫
        (modulePullback B S hS (representedSpaceMap B S hS yU)).map κ ≫
          (modulePullbackRepresentedQuasicoherentIso B S hS yU M).hom ≫
            ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map Ψ).hom)
  (hwc : c' ≫ y = w ≫ c)

/-- The reading along `c'` of the inverse image of `E₀` along `y`, moved to the reading along
`w ≫ c`. -/
theorem modulePullback_map_reading_eq_ab :
    type_of% (reading_chase_ab _ _ _ _ _ _ _ _ _ _ _ _
      (modulePullback_map_reading_comp T c' y hW E₀) (reading_eq_of_eq T hwc hW E₀)) :=
  reading_chase_ab _ _ _ _ _ _ _ _ _ _ _ _
    (modulePullback_map_reading_comp T c' y hW E₀) (reading_eq_of_eq T hwc hW E₀)

include hE in
/-- The reading of `E₀` along `w ≫ c`, through its description on the chart `c`. -/
theorem reading_comp_eq_of_eq :
    type_of% (reading_chase_cde _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (reading_comp_eq T w c hW E₀)
      (functor_map_comp_eq_of_eq (modulePullback B S hS (representedSpaceMap B S hS w))
        _ _ _ _ _ _ _ _ hE)
      (modulePullbackRepresentedQuasicoherentIso_naturality B S hS w Ψ)) :=
  reading_chase_cde _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (reading_comp_eq T w c hW E₀)
    (functor_map_comp_eq_of_eq (modulePullback B S hS (representedSpaceMap B S hS w))
      _ _ _ _ _ _ _ _ hE)
    (modulePullbackRepresentedQuasicoherentIso_naturality B S hS w Ψ)

include hE in
/-- The reading of `E₀` along `w ≫ c`, with the description pulled back to `w ≫ yU`. -/
theorem reading_comp_eq_of_eq_comp :
    type_of% (reading_chase_f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (reading_comp_eq_of_eq T w c yU hW ab E₀ κ Ψ hY hE)
      (modulePullback_map_reading_comp T w yU ab κ)) :=
  reading_chase_f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (reading_comp_eq_of_eq T w c yU hW ab E₀ κ Ψ hY hE)
    (modulePullback_map_reading_comp T w yU ab κ)

include hE in
/-- **The reading of an identification `h^*𝒯 ≅ N^a` transferred along a morphism of schemes.**
For `y : W' ⟶ W`, a chart `c' : V'' ⟶ W'` with `c' ≫ y = w ≫ c` for a chart `c : V ⟶ W` on which
the reading of `E₀` is described by `hE` through `yU : V ⟶ U` and `κ`, the reading along `c'` of
the inverse image of `E₀` along `y` is the chain of comparisons of Stacks 03LU and transports,
followed by the inverse image of `κ` along `w ≫ yU`, its identification, and the module attached
to the pullback of the description along `w`. -/
theorem modulePullback_map_reading_eq :
    type_of% (reading_chase
      ((modulePullback B S hS (representedSpaceMap B S hS c')).map
        (modulePullbackCompInv B S hS (representedSpaceMap B S hS y) hW T))
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (modulePullback_map_reading_eq_ab T c' y w c hW E₀ hwc)
      (reading_comp_eq_of_eq_comp T w c yU hW ab E₀ κ Ψ hY hE)) :=
  reading_chase
    ((modulePullback B S hS (representedSpaceMap B S hS c')).map
      (modulePullbackCompInv B S hS (representedSpaceMap B S hS y) hW T))
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (modulePullback_map_reading_eq_ab T c' y w c hW E₀ hwc)
    (reading_comp_eq_of_eq_comp T w c yU hW ab E₀ κ Ψ hY hE)

end Transfer

end Readings

/-! ### The transfer of an identification along a morphism of representable spaces -/

section AttachedTransfer

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Solving `x ≫ y ≫ β = z₁ ≫ … ≫ z₅ ≫ γ` for `x ≫ y`, with `β` and `γ` the images of `θB` and
`θ` under a functor to a full subcategory. -/
theorem comp_eq_comp_map_comp_inv {C D : Type*} [Category C] [Category D]
    {Q : ObjectProperty D} (F : C ⥤ Q.FullSubcategory) {p q r : C} {a b d₁ d₂ d₃ d₄ : D}
    (x : a ⟶ b) (y : b ⟶ (F.obj p).obj) (z₁ : a ⟶ d₁) (z₂ : d₁ ⟶ d₂) (z₃ : d₂ ⟶ d₃)
    (z₄ : d₃ ⟶ d₄) (z₅ : d₄ ⟶ (F.obj q).obj) (θ : q ⟶ r) (θB : p ≅ r)
    (H : x ≫ y ≫ (F.map θB.hom).hom = (z₁ ≫ z₂ ≫ z₃) ≫ z₄ ≫ z₅ ≫ (F.map θ).hom) :
    x ≫ y = z₁ ≫ z₂ ≫ z₃ ≫ z₄ ≫ z₅ ≫ (F.map (θ ≫ θB.inv)).hom := by
  have h1 : y = y ≫ (F.map θB.hom).hom ≫ (F.map θB.inv).hom := by
    rw [functor_map_hom_comp_map_hom, θB.hom_inv_id, F.map_id]
    exact (Category.comp_id _).symm
  rw [h1, reassoc_of% H, functor_map_hom_comp_map_hom]

variable {W' W : BigFppfOver B S hS} {X : AlgebraicSpaces B S hS}
  (T : Modules.{u, u} B S hS X.1 X.2)
  (hW : (⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ : AlgebraicSpaces B S hS) ⟶ X)
  (y : W' ⟶ W)
  {N : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj W).ringCatSheaf).FullSubcategory}
  {N' : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj W').ringCatSheaf).FullSubcategory}
  (E₀ : (modulePullback B S hS hW).obj T ≅
    ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj N).obj)
  (cmp : quasicoherentPullbackObj B S hS y N ≅ N')

/-- The comparison `(f ≫ g)^*M ≅ f^*g^*M` of Stacks 03LU at a module, with
`AlgebraicGeometry.Space.modulePullbackCompInv` as its underlying morphism. -/
def modulePullbackCompInvIso {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Modules.{u, u} B S hS Z.1 Z.2) :
    (modulePullback B S hS (f ≫ g)).obj M ≅
      (modulePullback B S hS f).obj ((modulePullback B S hS g).obj M) where
  hom := modulePullbackCompInv B S hS f g M
  inv := modulePullbackCompHom B S hS f g M
  hom_inv_id := modulePullbackCompInv_comp_compHom B S hS f g M
  inv_hom_id := modulePullbackCompHom_comp_compInv B S hS f g M

/-- **An identification `hW^*𝒯 ≅ N^a` transferred along a morphism of schemes** `y : W' ⟶ W`:
the identification `(y ≫ hW)^*𝒯 ≅ y^*hW^*𝒯 ≅ y^*(N^a) ≅ (y^*N)^a ≅ N'^a` of the comparison of
Stacks 03LU, the inverse image of `E₀`, Stacks 03DX (2) and the module attached to
`cmp : y^*N ≅ N'`. -/
def attachedModuleIsoPullback :
    (modulePullback B S hS (representedSpaceMap B S hS y ≫ hW)).obj T ≅
      ((representedQuasicoherentSchemeEquivalence B S hS W').functor.obj N').obj :=
  modulePullbackCompInvIso (representedSpaceMap B S hS y) hW T ≪≫
    (modulePullback B S hS (representedSpaceMap B S hS y)).mapIso E₀ ≪≫
      modulePullbackRepresentedQuasicoherentIso B S hS y N ≪≫
        (ObjectProperty.ι _).mapIso
          ((representedQuasicoherentSchemeEquivalence B S hS W').functor.mapIso cmp)

end AttachedTransfer

section SpecTransfer

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
  (P0 : Presentation B S hS F hF) {W : BigFppfOver B S hS} (e : F ≅ yoneda.obj W)
  (c : P0.U ⟶ W) (hc : yoneda.map c = P0.toSpace ≫ e.hom)
  {F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF' : IsAlgebraicSpace B S hS F'}
  (P0' : Presentation B S hS F' hF') {W' : BigFppfOver B S hS} (e' : F' ≅ yoneda.obj W')
  (c' : P0'.U ⟶ W') (hc' : yoneda.map c' = P0'.toSpace ≫ e'.hom)
  (N : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj W).ringCatSheaf).FullSubcategory)
  {M'' : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj P0.U).ringCatSheaf).FullSubcategory}
  (ΘB : quasicoherentPullbackObj B S hS c N ≅ M'')
  (N' : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj W').ringCatSheaf).FullSubcategory)
  {M''' : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj P0'.U).ringCatSheaf).FullSubcategory}
  (ΘB' : quasicoherentPullbackObj B S hS c' N' ≅ M''')
  {XA : AlgebraicSpaces B S hS} (Pb : Presentation B S hS XA.obj XA.property)
  (Tm : QuasicoherentSheaves.{u, u} B S hS XA.obj XA.property)
  {M : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj Pb.U).ringCatSheaf).FullSubcategory}
  (κ : (modulePullback B S hS (presentationAtlas Pb)).obj Tm.obj ≅
    ((representedQuasicoherentSchemeEquivalence B S hS Pb.U).functor.obj M).obj)
  (hW : representedAlgebraicSpace B S hS W ⟶ XA) (yU : P0.U ⟶ Pb.U)
  (hY : presentationAtlas (P0.ofIsoYoneda e c hc) ≫ hW =
    representedSpaceMap B S hS yU ≫ presentationAtlas Pb)
  (Θ : quasicoherentPullbackObj B S hS yU M ≅ M'')
  (y : W' ⟶ W) (yU' : P0'.U ⟶ Pb.U)
  (hY' : presentationAtlas (P0'.ofIsoYoneda e' c' hc') ≫ (representedSpaceMap B S hS y ≫ hW) =
    representedSpaceMap B S hS yU' ≫ presentationAtlas Pb)
  (Θ' : quasicoherentPullbackObj B S hS yU' M ≅ M''')
  (E₀ : (modulePullback B S hS hW).obj Tm.obj ≅
    ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj N).obj)
  (hE : (modulePullback B S hS (presentationAtlas (P0.ofIsoYoneda e c hc))).map E₀.hom ≫
      (ofIsoYonedaChartIso P0 e c hc N ΘB).hom =
    (presentationPullbackChartIso (P0.ofIsoYoneda e c hc) Pb hW yU hY Tm κ Θ).hom)
  (cmp : quasicoherentPullbackObj B S hS y N ≅ N') (w : P0'.U ⟶ P0.U)
  (hwc : c' ≫ y = w ≫ c) (hwy : w ≫ yU = yU')
  (H : quasicoherentPullbackEqToHom B S hS hwy M ≫ Θ'.hom =
    (quasicoherentPullbackCompIso B S hS w yU M).inv ≫
      quasicoherentPullbackMap B S hS w Θ.hom ≫ quasicoherentPullbackMap B S hS w ΘB.inv ≫
        (quasicoherentPullbackCompIso B S hS w c N).hom ≫
          quasicoherentPullbackEqToHom B S hS hwc.symm N ≫
            (quasicoherentPullbackCompIso B S hS c' y N).inv ≫
              quasicoherentPullbackMap B S hS c' cmp.hom ≫ ΘB'.hom)

/-- The underlying morphisms of an equation of isomorphisms
`F(E₀) ≪≫ ρ ≪≫ ι(G(θB)) = π ≪≫ K ≪≫ R ≪≫ ι(G(θ))`, read as a description of `F(E₀)` through the
ratio `θ ≫ θB⁻¹`, with the first factor `π` written out as `cH ≫ tr ≫ cI`. -/
theorem map_comp_eq_of_iso_eq {C C' D : Type*} [Category C] [Category C'] [Category D]
    {Q : ObjectProperty D} (F : C ⥤ D) (G : C' ⥤ Q.FullSubcategory) {a b : C} {p q r : C'}
    {d₀ d₁ d₃ d₄ : D} (E₀ : a ≅ b) (ρ : F.obj b ≅ (G.obj p).obj) (θB : p ≅ r)
    (π : F.obj a ≅ d₃) (K : d₃ ≅ d₄) (R : d₄ ≅ (G.obj q).obj) (θ : q ≅ r)
    (cH : F.obj a ⟶ d₀) (tr : d₀ ⟶ d₁) (cI : d₁ ⟶ d₃) (hπ : π.hom = cH ≫ tr ≫ cI)
    (H : F.mapIso E₀ ≪≫ ρ ≪≫ (ObjectProperty.ι _).mapIso (G.mapIso θB) =
      π ≪≫ K ≪≫ R ≪≫ (ObjectProperty.ι _).mapIso (G.mapIso θ)) :
    F.map E₀.hom ≫ ρ.hom = cH ≫ tr ≫ cI ≫ K.hom ≫ R.hom ≫ (G.map (θ.hom ≫ θB.inv)).hom := by
  have h := congrArg Iso.hom H
  simp only [Iso.trans_hom, Functor.mapIso_hom, ObjectProperty.ι_map, hπ] at h
  exact comp_eq_comp_map_comp_inv G _ _ _ _ _ _ _ θ.hom θB h

include hE in
/-- The description `hE` of `E₀` on the atlas `c` of `W`, as an equation of isomorphisms on the
represented algebraic space of the presenting scheme. -/
theorem ofIsoYonedaChartIso_spec_represented :
    (modulePullback B S hS (representedSpaceMap B S hS c)).mapIso E₀ ≪≫
      modulePullbackRepresentedQuasicoherentIso B S hS c N ≪≫
        (ObjectProperty.ι _).mapIso
          ((representedQuasicoherentSchemeEquivalence B S hS P0.U).functor.mapIso ΘB) =
      pullbackSquareIso (representedSpaceMap B S hS c) (presentationAtlas Pb) hW
          (representedSpaceMap B S hS yU) hY Tm.obj ≪≫
        (modulePullback B S hS (representedSpaceMap B S hS yU)).mapIso κ ≪≫
          modulePullbackRepresentedQuasicoherentIso B S hS yU M ≪≫
            (ObjectProperty.ι _).mapIso
              ((representedQuasicoherentSchemeEquivalence B S hS P0.U).functor.mapIso Θ) :=
  (Iso.ext hE : (modulePullback B S hS (presentationAtlas (P0.ofIsoYoneda e c hc))).mapIso E₀ ≪≫
      ofIsoYonedaChartIso P0 e c hc N ΘB =
      presentationPullbackChartIso (P0.ofIsoYoneda e c hc) Pb hW yU hY Tm κ Θ)

variable (hER : (modulePullback B S hS (representedSpaceMap B S hS c)).mapIso E₀ ≪≫
      modulePullbackRepresentedQuasicoherentIso B S hS c N ≪≫
        (ObjectProperty.ι _).mapIso
          ((representedQuasicoherentSchemeEquivalence B S hS P0.U).functor.mapIso ΘB) =
      pullbackSquareIso (representedSpaceMap B S hS c) (presentationAtlas Pb) hW
          (representedSpaceMap B S hS yU) hY Tm.obj ≪≫
        (modulePullback B S hS (representedSpaceMap B S hS yU)).mapIso κ ≪≫
          modulePullbackRepresentedQuasicoherentIso B S hS yU M ≪≫
            (ObjectProperty.ι _).mapIso
              ((representedQuasicoherentSchemeEquivalence B S hS P0.U).functor.mapIso Θ))
  (hY₁ : representedSpaceMap B S hS c' ≫ (representedSpaceMap B S hS y ≫ hW) =
    representedSpaceMap B S hS (w ≫ yU) ≫ presentationAtlas Pb)
  (Θ₁ : quasicoherentPullbackObj B S hS (w ≫ yU) M ≅ M''')
  (H₁ : quasicoherentPullbackEqToHom B S hS (rfl : w ≫ yU = w ≫ yU) M ≫ Θ₁.hom =
    (quasicoherentPullbackCompIso B S hS w yU M).inv ≫
      quasicoherentPullbackMap B S hS w Θ.hom ≫ quasicoherentPullbackMap B S hS w ΘB.inv ≫
        (quasicoherentPullbackCompIso B S hS w c N).hom ≫
          quasicoherentPullbackEqToHom B S hS hwc.symm N ≫
            (quasicoherentPullbackCompIso B S hS c' y N).inv ≫
              quasicoherentPullbackMap B S hS c' cmp.hom ≫ ΘB'.hom)

include hER H₁ hY₁ in
/-- **The description on the étale cover of a transferred identification**, on the represented
algebraic spaces of the presenting schemes, with all morphisms written out. -/
theorem attachedModuleIsoPullback_spec_represented :
    type_of% (attached_chase (modulePullback B S hS (representedSpaceMap B S hS c'))
      _ _ _ _ _ ((representedQuasicoherentSchemeEquivalence B S hS P0'.U).functor.map ΘB'.hom).hom
      _ _ _ _ _ _ _ _ _ _ _ _ _
      ((representedQuasicoherentSchemeEquivalence B S hS P0'.U).functor.map
        Θ₁.hom).hom
      (modulePullbackRepresentedQuasicoherentIso_naturality B S hS c' cmp.hom)
      (modulePullback_map_reading_eq Tm.obj c' y w c yU hW (presentationAtlas Pb) E₀.hom
        κ.hom (Θ.hom ≫ ΘB.inv) hY
        (eq_of_heq_of_heq (by heq_congr) (by heq_congr)
          (map_comp_eq_of_iso_eq _ _ _ _ _ _ _ _ _ _ _ _
            (pullbackSquareHom_eq_comp _ _ _ _ _ _) hER)) hwc)
      (eq_of_heq_of_heq (by heq_congr) HEq.rfl
        (modulePullbackCompInv_chain_eq (representedSpaceMap B S hS c')
        (representedSpaceMap B S hS y) hW (representedSpaceMap B S hS c)
        (representedSpaceMap B S hS w) (representedSpaceMap B S hS yU) (presentationAtlas Pb)
        (representedSpaceMap B S hS (w ≫ yU)) Tm.obj
        (algebraicSpacesComp_representedSpaceMap B S hS c' y)
        (congrArg (representedSpaceMap B S hS) hwc)
        (algebraicSpacesComp_representedSpaceMap B S hS w c).symm hY
        (algebraicSpacesComp_representedSpaceMap B S hS w yU) hY₁))
      (eq_of_heq_of_heq (by heq_congr) (by heq_congr)
        (functor_map_hom_chain_eq (representedQuasicoherentSchemeEquivalence B S hS P0'.U).functor
          _ _ _ _ _ _ _ _ _ _ _ (quasicoherentPullbackMap_comp B S hS w Θ.hom ΘB.inv)
          (quasicoherentPullbackEqToHom_rfl B S hS M) H₁))) :=
  attached_chase (modulePullback B S hS (representedSpaceMap B S hS c'))
    _ _ _ _ _ ((representedQuasicoherentSchemeEquivalence B S hS P0'.U).functor.map ΘB'.hom).hom
    _ _ _ _ _ _ _ _ _ _ _ _ _ ((representedQuasicoherentSchemeEquivalence B S hS P0'.U).functor.map
      Θ₁.hom).hom
    (modulePullbackRepresentedQuasicoherentIso_naturality B S hS c' cmp.hom)
    (modulePullback_map_reading_eq Tm.obj c' y w c yU hW (presentationAtlas Pb) E₀.hom
      κ.hom (Θ.hom ≫ ΘB.inv) hY
      (eq_of_heq_of_heq (by heq_congr) (by heq_congr)
        (map_comp_eq_of_iso_eq _ _ _ _ _ _ _ _ _ _ _ _
          (pullbackSquareHom_eq_comp _ _ _ _ _ _) hER)) hwc)
    (eq_of_heq_of_heq (by heq_congr) HEq.rfl
      (modulePullbackCompInv_chain_eq (representedSpaceMap B S hS c')
      (representedSpaceMap B S hS y) hW (representedSpaceMap B S hS c)
      (representedSpaceMap B S hS w) (representedSpaceMap B S hS yU) (presentationAtlas Pb)
      (representedSpaceMap B S hS (w ≫ yU)) Tm.obj
      (algebraicSpacesComp_representedSpaceMap B S hS c' y)
      (congrArg (representedSpaceMap B S hS) hwc)
      (algebraicSpacesComp_representedSpaceMap B S hS w c).symm hY
      (algebraicSpacesComp_representedSpaceMap B S hS w yU) hY₁))
    (eq_of_heq_of_heq (by heq_congr) (by heq_congr)
      (functor_map_hom_chain_eq (representedQuasicoherentSchemeEquivalence B S hS P0'.U).functor
        _ _ _ _ _ _ _ _ _ _ _ (quasicoherentPullbackMap_comp B S hS w Θ.hom ΘB.inv)
        (quasicoherentPullbackEqToHom_rfl B S hS M) H₁))

include e' hc' in
/-- **The inverse image along the represented atlas `c'` of `W'` is faithful** on morphisms from
the inverse image of a quasi-coherent module to `N'^a` (Stacks 03M3, read on the represented
algebraic space of the presenting scheme). -/
theorem modulePullback_representedSpaceMap_map_injective {XA' : AlgebraicSpaces B S hS}
    (hW' : (⟨yoneda.obj W', isAlgebraicSpace_yoneda B S hS W'⟩ : AlgebraicSpaces B S hS) ⟶ XA')
    (Tm' : QuasicoherentSheaves.{u, u} B S hS XA'.obj XA'.property)
    (φ ψ : (modulePullback B S hS hW').obj Tm'.obj ⟶
      ((representedQuasicoherentSchemeEquivalence B S hS W').functor.obj N').obj)
    (h : (modulePullback B S hS (representedSpaceMap B S hS c')).map φ =
      (modulePullback B S hS (representedSpaceMap B S hS c')).map ψ) : φ = ψ := by
  have key := @presentationAtlas_map_injective _ _ _ _ (P0'.ofIsoYoneda e' c' hc') _ _
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ _ Tm'.property)
    ((representedQuasicoherentSchemeEquivalence B S hS W').functor.obj N').property φ ψ
  dsimp only [presentationAtlas, presentationGroupoid, Presentation.ofIsoYoneda,
    Presentation.ofIso, representedAlgebraicSpace, representedSpaceMap] at key h ⊢
  exact key h

/-- `AlgebraicGeometry.Space.attachedModuleIsoPullback` as a composite of morphisms.

The module is an `𝒪`-module `Tmo` on `XA`, not the quasi-coherent object it is the underlying
module of: quasi-coherence is not used, and a statement reading the module off a quasi-coherent
object indexes its `𝒪`-modules by the site of `XA.obj` where a statement about an `𝒪`-module
indexes them by the site of the space the module is given on.  The two agree, but for a bundled
`XA` only after a projection of a constructor is reduced, and the kernel reduces
`AlgebraicGeometry.Space.modulePullbackCompIso` -- the uniqueness of a left adjoint -- to decide
it. -/
theorem attachedModuleIsoPullback_hom (Tmo : Modules.{u, u} B S hS XA.1 XA.2)
    (hWc : (⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ : AlgebraicSpaces B S hS) ⟶ XA)
    (E₀ : (modulePullback B S hS hWc).obj Tmo ≅
      ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj N).obj) :
    (attachedModuleIsoPullback Tmo hWc y E₀ cmp).hom =
      modulePullbackCompInv B S hS (representedSpaceMap B S hS y) hWc Tmo ≫
        (modulePullback B S hS (representedSpaceMap B S hS y)).map E₀.hom ≫
          (modulePullbackRepresentedQuasicoherentIso B S hS y N).hom ≫
            ((representedQuasicoherentSchemeEquivalence B S hS W').functor.map cmp.hom).hom :=
  rfl

variable (hY'' : representedSpaceMap B S hS c' ≫ (representedSpaceMap B S hS y ≫ hW) =
    representedSpaceMap B S hS yU' ≫ presentationAtlas Pb)

include hE H hY'' in
/-- **A transferred identification is the identification with the transferred description.**
If `E₀ : hW^*𝒯 ≅ N^a` has the description `hE` on the atlas `c` of `W`, and the comparisons on
the atlas `c'` of `W'` satisfy the scheme-level compatibility `H` along a morphism `w` of the
presenting schemes with `c' ≫ y = w ≫ c` and `w ≫ yU = yU'`, then every isomorphism
`E₂ : (y ≫ hW)^*𝒯 ≅ N'^a` with the description on the atlas `c'` through `yU'`, `κ`, `Θ'`, `ΘB'`
is the identification transferred along `y`. -/
theorem attachedModuleIsoPullback_eq_of_spec
    (E₂ : (modulePullback B S hS (representedSpaceMap B S hS y ≫ hW)).obj Tm.obj ≅
      ((representedQuasicoherentSchemeEquivalence B S hS W').functor.obj N').obj)
    (hE₂ : (modulePullback B S hS (presentationAtlas (P0'.ofIsoYoneda e' c' hc'))).map E₂.hom ≫
        (ofIsoYonedaChartIso P0' e' c' hc' N' ΘB').hom =
      (presentationPullbackChartIso (P0'.ofIsoYoneda e' c' hc') Pb
        (representedSpaceMap B S hS y ≫ hW) yU' hY' Tm κ Θ').hom) :
    attachedModuleIsoPullback Tm.obj hW y E₀ cmp = E₂ := by
  subst hwy
  have h₂ := attachedModuleIsoPullback_spec_represented P0 e c hc P0' c' N ΘB N' ΘB' Pb Tm κ hW
    yU hY Θ y E₀ cmp w hwc
    (ofIsoYonedaChartIso_spec_represented P0 e c hc N ΘB Pb Tm κ hW yU hY Θ E₀ hE) hY'' Θ' H
  have h₃ := map_hom_comp_eq_of_iso_eq _ _ _ _ _ _ _ _ _ _ _ _
    (pullbackSquareHom_eq_comp _ _ _ _ _ _)
    (ofIsoYonedaChartIso_spec_represented P0' e' c' hc' N' ΘB' Pb Tm κ
      (representedSpaceMap B S hS y ≫ hW) (w ≫ yU) hY' Θ' E₂ hE₂)
  have h₂' := eq_comp_comp_comp_of_eq_comp _ _ _ _ _ h₂
  refine Iso.ext ((attachedModuleIsoPullback_hom (N := N) (N' := N') (y := y)
    (cmp := cmp) Tm.obj hW E₀).trans
    (modulePullback_representedSpaceMap_map_injective P0' e' c' hc' N'
      (representedSpaceMap B S hS y ≫ hW) Tm _ _
    (eq_of_comp_comp_eq_comp_comp (modulePullbackRepresentedQuasicoherentIso B S hS c' N').hom
      ((representedQuasicoherentSchemeEquivalence B S hS P0'.U).functor.map ΘB'.hom).hom
      (modulePullbackRepresentedQuasicoherentIso B S hS c' N').inv
      ((representedQuasicoherentSchemeEquivalence B S hS P0'.U).functor.map ΘB'.inv).hom
      (Iso.hom_inv_id _) (functor_map_inv_hom_comp_map_hom_hom _ ΘB'.symm) ?_)))
  exact eq_of_eq_of_eq_of_heq h₂' h₃ (by heq_congr) (by heq_congr) (by heq_congr)

include hE H in
/-- **The identification along `hW₂ = y ≫ hW` with the transferred description is the transferred
identification**, read through the transport along `y ≫ hW = hW₂`: any isomorphism
`E₂ : hW₂^*𝒯 ≅ N'^a` with the description on the atlas `c'` of `W'` through `yU'`, `κ`, `Θ'` and
`ΘB'` is the transport followed by `AlgebraicGeometry.Space.attachedModuleIsoPullback`. -/
theorem eq_eqToIso_trans_attachedModuleIsoPullback
    {hW₂ : representedAlgebraicSpace B S hS W' ⟶ XA}
    (hk : representedSpaceMap B S hS y ≫ hW = hW₂)
    (hY₂ : presentationAtlas (P0'.ofIsoYoneda e' c' hc') ≫ hW₂ =
      representedSpaceMap B S hS yU' ≫ presentationAtlas Pb)
    (E₂ : (modulePullback B S hS hW₂).obj Tm.obj ≅
      ((representedQuasicoherentSchemeEquivalence B S hS W').functor.obj N').obj)
    (hE₂ : (modulePullback B S hS (presentationAtlas (P0'.ofIsoYoneda e' c' hc'))).map E₂.hom ≫
        (ofIsoYonedaChartIso P0' e' c' hc' N' ΘB').hom =
      (presentationPullbackChartIso (P0'.ofIsoYoneda e' c' hc') Pb hW₂ yU' hY₂ Tm κ Θ').hom) :
    E₂ = eqToIso (congrArg (fun k : (⟨yoneda.obj W', isAlgebraicSpace_yoneda B S hS W'⟩ :
        AlgebraicSpaces B S hS) ⟶ XA => (modulePullback B S hS k).obj Tm.obj) hk.symm) ≪≫
      attachedModuleIsoPullback Tm.obj hW y E₀ cmp := by
  subst hk
  have hY'' : representedSpaceMap B S hS c' ≫ (representedSpaceMap B S hS y ≫ hW) =
      representedSpaceMap B S hS yU' ≫ presentationAtlas Pb :=
    ObjectProperty.hom_ext _ (congrArg (fun k => k.hom) hY₂)
  rw [attachedModuleIsoPullback_eq_of_spec P0 e c hc P0' e' c' hc' N ΘB N' ΘB' Pb Tm κ hW yU hY Θ y
    yU' hY₂ Θ' E₀ hE cmp w hwc hwy H hY'' E₂ hE₂]
  exact Iso.ext (Category.id_comp _).symm

/-- The description on the étale cover of an identification, transported along an equality of
the morphisms to the space. -/
theorem ofIsoYonedaChartIso_spec_eqToIso_trans {F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hF' : IsAlgebraicSpace B S hS F'} (P0' : Presentation B S hS F' hF')
    {W' : BigFppfOver B S hS} (e' : F' ≅ yoneda.obj W') (c' : P0'.U ⟶ W')
    (hc' : yoneda.map c' = P0'.toSpace ≫ e'.hom)
    (N' : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj W').ringCatSheaf).FullSubcategory)
    {M''' : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj P0'.U).ringCatSheaf).FullSubcategory}
    (ΘB' : quasicoherentPullbackObj B S hS c' N' ≅ M''')
    {XA : AlgebraicSpaces B S hS} (Pb : Presentation B S hS XA.obj XA.property)
    (Tm : QuasicoherentSheaves.{u, u} B S hS XA.obj XA.property)
    {M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj Pb.U).ringCatSheaf).FullSubcategory}
    (κ : (modulePullback B S hS (presentationAtlas Pb)).obj Tm.obj ≅
      ((representedQuasicoherentSchemeEquivalence B S hS Pb.U).functor.obj M).obj)
    {hW₀ hW' : representedAlgebraicSpace B S hS W' ⟶ XA} (h : hW₀ = hW') (yU' : P0'.U ⟶ Pb.U)
    (hY₀ : presentationAtlas (P0'.ofIsoYoneda e' c' hc') ≫ hW₀ =
      representedSpaceMap B S hS yU' ≫ presentationAtlas Pb)
    (hY' : presentationAtlas (P0'.ofIsoYoneda e' c' hc') ≫ hW' =
      representedSpaceMap B S hS yU' ≫ presentationAtlas Pb)
    (Θ' : quasicoherentPullbackObj B S hS yU' M ≅ M''')
    (X₀ : (modulePullback B S hS hW₀).obj Tm.obj ≅
      ((representedQuasicoherentSchemeEquivalence B S hS W').functor.obj N').obj)
    (hX : (modulePullback B S hS (presentationAtlas (P0'.ofIsoYoneda e' c' hc'))).map X₀.hom ≫
        (ofIsoYonedaChartIso P0' e' c' hc' N' ΘB').hom =
      (presentationPullbackChartIso (P0'.ofIsoYoneda e' c' hc') Pb hW₀ yU' hY₀ Tm κ Θ').hom) :
    (modulePullback B S hS (presentationAtlas (P0'.ofIsoYoneda e' c' hc'))).map
        (eqToIso (congrArg (fun k => (modulePullback B S hS k).obj Tm.obj) h.symm) ≪≫ X₀).hom ≫
        (ofIsoYonedaChartIso P0' e' c' hc' N' ΘB').hom =
      (presentationPullbackChartIso (P0'.ofIsoYoneda e' c' hc') Pb hW' yU' hY' Tm κ Θ').hom := by
  subst h
  exact (congrArg (fun t => (modulePullback B S hS
    (presentationAtlas (P0'.ofIsoYoneda e' c' hc'))).map t ≫
      (ofIsoYonedaChartIso P0' e' c' hc' N' ΘB').hom) (Category.id_comp X₀.hom)).trans hX

end SpecTransfer

/-! ### Naturality of the identification along a representable base change -/

namespace RelativeProjPoints

section PullbackAlongYonedaIsoComp

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {XA XA' XA₂ : AlgebraicSpaces B S hS} {PA PA' PA₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {πA : PA ⟶ XA.obj} {πA' : PA' ⟶ XA'.obj} {πA₂ : PA₂ ⟶ XA₂.obj}
  {dA : RelativeProjPoints B S hS πA} {dA' : RelativeProjPoints B S hS πA'}
  {dA₂ : RelativeProjPoints B S hS πA₂} {hA : PA' ⟶ PA} {hA₂ : PA₂ ⟶ PA}
  (Px : Presentation B S hS XA.obj XA.property)
  (Px' : Presentation B S hS XA'.obj XA'.property)
  (Px₂ : Presentation B S hS XA₂.obj XA₂.property) (hP : IsAlgebraicSpace B S hS PA)
  (hP' : IsAlgebraicSpace B S hS PA') (hP₂ : IsAlgebraicSpace B S hS PA₂)
  {ℓ : Px'.U ⟶ Px.U} {ℓR : Px'.R ⟶ Px.R}
  (hℓt : ℓR ≫ Px.target = Px'.target ≫ ℓ) (hℓs : ℓR ≫ Px.source = Px'.source ≫ ℓ)
  (yU : dA'.fibre Px'.U Px'.toSpace ⟶ dA.fibre Px.U Px.toSpace)
  (hyU : dA'.LiesOverAlong dA hA yU ℓ)
  (yR : dA'.fibre Px'.R (relationPoint Px') ⟶ dA.fibre Px.R (relationPoint Px))
  (hyR : dA'.LiesOverAlong dA hA yR ℓR)
  {ℓ₂ : Px₂.U ⟶ Px.U} {ℓR₂ : Px₂.R ⟶ Px.R}
  (hℓt₂ : ℓR₂ ≫ Px.target = Px₂.target ≫ ℓ₂) (hℓs₂ : ℓR₂ ≫ Px.source = Px₂.source ≫ ℓ₂)
  (yU₂ : dA₂.fibre Px₂.U Px₂.toSpace ⟶ dA.fibre Px.U Px.toSpace)
  (hyU₂ : dA₂.LiesOverAlong dA hA₂ yU₂ ℓ₂)
  (yR₂ : dA₂.fibre Px₂.R (relationPoint Px₂) ⟶ dA.fibre Px.R (relationPoint Px))
  (hyR₂ : dA₂.LiesOverAlong dA hA₂ yR₂ ℓR₂)
  (Tm : QuasicoherentSheaves.{u, u} B S hS PA hP)
  {M : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj (dA.fibre Px.U Px.toSpace)).ringCatSheaf).FullSubcategory}
  (τ : quasicoherentPullbackObj B S hS (dA.spaceTarget Px hP) M ⟶
    quasicoherentPullbackObj B S hS (dA.spaceSource Px hP) M)
  (κ : (modulePullback B S hS (presentationAtlas (dA.spacePresentation Px hP))).obj Tm.obj ≅
    ((representedQuasicoherentSchemeEquivalence B S hS (dA.fibre Px.U Px.toSpace)).functor.obj
      M).obj)
  (hκ : TransitionCommutes B S hS (U := (presentationGroupoid (dA.spacePresentation Px hP)).objects)
    (V := (presentationGroupoid (dA.spacePresentation Px hP)).arrows)
    (a := (presentationGroupoid (dA.spacePresentation Px hP)).target)
    (b := (presentationGroupoid (dA.spacePresentation Px hP)).source)
    (spaceBaseDescent B S hS (presentationGroupoid (dA.spacePresentation Px hP))
      (presentationAtlas (dA.spacePresentation Px hP))
      (presentationAtlas_comm (dA.spacePresentation Px hP)) Tm.obj)
    (presentationSchemeTransition (dA.spacePresentation Px hP) M τ) κ.hom)
  {M'' : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj (dA'.fibre Px'.U Px'.toSpace)).ringCatSheaf).FullSubcategory}
  (τ'' : quasicoherentPullbackObj B S hS (dA'.spaceTarget Px' hP') M'' ⟶
    quasicoherentPullbackObj B S hS (dA'.spaceSource Px' hP') M'')
  (Θ : quasicoherentPullbackObj B S hS yU M ≅ M'')
  (hΘ : PullbackTransitionCompatible Px Px' hP hP' hℓt hℓs yU hyU yR hyR τ τ'' Θ)
  {W : BigFppfOver B S hS} (e : PA' ≅ yoneda.obj W) (c : dA'.fibre Px'.U Px'.toSpace ⟶ W)
  (hc : yoneda.map c = (dA'.spacePresentation Px' hP').toSpace ≫ e.hom)
  (hW : representedAlgebraicSpace B S hS W ⟶ ⟨PA, hP⟩)
  (hY : presentationAtlas ((dA'.spacePresentation Px' hP').ofIsoYoneda e c hc) ≫ hW =
    representedSpaceMap B S hS yU ≫ presentationAtlas (dA.spacePresentation Px hP))
  (N : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj W).ringCatSheaf).FullSubcategory)
  (ΘB : quasicoherentPullbackObj B S hS c N ≅ M'')
  (hΘB : canonicalSchemeTransition B S hS (dA'.spaceTarget Px' hP') (dA'.spaceSource Px' hP') c
      (Presentation.target_comp_eq_source_comp_of_iso (dA'.spacePresentation Px' hP') e c hc) N ≫
      quasicoherentPullbackMap B S hS (dA'.spaceSource Px' hP') ΘB.hom =
    quasicoherentPullbackMap B S hS (dA'.spaceTarget Px' hP') ΘB.hom ≫ τ'')
  {M₂ : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj (dA₂.fibre Px₂.U Px₂.toSpace)).ringCatSheaf).FullSubcategory}
  (τ₂ : quasicoherentPullbackObj B S hS (dA₂.spaceTarget Px₂ hP₂) M₂ ⟶
    quasicoherentPullbackObj B S hS (dA₂.spaceSource Px₂ hP₂) M₂)
  (Θ₂ : quasicoherentPullbackObj B S hS yU₂ M ≅ M₂)
  (hΘ₂ : PullbackTransitionCompatible Px Px₂ hP hP₂ hℓt₂ hℓs₂ yU₂ hyU₂ yR₂ hyR₂ τ τ₂ Θ₂)
  {W₂ : BigFppfOver B S hS} (e₂ : PA₂ ≅ yoneda.obj W₂) (c₂ : dA₂.fibre Px₂.U Px₂.toSpace ⟶ W₂)
  (hc₂ : yoneda.map c₂ = (dA₂.spacePresentation Px₂ hP₂).toSpace ≫ e₂.hom)
  (hW₂ : representedAlgebraicSpace B S hS W₂ ⟶ ⟨PA, hP⟩)
  (hY₂ : presentationAtlas ((dA₂.spacePresentation Px₂ hP₂).ofIsoYoneda e₂ c₂ hc₂) ≫ hW₂ =
    representedSpaceMap B S hS yU₂ ≫ presentationAtlas (dA.spacePresentation Px hP))
  (N₂ : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj W₂).ringCatSheaf).FullSubcategory)
  (ΘB₂ : quasicoherentPullbackObj B S hS c₂ N₂ ≅ M₂)
  (hΘB₂ : canonicalSchemeTransition B S hS (dA₂.spaceTarget Px₂ hP₂) (dA₂.spaceSource Px₂ hP₂) c₂
      (Presentation.target_comp_eq_source_comp_of_iso (dA₂.spacePresentation Px₂ hP₂) e₂ c₂ hc₂)
        N₂ ≫
      quasicoherentPullbackMap B S hS (dA₂.spaceSource Px₂ hP₂) ΘB₂.hom =
    quasicoherentPullbackMap B S hS (dA₂.spaceTarget Px₂ hP₂) ΘB₂.hom ≫ τ₂)
  (y : W₂ ⟶ W) (hk : representedSpaceMap B S hS y ≫ hW = hW₂)
  (cmp : quasicoherentPullbackObj B S hS y N ≅ N₂)
  (w : dA₂.fibre Px₂.U Px₂.toSpace ⟶ dA'.fibre Px'.U Px'.toSpace)
  (hwc : c₂ ≫ y = w ≫ c) (hwy : w ≫ yU = yU₂)
  (H : quasicoherentPullbackEqToHom B S hS hwy M ≫ Θ₂.hom =
    (quasicoherentPullbackCompIso B S hS w yU M).inv ≫
      quasicoherentPullbackMap B S hS w Θ.hom ≫ quasicoherentPullbackMap B S hS w ΘB.inv ≫
        (quasicoherentPullbackCompIso B S hS w c N).hom ≫
          quasicoherentPullbackEqToHom B S hS hwc.symm N ≫
            (quasicoherentPullbackCompIso B S hS c₂ y N).inv ≫
              quasicoherentPullbackMap B S hS c₂ cmp.hom ≫ ΘB₂.hom)

include hκ hΘ hΘB hΘ₂ hΘB₂ H in
/-- **The identification along a representable base change is natural**: for two compatible
presentations over `P` with identifications along `hW` and `hW₂ = y ≫ hW`, related through a
morphism `w` of the presenting schemes over `y` along which the comparisons are compatible (`H`),
the identification along `hW₂` is the identification along `hW` transferred along `y`. -/
theorem pullbackTransitionCompatibleIso_comp :
    pullbackTransitionCompatibleIso Px Px₂ hP hP₂ hℓt₂ hℓs₂ yU₂ hyU₂ yR₂ hyR₂ Tm τ κ hκ τ₂ Θ₂ hΘ₂
        e₂ c₂ hc₂ hW₂ hY₂ N₂ ΘB₂ hΘB₂ =
      eqToIso (congrArg (fun k : (⟨yoneda.obj W₂, isAlgebraicSpace_yoneda B S hS W₂⟩ :
          AlgebraicSpaces B S hS) ⟶ ⟨PA, hP⟩ => (modulePullback B S hS k).obj Tm.obj)
          hk.symm) ≪≫
        attachedModuleIsoPullback (X := ⟨PA, hP⟩) (N := N) (N' := N₂) Tm.obj hW y
          (pullbackTransitionCompatibleIso Px Px' hP hP' hℓt hℓs yU hyU yR hyR Tm τ κ hκ τ'' Θ hΘ
            e c hc hW hY N ΘB hΘB) cmp :=
  eq_eqToIso_trans_attachedModuleIsoPullback (dA'.spacePresentation Px' hP') e c hc
    (dA₂.spacePresentation Px₂ hP₂) e₂ c₂ hc₂ N ΘB N₂ ΘB₂ (dA.spacePresentation Px hP) Tm κ
    hW yU hY Θ y yU₂ Θ₂
    (pullbackTransitionCompatibleIso Px Px' hP hP' hℓt hℓs yU hyU yR hyR Tm τ κ hκ τ'' Θ hΘ
      e c hc hW hY N ΘB hΘB)
    (pullbackTransitionCompatibleIso_spec Px Px' hP hP' hℓt hℓs yU hyU yR hyR Tm τ κ hκ τ'' Θ hΘ
      e c hc hW hY N ΘB hΘB) cmp w hwc hwy H hk hY₂ _
    (pullbackTransitionCompatibleIso_spec Px Px₂ hP hP₂ hℓt₂ hℓs₂ yU₂ hyU₂ yR₂ hyR₂ Tm τ κ hκ
      τ₂ Θ₂ hΘ₂ e₂ c₂ hc₂ hW₂ hY₂ N₂ ΘB₂ hΘB₂)

end PullbackAlongYonedaIsoComp

end RelativeProjPoints

/-! ### Morphisms of base changes through three relative Projs -/

namespace RelativeProjPoints

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X X' X'' P P' P'' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : P ⟶ X} {π' : P' ⟶ X'}
  {π'' : P'' ⟶ X''} {d : RelativeProjPoints B S hS π} {d' : RelativeProjPoints B S hS π'}
  {d'' : RelativeProjPoints B S hS π''}

/-- Lying over composes along two morphisms of relative Projs. -/
theorem LiesOverAlong.comp {h₁ : P'' ⟶ P'} {h₂ : P' ⟶ P} {T T' T'' : BigFppfOver B S hS}
    {f : yoneda.obj T ⟶ X} {f' : yoneda.obj T' ⟶ X'} {f'' : yoneda.obj T'' ⟶ X''}
    {y₁ : d''.fibre T'' f'' ⟶ d'.fibre T' f'} {y₂ : d'.fibre T' f' ⟶ d.fibre T f}
    {k₁ : T'' ⟶ T'} {k₂ : T' ⟶ T} (hy₁ : d''.LiesOverAlong d' h₁ y₁ k₁)
    (hy₂ : d'.LiesOverAlong d h₂ y₂ k₂) : d''.LiesOverAlong d (h₁ ≫ h₂) (y₁ ≫ y₂) (k₁ ≫ k₂) :=
  ⟨by rw [Category.assoc, hy₂.1, ← Category.assoc, hy₁.1, Category.assoc],
    by rw [Functor.map_comp, Category.assoc, hy₂.2, ← Category.assoc, hy₁.2, Category.assoc]⟩

end RelativeProjPoints

/-! ### The base change identification is natural in the scheme point -/

namespace RelativeProjSituation

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable (s : RelativeProjSituation.{u, m})
  (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)
  {T T' : BigFppfOver s.site s.base s.containsBase} (τ : T' ⟶ T) (f : yoneda.obj T ⟶ s.space.1)

/-- The two morphisms `T'_U ⟶ X` into the chart, through `T'` and through `U`, agree with the
morphism through `T`. -/
theorem map_alongPointToAtlas_comp_toSpace_comp :
    yoneda.map (Px.alongPointToAtlas (yoneda.map τ ≫ f)) ≫ Px.toSpace =
      yoneda.map (Px.alongPointToPoint (yoneda.map τ ≫ f) ≫ τ) ≫ f := by
  rw [Px.map_alongPointToAtlas_comp_toSpace, Functor.map_comp, Category.assoc]

/-- **The morphism of charts `T'_U = T' ×_X U ⟶ T_U = T ×_X U`** over `τ : T' ⟶ T`. -/
def alongPointChartMap :
    (Px.alongPoint (yoneda.map τ ≫ f)).U ⟶ (Px.alongPoint f).U :=
  Yoneda.fullyFaithful.preimage ((Px.isPullback_alongPoint f).lift
    (yoneda.map (Px.alongPointToAtlas (yoneda.map τ ≫ f)))
    (yoneda.map (Px.alongPointToPoint (yoneda.map τ ≫ f) ≫ τ))
    (s.map_alongPointToAtlas_comp_toSpace_comp Px τ f))

/-- The morphism of charts lies over the atlas. -/
theorem alongPointChartMap_comp_toAtlas :
    s.alongPointChartMap Px τ f ≫ Px.alongPointToAtlas f =
      Px.alongPointToAtlas (yoneda.map τ ≫ f) :=
  Yoneda.fullyFaithful.map_injective (by
    rw [Functor.map_comp, alongPointChartMap, Yoneda.fullyFaithful.map_preimage]
    exact (Px.isPullback_alongPoint f).lift_fst _ _ _)

/-- The morphism of charts lies over `τ`. -/
theorem alongPointChartMap_comp_toPoint :
    s.alongPointChartMap Px τ f ≫ Px.alongPointToPoint f =
      Px.alongPointToPoint (yoneda.map τ ≫ f) ≫ τ :=
  Yoneda.fullyFaithful.map_injective (by
    rw [Functor.map_comp, alongPointChartMap, Yoneda.fullyFaithful.map_preimage]
    exact (Px.isPullback_alongPoint f).lift_snd _ _ _)

/-- `AlgebraicGeometry.Space.RelativeProjSituation.alongPointChartMap_comp_toAtlas`, through the
identity of `T_U`. -/
theorem toAtlas_eq_alongPointChartMap_comp_id_comp :
    Px.alongPointToAtlas (yoneda.map τ ≫ f) =
      (s.alongPointChartMap Px τ f ≫ 𝟙 _) ≫ Px.alongPointToAtlas f :=
  (s.alongPointChartMap_comp_toAtlas Px τ f).symm.trans
    (congrArg (· ≫ Px.alongPointToAtlas f) (Category.comp_id _).symm)

/-- `AlgebraicGeometry.Space.RelativeProjSituation.alongPointChartMap_comp_toPoint`, through the
identity of `T_U`. -/
theorem toPoint_comp_eq_alongPointChartMap_comp_id_comp :
    Px.alongPointToPoint (yoneda.map τ ≫ f) ≫ τ =
      (s.alongPointChartMap Px τ f ≫ 𝟙 _) ≫ Px.alongPointToPoint f :=
  (s.alongPointChartMap_comp_toPoint Px τ f).symm.trans
    (congrArg (· ≫ Px.alongPointToPoint f) (Category.comp_id _).symm)

/-- **The morphism of relative Projs `Proj_{T'}(f'^*𝒜) ⟶ Proj_T(f^*𝒜)`** over `τ`, from the
cartesian square of `Proj_T(f^*𝒜) = T ×_X P`. -/
def pointRelativeProjMap :
    (s.pullback (s.schemePointHom T' (yoneda.map τ ≫ f))).relativeProjFunctor ⟶
      (s.pullback (s.schemePointHom T f)).relativeProjFunctor :=
  (s.isPullback_relativeProjBaseChangeHom (s.schemePointHom T f)).lift
    (s.relativeProjBaseChangeHom (s.schemePointHom T' (yoneda.map τ ≫ f)))
    ((s.pullback (s.schemePointHom T' (yoneda.map τ ≫ f))).relativeProjπ ≫ yoneda.map τ)
    ((s.relativeProjBaseChangeHom_comp_relativeProjπ _).trans (Category.assoc _ _ _).symm)

/-- The morphism of relative Projs over `τ` commutes with the structure morphisms. -/
theorem pointRelativeProjMap_comp_relativeProjπ :
    s.pointRelativeProjMap τ f ≫ (s.pullback (s.schemePointHom T f)).relativeProjπ =
      (s.pullback (s.schemePointHom T' (yoneda.map τ ≫ f))).relativeProjπ ≫ yoneda.map τ :=
  (s.isPullback_relativeProjBaseChangeHom (s.schemePointHom T f)).lift_snd _ _ _

/-- The morphism of relative Projs over `τ` commutes with the morphisms to `P`. -/
theorem pointRelativeProjMap_comp_relativeProjBaseChangeHom :
    s.pointRelativeProjMap τ f ≫ s.relativeProjBaseChangeHom (s.schemePointHom T f) =
      s.relativeProjBaseChangeHom (s.schemePointHom T' (yoneda.map τ ≫ f)) :=
  (s.isPullback_relativeProjBaseChangeHom (s.schemePointHom T f)).lift_fst _ _ _

/-- **The morphism of presenting schemes `T'_U ×_{T'} P'' ⟶ T_U ×_T P'`** over `τ`. -/
abbrev pointPresentationMap :
    RelativeProjPoints.fibre (B := s.site) (S := s.base) (hS := s.containsBase)
        (X := (representedAlgebraicSpace s.site s.base s.containsBase T').obj)
          (s.pullback (s.schemePointHom T' (yoneda.map τ ≫ f))).relativeProjPoints
        (Px.alongPoint (yoneda.map τ ≫ f)).U (Px.alongPoint (yoneda.map τ ≫ f)).toSpace ⟶
      RelativeProjPoints.fibre (B := s.site) (S := s.base) (hS := s.containsBase)
        (X := (representedAlgebraicSpace s.site s.base s.containsBase T).obj)
          (s.pullback (s.schemePointHom T f)).relativeProjPoints
        (Px.alongPoint f).U (Px.alongPoint f).toSpace :=
  RelativeProjPoints.fibreMapAlong (B := s.site) (S := s.base) (hS := s.containsBase) _ _ _
    (s.pointRelativeProjMap_comp_relativeProjπ τ f) (Px.alongPoint f).toSpace
    (Px.alongPoint (yoneda.map τ ≫ f)).toSpace (s.alongPointChartMap Px τ f)
    (by
      change yoneda.map _ ≫ yoneda.map _ = yoneda.map _ ≫ yoneda.map τ
      rw [← Functor.map_comp, ← Functor.map_comp, s.alongPointChartMap_comp_toPoint])

/-- The point `T_U ⟶ X` of the chart through `T`. -/
abbrev chartPoint : yoneda.obj (Px.alongPoint f).U ⟶ s.space.1 := (Px.alongPoint f).toSpace ≫ f

/-- The point of the chart `T_U` through `T`, along the identity. -/
theorem map_id_comp_chartPoint :
    yoneda.map (𝟙 (Px.alongPoint f).U) ≫ s.chartPoint Px f =
      (Px.alongPoint f).toSpace ≫ (s.schemePointHom T f).hom := by
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

/-- The point of the chart `T'_U` through `T`. -/
theorem map_comp_alongPointToPoint :
    yoneda.map (Px.alongPointToPoint (yoneda.map τ ≫ f) ≫ τ) ≫ f =
      (Px.alongPoint (yoneda.map τ ≫ f)).toSpace ≫
        (s.schemePointHom T' (yoneda.map τ ≫ f)).hom := by
  rw [Functor.map_comp, Category.assoc]
  rfl

/-- **The morphism `T_U ×_T P' ⟶ T_U ×_X P`** from the presenting scheme of `P'` to the base
change of `P` along the point of the chart, lying over the identity of `T_U` and `P' ⟶ P`. -/
abbrev chartFibreMap :
    RelativeProjPoints.fibre (B := s.site) (S := s.base) (hS := s.containsBase)
        (X := (representedAlgebraicSpace s.site s.base s.containsBase T).obj)
          (s.pullback (s.schemePointHom T f)).relativeProjPoints
        (Px.alongPoint f).U (Px.alongPoint f).toSpace ⟶
      s.relativeProjPoints.fibre (Px.alongPoint f).U (s.chartPoint Px f) :=
  RelativeProjPoints.fibreMapAlong (B := s.site) (S := s.base) (hS := s.containsBase) _ _ _
    (s.relativeProjBaseChangeHom_comp_relativeProjπ (s.schemePointHom T f)) (s.chartPoint Px f)
    (Px.alongPoint f).toSpace (𝟙 _) (s.map_id_comp_chartPoint Px f)

/-- The morphism `T_U ×_X P ⟶ U ×_X P` over the atlas. -/
abbrev chartAtlasMap :
    s.relativeProjPoints.fibre (Px.alongPoint f).U (s.chartPoint Px f) ⟶
      s.relativeProjPoints.fibre Px.U Px.toSpace :=
  s.relativeProjPoints.fibreMapOver (Px.alongPointToAtlas f)
    (Px.map_alongPointToAtlas_comp_toSpace' f)

/-- The morphism `T_U ×_X P ⟶ T ×_X P` over the projection to the point. -/
abbrev chartPointMap :
    s.relativeProjPoints.fibre (Px.alongPoint f).U (s.chartPoint Px f) ⟶
      s.relativeProjPoints.fibre T f :=
  s.relativeProjPoints.fibreMapOver (Px.alongPointToPoint f) rfl

/-- The comparison of twists along `y ≫ x`, for `x` a morphism of base changes of `P`, as a
morphism of quasi-coherent modules:
`AlgebraicGeometry.Space.RelativeProjSituation.baseChangeTwistSheafIso_comp_liesOver`. -/
theorem baseChangeTwistPieceComparison_comp_liesOver_hom
    {X' : AlgebraicSpaces s.site s.base s.containsBase} (g : X' ⟶ s.space)
    {U V W : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {v : yoneda.obj V ⟶ X'.1} {w : yoneda.obj W ⟶ s.space.1}
    (k : V ⟶ U) (k₀ : U ⟶ W) (hv : yoneda.map k ≫ u = v ≫ g.hom) (hu : yoneda.map k₀ ≫ w = u)
    (hv' : yoneda.map (k ≫ k₀) ≫ w = v ≫ g.hom)
    (y : (s.pullback g).relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u)
    (x : s.relativeProjPoints.fibre U u ⟶ s.relativeProjPoints.fibre W w)
    (hy : (s.pullback g).relativeProjPoints.LiesOverAlong s.relativeProjPoints
      (s.relativeProjBaseChangeHom g) y k) (hx : s.relativeProjPoints.LiesOver x k₀) (n : ℤ) :
    (s.baseChangeTwistPieceComparison g (k ≫ k₀) hv' (y ≫ x) (hy.comp_liesOver hx) n).hom =
      (quasicoherentPullbackCompIso s.site s.base s.containsBase y x
          (s.twistPieceQcoh W w n)).inv ≫
        quasicoherentPullbackMap s.site s.base s.containsBase y
          (s.twistPieceComparison k₀ hu x hx n).hom ≫
          (s.baseChangeTwistPieceComparison g k hv y hy n).hom :=
  ObjectProperty.hom_ext _
    ((s.baseChangeTwistSheafIso_comp_liesOver g k k₀ hv hu hv' y x hy hx n).trans
      ((congrArg (· ≫ _) (rfl : (Scheme.Modules.pullbackCongr
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map_comp y x)).hom.app
          ((Scheme.Modules.pullback (s.toRelativeProj W w)).obj
            ((Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra
              (s.shrink.pointAlgebra W w)).piece n)) = 𝟙 _)).trans
        (Category.id_comp _)))

/-- **The comparison of twists along a morphism of base changes factoring through a morphism of
base changes of `P`**: along `y₁ = y₀ ≫ x`, it is the transport, the contraction, the comparison of
twists of `P` along `x` pulled back along `y₀`, and the comparison along `y₀`. -/
theorem baseChangeTwistPieceComparison_hom_eq_of_eq_comp
    {X' : AlgebraicSpaces s.site s.base s.containsBase} (g : X' ⟶ s.space)
    {U V W : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {v : yoneda.obj V ⟶ X'.1} {w : yoneda.obj W ⟶ s.space.1}
    (k : V ⟶ U) (k₀ : U ⟶ W) (k₁ : V ⟶ W) (hv : yoneda.map k ≫ u = v ≫ g.hom)
    (hu : yoneda.map k₀ ≫ w = u) (hv₁ : yoneda.map k₁ ≫ w = v ≫ g.hom)
    (y : (s.pullback g).relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u)
    (x : s.relativeProjPoints.fibre U u ⟶ s.relativeProjPoints.fibre W w)
    (y₁ : (s.pullback g).relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre W w)
    (hy : (s.pullback g).relativeProjPoints.LiesOverAlong s.relativeProjPoints
      (s.relativeProjBaseChangeHom g) y k) (hx : s.relativeProjPoints.LiesOver x k₀)
    (hy₁ : (s.pullback g).relativeProjPoints.LiesOverAlong s.relativeProjPoints
      (s.relativeProjBaseChangeHom g) y₁ k₁) (e : y₁ = y ≫ x) (hk : k₁ = k ≫ k₀) (n : ℤ) :
    (s.baseChangeTwistPieceComparison g k₁ hv₁ y₁ hy₁ n).hom =
      quasicoherentPullbackEqToHom s.site s.base s.containsBase e (s.twistPieceQcoh W w n) ≫
        (quasicoherentPullbackCompIso s.site s.base s.containsBase y x
          (s.twistPieceQcoh W w n)).inv ≫
          quasicoherentPullbackMap s.site s.base s.containsBase y
            (s.twistPieceComparison k₀ hu x hx n).hom ≫
            (s.baseChangeTwistPieceComparison g k hv y hy n).hom :=
  (s.quasicoherentPullbackEqToHom_comp_baseChangeTwistPieceComparison_hom g
    (hv₂ := (hk ▸ hv₁ : yoneda.map (k ≫ k₀) ≫ w = v ≫ g.hom)) (hy₂ := hy.comp_liesOver hx) e hk
      n).symm.trans
    (congrArg (_ ≫ ·)
      (s.baseChangeTwistPieceComparison_comp_liesOver_hom g k k₀ hv hu _ y x hy hx n))

variable {y : s.relativeProjPoints.fibre T' (yoneda.map τ ≫ f) ⟶ s.relativeProjPoints.fibre T f}
  (hy : s.relativeProjPoints.LiesOver y τ)

/-- The morphism `T'_U ×_{T'} P'' ⟶ T_U ×_X P` through `T_U ×_T P'` lies over `T'_U ⟶ T_U` and
`P'' ⟶ P`. -/
theorem liesOverAlong_pointPresentationMap_comp_chartFibreMap :
    (s.pullback (s.schemePointHom T' (yoneda.map τ ≫ f))).relativeProjPoints.LiesOverAlong
      s.relativeProjPoints (s.relativeProjBaseChangeHom (s.schemePointHom T' (yoneda.map τ ≫ f)))
      (s.pointPresentationMap Px τ f ≫ s.chartFibreMap Px f) (s.alongPointChartMap Px τ f ≫ 𝟙 _) :=
  s.pointRelativeProjMap_comp_relativeProjBaseChangeHom τ f ▸
    (RelativeProjPoints.liesOverAlong_fibreMapAlong _ _ _ _ _).comp
      (RelativeProjPoints.liesOverAlong_fibreMapAlong _ _ _ _ _)

/-- The point of `T'_U` through `T_U`. -/
theorem map_comp_chartPoint :
    yoneda.map (s.alongPointChartMap Px τ f ≫ 𝟙 _) ≫ s.chartPoint Px f =
      (Px.alongPoint (yoneda.map τ ≫ f)).toSpace ≫
        (s.schemePointHom T' (yoneda.map τ ≫ f)).hom := by
  change yoneda.map (s.alongPointChartMap Px τ f ≫ 𝟙 _) ≫ yoneda.map (Px.alongPointToPoint f) ≫ f =
    yoneda.map (Px.alongPointToPoint (yoneda.map τ ≫ f)) ≫ yoneda.map τ ≫ f
  rw [Category.comp_id, ← Category.assoc, ← Functor.map_comp, s.alongPointChartMap_comp_toPoint,
    Functor.map_comp, Category.assoc]

/-- The chart morphism `T_U ×_T P' ⟶ U ×_X P` factors through `T_U ×_X P`. -/
theorem chartBaseChangeMap_eq_comp :
    s.chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f) (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f) = s.chartFibreMap Px f ≫ s.chartAtlasMap Px f :=
  (s.liesOverAlong_chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
      (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f)).eq
    ((RelativeProjPoints.liesOverAlong_fibreMapAlong _ _ _ _ _).comp_liesOver
      (s.relativeProjPoints.liesOver_fibreMapOver _ _)) (Category.id_comp _).symm

/-- The chart morphism `T_U ×_T P' ⟶ T ×_X P` factors through `T_U ×_X P`. -/
theorem pointChartMap_eq_comp :
    s.pointChartMap Px T f = s.chartFibreMap Px f ≫ s.chartPointMap Px f :=
  (s.liesOverAlong_pointChartMap Px T f).eq
    ((RelativeProjPoints.liesOverAlong_fibreMapAlong _ _ _ _ _).comp_liesOver
      (s.relativeProjPoints.liesOver_fibreMapOver _ _)) (Category.id_comp _).symm

/-- The chart morphism `T'_U ×_{T'} P'' ⟶ U ×_X P` factors through `T_U ×_X P`. -/
theorem chartBaseChangeMap_comp_eq_comp :
    s.chartBaseChangeMap (s.schemePointHom T' (yoneda.map τ ≫ f)) Px
        (Px.alongPoint (yoneda.map τ ≫ f)) (Px.alongPointToAtlas (yoneda.map τ ≫ f))
        (Px.map_alongPointToAtlas_comp_toSpace' (yoneda.map τ ≫ f)) =
      (s.pointPresentationMap Px τ f ≫ s.chartFibreMap Px f) ≫ s.chartAtlasMap Px f :=
  (s.liesOverAlong_chartBaseChangeMap (s.schemePointHom T' (yoneda.map τ ≫ f)) Px
      (Px.alongPoint (yoneda.map τ ≫ f)) (Px.alongPointToAtlas (yoneda.map τ ≫ f))
      (Px.map_alongPointToAtlas_comp_toSpace' (yoneda.map τ ≫ f))).eq
    ((s.liesOverAlong_pointPresentationMap_comp_chartFibreMap Px τ f).comp_liesOver
      (s.relativeProjPoints.liesOver_fibreMapOver _ _))
    (s.toAtlas_eq_alongPointChartMap_comp_id_comp Px τ f)

include hy in
/-- The chart morphism `T'_U ×_{T'} P'' ⟶ T' ×_X P`, followed by `y`, factors through
`T_U ×_X P`. -/
theorem pointChartMap_comp_eq_comp :
    s.pointChartMap Px T' (yoneda.map τ ≫ f) ≫ y =
      (s.pointPresentationMap Px τ f ≫ s.chartFibreMap Px f) ≫ s.chartPointMap Px f :=
  ((s.liesOverAlong_pointChartMap Px T' (yoneda.map τ ≫ f)).comp_liesOver hy).eq
    ((s.liesOverAlong_pointPresentationMap_comp_chartFibreMap Px τ f).comp_liesOver
      (s.relativeProjPoints.liesOver_fibreMapOver _ _))
    (s.toPoint_comp_eq_alongPointChartMap_comp_id_comp Px τ f)

include hy in
/-- The morphism of presenting schemes over `τ` intertwines the two chart morphisms to `T' ×_X P`
and `T ×_X P` with `y`. -/
theorem pointChartMap_comp_eq_pointPresentationMap_comp :
    s.pointChartMap Px T' (yoneda.map τ ≫ f) ≫ y =
      s.pointPresentationMap Px τ f ≫ s.pointChartMap Px T f :=
  (s.pointChartMap_comp_eq_comp Px τ f hy).trans ((Category.assoc _ _ _).trans
    (congrArg (s.pointPresentationMap Px τ f ≫ ·) (s.pointChartMap_eq_comp Px f).symm))

/-- The morphism of presenting schemes over `τ` intertwines the two chart morphisms to
`U ×_X P`. -/
theorem pointPresentationMap_comp_chartBaseChangeMap :
    s.pointPresentationMap Px τ f ≫
        s.chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f) (Px.alongPointToAtlas f)
          (Px.map_alongPointToAtlas_comp_toSpace' f) =
      s.chartBaseChangeMap (s.schemePointHom T' (yoneda.map τ ≫ f)) Px
        (Px.alongPoint (yoneda.map τ ≫ f)) (Px.alongPointToAtlas (yoneda.map τ ≫ f))
        (Px.map_alongPointToAtlas_comp_toSpace' (yoneda.map τ ≫ f)) :=
  (congrArg (s.pointPresentationMap Px τ f ≫ ·) (s.chartBaseChangeMap_eq_comp Px f)).trans
    ((Category.assoc _ _ _).symm.trans (s.chartBaseChangeMap_comp_eq_comp Px τ f).symm)

include hy in
/-- **The compatibility of the comparisons of twists of Tag 01O3 on the two charts** with the
comparison of twists along `y : T' ×_X P ⟶ T ×_X P`: the comparison `Θ'` along
`T'_U ×_{T'} P'' ⟶ U ×_X P` is the pullback along `T'_U ×_{T'} P'' ⟶ T_U ×_T P'` of the ratio of
the comparisons along `T_U ×_T P' ⟶ U ×_X P` and `T_U ×_T P' ⟶ T ×_X P`, followed by the comparison
along `y` and the comparison along `T'_U ×_{T'} P'' ⟶ T' ×_X P`. -/
theorem chartTwistComparison_pointNatural (n : ℤ) :
    type_of% (comparison_eq_pullback_ratio s.site s.base s.containsBase
      (s.pointPresentationMap Px τ f) (s.chartFibreMap Px f) (s.chartAtlasMap Px f)
      (s.chartPointMap Px f) (s.pointChartMap Px T' (yoneda.map τ ≫ f)) y
      (s.twistPieceComparison (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f)
        (s.chartAtlasMap Px f) (s.relativeProjPoints.liesOver_fibreMapOver _ _) n)
      (s.twistPieceComparison (Px.alongPointToPoint f) rfl (s.chartPointMap Px f)
        (s.relativeProjPoints.liesOver_fibreMapOver _ _) n)
      (s.baseChangeTwistPieceComparison (s.schemePointHom T f) (𝟙 _) (s.map_id_comp_chartPoint Px f)
        (s.chartFibreMap Px f) (RelativeProjPoints.liesOverAlong_fibreMapAlong _ _ _ _ _) n)
      (s.baseChangeTwistPieceComparison (s.schemePointHom T' (yoneda.map τ ≫ f))
        (s.alongPointChartMap Px τ f ≫ 𝟙 _) (s.map_comp_chartPoint Px τ f)
        (s.pointPresentationMap Px τ f ≫ s.chartFibreMap Px f)
        (s.liesOverAlong_pointPresentationMap_comp_chartFibreMap Px τ f) n)
      (s.twistPieceComparison τ rfl y hy n) (s.pointChartTwistComparison Px T' (yoneda.map τ ≫ f) n)
      (s.chartTwistComparison (s.schemePointHom T f) Px (Px.alongPoint f) (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f) n)
      (s.pointChartTwistComparison Px T f n)
      (s.chartTwistComparison (s.schemePointHom T' (yoneda.map τ ≫ f)) Px
        (Px.alongPoint (yoneda.map τ ≫ f)) (Px.alongPointToAtlas (yoneda.map τ ≫ f))
        (Px.map_alongPointToAtlas_comp_toSpace' (yoneda.map τ ≫ f)) n)
      (s.chartBaseChangeMap_eq_comp Px f) (s.pointChartMap_eq_comp Px f)
      (s.chartBaseChangeMap_comp_eq_comp Px τ f) (s.pointChartMap_comp_eq_comp Px τ f hy)
      (s.pointChartMap_comp_eq_pointPresentationMap_comp Px τ f hy)
      (s.pointPresentationMap_comp_chartBaseChangeMap Px τ f)
      (s.baseChangeTwistPieceComparison_hom_eq_of_eq_comp _ _ _ _ _ _ _ _ _ _ _ _ _
        (s.chartBaseChangeMap_eq_comp Px f) (Category.id_comp _).symm n)
      (s.baseChangeTwistPieceComparison_hom_eq_of_eq_comp _ _ _ _ _ _ _ _ _ _ _ _ _
        (s.pointChartMap_eq_comp Px f) (Category.id_comp _).symm n)
      (s.baseChangeTwistPieceComparison_hom_eq_of_eq_comp _ _ _ _ _ _ _ _ _ _ _ _ _
        (s.chartBaseChangeMap_comp_eq_comp Px τ f)
        (s.toAtlas_eq_alongPointChartMap_comp_id_comp Px τ f) n)
      ((s.baseChangeTwistPieceComparison_comp_liesOver_hom (s.schemePointHom T' (yoneda.map τ ≫ f))
          (Px.alongPointToPoint (yoneda.map τ ≫ f)) τ rfl rfl (s.map_comp_alongPointToPoint Px τ f)
          (s.pointChartMap Px T' (yoneda.map τ ≫ f)) y
          (s.liesOverAlong_pointChartMap Px T' (yoneda.map τ ≫ f)) hy n).symm.trans
        (s.baseChangeTwistPieceComparison_hom_eq_of_eq_comp _ _ _ _ _ _ _ _ _ _ _ _ _
          (s.pointChartMap_comp_eq_comp Px τ f hy)
          (s.toPoint_comp_eq_alongPointChartMap_comp_id_comp Px τ f) n))) :=
  comparison_eq_pullback_ratio s.site s.base s.containsBase
      (s.pointPresentationMap Px τ f) (s.chartFibreMap Px f) (s.chartAtlasMap Px f)
      (s.chartPointMap Px f) (s.pointChartMap Px T' (yoneda.map τ ≫ f)) y
      (s.twistPieceComparison (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f)
        (s.chartAtlasMap Px f) (s.relativeProjPoints.liesOver_fibreMapOver _ _) n)
      (s.twistPieceComparison (Px.alongPointToPoint f) rfl (s.chartPointMap Px f)
        (s.relativeProjPoints.liesOver_fibreMapOver _ _) n)
      (s.baseChangeTwistPieceComparison (s.schemePointHom T f) (𝟙 _) (s.map_id_comp_chartPoint Px f)
        (s.chartFibreMap Px f) (RelativeProjPoints.liesOverAlong_fibreMapAlong _ _ _ _ _) n)
      (s.baseChangeTwistPieceComparison (s.schemePointHom T' (yoneda.map τ ≫ f))
        (s.alongPointChartMap Px τ f ≫ 𝟙 _) (s.map_comp_chartPoint Px τ f)
        (s.pointPresentationMap Px τ f ≫ s.chartFibreMap Px f)
        (s.liesOverAlong_pointPresentationMap_comp_chartFibreMap Px τ f) n)
      (s.twistPieceComparison τ rfl y hy n) (s.pointChartTwistComparison Px T' (yoneda.map τ ≫ f) n)
      (s.chartTwistComparison (s.schemePointHom T f) Px (Px.alongPoint f) (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f) n)
      (s.pointChartTwistComparison Px T f n)
      (s.chartTwistComparison (s.schemePointHom T' (yoneda.map τ ≫ f)) Px
        (Px.alongPoint (yoneda.map τ ≫ f)) (Px.alongPointToAtlas (yoneda.map τ ≫ f))
        (Px.map_alongPointToAtlas_comp_toSpace' (yoneda.map τ ≫ f)) n)
      (s.chartBaseChangeMap_eq_comp Px f) (s.pointChartMap_eq_comp Px f)
      (s.chartBaseChangeMap_comp_eq_comp Px τ f) (s.pointChartMap_comp_eq_comp Px τ f hy)
      (s.pointChartMap_comp_eq_pointPresentationMap_comp Px τ f hy)
      (s.pointPresentationMap_comp_chartBaseChangeMap Px τ f)
      (s.baseChangeTwistPieceComparison_hom_eq_of_eq_comp _ _ _ _ _ _ _ _ _ _ _ _ _
        (s.chartBaseChangeMap_eq_comp Px f) (Category.id_comp _).symm n)
      (s.baseChangeTwistPieceComparison_hom_eq_of_eq_comp _ _ _ _ _ _ _ _ _ _ _ _ _
        (s.pointChartMap_eq_comp Px f) (Category.id_comp _).symm n)
      (s.baseChangeTwistPieceComparison_hom_eq_of_eq_comp _ _ _ _ _ _ _ _ _ _ _ _ _
        (s.chartBaseChangeMap_comp_eq_comp Px τ f)
        (s.toAtlas_eq_alongPointChartMap_comp_id_comp Px τ f) n)
      ((s.baseChangeTwistPieceComparison_comp_liesOver_hom (s.schemePointHom T' (yoneda.map τ ≫ f))
          (Px.alongPointToPoint (yoneda.map τ ≫ f)) τ rfl rfl (s.map_comp_alongPointToPoint Px τ f)
          (s.pointChartMap Px T' (yoneda.map τ ≫ f)) y
          (s.liesOverAlong_pointChartMap Px T' (yoneda.map τ ≫ f)) hy n).symm.trans
        (s.baseChangeTwistPieceComparison_hom_eq_of_eq_comp _ _ _ _ _ _ _ _ _ _ _ _ _
          (s.pointChartMap_comp_eq_comp Px τ f hy)
          (s.toPoint_comp_eq_alongPointChartMap_comp_id_comp Px τ f) n))

include hy in
/-- The morphism `T' ×_X P ⟶ T ×_X P` lying over `τ` commutes with the base changes to `P`. -/
theorem representedSpaceMap_comp_fibreToSpaceHom :
    representedSpaceMap s.site s.base s.containsBase y ≫ s.fibreToSpaceHom T f =
      s.fibreToSpaceHom T' (yoneda.map τ ≫ f) :=
  ObjectProperty.hom_ext _ hy.2

include hy in
/-- The chart morphism `T'_U ×_{T'} P'' ⟶ T' ×_X P`, followed by `y` and the base change to `P`,
is the chart morphism to `U ×_X P` followed by the atlas of `P`, as morphisms of represented
algebraic spaces. -/
theorem representedSpaceMap_pointChartMap_comp :
    representedSpaceMap s.site s.base s.containsBase (s.pointChartMap Px T' (yoneda.map τ ≫ f)) ≫
        (representedSpaceMap s.site s.base s.containsBase y ≫ s.fibreToSpaceHom T f) =
      representedSpaceMap s.site s.base s.containsBase
          (s.chartBaseChangeMap (s.schemePointHom T' (yoneda.map τ ≫ f)) Px
            (Px.alongPoint (yoneda.map τ ≫ f)) (Px.alongPointToAtlas (yoneda.map τ ≫ f))
            (Px.map_alongPointToAtlas_comp_toSpace' (yoneda.map τ ≫ f))) ≫
        presentationAtlas
          (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor) :=
  ObjectProperty.hom_ext _ ((congrArg (yoneda.map (s.pointChartMap Px T' (yoneda.map τ ≫ f)) ≫ ·)
    hy.2).trans ((s.liesOverAlong_pointChartMap Px T' (yoneda.map τ ≫ f)).2.trans
      (s.liesOverAlong_chartBaseChangeMap (s.schemePointHom T' (yoneda.map τ ≫ f)) Px
        (Px.alongPoint (yoneda.map τ ≫ f)) (Px.alongPointToAtlas (yoneda.map τ ≫ f))
        (Px.map_alongPointToAtlas_comp_toSpace' (yoneda.map τ ≫ f))).2.symm))

include hy in
/-- **The base change identification of Stacks 084D is natural in the scheme point.**  For a
morphism `τ : T' ⟶ T` of the site, a scheme point `f : T ⟶ X` and a morphism
`y : T' ×_X P ⟶ T ×_X P` of base changes lying over `τ`, the identification
`(T' ×_X P ⟶ P)^*𝒪_P(n) ≅ 𝒪(n)^a` at `f ∘ τ` is the identification at `f` pulled back along `y`:
the transport along `(T' ×_X P ⟶ P) = y ≫ (T ×_X P ⟶ P)`, the comparison of Stacks 03LU, the
inverse image along `y` of the identification at `f`, Stacks 03DX (2), and the module attached to
the comparison `y^*𝒪(n) ≅ 𝒪(n)` of twists of Tag 01O3. -/
theorem fibreToSpaceTwistModuleIso_comp (n : ℤ) :
    s.fibreToSpaceTwistModuleIso Px T' (yoneda.map τ ≫ f) n =
      eqToIso (congrArg (fun k : (⟨yoneda.obj (s.relativeProjPoints.fibre T' (yoneda.map τ ≫ f)),
            isAlgebraicSpace_yoneda s.site s.base s.containsBase _⟩ :
            AlgebraicSpaces s.site s.base s.containsBase) ⟶
              ⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ =>
          (modulePullback s.site s.base s.containsBase k).obj (s.twistModule Px n).obj)
          (s.representedSpaceMap_comp_fibreToSpaceHom τ f hy).symm) ≪≫
        attachedModuleIsoPullback
          (X := ⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩)
          (s.twistModule Px n).obj (s.fibreToSpaceHom T f) y
          (s.fibreToSpaceTwistModuleIso Px T f n) (s.twistPieceComparison τ rfl y hy n) :=
  RelativeProjPoints.pullbackTransitionCompatibleIso_comp
      (XA' := representedAlgebraicSpace s.site s.base s.containsBase T)
      (XA₂ := representedAlgebraicSpace s.site s.base s.containsBase T')
      (dA := s.relativeProjPoints) (dA' := (s.pullback (s.schemePointHom T f)).relativeProjPoints)
      (dA₂ := (s.pullback (s.schemePointHom T' (yoneda.map τ ≫ f))).relativeProjPoints)
      (hA := s.relativeProjBaseChangeHom (s.schemePointHom T f))
      (hA₂ := s.relativeProjBaseChangeHom (s.schemePointHom T' (yoneda.map τ ≫ f)))
      Px
      (Px.alongPoint f)
      (Px.alongPoint (yoneda.map τ ≫ f))
      s.isAlgebraicSpace_relativeProjFunctor
      (s.isAlgebraicSpace_pointRelativeProjFunctor T f)
      (s.isAlgebraicSpace_pointRelativeProjFunctor T' (yoneda.map τ ≫ f))
      (Px.alongPointRelationMap_comp_target f)
      (Px.alongPointRelationMap_comp_source f)
      (s.chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f) (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f))
      (s.liesOverAlong_pointChartBaseChangeMap Px T f)
      (s.relationBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f) (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f) (Px.alongPointRelationMap f)
        (Px.alongPointRelationMap_comp_target f))
      (s.liesOverAlong_pointRelationBaseChangeMap Px T f)
      (Px.alongPointRelationMap_comp_target (yoneda.map τ ≫ f))
      (Px.alongPointRelationMap_comp_source (yoneda.map τ ≫ f))
      (s.chartBaseChangeMap (s.schemePointHom T' (yoneda.map τ ≫ f))
        Px (Px.alongPoint (yoneda.map τ ≫ f))
        (Px.alongPointToAtlas (yoneda.map τ ≫ f))
        (Px.map_alongPointToAtlas_comp_toSpace' (yoneda.map τ ≫ f)))
      (s.liesOverAlong_pointChartBaseChangeMap Px T' (yoneda.map τ ≫ f))
      (s.relationBaseChangeMap (s.schemePointHom T' (yoneda.map τ ≫ f))
        Px (Px.alongPoint (yoneda.map τ ≫ f))
        (Px.alongPointToAtlas (yoneda.map τ ≫ f))
        (Px.map_alongPointToAtlas_comp_toSpace' (yoneda.map τ ≫ f))
        (Px.alongPointRelationMap (yoneda.map τ ≫ f))
        (Px.alongPointRelationMap_comp_target (yoneda.map τ ≫ f)))
      (s.liesOverAlong_pointRelationBaseChangeMap Px T' (yoneda.map τ ≫ f))
      (presentationDescendedModule
        (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)
        (s.twistPieceQcoh Px.U Px.toSpace n) (s.twistTransition Px n)
        (s.presentationSchemeCocycle_twistTransition Px n)
        (s.presentationSchemeUnit_twistTransition Px n))
      (s.twistTransition Px n)
      (presentationDescendedModuleChartIso
        (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)
        (s.twistPieceQcoh Px.U Px.toSpace n) (s.twistTransition Px n)
        (s.presentationSchemeCocycle_twistTransition Px n)
        (s.presentationSchemeUnit_twistTransition Px n))
      (s.presentationDescendedModuleChartIso_comm_twistTransition Px n)
      ((s.pullback (s.schemePointHom T f)).twistTransition (Px.alongPoint f) n)
      (s.chartTwistComparison (s.schemePointHom T f) Px (Px.alongPoint f) (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f) n)
      (s.pullbackTransitionCompatible_pointChartBaseChangeMap Px T f n)
      (s.pointBaseChangeIso T f)
      (s.pointChartMap Px T f)
      (s.map_pointChartMap Px T f)
      (s.fibreToSpaceHom T f)
      (s.presentationAtlas_ofIsoYoneda_comp_fibreToSpaceHom Px T f)
      (s.twistPieceQcoh T f n)
      (s.pointChartTwistComparison Px T f n)
      (s.canonicalSchemeTransition_pointChartTwistComparison Px T f n)
      ((s.pullback (s.schemePointHom T' (yoneda.map τ ≫ f))).twistTransition
        (Px.alongPoint (yoneda.map τ ≫ f)) n)
      (s.chartTwistComparison (s.schemePointHom T' (yoneda.map τ ≫ f))
        Px (Px.alongPoint (yoneda.map τ ≫ f))
        (Px.alongPointToAtlas (yoneda.map τ ≫ f))
        (Px.map_alongPointToAtlas_comp_toSpace' (yoneda.map τ ≫ f)) n)
      (s.pullbackTransitionCompatible_pointChartBaseChangeMap Px T' (yoneda.map τ ≫ f) n)
      (s.pointBaseChangeIso T' (yoneda.map τ ≫ f))
      (s.pointChartMap Px T' (yoneda.map τ ≫ f))
      (s.map_pointChartMap Px T' (yoneda.map τ ≫ f))
      (s.fibreToSpaceHom T' (yoneda.map τ ≫ f))
      (s.presentationAtlas_ofIsoYoneda_comp_fibreToSpaceHom Px T' (yoneda.map τ ≫ f))
      (s.twistPieceQcoh T' (yoneda.map τ ≫ f) n)
      (s.pointChartTwistComparison Px T' (yoneda.map τ ≫ f) n)
      (s.canonicalSchemeTransition_pointChartTwistComparison Px T' (yoneda.map τ ≫ f) n)
      y
      (s.representedSpaceMap_comp_fibreToSpaceHom τ f hy)
      (s.twistPieceComparison τ rfl y hy n)
      (s.pointPresentationMap Px τ f)
      (s.pointChartMap_comp_eq_pointPresentationMap_comp Px τ f hy)
      (s.pointPresentationMap_comp_chartBaseChangeMap Px τ f)
      (s.chartTwistComparison_pointNatural Px τ f hy n)

end RelativeProjSituation

end AlgebraicGeometry.Space

end
