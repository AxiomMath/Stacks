module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativeInverseImageComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorAlongAComposite
public import StacksFrontier.Topology.Sheaves.RingedSpace.Thickening

/-!
# The comparison `p^{-1}𝓕 ⟶ p^*𝓕` read through `τ^* ⊣ τ_*`

Let `p : W ⟶ X` and `a : X ⟶ S` be morphisms of schemes, write `τ_W : W ⟶ (W, (p ∘ a)^{-1}𝒪_S)`
and `τ_X : X ⟶ (X, a^{-1}𝒪_S)` for the identity-on-spaces morphisms of ringed spaces and `p'` for
the canonical morphism `(W, (p ∘ a)^{-1}𝒪_S) ⟶ (X, a^{-1}𝒪_S)`, so that `τ_W ≫ p' = p ≫ τ_X`.
The comparison `p'^*τ_{X,*}𝓕 ⟶ τ_{W,*}p^*𝓕` of
`Stacks.DeRhamDirectImage.relativeInverseImageToPullback` is the transpose along
`τ_W^* ⊣ τ_{W,*}` of the composite

`τ_W^*p'^*τ_{X,*}𝓕 ≅ (τ_W ≫ p')^*τ_{X,*}𝓕 = (p ≫ τ_X)^*τ_{X,*}𝓕 ≅ p^*τ_X^*τ_{X,*}𝓕 ⟶ p^*𝓕`

of the composition isomorphisms of Stacks 0097 and the counit of `τ_X^* ⊣ τ_{X,*}`.

## Main results

* `Stacks.DeRhamDirectImage.modulePullbackComp_homEquiv`: the transposition coherence of the
  composition isomorphism for pullback of modules.
* `Stacks.DeRhamDirectImage.pullback_relativeInverseImageToPullback_counit`: the statement above.

## References

* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 0097](https://stacks.math.columbia.edu/tag/0097)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open _root_.AlgebraicGeometry
open RingedSpaceModuleAdjunction

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.DeRhamDirectImage

section Coherence

variable {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The chase behind `modulePullbackComp_homEquiv`, every object and morphism a variable. -/
private theorem chase_unit {C : Type*} [Category C] {a c d e f' g' : C}
    {cu : a ⟶ c} {Cc : c ⟶ d} {Cφ : d ⟶ e} {pch : e ⟶ f'} {ufg : a ⟶ g'} {pci : g' ⟶ d}
    {Fφ : g' ⟶ f'} {pciN : f' ⟶ e} (_ : True) (_ : True)
    (hu : ufg ≫ pci = cu ≫ Cc) (hn : Fφ ≫ pciN = pci ≫ Cφ) (hinv : pciN ≫ pch = 𝟙 f') :
    (cu ≫ Cc ≫ Cφ) ≫ pch = ufg ≫ Fφ := by
  rw [← Category.assoc cu, ← hu, Category.assoc, Category.assoc, ← Category.assoc pci, ← hn,
    Category.assoc, hinv, Category.comp_id]

/-- **The transposition coherence of the composition isomorphism for pullback of modules**:
successive transposition along `g^* ⊣ g_*` and `f^* ⊣ f_*`, followed by the composition
isomorphism of pushforwards, is transposition along `(f ≫ g)^* ⊣ (f ≫ g)_*`. -/
theorem modulePullbackComp_homEquiv (M : SheafOfModules.{u} (structureSheafRing Z))
    (N : SheafOfModules.{u} (structureSheafRing X))
    (φ : (modulePullback (f ≫ g)).obj M ⟶ N) :
    (modulePullbackPushforwardAdjunction g).homEquiv _ _
        ((modulePullbackPushforwardAdjunction f).homEquiv _ _
          ((Stacks.DerivedPullback.Composition.modulePullbackComp f g).hom.app M ≫ φ)) ≫
      (modulePushforwardComp f g).hom.app N =
    (modulePullbackPushforwardAdjunction (f ≫ g)).homEquiv M N φ := by
  have e1 : (modulePullbackPushforwardAdjunction g).homEquiv _ _
        ((modulePullbackPushforwardAdjunction f).homEquiv _ _
          ((Stacks.DerivedPullback.Composition.modulePullbackComp f g).hom.app M ≫ φ)) =
      ((modulePullbackPushforwardAdjunction g).comp
          (modulePullbackPushforwardAdjunction f)).unit.app M ≫
        (modulePushforward f ⋙ modulePushforward g).map
          ((Stacks.DerivedPullback.Composition.modulePullbackComp f g).hom.app M ≫ φ) := by
    have e0 : ((modulePullbackPushforwardAdjunction g).comp
          (modulePullbackPushforwardAdjunction f)).homEquiv M N
          ((Stacks.DerivedPullback.Composition.modulePullbackComp f g).hom.app M ≫ φ) =
        (modulePullbackPushforwardAdjunction g).homEquiv _ _
          ((modulePullbackPushforwardAdjunction f).homEquiv _ _
            ((Stacks.DerivedPullback.Composition.modulePullbackComp f g).hom.app M ≫ φ)) := by
      rw [Adjunction.comp_homEquiv]
      rfl
    exact e0.symm.trans (Adjunction.homEquiv_unit _ _ _ _)
  rw [e1, Functor.map_comp, (modulePullbackPushforwardAdjunction (f ≫ g)).homEquiv_unit]
  exact chase_unit trivial trivial
    (Stacks.PullbackTensorComposition.modulePullbackComp_unit f g M)
    ((modulePushforwardComp f g).inv.naturality φ)
    ((modulePushforwardComp f g).inv_hom_id_app N)

/-- Transposition along `g^* ⊣ g_*` transported along an equality of morphisms. -/
theorem modulePullback_homEquiv_eqToHom {g₁ g₂ : X ⟶ Y} (h : g₁ = g₂)
    (M : SheafOfModules.{u} (structureSheafRing Y))
    (N : SheafOfModules.{u} (structureSheafRing X)) (φ : (modulePullback g₂).obj M ⟶ N) :
    (modulePullbackPushforwardAdjunction g₁).homEquiv M N
        (eqToHom (congrArg (fun z : X ⟶ Y => (modulePullback z).obj M) h) ≫ φ) =
      (modulePullbackPushforwardAdjunction g₂).homEquiv M N φ ≫
        eqToHom (congrArg (fun z : X ⟶ Y => (modulePushforward z).obj N) h.symm) := by
  subst h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

end Coherence

section Leg

/-- The double transpose of `L₂` of a counit is `R₁` of a unit. -/
private theorem homEquiv_homEquiv_map_counit {A B C : Type*} [Category A] [Category B]
    [Category C] {L₁ : A ⥤ B} {R₁ : B ⥤ A} (adj₁ : L₁ ⊣ R₁) {L₂ : B ⥤ C} {R₂ : C ⥤ B}
    (adj₂ : L₂ ⊣ R₂) (F : B) :
    adj₁.homEquiv _ _ (adj₂.homEquiv _ _ (L₂.map (adj₁.counit.app F))) =
      R₁.map (adj₂.unit.app F) := by
  have h : adj₂.homEquiv (L₁.obj (R₁.obj F)) (L₂.obj F) (L₂.map (adj₁.counit.app F)) =
      adj₁.counit.app F ≫ adj₂.unit.app F :=
    (Adjunction.homEquiv_unit _ _ _ _).trans (adj₂.unit.naturality (adj₁.counit.app F)).symm
  have h' : adj₁.unit.app (R₁.obj F) ≫ R₁.map (adj₁.counit.app F ≫ adj₂.unit.app F) =
      R₁.map (adj₂.unit.app F) := by
    rw [Functor.map_comp, ← Category.assoc, adj₁.right_triangle_components]
    exact Category.id_comp _
  exact (congrArg (adj₁.homEquiv _ _) h).trans ((Adjunction.homEquiv_unit _ _ _ _).trans h')

/-- A four-step rewriting chain, every object and morphism a variable. -/
private theorem chase4 {C : Type*} [Category C] {a b c d e : C} {x x' : a ⟶ b} {pc : b ⟶ c}
    {y₃ : a ⟶ c} {ee : c ⟶ d} {y₂ : a ⟶ d} {pci : d ⟶ e} {z : a ⟶ e} (h4 : x' = x)
    (h3 : x' ≫ pc = y₃) (h2 : y₂ = y₃ ≫ ee) (h1 : z = y₂ ≫ pci) :
    ((x ≫ pc) ≫ ee) ≫ pci = z := by
  rw [← h4, h3, ← h2, h1]

variable {W X S : Scheme.{u}} (p : W ⟶ X) (a : X ⟶ S)

/-- **The comparison `p'^*τ_{X,*}𝓕 ⟶ τ_{W,*}p^*𝓕` is the transpose of the crossing leg.**
`τ_W^*` of `Stacks.DeRhamDirectImage.relativeInverseImageToPullback`, followed by the counit of
`τ_W^* ⊣ τ_{W,*}`, is the composition isomorphism for `(τ_W, p')`, the transport along
`τ_W ≫ p' = p ≫ τ_X`, the inverse composition isomorphism for `(p, τ_X)` and `p^*` of the counit
of `τ_X^* ⊣ τ_{X,*}`. -/
theorem pullback_relativeInverseImageToPullback_counit (F : X.Modules) :
    (modulePullback (toInverseImageBase (p ≫ a))).map (relativeInverseImageToPullback p a F) ≫
        (modulePullbackPushforwardAdjunction (toInverseImageBase (p ≫ a))).counit.app
          ((modulePullback p.toLRSHom.toShHom).obj F) =
      (Stacks.DerivedPullback.Composition.modulePullbackComp (toInverseImageBase (p ≫ a))
          (relativeInverseImageProjection p a)).hom.app
          ((modulePushforward (toInverseImageBase a)).obj F) ≫
        eqToHom (congrArg (fun z : W.toRingedSpace ⟶ inverseImageBase a =>
          (modulePullback z).obj ((modulePushforward (toInverseImageBase a)).obj F))
          (toInverseImageBase_comp_relativeInverseImageProjection p a)) ≫
        (Stacks.DerivedPullback.Composition.modulePullbackComp p.toLRSHom.toShHom
          (toInverseImageBase a)).inv.app ((modulePushforward (toInverseImageBase a)).obj F) ≫
        (modulePullback p.toLRSHom.toShHom).map
          ((modulePullbackPushforwardAdjunction (toInverseImageBase a)).counit.app F) := by
  apply ((modulePullbackPushforwardAdjunction (toInverseImageBase (p ≫ a))).homEquiv _ _).injective
  apply ((modulePullbackPushforwardAdjunction (relativeInverseImageProjection p a)).homEquiv
    _ _).injective
  have hL : (modulePullbackPushforwardAdjunction (toInverseImageBase (p ≫ a))).homEquiv _ _
      ((modulePullback (toInverseImageBase (p ≫ a))).map (relativeInverseImageToPullback p a F) ≫
        (modulePullbackPushforwardAdjunction (toInverseImageBase (p ≫ a))).counit.app
          ((modulePullback p.toLRSHom.toShHom).obj F)) = relativeInverseImageToPullback p a F :=
    (congrArg _ (Adjunction.homEquiv_counit _ _ _ _).symm).trans (Equiv.apply_symm_apply _ _)
  have hR1 := (Iso.eq_comp_inv ((modulePushforwardComp (toInverseImageBase (p ≫ a))
      (relativeInverseImageProjection p a)).app ((modulePullback p.toLRSHom.toShHom).obj F))).mpr
    (modulePullbackComp_homEquiv (toInverseImageBase (p ≫ a)) (relativeInverseImageProjection p a)
      ((modulePushforward (toInverseImageBase a)).obj F)
      ((modulePullback p.toLRSHom.toShHom).obj F)
      (eqToHom (congrArg (fun z : W.toRingedSpace ⟶ inverseImageBase a =>
          (modulePullback z).obj ((modulePushforward (toInverseImageBase a)).obj F))
          (toInverseImageBase_comp_relativeInverseImageProjection p a)) ≫
        (Stacks.DerivedPullback.Composition.modulePullbackComp p.toLRSHom.toShHom
          (toInverseImageBase a)).inv.app ((modulePushforward (toInverseImageBase a)).obj F) ≫
        (modulePullback p.toLRSHom.toShHom).map
          ((modulePullbackPushforwardAdjunction (toInverseImageBase a)).counit.app F)))
  have hR2 := modulePullback_homEquiv_eqToHom
    (toInverseImageBase_comp_relativeInverseImageProjection p a)
    ((modulePushforward (toInverseImageBase a)).obj F) ((modulePullback p.toLRSHom.toShHom).obj F)
    ((Stacks.DerivedPullback.Composition.modulePullbackComp p.toLRSHom.toShHom
      (toInverseImageBase a)).inv.app ((modulePushforward (toInverseImageBase a)).obj F) ≫
      (modulePullback p.toLRSHom.toShHom).map
        ((modulePullbackPushforwardAdjunction (toInverseImageBase a)).counit.app F))
  have hR3 := modulePullbackComp_homEquiv p.toLRSHom.toShHom (toInverseImageBase a)
    ((modulePushforward (toInverseImageBase a)).obj F) ((modulePullback p.toLRSHom.toShHom).obj F)
    ((Stacks.DerivedPullback.Composition.modulePullbackComp p.toLRSHom.toShHom
      (toInverseImageBase a)).inv.app ((modulePushforward (toInverseImageBase a)).obj F) ≫
      (modulePullback p.toLRSHom.toShHom).map
        ((modulePullbackPushforwardAdjunction (toInverseImageBase a)).counit.app F))
  rw [Iso.hom_inv_id_app_assoc] at hR3
  have hR4 := homEquiv_homEquiv_map_counit
    (modulePullbackPushforwardAdjunction (toInverseImageBase a))
    (modulePullbackPushforwardAdjunction p.toLRSHom.toShHom) F
  have hfin : relativeToPullbackLeg p a F =
      (((modulePushforward (toInverseImageBase a)).map
          ((modulePullbackPushforwardAdjunction p.toLRSHom.toShHom).unit.app F) ≫
        (modulePushforwardComp p.toLRSHom.toShHom (toInverseImageBase a)).hom.app
          ((modulePullback p.toLRSHom.toShHom).obj F)) ≫
        eqToHom (congrArg (fun z : W.toRingedSpace ⟶ inverseImageBase a =>
          (modulePushforward z).obj ((modulePullback p.toLRSHom.toShHom).obj F))
          (toInverseImageBase_comp_relativeInverseImageProjection p a).symm)) ≫
        (modulePushforwardComp (toInverseImageBase (p ≫ a))
          (relativeInverseImageProjection p a)).inv.app
          ((modulePullback p.toLRSHom.toShHom).obj F) := by
    simp only [Category.assoc]
    rfl
  refine (congrArg _ hL).trans ((homEquiv_relativeInverseImageToPullback p a F).trans
    (hfin.trans ?_))
  exact chase4 hR4 hR3 hR2 hR1
end Leg

end Stacks.DeRhamDirectImage

end
