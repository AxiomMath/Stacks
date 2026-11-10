module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleFiniteSupportTensor

/-!
# The projection-formula recipe is natural in the test object

Let `f : X ⟶ Y` be a morphism of a big étale site, let `Λ` be a commutative ring, let `F` be a
sheaf of `Λ`-modules on `X_étale` and `G` one on `Y_étale`. The recipe
`(Z, s) ⊗ t ↦ (Z, s ⊗ f^{-1}t)` of [Stacks, Tag 0GKF] is, over each test object `V` of
`Y_étale`, the map `AlgebraicGeometry.SmallEtale.finiteSupportTensorSectionsHom`. This file
proves it compatible with base change along a morphism `V' ⟶ V`, which is the naturality in the
test object that turns the family of maps into a morphism of presheaves.

## Main results

* `AlgebraicGeometry.SmallEtale.finiteSupportBaseChange_openMap_fac` — the morphism of canonical
  opens produced by base change of a support is compatible with the two open inclusions. This is
  `AlgebraicGeometry.SmallEtale.openObjectMap_fac` for that morphism.
* `AlgebraicGeometry.SmallEtale.modPullbackUnitSection_supportOpen` — **the inverse image of a
  section, restricted to a canonical support-open, is compatible with base change.** Restricting
  `f^{-1}t` along the induced morphism of canonical opens gives the restriction of
  `f^{-1}(t|_{V'})`.
* `AlgebraicGeometry.SmallEtale.finiteSupportBaseChange_tensorSupportedSections` — **the recipe
  commutes with base change on supported sections**: restricting `s ⊗ f^{-1}t` gives
  `(s|) ⊗ f^{-1}(t|)`, with the same support on both sides.
* `AlgebraicGeometry.SmallEtale.finiteSupportTensorSectionsHom_naturality` — **the recipe is
  natural in the test object**, as a commuting square of maps of the colimits of supported
  sections.

## Implementation notes

The base-change data `AlgebraicGeometry.SmallEtale.finiteSupportBaseChange` depends on the
abelian sheaf only through its map on sections: the support is the set-theoretic inverse image
and the morphism of canonical opens is `AlgebraicGeometry.SmallEtale.openObjectMap`, neither of
which mentions the sheaf. So the base change of a support for `F` and for `F ⊗_Λ f^{-1}G` have
the same support and the same morphism of canonical opens, definitionally, and the statements
below take the abelian sheaf producing that data as a separate argument. This is why the `HEq`
transport which `AlgebraicGeometry.SmallEtale.finiteSupportBaseChange_sections_comp` needs does
not arise here.

Nothing here carries a `stacks` attribute: this is one input to [Stacks, Tag 0GKF] and not that
tag.

## References

* [Stacks Project, Tag 0F6M](https://stacks.math.columbia.edu/tag/0F6M)
* [Stacks Project, Tag 0GKF](https://stacks.math.columbia.edu/tag/0GKF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace Stacks

/-- **Pasting a naturality square against two colimit generators.** If `i₁ ≫ Tv = a ≫ j₁` and
`i₂ ≫ Tv' = a' ≫ j₂` express two maps on the generators, `j₁ ≫ u = b ≫ j₂` and
`i₁ ≫ w = c ≫ i₂` express two restriction maps on the generators, and the square
`a ≫ b = c ≫ a'` commutes on the generators, then the two composites agree after the first
generator. This is the combinatorics of a naturality proof for a map out of a colimit, isolated
so that it can be applied to terms whose types agree only up to unfolding a diagram. -/
public theorem comp_assoc_square {C : Type*} [Category* C]
    {A₁ A₂ A₃ A₄ P P' Q Q' : C} (i₁ : A₁ ⟶ P) (i₂ : A₃ ⟶ P') (j₁ : A₂ ⟶ Q) (j₂ : A₄ ⟶ Q')
    (Tv : P ⟶ Q) (Tv' : P' ⟶ Q') (u : Q ⟶ Q') (w : P ⟶ P')
    (a : A₁ ⟶ A₂) (a' : A₃ ⟶ A₄) (b : A₂ ⟶ A₄) (c : A₁ ⟶ A₃)
    (h1 : i₁ ≫ Tv = a ≫ j₁) (h2 : j₁ ≫ u = b ≫ j₂) (h3 : i₁ ≫ w = c ≫ i₂)
    (h4 : i₂ ≫ Tv' = a' ≫ j₂) (hc : a ≫ b = c ≫ a') :
    i₁ ≫ Tv ≫ u = i₁ ≫ w ≫ Tv' := by
  rw [← Category.assoc, h1, Category.assoc, h2, ← Category.assoc, hc, Category.assoc, ← h4,
    ← Category.assoc, ← h3, Category.assoc]

end Stacks

namespace AlgebraicGeometry.SmallEtale

universe u v

section OpenMap

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)

/-- **The morphism of canonical opens produced by base change of a support is compatible with
the two open inclusions.** -/
public theorem finiteSupportBaseChange_openMap_fac
    (A : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    {V V' : SmallEtale B Y.obj Y.property} (g : V' ⟶ V) (E : FiniteSupport B f V) :
    (finiteSupportBaseChange B f A g E).openMap ≫
        openObjectι B X.obj X.property (baseChange B f V)
          (supportOpen B X.obj X.property (baseChange B f V) E.1
            (finiteSupport_isLocallyClosed B f V E)) =
      openObjectι B X.obj X.property (baseChange B f V')
          (supportOpen B X.obj X.property (baseChange B f V')
            (finiteSupportBaseChange B f A g E).support.1
            (finiteSupport_isLocallyClosed B f V'
              (finiteSupportBaseChange B f A g E).support)) ≫
        (smallEtaleBaseChange B f).map g :=
  openObjectMap_fac B X.obj X.property ((smallEtaleBaseChange B f).map g) _ _
    (supportOpen_preimage_subset B f g E (finiteSupportBaseChange B f A g E).support
      (finiteSupportBaseChange B f A g E).support_eq)

end OpenMap

section Naturality

variable (B : BigEtaleSite.{u}) (Λ : Type (max (u + 1) v)) [CommRing Λ] {X Y : B.Scheme}
  (f : X ⟶ Y)

attribute [local instance] moduleSheafMonoidal
attribute [local instance] SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat

/-- **The inverse image of a section, restricted to a canonical support-open, is compatible with
base change.** Restricting `f^{-1}(t|_{V'})` to the canonical open of the inverse-image support
is the same as restricting `f^{-1}t` to the canonical open of the original support and then
along the induced morphism of canonical opens. -/
public theorem modPullbackUnitSection_supportOpen
    (A : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ)
    {V V' : SmallEtale B Y.obj Y.property} (g : V' ⟶ V) (t : G.obj.obj (op V))
    (E : FiniteSupport B f V) :
    ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G).obj.map
        (openObjectι B X.obj X.property (baseChange B f V')
          (supportOpen B X.obj X.property (baseChange B f V')
            (finiteSupportBaseChange B f A g E).support.1
            (finiteSupport_isLocallyClosed B f V'
              (finiteSupportBaseChange B f A g E).support))).op
        (modPullbackUnitSection B Λ f G V' (G.obj.map g.op t)) =
      ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G).obj.map
        (finiteSupportBaseChange B f A g E).openMap.op
        (((modPullback.{u, v, max (u + 1) v} B Λ f).obj G).obj.map
          (openObjectι B X.obj X.property (baseChange B f V)
            (supportOpen B X.obj X.property (baseChange B f V) E.1
              (finiteSupport_isLocallyClosed B f V E))).op
          (modPullbackUnitSection B Λ f G V t)) := by
  have hmor : G.obj.map g.op ≫ modPullbackUnitSection B Λ f G V' =
      modPullbackUnitSection B Λ f G V ≫
        ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G).obj.map
          ((smallEtaleBaseChange B f).map g).op :=
    ModuleCat.hom_ext (LinearMap.ext fun x =>
      modPullbackUnitSection_naturality B Λ f G g x)
  have key : G.obj.map g.op ≫ modPullbackUnitSection B Λ f G V' ≫
        ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G).obj.map
          (openObjectι B X.obj X.property (baseChange B f V')
            (supportOpen B X.obj X.property (baseChange B f V')
              (finiteSupportBaseChange B f A g E).support.1
              (finiteSupport_isLocallyClosed B f V'
                (finiteSupportBaseChange B f A g E).support))).op =
      modPullbackUnitSection B Λ f G V ≫
        ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G).obj.map
          (openObjectι B X.obj X.property (baseChange B f V)
            (supportOpen B X.obj X.property (baseChange B f V) E.1
              (finiteSupport_isLocallyClosed B f V E))).op ≫
        ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G).obj.map
          (finiteSupportBaseChange B f A g E).openMap.op := by
    rw [← Category.assoc, hmor, Category.assoc, ← CategoryTheory.Functor.map_comp,
      ← CategoryTheory.Functor.map_comp]
    simp only [← op_comp]
    rw [finiteSupportBaseChange_openMap_fac B f A g E]
  exact ConcreteCategory.congr_hom key t

/-- **The projection-formula recipe commutes with base change on supported sections.**
Restricting `s ⊗ f^{-1}t` along the morphism of canonical opens induced by `V' ⟶ V` gives the
restriction of `s` tensored with the inverse image of the restriction of `t`; the support is the
inverse-image support on both sides. -/
public theorem finiteSupportBaseChange_tensorSupportedSections
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ)
    {V V' : SmallEtale B Y.obj Y.property} (g : V' ⟶ V) (t : G.obj.obj (op V))
    (E : FiniteSupport B f V) :
    (finiteSupportBaseChange B f
          ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj
            (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G)) g E).sectionsMap.comp
        (tensorSupportedSectionsHom B Λ F
          ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G) (baseChange B f V)
          (modPullbackUnitSection B Λ f G V t) E.1
          (finiteSupport_isLocallyClosed B f V E)) =
      (tensorSupportedSectionsHom B Λ F
          ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G) (baseChange B f V')
          (modPullbackUnitSection B Λ f G V' (G.obj.map g.op t))
          (finiteSupportBaseChange B f
            ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) g E).support.1
          (finiteSupport_isLocallyClosed B f V'
            (finiteSupportBaseChange B f
              ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) g E).support)).comp
        (finiteSupportBaseChange B f
          ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) g E).sectionsMap := by
  refine AddMonoidHom.ext fun s => Subtype.ext ?_
  change (F ⊗ ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)).obj.map
        (finiteSupportBaseChange B f
          ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) g E).openMap.op
        ((Stacks.ModuleSheafTensorSection.moduleToTensorSection
            (SmallEtale.topology B X.obj X.property) Λ F
            ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)).app
          (op (openObject B X.obj X.property (baseChange B f V)
            (supportOpen B X.obj X.property (baseChange B f V) E.1
              (finiteSupport_isLocallyClosed B f V E))))
          (s.val ⊗ₜ[Λ] ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G).obj.map
            (openObjectι B X.obj X.property (baseChange B f V)
              (supportOpen B X.obj X.property (baseChange B f V) E.1
                (finiteSupport_isLocallyClosed B f V E))).op
            (modPullbackUnitSection B Λ f G V t))) =
      (Stacks.ModuleSheafTensorSection.moduleToTensorSection
          (SmallEtale.topology B X.obj X.property) Λ F
          ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)).app
        (op (openObject B X.obj X.property (baseChange B f V')
          (supportOpen B X.obj X.property (baseChange B f V')
            (finiteSupportBaseChange B f
              ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) g E).support.1
            (finiteSupport_isLocallyClosed B f V'
              (finiteSupportBaseChange B f
                ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) g E).support))))
        (F.obj.map (finiteSupportBaseChange B f
            ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) g E).openMap.op s.val ⊗ₜ[Λ]
          ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G).obj.map
            (openObjectι B X.obj X.property (baseChange B f V')
              (supportOpen B X.obj X.property (baseChange B f V')
                (finiteSupportBaseChange B f
                  ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) g E).support.1
                (finiteSupport_isLocallyClosed B f V'
                  (finiteSupportBaseChange B f
                    ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) g E).support))).op
            (modPullbackUnitSection B Λ f G V' (G.obj.map g.op t)))
  rw [modPullbackUnitSection_supportOpen B Λ f
    ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) G g t E]
  exact (Stacks.ModuleSheafTensorSection.moduleToTensorSection_naturality_tmul
    (SmallEtale.topology B X.obj X.property) Λ F ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)
    (finiteSupportBaseChange B f
      ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) g E).openMap.op s.val
    (((modPullback.{u, v, max (u + 1) v} B Λ f).obj G).obj.map
      (openObjectι B X.obj X.property (baseChange B f V)
        (supportOpen B X.obj X.property (baseChange B f V) E.1
          (finiteSupport_isLocallyClosed B f V E))).op
      (modPullbackUnitSection B Λ f G V t))).symm

variable [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- **The projection-formula recipe is natural in the test object.** For a morphism `V' ⟶ V` of
the small étale site of `Y`, restricting and then applying the recipe for the restricted section
is applying the recipe over `V` and then restricting. -/
public theorem finiteSupportTensorSectionsHom_naturality
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ)
    {V V' : SmallEtale B Y.obj Y.property} (g : V' ⟶ V) (t : G.obj.obj (op V)) :
    finiteSupportTensorSectionsHom B Λ f F G V t ≫
        finiteSupportBaseChangeHom B f
          ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj
            (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G)) g =
      finiteSupportBaseChangeHom B f
          ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) g ≫
        finiteSupportTensorSectionsHom B Λ f F G V' (G.obj.map g.op t) := by
  refine colimit.hom_ext fun E => ?_
  refine Stacks.comp_assoc_square _ _ _
    (colimit.ι (finiteSupportDiagram B f
      ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj
        (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G)) V')
      (finiteSupportBaseChange B f
        ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) g E).support)
    _ _ _ _ _ _ _ _
    (finiteSupportTensorSectionsHom_ι B Λ f F G V t E)
    (finiteSupportBaseChangeHom_ι B f
      ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj
        (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G)) g E)
    (finiteSupportBaseChangeHom_ι B f
      ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) g E)
    (finiteSupportTensorSectionsHom_ι B Λ f F G V' (G.obj.map g.op t)
      (finiteSupportBaseChange B f
        ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) g E).support)
    ?_
  exact AddCommGrpCat.hom_ext
    (finiteSupportBaseChange_tensorSupportedSections B Λ f F G g t E)

end Naturality

end AlgebraicGeometry.SmallEtale

end
