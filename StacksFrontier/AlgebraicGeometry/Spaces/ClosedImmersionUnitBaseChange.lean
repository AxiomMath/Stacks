module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleEssentialImageUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleUnitEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleAffineBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleBaseChangeMate
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardIdIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions

/-!
# The unit of a closed immersion under base change

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, and let `𝒢` be a quasi-coherent `𝒪_X`-module.  By Stacks 04CJ, `𝒢` is a direct
image along `i` exactly when the unit `η_𝒢 : 𝒢 ⟶ i_*i^*𝒢` of the adjunction of Stacks 03LU is an
isomorphism, and that unit is always an epimorphism, with kernel `𝓘𝒢`.  This file records how
that condition behaves under an arbitrary base change `g : X' ⟶ X`, which is what the proof of
Stacks 0DNB needs: the condition at `g^*𝒢` is that the inverse image of the inclusion
`ker η_𝒢 ⟶ 𝒢` vanishes, so it is the vanishing of the base change of one fixed map of
quasi-coherent modules, the shape of the vanishing locus of Stacks 083M.

## Main results

* `AlgebraicGeometry.Space.modulePullback_map_unit_comp_moduleBaseChangeMap`: for a commutative
  square `g' ≫ f = f' ≫ g` and an `𝒪_Y`-module `𝒢`, the inverse image along `g` of the unit of
  `f^* ⊣ f_*` followed by the base change map is the unit of `f'^* ⊣ f'_*` followed by the direct
  image of the comparison of the two composite inverse images.
* `AlgebraicGeometry.Space.isIso_modulePullback_map_unit_iff`: for a cartesian square whose right
  morphism is affine and a quasi-coherent `𝒢`, the inverse image of the unit at `𝒢` is invertible
  exactly when the unit of the base change at `g^*𝒢` is.
* `AlgebraicGeometry.Space.modulePullback_map_kernel_ι_eq_zero_iff`: for an epimorphism `η`, the
  inverse image of `ker η ⟶ 𝒢` vanishes exactly when the inverse image of `η` is invertible.
* `AlgebraicGeometry.Space.essImage_modulePushforward_modulePullback_iff`: **the combination**:
  for a closed immersion `i` and a cartesian square over it, `g^*𝒢` is a direct image along the
  base change of `i` exactly when the inverse image along `g` of `ker η_𝒢 ⟶ 𝒢` is zero.

## Implementation notes

The identification of the unit with the base change map is `CategoryTheory.unit_mateEquiv` at
the description of the base change map as a mate under the adjunctions of the *vertical*
morphisms, `AlgebraicGeometry.Space.moduleBaseChangeMap_eq_mateEquiv`.

## References

* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
* [Stacks Project, Tag 083M](https://stacks.math.columbia.edu/tag/083M)
* [Stacks Project, Tag 0DNB](https://stacks.math.columbia.edu/tag/0DNB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

/- The global instances `Abelian (SheafOfModules.{max u v r w} O)` and its Grothendieck
counterpart leave a stuck universe constraint against the modules of the small étale site; the
abelian structure used here is the one of `StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian`.
-/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄} [Category.{v₁} C]
  [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]

/-- `CategoryTheory.unit_mateEquiv` for a transformation known to be the mate only up to an
equation.  Stated over opaque functors, so that instantiating it does not unfold the mate. -/
theorem unit_app_comp_app_of_eq_mateEquiv {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C}
    {L₂ : E ⥤ F} {R₂ : F ⥤ E} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : G ⋙ L₂ ⟶ L₁ ⋙ H)
    (β : R₁ ⋙ G ⟶ H ⋙ R₂) (h : β = mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ α)) (c : C) :
    G.map (adj₁.unit.app c) ≫ β.app (L₁.obj c) = adj₂.unit.app (G.obj c) ≫ R₂.map (α.app c) := by
  subst h
  exact unit_mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ α) c

end CategoryTheory

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Square

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X)

/-- **The unit and the base change map.**  For a commutative square `g' ≫ f = f' ≫ g` and an
`𝒪_Y`-module `𝒢`, the inverse image along `g` of the unit `𝒢 ⟶ f_*f^*𝒢` followed by the base
change map `g^*f_*f^*𝒢 ⟶ f'_*g'^*f^*𝒢` is the unit `g^*𝒢 ⟶ f'_*f'^*g^*𝒢` followed by the direct
image along `f'` of the comparison `f'^*g^*𝒢 ≅ g'^*f^*𝒢` of the two composite inverse images. -/
theorem modulePullback_map_unit_comp_moduleBaseChangeMap (comm : g' ≫ f = f' ≫ g)
    (G : Modules.{u, u} B S hS Y.1 Y.2) :
    (modulePullback B S hS g).map ((modulePullbackAdjunction B S hS f).unit.app G) ≫
        (moduleBaseChangeMap f g f' g' comm).app ((modulePullback B S hS f).obj G) =
      (modulePullbackAdjunction B S hS f').unit.app ((modulePullback B S hS g).obj G) ≫
        (modulePushforward B S hS f').map
          ((modulePullbackSquareComparison f g f' g' comm).inv.app G) :=
  unit_app_comp_app_of_eq_mateEquiv (modulePullbackAdjunction B S hS f)
    (modulePullbackAdjunction B S hS f') (modulePullbackSquareComparison f g f' g' comm).inv
    (moduleBaseChangeMap f g f' g' comm) (moduleBaseChangeMap_eq_mateEquiv f g f' g' comm) G

/-- **Inverse images of the unit along a cartesian square with affine right morphism.**  For a
cartesian square whose right morphism `f` is affine and a quasi-coherent `𝒪_Y`-module `𝒢`, the
inverse image along `g` of the unit `𝒢 ⟶ f_*f^*𝒢` is an isomorphism exactly when the unit
`g^*𝒢 ⟶ f'_*f'^*g^*𝒢` of the base change is.  The base change map is invertible at the
quasi-coherent `f^*𝒢` by Stacks 07U8. -/
theorem isIso_modulePullback_map_unit_iff (sq : IsPullback g' f' f g)
    (hf : IsAffineHom B S hS f.hom) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (hG : G.IsQuasicoherentOnSite) :
    IsIso ((modulePullback B S hS g).map ((modulePullbackAdjunction B S hS f).unit.app G)) ↔
      IsIso ((modulePullbackAdjunction B S hS f').unit.app ((modulePullback B S hS g).obj G)) := by
  have hθ : IsIso ((moduleBaseChangeMap f g f' g' sq.w).app ((modulePullback B S hS f).obj G)) :=
    isIso_moduleBaseChangeMap_app_of_isAffineHom sq hf _
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS f G hG)
  rw [← isIso_comp_right_iff _ ((moduleBaseChangeMap f g f' g' sq.w).app
      ((modulePullback B S hS f).obj G)),
    modulePullback_map_unit_comp_moduleBaseChangeMap f g f' g' sq.w G, isIso_comp_right_iff]

end Square

section Kernel

variable {X Y : AlgebraicSpaces B S hS}

/-- **Vanishing of the inverse image of a kernel inclusion.**  For an epimorphism `η : 𝒢 ⟶ 𝒬`
of `𝒪_X`-modules and any morphism `g : X' ⟶ X`, the inverse image along `g` of the inclusion
`ker η ⟶ 𝒢` is zero exactly when the inverse image of `η` is an isomorphism.  The epimorphism
`η` is the cokernel of its kernel, and `g^*` is a left adjoint, so `g^*η` is the cokernel of
`g^*(ker η ⟶ 𝒢)`; a morphism is zero exactly when its cokernel is invertible. -/
theorem modulePullback_map_kernel_ι_eq_zero_iff (g : Y ⟶ X)
    {G Q : Modules.{u, u} B S hS X.1 X.2} (η : G ⟶ Q) [Epi η] :
    (modulePullback B S hS g).map (kernel.ι η) = 0 ↔
      IsIso ((modulePullback B S hS g).map η) := by
  let L := modulePullback B S hS g
  have : L.IsLeftAdjoint := (modulePullbackAdjunction B S hS g).isLeftAdjoint
  have hc : IsColimit (CokernelCofork.ofπ η (kernel.condition η)) :=
    Abelian.epiIsCokernelOfKernel _ (limit.isLimit _)
  refine ⟨fun h0 => ?_, fun h => ?_⟩
  · obtain ⟨d, hd⟩ := CokernelCofork.IsColimit.desc' (CokernelCofork.mapIsColimit _ hc L) (𝟙 _)
      (by rw [h0, zero_comp])
    change L.map η ≫ d = 𝟙 _ at hd
    refine ⟨⟨d, hd, (cancel_epi (L.map η)).1 ?_⟩⟩
    rw [← Category.assoc, hd, Category.id_comp, Category.comp_id]
  · have hw : L.map (kernel.ι η) ≫ L.map η = 0 :=
      CokernelCofork.condition ((CokernelCofork.ofπ η (kernel.condition η)).map L)
    exact (IsIso.mono_of_iso (L.map η)).right_cancellation _ _ (hw.trans zero_comp.symm)

/-- **Vanishing of an inverse image does not see an isomorphism of the source.**  If
`a = e ≫ b` with `e` an isomorphism of algebraic spaces, then the inverse image of a morphism of
modules along `a` vanishes exactly when its inverse image along `b` does: `a^* ≅ e^* ∘ b^*` and
`e^*` is an equivalence. -/
theorem modulePullback_map_eq_zero_iff_of_iso_comp {X' W : AlgebraicSpaces B S hS} (e : Y ≅ X')
    (b : X' ⟶ W) {a : Y ⟶ W} (hab : e.hom ≫ b = a) {F G : Modules.{u, u} B S hS W.1 W.2}
    (v : F ⟶ G) :
    (modulePullback B S hS a).map v = 0 ↔ (modulePullback B S hS b).map v = 0 := by
  let t := modulePullbackTriangle B S hS hab
  have hnat : (modulePullback B S hS a).map v =
      t.hom.app F ≫ (modulePullback B S hS e.hom).map ((modulePullback B S hS b).map v) ≫
        t.inv.app G := (NatIso.naturality_2 t v).symm
  have : (modulePullback B S hS e.hom).Faithful :=
    ((modulePushforwardCoherence B S hS).modulePullbackEquivalence e).faithful_functor
  have : (modulePullback B S hS e.hom).PreservesZeroMorphisms :=
    have := (modulePullbackAdjunction B S hS e.hom).isLeftAdjoint
    inferInstance
  rw [hnat, Preadditive.IsIso.comp_left_eq_zero, Preadditive.IsIso.comp_right_eq_zero,
    Functor.map_eq_zero_iff]

end Kernel

section ClosedImmersion

variable {X Y X' Y' : AlgebraicSpaces B S hS} (i : X ⟶ Y) (g : Y' ⟶ Y) (i' : X' ⟶ Y')
    (g' : X' ⟶ X)

/-- **Being a direct image along a closed immersion, after base change, is a vanishing
condition.**  Let `i : X ⟶ Y` be a closed immersion, `g' ≫ i = i' ≫ g` a cartesian square and
`𝒢` a quasi-coherent `𝒪_Y`-module.  Then `g^*𝒢` is a direct image along `i'` exactly when the
inverse image along `g` of the inclusion `ker η_𝒢 ⟶ 𝒢` of the kernel of the unit
`η_𝒢 : 𝒢 ⟶ i_*i^*𝒢` is zero.

The base change `i'` is a closed immersion (Stacks 03M4), so `g^*𝒢` is a direct image along it
exactly when the unit at `g^*𝒢` is invertible (Stacks 04CJ); by Stacks 07U8 this is the
invertibility of `g^*η_𝒢`, and as `η_𝒢` is an epimorphism (Stacks 04CJ) this is the vanishing of
`g^*(ker η_𝒢 ⟶ 𝒢)`. -/
theorem essImage_modulePushforward_modulePullback_iff (sq : IsPullback g' i' i g)
    (hi : IsClosedImmersion B S hS i.hom) (hi' : IsClosedImmersion B S hS i'.hom)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (hG : G.IsQuasicoherentOnSite) :
    (modulePushforward B S hS i').essImage ((modulePullback B S hS g).obj G) ↔
      (modulePullback B S hS g).map
        (kernel.ι ((modulePullbackAdjunction B S hS i).unit.app G)) = 0 := by
  have : Epi ((modulePullbackAdjunction B S hS i).unit.app G) :=
    epi_modulePullbackAdjunction_unit_of_essImage_of_annihilated B S hS i hi
      (fun M hM => essImage_modulePushforward_of_annihilatedByKerIdeal B S hS i hi M hM) G
  rw [essImage_modulePushforward_iff_isIso_modulePullbackAdjunction_unit B S hS i' hi',
    modulePullback_map_kernel_ι_eq_zero_iff,
    isIso_modulePullback_map_unit_iff i g i' g' sq (isAffineHom_of_isClosedImmersion B S hS
      i.hom hi) G hG]

end ClosedImmersion

end AlgebraicGeometry.Space

end
