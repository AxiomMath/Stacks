module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.PullbackSections
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.AffineSections
public import StacksFrontier.AlgebraicGeometry.SectionsColimit.Basic

/-!
# The pullback-sections presheaf of a quasi-coherent module over an affine base

`AlgebraicGeometry.pullbackSectionsMap` is the canonical map on global sections attached to a
morphism of schemes over a base, and it is what the functor of Tag 03DS does on morphisms, by
`AlgebraicGeometry.PullbackSectionsPresheaf.map_objIso`.  This file computes it over an affine
base.

Three facts are proved, and together they pin the functor down on the affine part of the site.

* It is the adjunction transpose read on global sections:
  `pullbackSectionsMap_eq_secMor` identifies it with the sections at `⊤` of the morphism
  `secMor`, which is the unit of the inverse-image--direct-image adjunction followed by the
  canonical comparison of iterated inverse images.  The `eqToHom` that the definition of
  `pullbackSectionsMap` carries is the identity, because `f ⁻¹ᵁ ⊤ = ⊤`.
* It is semilinear: `pullbackSectionsMap_smul`.  The scalars are transported along
  `Scheme.Hom.appTop` of the morphism.
* Over an affine base its transpose under extension of scalars is invertible, by
  `isIso_transposeExtend_sectionsLinearMap`: the global sections of the inverse image to a
  later affine stage are the extension of scalars of the global sections at the earlier one.
  This is `Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_transposeExtend_pullbackΓUnit`,
  carried across the comparison of iterated inverse images.

From the last fact, `bijective_smul_sectionsLinearMap` says that if the earlier stage's global
sections are free of rank one, so are the later stage's, on the image of the generator.

## Implementation notes

The affine statements are indexed by the *ring homomorphisms* rather than by objects of the
over-category together with equations identifying their structure morphisms with spectra: the
over-category objects are spelled `Over.mk (Spec.map β)`, so that `Over.left` and `Over.hom`
reduce to `Spec` and `Spec.map` and nothing has to be transported.  The structure morphism of
the terminal object is spelled `Spec.map (𝟙 A)` rather than `𝟙 (Spec A)` for the same reason:
the inverse image along it is then quasi-coherent by the instance
`Stacks.AlgebraicGeometry.SectionsColimit.isQuasicoherent_pullback_specMap`, and terminality is
recovered from `Spec.map_id`.

`Γ(M, ⊤)` lives in `AddCommGrpCat` while `AlgebraicGeometry.moduleSpecΓFunctor.obj M` lives in
`ModuleCat`; the two have the same carrier, which is why `sectionsLinearMap` can be used as a
semilinear refinement of `pullbackSectionsMap`.

## References

* [The Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [The Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.AffineBaseChangeIso
open scoped ChangeOfRings

universe u

namespace Stacks.LimitSectionsIdentification

section General

variable {S : Scheme.{u}} (F : S.Modules) {X Y : Over S} (g : X ⟶ Y)

/-- The canonical comparison of the iterated inverse image along `g.left` and `Y.hom` with the
inverse image along `X.hom`. -/
def comparison : (Scheme.Modules.pullback g.left).obj ((Scheme.Modules.pullback Y.hom).obj F) ⟶
    (Scheme.Modules.pullback X.hom).obj F :=
  (Scheme.Modules.pullbackComp g.left Y.hom).hom.app F ≫
    (Scheme.Modules.pullbackCongr (Over.w g)).hom.app F

/-- The comparison of iterated inverse images is an isomorphism. -/
instance : IsIso (comparison F g) := by
  dsimp only [comparison]
  infer_instance

/-- The morphism of `𝒪_{Y}`-modules whose global sections are `pullbackSectionsMap`: the unit of
the inverse-image--direct-image adjunction for `g.left`, followed by `comparison`. -/
def secMor : (Scheme.Modules.pullback Y.hom).obj F ⟶
    (Scheme.Modules.pushforward g.left).obj ((Scheme.Modules.pullback X.hom).obj F) :=
  (Scheme.Modules.pullbackPushforwardAdjunction g.left).unit.app
      ((Scheme.Modules.pullback Y.hom).obj F) ≫
    (Scheme.Modules.pushforward g.left).map (comparison F g)

/-- The inverse image of the top open along any morphism of schemes is the top open. -/
theorem preimage_top : (⊤ : X.left.Opens) = g.left ⁻¹ᵁ ⊤ := rfl

/-- The restriction map that the definition of `pullbackSectionsMap` carries is the identity. -/
theorem map_preimage_top :
    ((Scheme.Modules.pullback X.hom).obj F).presheaf.map (eqToHom (preimage_top g)).op
      = 𝟙 Γ((Scheme.Modules.pullback X.hom).obj F, ⊤) := by
  rw [Subsingleton.elim (eqToHom (preimage_top g)) (eqToHom (rfl : (⊤ : X.left.Opens) = ⊤))]
  simp

/-- **The canonical map on global sections is the adjunction transpose, read at `⊤`.** -/
theorem pullbackSectionsMap_eq_secMor : pullbackSectionsMap F g = (secMor F g).app ⊤ := by
  rw [show pullbackSectionsMap F g = (secMor F g).app ⊤ ≫
    ((Scheme.Modules.pullback X.hom).obj F).presheaf.map
      (eqToHom (preimage_top g)).op from rfl, map_preimage_top F g]
  exact Category.comp_id _

/-- **The canonical map on global sections is semilinear**, the scalars being transported along
the morphism of schemes. -/
theorem pullbackSectionsMap_smul (r : Γ(Y.left, ⊤))
    (x : Γ((Scheme.Modules.pullback Y.hom).obj F, ⊤)) :
    pullbackSectionsMap F g (r • x) = g.left.appTop r • pullbackSectionsMap F g x := by
  rw [pullbackSectionsMap_eq_secMor]
  exact Scheme.Modules.Hom.app_smul (secMor F g) r x

end General

section Functoriality

variable {S : Scheme.{u}} (F : S.Modules) [F.IsQuasicoherent]

/-- The canonical map on global sections, read through the functor of Tag 03DS. -/
theorem pullbackSectionsMap_eq_functor {X Y : Over S} (g : X ⟶ Y) :
    pullbackSectionsMap F g =
      ((quasiCoherentPresheaf S F).objIso (op Y)).inv ≫
        (quasiCoherentPresheafFunctor S F).map g.op ≫
        ((quasiCoherentPresheaf S F).objIso (op X)).hom :=
  ((quasiCoherentPresheaf S F).map_objIso g.op).symm

/-- **The canonical map on global sections is contravariantly functorial.**  This is the
functoriality of the presheaf of Tag 03DS, read through `map_objIso`. -/
theorem pullbackSectionsMap_comp {X Y Z : Over S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullbackSectionsMap F (f ≫ g) = pullbackSectionsMap F g ≫ pullbackSectionsMap F f := by
  simp [pullbackSectionsMap_eq_functor]

end Functoriality

section Affine

variable {A₀ : CommRingCat.{u}} (F : (Spec A₀).Modules)
  {A A' : CommRingCat.{u}} (b : Spec A ⟶ Spec A₀) (γ : A ⟶ A') (b' : Spec A' ⟶ Spec A₀)
  (hw : Spec.map γ ≫ b = b')

/-- A morphism of affine schemes over `Spec A₀`, presented so that `Over.left`, `Over.hom` and
`Over.Hom.left` all reduce. -/
def overHom : Over.mk b' ⟶ Over.mk b := Over.homMk (Spec.map γ) hw

/-- The canonical map on global sections of the inverse images, refined to an `A`-linear map into
the `A'`-module of global sections at the later stage with its scalars restricted along `γ`.  It
is spelled as the normalized affine comparison
`Stacks.AlgebraicGeometry.AffineBaseChangeIso.pullbackΓUnit` followed by the global sections of
the comparison of iterated inverse images; `sectionsLinearMap_apply` is what makes it a
refinement of `pullbackSectionsMap`. -/
def sectionsLinearMap : moduleSpecΓFunctor.obj ((Scheme.Modules.pullback b).obj F) ⟶
    (ModuleCat.restrictScalars γ.hom).obj
      (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback b').obj F)) :=
  pullbackΓUnit γ ((Scheme.Modules.pullback b).obj F) ≫
    (ModuleCat.restrictScalars γ.hom).map
      (moduleSpecΓFunctor.map (comparison F (overHom b γ b' hw)))

/-- **The `A`-linear refinement has the same underlying function as `pullbackSectionsMap`.**
Both are the unit of the inverse-image--direct-image adjunction followed by the comparison of
iterated inverse images, read at the top open; the one carries the scalar bookkeeping of
`pushforwardΓIso`, whose underlying map is the identity, and the other the restriction map along
`g.left ⁻¹ᵁ ⊤ = ⊤`, which is the identity. -/
theorem sectionsLinearMap_apply (x : Γ((Scheme.Modules.pullback b).obj F, ⊤)) :
    sectionsLinearMap F b γ b' hw x = pullbackSectionsMap F (overHom b γ b' hw) x := by
  rw [pullbackSectionsMap_eq_secMor]
  rfl

/-- The same, after precomposition with a map of `A`-modules.  This is the shape in which the
refinement is used: stated this way, instantiating it needs only the unfolding of the composite,
never that of the module whose sections are being taken. -/
theorem comp_sectionsLinearMap_apply {N : ModuleCat.{u} A}
    (e : N ⟶ moduleSpecΓFunctor.obj ((Scheme.Modules.pullback b).obj F)) (n : N) :
    (e ≫ sectionsLinearMap F b γ b' hw) n
      = pullbackSectionsMap F (overHom b γ b' hw) (e n) :=
  sectionsLinearMap_apply F b γ b' hw (e n)

/-- The transpose of a map followed by the restriction of scalars of a map of `A'`-modules is
the transpose followed by that map. -/
theorem transposeExtend_comp {M : ModuleCat.{u} A} {P Q : ModuleCat.{u} A'}
    (u : M ⟶ (ModuleCat.restrictScalars γ.hom).obj P) (k : P ⟶ Q) :
    transposeExtend γ (u ≫ (ModuleCat.restrictScalars γ.hom).map k)
      = transposeExtend γ u ≫ k :=
  (ModuleCat.extendRestrictScalarsAdj γ.hom).homEquiv_naturality_right_symm u k

/-- **Over an affine base, the global sections of the inverse image to a later stage are the
extension of scalars of the global sections at the earlier stage.** -/
theorem isIso_transposeExtend_sectionsLinearMap
    [((Scheme.Modules.pullback b).obj F).IsQuasicoherent] :
    IsIso (transposeExtend γ (sectionsLinearMap F b γ b' hw)) := by
  have hc : IsIso (comparison F (overHom b γ b' hw)) := by
    dsimp only [comparison]; infer_instance
  have h : IsIso (transposeExtend γ (pullbackΓUnit γ ((Scheme.Modules.pullback b).obj F))) :=
    isIso_transposeExtend_pullbackΓUnit γ _
  have h2 : IsIso (moduleSpecΓFunctor.map (comparison F (overHom b γ b' hw))) :=
    Functor.map_isIso _ _
  rw [sectionsLinearMap, transposeExtend_comp]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h h2

end Affine

end Stacks.LimitSectionsIdentification

end
