module

public import StacksFrontier.AlgebraicGeometry.DeRham.DiffOpBoxRelativeTensor
public import StacksFrontier.AlgebraicGeometry.DeRham.BoxKunnethFlat.BoxComparisonTranspose
public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatSource.UnderivedComparison

/-!
# The underived base change map of the relative inverse image square is `p⁻¹ ⟶ p^*`

Let `p : W ⟶ X` and `a : X ⟶ S` be morphisms of schemes. The square of ringed spaces
```
(W, 𝒪_W) --p--> (X, 𝒪_X)
    |ι_W            |ι_X
(W, (p∘a)⁻¹𝒪_S) --p₂--> (X, a⁻¹𝒪_S)
```
commutes (`Stacks.DeRhamDirectImage.toInverseImageBase_comp_relativeInverseImageProjection`), so
it has an underived base change map `p₂^* ∘ ι_{X*} ⟶ ι_{W*} ∘ p^*`, the mate of the composition
isomorphisms of pullbacks. This file identifies it with the comparison
`Stacks.DeRhamDirectImage.relativeInverseImageToPullback`, both on sheaves of modules and, at the
class of a complex, on the homotopy categories. The same holds for a projection presented as a
factorization and for the second projection of a fibre product.

## Main results

* `Stacks.DeRhamDirectImage.moduleBaseChangeSquare_app_relative`: the underived base change map
  of sheaves of modules is `p⁻¹𝓕 ⟶ p^*𝓕`.
* `Stacks.DeRhamDirectImage.underivedBaseChangeSquare_app_quotient_relative` and
  `Stacks.DeRhamDirectImage.mapHomologicalComplex_moduleBaseChangeSquare_app_f_relative`: on the
  class of a complex `K` the underived base change map is the class of the morphism of complexes
  with components `p⁻¹(K^n) ⟶ p^*(K^n)`.
* `Stacks.DeRhamDirectImage.moduleBaseChangeSquare_app_relativeOfFactors`,
  `Stacks.DeRhamDirectImage.moduleBaseChangeSquare_app_sndRelative`: the same for a projection
  presented as a factorization, and for the second projection.

## Implementation notes

Both maps are transposes along `p₂^* ⊣ p₂_*`: the comparison is by definition the transpose of the
unit of `p^* ⊣ p_*` read through the square, and the transpose of a mate is the unit followed by
the iterated mate (`CategoryTheory.unit_mateEquiv`), which is the transport along the square
(`Stacks.AlgebraicGeometry.FlatSourceBaseChange.mateEquiv_moduleBaseChangeSquare`). The two
transports are compared on local sections, where both act trivially.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.FlatSourceBaseChange

universe u

namespace Stacks.DeRhamDirectImage

section Bridges

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **The two spellings of pullback agree**: `modulePullback f`, in which the underived base
change map is written, and `pullback f`, in which `relativeInverseImageToPullback` is written, are
the same functor. (For pushforward see `Stacks.RelativeLeray.pushforward_eq_modulePushforward`.) -/
theorem modulePullback_eq_pullback : modulePullback f = _root_.pullback f := rfl

/-- The two spellings of the adjunction `f^* ⊣ f_*` agree. -/
theorem modulePullbackPushforwardAdjunction_eq_pullbackPushforwardAdjunction :
    modulePullbackPushforwardAdjunction f = _root_.pullbackPushforwardAdjunction f := rfl

end Bridges


section Transport

/-- A transport between equal sheaves of modules acts trivially on local sections. -/
theorem eqToHom_val_app_heq {Z : RingedSpace.{u, u}}
    {A B : SheafOfModules.{u} (structureSheafRing Z)}
    (h : A = B) (V : (TopologicalSpace.Opens Z.carrier)ᵒᵖ) (s : A.val.obj V) :
    HEq (((eqToHom h).val.app V).hom s) s := by
  subst h
  rfl

/-- A transport between equal functors to sheaves of modules acts trivially on local sections. -/
theorem eqToHom_app_val_app_heq {C : Type*} [Category C] {Z : RingedSpace.{u, u}}
    {P Q : C ⥤ SheafOfModules.{u} (structureSheafRing Z)} (h : P = Q) (M : C)
    (V : (TopologicalSpace.Opens Z.carrier)ᵒᵖ) (s : (P.obj M).val.obj V) :
    HEq ((((eqToHom h).app M).val.app V).hom s) s := by
  subst h
  rfl

/-- A composite of morphisms of sheaves of modules acting trivially on local sections acts
trivially on local sections. -/
theorem comp_val_app_heq {Z : RingedSpace.{u, u}}
    {A B C : SheafOfModules.{u} (structureSheafRing Z)} (φ : A ⟶ B) (ψ : B ⟶ C)
    (V : (TopologicalSpace.Opens Z.carrier)ᵒᵖ) (hφ : ∀ s, HEq ((φ.val.app V).hom s) s)
    (hψ : ∀ s, HEq ((ψ.val.app V).hom s) s) (s : A.val.obj V) :
    HEq (((φ ≫ ψ).val.app V).hom s) s :=
  (hψ _).trans (hφ s)

end Transport

section Square

variable {X' X S' S : RingedSpace.{u, u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
  (sq : g' ≫ f = f' ≫ g)

/-- Morphisms of sheaves of modules agreeing up to `HEq` on local sections are equal. -/
private theorem hom_eq_of_heq_app {Z : RingedSpace.{u, u}}
    {A B : SheafOfModules.{u} (structureSheafRing Z)} {φ ψ : A ⟶ B}
    (h : ∀ U x, HEq ((φ.val.app U).hom x) ((ψ.val.app U).hom x)) : φ = ψ :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun x => eq_of_heq (h U x)))

/-- **The mate of the underived base change map is the transport along the square**, on
components: the composition isomorphisms of direct images have identity components. -/
theorem mateEquiv_moduleBaseChangeSquare_app (M : SheafOfModules.{u} (structureSheafRing X')) :
    (mateEquiv (modulePullbackPushforwardAdjunction g') (modulePullbackPushforwardAdjunction g)
      (moduleBaseChangeSquare g' f' f g sq)).natTrans.app M =
      eqToHom (congrArg (fun k => (modulePushforward k).obj M) sq) := by
  refine (congrArg (fun t => NatTrans.app t M)
    (mateEquiv_moduleBaseChangeSquare g' f' f g sq)).trans ?_
  rw [NatTrans.comp_app, NatTrans.comp_app]
  refine hom_eq_of_heq_app fun U x => (comp_val_app_heq _ _ U (fun _ => HEq.rfl)
    (comp_val_app_heq _ _ U (eqToHom_app_val_app_heq _ _ U) (fun _ => HEq.rfl)) x).trans
      (eqToHom_val_app_heq _ U x).symm

end Square

variable {W X S : Scheme.{u}} (p : W ⟶ X) (a : X ⟶ S)

/-- The mate of the base change map at `p^*𝓕` is the transport along the square. -/
theorem mateEquiv_moduleBaseChangeSquare_app_relative (F : Modules X.toRingedSpace) :
    (mateEquiv (modulePullbackPushforwardAdjunction p.toLRSHom.toShHom)
      (modulePullbackPushforwardAdjunction (relativeInverseImageProjection p a))
      (moduleBaseChangeSquare p.toLRSHom.toShHom (toInverseImageBase (p ≫ a))
        (toInverseImageBase a) (relativeInverseImageProjection p a)
        (toInverseImageBase_comp_relativeInverseImageProjection p a).symm)).app
        ((modulePullback p.toLRSHom.toShHom).obj F) =
      (_root_.pushforwardComp p.toLRSHom.toShHom (toInverseImageBase a)).inv.app _ ≫
        relativeSquareTransport p a _ ≫
        (_root_.pushforwardComp (toInverseImageBase (p ≫ a))
          (relativeInverseImageProjection p a)).hom.app _ := by
  refine (mateEquiv_moduleBaseChangeSquare_app p.toLRSHom.toShHom (toInverseImageBase (p ≫ a))
    (toInverseImageBase a) (relativeInverseImageProjection p a)
    (toInverseImageBase_comp_relativeInverseImageProjection p a).symm
    ((modulePullback p.toLRSHom.toShHom).obj F)).trans ?_
  exact hom_eq_of_heq_app fun U x => (eqToHom_val_app_heq _ U x).trans
    (comp_val_app_heq _ _ U (fun _ => HEq.rfl)
      (comp_val_app_heq _ _ U (eqToHom_val_app_heq _ U) (fun _ => HEq.rfl)) x).symm

/-- **The underived base change map of the square is the comparison `p⁻¹𝓕 ⟶ p^*𝓕`.** -/
theorem moduleBaseChangeSquare_app_relative (F : Modules X.toRingedSpace) :
    (moduleBaseChangeSquare p.toLRSHom.toShHom (toInverseImageBase (p ≫ a)) (toInverseImageBase a)
      (relativeInverseImageProjection p a)
      (toInverseImageBase_comp_relativeInverseImageProjection p a).symm).natTrans.app F =
      relativeInverseImageToPullback p a F := by
  apply ((_root_.pullbackPushforwardAdjunction (relativeInverseImageProjection p a)).homEquiv
    _ _).injective
  refine (Adjunction.homEquiv_unit _ _ _ _).trans (Eq.trans ?_
    (homEquiv_relativeInverseImageToPullback p a F).symm)
  refine (unit_mateEquiv (modulePullbackPushforwardAdjunction p.toLRSHom.toShHom)
    (modulePullbackPushforwardAdjunction (relativeInverseImageProjection p a))
    (moduleBaseChangeSquare p.toLRSHom.toShHom (toInverseImageBase (p ≫ a)) (toInverseImageBase a)
      (relativeInverseImageProjection p a)
      (toInverseImageBase_comp_relativeInverseImageProjection p a).symm) F).symm.trans ?_
  exact congrArg (fun t => (modulePushforward (toInverseImageBase a)).map
      ((modulePullbackPushforwardAdjunction p.toLRSHom.toShHom).unit.app F) ≫ t)
    (mateEquiv_moduleBaseChangeSquare_app_relative p a F)

open Stacks.Cohomology.DerivedBaseChange in
/-- **The underived base change map on homotopy categories is the class of the degreewise
comparison `p⁻¹ ⟶ p^*`.** At the class of a complex `K` of `𝒪_X`-modules it is the class of the
morphism of complexes of `(p ∘ a)^{-1}𝒪_S`-modules whose components are
`relativeInverseImageToPullback p a (K.X n)`. -/
theorem underivedBaseChangeSquare_app_quotient_relative
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ℤ) :
    (underivedBaseChangeSquare p.toLRSHom.toShHom (toInverseImageBase (p ≫ a))
      (toInverseImageBase a) (relativeInverseImageProjection p a)
      (toInverseImageBase_comp_relativeInverseImageProjection p a).symm).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex
          (moduleBaseChangeSquare p.toLRSHom.toShHom (toInverseImageBase (p ≫ a))
            (toInverseImageBase a) (relativeInverseImageProjection p a)
            (toInverseImageBase_comp_relativeInverseImageProjection p a).symm).natTrans
          (ComplexShape.up ℤ)).app K) :=
  underivedBaseChangeSquare_app_quotient p.toLRSHom.toShHom (toInverseImageBase (p ≫ a))
    (toInverseImageBase a) (relativeInverseImageProjection p a)
    (toInverseImageBase_comp_relativeInverseImageProjection p a).symm K

/-- **The degreewise components of the underived base change map are the comparisons
`p⁻¹ ⟶ p^*`.** -/
theorem mapHomologicalComplex_moduleBaseChangeSquare_app_f_relative
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ℤ) (n : ℤ) :
    ((NatTrans.mapHomologicalComplex
      (moduleBaseChangeSquare p.toLRSHom.toShHom (toInverseImageBase (p ≫ a))
        (toInverseImageBase a) (relativeInverseImageProjection p a)
        (toInverseImageBase_comp_relativeInverseImageProjection p a).symm).natTrans
      (ComplexShape.up ℤ)).app K).f n =
      relativeInverseImageToPullback p a (K.X n) :=
  moduleBaseChangeSquare_app_relative p a (K.X n)

/-! ### A projection presented as a factorization, and the second projection -/

section Factors

variable {W X' S' : Scheme.{u}} (p : W ⟶ X') (c : X' ⟶ S') (g : W ⟶ S') (hg : p ≫ c = g)

open AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory

/-- **The underived base change map of the square is the comparison `p⁻¹𝓕 ⟶ p^*𝓕`**, for
`p ∘ c` presented as `g`. -/
theorem moduleBaseChangeSquare_app_relativeOfFactors (F : Modules X'.toRingedSpace) :
    (moduleBaseChangeSquare p.toLRSHom.toShHom (toInverseImageBase g) (toInverseImageBase c)
      (relativeInverseImageProjectionOfFactors p c g hg)
      (toInverseImageBase_comp_relativeInverseImageProjectionOfFactors p c g hg).symm).natTrans.app
        F =
      relativeInverseImageToPullbackOfFactors p c g hg F := by
  subst hg
  exact moduleBaseChangeSquare_app_relative p c F

/-- The degreewise components of the underived base change map, for `p ∘ c` presented as
`g`. -/
theorem mapHomologicalComplex_moduleBaseChangeSquare_app_f_relativeOfFactors
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace)) ℤ) (n : ℤ) :
    ((NatTrans.mapHomologicalComplex
      (moduleBaseChangeSquare p.toLRSHom.toShHom (toInverseImageBase g) (toInverseImageBase c)
        (relativeInverseImageProjectionOfFactors p c g hg)
        (toInverseImageBase_comp_relativeInverseImageProjectionOfFactors p c g hg).symm).natTrans
      (ComplexShape.up ℤ)).app K).f n =
      relativeInverseImageToPullbackOfFactors p c g hg (K.X n) :=
  moduleBaseChangeSquare_app_relativeOfFactors p c g hg (K.X n)

end Factors

end Stacks.DeRhamDirectImage

namespace Stacks.DeRhamDirectImage

section Snd

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

open AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory

/-- The square comparing the two factorizations of the second projection of `X ×_S Y`. -/
theorem toInverseImageBase_comp_sndRelativeInverseImageProjection :
    toInverseImageBase (pullback.fst a b ≫ a) ≫ sndRelativeInverseImageProjection a b =
      (pullback.snd a b).toLRSHom.toShHom ≫ toInverseImageBase b :=
  toInverseImageBase_comp_relativeInverseImageProjectionOfFactors _ _ _ _

/-- **The underived base change map of the square of the second projection is the comparison
`q⁻¹𝓖 ⟶ q^*𝓖`.** -/
theorem moduleBaseChangeSquare_app_sndRelative (G : Modules Y.toRingedSpace) :
    (moduleBaseChangeSquare (pullback.snd a b).toLRSHom.toShHom
      (toInverseImageBase (pullback.fst a b ≫ a)) (toInverseImageBase b)
      (sndRelativeInverseImageProjection a b)
      (toInverseImageBase_comp_sndRelativeInverseImageProjection a b).symm).natTrans.app G =
      sndRelativeInverseImageToPullback a b G := by
  unfold sndRelativeInverseImageToPullback sndRelativeInverseImageProjection
  exact moduleBaseChangeSquare_app_relativeOfFactors _ _ _ _ G

/-- The degreewise components of the underived base change map of the square of the second
projection. -/
theorem mapHomologicalComplex_moduleBaseChangeSquare_app_f_sndRelative
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) ℤ) (n : ℤ) :
    ((NatTrans.mapHomologicalComplex
      (moduleBaseChangeSquare (pullback.snd a b).toLRSHom.toShHom
        (toInverseImageBase (pullback.fst a b ≫ a)) (toInverseImageBase b)
        (sndRelativeInverseImageProjection a b)
        (toInverseImageBase_comp_sndRelativeInverseImageProjection a b).symm).natTrans
      (ComplexShape.up ℤ)).app K).f n =
      sndRelativeInverseImageToPullback a b (K.X n) := by
  rw [NatTrans.mapHomologicalComplex_app_f]
  unfold sndRelativeInverseImageToPullback sndRelativeInverseImageProjection
  exact moduleBaseChangeSquare_app_relativeOfFactors _ _ _ _ (K.X n)

end Snd

end Stacks.DeRhamDirectImage
