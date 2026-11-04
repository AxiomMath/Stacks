module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentDerivedHom
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.ExtSequence
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.ExtensionByZeroBaseChangeDerived
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.DerivedAdjunction
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
public import StacksFrontier.AlgebraicGeometry.Perfect.Approximation.OpenSubscheme
public import StacksFrontier.AlgebraicGeometry.Perfect.LimitHomDescent.ExtensionByZero

/-!
# Derived morphism sets out of an extension by zero, along a relative descent situation

Let `j : U ⟶ X` be the inclusion of an open subspace of a ringed space. Extension by zero `j_!`
is left adjoint to restriction `j^*`, and `j^* j_! ≅ id`; on unbounded derived categories the
same holds for the induced functors `D(j_!)` and `D(j^*)` (Stacks 08BT). Consequently, for an
object `E` isomorphic to `D(j_!)D(j^*)E'`, restriction to `U` is a bijection
`Hom(E, F) ≅ Hom(E|_U, F|_U)` for every `F`.

In the relative descent situation of Stacks 0DI6, extension by zero commutes with the derived
pullbacks to the stages and to the limit, so this bijection holds at every stage and at the limit
for the derived pullbacks of `E = j_{A!}j_A^*M`, `A ⊆ X₀` a quasi-compact open. Restriction to
`A` is a map of systems of derived morphism sets, so the colimit statement of Stacks 0DI7 for
`(j_{A!}j_A^*M, L₀)` on `X₀` is equivalent to the same statement for `(M|_A, L₀|_A)` on the
situation restricted to `A`.

## Main results

* `AlgebraicGeometry.bijective_derivedPullback_map_of_extensionRestriction`: the same for the
  derived pullback along an open immersion of schemes, at the derived pullback of an extension
  by zero along an arbitrary morphism whose preimage of the open is the range of the immersion.
* `AlgebraicGeometry.RelativeDescentSituation.homDescent_derivedExtensionRestriction_iff`: the
  colimit statement of Stacks 0DI7 at `(j_{A!}j_A^*M, L₀)` is the same statement at
  `(M|_A, L₀|_A)` for the situation restricted to `A`.

## References

* [Stacks Project, Tag 08BT](https://stacks.math.columbia.edu/tag/08BT)
* [Stacks Project, Tag 0DI7](https://stacks.math.columbia.edu/tag/0DI7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open RingedSpaceModuleAdjunction ExtensionByZeroModules
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.Cohomology.PerfectComplexTriangles (mapDerivedCategoryCompIso
  mapDerivedCategoryIsoOfNatIso)

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] preservesFiniteLimits_jStar preservesFiniteColimits_jStar

universe u

namespace AlgebraicGeometry

open Stacks.ExtensionByZero (derivedExtensionRestriction derivedRestriction)

/-! ### Open immersions of schemes -/

section OpenImmersion

variable {X Y Z : Scheme.{u}}

/-- Derived pullback along the inclusion of an open subscheme `V` is bijective on morphisms out
of an object isomorphic to an extension by zero of a restriction to `V`. -/
theorem bijective_derivedPullback_opensι_map {V : Y.Opens}
    {E E' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))}
    (e : E ≅ (derivedExtensionRestriction (structureSheafRing Y.toRingedSpace) V).obj E')
    (F : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))) :
    Function.Bijective (fun φ : E ⟶ F => (derivedPullback V.ι.toLRSHom.toShHom).map φ) :=
  Stacks.LimitHomDescent.bijective_map_of_natIso (Stacks.LimitHomDescent.pbOpensιIso V)
    (Stacks.LimitHomDescent.bijective_restriction_map_of_iso _ V e F)

/-- **Derived pullback along an open immersion `ι` is bijective on morphisms out of an object
isomorphic to an extension by zero of a restriction to the range of `ι`.** -/
theorem bijective_derivedPullback_map_of_isOpenImmersion (ι : Z ⟶ Y) [IsOpenImmersion ι]
    {E E' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))}
    (e : E ≅ (derivedExtensionRestriction (structureSheafRing Y.toRingedSpace) ι.opensRange).obj E')
    (F : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))) :
    Function.Bijective (fun φ : E ⟶ F => (derivedPullback ι.toLRSHom.toShHom).map φ) :=
  Stacks.LimitHomDescent.bijective_map_of_natIso
    (Stacks.DerivedPullback.schemeFactorIso ι.isoOpensRange.hom ι.opensRange.ι ι
      ι.isoOpensRange_hom_ι).symm
    ((Stacks.DerivedPullback.bijective_derivedPullback_map
      ι.isoOpensRange.hom.toLRSHom.toShHom ι.isoOpensRange.inv.toLRSHom.toShHom
      (congrArg (fun m => m.toLRSHom.toShHom) ι.isoOpensRange.hom_inv_id)
      (congrArg (fun m => m.toLRSHom.toShHom) ι.isoOpensRange.inv_hom_id)
      ((derivedPullback ι.opensRange.ι.toLRSHom.toShHom).obj E)
      ((derivedPullback ι.opensRange.ι.toLRSHom.toShHom).obj F)).comp
      (bijective_derivedPullback_opensι_map e F))

end OpenImmersion

/-! ### Base change of extension by zero -/

/-- **Extension by zero of a restriction commutes with derived pullback**, objectwise:
`Lf^*(j_{U!}j_U^*M) ≅ j_{U'!}j_{U'}^*(Lf^*M)` with `U' = f⁻¹U`. -/
def derivedPullbackExtensionRestrictionObjIso {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (U : Opens Y.carrier) (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    (derivedPullback f).obj ((derivedExtensionRestriction (structureSheafRing Y) U).obj M) ≅
      (derivedExtensionRestriction (structureSheafRing X) ((Opens.map f.hom.base).obj U)).obj
        ((derivedPullback f).obj M) :=
  (derivedPullback f).mapIso
      ((mapDerivedCategoryCompIso (jStar U (structureSheafRing Y))
        (jShriek U (structureSheafRing Y))).symm.app M) ≪≫
    (Stacks.Cohomology.ExtensionByZeroBaseChangeDerived.derivedPullbackExtensionRestrictionIso
      f U).app M ≪≫
    (mapDerivedCategoryCompIso _ _).app ((derivedPullback f).obj M)

/-- **Derived pullback along an open immersion is bijective on morphisms out of the derived
pullback of an extension by zero**, when the range of the immersion is the preimage of the
open. -/
theorem bijective_derivedPullback_map_of_extensionRestriction {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (ι : Z ⟶ X) [IsOpenImmersion ι] (U : Y.Opens) (hU : ι.opensRange = f ⁻¹ᵁ U)
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)))
    (F : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :
    Function.Bijective (fun φ : (derivedPullback f.toLRSHom.toShHom).obj
        ((derivedExtensionRestriction (structureSheafRing Y.toRingedSpace) U).obj M) ⟶ F =>
      (derivedPullback ι.toLRSHom.toShHom).map φ) :=
  bijective_derivedPullback_map_of_isOpenImmersion ι
    (derivedPullbackExtensionRestrictionObjIso f.toLRSHom.toShHom U M ≪≫
      eqToIso (by rw [hU]; rfl)) F

end AlgebraicGeometry

namespace Stacks.DerivedPullback

variable {X Y Z : RingedSpace.{u, u}}

/-- The map on derived morphism sets of a factorisation is natural in the first argument. -/
private theorem factorHom_precomp (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k)
    {K K' L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z))} (a : K' ⟶ K)
    (φ : (derivedPullback g).obj K ⟶ (derivedPullback g).obj L) :
    factorHom f g k h K' L ((derivedPullback g).map a ≫ φ) =
      (derivedPullback k).map a ≫ factorHom f g k h K L φ := by
  have nat : (factorIso f g k h).inv.app K' ≫ (derivedPullback f).map ((derivedPullback g).map a) =
      (derivedPullback k).map a ≫ (factorIso f g k h).inv.app K :=
    ((factorIso f g k h).inv.naturality a).symm
  simp only [factorHom, Iso.homCongr_apply, Functor.map_comp, Iso.app_inv, Iso.app_hom,
    Category.assoc]
  rw [reassoc_of% nat]

end Stacks.DerivedPullback

namespace AlgebraicGeometry.RelativeDescentSituation

open Stacks.ExtensionByZero (derivedExtensionRestriction derivedRestriction)

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : RelativeDescentSituation.{u, u} I)

attribute [local implicit_reducible] restrict

section IsoFst

variable {K K' L :
  DerivedCategory (SheafOfModules.{u} (structureSheafRing D.X₀.left.toRingedSpace))}

private theorem homTransition_precomp {i j : D.LaterIndex} (h : i.1 ≤ j.1) (a : K' ⟶ K)
    (φ : (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).obj K ⟶
      (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).obj L) :
    D.homTransition K' L h ((derivedPullback (D.toFixedStage i).toLRSHom.toShHom).map a ≫ φ) =
      (derivedPullback (D.toFixedStage j).toLRSHom.toShHom).map a ≫ D.homTransition K L h φ :=
  Stacks.DerivedPullback.factorHom_precomp _ _ _ _ a φ

private theorem homComparison_precomp (i : D.LaterIndex) (a : K' ⟶ K)
    (φ : (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).obj K ⟶
      (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).obj L) :
    D.homComparison K' L i ((derivedPullback (D.toFixedStage i).toLRSHom.toShHom).map a ≫ φ) =
      (derivedPullback D.limitToFixedStage.toLRSHom.toShHom).map a ≫ D.homComparison K L i φ :=
  Stacks.DerivedPullback.factorHom_precomp _ _ _ _ a φ

/-- The colimit statement of Stacks 0DI7 depends on its first argument only up to
isomorphism. -/
private theorem homDescent_of_iso_fst' (e : K ≅ K') (hK : D.HomDescent K L) :
    D.HomDescent K' L := by
  obtain ⟨hs, hi⟩ := hK
  refine ⟨fun ψ => ?_, fun i φ φ' hφ => ?_⟩
  · obtain ⟨i, φ, hφ⟩ := hs ((derivedPullback D.limitToFixedStage.toLRSHom.toShHom).map e.hom ≫ ψ)
    refine ⟨i, (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).map e.inv ≫ φ, ?_⟩
    rw [homComparison_precomp, hφ, ← Functor.map_comp_assoc, e.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  · obtain ⟨j, hij, hj⟩ := hi i
      ((derivedPullback (D.toFixedStage i).toLRSHom.toShHom).map e.hom ≫ φ)
      ((derivedPullback (D.toFixedStage i).toLRSHom.toShHom).map e.hom ≫ φ')
      (by rw [homComparison_precomp, homComparison_precomp, hφ])
    refine ⟨j, hij, ?_⟩
    rw [homTransition_precomp, homTransition_precomp] at hj
    simpa only [← Functor.map_comp_assoc, e.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.id_comp] using
      congrArg (fun t => (derivedPullback (D.toFixedStage j).toLRSHom.toShHom).map e.inv ≫ t) hj

end IsoFst

section Extension

variable (A : D.X₀.left.Opens) (hA : IsCompact (A : Set D.X₀.left))
  (M L₀ : DerivedCategory (SheafOfModules.{u} (structureSheafRing D.X₀.left.toRingedSpace)))

/-- The square comparison of derived morphism sets is bijective at the derived pullback of
`j_{U!}j_U^*M`, when the range of `r` is the preimage of `U`. -/
private theorem bijective_schemeFactorSquareHom_derivedExtensionRestriction
    {V W Z : Scheme.{u}} (r : V ⟶ W) [IsOpenImmersion r] (g : W ⟶ Z) (U : Z.Opens)
    (e : V ⟶ (U : Scheme.{u})) (h : r ≫ g = e ≫ U.ι) (hU : r.opensRange = g ⁻¹ᵁ U)
    (M L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))) :
    Function.Bijective (Stacks.DerivedPullback.schemeFactorSquareHom r g e U.ι h
      ((derivedExtensionRestriction (structureSheafRing Z.toRingedSpace) U).obj M) L) := by
  have key : Stacks.DerivedPullback.schemeFactorSquareHom r g e U.ι h
      ((derivedExtensionRestriction (structureSheafRing Z.toRingedSpace) U).obj M) L =
      (Iso.homCongr ((Stacks.DerivedPullback.schemeFactorSquareIso r g e U.ι h).app _).symm
        ((Stacks.DerivedPullback.schemeFactorSquareIso r g e U.ι h).app L).symm) ∘
        (derivedPullback r.toLRSHom.toShHom).map := by
    funext φ
    exact Stacks.DerivedPullback.schemeFactorSquareHom_eq _ _ _ _ _ _ _ φ
  rw [key]
  exact (Equiv.bijective _).comp
    (bijective_derivedPullback_map_of_extensionRestriction g r U hU M _)

/-- **Restriction to `Aᵢ` is bijective at a stage on morphisms out of the derived pullback of
`j_{A!}j_A^*M`.** -/
theorem bijective_homRestrictToOpen_derivedExtensionRestriction (i : D.LaterIndex) :
    Function.Bijective (D.homRestrictToOpen
      ((derivedExtensionRestriction (structureSheafRing D.X₀.left.toRingedSpace) A).obj M)
      L₀ A hA i) :=
  bijective_schemeFactorSquareHom_derivedExtensionRestriction (D.restrictToAmbient A hA i)
    (D.toFixedStage i) A _ (D.restrictToAmbient_comp_toFixedStage A hA i)
    (D.opensRange_restrictToAmbient A hA i) M L₀

/-- **Restriction to `A` is bijective at the limit on morphisms out of the derived pullback of
`j_{A!}j_A^*M`.** -/
theorem bijective_homRestrictToOpenLimit_derivedExtensionRestriction :
    Function.Bijective (D.homRestrictToOpenLimit
      ((derivedExtensionRestriction (structureSheafRing D.X₀.left.toRingedSpace) A).obj M)
      L₀ A hA) :=
  bijective_schemeFactorSquareHom_derivedExtensionRestriction (D.restrictToAmbientLimit A hA)
    D.limitToFixedStage A _ (D.restrictToAmbientLimit_comp_limitToFixedStage A hA)
    (D.opensRange_restrictToAmbientLimit A hA) M L₀

/-- **The restriction of `j_{A!}j_A^*M` to `A` is the restriction of `M`.** -/
def derivedPullbackOpensιExtensionRestrictionIso :
    (derivedPullback A.ι.toLRSHom.toShHom).obj
        ((derivedExtensionRestriction (structureSheafRing D.X₀.left.toRingedSpace) A).obj M) ≅
      (derivedPullback A.ι.toLRSHom.toShHom).obj M :=
  (Stacks.LimitHomDescent.pbOpensιIso A).app _ ≪≫
    (Stacks.LimitHomDescent.restrictionExtensionIso
      (structureSheafRing D.X₀.left.toRingedSpace) A).app
      ((derivedRestriction (structureSheafRing D.X₀.left.toRingedSpace) A).obj M) ≪≫
    (Stacks.LimitHomDescent.pbOpensιIso A).symm.app M

/-- **Restriction to `A` transfers the colimit statement of Stacks 0DI7**, in both directions,
once it is bijective at every stage and at the limit. -/
theorem homDescent_iff_restrictHomDescent_of_bijective (K : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing D.X₀.left.toRingedSpace)))
    (bij : ∀ i, Function.Bijective (D.homRestrictToOpen K L₀ A hA i))
    (bijl : Function.Bijective (D.homRestrictToOpenLimit K L₀ A hA)) :
    D.HomDescent K L₀ ↔ D.RestrictHomDescent K L₀ A hA := by
  constructor
  · rintro ⟨hs, hi⟩
    refine ⟨fun ψ' => ?_, fun i φ₁ φ₂ h => ?_⟩
    · obtain ⟨ψ, hψ⟩ := bijl.surjective ψ'
      obtain ⟨i, φ, hφ⟩ := hs ψ
      exact ⟨i, D.homRestrictToOpen K L₀ A hA i φ,
        (D.homComparison_homRestrictToOpen K L₀ A hA i φ).trans
          ((congrArg (D.homRestrictToOpenLimit K L₀ A hA) hφ).trans hψ)⟩
    · obtain ⟨ψ₁, hψ₁⟩ := (bij i).surjective φ₁
      obtain ⟨ψ₂, hψ₂⟩ := (bij i).surjective φ₂
      obtain ⟨j, hij, hj⟩ := hi i ψ₁ ψ₂ (bijl.injective
        ((D.homComparison_homRestrictToOpen K L₀ A hA i ψ₁).symm.trans
          ((congrArg _ hψ₁).trans (h.trans ((congrArg _ hψ₂).symm.trans
            (D.homComparison_homRestrictToOpen K L₀ A hA i ψ₂))))))
      exact ⟨j, hij, (congrArg _ hψ₁.symm).trans
        ((D.homTransition_homRestrictToOpen K L₀ A hA hij ψ₁).trans
          ((congrArg _ hj).trans ((D.homTransition_homRestrictToOpen K L₀ A hA hij ψ₂).symm.trans
            (congrArg _ hψ₂))))⟩
  · rintro ⟨hs, hi⟩
    refine ⟨fun ψ => ?_, fun i φ φ' hφ => ?_⟩
    · obtain ⟨i, φ', hφ'⟩ := hs (D.homRestrictToOpenLimit K L₀ A hA ψ)
      obtain ⟨φ, hφ⟩ := (bij i).surjective φ'
      exact ⟨i, φ, bijl.injective ((D.homComparison_homRestrictToOpen K L₀ A hA i φ).symm.trans
        ((congrArg _ hφ).trans hφ'))⟩
    · obtain ⟨j, hij, hj⟩ := hi i (D.homRestrictToOpen K L₀ A hA i φ)
        (D.homRestrictToOpen K L₀ A hA i φ')
        ((D.homComparison_homRestrictToOpen K L₀ A hA i φ).trans
          ((congrArg (D.homRestrictToOpenLimit K L₀ A hA) hφ).trans
            (D.homComparison_homRestrictToOpen K L₀ A hA i φ').symm))
      exact ⟨j, hij, (bij j).injective
        ((D.homTransition_homRestrictToOpen K L₀ A hA hij φ).symm.trans
          (hj.trans (D.homTransition_homRestrictToOpen K L₀ A hA hij φ')))⟩

/-- **The colimit statement of Stacks 0DI7 at an extension by zero.** For a quasi-compact open
`A ⊆ X₀`, the comparison `colim_i Hom(Lf_{i0}^*(j_{A!}j_A^*M), Lf_{i0}^*L₀) ⟶
Hom(Lf₀^*(j_{A!}j_A^*M), Lf₀^*L₀)` is bijective exactly when the comparison for `M|_A` and
`L₀|_A` along the situation restricted to `A` is. -/
theorem homDescent_derivedExtensionRestriction_iff :
    D.HomDescent
        ((derivedExtensionRestriction (structureSheafRing D.X₀.left.toRingedSpace) A).obj M) L₀ ↔
      D.RestrictHomDescent M L₀ A hA :=
  (D.homDescent_iff_restrictHomDescent_of_bijective A hA L₀ _
    (D.bijective_homRestrictToOpen_derivedExtensionRestriction A hA M L₀)
    (D.bijective_homRestrictToOpenLimit_derivedExtensionRestriction A hA M L₀)).trans
    ⟨homDescent_of_iso_fst' (D.restrict A hA) (D.derivedPullbackOpensιExtensionRestrictionIso A M),
      homDescent_of_iso_fst' (D.restrict A hA)
        (D.derivedPullbackOpensιExtensionRestrictionIso A M).symm⟩

end Extension

end AlgebraicGeometry.RelativeDescentSituation

end
