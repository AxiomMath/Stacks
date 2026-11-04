module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ExtensionByZeroSupported
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisComparisonStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRestrictionFiber

/-!
# Invertibility of maps of modules on algebraic spaces, read on geometric stalks

Let `f : Y ⟶ X` be an étale morphism of algebraic spaces over a scheme `S`, write `(-)|_Y` for
restriction of `𝒪_X`-modules along `f` and `f_!` for extension by zero.  This file records four
facts about invertibility of maps of modules, all read on the stalks at geometric points.

* A map of `𝒪_X`-modules is invertible as soon as it is invertible on every geometric stalk.
* The restriction to `Y` of a map is invertible on the stalk at `ȳ` as soon as the map itself is
  invertible on the stalk at the image `f(ȳ)` (Equation 08GT).
* Extension by zero reflects isomorphisms: if `f_!φ` is invertible then so is `φ`, since by
  Equation 08GU the stalk of `f_!φ` at `f(ȳ)` is the direct sum of the stalks of `φ` at the lifts
  of `f(ȳ)`, one of which is `ȳ`.
* If `f` is a monomorphism (an open immersion), the unit `𝒢 ⟶ (f_!𝒢)|_Y` is invertible: the
  counit at `f_!𝒢` is invertible on stalks, a geometric point of `X` having at most one lift, so
  `f_!` of the unit is invertible by a triangle identity, and `f_!` reflects isomorphisms.

The last two are what the glueing of objects along an elementary distinguished square uses.

## Main results

* `AlgebraicGeometry.Space.isIso_of_forall_isIso_sheafFiber`
* `AlgebraicGeometry.Space.isIso_sheafFiber_etaleModulePullback_map`
* `AlgebraicGeometry.Space.isIso_of_isIso_etaleModuleLowerShriek_map`
* `AlgebraicGeometry.Space.isIso_etaleModuleLowerShriekAdjunction_unit_app_of_mono`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.Limits

/-- **A coproduct of maps which is invertible has invertible components.**  Each component is a
retract of the coproduct map. -/
theorem isIso_of_isIso_sigmaMap {C : Type*} [Category C] [HasZeroMorphisms C] {I : Type*}
    {K L : I → C} [HasCoproduct K] [HasCoproduct L] (φ : ∀ i, K i ⟶ L i)
    (hφ : IsIso (Sigma.map φ)) (i : I) : IsIso (φ i) := by
  classical
  let πK : ∐ K ⟶ K i := Sigma.desc fun j => if h : j = i then eqToHom (by rw [h]) else 0
  let πL : ∐ L ⟶ L i := Sigma.desc fun j => if h : j = i then eqToHom (by rw [h]) else 0
  have hK : Sigma.ι K i ≫ πK = 𝟙 _ := by simp [πK]
  have hL : Sigma.ι L i ≫ πL = 𝟙 _ := by simp [πL]
  have hnat : Sigma.map φ ≫ πL = πK ≫ φ i := by
    refine Sigma.hom_ext _ _ fun j => ?_
    rw [Sigma.ι_map_assoc]
    by_cases h : j = i
    · subst h
      simp [πK, πL]
    · simp [πK, πL, h]
  refine ⟨Sigma.ι L i ≫ inv (Sigma.map φ) ≫ πK, ?_, ?_⟩
  · rw [← Category.assoc, ← Sigma.ι_map, Category.assoc, IsIso.hom_inv_id_assoc, hK]
  · rw [Category.assoc, Category.assoc, ← hnat, IsIso.inv_hom_id_assoc, hL]

end CategoryTheory.Limits

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A map of modules on an algebraic space which is invertible on every geometric stalk is
invertible.** -/
theorem isIso_of_forall_isIso_sheafFiber {X : AlgebraicSpaces B S hS}
    {M N : Modules.{u, u} B S hS X.1 X.2} (g : M ⟶ N)
    (h : ∀ x : GeometricPoint B S hS X.1, IsIso ((etaleSitePoint B S hS X.1 x X.2).sheafFiber.map
      ((SheafOfModules.toSheaf (etaleRingSheaf B S hS X)).map g))) : IsIso g := by
  refine isIso_of_isIso_geometricModuleStalk B S hS X.1 X.2 (etaleRingSheaf B S hS X) g
    fun x => ?_
  exact isIso_edsModuleStalk_of_isIso_sheafFiber B S hS g x (h x)

variable {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)

/-- **Equation 08GT, on invertibility.**  The restriction along an étale morphism `f : Y ⟶ X` of
a map of `𝒪_X`-modules is invertible on the stalk at a lift `t` to `Y` of a geometric point `x̄`
of `X` as soon as the map is invertible on the stalk at `x̄`. -/
theorem isIso_sheafFiber_etaleModulePullback_map {M N : Modules.{u, u} B S hS X.1 X.2}
    (g : M ⟶ N) {x : GeometricPoint B S hS X.1} (t : GeometricPointLift B S hS f.hom x)
    (h : IsIso ((etaleSitePoint B S hS X.1 x X.2).sheafFiber.map
      ((SheafOfModules.toSheaf (etaleRingSheaf B S hS X)).map g))) :
    IsIso ((liftSitePoint B S hS f t).sheafFiber.map
      ((abelianEtaleRestriction B S hS f hf).map
        ((SheafOfModules.toSheaf (etaleRingSheaf B S hS X)).map g))) := by
  exact (NatIso.isIso_map_iff (restrictionSheafFiberIso B S hS f hf t) _).2 h

/-- **Restriction along an étale morphism `f : Y ⟶ X` inverts a map of `𝒪_X`-modules which is
invertible on the stalk at the image of every geometric point of `Y`.** -/
theorem isIso_etaleModulePullback_map_of_forall {M N : Modules.{u, u} B S hS X.1 X.2}
    (g : M ⟶ N) (h : ∀ y : GeometricPoint B S hS Y.1,
      IsIso ((etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2).sheafFiber.map
        ((SheafOfModules.toSheaf (etaleRingSheaf B S hS X)).map g))) :
    IsIso ((etaleModulePullback.{u, u} B S hS f hf).map g) := by
  refine isIso_of_forall_isIso_sheafFiber B S hS _ fun y => ?_
  have h₁ : IsIso ((etaleSitePoint B S hS Y.1 y Y.2).sheafFiber.map
      ((abelianEtaleRestriction B S hS f hf).map
        ((SheafOfModules.toSheaf (etaleRingSheaf B S hS X)).map g))) :=
    isIso_sheafFiber_etaleModulePullback_map B S hS f hf g (selfLift B S hS f y) (h y)
  exact h₁

/-- **Extension by zero along an étale morphism reflects isomorphisms of modules.** -/
theorem isIso_of_isIso_etaleModuleLowerShriek_map {M N : Modules.{u, u} B S hS Y.1 Y.2}
    (g : M ⟶ N) (hg : IsIso ((etaleModuleLowerShriek B S hS f hf).map g)) : IsIso g := by
  refine isIso_of_forall_isIso_sheafFiber B S hS g fun y => ?_
  let x := geometricPointMap f.hom y
  let a := (SheafOfModules.toSheaf (etaleRingSheaf B S hS Y)).map g
  -- the abelian extension by zero of the underlying map is invertible
  have h₁ : IsIso ((abelianEtaleExtensionByZero B S hS f hf).map a) := by
    refine (NatIso.isIso_map_iff (etaleModuleShriekForgetIso B S hS f hf) g).2 ?_
    exact Iso.isIso_hom ((SheafOfModules.toSheaf (etaleRingSheaf B S hS X)).mapIso
      (@asIso _ _ _ _ _ hg))
  -- hence so is its stalk at `x`, hence the coproduct of the stalks at the lifts
  have h₂ : IsIso ((EtaleShriekStalk.stalkFamily B S hS f x ⋙
      Sigma.functor (GeometricPointLift B S hS f.hom x)).map a) := by
    have hn := EtaleShriekStalk.stalkExtensionByZeroIso_naturality B S hS f hf x a
    have : IsIso ((etaleSitePoint B S hS X.1 x X.2).sheafFiber.map
        ((abelianEtaleExtensionByZero B S hS f hf).map a)) :=
      Iso.isIso_hom ((etaleSitePoint B S hS X.1 x X.2).sheafFiber.mapIso
        (@asIso _ _ _ _ _ h₁))
    have h' : IsIso ((EtaleShriekStalk.stalkExtensionByZeroIso B S hS f hf x _).hom ≫
        (EtaleShriekStalk.stalkFamily B S hS f x ⋙
          Sigma.functor (GeometricPointLift B S hS f.hom x)).map a) := by
      rw [← hn]
      exact IsIso.comp_isIso' this (Iso.isIso_hom _)
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ (Iso.isIso_hom _) h'
  exact isIso_of_isIso_sigmaMap (fun t : GeometricPointLift B S hS f.hom x =>
      (liftSitePoint B S hS f t).sheafFiber.map a) h₂ (selfLift B S hS f y)

/-- **For an étale monomorphism the unit of extension by zero is invertible**: a module `𝒢` on
`Y` is the restriction to `Y` of its extension by zero. -/
theorem isIso_etaleModuleLowerShriekAdjunction_unit_app_of_mono [Mono f.hom]
    (G : Modules.{u, u} B S hS Y.1 Y.2) :
    IsIso ((etaleModuleLowerShriekAdjunction B S hS f hf).unit.app G) := by
  have hε : IsIso ((etaleModuleLowerShriekAdjunction B S hS f hf).counit.app
      ((etaleModuleLowerShriek B S hS f hf).obj G)) := by
    refine isIso_of_forall_isIso_sheafFiber B S hS _ fun x => ?_
    have := subsingleton_geometricPointLift_of_mono B S hS f.hom inferInstance x
    by_cases hx : Nonempty (GeometricPointLift B S hS f.hom x)
    · have : Unique (GeometricPointLift B S hS f.hom x) := uniqueOfSubsingleton hx.some
      exact isIso_sheafFiber_toSheaf_etaleModuleCounit B S hS f hf x _
        (EtaleShriekStalk.isIso_sheafFiber_counit_of_unique B S hS f hf x _)
    · have : IsEmpty (GeometricPointLift B S hS f.hom x) := not_nonempty_iff.1 hx
      refine isIso_of_source_target_iso_zero _ ?_ ?_
      · exact (isZero_sheafFiber_toSheaf_etaleModuleShriek B S hS f hf x _
          (EtaleShriekStalk.isZero_stalkExtensionByZero_of_isEmpty B S hS f hf x _)).isoZero
      · exact (isZero_sheafFiber_toSheaf_etaleModuleShriek B S hS f hf x _
          (EtaleShriekStalk.isZero_stalkExtensionByZero_of_isEmpty B S hS f hf x _)).isoZero
  have hs : IsIso ((etaleModuleLowerShriek B S hS f hf).map
      ((etaleModuleLowerShriekAdjunction B S hS f hf).unit.app G)) := by
    have ht := (etaleModuleLowerShriekAdjunction B S hS f hf).left_triangle_components G
    have : IsIso ((etaleModuleLowerShriek B S hS f hf).map
        ((etaleModuleLowerShriekAdjunction B S hS f hf).unit.app G) ≫
          (etaleModuleLowerShriekAdjunction B S hS f hf).counit.app
            ((etaleModuleLowerShriek B S hS f hf).obj G)) := by
      rw [ht]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((etaleModuleLowerShriekAdjunction B S hS f hf).counit.app
      ((etaleModuleLowerShriek B S hS f hf).obj G))
  exact isIso_of_isIso_etaleModuleLowerShriek_map B S hS f hf _ hs

section Square

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- **At a geometric point of the open subspace of an elementary distinguished square, the
extension by zero along `j_V` of the counit of extension by zero along `P ⟶ V` is invertible on
stalks.**  Every lift of the point to `V` lifts uniquely to `P = U ×_X V`. -/
theorem isIso_sheafFiber_edsEtale_shriek_map_edsSnd_counit_of_mem
    (N : Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2)
    (x : GeometricPoint B S hS W.1)
    (hx : x.image ∈ Set.range (pointsMap B S hS Uo.toFunctor Uo.ι)) :
    IsIso ((etaleSitePoint B S hS W.1 x W.2).sheafFiber.map
      ((SheafOfModules.toSheaf (etaleRingSheaf B S hS W)).map
        ((etaleModuleLowerShriek B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq)).map
          ((etaleModuleLowerShriekAdjunction B S hS (edsSnd B S hS hsq)
            (isEtale_edsSnd B S hS hsq)).counit.app N)))) := by
  refine isIso_sheafFiber_toSheaf_etaleModuleShriek_map_of_lifts B S hS
    (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq) x _ fun t => ?_
  have : Unique (GeometricPointLift B S hS (edsSnd B S hS hsq).hom
      (liftGeometricPoint B S hS (edsEtaleHom B S hS hsq) t)) :=
    unique_geometricPointLift_edsSnd_of_mem B S hS hsq
      (liftGeometricPoint B S hS (edsEtaleHom B S hS hsq) t)
      (by rw [geometricPointMap_liftGeometricPoint]; exact hx)
  exact isIso_sheafFiber_toSheaf_etaleModuleCounit B S hS (edsSnd B S hS hsq)
    (isEtale_edsSnd B S hS hsq) (liftGeometricPoint B S hS (edsEtaleHom B S hS hsq) t) N
    (EtaleShriekStalk.isIso_sheafFiber_counit_of_unique B S hS (edsSnd B S hS hsq)
      (isEtale_edsSnd B S hS hsq) (liftGeometricPoint B S hS (edsEtaleHom B S hS hsq) t) _)

end Square

end AlgebraicGeometry.Space
