module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleSheafifiedBaseChangeComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleModuleComparisonUnivLE
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentAbelianUnivLE
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeNaturality
public import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-!
# The inverse image of sheaves of modules on small étale sites, at any section universe

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and `φ : x ⟶ y` an arrow of `𝒳`
lying over a morphism of schemes `a : U ⟶ V`. The inverse image `a_{small}^*` of sheaves of
modules on the small étale sites is the inverse image of presheaves of modules along the map
`a_{small}^♯` of **Stacks 06WC**, followed by sheafification on `U_ét`.

`AlgebraicGeometry.Stack.sheafifiedPullbackComparison`, the adjunction
`AlgebraicGeometry.Stack.sheafifiedPullbackComparisonAdjunction` and the sheafification
`AlgebraicGeometry.Stack.smallEtaleSheafificationAdjunction` of the small étale site are stated
for modules whose sections live in the universe `u` of the schemes. The higher direct images
along a 1-morphism of algebraic stacks have sections in `u + 1`, so this file states the same
objects for sections in any universe `m` with `UnivLE.{u, m}`. At `m = u` each of them is the
corresponding object at `u`, by `rfl`: the instance arguments the two spellings are built from
are propositions.

The universe-sensitive inputs are existence statements, supplied here as instances: the
sheafification of presheaves of abelian groups with sections in `m` on a small étale site, which
is essentially small in `Type u` and hence in `Type m`; the fact that this sheafification inverts
exactly the locally bijective maps; and the left adjoint of the direct image of presheaves of
modules along the structure map of the morphism of ringed sites `ε_a` of **Stacks 070R (2)**.

## Main definitions

* `AlgebraicGeometry.Stack.smallEtaleSheafificationAdjunctionUnivLE`: the sheafification of
  presheaves of modules on the small étale site below an object of `𝒳`, at section universe `m`.
* `AlgebraicGeometry.Stack.sheafifiedPullbackComparisonUnivLE`: the inverse image `a_{small}^*`
  of sheaves of modules below an arrow of `𝒳`, at section universe `m`.
* `AlgebraicGeometry.Stack.sheafifiedPullbackComparisonAdjunctionUnivLE`: it is left adjoint to
  the direct image along `ε_a`.

## Main results

* `AlgebraicGeometry.Stack.sheafifiedPullbackComparisonUnivLE_eq`: at `m = u` the inverse image
  is `AlgebraicGeometry.Stack.sheafifiedPullbackComparison`.

## References

* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w m r u₁ v₁ u₂ v₂

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{r}} {S : Cᵒᵖ ⥤ RingCat.{r}}

/-- **The pullback of presheaves of modules only depends on the map of presheaves of rings**, at
a universe `m` of the module sections unrelated to the universe `r` of the rings. Two equal maps
`φ = ψ` of presheaves of rings have isomorphic pullback functors, a left adjoint being determined
by its right adjoint. `PresheafOfModules.pullbackCongr` is the case `m = r`. -/
noncomputable def pullbackCongrUniv {φ ψ : S ⟶ F.op ⋙ R} (hφψ : φ = ψ)
    [(pushforward.{m} φ).IsRightAdjoint] [(pushforward.{m} ψ).IsRightAdjoint] :
    pullback.{m} φ ≅ pullback.{m} ψ :=
  Adjunction.leftAdjointUniq (pullbackPushforwardAdjunction.{m} φ)
    ((pullbackPushforwardAdjunction.{m} ψ).ofNatIsoRight
      (eqToIso (congrArg (fun k => pushforward.{m} k) hφψ.symm)))

/-- `PresheafOfModules.pullbackCongr` is `PresheafOfModules.pullbackCongrUniv` at module universe
the universe of the rings. -/
theorem pullbackCongr_eq_pullbackCongrUniv {φ ψ : S ⟶ F.op ⋙ R} (hφψ : φ = ψ)
    [(pushforward.{r} φ).IsRightAdjoint] [(pushforward.{r} ψ).IsRightAdjoint] :
    pullbackCongr hφψ = pullbackCongrUniv.{r} hφψ :=
  rfl

end PresheafOfModules

namespace AlgebraicGeometry.SmallEtale

variable (E : BigEtaleSite.{u})

/-- **The direct image of presheaves of modules with sections in `m` along the structure map of
`ε_a` has a left adjoint**, the small étale site of the target being essentially small in
`Type u`, hence in `Type m`. This is
`AlgebraicGeometry.SmallEtale.presheafPushforward_smallEtaleStructureMapRing_isRightAdjoint` at
an arbitrary section universe `m` containing `u`. -/
instance (priority := low) presheafPushforward_smallEtaleStructureMapRing_isRightAdjoint_univLE
    [UnivLE.{u, m}]
    {X Y : E.Scheme} (a : X ⟶ Y) :
    (PresheafOfModules.pushforward.{m}
      (smallEtaleStructureMapRing E a).hom).IsRightAdjoint :=
  haveI : EssentiallySmall.{m} (SmallEtale E Y.obj Y.property) :=
    essentiallySmall_trans_univLE (inferInstance : EssentiallySmall.{u} (SmallEtale E Y.obj
      Y.property))
  haveI : LocallySmall.{m} (SmallEtale E X.obj X.property) :=
    locallySmall_trans_univLE (inferInstance : LocallySmall.{u} (SmallEtale E X.obj X.property))
  PresheafOfModules.isRightAdjoint_pushforward_of_essentiallySmall_univLE.{m}
    (show (structureSheaf E Y.obj Y.property).obj ⟶
        (smallEtaleBaseChange E a).op ⋙ (structureSheaf E X.obj X.property).obj from
      (smallEtaleStructureMapRing E a).hom)

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

section Comparison

variable (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
  {x y : 𝒳} (φ : x ⟶ y) [UnivLE.{u, m}]

omit [UnivLE.{u, m}] in
/-- At `m = u` the comparison map is `AlgebraicGeometry.Stack.restrictModulePullbackComparison`. -/
theorem restrictModulePullbackComparisonUnivLE_eq_comparison
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ hτ).obj) :
    restrictModulePullbackComparisonUnivLE.{u, v, w, u} B E h S hS p hp φ τ hτ F =
      restrictModulePullbackComparison B E h S hS p hp φ τ hτ F :=
  rfl

/-- **The inverse image `a_{small}^*` of sheaves of modules, at section universe `m`.** For an
arrow `φ : x ⟶ y` of `𝒳` lying over `a : U ⟶ V`, the underlying presheaf of modules of a sheaf on
`V_ét`, pulled back along the map `a_{small}^♯` of **Stacks 06WC**, and sheafified on `U_ét`. At
`m = u` it is `AlgebraicGeometry.Stack.sheafifiedPullbackComparison`. -/
noncomputable def sheafifiedPullbackComparisonUnivLE :
    SheafOfModules.{m} (SmallEtale.structureSheaf E (p.obj y).left.1
        (contains_base B E h S hS p y)) ⥤
      SheafOfModules.{m} (SmallEtale.structureSheaf E (p.obj x).left.1
        (contains_base B E h S hS p x)) :=
  SheafOfModules.forget _ ⋙
    PresheafOfModules.pullback.{m}
      (F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ))
      (smallEtaleStructureComparison B E h S hS p hp φ τ hτ) ⋙
      PresheafOfModules.sheafification
        (R₀ := (SmallEtale.structureSheaf E (p.obj x).left.1
          (contains_base B E h S hS p x)).obj) (𝟙 _)

omit [UnivLE.{u, m}] in
/-- At `m = u` the inverse image of sheaves of modules is
`AlgebraicGeometry.Stack.sheafifiedPullbackComparison`. -/
theorem sheafifiedPullbackComparisonUnivLE_eq :
    sheafifiedPullbackComparisonUnivLE.{u, v, w, u} B E h S hS p hp τ hτ φ =
      sheafifiedPullbackComparison B E h S hS p hp τ hτ φ :=
  rfl

/-- The comparison of `AlgebraicGeometry.Stack.sheafifiedPullbackComparisonUnivLE` with the
construction of the pullback of sheaves of modules along `ε_a` out of the pullback of presheaves
of modules and sheafification, read at the map `a_{small}^♯` of **Stacks 06WC** rather than at
the structure map of `ε_a` itself. This is
`AlgebraicGeometry.Stack.pullbackConstructionComparisonIso` at section universe `m`. -/
noncomputable def pullbackConstructionComparisonIsoUnivLE :
    SheafOfModules.forget (SmallEtale.structureSheaf E (p.obj y).left.1
          (contains_base B E h S hS p y)) ⋙
        PresheafOfModules.pullback.{m} (SmallEtale.smallEtaleStructureMapRing E
          (smallEtaleBaseMorphism B E h S hS p φ)).hom ⋙
        PresheafOfModules.sheafification
          (R₀ := (SmallEtale.structureSheaf E (p.obj x).left.1
            (contains_base B E h S hS p x)).obj) (𝟙 _) ≅
      sheafifiedPullbackComparisonUnivLE B E h S hS p hp τ hτ φ :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
    (@PresheafOfModules.pullbackCongrUniv.{m} _ _ _ _ _ _ _ _ _
      (smallEtaleStructureComparison_eq_smallEtaleStructureMapRing B E h S hS p hp τ hτ
        φ).symm inferInstance
      (isRightAdjoint_pushforward_smallEtaleStructureComparison_univLE B E h S hS p hp φ τ
        hτ)) _)

/-- **The inverse image of sheaves of modules is left adjoint to the direct image along `ε_a`**,
at section universe `m`: the adjunction building the pullback of sheaves of modules out of
presheaves, transported along
`AlgebraicGeometry.Stack.pullbackConstructionComparisonIsoUnivLE`. This is
`AlgebraicGeometry.Stack.sheafifiedPullbackComparisonAdjunction` at section universe `m`. -/
noncomputable def sheafifiedPullbackComparisonAdjunctionUnivLE :
    sheafifiedPullbackComparisonUnivLE B E h S hS p hp τ hτ φ ⊣
      SheafOfModules.pushforward.{m} (SmallEtale.smallEtaleStructureMapRing E
        (smallEtaleBaseMorphism B E h S hS p φ)) :=
  (SheafOfModules.PullbackConstruction.adjunction.{m}
    (SmallEtale.smallEtaleStructureMapRing E
      (smallEtaleBaseMorphism B E h S hS p φ))).ofNatIsoLeft
      (pullbackConstructionComparisonIsoUnivLE B E h S hS p hp τ hτ φ)

end Comparison

end AlgebraicGeometry.Stack

end
