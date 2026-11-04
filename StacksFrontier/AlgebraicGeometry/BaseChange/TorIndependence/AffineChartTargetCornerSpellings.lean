module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineOpenDerivedStalk
public import
  StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeCohomologyFlatExtension
public import StacksFrontier.Homology.Tor.DerivedExtensionLocalizationComp

/-!
# The three spellings of the target corner of an affine chart

Let `i : Spec A ⟶ X` present an affine open `U` of a scheme, let `y` be a point of `Spec A` and
let `K` be an object of `D(𝒪_X)` with quasi-coherent cohomology sheaves. The germ localization
`RΓ(U, K) ⊗ᴸ_A 𝒪_{Spec A, y}` of the derived sections is identified with the derived stalk of `K`
at `i y` in three different ways in the library, and the affine reduction of Stacks 0DJ8 has to
move between them:

1. by `AlgebraicGeometry.derivedStalkAffineSectionsIso`, whose right-hand side is the derived
   stalk **extended** along the germ comparison `𝒪_{X, i y} ⟶ 𝒪_{Spec A, y}`. This is the
   spelling of `AlgebraicGeometry.BaseChangeChart.extendScalars_map_sectionsBaseChangeMap_eq`,
   the morphism factor of the chart comparison;
2. over the local ring `𝒪_{X, i y}` itself, with the passage from `𝒪_X(U)` to a further
   `𝒪_{X, i y}`-algebra done by `RingTheory.TorIndependence.restrictScalarsDerivedExtendCompIso`
   and the stalk of a derived pullback by `AlgebraicGeometry.derivedPullbackStalkIso`. This is
   the spelling of `AlgebraicGeometry.BaseChangeChart.localTail`, the tail of the chart's
   outer-rectangle comparison;
3. by `AlgebraicGeometry.derivedStalkAffineSectionsRestrictIso`, whose right-hand side is the
   derived stalk **restricted** along a given inverse `ε'` of the germ comparison. This is the
   spelling `AlgebraicGeometry.homologyDerivedStalkAffineSectionsRestrictIso` — the target
   bijection of `AlgebraicGeometry.baseChange_tfae_of_sourceBridge` — is built from.

The three differ only in how the corner's module structure is presented: (1) extends scalars
along the germ comparison, (3) restricts along its inverse, and (2) keeps the local ring and
absorbs the germ map into the localization. They are therefore interchangeable, and this module
records the equations that interchange them.

## Main definitions

* `AlgebraicGeometry.totalDerivedExtensionScalarsCompIsoRestrict`: derived extension of scalars
  along a composite whose second factor is invertible, read as extension along the first factor
  followed by restriction along the inverse of the second. This is the identification of the
  object spelling (1) produces with the one spellings (2) and (3) produce.

## Main results

* `AlgebraicGeometry.derivedStalkAffineSectionsRestrictIso_eq`: spelling (3) is spelling (1)
  followed by `AlgebraicGeometry.totalDerivedExtensionScalarsIsoRestrict`.
* `AlgebraicGeometry.derivedStalkAffineSectionsIso_hom_comp_map`: spelling (1) followed by a
  morphism out of the derived stalk is spelling (3) followed by that morphism restricted — the
  form in which a consumer holding the morphism factor of the chart comparison rewrites it into
  the spelling of the target bijection.
* `AlgebraicGeometry.derivedStalkAffineSectionsIso_hom_comp_merge`: the same with the two
  extensions of scalars on the right of spelling (1) merged, which is the shape the chart
  comparison's morphism factor actually ends in.
* `RingTheory.TorIndependence.restrictScalarsDerivedExtendCompIso_hom_app`: spelling (2)'s
  passage through the localization, written with the composition isomorphism of derived
  extension of scalars and the localization idempotence `restrictScalarsDerivedExtendIso`. This
  is what puts spelling (2) into the vocabulary of spelling (1), whose merges are composition
  isomorphisms.
* `RingTheory.TorIndependence.restrictScalarsDerivedExtendIso_hom_eq_counit`: the localization
  idempotence is the counit of the derived change-of-rings adjunction, so the triangle
  identities of the adjunction apply to it.
* `RingTheory.TorIndependence.map_unit_comp_restrictScalarsDerivedExtendCompIso_hom_app`:
  spelling (2) begins with the unit of that adjunction along the germ map, and the unit is
  absorbed: unit followed by the passage of spelling (2) is the inverse of the composition
  isomorphism, which is spelling (1)'s merge read backwards. With this and the two equations
  above, neither spelling retains anything the other does not have.

## Implementation notes

Every category, functor, object and morphism that is not the subject of the statement is a
variable: the ring the derived stalk is extended to, the complex over it and the morphism into
it are all free in
`AlgebraicGeometry.derivedStalkAffineSectionsIso_hom_comp_merge`, because `rw` matches these
composites only at reducible transparency and a statement pinned to a particular chart's rings
does not fire.

The identifications are proved at the level of the isomorphism or by naturality, never
component by component: unfolding one of these isomorphisms at a component forces the
definitional equality of two spellings of `𝒪_X(U) → 𝒪_{X, i y}` inside a term the size of the
whole comparison.

`RingTheory.TorIndependence.restrictScalarsDerivedExtendIso` is built by descending the
degreewise idempotence along the localization functor, not as the counit of an adjunction, so
the triangle identity is not available for it until the two are identified. They are identified
pointwise on localized complexes, where the two characterizing equations
`RingTheory.TorIndependence.restrictScalarsDerivedExtendIso_hom_app_Q` and
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_counit_app_eq` are the
same composite; the second is applied with its universe levels and its
`IsLeftDerivedFunctor` argument written out, since the instance it asks for is the one the
derived extension-of-scalars package carries as a field rather than as an instance.

No tag attribute is placed here. These are readings of inputs to Stacks 0DJ8, which carry no tag
either, rather than clauses of it.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars
  (totalDerivedExtensionScalars totalDerivedExtensionScalarsComp)

universe u w

namespace AlgebraicGeometry

/-! ### Extension of scalars along a composite ending in an invertible map -/

section Algebra

variable {C R₁ R₂ : Type u} [CommRing C] [CommRing R₁] [CommRing R₂]
  [HasDerivedCategory.{w} (ModuleCat.{u} C)] [HasDerivedCategory.{w} (ModuleCat.{u} R₁)]
  [HasDerivedCategory.{w} (ModuleCat.{u} R₂)]

/-- **Derived extension of scalars along `σ ∘ b` with `σ` invertible is extension along `b`,
restricted along the inverse of `σ`.** The composition isomorphism splits the extension into the
one along `b` and the one along `σ`, and
`AlgebraicGeometry.totalDerivedExtensionScalarsIsoRestrict` replaces the second by restriction
of scalars along the given inverse `ε'` of `σ`.

This is the identification of the object the target corner is read into by
`AlgebraicGeometry.derivedStalkAffineSectionsIso` — an extension of scalars — with the one
`AlgebraicGeometry.derivedStalkAffineSectionsRestrictIso` and
`AlgebraicGeometry.BaseChangeChart.localTail` read it into, where the local ring is kept and the
germ comparison appears as a restriction. -/
public def totalDerivedExtensionScalarsCompIsoRestrict (b : C →+* R₁) (σ : R₁ →+* R₂)
    (ε' : R₂ →+* R₁) (h₁ : ∀ x, ε' (σ x) = x) (h₂ : ∀ z, σ (ε' z) = z) :
    (totalDerivedExtensionScalars.{u, u, u} (σ.comp b)).functor ≅
      (totalDerivedExtensionScalars.{u, u, u} b).functor ⋙
        (ModuleCat.restrictScalars.{u, u, u} ε').mapDerivedCategory :=
  (totalDerivedExtensionScalarsComp.{u, u} b σ).symm ≪≫
    Functor.isoWhiskerLeft (totalDerivedExtensionScalars.{u, u, u} b).functor
      (totalDerivedExtensionScalarsIsoRestrict σ ε' h₁ h₂)

/-- The two factors of `AlgebraicGeometry.totalDerivedExtensionScalarsCompIsoRestrict`, read
backwards at a complex: the restriction along `ε'` is turned back into an extension along `σ`,
and the two extensions are then merged. -/
public theorem totalDerivedExtensionScalarsCompIsoRestrict_inv_app (b : C →+* R₁)
    (σ : R₁ →+* R₂) (ε' : R₂ →+* R₁) (h₁ : ∀ x, ε' (σ x) = x) (h₂ : ∀ z, σ (ε' z) = z)
    (N : DerivedCategory (ModuleCat.{u} C)) :
    (totalDerivedExtensionScalarsCompIsoRestrict b σ ε' h₁ h₂).inv.app N =
      (totalDerivedExtensionScalarsIsoRestrict σ ε' h₁ h₂).inv.app
          ((totalDerivedExtensionScalars.{u, u, u} b).functor.obj N) ≫
        (totalDerivedExtensionScalarsComp.{u, u} b σ).hom.app N :=
  rfl

end Algebra

/-! ### The three spellings of the target corner -/

variable {A : CommRingCat.{u}} {X : Scheme.{u}} (i : Spec A ⟶ X) (y : Spec A)
  (K : DerivedCategory X.Modules)
  (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj K).IsQuasicoherent)
  (ε' : (Spec A).presheaf.stalk y →+* X.presheaf.stalk (i y))
  (h₁ : ∀ x, ε' ((i.stalkMap y).hom x) = x) (h₂ : ∀ z, (i.stalkMap y).hom (ε' z) = z)

/-- **Spelling (3) is spelling (1), restricted.**
`AlgebraicGeometry.derivedStalkAffineSectionsRestrictIso` is
`AlgebraicGeometry.derivedStalkAffineSectionsIso` followed by the replacement of the extension of
scalars along the germ comparison by restriction of scalars along its inverse: the two spellings
differ in nothing else. -/
public theorem derivedStalkAffineSectionsRestrictIso_eq :
    derivedStalkAffineSectionsRestrictIso i y K hK ε' h₁ h₂ =
      derivedStalkAffineSectionsIso i y K hK ≪≫
        (totalDerivedExtensionScalarsIsoRestrict (i.stalkMap y).hom ε' h₁ h₂).app
          ((derivedStalkFunctor (i y)).obj K) :=
  rfl

/-- **Spelling (1) followed by a morphism is spelling (3) followed by that morphism,
restricted.** For any morphism `ψ` out of the derived stalk of `K` at `i y`, reading the germ
localization of the derived sections by `AlgebraicGeometry.derivedStalkAffineSectionsIso`,
pushing it along `ψ` extended to `𝒪_{Spec A, y}` and then restricting along `ε'` is reading it by
`AlgebraicGeometry.derivedStalkAffineSectionsRestrictIso` and pushing it along `ψ` restricted.

This is the naturality of `AlgebraicGeometry.totalDerivedExtensionScalarsIsoRestrict` in the
complex: the two spellings differ by that isomorphism, and a morphism of complexes over the local
ring crosses it. -/
public theorem derivedStalkAffineSectionsIso_hom_comp_map
    {M : DerivedCategory (ModuleCat.{u} (X.presheaf.stalk (i y)))}
    (ψ : (derivedStalkFunctor (i y)).obj K ⟶ M) :
    (derivedStalkAffineSectionsIso i y K hK).hom ≫
        (totalDerivedExtensionScalars.{u, u, u} (i.stalkMap y).hom).functor.map ψ ≫
          (totalDerivedExtensionScalarsIsoRestrict (i.stalkMap y).hom ε' h₁ h₂).hom.app M =
      (derivedStalkAffineSectionsRestrictIso i y K hK ε' h₁ h₂).hom ≫
        (ModuleCat.restrictScalars.{u, u, u} ε').mapDerivedCategory.map ψ :=
  Eq.trans
    (congrArg (fun z => (derivedStalkAffineSectionsIso i y K hK).hom ≫ z)
      ((totalDerivedExtensionScalarsIsoRestrict (i.stalkMap y).hom ε' h₁ h₂).hom.naturality ψ))
    (Category.assoc _ _ _).symm

/-- **Spelling (1) with its two extensions of scalars merged is spelling (3).** For a ring map
`b` out of the local ring `𝒪_{X, i y}`, a complex `N` over its target and a morphism `ψ` from the
derived stalk of `K` into `N` extended along `b`: reading the germ localization of the derived
sections by `AlgebraicGeometry.derivedStalkAffineSectionsIso`, pushing it along `ψ` and merging
the two extensions of scalars is reading it by
`AlgebraicGeometry.derivedStalkAffineSectionsRestrictIso`, pushing it along `ψ` restricted, and
undoing `AlgebraicGeometry.totalDerivedExtensionScalarsCompIsoRestrict`.

The left-hand side is the shape in which the morphism factor of the chart comparison of
Stacks 0DJ8 ends — `b` the germ map of the stalk of a morphism of schemes, the merge the
composition isomorphism of
`AlgebraicGeometry.derivedStalkExtensionCompIsoGeneral` — and the right-hand side is the shape its
target bijection has. -/
public theorem derivedStalkAffineSectionsIso_hom_comp_merge {C : Type u} [CommRing C]
    (b : C →+* X.presheaf.stalk (i y)) (N : DerivedCategory (ModuleCat.{u} C))
    (ψ : (derivedStalkFunctor (i y)).obj K ⟶
      (totalDerivedExtensionScalars.{u, u, u} b).functor.obj N) :
    (derivedStalkAffineSectionsIso i y K hK).hom ≫
        (totalDerivedExtensionScalars.{u, u, u} (i.stalkMap y).hom).functor.map ψ ≫
          (totalDerivedExtensionScalarsComp.{u, u} b (i.stalkMap y).hom).hom.app N =
      (derivedStalkAffineSectionsRestrictIso i y K hK ε' h₁ h₂).hom ≫
        (ModuleCat.restrictScalars.{u, u, u} ε').mapDerivedCategory.map ψ ≫
          (totalDerivedExtensionScalarsCompIsoRestrict b (i.stalkMap y).hom ε' h₁ h₂).inv.app
            N := by
  rw [totalDerivedExtensionScalarsCompIsoRestrict_inv_app]
  simp only [← Category.assoc]
  refine congrArg
    (fun z => z ≫ (totalDerivedExtensionScalarsComp.{u, u} b (i.stalkMap y).hom).hom.app N) ?_
  rw [← derivedStalkAffineSectionsIso_hom_comp_map i y K hK ε' h₁ h₂ ψ]
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

end AlgebraicGeometry

namespace RingTheory.TorIndependence

section Comp

variable {A A₂ B : Type u} [CommRing A] [CommRing A₂] [CommRing B] [Algebra A A₂]
  (S : Submonoid A) [IsLocalization S A₂] (g : A₂ →+* B)
  [HasDerivedCategory.{w} (ModuleCat.{u} A)] [HasDerivedCategory.{w} (ModuleCat.{u} A₂)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]

include S in
/-- **Spelling (2)'s passage through the localization, in the vocabulary of spelling (1).** At a
complex `N` over the localization, `RingTheory.TorIndependence.restrictScalarsDerivedExtendCompIso`
is the inverse of the composition isomorphism of derived extension of scalars followed by the
derived extension along `g` of the localization idempotence
`RingTheory.TorIndependence.restrictScalarsDerivedExtendIso`.

Spelling (2) reaches the target corner from `𝒪_X(U)` through the local ring and uses this
isomorphism for the passage, while spelling (1) reaches it through the germ localization and
uses composition isomorphisms; this is the equation that lets one be rewritten into the other.
`RingTheory.TorIndependence.restrictScalarsDerivedExtendCompIso_hom_app_Q` is the same reading
at a localized complex and against the comparison with degreewise extension of scalars, which is
one level further down. -/
public theorem restrictScalarsDerivedExtendCompIso_hom_app
    (N : DerivedCategory (ModuleCat.{u} A₂)) :
    (restrictScalarsDerivedExtendCompIso.{u, w} S g).hom.app N =
      (totalDerivedExtensionScalarsComp.{u, u} (algebraMap A A₂) g).inv.app
          ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory.obj N) ≫
        (totalDerivedExtensionScalars.{u, u, u} g).functor.map
          ((restrictScalarsDerivedExtendIso.{u, w} S (A₂ := A₂)).hom.app N) := by
  simp [restrictScalarsDerivedExtendCompIso]

end Comp

section Idempotence

variable {A A₂ : Type u} [CommRing A] [CommRing A₂] [Algebra A A₂]
  (S : Submonoid A) [IsLocalization S A₂]

include S in
/-- **The degreewise localization idempotence is the counit of the degreewise
extension–restriction adjunction**, read on cochain complexes. On modules this is
`RingTheory.TorIndependence.restrictExtendScalarsIso_hom`; applying a natural isomorphism
degreewise to a complex applies its components, so nothing happens here. -/
public theorem restrictExtendScalarsComplexIso_hom_app
    (P : CochainComplex (ModuleCat.{u} A₂) ℤ) :
    (restrictExtendScalarsComplexIso S (A₂ := A₂)).hom.app P =
      ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap A A₂)).mapHomologicalComplex
        (ComplexShape.up ℤ)).counit.app P :=
  rfl

variable [HasDerivedCategory.{u} (ModuleCat.{u} A)] [HasDerivedCategory.{u} (ModuleCat.{u} A₂)]

include S in
/-- **The derived localization idempotence is the counit of the derived change-of-rings
adjunction.** Both are natural transformations `(-|_A) ⊗ᴸ_A A₂ ⟶ -`, and a natural
transformation out of a functor on the derived category is determined by its values on
localized complexes; there
`RingTheory.TorIndependence.restrictScalarsDerivedExtendIso_hom_app_Q` and
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_counit_app_eq` give
the same composite, the two differing only in the degreewise factor, which
`RingTheory.TorIndependence.restrictExtendScalarsComplexIso_hom_app` identifies.

This is what makes the triangle identity of the adjunction available for
`RingTheory.TorIndependence.restrictScalarsDerivedExtendIso`, which is constructed by descent
along the localization functor rather than as a counit. -/
public theorem restrictScalarsDerivedExtendIso_hom_eq_counit :
    (restrictScalarsDerivedExtendIso.{u, u} S (A₂ := A₂)).hom =
      (derivedExtendRestrictAdjunction (A := A) (A₂ := A₂)).counit := by
  refine CategoryTheory.Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} A₂) (ComplexShape.up ℤ)) fun P => ?_
  have hc :=
    @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_counit_app_eq.{u,
        u, u, u, u} A A₂ _ _ (algebraMap A A₂) _ _
      (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A₂)).functor
      (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A₂)).comparison
      (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A₂)).isLeftDerived P
  rw [restrictScalarsDerivedExtendIso_hom_app_Q, restrictExtendScalarsComplexIso_hom_app]
  exact hc.symm

include S in
/-- **The localization idempotence cancels the unit.** The left triangle identity of the derived
change-of-rings adjunction along a localization, with the counit written as
`RingTheory.TorIndependence.restrictScalarsDerivedExtendIso`. -/
public theorem map_unit_comp_restrictScalarsDerivedExtendIso_hom_app
    (P : DerivedCategory (ModuleCat.{u} A)) :
    (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A₂)).functor.map
          ((derivedExtendRestrictAdjunction (A := A) (A₂ := A₂)).unit.app P) ≫
        (restrictScalarsDerivedExtendIso.{u, u} S (A₂ := A₂)).hom.app
          ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A A₂)).functor.obj P) =
      CategoryStruct.id _ := by
  rw [restrictScalarsDerivedExtendIso_hom_eq_counit S]
  exact (derivedExtendRestrictAdjunction (A := A) (A₂ := A₂)).left_triangle_components P

include S in
/-- **Spelling (2) absorbs the unit.** For `g` out of the localization `A₂` of `A`, the derived
extension along `g ∘ (A → A₂)` of the unit of the derived change-of-rings adjunction, followed by
`RingTheory.TorIndependence.restrictScalarsDerivedExtendCompIso`, is the inverse of the
composition isomorphism of derived extension of scalars.

This is the equation that turns spelling (2) of the target corner — where the passage from
`𝒪_X(U)` to the further algebra `B` goes through the local ring and begins with the unit — into
spelling (1), where it is a composition isomorphism and no unit appears. The unit and the
localization idempotence inside `restrictScalarsDerivedExtendCompIso` cancel by
`RingTheory.TorIndependence.map_unit_comp_restrictScalarsDerivedExtendIso_hom_app`, and the
naturality of the composition isomorphism carries the unit across it. -/
public theorem map_unit_comp_restrictScalarsDerivedExtendCompIso_hom_app {B : Type u}
    [CommRing B] [HasDerivedCategory.{u} (ModuleCat.{u} B)] (g : A₂ →+* B)
    (P : DerivedCategory (ModuleCat.{u} A)) :
    (totalDerivedExtensionScalars.{u, u, u} (g.comp (algebraMap A A₂))).functor.map
          ((derivedExtendRestrictAdjunction (A := A) (A₂ := A₂)).unit.app P) ≫
        (restrictScalarsDerivedExtendCompIso.{u, u} S g).hom.app
          ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A A₂)).functor.obj P) =
      (totalDerivedExtensionScalarsComp.{u, u} (algebraMap A A₂) g).inv.app P := by
  have hnat := (totalDerivedExtensionScalarsComp.{u, u} (algebraMap A A₂) g).inv.naturality
    ((derivedExtendRestrictAdjunction (A := A) (A₂ := A₂)).unit.app P)
  dsimp only [CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.comp_map,
    CategoryTheory.Functor.id_obj] at hnat
  rw [restrictScalarsDerivedExtendCompIso_hom_app, ← Category.assoc, hnat,
    Category.assoc, ← CategoryTheory.Functor.map_comp,
    map_unit_comp_restrictScalarsDerivedExtendIso_hom_app S P]
  simp only [CategoryTheory.Functor.id_obj, CategoryTheory.Functor.map_id, Category.comp_id]

end Idempotence

end RingTheory.TorIndependence

end
