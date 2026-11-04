module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartDerivedStalk
public import StacksFrontier.Homology.Tor.DerivedBaseChangeSquareLocalization
public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunction
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsRingIso
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTotalComp
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.DerivedAdjunction

/-!
# The localization of the derived sections over an affine *open* is the derived stalk

`AlgebraicGeometry.derivedStalkAffineSectionsIso` identifies, for `i : Spec A ⟶ X` presenting an
affine open `U` of a scheme and `K` in `D(𝒪_X)` with quasi-coherent cohomology sheaves,

`RΓ(U, K) ⊗ᴸ_A 𝒪_{Spec A, y}  ≅  K_{i y} ⊗ᴸ_{𝒪_{X, i y}} 𝒪_{Spec A, y}`.

When `i` is an open immersion the germ comparison `𝒪_{X, i y} ⟶ 𝒪_{Spec A, y}` is an isomorphism
of rings, so the right-hand side is the derived stalk of `K` itself, read over `𝒪_{Spec A, y}`
along the inverse of that comparison. This module records that reading, which is the form the
affine reduction of Stacks 0DJ8 consumes: the pointwise map of Stacks 0DJ7 at a point of `U'` is
stated at the derived stalks, while the chart comparison is stated at the derived sections.

## Main definitions

* `AlgebraicGeometry.totalDerivedExtensionScalarsIsoRestrict`: derived extension of scalars along
  an invertible ring homomorphism is derived restriction of scalars along its inverse, at a free
  model of the derived category.
* `AlgebraicGeometry.derivedStalkAffineSectionsRestrictIso`: the identification displayed above
  with the right-hand side written as the derived stalk, restricted along a given inverse of the
  germ comparison.
* `AlgebraicGeometry.restrictScalarsIdDerivedIso`: derived restriction of scalars along a
  homomorphism equal to the identity is the identity functor of the derived category.
* `AlgebraicGeometry.totalDerivedExtensionScalarsIdOf`: derived *extension* of scalars along a
  homomorphism equal to the identity is the identity functor, which is
  `CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsId` read at a homomorphism
  given together with a proof that it is the identity.

## Main results

* `AlgebraicGeometry.unit_mapDerivedCategory_adjRestrictScalarsOfInv_app`: **the transport unit.**
  For `ε` invertible with inverse `ε'`, the unit of the derived transport adjunction of the
  restriction-of-scalars equivalence attached to `ε` is
  `AlgebraicGeometry.restrictScalarsIdDerivedIso` at `ε' ∘ ε`, read against the merge of the two
  derived restrictions. This is the law every identification of
  `AlgebraicGeometry.totalDerivedExtensionScalarsIsoRestrict` passes through, since that
  isomorphism is uniqueness of left adjoints applied to that transport adjunction; the point is
  that no universal property of a derived functor survives in the right-hand side.
* `AlgebraicGeometry.map_restrictScalarsIdDerivedIso_hom_comp_counit`: **the companion.** The
  adjunct of that comparison under the derived change-of-rings adjunction of Stacks 0GMT along
  `ε' ∘ ε` is the inverse of
  `AlgebraicGeometry.totalDerivedExtensionScalarsIdOf`, so neither the comparison nor the counit
  survives either.
* `AlgebraicGeometry.unit_mapDerivedCategory_app_Q`: the unit of
  `CategoryTheory.Adjunction.mapDerivedCategory` at a localized complex, which is what makes
  the first of these computable.

## Implementation notes

The inverse of the germ comparison is taken as data — a ring homomorphism together with the two
equations saying it inverts `i.stalkMap y` — rather than as `CategoryTheory.inv` of an
`IsIso` instance, because that is the shape
`StacksDraft.DerivedRingIso.derivedExtensionScalarsRestrictIso` asks for. A consumer holding
`IsOpenImmersion i` supplies it from the inverse of the stalk map.

Derived extension of scalars along a ring isomorphism is derived restriction of scalars along its
inverse. `StacksDraft.DerivedRingIso.derivedExtensionScalarsRestrictIso` says this, but only at
the standard model of the derived category; the consumer here works at the locally small model, so
`totalDerivedExtensionScalarsIsoRestrict` below reproves it at a free `HasDerivedCategory` binder
out of the same two adjunctions.

The two laws about the transport unit are stated with the merge `Ψ` of the two derived
restrictions taken as data pinned by an equation, rather than written out, so that a consumer
holding it in that spelling uses them with nothing transported.

Derived extension of scalars along a homomorphism `f` with a proof `hf : f = RingHom.id R` is
*not* interchangeable with derived extension along `RingHom.id R`: the two functors are
propositionally but not definitionally equal, and the consumer's homomorphism is the composite
`ε' ∘ ε` of two mutually inverse isomorphisms. Both identity comparisons are therefore stated at
a homomorphism together with such a proof, `hf` being what reduces them to the case of
`RingHom.id`.

The chases on localized complexes end in term mode rather than with a rewrite. The comparison
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.comparison` has
`CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplexGeneral` as its target while
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction` asks for degreewise
extension of scalars followed by the localization functor; the two agree at default transparency
only, so a composite built out of both is matched by `exact` and not by `rw`.
`AlgebraicGeometry.comp_eq_of_naturality` is the step that does this, with every object and
morphism a variable.

No tag attribute is placed here. This is a reading of
`AlgebraicGeometry.derivedStalkAffineSectionsIso`, which carries no tag either, both being inputs
to Stacks 0DJ8 rather than clauses of it.

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
open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars)

universe u w

namespace AlgebraicGeometry

variable {A : CommRingCat.{u}} {X : Scheme.{u}} (i : Spec A ⟶ X)

/-- **Derived extension of scalars along an invertible ring homomorphism is derived restriction of
scalars along its inverse.** Both are left adjoint to derived restriction of scalars along `ε`:
the left-hand side by the derived change-of-rings adjunction of Stacks 0GMT, and the right-hand
side because restriction of scalars along a ring isomorphism is an equivalence, which passes to
derived categories. Left adjoints of one functor are isomorphic.

Unlike `StacksDraft.DerivedRingIso.derivedExtensionScalarsRestrictIso`, this is stated at a free
`HasDerivedCategory` binder, which is what a consumer working at the locally small model needs. -/
public def totalDerivedExtensionScalarsIsoRestrict {R R₂ : Type u} [CommRing R] [CommRing R₂]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} R₂)]
    (ε : R →+* R₂) (ε' : R₂ →+* R) (h₁ : ∀ x, ε' (ε x) = x) (h₂ : ∀ z, ε (ε' z) = z) :
    (totalDerivedExtensionScalars.{u, u, u} ε).functor ≅
      (ModuleCat.restrictScalars.{u, u, u} ε').mapDerivedCategory :=
  Adjunction.leftAdjointUniq
    (@CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, u, w, w}
      R R₂ _ _ ε _ _
      (totalDerivedExtensionScalars.{u, u, u} ε).functor
      (totalDerivedExtensionScalars.{u, u, u} ε).comparison
      (totalDerivedExtensionScalars.{u, u, u} ε).isLeftDerived)
    (Adjunction.mapDerivedCategory
      (StacksDraft.DerivedRingIso.adjRestrictScalarsOfInv.{u} ε ε' h₁ h₂))

/-- **The localization of the derived sections over an affine open is the derived stalk.** For
`i : Spec A ⟶ X` whose germ comparison at `y` is invertible — an open immersion, say — and for `K`
in `D(𝒪_X)` with quasi-coherent cohomology sheaves,

`RΓ(U, K) ⊗ᴸ_A 𝒪_{Spec A, y}  ≅  K_{i y}`,

the right-hand side read over `𝒪_{Spec A, y}` along the given inverse `ε'` of the germ
comparison. -/
public def derivedStalkAffineSectionsRestrictIso (y : Spec A) (K : DerivedCategory X.Modules)
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj K).IsQuasicoherent)
    (ε' : (Spec A).presheaf.stalk y →+* X.presheaf.stalk (i y))
    (h₁ : ∀ x, ε' ((i.stalkMap y).hom x) = x)
    (h₂ : ∀ z, (i.stalkMap y).hom (ε' z) = z) :
    (totalDerivedExtensionScalars.{u, u, u} (specGermRingHom A y)).functor.obj
        ((affineDerivedSections i).obj K) ≅
      (ModuleCat.restrictScalars.{u, u, u} ε').mapDerivedCategory.obj
        ((derivedStalkFunctor (i y)).obj K) :=
  derivedStalkAffineSectionsIso i y K hK ≪≫
    (totalDerivedExtensionScalarsIsoRestrict (i.stalkMap y).hom ε' h₁ h₂).app
      ((derivedStalkFunctor (i y)).obj K)

/-! ### Derived restriction of scalars along a homomorphism equal to the identity -/

section RestrictScalarsId

variable {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- **Restriction of scalars along a homomorphism equal to the identity is the identity**, read
degreewise on cochain complexes. On modules this is `ModuleCat.restrictScalarsId'`, which carries
no transport along the equality of homomorphisms: it is the identity on the underlying additive
group, with the module structures identified by the equality. -/
public def restrictScalarsIdComplexIso (f : R →+* R) (hf : f = RingHom.id R) :
    (ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      𝟭 (CochainComplex (ModuleCat.{u} R) ℤ) :=
  NatIso.mapHomologicalComplex (ModuleCat.restrictScalarsId' f hf) (ComplexShape.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso (ModuleCat.{u} R) (ComplexShape.up ℤ)

/-- The comparison of the identity functor with derived restriction of scalars along a
homomorphism equal to the identity, before descent along the localization functor. -/
public def restrictScalarsIdDerivedQIso (f : R →+* R) (hf : f = RingHom.id R) :
    DerivedCategory.Q ⋙ 𝟭 (DerivedCategory (ModuleCat.{u} R)) ≅
      DerivedCategory.Q ⋙ (ModuleCat.restrictScalars.{u} f).mapDerivedCategory :=
  Functor.rightUnitor DerivedCategory.Q ≪≫
    (Functor.leftUnitor DerivedCategory.Q).symm ≪≫
    Functor.isoWhiskerRight (restrictScalarsIdComplexIso f hf).symm DerivedCategory.Q ≪≫
    (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.symm

/-- **Derived restriction of scalars along a homomorphism equal to the identity is the identity
functor of the derived category.** The degreewise comparison
`AlgebraicGeometry.restrictScalarsIdComplexIso` descended along the localization functor.

This is the transformation the restriction model of derived extension of scalars along an
invertible homomorphism is read against: see
`AlgebraicGeometry.unit_mapDerivedCategory_adjRestrictScalarsOfInv_app`. It is stated for a
homomorphism `f` together with a proof that `f` is the identity, rather than for `RingHom.id`
itself, because the consumer's homomorphism is a composite `ε' ∘ ε` of two inverse isomorphisms
and `ModuleCat.restrictScalars (RingHom.id R)` is not the identity functor. -/
public def restrictScalarsIdDerivedIso (f : R →+* R) (hf : f = RingHom.id R) :
    𝟭 (DerivedCategory (ModuleCat.{u} R)) ≅
      (ModuleCat.restrictScalars.{u} f).mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ 𝟭 (DerivedCategory (ModuleCat.{u} R)))
    (DerivedCategory.Q ⋙ (ModuleCat.restrictScalars.{u} f).mapDerivedCategory)
    _ _ (restrictScalarsIdDerivedQIso f hf)

/-- **The characterizing equation of `AlgebraicGeometry.restrictScalarsIdDerivedIso`.** At a
localized complex it is the degreewise comparison, followed by the canonical factorization
`CategoryTheory.Functor.mapDerivedCategoryFactors` of derived restriction of scalars. -/
public theorem restrictScalarsIdDerivedIso_hom_app_Q (f : R →+* R) (hf : f = RingHom.id R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (restrictScalarsIdDerivedIso.{u, w} f hf).hom.app (DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map ((restrictScalarsIdComplexIso.{u} f hf).inv.app P) ≫
        (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.inv.app P := by
  simp only [restrictScalarsIdDerivedIso, Localization.liftNatIso_hom,
    Localization.liftNatTrans_app, Localization.Lifting.compLeft_iso, Iso.refl_hom,
    Iso.refl_inv, NatTrans.id_app, Category.id_comp, Category.comp_id,
    restrictScalarsIdDerivedQIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.rightUnitor_hom_app,
    Functor.leftUnitor_inv_app, Functor.id_obj]
  exact Category.id_comp _

end RestrictScalarsId

/-! ### The unit of the derived transport adjunction of an invertible homomorphism -/

section TransportUnit

/-- Two inverse pairs cancel out of a composite of seven morphisms. Every object and morphism is
a variable: the composite this is applied to below is built out of two canonical factorizations
and the derived action of one of them, and no rewrite matches such a composite in place. -/
private lemma comp_cancel_two {𝒞 : Type*} [Category 𝒞] {W X Y Z T V : 𝒞}
    (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) (c' : Z ⟶ Y) (b' : Y ⟶ X) (d : X ⟶ T) (e : T ⟶ V)
    (hc : c ≫ c' = 𝟙 Y) (hb : b ≫ b' = 𝟙 X) :
    a ≫ b ≫ c ≫ c' ≫ b' ≫ d ≫ e = a ≫ d ≫ e := by
  rw [← Category.assoc c c', hc, Category.id_comp, ← Category.assoc b b', hb, Category.id_comp]

/-- **The unit of `CategoryTheory.Adjunction.mapDerivedCategory` at a localized complex.** The
derived form of an adjunction of exact additive functors is the degreewise adjunction on cochain
complexes transported along the two localization functors, so its unit at a localized complex is
the localized degreewise unit, read through the canonical factorizations
`CategoryTheory.Functor.mapDerivedCategoryFactors` of the two derived functors. Nothing of the
transport survives in it.

This is `CategoryTheory.Adjunction.localization_unit_app` with the two `CategoryTheory.CatCommSq`
data of `CategoryTheory.Adjunction.mapDerivedCategory` resolved. -/
public theorem unit_mapDerivedCategory_app_Q {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D] {F : C ⥤ D} {G : D ⥤ C}
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (adj : F ⊣ G)
    (P : CochainComplex C ℤ) :
    (Adjunction.mapDerivedCategory adj).unit.app (DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app P) ≫
        G.mapDerivedCategoryFactors.inv.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app P) := by
  rw [Adjunction.mapDerivedCategory, Adjunction.localization_unit_app]
  rfl

variable {R R₂ : Type u} [CommRing R] [CommRing R₂]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} R₂)]
  (ε : R →+* R₂) (ε' : R₂ →+* R) (h₁ : ∀ x, ε' (ε x) = x) (h₂ : ∀ z, ε (ε' z) = z)

omit [HasDerivedCategory (ModuleCat R)] [HasDerivedCategory (ModuleCat R₂)] in
/-- **The degreewise content of the transport unit.** The unit of the degreewise
restriction-of-scalars adjunction of an invertible homomorphism, followed by the merge of the two
restrictions, is the canonical identification of the identity functor with restriction along
`ε' ∘ ε`. All three are the identity on the underlying graded additive group, so there is nothing
to compute. -/
public theorem unit_mapHomologicalComplex_comp_mapHomologicalComplexCompIso
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((StacksDraft.DerivedRingIso.adjRestrictScalarsOfInv.{u} ε ε' h₁ h₂).mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app P ≫
        (Functor.mapHomologicalComplexCompIso
            (ModuleCat.restrictScalarsComp'.{u} ε ε' (ε'.comp ε) rfl).symm
            (ComplexShape.up ℤ)).hom.app P =
      (restrictScalarsIdComplexIso.{u} (ε'.comp ε) (RingHom.ext h₁)).inv.app P := by
  ext i
  rfl

/-- A functor sends the inverse followed by the forward component of an isomorphism of functors
to the identity. -/
private lemma map_inv_app_comp_map_hom_app {𝒞 𝒟 ℰ : Type*} [Category 𝒞] [Category 𝒟]
    [Category ℰ] (F : 𝒟 ⥤ ℰ) {G H : 𝒞 ⥤ 𝒟} (e : G ≅ H) (P : 𝒞) :
    F.map (e.inv.app P) ≫ F.map (e.hom.app P) = 𝟙 _ := by
  rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]

/-- **The unit of the derived transport adjunction of the restriction-of-scalars equivalence is
the canonical comparison of the identity functor with restriction along `ε' ∘ ε`, read against
the merge of the two restrictions.** For `ε` invertible with inverse `ε'`, the unit of the
derived form of the adjunction `StacksDraft.DerivedRingIso.adjRestrictScalarsOfInv` is
`AlgebraicGeometry.restrictScalarsIdDerivedIso` followed by the inverse of the composition
isomorphism `Ψ` of the two derived restrictions.

Both sides are natural transformations out of the identity functor of `D(R)`, so they agree as
soon as they agree on localized complexes; there the left-hand side is
`AlgebraicGeometry.unit_mapDerivedCategory_app_Q`, the right-hand side is
`AlgebraicGeometry.restrictScalarsIdDerivedIso_hom_app_Q` against
`RingTheory.TorIndependence.mapDerivedCategoryCompNatIso_hom_app_Q`, the two canonical
factorizations of the derived restrictions cancel, and what is left is the degreewise equation
`AlgebraicGeometry.unit_mapHomologicalComplex_comp_mapHomologicalComplexCompIso`.

The point is that the right-hand side retains no universal property of a derived functor: it is
the descent of a degreewise identity read against a composition isomorphism. `Ψ` is taken as
data pinned by `hΨ` so that a consumer holding the merge in that spelling can use the statement
with nothing transported. -/
public theorem unit_mapDerivedCategory_adjRestrictScalarsOfInv_app
    (Ψ : (ModuleCat.restrictScalars.{u} ε').mapDerivedCategory ⋙
          (ModuleCat.restrictScalars.{u} ε).mapDerivedCategory ≅
        (ModuleCat.restrictScalars.{u} (ε'.comp ε)).mapDerivedCategory)
    (hΨ : Ψ = RingTheory.TorIndependence.mapDerivedCategoryCompNatIso
      (ModuleCat.restrictScalars.{u} ε') (ModuleCat.restrictScalars.{u} ε)
      (ModuleCat.restrictScalars.{u} (ε'.comp ε))
      (ModuleCat.restrictScalarsComp'.{u} ε ε' (ε'.comp ε) rfl).symm)
    (M : DerivedCategory (ModuleCat.{u} R)) :
    (Adjunction.mapDerivedCategory
          (StacksDraft.DerivedRingIso.adjRestrictScalarsOfInv.{u} ε ε' h₁ h₂)).unit.app M =
      (restrictScalarsIdDerivedIso.{u, w} (ε'.comp ε) (RingHom.ext h₁)).hom.app M ≫
        Ψ.inv.app M := by
  have hmain : ∀ P : CochainComplex (ModuleCat.{u} R) ℤ,
      (Adjunction.mapDerivedCategory
            (StacksDraft.DerivedRingIso.adjRestrictScalarsOfInv.{u} ε ε' h₁ h₂)).unit.app
          (DerivedCategory.Q.obj P) ≫ Ψ.hom.app (DerivedCategory.Q.obj P) =
        (restrictScalarsIdDerivedIso.{u, w} (ε'.comp ε) (RingHom.ext h₁)).hom.app
          (DerivedCategory.Q.obj P) := by
    subst hΨ
    intro P
    rw [unit_mapDerivedCategory_app_Q,
      RingTheory.TorIndependence.mapDerivedCategoryCompNatIso_hom_app_Q,
      restrictScalarsIdDerivedIso_hom_app_Q]
    simp only [Category.assoc]
    rw [comp_cancel_two _ _ _ _ _ _ _
      (map_inv_app_comp_map_hom_app (ModuleCat.restrictScalars.{u} ε).mapDerivedCategory
        (ModuleCat.restrictScalars.{u} ε').mapDerivedCategoryFactors P)
      (Iso.inv_hom_id_app (ModuleCat.restrictScalars.{u} ε).mapDerivedCategoryFactors _),
      ← CategoryTheory.Functor.map_comp_assoc,
      unit_mapHomologicalComplex_comp_mapHomologicalComplexCompIso ε ε' h₁ h₂ P]
  have key : (Adjunction.mapDerivedCategory
        (StacksDraft.DerivedRingIso.adjRestrictScalarsOfInv.{u} ε ε' h₁ h₂)).unit =
      (restrictScalarsIdDerivedIso.{u, w} (ε'.comp ε) (RingHom.ext h₁)).hom ≫ Ψ.inv := by
    refine CategoryTheory.Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) fun P => ?_
    rw [NatTrans.comp_app, ← hmain P, Category.assoc, ← NatTrans.comp_app, Iso.hom_inv_id,
      NatTrans.id_app, Category.comp_id]
  exact (NatTrans.congr_app key M).trans (NatTrans.comp_app _ _ _)

end TransportUnit

/-! ### The adjunct of the comparison, and derived extension of scalars along the identity -/

section Adjunct

variable {R : Type u} [CommRing R]

/-- **The counit of the degreewise change-of-rings adjunction along the identity.** It is the
canonical identification of restriction of scalars along the identity with the identity functor,
extended, followed by the canonical identification of extension of scalars along the identity
with the identity functor: all three send `r ⊗ m` to `r • m`. -/
public theorem map_restrictScalarsId'_hom_comp_extendScalarsId_hom (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars.{u, u, u} (RingHom.id R)).map
          ((ModuleCat.restrictScalarsId' (RingHom.id R) rfl).hom.app M) ≫
        (ModuleCat.extendScalarsId.{u, u} R).hom.app M =
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (RingHom.id R)).counit.app M := by
  ext a
  rfl

/-- The same identity with the two comparisons inverted: the extension along the identity of the
comparison of the identity functor with restriction along the identity, followed by the counit
and by the inverse comparison for extension, is the identity. -/
public theorem map_restrictScalarsId'_inv_comp_counit (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars.{u, u, u} (RingHom.id R)).map
          ((ModuleCat.restrictScalarsId' (RingHom.id R) rfl).inv.app M) ≫
        (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (RingHom.id R)).counit.app M ≫
          (ModuleCat.extendScalarsId.{u, u} R).inv.app M =
      𝟙 _ := by
  rw [← map_restrictScalarsId'_hom_comp_extendScalarsId_hom M]
  simp only [Category.assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  exact Iso.hom_inv_id_app _ _

/-- `AlgebraicGeometry.map_restrictScalarsId'_inv_comp_counit` read degreewise on cochain
complexes. -/
public theorem map_restrictScalarsIdComplexIso_inv_comp_counit
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((ModuleCat.extendScalars.{u, u, u} (RingHom.id R)).mapHomologicalComplex
              (ComplexShape.up ℤ)).map
          ((restrictScalarsIdComplexIso.{u} (RingHom.id R) rfl).inv.app P) ≫
        ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} (RingHom.id R)).mapHomologicalComplex
              (ComplexShape.up ℤ)).counit.app P ≫
          (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsId.{u, u} R)
            (ComplexShape.up ℤ)).inv.app P =
      𝟙 _ := by
  ext i : 1
  exact map_restrictScalarsId'_inv_comp_counit (P.X i)

variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- Three consecutive factors under one functor. -/
private lemma map_comp_three {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (F : 𝒞 ⥤ 𝒟)
    {X Y Z T : 𝒞} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    F.map f ≫ F.map g ≫ F.map h = F.map (f ≫ g ≫ h) := by
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]

/-- One inverse pair cancels out of a composite of four morphisms. -/
private lemma comp_cancel_one {𝒞 : Type*} [Category 𝒞] {W X Y T : 𝒞}
    (a : W ⟶ X) (b : X ⟶ Y) (b' : Y ⟶ X) (d : X ⟶ T) (hb : b ≫ b' = 𝟙 X) :
    a ≫ b ≫ b' ≫ d = a ≫ d := by
  rw [← Category.assoc b b', hb, Category.id_comp]

/-- A naturality square whose far edge is a retraction. Every object and morphism is a variable
and the conclusion is proved in term mode: the composites below carry the comparison of a derived
functor with its degreewise model, whose target is spelled two ways that agree only at default
transparency, so a rewrite does not match them. -/
private lemma comp_eq_of_naturality {𝒞 : Type*} [Category 𝒞] {W X Y Z : 𝒞}
    (a : W ⟶ X) (b : X ⟶ Y) (t : Y ⟶ Z) (p : W ⟶ Z) (q : Z ⟶ Y)
    (h₁ : a ≫ b = p ≫ q) (h₂ : q ≫ t = 𝟙 Z) :
    a ≫ b ≫ t = p := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.comp_id]

/-- **The adjunct of the comparison of the identity functor with derived restriction of scalars
along the identity is the inverse of
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsId`.** Derived extension of
scalars along the identity applied to `AlgebraicGeometry.restrictScalarsIdDerivedIso`, followed
by the counit of the derived change-of-rings adjunction of Stacks 0GMT along the identity, is
the inverse of the identification of derived extension of scalars along the identity with the
identity functor.

Both sides are maps into the left derived functor, so it is enough to compare them against its
comparison with degreewise extension of scalars; there
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_counit_app_eq` and
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsId_comparison` reduce
everything to the degreewise identity
`AlgebraicGeometry.map_restrictScalarsIdComplexIso_inv_comp_counit`. -/
public theorem map_restrictScalarsIdDerivedIso_hom_comp_counit_id
    (M : DerivedCategory (ModuleCat.{u} R)) :
    (totalDerivedExtensionScalars.{u, u, u} (RingHom.id R)).functor.map
          ((restrictScalarsIdDerivedIso.{u, w} (RingHom.id R) rfl).hom.app M) ≫
        (@CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, u, w, w}
          R R _ _ (RingHom.id R) _ _
          (totalDerivedExtensionScalars.{u, u, u} (RingHom.id R)).functor
          (totalDerivedExtensionScalars.{u, u, u} (RingHom.id R)).comparison
          (totalDerivedExtensionScalars.{u, u, u} (RingHom.id R)).isLeftDerived).counit.app M =
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsId.{u, u, w}
        R).inv.app M := by
  have := (totalDerivedExtensionScalars.{u, u, u} (RingHom.id R)).isLeftDerived
  have key : Functor.whiskerRight
          (restrictScalarsIdDerivedIso.{u, w} (RingHom.id R) rfl).hom
          (totalDerivedExtensionScalars.{u, u, u} (RingHom.id R)).functor ≫
        (@CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u,
            u, u, w, w} R R _ _ (RingHom.id R) _ _
          (totalDerivedExtensionScalars.{u, u, u} (RingHom.id R)).functor
          (totalDerivedExtensionScalars.{u, u, u} (RingHom.id R)).comparison
          (totalDerivedExtensionScalars.{u, u, u} (RingHom.id R)).isLeftDerived).counit ≫
          (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsId.{u, u, w}
            R).hom =
      (Functor.leftUnitor
        (totalDerivedExtensionScalars.{u, u, u} (RingHom.id R)).functor).hom := by
    refine CategoryTheory.Functor.leftDerived_ext
      (totalDerivedExtensionScalars.{u, u, u} (RingHom.id R)).functor
      (totalDerivedExtensionScalars.{u, u, u} (RingHom.id R)).comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) _ _ _ ?_
    ext P
    have hcounit :=
      @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_counit_app_eq.{u,
          u, u, w, w} R R _ _ (RingHom.id R) _ _
        (totalDerivedExtensionScalars.{u, u, u} (RingHom.id R)).functor
        (totalDerivedExtensionScalars.{u, u, u} (RingHom.id R)).comparison
        (totalDerivedExtensionScalars.{u, u, u} (RingHom.id R)).isLeftDerived P
    have hnat : (totalDerivedExtensionScalars.{u, u, u} (RingHom.id R)).functor.map
            (DerivedCategory.Q.map
              ((restrictScalarsIdComplexIso.{u} (RingHom.id R) rfl).inv.app P)) ≫
          (totalDerivedExtensionScalars.{u, u, u} (RingHom.id R)).comparison.app
            (((ModuleCat.restrictScalars.{u} (RingHom.id R)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) =
        (totalDerivedExtensionScalars.{u, u, u} (RingHom.id R)).comparison.app P ≫
          DerivedCategory.Q.map
            (((ModuleCat.extendScalars.{u, u, u} (RingHom.id R)).mapHomologicalComplex
                (ComplexShape.up ℤ)).map
              ((restrictScalarsIdComplexIso.{u} (RingHom.id R) rfl).inv.app P)) :=
      (totalDerivedExtensionScalars.{u, u, u} (RingHom.id R)).comparison.naturality
        ((restrictScalarsIdComplexIso.{u} (RingHom.id R) rfl).inv.app P)
    have hretract : DerivedCategory.Q.map
              (((ModuleCat.extendScalars.{u, u, u} (RingHom.id R)).mapHomologicalComplex
                  (ComplexShape.up ℤ)).map
                ((restrictScalarsIdComplexIso.{u} (RingHom.id R) rfl).inv.app P)) ≫
            DerivedCategory.Q.map
                (((ModuleCat.extendRestrictScalarsAdj.{u, u, u}
                    (RingHom.id R)).mapHomologicalComplex
                  (ComplexShape.up ℤ)).counit.app P) ≫
              DerivedCategory.Q.map
                ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsId.{u, u} R)
                  (ComplexShape.up ℤ)).inv.app P) =
        𝟙 _ :=
      (map_comp_three DerivedCategory.Q _ _ _).trans
        ((congrArg DerivedCategory.Q.map
            (map_restrictScalarsIdComplexIso_inv_comp_counit.{u} P)).trans
          (CategoryTheory.Functor.map_id _ _))
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app]
    refine Eq.trans ?_ (Category.id_comp _).symm
    rw [restrictScalarsIdDerivedIso_hom_app_Q, CategoryTheory.Functor.map_comp, hcounit]
    simp only [Category.assoc]
    rw [CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsId_comparison,
      comp_cancel_one _ _ _ _
        (map_inv_app_comp_map_hom_app
          (totalDerivedExtensionScalars.{u, u, u} (RingHom.id R)).functor
          (ModuleCat.restrictScalars.{u} (RingHom.id R)).mapDerivedCategoryFactors P)]
    exact comp_eq_of_naturality _ _ _ _ _ hnat hretract
  have h := NatTrans.congr_app key M
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at h
  calc (totalDerivedExtensionScalars.{u, u, u} (RingHom.id R)).functor.map
          ((restrictScalarsIdDerivedIso.{u, w} (RingHom.id R) rfl).hom.app M) ≫
        (@CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u,
            u, u, w, w} R R _ _ (RingHom.id R) _ _
          (totalDerivedExtensionScalars.{u, u, u} (RingHom.id R)).functor
          (totalDerivedExtensionScalars.{u, u, u} (RingHom.id R)).comparison
          (totalDerivedExtensionScalars.{u, u, u} (RingHom.id R)).isLeftDerived).counit.app M
      = ((totalDerivedExtensionScalars.{u, u, u} (RingHom.id R)).functor.map
              ((restrictScalarsIdDerivedIso.{u, w} (RingHom.id R) rfl).hom.app M) ≫
            (@CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u,
                u, u, w, w} R R _ _ (RingHom.id R) _ _
              (totalDerivedExtensionScalars.{u, u, u} (RingHom.id R)).functor
              (totalDerivedExtensionScalars.{u, u, u} (RingHom.id R)).comparison
              (totalDerivedExtensionScalars.{u, u, u}
                (RingHom.id R)).isLeftDerived).counit.app M ≫
              (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsId.{u, u, w}
                R).hom.app M) ≫
          (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsId.{u, u, w}
            R).inv.app M := by
        rw [Category.assoc, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
    _ = _ := by rw [h]; exact Category.id_comp _

/-- **Derived extension of scalars along a homomorphism equal to the identity is the identity
functor.** For `RingHom.id` itself this is
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsId`; the hypothesis form is
what a consumer whose homomorphism is a composite `ε' ∘ ε` of two inverse isomorphisms needs. -/
public def totalDerivedExtensionScalarsIdOf (f : R →+* R) (hf : f = RingHom.id R) :
    𝟭 (DerivedCategory (ModuleCat.{u} R)) ≅
      (totalDerivedExtensionScalars.{u, u, u} f).functor :=
  CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsId.{u, u, w} R ≪≫
    eqToIso (congrArg
      (fun g : R →+* R => (totalDerivedExtensionScalars.{u, u, u} g).functor) hf.symm)

/-- **The adjunct of `AlgebraicGeometry.restrictScalarsIdDerivedIso` is the inverse of
`AlgebraicGeometry.totalDerivedExtensionScalarsIdOf`.** The companion of
`AlgebraicGeometry.unit_mapDerivedCategory_adjRestrictScalarsOfInv_app`: having read the
transport unit as the canonical comparison `ζ` with restriction along `ε' ∘ ε`, this says what
`ζ`'s adjunct under the derived change-of-rings adjunction along `ε' ∘ ε` is, namely the inverse
of the identification of derived extension of scalars along `ε' ∘ ε` with the identity functor.
No unit, no counit and no comparison with `ζ` survives.

For `f = RingHom.id R` this is
`AlgebraicGeometry.map_restrictScalarsIdDerivedIso_hom_comp_counit_id`, and the hypothesis `hf`
reduces the general case to it. -/
public theorem map_restrictScalarsIdDerivedIso_hom_comp_counit (f : R →+* R)
    (hf : f = RingHom.id R) (M : DerivedCategory (ModuleCat.{u} R)) :
    (totalDerivedExtensionScalars.{u, u, u} f).functor.map
          ((restrictScalarsIdDerivedIso.{u, w} f hf).hom.app M) ≫
        (@CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, u, w, w}
          R R _ _ f _ _
          (totalDerivedExtensionScalars.{u, u, u} f).functor
          (totalDerivedExtensionScalars.{u, u, u} f).comparison
          (totalDerivedExtensionScalars.{u, u, u} f).isLeftDerived).counit.app M =
      (totalDerivedExtensionScalarsIdOf.{u, w} f hf).inv.app M := by
  subst hf
  rw [totalDerivedExtensionScalarsIdOf]
  simp only [eqToIso_refl, Iso.trans_inv, Iso.refl_inv, Category.id_comp]
  exact map_restrictScalarsIdDerivedIso_hom_comp_counit_id M

end Adjunct

end AlgebraicGeometry

end
