module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.CompareIsoCoherence

/-!
# The two comparisons of restriction, as natural isomorphisms

Let `(X, 𝒪_X)` be a ringed space.  The coherence that the uniqueness clause of [Stacks, Tag 0D68]
still owes was reduced in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.CompareIsoCoherence` to a single
equation between the two canonical comparisons of restriction,
`Stacks.DerivedGlueing.canonicalCompareIso K hTW hWO = Stacks.DerivedGlueing.overMapCompareIso K
hTW`, with no system involved.

This file records the two sides of that equation as natural isomorphisms between one pair of
functors out of `Stacks.DerivedGlueing.OpenDerivedCategory X O`, and reduces the equation to its
instances at the class of a complex: that is
`Stacks.DerivedGlueing.canonicalCompareIso_eq_of_forall_Q`.  It also collects the generic
category algebra such a computation needs, each statement with every category and functor a
variable so that it applies at one definitional unification.

## Main results

* `Stacks.DerivedGlueing.canonicalCompareNatIso` and
  `Stacks.DerivedGlueing.overMapCompareNatIso`, with
  `Stacks.DerivedGlueing.canonicalCompareNatIso_app` and
  `Stacks.DerivedGlueing.overMapCompareNatIso_app` identifying their components.
* `Stacks.DerivedGlueing.canonicalCompareIso_eq_of_forall_Q` — the equation at every class of a
  complex gives it at every object.
* `Stacks.DerivedGlueing.mapDerivedCategoryCompIso_chain` — the two comparisons assembling a
  threefold composite, followed by the canonical factorization of that composite, are the three
  factorizations in turn.
* `Stacks.DerivedGlueing.eqToHom_openModuleRestriction_eq` — the transport identifying the two
  spellings of restriction from `O` to `U` is the identity.

## Implementation notes

The whole difficulty of the remaining equation is one definitional identification, and it is
worth recording where it sits.  Restriction from `O` to `U` is spelled in two ways in this
development: as `Stacks.DerivedGlueing.openModuleRestriction X U O hUO`, which the field
`restrictionFactors` of `Stacks.DerivedGlueing.LocallyGiven` is stated with, and as
`jShriek O 𝒪_X ⋙ (SheafOfModules.overFunctor 𝒪_X U ⋙ sliceToSubspace 𝒪_X U)`, which the ringed
site is stated with.  `Stacks.DerivedGlueing.openModuleRestriction_eq` says they are equal, and
the two halves of that equality cost very differently to identify:

* `openModuleRestriction X U O hUO` against `jShriek O 𝒪_X ⋙ jStar U 𝒪_X` is one delta step and
  costs about 5500 heartbeats at the level of complexes;
* `SheafOfModules.overFunctor 𝒪_X U ⋙ sliceToSubspace 𝒪_X U` against `jStar U 𝒪_X`, carried under
  `jShriek O 𝒪_X` to the level of complexes, costs about 205000 — **above the per-declaration
  ceiling of 200000**.  At the level of modules the same identification costs about 35000, and at
  the level of functors about 170000.

So an equation whose two sides end at the two spellings of a *complex* cannot be stated, however
its proof is split; the identification has to be paid at the level of modules, or carried as the
transport of the one existing proof.  `Stacks.DerivedGlueing.eqToHom_openModuleRestriction_eq`
below is the first of those: it is proved at a module, where the reduction is immediate, and
lifted by the fact that a natural transformation is determined by its components.

## References

* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)

Tags covered: none.  Everything here is a step of a proof, not a clause of a tag statement.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open ExtensionByZeroModules RingedSpaceModuleAdjunction

namespace Stacks.DerivedGlueing

universe w₁ w₂ w₃ w₄ v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ u

/-! ### Category algebra -/

/-- A natural transformation at an object, read at an isomorphic one. -/
theorem natTrans_app_eq_conj {D₂ : Type u₁} [Category.{v₁} D₂] {D₃ : Type u₂} [Category.{v₂} D₃]
    {Φ Ψ : D₂ ⥤ D₃} (β : Φ ⟶ Ψ) {x y : D₂} (u : x ≅ y) :
    β.app x = Φ.map u.hom ≫ β.app y ≫ Ψ.map u.inv := by
  rw [← Category.assoc, β.naturality u.hom, Category.assoc, ← Ψ.map_comp, u.hom_inv_id, Ψ.map_id,
    Category.comp_id]

/-- Two isomorphisms with the same source and target agree once they agree after composition
with one common invertible leg. -/
theorem iso_eq_of_comp_eq {D : Type u₁} [Category.{v₁} D] {x y z : D} (a b : x ≅ y) (g : y ⟶ z)
    [IsIso g] (h : a.hom ≫ g = b.hom ≫ g) : a = b :=
  Iso.ext ((cancel_mono g).mp h)

section Generic

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]
  {C₄ : Type u₄} [Category.{v₄} C₄] [Abelian C₄] [HasDerivedCategory.{w₄} C₄]

/-- The functor induced on derived categories by an identity comparison of exact functors is the
identity. -/
theorem mapDerivedCategoryCongr_refl (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] :
    mapDerivedCategoryCongr (Iso.refl F) = Iso.refl F.mapDerivedCategory := by
  refine Iso.ext (Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ)) fun P => ?_)
  have h : (NatIso.mapHomologicalComplex (Iso.refl F) (ComplexShape.up ℤ)).hom.app P = 𝟙 _ := by
    ext n
    simp
  rw [mapDerivedCategoryCongr_hom_app_Q, h]
  simp

/-- **The two comparisons that assemble a threefold composite, followed by the canonical
factorization of that composite, are the three factorizations in turn.**  Every category and
functor is a variable, so this applies by `exact` at one definitional unification. -/
theorem mapDerivedCategoryCompIso_chain (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (G : C₂ ⥤ C₃) [G.Additive] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] (H : C₃ ⥤ C₄) [H.Additive] [PreservesFiniteLimits H]
    [PreservesFiniteColimits H] [(G ⋙ H).Additive] [PreservesFiniteLimits (G ⋙ H)]
    [PreservesFiniteColimits (G ⋙ H)] [(F ⋙ G ⋙ H).Additive]
    [PreservesFiniteLimits (F ⋙ G ⋙ H)] [PreservesFiniteColimits (F ⋙ G ⋙ H)]
    (P : CochainComplex C₁ ℤ) :
    (mapDerivedCategoryCompIso G H).hom.app
          (F.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≫
        (mapDerivedCategoryCompIso F (G ⋙ H)).hom.app (DerivedCategory.Q.obj P) ≫
          (F ⋙ G ⋙ H).mapDerivedCategoryFactors.hom.app P =
      H.mapDerivedCategory.map
          (G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P)) ≫
        H.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
          H.mapDerivedCategoryFactors.hom.app
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) := by
  have hconj : (mapDerivedCategoryCompIso G H).hom.app
        (F.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) =
      H.mapDerivedCategory.map
          (G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P)) ≫
        (mapDerivedCategoryCompIso G H).hom.app
            (DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
          (G ⋙ H).mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app P) :=
    natTrans_app_eq_conj _ (F.mapDerivedCategoryFactors.app P)
  have hBC : (G ⋙ H).mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app P) ≫
      (G ⋙ H).mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  rw [hconj, mapDerivedCategoryCompIso_hom_app_Q_comp F (G ⋙ H) P]
  simp only [Category.assoc]
  rw [reassoc_of% hBC,
    mapDerivedCategoryCompIso_hom_app_Q_comp G H
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)]

end Generic

/-! ### The comparisons of the concrete situation, read at the class of a complex -/

section Concrete

variable {X : RingedSpace.{u, u}}

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] Stacks.DerivedGlueing.preservesFiniteLimitsOverMap
  Stacks.DerivedGlueing.preservesFiniteColimitsOverMap

/-- **The transport of `Stacks.DerivedGlueing.openModuleRestriction_eq`, at a module.**  The two
spellings of restriction from `O` to `U` agree on objects on the nose, so the transport is the
identity there.

The componentwise statement is the one to prove: the transport is a `CategoryTheory.eqToHom`
between two spellings of a *functor*, and reducing it at that level forces the unifier through
the two spellings' exactness data, which it cannot afford; at a module there is no such data and
the reduction is immediate. -/
theorem eqToHom_openModuleRestriction_eq_app (O U : Opens X.carrier) (hUO : U ≤ O)
    (M : SheafOfModules.{u} (restrictedRingSheaf X O)) :
    (eqToHom (openModuleRestriction_eq O U hUO)).app M = 𝟙 _ := by
  rw [eqToHom_app]
  exact eqToHom_refl _ _

/-- **The transport of `Stacks.DerivedGlueing.openModuleRestriction_eq` is the identity.**  This
is `Stacks.DerivedGlueing.eqToHom_openModuleRestriction_eq_app` at every module; a natural
transformation is determined by its components, so the identification of the two spellings of
restriction from `O` to `U` never has to be reduced at the level of functors. -/
theorem eqToHom_openModuleRestriction_eq (O U : Opens X.carrier) (hUO : U ≤ O) :
    eqToHom (openModuleRestriction_eq O U hUO) = 𝟙 _ :=
  NatTrans.ext (funext fun M => eqToHom_openModuleRestriction_eq_app O U hUO M)

/-- **`Stacks.DerivedGlueing.canonicalCompareIso` as a natural isomorphism.**  The comparison of
the two readings of the restriction of an extension by zero, assembled from the identification of
restriction with the restriction of an extension by zero, the canonical comparison of restriction
in two steps, and `Stacks.DerivedGlueing.sliceRestrictOverDerivedIso`. -/
def canonicalCompareNatIso (O : Opens X.carrier) {T W : Opens X.carrier}
    (hTW : T ≤ W) (hWO : W ≤ O) :
    (jShriek O (underlyingRingSheaf X)).mapDerivedCategory ⋙
        ((SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) T).mapDerivedCategory ⋙
          (sliceToSubspace (underlyingRingSheaf X) T).mapDerivedCategory) ≅
      (jShriek O (underlyingRingSheaf X)).mapDerivedCategory ⋙
        ((SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) W).mapDerivedCategory ⋙
          ((SheafOfModules.overMap.{u} (underlyingRingSheaf X) hTW.hom).mapDerivedCategory ⋙
            (sliceToSubspace (underlyingRingSheaf X) T).mapDerivedCategory)) :=
  extensionRestrictionNatIso O T (hTW.trans hWO) ≪≫
    mapDerivedCategoryComp (openModuleRestriction X W O hWO)
        (openModuleRestriction X T W hTW) (openModuleRestriction X T O (hTW.trans hWO))
        (asIso (openModuleRestrictionComparison X T W O hTW hWO)) ≪≫
      Functor.isoWhiskerRight (extensionRestrictionNatIso O W hWO).symm
          (openModuleRestriction X T W hTW).mapDerivedCategory ≪≫
        Functor.isoWhiskerLeft
          ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory ⋙
            (SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) W).mapDerivedCategory)
          (sliceRestrictOverDerivedIso hTW)

/-- The components of `Stacks.DerivedGlueing.canonicalCompareNatIso` are the comparisons
`Stacks.DerivedGlueing.canonicalCompareIso`. -/
theorem canonicalCompareNatIso_app (O : Opens X.carrier) {T W : Opens X.carrier}
    (hTW : T ≤ W) (hWO : W ≤ O) (K : OpenDerivedCategory X O) :
    (canonicalCompareNatIso O hTW hWO).app K = canonicalCompareIso K hTW hWO :=
  Iso.ext rfl

/-- **`Stacks.DerivedGlueing.overMapCompareIso` as a natural isomorphism.**  The transitivity of
restriction to a slice on the ringed site, read in the open-subspace model of `T`. -/
def overMapCompareNatIso (O : Opens X.carrier) {T W : Opens X.carrier} (hTW : T ≤ W) :
    (jShriek O (underlyingRingSheaf X)).mapDerivedCategory ⋙
        ((SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) T).mapDerivedCategory ⋙
          (sliceToSubspace (underlyingRingSheaf X) T).mapDerivedCategory) ≅
      (jShriek O (underlyingRingSheaf X)).mapDerivedCategory ⋙
        ((SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) W).mapDerivedCategory ⋙
          ((SheafOfModules.overMap.{u} (underlyingRingSheaf X) hTW.hom).mapDerivedCategory ⋙
            (sliceToSubspace (underlyingRingSheaf X) T).mapDerivedCategory)) :=
  Functor.isoWhiskerLeft (jShriek O (underlyingRingSheaf X)).mapDerivedCategory
    (Functor.isoWhiskerRight
      (RingedSite.overMapDerivedCategoryRestrictIso (Stacks.SheafOfModules.ringedSite X.sheaf)
        hTW.hom).symm
      (sliceToSubspace (underlyingRingSheaf X) T).mapDerivedCategory)

/-- The components of `Stacks.DerivedGlueing.overMapCompareNatIso` are the comparisons
`Stacks.DerivedGlueing.overMapCompareIso`. -/
theorem overMapCompareNatIso_app (O : Opens X.carrier) {T W : Opens X.carrier} (hTW : T ≤ W)
    (K : OpenDerivedCategory X O) :
    (overMapCompareNatIso O hTW).app K = overMapCompareIso K hTW :=
  Iso.ext rfl

/-- **The coherence of the two comparisons needs checking only at the class of a complex.**
Both comparisons are components of natural isomorphisms between one pair of functors out of
`Stacks.DerivedGlueing.OpenDerivedCategory X O`, a localization of complexes of sheaves of
modules by the quasi-isomorphisms, so `CategoryTheory.Localization.natTrans_ext` carries an
identification at every `DerivedCategory.Q.obj C` to an identification at every object. -/
theorem canonicalCompareIso_eq_of_forall_Q (O : Opens X.carrier) {T W : Opens X.carrier}
    (hTW : T ≤ W) (hWO : W ≤ O)
    (h : ∀ C : HomologicalComplex (SheafOfModules.{u} (restrictedRingSheaf X O))
        (ComplexShape.up ℤ),
      canonicalCompareIso (DerivedCategory.Q.obj C) hTW hWO =
        overMapCompareIso (DerivedCategory.Q.obj C) hTW)
    (K : OpenDerivedCategory X O) :
    canonicalCompareIso K hTW hWO = overMapCompareIso K hTW := by
  have hnat : canonicalCompareNatIso O hTW hWO = overMapCompareNatIso O hTW := by
    refine Iso.ext (Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (restrictedRingSheaf X O))
        (ComplexShape.up ℤ)) fun C => ?_)
    exact congrArg Iso.hom (h C)
  rw [← canonicalCompareNatIso_app O hTW hWO K, ← overMapCompareNatIso_app O hTW K, hnat]

end Concrete

end Stacks.DerivedGlueing

end
