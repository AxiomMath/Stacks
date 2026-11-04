module

public import StacksFrontier.RingTheory.Dualizing.AdjunctionCoherence
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormulaCounit

/-!
# Restricted coextension of scalars is the internal Hom out of the algebra

Let `φ : A →+* B` be a homomorphism of commutative rings, write `i_*` for derived restriction of
scalars `D(B) ⥤ D(A)`, `Ext` for a total left derived model of extension of scalars and
`RHom_A(B, -) = Dualizing.derivedHom φ` for derived coextension of scalars.  This file constructs
the comparison

`i_* RHom_A(B, X) ⟶ hom_A(B[0], X)`

between restricted derived coextension of scalars and the internal Hom of the derived tensor--Hom
adjunction of [stacks 0A63] out of the algebra, and shows it is an isomorphism.  The target is the
*single-ring* internal Hom of `D(A)`; the source lives over `B` before restriction.  Both are right
adjoints, and the comparison is the one induced by an isomorphism of their left adjoints, so it is
invertible with no finiteness or flatness hypothesis anywhere.

## Main definitions

* `Dualizing.derivedTensorHomAdjunctionOverRing` -- the derived tensor--Hom adjunction of
  [stacks 0A63] at a fixed object, packaged as a `CategoryTheory.Adjunction`:
  `- ⊗ᴸ_A M ⊣ hom_A(M, -)`.  The adjunction data of
  `StacksDraft.DerivedHom.DerivedHomAdjunction` is a natural `AddEquiv` of hom-groups; this is the
  same datum read as an adjunction, which is what the uniqueness of adjoints needs.
* `Dualizing.ProjectionFormula.restrictedAlgebra` -- the algebra as a degree-zero object of `D(A)`,
  namely derived restriction of scalars applied to the tensor unit of `D(B)`.
* `Dualizing.ProjectionFormula.restrictExtendIso` -- derived extension of scalars followed by
  derived restriction of scalars is tensoring with the algebra, `i_*(Ext N) ≅ N ⊗ᴸ_A B`.
* `Dualizing.ProjectionFormula.restrictExtendAdjunction` -- hence tensoring with the algebra is
  left adjoint to restricted derived coextension of scalars.
* `Dualizing.ProjectionFormula.restrictCoextendInternalHomIso` -- **the comparison**, as an
  isomorphism of functors `D(A) ⥤ D(A)`.

## Main results

* `Dualizing.ProjectionFormula.homEquiv_restrictCoextendInternalHomIso` -- the comparison is
  determined by its transpose over [stacks 0A63]: that transpose is the action of the algebra on a
  restricted object, followed by the counit of [stacks 0A70].  Both factors are counits -- of
  [stacks 0GMT] and of [stacks 0A70] -- read through `restrictExtendIso`, so the characterisation
  mentions no comparison that is not already named.

## Implementation notes

The isomorphism `restrictExtendIso` is *not* built by hand: it is the projection formula
`Dualizing.ProjectionFormula.derivedProjBifunctorNatIso` evaluated at the tensor unit of `D(B)`,
`i_*(1_B ⊗ᴸ_B Ext N) ≅ i_*(1_B) ⊗ᴸ_A N`, with the unit removed on the left by the left unitor
`StacksDraft.DerivedHom.derivedTensorUnitLeft` of [stacks 0A63] and the two tensor factors
interchanged on the right by the symmetry.  Naturality in `N` is exactly the half of the projection
formula that `derivedProjBifunctorNatIso` adds to `derivedProjNatIso`, so nothing has to be
resolved and no K-flat representative is chosen.

The algebra is spelled `i_*(1_B)` rather than as a `DerivedCategory.singleFunctor` applied to `B`:
the two agree, but the first is the only one for which the projection formula has a value without a
further comparison, and it is the object the adjunction argument produces.

No `@[stacks]` attribute is placed here.  The comparison is [stacks 0A71] -- restricted derived
coextension of scalars computes derived Hom out of the algebra -- but that tag already sits on
`Dualizing.derivedCoextendScalarsCompDerivedRestrictScalarsIso`, which states the same mathematics
for a right derived functor of the Hom-along-`φ` functor instead of for the internal Hom of
[stacks 0A63]; duplicating the tag would break the covering-set discipline.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [Stacks Project, Tag 0A71](https://stacks.math.columbia.edu/tag/0A71)
* [Stacks Project, Tag 0E2H](https://stacks.math.columbia.edu/tag/0E2H)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public section

open CategoryTheory
open CochainComplex.DerivedExtensionScalars

universe u v

namespace Dualizing

attribute [local instance] HasDerivedCategory.standard

/-- **The derived tensor--Hom adjunction of [stacks 0A63] at a fixed object**, as an adjunction:
tensoring on the right with `M` is left adjoint to the internal Hom out of `M`.  The structure
`StacksDraft.DerivedHom.DerivedHomAdjunction` records this as a natural isomorphism of hom-groups;
the two naturality fields it carries are exactly the two the adjunction needs. -/
noncomputable def derivedTensorHomAdjunctionOverRing (R : Type u) [CommRing R]
    (M : DerivedCategory (ModuleCat.{max u v} R)) :
    ProjectionFormula.tensorRightDerived.{u, v} R M ⊣
      (Functor.curry.obj (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v,
        max u v + 1} R).hom).obj (Opposite.op M) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v,
          max u v + 1} R).homEquiv X M Y).toEquiv.symm
      homEquiv_naturality_left_symm := fun {_X' _X _Y} f g =>
        (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v,
          max u v + 1} R).homEquiv_naturality_left f g
      homEquiv_naturality_right := fun {X _Y Y'} f g => by
        apply ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v,
          max u v + 1} R).homEquiv X M Y').injective
        dsimp only [Functor.curry_obj_obj_map]
        rw [(StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v,
          max u v + 1} R).homEquiv_naturality_right]
        simp }

/-- The counit of the tensor--Hom adjunction is the evaluation morphism. -/
theorem derivedTensorHomAdjunctionOverRing_counit (R : Type u) [CommRing R]
    (M X : DerivedCategory (ModuleCat.{max u v} R)) :
    (derivedTensorHomAdjunctionOverRing.{u, v} R M).counit.app X =
      (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v, max u v + 1} R).evaluation M X :=
  rfl

namespace ProjectionFormula

attribute [local instance] Dualizing.extendScalarsAdditiveOfRingHom

variable {A B : Type u} [CommRing A] [CommRing B]

/-- **The algebra as a degree-zero object of `D(A)`**: the tensor unit of `D(B)`, restricted along
`φ`.  This is the object the projection formula produces, and the one the internal Hom of the
comparison below is taken out of. -/
noncomputable abbrev restrictedAlgebra
    (iStar : DerivedCategory (ModuleCat.{max u v} B) ⥤ DerivedCategory (ModuleCat.{max u v} A)) :
    DerivedCategory (ModuleCat.{max u v} A) :=
  iStar.obj (StacksDraft.DerivedHom.derivedTensorUnit.{u, v, max u v + 1} B)

/-- **Restricted derived extension of scalars is tensoring with the algebra**: `i_*(Ext N) ≅
N ⊗ᴸ_A B`, naturally in `N`.  This is the projection formula
`Dualizing.ProjectionFormula.derivedProjBifunctorNatIso` at the tensor unit of `D(B)`, with the
unit removed by the left unitor of [stacks 0A63] and the factors interchanged by the symmetry; the
naturality in `N` is the bifunctorial half of the projection formula. -/
noncomputable def restrictExtendIso (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, v, u, max u v + 1, max u v + 1} φ)
    (iStar : DerivedCategory (ModuleCat.{max u v} B) ⥤ DerivedCategory (ModuleCat.{max u v} A))
    (adj : iStar ⊣ Dualizing.derivedHom.{u, v, u} φ) :
    E.functor ⋙ iStar ≅ tensorRightDerived.{u, v} A (restrictedAlgebra.{u, v} iStar) :=
  NatIso.ofComponents
    (fun N =>
      iStar.mapIso (StacksDraft.DerivedHom.derivedTensorUnitLeft.{u, v, max u v + 1} B
          (E.functor.obj N)).symm ≪≫
        (derivedProjNatIso.{u, v} φ E iStar adj N).app
          (StacksDraft.DerivedHom.derivedTensorUnit.{u, v, max u v + 1} B) ≪≫
        (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensorSwap
          (restrictedAlgebra.{u, v} iStar) N)
    (by
      intro N N' f
      have h1 := StacksDraft.DerivedHom.derivedTensorUnitLeft_natural.{u, v, max u v + 1} B
        (E.functor.map f)
      have h2 : iStar.map
            ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v,
                max u v + 1} B).tensor.map
              (X := (StacksDraft.DerivedHom.derivedTensorUnit.{u, v, max u v + 1} B,
                E.functor.obj N))
              (Y := (StacksDraft.DerivedHom.derivedTensorUnit.{u, v, max u v + 1} B,
                E.functor.obj N'))
              (𝟙 (StacksDraft.DerivedHom.derivedTensorUnit.{u, v, max u v + 1} B),
                E.functor.map f)) ≫
          ((derivedProjNatIso.{u, v} φ E iStar adj N').app
            (StacksDraft.DerivedHom.derivedTensorUnit.{u, v, max u v + 1} B)).hom =
        ((derivedProjNatIso.{u, v} φ E iStar adj N).app
            (StacksDraft.DerivedHom.derivedTensorUnit.{u, v, max u v + 1} B)).hom ≫
          (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor.map
            (X := (restrictedAlgebra.{u, v} iStar, N)) (Y := (restrictedAlgebra.{u, v} iStar, N'))
            (𝟙 (restrictedAlgebra.{u, v} iStar), f) :=
        NatTrans.congr_app
          ((derivedProjBifunctorNatIso.{u, v} φ E iStar adj).hom.naturality f)
          (StacksDraft.DerivedHom.derivedTensorUnit.{u, v, max u v + 1} B)
      have h3 := (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v,
        max u v + 1} A).tensorSwap_naturality
        (𝟙 (restrictedAlgebra.{u, v} iStar)) f
      dsimp only [StacksDraft.DerivedHom.DerivedHomAdjunction.IsUnitorNatural] at h1
      have h1' : E.functor.map f ≫
            (StacksDraft.DerivedHom.derivedTensorUnitLeft.{u, v, max u v + 1} B
              (E.functor.obj N')).inv =
          (StacksDraft.DerivedHom.derivedTensorUnitLeft.{u, v, max u v + 1} B
              (E.functor.obj N)).inv ≫
            (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v, max u v + 1} B).tensor.map
              (X := (StacksDraft.DerivedHom.derivedTensorUnit.{u, v, max u v + 1} B,
                E.functor.obj N))
              (Y := (StacksDraft.DerivedHom.derivedTensorUnit.{u, v, max u v + 1} B,
                E.functor.obj N'))
              (𝟙 (StacksDraft.DerivedHom.derivedTensorUnit.{u, v, max u v + 1} B),
                E.functor.map f) := by
        rw [Iso.eq_inv_comp, ← Category.assoc, ← h1, Category.assoc, Iso.hom_inv_id,
          Category.comp_id]
      dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
        Functor.comp_map, Functor.flip_obj_map, Functor.curry_obj_map_app, Prod.mkHom]
      simp only [Category.assoc]
      rw [← h3, ← reassoc_of% h2, ← Functor.map_comp_assoc, h1', Functor.map_comp_assoc])

/-- **Tensoring with the algebra is left adjoint to restricted derived coextension of scalars.**
Derived extension of scalars is left adjoint to derived restriction of scalars by [stacks 0GMT],
derived restriction of scalars is left adjoint to derived coextension of scalars by [stacks 0A70],
and the composite of those two left adjoints is tensoring with the algebra by
`Dualizing.ProjectionFormula.restrictExtendIso`. -/
noncomputable def restrictExtendAdjunction (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, v, u, max u v + 1, max u v + 1} φ)
    (iStar : DerivedCategory (ModuleCat.{max u v} B) ⥤ DerivedCategory (ModuleCat.{max u v} A))
    (adj : iStar ⊣ Dualizing.derivedHom.{u, v, u} φ) (adjE : E.functor ⊣ iStar) :
    tensorRightDerived.{u, v} A (restrictedAlgebra.{u, v} iStar) ⊣
      Dualizing.derivedHom.{u, v, u} φ ⋙ iStar :=
  (adjE.comp adj).ofNatIsoLeft (restrictExtendIso.{u, v} φ E iStar adj)

/-- **Restricted derived coextension of scalars is the internal Hom out of the algebra.**  For
`φ : A →+* B`, the canonical comparison

`i_* RHom_A(B, X) ⟶ hom_A(B[0], X)`

into the internal Hom of the derived tensor--Hom adjunction of [stacks 0A63], as an isomorphism of
functors `D(A) ⥤ D(A)`.  Both functors are right adjoints -- the first by [stacks 0GMT] and
[stacks 0A70] composed, the second by [stacks 0A63] -- of left adjoints identified by
`Dualizing.ProjectionFormula.restrictExtendIso`, so this is the comparison of right adjoints
induced by that identification, and it is invertible for that reason alone.
`Dualizing.ProjectionFormula.homEquiv_restrictCoextendInternalHomIso` says what it is. -/
noncomputable def restrictCoextendInternalHomIso (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, v, u, max u v + 1, max u v + 1} φ)
    (iStar : DerivedCategory (ModuleCat.{max u v} B) ⥤ DerivedCategory (ModuleCat.{max u v} A))
    (adj : iStar ⊣ Dualizing.derivedHom.{u, v, u} φ) (adjE : E.functor ⊣ iStar) :
    Dualizing.derivedHom.{u, v, u} φ ⋙ iStar ≅
      (Functor.curry.obj (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v,
        max u v + 1} A).hom).obj (Opposite.op (restrictedAlgebra.{u, v} iStar)) :=
  (restrictExtendAdjunction.{u, v} φ E iStar adj adjE).rightAdjointUniq
    (Dualizing.derivedTensorHomAdjunctionOverRing.{u, v} A (restrictedAlgebra.{u, v} iStar))

/-- **The comparison is characterised by its transpose over [stacks 0A63].**  That transpose is
the action of the algebra on the restriction -- the inverse of
`Dualizing.ProjectionFormula.restrictExtendIso` followed by the counit of [stacks 0GMT] -- composed
with the counit of [stacks 0A70].  Since the transposition is a bijection, this determines
`Dualizing.ProjectionFormula.restrictCoextendInternalHomIso` uniquely. -/
theorem homEquiv_restrictCoextendInternalHomIso (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, v, u, max u v + 1, max u v + 1} φ)
    (iStar : DerivedCategory (ModuleCat.{max u v} B) ⥤ DerivedCategory (ModuleCat.{max u v} A))
    (adj : iStar ⊣ Dualizing.derivedHom.{u, v, u} φ) (adjE : E.functor ⊣ iStar)
    (X : DerivedCategory (ModuleCat.{max u v} A)) :
    (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).homEquiv
        (iStar.obj ((Dualizing.derivedHom.{u, v, u} φ).obj X))
        (restrictedAlgebra.{u, v} iStar) X
        ((restrictCoextendInternalHomIso.{u, v} φ E iStar adj adjE).hom.app X) =
      (restrictExtendIso.{u, v} φ E iStar adj).inv.app
          (iStar.obj ((Dualizing.derivedHom.{u, v, u} φ).obj X)) ≫
        iStar.map (adjE.counit.app ((Dualizing.derivedHom.{u, v, u} φ).obj X)) ≫
          adj.counit.app X := by
  have h := Adjunction.rightAdjointUniq_hom_app_counit
    (restrictExtendAdjunction.{u, v} φ E iStar adj adjE)
    (Dualizing.derivedTensorHomAdjunctionOverRing.{u, v} A (restrictedAlgebra.{u, v} iStar)) X
  have e := (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v,
      max u v + 1} A).homEquiv_naturality_left
    ((restrictCoextendInternalHomIso.{u, v} φ E iStar adj adjE).hom.app X)
    (𝟙 (((Functor.curry.obj (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v,
      max u v + 1} A).hom).obj (Opposite.op (restrictedAlgebra.{u, v} iStar))).obj X))
  rw [Category.comp_id] at e
  refine e.trans (h.trans ?_)
  simp [restrictExtendAdjunction, Adjunction.ofNatIsoLeft, Adjunction.comp]

end ProjectionFormula

end Dualizing

end
