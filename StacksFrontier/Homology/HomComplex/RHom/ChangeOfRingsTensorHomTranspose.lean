module

public import StacksFrontier.Homology.HomComplex.RHom.ChangeOfRingsTensorSide

/-!
# The Hom-side change-of-rings map as a [stacks 0A63] transpose

`Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap` is the chain-level map underlying the
change-of-rings isomorphism of [stacks 0E1W]: scalar adjunction on Hom complexes followed by
postcomposition with a chosen map `q : J|_R ⟶ I`.
`Stacks.DerivedHom.BaseChangeIso.homComplexChangeOfRingsMap_uncurry_monoidalIso` compares it with
the tensor side, but only *relative to* a map `s : A ⊗_R P ⟶ Hom^•_A(A ⊗_R K, J)`: it is an
equation between two transposes of `s`, true for every `s`, which determines the comparison but
is not itself a formula for it.

Here `P` is the restriction of scalars of `Z = Hom^•_A(A ⊗_R K, J)` and `s` is the counit of
degreewise extension--restriction, whose transpose is the identity; the uncurried change-of-rings
map is then expressed through the monoidality isomorphism of degreewise extension of scalars, the
[stacks 0A63] uncurrying of the counit — the evaluation map of `Z` over `A` — and `q`. Over a
K-flat `K` and a K-injective `I` this formula is carried to the derived category, as a
[stacks 0A63] tensor--Hom transpose.

Both statements are at a single universe, which is what the scalar-lift world of [stacks 0E1W]
provides: for `f' : ULift R →+* ULift A` the two rings and all their modules live in one
universe together.

## Main results

* `Stacks.DerivedHom.BaseChangeIso.uncurry_homComplexChangeOfRingsMap` — **the chain-level
  formula**: the [stacks 0A63] uncurrying of the Hom-side change-of-rings map is the
  extension--restriction transpose of the inverse monoidality isomorphism followed by the
  uncurried counit, postcomposed with `q`.
* `Stacks.DerivedHom.BaseChangeIso.homEquiv_Q_map_homComplexChangeOfRingsMap` — the same after
  localization, as a [stacks 0A63] transpose: the derived transpose of
  `DerivedCategory.Q.map (homComplexChangeOfRingsMap f K J I q)` composed with the K-injective
  representation of derived internal Hom is the K-flat representation of the derived tensor
  product followed by the localization of that chain-level formula.
* `Stacks.DerivedHom.BaseChangeIso.Q_map_homComplexChangeOfRingsMap_eq` — the same solved for
  the localized change-of-rings map, with nothing inverted on the left.
* `Stacks.DerivedHom.BaseChangeIso.isIso_homEquiv_symm_tensorIso` — where the localized
  change-of-rings map is an isomorphism, so is that transpose.
* `Stacks.DerivedHom.BaseChangeIso.inv_Q_map_homComplexChangeOfRingsMap_comp` — and then the
  inverse of the localized change-of-rings map followed by that transpose is the K-injective
  representation of derived internal Hom.
* `Stacks.DerivedHom.BaseChangeIso.inv_Q_map_homComplexChangeOfRingsMap_eq` — equivalently, that
  inverse is the K-injective representation followed by the inverse of the transpose.

## Implementation notes

`CochainComplex.restrictScalarsLarge` and
`CategoryTheory.Functor.mapHomologicalComplex` of `ModuleCat.restrictScalars` are the same
functor but not syntactically equal, so `rw` refuses goals mixing them; the triangle identity is
therefore applied in term position, where default transparency settles the two spellings.

## References

* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open CochainComplex.ExtendScalars
open StacksDraft.DerivedHom

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.DerivedHom.BaseChangeIso

variable {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)

local instance extendScalarsAdditive' : (ModuleCat.extendScalars.{u, u, u} f).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).left_adjoint_additive

/-- **The Hom-side change-of-rings map, uncurried, in closed form.**  Write
`Z = Hom^•_A(A ⊗_R K, J)` and `P = Z|_R`.  The [stacks 0A63] uncurrying of
`Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap` is the extension--restriction transpose
of the inverse monoidality isomorphism `A ⊗_R (P ⊗_R K) ≅ (A ⊗_R P) ⊗_A (A ⊗_R K)` followed by
the uncurried counit — the evaluation `(A ⊗_R Z) ⊗_A (A ⊗_R K) ⟶ J` over `A` — and then `q`. -/
theorem uncurry_homComplexChangeOfRingsMap
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (J : CochainComplex (ModuleCat.{u} A) ℤ)
    (I : CochainComplex (ModuleCat.{u} R) ℤ)
    (q : (CochainComplex.restrictScalarsLarge.{u, u, u} f).obj J ⟶ I) :
    let adj := (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
      (ComplexShape.up ℤ)
    let Z := CochainComplex.HomComplexR A
      ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J
    let P := (CochainComplex.restrictScalarsLarge.{u, u, u} f).obj Z
    DerivedInternalHom.Model.uncurry
        (Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap f K J I q) =
      adj.homEquiv (P ⊗ K) J
          ((extendScalarsMonoidalIso f P K).inv ≫
            DerivedInternalHom.Model.uncurry (adj.counit.app Z)) ≫ q := by
  intro adj Z P
  have hid : adj.homEquiv P Z (adj.counit.app Z) = 𝟙 P :=
    (adj.homEquiv_unit P Z (adj.counit.app Z)).trans (adj.right_triangle_components Z)
  have h := homComplexChangeOfRingsMap_uncurry_monoidalIso f P K J I q (adj.counit.app Z)
  rw [hid] at h
  exact (congrArg (fun z => DerivedInternalHom.Model.uncurry z)
    (Category.id_comp
      (Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap f K J I q))).symm.trans h.symm

/-- **The Hom-side change-of-rings map as a [stacks 0A63] transpose, after localization.**  For
`K` K-flat and `I` K-injective, the derived transpose of
`DerivedCategory.Q.map (homComplexChangeOfRingsMap f K J I q)` followed by the K-injective
representation `homIso` of derived internal Hom is the K-flat representation `tensorIso` of the
derived tensor product followed by the localization of the chain-level formula
`Stacks.DerivedHom.BaseChangeIso.uncurry_homComplexChangeOfRingsMap`. -/
theorem homEquiv_Q_map_homComplexChangeOfRingsMap
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (J : CochainComplex (ModuleCat.{u} A) ℤ)
    (I : CochainComplex (ModuleCat.{u} R) ℤ)
    (q : (CochainComplex.restrictScalarsLarge.{u, u, u} f).obj J ⟶ I)
    (hK : K.KFlat) [I.IsKInjective] :
    let adj := (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
      (ComplexShape.up ℤ)
    let Z := CochainComplex.HomComplexR A
      ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J
    let P := (CochainComplex.restrictScalarsLarge.{u, u, u} f).obj Z
    DerivedInternalHom.Model.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K)
          (DerivedCategory.Q.obj I)
          (DerivedCategory.Q.map
              (Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap f K J I q) ≫
            ((DerivedInternalHom.Model.adjunction R).homIso K I).inv) =
      ((DerivedInternalHom.Model.adjunction R).tensorIso P K hK).hom ≫
        DerivedCategory.Q.map
          (adj.homEquiv (P ⊗ K) J
              ((extendScalarsMonoidalIso f P K).inv ≫
                DerivedInternalHom.Model.uncurry (adj.counit.app Z)) ≫ q) := by
  intro adj Z P
  rw [← uncurry_homComplexChangeOfRingsMap f K J I q]
  exact DerivedInternalHom.Model.homEquiv_map_uncurry P K I hK _

/-- **The localized Hom-side change-of-rings map, solved for.**  This is
`Stacks.DerivedHom.BaseChangeIso.homEquiv_Q_map_homComplexChangeOfRingsMap` with the [stacks 0A63]
transpose and the K-injective representation moved to the other side: for `K` K-flat and `I`
K-injective, `DerivedCategory.Q.map (homComplexChangeOfRingsMap f K J I q)` *is* the inverse
transpose of the K-flat representation of the derived tensor product followed by the localized
chain-level formula, followed by `homIso`. -/
theorem Q_map_homComplexChangeOfRingsMap_eq
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (J : CochainComplex (ModuleCat.{u} A) ℤ)
    (I : CochainComplex (ModuleCat.{u} R) ℤ)
    (q : (CochainComplex.restrictScalarsLarge.{u, u, u} f).obj J ⟶ I)
    (hK : K.KFlat) [I.IsKInjective] :
    let adj := (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
      (ComplexShape.up ℤ)
    let Z := CochainComplex.HomComplexR A
      ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J
    let P := (CochainComplex.restrictScalarsLarge.{u, u, u} f).obj Z
    let W := adj.homEquiv (P ⊗ K) J
        ((extendScalarsMonoidalIso f P K).inv ≫
          DerivedInternalHom.Model.uncurry (adj.counit.app Z)) ≫ q
    DerivedCategory.Q.map
          (Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap f K J I q) =
      (DerivedInternalHom.Model.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K)
            (DerivedCategory.Q.obj I)).symm
          (((DerivedInternalHom.Model.adjunction R).tensorIso P K hK).hom ≫
            DerivedCategory.Q.map W) ≫
        ((DerivedInternalHom.Model.adjunction R).homIso K I).hom := by
  intro adj Z P W
  rw [← Iso.comp_inv_eq, AddEquiv.eq_symm_apply]
  exact homEquiv_Q_map_homComplexChangeOfRingsMap f K J I q hK

/-- **The [stacks 0A63] transpose is invertible wherever the change-of-rings map is.**  For `K`
K-flat and `I` K-injective, if the localized change-of-rings map is an isomorphism, then so is the
[stacks 0A63] transpose of `Stacks.DerivedHom.BaseChangeIso.Q_map_homComplexChangeOfRingsMap_eq`.
The hypothesis holds for `J` K-injective and `q` a quasi-isomorphism, by
`Stacks.DerivedHom.BaseChange.quasiIso_homComplexChangeOfRingsMap_of_kFlat`. -/
theorem isIso_homEquiv_symm_tensorIso
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (J : CochainComplex (ModuleCat.{u} A) ℤ)
    (I : CochainComplex (ModuleCat.{u} R) ℤ)
    (q : (CochainComplex.restrictScalarsLarge.{u, u, u} f).obj J ⟶ I)
    (hK : K.KFlat) [I.IsKInjective]
    [IsIso (DerivedCategory.Q.map
      (Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap f K J I q))] :
    let adj := (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
      (ComplexShape.up ℤ)
    let Z := CochainComplex.HomComplexR A
      ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J
    let P := (CochainComplex.restrictScalarsLarge.{u, u, u} f).obj Z
    let W := adj.homEquiv (P ⊗ K) J
        ((extendScalarsMonoidalIso f P K).inv ≫
          DerivedInternalHom.Model.uncurry (adj.counit.app Z)) ≫ q
    IsIso ((DerivedInternalHom.Model.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K)
        (DerivedCategory.Q.obj I)).symm
      (((DerivedInternalHom.Model.adjunction R).tensorIso P K hK).hom ≫
        DerivedCategory.Q.map W)) := by
  intro adj Z P W
  rw [← (Iso.comp_inv_eq _).2 (Q_map_homComplexChangeOfRingsMap_eq f K J I q hK)]
  infer_instance

/-- **The inverse of the localized Hom-side change-of-rings map, with the inverse eliminated.**
Where the change-of-rings map is a quasi-isomorphism — which it is for `K` K-flat, `J` and `I`
K-injective and `q` a quasi-isomorphism, by
`Stacks.DerivedHom.BaseChange.quasiIso_homComplexChangeOfRingsMap_of_kFlat` — the inverse of its
localization, followed by the [stacks 0A63] transpose of
`Stacks.DerivedHom.BaseChangeIso.Q_map_homComplexChangeOfRingsMap_eq`, is the K-injective
representation of derived internal Hom. -/
theorem inv_Q_map_homComplexChangeOfRingsMap_comp
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (J : CochainComplex (ModuleCat.{u} A) ℤ)
    (I : CochainComplex (ModuleCat.{u} R) ℤ)
    (q : (CochainComplex.restrictScalarsLarge.{u, u, u} f).obj J ⟶ I)
    (hK : K.KFlat) [I.IsKInjective]
    [IsIso (DerivedCategory.Q.map
      (Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap f K J I q))] :
    let adj := (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
      (ComplexShape.up ℤ)
    let Z := CochainComplex.HomComplexR A
      ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J
    let P := (CochainComplex.restrictScalarsLarge.{u, u, u} f).obj Z
    let W := adj.homEquiv (P ⊗ K) J
        ((extendScalarsMonoidalIso f P K).inv ≫
          DerivedInternalHom.Model.uncurry (adj.counit.app Z)) ≫ q
    inv (DerivedCategory.Q.map
            (Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap f K J I q)) ≫
        (DerivedInternalHom.Model.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K)
            (DerivedCategory.Q.obj I)).symm
          (((DerivedInternalHom.Model.adjunction R).tensorIso P K hK).hom ≫
            DerivedCategory.Q.map W) =
      ((DerivedInternalHom.Model.adjunction R).homIso K I).inv := by
  intro adj Z P W
  rw [← (Iso.comp_inv_eq _).2 (Q_map_homComplexChangeOfRingsMap_eq f K J I q hK),
    IsIso.inv_hom_id_assoc]

/-- **The inverse of the localized Hom-side change-of-rings map is the inverse of a [stacks 0A63]
transpose.**  Where the localized change-of-rings map is an isomorphism, its inverse is the
K-injective representation of derived internal Hom followed by the inverse of the transpose of
`Stacks.DerivedHom.BaseChangeIso.Q_map_homComplexChangeOfRingsMap_eq`, which is invertible by
`Stacks.DerivedHom.BaseChangeIso.isIso_homEquiv_symm_tensorIso`. -/
theorem inv_Q_map_homComplexChangeOfRingsMap_eq
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (J : CochainComplex (ModuleCat.{u} A) ℤ)
    (I : CochainComplex (ModuleCat.{u} R) ℤ)
    (q : (CochainComplex.restrictScalarsLarge.{u, u, u} f).obj J ⟶ I)
    (hK : K.KFlat) [I.IsKInjective]
    [IsIso (DerivedCategory.Q.map
      (Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap f K J I q))] :
    let adj := (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
      (ComplexShape.up ℤ)
    let Z := CochainComplex.HomComplexR A
      ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J
    let P := (CochainComplex.restrictScalarsLarge.{u, u, u} f).obj Z
    let W := adj.homEquiv (P ⊗ K) J
        ((extendScalarsMonoidalIso f P K).inv ≫
          DerivedInternalHom.Model.uncurry (adj.counit.app Z)) ≫ q
    letI : IsIso ((DerivedInternalHom.Model.homEquiv (DerivedCategory.Q.obj P)
        (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj I)).symm
          (((DerivedInternalHom.Model.adjunction R).tensorIso P K hK).hom ≫
            DerivedCategory.Q.map W)) :=
      isIso_homEquiv_symm_tensorIso f K J I q hK
    inv (DerivedCategory.Q.map
          (Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap f K J I q)) =
      ((DerivedInternalHom.Model.adjunction R).homIso K I).inv ≫
        inv ((DerivedInternalHom.Model.homEquiv (DerivedCategory.Q.obj P)
          (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj I)).symm
            (((DerivedInternalHom.Model.adjunction R).tensorIso P K hK).hom ≫
              DerivedCategory.Q.map W)) := by
  intro adj Z P W
  refine IsIso.inv_eq_of_hom_inv_id ?_
  rw [← Category.assoc,
    (Iso.comp_inv_eq _).2 (Q_map_homComplexChangeOfRingsMap_eq f K J I q hK), IsIso.hom_inv_id]

end Stacks.DerivedHom.BaseChangeIso

end
