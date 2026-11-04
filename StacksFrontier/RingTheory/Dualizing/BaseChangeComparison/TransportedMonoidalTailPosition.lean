module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.HomRestrictScalarsTransportClass
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TransportedMonoidalUnitChain

/-!
# The tensor base-change isomorphism of the [stacks 0GMT] side, moved to the [stacks 068I] position

`Dualizing.tensorBaseChangeMor_eq_of_unit_chain_prefix` reduces the [stacks 068I] identification
at a pair of K-flat complexes to one equation naming exactly two non-bookkeeping morphisms, each
on both sides: a tensor base-change isomorphism `e` of total complexes over `f` and the
scalar-lift comparison `CochainComplex.DerivedTensor.extendScalarsLiftChainIso`.  But the two
occurrences of `e` sit in different places.  On the [stacks 068I] side the prefix-pinning
hypothesis reads it inside `E.functor` of the restriction along `f` of a morphism of `D(A)`; on
the [stacks 0GMT] side `CochainComplex.DerivedTensor.transportedMonoidalInvTail` carries it as a
degreewise restriction along `ULift.ringEquiv` over `A`, localized, in the world of modules over
the lift of `A`.  Nothing moved one into the other.

This file moves the [stacks 0GMT] occurrence into the [stacks 068I] position.  Two steps do it,
and both already exist:

* `Stacks.DerivedHom.BaseChange.scalarEquivalence_functor_map_Q_map_comp_scalarLiftQObjIso`,
  naturality of the scalar-lift presentation, read at `e.inv`, replaces the localized degreewise
  restriction of `e.inv` by the scalar lift over `A` of `DerivedCategory.Q` of `e.inv`,
  conjugated by two scalar-lift presentations;
* the transported restriction comparison `τ` of [stacks 0E1W] is natural, so the scalar lift over
  `A` pushed forward by derived restriction along the lifted ring map is derived restriction along
  `f` pushed forward by the scalar lift over `R`, conjugated by `τ`.

After both, the [stacks 0GMT] side carries `e` as `E.functor` of the restriction along `f` of
`DerivedCategory.Q.map e.inv` -- which is where the [stacks 068I] side carries `e.hom`, inside
the internal Hom of the transposed candidate.

**What is not done here.**  Nothing is registered and no caveat is lifted.  The tensor base-change
isomorphism is **not** cancelled: `e` still occurs once on each side of the keystone's equation,
and the cancellation needs the [stacks 068I] occurrence uncurried, which this file does not do.
Both hypotheses of `Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor` remain open;
in particular the comparison identity `h` is untouched, and its frontier remains
`Dualizing.tensorComparisonCompatibility_of_kFlat_tail`.  What this file changes is where in the
[stacks 0GMT] side the tensor base-change isomorphism sits.

## Main results

* `Stacks.DerivedHom.BaseChange.scalarRestrictionTransportedIso_naturality` -- the transported
  restriction comparison of [stacks 0E1W] carries derived restriction along `f` pushed forward by
  the scalar lift over `R` to the scalar lift over `A` pushed forward by derived restriction along
  the lifted ring map.
* `CochainComplex.DerivedTensor.Q_map_transportedMonoidalInvTail` -- the localization of the
  transported monoidality tail, with the degreewise restriction of `e.inv` replaced by the scalar
  lift over `A` of its localization.
* `CochainComplex.DerivedTensor.map_Q_map_transportedMonoidalInvTail` -- **the move**: the same
  pushed forward by derived restriction along the lifted ring map, with the tensor base-change
  isomorphism in the position the [stacks 068I] side reads it in.
* `Stacks.DerivedHom.BaseChange.functor_map_comp_hom_map_comp_counit` -- the covariant slot of the
  transported internal Hom over `A`, moved out of the [stacks 0E1W] prefix: this is what takes the
  [stacks 068I] occurrence of `e` out of the transposed candidate.
* `Stacks.DerivedHom.BaseChange.functor_map_comp_tensorKFlatKInjectiveLift_hom` -- **the
  absorption**: the [stacks 068I] occurrence of `e`, followed by the identification of the
  covariant slot with the class of the K-injective complex `J`, is the scalar-lift presentation of
  the total tensor complex followed by the localization of the degreewise restriction of `e.hom`
  composed with the chosen resolution.  The K-flat description of `F (Q K ⊗ᴸ_R Q L)` cancels, and
  the chain map left over has exactly the leading factor of
  `CochainComplex.DerivedTensor.transportedMonoidalInvTail` read backwards.

## Implementation notes

The naturality step is stated over variable categories by a `private` lemma and instantiated with
`exact`: the concrete `τ` is a `let`-bound conjugate of the scalar-restriction comparison, and the
elaborator does not unfold a `let` while inferring the middle object of a composition, so a
rewrite in place against the spelled-out conjugate fails where instantiating an abstract lemma at
default transparency succeeds.

## References

* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open CochainComplex.ExtendScalars
open Stacks.DerivedHom.ScalarTransportedInternalHom
open Stacks.DerivedHom.BaseChange

attribute [local instance] HasDerivedCategory.standard

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄ uR uA uM

namespace Stacks.DerivedHom.BaseChange

/-- **Naturality of a conjugating isomorphism of composites.**  For `τ : U ⋙ Ef ≅ Sf ⋙ V`, the
image under `V` of the image under `Sf` of a morphism is the image under `Ef` of its image under
`U`, conjugated by `τ`.  Stated over variable categories so that the concrete instance, whose `τ`
is a `let`-bound conjugate, is checked at default transparency. -/
private theorem transported_naturality {C : Type u₁} {D : Type u₂} {C' : Type u₃} {D' : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} C'] [Category.{v₄} D']
    (Ef : C ⥤ C') (Sf : D ⥤ D') (U : D ⥤ C) (V : D' ⥤ C') (τ : U ⋙ Ef ≅ Sf ⋙ V)
    {M N : D} (h : M ⟶ N) :
    V.map (Sf.map h) = τ.inv.app M ≫ Ef.map (U.map h) ≫ τ.hom.app N := by
  have hn : Ef.map (U.map h) ≫ τ.hom.app N = τ.hom.app M ≫ V.map (Sf.map h) := τ.hom.naturality h
  rw [hn, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

/-- **The conjugation with a prefix and a tail.**  `transported_naturality` with a morphism before
and a morphism after the image of `h`, which is the shape the localized monoidality tail has.
Stated over variable categories for the same reason. -/
private theorem transported_naturality_comp {C : Type u₁} {D : Type u₂} {C' : Type u₃}
    {D' : Type u₄} [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} C'] [Category.{v₄} D']
    (Ef : C ⥤ C') (Sf : D ⥤ D') (U : D ⥤ C) (V : D' ⥤ C') (τ : U ⋙ Ef ≅ Sf ⋙ V)
    {M N : D} (h : M ⟶ N) {P Z : D'} (α : P ⟶ Sf.obj M) (β : Sf.obj N ⟶ Z) :
    V.map (α ≫ Sf.map h ≫ β) =
      V.map α ≫ (τ.inv.app M ≫ Ef.map (U.map h) ≫ τ.hom.app N) ≫ V.map β := by
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    transported_naturality Ef Sf U V τ h]

/-- **The transported restriction comparison of [stacks 0E1W] is natural.**

Derived restriction of scalars along the lifted ring map applied to the scalar lift over `A` of a
morphism of `D(A)` is the scalar lift over `R` of its derived restriction along `f`, conjugated by
the transported comparison `τ` of
`Stacks.DerivedHom.BaseChange.scalarRestrictionTransportedIso_hom_app`.

This is what carries a morphism of `D(A)` from the `ULift A` world, where the [stacks 0GMT] side
of the keystone of Chapter 47 reads it, to the `D(R)` world pushed forward by the scalar lift,
where its [stacks 068I] side reads it. -/
public theorem scalarRestrictionTransportedIso_naturality
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
    {M N : DerivedCategory (ModuleCat.{max uR uA uM} A)} (h : M ⟶ N) :
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    let E := scalarEquivalence.{uR, max uR uA uM} R
    let S := scalarEquivalence.{uA, max uR uA uM} A
    let U := (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory
    let V := (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory
    let δ : S.inverse ⋙ U ≅ V ⋙ E.inverse := scalarRestrictionIso.{uR, uA, uM} f
    let τ : U ⋙ E.functor ≅ S.functor ⋙ V :=
      Iso.compInverseIso (H := E.symm)
        ((Iso.inverseCompIso (G := S.symm) δ.symm).symm ≪≫
          (Functor.associator _ _ _).symm)
    V.map (S.functor.map h) = τ.inv.app M ≫ E.functor.map (U.map h) ≫ τ.hom.app N := by
  intro f'
  exact transported_naturality _ _ _ _ _ h

/-- **Moving a morphism of the inner category out of the comparison prefix.**  Over variable
categories: a comparison `δ : S.inverse ⋙ U ≅ V ⋙ E.inverse` read at the target of `ψ`, preceded
by the restriction of `ψ` and followed by the counit of `E`, is `δ` read at the source of `ψ`,
followed by the counit and by the image of `ψ` under `V`.  This is naturality of `δ` and of the
counit of `E`; it is the private step of
`Stacks.DerivedHom.BaseChange.scalarRestrictionIso_hom_comp_counit_comp_eq`, read in the direction
that takes `ψ` *out* of the prefix. -/
private theorem map_out_of_delta_prefix
    {C : Type u₁} {D : Type u₂} {C' : Type u₃} {D' : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} C'] [Category.{v₄} D']
    (E : C ≌ C') (S : D ≌ D') (U : D ⥤ C) (V : D' ⥤ C')
    (δ : S.inverse ⋙ U ≅ V ⋙ E.inverse)
    {X : C} {Y Y₀ : D'} {P : C'} (g : X ⟶ U.obj (S.inverse.obj Y)) (ψ : Y ⟶ Y₀)
    (p : V.obj Y₀ ⟶ P) :
    E.functor.map ((g ≫ U.map (S.inverse.map ψ)) ≫ δ.hom.app Y₀) ≫
        E.counitIso.hom.app (V.obj Y₀) ≫ p =
      E.functor.map (g ≫ δ.hom.app Y) ≫
        E.counitIso.hom.app (V.obj Y) ≫ V.map ψ ≫ p := by
  have h1 : E.counitIso.hom.app (V.obj Y) ≫ V.map ψ =
      E.functor.map (E.inverse.map (V.map ψ)) ≫ E.counitIso.hom.app (V.obj Y₀) :=
    (E.counitIso.hom.naturality (V.map ψ)).symm
  have h2 : U.map (S.inverse.map ψ) ≫ δ.hom.app Y₀ = δ.hom.app Y ≫ E.inverse.map (V.map ψ) :=
    δ.hom.naturality ψ
  have hcore : ∀ {Q : C'} (z : E.functor.obj (E.inverse.obj (V.obj Y₀)) ⟶ Q),
      E.functor.map (δ.hom.app Y) ≫ E.functor.map (E.inverse.map (V.map ψ)) ≫ z =
        E.functor.map (U.map (S.inverse.map ψ)) ≫ E.functor.map (δ.hom.app Y₀) ≫ z := by
    intro Q z
    rw [← Category.assoc, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
      ← CategoryTheory.Functor.map_comp, h2]
  refine Eq.symm ?_
  rw [← Category.assoc (E.counitIso.hom.app (V.obj Y)), h1]
  simp only [Category.assoc, CategoryTheory.Functor.map_comp]
  rw [hcore]

/-- **The covariant slot of the transported internal Hom over `A`, moved out of the [stacks 0E1W]
prefix.**

The [stacks 068I] side of the keystone of Chapter 47 reads the tensor base-change isomorphism `e`
inside the transported internal Hom over `A`: by
`Dualizing.tensorBaseChangeMor_transpose_eq_q_obj` the transposed candidate ends in
`dA.hom.map (𝟙, DerivedCategory.Q.map e.hom ≫ …)`, which the keystone's prefix then restricts
along `f` and pushes forward by the scalar lift over `R`.

This moves any such morphism of the transported internal Hom out of the prefix: what is left in
front is the prefix read one step earlier, and what comes out behind the counit is the image of the
morphism under the internal Hom over the lift of `A`, pushed forward by derived restriction along
the lifted ring map.

That is the position `CochainComplex.DerivedTensor.Q_map_transportedMonoidalInvTail` puts the
[stacks 0GMT] occurrence of `e` in: both are then the scalar lift over `A` of a localized morphism
of `D(A)`, in the world of modules over the lift of `A`.  What still separates them is that the
[stacks 068I] occurrence sits inside the internal Hom and the [stacks 0GMT] one does not; bringing
them together needs the [stacks 068I] side uncurried. -/
public theorem functor_map_comp_hom_map_comp_counit
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A) :
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    let E := scalarEquivalence.{uR, max uR uA uM} R
    let S := scalarEquivalence.{uA, max uR uA uM} A
    let U := (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory
    let V := (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory
    let δ : S.inverse ⋙ U ≅ V ⋙ E.inverse := scalarRestrictionIso.{uR, uA, uM} f
    let HA := StacksDraft.DerivedHom.DerivedInternalHom.Model.hom
      (ULift.{max uR uA uM} A)
    let dA := StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{uA, max uR uA uM,
      max uR uA uM + 1} A
    ∀ (X : DerivedCategory (ModuleCat.{max uR uA uM} R))
      (P : DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)))
      (Y₁ Y₂ M N : DerivedCategory (ModuleCat.{max uR uA uM} A))
      (l : Y₂ ⟶ Y₁) (γ : M ⟶ N)
      (g : X ⟶ U.obj (dA.hom.obj (Opposite.op Y₁, M)))
      (p : V.obj (HA.obj (Opposite.op (S.functor.obj Y₂), S.functor.obj N)) ⟶ P),
    E.functor.map ((g ≫ U.map (dA.hom.map ((l.op, γ) :
              ((Opposite.op Y₁, M) : (DerivedCategory (ModuleCat.{max uR uA uM} A))ᵒᵖ ×
                DerivedCategory (ModuleCat.{max uR uA uM} A)) ⟶ (Opposite.op Y₂, N)))) ≫
          δ.hom.app (HA.obj (Opposite.op (S.functor.obj Y₂), S.functor.obj N))) ≫
        E.counitIso.hom.app (V.obj (HA.obj (Opposite.op (S.functor.obj Y₂),
          S.functor.obj N))) ≫ p =
      E.functor.map (g ≫ δ.hom.app (HA.obj (Opposite.op (S.functor.obj Y₁),
            S.functor.obj M))) ≫
        E.counitIso.hom.app (V.obj (HA.obj (Opposite.op (S.functor.obj Y₁),
            S.functor.obj M))) ≫
          V.map (HA.map (((S.functor.map l).op, S.functor.map γ) :
            ((Opposite.op (S.functor.obj Y₁), S.functor.obj M) :
                (DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)))ᵒᵖ ×
                  DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A))) ⟶
              (Opposite.op (S.functor.obj Y₂), S.functor.obj N))) ≫ p := by
  intro f' E S U V δ HA dA X P Y₁ Y₂ M N l γ g p
  exact map_out_of_delta_prefix E S U V δ g
    (HA.map (((S.functor.map l).op, S.functor.map γ) :
      ((Opposite.op (S.functor.obj Y₁), S.functor.obj M) :
          (DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)))ᵒᵖ ×
            DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A))) ⟶
        (Opposite.op (S.functor.obj Y₂), S.functor.obj N))) p

/-- **Cancelling an invertible pair in the middle of a four-factor composite.**  Stated over a
variable category so that the concrete instance is checked at default transparency: the concrete
composite is spelled with two definitionally but not syntactically equal presentations of the
K-flat description of `F (Q K ⊗ᴸ_R Q L)`, and a rewrite in place fails on the second. -/
private theorem cancelMiddle {C : Type u₁} [Category.{v₁} C] {W X Y Z : C}
    (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ X) (d : X ⟶ Z) (hbc : b ≫ c = 𝟙 X) :
    (a ≫ b) ≫ c ≫ d = a ≫ d := by
  rw [Category.assoc, ← Category.assoc b, hbc, Category.id_comp]

section KFlatAbsorption

attribute [local instance] Dualizing.extendScalarsAdditiveOfRingHom

open CochainComplex.DerivedTensor CochainComplex.DerivedExtensionScalars
open CochainComplex.ExtendScalars

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
  (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
    DerivedCategory (ModuleCat.{max uR uA uM} A))
  (comparison : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [hF : F.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]

include hF in
/-- **The [stacks 068I] occurrence of the tensor base-change isomorphism absorbed into the chosen
K-injective resolution.**

By `Dualizing.tensorBaseChangeMor_transpose_eq_q_obj` the [stacks 0A63] transpose over `A` of the
[stacks 068I] candidate ends in the internal Hom of `DerivedCategory.Q.map e.hom` followed by the
inverse of the K-flat description `Stacks.DerivedHom.BaseChange.tensorKFlatComparisonIso` of
`F (Q K ⊗ᴸ_R Q L)`; and the covariant slot of the keystone's [stacks 0E1W] prefix is then
identified with the class of the K-injective complex `J` by
`Stacks.DerivedHom.BaseChange.tensorKFlatKInjectiveLift`, which *begins* with the scalar lift of
that same K-flat description.

So the K-flat description cancels, and what is left of the [stacks 068I] occurrence of `e` is a
chain map: the degreewise restriction of `e.hom` along `ULift.ringEquiv` over `A`, followed by the
chosen resolution `n`.  Its leading factor is exactly the leading factor of
`CochainComplex.DerivedTensor.transportedMonoidalInvTail`, read in the opposite direction -- which
is where the two occurrences of `e` in the keystone's residual equation cancel.

The step that turns the scalar lift of `DerivedCategory.Q.map e.hom` into the localization of its
degreewise restriction is
`Stacks.DerivedHom.BaseChange.scalarEquivalence_functor_map_Q_map_comp_scalarLiftQObjIso` at
`γ = e.hom`. -/
public theorem functor_map_comp_tensorKFlatKInjectiveLift_hom
    (K L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (hK : IsKFlat.{uR, max uR uA uM} K) (hL : IsKFlat.{uR, max uR uA uM} L)
    (J : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)) ℤ) [J.IsKInjective]
    (n : ((ModuleCat.restrictScalars.{max uR uA uM}
        (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj
            (tensorComplex.{uR, max uR uA uM} K L)) ⟶ J) [QuasiIso n]
    (e : tensorComplex.{uA, max uR uM}
        ((extensionOfScalarsCochain.{uR, uA, uM} f).obj K)
        ((extensionOfScalarsCochain.{uR, uA, uM} f).obj L) ≅
      (extensionOfScalarsCochain.{uR, uA, uM} f).obj (tensorComplex.{uR, max uA uM} K L)) :
    (scalarEquivalence.{uA, max uR uA uM} A).functor.map
          (DerivedCategory.Q.map e.hom ≫
            (tensorKFlatComparisonIso.{uR, uA, uM} f F comparison K L hK hL).inv) ≫
        (tensorKFlatKInjectiveLift.{uR, uA, uM} f F comparison K L hK hL J n).hom =
      (scalarLiftQObjIso.{uA, max uR uA uM} A
            (tensorComplex.{uA, max uR uM}
              ((extensionOfScalarsCochain.{uR, uA, uM} f).obj K)
              ((extensionOfScalarsCochain.{uR, uA, uM} f).obj L))).hom ≫
        DerivedCategory.Q.map (((ModuleCat.restrictScalars.{max uR uA uM}
              (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).toRingHom).mapHomologicalComplex
            (ComplexShape.up ℤ)).map e.hom ≫ n) := by
  have hb := scalarEquivalence_functor_map_Q_map_comp_scalarLiftQObjIso.{uA,
    max uR uA uM} A e.hom
  have hcancel : (scalarEquivalence.{uA, max uR uA uM} A).functor.map
          (tensorKFlatComparisonIso.{uR, uA, uM} f F comparison K L hK hL).inv ≫
        (scalarEquivalence.{uA, max uR uA uM} A).functor.map
          (F.map (derivedTensor_comparison.{uR, max uR uA uM} R K L hL).hom ≫
            comparison.app (tensorComplex.{uR, max uR uA uM} K L)) = 𝟙 _ :=
    ((scalarEquivalence.{uA, max uR uA uM} A).functor.mapIso
      (tensorKFlatComparisonIso.{uR, uA, uM} f F comparison K L hK hL)).inv_hom_id
  have hsplit : (scalarEquivalence.{uA, max uR uA uM} A).functor.map
        (DerivedCategory.Q.map e.hom ≫
          (tensorKFlatComparisonIso.{uR, uA, uM} f F comparison K L hK hL).inv) =
      (scalarEquivalence.{uA, max uR uA uM} A).functor.map (DerivedCategory.Q.map e.hom) ≫
        (scalarEquivalence.{uA, max uR uA uM} A).functor.map
          (tensorKFlatComparisonIso.{uR, uA, uM} f F comparison K L hK hL).inv :=
    CategoryTheory.Functor.map_comp _ _ _
  have step : (scalarEquivalence.{uA, max uR uA uM} A).functor.map
          (DerivedCategory.Q.map e.hom ≫
            (tensorKFlatComparisonIso.{uR, uA, uM} f F comparison K L hK hL).inv) ≫
        (tensorKFlatKInjectiveLift.{uR, uA, uM} f F comparison K L hK hL J n).hom =
      (scalarEquivalence.{uA, max uR uA uM} A).functor.map (DerivedCategory.Q.map e.hom) ≫
        (scalarLiftQObjIso.{uA, max uR uA uM} A
            ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj
              (tensorComplex.{uR, max uR uA uM} K L))).hom ≫
          DerivedCategory.Q.map n := by
    rw [tensorKFlatKInjectiveLift_hom.{uR, uA, uM} f F comparison K L hK hL J n, hsplit]
    exact cancelMiddle _ _ _ _ hcancel
  refine step.trans (((reassoc_of% hb) (DerivedCategory.Q.map n)).trans ?_)
  exact congrArg (fun z => (scalarLiftQObjIso.{uA, max uR uA uM} A
      (tensorComplex.{uA, max uR uM}
        ((extensionOfScalarsCochain.{uR, uA, uM} f).obj K)
        ((extensionOfScalarsCochain.{uR, uA, uM} f).obj L))).hom ≫ z)
    (CategoryTheory.Functor.map_comp DerivedCategory.Q
      (((ModuleCat.restrictScalars.{max uR uA uM}
          (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).map e.hom) n).symm

end KFlatAbsorption

end Stacks.DerivedHom.BaseChange

namespace CochainComplex.DerivedTensor

attribute [local instance] Dualizing.extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)

/-- **The localization of the transported monoidality tail, with the tensor base-change
isomorphism read in `D(A)`.**

`CochainComplex.DerivedTensor.transportedMonoidalInvTail` carries the tensor base-change
isomorphism `e` as the degreewise restriction of `e.inv` along `ULift.ringEquiv` over `A`.
Naturality of the scalar-lift presentation
`Stacks.DerivedHom.BaseChange.scalarLiftQObjIso`, read at `e.inv`, replaces that by the scalar
lift over `A` of `DerivedCategory.Q.map e.inv`, conjugated by the presentations at the total
tensor complex and at the base change of the total tensor complex. -/
public theorem Q_map_transportedMonoidalInvTail
    (K L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (e : tensorComplex.{uA, max uR uM}
        ((extensionOfScalarsCochain.{uR, uA, uM} f).obj K)
        ((extensionOfScalarsCochain.{uR, uA, uM} f).obj L) ≅
      (extensionOfScalarsCochain.{uR, uA, uM} f).obj (tensorComplex.{uR, max uA uM} K L)) :
    DerivedCategory.Q.map (transportedMonoidalInvTail.{uR, uA, uM} f K L e) =
      (scalarLiftQObjIso.{uA, max uR uA uM} A
            ((extensionOfScalarsCochain.{uR, uA, uM} f).obj
              (tensorComplex.{uR, max uA uM} K L))).inv ≫
        (scalarEquivalence.{uA, max uR uA uM} A).functor.map (DerivedCategory.Q.map e.inv) ≫
          (scalarLiftQObjIso.{uA, max uR uA uM} A
              (tensorComplex.{uA, max uR uM}
                ((extensionOfScalarsCochain.{uR, uA, uM} f).obj K)
                ((extensionOfScalarsCochain.{uR, uA, uM} f).obj L))).hom ≫
            DerivedCategory.Q.map
              ((restrictScalarsTensorComplexIso
                  (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A)
                  ((extensionOfScalarsCochain.{uR, uA, uM} f).obj K)
                  ((extensionOfScalarsCochain.{uR, uA, uM} f).obj L)).inv ≫
                (MonoidalCategory.tensorIso (extendScalarsLiftChainIso.{uR, uA, uM} f K)
                  (extendScalarsLiftChainIso.{uR, uA, uM} f L)).inv) := by
  have hb := scalarEquivalence_functor_map_Q_map_comp_scalarLiftQObjIso.{uA,
    max uR uA uM} A e.inv
  have h1 : DerivedCategory.Q.map (transportedMonoidalInvTail.{uR, uA, uM} f K L e) =
      DerivedCategory.Q.map (((ModuleCat.restrictScalars.{max uR uA uM}
            (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).map e.inv) ≫
        DerivedCategory.Q.map
          ((restrictScalarsTensorComplexIso
              (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A)
              ((extensionOfScalarsCochain.{uR, uA, uM} f).obj K)
              ((extensionOfScalarsCochain.{uR, uA, uM} f).obj L)).inv ≫
            (MonoidalCategory.tensorIso (extendScalarsLiftChainIso.{uR, uA, uM} f K)
              (extendScalarsLiftChainIso.{uR, uA, uM} f L)).inv) := by
    rw [← CategoryTheory.Functor.map_comp]
    rfl
  refine h1.trans ?_
  rw [← Category.assoc ((scalarEquivalence.{uA, max uR uA uM} A).functor.map
    (DerivedCategory.Q.map e.inv)), hb]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_assoc]

/-- **The transported monoidality tail with the tensor base-change isomorphism in the
[stacks 068I] position.**

`CochainComplex.DerivedTensor.Q_map_transportedMonoidalInvTail` pushed forward by derived
restriction of scalars along the lifted ring map, with the scalar lift over `A` of
`DerivedCategory.Q.map e.inv` carried across the transported comparison `τ` of [stacks 0E1W] by
`Stacks.DerivedHom.BaseChange.scalarRestrictionTransportedIso_naturality`.

The tensor base-change isomorphism now occurs as `E.functor` of the derived restriction along `f`
of `DerivedCategory.Q.map e.inv`.  That is the position the [stacks 068I] side of the keystone of
Chapter 47 reads it in: the prefix-pinning hypothesis of
`Dualizing.tensorBaseChangeMor_eq_of_unit_chain_prefix` begins with `E.functor` of the unit of
[stacks 0GMT] followed by the restriction along `f` of the transposed candidate, and the candidate
carries `e.hom` inside the internal Hom over `A`. -/
public theorem map_Q_map_transportedMonoidalInvTail
    (K L : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (e : tensorComplex.{uA, max uR uM}
        ((extensionOfScalarsCochain.{uR, uA, uM} f).obj K)
        ((extensionOfScalarsCochain.{uR, uA, uM} f).obj L) ≅
      (extensionOfScalarsCochain.{uR, uA, uM} f).obj (tensorComplex.{uR, max uA uM} K L)) :
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    let E := scalarEquivalence.{uR, max uR uA uM} R
    let S := scalarEquivalence.{uA, max uR uA uM} A
    let U := (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory
    let V := (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory
    let δ : S.inverse ⋙ U ≅ V ⋙ E.inverse := scalarRestrictionIso.{uR, uA, uM} f
    let τ : U ⋙ E.functor ≅ S.functor ⋙ V :=
      Iso.compInverseIso (H := E.symm)
        ((Iso.inverseCompIso (G := S.symm) δ.symm).symm ≪≫
          (Functor.associator _ _ _).symm)
    V.map (DerivedCategory.Q.map (transportedMonoidalInvTail.{uR, uA, uM} f K L e)) =
      V.map (scalarLiftQObjIso.{uA, max uR uA uM} A
              ((extensionOfScalarsCochain.{uR, uA, uM} f).obj
                (tensorComplex.{uR, max uA uM} K L))).inv ≫
        (τ.inv.app (DerivedCategory.Q.obj ((extensionOfScalarsCochain.{uR, uA, uM} f).obj
              (tensorComplex.{uR, max uA uM} K L))) ≫
            E.functor.map (U.map (DerivedCategory.Q.map e.inv)) ≫
              τ.hom.app (DerivedCategory.Q.obj (tensorComplex.{uA, max uR uM}
                ((extensionOfScalarsCochain.{uR, uA, uM} f).obj K)
                ((extensionOfScalarsCochain.{uR, uA, uM} f).obj L)))) ≫
          V.map ((scalarLiftQObjIso.{uA, max uR uA uM} A
                (tensorComplex.{uA, max uR uM}
                  ((extensionOfScalarsCochain.{uR, uA, uM} f).obj K)
                  ((extensionOfScalarsCochain.{uR, uA, uM} f).obj L))).hom ≫
            DerivedCategory.Q.map
              ((restrictScalarsTensorComplexIso
                  (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A)
                  ((extensionOfScalarsCochain.{uR, uA, uM} f).obj K)
                  ((extensionOfScalarsCochain.{uR, uA, uM} f).obj L)).inv ≫
                (MonoidalCategory.tensorIso (extendScalarsLiftChainIso.{uR, uA, uM} f K)
                  (extendScalarsLiftChainIso.{uR, uA, uM} f L)).inv)) := by
  intro f'
  rw [Q_map_transportedMonoidalInvTail.{uR, uA, uM} f K L e]
  exact transported_naturality_comp _ _ _ _ _ (DerivedCategory.Q.map e.inv) _ _

end CochainComplex.DerivedTensor

end
