module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionComp
public import StacksFrontier.AlgebraicGeometry.Spaces.RingSheafChartProjection
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHomInverseImage
public import StacksFrontier.AlgebraicGeometry.Size.CoveringsSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleToposSupplement
public import StacksFrontier.Topology.Dimension.KrullSupplement

/-!
# Chart components of maps out of an iterated inverse image

For a morphism `f : X ⟶ Y` of algebraic spaces and a map `φ : f⁻¹𝒪_Y ⟶ 𝒜` of sheaves of
commutative rings on the small étale site of `X`, the *chart components* of `φ`
(`AlgebraicGeometry.Space.inverseImageHomChartRingHom`) are the ring maps `𝒪_Y(V) ⟶ 𝒜(U)` on
the étale charts `U` of `X` above `X ×_Y V`. This file computes them for a map out of an
iterated inverse image: for `p : U ⟶ X`, `f : X ⟶ Y` and `ψ : p⁻¹𝒪_X ⟶ 𝒜`, the map

`(p ≫ f)⁻¹𝒪_Y ≅ p⁻¹f⁻¹𝒪_Y ⟶ p⁻¹𝒪_X ⟶ 𝒜`

(the comparison of Stacks 03G8, the inverse image along `p` of the structure map of `f`, then
`ψ`) has, at the chart of `U` above `U ×_Y W` attached to a chart `V` of `X` above `X ×_Y W`,
the chart component of `ψ` at `V` composed with pullback of functions along `V ⟶ W`.

## Main results

* `AlgebraicGeometry.Space.inverseImageHomChartRingHom_eq_directImageChartProjection`: the
  chart components read through the direct image of sheaves of sets.
* `AlgebraicGeometry.Space.inverseImageHomChartRingHom_compInverseImage`: the composition
  formula.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace CategoryTheory.Adjunction

/-- Transposing a map out of the left adjoint `L'` precomposed with the comparison of two left
adjoints of isomorphic right adjoints. -/
theorem homEquiv_leftAdjointUniq_ofNatIsoRight_inv_app_comp {C : Type*} [Category* C]
    {D : Type*} [Category* D] {L L' : C ⥤ D} {R R' : D ⥤ C} (adj1 : L ⊣ R) (adj2 : L' ⊣ R')
    (nu : R ≅ R') {X : C} {Y : D} (ξ : L.obj X ⟶ Y) :
    adj2.homEquiv X Y (((adj1.ofNatIsoRight nu).leftAdjointUniq adj2).inv.app X ≫ ξ) =
      adj1.homEquiv X Y ξ ≫ nu.hom.app Y := by
  have hL := leftAdjointUniq_ofNatIsoRight_hom_app_comp_homEquiv_symm adj1 adj2 nu
    (adj1.homEquiv X Y ξ ≫ nu.hom.app Y)
  rw [Category.assoc, Iso.hom_inv_id_app, Category.comp_id, Equiv.symm_apply_apply] at hL
  have h := (Iso.inv_comp_eq (((adj1.ofNatIsoRight nu).leftAdjointUniq adj2).app X)).mpr hL.symm
  rw [Iso.app_inv] at h
  rw [h, Equiv.apply_symm_apply]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
  (A : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u})

/-- The chart components of `φ : f⁻¹𝒪_Y ⟶ 𝒜` are the chart projections of its adjoint for
sheaves of sets. -/
theorem inverseImageHomChartRingHom_eq_directImageChartProjection
    (φ : (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImageRing.obj
      (smallEtaleRingedTopos B S hS Y).O ⟶ A) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (x : (smallEtaleRingedTopos B S hS Y).O.obj.obj (op V)) :
    inverseImageHomChartRingHom B S hS f A φ V j x =
      (directImageChartProjection B S hS f V j).app
        ((sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).obj A)
        (((smallEtaleRingedToposHom B S hS f).toToposHom.adj.homEquiv _ _
          ((sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map
            φ)).hom.app (op V) x) := by
  rw [inverseImageHomChartRingHom_apply, inverseImageHomRanSet_eq]
  rfl

/-- `inverseImageHomChartRingHom_eq_directImageChartProjection` with the adjoint given by an
equation. -/
theorem inverseImageHomChartRingHom_eq_of_homEquiv_eq
    (φ : (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImageRing.obj
      (smallEtaleRingedTopos B S hS Y).O ⟶ A) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (M : (smallEtaleRingedTopos B S hS Y).forgetRing.obj (smallEtaleRingedTopos B S hS Y).O ⟶
      (smallEtaleDirectImage B S hS f).obj
        ((sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).obj A))
    (hM : (smallEtaleRingedToposHom B S hS f).toToposHom.adj.homEquiv _ _
      ((sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map φ) = M)
    (x : (smallEtaleRingedTopos B S hS Y).O.obj.obj (op V)) :
    inverseImageHomChartRingHom B S hS f A φ V j x =
      (directImageChartProjection B S hS f V j).app
        ((sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).obj A)
        (M.hom.app (op V) x) := by
  subst hM
  exact inverseImageHomChartRingHom_eq_directImageChartProjection B S hS f A φ V j x

section Comp

variable {X Y Z : AlgebraicSpaces B S hS} (p : X ⟶ Y) (q : Y ⟶ Z)
  (A : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u})

/-- On underlying sheaves of sets the comparison `p⁻¹q⁻¹ ≅ (p ≫ q)⁻¹` of inverse images of
sheaves of commutative rings is the geometric comparison. -/
theorem forget_map_compInverseImageRingIso_hom :
    (smallEtaleRingedTopos B S hS X).forgetRing.map
        ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS p q).hom.app
          (smallEtaleRingedTopos B S hS Z).O) =
      (smallEtaleRingedToposHom_compInverseImageIso B S hS p q).hom.app
        ((smallEtaleRingedTopos B S hS Z).forgetRing.obj (smallEtaleRingedTopos B S hS Z).O) := by
  have h₁ := forget_map_inverseImageCommRingComp_hom
    (smallEtaleRingedToposHom B S hS q).toToposHom
    (smallEtaleRingedToposHom B S hS p).toToposHom (smallEtaleRingedTopos B S hS Z).O
  have : PreservesFiniteProducts ((smallEtaleRingedToposHom B S hS q).toToposHom.comp
      (smallEtaleRingedToposHom B S hS p).toToposHom).inverseImage :=
    ⟨fun n ↦ ((smallEtaleRingedToposHom B S hS q).toToposHom.comp
      (smallEtaleRingedToposHom B S hS p).toToposHom).preservesFiniteLimits.preservesFiniteLimits
        (Discrete (Fin n))⟩
  have : PreservesFiniteProducts
      (smallEtaleRingedToposHom B S hS (p ≫ q)).toToposHom.inverseImage :=
    ⟨fun n ↦ (smallEtaleRingedToposHom B S hS (p ≫ q)).toToposHom.preservesFiniteLimits
      |>.preservesFiniteLimits (Discrete (Fin n))⟩
  have h₂ := underlyingRingSheaf_map_pullbackCommRingSheafFunctorIsoOfNatIso_hom
    (smallEtaleRingedTopos B S hS X).J (smallEtaleRingedTopos B S hS Z).O
    (smallEtaleRingedToposHom_compInverseImageIso B S hS p q)
  refine Eq.trans ((smallEtaleRingedTopos B S hS X).forgetRing.map_comp _ _) ?_
  refine Eq.trans (congrArg₂ (fun a b ↦ a ≫ b) h₁ h₂) ?_
  exact Category.id_comp _

/-- On underlying sheaves of sets the inverse of the comparison `p⁻¹q⁻¹ ≅ (p ≫ q)⁻¹` of inverse
images of sheaves of commutative rings is the inverse of the geometric comparison. -/
theorem forget_map_compInverseImageRingIso_inv :
    (smallEtaleRingedTopos B S hS X).forgetRing.map
        ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS p q).inv.app
          (smallEtaleRingedTopos B S hS Z).O) =
      (smallEtaleRingedToposHom_compInverseImageIso B S hS p q).inv.app
        ((smallEtaleRingedTopos B S hS Z).forgetRing.obj (smallEtaleRingedTopos B S hS Z).O) :=
  congrArg Iso.inv (show (smallEtaleRingedTopos B S hS X).forgetRing.mapIso
      ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS p q).app
        (smallEtaleRingedTopos B S hS Z).O) =
    (smallEtaleRingedToposHom_compInverseImageIso B S hS p q).app
      ((smallEtaleRingedTopos B S hS Z).forgetRing.obj (smallEtaleRingedTopos B S hS Z).O) from
    Iso.ext (forget_map_compInverseImageRingIso_hom B S hS p q))

/-- The chart projection along `p ≫ q` of `s ≫ q_*m` followed by the composition comparison is
the chart projection along `p` of `m` applied to the chart projection along `q` of `s`. -/
theorem directImageChartProjection_comp_pushforward_map
    {F : Sheaf (SmallEtale.topology B S hS X.1) (Type u)}
    {G : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)}
    {Q : Sheaf (SmallEtale.topology B S hS Z.1) (Type u)}
    (s : Q ⟶ (smallEtaleRingedToposHom B S hS q).toToposHom.pushforward.obj G)
    (m : G ⟶ (smallEtaleRingedToposHom B S hS p).toToposHom.pushforward.obj F)
    (W : SmallEtale B S hS Z.1)
    (j : StructuredArrow (op (chartBaseChange B S hS q W)) (comparisonFunctor B S hS Y).op)
    (k : StructuredArrow (op (chartBaseChange B S hS p j.right.unop))
      (comparisonFunctor B S hS X).op)
    (x : Q.obj.obj (op W)) :
    (directImageChartProjection B S hS (p ≫ q) W
        (StructuredArrow.mk ((chartBaseChangeComp B S hS p q W j).op ≫ k.hom))).app F
        ((s ≫ (smallEtaleRingedToposHom B S hS q).toToposHom.pushforward.map m ≫
          (smallToposMorphismTypeU_comp B S hS p q).hom.app F).hom.app (op W) x) =
      (directImageChartProjection B S hS p j.right.unop k).app F
        (m.hom.app j.right
          ((directImageChartProjection B S hS q W j).app G (s.hom.app (op W) x))) :=
  (directImageChartProjection_smallToposMorphismTypeU_comp B S hS p q W j k F
    (((smallEtaleDirectImage B S hS q).map m).hom.app (op W) (s.hom.app (op W) x))).trans
    (congrArg ((directImageChartProjection B S hS p j.right.unop k).app F)
      (directImageChartProjection_map B S hS q W j m (s.hom.app (op W) x)))

/-- **The adjoint of a map out of an iterated inverse image**, on underlying sheaves of sets:
the adjoint along `p ≫ q` of `(p ≫ q)⁻¹𝒪_Z ≅ p⁻¹q⁻¹𝒪_Z ⟶ p⁻¹𝒪_Y ⟶ 𝒜` is the structure map of
`q`, followed by the direct image along `q` of the adjoint of `ψ` and the composition
comparison of direct images. -/
theorem adj_homEquiv_compInverseImage
    (ψ : (smallEtaleRingedToposHom B S hS p).toToposHom.inverseImageRing.obj
      (smallEtaleRingedTopos B S hS Y).O ⟶ A)
    (a : (smallEtaleRingedToposHom B S hS q).toToposHom.inverseImage.obj
        ((smallEtaleRingedTopos B S hS Z).forgetRing.obj (smallEtaleRingedTopos B S hS Z).O) ⟶
      (smallEtaleRingedTopos B S hS Y).forgetRing.obj (smallEtaleRingedTopos B S hS Y).O)
    (ha : a = (sheafCompose (SmallEtale.topology B S hS Y.1) (forget CommRingCat.{u})).map
      (smallEtaleRingedToposHom B S hS q).fSharpInverseImage)
    (m : (smallEtaleRingedTopos B S hS Y).forgetRing.obj (smallEtaleRingedTopos B S hS Y).O ⟶
      (smallEtaleRingedToposHom B S hS p).toToposHom.pushforward.obj
        ((sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).obj A))
    (hm : m = (smallEtaleRingedToposHom B S hS p).toToposHom.adj.homEquiv _ _
      ((sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map ψ)) :
    (smallEtaleRingedToposHom B S hS (p ≫ q)).toToposHom.adj.homEquiv _ _
      ((sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map
      ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS p q).inv.app
          (smallEtaleRingedTopos B S hS Z).O ≫
        (smallEtaleInverseImageRing B S hS p).map
          (smallEtaleRingedToposHom B S hS q).fSharpInverseImage ≫ ψ)) =
      (smallEtaleRingedToposHom B S hS q).toToposHom.adj.homEquiv _ _ a ≫
        (smallEtaleRingedToposHom B S hS q).toToposHom.pushforward.map m ≫
        (smallToposMorphismTypeU_comp B S hS p q).hom.app
          ((sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).obj A) := by
  subst ha hm
  let tp := (smallEtaleRingedToposHom B S hS p).toToposHom
  let tq := (smallEtaleRingedToposHom B S hS q).toToposHom
  let fX := sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})
  let a := (sheafCompose (SmallEtale.topology B S hS Y.1) (forget CommRingCat.{u})).map
    (smallEtaleRingedToposHom B S hS q).fSharpInverseImage
  let ξ := tp.inverseImage.map a ≫ fX.map ψ
  have hb : fX.map ((smallEtaleInverseImageRing B S hS p).map
      (smallEtaleRingedToposHom B S hS q).fSharpInverseImage) = tp.inverseImage.map a :=
    MorphismOfTopoi.inverseImageRing_map_forget tp _
  have e1 : fX.map
      ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS p q).inv.app
          (smallEtaleRingedTopos B S hS Z).O ≫
        (smallEtaleInverseImageRing B S hS p).map
          (smallEtaleRingedToposHom B S hS q).fSharpInverseImage ≫ ψ) =
      (smallEtaleRingedToposHom_compInverseImageIso B S hS p q).inv.app _ ≫ ξ :=
    (fX.map_comp _ _).trans (congrArg₂ (· ≫ ·) (forget_map_compInverseImageRingIso_inv B S hS p q)
      ((fX.map_comp _ _).trans (congrArg (· ≫ fX.map ψ) hb)))
  have hc : (tq.comp tp).adj.homEquiv _ _ ξ = tq.adj.homEquiv _ _ (tp.adj.homEquiv _ _ ξ) :=
    congrArg (fun e ↦ (e _ _ : _ ≃ _) ξ)
      (Adjunction.comp_homEquiv (adj₁ := tq.adj) (adj₂ := tp.adj))
  have hU := Adjunction.homEquiv_leftAdjointUniq_ofNatIsoRight_inv_app_comp (tq.comp tp).adj
    (smallEtaleRingedToposHom B S hS (p ≫ q)).toToposHom.adj
    (smallToposMorphismTypeU_comp B S hS p q) ξ
  have hN : tq.adj.homEquiv _ _ (tp.adj.homEquiv _ _ ξ) =
      tq.adj.homEquiv _ _ a ≫ tq.pushforward.map (tp.adj.homEquiv _ _ (fX.map ψ)) :=
    (congrArg (tq.adj.homEquiv _ _) (tp.adj.homEquiv_naturality_left a (fX.map ψ))).trans
      (tq.adj.homEquiv_naturality_right a _)
  exact (congrArg ((smallEtaleRingedToposHom B S hS (p ≫ q)).toToposHom.adj.homEquiv _ _) e1).trans
    (hU.trans ((congrArg (· ≫ _) (hc.trans hN)).trans (Category.assoc _ _ _)))

/-- **The chart components of a map out of an iterated inverse image.** For `ψ : p⁻¹𝒪_Y ⟶ 𝒜`
the composite `(p ≫ q)⁻¹𝒪_Z ≅ p⁻¹q⁻¹𝒪_Z ⟶ p⁻¹𝒪_Y ⟶ 𝒜` has, at the chart of `X` above
`X ×_Z W` attached to a chart `V` of `Y` above `Y ×_Z W` and a chart of `X` above `X ×_Y V`,
the chart component of `ψ` composed with pullback of functions along `V ⟶ W`. -/
theorem inverseImageHomChartRingHom_compInverseImage
    (ψ : (smallEtaleRingedToposHom B S hS p).toToposHom.inverseImageRing.obj
      (smallEtaleRingedTopos B S hS Y).O ⟶ A)
    (W : SmallEtale B S hS Z.1)
    (j : StructuredArrow (op (chartBaseChange B S hS q W)) (comparisonFunctor B S hS Y).op)
    (k : StructuredArrow (op (chartBaseChange B S hS p j.right.unop))
      (comparisonFunctor B S hS X).op)
    (x : (smallEtaleRingedTopos B S hS Z).O.obj.obj (op W)) :
    inverseImageHomChartRingHom B S hS (p ≫ q) A
        ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS p q).inv.app
            (smallEtaleRingedTopos B S hS Z).O ≫
          (smallEtaleInverseImageRing B S hS p).map
            (smallEtaleRingedToposHom B S hS q).fSharpInverseImage ≫ ψ)
        W (StructuredArrow.mk ((chartBaseChangeComp B S hS p q W j).op ≫ k.hom)) x =
      inverseImageHomChartRingHom B S hS p A ψ j.right.unop k
        (chartPullback B S hS q W j x) := by
  let fX := sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})
  let m := (smallEtaleRingedToposHom B S hS p).toToposHom.adj.homEquiv _ _ (fX.map ψ)
  refine (inverseImageHomChartRingHom_eq_of_homEquiv_eq B S hS (p ≫ q) A _ W _ _
    (adj_homEquiv_compInverseImage B S hS p q A ψ _ rfl m rfl) x).trans
    (Eq.trans ?_ (inverseImageHomChartRingHom_eq_of_homEquiv_eq B S hS p A ψ _ k m rfl _).symm)
  refine (directImageChartProjection_comp_pushforward_map B S hS p q (F := fX.obj A)
    (G := (smallEtaleRingedTopos B S hS Y).forgetRing.obj (smallEtaleRingedTopos B S hS Y).O)
    (Q := (smallEtaleRingedTopos B S hS Z).forgetRing.obj (smallEtaleRingedTopos B S hS Z).O)
    ((smallEtaleRingedToposHom B S hS q).toToposHom.adj.homEquiv _ _
      ((sheafCompose (SmallEtale.topology B S hS Y.1) (forget CommRingCat.{u})).map
        (smallEtaleRingedToposHom B S hS q).fSharpInverseImage)) m W j k x).trans ?_
  exact congrArg ((directImageChartProjection B S hS p j.right.unop k).app (fX.obj A))
    (congrArg (m.hom.app j.right)
      ((inverseImageHomChartRingHom_eq_of_homEquiv_eq B S hS q _
        (smallEtaleRingedToposHom B S hS q).fSharpInverseImage W j _ rfl x).symm.trans
        (inverseImageHomChartRingHom_fSharpInverseImage B S hS q W j x)))

end Comp

end AlgebraicGeometry.Space

end
