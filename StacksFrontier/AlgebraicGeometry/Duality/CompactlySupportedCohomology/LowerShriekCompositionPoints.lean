module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.BindConstMap
public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.LowerShriekComposition

/-!
# Points of `Rg_! Rf_! K` and `Rg_!` applied to a morphism into a constant pro-object

In the proof of [Stacks, Tag 0G55] the functor of points of `Rg_! Rf_! K` is identified with
`L ↦ Hom_X(K, f^! g^! L)` (`AlgebraicGeometry.lowerShriekCompPointsUpperShriekIso`). For a
morphism `φ : Rf_! K ⟶ K₀` into a constant pro-object and a point `x` of `Rg_! K₀` at `L`, i.e. a
morphism `ψ_x : K₀ ⟶ g^! L`, the point of `Rg_! Rf_! K` obtained by applying `Rg_!` to `φ`
(`CategoryTheory.ProSeq.bindConstMap`) corresponds to the morphism `K ⟶ f^! g^! L` attached by
[Stacks, Tag 0G51] for `f` to the composite `Rf_! K ⟶ K₀ ⟶ g^! L`.

## Main definitions

* `CategoryTheory.ProSeq.bindObjPointsIsoOfHomIso`: the identification of the proof of
  [Stacks, Tag 0G55], for abstract adjointness isomorphisms.

## Main results

* `CategoryTheory.ProSeq.bindObjPointsIsoOfHomIso_hom_app_bindConstLeg`: the chase above.
* `AlgebraicGeometry.lowerShriekCompPointsUpperShriekIso_hom_app_bindConstMap`: its instance.

## References

* [Stacks Project, Tag 0G55](https://stacks.math.columbia.edu/tag/0G55)
* [Stacks Project, Tag 0G56](https://stacks.math.columbia.edu/tag/0G56)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] CategoryTheory.uliftCategory

universe v u

namespace CategoryTheory.ProSeq

section Helpers

variable {𝒟 : Type v} [Category.{v} 𝒟]

/-- Under `CategoryTheory.ProSeq.ofPointsIso`, the leg at `n` of the class of `g : M_n ⟶ N` is the
class `Pro.seqStage M g`. -/
lemma ofPointsIso_inv_app_ι_app (M : ℕᵒᵖ ⥤ 𝒟) (n : ℕ) {N : 𝒟} (g : M.obj (op n) ⟶ N) :
    (ofPointsIso M).inv.app N ((colimit.ι (M.rightOp ⋙ coyoneda) n).app N g) =
      (Pro.seqHomColimIso M).inv.app N (Pro.seqStage M g) := by
  have h := HasColimit.ι_isoOfEquivalence_inv (F := M.op ⋙ coyoneda)
    (G := M.rightOp ⋙ coyoneda) (opOpEquivalence ℕ) (NatIso.ofComponents (fun _ => Iso.refl _)) n
  have h₁ : (M.rightOp ⋙ coyoneda).map ((opOpEquivalence ℕ).counitInv.app n) = 𝟙 _ :=
    (congrArg (M.rightOp ⋙ coyoneda).map (Subsingleton.elim _ (𝟙 n))).trans
      ((M.rightOp ⋙ coyoneda).map_id n)
  rw [h₁, Category.id_comp] at h
  exact congrArg ((Pro.seqHomColimIso M).inv.app N) (ConcreteCategory.congr_hom (congr_app h N) g)

/-- The class of `g ≫ h` is the image of the class of `g` under the functor of points. -/
lemma seqHomColimIso_inv_app_seqStage_comp (M : ℕᵒᵖ ⥤ 𝒟) {n : ℕ} {N N' : 𝒟}
    (g : M.obj (op n) ⟶ N) (h : N ⟶ N') :
    (Pro.seqHomColimIso M).inv.app N' (Pro.seqStage M (g ≫ h)) =
      (of M).points.map h ((Pro.seqHomColimIso M).inv.app N (Pro.seqStage M g)) := by
  rw [← Pro.seqHomColim_map_seqStage]
  exact NatTrans.naturality_apply (Pro.seqHomColimIso M).inv h _

/-- The element of the functor of points of `P` at `L'` attached to `g ≫ const.map h` is the image
under `h` of the element attached to `g`. -/
lemma homConstEquiv_comp_const_map {P : ProSeq 𝒟} {L L' : 𝒟} (g : P ⟶ const.obj L) (h : L ⟶ L') :
    homConstEquiv P L' (g ≫ const.map h) = P.points.map h (homConstEquiv P L g) := by
  rw [homConstEquiv_apply, homConstEquiv_apply]
  exact (coyonedaEquiv_naturality g.unop.hom h).symm

/-- An isomorphism of pro-objects acts bijectively on functors of points. -/
private lemma iso_unop_hom_app_inv_app_hom_app {P Q : ProSeq 𝒟} (e : P ≅ Q) (X : 𝒟)
    (y : Q.points.obj X) : e.inv.unop.hom.app X (e.hom.unop.hom.app X y) = y := by
  exact congrArg (fun t : Q ⟶ Q => t.unop.hom.app X y) e.inv_hom_id

end Helpers

variable {𝒜 : Type v} [Category.{v} 𝒜] {𝒞 : Type v} [Category.{v} 𝒞] {𝒟 : Type v}
  [Category.{v} 𝒟] {𝒞p : Type v} [Category.{v} 𝒞p] {𝒟p : Type v} [Category.{v} 𝒟p]
  {𝒜s : Type v} [Category.{v} 𝒜s]
  (F : 𝒜 ⥤ ProSeq 𝒞) (G : 𝒞 ⥤ ProSeq 𝒟) (ιC : 𝒞 ⥤ 𝒞p) (ιD : 𝒟 ⥤ 𝒟p) (R : 𝒟p ⥤ 𝒞p)
  [∀ A : 𝒞 ⥤ Type v, ιC.HasLeftKanExtension A]
  (Φ : pointsFunctor G ≅ ιC.op ⋙ coyoneda ⋙ (Functor.whiskeringLeft _ _ _).obj (ιD ⋙ R))
  (T : 𝒞p ⥤ 𝒜s) (ιA : 𝒜 ⥤ 𝒜s)
  (Ψ : (F ⋙ map ιC).op ⋙ coyoneda ⋙ (Functor.whiskeringLeft _ _ _).obj const ≅
    ιA.op ⋙ coyoneda ⋙ (Functor.whiskeringLeft _ _ _).obj T)

/-- **`Hom(G F K, L) = Hom(K, T R L)`** for `G` and `F` with values in pro-objects, from
identifications `Hom(G M, L) = Hom(ι M, R L)` and `Hom(F K, N) = Hom(K, T N)`: the first four
identifications of the proof of [Stacks, Tag 0G55],
`Hom(G F K, L) = colim_n Hom(G M_n, L) = colim_n Hom(M_n, R L) = Hom(F K, R L) = Hom(K, T R L)`. -/
def bindObjPointsIsoOfHomIso (K : 𝒜) :
    (bindObj G (F.obj K)).points ≅ ιD ⋙ R ⋙ T ⋙ coyoneda.obj (op (ιA.obj K)) :=
  bindObjPointsIso G (ofSeqOfIso _) ≪≫
    HasColimit.isoOfNatIso (Functor.isoWhiskerLeft _ Φ) ≪≫
    colimitCompWhiskeringLeftIsoCompColimit
      ((seqOf (F.obj K)).rightOp ⋙ ιC.op ⋙ coyoneda) (ιD ⋙ R) ≪≫
    Functor.isoWhiskerLeft (ιD ⋙ R)
      ((ofPointsIso (seqOf (F.obj K) ⋙ ιC)).symm ≪≫
        (IsSequentialProObject _).ι.mapIso (mapOfIso ιC _).unop ≪≫
        ((IsSequentialProObject _).ι.mapIso ((map ιC).mapIso (ofSeqOfIso (F.obj K))).unop).symm ≪≫
        pointsIsoHomConst _ ≪≫ Ψ.app (op K)) ≪≫
    (Functor.associator _ _ _)

/-- **The chase of the proof of [Stacks, Tag 0G55] on a leg of `G` applied to `φ`.** For
`φ : F K ⟶ K₀` represented by `a : M_n ⟶ K₀` and a point `x` of `G K₀` at `L`, the point
`CategoryTheory.ProSeq.bindConstLeg G a x` of `bindObj G (F K)` corresponds to the morphism
`K ⟶ T R L` attached by `Ψ` to `F K ⟶ K₀ ⟶ R L`, the second arrow being the morphism attached to
`x` by `Φ`. -/
theorem bindObjPointsIsoOfHomIso_hom_app_bindConstLeg {K : 𝒜} {K₀ : 𝒞}
    (φ : F.obj K ⟶ const.obj K₀) {n : ℕ} (a : (seqOf (F.obj K)).obj (op n) ⟶ K₀)
    (ha : Pro.seqStage (seqOf (F.obj K)) a = constHomClass φ) (L : 𝒟)
    (x : (G.obj K₀).points.obj L) :
    (bindObjPointsIsoOfHomIso F G ιC ιD R Φ T ιA Ψ K).hom.app L ((bindConstLeg G a).app L x) =
      (Ψ.hom.app (op K)).app (R.obj (ιD.obj L))
        (mapConst ιC φ ≫ const.map ((Φ.hom.app (op K₀)).app L x)) := by
  set h : ιC.obj K₀ ⟶ (R.obj (ιD.obj L)) := (Φ.hom.app (op K₀)).app L x
  have key : ∀ z, (bindObjPointsIsoOfHomIso F G ιC ιD R Φ T ιA Ψ K).hom.app L z =
      (Ψ.hom.app (op K)).app (R.obj (ιD.obj L))
        ((pointsIsoHomConst ((map ιC).obj (F.obj K))).hom.app (R.obj (ιD.obj L))
        (((map ιC).map (ofSeqOfIso (F.obj K)).inv).unop.hom.app (R.obj (ιD.obj L))
          ((mapOfIso ιC (seqOf (F.obj K))).hom.unop.hom.app (R.obj (ιD.obj L))
            ((ofPointsIso ((seqOf (F.obj K)) ⋙ ιC)).inv.app (R.obj (ιD.obj L))
            ((colimitCompWhiskeringLeftIsoCompColimit ((seqOf (F.obj K)).rightOp ⋙ ιC.op ⋙ coyoneda)
              (ιD ⋙ R)).hom.app L ((HasColimit.isoOfNatIso
                (Functor.isoWhiskerLeft (seqOf (F.obj K)).rightOp Φ)).hom.app L
                  ((bindObjPointsIso G (ofSeqOfIso (F.obj K))).hom.app L z))))))) := fun _ => rfl
  have s1 : (bindObjPointsIso G (ofSeqOfIso (F.obj K))).hom.app L ((bindConstLeg G a).app L x) =
      (bindConstLeg G a).app L x :=
    ConcreteCategory.congr_hom (congr_app (bindConstLeg_comp_bindObjPointsIso_hom G a) L) x
  have s2 : (HasColimit.isoOfNatIso (Functor.isoWhiskerLeft (seqOf (F.obj K)).rightOp Φ)).hom.app L
      ((colimit.ι ((seqOf (F.obj K)).rightOp ⋙ pointsFunctor G) n).app L
        (((pointsFunctor G).map a.op).app L x)) =
      (colimit.ι (((seqOf (F.obj K)).rightOp ⋙ ιC.op ⋙ coyoneda) ⋙
        (Functor.whiskeringLeft _ _ _).obj (ιD ⋙ R)) n).app L
        ((Φ.hom.app (op ((seqOf (F.obj K)).obj (op n)))).app L
          (((pointsFunctor G).map a.op).app L x)) :=
    ConcreteCategory.congr_hom (congr_app
      (HasColimit.isoOfNatIso_ι_hom (Functor.isoWhiskerLeft (seqOf (F.obj K)).rightOp Φ) n) L)
        (((pointsFunctor G).map a.op).app L x)
  have s3 : (Φ.hom.app (op ((seqOf (F.obj K)).obj (op n)))).app L
      (((pointsFunctor G).map a.op).app L x) =
      ιC.map a ≫ h :=
    ConcreteCategory.congr_hom (congr_app (Φ.hom.naturality a.op) L) x
  have s4 : (colimitCompWhiskeringLeftIsoCompColimit ((seqOf (F.obj K)).rightOp ⋙ ιC.op ⋙ coyoneda)
      (ιD ⋙ R)).hom.app L ((colimit.ι (((seqOf (F.obj K)).rightOp ⋙ ιC.op ⋙ coyoneda) ⋙
        (Functor.whiskeringLeft _ _ _).obj (ιD ⋙ R)) n).app L (ιC.map a ≫ h)) =
      (colimit.ι (((seqOf (F.obj K)) ⋙ ιC).rightOp ⋙ coyoneda) n).app (R.obj (ιD.obj L))
        (ιC.map a ≫ h) :=
    ConcreteCategory.congr_hom (congr_app
      (ι_colimitCompWhiskeringLeftIsoCompColimit_hom ((seqOf (F.obj K)).rightOp ⋙ ιC.op ⋙ coyoneda)
        (ιD ⋙ R) n) L) _
  have s5 := (ofPointsIso_inv_app_ι_app ((seqOf (F.obj K)) ⋙ ιC) n (ιC.map a ≫ h)).trans
    (seqHomColimIso_inv_app_seqStage_comp ((seqOf (F.obj K)) ⋙ ιC) (ιC.map a) h)
  have s6 := NatTrans.naturality_apply (mapOfIso ιC (seqOf (F.obj K))).hom.unop.hom h
    ((Pro.seqHomColimIso ((seqOf (F.obj K)) ⋙ ιC)).inv.app (ιC.obj K₀)
      (Pro.seqStage ((seqOf (F.obj K)) ⋙ ιC) (ιC.map a)))
  have s6' : (mapOfIso ιC (seqOf (F.obj K))).hom.unop.hom.app (ιC.obj K₀)
      ((Pro.seqHomColimIso ((seqOf (F.obj K)) ⋙ ιC)).inv.app (ιC.obj K₀)
        (Pro.seqStage ((seqOf (F.obj K)) ⋙ ιC) (ιC.map a))) =
      (ιC.lanUnit.app (of (seqOf (F.obj K))).points).app K₀
        ((Pro.seqHomColimIso (seqOf (F.obj K))).inv.app K₀ (Pro.seqStage (seqOf (F.obj K)) a)) := by
    rw [← mapOfIso_inv_app_lanUnit_app]
    exact iso_unop_hom_app_inv_app_hom_app (mapOfIso ιC (seqOf (F.obj K))).symm _ _
  have s7 := NatTrans.naturality_apply ((map ιC).map (ofSeqOfIso (F.obj K)).inv).unop.hom h
    ((ιC.lanUnit.app (of (seqOf (F.obj K))).points).app K₀
      ((Pro.seqHomColimIso (seqOf (F.obj K))).inv.app K₀ (Pro.seqStage (seqOf (F.obj K)) a)))
  have s7' : ((map ιC).map (ofSeqOfIso (F.obj K)).inv).unop.hom.app (ιC.obj K₀)
      ((ιC.lanUnit.app (of (seqOf (F.obj K))).points).app K₀
        ((Pro.seqHomColimIso (seqOf (F.obj K))).inv.app K₀ (Pro.seqStage (seqOf (F.obj K)) a))) =
      (ιC.lanUnit.app (F.obj K).points).app K₀ (homConstEquiv (F.obj K) K₀ φ) := by
    refine (lan_map_app_lanUnit_app ιC (ofSeqOfIso (F.obj K)).inv.unop.hom K₀ _).trans ?_
    congr 1
    have e1 : (Pro.seqHomColimIso (seqOf (F.obj K))).inv.app K₀ (Pro.seqStage (seqOf (F.obj K)) a) =
        (ofSeqOfIso (F.obj K)).hom.unop.hom.app K₀ (homConstEquiv (F.obj K) K₀ φ) := by
      rw [ha]
      exact Iso.hom_inv_id_app_apply _ _ _
    rw [e1]
    exact iso_unop_hom_app_inv_app_hom_app (ofSeqOfIso (F.obj K)) _ _
  have s8 : (pointsIsoHomConst ((map ιC).obj (F.obj K))).hom.app (R.obj (ιD.obj L))
      (((map ιC).obj (F.obj K)).points.map h
        ((ιC.lanUnit.app (F.obj K).points).app K₀ (homConstEquiv (F.obj K) K₀ φ))) =
      mapConst ιC φ ≫ const.map h := by
    apply (homConstEquiv _ _).injective
    refine (Equiv.apply_symm_apply _ _).trans ?_
    rw [homConstEquiv_comp_const_map, homConstEquiv_mapConst]
  rw [key, s1]
  change (Ψ.hom.app (op K)).app (R.obj (ιD.obj L))
    ((pointsIsoHomConst ((map ιC).obj (F.obj K))).hom.app (R.obj (ιD.obj L))
    (((map ιC).map (ofSeqOfIso (F.obj K)).inv).unop.hom.app (R.obj (ιD.obj L))
      ((mapOfIso ιC (seqOf (F.obj K))).hom.unop.hom.app (R.obj (ιD.obj L))
        ((ofPointsIso ((seqOf (F.obj K)) ⋙ ιC)).inv.app (R.obj (ιD.obj L))
        ((colimitCompWhiskeringLeftIsoCompColimit ((seqOf (F.obj K)).rightOp ⋙ ιC.op ⋙ coyoneda)
          (ιD ⋙ R)).hom.app L ((HasColimit.isoOfNatIso
            (Functor.isoWhiskerLeft (seqOf (F.obj K)).rightOp Φ)).hom.app L
              ((colimit.ι ((seqOf (F.obj K)).rightOp ⋙ pointsFunctor G) n).app L
                (((pointsFunctor G).map a.op).app L x)))))))) = _
  rw [s2]
  show (Ψ.hom.app (op K)).app (R.obj (ιD.obj L))
    ((pointsIsoHomConst ((map ιC).obj (F.obj K))).hom.app (R.obj (ιD.obj L))
    (((map ιC).map (ofSeqOfIso (F.obj K)).inv).unop.hom.app (R.obj (ιD.obj L))
      ((mapOfIso ιC (seqOf (F.obj K))).hom.unop.hom.app (R.obj (ιD.obj L))
        ((ofPointsIso ((seqOf (F.obj K)) ⋙ ιC)).inv.app (R.obj (ιD.obj L))
        ((colimitCompWhiskeringLeftIsoCompColimit ((seqOf (F.obj K)).rightOp ⋙ ιC.op ⋙ coyoneda)
          (ιD ⋙ R)).hom.app L ((colimit.ι (((seqOf (F.obj K)).rightOp ⋙ ιC.op ⋙ coyoneda) ⋙
            (Functor.whiskeringLeft _ _ _).obj (ιD ⋙ R)) n).app L
            ((Φ.hom.app (op ((seqOf (F.obj K)).obj (op n)))).app L
              (((pointsFunctor G).map a.op).app L x)))))))) = _
  rw [s3, s4]
  show (Ψ.hom.app (op K)).app (R.obj (ιD.obj L))
    ((pointsIsoHomConst ((map ιC).obj (F.obj K))).hom.app (R.obj (ιD.obj L))
    (((map ιC).map (ofSeqOfIso (F.obj K)).inv).unop.hom.app (R.obj (ιD.obj L))
      ((mapOfIso ιC (seqOf (F.obj K))).hom.unop.hom.app (R.obj (ιD.obj L))
        ((ofPointsIso ((seqOf (F.obj K)) ⋙ ιC)).inv.app (R.obj (ιD.obj L))
        ((colimit.ι (((seqOf (F.obj K)) ⋙ ιC).rightOp ⋙ coyoneda) n).app (R.obj (ιD.obj L))
          (ιC.map a ≫ h)))))) = _
  rw [s5, s6, s6', s7, s7', s8]

end CategoryTheory.ProSeq

namespace AlgebraicGeometry

open Stacks.Duality Stacks.Duality.TwistedInverseImageDuality Stacks.Duality.UpperShriekDuality

attribute [local instance 10000] CategoryTheory.Functor.hasLeftKanExtension_of_type
  CategoryTheory.Functor.hasPointwiseLeftKanExtension_of_type
attribute [local instance] Stacks.Cohomology.ProjectionFormulaPerfect.hasSheafifyOpens
  Stacks.Cohomology.ProjectionFormulaPerfect.wEqualsLocallyBijectiveOpens
attribute [local instance] Stacks.AssociatedSheaf.abelianModulesRingSheaf

variable {S : Scheme.{u}} [IsNoetherian S] {X Y Z : FTS S}

/-- The isomorphism `lowerShriekCompPointsUpperShriekIso f g cf cg K` is, by definition, the
isomorphism `CategoryTheory.ProSeq.bindObjPointsIsoOfHomIso` built from `lowerShriek f cf`,
`lowerShriek g cg`, `lowerShriekPointsFunctorIso g cg` and `lowerShriekHomIso f cf`. -/
theorem lowerShriekCompPointsUpperShriekIso_eq_bindObjPointsIsoOfHomIso (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : CompactificationOf (Over.mk f.left)) (cg : CompactificationOf (Over.mk g.left))
    (K : BoundedCoherentDerived X.left) :
    lowerShriekCompPointsUpperShriekIso f g cf cg K =
      ProSeq.bindObjPointsIsoOfHomIso (lowerShriek f cf) (lowerShriek g cg)
        (boundedCoherentToPlusCoh Y.left) (boundedCoherentToPlusCoh Z.left)
        (upperShriekStdPlusCoh g cg) (lowerShriekPointsFunctorIso g cg) (upperShriekStd f cf)
        (boundedCoherentDerived X.left).ι (lowerShriekHomIso f cf) K :=
  rfl

/-- **`Rg_!` applied to a morphism into a constant pro-object, on points of `Rg_! Rf_! K`.** For
`φ : Rf_! K ⟶ K₀` and a point `x` of `Rg_! K₀` at `L`, that is a morphism `ψ_x : K₀ ⟶ g^! L`
([Stacks, Tag 0G51] for `g`), the image of `x` under `Rg_!` applied to `φ`
(`CategoryTheory.ProSeq.bindConstMap`) is, under the identification
`Hom(Rg_! Rf_! K, L) = Hom_X(K, f^! g^! L)` of the proof of [Stacks, Tag 0G55], the morphism
attached by [Stacks, Tag 0G51] for `f` to `Rf_! K ⟶ K₀ ⟶ g^! L`. -/
theorem lowerShriekCompPointsUpperShriekIso_hom_app_bindConstMap (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : CompactificationOf (Over.mk f.left)) (cg : CompactificationOf (Over.mk g.left))
    (K : BoundedCoherentDerived X.left) {K₀ : BoundedCoherentDerived Y.left}
    (φ : (lowerShriek f cf).obj K ⟶ ProSeq.const.obj K₀) (L : BoundedCoherentDerived Z.left)
    (x : ((lowerShriek g cg).obj K₀).points.obj L) :
    (lowerShriekCompPointsUpperShriekIso f g cf cg K).hom.app L
        ((ProSeq.bindConstMap (lowerShriek g cg) φ).unop.hom.app L x) =
      lowerShriekHomEquiv f cf K
        ((upperShriekStdPlusCoh g cg).obj ((boundedCoherentToPlusCoh Z.left).obj L))
        (ProSeq.mapConst (boundedCoherentToPlusCoh Y.left) φ ≫
          ProSeq.const.map (((lowerShriekPointsFunctorIso g cg).hom.app (op K₀)).app L x)) :=
  ProSeq.bindObjPointsIsoOfHomIso_hom_app_bindConstLeg (lowerShriek f cf) (lowerShriek g cg)
    (boundedCoherentToPlusCoh Y.left) (boundedCoherentToPlusCoh Z.left)
    (upperShriekStdPlusCoh g cg) (lowerShriekPointsFunctorIso g cg) (upperShriekStd f cf)
    (boundedCoherentDerived X.left).ι (lowerShriekHomIso f cf) φ (ProSeq.constHomRep φ).2
    (ProSeq.seqStage_constHomRep φ) L x

end AlgebraicGeometry

end
