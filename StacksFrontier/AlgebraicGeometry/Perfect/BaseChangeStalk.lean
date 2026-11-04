module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.Flat.Localization
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk

/-!
# Local rings in a base-change square

At a point of a fibre product of schemes, the local ring is a localization of the tensor
product of the local rings at the images of that point on the other three corners.

## Main results

* `AlgebraicGeometry.BaseChangeStalk.pullback_stalk_isLocalization`: the two projections out
  of a scheme fibre product induce a ring map from the tensor product of local rings
  `O_{X,x} ⊗_{O_{Y,y}} O_{Y',y'}` to `O_{X ×_Y Y', x'}` which restricts on the two factors
  to the two stalk maps, and which exhibits its target as a localization of its source.

## Implementation notes

The equality between the two images of the chosen point in the base is used to transport the
second base-ring action.  The asserted map out of the tensor product is characterized by its
restrictions to both factors; these equations simultaneously express the commutativity of the
square of local rings and make the localization algebra structure canonical.

The localization is produced by identifying the local ring of the fibre product with a stalk
of an affine scheme `Spec T`, where `T` is the tensor product, and then reading off
`StructureSheaf.IsLocalization.to_stalk`.  The comparison morphism from the fibre product of
the three spectra is an isomorphism on stalks because it is a flat pre-immersion.

## References

* [Stacks Project, *Duality for Schemes*, Lemma "local rings in the base change square"]
-/

open CategoryTheory Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- The forward map of the stalk congruence along an equality of points is the corresponding
`eqToHom`. -/
public lemma stalkCongr_of_eq {X : TopCat} (F : X.Presheaf CommRingCat)
    {x y : X} (h : x = y) :
    (F.stalkCongr (.of_eq h)).hom = eqToHom (congrArg F.stalk h) := by
  subst y
  simp [TopCat.Presheaf.stalkCongr]

/-- A pullback square of schemes whose vertical maps become isomorphic after composing with a
monomorphism induces an isomorphism of the two pullbacks. -/
public lemma pullbackMap_of_comp_mono_isIso {A B W Z : Scheme}
    (a : A ⟶ W) (b : B ⟶ W) (i : W ⟶ Z) [Mono i] :
    IsIso (pullback.map a b (a ≫ i) (b ≫ i) (𝟙 A) (𝟙 B) i
      (by simp) (by simp)) := by
  let k : pullback (a ≫ i) (b ≫ i) ⟶ pullback a b :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _)
      ((cancel_mono i).mp (by simpa only [Category.assoc] using
        (pullback.condition : pullback.fst (a ≫ i) (b ≫ i) ≫ (a ≫ i) =
          pullback.snd (a ≫ i) (b ≫ i) ≫ (b ≫ i))))
  refine ⟨⟨k, ?_, ?_⟩⟩ <;> ext <;> simp [k, pullback.map, Category.assoc,
    pullback.lift_fst, pullback.lift_snd]

end AlgebraicGeometry

namespace AlgebraicGeometry.BaseChangeStalk

/-- **The canonical morphism out of the spectrum of a local ring is natural in the pointed
scheme.** For `g : X ⟶ Y`, a point `x` of `X` and a point `z` of `Y` equal to `g x`, the
stalk map of `g` at `x`, transported along that equality, carries `Spec 𝒪_{Y, z} ⟶ Y` to
`Spec 𝒪_{X, x} ⟶ X ⟶ Y`. -/
public lemma specMap_eqToHom_stalkMap_fromSpecStalk {X Y : Scheme} (g : X ⟶ Y) (x : X)
    {z : Y} (h : z = g.base x) :
    Spec.map (eqToHom (congrArg Y.presheaf.stalk h) ≫ g.stalkMap x) ≫
      Y.fromSpecStalk z = X.fromSpecStalk x ≫ g := by
  cases h
  simp

private alias specMap_stalkMap_congr := specMap_eqToHom_stalkMap_fromSpecStalk

/- `stalkMap_isIso_of_flat_preimmersion` stood here, one of four private copies of one
statement. All four are replaced by the public
`AlgebraicGeometry.isIso_stalkMap_of_flat_isPreimmersion`,
`StacksFrontier/AlgebraicGeometry/Pullback/StalkFromSpecStalk.lean:68`, whose proof is the same
and which every one of the four modules already imported. -/

/-- **The comparison map between two pullbacks over a monomorphism is a flat preimmersion**
when the two vertical maps are. The comparison factors as an isomorphism followed by the
pullback of the two vertical maps, and both properties are stable under base change. -/
public lemma flat_isPreimmersion_pullbackMap_of_comp_mono
    {A B W X Y Z : Scheme} (a : A ⟶ W) (b : B ⟶ W)
    (i : W ⟶ Z) [Mono i] (u : A ⟶ X) (v : B ⟶ Y)
    (f : X ⟶ Z) (g : Y ⟶ Z)
    (e₁ : a ≫ i = u ≫ f) (e₂ : b ≫ i = v ≫ g)
    [Flat u] [Flat v] [IsPreimmersion u] [IsPreimmersion v] :
    Flat (pullback.map a b f g u v i e₁ e₂) ∧
      IsPreimmersion (pullback.map a b f g u v i e₁ e₂) := by
  let m₀ : pullback a b ⟶ pullback (a ≫ i) (b ≫ i) :=
    pullback.map a b (a ≫ i) (b ≫ i) (𝟙 A) (𝟙 B) i (by simp) (by simp)
  let m₁ : pullback (a ≫ i) (b ≫ i) ⟶ pullback f g :=
    pullback.map (a ≫ i) (b ≫ i) f g u v (𝟙 Z)
      (by simpa using e₁) (by simpa using e₂)
  have : IsIso m₀ := pullbackMap_of_comp_mono_isIso a b i
  have : Flat m₁ :=
    MorphismProperty.pullbackMap (P := @Flat) (h₁ := inferInstance)
      (h₂ := inferInstance) e₁ e₂
  let : MorphismProperty.IsStableUnderComposition (@IsPreimmersion) :=
    ⟨fun _ _ h₁ h₂ => by
      let := h₁
      let := h₂
      infer_instance⟩
  have : IsPreimmersion m₁ :=
    MorphismProperty.pullbackMap (P := @IsPreimmersion) (h₁ := inferInstance)
      (h₂ := inferInstance) e₁ e₂
  have hw : pullback.map a b f g u v i e₁ e₂ = m₀ ≫ m₁ := by
    ext <;> simp [m₀, m₁, pullback.map, Category.assoc,
      pullback.lift_fst, pullback.lift_snd,
      pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  rw [hw]
  exact ⟨inferInstance, inferInstance⟩

private alias pullbackMap_flat_preimmersion_of_comp_mono := flat_isPreimmersion_pullbackMap_of_comp_mono

/-- The local ring at a point of a scheme-theoretic fibre product is a localization of the
tensor product of the local rings at its two images over the local ring of the base. -/
public theorem pullback_stalk_isLocalization
    {X Y Y' : Scheme} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (x' : (pullback f g).carrier) :
    let pX : pullback f g ⟶ X := pullback.fst f g
    let pY : pullback f g ⟶ Y' := pullback.snd f g
    let h : (pX ≫ f).base x' = (pY ≫ g).base x' :=
      congrArg (fun k : pullback f g ⟶ Y => k.base x') pullback.condition
    let R := Y.presheaf.stalk ((pX ≫ f).base x')
    let A := X.presheaf.stalk (pX.base x')
    let B := Y'.presheaf.stalk (pY.base x')
    let C := (pullback f g).presheaf.stalk x'
    letI : Algebra R A := (f.stalkMap (pX.base x')).hom.toAlgebra
    letI : Algebra R B :=
      ((eqToHom (congrArg Y.presheaf.stalk h)) ≫ g.stalkMap (pY.base x')).hom.toAlgebra
    ∃ φ : TensorProduct R A B →+* C,
      φ.comp Algebra.TensorProduct.includeLeftRingHom = (pX.stalkMap x').hom ∧
      φ.comp Algebra.TensorProduct.includeRight.toRingHom = (pY.stalkMap x').hom ∧
      letI : Algebra (TensorProduct R A B) C := φ.toAlgebra
      ∃ M : Submonoid (TensorProduct R A B), IsLocalization M C := by
        dsimp only
        let : Algebra (Y.presheaf.stalk ((pullback.fst f g ≫ f).base x'))
            (X.presheaf.stalk ((pullback.fst f g).base x')) :=
          (f.stalkMap ((pullback.fst f g).base x')).hom.toAlgebra
        let : Algebra (Y.presheaf.stalk ((pullback.fst f g ≫ f).base x'))
            (Y'.presheaf.stalk ((pullback.snd f g).base x')) :=
          ((eqToHom (congrArg Y.presheaf.stalk
              (congrArg (fun k : pullback f g ⟶ Y => k.base x')
                pullback.condition))) ≫
            g.stalkMap ((pullback.snd f g).base x')).hom.toAlgebra
        let : Algebra _ _ := ((pullback.fst f g ≫ f).stalkMap x').hom.toAlgebra
        let a : X.presheaf.stalk ((pullback.fst f g).base x') →ₐ[
            Y.presheaf.stalk ((pullback.fst f g ≫ f).base x')]
            (pullback f g).presheaf.stalk x' :=
          AlgHom.mk' ((pullback.fst f g).stalkMap x').hom (by
          intro r z
          show ((pullback.fst f g).stalkMap x').hom
              ((f.stalkMap _).hom r * z) =
            (((pullback.fst f g ≫ f).stalkMap x').hom r) *
              ((pullback.fst f g).stalkMap x').hom z
          rw [map_mul]
          congr 1
          exact DFunLike.congr_fun
            (congrArg CommRingCat.Hom.hom
              (Scheme.Hom.stalkMap_comp (pullback.fst f g) f x')) r |>.symm)
        let b : Y'.presheaf.stalk ((pullback.snd f g).base x') →ₐ[
            Y.presheaf.stalk ((pullback.fst f g ≫ f).base x')]
            (pullback f g).presheaf.stalk x' :=
          AlgHom.mk' ((pullback.snd f g).stalkMap x').hom (by
          intro r z
          show ((pullback.snd f g).stalkMap x').hom
              ((((eqToHom _) ≫ g.stalkMap _).hom r) * z) =
            (((pullback.fst f g ≫ f).stalkMap x').hom r) *
              ((pullback.snd f g).stalkMap x').hom z
          rw [map_mul]
          congr 1
          show (((eqToHom _) ≫ g.stalkMap _ ≫
            (pullback.snd f g).stalkMap x').hom r) =
              ((pullback.fst f g ≫ f).stalkMap x').hom r
          have e := (Scheme.Hom.stalkMap_congr_hom
            (pullback.fst f g ≫ f) (pullback.snd f g ≫ g)
              pullback.condition x').symm
          rw [stalkCongr_of_eq Y.presheaf (congrArg (fun k : pullback f g ⟶ Y => k.base x')
            pullback.condition), Scheme.Hom.stalkMap_comp] at e
          exact DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp e) r)
        let φ : TensorProduct _ _ _ →+* _ :=
          (Algebra.TensorProduct.lift a b fun _ _ => .all _ _).toRingHom
        have hleft : φ.comp Algebra.TensorProduct.includeLeftRingHom =
            ((pullback.fst f g).stalkMap x').hom :=
          congrArg AlgHom.toRingHom
            (Algebra.TensorProduct.lift_comp_includeLeft a b fun _ _ => .all _ _)
        have hright : φ.comp Algebra.TensorProduct.includeRight.toRingHom =
            ((pullback.snd f g).stalkMap x').hom :=
          congrArg AlgHom.toRingHom
            (Algebra.TensorProduct.lift_comp_includeRight a b fun _ _ => .all _ _)
        refine ⟨φ, hleft, hright, ?_⟩
        let x := (pullback.fst f g).base x'
        let y := (pullback.snd f g).base x'
        let z := (pullback.fst f g ≫ f).base x'
        let R := Y.presheaf.stalk z
        let A := X.presheaf.stalk x
        let B := Y'.presheaf.stalk y
        let T := TensorProduct R A B
        let α : Spec (.of A) ⟶ Spec (.of R) :=
          Spec.map (CommRingCat.ofHom (algebraMap R A))
        let β : Spec (.of B) ⟶ Spec (.of R) :=
          Spec.map (CommRingCat.ofHom (algebraMap R B))
        let u : Spec (.of A) ⟶ X := X.fromSpecStalk x
        let v : Spec (.of B) ⟶ Y' := Y'.fromSpecStalk y
        let i : Spec (.of R) ⟶ Y := Y.fromSpecStalk z
        have e₁ : α ≫ i = u ≫ f := by
          show Spec.map (f.stalkMap x) ≫ Y.fromSpecStalk (f.base x) =
            X.fromSpecStalk x ≫ f
          exact Scheme.SpecMap_stalkMap_fromSpecStalk f
        have e₂ : β ≫ i = v ≫ g := by
          show Spec.map (eqToHom (congrArg Y.presheaf.stalk
            (congrArg (fun k : pullback f g ⟶ Y => k.base x')
              pullback.condition)) ≫ g.stalkMap y) ≫
              Y.fromSpecStalk z = Y'.fromSpecStalk y ≫ g
          exact specMap_eqToHom_stalkMap_fromSpecStalk g y
            (congrArg (fun k : pullback f g ⟶ Y => k.base x')
              pullback.condition)
        let wQ : pullback α β ⟶ pullback f g :=
          pullback.map α β f g u v i e₁ e₂
        let w : Spec (.of T) ⟶ pullback f g :=
          (pullbackSpecIso R A B).inv ≫ wQ
        have : Flat u := flat_fromSpecStalk X x
        have : Flat v := flat_fromSpecStalk Y' y
        have : IsPreimmersion u := inferInstance
        have : IsPreimmersion v := inferInstance
        have hwQ := flat_isPreimmersion_pullbackMap_of_comp_mono
          α β i u v f g e₁ e₂
        have : Flat wQ := hwQ.1
        have : IsPreimmersion wQ := hwQ.2
        have : Flat w := inferInstance
        have : IsPreimmersion w := inferInstance
        have hwLeft : w ≫ pullback.fst f g =
            Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.includeLeftRingHom : A →+* T)) ≫ u := by
          simp only [w, wQ, Category.assoc, pullback.lift_fst, pullback.map]
          rw [pullbackSpecIso_inv_fst_assoc]
        have hwRight : w ≫ pullback.snd f g =
            Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.includeRight.toRingHom : B →+* T)) ≫ v := by
          simp only [w, wQ, Category.assoc, pullback.lift_snd, pullback.map]
          rw [pullbackSpecIso_inv_snd_assoc]
          rfl
        let φC : CommRingCat.of T ⟶ (pullback f g).presheaf.stalk x' :=
          CommRingCat.ofHom φ
        have heL : CommRingCat.ofHom
            (Algebra.TensorProduct.includeLeftRingHom : A →+* T) ≫ φC =
              (pullback.fst f g).stalkMap x' :=
          CommRingCat.hom_ext hleft
        have heR : CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight.toRingHom : B →+* T) ≫ φC =
              (pullback.snd f g).stalkMap x' :=
          CommRingCat.hom_ext hright
        have hfac : Spec.map φC ≫ w = (pullback f g).fromSpecStalk x' := by
          apply pullback.hom_ext
          · rw [Category.assoc, hwLeft, ← Category.assoc, ← Spec.map_comp, heL]
            exact Scheme.SpecMap_stalkMap_fromSpecStalk (pullback.fst f g)
          · rw [Category.assoc, hwRight, ← Category.assoc, ← Spec.map_comp, heR]
            exact Scheme.SpecMap_stalkMap_fromSpecStalk (pullback.snd f g)
        let C := (pullback f g).presheaf.stalk x'
        let q : Spec (.of T) := Spec.map φC (IsLocalRing.closedPoint C)
        have hq : w q = x' := by
          show (Spec.map φC ≫ w) (IsLocalRing.closedPoint C) = x'
          rw [hfac]
          exact Scheme.fromSpecStalk_closedPoint
        have : IsIso (w.stalkMap q) := isIso_stalkMap_of_flat_isPreimmersion w q
        let ρ : (Spec (.of T)).presheaf.stalk q ⟶ CommRingCat.of C :=
          Scheme.stalkClosedPointTo (Spec.map φC)
        have hρcomp : IsIso (w.stalkMap q ≫ ρ) := by
          have h : IsIso (Scheme.stalkClosedPointTo (Spec.map φC ≫ w)) := by
            rw [hfac, Scheme.stalkClosedPointTo_fromSpecStalk]
            infer_instance
          show IsIso (w.stalkMap ((Spec.map φC) (IsLocalRing.closedPoint C)) ≫
            Scheme.stalkClosedPointTo (Spec.map φC))
          rw [← Scheme.stalkClosedPointTo_comp]
          exact h
        have : IsIso ρ := (isIso_comp_left_iff _ _).mp hρcomp
        let : Algebra T ((Spec (.of T)).presheaf.stalk q) :=
          StructureSheaf.stalkAlgebra T q
        have hmap : CommRingCat.ofHom
            (algebraMap T ((Spec (.of T)).presheaf.stalk q)) ≫ ρ = φC := by
          show StructureSheaf.toStalk T q ≫ ρ = φC
          rw [show StructureSheaf.toStalk T q =
            (Scheme.ΓSpecIso (.of T)).inv ≫
              (Spec (.of T)).presheaf.germ ⊤ q trivial from rfl]
          dsimp only [ρ, q]
          calc
            _ = (Scheme.ΓSpecIso (CommRingCat.of T)).inv ≫
                ((Spec (CommRingCat.of T)).presheaf.germ ⊤ q trivial ≫ ρ) :=
              Category.assoc _ _ _
            _ = (Scheme.ΓSpecIso (CommRingCat.of T)).inv ≫
                ((Scheme.ΓSpecIso (CommRingCat.of T)).hom ≫ φC) := by
              rw [Scheme.germ_stalkClosedPointTo_Spec]
            _ = φC := by simp
        let e : ((Spec (.of T)).presheaf.stalk q : Type _) ≃+* C :=
          (asIso ρ).commRingCatIsoToRingEquiv
        have he (r : T) : e (algebraMap T ((Spec (.of T)).presheaf.stalk q) r) =
            φ r :=
          DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp hmap) r
        let : Algebra T C := φ.toAlgebra
        let ae : ((Spec (.of T)).presheaf.stalk q : Type _) ≃ₐ[T] C :=
          AlgEquiv.ofRingEquiv he
        let p : PrimeSpectrum T := q
        have : IsLocalization.AtPrime
            ((Spec (.of T)).presheaf.stalk q) p.asIdeal := by
          show IsLocalization.AtPrime
            ((Spec (.of T)).presheaf.stalk p) p.asIdeal
          exact StructureSheaf.IsLocalization.to_stalk (CommRingCat.of T) p
        exact ⟨p.asIdeal.primeCompl,
          IsLocalization.isLocalization_of_algEquiv p.asIdeal.primeCompl ae⟩

end AlgebraicGeometry.BaseChangeStalk
