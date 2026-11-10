module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineSite.Colimit.BinaryCoproduct
public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineSite.Colimit.Coequalizer

/-!
# Nonempty finite colimits in `CRIS(C/A)` and `Cris(C/A)`

From binary coproducts and coequalizers, `CRIS(C/A)` has all nonempty finite colimits.  The
quotient functor is a left adjoint, its right adjoint equipping a `C`-algebra with the zero
ideal, hence preserves them; and the full subcategory `Cris(C/A)` inherits them, its inclusion
into `CRIS(C/A)` preserving them.

## Main results

* `Crystalline.hasNonemptyFiniteColimits_dividedPowerThickening` — `CRIS(C/A)` has all
  nonempty finite colimits.
* `Crystalline.preservesColimitsOfShape_quotientFunctor` — the quotient functor preserves
  them.
* `Crystalline.DividedPowerThickening.instHasNonemptyFiniteColimits` and
  `Crystalline.preservesColimitsOfShape_crystallineThickeningInclusion` — `Cris(C/A)` has
  them too, and the inclusion into `CRIS(C/A)` preserves them.

## References

* [Stacks Project, Tag 07HN](https://stacks.math.columbia.edu/tag/07HN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v w

namespace Crystalline

/-- **Stacks Project, Tag 07HN.** In an affine crystalline situation, the
category `CRIS(C/A)` has all nonempty finite colimits. -/
@[stacks 07HN "cris_colimits"]
public instance hasNonemptyFiniteColimits_dividedPowerThickening
    (S : AffineCrystallineSituation.{u, v}) :
    HasNonemptyFiniteColimits
      (DividedPowerThickening.{u, v, w} S) := by
  let C := DividedPowerThickening.{u, v, w} S
  let : ∀ {X Y : C}, HasColimit (pair X Y) := fun {X Y} =>
    let ⟨t, ht, _⟩ := binaryCoproductWithTensorProductQuotient X Y
    ⟨⟨t, ht⟩⟩
  let : HasBinaryCoproducts C := hasBinaryCoproducts_of_hasColimit_pair (C := C)
  let : ∀ {X Y : C} (f g : X ⟶ Y), HasColimit (parallelPair f g) := fun {X Y} f g =>
    let ⟨Q, q, hq, hcolim, _⟩ := exists_coequalizer_with_quotient f g
    ⟨⟨Cofork.ofπ q hq, hcolim.some⟩⟩
  let : HasCoequalizers C := hasCoequalizers_of_hasColimit_parallelPair (C := C)
  exact hasNonemptyFiniteColimits_of_hasBinaryCoproducts_and_hasCoequalizers C

section QuotientPreserves

private noncomputable def trivialThickening
    (S : AffineCrystallineSituation.{u, v})
    (R : CommAlgCat.{w, v} S.C) : DividedPowerThickening.{u, v, w} S := by
  let f : S.A →+* R := (algebraMap S.C R).comp (algebraMap S.A S.C)
  have hf : S.A.ideal.map f ≤ (⊥ : Ideal R) := by
    rw [show f = (algebraMap S.C R).comp (algebraMap S.A S.C) from rfl,
      ← Ideal.map_map, S.ideal_map_eq_bot]
    simp
  refine { ring := { carrier := R, ideal := ⊥, dividedPowers := dividedPowersBot R }
           fromBase := dpMorphismToBot S.A.dividedPowers f
             fun z hz => Ideal.mem_bot.mp (hf (Ideal.mem_map_of_mem _ hz))
           prime_nilpotent := ?_
           toQuotient := (Ideal.Quotient.mk ⊥).comp (algebraMap S.C R)
           commutes := ?_ }
  · simpa only [map_natCast] using S.prime_nilpotent.map (algebraMap S.C R)
  · rfl

private noncomputable def trivialThickeningFunctor
    (S : AffineCrystallineSituation.{u, v}) :
    CommAlgCat.{w, v} S.C ⥤ DividedPowerThickening.{u, v, w} S where
  obj := trivialThickening S
  map {R T} f := by
    letI : Algebra S.C (trivialThickening S R).ring := R.algebra
    letI : Algebra S.C (trivialThickening S T).ring := T.algebra
    let f' : (trivialThickening S R).ring →+* (trivialThickening S T).ring := f.hom.toRingHom
    let m : (trivialThickening S R).ring ⟶ (trivialThickening S T).ring :=
      dpMorphismToBot (trivialThickening S R).ring.dividedPowers f'
        fun z hz => by rw [Ideal.mem_bot.mp hz]; exact map_zero f'
    refine { hom := m
             fromBase_comp := ?_
             toQuotient_comp := ?_ }
    · apply DividedPowers.DPMorphism.ext; funext x
      change f' (algebraMap S.C R (algebraMap S.A S.C x)) =
        algebraMap S.C T (algebraMap S.A S.C x)
      exact f.hom.commutes _
    · apply RingHom.ext; intro x
      let X₀ := trivialThickening S R
      let Y₀ := trivialThickening S T
      change DividedPowerRing.quotientRingHom m
          (Ideal.Quotient.mk X₀.ring.ideal (algebraMap S.C X₀.ring x)) =
        Ideal.Quotient.mk Y₀.ring.ideal (algebraMap S.C Y₀.ring x)
      rw [DividedPowerRing.quotientRingHom_mk]
      exact congrArg (Ideal.Quotient.mk Y₀.ring.ideal) (f.hom.commutes x)
  map_id R := by apply DividedPowerThickening.Hom.ext; apply DividedPowers.DPMorphism.ext; rfl
  map_comp f g := by apply DividedPowerThickening.Hom.ext; apply DividedPowers.DPMorphism.ext; rfl

private noncomputable def quotientToTrivial
    (S : AffineCrystallineSituation.{u, v})
    (X : DividedPowerThickening.{u, v, w} S)
    (R : CommAlgCat.{w, v} S.C)
    (g : (quotientFunctor S).obj X ⟶ R) :
    X ⟶ (trivialThickeningFunctor S).obj R := by
  letI : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
  let T := (trivialThickeningFunctor S).obj R
  letI : Algebra S.C T.ring := R.algebra
  let g' : (X.ring ⧸ X.ring.ideal) →ₐ[S.C] T.ring := g.hom
  let f : X.ring →+* T.ring :=
    g'.toRingHom.comp (Ideal.Quotient.mk X.ring.ideal)
  have hf : ∀ x ∈ X.ring.ideal, f x = 0 := by
    intro x hx
    dsimp [f]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact map_zero g'.toRingHom
  let fm : X.ring ⟶ T.ring := dpMorphismToBot X.ring.dividedPowers f hf
  exact {
      hom := fm
      fromBase_comp := by
        apply DividedPowers.DPMorphism.ext; funext a
        have hc := DFunLike.congr_fun X.commutes a
        change f (X.fromBase.toRingHom a) = T.fromBase.toRingHom a
        dsimp [f]
        change Ideal.Quotient.mk X.ring.ideal (X.fromBase.toRingHom a) =
          X.toQuotient (algebraMap S.A S.C a) at hc
        calc
          _ = g'.toRingHom (X.toQuotient (algebraMap S.A S.C a)) :=
            congrArg g'.toRingHom hc
          _ = algebraMap S.C T.ring (algebraMap S.A S.C a) :=
            g'.commutes _
      toQuotient_comp := by
        apply RingHom.ext; intro c
        have hq : DividedPowerRing.quotientRingHom (A := X.ring) (B := T.ring) fm =
            (Ideal.Quotient.mk T.ring.ideal).comp g'.toRingHom := by
          apply Ideal.Quotient.ringHom_ext; ext x
          change Ideal.Quotient.mk T.ring.ideal (f x) =
            Ideal.Quotient.mk T.ring.ideal
              (g'.toRingHom (Ideal.Quotient.mk X.ring.ideal x))
          rfl
        rw [hq]
        calc
          _ = Ideal.Quotient.mk T.ring.ideal
                (g'.toRingHom (X.toQuotient c)) := rfl
          _ = Ideal.Quotient.mk T.ring.ideal (algebraMap S.C T.ring c) :=
              congrArg (Ideal.Quotient.mk T.ring.ideal)
                (g'.commutes c)
          _ = _ := rfl
    }

/-- A morphism into a trivial thickening kills the divided power ideal of the source. -/
private theorem hom_eq_zero_of_mem_ideal
    {S : AffineCrystallineSituation.{u, v}} {X : DividedPowerThickening.{u, v, w} S}
    {R : CommAlgCat.{w, v} S.C} (h : X ⟶ (trivialThickeningFunctor S).obj R) :
    ∀ x ∈ X.ring.ideal, h.hom.toRingHom x = 0 := fun _ hx =>
  Ideal.mem_bot.mp (Ideal.map_le_iff_le_comap.mp h.hom.ideal_comp hx)

private noncomputable def trivialToQuotient
    (S : AffineCrystallineSituation.{u, v})
    (X : DividedPowerThickening.{u, v, w} S)
    (R : CommAlgCat.{w, v} S.C)
    (h : X ⟶ (trivialThickeningFunctor S).obj R) :
    (quotientFunctor S).obj X ⟶ R := by
  letI : Algebra S.C (X.ring ⧸ X.ring.ideal) := X.toQuotient.toAlgebra
  let T := (trivialThickeningFunctor S).obj R
  letI : Algebra S.C T.ring := R.algebra
  let f : X.ring ⧸ X.ring.ideal →+* T.ring := Ideal.Quotient.lift X.ring.ideal
    h.hom.toRingHom (hom_eq_zero_of_mem_ideal h)
  have hq : (Ideal.Quotient.mk T.ring.ideal).comp f =
      DividedPowerRing.quotientRingHom h.hom := by
    apply Ideal.Quotient.ringHom_ext; ext x
    change Ideal.Quotient.mk T.ring.ideal (f (Ideal.Quotient.mk X.ring.ideal x)) =
      DividedPowerRing.quotientRingHom h.hom (Ideal.Quotient.mk X.ring.ideal x)
    rw [Ideal.Quotient.lift_mk, DividedPowerRing.quotientRingHom_mk]; rfl
  refine CommAlgCat.ofHom {
    toRingHom := f
    commutes' := ?_ }
  intro c
  change f (X.toQuotient c) = algebraMap S.C R c
  have hc := DFunLike.congr_fun hq (X.toQuotient c)
  have hh := DFunLike.congr_fun h.toQuotient_comp c
  have hval : Ideal.Quotient.mk T.ring.ideal (f (X.toQuotient c)) =
      Ideal.Quotient.mk T.ring.ideal (algebraMap S.C T.ring c) := by
    calc
      _ = DividedPowerRing.quotientRingHom h.hom (X.toQuotient c) := hc
      _ = T.toQuotient c := hh
      _ = _ := rfl
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem] at hval
  change _ ∈ (⊥ : Ideal T.ring) at hval
  exact sub_eq_zero.mp (Ideal.mem_bot.mp hval)

private noncomputable def quotientTrivialHomEquiv
    (S : AffineCrystallineSituation.{u, v})
    (X : DividedPowerThickening.{u, v, w} S)
    (R : CommAlgCat.{w, v} S.C) :
    ((quotientFunctor S).obj X ⟶ R) ≃
      (X ⟶ (trivialThickeningFunctor S).obj R) where
  toFun := quotientToTrivial S X R
  invFun := trivialToQuotient S X R
  left_inv := by
    intro g
    apply CommAlgCat.hom_ext; apply AlgHom.ext; intro x
    induction x using Quotient.inductionOn with
    | _ y =>
      change (Ideal.Quotient.lift X.ring.ideal
          ((quotientToTrivial S X R g).hom.toRingHom) ?_) (Ideal.Quotient.mk _ y) =
        g.hom (Ideal.Quotient.mk _ y)
      rw [Ideal.Quotient.lift_mk]; rfl
  right_inv := by
    intro h
    apply DividedPowerThickening.Hom.ext; apply DividedPowers.DPMorphism.ext; funext x
    change Ideal.Quotient.lift X.ring.ideal h.hom.toRingHom (hom_eq_zero_of_mem_ideal h)
        (Ideal.Quotient.mk X.ring.ideal x) = h.hom x
    rw [Ideal.Quotient.lift_mk]; rfl

private noncomputable def quotientFunctorAdjunction
    (S : AffineCrystallineSituation.{u, v}) :
    quotientFunctor.{u, v, w} S ⊣ trivialThickeningFunctor S :=
  Adjunction.mkOfHomEquiv {
    homEquiv := quotientTrivialHomEquiv S
    homEquiv_naturality_left_symm := by
      intro X' X Y f g
      apply CommAlgCat.hom_ext; apply AlgHom.ext; intro x
      induction x using Quotient.inductionOn with
      | _ a =>
        change Ideal.Quotient.lift X'.ring.ideal (f ≫ g).hom.toRingHom
            (hom_eq_zero_of_mem_ideal (f ≫ g)) (Ideal.Quotient.mk X'.ring.ideal a) =
          Ideal.Quotient.lift X.ring.ideal g.hom.toRingHom (hom_eq_zero_of_mem_ideal g)
            (DividedPowerRing.quotientRingHom f.hom
              (Ideal.Quotient.mk X'.ring.ideal a))
        rw [Ideal.Quotient.lift_mk, DividedPowerRing.quotientRingHom_mk,
          Ideal.Quotient.lift_mk]; rfl
    homEquiv_naturality_right := by
      intro X Y Y' f g
      apply DividedPowerThickening.Hom.ext; apply DividedPowers.DPMorphism.ext; funext x
      change (quotientToTrivial S X Y' (f ≫ g)).hom.toRingHom x =
        ((quotientToTrivial S X Y f).hom ≫
          ((trivialThickeningFunctor S).map g).hom).toRingHom x
      dsimp [quotientToTrivial, trivialThickeningFunctor, dpMorphismToBot]
      rfl
  }

/-- **Stacks Project, Tag 07HN.** The quotient functor from `CRIS(C/A)` to
commutative `C`-algebras preserves all nonempty finite colimits. -/
@[stacks 07HN "quotient_preserves_colimits"]
public instance preservesColimitsOfShape_quotientFunctor
    (S : AffineCrystallineSituation.{u, v})
    (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J] :
    PreservesColimitsOfShape J (quotientFunctor.{u, v, w} S) := by
  let _ : (quotientFunctor.{u, v, w} S).IsLeftAdjoint :=
    ⟨trivialThickeningFunctor S, ⟨quotientFunctorAdjunction S⟩⟩
  exact Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint _

end QuotientPreserves

section LittleCris
private abbrev crystallineProperty (S : AffineCrystallineSituation.{u, v}) :
    ObjectProperty (DividedPowerThickening.{u, v, w} S) :=
  DividedPowerThickening.IsCrystalline (S := S)

private abbrev crystallineInclusion (S : AffineCrystallineSituation.{u, v}) :
    CrystallineThickening.{u, v, w} S ⥤
      DividedPowerThickening.{u, v, w} S := (crystallineProperty S).ι

private def isInitial_of_isColimit_of_initial
    {J : Type} [Category J] {C : Type*} [Category C] {F : J ⥤ C}
    {c : Cocone F} (hc : IsColimit c) (hF : ∀ j, IsInitial (F.obj j)) :
    IsInitial c.pt :=
  IsInitial.ofUniqueHom
    (fun Y => hc.desc ⟨Y, ⟨fun j => (hF j).to Y, by intros; apply (hF _).hom_ext⟩⟩)
    fun Y f => hc.hom_ext (fun j => (hF j).hom_ext _ _)

private noncomputable def quotient_initial_of_crystalline
    (S : AffineCrystallineSituation.{u, v})
    (X : CrystallineThickening.{u, v, w} S) :
    IsInitial ((quotientFunctor.{u, v, w} S).obj X.obj) := by
  letI : Algebra S.C (X.obj.ring ⧸ X.obj.ring.ideal) := X.obj.toQuotient.toAlgebra
  let e : S.C ≃ₐ[S.C] (X.obj.ring ⧸ X.obj.ring.ideal) :=
    AlgEquiv.ofBijective (Algebra.ofId S.C _)
      (show Function.Bijective X.obj.toQuotient from X.property)
  refine IsInitial.ofUniqueHom
      (fun Y => CommAlgCat.ofHom ((Algebra.ofId S.C Y).comp e.symm.toAlgHom)) ?_
  intro Y f
  change CommAlgCat.of S.C (X.obj.ring ⧸ X.obj.ring.ideal) ⟶ Y at f
  have hcomp : f.hom.comp e.toAlgHom = Algebra.ofId S.C Y := by ext
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  obtain ⟨x, rfl⟩ := e.surjective x
  change (f.hom.comp e.toAlgHom) x =
    ((Algebra.ofId S.C Y).comp e.symm.toAlgHom) (e x)
  rw [hcomp]
  simp [AlgHom.comp_apply]

private theorem quotient_colimit_crystalline
    (S : AffineCrystallineSituation.{u, v})
    {J : Type} [SmallCategory J] [FinCategory J] [Nonempty J]
    (F : J ⥤ CrystallineThickening.{u, v, w} S)
    [HasColimit (F ⋙ crystallineInclusion S)] :
    crystallineProperty S (colimit (F ⋙ crystallineInclusion S)) := by
  let Q := quotientFunctor.{u, v, w} S
  have hcolim : IsColimit (Q.mapCocone
      (colimit.cocone (F ⋙ crystallineInclusion S))) :=
    isColimitOfPreserves Q (colimit.isColimit _)
  have hinit : IsInitial (Q.obj
      (colimit (F ⋙ crystallineInclusion S))) :=
    isInitial_of_isColimit_of_initial hcolim (fun j => quotient_initial_of_crystalline S (F.obj j))
  obtain ⟨j₀⟩ := ‹Nonempty J›
  let X := F.obj j₀
  let Y := colimit (F ⋙ crystallineInclusion S)
  let f : X.obj ⟶ Y := colimit.ι (F ⋙ crystallineInclusion S) j₀
  have hsource : IsInitial (Q.obj X.obj) := quotient_initial_of_crystalline S X
  have hQiso : IsIso (Q.map f) := by
    let i := hsource.uniqueUpToIso hinit
    have heq : Q.map f = i.hom := hsource.hom_ext _ _
    rw [heq]
    infer_instance
  have hq : Function.Bijective (DividedPowerRing.quotientRingHom f.hom) := by
    convert ConcreteCategory.bijective_of_isIso (Q.map f) using 1 <;> rfl
  change Function.Bijective Y.toQuotient
  have hcomp :
      (DividedPowerRing.quotientRingHom f.hom).comp X.obj.toQuotient =
        Y.toQuotient := f.toQuotient_comp
  rw [← hcomp]
  exact hq.comp X.property
namespace DividedPowerThickening
/-- **Stacks Project, Tag 07HN.** In an affine crystalline situation, the little
crystalline category `Cris(C/A)` has all finite nonempty colimits. -/
@[stacks 07HN "little_cris_colimits"]
public instance instHasNonemptyFiniteColimits
    (S : AffineCrystallineSituation.{u, v}) :
    HasNonemptyFiniteColimits
      (CrystallineThickening.{u, v, w} S) := by
  refine ⟨fun J _ _ _ => ⟨fun F => ?_⟩⟩
  let P := DividedPowerThickening.IsCrystalline (S := S)
  let _ : HasColimitsOfShape J (DividedPowerThickening S) :=
    HasNonemptyFiniteColimits.out J
  let _ : HasColimit (F ⋙ P.ι) := inferInstance
  have hP : P (colimit (F ⋙ P.ι)) := quotient_colimit_crystalline S F
  have hcreate : CreatesColimit F P.ι :=
    Limits.createsColimitFullSubcategoryInclusion F hP
  exact hasColimit_of_created F P.ι

end DividedPowerThickening
/-- **Stacks Project, Tag 07HN.** The inclusion `Cris(C/A) ⥤ CRIS(C/A)`
preserves finite nonempty colimits. -/
@[stacks 07HN "little_cris_inclusion"]
public instance preservesColimitsOfShape_crystallineThickeningInclusion
    (S : AffineCrystallineSituation.{u, v})
    (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J] :
    PreservesColimitsOfShape J
      ((DividedPowerThickening.IsCrystalline (S := S) :
      ObjectProperty (DividedPowerThickening.{u, v, w} S)).ι) := by
  refine ⟨?_⟩
  let P := DividedPowerThickening.IsCrystalline (S := S)
  let ι := P.ι
  let _ : HasColimitsOfShape J (DividedPowerThickening.{u, v, w} S) :=
    HasNonemptyFiniteColimits.out J
  intro F
  let _ : HasColimit (F ⋙ ι) := inferInstance
  have hP : P (colimit (F ⋙ ι)) := quotient_colimit_crystalline S F
  let _ : CreatesColimit F ι := Limits.createsColimitFullSubcategoryInclusion F hP
  infer_instance

end LittleCris

end Crystalline
