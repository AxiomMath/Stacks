module

public import Mathlib.CategoryTheory.Comma.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSmallerBase

/-!
# The Beauville--Laszlo gluing functor for algebraic spaces (Stacks 0F9N)

Given a square of schemes `U' → X'`, `U' → U`, `U → X`, `X' → X` in a big fppf site, base change
sends an algebraic space over `X` to compatible algebraic spaces over `U` and `X'`. In the
Beauville--Laszlo setting `X = Spec R`, `U = Spec R_f`, `X' = Spec R'` and `U' = Spec R'_f`.

## Main definitions

* `BeauvilleLaszlo.Space.baseChange`: base change as a functor between categories of algebraic
  spaces, i.e. restriction along a morphism of the big fppf site.
* `BeauvilleLaszlo.Space.GlueingData`: cartesian triples of algebraic spaces over `U ← U' → X'`.
* `BeauvilleLaszlo.Space.GlueingFunctorSpec`: a gluing functor together with its canonical
  component comparisons.

## Main results

* `BeauvilleLaszlo.Space.beauvilleLaszloGlueingSpaces`: the canonical functor from algebraic
  spaces over `X` to gluing data, with its comparisons to the three base changes.

## Implementation notes

The category of triples is an iterated comma category: its middle object is a space over `U'`,
and its two structure arrows exhibit it as the base change of each outside object. The
construction is stated for any commutative square of schemes; the exactness condition on the
associated rings is only needed by later equivalence results. The specification identifies all
three component functors and both structure arrows with the canonical base changes.

Base change is `CategoryTheory.OverShriek.relocalizeRestrict` on presheaves, cut down to
algebraic spaces by Stacks 03I5 part (1)
(`AlgebraicGeometry.isAlgebraicSpace_relocalizeRestrict`). This is the gluing datum for
algebraic spaces, as opposed to the gluing datum for modules of Stacks 0BNV/0BNW.

## References

* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 0F9N](https://stacks.math.columbia.edu/tag/0F9N)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace BeauvilleLaszlo.Space

/-- Restriction of algebraic spaces along a morphism in the big fppf site. -/
noncomputable def baseChange (B : BigFppfSite.{u})
    (S T : Scheme.{u}) (hS : B.Contains S) (hT : B.Contains T)
    (g : B.obj hS ⟶ B.obj hT) :
    AlgebraicSpaces B T hT ⥤ AlgebraicSpaces B S hS :=
  ObjectProperty.lift (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
    IsAlgebraicSpace B S hS F)
    ((ObjectProperty.ι (fun F : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u =>
      IsAlgebraicSpace B T hT F)) ⋙ OverShriek.relocalizeRestrict g)
    (fun F => isAlgebraicSpace_relocalizeRestrict B S T hS hT g F.1 F.2)

/-- Cartesian triples of algebraic spaces over `U ← U' → X'`. An object has
three components and two arrows from the middle component to the restrictions
of the outer components; both arrows are isomorphisms. -/
abbrev GlueingData (B : BigFppfSite.{u})
    (U' U X' : Scheme.{u}) (hU' : B.Contains U')
    (hU : B.Contains U) (hX' : B.Contains X')
    (gU : B.obj hU' ⟶ B.obj hU)
    (gX' : B.obj hU' ⟶ B.obj hX') :=
  ObjectProperty.FullSubcategory
    (fun Z : Comma
      (Comma.fst (𝟭 (AlgebraicSpaces B U' hU'))
        (baseChange B U' U hU' hU gU))
      (baseChange B U' X' hU' hX' gX') =>
      IsIso Z.left.hom ∧ IsIso Z.hom)

/-- The component of a cartesian gluing triple over `U`. -/
noncomputable abbrev overU (B : BigFppfSite.{u})
    (U' U X' : Scheme.{u}) (hU' : B.Contains U')
    (hU : B.Contains U) (hX' : B.Contains X')
    (gU : B.obj hU' ⟶ B.obj hU)
    (gX' : B.obj hU' ⟶ B.obj hX') :
    GlueingData B U' U X' hU' hU hX' gU gX' ⥤
      AlgebraicSpaces B U hU :=
  ObjectProperty.ι _ ⋙
    Comma.fst _ _ ⋙ Comma.snd _ _

/-- The component of a cartesian gluing triple over `U'`. -/
noncomputable abbrev overU' (B : BigFppfSite.{u})
    (U' U X' : Scheme.{u}) (hU' : B.Contains U')
    (hU : B.Contains U) (hX' : B.Contains X')
    (gU : B.obj hU' ⟶ B.obj hU)
    (gX' : B.obj hU' ⟶ B.obj hX') :
    GlueingData B U' U X' hU' hU hX' gU gX' ⥤
      AlgebraicSpaces B U' hU' :=
  ObjectProperty.ι _ ⋙
    Comma.fst _ _ ⋙ Comma.fst _ _

/-- The component of a cartesian gluing triple over `X'`. -/
noncomputable abbrev overX' (B : BigFppfSite.{u})
    (U' U X' : Scheme.{u}) (hU' : B.Contains U')
    (hU : B.Contains U) (hX' : B.Contains X')
    (gU : B.obj hU' ⟶ B.obj hU)
    (gX' : B.obj hU' ⟶ B.obj hX') :
    GlueingData B U' U X' hU' hU hX' gU gX' ⥤
      AlgebraicSpaces B X' hX' :=
  ObjectProperty.ι _ ⋙ Comma.snd _ _

/-- A gluing functor together with its natural identifications with the three
base changes and compatibility with both canonical arrows from the middle
base change. -/
structure GlueingFunctorSpec
    (B : BigFppfSite.{u})
    (U' U X' X : Scheme.{u}) (hU' : B.Contains U')
    (hU : B.Contains U) (hX' : B.Contains X') (hX : B.Contains X)
    (gU : B.obj hU' ⟶ B.obj hU)
    (gX' : B.obj hU' ⟶ B.obj hX')
    (jU : B.obj hU ⟶ B.obj hX)
    (jX' : B.obj hX' ⟶ B.obj hX)
    (hcomm : gU ≫ jU = gX' ≫ jX') where
  /-- The gluing functor. -/
  functor : AlgebraicSpaces B X hX ⥤
    GlueingData B U' U X' hU' hU hX' gU gX'
  /-- The `U`-component is base change along `U → X`. -/
  overUIso : functor ⋙ overU B U' U X' hU' hU hX' gU gX' ≅
    baseChange B U X hU hX jU
  /-- The middle `U'`-component is base change along `U' → X`. -/
  overU'Iso : functor ⋙ overU' B U' U X' hU' hU hX' gU gX' ≅
    baseChange B U' X hU' hX (gU ≫ jU)
  /-- The `X'`-component is base change along `X' → X`. -/
  overX'Iso : functor ⋙ overX' B U' U X' hU' hU hX' gU gX' ≅
    baseChange B X' X hX' hX jX'
  /-- The arrow to the `U`-restriction is induced by iterated base change. -/
  toU_eq (Y : AlgebraicSpaces B X hX) :
    (functor.obj Y).1.left.hom ≫
      (baseChange B U' U hU' hU gU).map (overUIso.hom.app Y) =
    overU'Iso.hom.app Y ≫ eqToHom (by rfl)
  /-- The arrow to the `X'`-restriction is induced by the commutative square. -/
  toX'_eq (Y : AlgebraicSpaces B X hX) :
    (functor.obj Y).1.hom ≫
      (baseChange B U' X' hU' hX' gX').map (overX'Iso.hom.app Y) =
    overU'Iso.hom.app Y ≫ eqToHom (by rw [hcomm]; rfl)

/-- Iterated base change is canonically identified with base change along the composite. -/
noncomputable def baseChangeIterToDirectIso
    (B : BigFppfSite.{u})
    (A M X : Scheme.{u}) (hA : B.Contains A) (hM : B.Contains M) (hX : B.Contains X)
    (g : B.obj hA ⟶ B.obj hM) (j : B.obj hM ⟶ B.obj hX) :
    baseChange B M X hM hX j ⋙ baseChange B A M hA hM g ≅
      baseChange B A X hA hX (g ≫ j) := by
  refine NatIso.ofComponents (fun Y => by
    change (baseChange B A X hA hX (g ≫ j)).obj Y ≅
      (baseChange B A X hA hX (g ≫ j)).obj Y
    exact Iso.refl _) ?_
  intro Y Z f
  apply ObjectProperty.hom_ext
  rfl

/-- The component of the iterated base-change identification is the canonical cast. -/
theorem baseChangeIterToDirectIso_hom_app_eqToHom
    (B : BigFppfSite.{u})
    (A M X : Scheme.{u}) (hA : B.Contains A) (hM : B.Contains M) (hX : B.Contains X)
    (g : B.obj hA ⟶ B.obj hM) (j : B.obj hM ⟶ B.obj hX)
    (Y : AlgebraicSpaces B X hX) :
    (baseChangeIterToDirectIso B A M X hA hM hX g j).hom.app Y = eqToHom (by rfl) :=
  rfl

/-- The two iterated base changes associated to a commutative square are isomorphic. -/
noncomputable def squareBaseChangeIso
    (B : BigFppfSite.{u})
    (U' U X' X : Scheme.{u}) (hU' : B.Contains U')
    (hU : B.Contains U) (hX' : B.Contains X') (hX : B.Contains X)
    (gU : B.obj hU' ⟶ B.obj hU) (gX' : B.obj hU' ⟶ B.obj hX')
    (jU : B.obj hU ⟶ B.obj hX) (jX' : B.obj hX' ⟶ B.obj hX)
    (hcomm : gU ≫ jU = gX' ≫ jX') :
    (baseChange B U X hU hX jU ⋙ baseChange B U' U hU' hU gU) ≅
      (baseChange B X' X hX' hX jX' ⋙ baseChange B U' X' hU' hX' gX') := by
  let eU := baseChangeIterToDirectIso B U' U X hU' hU hX gU jU
  let eX' := baseChangeIterToDirectIso B U' X' X hU' hX' hX gX' jX'
  have hF : baseChange B U' X hU' hX (gU ≫ jU) =
      baseChange B U' X hU' hX (gX' ≫ jX') :=
    congrArg (fun f => baseChange B U' X hU' hX f) hcomm
  exact (eU.trans (eqToIso hF)).trans eX'.symm

/-- The compatible triple of base changes associated to an algebraic space. -/
noncomputable def canonicalGlueingTriple
    (B : BigFppfSite.{u})
    (U' U X' X : Scheme.{u}) (hU' : B.Contains U')
    (hU : B.Contains U) (hX' : B.Contains X') (hX : B.Contains X)
    (gU : B.obj hU' ⟶ B.obj hU) (gX' : B.obj hU' ⟶ B.obj hX')
    (jU : B.obj hU ⟶ B.obj hX) (jX' : B.obj hX' ⟶ B.obj hX)
    (hcomm : gU ≫ jU = gX' ≫ jX')
    (Y : AlgebraicSpaces B X hX) :
    GlueingData B U' U X' hU' hU hX' gU gX' := by
  let YU := (baseChange B U X hU hX jU).obj Y
  let YM := (baseChange B U' U hU' hU gU).obj YU
  let YX' := (baseChange B X' X hX' hX jX').obj Y
  let α := squareBaseChangeIso B U' U X' X hU' hU hX' hX gU gX' jU jX' hcomm
  refine ⟨Comma.mk (Comma.mk YM YU (𝟙 YM)) YX' (α.hom.app Y), ?_⟩
  constructor
  · change IsIso (𝟙 YM)
    infer_instance
  · dsimp
    exact (α.app Y).isIso_hom

/-- Functoriality of the canonical triple of base changes. -/
noncomputable def canonicalGlueingDataFunctor
    (B : BigFppfSite.{u})
    (U' U X' X : Scheme.{u}) (hU' : B.Contains U')
    (hU : B.Contains U) (hX' : B.Contains X') (hX : B.Contains X)
    (gU : B.obj hU' ⟶ B.obj hU) (gX' : B.obj hU' ⟶ B.obj hX')
    (jU : B.obj hU ⟶ B.obj hX) (jX' : B.obj hX' ⟶ B.obj hX)
    (hcomm : gU ≫ jU = gX' ≫ jX') :
    AlgebraicSpaces B X hX ⥤ GlueingData B U' U X' hU' hU hX' gU gX' := by
  let α := squareBaseChangeIso B U' U X' X hU' hU hX' hX gU gX' jU jX' hcomm
  refine
    { obj := canonicalGlueingTriple B U' U X' X hU' hU hX' hX gU gX' jU jX' hcomm
      map := fun {Y Z} f => ObjectProperty.homMk
        (CommaMorphism.mk
          (CommaMorphism.mk
            ((baseChange B U' U hU' hU gU).map ((baseChange B U X hU hX jU).map f))
            ((baseChange B U X hU hX jU).map f)
            (by simp [canonicalGlueingTriple]))
          ((baseChange B X' X hX' hX jX').map f)
          (by simpa [canonicalGlueingTriple, Functor.comp_map] using α.hom.naturality f))
      map_id := by
        intro Y
        apply ObjectProperty.hom_ext
        apply CommaMorphism.ext
        · apply CommaMorphism.ext <;> simp [canonicalGlueingTriple]
        · simp [canonicalGlueingTriple]
      map_comp := by
        intro Y Z W f k
        apply ObjectProperty.hom_ext
        apply CommaMorphism.ext
        · apply CommaMorphism.ext <;> simp [canonicalGlueingTriple]
        · simp [canonicalGlueingTriple] }

/-- The arrow over `U` of the canonical triple of an algebraic space is the identification of
iterated base change with direct base change. -/
private theorem canonicalGlueingDataFunctor_toU_eq
    (B : BigFppfSite.{u})
    (U' U X' X : Scheme.{u}) (hU' : B.Contains U')
    (hU : B.Contains U) (hX' : B.Contains X') (hX : B.Contains X)
    (gU : B.obj hU' ⟶ B.obj hU)
    (gX' : B.obj hU' ⟶ B.obj hX')
    (jU : B.obj hU ⟶ B.obj hX)
    (jX' : B.obj hX' ⟶ B.obj hX)
    (hcomm : gU ≫ jU = gX' ≫ jX')
    (Y : AlgebraicSpaces B X hX) :
    (canonicalGlueingDataFunctor B U' U X' X hU' hU hX' hX
      gU gX' jU jX' hcomm).obj Y |>.1.left.hom ≫
        (baseChange B U' U hU' hU gU).map
          (𝟙 ((baseChange B U X hU hX jU).obj Y)) =
      (baseChangeIterToDirectIso B U' U X hU' hU hX gU jU).hom.app Y ≫
        eqToHom (by rfl) := by
  change
    (𝟙 ((baseChange B U' U hU' hU gU).obj
      ((baseChange B U X hU hX jU).obj Y))) ≫
        (baseChange B U' U hU' hU gU).map
          (𝟙 ((baseChange B U X hU hX jU).obj Y)) =
      (baseChangeIterToDirectIso B U' U X hU' hU hX gU jU).hom.app Y ≫
        eqToHom (by rfl)
  rw [baseChangeIterToDirectIso_hom_app_eqToHom]
  simp only [CategoryTheory.Functor.map_id, Category.comp_id, Functor.comp_obj]
  cat_disch

private theorem canonicalGlueingDataFunctor_toX'_eq
    (B : BigFppfSite.{u})
    (U' U X' X : Scheme.{u}) (hU' : B.Contains U')
    (hU : B.Contains U) (hX' : B.Contains X') (hX : B.Contains X)
    (gU : B.obj hU' ⟶ B.obj hU)
    (gX' : B.obj hU' ⟶ B.obj hX')
    (jU : B.obj hU ⟶ B.obj hX)
    (jX' : B.obj hX' ⟶ B.obj hX)
    (hcomm : gU ≫ jU = gX' ≫ jX')
    (Y : AlgebraicSpaces B X hX) :
    (canonicalGlueingDataFunctor B U' U X' X hU' hU hX' hX
      gU gX' jU jX' hcomm).obj Y |>.1.hom ≫
        (baseChange B U' X' hU' hX' gX').map
          (𝟙 ((baseChange B X' X hX' hX jX').obj Y)) =
      (baseChangeIterToDirectIso B U' U X hU' hU hX gU jU).hom.app Y ≫
        eqToHom (by rw [hcomm]; rfl) := by
  change
    (squareBaseChangeIso B U' U X' X hU' hU hX' hX
      gU gX' jU jX' hcomm).hom.app Y ≫
        (baseChange B U' X' hU' hX' gX').map
          (𝟙 ((baseChange B X' X hX' hX jX').obj Y)) =
      (baseChangeIterToDirectIso B U' U X hU' hU hX gU jU).hom.app Y ≫
        eqToHom (by rw [hcomm]; rfl)
  unfold squareBaseChangeIso baseChangeIterToDirectIso
  simp only [Functor.comp_obj, Iso.trans_assoc, Iso.trans_hom, eqToIso.hom, Iso.symm_hom,
    NatTrans.comp_app, NatIso.ofComponents_hom_app, eqToHom_app, NatIso.ofComponents_inv_app,
    CategoryTheory.Functor.map_id, Category.comp_id, Iso.cancel_iso_hom_left]
  cat_disch

/-- The canonical functor from spaces over `X` to cartesian gluing triples, including its natural
comparison with all three base changes and the two induced arrows. -/
@[stacks 0F9N]
noncomputable def beauvilleLaszloGlueingSpaces
    (B : BigFppfSite.{u})
    (U' U X' X : Scheme.{u}) (hU' : B.Contains U')
    (hU : B.Contains U) (hX' : B.Contains X') (hX : B.Contains X)
    (gU : B.obj hU' ⟶ B.obj hU)
    (gX' : B.obj hU' ⟶ B.obj hX')
    (jU : B.obj hU ⟶ B.obj hX)
    (jX' : B.obj hX' ⟶ B.obj hX)
    (hcomm : gU ≫ jU = gX' ≫ jX') :
    GlueingFunctorSpec B U' U X' X hU' hU hX' hX gU gX' jU jX' hcomm := by
  let F := canonicalGlueingDataFunctor B U' U X' X hU' hU hX' hX gU gX' jU jX' hcomm
  let eUOverUIso : F ⋙ overU B U' U X' hU' hU hX' gU gX' ≅
      baseChange B U X hU hX jU := NatIso.ofComponents
    (fun Y => Iso.refl ((baseChange B U X hU hX jU).obj Y)) (by
    intro Y Z f
    rfl)
  let eMid := baseChangeIterToDirectIso B U' U X hU' hU hX gU jU
  let eXOverX'Iso : F ⋙ overX' B U' U X' hU' hU hX' gU gX' ≅
      baseChange B X' X hX' hX jX' := NatIso.ofComponents
    (fun Y => Iso.refl ((baseChange B X' X hX' hX jX').obj Y)) (by
    intro Y Z f
    rfl)
  refine
    { functor := F
      overUIso := eUOverUIso
      overU'Iso := eMid
      overX'Iso := eXOverX'Iso
      toU_eq := by
        intro Y
        exact canonicalGlueingDataFunctor_toU_eq B U' U X' X hU' hU hX' hX
          gU gX' jU jX' hcomm Y
      toX'_eq := by
        intro Y
        exact canonicalGlueingDataFunctor_toX'_eq B U' U X' X hU' hU hX' hX
          gU gX' jU jX' hcomm Y }

end BeauvilleLaszlo.Space

end
